# Network model
Chord nodes have addresses and IDs. An ID is a hash of an address. The `pointer`
type is pairs of addresses and their corresponding ID. Think of addresses as
being opaque things like IP addresses and think of IDs as being a circularly
ordered space on those addresses.

# Local state
Between operations, a Chord node keeps track of these things and these things
only.
```
  Record _data := mkData { ptr : pointer;
                          pred : option pointer;
                          succ_list : list pointer;
                          known : pointer;
                          joined : bool;
                          rectify_with : option pointer;
                          cur_request : option (pointer * query * payload);
                          delayed_queries : list (addr * payload) }.
```

  - The first field `ptr` is just a pointer to the node itself.
  - The `pred` pointer, if defined, points to what the node thinks its predecessor is.
  - The successor list `succ\_list` is a list of `SUCC\_LIST\_LEN` elements
    (hopefully) ordered by nearness in the ring.
  - The `known` pointer identifies the node we used (or are using) to join the
    network.
  - The `joined` flag starts out `false` and is set to `true` when we obtain a
    successor list from `known` at the end of the Join sequence.
  - When someone sends us a `Notify` message, the `rectify_with` pointer is set
    to point to them and later cleared when a `Rectify` query begins.
  - When we start a query, `cur_request` is set to a tuple `(dst, q, msg)` where
    `dst` is the address of the node we're querying, `q` is the query we're
    performing, and `msg` is the message we sent them.
  - When we're performing a query that could change our local state, we reply to
    requests with a `Busy` message and record the request in `delayed_queries`.
    Once we're done changing (or not changing) our local state, we send replies
    to all the stored messages in `delayed_queries`.

# Timeouts
## `KeepaliveTick` and the shared memory model
## `Tick`: stabilize if you can
## `Request h msg`

# Joining operations
## Finding best predecessor
### `Join`
## Getting some state
### `Join2`

# Repair operations

## Stabilization
To repair their succesor lists, nodes periodically stabilize. This involves two
queries: a `Stabilize` and possibly a `Stabilize2`. Regardless of how their
successor list changes while stabilizing, upon finishing the operation nodes
always send a `Notify` message to their first successor. This lets the first
successor know it should rectify (see below).

### `Stabilize`
To start stabilizing, a node `n` queries its first successor `s` for its
predecessor and list of successors. If the request times out, `n` drops `s` from
its successor list and tries to run a `Stabilize` on the next node in the list.

If `n` gets back a predecessor `p` and list of successors `succs` from `s`, the
successor list at `n` is updated to be `s :: succs`. If `p` is between `n` and
`s` in identifier order, then `n` will try running a Stabilize2 query to it
(more on this later).

> Why doesn't `n` just adopt `s` as its successor immediately? Because Chord
> nodes *never* adopt new pointers, whether predecessors or successors, without
> first checking that the pointer refers to a live node.

If `p` is not a better successor for `n` than `s`, the query is closed and `n`
sends a `Notify` message to `s`.

In pseudocode:
```
query Stabilize():
  succ_pred, succ_succs <- query (head succ_list) for its pred and succ_list
  if query times out
  then set succ_list = tail succ_list
       start query Stabilize()
  else if succ_pred = None
  then end query
  else
    let Some new_succ = succ_pred
    set succ_list = chop (head succ_list :: succ_succs)
    if better_succ(new_succ, head succ_list)
    then
      start query Stabilize2(new_succ)
    else
      send Notify to (head succ_list)
      end query
```

### `Stabilize2`
If `n` determines in the course of its `Stabilize` query that its first
successor's predecessor `p` is a better first successor for it, then it runs a
`Stabilize2` query to ask `p` for its successor list. In the identifier space,
the situation looks something like this.
```
n ----- 1st successor -----> s
     p < - - predecessor - - s
```
If the query to `p` times out, then `n` ends the query, sends a `Notify` to `s`,
and doesn't change its state.

If `p` replies with its successor list `succs`, then `n` ends the query, updates
its successor list to be `p :: succs` truncated to `SUCC\_LIST\_LEN`, and sends a
`Notify` to `s`.

## Rectifying
### `Rectify`
