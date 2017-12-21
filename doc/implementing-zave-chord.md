# Table of contents
1. Network model
2. Local state
3. Timeouts
   - `KeepaliveTick`
   - `Tick`
   - `Request h msg`
4. Joining operations
5. Repair operations
   - Stabilization
   - Rectifying

# Network model
Chord nodes have addresses and IDs. An ID is a hash of an address. The `pointer`
type is pairs of addresses and their corresponding ID. Think of addresses as
being opaque things like IP addresses and think of IDs as being a circularly
ordered space on those addresses.

The network semantics allow nodes to join at any time. They do not allow
failures in general: instead, nodes that fail have to have no outgoing messages
in the network. Timeouts are also constrained. A `Request` timeout can only fire
if the node on the other end has failed.

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
  - The successor list `succ_list` is a list of `SUCC_LIST_LEN` elements
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
Queries to other nodes can change a node's local state. According to Zave:

> In an implementation, a node reads the state of another node by querying it.
> If the node does not respond within a time parameter t, then it is presumed
> dead. If the node does respond, then the atomic step associated with the query
> is deemed to occur at the instant that the queried node responds with
> information about its own state.
>
> To maintain the shared-state abstraction, the querying node must obey the
> following rules:
> - The querying node does not know the instant that its query is answered; it
>   only knows that the response was sent some time after it sent the query. So
>   the querying node must treat its own state, between the time it sends the
>   query and the time it finishes the step by updating its own state, as
>   undefined. The querying node cannot respond to queries about its state from
>   other nodes during this time.
> - If the querying node is delaying response to a query because it is waiting
>   for a response to its own query, it must return interim “response pending”
>   messages so that it is not presumed dead.
> - If a querying node is waiting for a response, and is queried by another node
>   just to find out if it is alive or dead, it can respond immediately. This is
>   possible because the response does not contain any information about its
>   state.

This is a big wall of text, but what it boils down to is this: nodes that are
waiting for responses to queries that could potentially alter their state (nodes
that are *busy*) can't tell other nodes what their `succ_list` or `pred` are.

A busy node `b` replies to requests about state with a `Busy` message and
registers a `KeepaliveTick` timeout, which the other node takes as a sign to
reset its timeouts. This keeps `b` from being marked as dead. All requests while
`b` is busy are stored in `delayed_queries`. When the query `b` is working on
completes, it sends actual responses to all the queries in `delayed_queries` all
at once.

Until then, the `KeepaliveTick` causes `b` to send a `Busy` message back to each
node that has sent `b` a request it had to delay. The `KeepliaveTick` is cleared
when `b` finishes its query. There is only ever one `KeepaliveTick` pending at
any node since they are only registered for the first delayed request and then
again after they fire.

## `Tick`: stabilize if you can
The `Tick` timeout is registered when a node finishes joining and sets `joined =
true`. When a `Tick` fires at a node `n` that isn't busy, `n` starts a
`Stabilize` step.

## `Request h msg`
When a node `n` sends a request to a node `h`, it registers a `Request h msg`
timeout which is only ever cleared if `h` sends an appropriate response to the
`msg`. If a `Request` timeout fires, `h` is presumed dead. Exact behavior
depends on what kind of query `n` was trying to complete.

# Joining operations
## Finding a best predecessor
### The `Join` query
When a node `n` starts up with a known node `k`, it sends a
`GetBestPredecessor(n)` request to `k`. If `n` sits between two consecutive
nodes `s1` and `s2` in the successor list of `k`, it replies with `s1`.
Otherwise `k` sends back the address of the last node `s` in its successor list.
Then, whatever `k` replies with, `n` does the same thing again until it reaches
a fixpoint: it queries a node `p` for the best predecessor of `n` and `p` says
`p` is the best predecessor.

Then `n` queries `p` for its successor list. If that query times out, it
backtracks to `k` and starts over. If `p` responds with a successor list `s ::
rest`, then `n` starts a `Join2(s)` query.

## Getting some state
### The `Join2(s)` query
A node `n` requests a copy of the successor list `succs` of `s`. If the query
times out, `n` starts back over joining at its `known_node`. Otherwise, `n` sets
its successor list to `s :: succs` truncated to `SUCC_LIST_LEN` and sets `joined
= true`.

This means a node with `joined = true` will initially have `pred = None`.

# Repair operations
## Stabilization
To repair their succesor lists, nodes periodically stabilize. This involves two
queries: a `Stabilize` and possibly a `Stabilize2`. Regardless of how their
successor list changes while stabilizing, upon finishing the operation nodes
always send a `Notify` message to their first successor. This lets the first
successor know it should rectify (see below).

### The `Stabilize` query
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

### The `Stabilize2` query
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
its successor list to be `p :: succs` truncated to `SUCC_LIST_LEN`, and sends a
`Notify` to `s`.

## Rectifying
The top-level message handler does three things in a row. First, it handles
whatever message came in. This usually means replying to queries or handling
query responses. Second, it sends any delayed responses. Third, it tries to
rectify. This means that if you end a query, you can go straight to rectifying
without leaving a chance for a timeout--but it also makes it more likely that a
rectify operation will happen sooner.

Note that we don't need to worry about one `rectify_with` being overwritten by
another `Notify` message because we only update `rectify_with` when the new
value is a better predecessor.

```
handle_notify(src):
  if between(rectify_with, src, me)
  then rectify_with := src
  else do nothing
```

In any case, at some point we handle a message, run the `do_rectify` function,
have a pointer in `rectify_with`, and aren't already in the middle of some other
query. At this point we run `Rectify`.

### The `Rectify` query

When a node `n` runs a `Rectify(notifier)` query, it sends a `Ping` to its
predecessor `p`. If it never gets a `Pong` back or `notifier` is a better
predecessor for `n` than `p` is, `n` updates its predecessor pointer to be
`notifier`. Otherwise nothing happens.

```
query Rectify(notifier):
  query predecessor with a Ping

  if query times out
  then set predecessor = notifier
  else if between(predecessor, notifier, me)
  then set predecessor = notifier
  else do nothing

  end query
```
