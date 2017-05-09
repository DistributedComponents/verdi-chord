To detect failures, nodes periodically stabilize.
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


Chord nodes have addresses and IDs. An ID is a hash of an address. The `pointer`
type is pairs of addresses and their corresponding ID. A Chord node maintains
the following state.
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

Here's what all these mean.
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
