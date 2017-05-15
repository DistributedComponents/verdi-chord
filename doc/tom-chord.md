let me amplify a bit on the (garbled audio) comment I made thursday about
labelling distributed state transfers with version numbers.  Obviously if you
have see a path to proving correctness/liveness of the original chord algorithm
and/or Zave's version of the algorithm, you can safely ignore this.  one thing
worth doing (imo), if we haven't yet, is to implement Zave's algorithm and then
turn model checking loose on it.

I set myself the task of trying to come up with a workable ring maintenance
algorithm, under the Zave constraint -- joins, async comms, limited number of
failures, eventually consistent, live, ring size > epsilon. Working through the
details caused me to think proving liveness of Chord/Zave would be harder than
I thought.

The intuition behind version numbers is to turn distributed state management
into a functional program (local state is never updated, it is just versioned).
This can make invariants easier to specify. For example, finding an eventually
consistent minimum spanning tree is trivial in this model and not otherwise --
you pong repeatedly from the root, with version numbers, and all state derived
from the same version number is consistent everywhere, regardless of message
order delivery and failures. So, somewhat trivially, if there are no further
changes, a single recursively broadcast pong after the last change, and building
state based on the highest numbered pong you have seen to date, is enough to get
convergence. If you label messages with the version of known at the time at the
source of the message, you can safely deliver it everywhere using that version
of the MST (rather than the current state that may be dynamically being updated
while the message is in flight!) -- if the specific MST version becomes
disconnected by a later failure, you can just retry.

The original Chord implementation did not do this; it attempts to update state
in place, and so any proof needs to reason about the effect on global/local
state of all possible join, failure, and message orderings.  I don't know enough
about Zave's changes to be able to speak authoritatively about it, so I started
looking for a simple implementation of a Chord-like ring maintenance algorithm
based on version #s where I could be easily convinced it is both correct and
live. It is possible I'm just recapitulating Zave here.  (Another place to look
is Pastry -- unlike Chord, those authors did understand consensus.)

My approach uses version #'s, commutativity, and chain replication.  I assume we
want to be able to survive k-1 failures (between reconvergence steps), and each
node keeps k successors, and 1 predecessor.  for now, i'm going to ignore key
replication.  

1) if we assume no joins, and up to k-1 failures, and the ring was k-connected
   prior to any failures, then it is simple to rebuild the k-successor list by
   repeated versioned pongs, MST style with a depth of k.

2)  there are k+2 nodes whose state we need to update on a join (joiner,
    k predecessors, and the one successor). keeping things simple, let's insist
    that the k predecessors and the one successor need to have a consistent view
    of their state to proceed (which they can get from step 1).  

Secondly, let's insist that each successor node processes at most one join
request at a time.  No harm here -- the joiner talks to the successor, so if the
joiner fails during the join process, the successor can pick up and move the
system back to quiescence before accepting the next join request.

I would like to further insist that none of the k predecessors processes a join
request at the same time, as that would give us serializable updates to
distributed state.  as long as joins are serializable, we're done, because step
1 lets us recover from failures. However, since we're in a ring, we can't use
per-node locks (because of deadlock).  It is possible that we could devise
a special purpose paxos like algorithm that is both non-blocking and
serializable.  Let me leave that option on the shelf for now, as my initial
attempts in that direction weren't simple (e.g., it would probably need to
involve 2k+1 nodes, not just the k+2 with state to be updated).

Instead, let's note that simultaneous joins to different successors are
commutative with respect to node state.  The tricky part is to make that work
despite k-1 failures that can occur during the join process.

3) a three phase algorithm

a) verify all k+2 nodes have the same version.  Joiner starts a message at the
successor, which is forwarded to predecessors.  when it reaches the tail (the
kth predecessor), it goes back to the joiner, with success.  If the predecessor
links are wrong or any of the nodes are out of date, you can just drop, go back
to step 1 (resynch state), and retry later

at this point, all nodes know about the join (equal to "joined" in the Zave
protocol?).

b)  joiner starts a versioned message at the successor with all of the
information about the join (e.g., names and versions of the successor and
predecessors).  It proceeds to construct the new state needed at each node if
this join succeeds, but the old state is kept around.  commit happens when it
reaches the tail and returns to the joiner.

possible that multiple updates will proceed concurrently.  Since you don't know
if a change will commit, you need to keep multiple versions, and merge as
necessary. 

at this point, all nodes have computed the new state (equal to "rectify" in the
Zave protocol?) but have the old state to fall back upon

c) garbage collection.  joiner can pass a message from successor through all
predecessors saying the update committed and it is ok to throw away the old
state.

during this join process, you need to do key replication across k+1 rather than
k nodes -- the joiner, its immediate successor, and the k-1 other successors, so
that the joiner is up to date with respect to the successor, and so that the
successor can discard its (now redundantly stored) keys in step c.
