Files
=====

Files in Verdi Chord.

Support files
-------------

- `lib/Sorting.v`: mergesort used by the Chord start handler to sort nodes according to identifier order
  * admitted `sort_permutes`

- `lib/Bitvectors.v`: representation and operations of node identifiers - namespace parameterized on the number of bytes in identifiers (could contain order as well)

- `lib/IDSpace.v`: module type for Chord namespace, operations on identifiers, and lemmas on identifiers

Network files
-------------

- `core/DynamicNet.v`: systems and network semantics definitions
  * dynamic system - all basic types used in the semantics
  * constrained dynamic system - defines events for trace (never use); unify labels and the event type?
  * timeout_constraint - when can a timeout fire?
  * failure_constraint - when can nodes crash?
  * various functions used in network semantics to update state
  * churn semantics: clients can put messages in network or take messages
  * labeled semantics: all steps except join/fail + definitions for infseq
  * if you take churn step, there must be new nodes or fewer nodes
  * admitted: `labeled_step_dynamic_is_step_dynamic_without_churn` (connection between labeled and unlabeled semantics)

Chord files
-----------

- `systems/chord/Chord.v`: Chord system and handler definitions
  * contains order on identifiers
  * has axiom for injectivity of identifiers (prevent adding addresses that violate injectivity, can be used to prove false)
  * definition of messages, clients, data, actual code that nodes execute (not in semantics)
  * query is internal state node uses to track what to do when they get a response
  * handle_msg is the interesting function; Notify -> schedule rectify; forward to busy/non-busy handler; otherwise handle req
  * functions are deeply nested
  * timeout constraints
  * failure constraints
  * module yields the naked semantics
  * plugs Chord handler definitions into the semantics
  * split out constraints that don't refer to chord?
  * initial state definition
  * admitted: `ext_succ_list_span_includes` (definition needs to be changed to work with bitvectors)

- `systems/chord/ChordCorrectPhaseOne.v`: general facts about that stabilization eventually happens in Chord systems
  * admits can be proved using simple facts from labeled semantics, exactly what is needed, may need to be reformulated
  * proofs are somewhat ad-hoc
  * uses measure machinery heavily

- `systems/chord/ChordChordPhaseTwo.v`: proves chains of eventually properties
  * event e -> error decreases
  * event e' -> error decreases
  * use that ticks eventually happen, we have that from phase one
  * lots of admits, not all used
  * mergepoints: part of the argument, case analysis

- `systems/chord/ChordCorrectPhaseThree.v`: collection of all liveness lemmas
   * top level theorem is the last theorem in file
   * phases are in their own files
   * request always effective: distinguish between timeouts

Chord correctness support files
-------------------------------

- `systems/chord-util/HandlerLemmas.v`: lemmas about handlers
   * lemmas that characterize the output of each handler function used by nodes
   * admitted: `joined_preserved_by_timeout_handler_eff`

- `systems/chord-util/SystemLemmas.v`: lemmas about the Chord system and handler effects on global state
  * admitted: `nodes_have_state` (all live nodes have some state in semantics with churn)
  * admitted: `adding_nodes_did_not_affect_best_succ` (best successor remains the same under churn)

- `systems/chord-util/SystemPointers.v`: definition and lemmas about (valid) pointers
  * admitted: `valid_ptrs_global_timeout_handler`
  * admitted: `valid_ptrs_global_recv_handler`
  * admitted: `apply_handler_result_In_timeouts`
  * admitted: `valid_ptrs_global_timeouts`
  * admitted: `valid_ptrs_global_sigma`
  * admitted: `valid_ptrs_global_net`
  * admitted: `valid_ptrs_global_trace`
  * admitted: `valid_ptrs_state_nodes_subset`
  * admitted: `start_handler_valid_ptrs_state`

- `systems/chord-util/LabeledLemmas.v`: basic lemmas about labeled semantics
  * messages eventually delivered, etc.
  * admitted: `recv_implies_node_in` (receiving messages means receiver hasn't failed)
  * admitted: `RecvMsg_enabled_until_occurred`
  * admitted: `recv_handler_never_clears_RectifyTick`
  * admitted: `constrained_Request_not_cleared_by_recv_handler`
  * admitted: `request_constraint_prevents_recv_adding_msgs`
  * admitted: `Tick_eventually_enabled`
  * admitted: `clients_not_in_failed`
  * admitted: `other_timeouts_not_cleared`
  * admitted: `channel_stays_empty`
  * admitted: `dead_node_channel_empties_out`
  * admitted: `request_stays_in`
  * admitted: `msgs_remain_after_timeout`
  * admitted: `timeout_constraint_lifted_by_clearing`
  * admitted: `queries_are_closed_by_recvmsg_occ`
  * admitted: `inv_responses_are_unique`
  * admitted: `inv_Request_payload_has_response`
  * admitted: `now_recvmsg_now_clears_timeout`
  * admitted: `Request_implies_open_request_to`
  * admitted: `requests_eventually_get_responses`

- `systems/chord-util/LabeledMeasures.v`: localized liveness reasoning on the labeled semantics

- `systems/chord-util/SystemReachable.v`: definition of a reachable state in the Chord system
  * proves "meta-theorems" that make proving induction properties easier (not finished yet, though)
  * admitted: `queries_always_remote`
  * admitted: `adding_node_preserves_reachable_converse`
  * admitted: `query_state_net_invariant_inductive`

Chord correctness properties files
----------------------------------

- `systems/chord-props/DeadNodesGoQuiet.v`: messages from dead nodes are eventually all processed
  * used in phase one correctness

- `systems/chord-props/NodesAlwaysHaveLiveSuccs.v`: in all reachable states, successor lists are nonempty and have only live nodes
  * nonempty successor list property is used in phase on correctness
  * in Zave's paper, that nodes only have live nodes in successor lists is one half of the inductive invariant

- `systems/chord-props/QueriesEventuallyStop.v`: operations undertaken by joined nodes complete in finitely many request-response pairs
  * if you have an open request, you're in the middle of some operation
  * a request eventually gets a response if there are no circular waits
  * used in phase one correctness for the proof of eventual stabilization

- `systems/chord-props/TickInvariant.v`: not formulated yet

- `systems/chord-props/FirstSuccNeverSelf.v`: if a node's successor list contains a first entry, it is not the node itself
  * a consequence of the Zave invariant.
  * used in phase two correctness

- `systems/chord-props/NodesNotJoinedHaveNoSuccessors.v`: successor lists of never-active nodes are empty
  * used in phase one correctness

- `systems/chord-props/QueryInvariant.v`: at most one request per timeout

- `systems/chord-props/ValidPointersInvariant.v`: pointers point to reasonable things
  * used in labeled lemmas

- `systems/chord-props/LiveNodeHasTickInTimeouts.v`: newly activated nodes have no Tick
  * used in phase one correctness

- `systems/chord-props/PredNeverSelfInvariant.v`: if a node has a predecessor, it is not itself
  * used in phase two correctness

- `systems/chord-props/StabilizeOnlyWithFirstSucc.v`: if we have an appropriate Request timeout, we have all the other trappings of a Stabilize request
  * used in phase one correctness

- `systems/chord-props/WfPtrSuccListInvariant.v`: pointers in successor lists are well-formed
  * used in phase one correctness

- `systems/chord-props/WfPtrPredInvariant.v`: pointers in predecessor lists are well-formed
  * could potentially be used in phase two correctness to lift some assumptions

- `systems/chord-props/LiveNodesStayLive.v`: live nodes in the labeled semantics stay live

- `systems/chord-props/PtrCorrectInvariant.v`: at a node, a copy of a self-pointer is set at startup and never changed
  * used in phase two correctness

- `systems/chord-props/SuccessorNodesAlwaysValid.v`: every successor list points to a node that is both live and has joined the ring
  * used in phase one correctness

OCaml files
-----------

* `extraction/chord/ml/DynamicShim.ml`: TCP-based shim that handles network communication

* `extraction/chord/ml/ChordArrangement.ml`: modules and functions to connect extracted functions to the shim

* `extraction/chord/ml/ChordUtil.ml`: IP address and socket utility functions used by shim

* `extraction/chord/ml/chord.ml`: command line interface to Chord node that uses shim and arrangement

* `extraction/chord/ml/client.ml`: command line program to query Chord systems
