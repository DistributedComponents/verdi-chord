Files
=====

Files in Verdi Chord.

Support files
-------------

- `lib/Sorting.v`: mergesort used by the Chord start handler to sort nodes according to identifier order

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

- `systems/chord-util/SystemLemmas.v`: lemmas about the Chord system and handler effects on global state

- `systems/chord-util/LabeledLemmas.v`: basic lemmas about labeled semantics
  * messages eventually delivered, etc.

- `systems/chord-util/LabeledMeasures.v`: localizing liveness reasoning, uses the labeled semantics

- `systems/chord-util/SystemReachable.v`: definition of a reachable state in the Chord system
  * proves "meta-theorems" that make proving induction properties easier (not finished yet, though)

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


