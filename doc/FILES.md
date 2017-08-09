Files
=====

Files in Verdi Chord.

Support files/modules
---------------------

- `Sorting.v`: mergesort used by the Chord start handler to sort nodes according to identifier order

- `Bitvectors.v`: representation and operations of node identifiers - namespace parameterized on the number of bytes in identifiers (could contain order as well)

- `IDSpace.v`: module type for Chord namespace, and operations on identifiers, and lemmas on identifiers

- `Measure.v`: localizing liveness reasoning, uses the semantics

Core files
----------

- `DynamicNet.v`: systems and network semantics definitions
  * dynamic system - all basic types used in the semantics
  * constrained dynamic system - defines events for trace (never use); unify labels and the event type?
  * timeout_constraint - when can a timeout fire?
  * failure_constraint - when can nodes crash?
  * various functions used in network semantics to update state
  * churn semantics: clients can put messages in network or take messages
  * labeled semantics: all steps except join/fail + definitions for infseq
  * if you take churn step, there must be new nodes or fewer nodes

- `Chord.v`: handler functions and lemmas about handlers
  * contains order on identifiers
  * has axiom for injectivity of identifiers (prevent adding addresses that violate injectivity, can be used to prove false)
  * definition of messages, clients, data, actual code that nodes execute (not in semantics)
  * query is internal state node uses to track what to do when they get a response
  * handle_msg is the interesting function; Notify -> schedule rectify; forward to busy/non-busy handler; otherwise handle req
  * functions are deeply nested
  * timeout constraints
  * failure constraints
  * bottom module yields the naked semantics
  * plugs Chord handler definitions into the semantics
  * merge into chord.v?
  * split out constraints that don't refer to chord?

- `ChordHandlerLemmas.v`: huge lemmas that characterize the output of each handler function used by nodes
  * facts about implementation functions only!
  * distinct lemmas, no big plan

- `ChordProof.v`: basic handler lemmas, simple safety properties
  * defines initial state of the network
  * mix of semantic properties and handler properties
  * candidate for reorganization
  * proves "meta-theorems" that make proving induction properties easier (not finished yet, though)

- `ChordLocalProps.v`: predicates on payloads and lemmas about predicates
  * merge into chord semantics? or chord.v?
 
- `ChordLabeled.v`: basic lemmas about labeled semantics (messages eventually delivered, etc.)
  * move into core?

- `ChordValidPointersInvariant.v`: pointers point to reasonable things
  * move into `invariants` subdirectory
  
- `LiveNodesStayLive.`
  * move into `invariants` subdirectory

- `ChordPromises.v`: admits that should be proven

- `ChordPhaseOne.v`: general facts about that stabilization eventually happens
  * admits can be proved using simple facts from labeled semantics, exactly what is needed, may need to be reformulated 
  * proofs are somewhat ad-hoc
  * uses measure machinery heavily

- `ChordPhaseTwo.v`: proves chains of eventually properties
  * event e -> error decreases
  * event e' -> error decreases
  * use that ticks eventually happen, we have that from phase one
  * lots of admits, not all used
  * mergepoints: part of the argument, case analysis

- `ChordCorrectness.v`: collection of all liveness lemmas
   * top level theorem is the last theorem in file
   * phases are in their own files
   * request always effective: distinguish between timeouts
