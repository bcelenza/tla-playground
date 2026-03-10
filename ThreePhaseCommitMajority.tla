---- MODULE ThreePhaseCommitMajority ----
\*
\* Majority-Quorum Three-Phase Commit with Concurrent Transactions & Locking
\*
\* Extends the majority-quorum 3PC to model multiple concurrent transactions
\* competing for locks on RMs.  Locking strategy:
\*
\*   - Locks acquired in deterministic order (sorted RM names)
\*   - If FIRST RM is busy → abort entire TX ("losing race")
\*   - If later RM is busy → skip it, try for quorum from others
\*   - Sequential locking until quorum; then parallel for remainder
\*   - Lock released on commit/abort (connection-scoped)
\*
\* Compare with single-TX version — now we can verify deadlock freedom
\* and mutual exclusion with multiple competing coordinators.
\*

EXTENDS FiniteSets, Naturals

\* --- Constants ---
CONSTANT RM  \* The set of resource managers, e.g. {"rm1", "rm2", "rm3"}
CONSTANT TX  \* The set of transactions, e.g. {"tx1", "tx2"}

\* --- Variables ---
VARIABLES
    rmState,        \* Function: rmState[r] \in {"working", "prepared", "precommitted", "committed", "aborted", "failed"}
    lockHolder,     \* Function: lockHolder[r] \in TX \cup {"none"} — who holds the lock on RM r
    txState,        \* Function: txState[t] \in {"acquiring", "init", "precommitted", "committed", "aborted"}
    txLocked,       \* Function: txLocked[t] = set of RMs that TX t has locked
    txPrepared,     \* Function: txPrepared[t] = set of RMs that prepared for TX t
    txPrecommitted  \* Function: txPrecommitted[t] = set of RMs that precommitted for TX t

vars == <<rmState, lockHolder, txState, txLocked, txPrepared, txPrecommitted>>

\* ===================================================================
\* Helper: majority quorum
\* ===================================================================

\* True when S contains more than half the resource managers.
IsMajority(S) == Cardinality(S) * 2 > Cardinality(RM)

\* ===================================================================
\* Helper: deterministic lock order
\* ===================================================================

\* For simplicity, we assign each RM a numeric index for ordering.
\* In TLC, we use a CHOOSE to pick a consistent ordering.
\* This models alphabetical or priority-based sorting.

\* Pick a total ordering of RMs (any consistent ordering works).
\* We represent this as a function from RM -> 1..Cardinality(RM).
RMOrdering == CHOOSE f \in [RM -> 1..Cardinality(RM)] :
    \A r1, r2 \in RM : r1 # r2 => f[r1] # f[r2]

\* Index of an RM in the lock order (1-based).
RMIndex(r) == RMOrdering[r]

\* The "first" RM in lock order (index 1).
\* If this one is busy, TX should abort immediately.
FirstRM == CHOOSE r \in RM : RMIndex(r) = 1

\* RMs that come BEFORE r in lock order (must be locked first).
RMsBefore(r) == {r2 \in RM : RMIndex(r2) < RMIndex(r)}

\* Next RM to lock for TX t: first RM in order that t hasn't tried yet.
NextRMToLock(t) ==
    LET untried == {r \in RM : r \notin txLocked[t]}
    IN IF untried = {} THEN "none"
       ELSE CHOOSE r \in untried : \A r2 \in untried : RMIndex(r) <= RMIndex(r2)

\* ===================================================================
\* Type invariant
\* ===================================================================

TypeOK ==
    /\ rmState \in [RM -> {"working", "prepared", "precommitted", "committed", "aborted", "failed"}]
    /\ lockHolder \in [RM -> TX \cup {"none"}]
    /\ txState \in [TX -> {"acquiring", "init", "precommitted", "committed", "aborted"}]
    /\ txLocked \in [TX -> SUBSET RM]
    /\ txPrepared \in [TX -> SUBSET RM]
    /\ txPrecommitted \in [TX -> SUBSET RM]

\* ===================================================================
\* Initial state
\* ===================================================================

Init ==
    /\ rmState         = [r \in RM |-> "working"]
    /\ lockHolder      = [r \in RM |-> "none"]
    /\ txState         = [t \in TX |-> "acquiring"]  \* All TXs start trying to acquire locks
    /\ txLocked        = [t \in TX |-> {}]
    /\ txPrepared      = [t \in TX |-> {}]
    /\ txPrecommitted  = [t \in TX |-> {}]

\* ===================================================================
\* Lock Acquisition Phase
\* ===================================================================

\* TX t successfully acquires lock on RM r.
\* Preconditions:
\*   - TX is in acquiring state
\*   - r is the next RM in lock order for this TX
\*   - r is not locked by anyone
TXAcquireLock(t, r) ==
    /\ txState[t] = "acquiring"
    /\ NextRMToLock(t) = r
    /\ lockHolder[r] = "none"
    /\ lockHolder' = [lockHolder EXCEPT ![r] = t]
    /\ txLocked' = [txLocked EXCEPT ![t] = @ \cup {r}]
    /\ UNCHANGED <<rmState, txState, txPrepared, txPrecommitted>>

\* TX t fails to acquire lock on FIRST RM (it's busy) → abort immediately.
\* This is the "losing race" optimization — if you can't get the first
\* lock, another TX is ahead of you, so back off immediately.
TXFirstRMBusy(t) ==
    /\ txState[t] = "acquiring"
    /\ txLocked[t] = {}                      \* Haven't locked anything yet
    /\ NextRMToLock(t) = FirstRM             \* Trying for first RM
    /\ lockHolder[FirstRM] \in TX \ {t}      \* Someone else holds it
    /\ txState' = [txState EXCEPT ![t] = "aborted"]
    /\ UNCHANGED <<rmState, lockHolder, txLocked, txPrepared, txPrecommitted>>

\* TX t fails to acquire lock on a LATER RM (it's busy) → skip it.
\* TX will try to proceed with whatever quorum it can get.
TXLaterRMBusy(t, r) ==
    /\ txState[t] = "acquiring"
    /\ txLocked[t] # {}                      \* Have locked at least one
    /\ NextRMToLock(t) = r
    /\ r # FirstRM                           \* Not the first RM
    /\ lockHolder[r] \in TX \ {t}            \* Someone else holds it
    \* "Skip" this RM by marking it as if we tried (add to a skip set)
    \* For simplicity, we model this by just moving on — the RM won't be in txLocked
    /\ txLocked' = [txLocked EXCEPT ![t] = @ \cup {r}]  \* Mark as "attempted" (but won't hold lock)
    /\ UNCHANGED <<rmState, lockHolder, txState, txPrepared, txPrecommitted>>

\* TX t has finished lock acquisition phase → transition to init.
\* Requires: acquired locks on enough RMs for potential quorum.
TXFinishAcquiring(t) ==
    /\ txState[t] = "acquiring"
    /\ NextRMToLock(t) = "none"              \* Tried all RMs
    /\ LET actuallyLocked == {r \in txLocked[t] : lockHolder[r] = t}
       IN IsMajority(actuallyLocked)          \* Have quorum of locks
    /\ txState' = [txState EXCEPT ![t] = "init"]
    /\ UNCHANGED <<rmState, lockHolder, txLocked, txPrepared, txPrecommitted>>

\* TX t cannot achieve quorum → abort.
TXQuorumImpossible(t) ==
    /\ txState[t] = "acquiring"
    /\ NextRMToLock(t) = "none"              \* Tried all RMs
    /\ LET actuallyLocked == {r \in txLocked[t] : lockHolder[r] = t}
       IN ~IsMajority(actuallyLocked)         \* Don't have quorum
    /\ txState' = [txState EXCEPT ![t] = "aborted"]
    /\ UNCHANGED <<rmState, lockHolder, txLocked, txPrepared, txPrecommitted>>

\* ===================================================================
\* RM Failure
\* ===================================================================

\* An RM can fail (crash) at any time, unless already in a terminal state.
\* Failed RMs stop participating in the protocol entirely.
\* Lock is released when RM fails (connection drops).
RMFail(r) ==
    /\ rmState[r] \notin {"committed", "aborted", "failed"}
    /\ rmState' = [rmState EXCEPT ![r] = "failed"]
    /\ lockHolder' = [lockHolder EXCEPT ![r] = "none"]  \* Lock released on failure
    /\ UNCHANGED <<txState, txLocked, txPrepared, txPrecommitted>>

\* ===================================================================
\* Phase 1: Prepare
\* ===================================================================

\* An RM votes to prepare (says "yes, I can commit").
\* Only if a TX holds its lock and TX is in init state.
RMPrepare(t, r) ==
    /\ txState[t] = "init"
    /\ lockHolder[r] = t
    /\ rmState[r] = "working"
    /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
    /\ UNCHANGED <<lockHolder, txState, txLocked, txPrepared, txPrecommitted>>

\* An RM decides to abort on its own.
RMChooseToAbort(t, r) ==
    /\ txState[t] = "init"
    /\ lockHolder[r] = t
    /\ rmState[r] = "working"
    /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
    /\ UNCHANGED <<lockHolder, txState, txLocked, txPrepared, txPrecommitted>>

\* TX receives a prepare vote from an RM.
TXReceivePrepare(t, r) ==
    /\ txState[t] = "init"
    /\ lockHolder[r] = t
    /\ rmState[r] = "prepared"
    /\ r \notin txPrepared[t]
    /\ txPrepared' = [txPrepared EXCEPT ![t] = @ \cup {r}]
    /\ UNCHANGED <<rmState, lockHolder, txState, txLocked, txPrecommitted>>

\* ===================================================================
\* Phase 2: Pre-Commit
\* ===================================================================

\* TX decides to pre-commit once a MAJORITY of its locked RMs have prepared.
TXPreCommit(t) ==
    /\ txState[t] = "init"
    /\ IsMajority(txPrepared[t])
    /\ txState' = [txState EXCEPT ![t] = "precommitted"]
    /\ UNCHANGED <<rmState, lockHolder, txLocked, txPrepared, txPrecommitted>>

\* An RM learns the TX pre-committed and acknowledges.
RMRcvPreCommitMsg(t, r) ==
    /\ txState[t] = "precommitted"
    /\ lockHolder[r] = t
    /\ rmState[r] = "prepared"
    /\ rmState' = [rmState EXCEPT ![r] = "precommitted"]
    /\ UNCHANGED <<lockHolder, txState, txLocked, txPrepared, txPrecommitted>>

\* TX receives a pre-commit acknowledgment from an RM.
TXReceivePreCommit(t, r) ==
    /\ txState[t] = "precommitted"
    /\ lockHolder[r] = t
    /\ rmState[r] = "precommitted"
    /\ r \notin txPrecommitted[t]
    /\ txPrecommitted' = [txPrecommitted EXCEPT ![t] = @ \cup {r}]
    /\ UNCHANGED <<rmState, lockHolder, txState, txLocked, txPrepared>>

\* ===================================================================
\* Phase 3: Commit
\* ===================================================================

\* TX decides to commit once a MAJORITY of RMs have acknowledged pre-commit.
TXCommit(t) ==
    /\ txState[t] = "precommitted"
    /\ IsMajority(txPrecommitted[t])
    /\ txState' = [txState EXCEPT ![t] = "committed"]
    /\ UNCHANGED <<rmState, lockHolder, txLocked, txPrepared, txPrecommitted>>

\* TX can abort during init phase.
TXAbort(t) ==
    /\ txState[t] = "init"
    /\ txState' = [txState EXCEPT ![t] = "aborted"]
    /\ UNCHANGED <<rmState, lockHolder, txLocked, txPrepared, txPrecommitted>>

\* TX aborts from precommitted if quorum is impossible.
TXTimeoutAbort(t) ==
    /\ txState[t] = "precommitted"
    /\ LET potential == {r \in RM : lockHolder[r] = t /\ rmState[r] \in {"prepared", "precommitted"}}
       IN ~IsMajority(txPrecommitted[t] \cup potential)
    /\ txState' = [txState EXCEPT ![t] = "aborted"]
    /\ UNCHANGED <<rmState, lockHolder, txLocked, txPrepared, txPrecommitted>>

\* ===================================================================
\* RMs learn final decision
\* ===================================================================

\* Only precommitted RMs receive the commit message directly.
RMRcvCommitMsg(t, r) ==
    /\ txState[t] = "committed"
    /\ lockHolder[r] = t
    /\ rmState[r] = "precommitted"
    /\ rmState' = [rmState EXCEPT ![r] = "committed"]
    /\ UNCHANGED <<lockHolder, txState, txLocked, txPrepared, txPrecommitted>>

\* An RM learns the TX aborted and aborts.
RMRcvAbortMsg(t, r) ==
    /\ txState[t] = "aborted"
    /\ lockHolder[r] = t
    /\ rmState[r] \notin {"committed", "aborted", "failed"}
    /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
    /\ UNCHANGED <<lockHolder, txState, txLocked, txPrepared, txPrecommitted>>

\* ===================================================================
\* Lock Release (after TX completes)
\* ===================================================================

\* TX releases lock on RM after transaction completes (commit or abort).
\* RM state resets to "working" for next transaction.
TXReleaseLock(t, r) ==
    /\ txState[t] \in {"committed", "aborted"}
    /\ lockHolder[r] = t
    /\ lockHolder' = [lockHolder EXCEPT ![r] = "none"]
    /\ rmState' = [rmState EXCEPT ![r] = "working"]  \* Reset for next TX
    /\ UNCHANGED <<txState, txLocked, txPrepared, txPrecommitted>>

\* ===================================================================
\* Repair process
\* ===================================================================

\* After the TX commits, a background process eventually repairs any
\* RM that isn't committed yet.
RepairRM(t, r) ==
    /\ txState[t] = "committed"
    /\ lockHolder[r] = t
    /\ rmState[r] # "committed"
    /\ rmState' = [rmState EXCEPT ![r] = "committed"]
    /\ UNCHANGED <<lockHolder, txState, txLocked, txPrepared, txPrecommitted>>

\* ===================================================================
\* Next-state relation
\* ===================================================================

Next ==
    \* Lock acquisition phase
    \/ \E t \in TX, r \in RM : TXAcquireLock(t, r)
    \/ \E t \in TX : TXFirstRMBusy(t)
    \/ \E t \in TX, r \in RM : TXLaterRMBusy(t, r)
    \/ \E t \in TX : TXFinishAcquiring(t)
    \/ \E t \in TX : TXQuorumImpossible(t)
    \* 3PC protocol (per TX)
    \/ \E t \in TX : TXPreCommit(t)
    \/ \E t \in TX : TXCommit(t)
    \/ \E t \in TX : TXAbort(t)
    \/ \E t \in TX : TXTimeoutAbort(t)
    \/ \E t \in TX, r \in RM :
        \/ RMPrepare(t, r)
        \/ RMChooseToAbort(t, r)
        \/ TXReceivePrepare(t, r)
        \/ RMRcvPreCommitMsg(t, r)
        \/ TXReceivePreCommit(t, r)
        \/ RMRcvCommitMsg(t, r)
        \/ RMRcvAbortMsg(t, r)
        \/ TXReleaseLock(t, r)
        \/ RepairRM(t, r)
    \* RM failures (independent of TX)
    \/ \E r \in RM : RMFail(r)

\* ===================================================================
\* Specification
\* ===================================================================

Spec == Init /\ [][Next]_vars

\* FairSpec adds weak fairness — needed for liveness
FairSpec == Spec /\ WF_vars(Next)

\* ===================================================================
\* Safety properties
\* ===================================================================

\* Mutual exclusion: No two TXs hold the same lock simultaneously.
\* This should ALWAYS hold (it's enforced by the lock acquisition logic).
MutualExclusion ==
    \A r \in RM : \A t1, t2 \in TX :
        (lockHolder[r] = t1 /\ lockHolder[r] = t2) => t1 = t2

\* No two committed TXs (different transactions both committed).
\* This is an interesting property — can two TXs both commit?
\* With proper locking, only one TX should be able to proceed at a time
\* on overlapping RMs.
AtMostOneCommittedTX ==
    \A t1, t2 \in TX :
        (txState[t1] = "committed" /\ txState[t2] = "committed") => t1 = t2

\* ===================================================================
\* Liveness properties (require FairSpec)
\* ===================================================================

\* Eventually, all transactions complete (either committed or aborted).
AllTXsComplete ==
    <>(\A t \in TX : txState[t] \in {"committed", "aborted"})

\* Eventually, all locks are released (no deadlock).
AllLocksReleased ==
    <>(\A r \in RM : lockHolder[r] = "none")

====
\*
\* New concepts in this version:
\*
\*   Multiple transactions (TX constant):
\*     - Each TX has its own state machine
\*     - TXs compete for locks on RMs
\*
\*   Lock acquisition:
\*     - TXAcquireLock(t, r)  — TX t acquires lock on RM r
\*     - TXFirstRMBusy(t)     — First RM busy → abort ("losing race")
\*     - TXLaterRMBusy(t, r)  — Later RM busy → skip it
\*     - TXFinishAcquiring(t) — Done acquiring, have quorum → proceed
\*     - TXQuorumImpossible(t) — Can't get quorum → abort
\*
\*   Lock release:
\*     - TXReleaseLock(t, r)  — Release lock after TX completes
\*     - RMFail releases lock (connection drops)
\*
\*   Deterministic ordering:
\*     - RMOrder constant defines lock acquisition order
\*     - FirstRM, RMIndex, RMsBefore, NextRMToLock helpers
\*
\*   Safety properties:
\*     - MutualExclusion     — No two TXs hold same lock
\*     - AtMostOneCommittedTX — At most one TX commits
\*
\*   Liveness properties:
\*     - AllTXsComplete      — All TXs eventually finish
\*     - AllLocksReleased    — No deadlock (all locks freed)
\*
\*   New syntax:
\*   ┌─────────────────────────────┬───────────────────────────────────────────┐
\*   │ CONSTANT TX                 │ Set of transaction identifiers            │
\*   │ [TX -> SUBSET RM]           │ Function from TX to sets of RMs           │
\*   │ TX \cup {"none"}            │ Union of set with literal                 │
\*   │ CHOOSE r \in S : P(r)       │ Pick an element satisfying predicate      │
\*   │ Len(seq)                    │ Length of a sequence                      │
\*   │ seq[i]                      │ i-th element of sequence (1-based)        │
\*   │ {expr : i \in 1..n}         │ Set comprehension with range              │
\*   └─────────────────────────────┴───────────────────────────────────────────┘
\*
