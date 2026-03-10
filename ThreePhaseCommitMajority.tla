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
\* Checksum consensus:
\*   - Each RM has a checksum value representing its data state
\*   - During lock acquisition, TX collects checksums from locked RMs
\*   - Consensus checksum = value held by majority of locked RMs
\*   - RMs with non-matching checksums are "unhealthy" (excluded from voting)
\*   - Unhealthy RMs are eventually repaired to match consensus
\*
\* Compare with single-TX version — now we can verify deadlock freedom
\* and mutual exclusion with multiple competing coordinators.
\*

EXTENDS FiniteSets, Naturals

\* --- Constants ---
CONSTANT RM        \* The set of resource managers, e.g. {"rm1", "rm2", "rm3"}
CONSTANT TX        \* The set of transactions, e.g. {"tx1", "tx2"}
CONSTANT Checksum  \* The set of possible checksum values, e.g. {"cs1", "cs2"}

\* --- Variables ---
VARIABLES
    rmState,        \* Function: rmState[r] \in {"working", "prepared", "precommitted", "committed", "aborted", "failed"}
    rmChecksum,     \* Function: rmChecksum[r] \in Checksum — current checksum of RM's data
    lockHolder,     \* Function: lockHolder[r] \in TX \cup {"none"} — who holds the lock on RM r
    txState,        \* Function: txState[t] \in {"acquiring", "init", "precommitted", "committed", "aborted"}
    txLocked,       \* Function: txLocked[t] = set of RMs that TX t has locked
    txHealthy,      \* Function: txHealthy[t] = set of RMs with matching checksum (healthy voters)
    txConsensus,    \* Function: txConsensus[t] \in Checksum \cup {"none"} — consensus checksum for TX
    txPrepared,     \* Function: txPrepared[t] = set of RMs that prepared for TX t
    txPrecommitted  \* Function: txPrecommitted[t] = set of RMs that precommitted for TX t

vars == <<rmState, rmChecksum, lockHolder, txState, txLocked, txHealthy, txConsensus, txPrepared, txPrecommitted>>

\* ===================================================================
\* Helper: majority quorum
\* ===================================================================

\* True when S contains more than half the resource managers.
IsMajority(S) == Cardinality(S) * 2 > Cardinality(RM)

\* True when S contains more than half of a given set T.
IsMajorityOf(S, T) == Cardinality(S) * 2 > Cardinality(T)

\* ===================================================================
\* Helper: checksum consensus
\* ===================================================================

\* Count how many RMs in set S have a given checksum value.
ChecksumCount(S, cs) == Cardinality({r \in S : rmChecksum[r] = cs})

\* Find the consensus checksum among a set of RMs.
\* Returns the checksum held by a strict majority, or "none" if no majority.
ConsensusChecksum(S) ==
    LET validCS == {cs \in Checksum : IsMajorityOf({r \in S : rmChecksum[r] = cs}, S)}
    IN IF validCS = {} THEN "none"
       ELSE CHOOSE cs \in validCS : TRUE

\* Set of "healthy" RMs = those matching the consensus checksum.
HealthyRMs(S, consensus) ==
    IF consensus = "none" THEN {}
    ELSE {r \in S : rmChecksum[r] = consensus}

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
    /\ rmChecksum \in [RM -> Checksum]
    /\ lockHolder \in [RM -> TX \cup {"none"}]
    /\ txState \in [TX -> {"acquiring", "init", "precommitted", "committed", "aborted"}]
    /\ txLocked \in [TX -> SUBSET RM]
    /\ txHealthy \in [TX -> SUBSET RM]
    /\ txConsensus \in [TX -> Checksum \cup {"none"}]
    /\ txPrepared \in [TX -> SUBSET RM]
    /\ txPrecommitted \in [TX -> SUBSET RM]

\* ===================================================================
\* Initial state
\* ===================================================================

\* All RMs start with the same checksum (consistent state).
\* An RM could later diverge due to partial failures or bugs.
Init ==
    /\ rmState         = [r \in RM |-> "working"]
    /\ rmChecksum      = [r \in RM |-> CHOOSE cs \in Checksum : TRUE]  \* All start same
    /\ lockHolder      = [r \in RM |-> "none"]
    /\ txState         = [t \in TX |-> "acquiring"]
    /\ txLocked        = [t \in TX |-> {}]
    /\ txHealthy       = [t \in TX |-> {}]
    /\ txConsensus     = [t \in TX |-> "none"]
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
    /\ UNCHANGED <<rmState, rmChecksum, txState, txHealthy, txConsensus, txPrepared, txPrecommitted>>

\* TX t fails to acquire lock on FIRST RM (it's busy) → abort immediately.
\* This is the "losing race" optimization — if you can't get the first
\* lock, another TX is ahead of you, so back off immediately.
TXFirstRMBusy(t) ==
    /\ txState[t] = "acquiring"
    /\ txLocked[t] = {}                      \* Haven't locked anything yet
    /\ NextRMToLock(t) = FirstRM             \* Trying for first RM
    /\ lockHolder[FirstRM] \in TX \ {t}      \* Someone else holds it
    /\ txState' = [txState EXCEPT ![t] = "aborted"]
    /\ UNCHANGED <<rmState, rmChecksum, lockHolder, txLocked, txHealthy, txConsensus, txPrepared, txPrecommitted>>

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
    /\ UNCHANGED <<rmState, rmChecksum, lockHolder, txState, txHealthy, txConsensus, txPrepared, txPrecommitted>>

\* TX t has finished lock acquisition phase → transition to init.
\* Computes consensus checksum and identifies healthy RMs.
\* Requires: majority of HEALTHY RMs (those with matching checksum).
TXFinishAcquiring(t) ==
    /\ txState[t] = "acquiring"
    /\ NextRMToLock(t) = "none"              \* Tried all RMs
    /\ LET actuallyLocked == {r \in txLocked[t] : lockHolder[r] = t}
           consensus == ConsensusChecksum(actuallyLocked)
           healthy == HealthyRMs(actuallyLocked, consensus)
       IN /\ consensus # "none"               \* Must have checksum consensus
          /\ IsMajority(healthy)              \* Healthy RMs form a majority
          /\ txConsensus' = [txConsensus EXCEPT ![t] = consensus]
          /\ txHealthy' = [txHealthy EXCEPT ![t] = healthy]
    /\ txState' = [txState EXCEPT ![t] = "init"]
    /\ UNCHANGED <<rmState, rmChecksum, lockHolder, txLocked, txPrepared, txPrecommitted>>

\* TX t cannot achieve quorum of healthy RMs → abort.
\* This can happen if:
\*   - Not enough locks acquired, OR
\*   - No checksum consensus among locked RMs, OR
\*   - Healthy RMs don't form a majority
TXQuorumImpossible(t) ==
    /\ txState[t] = "acquiring"
    /\ NextRMToLock(t) = "none"              \* Tried all RMs
    /\ LET actuallyLocked == {r \in txLocked[t] : lockHolder[r] = t}
           consensus == ConsensusChecksum(actuallyLocked)
           healthy == HealthyRMs(actuallyLocked, consensus)
       IN \/ consensus = "none"               \* No checksum consensus
          \/ ~IsMajority(healthy)             \* Not enough healthy RMs
    /\ txState' = [txState EXCEPT ![t] = "aborted"]
    /\ UNCHANGED <<rmState, rmChecksum, lockHolder, txLocked, txHealthy, txConsensus, txPrepared, txPrecommitted>>

\* ===================================================================
\* RM Failure and Checksum Divergence
\* ===================================================================

\* An RM can fail (crash) at any time, unless already in a terminal state.
\* Failed RMs stop participating in the protocol entirely.
\* Lock is released when RM fails (connection drops).
RMFail(r) ==
    /\ rmState[r] \notin {"committed", "aborted", "failed"}
    /\ rmState' = [rmState EXCEPT ![r] = "failed"]
    /\ lockHolder' = [lockHolder EXCEPT ![r] = "none"]  \* Lock released on failure
    /\ UNCHANGED <<rmChecksum, txState, txLocked, txHealthy, txConsensus, txPrepared, txPrecommitted>>

\* An RM's checksum diverges from others (models data corruption or partial update).
\* This can only happen to RMs not currently locked (between transactions).
\* This is how we introduce "unhealthy" replicas for testing.
RMChecksumDiverge(r, cs) ==
    /\ lockHolder[r] = "none"                \* Not locked
    /\ rmState[r] = "working"                \* In normal state
    /\ cs # rmChecksum[r]                    \* Changing to different checksum
    /\ rmChecksum' = [rmChecksum EXCEPT ![r] = cs]
    /\ UNCHANGED <<rmState, lockHolder, txState, txLocked, txHealthy, txConsensus, txPrepared, txPrecommitted>>

\* ===================================================================
\* Phase 1: Prepare
\* ===================================================================

\* An RM votes to prepare (says "yes, I can commit").
\* Only HEALTHY RMs (matching consensus checksum) can vote.
RMPrepare(t, r) ==
    /\ txState[t] = "init"
    /\ lockHolder[r] = t
    /\ r \in txHealthy[t]                    \* Must be healthy to vote
    /\ rmState[r] = "working"
    /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
    /\ UNCHANGED <<rmChecksum, lockHolder, txState, txLocked, txHealthy, txConsensus, txPrepared, txPrecommitted>>

\* An RM decides to abort on its own.
RMChooseToAbort(t, r) ==
    /\ txState[t] = "init"
    /\ lockHolder[r] = t
    /\ r \in txHealthy[t]                    \* Must be healthy to vote
    /\ rmState[r] = "working"
    /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
    /\ UNCHANGED <<rmChecksum, lockHolder, txState, txLocked, txHealthy, txConsensus, txPrepared, txPrecommitted>>

\* TX receives a prepare vote from an RM.
TXReceivePrepare(t, r) ==
    /\ txState[t] = "init"
    /\ lockHolder[r] = t
    /\ rmState[r] = "prepared"
    /\ r \notin txPrepared[t]
    /\ txPrepared' = [txPrepared EXCEPT ![t] = @ \cup {r}]
    /\ UNCHANGED <<rmState, rmChecksum, lockHolder, txState, txLocked, txHealthy, txConsensus, txPrecommitted>>

\* ===================================================================
\* Phase 2: Pre-Commit
\* ===================================================================

\* TX decides to pre-commit once a MAJORITY of HEALTHY RMs have prepared.
TXPreCommit(t) ==
    /\ txState[t] = "init"
    /\ IsMajority(txPrepared[t] \cap txHealthy[t])  \* Majority of healthy RMs
    /\ txState' = [txState EXCEPT ![t] = "precommitted"]
    /\ UNCHANGED <<rmState, rmChecksum, lockHolder, txLocked, txHealthy, txConsensus, txPrepared, txPrecommitted>>

\* An RM learns the TX pre-committed and acknowledges.
RMRcvPreCommitMsg(t, r) ==
    /\ txState[t] = "precommitted"
    /\ lockHolder[r] = t
    /\ r \in txHealthy[t]                    \* Must be healthy
    /\ rmState[r] = "prepared"
    /\ rmState' = [rmState EXCEPT ![r] = "precommitted"]
    /\ UNCHANGED <<rmChecksum, lockHolder, txState, txLocked, txHealthy, txConsensus, txPrepared, txPrecommitted>>

\* TX receives a pre-commit acknowledgment from an RM.
TXReceivePreCommit(t, r) ==
    /\ txState[t] = "precommitted"
    /\ lockHolder[r] = t
    /\ rmState[r] = "precommitted"
    /\ r \notin txPrecommitted[t]
    /\ txPrecommitted' = [txPrecommitted EXCEPT ![t] = @ \cup {r}]
    /\ UNCHANGED <<rmState, rmChecksum, lockHolder, txState, txLocked, txHealthy, txConsensus, txPrepared>>

\* ===================================================================
\* Phase 3: Commit
\* ===================================================================

\* TX decides to commit once a MAJORITY of HEALTHY RMs have acknowledged pre-commit.
TXCommit(t) ==
    /\ txState[t] = "precommitted"
    /\ IsMajority(txPrecommitted[t] \cap txHealthy[t])  \* Majority of healthy
    /\ txState' = [txState EXCEPT ![t] = "committed"]
    /\ UNCHANGED <<rmState, rmChecksum, lockHolder, txLocked, txHealthy, txConsensus, txPrepared, txPrecommitted>>

\* TX can abort during init phase.
TXAbort(t) ==
    /\ txState[t] = "init"
    /\ txState' = [txState EXCEPT ![t] = "aborted"]
    /\ UNCHANGED <<rmState, rmChecksum, lockHolder, txLocked, txHealthy, txConsensus, txPrepared, txPrecommitted>>

\* TX aborts from precommitted if quorum of healthy RMs is impossible.
TXTimeoutAbort(t) ==
    /\ txState[t] = "precommitted"
    /\ LET potential == {r \in txHealthy[t] : lockHolder[r] = t /\ rmState[r] \in {"prepared", "precommitted"}}
       IN ~IsMajority(txPrecommitted[t] \cup potential)
    /\ txState' = [txState EXCEPT ![t] = "aborted"]
    /\ UNCHANGED <<rmState, rmChecksum, lockHolder, txLocked, txHealthy, txConsensus, txPrepared, txPrecommitted>>

\* ===================================================================
\* RMs learn final decision
\* ===================================================================

\* Only precommitted RMs receive the commit message directly.
RMRcvCommitMsg(t, r) ==
    /\ txState[t] = "committed"
    /\ lockHolder[r] = t
    /\ rmState[r] = "precommitted"
    /\ rmState' = [rmState EXCEPT ![r] = "committed"]
    /\ UNCHANGED <<rmChecksum, lockHolder, txState, txLocked, txHealthy, txConsensus, txPrepared, txPrecommitted>>

\* An RM learns the TX aborted and aborts.
RMRcvAbortMsg(t, r) ==
    /\ txState[t] = "aborted"
    /\ lockHolder[r] = t
    /\ rmState[r] \notin {"committed", "aborted", "failed"}
    /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
    /\ UNCHANGED <<rmChecksum, lockHolder, txState, txLocked, txHealthy, txConsensus, txPrepared, txPrecommitted>>

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
    /\ UNCHANGED <<rmChecksum, txState, txLocked, txHealthy, txConsensus, txPrepared, txPrecommitted>>

\* ===================================================================
\* Repair process
\* ===================================================================

\* After the TX commits, a background process eventually repairs any
\* RM that isn't committed yet (brings state to committed).
RepairRMState(t, r) ==
    /\ txState[t] = "committed"
    /\ lockHolder[r] = t
    /\ rmState[r] # "committed"
    /\ rmState' = [rmState EXCEPT ![r] = "committed"]
    /\ UNCHANGED <<rmChecksum, lockHolder, txState, txLocked, txHealthy, txConsensus, txPrepared, txPrecommitted>>

\* After the TX commits, a background process repairs unhealthy RMs
\* by updating their checksum to match the consensus.
RepairRMChecksum(t, r) ==
    /\ txState[t] = "committed"
    /\ lockHolder[r] = t
    /\ r \notin txHealthy[t]                 \* Was unhealthy (divergent checksum)
    /\ rmChecksum[r] # txConsensus[t]        \* Checksum still differs
    /\ rmChecksum' = [rmChecksum EXCEPT ![r] = txConsensus[t]]
    /\ UNCHANGED <<rmState, lockHolder, txState, txLocked, txHealthy, txConsensus, txPrepared, txPrecommitted>>

\* ===================================================================
\* Next-state relation
\* ===================================================================

\* Protocol actions — these are the "real" protocol steps
\* that we want to be fair (eventually execute when enabled)
ProtocolNext ==
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
        \/ RepairRMState(t, r)
        \/ RepairRMChecksum(t, r)

\* Environmental/adversarial actions — failures and divergence
\* These should NOT be fair (they model "bad things that might happen")
EnvNext ==
    \/ \E r \in RM : RMFail(r)
    \/ \E r \in RM, cs \in Checksum : RMChecksumDiverge(r, cs)

Next == ProtocolNext \/ EnvNext

\* ===================================================================
\* Specification
\* ===================================================================

Spec == Init /\ [][Next]_vars

\* FairSpec adds weak fairness to PROTOCOL actions only.
\* Environmental actions (failures, divergence) are NOT fair —
\* they model adversarial behavior that may or may not happen.
FairSpec == Spec /\ WF_vars(ProtocolNext)

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

\* Checksum integrity: While a TX holds locks, all healthy RMs
\* that participated should have matching checksums (the consensus).
\* Note: Once locks are released, RMs may diverge (a subsequent TX
\* will detect and handle it).
ChecksumConsistency ==
    \A t \in TX :
        txState[t] \in {"init", "precommitted", "committed"} =>
            \A r \in txHealthy[t] :
                lockHolder[r] = t => rmChecksum[r] = txConsensus[t]

\* ===================================================================
\* Liveness properties (require FairSpec)
\* ===================================================================

\* Eventually, all transactions complete (either committed or aborted).
AllTXsComplete ==
    <>(\A t \in TX : txState[t] \in {"committed", "aborted"})

\* Eventually, all locks are released (no deadlock).
AllLocksReleased ==
    <>(\A r \in RM : lockHolder[r] = "none")

\* Eventually, all unhealthy RMs are repaired (checksums converge).
\* This requires FairSpec so that RepairRMChecksum eventually fires.
AllChecksumsConverge ==
    <>(\A t \in TX : txState[t] = "committed" =>
        \A r \in RM : lockHolder[r] = t => rmChecksum[r] = txConsensus[t])

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
\*   Checksum consensus:
\*     - rmChecksum[r]        — Each RM has a checksum value
\*     - txConsensus[t]       — Consensus checksum determined during lock phase
\*     - txHealthy[t]         — RMs matching consensus (can vote)
\*     - ConsensusChecksum(S) — Find majority checksum in a set of RMs
\*     - HealthyRMs(S, cs)    — RMs in S with checksum cs
\*     - RMChecksumDiverge(r) — RM's checksum changes (models corruption)
\*     - RepairRMChecksum     — Fix divergent RM's checksum
\*
\*   Safety properties:
\*     - MutualExclusion      — No two TXs hold same lock
\*     - AtMostOneCommittedTX — At most one TX commits
\*     - ChecksumConsistency  — Healthy RMs have matching checksums
\*
\*   Liveness properties:
\*     - AllTXsComplete       — All TXs eventually finish
\*     - AllLocksReleased     — No deadlock (all locks freed)
\*     - AllChecksumsConverge — Unhealthy RMs eventually repaired
\*
\*   New syntax:
\*   ┌─────────────────────────────┬───────────────────────────────────────────┐
\*   │ CONSTANT TX                 │ Set of transaction identifiers            │
\*   │ CONSTANT Checksum           │ Set of possible checksum values           │
\*   │ [TX -> SUBSET RM]           │ Function from TX to sets of RMs           │
\*   │ TX \cup {"none"}            │ Union of set with literal                 │
\*   │ CHOOSE r \in S : P(r)       │ Pick an element satisfying predicate      │
\*   │ Len(seq)                    │ Length of a sequence                      │
\*   │ seq[i]                      │ i-th element of sequence (1-based)        │
\*   │ {expr : i \in 1..n}         │ Set comprehension with range              │
\*   └─────────────────────────────┴───────────────────────────────────────────┘
\*
