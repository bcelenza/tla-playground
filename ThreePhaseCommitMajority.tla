---- MODULE ThreePhaseCommitMajority ----
\*
\* Majority-Quorum Three-Phase Commit
\*
\* A variant of Three-Phase Commit where the coordinator proceeds with
\* a majority quorum instead of requiring unanimous agreement.  RMs that
\* didn't participate are eventually "repaired" to reach consistency.
\*
\*   Phase 1 (Prepare):    Coordinator asks each RM to vote Yes or No
\*   Phase 2 (Pre-Commit): If MAJORITY voted Yes → coordinator sends pre-commit
\*   Phase 3 (Commit):     After majority acknowledge pre-commit → commit
\*   Repair:               A background process brings minority RMs to committed
\*
\* Compare with ThreePhaseCommit.tla — same structure, but quorum-based.
\*

EXTENDS FiniteSets, Naturals

\* --- Constants ---
CONSTANT RM  \* The set of resource managers, e.g. {"rm1", "rm2", "rm3"}

\* --- Variables ---
VARIABLES
    rmState,        \* Function: rmState[r] \in {"working", "prepared", "precommitted", "committed", "aborted", "failed"}
    tmState,        \* Transaction manager state: "init", "precommitted", "committed", "aborted"
    tmPrepared,     \* Set of RMs the TM has received "prepared" votes from
    tmPrecommitted  \* Set of RMs the TM has received "precommit ack" from

vars == <<rmState, tmState, tmPrepared, tmPrecommitted>>

\* ===================================================================
\* Helper: majority quorum (NEW — replaces unanimity checks)
\* ===================================================================

\* True when S contains more than half the resource managers.
\* For 3 RMs, need 2+.  For 5 RMs, need 3+.
IsMajority(S) == Cardinality(S) * 2 > Cardinality(RM)

\* ===================================================================
\* Type invariant
\* ===================================================================

TypeOK ==
    /\ rmState \in [RM -> {"working", "prepared", "precommitted", "committed", "aborted", "failed"}]
    /\ tmState \in {"init", "precommitted", "committed", "aborted"}
    /\ tmPrepared \subseteq RM
    /\ tmPrecommitted \subseteq RM

\* ===================================================================
\* Initial state
\* ===================================================================

Init ==
    /\ rmState         = [r \in RM |-> "working"]
    /\ tmState         = "init"
    /\ tmPrepared      = {}
    /\ tmPrecommitted  = {}

\* ===================================================================
\* RM Failure (NEW)
\* ===================================================================

\* An RM can fail (crash) at any time, unless already in a terminal state.
\* Failed RMs stop participating in the protocol entirely.
RMFail(r) ==
    /\ rmState[r] \notin {"committed", "aborted", "failed"}
    /\ rmState' = [rmState EXCEPT ![r] = "failed"]
    /\ UNCHANGED <<tmState, tmPrepared, tmPrecommitted>>

\* ===================================================================
\* Phase 1: Prepare (identical to ThreePhaseCommit)
\* ===================================================================

\* An RM votes to prepare (says "yes, I can commit")
RMPrepare(r) ==
    /\ rmState[r] = "working"
    /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
    /\ UNCHANGED <<tmState, tmPrepared, tmPrecommitted>>

\* An RM decides to abort on its own
RMChooseToAbort(r) ==
    /\ rmState[r] = "working"
    /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
    /\ UNCHANGED <<tmState, tmPrepared, tmPrecommitted>>

\* TM receives a prepare vote from an RM (guard avoids no-op re-receives)
TMReceivePrepare(r) ==
    /\ tmState = "init"
    /\ rmState[r] = "prepared"
    /\ r \notin tmPrepared
    /\ tmPrepared' = tmPrepared \union {r}
    /\ UNCHANGED <<rmState, tmState, tmPrecommitted>>

\* ===================================================================
\* Phase 2: Pre-Commit (CHANGED — majority instead of all)
\* ===================================================================

\* TM decides to pre-commit once a MAJORITY of RMs have prepared.
\* In ThreePhaseCommit this required tmPrepared = RM (unanimity).
TMPreCommit ==
    /\ tmState = "init"
    /\ IsMajority(tmPrepared)      \* was: tmPrepared = RM
    /\ tmState' = "precommitted"
    /\ UNCHANGED <<rmState, tmPrepared, tmPrecommitted>>

\* An RM learns the TM pre-committed and acknowledges
RMRcvPreCommitMsg(r) ==
    /\ tmState = "precommitted"
    /\ rmState[r] = "prepared"
    /\ rmState' = [rmState EXCEPT ![r] = "precommitted"]
    /\ UNCHANGED <<tmState, tmPrepared, tmPrecommitted>>

\* TM receives a pre-commit acknowledgment from an RM
TMReceivePreCommit(r) ==
    /\ tmState = "precommitted"
    /\ rmState[r] = "precommitted"
    /\ r \notin tmPrecommitted
    /\ tmPrecommitted' = tmPrecommitted \union {r}
    /\ UNCHANGED <<rmState, tmState, tmPrepared>>

\* ===================================================================
\* Phase 3: Commit (CHANGED — majority instead of all)
\* ===================================================================

\* TM decides to commit once a MAJORITY of RMs have acknowledged pre-commit.
\* In ThreePhaseCommit this required tmPrecommitted = RM (unanimity).
TMCommit ==
    /\ tmState = "precommitted"
    /\ IsMajority(tmPrecommitted)   \* was: tmPrecommitted = RM
    /\ tmState' = "committed"
    /\ UNCHANGED <<rmState, tmPrepared, tmPrecommitted>>

\* TM can abort during init phase (same as ThreePhaseCommit)
TMAbort ==
    /\ tmState = "init"
    /\ tmState' = "aborted"
    /\ UNCHANGED <<rmState, tmPrepared, tmPrecommitted>>

\* TM aborts from precommitted if quorum is impossible.
\* This matches spokesd's errQuorumImpossible handling in quorum.go.
\*
\* "Potential" = RMs that could still send a precommit ack:
\*   - "prepared" RMs can receive precommit msg and ack
\*   - "precommitted" RMs can ack (if not already counted)
\*
\* If (already acked) ∪ (potential) < majority, commit is impossible → abort.
TMTimeoutAbort ==
    /\ tmState = "precommitted"
    /\ LET potential == {r \in RM : rmState[r] \in {"prepared", "precommitted"}}
       IN ~IsMajority(tmPrecommitted \union potential)
    /\ tmState' = "aborted"
    /\ UNCHANGED <<rmState, tmPrepared, tmPrecommitted>>

\* ===================================================================
\* RMs learn final decision
\* ===================================================================

\* Only precommitted RMs receive the commit message directly.
\* (In ThreePhaseCommit, any RM could receive this — but here the
\* minority never reached precommitted, so they can't.)
RMRcvCommitMsg(r) ==
    /\ tmState = "committed"
    /\ rmState[r] = "precommitted"
    /\ rmState' = [rmState EXCEPT ![r] = "committed"]
    /\ UNCHANGED <<tmState, tmPrepared, tmPrecommitted>>

\* An RM learns the TM aborted and aborts.
\* Handles abort from precommitted state too (after TMTimeoutAbort).
\* Only transitions RMs that aren't already in a terminal state.
RMRcvAbortMsg(r) ==
    /\ tmState = "aborted"
    /\ rmState[r] \notin {"committed", "aborted"}
    /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
    /\ UNCHANGED <<tmState, tmPrepared, tmPrecommitted>>

\* ===================================================================
\* Repair process (brings all RMs to the committed outcome)
\* ===================================================================

\* After the TM commits, a background process eventually repairs any
\* RM that isn't committed yet — including failed RMs AND RMs that
\* locally aborted before knowing the global outcome.
\*
\* This models recovery: an RM comes back online (or learns the truth)
\* and syncs with the committed outcome.  In real systems, this is the
\* "anti-entropy" or "read-repair" process.
RepairRM(r) ==
    /\ tmState = "committed"
    /\ rmState[r] # "committed"
    /\ rmState' = [rmState EXCEPT ![r] = "committed"]
    /\ UNCHANGED <<tmState, tmPrepared, tmPrecommitted>>

\* ===================================================================
\* Next-state relation
\* ===================================================================

Next ==
    \/ TMPreCommit
    \/ TMCommit
    \/ TMAbort
    \/ TMTimeoutAbort
    \/ \E r \in RM :
        \/ RMFail(r)
        \/ RMPrepare(r)
        \/ RMChooseToAbort(r)
        \/ TMReceivePrepare(r)
        \/ RMRcvPreCommitMsg(r)
        \/ TMReceivePreCommit(r)
        \/ RMRcvCommitMsg(r)
        \/ RMRcvAbortMsg(r)
        \/ RepairRM(r)

\* ===================================================================
\* Specification
\* ===================================================================

Spec == Init /\ [][Next]_vars

\* FairSpec adds weak fairness — needed for liveness (EventualConsistency)
FairSpec == Spec /\ WF_vars(Next)

\* ===================================================================
\* Safety properties
\* ===================================================================

\* STRICT Consistency (from ThreePhaseCommit) — this will BREAK!
\* With majority quorum, an RM can be "committed" while another is still
\* "aborted" (before the repair process runs).  Uncomment INVARIANT
\* Consistency in the .cfg to see TLC produce a counterexample trace.
Consistency ==
    \A r1, r2 \in RM :
        ~ (rmState[r1] = "committed" /\ rmState[r2] = "aborted")

\* ===================================================================
\* Liveness properties (require FairSpec)
\* ===================================================================

\* Eventually, all RMs reach the same final state.
\* This holds because the repair process (and abort messages) eventually
\* bring every RM into agreement.
EventualConsistency ==
    <>(\A r1, r2 \in RM :
        (rmState[r1] = "committed" /\ rmState[r2] = "committed")
        \/ (rmState[r1] = "aborted" /\ rmState[r2] = "aborted"))

====
\*
\* Differences from ThreePhaseCommit.tla:
\*
\*   New operators:
\*     IsMajority(S)       — true when |S| > |RM|/2
\*
\*   New actions:
\*     RMFail(r)           — RM crashes (stops participating)
\*     RepairRM(r)         — brings failed/minority RMs to committed
\*     TMTimeoutAbort      — TM aborts from precommit if quorum impossible
\*                           (matches spokesd errQuorumImpossible behavior)
\*
\*   New properties:
\*     EventualConsistency — all RMs eventually converge (liveness)
\*     FairSpec            — Spec with weak fairness for liveness checking
\*
\*   Changed actions:
\*     TMPreCommit         — IsMajority(tmPrepared) instead of tmPrepared = RM
\*     TMCommit            — IsMajority(tmPrecommitted) instead of tmPrecommitted = RM
\*     RMRcvCommitMsg      — only fires for precommitted RMs (voters)
\*     RMRcvAbortMsg       — guards against already-terminal RMs
\*     TMReceivePrepare    — added r \notin tmPrepared guard
\*     TMReceivePreCommit  — added r \notin tmPrecommitted guard
\*
\*   Broken invariant:
\*     Consistency         — intentionally violated; minority RMs may be aborted
\*                           while majority has committed (until repair runs)
\*
\*   New syntax summary:
\*   ┌─────────────────────────────┬───────────────────────────────────────────┐
\*   │ Cardinality(S)              │ Number of elements in finite set S       │
\*   │ Cardinality(S) * 2 > N      │ Arithmetic comparison (majority test)    │
\*   │ r \notin S                  │ r is not an element of set S             │
\*   │ x \notin {a, b, c}          │ x is not in the literal set {a, b, c}    │
\*   │ <>P                         │ "Eventually P" — liveness temporal op    │
\*   │ WF_vars(Next)               │ Weak fairness — enabled ⟹ must happen   │
\*   │ LET x == expr IN body       │ Local definition within an expression    │
\*   │ ~IsMajority(S)              │ Negation — "not a majority"              │
\*   └─────────────────────────────┴───────────────────────────────────────────┘
\*
\*
