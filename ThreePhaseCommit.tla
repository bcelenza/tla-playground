---- MODULE ThreePhaseCommit ----
\*
\* Three-Phase Commit (3PC) Protocol
\*
\* Extends 2PC by adding a "pre-commit" phase between prepare and commit.
\* This reduces the blocking problem: if the coordinator crashes after
\* pre-commit, participants can safely commit on their own (they know
\* everyone voted yes).
\*
\*   Phase 1 (Prepare):    Coordinator asks each RM to vote Yes or No
\*   Phase 2 (Pre-Commit): If ALL voted Yes → coordinator sends pre-commit
\*   Phase 3 (Commit):     After all acknowledge pre-commit → commit
\*
\* Compare with TwoPhaseCommit.tla — same naming conventions, with the
\* new pre-commit phase inserted between prepare and commit.
\*

EXTENDS FiniteSets

\* --- Constants ---
CONSTANT RM  \* The set of resource managers, e.g. {"rm1", "rm2", "rm3"}

\* --- Variables ---
VARIABLES
    rmState,        \* Function: rmState[r] \in {"working", "prepared", "precommitted", "committed", "aborted"}
    tmState,        \* Transaction manager state: "init", "precommitted", "committed", "aborted"
    tmPrepared,     \* Set of RMs the TM has received "prepared" votes from
    tmPrecommitted  \* Set of RMs the TM has received "precommit ack" from (NEW in 3PC)

vars == <<rmState, tmState, tmPrepared, tmPrecommitted>>

\* ===================================================================
\* Type invariant
\* ===================================================================

TypeOK ==
    /\ rmState \in [RM -> {"working", "prepared", "precommitted", "committed", "aborted"}]
    /\ tmState \in {"init", "precommitted", "committed", "aborted"}
    /\ tmPrepared \subseteq RM
    /\ tmPrecommitted \subseteq RM

\* ===================================================================
\* Initial state — same as 2PC plus empty precommit set
\* ===================================================================

Init ==
    /\ rmState         = [r \in RM |-> "working"]
    /\ tmState         = "init"
    /\ tmPrepared      = {}
    /\ tmPrecommitted  = {}

\* ===================================================================
\* Phase 1: Prepare (identical to 2PC)
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

\* TM receives a prepare vote from an RM
TMReceivePrepare(r) ==
    /\ tmState = "init"
    /\ rmState[r] = "prepared"
    /\ tmPrepared' = tmPrepared \union {r}
    /\ UNCHANGED <<rmState, tmState, tmPrecommitted>>

\* ===================================================================
\* Phase 2: Pre-Commit (NEW — this is what 3PC adds)
\* ===================================================================

\* TM decides to pre-commit (all RMs prepared, just like TMCommit in 2PC,
\* but instead of jumping straight to committed, we go to precommitted)
TMPreCommit ==
    /\ tmState = "init"
    /\ tmPrepared = RM
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
    /\ tmPrecommitted' = tmPrecommitted \union {r}
    /\ UNCHANGED <<rmState, tmState, tmPrepared>>

\* ===================================================================
\* Phase 3: Commit (like 2PC, but only after pre-commit phase)
\* ===================================================================

\* TM decides to commit — all RMs have acknowledged pre-commit
TMCommit ==
    /\ tmState = "precommitted"
    /\ tmPrecommitted = RM
    /\ tmState' = "committed"
    /\ UNCHANGED <<rmState, tmPrepared, tmPrecommitted>>

\* ===================================================================
\* Abort (same as 2PC — TM can abort while in "init")
\* ===================================================================

TMAbort ==
    /\ tmState = "init"
    /\ tmState' = "aborted"
    /\ UNCHANGED <<rmState, tmPrepared, tmPrecommitted>>

\* ===================================================================
\* RMs learn final decision (same as 2PC)
\* ===================================================================

\* An RM learns the TM committed and commits
RMRcvCommitMsg(r) ==
    /\ tmState = "committed"
    /\ rmState' = [rmState EXCEPT ![r] = "committed"]
    /\ UNCHANGED <<tmState, tmPrepared, tmPrecommitted>>

\* An RM learns the TM aborted and aborts
RMRcvAbortMsg(r) ==
    /\ tmState = "aborted"
    /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
    /\ UNCHANGED <<tmState, tmPrepared, tmPrecommitted>>

\* ===================================================================
\* Next-state relation
\* ===================================================================

Next ==
    \/ TMPreCommit
    \/ TMCommit
    \/ TMAbort
    \/ \E r \in RM :
        \/ RMPrepare(r)
        \/ RMChooseToAbort(r)
        \/ TMReceivePrepare(r)
        \/ RMRcvPreCommitMsg(r)
        \/ TMReceivePreCommit(r)
        \/ RMRcvCommitMsg(r)
        \/ RMRcvAbortMsg(r)

\* ===================================================================
\* Specification
\* ===================================================================

Spec == Init /\ [][Next]_vars

\* ===================================================================
\* Safety properties
\* ===================================================================

\* Same as 2PC: no RM commits while another aborts
Consistency ==
    \A r1, r2 \in RM :
        ~ (rmState[r1] = "committed" /\ rmState[r2] = "aborted")

====
\*
\* Differences from TwoPhaseCommit.tla:
\*
\*   New variable:     tmPrecommitted   — tracks pre-commit acknowledgments
\*   New RM state:     "precommitted"   — RM has acknowledged pre-commit
\*   New TM state:     "precommitted"   — TM has entered pre-commit phase
\*
\*   New actions:
\*     TMPreCommit          — TM enters pre-commit (was TMCommit in 2PC)
\*     RMRcvPreCommitMsg(r) — RM acknowledges pre-commit
\*     TMReceivePreCommit(r)— TM records acknowledgment
\*
\*   Changed actions:
\*     TMCommit             — now requires tmState = "precommitted" and
\*                            all RMs acknowledged, instead of just all prepared
\*
