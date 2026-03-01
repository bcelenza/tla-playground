---- MODULE TwoPhaseCommit ----
\*
\* Two-Phase Commit (2PC) Protocol
\*
\* A coordinator asks a set of resource managers (RMs) to agree on
\* committing or aborting a transaction. The protocol has two phases:
\*
\*   Phase 1 (Prepare): Coordinator asks each RM to vote Yes or No
\*   Phase 2 (Decide):  If ALL voted Yes → commit. If ANY voted No → abort.
\*
\* We'll verify that:
\*   - No two RMs reach different decisions (one commits, another aborts)
\*   - If all RMs are willing to commit, the transaction commits
\*

EXTENDS FiniteSets

\* --- Constants ---
CONSTANT RM  \* The set of resource managers, e.g. {"rm1", "rm2", "rm3"}

\* --- Variables ---
VARIABLES
    rmState,   \* Function: rmState[r] \in {"working", "prepared", "committed", "aborted"}
    tmState,   \* Transaction manager state: "init", "committed", "aborted"
    tmPrepared \* Set of RMs that the TM has received "prepared" votes from

vars == <<rmState, tmState, tmPrepared>>

\* ===================================================================
\* Type invariant — are all variables well-formed?
\* ===================================================================

TypeOK ==
    /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
    /\ tmState \in {"init", "committed", "aborted"}
    /\ tmPrepared \subseteq RM

\* ===================================================================
\* Initial state — everyone starts fresh
\* ===================================================================

Init ==
    /\ rmState    = [r \in RM |-> "working"]  \* All RMs are working
    /\ tmState    = "init"                     \* TM hasn't decided yet
    /\ tmPrepared = {}                         \* No prepare votes received

\* ===================================================================
\* Actions — what can happen in the system
\* ===================================================================

\* --- Phase 1: An RM votes to prepare (says "yes, I can commit") ---
RMPrepare(r) ==
    /\ rmState[r] = "working"
    /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
    /\ UNCHANGED <<tmState, tmPrepared>>

\* --- Phase 1: An RM decides to abort on its own (says "no") ---
\* An RM can spontaneously abort if it hasn't committed yet.
RMChooseToAbort(r) ==
    /\ rmState[r] = "working"
    /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
    /\ UNCHANGED <<tmState, tmPrepared>>

\* --- TM receives a prepare vote from an RM ---
TMReceivePrepare(r) ==
    /\ tmState = "init"
    /\ rmState[r] = "prepared"
    /\ tmPrepared' = tmPrepared \union {r}
    /\ UNCHANGED <<rmState, tmState>>

\* --- Phase 2: TM decides to commit (all RMs prepared) ---
TMCommit ==
    /\ tmState = "init"
    /\ tmPrepared = RM         \* Every RM has voted "prepared"
    /\ tmState' = "committed"
    /\ UNCHANGED <<rmState, tmPrepared>>

\* --- Phase 2: TM decides to abort ---
TMAbort ==
    /\ tmState = "init"
    /\ tmState' = "aborted"
    /\ UNCHANGED <<rmState, tmPrepared>>

\* --- An RM learns the TM committed and commits ---
RMRcvCommitMsg(r) ==
    /\ tmState = "committed"
    /\ rmState' = [rmState EXCEPT ![r] = "committed"]
    /\ UNCHANGED <<tmState, tmPrepared>>

\* --- An RM learns the TM aborted and aborts ---
RMRcvAbortMsg(r) ==
    /\ tmState = "aborted"
    /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
    /\ UNCHANGED <<tmState, tmPrepared>>

\* ===================================================================
\* Next-state relation — any of the above can happen
\* ===================================================================

Next ==
    \/ TMCommit
    \/ TMAbort
    \/ \E r \in RM :  \* "there exists some RM r such that..."
        \/ RMPrepare(r)
        \/ RMChooseToAbort(r)
        \/ TMReceivePrepare(r)
        \/ RMRcvCommitMsg(r)
        \/ RMRcvAbortMsg(r)

\* ===================================================================
\* Specification
\* ===================================================================

Spec == Init /\ [][Next]_vars

\* ===================================================================
\* Safety properties — things that must NEVER go wrong
\* ===================================================================

\* THE key property: no RM commits while another aborts
Consistency ==
    \A r1, r2 \in RM :
        ~ (rmState[r1] = "committed" /\ rmState[r2] = "aborted")

====
\*
\* New syntax introduced in this spec:
\*
\*   [RM -> {...}]          A function mapping each RM to a value in the set.
\*                          Like a dictionary/map: rmState["rm1"] = "working"
\*
\*   [rmState EXCEPT ![r] = "prepared"]
\*                          "rmState, but with rmState[r] changed to prepared"
\*                          Like immutable update: {...rmState, [r]: "prepared"}
\*
\*   \E r \in RM : P        "there exists some r in RM such that P is true"
\*                          TLC will try every possible r.
\*
\*   \A r1, r2 \in RM : P   "for all r1, r2 in RM, P is true"
\*
\*   \union                  Set union. {1,2} \union {2,3} = {1,2,3}
\*
\*   \subseteq              Subset. tmPrepared \subseteq RM
\*
\*   ~ P                    "not P" (negation)
\*
