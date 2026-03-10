# Copilot Instructions

This is a TLA+ learning repository. The user (Brian) is learning TLA+ from scratch.

## Context

- Brian is a software engineer learning formal specification with TLA+
- Using the TLA+ VS Code extension (`alygin.vscode-tlaplus`) and TLC model checker

## What we've covered

1. **Counter.tla** — First spec. Learned: variables, Init, Next, Spec, invariants (TypeOK), liveness, fairness, stuttering, deadlock detection
2. **TwoPhaseCommit.tla** — Distributed transaction protocol. Learned: functions/maps (`[RM -> {...}]`), EXCEPT syntax, existential quantifiers (`\E`), universal quantifiers (`\A`), set operations, the Consistency safety property
3. **ThreePhaseCommit.tla** — Extended 2PC with pre-commit phase. Learned: how 3PC reduces blocking vs 2PC, incremental spec design using matching naming conventions
4. **ThreePhaseCommitMajority.tla** — Custom majority-quorum 3PC variant. Learned: `Cardinality(S)` and `EXTENDS Naturals` for arithmetic, `\notin` (set non-membership), `#` (not-equal), `IsMajority` quorum operator, `RepairRM` for eventual consistency, `<>P` (temporal "eventually"), `FairSpec` with `WF_vars(Next)`, state space explosion with RM count, strict vs eventual consistency tradeoffs, `RMFail` for RM crashes, `TMTimeoutAbort` for aborting when quorum impossible (verified against spokesd implementation), `LET...IN` local definitions

## Key concepts Brian understands

- Init / Next / Spec structure (and that only these are required)
- Invariants and safety properties
- Liveness and fairness (WF)
- Stuttering steps and `[][Next]_vars`
- TLC output columns (Diameter, Found, Distinct, Queue)
- Why TLA+ uses math notation instead of programming syntax
- Real-world usage (AWS paper on DynamoDB/S3 bugs)
- Intentionally introduced a bug in 2PC to see a TLC counterexample trace
- Majority quorum vs unanimity in commit protocols
- State space as the set of all reachable states TLC explores
- Why `EXTENDS Naturals` is needed for arithmetic operators like `>`
- Weak fairness: continuously enabled actions must eventually fire

## TODOs for ThreePhaseCommitMajority.tla

- [ ] **TM failure with recovery** — Demonstrate 3PC's key advantage over 2PC (new coordinator can recover safely)
- [ ] **Explicit message passing** — Replace direct state reads with message queues (foundation for partition modeling)
- [ ] **Network partitions** — Model split-brain scenarios where some RMs can't reach TM
- [ ] **Message loss** — Model dropped messages, retransmission, timeouts
- [ ] **Byzantine failures** — Malicious/corrupted nodes sending incorrect data

## Other suggested next steps

- Spec Raft consensus protocol
- Try PlusCal (algorithm language that compiles to TLA+)

## Style preferences

- Line-by-line plain English explanations when introducing new specs
- Use consistent naming conventions across specs for easy comparison
- Show new syntax in a summary table at the end of each spec
- Never automatically commit or push changes to this repository unless instructed
- Use the existing make commands for model checking
