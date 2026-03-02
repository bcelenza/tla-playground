# Copilot Instructions

This is a TLA+ learning repository. The user (Brian) is learning TLA+ from scratch.

## Context

- Brian is a software engineer learning formal specification with TLA+
- Using the TLA+ VS Code extension (`alygin.vscode-tlaplus`) and TLC model checker

## What we've covered

1. **Counter.tla** — First spec. Learned: variables, Init, Next, Spec, invariants (TypeOK), liveness, fairness, stuttering, deadlock detection
2. **TwoPhaseCommit.tla** — Distributed transaction protocol. Learned: functions/maps (`[RM -> {...}]`), EXCEPT syntax, existential quantifiers (`\E`), universal quantifiers (`\A`), set operations, the Consistency safety property
3. **ThreePhaseCommit.tla** — Extended 2PC with pre-commit phase. Learned: how 3PC reduces blocking vs 2PC, incremental spec design using matching naming conventions

## Key concepts Brian understands

- Init / Next / Spec structure (and that only these are required)
- Invariants and safety properties
- Liveness and fairness (WF)
- Stuttering steps and `[][Next]_vars`
- TLC output columns (Diameter, Found, Distinct, Queue)
- Why TLA+ uses math notation instead of programming syntax
- Real-world usage (AWS paper on DynamoDB/S3 bugs)
- Intentionally introduced a bug in 2PC to see a TLC counterexample trace

## Suggested next steps

- Model coordinator failure in 3PC to demonstrate recovery advantage
- Add explicit message passing (instead of reading state directly)
- Spec Raft consensus protocol
- Try PlusCal (algorithm language that compiles to TLA+)

## Style preferences

- Line-by-line plain English explanations when introducing new specs
- Use consistent naming conventions across specs for easy comparison
- Show new syntax in a summary table at the end of each spec
