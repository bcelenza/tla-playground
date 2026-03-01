---- MODULE Counter ----
\* A simple counter that increments from 0 up to a maximum value.
\* This is a great first spec to learn the basics of TLA+.

EXTENDS Integers

CONSTANT Max  \* The maximum value the counter can reach (set in model config)

VARIABLE count

\* --- Type invariant ---
\* This should always be true: count is an integer in the range 0..Max
TypeOK == count \in 0..Max

\* --- Initial state ---
Init == count = 0

\* --- Actions ---
Increment == count < Max /\ count' = count + 1
\* --- Done state ---
Done == count = Max /\ UNCHANGED count

\* --- Next-state relation ---
\* Each step is either an Increment or a stutter (no change)
Next == Increment \/ Done

\* --- Specification ---
Spec == Init /\ [][Next]_count

\* --- Properties to check ---

\* Safety: count never exceeds Max
SafetyInvariant == count <= Max

\* Liveness: the counter eventually reaches Max
\* (requires fairness — uncomment FairSpec below to check this)
Liveness == <>(count = Max)

\* Spec with weak fairness (guarantees progress)
FairSpec == Spec /\ WF_count(Next)

====
\* To run this:
\*   1. Install the TLA+ VS Code extension (alygin.vscode-tlaplus)
\*   2. Create Counter.cfg (already provided) to configure the model
\*   3. Use Cmd/Ctrl+Shift+P → "TLA+: Check Model with TLC"
\*
\* Exercises:
\*   - Change Max to different values and re-run TLC
\*   - Add a Decrement action and see what happens to TypeOK
\*   - Add a Reset action that sets count back to 0
\*   - Try checking Liveness with Spec (no fairness) — it should fail!
\*   - Then check Liveness with FairSpec — it should pass
