# TLA+ Playground

A learning repository for TLA+ formal specifications.

## Setup

1. Install the [TLA+ VS Code extension](https://marketplace.visualstudio.com/items?itemName=alygin.vscode-tlaplus)
2. Install Java (JDK 11+) — required by the TLC model checker
3. Download `tla2tools.jar` to `~/lib/`:
   ```bash
   mkdir -p ~/lib
   curl -L -o ~/lib/tla2tools.jar \
     https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar
   ```

## Running

### From VS Code

- Open a `.tla` file
- `Ctrl+Shift+P` → **TLA+: Check Model with TLC**

### From Command Line

```bash
make check MODEL=Counter              # Check a specific model
make check-all                        # Check all models
make list                             # List available models
make clean                            # Remove generated files
```

To override the jar location:
```bash
make check MODEL=Counter TLA2TOOLS=/path/to/tla2tools.jar
```

## Specs

| Spec | Description |
|------|-------------|
| `Counter` | Simple counter — intro to Init, Next, Spec, invariants |
| `TwoPhaseCommit` | 2PC distributed transaction protocol |
| `ThreePhaseCommit` | 3PC with pre-commit phase |
| `ThreePhaseCommitMajority` | Majority-quorum 3PC with concurrent transactions and locking |

## Learning Path

1. Read through each TLA file and understand each section
2. Run TLC and observe the output
3. Try the exercises in the comments
4. Create your own specs!
