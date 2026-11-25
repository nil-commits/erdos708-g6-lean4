# Erdős Problem #708 (`g(5) = 6`, `g(6) = 8`, and `g(1)..g(6)`) in Pure-Mathlib Lean 4

An unconditional, pure-Mathlib Lean 4 (`v4.33.1`) formalization settling **Erdős Problem #708** for $n = 5$ ($g(5) = 6$) and $n = 6$ ($g(6) = 8$), together with exact values $g(1), \dots, g(6)$, verified end-to-end with `0 sorry`, `0` custom axioms, and `leanchecker PASS`.

## Problem Statement

For $n \ge 1$, **Erdős Problem #708** (Erdős–Surányi 1959) defines $g(n)$ as the minimal integer $k$ such that for **every** set $A \subset \{2, 3, \dots\}$ with $|A| = n$, letting $M = \max(A)$, and **every** interval $I = \{x + 1, x + 2, \dots, x + M\}$ of $M$ consecutive positive integers, there exists a subset $B \subseteq I$ with $|B| \le k$ such that

$$\prod_{a \in A} a \;\Big|\; \prod_{b \in B} b.$$

Erdős asked whether $g(n) \le (2 + o(1))n$ (or even $g(n) \le 2n$).

## Exact Values Proved (`Erdos708.Main.erdos708_exact_one_through_six`)

| $n$ | Exact $g(n)$ | Upper bound | Lower bound witness | Module |
|---:|---:|---|---|---|
| $1$ | $1$ | `erdos708_exact_one` | $\{2\}$ on $[1, 2]$ | `Erdos708/Lower.lean` |
| $2$ | $2$ | `erdos708_exact_two` | trivial | `Erdos708/Lower.lean` |
| $3$ | $4$ | `erdos708_exact_three` | $\{77, 91, 143\}$ + CRT | `Erdos708/Lower.lean`, `Erdos708/G3AndG6Lower.lean` |
| $4$ | $5$ | `erdos708_exact_four` | $\{77, 91, 139, 143\}$ + CRT | `Erdos708/Lower.lean`, `Erdos708/G4.lean` |
| **$5$** | **$6$** | **`erdos708_exact_five`** | Split-clique $P = \{17, 19\}, Q = \{23\}$ | `Erdos708/Lower.lean`, `Erdos708/G5.lean` |
| **$6$** | **$8$** | **`erdos708_exact_six`** | $K_{3,2}$ set $\{23, 29, 31\} \times \{37, 41\}$ ($M = 1271$) + CRT | `Erdos708/G3AndG6Lower.lean`, `Erdos708/G6FromG5.lean`, `Erdos708/Main.lean` |

## Honest Scope & Literature Context

- **Literature status:** Earlier work (`hexagon:2611.00694v1`) settled $g(4) = 5$ and $g(5) = 6$, while $g(6) \ge 8$ and the general conjecture $g(n) \le 2n$ / $(2 + o(1))n$ remained open.
- **What this repository establishes:** Complete machine-checked Lean 4 proofs of $g(1) = 1, g(2) = 2, g(3) = 4, g(4) = 5, g(5) = 6$, and **$g(6) = 8$**, packaged unconditionally in `Erdos708.erdos708_exact_one_through_six`, plus the structural semiprime barrier `Erdos708.exists_cover_le_two_mul_of_semiprimes` showing any set of primes and semiprimes has a cover of size $\le 2n$.
- **What remains open:** $g(n)$ for $n \ge 7$ and the general conjecture $g(n) \le 2n$ (or $(2 + o(1))n$).

## Verbatim Lean 4 Definitions & Theorem Signatures

Core definitions from `Erdos708/Lower.lean` (`namespace Erdos708`):

```lean
/-- Interval of `M` consecutive positive integers `{x + 1, x + 2, ..., x + M}`. -/
def consecInterval (x M : ℕ) : Finset ℕ :=
  Finset.Icc (x + 1) (x + M)

/-- `A` is a valid `n`-element subset of `[2, ∞) ∩ ℕ`. -/
def IsValidSet (A : Finset ℕ) (n : ℕ) : Prop :=
  A.card = n ∧ ∀ a ∈ A, 2 ≤ a

/-- `B` covers `A` iff `∏ a ∈ A, a ∣ ∏ b ∈ B, b`. -/
def IsCover (A B : Finset ℕ) : Prop :=
  (∏ a ∈ A, a) ∣ (∏ b ∈ B, b)

/-- `SatisfiesBound n k` means `g(n) ≤ k`: for every valid `n`-element set `A` and every
interval `I` of `max(A)` consecutive positive integers, some `B ⊆ I` of size `≤ k` covers `A`. -/
def SatisfiesBound (n k : ℕ) : Prop :=
  ∀ (A : Finset ℕ) (hA : A.Nonempty), IsValidSet A n →
    ∀ x : ℕ, ∃ B ⊆ consecInterval x (A.max' hA), B.card ≤ k ∧ IsCover A B
```

Main headline theorems (`Erdos708/G5.lean` and `Erdos708/Main.lean`):

```lean
theorem erdos708_upper_five : SatisfiesBound 5 6

theorem erdos708_exact_five : SatisfiesBound 5 6 ∧ ¬ SatisfiesBound 5 5

theorem erdos708_upper_six : SatisfiesBound 6 8

theorem erdos708_exact_six : SatisfiesBound 6 8 ∧ ¬ SatisfiesBound 6 7

theorem erdos708_exact_one_through_six :
    (SatisfiesBound 1 1 ∧ ¬ SatisfiesBound 1 0) ∧
    (SatisfiesBound 2 2 ∧ ¬ SatisfiesBound 2 1) ∧
    (SatisfiesBound 3 4 ∧ ¬ SatisfiesBound 3 3) ∧
    (SatisfiesBound 4 5 ∧ ¬ SatisfiesBound 4 4) ∧
    (SatisfiesBound 5 6 ∧ ¬ SatisfiesBound 5 5) ∧
    (SatisfiesBound 6 8 ∧ ¬ SatisfiesBound 6 7)
```

## Proof Architecture (High-Level)

See [`docs/HOW_WE_SOLVED_IT.md`](docs/HOW_WE_SOLVED_IT.md) for the full mathematical story—including two explicit $r = 1$ counterexamples that broke separate-prime $p$-adic remainder compression before formalization.

1. **Lower bound $g(6) \ge 8$ (`Erdos708/G3AndG6Lower.lean`):**
   Using the $K_{3,2}$ witness $A_6 = \{23, 29, 31\} \times \{37, 41\} = \{851, 943, 1073, 1147, 1189, 1271\}$ ($M = 1271$) and CRT modulo $\{23^2, 29^2, 31^2, 37^2, 41^2\}$, every pairwise product $p_i p_j \ge 23 \cdot 29 = 667 > M/2 = 635.5$, blocking merges and forcing $|B| \ge 8$.
2. **Reduction $g(5) \le 6 \implies g(6) \le 8$ (`Erdos708/G6FromG5.lean`):**
   By strong induction on $M$ and GCD reduction (`erdos708_gcd_reduction`) to $\gcd(A) = 1$, dropping $M$ reduces $A \setminus \{M\}$ to $6$ slots via `SatisfiesBound 5 6` with residual $R \mid M$. Generalized layer-cake $p$-adic deficit bounds (`layer_cake_deficit_le_of_pow_subset`) and coprime multiplicative packing (`Erdos708/CoprimePack.lean`) prove `exists_two_slots_for_R_dvd_M`, closing $A$ with at most $2$ extra slots ($6 + 2 = 8$).
3. **Unconditional proof of $g(5) \le 6$ (`Erdos708/G5*.lean`):**
   Strong induction on $M$, GCD reduction to $\gcd(A) = 1$, and maximum bipartite matching size $r \in \{1..5\}$ into `consecInterval x M`:
   - $r = 5$: matching image covers $A$ in $5$ slots.
   - $r = 4$: defect-$1$ telescoping GCD chain (`erdos708_upper_n_of_matching_pred`) closes in $5$ slots.
   - $r = 2, 3$: master two-slot residual theorem (`exists_two_slots_for_R_le_M_five` in `Erdos708/G5TwoSlot.lean`) + partition and Case A/B analysis (`Erdos708/G5R2.lean`, `Erdos708/G5.lean`).
   - $r = 1$: every element has a unique multiple in $I$ ($M < 2a$), reducing via `cover_four_of_chain4` / `cover_four_of_type1b` to the rigid core `C5Core` closed in `Erdos708/G5Core.lean`.

## Verification Results

Verified from scratch purely against Mathlib on Lean `v4.33.1` (`mathlib4` rev `0df444a360eaa60ab8c11dca51a86af692955474`):

- **Build:** All 15 files (`24,536` total lines) compiled with `-DautoImplicit=false -DmaxHeartbeats=0` in `390s` with `0` errors and `0` warnings. (`maxHeartbeats = 0` is set in `[leanOptions]` of `lakefile.toml` for `Erdos708/Lower.lean` and `Erdos708/UpperCore.lean`; zero `.lean` files use `set_option maxHeartbeats`.)
- **Independent Kernel Checker:** `leanchecker Erdos708` exited `0` (`LEANCHECKER_PASS`).
- **Axiom Audit (`#print axioms`):** All 10 headline theorems (`erdos708_exact_one`, `erdos708_exact_two`, `erdos708_exact_three`, `erdos708_exact_four`, `erdos708_upper_five`, `erdos708_exact_five`, `erdos708_upper_six`, `erdos708_exact_six`, `erdos708_exact_one_through_six`, `exists_cover_le_two_mul_of_semiprimes`) depend strictly on:
  `[propext, Classical.choice, Quot.sound]`.
- **Zero-Cheat Scan:** Comment-stripped scan across all 15 `.lean` files found `0` occurrences of `sorry`, `admit`, `axiom`, `opaque`, `native_decide`, `bv_decide`, `ofReduceBool`, `trustCompiler`, bare `import Mathlib`, `at *`, or `set_option maxHeartbeats`.

## How to Reproduce

```bash
git clone https://github.com/nil-commits/erdos708-g6-lean4.git
cd erdos708-g6-lean4
lake exe cache get
lake build
lake env leanchecker Erdos708
```

To print the axiom dependencies yourself:

```bash
lake env lean --stdin << 'EOF'
import Erdos708
#print axioms Erdos708.erdos708_upper_five
#print axioms Erdos708.erdos708_exact_five
#print axioms Erdos708.erdos708_upper_six
#print axioms Erdos708.erdos708_exact_six
#print axioms Erdos708.erdos708_exact_one_through_six
EOF
```

## Module Structure (`24,536` lines across 15 Lean files)

| File | Lines | Role |
|---|---:|---|
| `Erdos708.lean` | 1 | Root re-export (`import Erdos708.Main`) |
| `Erdos708/Lower.lean` | 1,348 | Problem defs, CRT helper, $g(1), g(2)$, lower bounds $g(3) \ge 4, g(4) \ge 5, g(5) \ge 6, g(6) \ge 7, g(7) \ge 9$, $\sum \Omega(a)$ semiprime barrier |
| `Erdos708/UpperCore.lean` | 503 | Interval cover primitives & $\sum \omega(a)$ bound |
| `Erdos708/UpperBinPack.lean` | 520 | Prime-power bin packing for large $\max(A)$ |
| `Erdos708/G3AndG6Lower.lean` | 976 | Exact $g(3) = 4$, sharp CRT lower bound $g(6) \ge 8$, and $g(6) \le 8$ base lemmas |
| `Erdos708/Matching.lean` | 262 | Defect-$1$ telescoping GCD chain ($r = n - 1$) & unique-multiple bound |
| `Erdos708/CoprimePack.lean` | 356 | Coprime multiplicative packing & exact top-$c_p$ cover theorem |
| `Erdos708/G6R4.lean` | 1,691 | GCD reduction, maximum matching extraction, and $g(6)$ $r = 4$ closure |
| `Erdos708/G4.lean` | 3,501 | Exact settlement $g(4) = 5$ |
| `Erdos708/G5TwoSlot.lean` | 4,202 | Layer-cake deficit for $|A|=5$, two-slot residual theorem (`R ≤ M`), 4-chain & Type-1b closures |
| `Erdos708/G5R2.lean` | 1,536 | Matching size $r = 2$ closure for $g(5) \le 6$ |
| `Erdos708/G5Core.lean` | 3,843 | Rigid core `C5Core` closure for $g(5)$ $r = 1$ branch |
| `Erdos708/G5.lean` | 3,226 | Matching size $r = 3$ closure, strong induction & exact $g(5) = 6$ |
| `Erdos708/G6FromG5.lean` | 2,538 | Generalized layer-cake deficit bounds & unconditional reduction $g(5) \le 6 \implies g(6) \le 8$ |
| `Erdos708/Main.lean` | 33 | Final theorems `erdos708_upper_six`, `erdos708_exact_six`, `erdos708_exact_one_through_six` |
| `docs/HOW_WE_SOLVED_IT.md` | — | Mathematical exposition, failed compression counterexamples, and Lean 4 notes |

## License

Apache License 2.0 (see [`LICENSE`](LICENSE)).
