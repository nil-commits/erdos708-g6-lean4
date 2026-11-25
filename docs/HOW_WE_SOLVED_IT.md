# How We Solved and Formalized Erdős Problem #708 for $n = 5$ and $n = 6$

This note documents the mathematical discoveries, dead ends caught during exploration, final proof architecture, and Lean 4 engineering techniques behind the standalone formalization in this repository (`g(5) = 6`, `g(6) = 8`, and `g(1)..g(6)`).

---

## 1. Problem Setup and Definitions

For $n \ge 1$, **Erdős Problem #708** (Erdős–Surányi 1959) asks for the smallest integer $g(n)$ such that for every finite set $A \subset [2, \infty) \cap \mathbb{N}$ of size $|A| = n$, with $M = \max(A)$, and every interval $I = \{x + 1, \dots, x + M\}$ of $M$ consecutive positive integers, there exists a subset $B \subseteq I$ of size $|B| \le g(n)$ satisfying

$$\prod_{a \in A} a \;\Big|\; \prod_{b \in B} b.$$

Equivalently, for every prime $p$:

$$\sum_{a \in A} v_p(a) \le \sum_{b \in B} v_p(b).$$

The Lean 4 formalization (`Erdos708/Lower.lean`) expresses this directly with `consecInterval`, `IsValidSet`, `IsCover`, and `SatisfiesBound`.

---

## 2. Finding the Sharp Lower Bound $g(6) \ge 8$

While $g(4) = 5$ and $g(5) = 6$ were already settled, the split-clique CRT construction initially only gave $g(6) \ge 7$ via $r = 2, s = 2$. To determine whether $g(6)$ is $7$ or $8$, we take the $K_{3,2}$ semiprime family:

$$A_6 = \{23, 29, 31\} \times \{37, 41\} = \{851, 943, 1073, 1147, 1189, 1271\}, \qquad M = 1271.$$

Using the Chinese Remainder Theorem (`exists_crt_finset` in `Erdos708/Lower.lean`, instantiated in `erdos708_lower_six_sharp` in `Erdos708/G3AndG6Lower.lean`), we choose $b_0$ satisfying:
$$b_0 \equiv 23 \pmod{23^2},\quad b_0 \equiv 29 \pmod{29^2},\quad b_0 \equiv 31 \pmod{31^2},\quad b_0 \equiv 666 \pmod{37^2},\quad b_0 \equiv 820 \pmod{41^2}$$
inside $I = [b_0 - 635, b_0 + 635]$. Here $666 = 18 \cdot 37$ and $820 = 20 \cdot 41$, so $b_0$ is divisible by all five primes $\{23, 29, 31, 37, 41\}$ while avoiding all prime squares ($37^2 = 1369$ and $41^2 = 1681$ miss $I$ completely, and $23^2, 29^2, 31^2$ appear only away from $b_0$ without sharing multiples). Since every pairwise product of distinct primes from $\{23, 29, 31, 37, 41\}$ is at least $23 \cdot 29 = 667 > M/2 = 635.5$, distinct prime powers in $I \setminus \{b_0\}$ cannot merge either, forcing any cover $B \subseteq I$ to satisfy $|B| \ge 8$ (`¬ SatisfiesBound 6 7`).

---

## 3. A Dead End Caught Before Formalizing: Why Separate-Prime $p$-Adic Compression Fails

An early proof idea for the defect-$1$ / matching-$1$ residual in $g(6) \le 8$ was a **separate-prime $p$-adic remainder compression lemma**: after fixing a maximum bipartite matching $B_M$ of size $r$ leaving uncovered remainder $R = (\prod A) / \gcd(\prod A, \prod B_M)$, charge each prime $p \mid R$ at most $\lceil v_p(R) / k_p \rceil$ slots where $k_p = \max_{b \in I \setminus B_M} v_p(b)$, hoping $r + \sum_p \lceil v_p(R) / k_p \rceil \le 8$.

Two explicit $r = 1$ counterexamples break that approach cleanly:

### Counterexample A: $\lceil v_p(R) / k_p \rceil$ elements cannot always cover $p^{v_p(R)}$
The maximum $k_p = \max_{b \in I \setminus B_M} v_p(b)$ can be achieved by only a **single** element of $I \setminus B_M$, so $\lceil v_p(R) / k_p \rceil$ distinct elements may fall short:
- Take $A = \{36, 39, 42, 45, 48, 51\}$, $M = 51$, $I = [x + 1, x + 51]$, $b_1 = x + 36$.
- Choose $x \equiv 0 \pmod{81}$ and $x + 36 \equiv 0 \pmod{2^4 \cdot 5 \cdot 7 \cdot 13 \cdot 17}$. Since $v_3(\operatorname{lcm}(A)) = 2 = v_3(36)$, we have $\operatorname{lcm}(A) \mid b_1$ with $v_3(b_1) = 2$.
- Every $a \in A$ has $a \ge 36$, so $b_1$ is the unique multiple of every $a \in A$ in $I$, giving $r = 1$ and $B_M = \{b_1\}$.
- Then $v_3(\prod A) = 2 + 1 + 1 + 2 + 1 + 1 = 8 \implies v_3(R) = 6$. Since $81 \mid x$, $v_3(x + j) = v_3(j)$ for $1 \le j \le 51$. Inside $I \setminus \{b_1\}$, only $j = 27$ gives $k_3 = 3$; the next highest are $j \in \{9, 18, 45\}$ with $v_3 = 2$. So $\lceil v_3(R)/k_3 \rceil = \lceil 6/3 \rceil = 2$, whereas any $2$ elements of $I \setminus \{b_1\}$ have $v_3$-sum at most $3 + 2 = 5 < 6$ (3 slots are needed for $p = 3$).

### Counterexample B: $r + \sum_p \lceil v_p(R)/k_p \rceil$ can be arbitrarily large
Even after fixing Counterexample A by using exact top-$c_p$ valuation sums, treating primes independently still fails to bound $|B| \le 8$:
- Take the common-factor-scaled $K_{2,3}$ instance
  $$A = \{3 \cdot 23, 3 \cdot 29, 3 \cdot 31\} \times \{97, 101\} = \{6693, 6969, 8439, 8787, 9021, 9393\}, \qquad M = 9393.$$
- With $b_1 = x + 6693$ (`r = 1` since $2 \cdot 6693 = 13386 > 9393$) and CRT congruences $x \equiv 0 \pmod{9}$, $x + 6693 \equiv 0 \pmod{23 \cdot 29 \cdot 31}$, $x \equiv 0 \pmod{97^2}$ ($97^2 = 9409 > 9393 \implies k_{97} = 1$), $x \equiv 74 \pmod{101^2}$ ($74 + 6693 = 67 \cdot 101$ and $74 + j \le 9467 < 10201 \implies k_{101} = 1$):
  $$R = 3^5 \cdot 23 \cdot 29 \cdot 31 \cdot 97^2 \cdot 101^2,$$
  giving $r + \sum_p \lceil v_p(R) / k_p \rceil = 1 + (1 + 3 + 4) = 9 > 8$.
- Scaling $\{23, 29, 31\}$ by any primorial $P = \prod_{i=1}^k p_i$ and picking close primes $r_1, r_2 > 35 P$ with $r_2 / r_1 < 1.1$ yields $r = 1$ and separate-prime bound $\ge k + 8 \to \infty$.
- **Why the true cover still has size $\le 6$:** Cross-prime multiplicative packing merges factors into shared interval slots ($3^5 \cdot 23 = 5589 \le 9393$ and $3^5 \nmid b_1$, while $29 \cdot 97 = 2813 \le M/2$ and $31 \cdot 101 = 3131 \le M/2$).

---

## 4. The Pivot That Worked: Coprime Packing + Reduction `g(5) ≤ 6 → g(6) ≤ 8`

Replacing separate-prime bounds with two sharper ideas closed $g(6) = 8$ cleanly:

1. **Coprime Multiplicative Packing (`Erdos708/CoprimePack.lean`):**
   Any pairwise-coprime family of prime-power divisors $d_1, \dots, d_m \mid R$ whose product $D = \prod d_i$ satisfies either $(|S| + 1) D \le M$ (`coprime_packing_slot_of_mul_le`) or $D \le M \land \forall b \in S,\; D \nmid b$ (`coprime_packing_slot_of_not_dvd`) fits inside a single fresh slot in `consecInterval x M \ S`. Paired with greedy bin packing (`list_bin_pack_coprime`), distinct prime powers pack efficiently unless every pair has product $> M / (\text{slots}+1)$ — explaining structurally why $A_6$ with $23 \cdot 29 = 667 > M/2$ is extremal.

2. **Generalized Layer-Cake Deficit & Unconditional `g(5) ≤ 6 → g(6) ≤ 8` (`Erdos708/G6FromG5.lean`):**
   - For $|A| = 6$ and $\gcd(A) = 1$, `layer_cake_deficit_le_of_pow_subset` bounds the $p$-adic deficit between $A$ and any partial cover $B_0$ whenever all multiples of $p^t$ ($t \ge 1$) in `consecInterval x M` already lie in $B_0$:
     $$\sum_{a \in A} v_p(a) - \sum_{b \in B_0} v_p(b) \le (5 - \lfloor M / p^t \rfloor)(t - 1).$$
     Notice when $t = 1$ or $M / p^t \ge 5$, the deficit is $0$.
   - Given `SatisfiesBound 5 6` ($g(5) \le 6$), strong induction on $M$ + `erdos708_gcd_reduction` reduces to $\gcd(A) = 1$. Removing $M = \max(A)$ leaves a $5$-element set covered in $\le 6$ slots $B_0$, leaving residual $R \mid M$.
   - `exists_two_slots_for_R_dvd_M` proves that for $M \ge 9$, at most $2$ extra slots $B_1 \subseteq I \setminus B_0$ always absorb any residual $R \mid M$, yielding `erdos708_upper_six_of_upper_five : SatisfiesBound 5 6 → SatisfiesBound 6 8`.

---

## 5. Closing `g(5) ≤ 6` Unconditionally

Once `g(5) ≤ 6 → g(6) ≤ 8` was in place, settling $g(5) = 6$ closed both $n = 5$ and $n = 6$ together (`Erdos708/G5TwoSlot.lean`, `Erdos708/G5R2.lean`, `Erdos708/G5Core.lean`, `Erdos708/G5.lean`):

1. **Base & GCD reduction (`Erdos708/G5.lean`):**
   Strong induction on $M = \max(A)$. If $M \le 6$, take the full interval $I$ (`|I| = M ≤ 6`). If $g = \gcd(A) > 1$, divide out $g$ (`erdos708_gcd_reduction`); if $1$ appears after dividing, reduce the remaining 4 elements via `erdos708_upper_four : SatisfiesBound 4 5` (`Erdos708/G4.lean`).
2. **Maximum matching branch dispatch ($r \in \{1..5\}$):**
   - $r = 5$: the matching image itself covers $A$ in $5 \le 6$ slots.
   - $r = 4$: `erdos708_upper_n_of_matching_pred` (`Erdos708/Matching.lean`) extends a defect-1 matching via telescoping GCD chains to a $\le 5$-slot cover.
   - $r = 2, 3$: `exists_two_slots_for_R_le_M_five` (`Erdos708/G5TwoSlot.lean`) shows any $\le 4$-slot partial cover leaving residual $R \le M$ closes in $\le 2$ additional slots; combined with `cover_four_of_two_pairs`, `(U₁, U₂, C)` partition (`Erdos708/G5R2.lean`), and Case A/B two-slot analysis (`Erdos708/G5.lean`).
   - $r = 1$: every element $a \in A$ has a unique multiple $b_0 \in I$, forcing $M < 2a$ (`lt_two_mul_of_unique_multiple_in_consecInterval`). `cover_four_of_chain4` and `cover_four_of_type1b` close any 4-chain or pair-spanning 4-subset in $4 + 2 = 6$ slots; the remaining rigid configurations form `C5Core A M`, closed exhaustively via covering rules (`HasRule1`, `Rule2`, `Rule2b` in `Erdos708/G5Core.lean`).

---

## 6. Lean 4 Engineering Notes

- **Pure Mathlib & Zero Axioms:** Unlike the parent development (where `Lower.lean` originally imported asymptotic prime-density bounds for general-$n$ bounds), this standalone repository eliminates every external theorem and depends solely on Mathlib (`[propext, Classical.choice, Quot.sound]`).
- **Keeping proofs modular and kernel-fast:**
  - Deep multi-case closures in `Erdos708/G5.lean` were hoisted into standalone `private lemma`s (e.g., `cover_six_of_r3_two_slots_A3_one_not_b3`) so individual declarations stay responsive rather than exhausting a single elaboration budget.
  - Because `Finset.sum_insert` right-associates sums `c₁ + (c₂ + (b₃ + ...))`, small arithmetic helper lemmas (`a32_arith_*`) were matched verbatim to the right-associated form so `exact a32_arith_* ...` closes valuation goals without triggering heavy `omega` / `whnf` reductions.
  - `[leanOptions]` in `lakefile.toml` retains `maxHeartbeats = 0` (so `Lower.lean`'s 230-line `Finset`/`Nat` CRT proof and `UpperCore.lean`'s `Finset.sum_attach` proof compile cleanly across machines), while zero `.lean` files contain `set_option maxHeartbeats`, `sorry`, `admit`, `axiom`, `opaque`, `native_decide`, or `bv_decide`.
- **Independent Kernel Checking:** The entire dependency graph was compiled from scratch with `lean -DautoImplicit=false` (0 errors, 0 warnings) against pure Mathlib `.olean`s and verified end-to-end with `leanchecker Erdos708`.
