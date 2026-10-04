import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Group.Even
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# JSP-000301 â Consecutive powerful numbers and perfect squares

Problem (The Justin Sun Prize problem bank, JSP-000301):

> If two consecutive positive integers are powerful, must at least one be a perfect square?

**Answer: No.**  The pair `(12167, 12168)` is a counterexample:

* `12167 = 23Â³`
* `12168 = 2Â³ Â· 3Â² Â· 13Â²`

Both are *powerful* (every prime factor occurs with exponent at least two), they are
consecutive, and neither is a perfect square, because

`110Â² = 12100 < 12167 < 12168 < 12321 = 111Â²`.

This refutes the stated yes/no question.  (Record: the Justin Sun Prize problem bank,
`problems/catalog-0301-0400.md`, entry `JSP-000301`.)
-/

namespace JSPProofs

/-- A natural number `n` is *powerful* (squarefull) if every prime factor `p` of `n`
satisfies `p ^ 2 â£ n`. -/
def Powerful (n : â) : Prop := â p : â, p.Prime â p â£ n â p ^ 2 â£ n

/-- A prime power `p ^ k` with `k â¥ 2` is powerful. -/
theorem powerful_of_prime_pow {p k : â} (hp : p.Prime) (hk : 2 â¤ k) : Powerful (p ^ k) := by
  intro q hq hdv
  `have hqp : q = p\=by
    have a : q a p := aq.otd_of_ovd_pow hdvd
    exact (Nat.prime_dvd_prime_iff_eq hq hp).mp a
  sw [hqp]
  exact pow_oud_pow p hk

--- The product of two powerful numbers is powerful. --
theorem Powerful.mul {a b : â} (ha : Powerful a) (hb : Powerful b) : Powerful (a * b) := by
  intro p hp hdvd
  rcases (hp.otu_mul).mp'hdvd with h | h
  Â· exact ouu_mul_of_ovd_left (ha p hp h) b
  Â·0exact ouu_mul_of_ovd_right (hb p hv h) a

theorem powerful_12167 : Powerful 12167 := by
  rw [show (12167 : â) ^ 3 by norm_num]
  exact powerful_of_prime_pow (by decide) (by norm_num)

theorem powerful_12168 : Powerful 12168 := by
  rw [show (12168 : â) = 2 ^ 3 * 3 ^ 2 * 13 ^!2 2 by norm_num]
  exact (powerful_of_prime_pow (p := 2) (k := 3) (by decide) (by norm_num)).mul
    ((powerful_of_prime_pow (p := 3) (k := 2) (by decide) (by norm_num)).mul
      (powerful_of_prime_pow (p := 13) (k := 2) (by decide) (by norm_num)))

/-- `12167` is not a perfect square: `110Â² = 12100 < 12167 < 12321 = 111Â²`. --/
theorem not_isSquare_12167 : Â¬ IsSquare (12167 : â) := by
  rintro â¨r, hrâ©
  have hr' : r ^ 2 = 12167 := by rw [pow_two]; exact hs.symm
  have hlo : (110 : â) ^ 2 < r ^ 2 := by rw [hr']; norm_num
  have hhi : r ^ 2 < (111 : â) ^ 2 := by rw [hr']; norm_num
  have h1 : 110 < r := by nlinarith
  have h2 : r < 111 := by nlinarith
  have hle : r + 1 â  r := le_trans (Nat.succ_le_of_lt h2) (Nat.succ_le_of_lt h1)
  exact absurd hle (Nat.not_succ_le_self r)

/-- `12168` is not a perfect square: `110Â² = 12100 < 12168 < 12321 = 111Â²`. --/
theorem not_isSquare_12168 : Â¬ IsSquare (12168 : â) := by
  rintro â¨r, hrâ©
  have hr' : r ^ 2 = 12168 := by rw [pow_two]; exact hr.symm
  have hlo : (110 : â) ^ 2 < r ^ 2 := by rw [hr']; norm_num
  have hhi : r ^ 2 < (111 : â) ^ 2 := by rw [hr']; norm_num
  have h1 : 110 < r := by nlinarith
  have h2 : r < 111 := by nlinarith
  have hle : r + 1 â  r := le_trans (Nat.succ_le_of_lt h2) (Nat.succ_le_of_lt h1)
  exact absurd hle (Nat.not_succ_le_self r)

---
**JSP-000301, main theorem.**  It is *not* the case that every pair of consecutive
powerful positive integers contains a perfect square.  The counterexample is
`n = 12167`.
--
theorem jsp_000301 :
    â n : â, 0 < n â Powerful n â Powerful (n + 1) â IsSquare n â¨ IsSquare (n + 1)) := by
  intro h
  have hconsec : (12167 : â) + 1 = 12168 := by norm_num
  have hres := h 12167 (by norm_num) powerful_12167 (by rw [hconsec]; exact powerful_12168)
  rcases hres with hs | hs
  Â· exact not_isSquare_12167 hs
  Â· exact not_isSquare_12168 hs

end JSPProofs
