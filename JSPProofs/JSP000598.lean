import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum

/-!
# JSP-000598 — Central binomial coefficients with identical prime divisors

Problem (The Justin Sun Prize problem bank, JSP-000598):

> Can two distinct central binomial coefficients have exactly the same prime divisors?

**Answer: Yes.**  The pair of central binomial coefficients

* `C(174,87) = 1446307705450557558142084756547133980616347954754720`
* `C(176,88) = 5752360192132899378974200736267010150178656638229000`

are distinct, yet they have exactly the same set of prime divisors.  Both are

`2^a · 3 · 5^b · 7^c · 11^d · 13^2 · 19 · 23 · 31 · 47 · 53 · 89 · 97 · 101 ·
103 · 107 · 109 · 113 · 127 · 131 · 137 · 139 · 149 · 151 · 157 · 163 · 167 · 173`,

i.e. the same twenty-eight primes, so their prime-divisor sets coincide.

The formal proof below avoids exhibiting the full factorisations.  Writing
`A = C(174,87)` and `B = C(176,88)`, it suffices to observe that

* `A ∣ B ^ 2`  (every prime of `A` occurs in `B`), and
* `B ∣ A ^ 3`  (every prime of `B` occurs in `A`),

which forces `rad A = rad B`.  Both divisibilities, the two explicit values and
their distinctness are decided by computation.

(Record: the Justin Sun Prize problem bank, `problems/catalog-0501-0600.md`,
entry `JSP-000598`.)
-/

set_option maxRecDepth 100000

namespace JSPProofs

/-- Explicit value of the central binomial coefficient `C(174,87)`. -/
theorem choose_174_87 :
    Nat.choose 174 87 = 1446307705450557558142084756547133980616347954754720 := by
  decide

/-- Explicit value of the central binomial coefficient `C(176,88)`. -/
theorem choose_176_88 :
    Nat.choose 176 88 = 5752360192132899378974200736267010150178656638229000 := by
  decide

/-- `C(174,87)` divides `C(176,88) ^ 2`, so every prime divisor of `C(174,87)`
divides `C(176,88)`. -/
theorem choose_174_87_dvd_sq :
    (1446307705450557558142084756547133980616347954754720 : ℕ) ∣
      5752360192132899378974200736267010150178656638229000 ^ 2 := by
  decide

/-- `C(176,88)` divides `C(174,87) ^ 3`, so every prime divisor of `C(176,88)`
divides `C(174,87)`. -/
theorem choose_176_88_dvd_cube :
    (5752360192132899378974200736267010150178656638229000 : ℕ) ∣
      1446307705450557558142084756547133980616347954754720 ^ 3 := by
  decide

/--
**JSP-000598, main theorem.**  Two distinct central binomial coefficients can have
exactly the same prime divisors; the pair `(C(174,87), C(176,88))` is an example.
-/
theorem jsp_000598 :
    ∃ m n : ℕ,
      Nat.choose (2 * m) m ≠ Nat.choose (2 * n) n ∧
        ∀ p : ℕ, p.Prime → (p ∣ Nat.choose (2 * m) m ↔ p ∣ Nat.choose (2 * n) n) := by
  refine ⟨87, 88, ?_, ?_⟩
  · rw [show 2 * 87 = 174 by norm_num, show 2 * 88 = 176 by norm_num,
      choose_174_87, choose_176_88]
    decide
  · intro p hp
    rw [show 2 * 87 = 174 by norm_num, show 2 * 88 = 176 by norm_num,
      choose_174_87, choose_176_88]
    constructor
    · intro h
      exact hp.dvd_of_dvd_pow (dvd_trans h choose_174_87_dvd_sq)
    · intro h
      exact hp.dvd_of_dvd_pow (dvd_trans h choose_176_88_dvd_cube)

end JSPProofs
