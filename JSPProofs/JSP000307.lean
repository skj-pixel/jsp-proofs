import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum

namespace JSPProofs

/-- p is the largest prime factor of n. -/
def IsLargestPrimeFactor (p n : Nat) : Prop :=
  p.Prime ∧ p ∣ n ∧ ∀ q : Nat, q.Prime → q ∣ n → q ≤ p

theorem isLargestPrimeFactor_13_13 : IsLargestPrimeFactor 13 13 := by
  refine ⟨by decide, by norm_num, ?_⟩
  intro q hq hdvd
  have hq13 : q = 13 := (Nat.prime_dvd_prime_iff_eq hq (by decide)).mp hdvd
  subst hq13
  norm_num

theorem isLargestPrimeFactor_7_14 : IsLargestPrimeFactor 7 14 := by
  refine ⟨by decide, by norm_num, ?_⟩
  intro q hq hdvd
  rw [show (14 : Nat) = 2 * 7 by norm_num] at hdvd
  rcases hq.dvd_mul.mp hdvd with h | h
  · have hq2 : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by decide)).mp h
    subst hq2
    norm_num
  · have hq7 : q = 7 := (Nat.prime_dvd_prime_iff_eq hq (by decide)).mp h
    subst hq7
    norm_num

theorem isLargestPrimeFactor_5_15 : IsLargestPrimeFactor 5 15 := by
  refine ⟨by decide, by norm_num, ?_⟩
  intro q hq hdvd
  rw [show (15 : Nat) = 3 * 5 by norm_num] at hdvd
  rcases hq.dvd_mul.mp hdvd with h | h
  · have hq3 : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by decide)).mp h
    subst hq3
    norm_num
  · have hq5 : q = 5 := (Nat.prime_dvd_prime_iff_eq hq (by decide)).mp h
    subst hq5
    norm_num

theorem jsp_000307 :
    ∃ a : Nat, ∃ p q r : Nat,
      IsLargestPrimeFactor p a ∧ IsLargestPrimeFactor q (a + 1) ∧
        IsLargestPrimeFactor r (a + 2) ∧ p > q ∧ q > r :=
  ⟨13, 13, 7, 5, isLargestPrimeFactor_13_13, isLargestPrimeFactor_7_14,
    isLargestPrimeFactor_5_15, by norm_num, by norm_num⟩

end JSPProofs
