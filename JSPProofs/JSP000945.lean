import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option maxRecDepth 100000

namespace JSPProofs

/-- The problem's property, unrestricted reading: for every k >= 1 with 2k^2 < n,
the difference n - 2k^2 is prime. -/
def TwiceSquarePrime (n : Nat) : Prop :=
  ∀ k : Nat, 1 ≤ k → 2 * k ^ 2 < n → Nat.Prime (n - 2 * k ^ 2)

/-- Bounded variant, decidable by computation. -/
abbrev TwiceSquarePrimeB (n : Nat) : Prop :=
  ∀ k ∈ Finset.range (n + 1), 1 ≤ k → 2 * k ^ 2 < n → Nat.Prime (n - 2 * k ^ 2)

/-- The problem's property, coprime reading: for every k >= 1 with gcd(k,n) = 1
and 2k^2 < n, the difference n - 2k^2 is prime. -/
def TwiceSquarePrimeCoprime (n : Nat) : Prop :=
  ∀ k : Nat, 1 ≤ k → Nat.Coprime k n → 2 * k ^ 2 < n → Nat.Prime (n - 2 * k ^ 2)

/-- Bounded variant. -/
abbrev TwiceSquarePrimeCoprimeB (n : Nat) : Prop :=
  ∀ k ∈ Finset.range (n + 1), 1 ≤ k → Nat.Coprime k n → 2 * k ^ 2 < n →
    Nat.Prime (n - 2 * k ^ 2)

/-- Any k with 2k^2 < n lies in Finset.range (n+1). -/
theorem mem_range_of_two_sq {k n : Nat} (hk1 : 1 ≤ k) (hlt : 2 * k ^ 2 < n) :
    k ∈ Finset.range (n + 1) := by
  have hkpos : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hk1
  have h2k : 0 < 2 * k := Nat.mul_pos (by norm_num) hkpos
  have h1 : 1 ≤ 2 * k := Nat.succ_le_of_lt h2k
  have hk_le : k ≤ 2 * k ^ 2 :=
    calc k = k * 1 := (Nat.mul_one k).symm
      _ ≤ k * (2 * k) := Nat.mul_le_mul_left k h1
      _ = 2 * k ^ 2 := by ring
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le (le_of_lt (lt_of_le_of_lt hk_le hlt)))

theorem twiceSquarePrime_of_bounded {n : Nat} (h : TwiceSquarePrimeB n) :
    TwiceSquarePrime n :=
  fun k hk1 hlt => h k (mem_range_of_two_sq hk1 hlt) hk1 hlt

theorem twiceSquarePrimeCoprime_of_bounded {n : Nat} (h : TwiceSquarePrimeCoprimeB n) :
    TwiceSquarePrimeCoprime n :=
  fun k hk1 hc hlt => h k (mem_range_of_two_sq hk1 hlt) hk1 hc hlt

theorem good199 : TwiceSquarePrimeB 199 := by decide

theorem good861 : TwiceSquarePrimeCoprimeB 861 := by decide

theorem jsp_000945 :
    ∃ n : Nat, 0 < n ∧ TwiceSquarePrime n :=
  ⟨199, by norm_num, twiceSquarePrime_of_bounded good199⟩

theorem jsp_000945_coprime :
    ∃ n : Nat, 0 < n ∧ TwiceSquarePrimeCoprime n :=
  ⟨861, by norm_num, twiceSquarePrimeCoprime_of_bounded good861⟩

end JSPProofs
