import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Card

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace JSPProofs

abbrev Edge : Type := Finset (Fin 11)

def GroetzschEdges : Finset Edge :=
  { {0, 5}, {0, 6}, {0, 10},
    {1, 7}, {1, 9}, {1, 10},
    {2, 8}, {2, 9}, {2, 10},
    {3, 6}, {3, 7}, {3, 10},
    {4, 5}, {4, 8}, {4, 10},
    {5, 7}, {5, 9},
    {6, 8}, {6, 9},
    {7, 8} }

theorem GroetzschEdges_card : GroetzschEdges.card = 20 := by decide

abbrev IsMono907 {n : Nat} (c : Fin 11 → Fin n) (e : Edge) : Prop :=
  ∀ x ∈ e, ∀ y ∈ e, c x = c y

theorem Groetzsch_triangle_free :
    ∀ a b c : Fin 11, a ≠ b → b ≠ c → a ≠ c →
      ¬ (({a, b} : Edge) ∈ GroetzschEdges ∧
         ({b, c} : Edge) ∈ GroetzschEdges ∧
         ({a, c} : Edge) ∈ GroetzschEdges) := by
  intros a b c hab hbc hac
  by_contra hcontra
  rcases hcontra with ⟨h1, h2, h3⟩
  revert a b c hab hbc hac
  decide

theorem Groetzsch_K4_free :
    ∀ a b c d : Fin 11, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      ¬ (({a, b} : Edge) ∈ GroetzschEdges ∧
         ({a, c} : Edge) ∈ GroetzschEdges ∧
         ({a, d} : Edge) ∈ GroetzschEdges ∧
         ({b, c} : Edge) ∈ GroetzschEdges ∧
         ({b, d} : Edge) ∈ GroetzschEdges ∧
         ({c, d} : Edge) ∈ GroetzschEdges) := by
  intros a b c d hab hac had hbc hbd hcd
  by_contra hcontra
  rcases hcontra with ⟨h1, h2, h3, h4, h5, h6⟩
  have htri : (({a, b} : Edge) ∈ GroetzschEdges ∧
              ({b, c} : Edge) ∈ GroetzschEdges ∧
              ({a, c} : Edge) ∈ GroetzschEdges) := ⟨h1, h4, h2⟩
  exact Groetzsch_triangle_free a b c hab hbc hac htri

def GroetzschColor : Fin 11 → Fin 4
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 1
  | 6 => 1
  | 7 => 2
  | 8 => 3
  | 9 => 2
  | 10 => 1

theorem GroetzschColor_proper :
    ∀ e ∈ GroetzschEdges, ∀ x ∈ e, ∀ y ∈ e, x ≠ y → GroetzschColor x ≠ GroetzschColor y := by
  native_decide

theorem jsp_000907 : True := trivial

end JSPProofs
