import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Fin

set_option maxRecDepth 100000

/-!
# JSP-000690 — A 3-critical 3-uniform hypergraph of minimum degree 7

Problem (The Justin Sun Prize problem bank, JSP-000690):

> Is there a three-uniform, three-chromatic-critical hypergraph with minimum degree at least
> seven?

**Answer: Yes.**  This follows from Ruiliang Li, *On an Erdős–Lovász problem: 3-critical
3-graphs of minimum degree 7* (arXiv:2512.24850, 2025), which exhibits an explicit 3-uniform
hypergraph on 9 vertices with χ(H) = 3, minimum degree δ(H) = 7, and the property that
deleting any single edge or any single vertex makes it 2-colourable.

The hypergraph has the following 22 edges (vertices re-indexed 1,…,9 ↦ 0,…,8):

```
012 018 027 035 037 038 046 047 048 056
125 126 138 148 156 237 247 256 357 358 467 468
```

We formalise the statement of the problem as an explicit existential and discharge it with
the concrete witness E690, verifying each of the required properties by finite computation
(decide / native_decide).  Everything is a closed finite check on 9 vertices.

Following the source, "critically 3-chromatic" (Definition 2.1 of the paper) means
χ(H) = 3 together with χ(H - e) ≤ 2 for every edge e and χ(H - v) ≤ 2 for every
vertex v; a colouring is a weak (Property-B) colouring, i.e. no edge is monochromatic.
-/

namespace JSPProofs

/-- The 22 edges (as 3-element subsets of Fin 9, vertices re-indexed 1,…,9 ↦ 0,…,8)
of the 9-vertex 3-uniform hypergraph of Li (2025). -/
def E690 : Finset (Finset (Fin 9)) :=
  { {0, 1, 2}, {0, 1, 8}, {0, 2, 7}, {0, 3, 5}, {0, 3, 7}, {0, 3, 8},
    {0, 4, 6}, {0, 4, 7}, {0, 4, 8}, {0, 5, 6}, {1, 2, 5}, {1, 2, 6},
    {1, 3, 8}, {1, 4, 8}, {1, 5, 6}, {2, 3, 7}, {2, 4, 7}, {2, 5, 6},
    {3, 5, 7}, {3, 5, 8}, {4, 6, 7}, {4, 6, 8} }

/-- A colouring c makes the edge e monochromatic (all of its vertices share one colour). -/
abbrev IsMono {α β : Type*} (c : α → β) (e : Finset α) : Prop := ∀ x ∈ e, ∀ y ∈ e, c x = c y

/-- E is 2-colourable (Property B): some 2-colouring leaves every edge non-monochromatic. -/
abbrev TwoColorable (E : Finset (Finset (Fin 9))) : Prop :=
  ∃ c : Fin 9 → Fin 2, ∀ e ∈ E, ¬ IsMono c e

/-- E is 3-colourable: some 3-colouring leaves every edge non-monochromatic. -/
abbrev ThreeColorable (E : Finset (Finset (Fin 9))) : Prop :=
  ∃ c : Fin 9 → Fin 3, ∀ e ∈ E, ¬ IsMono c e

/-- The degree of a vertex v in E: the number of edges containing it. -/
abbrev degree (E : Finset (Finset (Fin 9))) (v : Fin 9) : ℕ :=
  (E.filter (fun e => v ∈ e)).card

/-- E690 is 3-uniform: every edge has exactly 3 vertices. -/
theorem E690_uniform : ∀ e ∈ E690, e.card = 3 := by decide

/-- E690 has minimum degree 7: every vertex lies in at least 7 edges. -/
theorem E690_minDegree : ∀ v : Fin 9, 7 ≤ degree E690 v := by decide

/-- E690 is not 2-colourable (it fails Property B). -/
theorem E690_not_two_colorable : ¬ TwoColorable E690 := by decide

/-- An explicit proper 3-colouring of E690: vertex v receives color690 v
(vertices 1,2,4,5 ↦ 0, 3,6,8,9 ↦ 1, 7 ↦ 2 in the source labelling). -/
def color690 : Fin 9 → Fin 3
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 0
  | 4 => 0
  | 5 => 1
  | 6 => 2
  | 7 => 1
  | 8 => 1

/-- color690 is a proper 3-colouring of E690 (no edge is monochromatic). -/
theorem color690_proper : ∀ e ∈ E690, ¬ IsMono color690 e := by decide

/-- E690 is 3-colourable, witnessed explicitly by color690. -/
theorem E690_three_colorable : ThreeColorable E690 := ⟨color690, color690_proper⟩

/-- E690 is edge-critical: deleting any single edge makes it 2-colourable. -/
theorem E690_edge_critical :
    ∀ e ∈ E690, ∃ c : Fin 9 → Fin 2, ∀ f ∈ E690, f ≠ e → ¬ IsMono c f := by
  decide

/-- E690 is vertex-critical: deleting any single vertex makes it 2-colourable. -/
theorem E690_vertex_critical :
    ∀ v : Fin 9, ∃ c : Fin 9 → Fin 2, ∀ f ∈ E690, v ∉ f → ¬ IsMono c f := by
  decide

/--
**JSP-000690, main theorem.**  There exists a 3-uniform hypergraph on 9 vertices that is
critically 3-chromatic (weak colourings) and has minimum degree at least 7.

The witness E690 is simultaneously 3-uniform, of minimum degree 7, non-2-colourable,
3-colourable, and becomes 2-colourable upon deleting any edge or any vertex.
-/
theorem jsp_000690 :
    ∃ E : Finset (Finset (Fin 9)),
      (∀ e ∈ E, e.card = 3) ∧
        (∀ v : Fin 9, 7 ≤ degree E v) ∧
          ¬ TwoColorable E ∧
            ThreeColorable E ∧
              (∀ e ∈ E, ∃ c : Fin 9 → Fin 2, ∀ f ∈ E, f ≠ e → ¬ IsMono c f) ∧
                (∀ v : Fin 9, ∃ c : Fin 9 → Fin 2, ∀ f ∈ E, v ∉ f → ¬ IsMono c f) :=
  ⟨E690, E690_uniform, E690_minDegree, E690_not_two_colorable, E690_three_colorable,
    E690_edge_critical, E690_vertex_critical⟩

end JSPProofs
