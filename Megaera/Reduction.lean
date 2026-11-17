import Megaera.CanonicalInd
import Megaera.Triangular

/-! Lemma 2.6 and the final reduction for Theorem 1.10 with the actual
weight-w operator and depth-lex order. Canonical straightening, the analytic
preservation of the relation space, and the specified generator and kernel
statements remain separate premises. -/
namespace Megaera.Reduction
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.CanonicalInd Megaera.Triangular
variable {F : Type u} [Arithmetic F] [Neg F]
local instance : Zero (Tuple → F) := ⟨fun _ => 0⟩

/-- On a nonzero vector in the span of the canonical L-rows the rank strictly
increases, even when its H-image is zero (the terminal rank). -/
theorem ind_rank_increases {q w : Nat} (hq : 0 < q) (field : ConstantField F q)
    (v : Tuple → F) (nonzero : v ≠ 0)
    (rows : Rows F q w) (hl : component L rows = v)
    (bounded : ∀ e ∈ rows, ∀ a ∈ e.2.val.1, a ≤ q) :
    vectorRank w v < vectorRank w (ind q w hq v) := by
  have pivot : ∃ s, component L rows s ≠ 0 := by
    apply Classical.byContradiction
    intro hn
    apply nonzero
    rw [← hl]
    apply funext
    intro s
    exact Classical.byContradiction (fun hs => hn ⟨s,hs⟩)
  rw [← hl,ind_components q w hq field rows bounded]
  exact canonical_components_increase hq rows bounded pivot

/-- Every relation is killed after at most one more step than the number
of valid tuples of its weight, given its canonical straightening and the
fact that Ind carries relations to relations. -/
theorem nilpotent_on_relations (q w : Nat) (hq : 0 < q) (field : ConstantField F q)
    (preserves : ∀ v : Tuple → F, RelationVector q w v → RelationVector q w (ind q w hq v))
    (canonical : ∀ v, RelationVector q w v → ∃ rows : Rows F q w, component L rows = v ∧
      ∀ e ∈ rows, ∀ a ∈ e.2.val.1, a ≤ q) (v : Tuple → F) (hv : RelationVector q w v) :
    Completeness.iterate (ind q w hq) ((Dimension.tuples Int.toNat w).length+1) v = 0 := by
  apply Completeness.nilpotent_of_strict_rank (RelationVector q w) (ind q w hq) (vectorRank w) _
    (ind_zero q w hq) preserves (fun r _ => vectorRank_bound w r) _ v hv
  intro r hr hn
  obtain ⟨rows,hl,hb⟩ := canonical r hr
  apply ind_rank_increases hq field r _ rows hl hb
  intro hz
  exact hn (hz ▸ ind_zero q w hq)

/-- Completeness with no rank bound, growth or termination hypotheses. -/
theorem completeness_at_weight (q w : Nat) (hq : 0 < q) (field : ConstantField F q)
    (preserves : ∀ v : Tuple → F, RelationVector q w v → RelationVector q w (ind q w hq v))
    (canonical : ∀ v, RelationVector q w v → ∃ rows : Rows F q w, component L rows = v ∧
      ∀ e ∈ rows, ∀ a ∈ e.2.val.1, a ≤ q)
    (kerL : ∀ v, BCPVector q w v → ∃ c : Rows F q w, component L c = 0 ∧ component H c = v)
    (kerH : ∀ c : Rows F q w, component H c = 0 → BCPVector q w (component L c))
    (binary_generators : ∀ u v s, Valid u → Valid v → Valid s → s ≠ [] →
      weight u + weight v + weight s + 2*q = w →
      Lift.Binary (F := F) q (bStar u (cOp v (primitive q s))))
    (p : FormalSum F) (hw : ∀ e ∈ p, Valid e.2 ∧ weight e.2 = w) :
    Relation q w p ↔ InBCP q w p := by
  apply completeness_with_ind q w hq field (vectorRank w) _ preserves
    (fun r _ => vectorRank_bound w r) _ canonical kerL kerH binary_generators p hw
  intro r hr hn
  obtain ⟨rows,hl,hb⟩ := canonical r hr
  apply ind_rank_increases hq field r _ rows hl hb
  intro hz
  exact hn (hz ▸ ind_zero q w hq)

end Megaera.Reduction
