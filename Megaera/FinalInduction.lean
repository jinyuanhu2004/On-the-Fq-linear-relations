import Megaera.FinalBinaryRows

namespace Megaera.FinalInduction
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.CanonicalInd
variable {F : Type u} [Arithmetic F] [Neg F] {q w : Nat}
local instance : Zero (Tuple → F) := ⟨fun _ => 0⟩

theorem preserves (field : ConstantField F q) (hq : 0<q) (tt : TTSpanning.TTPolynomialIndependent F q w)
    (v : Tuple → F) (hv : RelationVector q w v) : RelationVector q w (ind q w hq v) := by
  have law (e : Row q w) := FinalBinary.row_identity field _ _ e.property.1 e.property.2.1
  obtain ⟨c,hl,hb⟩ := TTSpanning.canonical_spanning_of_theorem_1_2 field tt law v hv
  rw [←hl,ind_components q w hq field c hb]
  exact RowEvaluation.relation_H_of_relation_L field c (RowEvaluation.rows_identity c (fun e _ => law e.2))
    (hl.symm ▸ hv)

theorem lemma_2_6 (field : ConstantField F q) (hq : 0<q) (tt : TTSpanning.TTPolynomialIndependent F q w)
    (v : Tuple → F) (hv : RelationVector q w v) :
    Completeness.iterate (ind q w hq) ((Dimension.tuples Int.toNat w).length+1) v=0 := by
  exact Reduction.nilpotent_on_relations q w hq field (preserves field hq tt)
    (TTSpanning.canonical_spanning_of_theorem_1_2 field tt
      (fun e => FinalBinary.row_identity field _ _ e.property.1 e.property.2.1)) v hv

theorem theorem_2_7 (field : ConstantField F q) (hq : 0<q) (tt : TTSpanning.TTPolynomialIndependent F q w)
    (S : (Tuple → F) → Prop) (zero_mem : S 0) (inside : ∀ x,S x → RelationVector q w x)
    (backward : ∀ x,RelationVector q w x → S (ind q w hq x) → S x) :
    S=RelationVector q w := by
  funext x; apply propext; refine ⟨inside x,?_⟩
  exact Completeness.of_nilpotent_backward (RelationVector q w) S (ind q w hq) zero_mem
    (preserves field hq tt) (fun v hv => ⟨_,lemma_2_6 field hq tt v hv⟩) backward x

end Megaera.FinalInduction
