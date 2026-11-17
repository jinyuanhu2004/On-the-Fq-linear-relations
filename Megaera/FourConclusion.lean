import Megaera.FourCaseIProof

namespace Megaera.FourReduction
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.Triangular Megaera.CanonicalInd
variable {F : Type u} [Arithmetic F] [Neg F] {q w : Nat}

def CaseITail (t : Tuple) : Prop :=
  t=[] ∨ ∃ r z, t=List.replicate r 1 ++ [z] ∧ 0<z

/-- The unproved Case II assertion, restricted to sorted canonical rows
whose L-image is a reduced relation and to the window of their actual H-image. -/
def CaseIISurvival (F : Type u) [Arithmetic F] [Neg F] (q w : Nat) : Prop :=
  ∀ (e : F × Row q w) (rows : Rows F q w),
    (e::rows).Pairwise (fun a b => Precedes (rowSource a) (rowSource b)) →
    (∀ f∈e::rows, f.1 ≠ 0 ∧ ∀ a∈f.2.val.1, a≤q) →
    ¬ CaseITail e.2.val.2 →
    RelationVector q w (component L (e::rows)) → Reduced F q w (component L (e::rows)) →
    let z := component H (e::rows)
    ¬ Reduces F q w (ImageWindow z) z (fun _ => 0)

/-- The two cases supply survival for the image of any completely reduced
nonzero relation, independently of the choice of stopping rule. -/
theorem survival_of_cases (field : ConstantField F q)
    (rowLaw : ∀ e : Row q w, RowEvaluation.Identity (F := F) q
      (withCoeff 1 (L q e.val.1 e.val.2)) (withCoeff 1 (H q e.val.1 e.val.2)))
    (tt : TTSpanning.TTPolynomialIndependent F q w)
    (caseII : CaseIISurvival F q w) : Survives F q w (by have := field.two_le; omega) := by
  have hq : 0 < q := by have := field.two_le; omega
  intro v hv red s first
  obtain ⟨c,hl,hb⟩ := TTSpanning.canonical_spanning_of_theorem_1_2 field tt rowLaw v hv
  obtain ⟨zs,ord,good,el⟩ := ordered_presentation c hb
  have same := el.trans hl
  cases zs with
  | nil => exact (first.1 ((congrFun same s).symm.trans rfl)).elim
  | cons e rows =>
    have bounded := fun f hf => (good f hf).2
    rw [←same,ind_components q w hq field _ bounded]
    by_cases typeI : CaseITail e.2.val.2
    · have tail : ∃ r z, (e.2.val.2=List.replicate r 1 ++ [z] ∧ 0<z) ∨
          (e.2.val.2=[] ∧ r=0 ∧ z=0) := by
        rcases typeI with emp | ⟨r,z,h⟩
        · exact ⟨0,0,.inr ⟨emp,rfl,rfl⟩⟩
        · exact ⟨r,z,.inl h⟩
      obtain ⟨r,z,ht⟩ := tail
      exact (FourCaseIProof.case_I_survives field e rows r z (good e (by simp)).1 ht
        (List.pairwise_cons.mp ord).1 bounded).2.2
    · exact caseII e rows ord good typeI (same ▸ hv) (same ▸ red)

/-- The only case-specific premise is Case II. Case I, selection of an
ordered nonzero presentation, and all finite elimination steps are proved. -/
theorem section_four_at_weight (field : ConstantField F q)
    (rowLaw : ∀ e : Row q w, RowEvaluation.Identity (F := F) q
      (withCoeff 1 (L q e.val.1 e.val.2)) (withCoeff 1 (H q e.val.1 e.val.2)))
    (tt : TTSpanning.TTPolynomialIndependent F q w)
    (sound : ∀ g : Tuple → F, BCPVector q w g → RelationVector q w g)
    (caseII : CaseIISurvival F q w) (p : FormalSum F)
    (hp : ∀ e ∈ p, Valid e.2 ∧ weight e.2 = w) : Relation q w p ↔ InBCP q w p := by
  have hq : 0 < q := by have := field.two_le; omega
  exact completeness_at_weight field hq rowLaw tt sound (survival_of_cases field rowLaw tt caseII) p hp

end Megaera.FourReduction
