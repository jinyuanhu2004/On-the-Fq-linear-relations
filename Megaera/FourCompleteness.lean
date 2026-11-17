import Megaera.FourReduction

/-! The maximal-illegal-minimum argument on pages 21–24. The hypothesis
`Survives` singles out the case analysis required of the new proof. -/
namespace Megaera.FourReduction
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.Triangular Megaera.CanonicalInd
variable {F : Type u} [Arithmetic F] [Neg F] {q w : Nat}
local instance : Zero (Tuple → F) := ⟨fun _ => 0⟩

theorem least_of_nonzero (v : Tuple → F) (hv : RelationVector q w v) (nz : v ≠ 0) :
    ∃ s, Least v s := by
  classical
  have ex : ∃ s ∈ Dimension.tuples Int.toNat w, v s ≠ 0 := by
    apply Classical.byContradiction
    intro missing
    apply nz
    funext s
    exact Classical.byContradiction (fun h => missing ⟨s,support_at_weight hv h,h⟩)
  obtain ⟨s,_,hs,hm⟩ := smallest _ _ ex
  exact ⟨s,hs,fun t ht => hm t (support_at_weight hv ht) ht⟩

omit [Neg F] in
/-- Strict rank increase moves every surviving coordinate above the old minimum. -/
theorem above_of_rank (v z : Tuple → F) (s : Tuple) (first : Least v s)
    (inc : vectorRank w v < vectorRank w z) : ∀ t, z t ≠ 0 → Precedes s t := by
  classical
  intro t ht
  rcases precedes_trichotomy s t with lt | eq | lt
  · exact lt
  all_goals
    apply False.elim
    apply Nat.not_le_of_lt inc
    unfold vectorRank
    apply count_mono
    intro x keep
    simp only [decide_eq_true_eq] at keep ⊢
    intro u hu
    have a := keep t ht
    have b : Precedes x s := by first | exact eq ▸ a | exact precedes_trans a lt
    rcases first.2 u hu with rfl | c
    · exact b
    · exact precedes_trans b c

/-- Tuples at or above the first nonzero coefficient of the input to elimination.
The zero vector permits no pivots. -/
def ImageWindow (z : Tuple → F) (t : Tuple) : Prop :=
  ∃ u, z u ≠ 0 ∧ (u = t ∨ Precedes u t)

/-- The remaining local assertion for §§4.2–4.3. The cutoff follows the
actual image. Every normalization step stays within this window. -/
def Survives (F : Type u) [Arithmetic F] [Neg F] (q w : Nat) (hq : 0 < q) : Prop :=
  ∀ v : Tuple → F, RelationVector q w v → Reduced F q w v → ∀ s, Least v s →
    let z := ind q w hq v
    ¬ Reduces F q w (ImageWindow z) z (fun _ => 0)

/-- A coefficient functional which is unchanged at every allowed reduction and
is nonzero on Ind v certifies survival, as required in Case II. -/
theorem survives_of_functional (allow : Tuple → Prop) (v : Tuple → F)
    (S : (Tuple → F) → F) (z : S (fun _ => 0) = 0) (nz : S v ≠ 0)
    (stable : ∀ (x g : Tuple → F) (s : Tuple) (k : F),
      Special F q w g → Least g s → allow s → S (addScaled x k g) = S x) :
    ¬ Reduces F q w allow v (fun _ => 0) := by
  have invariant {x y : Tuple → F} (steps : Reduces F q w allow x y) : S y = S x := by
    induction steps with
    | done => rfl
    | step hg hmin permitted _ _ _ ih => exact ih.trans (stable _ _ _ _ hg hmin permitted)
  intro steps
  exact nz ((invariant steps).symm.trans z)

private theorem reduced_zero (field : ConstantField F q) (hq : 0 < q)
    (sound : ∀ g, Special F q w g → RelationVector q w g)
    (nextRel : ∀ x : Tuple → F, RelationVector q w x → RelationVector q w (ind q w hq x))
    (inc : ∀ x : Tuple → F, RelationVector q w x → x ≠ 0 → vectorRank w x < vectorRank w (ind q w hq x))
    (survival : Survives F q w hq) (v : Tuple → F) (hv : RelationVector q w v)
    (red : Reduced F q w v) : v = 0 := by
  classical
  by_cases nz : v = 0
  · exact nz
  obtain ⟨s,first⟩ := least_of_nonzero v hv nz
  have above := above_of_rank v _ s first (inc v hv nz)
  let z := ind q w hq v
  have start (t : Tuple) (hn : z t ≠ 0) : ImageWindow z t := ⟨t,hn,.inl rfl⟩
  have up (t y : Tuple) (ht : ImageWindow z t) (later : Precedes t y) : ImageWindow z y := by
    obtain ⟨u,hu,rfl | h⟩ := ht
    · exact ⟨_,hu,.inr later⟩
    · exact ⟨_,hu,.inr (precedes_trans h later)⟩
  obtain ⟨r,hr,rr,ar,steps⟩ := normalize field sound (ImageWindow z) z (nextRel _ hv) start up
  have rise := vectorRank_strict w v r s (support_at_weight hv first.1) first.1 (by
    intro t ht
    obtain ⟨u,hu,rfl | h⟩ := ar t ht
    · exact above _ hu
    · exact precedes_trans (above _ hu) h)
  have ended := reduced_zero field hq sound nextRel inc survival r hr rr
  change r = (fun _ => 0) at ended
  rw [ended] at steps
  exact (survival v hv red s first steps).elim
termination_by (Dimension.tuples Int.toNat w).length - vectorRank w v
decreasing_by have := vectorRank_bound w r; omega

theorem bcp_of_reduces {v r : Tuple → F} (field : ConstantField F q) {allow : Tuple → Prop}
    (hr : BCPVector q w r) (moves : Reduces F q w allow v r) : BCPVector q w v := by
  induction moves with
  | done => exact hr
  | @step v r g s k hg _ _ _ _ _ ih =>
    have mem := GradedBCP.sub_mem field (ih hr) (GradedBCP.scale_mem k (special_mem field hg))
    have cancel (t : Tuple) : addScaled v k g t + -(k*g t) = v t := by
      simp [addScaled,Arithmetic.addAssoc,field.add_neg,Arithmetic.addZero]
    simpa only [cancel] using mem

/-- The new proof reduces completeness to its local survival assertion. This
does not use H(ker L)=BCP or L(ker H)⊆BCP. Soundness is the §2 input.
The row identity and the published TT hypothesis give canonical spanning. -/
theorem completeness_at_weight (field : ConstantField F q) (hq : 0 < q)
    (rowLaw : ∀ e : Row q w, RowEvaluation.Identity (F := F) q
      (withCoeff 1 (L q e.val.1 e.val.2)) (withCoeff 1 (H q e.val.1 e.val.2)))
    (tt : TTSpanning.TTPolynomialIndependent F q w)
    (sound : ∀ g : Tuple → F, BCPVector q w g → RelationVector q w g)
    (survival : Survives F q w hq) (p : FormalSum F)
    (hp : ∀ e ∈ p, Valid e.2 ∧ weight e.2 = w) : Relation q w p ↔ InBCP q w p := by
  have span := TTSpanning.canonical_spanning_of_theorem_1_2 field tt rowLaw
  have nextRel (v : Tuple → F) (hv : RelationVector q w v) : RelationVector q w (ind q w hq v) := by
    obtain ⟨c,hl,hb⟩ := span v hv
    rw [←hl,ind_components q w hq field c hb]
    exact RowEvaluation.relation_H_of_relation_L field c
      (RowEvaluation.rows_identity c (fun e _ => rowLaw e.2)) (hl ▸ hv)
  have inc (v : Tuple → F) (hv : RelationVector q w v) (hn : v ≠ 0) :
      vectorRank w v < vectorRank w (ind q w hq v) := by
    obtain ⟨c,hl,hb⟩ := span v hv
    exact Reduction.ind_rank_increases hq field v hn c hl hb
  have genSound := fun g hg => sound g (special_mem field hg)
  rw [relation_iff_vector q w p hp, bcp_iff_vector]
  refine ⟨?_,sound _⟩
  intro hv
  obtain ⟨r,hr,rr,_,steps⟩ := normalize field genSound (fun _ => True) _ hv
    (fun _ _ => trivial) (fun _ _ _ _ => trivial)
  have hzero := reduced_zero field hq genSound nextRel inc survival r hr rr
  exact bcp_of_reduces field (hzero ▸ GradedBCP.zero_mem) steps

end Megaera.FourReduction
