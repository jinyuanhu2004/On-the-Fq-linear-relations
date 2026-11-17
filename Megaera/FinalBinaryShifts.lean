import Megaera.FinalBinaryProof
import Megaera.SectionThreeSpaces

/-! The weighted form of Lemma 2.1 for homogeneous inputs, including the
weight-zero boundary, and its expression with constant-field coefficients. -/
namespace Megaera.FinalBinary
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.Shaped Megaera.BinaryOperators
open Megaera.FinalBinaryLaurent Megaera.FinalBinaryCarlitz Megaera.SectionThreeSpaces
variable {F : Type u} [Arithmetic F] [Neg F] {q w : Nat}

private theorem nil_of_zero (s : Tuple) (v : Valid s) (z : weight s=0) : s=[] := by
  cases s with
  | nil => rfl
  | cons a t =>
    have pos := v a (by simp)
    simp only [weight] at z
    omega

private theorem mapped_empty {K : Type v} [Arithmetic K] (G : Tuple→K) (x : Nat→K)
    (n : Nat) (g : Tuple→Tuple) (p : FormalSum K) (empty : ∀ e∈p,e.2=[]) :
    weighted G (mapTuples g p)=G (g []) * weighted (truncSum x n) p := by
  induction p with
  | nil => exact (Arithmetic.mulZero _).symm
  | cons e p ih =>
    have en := empty e (by simp)
    change e.1*G (g e.2)+weighted G (mapTuples g p) =
      G (g []) * (e.1*truncSum x n e.2+weighted (truncSum x n) p)
    rw [en,ih (fun z hz => empty z (List.mem_cons_of_mem _ hz)),trunc_nil,
      Arithmetic.mulOne,Arithmetic.distrib,Arithmetic.mulComm e.1]

/-- At internal weight zero the relation remains binary after any uniform
tuple map, so both common conventions for increasing the empty tuple work. -/
theorem zero_weight_shift (field : ConstantField F q) (P Q : FormalSum (Laurent F))
    (hp : homogeneous 0 P) (hq : homogeneous 0 Q) (g : Tuple→Tuple)
    (h : Shaped.Binary (inverse q) (weightedShaped q P Q)) :
    Shaped.Binary (inverse q) (weightedShaped q (mapTuples g P) (mapTuples g Q)) := by
  let c : Laurent F := theta + -power theta q
  have iff_ := fun A B => weighted_binary_iff (inverse (F:=F) q) q c A B
    (fundamental_level field) (cancel_level field) (add_cancel field) (negative_sum field 1)
  apply (iff_ _ _).mpr
  intro n
  have eq := (iff_ P Q).mp h n
  have nils (R : FormalSum (Laurent F)) (hr : homogeneous 0 R) (e) (he : e∈R) : e.2=[] :=
    nil_of_zero _ (hr e he).1 (hr e he).2
  rw [mapped_empty _ (inverse q) (n+1) _ _ (nils Q hq),
    mapped_empty _ (inverse q) (n+1) _ _ (nils P hp),eq,←Arithmetic.mulAssoc,
    Arithmetic.mulComm _ c,Arithmetic.mulAssoc]

theorem lemma_2_1_homogeneous (field : ConstantField F q) (P Q : FormalSum (Laurent F))
    (hp : homogeneous w P) (hq : homogeneous w Q)
    (h : Shaped.Binary (inverse q) (weightedShaped q P Q)) :
    Shaped.Binary (inverse q) (weightedShaped q (mapTuples (List.cons 1) P)
      (mapTuples (List.cons 1) Q)) ∧
    Shaped.Binary (inverse q) (weightedShaped q (mapTuples incFirst P) (mapTuples incFirst Q)) := by
  cases w with
  | zero => exact ⟨zero_weight_shift field _ _ hp hq _ h,zero_weight_shift field _ _ hp hq _ h⟩
  | succ n =>
    apply lemma_2_1 field P Q _ _ h
    all_goals
      intro e he eqn
      first | have wt := (hp e he).2 | have wt := (hq e he).2
      rw [eqn] at wt
      change 0=n+1 at wt
      omega

omit [Neg F] in
private theorem coeffs_expand (f : Tuple→List Tuple) (p : FormalSum F) :
    coeffs (expand f p)=expand f (coeffs p) := by
  simp [coeffs,expand,List.map_flatMap,List.flatMap_map,List.map_map,Function.comp_def]

omit [Neg F] in
private theorem coeffs_map (g : Tuple→Tuple) (p : FormalSum F) :
    coeffs (mapTuples g p)=mapTuples g (coeffs p) := by
  simp [coeffs,mapTuples,List.map_map,Function.comp_def]

private theorem coeffs_shaped (field : ConstantField F q) (P Q : FormalSum F) :
    coeffPair (weightedShaped q P Q)=weightedShaped q (coeffs P) (coeffs Q) := by
  have neg (R : FormalSum F) : coeffs (R.map (fun z => ((-(1:F))*z.1,z.2))) =
      (coeffs R).map (fun z => ((-(1:Laurent F))*z.1,z.2)) := by
    simp [coeffs,List.map_map,Function.comp_def,scalar_mul,scalar_neg field,scalar_one]
  simp only [coeffPair,weightedShaped,neg,coeffs_expand]

omit [Neg F] in
private theorem coeffs_homogeneous (p : FormalSum F) (h : homogeneous w p) :
    homogeneous w (coeffs p) := by
  intro z hz
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hz
  exact h e he

/-- Lemma 2.1 in the same coefficient model as the main theorem. There
is no factor recurrence, generic field-law, or support exclusion to supply. -/
theorem lemma_2_1_constants (field : ConstantField F q) (P Q : FormalSum F)
    (hp : homogeneous w P) (hq : homogeneous w Q) (h : Lift.Binary q (weightedShaped q P Q)) :
    Lift.Binary q (weightedShaped q (mapTuples (List.cons 1) P) (mapTuples (List.cons 1) Q)) ∧
    Lift.Binary q (weightedShaped q (mapTuples incFirst P) (mapTuples incFirst Q)) := by
  have transfer (A B : FormalSum F) :=
    (inverse_binary_iff q (weightedShaped q A B)).symm
  simp only [coeffs_shaped field] at transfer
  have both := lemma_2_1_homogeneous field _ _ (coeffs_homogeneous P hp) (coeffs_homogeneous Q hq)
    ((transfer P Q).mp h)
  constructor
  · apply (transfer _ _).mpr
    simpa only [coeffs_map] using both.1
  · apply (transfer _ _).mpr
    simpa only [coeffs_map] using both.2

end Megaera.FinalBinary
