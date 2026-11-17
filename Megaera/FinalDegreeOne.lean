import Megaera.CompletenessProof
import Megaera.RevisedProducts
import Megaera.Projection

/-! The degree-one relation space in §3.1. A lifted fundamental row has
two columns, the coefficients of 1 and D₁, given respectively by L and H. -/
namespace Megaera.FinalDegreeOne
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.SectionThreeSpaces
open Megaera.RowEvaluation Megaera.TTSpanning Megaera.BinaryOperators
variable {F : Type u} [Arithmetic F] [Neg F] {q w : Nat}

/-- The actual revised B* C lift of the fundamental pair has columns L and H.
The arbitrary coefficient D plays the role of D₁. The permutation accounts
for CW listing its diamond before its triangle. -/
theorem fundamental_row {K : Type v} [OfNat K 1] (q : Nat) (D : K) (h t : Tuple) :
    (liftPair (RevisedProducts.Bstar h (RevisedProducts.C t (fundamental q D)))).Perm
      (withCoeff (1:K) (L q h t) ++ withCoeff D (H q h t)) := by
  have supp : NonemptySupport (fundamental q D) := by
    constructor <;> intro z hz <;> simp [fundamental] at hz <;> subst z <;> simp
  rw [RevisedProducts.C_eq _ _ supp,
    (RevisedProducts.Bstar_eq h _ (cOp_nonempty t _ supp)).1]
  cases t with
  | nil =>
    have pair : cOp [] (fundamental q D) =
        (withCoeff (1:K) [[q]],withCoeff D ([[q-1]].map (List.cons 1))) := rfl
    rw [pair,PrimitiveRows.bStar_expansion_coeff]
    simp [L,H,start,quasiShuffle_nil_right]
  | cons a t =>
    let pos := [(q+a)::t,q::a::t]
    have pair : cOp (a::t) (fundamental q D) =
        (withCoeff (1:K) pos,withCoeff D ((quasiShuffle [q-1] (a::t)).map (List.cons 1))) := by
      simp [fundamental,cOp,expand,diamond,triangle,quasiShuffle_nil_left,pos,withCoeff]
    rw [pair,PrimitiveRows.bStar_expansion_coeff]
    exact ((List.Perm.swap (h++q::a::t) (h++(q+a)::t) []).map (fun x => ((1:K),x))).append_right _

theorem homogeneous_rows (field : ConstantField F q) (c : Rows F q w) :
    homogeneous w (presentation L c) ∧ homogeneous w (presentation H c) := by
  have hq := field.two_le
  constructor
  all_goals
    intro e he
    obtain ⟨g,_,hm⟩ := List.mem_flatMap.mp he
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hm
    obtain ⟨hs,ht,hw⟩ := g.2.property
  · have wt := L_weight q _ _ v hv
    exact ⟨L_valid q (by omega) _ _ hs ht v hv,by change weight v=w; omega⟩
  · have wt := H_weight q (by omega) _ _ v hv
    exact ⟨H_valid q hq _ _ hs ht v hv,by change weight v=w; omega⟩

/-- Two D₁-rows with the same first value have equal second values. -/
theorem equal_second (field : ConstantField F q) (A B C : Series F)
    (ab : cleared q A B) (ac : cleared q A C) : B=C := by
  have hq := field.two_le
  have cancel (a x y : F) (h : a+x=a+y) : x=y := by
    have hn : -a+a=0 := (Arithmetic.addComm ..).trans (field.add_neg _)
    simpa only [←Arithmetic.addAssoc,hn,zeroAdd] using congrArg ((-a)+·) h
  funext n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    apply cancel (shift q A n)
    rw [ab n,ac n]
    by_cases le : q-1≤n
    · simp only [shift,if_pos le]; exact ih _ (by omega)
    · simp [shift,le]

private def minus (a b : FormalSum F) : FormalSum F :=
  a ++ b.map (fun z => ((-1)*z.1,z.2))

private theorem minus_eval (field : ConstantField F q) (a b : FormalSum F) (n : Nat) :
    evaluate q (minus a b) n = evaluate q a n + -(evaluate q b n) := by
  unfold minus evaluate; rw [total_append']
  have neg := measure_scale (-1:F) (fun e => e.1 * li q e.2 n)
    (fun c t => Arithmetic.mulAssoc _ _ _) b
  rw [neg,neg_mul field,oneMul]

private theorem minus_coords (field : ConstantField F q) (a b : FormalSum F) (s : Tuple) :
    coordinates (minus a b) s = coordinates a s + -(coordinates b s) := by
  unfold minus coordinates; rw [total_append']
  have neg := measure_scale (-1:F) (fun e => if e.2=s then e.1 else 0)
    (fun c t => by by_cases e:t=s <;> simp [e,Arithmetic.mulZero]) b
  rw [neg,neg_mul field,oneMul]

private theorem minus_homogeneous (a b : FormalSum F) (ha : homogeneous w a)
    (hb : homogeneous w b) : homogeneous w (minus a b) := by
  intro z hz
  rcases List.mem_append.mp hz with hm | hm
  · exact ha z hm
  · obtain ⟨e,mem,rfl⟩ := List.mem_map.mp hm
    exact hb e mem

/-- Lemma 3.1. The row generators are the actual operator lifts in
fundamental_row. Both components are recorded at the same weight. -/
theorem lemma_3_1 (field : ConstantField F q) (rowLaw : CompletenessProof.LiftedRowIdentity F q)
    (tt : ∀ j, 0<j → TTPolynomialIndependent F q j) (hw : 0<w) (x : Bool × Tuple → F) :
    U q w x ↔ ∃ c : Rows F q w, ∀ s,
      x (false,s)=component L c s ∧ x (true,s)=component H c s := by
  constructor
  · rintro ⟨p,r,hp,hr,rel,rfl⟩
    obtain ⟨c,_,hc⟩ := degree_one_projection field (tt w hw) (rowLaw w hw) p r hp hr rel
    have ident := rows_identity c (fun e _ => rowLaw w hw e.2)
    have ep := evaluate_congr q (presentation L c) p ((coordinates_presentation L c).trans hc)
    change cleared q (evaluate q (presentation L c)) (evaluate q (presentation H c)) at ident
    rw [ep] at ident
    have he := equal_second field _ _ _ rel ident
    let rem := minus r (presentation H c)
    have hrem : homogeneous w rem := minus_homogeneous _ _ hr (homogeneous_rows field c).2
    have relation : Relation q w rem := ⟨hrem,fun n => by
      rw [show evaluate q rem n = _ from minus_eval field _ _ n,he,field.add_neg]⟩
    have bcp := ((CompletenessProof.theorem_1_10 q rowLaw tt field w hw rem hrem).mp relation)
    obtain ⟨d,dl,dh⟩ := BCPRows.bcp_in_H_ker_L q w field _ ⟨rem,bcp,rfl⟩
    refine ⟨c++d,fun s => ⟨?_,?_⟩⟩
    · change coordinates p s=_
      rw [component_append,dl,hc]; exact (Arithmetic.addZero _).symm
    · change coordinates r s=_
      rw [component_append,dh,show coordinates rem s=_ from minus_coords field _ _ s,
        coordinates_presentation]
      rw [Arithmetic.addComm (coordinates r s),←Arithmetic.addAssoc,field.add_neg,zeroAdd]
  · rintro ⟨c,eqn⟩
    obtain ⟨hl,hh⟩ := homogeneous_rows field c
    refine ⟨presentation L c,presentation H c,hl,hh,rows_identity c (fun e _ => rowLaw w hw e.2),?_⟩
    funext i
    rcases i with ⟨b,s⟩
    cases b
    · exact (congrFun (coordinates_presentation L c) s).trans (eqn s).1.symm
    · exact (congrFun (coordinates_presentation H c) s).trans (eqn s).2.symm

/-- The image of the projection in Corollary 3.2 is the full L-space. -/
theorem projection_image (field : ConstantField F q) (rowLaw : CompletenessProof.LiftedRowIdentity F q)
    (tt : ∀ j, 0<j → TTPolynomialIndependent F q j) (hw : 0<w) (v : Tuple → F) :
    (∃ x, U q w x ∧ ∀ s,x (false,s)=v s) ↔ ∃ c : Rows F q w,component L c=v := by
  constructor
  · rintro ⟨x,hx,eq⟩
    obtain ⟨c,ec⟩ := (lemma_3_1 field rowLaw tt hw x).mp hx
    exact ⟨c,funext (fun s => (ec s).1.symm.trans (eq s))⟩
  · rintro ⟨c,rfl⟩
    let x := fun i : Bool × Tuple => if i.1 then component H c i.2 else component L c i.2
    exact ⟨x,(lemma_3_1 field rowLaw tt hw x).mpr ⟨c,fun _ => ⟨rfl,rfl⟩⟩,fun _ => rfl⟩

end Megaera.FinalDegreeOne
