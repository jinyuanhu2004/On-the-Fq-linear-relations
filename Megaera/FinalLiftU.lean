import Megaera.FinalLinearSpaces
import Megaera.FinalQuotient

namespace Megaera.FinalLiftU
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.Lift Megaera.SectionThreeSpaces
open Megaera.FinalFiltration Megaera.FinalLinearSpaces Megaera.BCPRows Megaera.Singletons
variable {F : Type u} [Arithmetic F] [Neg F] {q w : Nat}

/-- Adding n to the front of a marked row gives the old L-column at head n,
and the old H-column there. Only an empty left label creates an extra term,
which has first entry n+1. -/
private theorem prepend_rows (q n : Nat) (h t : Tuple) :
    L q (n::h) t = (L q h t).map (List.cons n) ∧
    H q (n::h) t = (if h=[] then (quasiShuffle [q-1] t).map (List.cons (n+1)) else []) ++
      (H q h t).map (List.cons n) := by
  constructor
  · simp [L,List.map_map,Function.comp_def]
  · cases h with
    | nil => simp [H,endings,incLast,concatenate,List.map_map,Function.comp_def]
    | cons a h =>
      simpa only [List.cons_ne_nil,if_false,List.nil_append] using
        PrimitiveRows.H_prepend_nonempty q [n] a h t

omit [Neg F] in
theorem shape (q n : Nat) (h t : Tuple) (b : Bool) :
    let op := if b then H else L
    (∀ s,coordinates (withCoeff (1:F) (op q (n::h) t)) (n::s)=
      coordinates (withCoeff (1:F) (op q h t)) s) ∧
    (∀ s : Tuple,s.headD 0<n → coordinates (withCoeff (1:F) (op q (n::h) t)) s=0) := by
  have prepend (a : Nat) (vs : List Tuple) (le : n≤a) (s : Tuple) (hs : s.headD 0<n) :
      coordinates (withCoeff (1:F) (vs.map (List.cons a))) s=0 := by
    rw [coeff_prepend]
    cases s with
    | nil => rfl
    | cons b s =>
      change b<n at hs
      simp [head,show a≠b by omega]
  obtain ⟨l,r⟩ := prepend_rows q n h t
  cases b with
  | false =>
    change (∀ _,coordinates _ _=_) ∧ _
    simp only [Bool.false_eq_true,if_false,l]
    exact ⟨fun s => by rw [coeff_prepend]; simp [head],prepend n _ (Nat.le_refl n)⟩
  | true =>
    simp only [if_true,r,coeff_append]
    by_cases eq : h=[]
    · simp only [eq,if_true]
      constructor
      · intro s; rw [coeff_prepend,coeff_prepend]; simp [head,zeroAdd]
      · intro s hs; rw [prepend (n+1) _ (by omega) s hs,prepend n _ (by omega) s hs,Arithmetic.addZero]
    · simp only [if_neg eq,withCoeff,List.map_nil,coordinates,total,zeroAdd]
      change (∀ s,coordinates (withCoeff (1:F) ((H q h t).map (List.cons n))) (n::s)=_) ∧ _
      exact ⟨fun s => by rw [coeff_prepend]; simp [head]; rfl,prepend n _ (Nat.le_refl n)⟩

private def vector (q : Nat) (h t : Tuple) (i : Bool × Tuple) : F :=
  coordinates (withCoeff 1 ((if i.1 then H else L) q h t)) i.2

private theorem single (field : ConstantField F q) (law : CompletenessProof.LiftedRowIdentity F q)
    {n : Nat} (hn : 0<n) (e : Row q w) :
    stageU q (n+w) n (vector (F:=F) q (n::e.val.1) e.val.2) := by
  let h := e.val.1
  let t := e.val.2
  have nh : Valid (n::h) := List.forall_mem_cons.mpr ⟨hn,e.property.1⟩
  have wt : weight (n::h)+weight t+q=n+w := by
    have := e.property.2.2; simp only [weight]; dsimp [h,t]; omega
  let E : Row q (n+w) := ⟨(n::h,t),nh,e.property.2.1,wt⟩
  have qp := field.two_le
  have hL : homogeneous (n+w) (withCoeff (1:F) (L q (n::h) t)) := by
    intro z hz; obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hz
    exact ⟨L_valid q (by omega) _ t nh e.property.2.1 v hv,by have := L_weight q (n::h) t v hv; dsimp; omega⟩
  have hH : homogeneous (n+w) (withCoeff (1:F) (H q (n::h) t)) := by
    intro z hz; obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hz
    exact ⟨H_valid q qp _ t nh e.property.2.1 v hv,by have := H_weight q (by omega) (n::h) t v hv; dsimp; omega⟩
  refine ⟨⟨_,_,hL,hH,law (n+w) (by omega) E,FinalQuotient.prefixed_row_fixed field n h t,?_⟩,
    fun b s hs => (shape (F:=F) q n h t b).2 s hs⟩
  funext ⟨b,s⟩; cases b <;> rfl

theorem image_U (field : ConstantField F q) (law : CompletenessProof.LiftedRowIdentity F q)
    (tt : ∀ j,0<j → TTSpanning.TTPolynomialIndependent F q j) {n : Nat} (hn : 0<n) (lt : n<w)
    (y : Bool × Tuple → F) :
    U q (w-n) y ↔ ∃ x,stageU q w n x ∧ ∀ i : Bool × Tuple,x (i.1,n::i.2)=y i := by
  constructor
  · intro hy
    obtain ⟨rows,rep⟩ := (FinalDegreeOne.lemma_3_1 field law tt (by omega) y).mp hy
    have lift (xs : Rows F q (w-n)) : ∃ x,stageU q w n x ∧ ∀ i : Bool × Tuple,
        x (i.1,n::i.2)=component (if i.1 then H else L) xs i.2 := by
      induction xs with
      | nil => exact ⟨_,(stageU_linear n).zero,fun _ => rfl⟩
      | cons e xs ih =>
        obtain ⟨z,hz,ez⟩ := ih
        have h := single field law hn e.2
        rw [Nat.add_sub_of_le (by omega : n≤w)] at h
        refine ⟨_,(stageU_linear n).addScaled z _ e.1 hz h,fun i => ?_⟩
        change z _+e.1*vector q _ _ _=_+_
        rw [ez i,show vector (F:=F) q (n::e.2.val.1) e.2.val.2 (i.1,n::i.2)=_ from
          (shape (F:=F) q n e.2.val.1 e.2.val.2 i.1).1 i.2,Arithmetic.addComm]; rfl
    obtain ⟨x,h,hx⟩ := lift rows
    refine ⟨x,h,fun ⟨b,t⟩ => ?_⟩
    rw [hx]; cases b
    · exact (rep t).1.symm
    · exact (rep t).2.symm
  · rintro ⟨x,h,r⟩
    exact (funext r) ▸ restrict_U field hn lt x h

end Megaera.FinalLiftU
