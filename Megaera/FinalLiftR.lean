import Megaera.FinalLinearSpaces
import Megaera.FinalBinaryProof

/-! Lift the head projection on the fixed constant-coefficient relation space
by prefixing each binary generator with B_(n). -/
namespace Megaera.FinalLiftR
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.Lift Megaera.SectionThreeSpaces
open Megaera.FinalFiltration Megaera.FinalLinearSpaces Megaera.FinalRankEngine Megaera.BCPRows
variable {F : Type u} [Arithmetic F] [Neg F] {q w : Nat}

omit [Neg F] in
theorem coord_map (g : Tuple → Tuple) (p : FormalSum F) (s : Tuple) :
    coordinates (p.map (fun e => (e.1,g e.2))) s =
      total (fun e : F × Tuple => if g e.2=s then e.1 else 0) p := by
  induction p with
  | nil => rfl
  | cons e p ih => exact congrArg ((if g e.2=s then e.1 else 0)+·) ih

private def raised (n : Nat) : Tuple → Tuple
  | [] => [n]
  | a::t => (n+a)::t

omit [Arithmetic F] [Neg F] in
private theorem b_single (n : Nat) (r : BinaryPair F) : liftPair (bOp [n] r) =
    r.1.map (fun e => (e.1,n::e.2)) ++ r.2.map (fun e => (e.1,raised n e.2)) ++
      r.2.map (fun e => (e.1,n::e.2)) := by
  have tri (p : FormalSum F) : expand (triangle [n]) p=p.map (fun e => (e.1,n::e.2)) := by
    induction p with
    | nil => rfl
    | cons e p ih => change _++expand _ p=_; rw [ih]; simp [triangle,quasiShuffle_nil_left]
  have mer (p : FormalSum F) : expand (diamond [n]) p=p.map (fun e => (e.1,raised n e.2)) := by
    induction p with
    | nil => rfl
    | cons e p ih =>
      change _++expand _ p=_; rw [ih]; cases e with | mk k t => cases t <;> simp [diamond,raised,quasiShuffle_nil_left]
  simp only [liftPair,bOp,tri,mer,List.append_nil]

omit [Neg F] in
private theorem b_tail (n : Nat) (r : BinaryPair F)
    (val : ∀ e ∈ r.2, Valid e.2 ∧ e.2≠[]) (s : Tuple) :
    coordinates (liftPair (bOp [n] r)) (n::s)=coordinates (liftPair r) s := by
  rw [b_single,coord_append,coord_append,coord_map,coord_map,coord_map]
  have z : total (fun e : F × Tuple => if raised n e.2=n::s then e.1 else 0) r.2=0 := by
    apply total_zero_of_members
    intro e he; apply if_neg
    cases h : e.2 with
    | nil => exact False.elim ((val e he).2 h)
    | cons a t =>
      have pos := (val e he).1 a (by simp [h])
      simp [raised]; omega
  rw [z,Arithmetic.addZero]; simp only [liftPair,coord_append,List.cons.injEq,true_and]; rfl

omit [Neg F] in
private theorem b_small (n : Nat) (r : BinaryPair F) (s : Tuple) (lt : s.headD 0<n) :
    coordinates (liftPair (bOp [n] r)) s=0 := by
  rw [b_single,coord_append,coord_append,coord_map,coord_map,coord_map]
  have pr (p : FormalSum F) : total (fun e : F × Tuple => if n::e.2=s then e.1 else 0) p=0 := by
    apply total_zero_of_members; intro e _; apply if_neg
    rintro rfl; simp at lt
  have me : total (fun e : F × Tuple => if raised n e.2=s then e.1 else 0) r.2=0 := by
    apply total_zero_of_members; intro e _; apply if_neg
    rintro rfl; cases h : e.2 <;> simp [h,raised] at lt <;> omega
  rw [pr,me,pr,Arithmetic.addZero,Arithmetic.addZero]

private theorem single (field : ConstantField F q) {n : Nat} (hn : 0<n) (h t s : Tuple)
    (vh : Valid h) (vt : Valid t) (vs : Valid s) (hs : s≠[])
    (wt : weight h+weight t+weight s+2*q=w) :
    ∃ x, stageR q (n+w) n x ∧ ∀ v,x (n::v)=coordinates (bcpGenerator (K:=F) q h t s) v := by
  let r := bStar h (cOp t (primitive (K:=F) q s))
  let z := bcpGenerator (K:=F) q (n::h) t s
  have qp := field.two_le
  have vnh : Valid (n::h) := List.forall_mem_cons.mpr ⟨hn,vh⟩
  have hom : homogeneous (n+w) z := by
    intro e he
    have hv := bcpGenerator_valid q field.two_le (n::h) t s vnh vt vs e he
    have hw := bcpGenerator_weight q (by omega) (n::h) t s e he
    exact ⟨hv,by simp only [weight] at hw; omega⟩
  have fixed : fixedLevels q z := by
    have hb := FinalBinary.generator_binary (F:=F) field (n::h) t s vs hs
    change Binary q ((bOp [n] r).1,[]) at hb
    apply (fixedLevels_iff_binary q z).mpr
    simpa [z,bcpGenerator,liftPair,bStar,bOp,r,List.append_assoc] using hb
  have ne (e : F × Tuple) (he : e∈z) : e.2≠[] := by
    have wh := (hom e he).2; intro heq; rw [heq] at wh; simp [weight] at wh; omega
  have rel : Relation q (n+w) z := ⟨hom,by
    have h := binary_lift q field.two_le (z,[]) ((fixedLevels_iff_binary q z).mp fixed)
      (by intro e he; simp only [List.append_nil] at he; exact ⟨(hom e he).1,ne e he⟩)
    simpa [liftPair] using h⟩
  refine ⟨coordinates z,⟨⟨z,rel,fixed,rfl⟩,fun v hv => b_small n r v hv⟩,?_⟩
  intro v
  apply b_tail n r _ v
  intro e he
  have mem : e∈bcpGenerator (K:=F) q h t s := List.mem_append_right r.1 he
  have hv := bcpGenerator_valid q qp h t s vh vt vs e mem
  have hw := bcpGenerator_weight q (by omega) h t s e mem
  exact ⟨hv,by intro heq; rw [heq] at hw; simp [weight] at hw; omega⟩

/-- The image of the head projection is all of R_(w−n). -/
theorem image_R (field : ConstantField F q) (law : CompletenessProof.LiftedRowIdentity F q)
    (tt : ∀ j,0<j → TTSpanning.TTPolynomialIndependent F q j) {n : Nat} (hn : 0<n) (lt : n<w)
    (y : Tuple → F) :
    RelationVector q (w-n) y ↔ ∃ x,stageR q w n x ∧ ∀ t,x (n::t)=y t := by
  constructor
  · rintro ⟨p,hp,rfl⟩
    obtain ⟨rows,good,rep⟩ := (CompletenessProof.theorem_1_10 q law tt field (w-n) (by omega) p hp.1).mp hp
    suffices lift : ∃ x,stageR q w n x ∧ ∀ t,x (n::t)=total (fun e : F × Tuple × Tuple × Tuple =>
        e.1*coordinates (bcpGenerator q e.2.1 e.2.2.1 e.2.2.2) t) rows by
      obtain ⟨x,h,e⟩ := lift; exact ⟨x,h,fun t => (e t).trans (rep t).symm⟩
    clear rep
    induction rows with
    | nil => exact ⟨_,(stageR_linear n).zero,fun _ => rfl⟩
    | cons e rows ih =>
      obtain ⟨z,hz,ez⟩ := ih (fun e he => good e (List.mem_cons_of_mem _ he))
      obtain ⟨vh,vt,vs,ne,wt⟩ := good e (by simp)
      obtain ⟨v,hv,ev⟩ := single field hn _ _ _ vh vt vs ne wt
      rw [Nat.add_sub_of_le (by omega : n≤w)] at hv
      refine ⟨_,(stageR_linear n).addScaled z v e.1 hz hv,fun t => ?_⟩
      change z (n::t)+e.1*v (n::t)=_+_; rw [ez,ev,Arithmetic.addComm]
  · rintro ⟨x,h,r⟩
    exact (funext r) ▸ restrict_R field hn lt x h

end Megaera.FinalLiftR
