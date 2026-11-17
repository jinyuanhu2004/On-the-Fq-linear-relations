import Megaera.FinalLiftU
import Megaera.FinalLiftR
import Megaera.FinalRanks
import Megaera.FinalBinaryRows

/-! Theorem 3.3, including the terminal projection and zero-dimensional
weight-zero convention in the rank sequences. -/
namespace Megaera.FinalFixedRanks
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.Lift Megaera.SectionThreeSpaces
open Megaera.FinalFiltration Megaera.FinalLinearSpaces Megaera.FinalRankEngine
variable {F : Type u} [Arithmetic F] [Neg F] {q w : Nat}

omit [Neg F] in
private theorem outside (p : FormalSum F) (hp : homogeneous w p) (s : Tuple)
    (h : ¬(Valid s ∧ weight s=w)) : coordinates p s=0 := by
  apply total_zero_of_members; intro e he; apply if_neg
  intro eq; exact h (eq ▸ hp e he)

private theorem small (hw : 0<w) (s : Tuple) (hs : s.headD 0<1) : ¬(Valid s ∧ weight s=w) := by
  rintro ⟨v,h⟩
  cases s with
  | nil => simp [weight] at h; omega
  | cons a s => change a<1 at hs; have := v a (by simp); omega

private theorem large (hw : 0<w) (s : Tuple) (hs : w≤s.headD 0) (ne : s≠[w]) :
    ¬(Valid s ∧ weight s=w) := by
  rintro ⟨v,h⟩
  cases s with
  | nil => simp [weight] at h; omega
  | cons a s =>
    change w≤a at hs; change a+weight s=w at h
    cases s with
    | nil => simp [weight] at h; exact ne (by rw [h])
    | cons b s => have := v b (by simp); change a+(b+weight s)=w at h; omega

theorem first_R (hw : 0<w) : stageR (F:=F) q w 1=fixedR q w := by
  funext x; apply propext; constructor
  · exact And.left
  · intro h; refine ⟨h,?_⟩; obtain ⟨p,⟨hp,_⟩,_,rfl⟩ := h
    exact fun s hs => outside p hp s (small hw s hs)

theorem first_U (hw : 0<w) : stageU (F:=F) q w 1=fixedU q w := by
  funext x; apply propext; constructor
  · exact And.left
  · intro h; refine ⟨h,?_⟩; obtain ⟨p,r,hp,hr,_,_,rfl⟩ := h
    intro b s hs; cases b
    · exact outside p hp s (small hw s hs)
    · exact outside r hr s (small hw s hs)

omit [Neg F] in
private theorem unit_pow (a : Nat) : seriesPow (unitSeries (F:=F)) a=unitSeries := by
  induction a with
  | zero => rfl
  | succ a ih => rw [seriesPow,ih,FinalBinarySeries.product_unit]

/-- At degree zero and positive homogeneous weight only the one-part tuple survives. -/
private theorem at_zero (q : Nat) (hw : 0<w) (p : FormalSum F) (hp : homogeneous w p) :
    valueAt (degree q 0) p=fun j => if j=0 then coordinates p [w] else 0 := by
  funext j; induction p with
  | nil => simp [coordinates,valueAt,total]
  | cons e p ih =>
    have hv := hp e (by simp)
    have tail := ih (fun z hz => hp z (List.mem_cons_of_mem _ hz))
    have term : degree (F:=F) q 0 e.2 j=if e.2=[w] ∧ j=0 then 1 else 0 := by
      cases eq : e.2 with
      | nil => rw [eq] at hv; simp [weight] at hv; omega
      | cons a s =>
        cases s with
        | nil =>
          have aw : a=w := by simpa [eq,weight] using hv.2
          simp [aw,degree,exactLevel,inverseDenom,unit_pow,FinalBinarySeries.product_unit,trunc,unitSeries]
        | cons b t =>
          simp [degree,exactLevel,inverseDenom,unit_pow,FinalBinarySeries.product_unit,trunc]
    change e.1*degree q 0 e.2 j+valueAt (degree q 0) p j=
      if j=0 then (if e.2=[w] then e.1 else 0)+coordinates p [w] else 0
    rw [term,tail]
    by_cases h : j=0 <;> by_cases k : e.2=[w] <;>
      simp only [h,k,true_and,false_and,and_true,and_false,if_true,if_false,
        Arithmetic.mulZero,Arithmetic.addZero,Arithmetic.mulOne]

theorem last_R (hw : 0<w) : HasDimension (stageR (F:=F) q w w) 0 := by
  apply dimension_zero (stageR_linear w).zero
  rintro x ⟨⟨p,⟨hp,_⟩,fixed,rfl⟩,cut⟩ s
  by_cases lt : s.headD 0<w
  · exact cut s lt
  · by_cases eq : s=[w]
    · subst s; have h := fixed 0 0; rw [at_zero q hw p hp] at h; exact h
    · exact outside p hp s (large hw s (by omega) eq)

theorem last_U (field : ConstantField F q) (hw : 0<w) : HasDimension (stageU (F:=F) q w w) 0 := by
  apply dimension_zero (stageU_linear w).zero
  rintro x ⟨⟨p,r,hp,hr,_,fixed,rfl⟩,cut⟩ ⟨b,s⟩
  by_cases lt : s.headD 0<w
  · exact cut b s lt
  · by_cases eq : s=[w]
    · subst s; have z := fixed 0
      rw [at_zero q hw p hp,at_zero q hw r hr] at z
      have both := (cleared_scalars q field.two_le _ _).mp z
      cases b
      · exact both.1
      · exact both.2
    · cases b
      · exact outside p hp s (large hw s (by omega) eq)
      · exact outside r hr s (large hw s (by omega) eq)

private theorem extra (f : Dimension.Coeff) (k : Nat) (i : Int) :
    Dimension.window (k+1) f i=Dimension.window k f i+f (i-1-k) := by
  induction k generalizing i with
  | zero => simp [Dimension.window]
  | succ k ih =>
    change f (i-1)+Dimension.window (k+1) f (i-1) =
      (f (i-1)+Dimension.window k f (i-1))+f (i-1-(k+1:Nat))
    rw [ih]
    rw [Int.add_assoc,show i-1-1-k=i-1-(k+1:Nat) by omega]

/-- Dimension of a finite filtration whose head quotients are the given
lower-weight spaces. Weight zero contributes no summand. -/
theorem filtration_rank {I : Type v} (field : ConstantField F q)
    {fixed base : Nat → (I → F) → Prop} (S : Nat → Nat → (I → F) → Prop)
    (r f : Dimension.Coeff) (rb : IsRankSequence base r) (fb : IsRankSequence fixed f)
    (lin : ∀ w,Linear (fixed w)) (first : ∀ w,0<w → S w 1=fixed w)
    (last : ∀ w,0<w → HasDimension (S w w) 0)
    (step : ∀ w n,0<n → n<w → ∀ i j,HasDimension (base (w-n)) i →
      HasDimension (S w (n+1)) j → HasDimension (S w n) (i+j)) :
    ∀ i, f i=Dimension.previous r i := by
  intro i
  by_cases pos : 0<i
  · let w := i.toNat
    have iw : (w:Int)=i := Int.toNat_of_nonneg (by omega)
    have wp : 0<w := by omega
    have stages (k n : Nat) (np : 0<n) (eq : n+k=w) :
        ∃ m,HasDimension (S w n) m ∧ (m:Int)=Dimension.window k r ((k:Int)+1) := by
      induction k generalizing n with
      | zero =>
        rw [Nat.add_zero] at eq
        exact ⟨0,eq ▸ last n np,rfl⟩
      | succ k ih =>
        obtain ⟨m,hm,em⟩ := ih (n+1) (by omega) (by omega)
        have nr := rb.2 (k+1) (by omega)
        have e : w-n=k+1 := by omega
        refine ⟨_,step w n np (by omega) _ _ (e ▸ nr.2) hm,?_⟩
        change (((r ↑(w-n)).toNat+m:Nat):Int)=_
        rw [e,Int.natCast_add,Int.toNat_of_nonneg nr.1,em]
        simp only [Dimension.window,Int.natCast_succ,Int.add_sub_cancel]
    obtain ⟨m,hm,em⟩ := stages (w-1) 1 (by omega) (by omega)
    rw [first w wp] at hm
    have fr := fb.2 w wp
    have same := dimension_unique field (lin w) fr.2 hm
    have cast : (f i).toNat=m := by rwa [iw] at same
    have fn := fr.1; rw [iw] at fn
    have ep := extra r (w-1) i
    have e1 : w-1+1=w := by omega
    have e2 : i-1-(w-1:Nat)=0 := by omega
    rw [e1,e2,rb.1 0 (by omega),Int.add_zero] at ep
    change f i=Dimension.window w r i
    rw [show ((w-1:Nat):Int)+1=i by omega] at em
    rw [ep,←em,←cast,Int.toNat_of_nonneg fn]
  · rw [fb.1 i (by omega)]
    simp [Dimension.previous,show i.toNat=0 by omega,Dimension.window]

theorem theorem_3_3_R (field : ConstantField F q)
    (tt : ∀ j,0<j → TTSpanning.TTPolynomialIndependent F q j) (d : Ranks F q) :
    ∀ i,d.rFix i=Dimension.previous d.r i := by
  apply filtration_rank field (stageR q) d.r d.rFix d.r_basis d.rFix_basis
    (fun _ => fixedR_linear) (fun _ => first_R) (fun _ => last_R)
  intro w n hn lt i j di dj
  exact split_basis field (stageR_linear n) (List.cons n) _ _ (FinalLiftR.image_R field
    (FinalBinary.lifted_row_identity field) tt hn lt) (fun x => kernel_R n x hn) di dj

theorem theorem_3_3_U (field : ConstantField F q)
    (tt : ∀ j,0<j → TTSpanning.TTPolynomialIndependent F q j) (d : Ranks F q) :
    ∀ i,d.uFix i=Dimension.previous d.u i := by
  apply filtration_rank field (stageU q) d.u d.uFix d.u_basis d.uFix_basis
    (fun _ => fixedU_linear) (fun _ => first_U) (fun _ => last_U field)
  intro w n hn lt i j di dj
  exact split_basis field (stageU_linear n) (fun b : Bool × Tuple => (b.1,n::b.2)) _ _
    (FinalLiftU.image_U field (FinalBinary.lifted_row_identity field) tt hn lt)
    (fun x => kernel_U n x hn) di dj

end Megaera.FinalFixedRanks
