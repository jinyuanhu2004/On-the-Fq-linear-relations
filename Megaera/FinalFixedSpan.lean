import Megaera.FinalFixedRanks
import Megaera.FinalQuotientSpaces

/-! The spanning assertion in the proof of Lemma 3.4: fixed degree-one
relations are exactly the span of rows B*_h C_t(R₁) with h nonempty. -/
namespace Megaera.FinalFixedSpan
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.Lift Megaera.SectionThreeSpaces
open Megaera.FinalFiltration Megaera.FinalLinearSpaces Megaera.FinalRankEngine Megaera.RowEvaluation
variable {F : Type u} [Arithmetic F] [Neg F] {q w n : Nat}

def cols (c : Rows F q w) (i : Bool×Tuple) : F :=
  component (if i.1 then H else L) c i.2

def prefixed (c : Rows F q w) := ∀ z ∈ c, z.2.val.1≠[]

def span (q w : Nat) (x : Bool×Tuple→F) := ∃ c : Rows F q w, prefixed c ∧ cols c=x

omit [Neg F] in
private theorem linear : Linear (span (F:=F) q w) where
  zero := ⟨[],by simp [prefixed],rfl⟩
  addScaled := by
    rintro x y a ⟨c,hc,rfl⟩ ⟨r,hr,rfl⟩
    refine ⟨c++BCPRows.scaleRows a r,?_,?_⟩
    · intro e he
      rcases List.mem_append.mp he with h|h
      · exact hc e h
      · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp h; exact hr b hb
    · funext i; simp only [cols,component_append,BCPRows.scale_component]

private theorem fix (field : ConstantField F q) (hw : 0<w) (x : Bool×Tuple→F) (hx : span q w x) :
    fixedU q w x := by
  obtain ⟨c,h,rfl⟩ := hx
  have empty : FinalQuotientSpaces.tails c=[] := by
    induction c with
    | nil => rfl
    | cons z c ih =>
      simp only [FinalQuotientSpaces.tails,if_neg (h z (by simp))]
      exact ih (fun e he => h e (List.mem_cons_of_mem z he))
  obtain ⟨hl,hh⟩ := FinalDegreeOne.homogeneous_rows field c
  refine ⟨presentation L c,presentation H c,hl,hh,
    rows_identity c (fun e _ => FinalBinary.lifted_row_identity field w hw e.2),?_,?_⟩
  · intro d; apply (FinalBinaryCleared.cleared_iff field _ _).mp
    change FinalQuotient.defect q d d _ _=0
    rw [FinalQuotientSpaces.extract field,empty]
    change (0 : FinalBinaryLaurent.Laurent F)+FinalBinaryCleared.delta q*0=0
    rw [Arithmetic.mulZero,Arithmetic.addZero]
  · funext ⟨b,s⟩; cases b
    · exact congrFun (coordinates_presentation L c) s
    · exact congrFun (coordinates_presentation H c) s

private def prefixRows {m : Nat} (hn : 0<n) (c : Rows F q m) : Rows F q (n+m) :=
  c.map fun z => (z.1,⟨(n::z.2.val.1,z.2.val.2),List.forall_mem_cons.mpr ⟨hn,z.2.property.1⟩,
    z.2.property.2.1,by have h := z.2.property.2.2; change n+weight z.2.val.1+weight z.2.val.2+q=n+m; omega⟩)

private theorem frontLift (field : ConstantField F q) {m : Nat} (hn : 0<n) (c : Rows F q m) :
    ∃ x,span q (n+m) x ∧ stageU q (n+m) n x ∧ ∀ i : Bool×Tuple, x (i.1,n::i.2)=cols c i := by
  let r := prefixRows hn c
  have pr : prefixed r := by
    intro z hz; obtain ⟨e,_,rfl⟩ := List.mem_map.mp hz; simp
  have sp : span q (n+m) (cols r) := ⟨r,pr,rfl⟩
  have head (i : Bool×Tuple) : cols r (i.1,n::i.2)=cols c i := by
    clear sp pr; unfold cols component; unfold r prefixRows; clear r
    induction c with
    | nil => rfl
    | cons z c ih =>
      simp only [List.map_cons,total]
      rw [(FinalLiftU.shape (F:=F) q n z.2.val.1 z.2.val.2 i.1).1,ih]
  have low (b : Bool) (s : Tuple) (low : s.headD 0<n) : cols r (b,s)=0 := by
    apply total_zero_of_members; intro z hz
    obtain ⟨e,_,rfl⟩ := List.mem_map.mp hz
    change e.1*coordinates (withCoeff (1:F) ((if b then H else L) q (n::e.2.val.1) e.2.val.2)) s=0
    rw [(FinalLiftU.shape (F:=F) q n e.2.val.1 e.2.val.2 b).2 s low,Arithmetic.mulZero]
  exact ⟨_,sp,⟨fix field (by omega) _ sp,low⟩,head⟩

/-- The generator statement in the parenthesis following Lemma 3.4.
For the reverse direction eliminate first entries successively, choosing
all the lifts at that entry to be rows with one more B*-prefix. -/
theorem fixed_iff_prefixed (field : ConstantField F q)
    (tt : ∀ j,0<j→TTSpanning.TTPolynomialIndependent F q j) (hw : 0<w) (x : Bool×Tuple→F) :
    fixedU q w x ↔ span q w x := by
  refine ⟨?_,fix field hw x⟩
  have all (k n : Nat) (hn : 0<n) (sum : n+k=w) (y : Bool×Tuple→F) (stage : stageU q w n y) :
      span q w y := by
    induction k generalizing n y with
    | zero =>
      rw [Nat.add_zero] at sum; subst n
      obtain ⟨_,_,basis⟩ := FinalFixedRanks.last_U field hw
      obtain ⟨_,eq,_⟩ := basis y stage
      have z : y=(fun _ => 0) := funext fun i => by simpa only [List.finRange_zero,total] using eq i
      rw [z]; exact linear.zero
    | succ k ih =>
      let tail := fun i : Bool×Tuple => y (i.1,n::i.2)
      have hy : U q (w-n) tail := restrict_U field hn (by omega) y stage
      obtain ⟨c,hc⟩ := (FinalDegreeOne.lemma_3_1 field (FinalBinary.lifted_row_identity field) tt
        (by omega) tail).mp hy
      obtain ⟨z,sp,st,head⟩ := frontLift field hn c
      have ew : n+(w-n)=w := by omega
      rw [ew] at sp st
      have matchHead (i : Bool×Tuple) : z (i.1,n::i.2)=y (i.1,n::i.2) := by
        rw [head]; rcases i with ⟨b,t⟩; cases b
        · exact (hc t).1.symm
        · exact (hc t).2.symm
      let rem := fun i => y i+(-1:F)*z i
      have more : stageU q w (n+1) rem := (kernel_U n rem hn).mpr
        ⟨(stageU_linear n).addScaled y z (-1) stage st,fun i => by
          change y _+(-1:F)*z _=0
          rw [matchHead i,neg_mul field,oneMul,field.add_neg]⟩
      have sr := ih (n+1) (by omega) (by omega) rem more
      have sy := linear.addScaled rem z 1 sr sp
      have back : (fun i => rem i+(1:F)*z i)=y := by
        funext i
        simp only [rem,neg_mul field,oneMul,Arithmetic.addAssoc,
          show -(z i)+z i=0 by rw [Arithmetic.addComm,field.add_neg],Arithmetic.addZero]
      exact back ▸ sy
  intro fixed
  apply all (w-1) 1 (by decide) (by omega) x
  rw [FinalFixedRanks.first_U hw]; exact fixed

end Megaera.FinalFixedSpan
