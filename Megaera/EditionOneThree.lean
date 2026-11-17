import Megaera.FinalFixedRanks
import Megaera.FinalQuotientSpaces
import Megaera.FinalQuotientRank
import Megaera.FinalCor32

/-! The revised proof of Theorem 3.3 identifies the consecutive quotients
of the first-entry filtration. The class of a lift depends only on its
head-n coordinates, so the inverse is independent of the chosen lift. -/
namespace Megaera.EditionOneThree
open Megaera.Finite Megaera.Paper Megaera.SectionThreeSpaces Megaera.FinalRankEngine
open Megaera.FinalFiltration Megaera.FinalLinearSpaces Megaera.FinalQuotientSpaces

universe u v z
variable {F : Type u} [Arithmetic F] [Neg F] {q w n : Nat}
variable {I : Type v} {J : Type z}

/-- Quotient by the next stage. Its defining equivalence is equality of
head-n coordinates; `same_class` identifies it with difference in that stage. -/
def atHead (stage : (I → F) → Prop) (prepend : J → I) : Setoid {x // stage x} :=
  sameProfile (fun x : {x // stage x} => fun j => x.val (prepend j))

/-- The two mutually inverse maps of p. 20, together with their action on
representatives and on linear combinations. -/
structure HeadIsomorphism (stage next : (I → F) → Prop) (lower : (J → F) → Prop)
    (prepend : J → I) (linear : Linear stage) where
  rho : Quotient (atHead stage prepend) → {y // lower y}
  tau : {y // lower y} → Quotient (atHead stage prepend)
  same_class (x y : {x // stage x}) :
    Quotient.mk (atHead stage prepend) x=Quotient.mk _ y ↔ next (fun i => x.val i+ -y.val i)
  rho_mk (x : {x // stage x}) (j : J) : (rho (Quotient.mk _ x)).val j=x.val (prepend j)
  rho_tau (y) : rho (tau y)=y
  tau_rho (c) : tau (rho c)=c
  rho_linear (x y : {x // stage x}) (a : F) (j : J) :
    (rho (Quotient.mk _ (addScaled linear x y a))).val j=
      (rho (Quotient.mk _ x)).val j+a*(rho (Quotient.mk _ y)).val j

private noncomputable def of_image_kernel (field : ConstantField F q)
    {stage next : (I → F) → Prop} {lower : (J → F) → Prop}
    (linear : Linear stage) (prepend : J → I)
    (im : ∀ y,lower y ↔ ∃ x,stage x ∧ ∀ j,x (prepend j)=y j)
    (ker : ∀ x,next x ↔ stage x ∧ ∀ j,x (prepend j)=0) :
    HeadIsomorphism stage next lower prepend linear := by
  let p (x : {x // stage x}) : {y // lower y} :=
    ⟨fun j => x.val (prepend j),(im _).mpr ⟨x.val,x.property,fun _ => rfl⟩⟩
  let rho := Quotient.lift (s:=atHead stage prepend) p (fun _ _ h => Subtype.ext h)
  have lift (y : {y // lower y}) := (im y.val).mp y.property
  let rep (y : {y // lower y}) : {x // stage x} :=
    ⟨Classical.choose (lift y),(Classical.choose_spec (lift y)).1⟩
  have section_eq (y : {y // lower y}) : p (rep y)=y :=
    Subtype.ext (funext ((Classical.choose_spec (lift y)).2))
  refine ⟨rho,fun y => Quotient.mk _ (rep y),?_,fun _ _ => rfl,section_eq,?_,fun _ _ _ _ => rfl⟩
  · intro x y
    have diff : stage (fun i => x.val i + -y.val i) := by
      simpa only [neg_mul field,oneMul] using
        linear.addScaled x.val y.val (-1:F) x.property y.property
    rw [ker]
    constructor
    · intro eq
      have h : (fun j => x.val (prepend j))=fun j => y.val (prepend j) := Quotient.exact eq
      exact ⟨diff,fun j => by change x.val (prepend j)+ -y.val (prepend j)=0
                              rw [congrFun h j,field.add_neg]⟩
    · rintro ⟨_,h⟩
      apply Quotient.sound
      apply funext
      intro j
      have e := congrArg (·+y.val (prepend j)) (h j)
      simpa only [Arithmetic.addAssoc,Arithmetic.addComm (-(y.val (prepend j))) _,field.add_neg,
        Arithmetic.addZero,zeroAdd] using e
  · intro c
    refine Quotient.inductionOn c ?_
    intro x
    apply Quotient.sound
    exact congrArg Subtype.val (section_eq (p x))

/-- At n=w the terminal stage is zero. The relation spaces in the rank
formula are extended by the zero space in weight zero. -/
def lowerSpace (V : Nat → (J → F) → Prop) (k : Nat) (y : J → F) : Prop :=
  if k=0 then ∀ j,y j=0 else V k y

omit [Neg F] in
private theorem zero_image (stage : (I → F) → Prop) (linear : Linear stage)
    (dim : HasDimension stage 0) (prepend : J → I) (y : J → F) :
    (∀ j,y j=0) ↔ ∃ x,stage x ∧ ∀ j,x (prepend j)=y j := by
  obtain ⟨_,_,basis⟩ := dim
  constructor
  · intro h; exact ⟨_,linear.zero,fun j => (h j).symm⟩
  · rintro ⟨x,h,e⟩ j
    obtain ⟨_,repr,_⟩ := basis x h
    simpa only [List.finRange_zero,total, e j] using repr (prepend j)

/-- R^Fix_(w,n)/R^Fix_(w,n+1) is linearly isomorphic to R_(w−n).
The inverse sends any lower-weight relation to the class of its B_(n)-lift. -/
noncomputable def theorem_3_3_R (field : ConstantField F q)
    (tt : ∀ j,0<j → TTSpanning.TTPolynomialIndependent F q j) (hn : 0<n) (hw : n≤w) :
    HeadIsomorphism (stageR q w n) (stageR q w (n+1))
      (lowerSpace (RelationVector (F:=F) q) (w-n)) (List.cons n) (stageR_linear n) := by
  apply of_image_kernel field (stageR_linear n) (List.cons n) _ (fun x => kernel_R n x hn)
  intro y
  by_cases e : n=w
  · subst n
    simp only [lowerSpace,Nat.sub_self,if_true]
    exact zero_image _ (stageR_linear w) (FinalFixedRanks.last_R hn) _ _
  · simp only [lowerSpace,if_neg (show w-n≠0 by omega)]
    exact FinalLiftR.image_R field (FinalBinary.lifted_row_identity field) tt hn (by omega) y

/-- The quotient isomorphism in the case V=U, with both coefficient columns
restricted at the same first entry. -/
noncomputable def theorem_3_3_U (field : ConstantField F q)
    (tt : ∀ j,0<j → TTSpanning.TTPolynomialIndependent F q j) (hn : 0<n) (hw : n≤w) :
    HeadIsomorphism (stageU q w n) (stageU q w (n+1))
      (lowerSpace (U (F:=F) q) (w-n)) (fun j : Bool × Tuple => (j.1,n::j.2)) (stageU_linear n) := by
  apply of_image_kernel field (stageU_linear n) _ _ (fun x => kernel_U n x hn)
  intro y
  by_cases e : n=w
  · subst n
    simp only [lowerSpace,Nat.sub_self,if_true]
    exact zero_image _ (stageU_linear w) (FinalFixedRanks.last_U field hn) _ _
  · simp only [lowerSpace,if_neg (show w-n≠0 by omega)]
    exact FinalLiftU.image_U field (FinalBinary.lifted_row_identity field) tt hn (by omega) y

private theorem rank_step (field : ConstantField F q)
    {stage next : (I → F) → Prop} {lower : (J → F) → Prop}
    {linear : Linear stage} {prepend : J → I}
    (iso : HeadIsomorphism stage next lower prepend linear)
    (ker : ∀ x,next x ↔ stage x ∧ ∀ j,x (prepend j)=0)
    {l r : Nat} (ld : HasDimension lower l) (rd : HasDimension next r) :
    HasDimension stage (l+r) := by
  apply split_basis field linear prepend lower next _ ker ld rd
  intro y
  constructor
  · intro hy
    obtain ⟨x,hx⟩ := Quotient.exists_rep (iso.tau ⟨y,hy⟩)
    have eq := (congrArg iso.rho hx).trans (iso.rho_tau ⟨y,hy⟩)
    exact ⟨x.val,x.property,fun j =>
      (iso.rho_mk x j).symm.trans (congrArg (fun z : {v // lower v} => z.val j) eq)⟩
  · rintro ⟨x,hx,out⟩
    have rep := (iso.rho (Quotient.mk _ ⟨x,hx⟩)).property
    exact (funext (fun j => (iso.rho_mk ⟨x,hx⟩ j).trans (out j))) ▸ rep

theorem rank_R (field : ConstantField F q)
    (tt : ∀ j,0<j → TTSpanning.TTPolynomialIndependent F q j) (d : Ranks F q) :
    ∀ i,d.rFix i=Dimension.previous d.r i := by
  apply FinalFixedRanks.filtration_rank field (stageR q) d.r d.rFix d.r_basis d.rFix_basis
    (fun _ => fixedR_linear) (fun _ => FinalFixedRanks.first_R) (fun _ => FinalFixedRanks.last_R)
  intro w n hn lt i j di dj
  apply rank_step field (theorem_3_3_R (w:=w) field tt hn (Nat.le_of_lt lt)) (fun x => kernel_R n x hn) _ dj
  have pos : lowerSpace (RelationVector (F:=F) q) (w-n)=RelationVector q (w-n) :=
    funext (fun _ => if_neg (by omega : ¬w-n=0))
  rw [pos]; exact di

theorem rank_U (field : ConstantField F q)
    (tt : ∀ j,0<j → TTSpanning.TTPolynomialIndependent F q j) (d : Ranks F q) :
    ∀ i,d.uFix i=Dimension.previous d.u i := by
  apply FinalFixedRanks.filtration_rank field (stageU q) d.u d.uFix d.u_basis d.uFix_basis
    (fun _ => fixedU_linear) (fun _ => FinalFixedRanks.first_U) (fun _ => FinalFixedRanks.last_U field)
  intro w n hn lt i j di dj
  apply rank_step field (theorem_3_3_U (w:=w) field tt hn (Nat.le_of_lt lt)) (fun x => kernel_U n x hn) _ dj
  have pos : lowerSpace (U (F:=F) q) (w-n)=U q (w-n) :=
    funext (fun _ => if_neg (by omega : ¬w-n=0))
  rw [pos]; exact di

/-- Equation (1.21) deduced through the successive quotient isomorphisms
proved in the revised Theorem 3.3. -/
theorem theorem_1_12 (tt : ∀ j,0<j → TTSpanning.TTPolynomialIndependent F q j) :
    Theorem_1_12 F q := by
  intro field
  let d := FinalRanks.ranks field
  exact dimension_from_spaces q d
    (FinalCor32.corollary_3_2 field (FinalBinary.lifted_row_identity field) tt d)
    (rank_U field tt d) (rank_R field tt d) (FinalQuotientRank.lemma_3_4 field tt d) field

end Megaera.EditionOneThree
