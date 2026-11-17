import Megaera.FinalQuotient
import Megaera.FinalLinearSpaces
import Megaera.FinalBinaryRows

/-! The domain and target in the quotient isomorphism of Lemma 3.4. -/
namespace Megaera.FinalQuotientSpaces
open Megaera.Carlitz Megaera.Finite Megaera.Paper Megaera.Lift Megaera.SectionThreeSpaces
open Megaera.FinalBinarySeries Megaera.FinalBinaryTransport Megaera.FinalBinaryLaurent
open Megaera.FinalBinaryCarlitz Megaera.FinalBinaryCleared Megaera.FinalFixedKernel
open Megaera.FinalQuotient Megaera.FinalLinearSpaces Megaera.RowEvaluation
variable {F : Type u} [Arithmetic F] [Neg F] {q w : Nat}
local instance : Arithmetic (Series F) := seriesArithmetic

def S (w : Nat) (x : Tuple → F) : Prop := ∃ p : FormalSum F, homogeneous w p ∧ coordinates p=x

private noncomputable def repr (w : Nat) (x : Tuple → F) : FormalSum F := by
  classical exact if h : S w x then Classical.choose h else []

omit [Neg F] in
private theorem repr_spec {x : Tuple → F} (h : S w x) :
    homogeneous w (repr w x) ∧ coordinates (repr w x)=x := by
  classical simpa only [repr,dif_pos h] using Classical.choose_spec h

noncomputable def tailProfile (q w : Nat) (x : Tuple → F) (d : Int) : Laurent F :=
  defect q d d (expand (L q []) (repr w x)) (expand (H q []) (repr w x))

noncomputable def rowProfile (q w : Nat) (x : Bool × Tuple → F) (d : Int) : Laurent F :=
  defect q d d (repr w (fun s => x (false,s))) (repr w (fun s => x (true,s)))

omit [Neg F] in
private theorem ev_congr (f : Tuple → Series F) (p r : FormalSum F)
    (e : coordinates p=coordinates r) : valueAt f p=valueAt f r :=
  funext (fun n => linear_form_congr (fun t => f t n) p r e)

omit [Neg F] in
private theorem expanded (op : Tuple → List Tuple) (f : Tuple → Series F) (p : FormalSum F) :
    valueAt f (expand op p)=valueAt (fun s => total f (op s)) p := by
  simp only [value_weighted]
  induction p with
  | nil => rfl
  | cons z p ih =>
    change total _ (withCoeff z.1 _++expand op p)=_+_
    rw [total_append',sum_terms,ih]

private theorem tail_repr (p : FormalSum F) (hp : homogeneous w p) (d : Int) :
    tailProfile q w (coordinates p) d=defect q d d (expand (L q []) p) (expand (H q []) p) := by
  have eq := (repr_spec (show S w (coordinates p) from ⟨p,hp,rfl⟩)).2
  simp only [tailProfile,defect,expanded]
  rw [ev_congr (fun s => total (degree q d) (L q [] s)) _ p eq, ev_congr (fun s => total (degree q d) (H q [] s)) _ p eq]

private theorem row_repr (p r : FormalSum F) (hp : homogeneous w p) (hr : homogeneous w r) (d : Int) :
    rowProfile q w (pairCoordinates p r) d=defect q d d p r := by
  have ep := (repr_spec (show S w (coordinates p) from ⟨p,hp,rfl⟩)).2
  have er := (repr_spec (show S w (coordinates r) from ⟨r,hr,rfl⟩)).2
  change defect q d d (repr w (coordinates p)) (repr w (coordinates r))=_
  unfold defect
  rw [ev_congr (degree q d) _ p ep,ev_congr (degree q d) _ r er]

/-- A row presentation contributes only its unprefixed rows to the class. -/
def tails : Rows F q w → FormalSum F
  | [] => []
  | (a,r)::c => if r.val.1=[] then (a,r.val.2)::tails c else tails c

omit [Arithmetic F] [Neg F] in
private theorem tails_hom (c : Rows F q (q+w)) : homogeneous w (tails c) := by
  induction c with
  | nil => simp [homogeneous,tails]
  | cons z c ih =>
    obtain ⟨a,r⟩ := z
    have h := r.property
    by_cases eq : r.val.1=[]
    · simp only [tails,if_pos eq]
      intro e he
      rcases List.mem_cons.mp he with rfl|hm
      · refine ⟨h.2.1,?_⟩
        have wt := h.2.2
        change weight r.val.2=w
        simp only [eq,weight,Nat.zero_add] at wt; omega
      · exact ih e hm
    · simpa only [tails,if_neg eq] using ih

theorem extract (field : ConstantField F q) (c : Rows F q w) (d : Int) :
    defect q d d (presentation L c) (presentation H c)=
    defect q d d (expand (L q []) (tails c)) (expand (H q []) (tails c)) := by
  induction c with
  | nil => rfl
  | cons z c ih =>
    obtain ⟨a,r⟩ := z
    change defect q d d (withCoeff a (L q r.val.1 r.val.2)++presentation L c)
      (withCoeff a (H q r.val.1 r.val.2)++presentation H c)=_
    cases e : r.val.1 with
    | nil =>
      simp only [tails,e,if_true]
      change _=defect q d d (withCoeff a (L q [] r.val.2)++expand (L q []) (tails c))
        (withCoeff a (H q [] r.val.2)++expand (H q []) (tails c))
      rw [FinalQuotient.split_defect,FinalQuotient.split_defect,ih]
    | cons b t =>
      simp only [tails,e,List.cons_ne_nil,if_false]
      rw [FinalQuotient.split_defect,prefixed_row field,Arithmetic.mulZero,zeroAdd,ih]

private def tailRows (p : FormalSum F) (hp : homogeneous w p) : Rows F q (q+w) :=
  p.attach.map fun z =>
    (z.val.1,⟨([],z.val.2),fun _ h => by simp at h,(hp z.val z.property).1,
      by simp [weight,(hp z.val z.property).2,Nat.add_comm]⟩)

omit [Arithmetic F] [Neg F] in
private theorem tailRows_presents (op : Nat → Tuple → Tuple → List Tuple)
    (p : FormalSum F) (hp : homogeneous w p) :
    presentation op (tailRows (q:=q) p hp)=expand (op q []) p := by
  simp [presentation,tailRows,expand,withCoeff,List.flatMap_map]
  rw [←List.flatMap_map (f:=Subtype.val) (g:=fun z : F × Tuple => (op q [] z.2).map (fun t => (z.1,t))),List.attach_map_subtype_val]

/-- Both quotient presentations have precisely the same degree profiles. -/
theorem same_profiles (field : ConstantField F q)
    (tt : ∀ j, 0<j → TTSpanning.TTPolynomialIndependent F q j) :
    (∀ x : Tuple→F,S w x → ∃ y,U q (q+w) y ∧ tailProfile q w x=rowProfile q (q+w) y) ∧
    (∀ y : Bool×Tuple→F,U q (q+w) y → ∃ x,S w x ∧ tailProfile q w x=rowProfile q (q+w) y) := by
  have pos : 0<q+w := by have := field.two_le; omega
  have law := FinalBinary.lifted_row_identity field
  constructor
  · rintro x ⟨p,hp,rfl⟩
    let c := tailRows (q:=q) p hp
    have hL := tailRows_presents (q:=q) L p hp
    have hH := tailRows_presents (q:=q) H p hp
    let y := pairCoordinates (presentation L c) (presentation H c)
    have hy : U q (q+w) y := (FinalDegreeOne.lemma_3_1 field law tt pos y).mpr
      ⟨c,fun s => ⟨congrFun (coordinates_presentation L c) s,congrFun (coordinates_presentation H c) s⟩⟩
    refine ⟨y,hy,funext (fun d => ?_)⟩
    obtain ⟨hl,hh⟩ := FinalDegreeOne.homogeneous_rows field c
    change tailProfile q w (coordinates p) d=rowProfile q (q+w) (pairCoordinates _ _) d
    rw [tail_repr p hp,row_repr _ _ hl hh]
    change _=defect q d d (presentation L (tailRows p hp)) (presentation H (tailRows p hp))
    rw [hL,hH]
  · intro y hy
    obtain ⟨c,cs⟩ := (FinalDegreeOne.lemma_3_1 field law tt pos y).mp hy
    have cy : pairCoordinates (presentation L c) (presentation H c)=y := by
      funext ⟨b,t⟩
      cases b
      · exact (congrFun (coordinates_presentation L c) t).trans (cs t).1.symm
      · exact (congrFun (coordinates_presentation H c) t).trans (cs t).2.symm
    obtain ⟨hl,hh⟩ := FinalDegreeOne.homogeneous_rows field c
    refine ⟨coordinates (tails c),⟨_,tails_hom c,rfl⟩,funext (fun d => ?_)⟩
    rw [←cy,row_repr _ _ hl hh,tail_repr _ (tails_hom c)]
    exact (extract field c d).symm

private theorem val_sub (field : ConstantField F q) (f : Tuple→Series F) (p r : FormalSum F) :
    mk 0 (valueAt f (combine (-1) p r)) = mk 0 (valueAt f p) + -mk 0 (valueAt f r) := by
  rw [neg_mk field,←embed_add]; apply congrArg (mk 0)
  funext j
  change valueAt f (combine (-1) p r) j=valueAt f p j+ -(valueAt f r j)
  rw [combine_val,neg_mul field,oneMul]


private theorem neg_times (field : ConstantField F q) (x y : Laurent F) :
    x*(-y)= -(x*y) := by
  apply add_cancel field (x*y)
  rw [←Arithmetic.distrib,negative_sum field,Arithmetic.mulZero,negative_sum field]

private theorem compare (field : ConstantField F q) (a b c e : Laurent F) :
    (a+ -c)+delta q*(b+ -e)=0 ↔ a+delta q*b=c+delta q*e := by
  have shuffle : ((a+ -c)+delta q*(b+ -e))+(c+delta q*e)=a+delta q*b := by
    rw [Arithmetic.distrib,neg_times field]
    letI : Std.Associative (α:=Laurent F) (·+·) := ⟨Arithmetic.addAssoc⟩
    letI : Std.Commutative (α:=Laurent F) (·+·) := ⟨Arithmetic.addComm⟩
    calc
      _ = (a+delta q*b)+((c+ -c)+((delta q*e)+ -(delta q*e))) := by
        ac_nf
        rw [Arithmetic.addComm (delta q*e) (delta q*b)]
      _ = _ := by rw [negative_sum field,negative_sum field,Arithmetic.addZero,Arithmetic.addZero]
  constructor
  · intro hz; rw [←shuffle,hz,zeroAdd]
  · intro eq
    apply add_cancel field (c+delta q*e)
    rw [Arithmetic.addZero,Arithmetic.addComm (c+delta q*e),shuffle,eq]

private theorem relation_of_fixed (field : ConstantField F q) (p : FormalSum F)
    (hp : homogeneous w p) (h : fixedLevels q p) : Relation q w p := by
  refine ⟨hp,?_⟩
  by_cases z : w=0
  · intro j; apply total_zero_of_members
    intro e he
    obtain ⟨v,wt⟩ := hp e he
    cases le : e.2 with
    | nil => simp [le,li,Arithmetic.mulZero]
    | cons a t =>
      have ha := v a (by simp [le])
      simp [le,weight,z] at wt; omega
  · have supp (e) (he : e∈p) : Valid e.2 ∧ e.2≠[] := by
      obtain ⟨hv,hw⟩ := hp e he
      exact ⟨hv,fun t => z ((congrArg weight t).symm.trans hw).symm⟩
    have hb := binary_lift q field.two_le (p,[]) ((fixedLevels_iff_binary q p).mp h) (by simpa [liftPair] using supp)
    simpa [liftPair] using hb

theorem tail_kernel (field : ConstantField F q) (x y : Tuple→F) (hx : S w x) (hy : S w y) :
    tailProfile q w x=tailProfile q w y ↔ fixedR q w (fun i => x i+ -(y i)) := by
  obtain ⟨p,hp,rfl⟩ := hx
  obtain ⟨r,hr,rfl⟩ := hy
  let t := combine (-1:F) p r
  have hom : homogeneous w t := combine_hom _ _ _ hp hr
  have coord : coordinates t=(fun i => coordinates p i+ -(coordinates r i)) :=
    funext (fun i => (combine_coord _ _ _ i).trans (by rw [neg_mul field,oneMul]))
  have eqF (d : Int) : defect q d d (expand (L q []) t) (expand (H q []) t)=0 ↔
      tailProfile q w (coordinates p) d=tailProfile q w (coordinates r) d := by
    rw [tail_repr p hp,tail_repr r hr]
    simp only [defect,expanded,t,val_sub field]
    exact compare field .. 
  constructor
  · intro e
    have hz := (fixed_image_iff field t hom).mp (fun d => (eqF d).mpr (congrFun e d))
    exact ⟨t,relation_of_fixed field _ hom hz,hz,coord⟩
  · rintro ⟨z,_,hz,cz⟩
    have hzt : fixedLevels q t := fun d n =>
      (congrFun (ev_congr _ t z (coord.trans cz.symm)) n).trans (hz d n)
    exact funext (fun d => (eqF d).mp ((fixed_image_iff field t hom).mpr hzt d))

private theorem pair_sub (field : ConstantField F q) (p r P R : FormalSum F) :
    pairCoordinates (combine (-1) p P) (combine (-1) r R) =
    fun i => pairCoordinates p r i+ -(pairCoordinates P R i) := by
  funext ⟨b,s⟩
  cases b <;> simp only [pairCoordinates,Bool.false_eq_true,if_false,if_true,combine_coord,neg_mul field,oneMul]

theorem row_kernel (field : ConstantField F q) (x y : Bool×Tuple→F) (hx : U q w x) (hy : U q w y) :
    rowProfile q w x=rowProfile q w y ↔ fixedU q w (fun i => x i+ -(y i)) := by
  obtain ⟨p,r,hp,hr,ev,rfl⟩ := hx
  obtain ⟨P,R,hP,hR,eV,rfl⟩ := hy
  let a := combine (-1:F) p P
  let b := combine (-1:F) r R
  have ha : homogeneous w a := combine_hom _ _ _ hp hP
  have hb : homogeneous w b := combine_hom _ _ _ hr hR
  have co := pair_sub field p r P R
  have eqF (d : Int) : cleared q (valueAt (degree q d) a) (valueAt (degree q d) b) ↔
      rowProfile q w (pairCoordinates p r) d=rowProfile q w (pairCoordinates P R) d := by
    rw [row_repr p r hp hr,row_repr P R hP hR,←cleared_iff field]
    simp only [defect,a,b,val_sub field]
    exact compare field ..
  constructor
  · intro e
    refine ⟨a,b,ha,hb,?_,fun d => (eqF d).mpr (congrFun e d),co⟩
    apply (cleared_iff field _ _).mp
    change mk 0 (valueAt (li q) (combine (-1) p P))+delta q*mk 0 (valueAt (li q) (combine (-1) r R))=0
    rw [val_sub field,val_sub field,compare field]
    exact ((cleared_iff field _ _).mpr ev).trans ((cleared_iff field _ _).mpr eV).symm
  · rintro ⟨a',b',_,_,_,fixed,c⟩
    have cd : pairCoordinates a b=pairCoordinates a' b' := co.trans c.symm
    have ca : coordinates a=coordinates a' := funext (fun s => congrFun cd (false,s))
    have cb : coordinates b=coordinates b' := funext (fun s => congrFun cd (true,s))
    apply funext; intro d; apply (eqF d).mp
    rw [ev_congr _ a a' ca,ev_congr _ b b' cb]; exact fixed d

/-- Equivalence modulo the kernel of the displayed profile. -/
def sameProfile {A : Type v} {B : Type z} (f : A→B) : Setoid A where
  r a b := f a=f b
  iseqv := ⟨fun _ => rfl,Eq.symm,Eq.trans⟩

/-- Lemma 3.4. The source and target are quotients of the actual spaces.
The preceding kernel theorems identify their equivalence relations with
differences in R^Fix and U^Fix. The map sends every tail to the class
of its unprefixed lift, characterized by its degree profile. -/
theorem quotient_isomorphism (field : ConstantField F q)
    (tt : ∀ j, 0<j → TTSpanning.TTPolynomialIndependent F q j) :
    let src := sameProfile (fun x : {a // S (F:=F) w a} => tailProfile q w x.val)
    let dst := sameProfile (fun y : {b // U (F:=F) q (q+w) b} => rowProfile q (q+w) y.val)
    ∃ g : Quotient src → Quotient dst,
      (∀ a b, tailProfile q w a.val=rowProfile q (q+w) b.val →
        g (Quotient.mk src a)=Quotient.mk dst b) ∧
      (∀ x y,g x=g y→x=y) ∧ (∀ y,∃ x,g x=y) := by
  classical
  dsimp only
  obtain ⟨fw,bw⟩ := same_profiles (w:=w) field tt
  let f (x : {a // S (F:=F) w a}) : {b // U (F:=F) q (q+w) b} :=
    ⟨Classical.choose (fw x.val x.property),(Classical.choose_spec (fw x.val x.property)).1⟩
  have f_equation (x) : tailProfile q w x.val=rowProfile q (q+w) (f x).val :=
    (Classical.choose_spec (fw x.val x.property)).2
  obtain ⟨g,on_repr,inj,onto⟩ := SectionThree.quotient_fundamental
    (sameProfile (fun x : {a // S (F:=F) w a} => tailProfile q w x.val))
    (sameProfile (fun y : {b // U (F:=F) q (q+w) b} => rowProfile q (q+w) y.val)) f
    (fun a b => by change tailProfile q w a.val=tailProfile q w b.val ↔ _; rw [f_equation a,f_equation b]; rfl)
    (fun b => by obtain ⟨a,ha,e⟩ := bw b.val b.property; exact ⟨⟨a,ha⟩,(f_equation ⟨a,ha⟩).symm.trans e⟩)
  exact ⟨g,fun a b eq => (on_repr a).trans (Quotient.sound ((f_equation a).symm.trans eq)),inj,onto⟩

omit [Neg F] in
private theorem mk_combine (f : Tuple→Series F) (p r : FormalSum F) (a : F) :
    mk 0 (valueAt f (combine a p r))=mk 0 (valueAt f p)+scalar a*mk 0 (valueAt f r) := by
  change _=mk 0 _ + mk 0 (constant a)*mk 0 _
  rw [←embed_mul,←embed_add]; apply congrArg (mk 0)
  funext j
  change _=valueAt f p j+product (constant a) (valueAt f r) j
  rw [constant_product,combine_val]

omit [Neg F] in
private theorem distribute_profile (A B C D c k : Laurent F) :
    (A+c*C)+k*(B+c*D)=(A+k*B)+c*(C+k*D) := by
  rw [Arithmetic.distrib,Arithmetic.distrib]
  have e : k*(c*D)=c*(k*D) := by rw [←Arithmetic.mulAssoc,Arithmetic.mulComm k c,Arithmetic.mulAssoc]
  rw [e]
  letI : Std.Associative (α:=Laurent F) (·+·) := ⟨Arithmetic.addAssoc⟩
  letI : Std.Commutative (α:=Laurent F) (·+·) := ⟨Arithmetic.addComm⟩
  ac_nf; apply congrArg (A+·); rw [←Arithmetic.addAssoc,Arithmetic.addComm]

theorem tail_profile_linear {x y : Tuple→F} (hx : S w x) (hy : S w y) (a : F) (d : Int) :
    tailProfile q w (fun i => x i+a*y i) d=tailProfile q w x d+scalar a *tailProfile q w y d := by
  obtain ⟨p,hp,rfl⟩ := hx
  obtain ⟨r,hr,rfl⟩ := hy
  rw [←funext (combine_coord a p r),tail_repr _ (combine_hom a p r hp hr),tail_repr _ hp,tail_repr _ hr]
  simp only [defect,expanded,mk_combine]
  exact distribute_profile ..

theorem row_profile_linear {x y : Bool×Tuple→F} (hx : U q w x) (hy : U q w y) (a : F) (d : Int) :
    rowProfile q w (fun i => x i+a*y i) d=rowProfile q w x d+scalar a *rowProfile q w y d := by
  obtain ⟨p,r,hp,hr,_,rfl⟩ := hx
  obtain ⟨P,R,hP,hR,_,rfl⟩ := hy
  have comb : pairCoordinates (combine a p P) (combine a r R)=
      fun i => pairCoordinates p r i+a*pairCoordinates P R i := by
    funext ⟨b,s⟩; cases b <;> exact combine_coord _ _ _ _
  rw [←comb,row_repr _ _ (combine_hom a p P hp hP) (combine_hom a r R hr hR),
    row_repr _ _ hp hr,row_repr _ _ hP hR]
  simp only [defect,mk_combine]
  exact distribute_profile ..

def addScaled {I : Type v} {sp : (I→F)→Prop} (lin : FinalRankEngine.Linear sp)
    (x y : {i // sp i}) (a : F) : {i // sp i} :=
  ⟨fun t => x.val t+a*y.val t,lin.addScaled x.val y.val a x.property y.property⟩

omit [Neg F] in
private theorem s_linear : FinalRankEngine.Linear (S (F:=F) w) where
  zero := ⟨[],by simp [homogeneous],rfl⟩
  addScaled := by
    rintro x y a ⟨p,hp,rfl⟩ ⟨r,hr,rfl⟩
    exact ⟨_,combine_hom a p r hp hr,funext (combine_coord a p r)⟩

/-- The quotient bijection of Lemma 3.4 intertwines x+a y for arbitrary
representatives of both image classes. Thus it preserves vector-space
addition and scalar multiplication on the quotients. -/
theorem quotient_linear_isomorphism (field : ConstantField F q)
    (tt : ∀ j, 0<j → TTSpanning.TTPolynomialIndependent F q j) :
    let src := sameProfile (fun x : {a // S (F:=F) w a} => tailProfile q w x.val)
    let dst := sameProfile (fun y : {b // U (F:=F) q (q+w) b} => rowProfile q (q+w) y.val)
    ∃ g : Quotient src → Quotient dst,
      (∀ x y, tailProfile q w x.val=rowProfile q (q+w) y.val →
        g (Quotient.mk src x)=Quotient.mk dst y) ∧
      (∀ x y,g x=g y→x=y) ∧ (∀ y,∃ x,g x=y) ∧
      ∀ x x' y y' a, g (Quotient.mk src x)=Quotient.mk dst y →
        g (Quotient.mk src x')=Quotient.mk dst y' →
        g (Quotient.mk src (addScaled s_linear x x' a))=
        Quotient.mk dst (addScaled u_linear y y' a) := by
  obtain ⟨g,rows,inj,onto⟩ := quotient_isomorphism (w:=w) field tt
  refine ⟨g,rows,inj,onto,?_⟩
  intro x x' y y' a xy xy'
  have compare (X : {a // S (F:=F) w a}) (Y : {b // U (F:=F) q (q+w) b})
      (e : g (Quotient.mk _ X)=Quotient.mk _ Y) :
      tailProfile q w X.val=rowProfile q (q+w) Y.val := by
    obtain ⟨b,ub,hb⟩ := (same_profiles field tt).1 X.val X.property
    have c := (rows X ⟨b,ub⟩ hb).symm.trans e
    exact hb.trans (Quotient.exact c)
  apply rows; funext d
  change tailProfile q w (fun i => x.val i+a*x'.val i) d =
    rowProfile q (q+w) (fun i => y.val i+a*y'.val i) d
  rw [tail_profile_linear x.property x'.property,row_profile_linear y.property y'.property,
    compare x y xy,compare x' y' xy']

end Megaera.FinalQuotientSpaces
