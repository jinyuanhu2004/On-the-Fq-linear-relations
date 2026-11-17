import Megaera.FinalAmbient
import Megaera.FinalCosetRanks
import Megaera.EditionOneThree

/-! The value-space corollary in the opening sentence of Section 3:
the dimension of the actual CMPL value span is |I_w|−dim R_w. -/
namespace Megaera.FinalValueSpace
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.SectionThreeSpaces
open Megaera.FinalRankEngine Megaera.FinalLinearSpaces
variable {F : Type u} [Arithmetic F] [Neg F] {q w : Nat}

def ValueSpace (F : Type u) [Arithmetic F] [Neg F] (q w : Nat) (y : Series F) : Prop :=
  ∃ p : FormalSum F, homogeneous w p ∧ evaluate q p=y

private abbrev Ambient (F : Type u) [Arithmetic F] (w : Nat) (x : Tuple→F) :=
  ∃ p : FormalSum F, homogeneous w p ∧ coordinates p=x

private theorem linear_values : Linear (ValueSpace F q w) where
  zero := ⟨[],by simp [homogeneous],rfl⟩
  addScaled := by
    rintro a b k ⟨p,hp,rfl⟩ ⟨r,hr,rfl⟩
    exact ⟨combine k p r,combine_hom k p r hp hr,funext (combine_val k p r (li q))⟩

private noncomputable def profile (q : Nat) (a : {x // Ambient F w x}) : Series F :=
  evaluate q (Classical.choose a.property)

private theorem profile_rep (p : FormalSum F) (hp : homogeneous w p) :
    profile q (⟨coordinates p,p,hp,rfl⟩ : {x // Ambient F w x}) = evaluate q p :=
  evaluate_congr q _ _ (Classical.choose_spec (show Ambient F w (coordinates p) from ⟨p,hp,rfl⟩)).2

private theorem profile_mem (a : {x // Ambient F w x}) : ValueSpace F q w (profile q a) :=
  ⟨_,(Classical.choose_spec a.property).1,rfl⟩

private theorem sub_zero (field : ConstantField F q) (x y : F) : x+ -y=0 ↔ x=y := by
  constructor
  · intro h
    have e := congrArg (·+y) h
    simpa only [Arithmetic.addAssoc,Arithmetic.addComm (-y) y,field.add_neg,Arithmetic.addZero,
      zeroAdd] using e
  · rintro rfl; exact field.add_neg _

private theorem profile_kernel (field : ConstantField F q) (a b : {x // Ambient F w x}) :
    profile q a=profile q b ↔ RelationVector q w (fun s => a.val s + -b.val s) := by
  let p := Classical.choose a.property
  let r := Classical.choose b.property
  have ha : homogeneous w p ∧ coordinates p=a.val := Classical.choose_spec a.property
  have hb : homogeneous w r ∧ coordinates r=b.val := Classical.choose_spec b.property
  let d := combine (-1:F) p r
  have hd : coordinates d=(fun s => a.val s + -b.val s) := by
    funext s
    rw [show coordinates d s=_ from combine_coord (-1:F) p r s,neg_mul field,oneMul,ha.2,hb.2]
  have vd (j : Nat) : evaluate q d j=profile q a j+ -(profile q b j) := by
    rw [show evaluate q d j=_ from combine_val (-1:F) p r (li q) j,neg_mul field,oneMul]
    rfl
  constructor
  · intro eq
    exact ⟨d,⟨combine_hom _ _ _ ha.1 hb.1,fun j => (vd j).trans ((sub_zero field _ _).mpr (congrFun eq j))⟩,hd⟩
  · rintro ⟨v,hv,coords⟩
    have eq := evaluate_congr q d v (hd.trans coords.symm)
    funext j
    exact (sub_zero field _ _).mp ((vd j).symm.trans ((congrFun eq j).trans (hv.2 j)))

omit [Neg F] in
/-- Finitely many series can be separated from zero by finitely many coefficients. -/
private theorem cutoff (xs : List (Series F)) :
    ∃ n, ∀ y∈xs, (∀ j : Fin n, y j.val=0) → ∀ k,y k=0 := by
  classical
  induction xs with
  | nil => exact ⟨0,by simp⟩
  | cons x xs ih =>
    obtain ⟨m,hm⟩ := ih
    by_cases zz : ∀ i,x i=0
    · refine ⟨m,?_⟩
      intro y hy h
      rcases List.mem_cons.mp hy with rfl|mem
      · exact zz
      · exact hm y mem h
    · obtain ⟨j,hj⟩ := Classical.not_forall.mp zz
      refine ⟨m+j+1,?_⟩
      intro y hy h
      rcases List.mem_cons.mp hy with rfl|mem
      · exact False.elim (hj (h ⟨j,by omega⟩))
      · exact hm y mem (fun k => h ⟨k.val,by omega⟩)

private theorem value_basis_exists (field : ConstantField F q) : ∃ z,HasDimension (ValueSpace F q w) z := by
  classical
  obtain ⟨xs,_,_,members⟩ := count_space field (FinalAmbient.ambient_linear w) (FinalAmbient.ambient_dimension w)
  let eval (x : Tuple→F) := if h : Ambient F w x then profile q ⟨x,h⟩ else (fun _ => 0)
  obtain ⟨n,detect⟩ := cutoff (xs.map eval)
  have cover (y : Series F) (hy : ValueSpace F q w y) : y∈xs.map eval := by
    obtain ⟨p,hp,rfl⟩ := hy
    have ap : Ambient F w (coordinates p) := ⟨p,hp,rfl⟩
    exact List.mem_map.mpr ⟨coordinates p,(members _).mpr ap,by simp only [eval,dif_pos ap]; exact profile_rep p hp⟩
  let image := fun g : Fin n→F => ∃ y,ValueSpace F q w y ∧ ∀ j : Fin n,y j.val=g j
  have lin : Linear image := by
    refine ⟨⟨_,linear_values.zero,fun _ => rfl⟩,?_⟩
    rintro _ _ k ⟨a,ha,ea⟩ ⟨b,hb,eb⟩
    exact ⟨_,linear_values.addScaled _ _ k ha hb,fun j => by dsimp; rw [ea,eb]⟩
  obtain ⟨z,_,basis⟩ := finite_dimension field lin (List.finRange n) (fun _ _ i hi => False.elim
    (hi (List.mem_ofFn.mpr ⟨i,rfl⟩)))
  have kernel (v : Series F) : (∀ i,v i=0) ↔ ValueSpace F q w v ∧ ∀ j : Fin n,v j.val=0 := by
    constructor
    · intro zero
      exact ⟨(funext zero).symm ▸ linear_values.zero,fun j => zero j.val⟩
    · rintro ⟨hv,hz⟩
      exact detect v (cover v hv) hz
  exact ⟨z,split_basis field linear_values Fin.val image (fun v => ∀ i,v i=0)
    (fun _ => Iff.rfl) kernel basis (dimension_zero (fun _ => rfl) (fun _ h => h))⟩

/-- Evaluating the tuples has kernel R_w. This numerical corollary uses
no independence hypothesis or proposed basis of CMPL values. -/
theorem value_rank_nullity (field : ConstantField F q) {r : Nat}
    (rel : HasDimension (RelationVector (F:=F) q w) r) :
    ∃ z, HasDimension (ValueSpace F q w) z ∧ z+r=(Dimension.tupleCount w).toNat := by
  obtain ⟨n,basis⟩ := value_basis_exists (w:=w) field
  let zero := fun y : Series F => ∀ i,y i=0
  have zlin : Linear zero := ⟨fun _ => rfl,fun a b k ha hb i => by
    change a i+k*b i=0; rw [ha,hb,Arithmetic.mulZero,Arithmetic.addZero]⟩
  have dim := FinalCosetRanks.coset_ranks field (FinalAmbient.ambient_linear w) rel_linear
    linear_values zlin (fun x ⟨p,r,e⟩ => ⟨p,r.1,e⟩)
    (fun y h => (funext h).symm ▸ linear_values.zero)
    (fun a => profile q a) Subtype.val (profile_kernel field)
    (fun a b => ⟨fun e i => (sub_zero field _ _).mpr (congrFun e i),
      fun h => funext (fun i => (sub_zero field _ _).mp (h i))⟩) (by
      intro y
      constructor
      · rintro ⟨a,rfl⟩; exact ⟨⟨_,profile_mem a⟩,rfl⟩
      · rintro ⟨⟨y,p,hp,rfl⟩,rfl⟩
        exact ⟨⟨coordinates p,p,hp,rfl⟩,profile_rep p hp⟩)
    (FinalAmbient.ambient_dimension w) rel basis (dimension_zero zlin.zero (fun _ h => h))
  exact ⟨n,basis,by omega⟩

theorem value_dimension (field : ConstantField F q) {r : Nat}
    (rel : HasDimension (RelationVector (F:=F) q w) r) :
    HasDimension (ValueSpace F q w) ((Dimension.tupleCount w).toNat-r) := by
  obtain ⟨n,basis,sum⟩ := value_rank_nullity field rel
  simpa only [←sum,Nat.add_sub_cancel] using basis

/-- Explicit coefficient formula for dim Z_w obtained from Theorem 1.12. -/
theorem value_dimension_from_series (field : ConstantField F q)
    (tt : ∀ j,0<j → TTSpanning.TTPolynomialIndependent F q j) (hw : 0<w) :
    HasDimension (ValueSpace F q w) ((Dimension.tupleCount w).toNat -
      (Dimension.coefficients q (Dimension.numerator q) w).toNat) := by
  obtain ⟨r,initial,ranks,series⟩ := EditionOneThree.theorem_1_12 tt field
  have same := Dimension.relation_coefficients_of_series q r (fun k hk => initial k (by omega)) series
  rw [←same]
  exact value_dimension field (ranks w hw).2

end Megaera.FinalValueSpace
