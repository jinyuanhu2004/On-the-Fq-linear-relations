import Megaera.EditionOneFour
import Megaera.FinalValueSeries
import Megaera.Zeta

/-! Consequences over the constant field of the weight-preserving transfer
in Hu's Theorem 1.1. The transfer and its evaluation identity are inputs.
Both evaluations below are the concrete power-sum series. -/
namespace Megaera.EditionOneZeta
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.Lift Megaera.SectionThreeSpaces
open Megaera.FinalQuotientSpaces
variable {F : Type u} [Arithmetic F] [Neg F] {q w : Nat}

/-- An enumeration of precisely the q elements supplies the alphabet
for Thakur's monic polynomials. -/
noncomputable def elements (field : ConstantField F q) : List F :=
  List.ofFn (Classical.choose field.cardinality)

theorem elements_spec (field : ConstantField F q) :
    (elements field).length=q ∧ (elements field).Nodup ∧ ∀ a,a∈elements field := by
  obtain ⟨inj,onto⟩ := Classical.choose_spec field.cardinality
  refine ⟨List.length_ofFn, List.pairwise_iff_getElem.mpr ?_,fun a => List.mem_ofFn.mpr (onto a)⟩
  intro i j hi hj lt eq
  simp only [elements,List.getElem_ofFn] at eq
  have e : i=j := congrArg Fin.val (inj _ _ eq)
  omega

/-- The restriction of Hu's linear automorphism to the space of formal
tuples of weight w. Only its action on this space is specified. -/
structure HuTransfer (field : ConstantField F q) (w : Nat) where
  map : (Tuple → F) → (Tuple → F)
  homogeneous_map : ∀ x,S w x → S w (map x)
  injective : ∀ x y,S w x → S w y → map x=map y → x=y
  onto : ∀ y,S w y → ∃ x,S w x ∧ map x=y
  map_zero : map (fun _ => 0)=(fun _ => 0)
  map_add_scaled : ∀ x y a,S w x → S w y →
    map (fun i => x i+a*y i)=(fun i => map x i+a*map y i)
  evaluation : ∀ (p r : FormalSum F), homogeneous w p → homogeneous w r →
    map (coordinates p)=coordinates r → valueAt (Zeta.zeta (elements field)) r=evaluate q p

def ZetaRelations (field : ConstantField F q) (w : Nat) (x : Tuple → F) : Prop :=
  ∃ p : FormalSum F, homogeneous w p ∧ coordinates p=x ∧
    ∀ j,valueAt (Zeta.zeta (elements field)) p j=0

def ZetaValues (field : ConstantField F q) (w : Nat) (y : Series F) : Prop :=
  ∃ p : FormalSum F, homogeneous w p ∧ valueAt (Zeta.zeta (elements field)) p=y

variable {field : ConstantField F q}

private theorem relation_mem {x : Tuple → F} (hx : ZetaRelations field w x) : S w x := by
  obtain ⟨p,hp,rep,_⟩ := hx
  exact ⟨p,hp,rep⟩

theorem map_relation (T : HuTransfer field w) {x : Tuple → F} (hx : S w x) :
    ZetaRelations field w (T.map x) ↔ RelationVector q w x := by
  obtain ⟨p,hp,rfl⟩ := hx
  constructor
  · rintro ⟨r,hr,eq,van⟩
    have id := T.evaluation p r hp hr eq.symm
    exact ⟨p,⟨hp, fun j => (congrFun id j).symm.trans (van j)⟩,rfl⟩
  · rintro ⟨p',rel,eq⟩
    obtain ⟨r,hr,rep⟩ := T.homogeneous_map _ ⟨p,hp,rfl⟩
    have id := T.evaluation p r hp hr rep.symm
    exact ⟨r,hr,rep,fun j => (congrFun id j).trans
      ((congrFun (evaluate_congr q p' p eq) j).symm.trans (rel.2 j))⟩

/-- The zeta relations are exactly the images under T of the BCP span. -/
theorem zeta_completeness (T : HuTransfer field w)
    (tt : TTSpanning.TTPolynomialIndependent F q w) (y : Tuple → F) :
    ZetaRelations field w y ↔ ∃ x,S w x ∧ BCPVector q w x ∧ T.map x=y := by
  have comp {x : Tuple → F} (hx : S w x) : RelationVector q w x ↔ BCPVector q w x := by
    obtain ⟨p,hp,rfl⟩ := hx
    exact (relation_iff_vector q w p hp).symm.trans
      ((EditionOneFour.theorem_1_10 field tt p hp).trans (bcp_iff_vector q w p))
  constructor
  · intro hy
    obtain ⟨x,hx,eq⟩ := T.onto y (relation_mem hy)
    exact ⟨x,hx,(comp hx).mp ((map_relation T hx).mp (eq.symm ▸ hy)),eq⟩
  · rintro ⟨x,hx,span,rfl⟩
    exact (map_relation T hx).mpr ((comp hx).mpr span)

private def combination {n : Nat} (b : Fin n → Tuple → F) (c : Fin n → F)
    (indices : List (Fin n)) (s : Tuple) : F := total (fun i => c i*b i s) indices

private theorem map_combination (T : HuTransfer field w) {n : Nat}
    (b : Fin n → Tuple → F) (hb : ∀ i,S w (b i)) (c : Fin n → F) (is : List (Fin n)) :
    S w (combination b c is) ∧
    T.map (combination b c is)=combination (fun i => T.map (b i)) c is := by
  induction is with
  | nil => exact ⟨(FinalAmbient.ambient_linear w).zero,T.map_zero⟩
  | cons j is ih =>
    have step (v : Fin n → Tuple → F) :
        combination v c (j::is)=(fun s => combination v c is s+c j*v j s) :=
      funext (fun _ => Arithmetic.addComm ..)
    rw [step,step]
    exact ⟨(FinalAmbient.ambient_linear w).addScaled _ _ _ ih.1 (hb j),
      (T.map_add_scaled _ _ _ ih.1 (hb j)).trans (by rw [ih.2])⟩

/-- Transport a basis with its unique coefficient representation. -/
theorem transfer_basis (T : HuTransfer field w) {n : Nat}
    (basis : HasDimension (RelationVector (F:=F) q w) n) :
    HasDimension (ZetaRelations field w) n := by
  obtain ⟨b,rel,coords⟩ := basis
  have mem {x : Tuple → F} (r : RelationVector q w x) : S w x := by
    obtain ⟨p,hp,out⟩ := r
    exact ⟨p,hp.1,out⟩
  have hb (i) := mem (rel i)
  refine ⟨fun i => T.map (b i),fun i => (map_relation T (hb i)).mpr (rel i),?_⟩
  intro y hy
  obtain ⟨x,hx,eq⟩ := T.onto y (relation_mem hy)
  obtain ⟨c,ec,uc⟩ := coords x ((map_relation T hx).mp (eq.symm ▸ hy))
  have transport (d : Fin n → F) := map_combination T b hb d (List.finRange n)
  refine ⟨c,fun s => congrFun (eq.symm.trans ((congrArg T.map (funext ec)).trans (transport c).2)) s,?_⟩
  intro d ed
  apply uc d
  have e : T.map x=T.map (combination b d (List.finRange n)) :=
    eq.trans ((funext ed).trans (transport d).2.symm)
  exact congrFun (T.injective _ _ hx (transport d).1 e)

/-- The relation dimension is the coefficient of the generating function
in Theorem 1.12, now for the kernel of Thakur's evaluation. -/
theorem zeta_relation_dimension (T : HuTransfer field w)
    (tt : ∀ j,0<j → TTSpanning.TTPolynomialIndependent F q j) (hw : 0<w) :
    HasDimension (ZetaRelations field w) (Dimension.coefficients q (Dimension.numerator q) w).toNat := by
  obtain ⟨r,initial,bases,series⟩ := EditionOneThree.theorem_1_12 tt field
  have eq := Dimension.relation_coefficients_of_series q r (fun k hk => initial k (by omega)) series
  rw [←eq]
  exact transfer_basis T (bases w hw).2

/-- Equality of the two spans inside the same space of power series. -/
theorem value_spaces_eq (T : HuTransfer field w) :
    ZetaValues field w=FinalValueSpace.ValueSpace F q w := by
  funext y; apply propext
  constructor
  · rintro ⟨r,hr,rfl⟩
    obtain ⟨x,⟨p,hp,rfl⟩,eq⟩ := T.onto (coordinates r) ⟨r,hr,rfl⟩
    exact ⟨p,hp,(T.evaluation p r hp hr eq).symm⟩
  · rintro ⟨p,hp,rfl⟩
    obtain ⟨r,hr,eq⟩ := T.homogeneous_map _ ⟨p,hp,rfl⟩
    exact ⟨r,hr,T.evaluation p r hp hr eq.symm⟩

theorem zeta_value_dimension (T : HuTransfer field w)
    (tt : ∀ j,0<j → TTSpanning.TTPolynomialIndependent F q j) (hw : 0<w) :
    HasDimension (ZetaValues field w) ((Dimension.tupleCount w).toNat -
      (Dimension.coefficients q (Dimension.numerator q) w).toNat) := by
  rw [value_spaces_eq T]
  exact FinalValueSpace.value_dimension_from_series field tt hw

/-- Equation (1.18) for the Thakur value spaces follows from their
equality with the Carlitz value spaces at every positive weight. -/
theorem zeta_value_series (T : ∀ w, 0<w → HuTransfer field w)
    (tt : ∀ w, 0<w → TTSpanning.TTPolynomialIndependent F q w) :
    ∃ d : Dimension.Coeff, IsRankSequence (ZetaValues field) d ∧
      ∀ w, Dimension.den q (Dimension.den q d) w = FinalValueNumerator.valueNumerator q w := by
  obtain ⟨d,rank,series⟩ := FinalValueSpace.value_generating_series field tt
  refine ⟨d,⟨rank.1,?_⟩,series⟩
  intro w hw
  rw [value_spaces_eq (T w hw)]
  exact rank.2 w hw

end Megaera.EditionOneZeta
