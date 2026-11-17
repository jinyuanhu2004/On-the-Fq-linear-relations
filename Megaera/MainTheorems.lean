import Megaera.Lift
import Megaera.Dimension

/-! The two main statements for a specified finite field. The propositions
below expose what remains to be instantiated for the actual Carlitz values. -/
namespace Megaera.Paper
open Megaera.Finite Megaera.Carlitz

/-- Together with Arithmetic, these are the field and cardinality requirements
on the constants. Only positive characteristic fields of order q≥2 qualify. -/
structure ConstantField (F : Type u) [Arithmetic F] [Neg F] (q : Nat) : Prop where
  two_le : 2 ≤ q
  nontrivial : (0 : F) ≠ 1
  add_neg : ∀ a : F, a + (-a) = 0
  invertible : ∀ a : F, a ≠ 0 → ∃ b, a*b = 1
  cardinality : ∃ f : Fin q → F,
    (∀ i j, f i = f j → i = j) ∧ ∀ a, ∃ i, f i = a

variable {F : Type u} [Arithmetic F] [Neg F]

/-- A relation as a coefficient vector indexed by tuples. -/
def RelationVector (q w : Nat) (v : Tuple → F) : Prop :=
  ∃ p : FormalSum F, Relation q w p ∧ coordinates p = v

/-- The span of the weight-w lifts, as a predicate on coefficient vectors. -/
def BCPVector (q w : Nat) (v : Tuple → F) : Prop :=
  ∃ p : FormalSum F, InBCP q w p ∧ coordinates p = v

theorem relation_iff_vector (q w : Nat) (p : FormalSum F)
    (hw : ∀ e ∈ p, Valid e.2 ∧ weight e.2 = w) :
    Relation q w p ↔ RelationVector q w (coordinates p) := by
  constructor
  · intro h; exact ⟨p, h, rfl⟩
  · rintro ⟨p', ⟨_, he⟩, hv⟩
    exact ⟨hw, fun n => (congrFun (evaluate_congr q p' p hv) n).symm.trans (he n)⟩

theorem bcp_iff_vector (q w : Nat) (p : FormalSum F) :
    InBCP q w p ↔ BCPVector q w (coordinates p) := by
  constructor
  · intro h; exact ⟨p, h, rfl⟩
  · rintro ⟨p', ⟨rows, hw, hs⟩, hv⟩
    exact ⟨rows, hw, fun s => (congrFun hv s).symm.trans (hs s)⟩

private def flattenRows (q : Nat) (rows : List (F × Tuple × Tuple × Tuple)) : FormalSum F :=
  rows.flatMap fun (a,u,v,s) =>
    (bcpGenerator q u v s).map fun e : F × Tuple => (a * e.1, e.2)

omit [Neg F] in
theorem total_append' {A : Type v} (f : A → F) (l k : List A) :
    total f (l++k) = total f l + total f k := by
  induction l with
  | nil => simp [total, Arithmetic.addComm (0:F), Arithmetic.addZero]
  | cons a l ih => simp [total, ih, Arithmetic.addAssoc]

omit [Neg F] in
theorem measure_scale (a : F) (m : F × Tuple → F)
    (law : ∀ c t, m (a*c,t) = a*m (c,t)) (p : FormalSum F) :
    total m (p.map fun e => (a*e.1,e.2)) = a * total m p := by
  induction p with
  | nil => simp [total, Arithmetic.mulZero]
  | cons e p ih => simp [total, law, ih, Arithmetic.distrib]

private theorem measure_flatten (q : Nat) (m : F × Tuple → F)
    (law : ∀ a c t, m (a*c,t) = a*m (c,t)) (rows : List (F × Tuple × Tuple × Tuple)) :
    total m (flattenRows q rows) = total (fun e : F × Tuple × Tuple × Tuple =>
       e.1 * total m (bcpGenerator q e.2.1 e.2.2.1 e.2.2.2)) rows := by
  induction rows with
  | nil => rfl
  | cons e rows ih =>
    rcases e with ⟨a,u,v,s⟩
    change total m ((_ : FormalSum F) ++ flattenRows q rows) = _
    rw [total_append', measure_scale a m (law a), ih]
    rfl

/-- Soundness of the whole span reduces to evaluation of the individual
generators. The degree and positivity of their support are separate facts. -/
theorem span_sound_of_generators (q w : Nat)
    (generators : ∀ u v s, Valid u → Valid v → Valid s → s ≠ [] →
      weight u + weight v + weight s + 2*q = w → Relation (F := F) q w (bcpGenerator q u v s))
    (v : Tuple → F) (hv : BCPVector q w v) : RelationVector q w v := by
  obtain ⟨p, ⟨rows, valid, vector⟩, rfl⟩ := hv
  have each (z : F × Tuple × Tuple × Tuple) (hz : z ∈ rows) :
      Relation q w (bcpGenerator (K := F) q z.2.1 z.2.2.1 z.2.2.2) := by
    obtain ⟨hu,hv,hs,hn,hw⟩ := valid z hz
    exact generators _ _ _ hu hv hs hn hw
  refine ⟨flattenRows q rows, ⟨?_, ?_⟩, ?_⟩
  · intro e he
    obtain ⟨z,hz,ht⟩ := List.mem_flatMap.mp he
    obtain ⟨t,hm,rfl⟩ := List.mem_map.mp ht
    exact (each z hz).1 t hm
  · intro n
    unfold evaluate
    rw [measure_flatten _ _ (fun _ _ _ => Arithmetic.mulAssoc _ _ _)]
    apply total_zero_of_members
    intro z hz
    change z.1 * evaluate q (bcpGenerator q z.2.1 z.2.2.1 z.2.2.2) n = 0
    rw [(each z hz).2, Arithmetic.mulZero]
  · funext s
    rw [vector]
    unfold coordinates
    apply measure_flatten
    intro a c t
    by_cases h : t = s <;> simp [h, Arithmetic.mulZero]

/-- A marked pair indexing a row of weight w; both entries have valid
positive parts and either can be empty. -/
abbrev Row (q w : Nat) := {ht : Tuple × Tuple //
  Valid ht.1 ∧ Valid ht.2 ∧ weight ht.1 + weight ht.2 + q = w}

abbrev Rows (F : Type u) (q w : Nat) := List (F × Row q w)

def component {q w : Nat} (op : Nat → Tuple → Tuple → List Tuple)
    (rows : Rows F q w) (s : Tuple) : F :=
  total (fun e : F × Row q w =>
    e.1 * coordinates (withCoeff (1 : F) (op q e.2.val.1 e.2.val.2)) s) rows

local instance : Zero (Tuple → F) := ⟨fun _ => 0⟩

omit [Neg F] in
private theorem zero_add (a : F) : 0+a = a := by rw [Arithmetic.addComm, Arithmetic.addZero]

private theorem inverse_unique (Fq : ConstantField F q) (a b : F) (h : b+a=0) :
    b = -a := by
  calc
    b = b + (a + (-a)) := by rw [Fq.add_neg, Arithmetic.addZero]
    _ = (b+a) + (-a) := (Arithmetic.addAssoc _ _ _).symm
    _ = -a := by rw [h, zero_add]

theorem neg_mul (Fq : ConstantField F q) (a b : F) :
    (-a)*b = -(a*b) := by
  apply inverse_unique Fq
  rw [Arithmetic.mulComm (-a), Arithmetic.mulComm a b, ← Arithmetic.distrib]
  rw [Arithmetic.addComm (-a), Fq.add_neg, Arithmetic.mulZero]

theorem neg_add (Fq : ConstantField F q) (a b : F) :
    (-a)+(-b) = -(a+b) := by
  apply inverse_unique Fq
  let addA : Std.Associative (α := F) (· + ·) := ⟨Arithmetic.addAssoc⟩
  let addC : Std.Commutative (α := F) (· + ·) := ⟨Arithmetic.addComm⟩
  calc
    _ = (a+(-a))+(b+(-b)) := by ac_rfl
    _ = 0 := by rw [Fq.add_neg, Fq.add_neg, Arithmetic.addZero]

/-- Coefficient verification that multiplying the constructed inverse of
l_(d+1) by θ−θ^(q^(d+1)) gives the inverse of l_d. Multiplying by T^e
(e=q^(d+1)) removes negative exponents, yielding
g+T^e f=T^(e−1)g for g=1/l_(d+1), f=1/l_d. -/
theorem inverseDenom_factor {q : Nat} (Fq : ConstantField F q) (d n : Nat) :
    inverseDenom (F := F) q (d+1) n + shift (q^(d+1)) (inverseDenom q d) n =
    shift (q^(d+1)-1) (inverseDenom q (d+1)) n := by
  let e := q^(d+1)
  have he : 2 ≤ e := by
    have hq := Fq.two_le
    have h := Nat.pow_pos (show 0 < q by omega) (n := d)
    dsimp [e]
    rw [Nat.pow_succ, Nat.mul_comm]
    have h' := Nat.mul_le_mul_left q h
    omega
  let f := inverseDenom (F := F) q d
  let h := divideGeometric (e-1) f
  have cancel (a b : F) : -(a+b)+a = -b := by
    apply inverse_unique Fq
    rw [Arithmetic.addAssoc, Arithmetic.addComm (-(a+b)), Fq.add_neg]
  change shift e (fun j => -h j) n + shift e f n =
    shift (e-1) (shift e (fun j => -h j)) n
  by_cases hn : e ≤ n
  · have hn' : e-1 ≤ n := by omega
    simp only [shift, if_pos hn, if_pos hn']
    have hr := divideGeometric_spec (e-1) (by omega) f (n-e)
    change h (n-e) = f (n-e) + shift (e-1) h (n-e) at hr
    rw [hr, cancel]
    by_cases hm : e-1 ≤ n-e
    · have h' : e ≤ n-(e-1) := by omega
      have ha : n-e-(e-1) = n-(e-1)-e := by omega
      simp [shift, hm, h', ha]
    · have h' : ¬e ≤ n-(e-1) := by omega
      have nz := (inverse_unique Fq 0 0 (Arithmetic.addZero _)).symm
      simp [shift, hm, h', nz]
  · by_cases hm : e-1 ≤ n
    · have h' : ¬e ≤ n-(e-1) := by omega
      simp [shift, hn, hm, h', Arithmetic.addZero]
    · simp [shift, hn, hm, Arithmetic.addZero]

def negRows {q w : Nat} (c : Rows F q w) : Rows F q w :=
  c.map fun e => (-e.1,e.2)

theorem component_neg {q w : Nat} (Fq : ConstantField F q)
    (op : Nat → Tuple → Tuple → List Tuple) (c : Rows F q w) (s : Tuple) :
    component op (negRows c) s = -component op c s := by
  induction c with
  | nil => exact inverse_unique Fq 0 0 (Arithmetic.addZero _)
  | cons a c ih =>
    change (-a.1)*_ + component op (negRows c) s = -(a.1*_ + component op c s)
    rw [neg_mul Fq, ih, neg_add Fq]

omit [Neg F] in
theorem component_append {q w : Nat}
    (op : Nat → Tuple → Tuple → List Tuple) (a b : Rows F q w) (s : Tuple) :
    component op (a++b) s = component op a s + component op b s := by
  induction a with
  | nil => exact (zero_add _).symm
  | cons e a ih =>
    change _ + component op (a++b) s = (_ + component op a s) + component op b s
    rw [ih, Arithmetic.addAssoc]

theorem row_difference {q w : Nat} (Fq : ConstantField F q) (c k : Rows F q w)
    (hL : component L k = 0) (hH : component H k = component H c) :
    ∃ t : Rows F q w, component H t = 0 ∧ component L t = component L c := by
  refine ⟨c ++ negRows k, ?_, ?_⟩
  · funext s
    rw [component_append, component_neg Fq, hH]
    exact Fq.add_neg _
  · funext s
    rw [component_append, component_neg Fq, hL]
    change component L c s + (-(0:F)) = _
    have h := (inverse_unique Fq 0 0 (Arithmetic.addZero _)).symm
    rw [h, Arithmetic.addZero]

/-- Soundness from the binary lift (1.14) when the BCP pairs satisfy
the finite-degree identities in the concrete series model. -/
theorem sound_of_binary (q w : Nat) (field : ConstantField F q)
    (binary_generators : ∀ u v s, Valid u → Valid v → Valid s → s ≠ [] →
      weight u + weight v + weight s + 2*q = w →
      Lift.Binary (F := F) q (bStar u (cOp v (primitive q s)))) :
    ∀ g : Tuple → F, BCPVector q w g → RelationVector q w g := by
  apply span_sound_of_generators q w
  intro u v s hu hv hs hne hwt
  have hgen (e : F × Tuple) (he : e ∈ bcpGenerator q u v s) :
      Valid e.2 ∧ weight e.2 = w :=
    ⟨bcpGenerator_valid q field.two_le u v s hu hv hs e he,
      (bcpGenerator_weight q (by have := field.two_le; omega) u v s e he).trans hwt⟩
  refine ⟨hgen, Lift.binary_lift _ field.two_le _
    (binary_generators u v s hu hv hs hne hwt) ?_⟩
  intro e he
  obtain ⟨valid,wt⟩ := hgen e he
  refine ⟨valid, fun h => ?_⟩
  rw [h] at wt
  change 0 = w at wt
  have := field.two_le
  omega

/-- Theorem 1.10 for the concrete series and tuple generators. The canonical
lift, kernel image assertions and rank increase are explicit hypotheses. The
difference law is the compatibility of componentwise subtraction with the
two formal sums. The proof never assumes completeness. -/
theorem completeness_at_weight (q w : Nat) (Fq : ConstantField F q)
    (ind : (Tuple → F) → (Tuple → F)) (rank : (Tuple → F) → Nat) (bound : Nat)
    (ind_zero : ind 0 = 0)
    (preserves : ∀ r, RelationVector q w r → RelationVector q w (ind r))
    (bounded : ∀ r, RelationVector q w r → rank r ≤ bound)
    (increases : ∀ r, RelationVector q w r → ind r ≠ 0 → rank r < rank (ind r))
    (canonical : ∀ r, RelationVector q w r →
      ∃ c : Rows F q w, component L c = r ∧ component H c = ind r)
    (kerL : ∀ v, BCPVector q w v →
      ∃ k : Rows F q w, component L k = 0 ∧ component H k = v)
    (kerH : ∀ c : Rows F q w, component H c = 0 → BCPVector q w (component L c))
    (binary_generators : ∀ u v s, Valid u → Valid v → Valid s → s ≠ [] →
      weight u + weight v + weight s + 2*q = w →
      Lift.Binary (F := F) q (bStar u (cOp v (primitive q s))))
    (p : FormalSum F) (hw : ∀ e ∈ p, Valid e.2 ∧ weight e.2 = w) :
    Relation q w p ↔ InBCP q w p := by
  rw [relation_iff_vector q w p hw, bcp_iff_vector]
  refine ⟨?_, sound_of_binary q w Fq binary_generators _⟩
  apply Completeness.of_nilpotent_backward (RelationVector q w) (BCPVector q w) ind
  · exact ⟨[], ⟨[], by simp, fun _ => rfl⟩, rfl⟩
  · exact preserves
  · intro v hv
    exact ⟨bound+1, Completeness.nilpotent_of_strict_rank _ ind rank bound ind_zero
      preserves bounded increases v hv⟩
  · intro v hv ht
    obtain ⟨c,hL,hH⟩ := canonical v hv
    obtain ⟨k,hkL,hkH⟩ := kerL _ ht
    obtain ⟨t,htH,htL⟩ := row_difference Fq c k hkL (hkH.trans hH.symm)
    rw [← hL, ← htL]
    exact kerH t htH

/-- The dimension in Theorem 1.12, defined by a basis of n vectors of the
actual fixed-weight relation space; coefficients of basis vectors are unique. -/
def HasRelationDimension (F : Type u) [Arithmetic F] [Neg F] (q w n : Nat) : Prop :=
  ∃ basis : Fin n → (Tuple → F),
    (∀ i, RelationVector q w (basis i)) ∧
    ∀ v, RelationVector q w v →
      ∃ c : Fin n → F,
        (∀ s, v s = total (fun i => c i * basis i s) (List.finRange n)) ∧
        ∀ d : Fin n → F, (∀ s, v s = total (fun i => d i * basis i s) (List.finRange n)) →
          d = c

/-- The two positive-weight mathematical targets; Theorem 1.12 uses the
relation dimensions r_w in the numerator formula of (1.21). -/
def Theorem_1_10 (F : Type u) [Arithmetic F] [Neg F] (q : Nat) : Prop :=
  ConstantField F q → CompletenessStatement F q

def Theorem_1_12 (F : Type u) [Arithmetic F] [Neg F] (q : Nat) : Prop :=
  ConstantField F q → ∃ r : Dimension.Coeff,
    (∀ w ≤ 0, r w = 0) ∧
    (∀ w : Nat, 0 < w → 0 ≤ r w ∧ HasRelationDimension F q w (r w).toNat) ∧
    (∀ w, Dimension.oneMinusTwoX (Dimension.den q (Dimension.den q r)) w =
      Dimension.oneMinusX (Dimension.oneMinusX Dimension.unitSeries) (w-(q:Int)-(q:Int)-1))

/-- Read (1.21) as a statement about the actual dimensions. The remaining
inputs are the rank statements; extraction of the rational series and
all tuple counts are already proved in Dimension. -/
theorem dimension_from_ranks (q : Nat) (r U fixedU fixedR : Dimension.Coeff)
    (initial : ∀ w ≤ 0, r w = 0)
    (isDim : ∀ w : Nat, 0 < w → 0 ≤ r w ∧ HasRelationDimension F q w (r w).toNat)
    (dimU : ∀ w, U w = (Dimension.tupleCount w - Dimension.ttCount q w) + r w)
    (fixedU_count : ∀ w, fixedU w = Dimension.previous U w)
    (fixedR_count : ∀ w, fixedR w = Dimension.previous r w)
    (quotient_count : ∀ w, U w - fixedU w = Dimension.tupleCount (w-(q:Int)) -
        fixedR (w-(q:Int))) : Theorem_1_12 F q := by
  intro field
  exact ⟨r, initial, isDim, Dimension.theorem_1_12_of_ranks field.two_le _ _ _ _
    (fun w hw => initial w (Int.le_of_lt hw)) dimU fixedU_count fixedR_count quotient_count⟩

theorem li_one_at_zero (q : Nat) : li (F := F) q [1] 0 = 1 := by
  change (0:F) + ((1*1+0)*1+0) = 1
  simp [Arithmetic.mulOne, Arithmetic.addZero, zero_add]

private theorem weight_one (s : Tuple) (hs : Valid s) (hw : weight s = 1) : s = [1] := by
  cases s with
  | nil => simp [weight] at hw
  | cons a t =>
    have ha := hs a (by simp)
    cases t with
    | nil => simpa [weight] using hw
    | cons b t =>
      have hb := hs b (by simp)
      simp only [weight] at hw
      omega

/-- At weight 1, evaluation at T=0 reads the only possible tuple
coefficient. This calculation uses the actual Carlitz series. -/
theorem weight_one_relation (q : Nat) (p : FormalSum F)
    (hw : ∀ e ∈ p, Valid e.2 ∧ weight e.2 = 1) :
    Relation q 1 p ↔ coordinates p [1] = 0 := by
  have collapse (n : Nat) : evaluate q p n = coordinates p [1] * li q [1] n := by
    induction p with
    | nil => simp [coordinates, evaluate, total, Arithmetic.mulComm (0 : F), Arithmetic.mulZero]
    | cons e p ih =>
      have he := hw e (by simp)
      have he' := weight_one _ he.1 he.2
      have hp := ih (by intro z hz; exact hw z (by simp [hz]))
      change e.1 * li q e.2 n + evaluate q p n =
        ((if e.2 = [1] then e.1 else 0) + coordinates p [1]) * li q [1] n
      rw [he', if_pos rfl, hp, Arithmetic.mulComm (_+_), Arithmetic.distrib,
        Arithmetic.mulComm _ e.1, Arithmetic.mulComm _ (coordinates p [1])]
  constructor
  · intro h
    simpa [collapse, li_one_at_zero, Arithmetic.mulOne] using h.2 0
  · intro h
    exact ⟨hw, fun n => by rw [collapse, h, Arithmetic.mulComm, Arithmetic.mulZero]⟩

end Megaera.Paper
