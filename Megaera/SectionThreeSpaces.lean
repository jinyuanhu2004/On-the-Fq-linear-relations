import Megaera.MainTheorems

/-! The spaces in §3, with the same coefficient representatives as the two
main theorems. All levels of a fixed relation, including d = -1, are tested.
Put T = θ⁻¹. Multiplying A + (θ^q − θ)B by T^q gives
T^q A + B − T^(q−1) B. The Laurent-coefficient equivalence below verifies
this clearing of negative powers. -/
namespace Megaera.SectionThreeSpaces
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.Lift
variable {F : Type u} [Arithmetic F] [Neg F]

/-- Read a power series as a Laurent series with zero negative coefficients. -/
def coefficient (A : Series F) : Int → F
  | .ofNat n => A n
  | .negSucc _ => 0

omit [Neg F] in
private theorem coefficient_neg (A : Series F) (k : Int) (hk : k < 0) :
    coefficient A k = 0 := by
  cases k with
  | ofNat n => exact False.elim (Int.not_lt.mpr (Int.ofNat_nonneg n) hk)
  | negSucc => rfl

omit [Neg F] in
private theorem shifted (m n : Nat) (A : Series F) :
    shift m A n = coefficient A ((n:Int)-m) := by
  by_cases h : m ≤ n
  · rw [show (n:Int)-m = ((n-m:Nat):Int) by omega]
    simp [shift,h,coefficient]
  · rw [coefficient_neg _ _ (by omega)]
    simp [shift,h]

omit [Neg F] in
/-- Coefficient equations for A + D₁ B = 0, with D₁ = θ^q − θ. -/
def cleared (q : Nat) (A B : Series F) : Prop :=
  ∀ n, shift q A n + B n = shift (q-1) B n

omit [Neg F] in
theorem cleared_iff_laurent (q : Nat) (hq : 0 < q) (A B : Series F) :
    cleared q A B ↔ ∀ k : Int,
      coefficient A k + coefficient B (k+q) = coefficient B (k+1) := by
  constructor
  · intro h k
    by_cases hk : 0 ≤ k + q
    · let n := (k+q).toNat
      have hn : (n:Int) = k+q := Int.toNat_of_nonneg hk
      have he := h n
      rw [shifted,shifted] at he
      change coefficient A ((n:Int)-q) + coefficient B (n:Int) =
        coefficient B ((n:Int)-(q-1:Nat)) at he
      rw [show (n:Int)-q=k by omega,show (n:Int)-(q-1:Nat)=k+1 by omega,hn] at he
      exact he
    · rw [coefficient_neg A k (by omega),coefficient_neg B (k+q) (by omega),
        coefficient_neg B (k+1) (by omega),Arithmetic.addZero]
  · intro h n
    have he := h ((n:Int)-q)
    rw [shifted,shifted]
    simpa only [show (n:Int)-q+q=n by omega,show (n:Int)-q+1=(n:Int)-(q-1:Nat) by omega]
      using he

omit [Neg F] in
/-- A and B are uniquely recorded as the two constant-field coefficients of
a scalar a + D₁ b when q ≥ 2. Only the coefficients at 0 and q are needed. -/
theorem cleared_scalars (q : Nat) (hq : 2 ≤ q) (a b : F) :
    cleared q (fun n => if n=0 then a else 0) (fun n => if n=0 then b else 0) ↔ a=0 ∧ b=0 := by
  constructor
  · intro h
    have h₀ := h 0
    have hb : b=0 := by
      simpa [shift,show ¬q≤0 by omega,show ¬q-1≤0 by omega,zeroAdd] using h₀
    have hq' := h q
    have ha : a=0 := by
      simpa [shift,hb,Arithmetic.addZero,Nat.le_refl q, Nat.sub_self] using hq'
    exact ⟨ha,hb⟩
  · rintro ⟨rfl,rfl⟩
    intro n
    simp [shift,Arithmetic.addZero]

/-- Each list is a finite presentation in S_w; repetitions are allowed,
and the coordinate map adds their coefficients. -/
def homogeneous (w : Nat) (p : FormalSum F) : Prop :=
  ∀ e ∈ p, Valid e.2 ∧ weight e.2 = w

/-- A coordinate function of (P,Q); false selects P, true selects Q. -/
def pairCoordinates (p r : FormalSum F) (i : Bool × Tuple) : F :=
  if i.1 then coordinates r i.2 else coordinates p i.2

def fixedLevels (q : Nat) (p : FormalSum F) : Prop :=
  ∀ d : Int, ∀ n : Nat, valueAt (degree q d) p n = 0

theorem fixedLevels_iff_binary (q : Nat) (p : FormalSum F) :
    fixedLevels q p ↔ Binary q (p,[]) := by
  simp [fixedLevels,Binary,valueAt,total,Arithmetic.addZero]

/-- R_w^Fix in §3.2: a relation whose exact degree sums vanish for every
integer degree. The exceptional value Si_{-1}(∅)=1 is part of degree. -/
def fixedR (q w : Nat) (v : Tuple → F) : Prop :=
  ∃ p : FormalSum F, Relation q w p ∧ fixedLevels q p ∧ coordinates p = v

/-- U_w of §3.1, evaluated at the coefficient level in F((θ⁻¹)). -/
def U (q w : Nat) (v : Bool × Tuple → F) : Prop :=
  ∃ p r : FormalSum F, homogeneous w p ∧ homogeneous w r ∧
    cleared q (evaluate q p) (evaluate q r) ∧ pairCoordinates p r = v

/-- U_w^Fix of §3.2. The two columns are evaluated at the same level d. -/
def fixedU (q w : Nat) (v : Bool × Tuple → F) : Prop :=
  ∃ p r : FormalSum F, homogeneous w p ∧ homogeneous w r ∧
    cleared q (evaluate q p) (evaluate q r) ∧
    (∀ d : Int, cleared q (valueAt (degree q d) p) (valueAt (degree q d) r)) ∧
    pairCoordinates p r = v

theorem fixedR_mem_R (q w : Nat) (v : Tuple → F) (h : fixedR q w v) :
    RelationVector q w v := by
  obtain ⟨p,hr,_,hp⟩ := h
  exact ⟨p,hr,hp⟩

theorem fixedU_mem_U (q w : Nat) (v : Bool × Tuple → F) (h : fixedU q w v) :
    U q w v := by
  obtain ⟨p,r,hp,hr,h,_,hv⟩ := h
  exact ⟨p,r,hp,hr,h,hv⟩

/-- A basis with uniquely determined F-coordinates for any one of the
concrete predicates on indexed coefficient vectors. -/
def HasDimension {I : Type v} (space : (I → F) → Prop) (n : Nat) : Prop :=
  ∃ basis : Fin n → (I → F), (∀ i, space (basis i)) ∧
    ∀ x, space x → ∃ c : Fin n → F,
      (∀ s, x s = total (fun i => c i * basis i s) (List.finRange n)) ∧
      ∀ d : Fin n → F, (∀ s, x s = total (fun i => d i * basis i s) (List.finRange n)) →
        d = c

theorem relation_dimension (q w n : Nat) :
    HasDimension (F := F) (RelationVector q w) n ↔ HasRelationDimension F q w n := Iff.rfl

/-- The rank sequences used in the paper concern positive weights. They
are extended by zero for w ≤ 0 when performing the coefficient recurrences. -/
def IsRankSequence {I : Type v} (space : Nat → (I → F) → Prop) (d : Dimension.Coeff) : Prop :=
  (∀ w ≤ 0, d w = 0) ∧ ∀ w : Nat, 0 < w → 0 ≤ d w ∧ HasDimension (space w) (d w).toNat

structure Ranks (F : Type u) [Arithmetic F] [Neg F] (q : Nat) where
  r : Dimension.Coeff
  u : Dimension.Coeff
  rFix : Dimension.Coeff
  uFix : Dimension.Coeff
  r_basis : IsRankSequence (F := F) (RelationVector q) r
  u_basis : IsRankSequence (F := F) (U q) u
  rFix_basis : IsRankSequence (F := F) (fixedR q) rFix
  uFix_basis : IsRankSequence (F := F) (fixedU q) uFix

/-- Theorem 1.12 from the rank statements for the concrete spaces.
Corollary 3.2, both cases of Theorem 3.3 and the quotient dimension of
Lemma 3.4 (extended to the small weights) are explicit hypotheses. -/
theorem dimension_from_spaces (q : Nat) (d : Ranks F q)
    (cor32 : ∀ w, d.u w = (Dimension.tupleCount w - Dimension.ttCount q w) + d.r w)
    (thm33u : ∀ w, d.uFix w = Dimension.previous d.u w)
    (thm33r : ∀ w, d.rFix w = Dimension.previous d.r w)
    (lem34 : ∀ w, d.u w - d.uFix w =
      Dimension.tupleCount (w-(q:Int)) - d.rFix (w-(q:Int))) : Theorem_1_12 F q :=
  dimension_from_ranks q d.r d.u d.uFix d.rFix d.r_basis.1 d.r_basis.2
    cor32 thm33u thm33r lem34

end Megaera.SectionThreeSpaces
