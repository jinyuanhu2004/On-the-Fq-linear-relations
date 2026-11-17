import Megaera.FinalFixedRanks
import Megaera.FinalCor32
import Megaera.FinalQuotientRank

/-! Theorem 1.12 for the coefficient spaces of the actual Carlitz values. -/
namespace Megaera.FinalDimension
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.SectionThreeSpaces
variable {F : Type u} [Arithmetic F] [Neg F] {q : Nat}

/-- The sole external number-theoretic input is TT independence, stated on
finite polynomial-coefficient sums. Every rank comes from a basis of its
specified space of coefficient vectors. -/
theorem theorem_1_12 (tt : ∀ w,0<w → TTSpanning.TTPolynomialIndependent F q w) :
    Theorem_1_12 F q := by
  intro field
  let d := FinalRanks.ranks field
  exact dimension_from_spaces q d
    (FinalCor32.corollary_3_2 field (FinalBinary.lifted_row_identity field) tt d)
    (FinalFixedRanks.theorem_3_3_U field tt d) (FinalFixedRanks.theorem_3_3_R field tt d)
    (FinalQuotientRank.lemma_3_4 field tt d) field

/-- Direct coefficient formula for the dimension at a specified positive weight. -/
theorem relation_dimension_at (field : ConstantField F q)
    (tt : ∀ w,0<w → TTSpanning.TTPolynomialIndependent F q w) {w : Nat} (hw : 0<w) :
    HasRelationDimension F q w (Dimension.coefficients q (Dimension.numerator q) w).toNat := by
  obtain ⟨r,initial,bases,series⟩ := theorem_1_12 tt field
  have eq := Dimension.relation_coefficients_of_series q r (fun k hk => initial k (by omega)) series
  rw [←eq]; exact (bases w hw).2

/-- No positive-weight relation below the first possible weight; the first
relation space has a one-element basis at weight 2q+1. -/
theorem first_relation_dimension (field : ConstantField F q)
    (tt : ∀ w,0<w → TTSpanning.TTPolynomialIndependent F q w) :
    (∀ w : Nat,0<w → w≤2*q → HasRelationDimension F q w 0) ∧
      HasRelationDimension F q (2*q+1) 1 := by
  obtain ⟨r,initial,bases,series⟩ := theorem_1_12 tt field
  obtain ⟨zero,one⟩ := Dimension.relation_threshold_of_series q r (fun k hk => initial k (by omega)) series
  constructor
  · intro w pos bound
    have h := (bases w pos).2
    simpa only [zero w (by omega),Int.toNat_zero] using h
  · have h := (bases (2*q+1) (by omega)).2
    simpa only [show ((2*q+1:Nat):Int)=2*(q:Int)+1 by omega,one] using h

end Megaera.FinalDimension
