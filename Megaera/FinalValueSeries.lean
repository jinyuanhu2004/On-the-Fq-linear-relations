import Megaera.FinalValueSpace
import Megaera.FinalValueNumerator

/-! The rational generating function of the actual value dimensions, as
a corollary of Theorem 1.12 and rank-nullity of the CMPL evaluation map. -/
namespace Megaera.FinalValueSpace
open Megaera.Finite Megaera.Paper Megaera.SectionThreeSpaces
variable {F : Type u} [Arithmetic F] [Neg F] {q : Nat}

/-- The coefficients of equation (1.18), deduced from the relation
dimension formula and expressed coefficientwise over the integers. -/
theorem value_generating_series (field : ConstantField F q)
    (tt : ∀ w,0<w → TTSpanning.TTPolynomialIndependent F q w) :
    ∃ z : Dimension.Coeff, IsRankSequence (ValueSpace F q) z ∧
      ∀ w, Dimension.den q (Dimension.den q z) w = FinalValueNumerator.valueNumerator q w := by
  obtain ⟨r,initial,ranks,series⟩ := EditionOneThree.theorem_1_12 tt field
  let z : Dimension.Coeff := fun k => Dimension.tupleCount k-Dimension.unitSeries k-r k
  refine ⟨z,⟨?_,?_⟩,FinalValueNumerator.value_series q r (fun k hk => initial k (by omega)) series⟩
  · intro w hw
    by_cases lt : w<0
    · simp only [z,Dimension.tupleCount_neg w lt,Dimension.unitSeries,if_neg (Int.ne_of_lt lt),initial w hw]
      decide
    · have eq : w=0 := by omega
      subst w
      rw [show z 0=Dimension.tupleCount 0-Dimension.unitSeries 0-r 0 from rfl,initial 0 (by decide)]
      simp [Dimension.tupleCount,Dimension.tuples,Dimension.unitSeries]
  · intro w hw
    obtain ⟨nonneg,basis⟩ := ranks w hw
    obtain ⟨n,values,sum⟩ := value_rank_nullity field basis
    have tc : 0≤Dimension.tupleCount (w:Int) := Int.ofNat_nonneg _
    have uz : Dimension.unitSeries (w:Int)=0 := if_neg (by omega)
    have eq : z w=(n:Int) := by
      change Dimension.tupleCount w-Dimension.unitSeries w-r w=_
      rw [uz]; omega
    rw [eq]
    exact ⟨Int.ofNat_nonneg _,values⟩

end Megaera.FinalValueSpace
