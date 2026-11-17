import Megaera.FinalRanks
import Megaera.FinalLRank

/-! The numerical projection formula, including its zero-extension. -/
namespace Megaera.FinalCor32
open Megaera.Paper Megaera.FinalRankEngine Megaera.FinalLinearSpaces
open Megaera.SectionThreeSpaces Megaera.FinalLRankCount

private theorem no_source_at_zero (q : Nat) : sources q 0=[] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro s hs
  obtain ⟨valid,wt,outside⟩ := (mem_sources s).mp hs
  cases s with
  | nil => exact outside (Or.inl rfl)
  | cons a t =>
    have ha := valid a (by simp)
    simp only [weight] at wt
    omega

/-- Corollary 3.2 as an equality of integer coefficient sequences, with
the finite L-rank and the projection kernel both discharged. -/
theorem corollary_3_2 {F : Type u} [Finite.Arithmetic F] [Neg F] {q : Nat}
    (field : ConstantField F q) (rowLaw : CompletenessProof.LiftedRowIdentity F q)
    (tt : ∀ j,0<j→TTSpanning.TTPolynomialIndependent F q j)
    (d : Ranks F q) (k : Int) :
    d.u k=(Dimension.tupleCount k-Dimension.ttCount q k)+d.r k := by
  by_cases neg : k<0
  · rw [d.u_basis.1 _ (by omega),d.r_basis.1 _ (by omega),Dimension.tupleCount_neg _ neg,
      Dimension.ttCount_neg _ _ neg]; decide
  obtain ⟨w,rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0≤k)
  cases w with
  | zero =>
    have card := sourceList_card (q:=q) (w:=0)
    rw [no_source_at_zero] at card
    rw [d.u_basis.1 _ (by decide),d.r_basis.1 _ (by decide),←card]; decide
  | succ w =>
    have hw : 0<w+1 := by omega
    have rd := d.r_basis.2 (w+1) hw
    have ud := d.u_basis.2 (w+1) hw
    have combined := FinalBasisRanks.corollary_3_2 field rowLaw tt hw
      (FinalLRank.image_dimension field (w+1)) rd.2
    have ranks := dimension_unique field u_linear ud.2 combined
    have card := sourceList_card (q:=q) (w:=w+1)
    omega

end Megaera.FinalCor32
