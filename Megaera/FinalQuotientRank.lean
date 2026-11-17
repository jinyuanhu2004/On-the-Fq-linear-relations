import Megaera.FinalQuotientSpaces
import Megaera.FinalAmbient
import Megaera.FinalCosetRanks

/-! The rank identity in Lemma 3.4 including its boundary weights. -/
namespace Megaera.FinalQuotientRank
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.SectionThreeSpaces
open Megaera.FinalQuotientSpaces Megaera.FinalLinearSpaces
variable {F : Type u} [Arithmetic F] [Neg F] {q : Nat}

/-- Counting the fibers of the two degree profiles in Lemma 3.4. -/
theorem natural_rank (field : ConstantField F q)
    (tt : ∀ j,0<j→TTSpanning.TTPolynomialIndependent F q j) (w : Nat) {k u v : Nat}
    (bk : HasDimension (fixedR (F:=F) q w) k) (bu : HasDimension (U (F:=F) q (q+w)) u)
    (bv : HasDimension (fixedU (F:=F) q (q+w)) v) :
    (Dimension.tupleCount w).toNat+v=u+k := by
  obtain ⟨fw,bw⟩ := same_profiles (w:=w) field tt
  apply FinalCosetRanks.coset_ranks field (FinalAmbient.ambient_linear w) fixedR_linear
    u_linear fixedU_linear (fun x ⟨p,rel,_,e⟩ => ⟨p,rel.1,e⟩) (fixedU_mem_U q (q+w))
    (fun a => tailProfile q w a.val) (fun b => rowProfile q (q+w) b.val)
    (fun a b => tail_kernel field a.val b.val a.property b.property)
    (fun a b => row_kernel field a.val b.val a.property b.property) _
    (FinalAmbient.ambient_dimension w) bk bu bv
  intro z
  constructor
  · rintro ⟨a,rfl⟩
    obtain ⟨b,hb,eq⟩ := fw a.val a.property
    exact ⟨⟨b,hb⟩,eq.symm⟩
  · rintro ⟨b,rfl⟩
    obtain ⟨a,ha,eq⟩ := bw b.val b.property
    exact ⟨⟨a,ha⟩,eq⟩

theorem lemma_3_4 (field : ConstantField F q)
    (tt : ∀ j,0<j→TTSpanning.TTPolynomialIndependent F q j) (d : Ranks F q) (j : Int) :
    d.u j-d.uFix j=Dimension.tupleCount (j-(q:Int))-d.rFix (j-(q:Int)) := by
  by_cases lt : j<q
  · exact FinalRanks.quotient_below d field (FinalBinary.lifted_row_identity field) tt j lt
  · let w := (j-(q:Int)).toNat
    have ww : (w:Int)=j-(q:Int) := Int.toNat_of_nonneg (by omega)
    have jw : j=((q+w:Nat):Int) := by omega
    have pos : 0<q+w := by have := field.two_le; omega
    obtain ⟨upos,ub⟩ := d.u_basis.2 (q+w) pos
    obtain ⟨vpos,vb⟩ := d.uFix_basis.2 (q+w) pos
    have tc : 0≤Dimension.tupleCount (w:Int) := by
      simp only [Dimension.tupleCount,Int.ofNat_nonneg,if_false,Int.toNat_ofNat]

    rw [←ww,jw]
    by_cases w0 : w=0
    · have zb : HasDimension (fixedR (F:=F) q w) 0 := by rw [w0]; exact FinalRanks.fixedR_zero_weight
      have eq := natural_rank field tt w zb ub vb
      have z := d.rFix_basis.1 (w:Int) (by omega)
      omega
    · obtain ⟨kpos,kb⟩ := d.rFix_basis.2 w (by omega)
      have eq := natural_rank field tt w kb ub vb
      omega

end Megaera.FinalQuotientRank
