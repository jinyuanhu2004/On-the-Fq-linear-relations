import Megaera.FinalLinearSpaces
import Megaera.FinalCanonical

namespace Megaera.FinalRanks
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.SectionThreeSpaces
open Megaera.FinalRankEngine Megaera.FinalLinearSpaces
variable {F : Type u} [Arithmetic F] [Neg F] {q w : Nat}

private def support (w : Nat) := Dimension.tuples Int.toNat w
private def pairSupport (w : Nat) := (support w).map (Prod.mk false) ++ (support w).map (Prod.mk true)

private theorem wt_sum (s : Tuple) : s.sum=weight s := by
  induction s with
  | nil => rfl
  | cons a t ih => simp [weight,ih]

omit [Neg F] in
private theorem outside (p : FormalSum F) (hp : homogeneous w p) (i : Tuple) (hi : i∉support w) :
    coordinates p i=0 := by
  apply total_zero_of_members
  intro z hz; apply if_neg
  intro e
  exact hi ((Dimension.mem_unrestricted ..).mpr ⟨by rw [←e,wt_sum,(hp z hz).2],e ▸ (hp z hz).1⟩)

omit [Neg F] in
private theorem outside_pair (p r : FormalSum F) (hp : homogeneous w p) (hr : homogeneous w r)
    (i : Bool × Tuple) (hi : i∉pairSupport w) : pairCoordinates p r i=0 := by
  obtain ⟨b,i⟩ := i
  cases b
  · exact outside p hp i (fun h => hi (List.mem_append_left _ (List.mem_map.mpr ⟨i,h,rfl⟩)))
  · exact outside r hr i (fun h => hi (List.mem_append_right _ (List.mem_map.mpr ⟨i,h,rfl⟩)))

private theorem r_exists (field : ConstantField F q) : ∃ n,HasDimension (RelationVector (F:=F) q w) n := by
  obtain ⟨n,_,h⟩ := finite_dimension field rel_linear (support w) (by
    rintro x ⟨p,⟨hp,_⟩,rfl⟩; exact outside p hp)
  exact ⟨n,h⟩

private theorem rf_exists (field : ConstantField F q) : ∃ n,HasDimension (fixedR (F:=F) q w) n := by
  obtain ⟨n,_,h⟩ := finite_dimension field fixedR_linear (support w) (by
    rintro x ⟨p,⟨hp,_⟩,_,rfl⟩; exact outside p hp)
  exact ⟨n,h⟩

private theorem u_exists (field : ConstantField F q) : ∃ n,HasDimension (U (F:=F) q w) n := by
  obtain ⟨n,_,h⟩ := finite_dimension field u_linear (pairSupport w) (by
    rintro x ⟨p,r,hp,hr,_,rfl⟩; exact outside_pair p r hp hr)
  exact ⟨n,h⟩

private theorem uf_exists (field : ConstantField F q) : ∃ n,HasDimension (fixedU (F:=F) q w) n := by
  obtain ⟨n,_,h⟩ := finite_dimension field fixedU_linear (pairSupport w) (by
    rintro x ⟨p,r,hp,hr,_,_,rfl⟩; exact outside_pair p r hp hr)
  exact ⟨n,h⟩

private noncomputable def rankSeq {I : Type v} {sp : Nat → (I→F)→Prop}
    (ex : ∀ w,∃ n,HasDimension (sp w) n) : Dimension.Coeff :=
  fun w => if 0<w then Int.ofNat (Classical.choose (ex w.toNat)) else 0

omit [Neg F] in
private theorem ranks_correct {I : Type v} {sp : Nat → (I→F)→Prop}
    (ex : ∀ w,∃ n,HasDimension (sp w) n) : IsRankSequence sp (rankSeq ex) := by
  refine ⟨fun w le => by simp [rankSeq,show ¬0<w by omega],?_⟩
  intro w pos
  have h : (0:Int)<w := by omega
  simp only [rankSeq,if_pos h,Int.toNat_ofNat,Int.ofNat_zero_le,true_and]
  exact ⟨Int.ofNat_nonneg _,Classical.choose_spec (ex w)⟩

/-- The concrete rank sequences exist for every finite constant field. -/
noncomputable def ranks (field : ConstantField F q) : Ranks F q where
  r := rankSeq (fun _ => r_exists field)
  u := rankSeq (fun _ => u_exists field)
  rFix := rankSeq (fun _ => rf_exists field)
  uFix := rankSeq (fun _ => uf_exists field)
  r_basis := ranks_correct _
  u_basis := ranks_correct _
  rFix_basis := ranks_correct _
  uFix_basis := ranks_correct _

/-- The exceptional empty tuple is detected by its degree -1 evaluation. -/
theorem fixedR_zero_weight : HasDimension (fixedR (F:=F) q 0) 0 := by
  apply dimension_zero fixedR_linear.zero
  rintro x ⟨p,⟨hp,_⟩,lev,rfl⟩ s
  have nilpot (z) (hz : z∈p) : z.2=[] := by
    obtain ⟨valid,weightZero⟩ := hp z hz
    cases eq : z.2 with
    | nil => rfl
    | cons a l =>
      rw [eq] at weightZero valid
      have pos := valid a (by simp)
      simp only [weight] at weightZero; omega
  by_cases es : s=[]
  · subst s
    have eqn : coordinates p []=Lift.valueAt (Lift.degree q (-1)) p 0 := by
      apply FinalBinarySeries.sum_congr
      intro z hz
      rw [nilpot z hz]
      change (if ([]:Tuple)=[] then z.1 else 0)=z.1*1
      simp [Arithmetic.mulOne]
    exact eqn.trans (lev (-1) 0)
  · apply total_zero_of_members
    intro z hz; exact if_neg (fun (h : z.2=s) => es (h ▸ nilpot z hz))

/-- No marked row has weight below q. -/
theorem small_U (field : ConstantField F q) (rowLaw : CompletenessProof.LiftedRowIdentity F q)
    (tt : ∀ j,0<j→TTSpanning.TTPolynomialIndependent F q j) (hw : 0<w) (small : w<q) :
    HasDimension (U (F:=F) q w) 0 ∧ HasDimension (fixedU (F:=F) q w) 0 := by
  have van (v : Bool × Tuple→F) (hv : U q w v) (s : Bool × Tuple) : v s=0 := by
    obtain ⟨c,cols⟩ := (FinalDegreeOne.lemma_3_1 field rowLaw tt hw v).mp hv
    have hc : c=[] := by
      cases c with
      | nil => rfl
      | cons e c => have z := e.2.property.2.2; omega
    subst c
    cases s with
    | mk bit s => cases bit; exact (cols s).1; exact (cols s).2
  exact ⟨dimension_zero u_linear.zero van,dimension_zero fixedU_linear.zero
    (fun x hx => van x (fixedU_mem_U q w x hx))⟩

theorem quotient_below (d : Ranks F q) (field : ConstantField F q)
    (rowLaw : CompletenessProof.LiftedRowIdentity F q)
    (tt : ∀ j,0<j→TTSpanning.TTPolynomialIndependent F q j) (j : Int) (small : j<q) :
    d.u j-d.uFix j=Dimension.tupleCount (j-(q:Int))-d.rFix (j-(q:Int)) := by
  rw [Dimension.tupleCount_neg _ (by omega),d.rFix_basis.1 _ (by omega)]
  by_cases h : j≤0
  · rw [d.u_basis.1 _ h,d.uFix_basis.1 _ h]
  · obtain ⟨w,rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0≤j)
    have hw : 0<w := by omega
    obtain ⟨u,uf⟩ := small_U field rowLaw tt hw (by omega)
    have a := d.u_basis.2 w hw
    have b := d.uFix_basis.2 w hw
    have eu := dimension_unique field u_linear a.2 u
    have ef := dimension_unique field fixedU_linear b.2 uf
    omega

end Megaera.FinalRanks
