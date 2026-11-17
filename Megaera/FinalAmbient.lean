import Megaera.FinalRanks
namespace Megaera.FinalAmbient
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.SectionThreeSpaces
open Megaera.FinalRankEngine Megaera.FinalLinearSpaces
variable {F : Type u} [Arithmetic F] [Neg F]


omit [Neg F] in
theorem ambient_linear (w : Nat) : Linear (fun v => ∃ p : FormalSum F, homogeneous w p ∧ coordinates p=v) := by
  refine ⟨⟨[],by simp [homogeneous],rfl⟩,?_⟩
  rintro x y a ⟨p,hp,rfl⟩ ⟨r,hr,rfl⟩
  exact ⟨combine a p r,combine_hom a p r hp hr,funext (combine_coord a p r)⟩

private theorem sum_w (s : Tuple) : s.sum=weight s := by
  induction s with
  | nil => rfl
  | cons a t ih => simp [weight,ih]

omit [Neg F] in
private theorem one_position {n : Nat} (i : Fin n) (v : F) :
    total (fun j => if i=j then v else 0) (List.finRange n)=v := by
  have nodup : (List.finRange n).Nodup := by
    apply List.pairwise_iff_getElem.mpr
    intro a b ha hb lt eq
    have e : a=b := by simpa using congrArg Fin.val eq
    omega
  have mem : i∈List.finRange n := List.mem_ofFn.mpr ⟨i,rfl⟩
  suffices h : ∀ (xs : List (Fin n)),xs.Nodup →
      total (fun j => if i=j then v else 0) xs=(if i∈xs then v else 0) by
    simpa only [if_pos mem] using h _ nodup
  intro xs nd
  induction xs with
  | nil => simp [total]
  | cons a xs ih =>
    obtain ⟨na,d⟩ := List.nodup_cons.mp nd
    by_cases e : i=a
    · subst a; simp [total,ih d,na,Arithmetic.addZero]
    · simp [total,ih d,e,zeroAdd]


omit [Neg F] in
/-- The standard tuple basis, including the single empty tuple at weight zero. -/
theorem ambient_dimension (w : Nat) :
    HasDimension (fun v => ∃ p : FormalSum F,homogeneous w p ∧ coordinates p=v) (Dimension.tupleCount w).toNat := by
  classical
  let xs := Dimension.tuples Int.toNat w
  let b (j : Fin xs.length) (s : Tuple) := if xs.get j=s then (1:F) else 0
  have spec {s} : s∈xs ↔ Valid s ∧ weight s=w := by
    rw [Dimension.mem_unrestricted,sum_w]; exact ⟨fun ⟨eq,h⟩ => ⟨h,by omega⟩,fun ⟨h,eq⟩ => ⟨by omega,h⟩⟩
  have inj (i j : Fin xs.length) (h : xs.get i=xs.get j) : i=j := by
    apply Fin.ext
    have pair := List.pairwise_iff_getElem.mp (Dimension.tuples_nodup Int.toNat w)
    by_cases eq : i.val=j.val
    · exact eq
    · rcases Nat.lt_or_gt_of_ne eq with lt|lt
      · exact False.elim (pair i.val j.val i.isLt j.isLt lt h)
      · exact False.elim (pair j.val i.val j.isLt i.isLt lt h.symm)
  have atPos (c : Fin xs.length→F) (i : Fin xs.length) :
      total (fun j => c j*b j (xs.get i)) (List.finRange xs.length)=c i := by
    rw [←one_position i (c i)]
    apply FinalBinarySeries.sum_congr
    intro j _
    by_cases he : i=j
    · subst j; simp [b,Arithmetic.mulOne]
    · simp only [b,if_neg he,if_neg (show xs.get j≠xs.get i from fun h => he (inj i j h.symm)),Arithmetic.mulZero]
  change HasDimension _ xs.length
  refine ⟨b,?_,?_⟩
  · intro i
    refine ⟨[(1,xs.get i)],?_,?_⟩
    · intro e he
      obtain rfl := List.mem_singleton.mp he
      exact spec.mp (List.get_mem _ i)
    · funext s; simp [coordinates,b,total,Arithmetic.addZero]
  · rintro x ⟨p,hp,ep⟩
    refine ⟨fun j => x (xs.get j),?_,?_⟩
    · intro s
      by_cases hin : s∈xs
      · obtain ⟨j,lt,ej⟩ := List.getElem_of_mem hin
        subst s
        exact (atPos (fun j => x (xs.get j)) ⟨j,lt⟩).symm
      · have z : x s=0 := by
          rw [←ep]
          apply total_zero_of_members; intro e he; apply if_neg
          intro e'; exact hin (e' ▸ spec.mpr (hp e he))
        rw [z]; symm
        exact total_zero_of_members _ _ (fun j _ => by simp only [b,if_neg (show xs.get j≠s from fun h => hin (h ▸ List.get_mem _ j)),Arithmetic.mulZero])
    · intro d eq; funext j
      exact (atPos d j).symm.trans (eq (xs.get j)).symm

end Megaera.FinalAmbient
