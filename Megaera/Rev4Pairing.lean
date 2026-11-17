import Megaera.FourShapes

namespace Megaera.Rev4Pairing
open Megaera.Carlitz Megaera.Finite Megaera.Paper Megaera.FourMinimum Megaera.FourReduction
variable {F : Type u} [Arithmetic F]

/-- Apply f to the homogeneous coordinate vector g at weight w. -/
def reading (w : Nat) (f g : Tuple → F) : F :=
  total (fun x => g x * f x) (Dimension.tuples Int.toNat w)

theorem reading_zero (w : Nat) (f : Tuple → F) : reading w f (fun _ => 0)=0 := by
  apply total_zero_of_members
  exact fun _ _ => zeroMul _

theorem reading_add (w : Nat) (f x g : Tuple → F) :
    reading w f (fun s => x s + g s) = reading w f x + reading w f g := by
  have dist (a b z : F) : (a+b)*z = a*z+b*z := by
    rw [Arithmetic.mulComm,Arithmetic.distrib,Arithmetic.mulComm z a,Arithmetic.mulComm z b]
  simp only [reading,dist,Carlitz.sum_add]

theorem reading_scale (w : Nat) (f : Tuple → F) (k : F) (g : Tuple → F) :
    reading w f (fun s => k*g s) = k*reading w f g := by
  simp only [reading,Arithmetic.mulAssoc,total_scale]

theorem reading_addScaled (w : Nat) (f x : Tuple → F) (k : F) (g : Tuple → F) :
    reading w f (addScaled x k g) = reading w f x + k * reading w f g := by
  unfold addScaled
  rw [reading_add,reading_scale]

private theorem sum_weight (s : Tuple) : s.sum = weight s := by
  induction s with
  | nil => rfl
  | cons j s ih => simp [weight,ih]

/-- Collecting repeated tuples in a homogeneous presentation commutes
with applying a linear functional. -/
theorem reading_coordinates (w : Nat) (f : Tuple → F) (p : FormalSum F)
    (ok : ∀ e∈p, Valid e.2 ∧ weight e.2=w) :
    reading w f (coordinates p) = total (fun e : F × Tuple => e.1*f e.2) p := by
  apply pairing p f _ (Dimension.tuples_nodup ..)
  intro e he
  obtain ⟨v,wt⟩ := ok e he
  exact (Dimension.mem_unrestricted ..).mpr ⟨by rw [sum_weight,wt],v⟩

theorem reading_lifted [Neg F] (field : ConstantField F q) (w : Nat) (f : Tuple → F)
    (h u v : Tuple) (vh : Valid h) (vu : Valid u) (vv : Valid v)
    (hw : weight h + weight u + weight v + 2*q=w) :
    reading w f (liftP q h u v) =
      total (fun e : F × Tuple => e.1*f e.2) (lifted q h u v) := by
  have val := bStar_valid h _ vh (generalP_valid (K:=F) q field.two_le u v vu vv)
  have hq := field.two_le
  have wt := bStar_weight h _ _ (generalP_weight (K:=F) q (by omega) u v)
  apply reading_coordinates
  intro e he
  refine ⟨(List.mem_append.mp he).elim (val.1 e) (val.2 e),?_⟩
  have := (List.mem_append.mp he).elim (wt.1 e) (wt.2 e)
  omega

theorem reading_component (hq : 2≤q) (xs : Rows F q w) (f : Tuple → F) :
    reading w f (component H xs) =
      total (fun e => e.1 * total f (H q e.2.val.1 e.2.val.2)) xs := by
  induction xs with
  | nil => exact reading_zero w f
  | cons e xs ih =>
    let v := H q e.2.val.1 e.2.val.2
    have sum : component H (e::xs) =
        fun s => e.1 * coordinates (withCoeff (1:F) v) s + component H xs s := rfl
    have rep := reading_coordinates w f (withCoeff (1:F) v) (by
      intro a ha
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
      refine ⟨H_valid q hq _ _ e.2.property.1 e.2.property.2.1 x hx,?_⟩
      change weight x=w
      have weight_x := H_weight q (by omega) _ _ x hx
      have wt := e.2.property.2.2
      omega)
    rw [sum,reading_add,reading_scale,ih,rep,total]
    have unit (l : List Tuple) :
        total (fun z : F × Tuple => z.1 * f z.2) (withCoeff 1 l) = total f l := by
      induction l with
      | nil => rfl
      | cons a l ih => change 1*f a+_=f a+_; rw [oneMul]; exact congrArg (f a + ·) ih
    rw [unit]

end Megaera.Rev4Pairing
