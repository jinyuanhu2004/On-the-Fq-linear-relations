import Megaera.Dimension

/-! The dimension numerator for the space of values follows by subtracting
the relation series from the generating series of all positive tuples. -/
namespace Megaera.FinalValueNumerator
open Megaera.Dimension

/-- The coefficients of X(1−X^q)(1−2X+X^q). -/
def valueNumerator (q : Nat) (w : Int) : Int :=
  unitSeries (w-1)-2*unitSeries (w-2)+2*unitSeries (w-(q:Int)-2)-unitSeries (w-2*(q:Int)-1)

private theorem den_sub (q : Nat) (a b : Coeff) :
    den q (fun w => a w-b w)=fun w => den q a w-den q b w := by
  funext w; simp only [den,oneMinusTwoX]; omega

private theorem difference_den (q : Nat) (a : Coeff) :
    oneMinusTwoX (den q a)=den q (oneMinusTwoX a) := by
  funext w
  simp only [den,oneMinusTwoX]
  rw [show w-1-(q:Int)-1=w-(q:Int)-1-1 by omega]
  omega

private theorem den_zero_below (q : Nat) (a : Coeff) (neg : ∀ k<0,a k=0)
    (k : Int) (hk : k<0) : den q a k=0 := by
  simp [den,oneMinusTwoX,neg k hk,neg (k-1) (by omega),neg (k-(q:Int)-1) (by omega)]

private theorem explicit_identity (q : Nat) (w : Int) :
    den q (den q (oneMinusX unitSeries)) w-den q (den q (oneMinusTwoX unitSeries)) w -
      numerator q w=oneMinusTwoX (valueNumerator q) w := by
  simp only [den,oneMinusX,oneMinusTwoX,numerator,valueNumerator]
  simp only [show w-1-1=w-2 by omega,
    show w-(q:Int)-1-1=w-(q:Int)-2 by omega,
    show w-2-1=w-3 by omega,
    show w-1-(q:Int)=w-(q:Int)-1 by omega,
    show w-(q:Int)-2-1=w-(q:Int)-3 by omega,
    show w-(q:Int)-1-(q:Int)=w-2*(q:Int)-1 by omega,
    show w-2*(q:Int)-1-1=w-2*(q:Int)-2 by omega,
    show w-2*(q:Int)-2-1=w-2*(q:Int)-3 by omega,
    show w-(q:Int)-(q:Int)=w-2*(q:Int) by omega,
    show w-1-2=w-3 by omega,
    show w-(q:Int)-1-2=w-(q:Int)-3 by omega,
    show w-1-2*(q:Int)=w-2*(q:Int)-1 by omega]
  omega

private theorem cancel_difference (a b : Coeff) (neg : ∀ k<0,a k=b k)
    (eqn : ∀ w,oneMinusTwoX a w=oneMinusTwoX b w) (w : Int) : a w=b w := by
  by_cases hn : w<0
  · exact neg w hn
  · have prior := cancel_difference a b neg eqn (w-1)
    have e := eqn w
    unfold oneMinusTwoX at e
    omega
termination_by (w+1).toNat
decreasing_by omega

/-- Formal series consequence of (1.21). All negative coefficients
vanish, and the empty tuple is removed in weight zero. -/
theorem value_series (q : Nat) (r : Coeff) (neg : ∀ k<0,r k=0)
    (relation_series : ∀ w,denominator q r w=numerator q w) (w : Int) :
    den q (den q (fun k => tupleCount k-unitSeries k-r k)) w = valueNumerator q w := by
  let z : Coeff := fun k => tupleCount k-unitSeries k-r k
  have uz (k : Int) (h : k<0) : unitSeries k=0 := by simp [unitSeries,Int.ne_of_lt h]
  have zn (k : Int) (h : k<0) : z k=0 := by simp [z,tupleCount_neg k h,uz k h,neg k h]
  apply cancel_difference (den q (den q z)) (valueNumerator q)
  · intro k hk
    rw [den_zero_below q _ (den_zero_below q _ zn) k hk]
    simp [valueNumerator,uz _ (by omega : k-1<0),uz _ (by omega : k-2<0),
      uz _ (by omega : k-(q:Int)-2<0),uz _ (by omega : k-2*(q:Int)-1<0)]
  · intro k
    have h : oneMinusTwoX (den q (den q r)) k=numerator q k := relation_series k
    rw [difference_den,difference_den] at h
    rw [difference_den,difference_den]
    have diff : oneMinusTwoX z=fun j =>
        oneMinusX unitSeries j-oneMinusTwoX unitSeries j-oneMinusTwoX r j := by
      funext j
      have eq := tupleCount_series j
      simp only [oneMinusTwoX,z,oneMinusX] at *
      omega
    rw [diff,den_sub,den_sub,den_sub,den_sub]
    change _ - den q (den q (oneMinusTwoX r)) k=_
    rw [h]
    exact explicit_identity q k

end Megaera.FinalValueNumerator
