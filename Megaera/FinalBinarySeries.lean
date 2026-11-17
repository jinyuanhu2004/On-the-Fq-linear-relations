import Megaera.RevisedProducts
import Megaera.BCPRows

/-! The Cauchy product at infinity, with the actual coefficients of 1/l_d. -/
namespace Megaera.FinalBinarySeries
open Megaera.Finite Megaera.Carlitz
variable {F : Type u} [Arithmetic F]

theorem sum_congr {A : Type v} (f g : A → F) (l : List A)
    (eqn : ∀ j∈l,f j=g j) : total f l=total g l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [total,total,eqn a (by simp),ih (fun j hj => eqn j (by simp [hj]))]

private theorem sum_mul {A : Type v} (a : F) (f : A → F) (l : List A) :
    total (fun j => a*f j) l=a*total f l := by
  induction l with
  | nil => exact (Arithmetic.mulZero _).symm
  | cons b l ih => simp only [total,ih,Arithmetic.distrib]

theorem product_comm (f g : Series F) : product f g=product g f := by
  funext n
  have rev : (List.range (n+1)).reverse=(List.range (n+1)).map (n-·) := by
    simpa [List.range_eq_range'] using (List.reverse_range' (s:=0) (n:=n+1))
  unfold product
  rw [←BCPRows.permSum _ (List.reverse_perm (List.range (n+1))),rev,total_map]
  apply sum_congr
  intro j hj
  have le := List.mem_range.mp hj
  simp only [show n-(n-j)=j by omega,Arithmetic.mulComm]

theorem product_add (f g h : Series F) :
    product f (addSeries g h)=addSeries (product f g) (product f h) := by
  funext n
  simp only [product,addSeries,Arithmetic.distrib,sum_add]

theorem add_product (f g h : Series F) :
    product (addSeries f g) h=addSeries (product f h) (product g h) := by
  rw [product_comm,product_add,product_comm h f,product_comm h g]

theorem scale_product (a : F) (f g : Series F) :
    product (fun i => a*f i) g=fun n => a*product f g n := by
  funext n; simp only [product,Arithmetic.mulAssoc,sum_mul]

theorem product_first (f g : Series F) : product f g 0=f 0*g 0 := by
  simp [product,List.range_succ,total,Arithmetic.addZero]

theorem product_next (f g : Series F) (n : Nat) :
    product f g (n+1)=f 0*g (n+1)+product (fun i => f (i+1)) g n := by
  unfold product
  rw [List.range_succ_eq_map (n:=n+1),total,total_map]
  simp

theorem product_assoc (f g h : Series F) : product (product f g) h=product f (product g h) := by
  funext n
  induction n generalizing f g h with
  | zero => simp only [product_first,Arithmetic.mulAssoc]
  | succ n ih =>
    rw [product_next,product_next f (product g h),product_first,product_next g h]
    have tail : (fun i => product f g (i+1)) =
        addSeries (fun i => f 0*g (i+1)) (product (fun i => f (i+1)) g) := by
      funext i; exact product_next _ _ _
    rw [tail,add_product]
    simp only [addSeries,scale_product,ih,Arithmetic.distrib,Arithmetic.mulAssoc,Arithmetic.addAssoc]

theorem product_unit (f : Series F) : product unitSeries f=f := by
  funext n
  unfold product
  rw [List.range_succ_eq_map,total,total_map]
  have z := Carlitz.total_zero_of_members
    (fun i => unitSeries (F:=F) (i+1)*f (n-(i+1))) (List.range n)
    (fun i _ => by simp [unitSeries,zeroMul])
  change unitSeries 0 * f n + total (fun i => unitSeries (i+1)*f (n-(i+1))) (List.range n)=f n
  rw [z,Arithmetic.addZero]; exact oneMul _

/-- Used locally so function-level arithmetic outside this module is unaffected. -/
def seriesArithmetic : Arithmetic (Series F) where
  zero := fun _ => 0
  ofNat := unitSeries
  add := addSeries
  mul := product
  addAssoc a b c := funext fun n => Arithmetic.addAssoc (a n) (b n) (c n)
  addComm a b := funext fun n => Arithmetic.addComm (a n) (b n)
  addZero a := funext fun n => Arithmetic.addZero (a n)
  mulAssoc := product_assoc
  mulComm := product_comm
  mulOne a := (product_comm a _).trans (product_unit a)
  mulZero a := funext fun _ => total_zero_of_members _ _ (fun j _ => Arithmetic.mulZero (a j))
  distrib := product_add

end Megaera.FinalBinarySeries
