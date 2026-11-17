import Megaera.MainTheorems
import Megaera.Singletons

namespace Megaera.SingletonTop
open Megaera.Finite Megaera.Paper Megaera.Singletons
variable {F : Type u} [Arithmetic F] [Neg F]
local instance : Std.Associative (α := F) (· + ·) := ⟨Arithmetic.addAssoc⟩
local instance : Std.Commutative (α := F) (· + ·) := ⟨Arithmetic.addComm⟩

private theorem root_inside (b : Nat) {v : Tuple → F} (h : HPlus q v) : HPlus q (root b v) :=
  .add (.cons (b+1) h) (.cons b (.cons 0 h))

private theorem at_root (field : ConstantField F q) (a n : Nat) (v : Tuple → F) :
    restore (root a v) n = if n=a+2 then v else fun _ => 0 := by
  have r := field.add_neg
  funext t
  change restore (fun x => head (a+2) v x + head (a+1) (head 1 v) x) n t = _
  rw [restore_add r]
  by_cases hn : n=a+2
  · subst n
    rw [restore_above r (a+1) (a+2) _ (by omega),Arithmetic.addZero]
    have he := congrFun (restore_head r v (a+2) 0) t
    simpa [ones] using he
  · simp only [if_neg hn]
    by_cases gt : a+2<n
    · rw [restore_above r _ _ _ gt,restore_above r _ _ _ (by omega),Arithmetic.addZero]
    · let k := a+1-n
      have h₁ : n+k=a+1 := by dsimp [k]; omega
      have h₂ : n+(k+1)=a+2 := by omega
      have e₁ := congrFun (restore_head r (head 1 v) n k) t
      have e₂ := congrFun (restore_head r v n (k+1)) t
      rw [h₁] at e₁
      rw [h₂] at e₂
      rw [e₁,e₂,ones_head r]
      exact (Arithmetic.addComm ..).trans (r _)

theorem rooted_restore (field : ConstantField F q) (n b : Nat) (v : Tuple → F)
    (hv : HPlus q v) : HPlus q (root b (restore v n)) := by
  have inv := field.add_neg
  induction hv with
  | zero =>
    rw [funext (restore_zero inv n)]
    exact root_inside _ .zero
  | @add v z hv hz iv iz =>
    rw [funext (restore_add inv v z n)]
    have eq : root b (fun t => restore v n t + restore z n t) =
        fun t => root b (restore v n) t + root b (restore z n) t := by
      funext t; simp only [root,head_add]; ac_rfl
    rw [eq]; exact .add iv iz
  | @neg v hv iv =>
    rw [funext (restore_neg inv v n)]
    have eq : root b (fun t => -restore v n t) = fun t => -root b (restore v n) t := by
      funext t; simp only [root,head_neg inv,Singletons.neg_add inv]
    rw [eq]; exact .neg iv
  | @cons a v hv ih =>
    by_cases le : n ≤ a+1
    · have e : n+(a+1-n)=a+1 := by omega
      rw [←e,restore_head inv]; exact root_inside _ (ones_inside _ _ _ hv)
    · rw [funext (restore_above inv _ _ v (by omega))]
      exact root_inside _ .zero
  | gen a t k ht =>
    rw [at_root field]
    split
    · exact .gen _ _ _ ht
    · exact root_inside _ .zero

theorem restore_vanishing_above (field : ConstantField F q) (A : Tuple → F) (N : Nat)
    (above : ∀ j, N<j → ∀ t, A (j::t)=0) (j : Nat) (hj : N<j) (t : Tuple) :
    restore A j t = 0 := by
  induction t generalizing j with
  | nil => exact above j hj []
  | cons b t ih =>
    simp only [restore,above j hj]
    split <;> simp [ih _ (by omega : N<j+1),nz field.add_neg,Arithmetic.addZero]

theorem root_of_top (field : ConstantField F q) (N b : Nat) (A : Tuple → F)
    (h : HPlus q A) (above : ∀ j, N<j → ∀ t, A (j::t)=0) :
    HPlus q (root b (fun t => A (N::t))) := by
  have eq : restore A N = fun t => A (N::t) := by
    funext t; cases t with
    | nil => rfl
    | cons a t =>
      simp [restore,restore_vanishing_above field _ N above _ (by omega : N<N+1),
        nz field.add_neg,Arithmetic.addZero]
  exact eq ▸ rooted_restore field N b A h

end Megaera.SingletonTop
