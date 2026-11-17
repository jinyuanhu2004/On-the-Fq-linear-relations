import Megaera.SingletonTop
import Megaera.MainTheorems

/-! Singleton stuffle on coefficient vectors; the empty tuple and all merged
heads are included. -/
namespace Megaera.Saturation
open Megaera.Finite Megaera.Carlitz Megaera.Singletons Megaera.Paper
variable {F : Type u} [Arithmetic F]
local instance : Std.Associative (α := F) (· + ·) := ⟨Arithmetic.addAssoc⟩
local instance : Std.Commutative (α := F) (· + ·) := ⟨Arithmetic.addComm⟩

def star (n : Nat) (p : Tuple → F) : Tuple → F
  | [] => 0
  | b::s => (if n=b then p s else 0) + (if n ≤ b then p ((b-n)::s) else 0) +
      star n (fun x => p (b::x)) s

theorem star_zero (n : Nat) : star n (fun _ => (0:F)) = fun _ => 0 := by
  funext s
  induction s with
  | nil => rfl
  | cons b s ih => simp [star, ih, Arithmetic.addZero]

theorem star_add (n : Nat) (p r : Tuple → F) :
    star n (fun x => p x + r x) = fun x => star n p x + star n r x := by
  funext s
  induction s generalizing p r with
  | nil => exact (Arithmetic.addZero _).symm
  | cons b s ih =>
    simp only [star,ih (fun x => p (b::x)) (fun x => r (b::x))]
    by_cases h : n=b <;> by_cases k : n≤b <;> simp [h,k, Arithmetic.addZero, zeroAdd] <;> ac_rfl

theorem star_neg [Neg F] (inv : ∀ x : F, x + -x = 0) (n : Nat) (p : Tuple → F) :
    star n (fun s => -p s) = fun x => -(star n p x) := by
  funext s
  induction s generalizing p with
  | nil => exact (nz inv).symm
  | cons b s ih =>
    simp only [star, ih (fun t => p (b::t)), neg_add inv]
    split <;> split <;> simp [nz inv, Arithmetic.addZero, zeroAdd]

theorem star_head (n a : Nat) (p : Tuple → F) :
    star n (head a p) = fun x => (head n (head a p) x + head (n+a) p x) + head a (star n p) x := by
  funext s
  cases s with
  | nil => simp [head,star,Arithmetic.addZero]
  | cons b s =>
    have ea : ((if n ≤ b then head a p ((b-n)::s) else 0)) = head (n+a) p (b::s) := by
      simp only [head]; by_cases h : n ≤ b
      · simp [h, show (a=b-n ↔ n+a=b) from by omega]
      · simp [h, show n+a ≠ b from by omega]
    have ec : star n (fun x => head a p (b::x)) s = head a (star n p) (b::s) := by
      by_cases h : a=b
      · simp [head,h]
      · simp [head,h,star_zero]
    change ((if n=b then head a p s else 0) + _ + _) = _
    rw [ea,ec]
    rfl

private def atom (k : F) (s : Tuple) : Tuple → F := fun t => if s=t then k else 0

private theorem atom_cons (k : F) (a : Nat) (s : Tuple) :
    atom k (a::s) = head a (atom k s) := by
  funext t
  cases t with
  | nil => simp [atom,head]
  | cons b t => by_cases e : a=b <;> simp [atom,head,e]

private theorem atom_single (k : F) (s : Tuple) :
    coordinates (withCoeff k [s]) = atom k s := by
  funext t; simp [withCoeff,coordinates,total,atom, Arithmetic.addZero]

theorem star_atom (n : Nat) (k : F) (s : Tuple) :
    star n (atom k s) = coordinates (withCoeff k (quasiShuffle [n] s)) := by
  induction s with
  | nil =>
    rw [quasiShuffle_nil_right,atom_single]
    funext t
    cases t with
    | nil => simp [atom,star]
    | cons b t =>
      have eqn : (fun x => atom k [] (b::x)) = (fun _ => 0) := by funext x; simp [atom]
      simp [star,atom,show (fun x : Tuple => if ([]:Tuple)=b::x then k else 0) = fun _ => 0 by simp,
        star_zero,Arithmetic.addZero]
      split <;> simp_all
  | cons a s ih =>
    rw [atom_cons,star_head,ih,quasiShuffle.eq_3,quasiShuffle_nil_left,quasiShuffle_nil_left]
    funext x
    simp only [coeff_append,coeff_prepend,atom_single,atom_cons]
    ac_rfl

theorem star_coeff (n : Nat) (k : F) (l : List Tuple) :
    star n (coordinates (withCoeff k l)) =
      coordinates (withCoeff k (l.flatMap (quasiShuffle [n]))) := by
  induction l with
  | nil => exact star_zero _
  | cons a s ih =>
    have e : coordinates (withCoeff k (a::s)) = (fun x => atom k a x + coordinates (withCoeff k s) x) := rfl
    rw [e,star_add,star_atom,ih,List.flatMap_cons]
    funext x
    exact (coeff_append ..).symm

variable [Neg F] {q : Nat}

/-- A bound on the weight of every nonzero coefficient, with positive entries. -/
def Supported (w : Nat) (p : Tuple → F) : Prop :=
  ∀ s, p s ≠ 0 → Valid s ∧ weight s ≤ w

def Above (m : Nat) (p : Tuple → F) : Prop :=
  ∀ j, m < j → ∀ s, p (j::s) = 0

omit [Neg F] in
private theorem support_zero {p : Tuple → F} {w : Nat} (h : Supported w p) (s : Tuple)
    (no : ¬(Valid s ∧ weight s ≤ w)) : p s = 0 := by
  exact Classical.byContradiction (fun nz => no (h s nz))

omit [Neg F] in
theorem above_of_supported {w : Nat} {p : Tuple → F} (hw : Supported w p) : Above w p := by
  intro j hj s
  apply support_zero hw
  simp only [weight]; omega

private theorem low (field : ConstantField F q) (p : Tuple → F) (hp : HPlus q p) :
    p [] = 0 ∧ ∀ a, p [a] = 0 := by
  induction hp with
  | zero => exact ⟨rfl,fun _ => rfl⟩
  | add _ _ ih jh =>
    exact ⟨by simp [ih.1,jh.1,Arithmetic.addZero],
      fun a => by simp [ih.2 a,jh.2 a,Arithmetic.addZero]⟩
  | neg _ ih => exact ⟨by simp [ih.1,nz field.add_neg],fun a => by simp [ih.2 a,nz field.add_neg]⟩
  | cons a hp ih =>
    refine ⟨rfl,fun b => ?_⟩
    simp [head,ih.1]
  | gen a t k ht =>
    have v : coordinates (withCoeff k (quasiShuffle [q-1] t)) [] = 0 := by
      rw [← star_atom]; rfl
    simp [root, head,v,Arithmetic.addZero]

private theorem empty_zero (field : ConstantField F q) (n w : Nat) (p : Tuple → F) (hs : Supported w p)
    (h : HPlus q (star n p)) : p [] = 0 := by
  have hv : p [0] = 0 := support_zero hs _ (by
    intro ok; have := ok.1 0 (by simp); omega)
  have H := (low field _ h).2 n
  simpa [star,hv,Arithmetic.addZero] using H

omit [Neg F] in
theorem star_above {m : Nat} (n : Nat) (p : Tuple → F) (h : Above m p) : Above (n+m) (star n p) := by
  intro j hj s
  have z := funext (h j (by omega))
  simp [star,show n ≠ j by omega,show n ≤ j by omega, h _ (by omega : m < j-n), z, star_zero,Arithmetic.addZero]

omit [Neg F] in
theorem star_top {m n : Nat} (hm : 0 < m) (hn : 0 < n) (p : Tuple → F) (h : Above m p) :
    (fun t => star n p ((n+m)::t)) = fun t => p (m::t) := by
  have z := funext (h (n+m) (by omega))
  funext s
  simp [star,show n ≠ n+m by omega,show n ≤ n+m by omega, show n+m-n=m by omega,z,star_zero,Arithmetic.addZero,zeroAdd]

private theorem top_root (field : ConstantField F q) (p : Tuple → F) (b m : Nat) (hm : 0 < m)
    (hp : Above m p) (hz : HPlus q (star (q-1) p)) : HPlus q (root b (fun t => p (m::t))) := by
  have H := SingletonTop.root_of_top field (q-1+m) b _ hz (star_above _ p hp)
  rw [star_top hm (by have := field.two_le; omega) p hp] at H
  exact H

private theorem peel_one (field : ConstantField F q) (p : Tuple → F)
    (h : HPlus q (star (q-1) (head 1 p))) : HPlus q (star (q-1) p) := by
  have up : Above 1 (head 1 p) := by intro j hj s; simp [head,show 1 ≠ j by omega]
  have r := top_root field (head 1 p) (q-2) 1 (by omega) up h
  have proj : (fun t => head 1 p (1 :: t)) = p := by funext t; simp [head]
  rw [proj] at r
  have eqn : star (q-1) (head 1 p) = fun x => root (q-2) p x + head 1 (star (q-1) p) x := by
    rw [star_head]; funext t
    have hq := field.two_le
    simp only [root,show q-2+2=q-1+1 by omega,show q-2+1=q-1 by omega]
    ac_rfl
  rw [eqn] at h
  have sub := HPlus.add h (HPlus.neg r)
  apply (prepend_one_iff field.add_neg q _).mp
  have cancel (a b:F) : a+b+(-a) = b := by
    calc _ = (a + (-a))+b := by ac_rfl
         _ = _ := by rw [field.add_neg,zeroAdd]
  simpa only [cancel] using sub

/-- Eliminate the top first-entry slice using its root relation. -/
private def trim (b : Nat) (p : Tuple → F) (x : Tuple) : F :=
  p x + -(root b (fun t => p ((b+2)::t)) x)

private theorem trim_above (field : ConstantField F q) (b : Nat) (p : Tuple → F)
    (high : Above (b+2) p) : Above (b+1) (trim b p) := by
  intro j hj s
  have e : b+1 ≠ j := by omega
  by_cases h : j=b+2
  · subst j; simp [trim,root,head,e,Arithmetic.addZero,field.add_neg]
  · simp [trim,root,head, Ne.symm h,e,high j (by omega),Arithmetic.addZero,nz field.add_neg]

private theorem trim_supported (field : ConstantField F q) (w b : Nat) (p : Tuple → F)
    (hw : Supported w p) : Supported w (trim b p) := by
  intro s hs
  by_cases hp : p s = 0
  · have rn : root b (fun t => p ((b+2)::t)) s ≠ 0 := by
      intro he; exact hs (by simp [trim, hp,he,nz field.add_neg,Arithmetic.addZero])
    cases s with
    | nil => exact (rn (Arithmetic.addZero _)).elim
    | cons a t =>
      by_cases ha : b+2 = a
      · subst a; exact (rn (by simp [root,head,hp,show b+1≠b+2 by omega,Arithmetic.addZero])).elim
      by_cases ha' : b+1 = a
      · subst a
        cases t with
        | nil => exact (rn (by simp [root,head,ha,Arithmetic.addZero])).elim
        | cons c t =>
          by_cases hc : c = 1
          · subst c
            have hbase : p ((b+2)::t) ≠ 0 := by
              intro h; exact rn (by simp [root,head,ha,h,Arithmetic.addZero])
            obtain ⟨hv,hwt⟩ := hw _ hbase
            refine ⟨?_,?_⟩
            · intro i hi
              rcases List.mem_cons.mp hi with rfl | hi
              · omega
              rcases List.mem_cons.mp hi with rfl | hi
              · omega
              · exact hv _ (List.mem_cons_of_mem _ hi)
            · simp only [weight] at hwt ⊢; omega
          · exact (rn (by simp [root,head,ha,Ne.symm hc,Arithmetic.addZero])).elim
      · exact (rn (by simp [root,head,ha,ha',Arithmetic.addZero])).elim
  · exact hw _ hp

/-- Reflection in Lemma 2.14(ii). Stability is the opposite inclusion,
proved independently on the generators by the Lambda identity. -/
theorem reflect_bounded (field : ConstantField F q)
    (stable : ∀ p : Tuple → F, HPlus q p → HPlus q (star (q-1) p))
    (w m : Nat) (p : Tuple → F) (hw : Supported w p) (hm : Above m p)
    (hstar : HPlus q (star (q-1) p)) : HPlus q p := by
  have empty := empty_zero field _ w p hw hstar
  cases m with
  | zero =>
    have z : p = fun _ => 0 := by
      funext t
      cases t with
      | nil => exact empty
      | cons a t =>
        cases a with
        | zero => exact support_zero hw _ (by intro h; have := h.1 0 (by simp); omega)
        | succ a => exact hm _ (by omega) _
    rw [z]; exact .zero
  | succ m =>
    cases m with
    | zero =>
      let r : Tuple → F := fun t => p (1::t)
      have h1 : p = head 1 r := by
        funext s
        cases s with
        | nil => exact empty
        | cons a t =>
          by_cases ha : a=1
          · simp [head,r,ha]
          · rw [head, if_neg (Ne.symm ha)]
            by_cases hz : a=0
            · subst a; exact support_zero hw _ (by intro h; have := h.1 0 (by simp); omega)
            · exact hm _ (by omega) _
      have lower : Supported (w-1) r := by
        intro s nz
        obtain ⟨valid,wt⟩ := hw (1::s) nz
        exact ⟨fun a ha => valid _ (List.mem_cons_of_mem _ ha),by simp only [weight] at wt; omega⟩
      rw [h1] at hstar ⊢
      by_cases hw0 : w = 0
      · have eqn : r = fun _ => 0 := by
          funext t
          apply support_zero hw
          simp only [weight]; omega
        rw [eqn,head_zero]; exact .zero
      · exact .cons 0 (reflect_bounded field stable (w-1) (w-1) r lower (above_of_supported lower)
          (peel_one field r hstar))
    | succ b =>
      have hroot := top_root field p b (b+2) (by omega) hm hstar
      have trstar : HPlus q (star (q-1) (trim b p)) := by
        unfold trim
        rw [star_add,star_neg field.add_neg]
        exact .add hstar (.neg (stable _ hroot))
      have htr := reflect_bounded field stable w (b+1) (trim b p) (trim_supported field w b p hw)
        (trim_above field b p hm) trstar
      have H := HPlus.add htr hroot
      have cancel (x y : F) : (x+(-y))+y = x := by
        rw [Arithmetic.addAssoc,Arithmetic.addComm (-y),field.add_neg,Arithmetic.addZero]
      simpa only [trim,cancel] using H
termination_by (w,m)
decreasing_by all_goals simp_wf; all_goals omega

theorem reflect (field : ConstantField F q)
    (stable : ∀ v : Tuple → F, HPlus q v → HPlus q (star (q-1) v))
    {w : Nat} (p : Tuple → F) (hw : Supported w p) :
    HPlus q (star (q-1) p) → HPlus q p :=
  reflect_bounded field stable w w p hw (above_of_supported hw)

end Megaera.Saturation
