import Megaera.Cuts

/-! The second cut identity, including all stuffle multiplicities. -/

namespace Megaera.EndingCut

private def value (xs : List A) (g : A → Nat) : Nat := (xs.map g).sum

private theorem val_cons (x : A) (xs : List A) (g : A → Nat) :
    value (x::xs) g = g x + value xs g := rfl

private theorem val_nil (g : A → Nat) : value [] g = 0 := rfl

private theorem sum_append (xs ys : List Nat) : (xs++ys).sum = xs.sum + ys.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih,Nat.add_assoc]

private theorem sum_zero (xs : List A) (f : A → Nat) (h : ∀ x ∈ xs, f x=0) : value xs f=0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change f x + value xs f = 0
    rw [h x (by simp),ih (fun _ hm => h _ (List.mem_cons_of_mem _ hm)),Nat.add_zero]

private theorem val_append (xs ys : List A) (g : A → Nat) :
    value (xs++ys) g = value xs g + value ys g := by simp [value,sum_append]

private theorem val_map (xs : List A) (f : A → B) (g : B → Nat) :
    value (xs.map f) g = value xs (fun x => g (f x)) := by simp [value,List.map_map,Function.comp_def]

private theorem val_flat (xs : List A) (f : A → List B) (g : B → Nat) :
    value (xs.flatMap f) g = value xs (fun x => value (f x) g) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [List.flatMap_cons,val_append,ih]
    rfl

private theorem val_add (xs : List A) (f g : A → Nat) :
    value xs (fun x => f x + g x) = value xs f + value xs g := by
  induction xs with
  | nil => simp [value]
  | cons a xs ih => simp [value] at ih ⊢; omega

private def convolve (s t : Tuple) (f : Tuple → Tuple → Nat) : Nat :=
  value (Cuts.cuts t) (fun p => value (quasiShuffle s p.1) (fun x => f x p.2))

private theorem cv_cons (a b : Nat) (s t : Tuple) (f : Tuple → Tuple → Nat) :
    convolve (a::s) (b::t) f = convolve s (b::t) (fun x v => f (a::x) v) +
      convolve (a::s) t (fun x v => f (b::x) v) + convolve s t (fun x v => f ((a+b)::x) v) := by
  simp only [convolve,Cuts.cuts,val_cons,val_nil,val_map,quasiShuffle_nil_right,
    quasiShuffle.eq_3,val_append,val_add,Nat.add_zero,Nat.add_assoc]

private theorem cv_nil (b : Nat) (t : Tuple) (f : Tuple → Tuple → Nat) :
    convolve [] (b::t) f = f [] (b::t) + convolve [] t (fun x v => f (b::x) v) := by
  simp [convolve,Cuts.cuts,value,Function.comp_def,List.map_map]

private theorem cv_add (s t : Tuple) (f g : Tuple → Tuple → Nat) :
    convolve s t (fun x v => f x v + g x v) = convolve s t f + convolve s t g := by
  simp only [convolve,val_add]

private theorem cv_delta (s t : Tuple) (g : Tuple → Nat) :
    convolve s t (fun x v => if x=[] then g v else 0) = if s=[] then g t else 0 := by
  cases s with
  | nil =>
    cases t with
    | nil => simp [convolve,Cuts.cuts,value]
    | cons b t =>
      rw [cv_nil]
      simp only [convolve,quasiShuffle_nil_left, List.cons_ne_nil,if_false,if_true]
      rw [sum_zero _ _ (by intros; rfl),Nat.add_zero]
  | cons a s =>
    have nonempty (u : Tuple) : ∀ x ∈ quasiShuffle (a::s) u, x ≠ [] := by
      intro x hx
      cases u with
      | nil => simp_all
      | cons b u =>
        simp only [quasiShuffle.eq_3,List.mem_append,List.mem_map] at hx
        rcases hx with ((⟨_,_,rfl⟩ | ⟨_,_,rfl⟩) | ⟨_,_,rfl⟩) <;> simp
    have e (u v : Tuple) : value (quasiShuffle (a::s) u) (fun x => if x=[] then g v else 0) = 0 := by
      exact sum_zero _ _ (fun x hx => if_neg (nonempty u x hx))
    simp only [convolve,e,List.cons_ne_nil,if_false]
    apply sum_zero
    intros
    rfl

private def block (g : Tuple → Nat) (x v : Tuple) := value (endings x) (fun y => g (y++v))

private theorem block_shift (a : Nat) (g : Tuple → Nat) (x v : Tuple) :
    block g (a::x) v = block (fun z => g (a::z)) x v + (if x=[] then g ((a+1)::v) else 0) := by
  cases x with
  | nil => simp [block,value,endings,incLast,Nat.add_comm]
  | cons b x => simp [block,value,endings,incLast]

private def cut (s t : Tuple) (g : Tuple → Nat) := convolve s t (block g)

private theorem shifted (a : Nat) (s t : Tuple) (g : Tuple → Nat) :
    convolve s t (fun x v => block g (a::x) v) =
    cut s t (fun x => g (a::x)) + (if s=[] then g ((a+1)::t) else 0) := by
  simp only [block_shift,cv_add,cv_delta,cut]

private def lhs (s t : Tuple) (g : Tuple → Nat) :=
  value (endings s) (fun y => value (quasiShuffle y t) g)

private theorem main (s t : Tuple) (g : Tuple → Nat) : lhs s t g = cut s t g := by
  cases t with
  | nil => simp [lhs,cut,convolve,Cuts.cuts,block,value]
  | cons b t =>
    cases s with
    | nil =>
      have ih := main [] t (fun x => g (b::x))
      change _ = convolve [] (b::t) (block g)
      rw [cv_nil,shifted,←ih]
      simp [lhs,endings,block,value,quasiShuffle.eq_3,sum_append,List.map_map,Function.comp_def,Nat.add_comm]
    | cons a s =>
      change _ = convolve (a::s) (b::t) (block g)
      rw [cv_cons,shifted,shifted,shifted]
      rw [←main s (b::t) (fun x => g (a::x)),←main (a::s) t (fun x => g (b::x)),
          ←main s t (fun x => g ((a+b)::x))]
      cases s with
      | nil =>
        simp [lhs,endings,incLast,value,quasiShuffle.eq_3,sum_append,List.map_map,
          Function.comp_def,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
      | cons c s =>
        have peel (k : Nat) (l : Tuple) : value (quasiShuffle (k::l) (b::t)) g =
            value (quasiShuffle l (b::t)) (fun x => g (k::x)) +
            value (quasiShuffle (k::l) t) (fun x => g (b::x)) +
            value (quasiShuffle l t) (fun x => g ((k+b)::x)) := by
          rw [quasiShuffle.eq_3]
          simp only [val_append,val_map]
        simp only [lhs,endings,incLast,List.cons_append,val_cons,val_nil,Nat.add_zero,
          List.cons_ne_nil,if_false]
        rw [peel,peel]
        ac_rfl
termination_by s.length + t.length
decreasing_by all_goals simp_wf <;> omega

private theorem count_value (x : Tuple) (xs : List Tuple) :
    @List.count Tuple instBEqOfDecidableEq x xs = value xs (fun y => if y=x then 1 else 0) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    by_cases h : a=x <;> simp_all [value,List.count_cons,instBEqOfDecidableEq,Nat.add_comm]

/-- Equation (2.6) as a permutation, so the equality includes multiplicities. -/
theorem endings_cut (s t : Tuple) :
    ((endings s).flatMap (fun y => quasiShuffle y t)).Perm
      ((Cuts.cuts t).flatMap (fun p => (quasiShuffle s p.1).flatMap
        (fun y => (endings y).map (fun z => z++p.2)))) := by
  apply List.perm_iff_count.mpr
  intro x
  rw [count_value,count_value]
  simp only [val_flat,val_map]
  exact main s t _

end Megaera.EndingCut
