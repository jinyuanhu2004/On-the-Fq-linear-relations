import Megaera.FourShapes
import Megaera.FourCases

/-! The bounds on v₁,…,vₙ,b in Case II on page 23, derived from the
explicit shapes in Lemma 4.1. -/
namespace Megaera.FourBoundary
open Megaera.FourReduction Megaera.FourMinimum

private theorem valid_join {s t : Tuple} (hs : Valid s) (ht : Valid t) : Valid (s++t) :=
  fun a ha => (List.mem_append.mp ha).elim (hs a) (ht a)

private theorem singleton_valid {a : Nat} (ha : 0 < a) : Valid [a] := by
  intro x hx; obtain rfl := List.mem_singleton.mp hx; exact ha

private theorem shift_last (k : Nat) (s : Tuple) (b : Nat) :
    addLast k (s++[b]) = s++[k+b] := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    cases s with
    | nil => rfl
    | cons c s => exact congrArg (a::·) ih

private theorem weight_head (q : Nat) (a : Tuple) (hn : a ≠ []) :
    weight (raiseFirst q (incLast a)) = weight a + q + 1 := by
  cases a with
  | nil => contradiction
  | cons z a =>
    have wi := incLast_weight z a
    have hd := Triangular.incLast_length z a
    cases he : incLast (z::a) with
    | nil => simp [he] at hd
    | cons c l =>
      simp only [he,weight] at wi
      simp only [raiseFirst,weight]; omega

private theorem head_join (q : Nat) (u v : Tuple) (hu : u≠[]) :
    raiseFirst q (u++v) = raiseFirst q u ++ v := by cases u <;> simp_all [raiseFirst]


/-- An illegal tuple (h, {}^{q+}a^{+1}, v, b) has the bounds needed to
choose the base tuple for λ. If b=q−1 then v ends in 1. -/
theorem case_II_bounds (q : Nat) (hq : 2 ≤ q) (h a v : Tuple) (b : Nat)
    (hh : Valid h) (ha : Valid a) (hn : a ≠ []) (hv : Valid v) (hb : 0 < b)
    (no : ¬ Shape q (weight (h ++ (raiseFirst q (incLast a) ++ (v++[b]))))
      (h ++ (raiseFirst q (incLast a) ++ (v++[b])))) :
    (∀ x ∈ v, x ≤ q) ∧ b ≤ q-1 ∧ (b=q-1 → ∃ p, v=p++[1]) := by
  have wa := weight_head q a hn
  have bounded (x : Nat) (hx : x ∈ v) : x ≤ q := by
    apply Classical.byContradiction; intro bad
    obtain ⟨p,r,eq⟩ := List.append_of_mem hx
    have xp : 0 < x-q := by omega
    have pv : Valid p := fun i hi => hv i (eq ▸ List.mem_append_left _ hi)
    have rv : Valid r := fun i hi => hv i (eq ▸ List.mem_append_right _ (List.mem_cons_of_mem _ hi))
    apply no
    have cand := Shape.difference (q:=q) h a (p++[x-q]) (r++[b]) hh ha hn
      (valid_join pv (singleton_valid xp)) (by simp) (valid_join rv (singleton_valid hb))
      (w:=weight (h ++ (raiseFirst q (incLast a) ++ (v++[b])))) (by
        rw [eq]; simp only [weight_append,weight] at *; omega)
    simpa only [eq,shift_last,show q+(x-q)=x by omega,List.append_assoc,List.singleton_append,
      List.cons_append] using cand
  have small : b ≤ q-1 := by
    apply Classical.byContradiction; intro bad
    have bp : 0 < b-(q-1) := by omega
    apply no
    have cand := Shape.general (q:=q) h a (v++[b-(q-1)]) hh ha hn
      (valid_join hv (singleton_valid bp))
      (w:=weight (h ++ (raiseFirst q (incLast a) ++ (v++[b])))) (by
        simp only [weight_append,weight] at *; omega)
    simpa only [shift_last,show q-1+(b-(q-1))=b by omega] using cand
  refine ⟨bounded,small,?_⟩
  intro eq
  subst b
  cases hvr : v.reverse with
  | nil =>
    have ev : v=[] := List.reverse_eq_nil_iff.mp hvr
    subst v
    apply False.elim; apply no
    exact Shape.general h a [] hh ha hn (by simp [Valid]) (by
      simp only [List.nil_append,weight_append,weight] at *; omega)
  | cons c rest =>
    have ev : v=rest.reverse++[c] := by simpa using congrArg List.reverse hvr
    have cp := hv c (ev ▸ List.mem_append_right _ (by simp))
    by_cases hc : c=1
    · exact ⟨rest.reverse,by simpa [hc] using ev⟩
    apply False.elim; apply no
    let s := incLast a ++ (rest.reverse++[c-1])
    have si : incLast s = incLast a ++ (rest.reverse++[c]) := by
      rw [show s=(incLast a++rest.reverse)++[c-1] by simp [s],FourCases.incLast_concat,
        show c-1+1=c by omega,List.append_assoc]
    have ia : Valid (incLast a) := fun _ hi => endings_valid a ha _ (by
      cases a <;> simp_all [endings]) _ hi
    have ian : incLast a ≠ [] := by cases a with
      | nil => contradiction
      | cons a tail => intro he; have := Triangular.incLast_length a tail; simp [he] at this
    have vp : Valid rest.reverse := fun i hi => hv i (ev ▸ List.mem_append_left _ hi)
    have ss : Valid s := valid_join ia (valid_join vp (singleton_valid (by omega)))
    have localwt : weight (incLast a)=weight a+1 := by cases a with
      | nil => contradiction
      | cons a t => exact incLast_weight a t
    have cand := Shape.general (q:=q) h s [] hh ss (by simp [s]) (by simp [Valid])
      (w:=weight (h ++ (raiseFirst q (incLast a) ++ (v++[q-1])))) (by
        rw [ev]; simp only [s,weight_append,weight] at *; omega)
    simpa only [si,head_join q (incLast a) _ ian,addLast,ev,List.append_assoc] using cand

end Megaera.FourBoundary
