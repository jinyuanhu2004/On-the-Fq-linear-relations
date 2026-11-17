import Megaera.SplitKernel

/-! The algebraic basis in Lemma 2.4. Values may be prescribed independently
on TT tuples and on L-rows with bounded prefix. There is exactly one extension
to the valid tuples. Every step preserves weight. -/
namespace Megaera.CanonicalBasis
open Megaera.Splitting Megaera.SplitKernel

variable {V : Type u} [Add V] [Sub V]

/-- A prefix already read by the algorithm consists of entries at most q. -/
def extend (q : Nat) (hq : 0 < q) (b : Tuple → V) (g : Tuple → Tuple → V)
    (p : Tuple) (s : Tuple) : V :=
  match s with
  | [] => b p
  | a::t =>
    if q < a then g p ((a-q)::t) - extend q hq b g (p++[q]) ((a-q)::t)
    else if a = q ∧ t = [] then g p []
    else extend q hq b g (p++[a]) t
termination_by (weight s, s.length)
decreasing_by all_goals simp_wf <;> simp [weight] <;> omega

omit [Add V] in
private theorem skip (q : Nat) (hq : 0 < q) (b : Tuple → V) (g : Tuple → Tuple → V)
    (p h t : Tuple) (hb : ∀ a ∈ h, a ≤ q) (hn : t ≠ []) :
    extend q hq b g p (h++t) = extend q hq b g (p++h) t := by
  induction h generalizing p with
  | nil => simp
  | cons a h ih =>
    have ha := hb a (by simp)
    have hne : h ++ t ≠ [] := fun he => hn (List.append_eq_nil_iff.mp he).2
    rw [List.cons_append, extend, if_neg (by omega), if_neg (fun e => hne e.2),
      ih (p++[a]) (fun j hj => hb j (List.mem_cons_of_mem _ hj))]
    simp

omit [Add V] in
theorem on_TT (q : Nat) (hq : 0 < q) (b : Tuple → V) (g : Tuple → Tuple → V)
    (s : Tuple) (hs : TT q s) : extend q hq b g [] s = b s := by
  rcases hs with rfl | ⟨h,z,rfl,_,hb,_,hz⟩
  · rw [extend]
  · rw [skip q hq b g [] h [z] hb (by simp), List.nil_append, extend,
      if_neg (by omega), if_neg (fun e => (by omega : z ≠ q) e.1), extend]

theorem on_canonical (laws : Subtraction V) (q : Nat) (hq : 0 < q)
    (b : Tuple → V) (g : Tuple → Tuple → V) (h t : Tuple)
    (hb : ∀ a ∈ h, a ≤ q) (ht : Valid t) :
    onRow q (extend q hq b g []) h t = g h t := by
  cases t with
  | nil =>
    simp only [onRow, skip q hq b g [] h [q] hb (by simp), List.nil_append]
    rw [extend, if_neg (by omega), if_pos ⟨rfl,rfl⟩]
  | cons r t =>
    have hr := ht r (by simp)
    simp only [onRow, skip q hq b g [] h ((q+r)::t) hb (by simp),
      skip q hq b g [] h (q::r::t) hb (by simp), List.nil_append]
    rw [extend, if_pos (by omega), Nat.add_sub_cancel_left]
    have es : extend q hq b g h (q::r::t) = extend q hq b g (h++[q]) (r::t) := by
      rw [extend, if_neg (by omega), if_neg (by simp)]
    rw [es, laws.sub_add]

private theorem depth_bound (s : Tuple) (hs : Valid s) : s.length ≤ weight s := by
  induction s with
  | nil => exact Nat.le_refl _
  | cons a s ih =>
    have ha := hs a (by simp)
    have hb := ih (fun j hj => hs j (List.mem_cons_of_mem _ hj))
    simp only [List.length_cons, weight]; omega

/-- Uniqueness uses only the canonical rows, including the terminal row. -/
theorem unique (laws : Subtraction V) (q : Nat) (hq : 0 < q)
    (f k : Tuple → V) (tt : ∀ s, TT q s → f s = k s)
    (rows : ∀ h t, Valid h → (∀ a ∈ h, a ≤ q) → Valid t →
      onRow q f h t = onRow q k h t) (s : Tuple) (hs : Valid s) : f s = k s := by
  by_cases ht : TT q s
  · exact tt s ht
  obtain ⟨h,t,he,hv,hb,tv⟩ := canonical_source_surjective q s hs ht
  cases t with
  | nil => simpa only [← he, source] using rows h [] hv hb tv
  | cons r t =>
    have hr := tv r (by simp)
    have valid : Valid (h ++ q :: r :: t) := by
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hv a ha
      · rcases List.mem_cons.mp ha with rfl | ha
        · exact hq
        · exact tv a ha
    have ih := unique laws q hq f k tt rows _ valid
    have eqr := rows h (r::t) hv hb tv
    simp only [onRow] at eqr
    rw [← ih] at eqr
    have cancel := congrArg (fun z => z - f (h ++ q :: r :: t)) eqr
    simpa only [laws.add_sub, ← he, source] using cancel
termination_by weight s - s.length
decreasing_by
  have hd := depth_bound _ valid
  rw [← he]
  simp only [source, weight_append, weight, List.length_append, List.length_cons] at hd ⊢
  omega

end Megaera.CanonicalBasis
