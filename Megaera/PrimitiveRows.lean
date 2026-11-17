import Megaera.Tuples

/-! Explicit signed marked-row witness for the unprefixed primitive pair
in Theorem 2.13. Permutations compare lists with their full multiplicities
before reduction in the coefficient field. -/

namespace Megaera.PrimitiveRows

private theorem interleave {α β} (xs : List α) (f g : α → β) :
    (xs.map f ++ xs.map g).Perm (xs.flatMap (fun x => [f x, g x])) := by
  induction xs with
  | nil => exact .refl _
  | cons x xs ih =>
    apply List.Perm.cons (f x)
    exact List.perm_middle.trans (ih.cons (g x))

private theorem start_append (q a : Nat) (s v : Tuple) :
    start q ((a :: s) ++ v) = (start q (a :: s)).map (fun x => x ++ v) := by
  rfl

private theorem interchange_endings (q a : Nat) (s : Tuple) :
    ((start q (a :: s)).flatMap endings).Perm
      ((endings (a :: s)).flatMap (start q)) := by
  cases s with
  | nil =>
    simp [start, endings, incLast, Nat.add_assoc]
    exact .swap _ _ _
  | cons b s =>
    simp [start, endings, incLast]
    exact .swap _ _ _

/-- L is applied to the row (L(∅,s),t) on the left and the row
(∅,(s,L(∅,t))) on the right. Their signed difference lies in ker L. -/
theorem primitive_L_cancels (q a : Nat) (s t : Tuple) :
    ((start q (a::s)).flatMap (fun h => L q h t)).Perm
    ((L q (a::s) t).flatMap (fun v => L q [] v)) := by
  simp only [L, List.nil_append, List.map_id_fun, List.flatMap_map]
  simp only [start_append]
  simpa [start] using interleave (start q t)
    (fun v => (q::a::s) ++ v) (fun v => ((q+a)::s) ++ v)

private theorem start_on_concat (q a : Nat) (s : Tuple) (vs : List Tuple) :
    (concatenate (start q (a::s)) vs).Perm
      ((vs.map (fun y => (a::s) ++ y)).flatMap (start q)) := by
  simp only [List.flatMap_map, start_append]
  simpa [start, concatenate] using interleave vs
    (fun v => (q::a::s) ++ v) (fun v => ((q+a)::s) ++ v)

private theorem start_on_concats (q : Nat) (xs vs : List Tuple)
    (hne : ∀ x ∈ xs, x ≠ []) :
    (concatenate (xs.flatMap (start q)) vs).Perm
      ((concatenate xs vs).flatMap (start q)) := by
  induction xs with
  | nil => exact .refl _
  | cons x xs ih =>
    have hx := hne x (by simp)
    cases x with
    | nil => contradiction
    | cons a s =>
      have ht := ih (fun z hz => hne z (List.mem_cons_of_mem _ hz))
      simpa only [concatenate, List.flatMap_append, List.flatMap_cons] using
        (start_on_concat q a s vs).append ht

/-- H applied to the positive row gives the positive (first) component
of the primitive pair up to permutation. -/
theorem primitive_H_positive (q a : Nat) (s t : Tuple) :
    ((start q (a::s)).flatMap (fun h => H q h t)).Perm
    ((H q (a::s) t).flatMap (start q)) := by
  let vs := quasiShuffle [q-1] t
  have hswap := (interchange_endings q a s).flatMap_right
    (fun h => vs.map (fun y => h ++ y))
  have hn : ∀ x ∈ endings (a::s), x ≠ [] := by
    cases s <;> simp [endings, incLast]
  have hfinal := start_on_concats q (endings (a::s)) vs hn
  apply List.Perm.trans _ hfinal
  simpa only [H, concatenate, List.flatMap_assoc, vs] using hswap

/-- H applied to the negative row gives the shifted component, with the
minus sign represented by its position in the signed difference. -/
theorem primitive_H_negative (q : Nat) (s t : Tuple) :
    ((L q s t).flatMap (fun v => H q [] v)) =
    ((L q s t).flatMap (fun v => (quasiShuffle [q-1] v).map (List.cons 1))) := by
  simp [H, endings, concatenate]

private theorem incLast_append_nonempty (h : Tuple) (a : Nat) (s : Tuple) :
    incLast (h ++ a::s) = h ++ incLast (a::s) := by
  induction h with
  | nil => rfl
  | cons b h ih =>
    cases h with
    | nil => rfl
    | cons k h => exact congrArg (List.cons b) ih

private theorem endings_append_nonempty (h : Tuple) (a : Nat) (s : Tuple) :
    endings (h ++ a::s) = (endings (a::s)).map (fun v => h ++ v) := by
  cases h with
  | nil => simp
  | cons b h =>
    simp only [List.cons_append, endings, List.map_cons, List.map_nil]
    rw [← List.cons_append, incLast_append_nonempty]
    simp [List.append_assoc]

private theorem L_prepend (q : Nat) (h u v : Tuple) :
    L q (h ++ u) v = (L q u v).map (fun x => h ++ x) := by
  simp [L, List.map_map, Function.comp_def, List.append_assoc]

theorem H_prepend_nonempty (q : Nat) (h : Tuple) (a : Nat) (s v : Tuple) :
    H q (h ++ a::s) v = (H q (a::s) v).map (fun x => h ++ x) := by
  simp only [H, endings_append_nonempty, concatenate, List.flatMap_map, List.map_flatMap,
    List.map_map, Function.comp_def, List.append_assoc]

theorem prefixed_L_cancels (q a : Nat) (h s t : Tuple) :
    ((start q (a::s)).flatMap (fun u => L q (h ++ u) t)).Perm
    ((L q (a::s) t).flatMap (fun v => L q h v)) := by
  have hl (v : Tuple) : L q h v = (L q [] v).map (fun x => h ++ x) := by
    simpa using L_prepend q h [] v
  simpa only [L_prepend, hl, List.map_flatMap] using
    (primitive_L_cancels q a s t).map (fun x => h ++ x)

theorem prefixed_H_positive (q a : Nat) (h s t : Tuple) :
    ((start q (a::s)).flatMap (fun u => H q (h ++ u) t)).Perm
    (((H q (a::s) t).flatMap (start q)).map (fun x => h ++ x)) := by
  have hp := (primitive_H_positive q a s t).map (fun x => h ++ x)
  simpa only [start, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    H_prepend_nonempty, List.map_append] using hp

theorem collect_by_prefix (hs : List Tuple) (f : Tuple → List Tuple) (xs : List Tuple) :
    (xs.flatMap (fun v => concatenate hs (f v))).Perm
      (concatenate hs (xs.flatMap f)) := by
  induction hs with
  | nil => simp [concatenate]
  | cons h hs ih =>
    simp only [concatenate, List.flatMap_cons, List.map_flatMap] at *
    have combine {α β : Type} (ys : List α) (g k : α → List β) :
        (ys.flatMap (fun y => g y ++ k y)).Perm (ys.flatMap g ++ ys.flatMap k) := by
      induction ys with
      | nil => exact .refl _
      | cons y ys ih =>
        simp only [List.flatMap_cons, List.append_assoc]
        apply List.Perm.append_left
        exact (ih.append_left _).trans (List.perm_append_comm_assoc _ _ _)
    exact (combine xs _ _).trans (ih.append_left _)

theorem prefixed_H_negative (q : Nat) (h s t : Tuple) :
    ((L q s t).flatMap (fun v => H q h v)).Perm
      (concatenate (endings h) ((L q s t).flatMap (quasiShuffle [q-1]))) :=
  collect_by_prefix _ _ _

private def prefixSum (a : Nat) (p : FormalSum K) : FormalSum K :=
  p.map (fun z => (z.1, a :: z.2))

private theorem prefix_expand (a : Nat) (p : FormalSum K) :
    expand (triangle [a]) p = prefixSum a p := by
  induction p with
  | nil => rfl
  | cons z p ih =>
    simp only [expand, prefixSum, List.flatMap_cons, triangle, quasiShuffle_nil_left,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append] at *
    rw [ih]

private theorem fixed_prefix (a : Nat) (p : FormalSum K) :
    bOp [a] (p,[]) = (prefixSum a p, []) := by
  change ((expand (triangle [a]) p ++ []) ++ [], []) = _
  rw [prefix_expand, List.append_nil, List.append_nil]

private theorem weight_one_diamond (a : Nat) (k : K) (ts : List Tuple) :
    expand (diamond [a]) (withCoeff k (ts.map (List.cons 1))) =
    withCoeff k (ts.map (List.cons (a+1))) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [expand, withCoeff, List.map_cons, List.flatMap_cons, diamond,
      quasiShuffle_nil_left, List.map_nil, List.cons_append, List.nil_append] at *
    rw [ih]

private theorem prefix_coeff (a : Nat) (k : K) (l : List Tuple) :
    prefixSum a (withCoeff k l) = withCoeff k (l.map (List.cons a)) := by
  simp [prefixSum, withCoeff, List.map_map, Function.comp_def]

/-- Prefix a lifted pair with independent constant and shifted coefficients. -/
theorem bStar_expansion_coeff (base shifted : K) (h : Tuple) (pos tails : List Tuple) :
    liftPair (bStar h (withCoeff base pos,
      withCoeff shifted (tails.map (List.cons 1)))) =
    withCoeff base (pos.map (fun x => h ++ x)) ++
      withCoeff shifted (concatenate (endings h) tails) := by
  induction h with
  | nil => simp [liftPair, bStar, endings, concatenate]
  | cons a h ih =>
    cases h with
    | nil =>
      simp only [bStar, bOp, prefix_expand, weight_one_diamond, liftPair, List.append_nil,
        prefix_coeff]
      simp only [endings, incLast, concatenate, List.flatMap_cons, List.flatMap_nil,
        withCoeff, List.map_append, List.map_map, List.append_assoc, Function.comp_def,
        List.map_nil, List.append_nil]
      rfl
    | cons b h =>
      let r := bStar (b::h) (withCoeff base pos,
        withCoeff shifted (tails.map (List.cons 1)))
      have hr : r.2 = [] := bStar_fixed _ _ _
      have hfst : r.1 = withCoeff base (pos.map (fun x => (b::h) ++ x)) ++
          withCoeff shifted (concatenate (endings (b::h)) tails) := by
        change r.1 ++ r.2 = _ at ih
        simpa [hr] using ih
      change liftPair (bOp [a] r) = _
      have hp : r = (r.1,[]) := Prod.ext rfl hr
      conv => lhs; rw [hp, fixed_prefix]
      simp only [liftPair, List.append_nil, hfst, prefixSum, List.map_append,
        concatenate, withCoeff, List.map_flatMap, List.map_map, Function.comp_def,
        endings, incLast, List.flatMap_cons, List.flatMap_nil]
      rfl

/-- Apply an outer B* to a pair with shifted component -∑(1,m).
The formula is for its lift and includes the identity at h=∅. -/
theorem bStar_expansion [OfNat K 1] [Neg K] (h : Tuple) (pos tails : List Tuple) :
    liftPair (bStar h (withCoeff (1 : K) pos,
      withCoeff (-(1 : K)) (tails.map (List.cons 1)))) =
    withCoeff (1 : K) (pos.map (fun x => h ++ x)) ++
      withCoeff (-(1 : K)) (concatenate (endings h) tails) :=
  bStar_expansion_coeff 1 (-1) h pos tails

/-- A concrete signed row certificate simultaneously realizing both components.
The positive labels are (h·u,t) for u in L(∅,s); the negative labels are
(h,v) for v in L(s,t). The displayed positive-minus-negative H expansion
is the lift of B*_h P(s;t), in any characteristic. -/
theorem bStar_generalP_row_certificate [OfNat K 1] [Neg K] (q a : Nat) (h s t : Tuple) :
    ((start q (a::s)).flatMap (fun u => L q (h ++ u) t)).Perm
      ((L q (a::s) t).flatMap (fun v => L q h v)) ∧
    (withCoeff (1 : K) ((start q (a::s)).flatMap (fun u => H q (h ++ u) t)) ++
      withCoeff (-(1 : K)) ((L q (a::s) t).flatMap (fun v => H q h v))).Perm
        (liftPair (bStar h (generalP q (a::s) t))) := by
  refine ⟨prefixed_L_cancels _ _ _ _ _, ?_⟩
  unfold generalP
  rw [← List.map_flatMap, bStar_expansion]
  exact ((prefixed_H_positive q a h s t).map (fun x => ((1 : K),x))).append
    ((prefixed_H_negative q h (a::s) t).map (fun x => (-(1 : K),x)))

end Megaera.PrimitiveRows
