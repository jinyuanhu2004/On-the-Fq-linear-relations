import Megaera.Splitting

/-! # Marked rows and commuting splits (Theorem 2.9)

The theorem `integrate` proves the dual exactness statement. Every assignment
of values to marked pairs satisfying the squares and terminal triangles is the
evaluation of L on a single tuple functional. Its values on irreducible
tuples are set to zero. Only ordinary abelian-group identities are used.
-/

namespace Megaera.SplitKernel

/-- The three abelian-group identities used by the proof are kept explicit
so that neither division nor any characteristic restriction is required. -/
structure Subtraction (V : Type u) [Add V] [Sub V] : Prop where
  sub_add : ∀ a b : V, (a - b) + b = a
  add_sub : ∀ a b : V, (a + b) - b = a
  collect : ∀ a b c d : V, (a - b) + (c - d) = (a + c) - (b + d)

private theorem vcons {a : Nat} {s : Tuple} (h : Valid (a::s)) : Valid s :=
  fun b hb => h b (List.mem_cons_of_mem _ hb)

private theorem vsnoc (h : Tuple) (q : Nat) (hv : Valid h) (hq : 0 < q) : Valid (h ++ [q]) := by
  intro b hb
  rcases List.mem_append.mp hb with hb | hb
  · exact hv b hb
  · simpa only [List.mem_singleton] using (show b = q from List.mem_singleton.mp hb) ▸ hq

/-- Equality of the sums of the positive and negative rows in each local
kernel generator of the paper (both sites split, or the second site is final). -/
structure Compatible [Add V] (q : Nat) (g : Tuple → Tuple → V) : Prop where
  square : ∀ p m t r c, Valid p → Valid m → Valid t → 0 < r → 0 < c →
    g p (r :: (m ++ (q+c)::t)) + g p (r :: (m ++ q::c::t)) =
    g (p ++ (q+r)::m) (c::t) + g (p ++ q::r::m) (c::t)
  triangle : ∀ p m r, Valid p → Valid m → 0 < r →
    g p (r :: (m ++ [q])) = g (p ++ (q+r)::m) [] + g (p ++ q::r::m) []

/-- Read the unprocessed tail left to right. A split contributes its marked
value and reverses the sign of the remaining potential. -/
def potential [Zero V] [Sub V] (q : Nat) (hq : 0 < q) (g : Tuple → Tuple → V)
    (p : Tuple) (s : Tuple) : V :=
  match s with
  | [] => 0
  | a::t =>
    if q < a then g p ((a-q)::t) - potential q hq g (p++[q]) ((a-q)::t)
    else if a = q ∧ t = [] then g p []
    else potential q hq g (p++[a]) t
termination_by (weight s,s.length)
decreasing_by all_goals simp_wf <;> simp [weight] <;> omega

private theorem large [Zero V] [Sub V] (q : Nat) (hq : 0 < q) (g : Tuple → Tuple → V)
    (p t : Tuple) (a : Nat) (ha : q < a) :
    potential q hq g p (a::t) = g p ((a-q)::t) - potential q hq g (p++[q]) ((a-q)::t) := by
  rw [potential, if_pos ha]

private theorem small [Zero V] [Sub V] (q : Nat) (hq : 0 < q) (g : Tuple → Tuple → V)
    (p t : Tuple) (a : Nat) (ha : a ≤ q) (hn : t ≠ []) :
    potential q hq g p (a::t) = potential q hq g (p++[a]) t := by
  rw [potential,if_neg (Nat.not_lt.mpr ha),if_neg (fun h => hn h.2)]

/-- Evaluate the row L(h;t) with a held prefix p. -/
def rowValue [Zero V] [Add V] [Sub V] (q : Nat) (hq : 0 < q)
    (g : Tuple → Tuple → V) (p h : Tuple) : Tuple → V
  | [] => potential q hq g p (h ++ [q])
  | c::t => potential q hq g p (h ++ (q+c)::t) +
            potential q hq g p (h ++ q::c::t)

theorem integrate [Zero V] [Add V] [Sub V] (laws : Subtraction V) (q : Nat) (hq : 0 < q)
    (g : Tuple → Tuple → V) (hg : Compatible q g) (p h t : Tuple)
    (hp : Valid p) (hh : Valid h) (ht : Valid t) :
    rowValue q hq g p h t = g (p++h) t := by
  cases eqH : h with
  | nil =>
    cases t with
    | nil => simp [rowValue, potential]
    | cons c t =>
      have hc := ht c (by simp)
      simp only [rowValue,List.nil_append,List.append_nil]
      rw [large q hq g _ _ (q+c) (by omega), Nat.add_sub_cancel_left,
        small q hq g _ _ q (Nat.le_refl _) (by simp), laws.sub_add]
  | cons a h =>
    have hh' := eqH ▸ hh
    have htail := vcons hh'
    have ha := hh' a (by simp)
    by_cases hbig : q < a
    · have hr : 0 < a-q := by omega
      have hv : Valid ((a-q)::h) := by
        intro i hi
        rcases List.mem_cons.mp hi with rfl | hi
        · exact hr
        · exact htail i hi
      have ih := integrate laws q hq g hg (p++[q]) ((a-q)::h) t (vsnoc p q hp hq) hv ht
      have he : q + (a-q) = a := by omega
      cases t with
      | nil =>
        have sq := hg.triangle p h (a-q) hp htail hr
        simp only [he] at sq
        simp only [rowValue,List.cons_append,List.append_assoc,List.nil_append] at ih ⊢
        rw [large q hq g _ _ a hbig,ih,sq,laws.add_sub]
      | cons c t =>
        have sq := hg.square p h t (a-q) c hp htail (vcons ht) hr (ht c (by simp))
        simp only [he] at sq
        simp only [rowValue,List.cons_append,List.append_assoc,List.nil_append] at ih ⊢
        rw [large q hq g _ _ a hbig,large q hq g _ _ a hbig,laws.collect,ih,sq,laws.add_sub]
    · have hle := Nat.le_of_not_gt hbig
      have ih := integrate laws q hq g hg (p++[a]) h t (vsnoc p a hp ha) htail ht
      cases t with
      | nil =>
        simp only [rowValue,List.cons_append,List.append_assoc,List.nil_append] at ih ⊢
        rw [small q hq g _ _ a hle (by simp),ih]
      | cons c t =>
        simp only [rowValue,List.cons_append,List.append_assoc,List.nil_append] at ih ⊢
        rw [small q hq g _ _ a hle (by simp),small q hq g _ _ a hle (by simp),ih]
termination_by weight h
decreasing_by all_goals rw [eqH]; all_goals simp only [weight]; all_goals omega

/-- Evaluation of an L-row from values attached to its tuple terms. -/
def onRow [Add V] (q : Nat) (f : Tuple → V) (h : Tuple) : Tuple → V
  | [] => f (h ++ [q])
  | c::t => f (h ++ (q+c)::t) + f (h ++ q::c::t)

theorem onRow_compatible [Add V] [Std.Associative (α := V) (· + ·)]
    [Std.Commutative (α := V) (· + ·)] (q : Nat) (f : Tuple → V) :
    Compatible q (onRow q f) := by
  constructor
  · intros
    simp only [onRow,List.append_assoc,List.cons_append,List.nil_append]
    ac_rfl
  · intros
    simp only [onRow,List.append_assoc,List.cons_append,List.nil_append]

/-- Dual exactness, in both directions. No dimension bound or abstract
tuple-specific compatibility premise is needed to characterize the image. -/
theorem compatible_iff [Zero V] [Add V] [Sub V] [Std.Associative (α := V) (· + ·)]
    [Std.Commutative (α := V) (· + ·)] (laws : Subtraction V) (q : Nat) (hq : 0 < q)
    (g : Tuple → Tuple → V) :
    Compatible q g ↔ ∃ f : Tuple → V, ∀ h t, Valid h → Valid t → onRow q f h t = g h t := by
  constructor
  · intro hg
    refine ⟨potential q hq g [], ?_⟩
    intro h t hh ht
    have eq := integrate laws q hq g hg [] h t (by simp [Megaera.Valid]) hh ht
    cases t <;> simpa only [rowValue,onRow,List.nil_append] using eq
  · rintro ⟨f,hf⟩
    have on := onRow_compatible q f
    have consValid {a : Nat} {s : Tuple} (ha : 0 < a) (hs : Valid s) : Valid (a::s) :=
      fun i hi => (List.mem_cons.mp hi).elim (fun hi => hi ▸ ha) (hs i)
    have appendValid {u v : Tuple} (hu : Valid u) (hv : Valid v) : Valid (u++v) :=
      fun i hi => (List.mem_append.mp hi).elim (hu i) (hv i)
    have ve : Valid [] := by simp [Megaera.Valid]
    constructor
    · intro p m t r c hp hm ht hr hc
      have eq := on.square p m t r c hp hm ht hr hc
      rw [hf _ _ hp (consValid hr (appendValid hm (consValid (by omega) ht))),
          hf _ _ hp (consValid hr (appendValid hm (consValid hq (consValid hc ht)))),
          hf _ _ (appendValid hp (consValid (by omega) hm)) (consValid hc ht),
          hf _ _ (appendValid hp (consValid hq (consValid hr hm))) (consValid hc ht)] at eq
      exact eq
    · intro p m r hp hm hr
      have eq := on.triangle p m r hp hm hr
      rw [hf _ _ hp (consValid hr (appendValid hm (consValid hq ve))),
          hf _ _ (appendValid hp (consValid (by omega) hm)) ve,
          hf _ _ (appendValid hp (consValid hq (consValid hr hm))) ve] at eq
      exact eq

end Megaera.SplitKernel
