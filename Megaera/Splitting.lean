import Megaera.Tuples

/-! # The canonical splitting calculation of §2.3

A split replaces an entry q+r by q,r and changes the sign. A final q
represents zero. The calculation below takes place over the integers before
any change of coefficient field. It applies also in characteristic two.
-/

namespace Megaera.Splitting

/-- Count the splits of one entry and list the resulting entries. -/
def chunk (q : Nat) (hq : 0 < q) (n : Nat) : Nat × Tuple :=
  if q < n then
    let (k,t) := chunk q hq (n-q)
    (k+1,q::t)
  else (0,[n])
termination_by n
decreasing_by omega

theorem chunk_small (q : Nat) (hq : 0 < q) (n : Nat) (hn : n ≤ q) :
    chunk q hq n = (0,[n]) := by
  rw [chunk, if_neg (Nat.not_lt.mpr hn)]

theorem chunk_split (q : Nat) (hq : 0 < q) (r : Nat) (hr : 0 < r) :
    chunk q hq (q+r) = ((chunk q hq r).1+1, q :: (chunk q hq r).2) := by
  rw [chunk, if_pos (by omega : q < q+r), Nat.add_sub_cancel_left]

def expandTuple (q : Nat) (hq : 0 < q) : Tuple → Nat × Tuple
  | [] => (0, [])
  | a::s =>
    let (k,u) := chunk q hq a
    let (l,v) := expandTuple q hq s
    (k + l,u ++ v)

theorem expand_append (q : Nat) (hq : 0 < q) (s t : Tuple) :
    expandTuple q hq (s ++ t) =
      ((expandTuple q hq s).1 + (expandTuple q hq t).1,
       (expandTuple q hq s).2 ++ (expandTuple q hq t).2) := by
  induction s with
  | nil => simp [expandTuple]
  | cons a s ih => simp [expandTuple, ih, Nat.add_assoc, List.append_assoc]

theorem expand_split (q : Nat) (hq : 0 < q) (h t : Tuple) (r : Nat) (hr : 0 < r) :
    expandTuple q hq (h ++ (q+r)::t) =
       ((expandTuple q hq (h ++ q::r::t)).1 + 1,
        (expandTuple q hq (h ++ q::r::t)).2) := by
  simp only [expand_append, expandTuple, chunk_split q hq r hr,
    chunk_small q hq q (Nat.le_refl q)]
  simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Odd split count denotes a minus sign; no term survives a final q. -/
def signedTerm (q : Nat) (k : Nat) (t : Tuple) : Option (Bool × Tuple) :=
  if t.getLast? = some q then none else some (decide (k % 2 = 1), t)

def normalize (q : Nat) (hq : 0 < q) (s : Tuple) : Option (Bool × Tuple) :=
  signedTerm q (expandTuple q hq s).1 (expandTuple q hq s).2

def reverseSign : Option (Bool × Tuple) → Option (Bool × Tuple)
  | none => none
  | some (b,t) => some (!b,t)

private theorem signedTerm_succ (q k : Nat) (t : Tuple) :
    signedTerm q (k+1) t = reverseSign (signedTerm q k t) := by
  unfold signedTerm
  split
  · rfl
  · by_cases h : k % 2 = 1
    · simp [h, show (k+1)%2 ≠ 1 by omega, reverseSign]
    · simp [h, show (k+1)%2 = 1 by omega, reverseSign]

theorem normalize_split (q : Nat) (hq : 0 < q) (h t : Tuple) (r : Nat) (hr : 0 < r) :
    normalize q hq (h ++ (q+r)::t) = reverseSign (normalize q hq (h ++ q::r::t)) := by
  simp only [normalize, expand_split q hq h t r hr, signedTerm_succ]

theorem normalize_terminal (q : Nat) (hq : 0 < q) (h : Tuple) :
    normalize q hq (h ++ [q]) = none := by
  simp [normalize, expand_append, expandTuple, chunk_small q hq q (Nat.le_refl q),
    signedTerm]

theorem expand_bounded (q : Nat) (hq : 0 < q) (s : Tuple) (hs : ∀ a ∈ s, a ≤ q) :
    expandTuple q hq s = (0,s) := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    simp [expandTuple, chunk_small q hq a (hs a (by simp)),
      ih (fun b hb => hs b (List.mem_cons_of_mem _ hb))]

/-- The normalizer restricts to the identity on the TT tuples. -/
theorem normalize_TT (q : Nat) (hq : 0 < q) (s : Tuple) (hs : TT q s) :
    normalize q hq s = some (false,s) := by
  rcases hs with rfl | ⟨h,z,rfl,_,hb,_,hz⟩
  · rfl
  · simp [normalize, expand_append, expand_bounded q hq h hb, expandTuple,
      chunk_small q hq z (Nat.le_of_lt hz), signedTerm, Nat.ne_of_lt hz]

private theorem chunk_bounded (q : Nat) (hq : 0 < q) (a : Nat) (ha : 0 < a) :
    ∀ b ∈ (chunk q hq a).2, 0 < b ∧ b ≤ q := by
  rw [chunk]
  split
  · rename_i h
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨hq,Nat.le_refl _⟩
    · exact chunk_bounded q hq (a-q) (by omega) b hb
  · rename_i h
    simp_all
termination_by a
decreasing_by omega

theorem expand_bounded_valid (q : Nat) (hq : 0 < q) (s : Tuple) (hs : Valid s) :
    ∀ b ∈ (expandTuple q hq s).2, 0 < b ∧ b ≤ q := by
  induction s with
  | nil => simp [expandTuple]
  | cons a s ih =>
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact chunk_bounded q hq a (hs a (by simp)) b hb
    · exact ih (fun i hi => hs i (List.mem_cons_of_mem _ hi)) b hb

theorem normalized_mem_TT (q : Nat) (hq : 0 < q) (s : Tuple) (hs : Valid s)
    (b : Bool) (t : Tuple) (hn : normalize q hq s = some (b,t)) : TT q t := by
  unfold normalize signedTerm at hn
  split at hn
  · contradiction
  · rename_i hl
    have heq := (Option.some.inj hn)
    have ht := congrArg Prod.snd heq
    change (expandTuple q hq s).2 = t at ht
    rw [ht] at hl
    have hb := expand_bounded_valid q hq s hs
    rw [ht] at hb
    cases hlast : t.getLast? with
    | none => exact Or.inl (List.getLast?_eq_none_iff.mp hlast)
    | some z =>
      obtain ⟨u, rfl⟩ := List.getLast?_eq_some_iff.mp hlast
      right
      have hz := hb z (by simp)
      have hz' : z ≠ q := by simpa using hl
      exact ⟨u,z,rfl,fun i hi => (hb i (by simp [hi])).1,
        fun i hi => (hb i (by simp [hi])).2,hz.1,by omega⟩

/-- Evaluate a signed normal tuple on prescribed values. -/
def signedValue [Zero V] [Neg V] (f : Tuple → V) : Option (Bool × Tuple) → V
  | none => 0
  | some (true,t) => -(f t)
  | some (false,t) => f t

theorem signedValue_reverse [Zero V] [Neg V] (h₀ : -(0:V) = 0) (h₂ : ∀ y : V, -(-y) = y)
    (f : Tuple → V) (v : Option (Bool × Tuple)) :
    signedValue f (reverseSign v) = -(signedValue f v) := by
  cases v with
  | none => exact h₀.symm
  | some p =>
    obtain ⟨b,t⟩ := p
    cases b <;> simp [reverseSign, signedValue, h₂]

/-- The integral coefficient of a specified TT tuple after reducing an
entire row of L is zero. Thus the calculation is characteristic-independent. -/
theorem normalize_L (q : Nat) (hq : 0 < q) (h t v : Tuple) (ht : Valid t) :
    ((L q h t).map (fun s => signedValue (fun u => if u = v then (1:Int) else 0)
      (normalize q hq s))).sum = 0 := by
  cases t with
  | nil => simp [L,start,normalize_terminal,signedValue]
  | cons r t =>
    have hr := ht r (by simp)
    simp [L,start,normalize_split q hq h t r hr,
      signedValue_reverse (V := Int) (by decide) Int.neg_neg] <;> omega

private theorem length_le_weight (s : Tuple) (hs : Valid s) : s.length ≤ weight s := by
  induction s with
  | nil => exact Nat.le_refl _
  | cons a s ih =>
    have ha := hs a (by simp)
    have h := ih (fun i hi => hs i (by simp [hi]))
    simp only [weight, List.length_cons]
    omega

/-- A proof principle for all positive tuples. It suffices to handle the
TT forms and the terminal vanishing row, and to pass backwards through
one split. The measure is weight minus depth. -/
theorem split_induction (q : Nat) (hq : 0 < q) (P : Tuple → Prop)
    (base : ∀ s, TT q s → P s)
    (terminal : ∀ h, P (h ++ [q]))
    (step : ∀ h r t, 0 < r → P (h ++ q :: r :: t) → P (h ++ (q+r) :: t))
    (s : Tuple) (hs : Valid s) : P s := by
  classical
  by_cases hbd : ∀ a ∈ s, a ≤ q
  · cases hlast : s.getLast? with
    | none => exact base s (Or.inl (List.getLast?_eq_none_iff.mp hlast))
    | some z =>
      obtain ⟨h,rfl⟩ := List.getLast?_eq_some_iff.mp hlast
      by_cases hz : z = q
      · subst z; exact terminal h
      · have hl := hbd z (by simp)
        exact base _ (Or.inr ⟨h,z,rfl,fun i hi => hs i (by simp [hi]),
          fun i hi => hbd i (by simp [hi]),hs z (by simp),by omega⟩)
  · have hex : ∃ a ∈ s, q < a := by
      apply Classical.byContradiction
      intro nh
      apply hbd
      intro a ha
      exact Nat.le_of_not_gt (fun h => nh ⟨a,ha,h⟩)
    obtain ⟨a,ha,hl⟩ := hex
    obtain ⟨h,t,heq,_⟩ := List.eq_append_cons_of_mem ha
    subst s
    have hr : 0 < a-q := by omega
    have hsplit : Valid (h ++ q :: (a-q) :: t) := by
      intro i hi
      simp only [List.mem_append, List.mem_cons] at hi
      rcases hi with hi | rfl | rfl | hi
      · exact hs i (by simp [hi])
      · exact hq
      · exact hr
      · exact hs i (by simp [hi])
    have ih := split_induction q hq P base terminal step _ hsplit
    simpa [show q + (a-q) = a by omega] using step h (a-q) t hr ih
termination_by weight s - s.length
decreasing_by
  have hb := length_le_weight _ hsplit
  rw [heq]
  simp only [weight_append, weight, List.length_append, List.length_cons] at hb ⊢
  omega

/-- Two evaluations satisfying all L rows coincide on valid tuples as soon
as they agree on TT. This is the uniqueness part of straightening. -/
theorem determined_by_TT [Neg V] [Zero V] (q : Nat) (hq : 0 < q) (f g : Tuple → V)
    (agree : ∀ s, TT q s → f s = g s)
    (f₀ : ∀ h, f (h ++ [q]) = 0) (g₀ : ∀ h, g (h ++ [q]) = 0)
    (fs : ∀ h r t, 0 < r → f (h ++ (q+r)::t) = -(f (h ++ q::r::t)))
    (gs : ∀ h r t, 0 < r → g (h ++ (q+r)::t) = -(g (h ++ q::r::t)))
    (s : Tuple) (hs : Valid s) : f s = g s := by
  apply split_induction q hq (fun u => f u = g u) agree _ _ s hs
  · intro h
    rw [f₀, g₀]
  · intro h r t hr same
    rw [fs h r t hr, gs h r t hr, same]

/-- The universal formula: an evaluation satisfying the L rows is the
signed extension of its values on TT tuples. -/
theorem evaluate_normalize [Neg V] [Zero V] (q : Nat) (hq : 0 < q) (f : Tuple → V)
    (negZero : -(0:V) = 0) (negNeg : ∀ y : V, -(-y) = y)
    (terminal : ∀ h, f (h ++ [q]) = 0)
    (splitRow : ∀ h r t, 0 < r → f (h ++ (q+r)::t) = -(f (h ++ q::r::t)))
    (s : Tuple) (hs : Valid s) : f s = signedValue f (normalize q hq s) := by
  apply determined_by_TT q hq f (fun u => signedValue f (normalize q hq u)) _
    terminal _ splitRow _ s hs
  · intro t ht; simp [normalize_TT q hq t ht,signedValue]
  · intro h; simp [normalize_terminal,signedValue]
  · intro h r t hr
    exact congrArg (signedValue f) (normalize_split q hq h t r hr) |>.trans
      (signedValue_reverse negZero negNeg f _)

/-- Leading tuple of the row indexed by a marked pair. -/
def source (q : Nat) (h : Tuple) : Tuple → Tuple
  | [] => h ++ [q]
  | r::t => h ++ (q+r)::t

theorem source_ne_nil (q : Nat) (h t : Tuple) : source q h t ≠ [] := by
  cases t <;> simp [source]

theorem source_cons (q a : Nat) (h t : Tuple) :
    source q (a::h) t = a :: source q h t := by
  cases t <;> rfl

theorem source_weight (q : Nat) (h t : Tuple) :
    weight (source q h t) = weight h + q + weight t := by
  cases t <;> simp [source, weight, Nat.add_assoc]

theorem source_L (q : Nat) (h t : Tuple) : source q h t ∈ L q h t := by
  cases t <;> simp [source,L,start]

private def prependMark (a : Nat) (p : Tuple × Tuple) : Tuple × Tuple := (a::p.1,p.2)

/-- Inspect the first entry greater than q, or a final q after bounded entries. -/
def mark (q : Nat) : Tuple → Option (Tuple × Tuple)
  | [] => none
  | a::s => if q < a then some ([],(a-q)::s)
            else if a = q ∧ s = [] then some ([],[])
            else (mark q s).map (prependMark a)

private theorem mark_cons_bounded (q a : Nat) (s : Tuple) (ha : a ≤ q) (hs : s ≠ []) :
    mark q (a::s) = (mark q s).map (prependMark a) := by
  simp [mark, Nat.not_lt.mpr ha, hs]

theorem mark_source (q : Nat) (h t : Tuple) (hb : ∀ a ∈ h, a ≤ q) (ht : Valid t) :
    mark q (source q h t) = some (h,t) := by
  induction h with
  | nil =>
    cases t with
    | nil => simp [source,mark]
    | cons r t =>
      have hr := ht r (by simp)
      simp [source,mark, show q < q+r by omega, Nat.add_sub_cancel_left]
  | cons a h ih =>
    rw [source_cons, mark_cons_bounded q a _ (hb a (by simp)) (source_ne_nil q h t)]
    simp [ih (fun b hbh => hb b (by simp [hbh])), prependMark]

theorem source_mark (q : Nat) (s h t : Tuple) (hs : Valid s) (hm : mark q s = some (h,t)) :
    source q h t = s ∧ Valid h ∧ (∀ a ∈ h, a ≤ q) ∧ Valid t := by
  induction s generalizing h t with
  | nil => simp [mark] at hm
  | cons a s ih =>
    have ha := hs a (by simp)
    have htail : Valid s := fun b hb => hs b (by simp [hb])
    by_cases hbig : q < a
    · simp [mark,hbig] at hm
      obtain ⟨rfl,rfl⟩ := hm
      refine ⟨?_,by simp [Valid], by simp,?_⟩
      · simp [source, show q+(a-q)=a by omega]
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · omega
        · exact htail b hb
    · by_cases hend : a=q ∧ s=[]
      · obtain ⟨rfl,rfl⟩ := hend
        simp [mark] at hm
        obtain ⟨rfl,rfl⟩ := hm
        simp [source,Valid]
      · simp only [mark,if_neg hbig,if_neg hend] at hm
        cases he : mark q s with
        | none => simp [he] at hm
        | some p =>
          obtain ⟨h',t'⟩ := p
          simp [he,prependMark] at hm
          obtain ⟨rfl,rfl⟩ := hm
          obtain ⟨H,hv,hb,tv⟩ := ih h' t' htail he
          refine ⟨by simp [source_cons,H], ?_, ?_, tv⟩
          · intro n hn
            exact (List.mem_cons.mp hn).elim (fun hn => hn ▸ ha) (hv _)
          · intro n hn
            rcases List.mem_cons.mp hn with rfl | hn
            · omega
            · exact hb _ hn

theorem mark_none_iff_TT (q : Nat) (s : Tuple) (hs : Valid s) : mark q s = none ↔ TT q s := by
  constructor
  · intro hm
    induction s with
    | nil => exact Or.inl rfl
    | cons a s ih =>
      have ha := hs a (by simp)
      have htail : Valid s := fun b hb => hs b (by simp [hb])
      by_cases hbig : q < a
      · simp [mark,hbig] at hm
      · cases s with
        | nil =>
          have hne : a ≠ q := by
            intro h
            simp [mark,h] at hm
          exact Or.inr ⟨[],a,rfl,by simp [Valid],by simp,ha,by omega⟩
        | cons b s =>
          have hsmall := Nat.le_of_not_gt hbig
          rw [mark_cons_bounded q a _ hsmall (by simp)] at hm
          have hn : mark q (b::s) = none := by simpa using hm
          rcases ih htail hn with hh | ⟨t,z,he,hv,hb,hz₀,hz⟩
          · contradiction
          · refine Or.inr ⟨a::t,z,by simp [he],?_,?_,hz₀,hz⟩
            · intro n h
              exact (List.mem_cons.mp h).elim (fun h => h ▸ ha) (hv _)
            · intro n h
              exact (List.mem_cons.mp h).elim (fun h => h ▸ hsmall) (hb _)
  · rintro (rfl | ⟨h,z,rfl,hv,hb,_,hz⟩)
    · rfl
    · clear hs hv
      induction h with
      | nil => simp [mark, Nat.ne_of_lt hz, show ¬q < z by omega]
      | cons a h ih =>
        simp only [List.cons_append]
        rw [mark_cons_bounded q a _ (hb a (by simp)) (by simp)]
        simp [ih (fun n hn => hb n (by simp [hn]))]

/-- The two constructions are inverse on the canonical indices.
In particular a leading source cannot occur twice among bounded-prefix rows. -/
theorem canonical_source_injective (q : Nat) {h t h' t' : Tuple}
    (hb : ∀ a ∈ h, a ≤ q) (hb' : ∀ a ∈ h', a ≤ q) (ht : Valid t) (ht' : Valid t')
    (he : source q h t = source q h' t') : h = h' ∧ t = t' := by
  have hEq := congrArg (mark q) he
  simpa [mark_source q h t hb ht,mark_source q h' t' hb' ht'] using hEq

theorem canonical_source_surjective (q : Nat) (s : Tuple) (hs : Valid s) (hn : ¬TT q s) :
    ∃ h t, source q h t = s ∧ Valid h ∧ (∀ a ∈ h, a ≤ q) ∧ Valid t := by
  cases he : mark q s with
  | none => exact (hn ((mark_none_iff_TT q s hs).mp he)).elim
  | some p =>
    obtain ⟨h,t⟩ := p
    exact ⟨h,t,source_mark q s h t hs he⟩

/-- Each L-row has a unique least-depth tuple; the split term (when present)
is exactly one entry longer. -/
theorem source_least_depth (q : Nat) (h t u : Tuple) (hu : u ∈ L q h t) :
    u = source q h t ∨ depth u = depth (source q h t) + 1 := by
  cases t with
  | nil => left; simpa [L,start,source] using hu
  | cons r s =>
    simp [L,start] at hu
    rcases hu with rfl | rfl
    · right; simp [source,depth]; omega
    · left; rfl

private theorem swapEnds (a b c d : Tuple) :
    ([a,b,c,d] : List Tuple).Perm [d,b,c,a] := by
  have h₁ := List.perm_middle (a := d) (l₁ := [a,b,c]) (l₂ := [])
  have h₂ := (List.perm_middle (a := a) (l₁ := [b,c]) (l₂ := [])).symm.cons d
  exact h₁.trans h₂

/-- The local square of Theorem 2.9. Both sides are the same multiset of
four tuples. Subtracting them gives zero over every coefficient field. -/
theorem square_L (q r c : Nat) (h m t : Tuple) :
    (L q h (r :: (m ++ (q+c) :: t)) ++
     L q h (r :: (m ++ q :: c :: t))).Perm
    (L q (h ++ (q+r) :: m) (c :: t) ++
     L q (h ++ q :: r :: m) (c :: t)) := by
  simp only [L, start, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.append_assoc]
  apply swapEnds

/-- The terminal triangle of Theorem 2.9, where the last entry is q. -/
theorem triangle_L (q r : Nat) (h m : Tuple) :
    (L q h (r :: (m ++ [q]))).Perm
    (L q (h ++ (q+r) :: m) [] ++ L q (h ++ q :: r :: m) []) := by
  simp only [L,start,List.map_cons,List.map_nil,List.cons_append,List.nil_append,
    List.append_assoc]
  apply List.Perm.swap

end Megaera.Splitting
