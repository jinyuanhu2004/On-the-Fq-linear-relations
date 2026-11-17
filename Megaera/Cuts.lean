import Megaera.Tuples

/-! The first cut identity, Lemma 2.10(i), with multiplicities. -/

namespace Megaera.Cuts

def total {α : Type u} (xs : List α) (f : α → Nat) : Nat :=
  match xs with
  | [] => 0
  | x :: l => f x + total l f

theorem total_append {α : Type u} (s t : List α) (f : α → Nat) :
    total (s ++ t) f = total s f + total t f := by
  induction s with
  | nil => simp [total]
  | cons a s ih => simp [total, ih, Nat.add_assoc]

theorem total_map {α : Type u} {β : Type v} (s : List α) (g : α → β) (f : β → Nat) :
    total (s.map g) f = total s (fun a => f (g a)) := by
  induction s with
  | nil => rfl
  | cons a s ih => simp [total, ih]

def cutSum : Tuple → (Tuple → Tuple → Nat) → Nat
  | [], f => f [] []
  | b :: t, f => f [] (b :: t) + cutSum t (fun u v => f (b :: u) v)

theorem cutSum_add (t : Tuple) (f g : Tuple → Tuple → Nat) :
    cutSum t (fun u v => f u v + g u v) = cutSum t f + cutSum t g := by
  induction t generalizing f g with
  | nil => rfl
  | cons b t ih =>
    simp only [cutSum]
    rw [ih (fun u v => f (b::u) v) (fun u v => g (b::u) v)]
    omega

def block (s : Tuple) (c : Nat) (u v : Tuple) (g : Tuple → Nat) : Nat :=
  total (quasiShuffle s u) fun x => total (start c v) fun y => g (x ++ y)

def cutValue (s : Tuple) (c : Nat) (t : Tuple) (g : Tuple → Nat) : Nat :=
  cutSum t fun u v => block s c u v g

private theorem block_cons (a b c : Nat) (s u v : Tuple) (g : Tuple → Nat) :
    block (a::s) c (b::u) v g =
    block s c (b::u) v (fun x => g (a::x)) +
    block (a::s) c u v (fun x => g (b::x)) +
    block s c u v (fun x => g ((a+b)::x)) := by
  simp only [block, quasiShuffle.eq_3, total_append, total_map, List.cons_append]

private theorem cutValue_cons (a b c : Nat) (s t : Tuple) (g : Tuple → Nat) :
    cutValue (a::s) c (b::t) g =
    cutValue s c (b::t) (fun x => g (a::x)) +
    cutValue (a::s) c t (fun x => g (b::x)) +
    cutValue s c t (fun x => g ((a+b)::x)) := by
  simp only [cutValue, cutSum, block_cons, cutSum_add]
  simp only [block, quasiShuffle_nil_right, total, Nat.add_zero, List.cons_append]
  omega

private theorem cutValue_nil (c b : Nat) (t : Tuple) (g : Tuple → Nat) :
    cutValue [] c (b::t) g =
    g (c::b::t) + cutValue [] c t (fun x => g (b::x)) + g ((c+b)::t) := by
  simp only [cutValue, cutSum, block, quasiShuffle_nil_left, total, Nat.add_zero,
    List.nil_append, List.cons_append, start]
  omega

theorem singleton_cut (c : Nat) (t : Tuple) (g : Tuple → Nat) :
    total (quasiShuffle [c] t) g = cutValue [] c t g := by
  induction t generalizing g with
  | nil => simp [cutValue, cutSum, block, total, start]
  | cons b t ih =>
    rw [cutValue_nil, quasiShuffle.eq_3]
    simp only [total_append, total_map, quasiShuffle_nil_left, total, Nat.add_zero]
    rw [ih]

theorem cut_value_eq (s : Tuple) (c : Nat) (t : Tuple) (g : Tuple → Nat) :
    total (quasiShuffle (s ++ [c]) t) g = cutValue s c t g := by
  induction s generalizing t g with
  | nil => exact singleton_cut c t g
  | cons a s ih =>
    induction t generalizing g with
    | nil => simp [cutValue, cutSum, block, total, start]
    | cons b t jt =>
      rw [cutValue_cons, List.cons_append, quasiShuffle.eq_3]
      simp only [total_append, total_map]
      rw [ih, ih, ← List.cons_append, jt]

/-- All cuts in order of their prefix length, including both ends. -/
def cuts : Tuple → List (Tuple × Tuple)
  | [] => [([], [])]
  | b :: t => ([], b::t) :: (cuts t).map (fun p => (b::p.1, p.2))

theorem total_cuts (t : Tuple) (f : Tuple → Tuple → Nat) :
    total (cuts t) (fun p => f p.1 p.2) = cutSum t f := by
  induction t generalizing f with
  | nil => simp [cuts, total, cutSum]
  | cons b t ih =>
    simp only [cuts, total, total_map, cutSum]
    rw [ih (fun u v => f (b::u) v)]

theorem total_flatMap {α : Type u} {β : Type v} (xs : List α)
    (ys : α → List β) (f : β → Nat) :
    total (xs.flatMap ys) f = total xs (fun x => total (ys x) f) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, total_append, total, ih]

theorem count_total (x : Tuple) (xs : List Tuple) :
    @List.count Tuple instBEqOfDecidableEq x xs =
      total xs (fun y => if y = x then 1 else 0) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    by_cases h : a = x
    · subst a
      simp [total, ih, List.count_cons, Nat.add_comm, instBEqOfDecidableEq]
    · simp [total, ih, List.count_cons, h, instBEqOfDecidableEq]

/-- Equation (2.5). Permutation equality retains all multiplicities,
including when several merges yield the same tuple. -/
theorem append_singleton_cut (s : Tuple) (c : Nat) (t : Tuple) :
    (quasiShuffle (s ++ [c]) t).Perm
      ((cuts t).flatMap fun p => concatenate (quasiShuffle s p.1) (start c p.2)) := by
  apply List.perm_iff_count.mpr
  intro x
  rw [count_total, count_total, cut_value_eq]
  simp only [concatenate, total_flatMap, total_map, cutValue, block]
  exact (total_cuts t _).symm

/-- Every enumerated pair really is a cut of the indicated tuple. -/
theorem pieces_append {l : Tuple} {p : Tuple × Tuple} (hp : p ∈ cuts l) :
    p.1 ++ p.2 = l := by
  induction l generalizing p with
  | nil =>
    simp only [cuts, List.mem_singleton] at hp
    subst p
    rfl
  | cons b t ih =>
    simp only [cuts, List.mem_cons, List.mem_map] at hp
    rcases hp with rfl | ⟨r, hr, rfl⟩
    · rfl
    · exact congrArg (List.cons b) (ih hr)

/-- Sum a finite family of contributions in an additive target.
For Corollary 2.12 the target is the space of binary pairs. -/
def sumRows {α : Type u} {V : Type v} [Zero V] [Add V]
    (xs : List α) (f : α → V) : V :=
  match xs with
  | [] => 0
  | a :: t => f a + sumRows t f

private theorem sumRows_mem {α : Type u} {V : Type v} [Zero V] [Add V]
    (inside : V → Prop) (zero : inside 0)
    (plus : ∀ x y, inside x → inside y → inside (x+y))
    (xs : List α) (f : α → V) (h : ∀ a ∈ xs, inside (f a)) :
    inside (sumRows xs f) := by
  induction xs with
  | nil => exact zero
  | cons a xs ih =>
    exact plus _ _ (h _ (by simp)) (ih (fun z hz => h z (List.mem_cons_of_mem _ hz)))

private theorem shuffle_nonempty {s t x : Tuple} (hs : s ≠ [])
    (hx : x ∈ quasiShuffle s t) : x ≠ [] := by
  cases s with
  | nil => contradiction
  | cons a s =>
    cases t with
    | nil => simp_all
    | cons b t =>
      simp only [quasiShuffle.eq_3, List.mem_append, List.mem_map] at hx
      rcases hx with ((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩) <;> simp

/-- Corollary 2.12 from Theorem 2.11. Read identifies a presentation
of a binary pair with its value in the additive space V. The
convolution hypothesis is exactly (2.11) on the full list of cuts.
The conclusion applies in particular when G is the span of the
one-argument C-translates. The proof isolates the empty *prefix*.
Every other cut has a strictly shorter suffix. -/
theorem generalP_generated_of_cutIdentity {K : Type u} [OfNat K 1] [Neg K]
    {V : Type v} [Zero V] [Add V] [Sub V]
    (q : Nat) (read : BinaryPair K → V) (G : V → Prop)
    (add_zero : ∀ z : V, z + 0 = z) (cancel : ∀ a b : V, a + b - b = a)
    (gzero : G 0) (gadd : ∀ a b, G a → G b → G (a+b))
    (gsub : ∀ a b, G a → G b → G (a-b))
    (generators : ∀ s t, Valid s → s ≠ [] → Valid t →
      G (read (cOp t (primitive q s))))
    (convolution : ∀ s t, Valid s → s ≠ [] → Valid t →
      read (cOp t (primitive q s)) = sumRows (cuts t)
        (fun p => sumRows (quasiShuffle s p.1) (fun x => read (generalP q x p.2)))) :
    ∀ s t, Valid s → s ≠ [] → Valid t → G (read (generalP q s t)) := by
  let P (t : Tuple) := ∀ s, Valid s → s ≠ [] → Valid t → G (read (generalP q s t))
  have all : ∀ n t, t.length = n → P t := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro t ht s hs hsne hv
      cases t with
      | nil =>
        exact generators s [] hs hsne hv
      | cons b t =>
        have eqn := convolution s (b::t) hs hsne hv
        simp only [cuts, sumRows, quasiShuffle_nil_right, add_zero] at eqn
        let rem := sumRows ((cuts t).map (fun p => (b::p.1, p.2)))
          (fun p => sumRows (quasiShuffle s p.1) (fun x => read (generalP q x p.2)))
        have grem : G rem := by
          apply sumRows_mem G gzero gadd
          intro p hp
          obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp
          have hcut := pieces_append hr
          have hjoin : (b :: r.1) ++ r.2 = b :: t := congrArg (List.cons b) hcut
          have validPrefix : Valid (b :: r.1) := by
            intro x hx
            exact hv x (hjoin ▸ List.mem_append_left _ hx)
          have validTail : Valid r.2 := by
            intro x hx
            exact hv x (hjoin ▸ List.mem_append_right _ hx)
          have hlen := congrArg List.length hcut
          simp only [List.length_append] at hlen
          have hlt : r.2.length < n := by simp only [List.length_cons] at ht; omega
          apply sumRows_mem G gzero gadd
          intro x hx
          exact ih r.2.length hlt r.2 rfl x
            (valid_quasiShuffle _ _ _ hs validPrefix hx) (shuffle_nonempty hsne hx) validTail
        have g := gsub _ rem (generators s (b::t) hs hsne hv) grem
        change read (cOp (b::t) (primitive q s)) = read (generalP q s (b::t)) + rem at eqn
        rwa [eqn, cancel] at g
  intro s t
  exact all t.length t rfl s

end Megaera.Cuts
