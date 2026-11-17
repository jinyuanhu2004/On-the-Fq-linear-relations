import Std

/-!
# Formal tuples and the operators in Megaera

Tuple entries are stored at their actual natural-number value. The predicate
`Valid` restricts the representation to positive entries. All paper
applications use `2 ≤ q`; the primitive family starts with a nonempty tuple.
Products return lists of terms, retaining every multiplicity. Formal sums
are presentations: addition concatenates lists, and an evaluator must add
coefficients of equal terms in its coefficient field.
-/

namespace Megaera

abbrev Tuple := List Nat

def Valid (s : Tuple) : Prop := ∀ n ∈ s, 0 < n

def weight : Tuple → Nat
  | [] => 0
  | n :: s => n + weight s

def depth (s : Tuple) : Nat := s.length

def TT (q : Nat) (s : Tuple) : Prop :=
  s = [] ∨ ∃ h z, s = h ++ [z] ∧ Valid h ∧ (∀ n ∈ h, n ≤ q) ∧ 0 < z ∧ z < q

@[simp] theorem weight_append (s t : Tuple) : weight (s ++ t) = weight s + weight t := by
  induction s with
  | nil => simp [weight]
  | cons _ _ ih => simp [weight, ih, Nat.add_assoc]

/-- Equation (1.5). A repeated tuple in the output is counted repeatedly. -/
def quasiShuffle : Tuple → Tuple → List Tuple
  | [], t => [t]
  | a :: s, [] => [a :: s]
  | a :: s, b :: t =>
      ((quasiShuffle s (b :: t)).map (List.cons a) ++
      (quasiShuffle (a :: s) t).map (List.cons b)) ++
      (quasiShuffle s t).map (List.cons (a + b))
termination_by s t => s.length + t.length
decreasing_by all_goals simp_wf <;> omega

@[simp] theorem quasiShuffle_nil_left (t : Tuple) : quasiShuffle [] t = [t] := by
  simp [quasiShuffle]

@[simp] theorem quasiShuffle_nil_right (s : Tuple) : quasiShuffle s [] = [s] := by
  cases s <;> simp [quasiShuffle]

/-- Every contribution in the stuffle expansion has the sum of the two weights. -/
theorem weight_quasiShuffle (s t u : Tuple) (h : u ∈ quasiShuffle s t) :
    weight u = weight s + weight t := by
  match s, t with
  | [], t =>
    simp only [quasiShuffle_nil_left, List.mem_singleton] at h
    subst u
    simp [weight]
  | a :: s, [] =>
    simp only [quasiShuffle_nil_right, List.mem_singleton] at h
    subst u
    simp [weight]
  | a :: s, b :: t =>
    simp only [quasiShuffle, List.mem_append, List.mem_map] at h
    rcases h with ((⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩) | ⟨v, hv, rfl⟩)
    · have H := weight_quasiShuffle s (b :: t) v hv
      simp only [weight] at H ⊢
      omega
    · have H := weight_quasiShuffle (a :: s) t v hv
      simp only [weight] at H ⊢
      omega
    · have H := weight_quasiShuffle s t v hv
      simp only [weight] at H ⊢
      omega
termination_by s.length + t.length
decreasing_by all_goals simp_wf <;> omega

/-- Equation (1.6) for a nonempty first input. An empty first input has no
head to prepend and contributes zero. -/
def triangle : Tuple → Tuple → List Tuple
  | [], _ => []
  | a :: s, t => (quasiShuffle s t).map (List.cons a)

/-- Equation (1.7), with the empty-tuple convention in Section 1. -/
def diamond : Tuple → Tuple → List Tuple
  | [], t => [t]
  | a :: s, [] => [a :: s]
  | a :: s, b :: t => (quasiShuffle s t).map (List.cons (a + b))

/-- `(q)(◁+⋄)t` with the separate empty-tail convention in the cut lemma. -/
def start (q : Nat) : Tuple → List Tuple
  | [] => [[q]]
  | a :: s => [q :: a :: s, (q + a) :: s]

def incLast : Tuple → Tuple
  | [] => []
  | [a] => [a + 1]
  | a :: b :: s => a :: incLast (b :: s)

/-- `s^{+1} + (s,1)`; the manuscript omits the first term for empty input. -/
def endings : Tuple → List Tuple
  | [] => [[1]]
  | a :: s => [incLast (a :: s), (a :: s) ++ [1]]

/-- Cartesian concatenation is the bilinear extension of tuple concatenation. -/
def concatenate (ss ts : List Tuple) : List Tuple :=
  ss.flatMap fun s => ts.map fun t => s ++ t

abbrev FormalSum (K : Type u) := List (K × Tuple)
abbrev BinaryPair (K : Type u) := FormalSum K × FormalSum K

def liftPair (r : BinaryPair K) : FormalSum K := r.1 ++ r.2

/-- Extend a list of output terms linearly, without changing coefficients. -/
def expand (f : Tuple → List Tuple) (p : FormalSum K) : FormalSum K :=
  p.flatMap fun term => (f term.2).map fun t => (term.1, t)

def withCoeff (c : K) (s : List Tuple) : FormalSum K :=
  s.map fun t => (c, t)

/-- Equation (1.11). At an empty subscript the operator is the identity. -/
def bOp (w : Tuple) (r : BinaryPair K) : BinaryPair K :=
  match w with
  | [] => r
  | a :: s =>
    (expand (triangle (a :: s)) r.1 ++
      expand (diamond (a :: s)) r.2 ++
      expand (triangle (a :: s)) r.2, [])

/-- Equations (1.3), (1.12), in the composition order in Definition 1.4. -/
def bStar : Tuple → BinaryPair K → BinaryPair K
  | [], r => r
  | a :: s, r => bOp [a] (bStar s r)

/-- Equation (1.13). -/
def cOp (w : Tuple) (r : BinaryPair K) : BinaryPair K :=
  match w with
  | [] => r
  | a :: s => (expand (fun t => diamond t (a :: s)) r.1 ++
               expand (fun t => triangle t (a :: s)) r.1,
               expand (fun t => triangle t (a :: s)) r.2)

theorem bStar_append (u v : Tuple) (r : BinaryPair K) :
    bStar (u ++ v) r = bStar u (bStar v r) := by
  induction u with
  | nil => rfl
  | cons _ _ ih => simp only [List.cons_append, bStar, ih]

theorem bStar_fixed (a : Nat) (s : Tuple) (r : BinaryPair K) :
    (bStar (a :: s) r).2 = [] := by rfl

/-- The initial binary pair (1.1), for a supplied coefficient D₁. -/
def fundamental [OfNat K 1] (q : Nat) (D₁ : K) : BinaryPair K :=
  ([(1, [q])], [(D₁, [1, q - 1])])

/-- The two tuple maps in (2.3). A pair (h,t) specifies the position of
the canonical split, with an empty t encoding a final q. -/
def L (q : Nat) (h t : Tuple) : List Tuple :=
  (start q t).map fun v => h ++ v

def H (q : Nat) (h t : Tuple) : List Tuple :=
  concatenate (endings h) (quasiShuffle [q - 1] t)

/-- The tuple terms of a presentation each have the displayed weight. -/
def TermsOfWeight (w : Nat) (ts : List Tuple) : Prop :=
  ∀ s ∈ ts, weight s = w

theorem start_weight (q : Nat) (t : Tuple) : TermsOfWeight (q + weight t) (start q t) := by
  intro s hs
  cases t with
  | nil =>
    simp only [start, List.mem_singleton] at hs
    subst s
    simp [weight]
  | cons a t =>
    simp [start] at hs
    rcases hs with rfl | rfl <;> simp [weight, Nat.add_assoc]

theorem incLast_weight (a : Nat) (s : Tuple) :
    weight (incLast (a :: s)) = weight (a :: s) + 1 := by
  induction s generalizing a with
  | nil => simp [incLast, weight]
  | cons b s ih =>
    simp only [incLast, weight, ih]
    omega

theorem endings_weight (s : Tuple) : TermsOfWeight (weight s + 1) (endings s) := by
  intro t ht
  cases s with
  | nil =>
    simp only [endings, List.mem_singleton] at ht
    subst t
    rfl
  | cons a s =>
    simp [endings] at ht
    rcases ht with rfl | rfl
    · exact incLast_weight a s
    · simp [weight, Nat.add_assoc]

theorem L_weight (q : Nat) (h t : Tuple) :
    TermsOfWeight (weight h + q + weight t) (L q h t) := by
  intro s hs
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hs
  rw [weight_append, start_weight q t v hv, Nat.add_assoc]

theorem H_weight (q : Nat) (hq : 0 < q) (h t : Tuple) :
    TermsOfWeight (weight h + q + weight t) (H q h t) := by
  intro s hs
  obtain ⟨v, hv, hs⟩ := List.mem_flatMap.mp hs
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hs
  have h₁ := endings_weight h v hv
  have h₂ := weight_quasiShuffle [q-1] t u hu
  simp only [weight, Nat.add_zero] at h₂
  rw [weight_append]
  omega

/-- General primitive pair of Section 2.4. The first tuple must be nonempty
in applications to BCP completeness. -/
def generalP [OfNat K 1] [Neg K] (q : Nat) (s t : Tuple) : BinaryPair K :=
  (withCoeff 1 ((H q s t).flatMap (start q)),
   withCoeff (-(1 : K)) ((L q s t).flatMap fun v =>
      (quasiShuffle [q - 1] v).map (List.cons 1)))

/-- The one-argument primitive pair (1.20). -/
def primitive [OfNat K 1] [Neg K] (q : Nat) (s : Tuple) : BinaryPair K :=
  generalP q s []

def bcpGenerator [OfNat K 1] [Neg K] (q : Nat) (u v s : Tuple) : FormalSum K :=
  liftPair (bStar u (cOp v (primitive q s)))

/-- The positive-weight grading is imposed on every term before combining
like tuples. This also works when a presentation has cancelling terms. -/
def PresentedAt (w : Nat) (p : FormalSum K) : Prop :=
  ∀ z ∈ p, weight z.2 = w

theorem generalP_weight [OfNat K 1] [Neg K] (q : Nat) (hq : 0 < q) (s t : Tuple) :
    PresentedAt (weight s + weight t + 2*q) ((generalP q s t : BinaryPair K).1) ∧
    PresentedAt (weight s + weight t + 2*q) ((generalP q s t : BinaryPair K).2) := by
  constructor
  · intro z hz
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hz
    obtain ⟨u, hu, hv⟩ := List.mem_flatMap.mp hv
    have h₁ := H_weight q hq s t u hu
    have h₂ := start_weight q u v hv
    change weight v = _
    omega
  · intro z hz
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hz
    obtain ⟨u, hu, hv⟩ := List.mem_flatMap.mp hv
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
    have h₁ := L_weight q s t u hu
    have h₂ := weight_quasiShuffle [q-1] u a ha
    simp only [weight, Nat.add_zero] at h₂
    change 1 + weight a = _
    omega

theorem primitive_weight [OfNat K 1] [Neg K] (q : Nat) (hq : 0 < q) (s : Tuple) :
    PresentedAt (weight s + 2*q) ((primitive q s : BinaryPair K).1) ∧
    PresentedAt (weight s + 2*q) ((primitive q s : BinaryPair K).2) := by
  simpa [primitive, weight] using generalP_weight (K := K) q hq s []

/-- Prepend 1 or increase the first entry. These are the two operations
on each *input* of a shaped binary pair in Lemma 2.1. -/
def incFirst : Tuple → Tuple
  | [] => []
  | a :: s => (a+1) :: s

def primitiveData (q : Nat) (s : Tuple) : List Tuple × List Tuple :=
  ((endings s).map (fun v => v ++ [q-1]), [s ++ [q]])

def mapData (f : Tuple → Tuple) (p : List Tuple × List Tuple) : List Tuple × List Tuple :=
  (p.1.map f, p.2.map f)

def shapedPair [OfNat K 1] [Neg K] (q : Nat) (p : List Tuple × List Tuple) : BinaryPair K :=
  (withCoeff 1 (p.1.flatMap (start q)),
   withCoeff (-(1 : K)) (p.2.flatMap fun v =>
     (quasiShuffle [q-1] v).map (List.cons 1)))

theorem primitive_eq_shaped [OfNat K 1] [Neg K] (q : Nat) (s : Tuple) :
    (primitive q s : BinaryPair K) = shapedPair q (primitiveData q s) := by
  cases s <;> simp [primitive, generalP, primitiveData, H, L, start, endings,
    concatenate, shapedPair]

theorem primitiveData_prepend (q a : Nat) (s : Tuple) :
    primitiveData q (1 :: a :: s) = mapData (List.cons 1) (primitiveData q (a :: s)) := by
  rfl

theorem primitiveData_increase (q a : Nat) (s : Tuple) :
    primitiveData q ((a+1) :: s) = mapData incFirst (primitiveData q (a :: s)) := by
  cases s <;> rfl

/-- Induction scheme in the proof of Theorem 2.2. Its three premises
correspond respectively to the tuple (1), prepending 1, and increasing
the first entry. -/
theorem positiveTuple_induction (P : Tuple → Prop)
    (base : P [1])
    (prependOne : ∀ a s, Valid (a :: s) → P (a :: s) → P (1 :: a :: s))
    (increase : ∀ a s, Valid (a :: s) → P (a :: s) → P ((a+1) :: s))
    (s : Tuple) (hs : Valid s) (hne : s ≠ []) : P s := by
  have raiseHead (t : Tuple) (ht : Valid t) (first : P (1 :: t)) (n : Nat) :
      P ((n + 1) :: t) := by
    induction n with
    | zero => exact first
    | succ n ih =>
      apply increase (n+1) t _ ih
      intro k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · omega
      · exact ht k hk
  induction s with
  | nil => exact (hne rfl).elim
  | cons a s ih =>
    have ha : 0 < a := hs a (by simp)
    have ht : Valid s := fun k hk => hs k (List.mem_cons_of_mem _ hk)
    cases a with
    | zero => omega
    | succ n =>
      apply raiseHead s ht _ n
      cases s with
      | nil => exact base
      | cons b t =>
        exact prependOne b t ht (ih ht (by simp))

/-- Theorem 2.2 as a deduction from the seed (IKN, Prop. 6.1) and the
two stability implications of Lemma 2.1 on primitive inputs. -/
theorem primitive_binary_of_stability [OfNat K 1] [Neg K] (q : Nat)
    (isBinary : BinaryPair K → Prop)
    (seed : isBinary (primitive q [1]))
    (stability₀ : ∀ a s, Valid (a :: s) → isBinary (shapedPair q (primitiveData q (a :: s))) →
      isBinary (shapedPair q (mapData (List.cons 1) (primitiveData q (a :: s)))))
    (stability₁ : ∀ a s, Valid (a :: s) → isBinary (shapedPair q (primitiveData q (a :: s))) →
      isBinary (shapedPair q (mapData incFirst (primitiveData q (a :: s)))))
    (s : Tuple) (hs : Valid s) (hne : s ≠ []) : isBinary (primitive q s) := by
  apply positiveTuple_induction (fun t => isBinary (primitive q t)) seed _ _ s hs hne
  · intro a t h ih
    rw [primitive_eq_shaped, primitiveData_prepend]
    exact stability₀ a t h (by simpa only [primitive_eq_shaped] using ih)
  · intro a t h ih
    rw [primitive_eq_shaped, primitiveData_increase]
    exact stability₁ a t h (by simpa only [primitive_eq_shaped] using ih)

private theorem valid_cons (a : Nat) (t : Tuple) (ha : 0 < a) (ht : Valid t) :
    Valid (a::t) := by
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact ha
  · exact ht b hb

theorem valid_quasiShuffle (s t u : Tuple) (hs : Valid s) (ht : Valid t)
    (h : u ∈ quasiShuffle s t) : Valid u := by
  match s, t with
  | [], t => simp_all
  | a::s, [] => simp_all
  | a::s, b::t =>
    have ha₀ := hs a (by simp)
    have hb₀ := ht b (by simp)
    have hs' : Valid s := fun i hi => hs i (List.mem_cons_of_mem _ hi)
    have ht' : Valid t := fun i hi => ht i (List.mem_cons_of_mem _ hi)
    simp only [quasiShuffle, List.mem_append, List.mem_map] at h
    rcases h with ((⟨v,hv,rfl⟩ | ⟨v,hv,rfl⟩) | ⟨v,hv,rfl⟩)
    · exact valid_cons _ _ ha₀ (valid_quasiShuffle s (b::t) v hs' ht hv)
    · exact valid_cons _ _ hb₀ (valid_quasiShuffle (a::s) t v hs ht' hv)
    · exact valid_cons _ _ (by omega) (valid_quasiShuffle s t v hs' ht' hv)
termination_by s.length + t.length
decreasing_by all_goals simp_wf <;> omega

theorem triangle_weight (s t : Tuple) : TermsOfWeight (weight s + weight t) (triangle s t) := by
  intro u hu
  cases s with
  | nil => simp [triangle] at hu
  | cons a s =>
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
    have hh := weight_quasiShuffle s t v hv
    simp only [weight]
    omega

theorem diamond_weight (s t : Tuple) : TermsOfWeight (weight s + weight t) (diamond s t) := by
  intro u hu
  cases s with
  | nil => simp_all [diamond, weight]
  | cons a s =>
    cases t with
    | nil => simp_all [diamond, weight]
    | cons b t =>
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
      have hh := weight_quasiShuffle s t v hv
      simp only [weight]
      omega

private theorem expand_at (f : Tuple → List Tuple) (p : FormalSum K)
    (n m : Nat) (hp : PresentedAt n p)
    (hf : ∀ s, weight s = n → TermsOfWeight m (f s)) : PresentedAt m (expand f p) := by
  intro z hz
  obtain ⟨term, ht, hz⟩ := List.mem_flatMap.mp hz
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hz
  exact hf _ (hp _ ht) v hv

private theorem append_at {p r : FormalSum K} {n : Nat}
    (hp : PresentedAt n p) (hr : PresentedAt n r) : PresentedAt n (p ++ r) := by
  intro z hz
  exact (List.mem_append.mp hz).elim (hp z) (hr z)

def PairAt (n : Nat) (p : BinaryPair K) : Prop :=
  PresentedAt n p.1 ∧ PresentedAt n p.2

theorem bOp_weight (w : Tuple) (r : BinaryPair K) (n : Nat) (hr : PairAt n r) :
    PairAt (weight w + n) (bOp w r) := by
  cases w with
  | nil => simpa [weight, bOp] using hr
  | cons a w =>
    have ht : ∀ s : Tuple, weight s = n →
        TermsOfWeight (weight (a::w) + n) (triangle (a::w) s) := by
      intro s hn
      simpa only [hn] using triangle_weight (a::w) s
    have hd : ∀ s : Tuple, weight s = n →
        TermsOfWeight (weight (a::w) + n) (diamond (a::w) s) := by
      intro s hn
      simpa only [hn] using diamond_weight (a::w) s
    constructor
    · exact append_at (append_at (expand_at _ _ _ _ hr.1 ht)
        (expand_at _ _ _ _ hr.2 hd)) (expand_at _ _ _ _ hr.2 ht)
    · intro z hz
      exact (List.not_mem_nil hz).elim

theorem bStar_weight (w : Tuple) (r : BinaryPair K) (n : Nat) (hr : PairAt n r) :
    PairAt (weight w + n) (bStar w r) := by
  induction w with
  | nil => simpa [weight, bStar] using hr
  | cons a w ih =>
    simpa [weight, bStar, Nat.add_assoc] using bOp_weight [a] (bStar w r) (weight w + n) ih

theorem cOp_weight (w : Tuple) (r : BinaryPair K) (n : Nat) (hr : PairAt n r) :
    PairAt (weight w + n) (cOp w r) := by
  cases w with
  | nil => simpa [weight, cOp] using hr
  | cons a w =>
    have ht : ∀ s : Tuple, weight s = n →
        TermsOfWeight (weight (a::w) + n) (triangle s (a::w)) := by
      intro s hn
      simpa only [hn, Nat.add_comm n] using triangle_weight s (a::w)
    have hd : ∀ s : Tuple, weight s = n →
        TermsOfWeight (weight (a::w) + n) (diamond s (a::w)) := by
      intro s hn
      simpa only [hn, Nat.add_comm n] using diamond_weight s (a::w)
    exact ⟨append_at (expand_at _ _ _ _ hr.1 hd) (expand_at _ _ _ _ hr.1 ht),
           expand_at _ _ _ _ hr.2 ht⟩

theorem bcpGenerator_weight [OfNat K 1] [Neg K] (q : Nat) (hq : 0 < q) (u v s : Tuple) :
    PresentedAt (weight u + weight v + weight s + 2*q) (bcpGenerator (K := K) q u v s) := by
  have hp := primitive_weight (K := K) q hq s
  have hc := cOp_weight v (primitive q s) _ hp
  have hb := bStar_weight u _ _ hc
  simpa only [Nat.add_assoc] using append_at hb.1 hb.2

def TermsValid (ts : List Tuple) : Prop := ∀ t ∈ ts, Valid t

def PresentedValid (p : FormalSum K) : Prop := ∀ z ∈ p, Valid z.2

private theorem valid_append {s t : Tuple} (hs : Valid s) (ht : Valid t) : Valid (s ++ t) :=
  fun a ha => (List.mem_append.mp ha).elim (hs a) (ht a)

private theorem valid_tail {a : Nat} {s : Tuple} (h : Valid (a::s)) : Valid s :=
  fun i hi => h i (List.mem_cons_of_mem _ hi)

private theorem valid_single (a : Nat) (ha : 0 < a) : Valid [a] := by
  intro i hi; simp only [List.mem_singleton] at hi; exact hi ▸ ha

private theorem start_valid (q : Nat) (hq : 0 < q) (t : Tuple) (ht : Valid t) :
    TermsValid (start q t) := by
  intro s hs
  cases t with
  | nil => simp [start] at hs; subst s; exact valid_single _ hq
  | cons a t =>
    simp [start] at hs
    rcases hs with rfl | rfl
    · exact valid_cons q _ hq ht
    · exact valid_cons _ _ (by omega) (valid_tail ht)

private theorem incLast_valid (a : Nat) (s : Tuple) (hs : Valid (a :: s)) :
    Valid (incLast (a :: s)) := by
  induction s generalizing a with
  | nil => exact valid_single _ (by omega)
  | cons b s ih => exact valid_cons a _ (hs a (by simp)) (ih b (valid_tail hs))

theorem endings_valid (s : Tuple) (hs : Valid s) : TermsValid (endings s) := by
  intro t ht
  cases s with
  | nil => simp [endings] at ht; subst t; exact valid_single 1 (by decide)
  | cons a s =>
    simp [endings] at ht
    rcases ht with rfl | rfl
    · exact incLast_valid _ _ hs
    · exact valid_append hs (valid_single 1 (by decide))

theorem L_valid (q : Nat) (hq : 0 < q) (h t : Tuple) (hh : Valid h) (ht : Valid t) :
    TermsValid (L q h t) := by
  intro s hs
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hs
  exact valid_append hh (start_valid _ hq t ht v hv)

theorem H_valid (q : Nat) (hq : 2 ≤ q) (h t : Tuple) (hh : Valid h) (ht : Valid t) :
    TermsValid (H q h t) := by
  intro s hs
  obtain ⟨u,hu,hs⟩ := List.mem_flatMap.mp hs
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hs
  exact valid_append (endings_valid h hh u hu)
    (valid_quasiShuffle _ _ _ (valid_single (q-1) (by omega)) ht hv)

theorem generalP_valid [OfNat K 1] [Neg K] (q : Nat) (hq : 2 ≤ q) (s t : Tuple)
    (hs : Valid s) (ht : Valid t) :
    PresentedValid ((generalP q s t : BinaryPair K).1) ∧
    PresentedValid ((generalP q s t : BinaryPair K).2) := by
  constructor
  · intro z hz
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hz
    obtain ⟨u,hu,hv⟩ := List.mem_flatMap.mp hv
    exact start_valid q (by omega) _ (H_valid q hq s t hs ht _ hu) _ hv
  · intro z hz
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hz
    obtain ⟨u,hu,hv⟩ := List.mem_flatMap.mp hv
    obtain ⟨v',hv',rfl⟩ := List.mem_map.mp hv
    exact valid_cons _ _ (by decide) (valid_quasiShuffle _ _ _
      (valid_single (q-1) (by omega)) (L_valid q (by omega) s t hs ht _ hu) hv')

private theorem triangle_valid (s t : Tuple) (hs : Valid s) (ht : Valid t) :
    TermsValid (triangle s t) := by
  intro u hu
  cases s with
  | nil => simp [triangle] at hu
  | cons a s =>
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hu
    exact valid_cons _ _ (hs a (by simp)) (valid_quasiShuffle _ _ _ (valid_tail hs) ht hv)

private theorem diamond_valid (s t : Tuple) (hs : Valid s) (ht : Valid t) :
    TermsValid (diamond s t) := by
  intro u hu
  cases s with
  | nil => simp [diamond] at hu; subst u; exact ht
  | cons a s =>
    cases t with
    | nil => simp [diamond] at hu; subst u; exact hs
    | cons b t =>
      have hpos := hs a (by simp)
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hu
      exact valid_cons _ _ (by omega)
        (valid_quasiShuffle _ _ _ (valid_tail hs) (valid_tail ht) hv)

private theorem expand_valid (f : Tuple → List Tuple) (p : FormalSum K) (hp : PresentedValid p)
    (hf : ∀ s, Valid s → TermsValid (f s)) : PresentedValid (expand f p) := by
  intro z hz
  obtain ⟨term,ht,hz⟩ := List.mem_flatMap.mp hz
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hz
  exact hf _ (hp _ ht) v hv

private theorem append_valid {p r : FormalSum K}
    (hp : PresentedValid p) (hr : PresentedValid r) : PresentedValid (p ++ r) :=
  fun z hz => (List.mem_append.mp hz).elim (hp z) (hr z)

def PairValid (r : BinaryPair K) : Prop := PresentedValid r.1 ∧ PresentedValid r.2

theorem bOp_valid (w : Tuple) (r : BinaryPair K) (hw : Valid w) (hr : PairValid r) :
    PairValid (bOp w r) := by
  cases w with
  | nil => exact hr
  | cons a w =>
    have ht := fun s => triangle_valid (a::w) s hw
    have hd := fun s => diamond_valid (a::w) s hw
    refine ⟨append_valid (append_valid (expand_valid _ _ hr.1 ht) (expand_valid _ _ hr.2 hd))
        (expand_valid _ _ hr.2 ht), ?_⟩
    intro z hz; exact (List.not_mem_nil hz).elim

theorem bStar_valid (w : Tuple) (r : BinaryPair K) (hw : Valid w) (hr : PairValid r) :
    PairValid (bStar w r) := by
  induction w with
  | nil => exact hr
  | cons a w ih =>
    exact bOp_valid [a] _ (valid_single a (hw a (by simp))) (ih (valid_tail hw))

theorem cOp_valid (w : Tuple) (r : BinaryPair K) (hw : Valid w) (hr : PairValid r) :
    PairValid (cOp w r) := by
  cases w with
  | nil => exact hr
  | cons a w =>
    have ht := fun s hs => triangle_valid s (a::w) hs hw
    have hd := fun s hs => diamond_valid s (a::w) hs hw
    exact ⟨append_valid (expand_valid _ _ hr.1 hd) (expand_valid _ _ hr.1 ht),
      expand_valid _ _ hr.2 ht⟩

theorem bcpGenerator_valid [OfNat K 1] [Neg K] (q : Nat) (hq : 2 ≤ q) (u v s : Tuple)
    (hu : Valid u) (hv : Valid v) (hs : Valid s) :
    PresentedValid (bcpGenerator (K := K) q u v s) := by
  have hp := generalP_valid (K := K) q hq s [] hs (by simp [Valid])
  have hc := cOp_valid v (primitive q s) hv hp
  have hb := bStar_valid u _ hu hc
  exact append_valid hb.1 hb.2

end Megaera
