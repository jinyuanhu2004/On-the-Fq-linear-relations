import Std

/-!
# The dimension calculation in §3.3

We use integer coefficients. A series is represented by its coefficients indexed
by integers, with zero coefficients in negative weights. Acting on such a
sequence, `oneMinusX`, `oneMinusTwoX` and `den` are multiplication by
`1-X`, `1-2X` and `1-2X+X^(q+1)`. No division of a truncated series is used.
-/
namespace Megaera.Dimension

abbrev Coeff := Int → Int

/-- Coefficients of the constant power series 1. -/
def unitSeries (w : Int) : Int := if w = 0 then 1 else 0

def oneMinusX (a : Coeff) (w : Int) : Int := a w - a (w - 1)

def oneMinusTwoX (a : Coeff) (w : Int) : Int := a w - 2 * a (w - 1)

def den (q : Nat) (a : Coeff) (w : Int) : Int :=
  oneMinusTwoX a w + a (w - (q : Int) - 1)

/-- Sum of the previous n coefficients, starting at weight w-1. -/
def window : Nat → Coeff → Int → Int
  | 0, _, _ => 0
  | n+1, a, w => a (w-1) + window n a (w-1)

theorem window_difference (a : Coeff) (n : Nat) (w : Int) :
    window n a w - window n a (w-1) = a (w-1) - a (w-(n:Int)-1) := by
  induction n generalizing w with
  | zero => simp [window]
  | succ n ih =>
    have h := ih (w-1)
    have hj : w-1-(n:Int)-1 = w-(↑(n+1):Int)-1 := by omega
    rw [hj] at h
    simp only [window]
    omega

/-- The strict prefix sum in the last term of the dimension recurrence. -/
def previous (a : Coeff) (w : Int) : Int := window w.toNat a w

theorem previous_difference (a : Coeff) (ha : ∀ k < 0, a k = 0) (w : Int) :
    previous a w - previous a (w-1) = a (w-1) := by
  unfold previous
  by_cases h : 0 < w
  · have k : w.toNat = (w-1).toNat + 1 := by omega
    rw [k]
    simp [window]
  · have h₁ : w.toNat = 0 := by omega
    have h₂ : (w-1).toNat = 0 := by omega
    have h₃ := ha (w-1) (by omega)
    simp [h₁, h₂, h₃, window]

/-- Multiply the dimension recurrence by 1-X, removing its partial sums.
Here I counts all tuples and B counts TT tuples, including the empty tuple. -/
theorem difference_recurrence (q : Nat) (r I B : Coeff)
    (neg : ∀ k < 0, I k - B k = 0)
    (recurrence : ∀ w, r w =
      window q r w + I (w-(q:Int)) - (I w - B w) +
        previous (fun k => I k - B k) w) (w : Int) :
    den q r w =
      oneMinusX I (w-(q:Int)) - oneMinusTwoX I w + oneMinusTwoX B w := by
  have h := recurrence w
  have h' := recurrence (w-1)
  have hw := window_difference r q w
  have hp := previous_difference (fun k => I k - B k) neg w
  have hj : w-1-(q:Int) = w-(q:Int)-1 := by omega
  rw [hj] at h'
  unfold den oneMinusTwoX oneMinusX
  omega

/-- Theorem 1.12, after clearing the denominator:

  (1-2X)(1-2X+X^(q+1))² R = X^(2q+1)(1-X)².

The hypotheses are precisely the dimension recurrence obtained at the end
of §3.3 and the two tuple-count series used there. The PDF's left-hand side
in (1.21) prints d_w; its recurrence and numerator concern r_w.
-/
theorem relation_dimension_series (q : Nat) (r I B : Coeff)
    (neg : ∀ k < 0, I k - B k = 0)
    (recurrence : ∀ w, r w =
      window q r w + I (w-(q:Int)) - (I w - B w) +
        previous (fun k => I k - B k) w)
    (allTuples : ∀ k, oneMinusTwoX I k = oneMinusX unitSeries k)
    (ttTuples : ∀ k, den q B k =
      oneMinusX unitSeries k - oneMinusX unitSeries (k-(q:Int))) (w : Int) :
    oneMinusTwoX (den q (den q r)) w =
      oneMinusX (oneMinusX unitSeries) (w-(q:Int)-(q:Int)-1) := by
  have diff := difference_recurrence q r I B neg recurrence
  have d₀ := diff w
  have d₁ := diff (w-1)
  have d₂ := diff (w-1-1)
  have d₃ := diff (w-(q:Int)-1)
  have d₄ := diff (w-(q:Int)-1-1)
  have b₀ := ttTuples w
  have b₁ := ttTuples (w-1)
  have b₂ := ttTuples (w-1-1)
  have i₀ := allTuples w
  have i₁ := allTuples (w-1)
  have i₂ := allTuples (w-1-1)
  have i₃ := allTuples (w-(q:Int))
  have i₄ := allTuples (w-(q:Int)-1)
  have i₅ := allTuples (w-(q:Int)-1-1)
  have i₆ := allTuples (w-(q:Int)-(q:Int)-1)
  have i₇ := allTuples (w-(q:Int)-(q:Int)-1-1)
  clear diff recurrence allTuples ttTuples neg
  have shift (k : Int) : k-1-(q:Int) = k-(q:Int)-1 := by omega
  simp only [den, oneMinusTwoX, oneMinusX, shift] at *
  omega

/-- Removing q terms from a strict prefix sum gives the length-q window. -/
theorem previous_sub_shift (a : Coeff) (ha : ∀ k < 0, a k = 0) (q : Nat) (w : Int) :
    previous a w - previous a (w-(q:Int)) = window q a w := by
  induction q generalizing w with
  | zero => simp [window]
  | succ q ih =>
    have hs := ih (w-1)
    have hd := previous_difference a ha w
    have hj : w-1-(q:Int) = w-(↑(q+1):Int) := by omega
    rw [hj] at hs
    simp only [window]
    omega

theorem window_add (a b : Coeff) (n : Nat) (w : Int) :
    window n (fun j => a j + b j) w = window n a w + window n b w := by
  induction n generalizing w with
  | zero => simp [window]
  | succ n ih =>
    simp only [window, ih]
    omega

/-- Numerical content of the two first-entry counts (3.3) and the quotient
dimension in (3.4), after using Corollary 3.2 and Lemma 2.4. All weights
outside the positive-weight relation spaces have dimension zero. -/
theorem recurrence_of_dimension_identities (q : Nat)
    (r I B U fixedU fixedR : Coeff) (negR : ∀ k < 0, r k = 0)
    (dimU : ∀ w, U w = (I w - B w) + r w)
    (dimFixedU : ∀ w, fixedU w = previous U w)
    (dimFixedR : ∀ w, fixedR w = previous r w)
    (quotient : ∀ w, U w - fixedU w = I (w-(q:Int)) - fixedR (w-(q:Int))) (w : Int) :
    r w = window q r w + I (w-(q:Int)) - (I w - B w) +
      previous (fun k => I k - B k) w := by
  have eqU : U = fun j => (I j - B j) + r j := funext dimU
  have h := quotient w
  rw [dimFixedU, dimFixedR, dimU w, eqU] at h
  change (I w - B w + r w) -
    window w.toNat (fun j => (I j - B j) + r j) w =
    I (w-(q:Int)) - previous r (w-(q:Int)) at h
  rw [window_add (fun j => I j - B j) r] at h
  have hd := previous_sub_shift r negR q w
  unfold previous at *
  omega

/-- Delete the first entry of an arbitrary nonempty tuple to obtain its
ordinary generating function, written without a denominator. -/
theorem allTuples_series_of_count (I : Coeff) (neg : ∀ k < 0, I k = 0)
    (count : ∀ w, I w = unitSeries w + previous I w) (w : Int) :
    oneMinusTwoX I w = oneMinusX unitSeries w := by
  have h := count w
  have h' := count (w-1)
  have hsum := previous_difference I neg w
  unfold oneMinusTwoX oneMinusX
  omega

/-- Removing the last entry gives the recurrence for bounded tuples. Among
them TT excludes precisely the nonempty tuples ending in q. These two
counts give the coefficient identity for the TT generating function. -/
theorem ttTuples_series_of_count (q : Nat) (C B : Coeff)
    (bounded : ∀ w, C w = unitSeries w + window q C w)
    (tt : ∀ w, B w = C w - C (w-(q:Int))) (w : Int) :
    den q B w = oneMinusX unitSeries w - oneMinusX unitSeries (w-(q:Int)) := by
  have bounds (k : Int) : den q C k = oneMinusX unitSeries k := by
    have h := bounded k
    have h' := bounded (k-1)
    have hs := window_difference C q k
    unfold den oneMinusTwoX oneMinusX
    omega
  have h := bounds w
  have h' := bounds (w-(q:Int))
  simp only [den, oneMinusTwoX, tt] at h h' ⊢
  have hj : w-1-(q:Int) = w-(q:Int)-1 := by omega
  have hk : w-(q:Int)-1-(q:Int) = w-(q:Int)-(q:Int)-1 := by omega
  rw [hj, hk]
  omega

/-- Collect the disjoint groups with prescribed first entries 1,...,b.
`tails j` is the list of tails for first entry j+1. -/
def byFirst : Nat → (Nat → List (List Nat)) → List (List Nat)
  | 0, _ => []
  | n+1, tails => byFirst n tails ++ (tails n).map (List.cons (n+1))

/-- Enumerate positive tuples of weight w. At remaining weight k the largest
allowed entry is width k. In particular width = Int.toNat gives unrestricted
tuples, and a constant width q gives tuples with entries at most q. -/
def tuples (width : Int → Nat) (w : Int) : List (List Nat) :=
  if w ≤ 0 then (if w = 0 then [[]] else []) else
    byFirst (width w) (fun j => tuples width (w-(j:Int)-1))
termination_by w.toNat
decreasing_by omega

theorem window_succ_last (n : Nat) (a : Coeff) (w : Int) :
    window (n+1) a w = window n a w + a (w-(n:Int)-1) := by
  have h := window_difference a n w
  simp only [window]
  omega

theorem byFirst_length (n : Nat) (tails : Int → List (List Nat)) (w : Int) :
    ((byFirst n (fun j => tails (w-(j:Int)-1))).length : Int) =
      window n (fun k => (tails k).length) w := by
  induction n with
  | zero => simp [window, byFirst]
  | succ n ih =>
    rw [window_succ_last]
    simp only [byFirst, List.length_append, List.length_map, Int.natCast_add, ih]

theorem window_nonpos (a : Coeff) (h : ∀ w < 0, a w = 0) (n : Nat) {w : Int}
    (hw : w ≤ 0) : window n a w = 0 := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
    have h' : w-1 < 0 := by omega
    simp [window, h _ h', ih (Int.le_of_lt h')]

/-- Counting the disjoint first-entry groups in the actual enumeration. -/
theorem tuples_count (width : Int → Nat) (w : Int) :
    ((tuples width w).length : Int) = unitSeries w +
      window (width w) (fun k => (tuples width k).length) w := by
  by_cases h : w ≤ 0
  · have neg (k : Int) (hk : k < 0) : ((tuples width k).length : Int) = 0 := by
      rw [tuples]
      simp [Int.le_of_lt hk, Int.ne_of_lt hk]
    rw [window_nonpos _ neg _ h, tuples]
    by_cases hz : w = 0 <;> simp [h, hz, unitSeries]
  · have hz : w ≠ 0 := by omega
    rw [tuples]
    simp only [if_neg h, unitSeries, if_neg hz, Int.zero_add]
    exact byFirst_length _ _ _

def tupleCount (w : Int) : Int := (tuples Int.toNat w).length

def boundedCount (q : Nat) (w : Int) : Int := (tuples (fun _ => q) w).length

/-- Attach the last entry j+1, j+1<q, to an arbitrary bounded prefix.
When w=0 the empty tuple is included by convention. -/
def ttRows (q : Nat) (w : Int) : List (List Nat) :=
  (if w = 0 then [[]] else []) ++
    (byFirst (q-1) (fun j => tuples (fun _ => q) (w-(j:Int)-1))).map List.reverse

def ttCount (q : Nat) (w : Int) : Int := (ttRows q w).length

theorem tupleCount_neg (k : Int) (hk : k < 0) : tupleCount k = 0 := by
  unfold tupleCount
  rw [tuples]
  simp [Int.le_of_lt hk, Int.ne_of_lt hk]

theorem ttCount_eq (q : Nat) (k : Int) :
    ttCount q k = unitSeries k + window (q-1) (boundedCount q) k := by
  unfold ttCount ttRows
  simp only [List.length_append, List.length_map, Int.natCast_add, byFirst_length]
  by_cases h : k = 0 <;> simp [h, unitSeries] <;> rfl

theorem ttCount_neg (q : Nat) (k : Int) (hk : k < 0) : ttCount q k = 0 := by
  have h (j : Int) (hj : j < 0) : boundedCount q j = 0 := by
    unfold boundedCount
    rw [tuples]
    simp [Int.le_of_lt hj, Int.ne_of_lt hj]
  rw [ttCount_eq, window_nonpos _ h _ (Int.le_of_lt hk)]
  simp [unitSeries, Int.ne_of_lt hk]

theorem tupleCount_series (w : Int) :
    oneMinusTwoX tupleCount w = oneMinusX unitSeries w := by
  apply allTuples_series_of_count
  · exact tupleCount_neg
  · exact tuples_count Int.toNat

theorem ttCount_series {q : Nat} (hq : 0 < q) (w : Int) :
    den q (ttCount q) w = oneMinusX unitSeries w - oneMinusX unitSeries (w-(q:Int)) := by
  apply ttTuples_series_of_count q (boundedCount q) (ttCount q)
  · exact tuples_count (fun _ => q)
  · intro k
    have eqC := tuples_count (fun _ => q) k
    change boundedCount q k = unitSeries k + window q (boundedCount q) k at eqC
    have eqB := ttCount_eq q k
    have hs := window_succ_last (q-1) (boundedCount q) k
    have hv : q-1+1 = q := by omega
    have hk : k-(↑(q-1):Int)-1 = k-(q:Int) := by omega
    rw [hv, hk] at hs
    omega

/-- End-to-end dimension calculation with concrete tuple enumerations.
The remaining assumptions identify the dimensions of the spaces via
Corollary 3.2, Theorem 3.3, Lemmas 2.4 and 3.4; their formulation includes
the paper's zero-weight and negative-weight conventions. -/
theorem theorem_1_12_of_ranks {q : Nat} (hq : 2 ≤ q)
    (r U fixedU fixedR : Coeff) (negR : ∀ k < 0, r k = 0)
    (dimU : ∀ w, U w = (tupleCount w - ttCount q w) + r w)
    (dimFixedU : ∀ w, fixedU w = previous U w)
    (dimFixedR : ∀ w, fixedR w = previous r w)
    (quotient : ∀ w, U w - fixedU w = tupleCount (w-(q:Int)) - fixedR (w-(q:Int)))
    (w : Int) :
    oneMinusTwoX (den q (den q r)) w =
      oneMinusX (oneMinusX unitSeries) (w-(q:Int)-(q:Int)-1) := by
  apply relation_dimension_series q r tupleCount (ttCount q)
  · intro k hk
    simp [tupleCount_neg k hk, ttCount_neg q k hk]
  · exact recurrence_of_dimension_identities q r tupleCount (ttCount q) U fixedU fixedR
      negR dimU dimFixedU dimFixedR quotient
  · exact tupleCount_series
  · exact ttCount_series (by omega)

/-- No first-entry group contains the empty tuple. -/
@[simp] theorem nil_not_byFirst (n : Nat) (tails : Nat → List (List Nat)) :
    [] ∉ byFirst n tails := by
  induction n with
  | zero => simp [byFirst]
  | succ n ih => simp [byFirst, ih]

theorem mem_byFirst (n a : Nat) (t : List Nat) (tails : Nat → List (List Nat)) :
    a :: t ∈ byFirst n tails ↔ 0 < a ∧ a ≤ n ∧ t ∈ tails (a-1) := by
  induction n with
  | zero => simp [byFirst]; omega
  | succ n ih =>
    rw [byFirst, List.mem_append, ih]
    constructor
    · rintro (h | h)
      · exact ⟨h.1, by omega, h.2.2⟩
      · obtain ⟨s, hs, eq⟩ := List.mem_map.mp h
        cases eq
        simp [hs]
    · rintro ⟨ha, hab, ht⟩
      by_cases he : a = n+1
      · subst a
        right
        exact List.mem_map.mpr ⟨t, by simpa using ht, rfl⟩
      · exact Or.inl ⟨ha, by omega, ht⟩

/-- Each listed tuple has one unique decomposition into first entry and tail. -/
theorem nodup_byFirst (n : Nat) (tails : Nat → List (List Nat))
    (h : ∀ j, (tails j).Nodup) : (byFirst n tails).Nodup := by
  induction n with
  | zero => simp [byFirst]
  | succ n ih =>
    apply List.pairwise_append.mpr
    refine ⟨ih, List.pairwise_map.mpr ?_, ?_⟩
    · exact (h n).imp (fun {a b} hn he => hn (List.cons.inj he).2)
    · intro a ha b hb he
      obtain ⟨t, _, rfl⟩ := List.mem_map.mp hb
      subst a
      have hn := (mem_byFirst n (n+1) t tails).mp ha
      omega

theorem tuples_nodup (width : Int → Nat) (w : Int) : (tuples width w).Nodup := by
  rw [tuples]
  split
  · split <;> simp
  · apply nodup_byFirst
    intro j
    exact tuples_nodup width (w-(j:Int)-1)
termination_by w.toNat
decreasing_by omega

/-- Condition on each entry and the weight of the remaining suffix. -/
def Fits (width : Int → Nat) : Int → List Nat → Prop
  | w, [] => w = 0
  | w, a :: t => 0 < a ∧ a ≤ width w ∧ Fits width (w-(a:Int)) t

theorem Fits.weight_nonneg {width w t} (h : Fits width w t) : 0 ≤ w := by
  induction t generalizing w with
  | nil =>
    change w = 0 at h
    omega
  | cons a t ih =>
    obtain ⟨ha, _, ht⟩ := h
    have hn := ih ht
    omega

theorem mem_tuples (width : Int → Nat) (w : Int) (t : List Nat) :
    t ∈ tuples width w ↔ Fits width w t := by
  induction t generalizing w with
  | nil =>
    rw [tuples]
    by_cases hz : w = 0
    · subst w; simp [Fits]
    · by_cases hn : w ≤ 0 <;> simp [Fits, hn, hz]
  | cons a t ih =>
    rw [tuples]
    by_cases hn : w ≤ 0
    · have bad : ¬Fits width w (a :: t) := by
        rintro ⟨ha, _, ht⟩
        have ht' := Fits.weight_nonneg ht
        omega
      by_cases hz : w = 0
      · subst w; simp [bad]
      · simp [hn, hz, bad]
    · simp only [if_neg hn, mem_byFirst, Fits]
      by_cases ha : 0 < a
      · have he : w-(↑(a-1):Int)-1 = w-(a:Int) := by omega
        rw [he, ih]
      · simp [ha]

theorem mem_bounded (q : Nat) (w : Int) (t : List Nat) :
    t ∈ tuples (fun _ => q) w ↔
      (t.sum : Int) = w ∧ ∀ a ∈ t, 0 < a ∧ a ≤ q := by
  rw [mem_tuples]
  induction t generalizing w with
  | nil => simp [Fits, eq_comm]
  | cons a t ih =>
    simp only [Fits, ih, List.sum_cons, Int.natCast_add, List.forall_mem_cons]
    constructor
    · rintro ⟨ha, hb, hw, ht⟩
      exact ⟨by omega, ⟨ha,hb⟩, ht⟩
    · rintro ⟨hw, ⟨ha,hb⟩, ht⟩
      exact ⟨ha,hb,by omega,ht⟩

theorem mem_unrestricted (w : Int) (t : List Nat) :
    t ∈ tuples Int.toNat w ↔ (t.sum : Int) = w ∧ ∀ a ∈ t, 0 < a := by
  rw [mem_tuples]
  induction t generalizing w with
  | nil => simp [Fits, eq_comm]
  | cons a t ih =>
    simp only [Fits, ih, List.sum_cons, Int.natCast_add, List.forall_mem_cons]
    constructor
    · rintro ⟨ha, _, hw, ht⟩
      exact ⟨by omega, ha, ht⟩
    · rintro ⟨hw, ha, ht⟩
      exact ⟨ha,by omega,by omega,ht⟩

private theorem sum_snoc (a : Nat) (t : List Nat) : (t ++ [a]).sum = t.sum + a := by
  induction t with
  | nil => simp
  | cons b t ih => simp [ih, Nat.add_assoc]

private theorem sum_rev (t : List Nat) : t.reverse.sum = t.sum := by
  induction t with
  | nil => rfl
  | cons a t ih => simp [sum_snoc, ih, Nat.add_comm]

/-- TT consists of the empty tuple and the bounded tuples whose last entry
is strictly below q. This formulation explicitly includes the weight. -/
theorem mem_ttRows (q : Nat) (w : Int) (s : List Nat) :
    s ∈ ttRows q w ↔ (w = 0 ∧ s = []) ∨
      ∃ h a, s = h ++ [a] ∧ 0 < a ∧ a < q ∧ (h.sum : Int) + a = w ∧
        ∀ b ∈ h, 0 < b ∧ b ≤ q := by
  unfold ttRows
  rw [List.mem_append]
  apply or_congr
  · by_cases hw : w = 0 <;> simp [hw]
  · constructor
    · rintro hx
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
      cases v with
      | nil => exact (nil_not_byFirst _ _ hv).elim
      | cons a t =>
        obtain ⟨ha,hq,ht⟩ := (mem_byFirst _ _ _ _).mp hv
        obtain ⟨hw, hb⟩ := (mem_bounded _ _ _).mp ht
        refine ⟨t.reverse, a, List.reverse_cons, ha, by omega, ?_, ?_⟩
        · rw [sum_rev]; omega
        · simpa using hb
    · rintro ⟨t,a,rfl,ha,hq,hw,hb⟩
      refine List.mem_map.mpr ⟨a :: t.reverse, ?_, ?_⟩
      · apply (mem_byFirst _ _ _ _).mpr
        refine ⟨ha,by omega,(mem_bounded _ _ _).mpr ⟨?_,?_⟩⟩
        · rw [sum_rev]; omega
        · simpa using hb
      · simp

theorem ttRows_nodup (q : Nat) (w : Int) : (ttRows q w).Nodup := by
  unfold ttRows
  apply List.pairwise_append.mpr
  refine ⟨?_, List.pairwise_map.mpr ?_, ?_⟩
  · split <;> simp
  · exact (nodup_byFirst _ _ (fun _ => tuples_nodup _ _)).imp
      (fun {a b} h he => h (by simpa using congrArg List.reverse he))
  · intro s hs t ht e
    have hs' : s = [] := by
      split at hs <;> simp_all
    subst s
    subst t
    obtain ⟨v,hv,eq⟩ := List.mem_map.mp ht
    have hv' : v = [] := by simpa using congrArg List.reverse eq
    subst v
    exact nil_not_byFirst _ _ hv

/-- Multiplication by the whole denominator of (1.21). -/
def denominator (q : Nat) (a : Coeff) : Coeff := oneMinusTwoX (den q (den q a))

private theorem den_preserves_below (q : Nat) (a b : Coeff) (w : Int)
    (earlier : ∀ j < w, a j = b j) :
    ∀ j < w, den q a j = den q b j := by
  intro j hj
  unfold den oneMinusTwoX
  rw [earlier j hj, earlier (j-1) (by omega), earlier (j-(q:Int)-1) (by omega)]

private theorem den_first_difference (q : Nat) (a b : Coeff) (w : Int)
    (earlier : ∀ j < w, a j = b j) :
    den q a w - den q b w = a w - b w := by
  unfold den oneMinusTwoX
  rw [earlier (w-1) (by omega), earlier (w-(q:Int)-1) (by omega)]
  omega

/-- The denominator has constant coefficient 1: at the first coefficient
where two series can differ, multiplication preserves their difference. -/
theorem denominator_first_difference (q : Nat) (a b : Coeff) (w : Int)
    (earlier : ∀ j < w, a j = b j) :
    denominator q a w - denominator q b w = a w - b w := by
  have h₁ := den_preserves_below q a b w earlier
  have h₂ := den_preserves_below q (den q a) (den q b) w h₁
  have e₁ := den_first_difference q a b w earlier
  have e₂ := den_first_difference q (den q a) (den q b) w h₁
  unfold denominator oneMinusTwoX
  rw [h₂ (w-1) (by omega)]
  omega

private theorem from_earlier_weights (P : Int → Prop)
    (neg : ∀ w < 0, P w) (step : ∀ w, 0 ≤ w → (∀ j < w, P j) → P w) (w : Int) :
    P w := by
  by_cases hn : w < 0
  · exact neg w hn
  · apply step w (by omega)
    intro j hj
    by_cases hj' : j < 0
    · exact neg j hj'
    · exact from_earlier_weights P neg step j
termination_by w.toNat
decreasing_by omega

/-- Cancellation of the denominator on power series with no negative powers. -/
theorem denominator_unique (q : Nat) (a b : Coeff)
    (neg : ∀ w < 0, a w = b w) (same : ∀ w, denominator q a w = denominator q b w) :
    a = b := by
  funext w
  apply from_earlier_weights (fun j => a j = b j) neg _ w
  intro j _ h
  have hd := denominator_first_difference q a b j h
  rw [same j] at hd
  omega

/-- Expand a numerator divided by the denominator of (1.21) at the origin.
At weight w, all terms involving smaller weights have already been defined. -/
def coefficients (q : Nat) (numer : Coeff) (w : Int) : Int :=
  if w < 0 then 0 else
    numer w - denominator q (fun k =>
      if 0 ≤ k ∧ k < w then coefficients q numer k else 0) w
termination_by w.toNat
decreasing_by omega

theorem coefficients_neg (q : Nat) (numer : Coeff) {w : Int} (h : w < 0) :
    coefficients q numer w = 0 := by
  rw [coefficients]
  simp [h]

private theorem denominator_zero (q : Nat) (w : Int) :
    denominator q (fun _ => 0) w = 0 := by
  simp [denominator, den, oneMinusTwoX]

theorem coefficients_spec (q : Nat) (numer : Coeff) (neg : ∀ w < 0, numer w = 0)
    (w : Int) : denominator q (coefficients q numer) w = numer w := by
  by_cases hn : w < 0
  · have h := denominator_first_difference q (coefficients q numer) (fun _ => 0) w
        (fun k hk => coefficients_neg q numer (by omega))
    rw [denominator_zero, coefficients_neg q numer hn] at h
    simp only [Int.sub_zero, Int.sub_self] at h
    rw [neg w hn]
    omega
  · let earlier : Coeff := fun k => if 0 ≤ k ∧ k < w then coefficients q numer k else 0
    have h := denominator_first_difference q (coefficients q numer) earlier w (by
      intro k hk
      by_cases nk : 0 ≤ k
      · simp [earlier,nk,hk]
      · simp [earlier,nk,coefficients_neg q numer (w := k) (by omega)])
    have hz : earlier w = 0 := by simp [earlier]
    have hw : coefficients q numer w = numer w - denominator q earlier w := by
      rw [coefficients]
      simp only [if_neg hn]
      rfl
    rw [hz, hw] at h
    omega

/-- The sequence of coefficients of X^(2q+1)(1-X)^2. -/
def numerator (q : Nat) (w : Int) : Int :=
  oneMinusX (oneMinusX unitSeries) (w-(q:Int)-(q:Int)-1)

theorem numerator_below {q : Nat} {w : Int} (hw : w < 2*(q:Int)+1) :
    numerator q w = 0 := by
  have h₀ : w-(q:Int)-(q:Int)-1 ≠ 0 := by omega
  have h₁ : w-(q:Int)-(q:Int)-1-1 ≠ 0 := by omega
  have h₂ : w-(q:Int)-(q:Int)-1-1-1 ≠ 0 := by omega
  simp [numerator, oneMinusX, unitSeries, h₀, h₁, h₂]

theorem numerator_first (q : Nat) : numerator q (2*(q:Int)+1) = 1 := by
  have hj : 2*(q:Int)+1-(q:Int)-(q:Int)-1 = 0 := by omega
  simp [numerator, hj, oneMinusX, unitSeries]

/-- Equality with the uniquely defined coefficients of the rational function. -/
theorem relation_coefficients_of_series (q : Nat) (r : Coeff) (neg : ∀ k < 0, r k = 0)
    (series : ∀ w, denominator q r w = numerator q w) :
    r = coefficients q (numerator q) := by
  apply denominator_unique
  · intro w hw
    rw [neg w hw, coefficients_neg q _ hw]
  · intro w
    rw [series w, coefficients_spec]
    exact fun k hk => numerator_below (by omega)

/-- The first nonzero relation dimension occurs at weight 2q+1 and equals 1. -/
theorem relation_threshold_of_series (q : Nat) (r : Coeff) (neg : ∀ k < 0, r k = 0)
    (series : ∀ w, denominator q r w = numerator q w) :
    (∀ w < 2*(q:Int)+1, r w = 0) ∧ r (2*(q:Int)+1) = 1 := by
  have below (w : Int) : w < 2*(q:Int)+1 → r w = 0 := by
    apply from_earlier_weights (fun w => w < 2*(q:Int)+1 → r w = 0)
      (fun k hk _ => neg k hk) _ w
    intro k _ ih hk
    have h := denominator_first_difference q r (fun _ => 0) k
      (fun j hj => ih j hj (by omega))
    rw [denominator_zero, series k, numerator_below hk] at h
    simp only [Int.sub_zero, Int.sub_self] at h
    omega
  refine ⟨below, ?_⟩
  have h := denominator_first_difference q r (fun _ => 0) (2*(q:Int)+1) below
  rw [denominator_zero, series, numerator_first] at h
  simp only [Int.sub_zero] at h
  omega

end Megaera.Dimension
