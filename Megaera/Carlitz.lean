import Megaera.FiniteSums
import Megaera.Completeness

/-! Concrete coefficients at infinity. With T=θ⁻¹, the inverse of the i-th
factor θ−θ^(q^i) expands as −T^(q^i)/(1−T^(q^i−1)), for i>0 and q≥2.
All series operations needed to evaluate a positive tuple use finite sums
at each coefficient. F is a parameter for the constant field. -/
namespace Megaera.Carlitz
open Megaera.Finite

variable {F : Type u} [Arithmetic F]

abbrev Series (F : Type u) := Nat → F

def unitSeries : Series F := fun n => if n = 0 then 1 else 0

def addSeries (f g : Series F) : Series F := fun n => f n + g n

/-- Finite Cauchy product. -/
def product (f g : Series F) : Series F := fun n =>
  total (fun j => f j * g (n-j)) (List.range (n+1))

/-- T^m f. -/
def shift (m : Nat) (f : Series F) : Series F :=
  fun n => if m ≤ n then f (n-m) else 0

/-- Coefficient recursion for f/(1-T^m), m positive. -/
def divideGeometric (m : Nat) (f : Series F) (n : Nat) : F :=
  if 0 < m ∧ m ≤ n then f n + divideGeometric m f (n-m) else f n
termination_by n
decreasing_by omega

theorem divideGeometric_spec (m : Nat) (hm : 0 < m) (f : Series F) (n : Nat) :
    divideGeometric m f n = f n + shift m (divideGeometric m f) n := by
  rw [divideGeometric]
  by_cases h : m ≤ n <;> simp [h, hm, shift, Arithmetic.addZero]

/-- Coefficients of 1/l_d. The initial coefficient sequence is 1. -/
def inverseDenom [Neg F] (q : Nat) : Nat → Series F
  | 0 => unitSeries
  | d+1 =>
    let e := q^(d+1)
    shift e (fun n => - divideGeometric (e-1) (inverseDenom q d) n)

def seriesPow (f : Series F) : Nat → Series F
  | 0 => unitSeries
  | n+1 => product f (seriesPow f n)

/-- The head index is strictly smaller than N. -/
def trunc [Neg F] (q : Nat) : Nat → Tuple → Series F
  | 0, [] => unitSeries
  | 0, _ :: _ => fun _ => 0
  | _+1, [] => unitSeries
  | d+1, a::t => addSeries (trunc q d (a::t))
      (product (seriesPow (inverseDenom q d) a) (trunc q d t))

theorem total_zero_of_members {A : Type v} (f : A → F) (l : List A)
    (h : ∀ j ∈ l, f j = 0) : total f l = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [total, h a (by simp), ih (by intro j hj; exact h j (by simp [hj])),
      Arithmetic.addZero]

theorem product_zero_below (f g : Series F) (n : Nat) (h : ∀ j ≤ n, f j = 0) :
    product f g n = 0 := by
  apply total_zero_of_members
  intro j hj
  have hj' := List.mem_range.mp hj
  rw [h j (by omega), Arithmetic.mulComm, Arithmetic.mulZero]

private theorem le_pow (q : Nat) (hq : 2 ≤ q) (d : Nat) : d+1 ≤ q^d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Nat.pow_succ]
    have h := Nat.mul_le_mul_left (q^d) hq
    omega

theorem inverseDenom_below [Neg F] (q d n : Nat) (hq : 2 ≤ q) (hn : n < d) :
    inverseDenom (F := F) q d n = 0 := by
  cases d with
  | zero => omega
  | succ d =>
    have hp := le_pow q hq (d+1)
    simp only [inverseDenom, shift, if_neg (show ¬ q^(d+1) ≤ n by omega)]

/-- At a fixed coefficient the truncated sums stabilize. The hypothesis
on the first entry is automatic for the nonempty tuples of the paper. -/
theorem trunc_stable [Neg F] (q n : Nat) (hq : 2 ≤ q) (s : Tuple)
    (hs : Valid s) (N : Nat) (hN : n+1 ≤ N) :
    trunc (F := F) q N s n = trunc q (n+1) s n := by
  induction N with
  | zero => omega
  | succ d ih =>
    by_cases heq : d = n
    · simp [heq]
    have hd : n < d := by omega
    cases s with
    | nil => rfl
    | cons a s =>
      have ha : 0 < a := hs a (by simp)
      have hz : product (seriesPow (inverseDenom (F := F) q d) a) (trunc q d s) n = 0 := by
        apply product_zero_below
        intro k hk
        cases a with
        | zero => omega
        | succ b =>
          apply product_zero_below
          intro j hj
          exact inverseDenom_below q d j hq (by omega)
      change trunc q d (a::s) n + _ = _
      rw [hz, Arithmetic.addZero]
      exact ih (by omega)

/-- Sum of exact levels d ≥ 0 in F[[θ⁻¹]]. An empty strict tail
contributes 1 in `trunc`; the exact level of the empty tuple is supported
at d = -1 and so contributes zero to this sum. -/
def li [Neg F] (q : Nat) (s : Tuple) : Series F :=
  if s = [] then fun _ => 0 else fun n => trunc q (n+1) s n

theorem li_coeff [Neg F] (q n N : Nat) (s : Tuple) (hq : 2 ≤ q)
    (hs : Valid s) (hne : s ≠ []) (hN : n+1 ≤ N) : li (F := F) q s n = trunc q N s n := by
  simpa [li, hne] using (trunc_stable (F := F) q n hq s hs N hN).symm

def evaluate [Neg F] (q : Nat) (p : FormalSum F) : Series F := fun n =>
  total (fun e : F × Tuple => e.1 * li q e.2 n) p

/-- Equality in the free vector space of tuples, independent of the order
of summands and of the presentation chosen. -/
def coordinates (p : FormalSum F) (s : Tuple) : F :=
  total (fun e : F × Tuple => if e.2 = s then e.1 else 0) p

theorem sum_add {A : Type v} (f g : A → F) (l : List A) :
    total (fun i => f i + g i) l = total f l + total g l := by
  let addA : Std.Associative (α := F) (· + ·) := ⟨Arithmetic.addAssoc⟩
  let addC : Std.Commutative (α := F) (· + ·) := ⟨Arithmetic.addComm⟩
  induction l with
  | nil => simp [total, Arithmetic.addZero]
  | cons a l ih => simp only [total, ih]; ac_rfl

private theorem sum_point (l : List Tuple) (s : Tuple) (v : F) (hn : l.Nodup) :
    total (fun j => if s = j then v else 0) l = (if s ∈ l then v else 0) := by
  induction l with
  | nil => simp [total]
  | cons a l ih =>
    obtain ⟨ha, hl⟩ := List.nodup_cons.mp hn
    by_cases he : s = a
    · subst s; simp [total, ih hl, ha, Arithmetic.addZero]
    · simp [total, ih hl, he, Arithmetic.addComm (0:F) _, Arithmetic.addZero]

theorem pairing (p : FormalSum F) (g : Tuple → F) (l : List Tuple)
    (hn : l.Nodup) (hs : ∀ e ∈ p, e.2 ∈ l) :
    total (fun s => coordinates p s * g s) l = total (fun e : F × Tuple => e.1 * g e.2) p := by
  induction p with
  | nil =>
    apply total_zero_of_members
    intro j _
    change 0 * _ = _
    rw [Arithmetic.mulComm, Arithmetic.mulZero]
  | cons e p ih =>
    have hh := hs e (by simp)
    have ht := ih (by intro z hz; exact hs z (by simp [hz]))
    have hex (s : Tuple) : coordinates (e::p) s * g s =
        (if e.2 = s then e.1 * g e.2 else 0) + coordinates p s * g s := by
      change ((if e.2 = s then e.1 else 0) + coordinates p s) * g s = _
      rw [Arithmetic.mulComm, Arithmetic.distrib]
      split <;> rename_i h
      · rw [h, Arithmetic.mulComm (g s), Arithmetic.mulComm (g s)]
      · rw [Arithmetic.mulZero, Arithmetic.mulComm (g s)]
    simp only [hex, sum_add, sum_point l e.2 _ hn, if_pos hh, ht, total]

private def support : List Tuple → List Tuple
  | [] => []
  | s::l => if s ∈ support l then support l else s :: support l

private theorem support_spec (l : List Tuple) :
    (support l).Nodup ∧ ∀ s ∈ l, s ∈ support l := by
  induction l with
  | nil => simp [support]
  | cons a l ih =>
    obtain ⟨hd, hm⟩ := ih
    by_cases h : a ∈ support l
    · simp only [support, if_pos h, List.mem_cons]
      exact ⟨hd, fun s hs => hs.elim (fun e => e ▸ h) (hm s)⟩
    · simp only [support, if_neg h, List.mem_cons, List.nodup_cons]
      exact ⟨⟨h,hd⟩, fun s hs => hs.imp id (hm s)⟩

/-- Every scalar linear functional on tuples respects equality of coordinates. -/
theorem linear_form_congr (g : Tuple → F) (p p' : FormalSum F) (h : coordinates p = coordinates p') :
    total (fun e : F × Tuple => e.1 * g e.2) p = total (fun e : F × Tuple => e.1 * g e.2) p' := by
  let l := p.map Prod.snd ++ p'.map Prod.snd
  obtain ⟨hd, hm⟩ := support_spec l
  rw [← pairing p g (support l) hd
        (fun z hz => hm _ (List.mem_append_left _ (List.mem_map.mpr ⟨z,hz,rfl⟩))),
      ← pairing p' g (support l) hd
        (fun z hz => hm _ (List.mem_append_right _ (List.mem_map.mpr ⟨z,hz,rfl⟩))), h]

/-- Evaluation respects equality of vector-space coefficients even when
the two presentations have different order, repetitions, or cancellations. -/
theorem evaluate_congr [Neg F] (q : Nat) (p p' : FormalSum F)
    (h : coordinates p = coordinates p') : evaluate q p = evaluate q p' :=
  funext (fun n => linear_form_congr (fun s => li q s n) p p' h)

/-- A homogeneous representative of a relation at the all-ones point. -/
def Relation [Neg F] (q w : Nat) (p : FormalSum F) : Prop :=
  (∀ e ∈ p, Valid e.2 ∧ weight e.2 = w) ∧ ∀ n, evaluate q p n = 0

/-- A finite F-linear combination of the actual BCP lifts at this weight.
The generators use nonempty primitive labels. -/
def InBCP [Neg F] (q w : Nat) (p : FormalSum F) : Prop :=
  ∃ rows : List (F × Tuple × Tuple × Tuple),
    (∀ e ∈ rows, Valid e.2.1 ∧ Valid e.2.2.1 ∧ Valid e.2.2.2 ∧ e.2.2.2 ≠ [] ∧
      weight e.2.1 + weight e.2.2.1 + weight e.2.2.2 + 2*q = w) ∧
    ∀ s, coordinates p s = total (fun e : F × Tuple × Tuple × Tuple =>
      e.1 * coordinates (bcpGenerator q e.2.1 e.2.2.1 e.2.2.2) s) rows

/-- The precise positive-weight completeness target, for a chosen coefficient
field F of order q (the cardinality/field hypotheses belong at instantiation).
This is a proposition, not a proof of Theorem 1.10. -/
def CompletenessStatement (F : Type u) [Arithmetic F] [Neg F] (q : Nat) : Prop :=
  ∀ w, 0 < w → ∀ p : FormalSum F, (∀ e ∈ p, Valid e.2 ∧ weight e.2 = w) →
    (Relation q w p ↔ InBCP q w p)

end Megaera.Carlitz
