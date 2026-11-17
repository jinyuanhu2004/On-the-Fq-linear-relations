import Megaera.FourLambda
import Megaera.FourMinimum

namespace Megaera.Rev4Indices

open Megaera.FourLambda Megaera.FourMinimum Megaera.Finite Megaera.Paper Megaera.Triangular
open Megaera.Carlitz

/-- The sum of j*x_j over the first n entries, with paper indices starting at one. -/
def moment (x : Coordinates) : Nat → Nat
  | 0 => 0
  | n+1 => moment x n + (n+1) * x n

theorem moment_bump (d i : Nat) (x : Coordinates) (n : Nat) :
    moment (bump d i x) n = moment x n + (if i < n then (i+1)*d else 0) := by
  induction n with
  | zero => simp [moment]
  | succ n ih =>
    simp only [moment, ih, bump]
    by_cases h : n = i
    · subst i
      simp [Nat.mul_add, Nat.add_assoc]
    · by_cases lt : i < n
      · simp [h, lt, Nat.lt_succ_of_lt lt]
        omega
      · simp [h, lt, show ¬ i < n+1 by omega]

/-- In y_k, move d=q−1 from coordinate r to an earlier coordinate k. -/
def transfer (d k r : Nat) (x : Coordinates) : Coordinates :=
  bump d k (fun j => if j = r then x j - d else x j)

/-- The precise decrease in the induction on page 23. Indices k,r here are zero-based. -/
theorem moment_transfer (d k r n : Nat) (x : Coordinates)
    (hk : k < r) (hr : r < n) (hd : d ≤ x r) :
    moment (transfer d k r x) n + (r-k)*d = moment x n := by
  let y : Coordinates := fun j => if j = r then x j - d else x j
  have restore : bump d r y = x := by
    funext j
    by_cases h : j = r
    · subst j
      simpa [bump, y] using Nat.sub_add_cancel hd
    · simp [bump, y, h]
  have original := moment_bump d r y n
  rw [restore, if_pos hr] at original
  have difference : (k+1)*d + (r-k)*d = (r+1)*d := by
    rw [← Nat.add_mul]
    congr 1
    omega
  change moment (bump d k y) n + _ = _
  rw [moment_bump, if_pos (Nat.lt_trans hk hr), Nat.add_assoc, difference, ← original]

theorem transfer_decreases (d k r n : Nat) (x : Coordinates)
    (hp : 0 < d) (hk : k < r) (hr : r < n) (hd : d ≤ x r) :
    moment (transfer d k r x) n < moment x n := by
  have := moment_transfer d k r n x hk hr hd
  have := Nat.mul_pos (Nat.sub_pos_of_lt hk) hp
  omega

/-- The same comparison applies when both tuples are increased at coordinate j. -/
theorem shifted_transfer_decreases (d j k r n : Nat) (x : Coordinates)
    (hp : 0 < d) (hk : k < r) (hr : r < n) (hd : d ≤ x r) :
    moment (bump d j (transfer d k r x)) n < moment (bump d j x) n := by
  rw [moment_bump, moment_bump]
  exact Nat.add_lt_add_right (transfer_decreases d k r n x hp hk hr hd) _

/-- Congruence of a positive final entry with b also allows a transfer when
b=q−1 (where the residue modulo q−1 is zero). -/
theorem terminal_transfer_positive {a b d : Nat} (hb : 0 < b) (ha : b < a)
    (congruent : a % d = b % d) : d < a := by
  apply Nat.lt_of_not_ge
  intro small
  rw [Nat.mod_eq_of_lt (show b < d by omega)] at congruent
  rcases Nat.eq_or_lt_of_le small with rfl | lt
  · simp at congruent
    omega
  · rw [Nat.mod_eq_of_lt lt] at congruent
    omega

/-- All permitted transfers are well-founded, even without requiring the
source to be the rightmost overflow. A further restriction inherits this. -/
theorem transfers_wellFounded (d n : Nat) (hd : 0 < d) :
    WellFounded (fun (y x : Coordinates) =>
      ∃ k r, k < r ∧ r < n ∧ d ≤ x r ∧ y = transfer d k r x) := by
  apply Subrelation.wf (r := fun y x : Coordinates => moment y n < moment x n)
  · intro y x step
    obtain ⟨k, r, hk, hr, valid, rfl⟩ := step
    exact transfer_decreases d k r n x hd hk hr valid
  · exact InvImage.wf (fun x => moment x n) Nat.lt_wfRel.wf

theorem inc_length (s : Tuple) (hs : s ≠ []) : (incLast s).length = s.length := by
  cases s with
  | nil => contradiction
  | cons a t => exact incLast_length a t

private theorem inc_nonempty (s : Tuple) (hs : s ≠ []) : incLast s ≠ [] := by
  intro h
  have he := inc_length s hs
  rw [h] at he
  exact hs (List.length_eq_zero_iff.mp he.symm)

theorem raised_length (q : Nat) (s : Tuple) (hs : s ≠ []) :
    (raiseFirst q (incLast s)).length = s.length := by
  have hn := inc_nonempty s hs
  rw [← inc_length s hs]
  cases he : incLast s with
  | nil => exact (hn he).elim
  | cons a t => rfl

private theorem added_length (k : Nat) (a : Nat) (s : Tuple) :
    (addLast k (a :: s)).length = (a :: s).length := by
  induction s generalizing a with
  | nil => rfl
  | cons b t ih =>
    simp only [addLast, List.length_cons, ih]

theorem last_width (k : Nat) (t : Tuple) : (addLast k t).length = max 1 t.length := by
  cases t with
  | nil => rfl
  | cons a s => simpa using added_length k a s

variable {F : Type u} [Arithmetic F] [Neg F]

/-- The actual minimum of a general lift has the corrected depth on page 24.
In particular the empty suffix contributes one. -/
theorem general_minimum_depth (q : Nat) (hq : 2 ≤ q) (h s t : Tuple) (hs : s ≠ []) :
    ∃ a, UnitMinimum (coordinates (lifted (F:=F) q h s t)) a ∧
      a.length = h.length + s.length + max 1 t.length := by
  refine ⟨_, lemma_4_1_i_ii q hq h s t hs, ?_⟩
  simp only [List.length_append, raised_length q s hs, last_width, Nat.add_assoc]

/-- At a type III pivot the left summand and the difference have the same minimum
depth. The right summand has one additional entry exactly when t is empty. -/
theorem typeIII_minimum_depths (q : Nat) (field : ConstantField F q) (h s u t : Tuple)
    (hs : s ≠ []) (hu : u ≠ []) :
    ∃ a b c : Tuple,
      UnitMinimum (coordinates (lifted (F:=F) q h s (incLast u ++ t))) a ∧
      UnitMinimum (coordinates (lifted (F:=F) q h (incLast s ++ u) t)) b ∧
      UnitMinimum (fun x => coordinates (lifted (F:=F) q h s (incLast u ++ t)) x +
        (-coordinates (lifted (F:=F) q h (incLast s ++ u) t) x)) c ∧
      c.length = h.length + s.length + u.length + t.length ∧
      a.length = c.length ∧ b.length = c.length + (if t = [] then 1 else 0) := by
  have hsu : incLast s ++ u ≠ [] := by simp [hu]
  obtain ⟨a, ha, da⟩ := general_minimum_depth (F:=F) q field.two_le h s (incLast u ++ t) hs
  obtain ⟨b, hb, db⟩ := general_minimum_depth (F:=F) q field.two_le h (incLast s ++ u) t hsu
  refine ⟨a, b, _, ha, hb, lemma_4_1_iii q field h s u t hs hu, ?_⟩
  simp only [List.length_append, raised_length q s hs, last_width, inc_length u hu,
    inc_length s hs] at *
  have pos : 0 < u.length := List.length_pos_iff.mpr hu
  cases t <;> simp_all <;> omega

/-- For an empty final tail the second general lift has zero coefficient
at every tuple on the shortest layer of the type III difference. -/
theorem typeIII_terminal_second_zero (q : Nat) (field : ConstantField F q)
    (h s u x : Tuple) (hs : s ≠ []) (hu : u ≠ [])
    (hx : x.length = h.length + s.length + u.length) :
    coordinates (lifted (F:=F) q h (incLast s ++ u) []) x = 0 := by
  obtain ⟨_, b, _, _, hb, _, dc, _, db⟩ := typeIII_minimum_depths q field h s u [] hs hu
  apply hb.2 x
  left
  change x.length < b.length
  simp at db dc
  omega

end Megaera.Rev4Indices
