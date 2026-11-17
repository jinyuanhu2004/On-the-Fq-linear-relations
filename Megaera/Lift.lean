import Megaera.Carlitz

/-! Binary relations and their lifts for the concrete coefficient model,
Definition 1.3 and (1.14). The level d=-1 supplies the left endpoint of the
telescoping sum. -/
namespace Megaera.Lift
open Megaera.Carlitz Megaera.Finite

variable {F : Type u} [Arithmetic F] [Neg F]
local instance : Std.Associative (α := F) (· + ·) := ⟨Arithmetic.addAssoc⟩
local instance : Std.Commutative (α := F) (· + ·) := ⟨Arithmetic.addComm⟩

def exactLevel (q d : Nat) : Tuple → Series F
  | [] => fun _ => 0
  | a::s => product (seriesPow (inverseDenom q d) a) (trunc q d s)

def degree (q : Nat) : Int → Tuple → Series F
  | .ofNat d, s => exactLevel q d s
  | .negSucc 0, [] => unitSeries
  | .negSucc _, _ => fun _ => 0

def valueAt (f : Tuple → Series F) (p : FormalSum F) (n : Nat) : F :=
  total (fun e : F × Tuple => e.1 * f e.2 n) p

def Binary (q : Nat) (p : BinaryPair F) : Prop :=
  ∀ (d : Int) (n : Nat), valueAt (degree q d) p.1 n + valueAt (degree q (d+1)) p.2 n = 0

theorem trunc_exact (q d : Nat) (s : Tuple) (n : Nat) :
    trunc (F := F) q (d+1) s n = trunc q d s n + exactLevel q d s n := by
  cases s with
  | nil => cases d <;> simp [trunc, exactLevel, Arithmetic.addZero]
  | cons => rfl

theorem eval_step (q d : Nat) (p : FormalSum F) (n : Nat) :
    valueAt (trunc q (d+1)) p n =
      valueAt (trunc q d) p n + valueAt (exactLevel q d) p n := by
  induction p with
  | nil => exact (Arithmetic.addZero _).symm
  | cons e p ih =>
    change e.1 * trunc q (d+1) e.2 n + valueAt (trunc q (d+1)) p n =
      (e.1 * trunc q d e.2 n + valueAt (trunc q d) p n) +
        (e.1 * exactLevel q d e.2 n + valueAt (exactLevel q d) p n)
    rw [trunc_exact, Arithmetic.distrib, ih]
    ac_rfl

omit [Neg F] in
private theorem append_value (f : Tuple → Series F) (p p' : FormalSum F) (n : Nat) :
    valueAt f (p++p') n = valueAt f p n + valueAt f p' n := by
  induction p with
  | nil => simp [valueAt, total, Arithmetic.addComm (0:F), Arithmetic.addZero]
  | cons e p ih =>
    change _ + valueAt f (p++p') n = (_ + valueAt f p n) + _
    rw [ih, Arithmetic.addAssoc]

omit [Neg F] in
private theorem value_congr (f g : Tuple → Series F) (p : FormalSum F) (n : Nat)
    (h : ∀ e ∈ p, f e.2 n = g e.2 n) : valueAt f p n = valueAt g p n := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    change e.1 * f e.2 n + valueAt f p n = e.1 * g e.2 n + valueAt g p n
    rw [h e (by simp), ih (by intro z hz; exact h z (by simp [hz]))]

private theorem zero_trunc (q : Nat) (p : FormalSum F) (n : Nat)
    (hp : ∀ e ∈ p, e.2 ≠ []) : valueAt (trunc q 0) p n = 0 := by
  apply Carlitz.total_zero_of_members
  intro e he
  cases h : e.2 with
  | nil => exact (hp e he h).elim
  | cons a s => simp [h, trunc, Arithmetic.mulZero]

theorem binary_lift (q : Nat) (hq : 2 ≤ q) (p : BinaryPair F) (hp : Binary q p)
    (hs : ∀ e ∈ p.1 ++ p.2, Valid e.2 ∧ e.2 ≠ []) :
    ∀ n, evaluate q (liftPair p) n = 0 := by
  intro n
  have h₁ (e) (he : e ∈ p.1) := hs e (List.mem_append_left _ he)
  have h₂ (e) (he : e ∈ p.2) := hs e (List.mem_append_right _ he)
  have endpoint : valueAt (degree q (-1)) p.1 n = 0 := by
    apply Carlitz.total_zero_of_members
    intro e he
    cases h : e.2 with
    | nil => exact ((h₁ e he).2 h).elim
    | cons a s =>
      exact Arithmetic.mulZero _
  have base := hp (-1) n
  rw [endpoint, Arithmetic.addComm, Arithmetic.addZero] at base
  have paired (d : Nat) : valueAt (trunc q d) p.1 n + valueAt (trunc q (d+1)) p.2 n = 0 := by
    induction d with
    | zero =>
      rw [eval_step, zero_trunc q p.1 n (fun e he => (h₁ e he).2),
        zero_trunc q p.2 n (fun e he => (h₂ e he).2)]
      change 0+(0+valueAt (degree q 0) p.2 n) = 0
      change valueAt (degree q 0) p.2 n = 0 at base
      rw [base, Arithmetic.addZero, Arithmetic.addZero]
    | succ d ih =>
      calc
        _ = (valueAt (trunc q d) p.1 n + valueAt (trunc q (d+1)) p.2 n) +
              (valueAt (exactLevel q d) p.1 n + valueAt (exactLevel q (d+1)) p.2 n) := by
                rw [eval_step q d p.1, eval_step q (d+1) p.2]; ac_rfl
        _ = 0 := by rw [ih, show valueAt (exactLevel q d) p.1 n +
                       valueAt (exactLevel q (d+1)) p.2 n = 0 from hp (.ofNat d) n,
                       Arithmetic.addZero]
  change valueAt (li q) (p.1++p.2) n = 0
  rw [append_value,
      value_congr (li q) (trunc q (n+1)) p.1 n
        (fun e he => li_coeff _ _ _ _ hq (h₁ e he).1 (h₁ e he).2 (by omega)),
      value_congr (li q) (trunc q (n+2)) p.2 n
        (fun e he => li_coeff _ _ _ _ hq (h₂ e he).1 (h₂ e he).2 (by omega))]
  exact paired (n+1)

end Megaera.Lift
