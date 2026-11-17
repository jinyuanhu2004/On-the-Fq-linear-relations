import Megaera.FiniteSums

/-! The fundamental relation by telescoping. Here x d = 1/l_d,
a d = θ-θ^(q^(d+1)), and c = θ-θ^q = -D₁. -/
namespace Megaera.Fundamental
open Megaera.Finite

variable {K : Type u} [Arithmetic K]
local instance : Std.Associative (α := K) (· * ·) := ⟨Arithmetic.mulAssoc⟩
local instance : Std.Commutative (α := K) (· * ·) := ⟨Arithmetic.mulComm⟩

theorem power_mul_base (a b : K) (n : Nat) :
    power (a*b) n = power a n * power b n := by
  induction n with
  | zero => simp [power, Arithmetic.mulOne]
  | succ n ih => simp only [power, ih]; ac_rfl

theorem power_power (a : K) (n k : Nat) : power (power a n) k = power a (n*k) := by
  induction k with
  | zero => simp [power]
  | succ k ih => rw [power, ih, Nat.mul_succ, power_add]

def factor [Sub K] (θ : K) (q d : Nat) : K := θ - power θ (q^(d+1))

/-- The characteristic-dependent input is the q-Frobenius law. The
second hypothesis is the additive-group cancellation (b-z)+(a-b)=a-z. -/
theorem next_factor [Sub K] (θ : K) (q d : Nat)
    (frob : ∀ u v : K, power (u-v) q = power u q - power v q)
    (cancel : ∀ a b z : K, (b-z)+(a-b)=a-z) :
    factor θ q (d+1) = power (factor θ q d) q + (θ-power θ q) := by
  simp only [factor, frob, power_power, cancel, Nat.pow_succ q (d+1)]

private theorem pow_one_base (n : Nat) : power (1:K) n = 1 := by
  induction n with
  | zero => rfl
  | succ n h => rw [power, h, Arithmetic.mulOne]

/-- Multiplying the elementary telescoping identity by x_(d+1) yields
Si_d(q) = c Si_(d+1)(1,q-1). Both fundamental binary levels vanish below d=0. -/
theorem finite_identity (q : Nat) (hq : 0 < q)
    (a x : Nat → K) (c : K)
    (base : a 0 = c) (normalized : x 0 = 1)
    (next : ∀ d, a (d+1) = power (a d) q + c)
    (inverse : ∀ d, a d * x (d+1) = x d) (d : Nat) :
    level x d [q] = c * level x (d+1) [1, q-1] := by
  have hq' : q = (q-1)+1 := by omega
  have telescopes (k : Nat) :
      a k * power (x k) (q-1) = c * truncSum x (k+1) [q-1] := by
    induction k with
    | zero =>
      simp [truncSum, normalized, base, pow_one_base, Arithmetic.mulOne,
        Arithmetic.addComm (0:K), Arithmetic.addZero]
    | succ k ih =>
      have exp : power (a k) q = power (a k) (q-1) * a k := congrArg (power (a k)) hq'
      have step : power (a k) q * power (x (k+1)) (q-1) = a k * power (x k) (q-1) := by
        rw [exp, ← inverse k, power_mul_base]
        ac_rfl
      rw [next, Arithmetic.mulComm (_+_), Arithmetic.distrib, Arithmetic.mulComm _ (power _ q),
        step, ih, Arithmetic.mulComm _ c, ← Arithmetic.distrib]
      simp only [trunc_step x (k+1) [q-1], level, trunc_nil, Arithmetic.mulOne]
  have exp : power (x d) q = power (x d) (q-1) * x d := congrArg (power (x d)) hq'
  simp only [level, trunc_nil, Arithmetic.mulOne]
  change power (x d) q = c * ((1 * x (d+1)) * truncSum x (d+1) [q-1])
  rw [Arithmetic.mulComm 1, Arithmetic.mulOne, exp]
  calc
    _ = x (d+1) * (a d * power (x d) (q-1)) := by rw [← inverse d]; ac_rfl
    _ = _ := by rw [telescopes]; ac_rfl

end Megaera.Fundamental
