import Megaera.Tuples

/-! Carlitz finite sums, §1.1. The finite product theorem only needs
a commutative semiring and a sequence of inverse denominators. We include
the precise algebraic laws we use to keep this development independent of mathlib. -/
namespace Megaera
namespace Finite

class Arithmetic (K : Type u) extends Add K, Mul K, Zero K, OfNat K 1 where
  addAssoc : ∀ a b c : K, a + b + c = a + (b + c)
  addComm : ∀ a b : K, a + b = b + a
  addZero : ∀ a : K, a + 0 = a
  mulAssoc : ∀ a b c : K, a * b * c = a * (b * c)
  mulComm : ∀ a b : K, a * b = b * a
  mulOne : ∀ a : K, a * 1 = a
  mulZero : ∀ a : K, a * 0 = 0
  distrib : ∀ a b c : K, a * (b + c) = a * b + a * c

variable {K : Type u} [Arithmetic K]
local instance : Std.Associative (α := K) (· + ·) := ⟨Arithmetic.addAssoc⟩
local instance : Std.Commutative (α := K) (· + ·) := ⟨Arithmetic.addComm⟩
local instance : Std.Associative (α := K) (· * ·) := ⟨Arithmetic.mulAssoc⟩
local instance : Std.Commutative (α := K) (· * ·) := ⟨Arithmetic.mulComm⟩

theorem zeroAdd (x : K) : 0 + x = x := by rw [Arithmetic.addComm, Arithmetic.addZero]
theorem oneMul (x : K) : 1 * x = x := by rw [Arithmetic.mulComm, Arithmetic.mulOne]
theorem zeroMul (x : K) : 0 * x = 0 := by rw [Arithmetic.mulComm, Arithmetic.mulZero]
private theorem addMul (a b c : K) : (a+b)*c = a*c+b*c := by
  rw [Arithmetic.mulComm, Arithmetic.distrib, Arithmetic.mulComm c a, Arithmetic.mulComm c b]

def power (x : K) : Nat → K
  | 0 => 1
  | n+1 => power x n * x

theorem power_add (x : K) (a b : Nat) : power x (a+b) = power x a * power x b := by
  induction b with
  | zero => simp [power, Arithmetic.mulOne]
  | succ b ih => simp [power, Nat.add_succ, ih, Arithmetic.mulAssoc]

/-- The paper's l_d. In use q is the cardinality of the constant field. -/
def carlitzDenom [Sub K] (θ : K) (q : Nat) : Nat → K
  | 0 => 1
  | d+1 => carlitzDenom θ q d * (θ - power θ (q^(d+1)))

/-- With x(d)=1/l_d, this is Si_<n(s), including the degree -1 convention. -/
def truncSum (x : Nat → K) : Nat → Tuple → K
  | 0, [] => 1
  | 0, _ :: _ => 0
  | _+1, [] => 1
  | n+1, a :: s => truncSum x n (a::s) + power (x n) a * truncSum x n s

def level (x : Nat → K) (n : Nat) : Tuple → K
  | [] => 0
  | a :: s => power (x n) a * truncSum x n s

/-- Extension to all integer degrees, as in §1.1. -/
def si (x : Nat → K) : Int → Tuple → K
  | .ofNat d, s => level x d s
  | .negSucc 0, [] => 1
  | .negSucc _, _ => 0

theorem trunc_nil (x : Nat → K) (n : Nat) : truncSum x n [] = 1 := by
  cases n <;> rfl

theorem trunc_step (x : Nat → K) (n : Nat) (s : Tuple) :
    truncSum x (n+1) s = truncSum x n s + level x n s := by
  cases s with
  | nil => simp only [trunc_nil, level, Arithmetic.addZero]
  | cons => rfl

/-- Evaluate a list of terms including its multiplicities. -/
def total {A : Type v} (f : A → K) : List A → K
  | [] => 0
  | a :: t => f a + total f t

theorem total_map {A B : Type} (f : B → K) (g : A → B) (s : List A) :
    total f (s.map g) = total (fun a => f (g a)) s := by
  induction s with
  | nil => rfl
  | cons _ _ ih => simp [total, ih]

private theorem total_add (f g : Tuple → K) (s : List Tuple) :
    total (fun t => f t + g t) s = total f s + total g s := by
  induction s with
  | nil => simp [total, Arithmetic.addZero]
  | cons _ _ ih => simp only [total, ih]; ac_rfl

theorem total_scale (a : K) (f : Tuple → K) (s : List Tuple) :
    total (fun t => a * f t) s = a * total f s := by
  induction s with
  | nil => simp [total, Arithmetic.mulZero]
  | cons _ _ ih => simp [total, ih, Arithmetic.distrib]

theorem total_append (f : Tuple → K) (s t : List Tuple) :
    total f (s++t) = total f s + total f t := by
  induction s with
  | nil => simp [total, zeroAdd]
  | cons _ _ ih => simp [total, ih, Arithmetic.addAssoc]

theorem total_step (x : Nat → K) (n : Nat) (s : List Tuple) :
    total (truncSum x (n+1)) s = total (truncSum x n) s + total (level x n) s := by
  rw [← total_add]
  apply congrArg (fun f : Tuple → K => total f s)
  funext t
  exact trunc_step x n t

theorem level_cons_map (x : Nat → K) (n a : Nat) (s : List Tuple) :
    total (level x n) (s.map (List.cons a)) = power (x n) a * total (truncSum x n) s := by
  rw [total_map]
  exact total_scale _ _ _

private theorem total_level_shuffle (x : Nat → K) (n a b : Nat) (s t : Tuple) :
    total (level x n) (quasiShuffle (a::s) (b::t)) =
      power (x n) a * total (truncSum x n) (quasiShuffle s (b::t)) +
      power (x n) b * total (truncSum x n) (quasiShuffle (a::s) t) +
      power (x n) (a+b) * total (truncSum x n) (quasiShuffle s t) := by
  rw [quasiShuffle]
  simp only [total_append, level_cons_map]

theorem total_zero_cons (x : Nat → K) (a : Nat) (s : List Tuple) :
    total (truncSum x 0) (s.map (List.cons a)) = 0 := by
  induction s with
  | nil => rfl
  | cons _ _ ih => simp [total, truncSum, ih, Arithmetic.addZero]

/-- Equation (1.8), at every natural truncation, for both empty and nonempty tuples. -/
theorem stuffle_product (x : Nat → K) (n : Nat) (s t : Tuple) :
    total (truncSum x n) (quasiShuffle s t) = truncSum x n s * truncSum x n t := by
  induction n generalizing s t with
  | zero =>
    cases s with
    | nil => simp [total, truncSum, oneMul, Arithmetic.addZero]
    | cons a s =>
      cases t with
      | nil => simp [total, truncSum, Arithmetic.mulOne, Arithmetic.addZero]
      | cons b t =>
        rw [quasiShuffle]
        simp only [total_append, total_zero_cons, truncSum, Arithmetic.addZero, Arithmetic.mulZero]
  | succ n ih =>
    cases s with
    | nil => simp [total, trunc_nil, oneMul, Arithmetic.addZero]
    | cons a s =>
      cases t with
      | nil => simp [total, trunc_nil, Arithmetic.mulOne, Arithmetic.addZero]
      | cons b t =>
        rw [total_step, total_level_shuffle, ih, ih, ih, ih, power_add]
        simp only [trunc_step, level, addMul, Arithmetic.distrib]
        ac_rfl

/-- Equation (1.9) on the nonempty domain of the head-merge rule. -/
theorem diamond_product (x : Nat → K) (n a b : Nat) (s t : Tuple) :
    total (level x n) (diamond (a::s) (b::t)) = level x n (a::s) * level x n (b::t) := by
  simp only [diamond, level_cons_map, stuffle_product, level, power_add]
  ac_rfl

/-- Equation (1.10) for a nonempty left input, including an empty right input. -/
theorem triangle_product (x : Nat → K) (n a : Nat) (s t : Tuple) :
    total (level x n) (triangle (a::s) t) = level x n (a::s) * truncSum x n t := by
  simp only [triangle, level_cons_map, stuffle_product, level, Arithmetic.mulAssoc]

/-- With the two printed empty-tuple conventions the unrestricted (1.9)
would imply 1=0 in the coefficient field. The normalized inverse l₀⁻¹ is 1. -/
theorem unrestricted_diamond_implies_one_eq_zero (x : Nat → K) (h₀ : x 0 = 1)
    (h : total (level x 0) (diamond [1] []) = level x 0 [1] * level x 0 []) :
    (1 : K) = 0 := by
  simpa [diamond, level, total, truncSum, power, h₀, Arithmetic.mulOne,
    Arithmetic.addZero, Arithmetic.mulZero] using h

end Finite
end Megaera
