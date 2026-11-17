import Megaera.FiniteSums

/-! The products (1.8)–(1.10) in integer degree, including the exceptional
exact value at d = -1. -/
namespace Megaera.Finite

variable {K : Type u} [Arithmetic K]

/-- Strict sum below an integer degree. For d ≤ -1 the range excludes
the exceptional level of the empty tuple. -/
def below (x : Nat → K) : Int → Tuple → K
  | .ofNat d, s => truncSum x d s
  | .negSucc _, _ => 0

private theorem total_vanish {A : Type} (f : A → K) (xs : List A)
    (h : ∀ a ∈ xs, f a = 0) : total f xs = 0 := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [total,h a (by simp),ih (fun t ht => h t (List.mem_cons_of_mem _ ht)),Arithmetic.addZero]

theorem stuffle_integer (x : Nat → K) (d : Int) (s t : Tuple) :
    total (below x d) (quasiShuffle s t) = below x d s * below x d t := by
  cases d with
  | ofNat d => exact stuffle_product _ _ _ _
  | negSucc n =>
    rw [total_vanish _ _ (by intros; rfl)]
    exact (Arithmetic.mulZero _).symm

private theorem si_negative_cons (x : Nat → K) (n a : Nat) (s : Tuple) :
    si x (.negSucc n) (a::s) = 0 := by cases n <;> rfl

/-- Exact product on nonempty arguments, the domain of the head-merge rule. -/
theorem diamond_integer (x : Nat → K) (d : Int) (a b : Nat) (s t : Tuple) :
    total (si x d) (diamond (a::s) (b::t)) = si x d (a::s) * si x d (b::t) := by
  cases d with
  | ofNat d => exact diamond_product _ _ _ _ _ _
  | negSucc n =>
    rw [diamond,total_map,total_vanish _ _ (fun v _ => si_negative_cons x n _ v),
      si_negative_cons, zeroMul]

/-- With the zero extension for the headless left argument this product
is defined for every pair of tuples. -/
theorem triangle_integer (x : Nat → K) (d : Int) (s t : Tuple) :
    total (si x d) (triangle s t) = si x d s * below x d t := by
  cases d with
  | ofNat d =>
    cases s with
    | nil => exact (zeroMul _).symm
    | cons a s => exact triangle_product _ _ _ _ _
  | negSucc n =>
    rw [show below x (.negSucc n) t = 0 from rfl, Arithmetic.mulZero]
    cases s with
    | nil => rfl
    | cons a s =>
      rw [triangle,total_map,total_vanish _ _ (fun v _ => si_negative_cons x n _ v)]

end Megaera.Finite
