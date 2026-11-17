import Megaera.Shaped

/-! Soundness of the B, B* and C operators in Definitions 1.3 and 1.4.
The empty tuple has a level at degree -1. Nonempty support is therefore
recorded explicitly; it follows from any positive homogeneous weight. -/
namespace Megaera.BinaryOperators
open Megaera.Finite Megaera.Shaped
variable {K : Type u}

/-- Every tuple in both components is nonempty. -/
def NonemptySupport (p : BinaryPair K) : Prop :=
  (∀ z ∈ p.1, z.2 ≠ []) ∧ (∀ z ∈ p.2, z.2 ≠ [])

theorem nonemptySupport_of_weight (w : Nat) (hw : 0 < w) (p : BinaryPair K)
    (h : PairAt w p) : NonemptySupport p := by
  constructor
  · intro z hz he
    have hw' := h.1 z hz
    rw [he] at hw'
    simp only [weight] at hw'
    omega
  · intro z hz he
    have hw' := h.2 z hz
    rw [he] at hw'
    simp only [weight] at hw'
    omega

private theorem expand_nonempty (f : Tuple → List Tuple) (p : FormalSum K)
    (h : ∀ t, [] ∉ f t) : ∀ z ∈ expand f p, z.2 ≠ [] := by
  intro z hz
  obtain ⟨a,_,hs⟩ := List.mem_flatMap.mp hz
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hs
  change b ≠ []
  intro he
  exact h a.2 (he ▸ hb)

private theorem tri_nonempty (s t : Tuple) : [] ∉ triangle s t := by
  cases s <;> simp [triangle]

private theorem dia_left_nonempty (a : Nat) (s t : Tuple) : [] ∉ diamond (a::s) t := by
  cases t <;> simp [diamond]

private theorem dia_right_nonempty (a : Nat) (s t : Tuple) : [] ∉ diamond t (a::s) := by
  cases t <;> simp [diamond]

theorem bOp_nonempty (w : Tuple) (p : BinaryPair K) (h : NonemptySupport p) :
    NonemptySupport (bOp w p) := by
  cases w with
  | nil => exact h
  | cons a s =>
    constructor
    · intro z hz
      simp only [bOp,List.mem_append] at hz
      rcases hz with ((ht|hd)|ht)
      · exact expand_nonempty _ _ (tri_nonempty (a::s)) z ht
      · exact expand_nonempty _ _ (dia_left_nonempty a s) z hd
      · exact expand_nonempty _ _ (tri_nonempty (a::s)) z ht
    · simp [bOp]

theorem cOp_nonempty (w : Tuple) (p : BinaryPair K) (h : NonemptySupport p) :
    NonemptySupport (cOp w p) := by
  cases w with
  | nil => exact h
  | cons a s =>
    constructor
    · intro z hz
      simp only [cOp,List.mem_append] at hz
      rcases hz with hd|ht
      · exact expand_nonempty _ _ (dia_right_nonempty a s) z hd
      · exact expand_nonempty _ _ (fun t => tri_nonempty t (a::s)) z ht
    · exact expand_nonempty _ _ (fun t => tri_nonempty t (a::s))

private theorem bStar_nonempty (w : Tuple) (p : BinaryPair K) (h : NonemptySupport p) :
    NonemptySupport (bStar w p) := by
  induction w with
  | nil => exact h
  | cons a s ih => exact bOp_nonempty [a] _ ih

variable [Arithmetic K]
local instance : Std.Associative (α := K) (· + ·) := ⟨Arithmetic.addAssoc⟩
local instance : Std.Commutative (α := K) (· + ·) := ⟨Arithmetic.addComm⟩
local instance : Std.Associative (α := K) (· * ·) := ⟨Arithmetic.mulAssoc⟩
local instance : Std.Commutative (α := K) (· * ·) := ⟨Arithmetic.mulComm⟩

/-- The last natural level of the shifted component, at d=-1, is used
to start summation of the binary identity. -/
private theorem eval_negative (x : Nat → K) (n : Nat) (p : FormalSum K)
    (h : ∀ z ∈ p, z.2 ≠ []) : evaluate x (.negSucc n) p = 0 := by
  change weighted (si x (.negSucc n)) p = 0
  rw [← weighted_zero p]
  apply weighted_congr
  intro z hz
  cases he : z.2 with
  | nil => exact (h z hz he).elim
  | cons => cases n <;> rfl

theorem truncated_binary (x : Nat → K) (p : BinaryPair K) (s : NonemptySupport p)
    (h : Binary x p) (n : Nat) :
    weighted (truncSum x n) p.1 + weighted (truncSum x (n+1)) p.2 = 0 := by
  induction n with
  | zero =>
    rw [weighted_base _ _ s.1,weighted_step,weighted_base _ _ s.2,zeroAdd,zeroAdd]
    have base := h (.negSucc 0)
    rw [eval_negative x 0 _ s.1,zeroAdd] at base
    exact base
  | succ n ih =>
    rw [weighted_step x n,weighted_step x (n+1)]
    have step := h (.ofNat n)
    change weighted (level x n) p.1 + weighted (level x (n+1)) p.2 = 0 at step
    calc
      _ = (weighted (truncSum x n) p.1 + weighted (truncSum x (n+1)) p.2)
            + (weighted (level x n) p.1 + weighted (level x (n+1)) p.2) := by ac_rfl
      _ = 0 := by rw [ih,step,Arithmetic.addZero]

/-- The truncation of the ordinary lift has just one boundary term. For
any coefficient where that term vanishes, the truncation of the lift vanishes. -/
theorem lift_boundary (x : Nat → K) (p : BinaryPair K) (s : NonemptySupport p)
    (h : Binary x p) (n : Nat) :
    weighted (truncSum x n) (liftPair p) + weighted (level x n) p.2 = 0 := by
  have hh := truncated_binary x p s h n
  rw [weighted_step x n] at hh
  rw [liftPair,weighted_append,Arithmetic.addAssoc]
  exact hh

private theorem left_triangle (x : Nat → K) (n a : Nat) (s : Tuple) (p : FormalSum K) :
    weighted (level x n) (expand (triangle (a::s)) p) =
      level x n (a::s) * weighted (truncSum x n) p := by
  rw [weighted_expand,← weighted_factor]
  exact weighted_congr _ _ _ (fun z _ => triangle_product x n a s z.2)

private theorem right_triangle (x : Nat → K) (n : Nat) (w : Tuple) (p : FormalSum K)
    (hp : ∀ z ∈ p, z.2 ≠ []) :
    weighted (level x n) (expand (fun t => triangle t w) p) =
      truncSum x n w * weighted (level x n) p := by
  rw [weighted_expand,← weighted_factor]
  apply weighted_congr
  intro z hz
  cases he : z.2 with
  | nil => exact (hp z hz he).elim
  | cons a t => rw [triangle_product,Arithmetic.mulComm]

private theorem left_diamond (x : Nat → K) (n a : Nat) (s : Tuple) (p : FormalSum K)
    (hp : ∀ z ∈ p, z.2 ≠ []) :
    weighted (level x n) (expand (diamond (a::s)) p) =
      level x n (a::s) * weighted (level x n) p := by
  rw [weighted_expand,← weighted_factor]
  apply weighted_congr
  intro z hz
  cases he : z.2 with
  | nil => exact (hp z hz he).elim
  | cons => exact diamond_product _ _ _ _ _ _

private theorem right_diamond (x : Nat → K) (n a : Nat) (s : Tuple) (p : FormalSum K)
    (hp : ∀ z ∈ p, z.2 ≠ []) :
    weighted (level x n) (expand (fun t => diamond t (a::s)) p) =
      level x n (a::s) * weighted (level x n) p := by
  rw [weighted_expand,← weighted_factor]
  apply weighted_congr
  intro z hz
  cases he : z.2 with
  | nil => exact (hp z hz he).elim
  | cons a t => rw [diamond_product,Arithmetic.mulComm]

private theorem add_dist_right (a b c : K) : (a+b)*c = a*c+b*c := by
  rw [Arithmetic.mulComm,Arithmetic.distrib,Arithmetic.mulComm c a,Arithmetic.mulComm c b]

theorem bOp_binary (x : Nat → K) (w : Tuple) (p : BinaryPair K)
    (hp : NonemptySupport p) (h : Binary x p) : Binary x (bOp w p) := by
  cases w with
  | nil => exact h
  | cons a s =>
    intro d
    have rhs : evaluate x (d+1) (bOp (a::s) p).2 = 0 := rfl
    rw [rhs,Arithmetic.addZero]
    cases d with
    | negSucc n => exact eval_negative _ _ _ (bOp_nonempty (a::s) p hp).1
    | ofNat n =>
      change weighted (level x n) ((bOp (a::s) p).1) = 0
      simp only [bOp,weighted_append,left_triangle,left_diamond x n a s p.2 hp.2]
      have ht := truncated_binary x p hp h n
      rw [weighted_step] at ht
      calc
        _ = level x n (a::s) * (weighted (truncSum x n) p.1 +
              (weighted (truncSum x n) p.2 + weighted (level x n) p.2)) := by
          simp only [Arithmetic.distrib]; ac_rfl
        _ = 0 := by rw [ht,Arithmetic.mulZero]

theorem bStar_binary (x : Nat → K) (w : Tuple) (p : BinaryPair K)
    (hp : NonemptySupport p) (h : Binary x p) : Binary x (bStar w p) := by
  induction w with
  | nil => exact h
  | cons a s ih => exact bOp_binary _ [a] _ (bStar_nonempty s p hp) ih

theorem cOp_binary (x : Nat → K) (w : Tuple) (p : BinaryPair K)
    (hp : NonemptySupport p) (h : Binary x p) : Binary x (cOp w p) := by
  cases w with
  | nil => exact h
  | cons a s =>
    intro d
    cases d with
    | negSucc n =>
      have hp' := cOp_nonempty (a::s) _ hp
      rw [eval_negative x n _ hp'.1,zeroAdd]
      cases n with
      | zero =>
        change weighted (level x 0) (expand (fun t => triangle t (a::s)) p.2) = 0
        rw [right_triangle _ _ _ _ hp.2]
        exact zeroMul _
      | succ n => exact eval_negative _ n _ hp'.2
    | ofNat n =>
      change weighted (level x n) _ + weighted (level x (n+1)) _ = 0
      simp only [cOp,weighted_append,right_diamond x n a s p.1 hp.1,
        right_triangle x n (a::s) p.1 hp.1,right_triangle x (n+1) (a::s) p.2 hp.2]
      have step := h (.ofNat n)
      change weighted (level x n) p.1 + weighted (level x (n+1)) p.2 = 0 at step
      calc
        _ = truncSum x (n+1) (a::s) * (weighted (level x n) p.1 + weighted (level x (n+1)) p.2) := by
          simp only [trunc_step x n (a::s),Arithmetic.distrib,add_dist_right]
          ac_rfl
        _ = 0 := by rw [step,Arithmetic.mulZero]

/-- Every pair whose lift generates BCP satisfies Definition 1.3 in every
integer degree. This is finite-level soundness; the CMPL passage to the
infinite sum is a separate statement. -/
theorem bcp_pair_from_factors [Neg K] (q : Nat) (hq : 0 < q)
    (a x : Nat → K) (c : K) (base : a 0 = c) (normalized : x 0 = 1)
    (next : ∀ d, a (d+1) = power (a d) q + c) (inverse : ∀ d, a d * x (d+1) = x d)
    (cancel : ∀ a b d : K, a+b=a+d → b=d) (negOne : (1:K)+(-1)=0)
    (u v s : Tuple) (hs : Valid s) (hne : s ≠ []) :
    Binary x (bStar u (cOp v (primitive q s))) := by
  have hpr := primitive_binary_from_factors q hq a x c base normalized next inverse cancel negOne s hs hne
  have wt : PairAt (weight s + 0 + 2*q) (primitive q s : BinaryPair K) :=
    generalP_weight q hq s []
  have supp := nonemptySupport_of_weight _ (by omega) _ wt
  exact bStar_binary x u _ (cOp_nonempty v _ supp) (cOp_binary x v _ supp hpr)

end Megaera.BinaryOperators
