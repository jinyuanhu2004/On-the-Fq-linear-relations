import Megaera.Fundamental

/-! §2.1. Propagate the two primitive inputs using the actual finite sums.
The sign convention is c=-D₁, so the normalized relation says c Si_<n(P)
= Si_<n(Q). Equalities of level sums below use characteristic-free
semiring algebra; cancellation is listed exactly where needed. -/
namespace Megaera.Shaped
open Megaera.Finite

variable {K : Type u} [Arithmetic K]
local instance : Std.Associative (α := K) (· + ·) := ⟨Arithmetic.addAssoc⟩
local instance : Std.Commutative (α := K) (· + ·) := ⟨Arithmetic.addComm⟩
local instance : Std.Associative (α := K) (· * ·) := ⟨Arithmetic.mulAssoc⟩
local instance : Std.Commutative (α := K) (· * ·) := ⟨Arithmetic.mulComm⟩

abbrev Data := List Tuple × List Tuple

def Proportional (x : Nat → K) (c : K) (p : Data) : Prop :=
  ∀ n, total (truncSum x n) p.2 = c * total (truncSum x n) p.1

theorem level_proportional (x : Nat → K) (c : K) (p : Data)
    (cancel : ∀ a b d : K, a+b=a+d → b=d) (h : Proportional x c p) (n : Nat) :
    total (level x n) p.2 = c * total (level x n) p.1 := by
  have h' := h (n+1)
  rw [total_step, total_step, Arithmetic.distrib, h n] at h'
  exact cancel _ _ _ h'

/-- Prepending one multiplies each new level by the singleton level at n. -/
theorem prepend_proportional (x : Nat → K) (c : K) (p : Data)
    (h : Proportional x c p) : Proportional x c (mapData (List.cons 1) p) := by
  intro n
  induction n with
  | zero => simp [mapData, total_zero_cons, Arithmetic.mulZero]
  | succ n ih =>
    simp only [mapData] at ih
    change total (truncSum x (n+1)) (p.2.map _) = c * total (truncSum x (n+1)) (p.1.map _)
    rw [total_step, total_step, Arithmetic.distrib, ih, level_cons_map, level_cons_map, h n]
    ac_rfl

private theorem inc_level (x : Nat → K) (n : Nat) (s : Tuple) :
    level x n (incFirst s) = x n * level x n s := by
  cases s with
  | nil => simp [incFirst, level, Arithmetic.mulZero]
  | cons a t => simp only [incFirst, level, power]; ac_rfl

private theorem inc_base (x : Nat → K) (p : List Tuple) :
    total (truncSum x 0) (p.map incFirst) = total (truncSum x 0) p := by
  rw [total_map]
  apply congrArg (fun f : Tuple → K => total f p)
  funext s
  cases s <;> rfl

/-- Increasing the first entry multiplies Si_n by x_n. -/
theorem increase_proportional (x : Nat → K) (c : K) (p : Data)
    (cancel : ∀ a b d : K, a+b=a+d → b=d)
    (h : Proportional x c p) : Proportional x c (mapData incFirst p) := by
  intro n
  induction n with
  | zero => simpa only [mapData, inc_base] using h 0
  | succ n ih =>
    simp only [mapData] at ih
    change total (truncSum x (n+1)) (p.2.map _) = c * total (truncSum x (n+1)) (p.1.map _)
    rw [total_step, total_step, Arithmetic.distrib, ih]
    simp only [total_map, inc_level, total_scale, level_proportional x c p cancel h n]
    ac_rfl

private theorem total_flatMap (f : Tuple → K) (g : Tuple → List Tuple) (l : List Tuple) :
    total f (l.flatMap g) = total (fun t => total f (g t)) l := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [total, List.flatMap_cons, total_append, ih]

private theorem start_level (x : Nat → K) (q n : Nat) (t : Tuple) :
    total (level x n) (start q t) = level x n [q] * truncSum x (n+1) t := by
  cases t with
  | nil => simp [start, total, trunc_nil, Arithmetic.mulOne, Arithmetic.addZero]
  | cons a t =>
    simp only [start,total,level,truncSum,power_add,trunc_nil,Arithmetic.mulOne,
      Arithmetic.addZero,Arithmetic.distrib]
    ac_rfl

private theorem shifted_level (x : Nat → K) (q n : Nat) (t : Tuple) :
    total (level x n) ((quasiShuffle [q-1] t).map (List.cons 1)) =
      level x n [1,q-1] * truncSum x n t := by
  rw [level_cons_map, stuffle_product, level]
  ac_rfl

/-- Eq. (2.1) at n≥0, with the negative second component moved to the right. -/
def Balanced (x : Nat → K) (q : Nat) (p : Data) : Prop :=
  ∀ n, total (level x n) (p.1.flatMap (start q)) =
    total (level x (n+1)) (p.2.flatMap fun t => (quasiShuffle [q-1] t).map (List.cons 1))

theorem balanced_iff_positive (x : Nat → K) (q : Nat) (c : K) (p : Data)
    (fund : ∀ n, level x n [q] = c * level x (n+1) [1,q-1])
    (cancel : ∀ n a b, level x (n+1) [1,q-1] * a = level x (n+1) [1,q-1] * b → a=b) :
    Balanced x q p ↔ ∀ n,
      total (truncSum x (n+1)) p.2 = c * total (truncSum x (n+1)) p.1 := by
  have norm (n : Nat) :
      level x n [q] * total (truncSum x (n+1)) p.1 =
      level x (n+1) [1,q-1] * (c * total (truncSum x (n+1)) p.1) := by
    rw [fund]; ac_rfl
  simp only [Balanced, total_flatMap, start_level, shifted_level, total_scale, norm]
  constructor
  · intro h n
    exact cancel n _ _ (h n).symm
  · intro h n
    rw [h n]

private theorem trunc_zero_nonempty (x : Nat → K) (p : List Tuple) (hp : [] ∉ p) :
    total (truncSum x 0) p = 0 := by
  induction p with
  | nil => rfl
  | cons a t ih =>
    cases a with
    | nil => exact (hp (by simp)).elim
    | cons a s => simp [total,truncSum, zeroAdd, ih (fun hh => hp (List.mem_cons_of_mem _ hh))]

/-- Both inputs have positive weight in the primitive family, hence their
strict truncations at n=0 vanish. -/
theorem balanced_iff (x : Nat → K) (q : Nat) (c : K) (p : Data) (hp : [] ∉ p.1)
    (hq : [] ∉ p.2) (fund : ∀ n, level x n [q] = c * level x (n+1) [1,q-1])
    (cancel : ∀ n a b, level x (n+1) [1,q-1] * a = level x (n+1) [1,q-1] * b → a=b) :
    Balanced x q p ↔ Proportional x c p := by
  rw [balanced_iff_positive x q c p fund cancel]
  constructor
  · intro h n
    cases n with
    | zero => rw [trunc_zero_nonempty _ _ hp,trunc_zero_nonempty _ _ hq, Arithmetic.mulZero]
    | succ n => exact h n
  · exact fun h n => h (n+1)

/-- Summing the fundamental identity up to a strict cutoff. -/
theorem sum_fundamental (x : Nat → K) (q : Nat) (c : K)
    (fund : ∀ n, level x n [q] = c * level x (n+1) [1,q-1]) (n : Nat) :
    truncSum x n [q] = c * truncSum x (n+1) [1,q-1] := by
  induction n with
  | zero => simp [truncSum, Arithmetic.mulZero, Arithmetic.addZero]
  | succ n ih => rw [trunc_step x n [q], trunc_step x (n+1) [1,q-1], Arithmetic.distrib, ih, fund]

/-- The seed P((1)) of Theorem 2.2 follows by expanding the strict
truncation of the fundamental relation. -/
theorem seed_proportional (x : Nat → K) (q : Nat) (c : K)
    (fund : ∀ n, level x n [q] = c * level x (n+1) [1,q-1]) :
    Proportional x c (primitiveData q [1]) := by
  intro n
  change total (truncSum x n) [[1,q]] = c * total (truncSum x n) [[2,q-1],[1,1,q-1]]
  induction n with
  | zero => simp [total,truncSum,Arithmetic.addZero,Arithmetic.mulZero]
  | succ n ih =>
    rw [total_step, total_step, Arithmetic.distrib, ih]
    apply congrArg (fun y : K => c * total (truncSum x n) [[2,q-1],[1,1,q-1]] + y)
    simp only [total,Arithmetic.addZero]
    change power (x n) 1 * truncSum x n [q] =
      c * (power (x n) 2 * truncSum x n [q-1] + power (x n) 1 * truncSum x n [1,q-1])
    rw [sum_fundamental x q c fund n, trunc_step, level]
    simp only [power,oneMul,Arithmetic.distrib]
    ac_rfl

/-- Both propagation operations preserve the actual proportionality on all
primitive data, including the initial tuple (1). -/
theorem primitive_proportional (x : Nat → K) (q : Nat) (c : K)
    (fund : ∀ n, level x n [q] = c * level x (n+1) [1,q-1])
    (cancel : ∀ a b d : K, a+b=a+d → b=d)
    (s : Tuple) (hs : Valid s) (hne : s ≠ []) :
    Proportional x c (primitiveData q s) := by
  apply positiveTuple_induction (fun s => Proportional x c (primitiveData q s)) _ _ _ s hs hne
  · exact seed_proportional x q c fund
  · intro a t _ ih
    rw [primitiveData_prepend]
    exact prepend_proportional _ _ _ ih
  · intro a t _ ih
    rw [primitiveData_increase]
    exact increase_proportional _ _ _ cancel ih

/-- The forward implication from strict truncations to binary levels needs
no multiplicative cancellation. -/
theorem balanced_of_proportional (x : Nat → K) (q : Nat) (c : K) (p : Data)
    (fund : ∀ n, level x n [q] = c * level x (n+1) [1,q-1])
    (h : Proportional x c p) : Balanced x q p := by
  intro n
  simp only [total_flatMap,start_level,shifted_level,total_scale, h (n+1),fund n]
  ac_rfl

/-- Interpret a coefficient presentation in the integer degree d. -/
def evaluate (x : Nat → K) (d : Int) (p : FormalSum K) : K :=
  total (fun z : K × Tuple => z.1 * si x d z.2) p

/-- The binary relation of Definition 1.3, including its negative degrees. -/
def Binary (x : Nat → K) (r : BinaryPair K) : Prop :=
  ∀ d : Int, evaluate x d r.1 + evaluate x (d+1) r.2 = 0

private theorem evaluate_uniform (x : Nat → K) (d : Int) (a : K) (ss : List Tuple) :
    evaluate x d (withCoeff a ss) = a * total (si x d) ss := by
  induction ss with
  | nil => simp [evaluate,withCoeff,total,Arithmetic.mulZero]
  | cons s ss ih =>
    change a * si x d s + evaluate x d (withCoeff a ss) = a * (si x d s + total (si x d) ss)
    rw [ih,Arithmetic.distrib]

private theorem uniform_negative (x : Nat → K) (n : Nat) (ss : List Tuple) (h : [] ∉ ss) :
    total (si x (.negSucc n)) ss = 0 := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    cases s with
    | nil => exact (h (by simp)).elim
    | cons a s =>
      have ht : [] ∉ ss := fun hh => h (List.mem_cons_of_mem _ hh)
      rw [total, ih ht]
      cases n <;> exact Arithmetic.addZero 0

private theorem negative_one_times [Neg K] (negOne : (1:K)+(-1) = 0) (a : K) :
    a + (-(1:K)) * a = 0 := by
  calc
    _ = a*1 + a*(-1) := by rw [Arithmetic.mulOne, Arithmetic.mulComm a (-1)]
    _ = a*(1+(-1)) := (Arithmetic.distrib _ _ _).symm
    _ = 0 := by rw [negOne,Arithmetic.mulZero]

theorem binary_of_balanced [Neg K] (x : Nat → K) (q : Nat) (p : Data)
    (negOne : (1:K)+(-1) = 0) (h : Balanced x q p) :
    Binary x (shapedPair q p) := by
  let left := p.1.flatMap (start q)
  let right := p.2.flatMap fun t => (quasiShuffle [q-1] t).map (List.cons 1)
  have hl : [] ∉ left := by
    intro h
    obtain ⟨v,_,hv⟩ := List.mem_flatMap.mp h
    cases v <;> simp [start] at hv
  have hr : [] ∉ right := by
    intro h
    obtain ⟨v,_,hv⟩ := List.mem_flatMap.mp h
    simp at hv
  intro d
  change evaluate x d (withCoeff 1 left) + evaluate x (d+1) (withCoeff (-1) right) = 0
  rw [evaluate_uniform,evaluate_uniform,oneMul]
  cases d with
  | ofNat n =>
    change total (level x n) left + -1 * total (level x (n+1)) right = 0
    rw [show total (level x n) left = total (level x (n+1)) right from h n]
    exact negative_one_times negOne _
  | negSucc n =>
    rw [uniform_negative _ _ _ hl,zeroAdd]
    cases n with
    | zero =>
      change -1 * total (level x 0) right = 0
      dsimp only [right]
      rw [total_flatMap]
      simp only [shifted_level,total_scale]
      change -1 * ((power (x 0) 1 * 0) * _) = 0
      rw [Arithmetic.mulZero,zeroMul,Arithmetic.mulZero]
    | succ n =>
      change -1 * total (si x (.negSucc n)) right = 0
      rw [uniform_negative _ _ _ hr,Arithmetic.mulZero]

/-- Theorem 2.2 for the finite Carlitz sums. The fundamental relation is
the output of Fundamental.finite_identity; cancellation and 1+(-1)=0
are elementary coefficient-field laws. -/
theorem primitive_binary [Neg K] (x : Nat → K) (q : Nat) (c : K)
    (fund : ∀ n, level x n [q] = c * level x (n+1) [1,q-1])
    (cancel : ∀ a b d : K, a+b=a+d → b=d) (negOne : (1:K)+(-1) = 0)
    (s : Tuple) (hs : Valid s) (hne : s ≠ []) : Binary x (primitive q s) := by
  rw [primitive_eq_shaped]
  apply binary_of_balanced _ _ _ negOne
  exact balanced_of_proportional x q c _ fund (primitive_proportional x q c fund cancel s hs hne)

theorem balanced_of_binary [Neg K] (x : Nat → K) (q : Nat) (p : Data)
    (cancel : ∀ a b d : K, a+b=a+d → b=d) (negOne : (1:K)+(-1) = 0)
    (h : Binary x (shapedPair q p)) : Balanced x q p := by
  intro n
  let A := total (level x n) (p.1.flatMap (start q))
  let B := total (level x (n+1)) (p.2.flatMap fun t => (quasiShuffle [q-1] t).map (List.cons 1))
  have z := h (.ofNat n)
  simp only [shapedPair, evaluate_uniform, oneMul] at z
  change A + -1 * B = 0 at z
  change A = B
  apply cancel ((-1)*B)
  calc
    _ = A + -1 * B := Arithmetic.addComm _ _
    _ = 0 := z
    _ = B + -1 * B := (negative_one_times negOne B).symm
    _ = _ := Arithmetic.addComm _ _

/-- Lemma 2.1 for tuple sums with unit multiplicities (the inputs used by
the primitive family). Both output pairs satisfy the binary equation in
every integer degree, including d=-1. -/
theorem lemma_2_1 [Neg K] (x : Nat → K) (q : Nat) (c : K) (p : Data)
    (hp : [] ∉ p.1) (hq : [] ∉ p.2)
    (fund : ∀ n, level x n [q] = c * level x (n+1) [1,q-1])
    (cancelLevel : ∀ n a b, level x (n+1) [1,q-1]*a = level x (n+1) [1,q-1]*b → a=b)
    (cancelAdd : ∀ a b d : K, a+b=a+d → b=d) (negOne : (1:K)+(-1) = 0)
    (hin : Binary x (shapedPair q p)) :
    Binary x (shapedPair q (mapData (List.cons 1) p)) ∧
      Binary x (shapedPair q (mapData incFirst p)) := by
  have bal := balanced_of_binary x q p cancelAdd negOne hin
  have prop := (balanced_iff x q c p hp hq fund cancelLevel).mp bal
  exact ⟨binary_of_balanced x q _ negOne
    (balanced_of_proportional x q c _ fund (prepend_proportional x c p prop)),
    binary_of_balanced x q _ negOne
    (balanced_of_proportional x q c _ fund (increase_proportional x c p cancelAdd prop))⟩

/-- The factor recurrence in the Carlitz denominators supplies the
fundamental identity required for Theorem 2.2. -/
theorem primitive_binary_from_factors [Neg K] (q : Nat) (hq : 0 < q)
    (a x : Nat → K) (c : K)
    (base : a 0 = c) (normalized : x 0 = 1)
    (next : ∀ d, a (d+1) = power (a d) q + c)
    (inverse : ∀ d, a d * x (d+1) = x d)
    (cancel : ∀ a b d : K, a+b=a+d → b=d) (negOne : (1:K)+(-1)=0)
    (s : Tuple) (hs : Valid s) (hne : s ≠ []) : Binary x (primitive q s) :=
  primitive_binary x q c
    (Fundamental.finite_identity q hq a x c base normalized next inverse) cancel negOne s hs hne

/-- Evaluate an arbitrary coefficient presentation against a tuple function.
The coefficient field may already contain the represented constant field. -/
def weighted (f : Tuple → K) (p : FormalSum K) : K :=
  total (fun z : K × Tuple => z.1 * f z.2) p

def mapTuples (f : Tuple → Tuple) (p : FormalSum K) : FormalSum K :=
  p.map fun z => (z.1, f z.2)

/-- Extend the two components of the shaped pair bilinearly to arbitrary
input coefficients. The factor -1 acts on each shifted coefficient. -/
def weightedShaped [Neg K] (q : Nat) (P Q : FormalSum K) : BinaryPair K :=
  (expand (start q) P, (expand (fun t => (quasiShuffle [q-1] t).map (List.cons 1)) Q).map
    fun z => ((-(1:K))*z.1,z.2))

theorem weighted_congr (f g : Tuple → K) (P : FormalSum K)
    (h : ∀ z ∈ P, f z.2 = g z.2) : weighted f P = weighted g P := by
  induction P with
  | nil => rfl
  | cons a P ih =>
    have ha := h a (by simp)
    have ht := ih (fun z hz => h z (List.mem_cons_of_mem _ hz))
    change a.1 * f a.2 + weighted f P = a.1 * g a.2 + weighted g P
    rw [ha,ht]

theorem weighted_zero (P : FormalSum K) : weighted (fun _ => 0) P = 0 := by
  induction P with
  | nil => rfl
  | cons a P ih => change a.1 * 0 + weighted (fun _ => 0) P = 0; rw [ih,Arithmetic.mulZero,Arithmetic.addZero]

private theorem weighted_add (f g : Tuple → K) (P : FormalSum K) :
    weighted (fun t => f t + g t) P = weighted f P + weighted g P := by
  induction P with
  | nil => exact (Arithmetic.addZero _).symm
  | cons a P ih =>
    change a.1 * (f a.2 + g a.2) + weighted (fun t => f t + g t) P =
      (a.1*f a.2 + weighted f P) + (a.1*g a.2 + weighted g P)
    rw [ih,Arithmetic.distrib]
    ac_rfl

theorem weighted_factor (c : K) (f : Tuple → K) (P : FormalSum K) :
    weighted (fun t => c*f t) P = c*weighted f P := by
  induction P with
  | nil => exact (Arithmetic.mulZero _).symm
  | cons a P ih =>
    change a.1*(c*f a.2) + weighted (fun t => c*f t) P = c*(a.1*f a.2 + weighted f P)
    rw [ih,Arithmetic.distrib]
    ac_rfl

private theorem weighted_mapTuples (f : Tuple → K) (g : Tuple → Tuple) (P : FormalSum K) :
    weighted f (mapTuples g P) = weighted (fun t => f (g t)) P := by
  induction P with
  | nil => rfl
  | cons a P ih => exact congrArg (fun y => a.1*f (g a.2) + y) ih

private theorem weighted_scale (a : K) (f : Tuple → K) (P : FormalSum K) :
    weighted f (P.map fun z => (a*z.1,z.2)) = a*weighted f P := by
  induction P with
  | nil => exact (Arithmetic.mulZero _).symm
  | cons b P ih =>
    change a*b.1*f b.2 + weighted _ _ = a*(b.1*f b.2 + weighted _ P)
    rw [ih,Arithmetic.distrib,Arithmetic.mulAssoc]

theorem weighted_append (f : Tuple → K) (P Q : FormalSum K) :
    weighted f (P++Q) = weighted f P + weighted f Q := by
  induction P with
  | nil => exact (zeroAdd _).symm
  | cons a P ih =>
    change a.1*f a.2 + weighted f (P++Q) = (a.1*f a.2 + weighted f P) + weighted f Q
    rw [ih,Arithmetic.addAssoc]

private theorem weighted_uniform (a : K) (f : Tuple → K) (s : List Tuple) :
    weighted f (withCoeff a s) = a * total f s := by
  induction s with
  | nil => exact (Arithmetic.mulZero _).symm
  | cons t s ih =>
    change a*f t + weighted f (withCoeff a s) = a*(f t + total f s)
    rw [ih,Arithmetic.distrib]

theorem weighted_expand (f : Tuple → K) (g : Tuple → List Tuple) (P : FormalSum K) :
    weighted f (expand g P) = weighted (fun t => total f (g t)) P := by
  induction P with
  | nil => rfl
  | cons a P ih =>
    change weighted f (withCoeff a.1 (g a.2) ++ expand g P) =
      a.1 * total f (g a.2) + weighted (fun t => total f (g t)) P
    rw [weighted_append,weighted_uniform,ih]

theorem weighted_step (x : Nat → K) (n : Nat) (P : FormalSum K) :
    weighted (truncSum x (n+1)) P = weighted (truncSum x n) P + weighted (level x n) P := by
  rw [← weighted_add]
  exact weighted_congr _ _ _ (fun z _ => trunc_step x n z.2)

theorem weighted_base (x : Nat → K) (P : FormalSum K)
    (h : ∀ z ∈ P, z.2 ≠ []) : weighted (truncSum x 0) P = 0 := by
  rw [← weighted_zero P]
  exact weighted_congr _ _ _ (by
    intro z hz
    cases ht : z.2 with
    | nil => exact (h z hz ht).elim
    | cons => rfl)

private theorem weighted_transforms (x : Nat → K) (c : K) (P Q : FormalSum K)
    (cancel : ∀ a b d : K, a+b=a+d → b=d)
    (hp : ∀ n, weighted (truncSum x n) Q = c * weighted (truncSum x n) P) :
    ∀ n, (weighted (truncSum x n) (mapTuples (List.cons 1) Q) =
           c * weighted (truncSum x n) (mapTuples (List.cons 1) P)) ∧
          (weighted (truncSum x n) (mapTuples incFirst Q) =
           c * weighted (truncSum x n) (mapTuples incFirst P)) := by
  intro n
  induction n with
  | zero =>
    simp only [weighted_mapTuples]
    constructor
    · simp only [truncSum,weighted_zero,Arithmetic.mulZero]
    · have hh : (fun t => truncSum x 0 (incFirst t)) = truncSum x 0 := by
        funext t; cases t <;> rfl
      rw [hh,hp]
  | succ n ih =>
    have hl : weighted (level x n) Q = c * weighted (level x n) P := by
      have h := hp (n+1)
      rw [weighted_step,weighted_step,Arithmetic.distrib,hp n] at h
      exact cancel _ _ _ h
    constructor
    · rw [weighted_step,weighted_step,Arithmetic.distrib,ih.1]
      apply congrArg (fun y => c * weighted (truncSum x n) (mapTuples (List.cons 1) P) + y)
      simp only [weighted_mapTuples,level,weighted_factor,hp n]
      ac_rfl
    · rw [weighted_step,weighted_step,Arithmetic.distrib,ih.2]
      apply congrArg (fun y => c * weighted (truncSum x n) (mapTuples incFirst P) + y)
      simp only [weighted_mapTuples,inc_level,weighted_factor,hl]
      ac_rfl

private theorem weighted_shaped_at [Neg K] (x : Nat → K) (q n : Nat) (P Q : FormalSum K) :
    evaluate x (.ofNat n) (weightedShaped q P Q).1 +
        evaluate x (.ofNat (n+1)) (weightedShaped q P Q).2 =
      level x n [q] * weighted (truncSum x (n+1)) P +
        -1 * (level x (n+1) [1,q-1] * weighted (truncSum x (n+1)) Q) := by
  change weighted (level x n) _ + weighted (level x (n+1)) _ = _
  simp only [weightedShaped,weighted_scale,weighted_expand,start_level,shifted_level,weighted_factor]

private theorem weighted_shaped_negative [Neg K] (x : Nat → K) (q n : Nat) (P Q : FormalSum K) :
    evaluate x (.negSucc n) (weightedShaped q P Q).1 +
        evaluate x (.negSucc n+1) (weightedShaped q P Q).2 = 0 := by
  change weighted (si x (.negSucc n)) _ + weighted (si x (.negSucc n+1)) _ = _
  simp only [weightedShaped,weighted_scale,weighted_expand]
  have hl (t : Tuple) : total (si x (.negSucc n)) (start q t) = 0 := by
    apply uniform_negative
    cases t <;> simp [start]
  simp only [hl,weighted_zero,zeroAdd]
  cases n with
  | zero =>
    change -1 * weighted (fun t => total (level x 0) _) Q = 0
    simp only [shifted_level,level,truncSum,Arithmetic.mulZero,zeroMul,weighted_zero]
  | succ n =>
    have hr (t : Tuple) :
        total (si x (.negSucc n)) ((quasiShuffle [q-1] t).map (List.cons 1)) = 0 := by
      apply uniform_negative
      simp
    change -1 * weighted (fun t => total (si x (.negSucc n)) _) Q = 0
    simp only [hr,weighted_zero,Arithmetic.mulZero]

/-- The full weighted form of the strict truncation criterion. The final
identity at the empty truncation is provided separately to cover degree zero. -/
theorem weighted_binary_iff [Neg K] (x : Nat → K) (q : Nat) (c : K) (P Q : FormalSum K)
    (fund : ∀ n, level x n [q] = c * level x (n+1) [1,q-1])
    (cancelLevel : ∀ n a b, level x (n+1) [1,q-1]*a=level x (n+1) [1,q-1]*b → a=b)
    (cancelAdd : ∀ a b d : K, a+b=a+d → b=d) (negOne : (1:K)+(-1)=0) :
    Binary x (weightedShaped q P Q) ↔
      ∀ n, weighted (truncSum x (n+1)) Q = c*weighted (truncSum x (n+1)) P := by
  constructor
  · intro h n
    let a := weighted (truncSum x (n+1)) P
    let b := weighted (truncSum x (n+1)) Q
    let l := level x (n+1) [1,q-1]
    have hy : (c*l)*a + (-1)*(l*b) = 0 := by
      have eq := h (.ofNat n)
      change evaluate x (.ofNat n) _ + evaluate x (.ofNat (n+1)) _ = 0 at eq
      rw [weighted_shaped_at,fund] at eq
      exact eq
    apply cancelLevel n
    change l*b = l*(c*a)
    apply cancelAdd ((-1)*(l*b))
    calc
      _ = l*b + (-1)*(l*b) := Arithmetic.addComm _ _
      _ = 0 := negative_one_times negOne _
      _ = (c*l)*a + (-1)*(l*b) := hy.symm
      _ = _ := by ac_rfl
  · intro h d
    cases d with
    | negSucc n => exact weighted_shaped_negative _ _ _ _ _
    | ofNat n =>
      change evaluate x (.ofNat n) _ + evaluate x (.ofNat (n+1)) _ = 0
      rw [weighted_shaped_at, fund, h n]
      have he (a b : K) : c*a*b = a*(c*b) := by ac_rfl
      rw [he]
      exact negative_one_times negOne _

/-- Lemma 2.1 with arbitrary coefficients in P,Q (no repeated-term encoding
of a coefficient as a natural number). -/
theorem lemma_2_1_weighted [Neg K] (x : Nat → K) (q : Nat) (c : K) (P Q : FormalSum K)
    (nonemptyP : ∀ z ∈ P, z.2 ≠ []) (nonemptyQ : ∀ z ∈ Q, z.2 ≠ [])
    (fund : ∀ n, level x n [q] = c * level x (n+1) [1,q-1])
    (cancelLevel : ∀ n a b, level x (n+1) [1,q-1]*a=level x (n+1) [1,q-1]*b → a=b)
    (cancelAdd : ∀ a b d : K, a+b=a+d → b=d) (negOne : (1:K)+(-1)=0)
    (h : Binary x (weightedShaped q P Q)) :
    Binary x (weightedShaped q (mapTuples (List.cons 1) P) (mapTuples (List.cons 1) Q)) ∧
      Binary x (weightedShaped q (mapTuples incFirst P) (mapTuples incFirst Q)) := by
  have iff_ := fun A B => weighted_binary_iff x q c A B fund cancelLevel cancelAdd negOne
  have hh (n : Nat) : weighted (truncSum x n) Q = c*weighted (truncSum x n) P := by
    cases n with
    | zero => rw [weighted_base _ _ nonemptyQ,weighted_base _ _ nonemptyP,Arithmetic.mulZero]
    | succ k => exact (iff_ P Q).mp h k
  have both := weighted_transforms x c P Q cancelAdd hh
  exact ⟨(iff_ _ _).mpr (fun n => (both (n+1)).1),(iff_ _ _).mpr (fun n => (both (n+1)).2)⟩

end Megaera.Shaped
