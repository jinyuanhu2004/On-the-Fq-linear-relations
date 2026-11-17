import Megaera.Singletons
import Megaera.MainTheorems

/-! Section 4.3. Coordinates are numbered from zero. Only the first
n+1 entries of a coordinate function are read. This allows the same
tuple to be used when eliminating its last entry. -/
namespace Megaera.FourLambda

open Megaera.Finite Megaera.Paper
variable {F : Type u} [Arithmetic F] [Neg F]
local instance : Std.Associative (α := F) (· + ·) := ⟨Arithmetic.addAssoc⟩
local instance : Std.Commutative (α := F) (· + ·) := ⟨Arithmetic.addComm⟩

abbrev Coordinates := Nat → Nat

def bump (d j : Nat) (x : Coordinates) (i : Nat) := x i + (if i = j then d else 0)

private theorem commute (d i j : Nat) (x : Coordinates) :
    bump d i (bump d j x) = bump d j (bump d i x) := by
  funext k; simp only [bump]; omega

/-- Sum after increasing, in turn, each of the entries start,...,start+k-1. -/
def shifts (d start : Nat) (f : Coordinates → F) : Nat → Coordinates → F
  | 0, _ => 0
  | k+1, x => shifts d start f k x + f (bump d (start+k) x)

omit [Neg F] in
private theorem shifts_congr (d s k : Nat) (f g : Coordinates → F) (x : Coordinates)
    (h : ∀ j, s ≤ j → j < s+k → f (bump d j x) = g (bump d j x)) :
    shifts d s f k x = shifts d s g k x := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [shifts]; rw [ih (fun j hj hk => h j hj (by omega)),h _ (by omega) (by omega)]

omit [Neg F] in
private theorem shifts_zero (d s k : Nat) : shifts d s (fun _ => (0:F)) k = fun _ => 0 := by
  funext x; induction k with
  | zero => rfl
  | succ k ih => simp only [shifts,ih,Arithmetic.addZero]

omit [Neg F] in
private theorem shifts_add (d s k : Nat) (f g : Coordinates → F) (x : Coordinates) :
    shifts d s (fun y => f y + g y) k x = shifts d s f k x + shifts d s g k x := by
  induction k with
  | zero => exact (Arithmetic.addZero _).symm
  | succ k ih => simp only [shifts,ih]; ac_rfl

omit [Neg F] in
private theorem shifts_bump (d s k j : Nat) (f : Coordinates → F) (x : Coordinates) :
    shifts d s (fun y => f (bump d j y)) k x = shifts d s f k (bump d j x) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [shifts,ih]; rw [commute d j (s+k)]

omit [Neg F] in
private theorem shifts_comm (d s k m : Nat) (f : Coordinates → F) (x : Coordinates) :
    shifts d s (shifts d 0 f m) k x = shifts d 0 (shifts d s f k) m x := by
  induction m with
  | zero => exact congrFun (shifts_zero d s k) x
  | succ m ih =>
    change shifts d s (fun y => shifts d 0 f m y + f (bump d (0+m) y)) k x = _
    rw [shifts_add,ih,shifts_bump]; rfl

private theorem shifts_neg (field : ConstantField F q) (d s k : Nat) (f : Coordinates → F)
    (x : Coordinates) :
    shifts d s (fun y => -(f y)) k x = -(shifts d s f k x) := by
  induction k with
  | zero => exact (Singletons.nz field.add_neg).symm
  | succ k ih => rw [shifts,shifts,ih,Singletons.neg_add field.add_neg]

/-- Extend a function of n earlier entries to one more entry. Each
overflow transfers d to one of the earlier positions with a minus sign. -/
def extend (d : Nat) (hd : 0 < d) (n cap v : Nat) (f : Coordinates → F)
    (a : Nat) : Coordinates → F :=
  if cap < a then fun x => -(shifts d 0 (extend d hd n cap v f (a-d)) n x)
  else if a = v then f else fun _ => 0
termination_by a
decreasing_by omega

/-- Values for the ordinary (nonfinal) entries, all bounded by q on the
initial rectangle. -/
def initial (q : Nat) (hq : 1 < q) (v : Coordinates) : Nat → Coordinates → F
  | 0, _ => 1
  | n+1, x => extend (q-1) (by omega) n q (v n) (initial q hq v n) (x n) x

/-- λ on n ordinary entries and a last entry of bound and residue b. -/
def lambda (q : Nat) (hq : 1 < q) (n b : Nat) (v x : Coordinates) : F :=
  extend (q-1) (by omega) n b b (initial q hq v n) (x n) x

/-- Dependence on the first n coordinates. -/
private def Uses (n : Nat) (f : Coordinates → F) : Prop :=
  ∀ x y, (∀ j, j < n → x j = y j) → f x = f y

omit [Neg F] in
private theorem shifts_uses {n : Nat} {f : Coordinates → F} (h : Uses n f) (d s k : Nat) :
    Uses n (shifts d s f k) := by
  intro x y he
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [shifts,shifts,ih]
    apply congrArg (_ + ·)
    apply h
    intro j hj
    simp only [bump,he j hj]

private theorem extend_uses (d hd n cap v) (f : Coordinates → F) (a : Nat)
    (h : Uses n f) : Uses n (extend d hd n cap v f a) := by
  rw [extend]
  split
  · intro x y he
    exact congrArg Neg.neg (shifts_uses (extend_uses d hd n cap v f (a-d) h) d 0 n x y he)
  · split
    · exact h
    · intro _ _ _; rfl
termination_by a
decreasing_by omega

private theorem initial_uses (q hq v n) : Uses n (initial (F:=F) q hq v n) := by
  induction n with
  | zero => intro _ _ _; rfl
  | succ n ih =>
    intro x y he
    simp only [initial,he n (by omega)]
    apply extend_uses _ _ _ _ _ _ _ ih
    exact fun j hj => he j (by omega)

private theorem across (d hd n cap v) (f : Coordinates → F) (x : Coordinates) {k : Nat}
    (hk : k ≤ n) :
    shifts d 0 (fun y => extend d hd n cap v f (y n) y) k x =
      shifts d 0 (extend d hd n cap v f (x n)) k x := by
  apply shifts_congr
  intro j _ hj
  simp [bump,show n≠j by omega]

private theorem last_cancel (field : ConstantField F q) (n cap v : Nat)
    (f : Coordinates → F) (hf : Uses n f) (x : Coordinates) (ha : cap < x n + (q-1)) :
    shifts (q-1) 0 (fun y => extend (q-1) (by have := field.two_le; omega) n cap v f (y n) y)
      (n+1) x = 0 := by
  have hd : 0 < q-1 := by have := field.two_le; omega
  simp only [shifts,Nat.zero_add,across _ _ n cap v f x (Nat.le_refl _)]
  have same (a : Nat) : extend (q-1) hd n cap v f a (bump (q-1) n x) =
      extend (q-1) hd n cap v f a x := by
    apply extend_uses _ _ _ _ _ _ _ hf
    intro j hj; simp [bump,show j≠n by omega]
  rw [same]
  simp only [bump,ite_true]
  conv => lhs; rhs; rw [extend, if_pos ha, Nat.add_sub_cancel]
  apply field.add_neg

/-- The sum over all n+1 single-coordinate shifts vanishes. A positive
last entry suffices whenever 1 ≤ b ≤ q−1, hence in particular on the
specified residue class. -/
theorem full_sum (field : ConstantField F q) (n b : Nat) (v x : Coordinates)
    (hb : b ≤ q-1) (hx : 0 < x n) :
    shifts (q-1) 0 (lambda (F:=F) q field.two_le n b v) (n+1) x = 0 :=
  last_cancel field n b b _ (initial_uses q field.two_le v n) x (by omega)

private theorem prefix_extend (field : ConstantField F q) (d : Nat) (hd : 0 < d) (n cap v i : Nat)
    (f : Coordinates → F) (h : ∀ x, 1 < x i → shifts d 0 f (i+1) x = 0) (a : Nat) :
    ∀ x, 1 < x i → shifts d 0 (extend d hd n cap v f a) (i+1) x = 0 := by
  intro x hx
  rw [extend]
  split
  · rw [shifts_neg field,shifts_comm]
    have eqn : shifts d 0 (shifts d 0 (extend d (by omega) n cap v f (a-d)) (i+1)) n x = 0 := by
      rw [← congrFun (shifts_zero (F:=F) d 0 n) x]
      apply shifts_congr
      intro j _ _
      apply prefix_extend field d hd n cap v i f h (a-d)
      simp only [bump]; omega
    rw [eqn,Singletons.nz field.add_neg]
  · split
    · exact h x hx
    · exact congrFun (shifts_zero ..) x
termination_by a
decreasing_by omega

private theorem initial_prefix (field : ConstantField F q) (v : Coordinates) (n i : Nat)
    (hi : i < n) (x : Coordinates) (hx : 1 < x i) :
    shifts (q-1) 0 (initial (F:=F) q field.two_le v n) (i+1) x = 0 := by
  induction n generalizing x with
  | zero => omega
  | succ n ih =>
    by_cases eqn : i=n
    · subst i
      exact last_cancel field n q (v n) _ (initial_uses q field.two_le v n) x (by have := field.two_le; omega)
    · change shifts (q-1) 0 (fun y => extend (F:=F) _ _ _ _ _ _ _ y) _ _ = _
      rw [across _ _ n q (v n) _ x (by omega)]
      apply prefix_extend field
      · intro y hy; exact ih (by omega) y hy
      · exact hx

/-- The sum through the i-th coordinate vanishes when that ordinary
entry exceeds one. Indices start at zero. -/
theorem prefix_sum (field : ConstantField F q) (n b i : Nat) (v x : Coordinates)
    (hi : i < n) (hx : 1 < x i) :
    shifts (q-1) 0 (lambda (F:=F) q field.two_le n b v) (i+1) x = 0 := by
  unfold lambda
  rw [across _ _ n b b _ x (by omega)]
  apply prefix_extend field
  · intro y hy; exact initial_prefix field v n i hi y hy
  · exact hx

omit [Neg F] in
private theorem split_shifts (d k r : Nat) (f : Coordinates → F) (x : Coordinates) :
    shifts d 0 f (k+r) x = shifts d 0 f k x + shifts d k f r x := by
  induction r with
  | zero => exact (Arithmetic.addZero _).symm
  | succ r ih =>
    change shifts d 0 f (k+r) x + f (bump d (0+(k+r)) x) = _
    rw [ih,shifts,Nat.zero_add,Arithmetic.addAssoc]

/-- The sum over coordinates strictly after i vanishes as well. -/
theorem suffix_sum (field : ConstantField F q) (n b i : Nat) (v x : Coordinates)
    (hb : b ≤ q-1) (hl : 0 < x n) (hi : i < n) (hx : 1 < x i) :
    shifts (q-1) (i+1) (lambda (F:=F) q field.two_le n b v) (n-i) x = 0 := by
  have sum := full_sum field n b v x hb hl
  rw [show n+1=i+1+(n-i) by omega,split_shifts,prefix_sum field n b i v x hi hx,zeroAdd] at sum
  exact sum

private theorem initial_base (q hq v n) (x : Coordinates) (bounded : ∀ j < n, x j ≤ q) :
    initial (F:=F) q hq v n x = if ∀ j : Fin n, x j = v j then 1 else 0 := by
  induction n with
  | zero => rw [if_pos (fun j => Fin.elim0 j)]; rfl
  | succ n ih =>
    rw [initial, extend, if_neg (Nat.not_lt.mpr (bounded n (by omega)))]
    have inner := ih (fun j hj => bounded j (by omega))
    by_cases e : x n = v n
    · rw [if_pos e,inner]
      have h : (∀ j : Fin n, x j = v j) ↔ (∀ j : Fin (n+1), x j = v j) := by
        constructor
        · intro h j
          by_cases k : j.val = n
          · simpa only [k] using e
          · exact h ⟨j.val,by omega⟩
        · intro h j; exact h ⟨j.val,by omega⟩
      simp only [h]
    · have h : ¬(∀ j : Fin (n+1), x j = v j) := fun t => e (t ⟨n,by omega⟩)
      rw [if_neg e,if_neg h]

/-- The initial values on the bounded rectangle are the Kronecker delta. -/
theorem bounded_value (field : ConstantField F q) (n b : Nat) (v x : Coordinates)
    (bounded : ∀ j < n, x j ≤ q) (last : x n = b) :
    lambda (F:=F) q field.two_le n b v x = if ∀ j : Fin n, x j=v j then 1 else 0 := by
  unfold lambda
  rw [last, extend,if_neg (Nat.lt_irrefl _),if_pos rfl]
  exact initial_base q field.two_le v n x bounded

/-- The last ordinary target entry is 1. Reducing an entry greater than
q by q−1 keeps it at least 2, so it can never match that target. -/
private theorem avoid_one (field : ConstantField F q) (n a : Nat) (f : Coordinates → F)
    (ha : 1 < a) : extend (q-1) (by have := field.two_le; omega) n q 1 f a = fun _ => 0 := by
  rw [extend]
  split
  · rename_i he
    rw [avoid_one field n (a-(q-1)) f (by omega),shifts_zero]
    funext x; exact Singletons.nz field.add_neg
  · rw [if_neg (show a≠1 by omega)]
termination_by a
decreasing_by have := field.two_le; omega

theorem terminal_zero (field : ConstantField F q) (n b : Nat) (v x : Coordinates)
    (target : v n = 1) (hx : 1 < x n) (last : x (n+1)=b) :
    lambda (F:=F) q field.two_le (n+1) b v x = 0 := by
  unfold lambda; rw [last,extend,if_neg (Nat.lt_irrefl _),if_pos rfl]
  simp only [initial,target]
  rw [avoid_one field n (x n) _ hx]

/-- Read an ordinary manuscript tuple by its zero-based coordinates. -/
def entries (t : Tuple) (i : Nat) : Nat := t[i]?.getD 0

/-- Raising the j-th entry in a manuscript tuple realizes the shift
used inside λ. The condition on j prevents changing a nonexistent entry. -/
theorem entries_modify (x : Tuple) (d j : Nat) (hj : j < x.length) :
    entries (x.modify j (· + d)) = bump d j (entries x) := by
  funext i
  by_cases he : i=j
  · subst i; simp [entries,bump,List.getElem?_eq_getElem hj]
  · simp [entries,bump,he,List.getElem?_modify_ne _ _ (Ne.symm he)]

omit [Neg F] in
/-- Actual tuple sum over the consecutive positions start,...,start+k−1. -/
theorem total_modified (d start k : Nat) (f : Coordinates → F) (x : Tuple)
    (hk : start+k ≤ x.length) :
    total (fun j => f (entries (x.modify j (·+d)))) (List.range' start k) =
      shifts d start f k (entries x) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range'_1_concat,total_append',ih (by omega)]
    simp only [total,Arithmetic.addZero,shifts,entries_modify x d (start+k) (by omega)]

/-- Section 4.3's three sums, all evaluated on a single list of length n+1. -/
theorem tuple_cancellations (field : ConstantField F q) (n b i : Nat) (v x : Tuple)
    (len : x.length=n+1) (hb : b ≤ q-1) (hl : 0 < entries x n)
    (hi : i < n) (hx : 1 < entries x i) :
    let value := fun j => lambda (F:=F) q field.two_le n b (entries v)
      (entries (x.modify j (·+(q-1))))
    total value (List.range' 0 (n+1)) = 0 ∧
    total value (List.range' 0 (i+1)) = 0 ∧
    total value (List.range' (i+1) (n-i)) = 0 := by
  dsimp only
  rw [total_modified _ 0 (n+1) _ _ (by omega),total_modified _ 0 (i+1) _ _ (by omega),
      total_modified _ (i+1) (n-i) _ _ (by omega)]
  exact ⟨full_sum field _ _ _ _ hb hl, prefix_sum field _ _ _ _ _ hi hx,
    suffix_sum field _ _ _ _ _ hb hl hi hx⟩

/-- Entries outside the prescribed residue class already have λ-value zero. -/
private theorem extend_wrong_residue (d : Nat) (hd : 0 < d) (n b a : Nat)
    (field : ConstantField F q) (f : Coordinates → F) (hb : 0<b) (h : a % d ≠ b % d) :
    extend d hd n b b f a = fun _ => 0 := by
  rw [extend]
  split
  · by_cases small : a < d
    · have z : a-d=0 := by omega
      rw [z,extend,if_neg (by omega : ¬ b < 0), if_neg (by omega : 0≠b),shifts_zero]
      funext x; exact Singletons.nz field.add_neg
    · have hm : (a-d)%d=a%d := by
        have he : a=(a-d)+d := by omega
        conv => rhs; rw [he,Nat.add_mod_right]
      rw [extend_wrong_residue d hd n b (a-d) field f hb (by rwa [hm]),shifts_zero]
      funext x; exact Singletons.nz field.add_neg
  · have ne : a≠b := fun he => h (congrArg (·%d) he)
    rw [if_neg ne]
termination_by a
decreasing_by omega

theorem wrong_residue (field : ConstantField F q) (n b : Nat) (v x : Coordinates)
    (hb : 0<b) (h : x n % (q-1) ≠ b % (q-1)) :
    lambda (F:=F) q field.two_le n b v x = 0 := by
  unfold lambda; rw [extend_wrong_residue _ _ _ _ _ field _ hb h]

end Megaera.FourLambda
