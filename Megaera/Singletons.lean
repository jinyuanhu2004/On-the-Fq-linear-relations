import Megaera.Carlitz
import Megaera.PrimitiveRows

/-! Lemma 2.14(i), with H+ in its tuple-generator description (2.9).
The retraction below sends a single tuple (a,s), a>0, to
(-1)^(a-1) times (1,...,1,s), with a-1 leading ones. For any given
output coordinate there are only finitely many possible inputs. -/
namespace Megaera.Singletons
open Megaera.Finite Megaera.Carlitz

variable {F : Type u} [Arithmetic F] [Neg F]

omit [Neg F] in
private theorem za (x : F) : 0 + x = x := by rw [Arithmetic.addComm, Arithmetic.addZero]

private theorem unique_neg (inv : ∀ x : F, x + -x = 0) (a b : F) (h : b+a=0) :
    b = -a := by
  calc
    b = b + (a + (-a)) := by rw [inv, Arithmetic.addZero]
    _ = (b+a) + (-a) := (Arithmetic.addAssoc ..).symm
    _ = -a := by rw [h, za]

theorem nz (inv : ∀ x : F, x + -x = 0) : -(0:F) = 0 := by
  exact (unique_neg inv 0 0 (za _)).symm

theorem neg_add (inv : ∀ x : F, x + -x = 0) (a b : F) :
    -(a+b) = -a + -b := by
  symm
  apply unique_neg inv
  letI : Std.Associative (α := F) (· + ·) := ⟨Arithmetic.addAssoc⟩
  letI : Std.Commutative (α := F) (· + ·) := ⟨Arithmetic.addComm⟩
  calc
    -a + -b + (a + b) = (a + -a) + (b + -b) := by ac_rfl
    _ = 0 := by rw [inv, inv, za]

/-- Prepending the entry a as an operator on coefficient vectors. -/
def head (a : Nat) (v : Tuple → F) : Tuple → F
  | [] => 0
  | b::s => if a = b then v s else 0

/-- The generator (2.9) with empty outer prefix and tail vector v. The
parameter a represents the final entry a+1 of the marked left tuple. -/
def root (a : Nat) (v : Tuple → F) (x : Tuple) : F :=
  head (a+2) v x + head (a+1) (head 1 v) x

/-- Span in (2.9). Arbitrary scalar coefficients are put on the
generators, and prepending any positive integer supplies the outer
tuple. Its generators use the actual singleton quasi-shuffle. -/
inductive HPlus (q : Nat) : (Tuple → F) → Prop
  | zero : HPlus q (fun _ => 0)
  | add {p r} : HPlus q p → HPlus q r → HPlus q (fun x => p x + r x)
  | neg {p} : HPlus q p → HPlus q (fun x => -p x)
  | cons (a : Nat) {p} : HPlus q p → HPlus q (head (a+1) p)
  | gen (a : Nat) (t : Tuple) (k : F) (hv : Valid t) :
      HPlus q (root a (coordinates (withCoeff k (quasiShuffle [q-1] t))))

/-- Coefficient at output t in the signed retraction; n is the index
of the next input head. Only leading ones in t can contribute further. -/
def restore (p : Tuple → F) (n : Nat) : Tuple → F
  | [] => p [n]
  | b :: t => if b = 1 then p (n :: b :: t) + -(restore p (n+1) t)
      else p (n::b::t)

theorem restore_zero (inv : ∀ x : F, x + -x = 0) (n : Nat) (s : Tuple) :
    restore (fun _ => (0:F)) n s = 0 := by
  induction s generalizing n with
  | nil => rfl
  | cons b t ih => simp [restore, ih, nz inv, za]

theorem restore_add (inv : ∀ x : F, x + -x = 0)
    (p r : Tuple → F) (n : Nat) (s : Tuple) :
    restore (fun x => p x + r x) n s = restore p n s + restore r n s := by
  induction s generalizing n with
  | nil => rfl
  | cons b t ih =>
    by_cases h : b=1
    · letI : Std.Associative (α := F) (· + ·) := ⟨Arithmetic.addAssoc⟩
      letI : Std.Commutative (α := F) (· + ·) := ⟨Arithmetic.addComm⟩
      simp only [restore, h, if_pos, ih, neg_add inv]
      ac_rfl
    · simp [restore, h]

theorem restore_neg (inv : ∀ x : F, x + -x = 0)
    (p : Tuple → F) (n : Nat) (s : Tuple) :
    restore (fun x => -p x) n s = -(restore p n s) := by
  apply unique_neg inv
  rw [← restore_add inv]
  have hz : (fun x => -p x + p x) = fun _ => (0:F) := by
    funext x
    rw [Arithmetic.addComm, inv]
  rw [hz, restore_zero inv]

theorem restore_above (inv : ∀ x : F, x + -x = 0)
    (a n : Nat) (v : Tuple → F) (lt : a<n) (s : Tuple) :
    restore (head a v) n s = 0 := by
  induction s generalizing n with
  | nil => simp [restore, head, Nat.ne_of_lt lt]
  | cons b t ih =>
    simp [restore, head, Nat.ne_of_lt lt, ih (n+1) (by omega), nz inv, za]

def ones : Nat → (Tuple → F) → Tuple → F
  | 0,v => v
  | k+1,v => fun x => -(head 1 (ones k v) x)

theorem restore_head (inv : ∀ x : F, x + -x = 0)
    (v : Tuple → F) (n k : Nat) :
    restore (head (n+k) v) n = ones k v := by
  induction k generalizing n with
  | zero =>
    funext t
    cases t with
    | nil => simp [restore, head, ones]
    | cons a t =>
      simp [restore, head, ones, restore_above inv n (n+1) v (by omega),
        nz inv, Arithmetic.addZero]
  | succ k ih =>
    have h := ih (n+1)
    have hne : n+(k+1) ≠ n := by omega
    have he : (n+1)+k = n+(k+1) := by omega
    rw [he] at h
    funext t
    cases t with
    | nil => simp [restore, head, ones, hne, nz inv]
    | cons a t =>
      by_cases ha : a=1
      · subst a
        simp only [restore, if_pos, head, hne, if_false, ones, za, h]
      · simp [restore, ha, head, hne, Ne.symm ha, ones, nz inv]

theorem ones_head (inv : ∀ x : F, x + -x = 0) (k : Nat) (v : Tuple → F) :
    ones k (head 1 v) = head 1 (ones k v) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext t
    cases t with
    | nil => simp [ones, head, nz inv]
    | cons a t => by_cases h : a=1 <;> simp [ones, head, h, ih, nz inv, Ne.symm]

private theorem restore_root (inv : ∀ x : F, x + -x = 0) (a : Nat) (v : Tuple → F) :
    restore (root a v) 1 = fun _ => 0 := by
  funext t
  change restore (fun x => head (a+2) v x + head (a+1) (head 1 v) x) 1 t = 0
  rw [restore_add inv]
  have h₂ : restore (head (a+2) v) 1 = ones (a+1) v := by
    rw [show a+2 = 1+(a+1) by omega, restore_head inv]
  have h₁ : restore (head (a+1) (head 1 v)) 1 = ones a (head 1 v) := by
    rw [show a+1 = 1+a by omega, restore_head inv]
  rw [h₂, h₁]
  change -(head 1 (ones a v) t) + ones a (head 1 v) t = 0
  rw [ones_head inv, Arithmetic.addComm, inv]

theorem ones_inside (q k : Nat) (v : Tuple → F) (hv : HPlus q v) :
    HPlus q (ones k v) := by
  induction k with
  | zero => exact hv
  | succ k ih => exact HPlus.neg (HPlus.cons 0 ih)

theorem restore_inside (inv : ∀ x : F, x + -x = 0)
    (q : Nat) (p : Tuple → F) (hp : HPlus q p) : HPlus q (restore p 1) := by
  induction hp with
  | zero =>
    rw [show (restore (fun _ => (0:F)) 1) = fun _ => 0 from funext (restore_zero inv 1)]
    exact HPlus.zero
  | @add p r hp hr ih jh =>
    rw [funext (restore_add inv p r 1)]
    exact HPlus.add ih jh
  | @neg p hp ih =>
    rw [funext (restore_neg inv p 1)]
    exact HPlus.neg ih
  | cons a hp ih =>
    rw [show a+1=1+a by omega, restore_head inv]
    exact ones_inside q a _ hp
  | gen a t k hv =>
    rw [restore_root inv]
    exact HPlus.zero

/-- Lemma 2.14(i). Valid over every coefficient field with the finite
sum arithmetic laws. The reflection direction uses a left inverse. -/
theorem prepend_one_iff (inv : ∀ x : F, x + -x = 0) (q : Nat) (p : Tuple → F) :
    HPlus q (head 1 p) ↔ HPlus q p := by
  constructor
  · intro hp
    have h := restore_inside inv _ _ hp
    rw [show (1:Nat) = 1+0 from rfl, restore_head inv (n:=1) (k:=0)] at h
    exact h
  · exact HPlus.cons 0

/-- The same space defined directly from H(q,h,t) with h nonempty.
Scalar multipliers on rows and finite sums give its linear span. -/
inductive RowSpan (q : Nat) : (Tuple → F) → Prop
  | zero : RowSpan q (fun _ => 0)
  | add {p r} : RowSpan q p → RowSpan q r → RowSpan q (fun x => p x + r x)
  | neg {p} : RowSpan q p → RowSpan q (fun x => -p x)
  | row (a : Nat) (h t : Tuple) (k : F) (hh : Valid (a::h)) (ht : Valid t) :
      RowSpan q (coordinates (withCoeff k (H q (a::h) t)))

omit [Neg F] in
theorem head_add (a : Nat) (p r : Tuple → F) :
    head a (fun x => p x + r x) = (fun x => head a p x + head a r x) := by
  funext x
  cases x with
  | nil => simp [head, za]
  | cons b x => by_cases h : a=b <;> simp [head,h,za]

theorem head_neg (inv : ∀ x : F, x + -x = 0) (a : Nat) (p : Tuple → F) :
    head a (fun x => -p x) = fun x => -(head a p x) := by
  funext x
  cases x with
  | nil => simp [head, nz inv]
  | cons b x => by_cases h : a=b <;> simp [head,h,nz inv]

omit [Neg F] in
private theorem coeff_nil (k : F) : coordinates (withCoeff k []) = fun _ => 0 := rfl

omit [Neg F] in
private theorem coeff_cons (k : F) (x : Tuple) (xs : List Tuple) (t : Tuple) :
    coordinates (withCoeff k (x::xs)) t =
      (if x=t then k else 0) + coordinates (withCoeff k xs) t := rfl

omit [Neg F] in
theorem head_zero (a : Nat) :
    head a (fun _ => (0:F)) = fun _ => (0:F) := by
  funext s
  cases s <;> simp [head]

omit [Neg F] in
theorem coeff_append (k : F) (l m : List Tuple) (x : Tuple) :
    coordinates (withCoeff k (l++m)) x =
      coordinates (withCoeff k l) x + coordinates (withCoeff k m) x := by
  induction l with
  | nil => exact (za _).symm
  | cons z l ih => simp only [List.cons_append, coeff_cons, ih, Arithmetic.addAssoc]

omit [Neg F] in
theorem coeff_prepend (a : Nat) (k : F) (l : List Tuple) :
    coordinates (withCoeff k (l.map (List.cons a))) =
      head a (coordinates (withCoeff k l)) := by
  induction l with
  | nil => simp only [List.map_nil, coeff_nil, head_zero]
  | cons z l ih =>
    funext x
    cases x with
    | nil => simp [coeff_cons, ih, head, za]
    | cons b x =>
      by_cases he : a=b
      · subst b
        simp [coeff_cons, ih, head]
      · simp [coeff_cons, ih, head, he, za]

omit [Neg F] in
private theorem root_eq_row (q a : Nat) (t : Tuple) (k : F) :
    root a (coordinates (withCoeff k (quasiShuffle [q-1] t))) =
      coordinates (withCoeff k (H q [a+1] t)) := by
  let ts := quasiShuffle [q-1] t
  have hx : H q [a+1] t = ts.map (List.cons (a+2)) ++
      (ts.map (List.cons 1)).map (List.cons (a+1)) := by
    simp [ts, H, concatenate, endings, incLast, List.map_map, Function.comp_def]
  funext x
  rw [hx, coeff_append, coeff_prepend, coeff_prepend, coeff_prepend]
  rfl

omit [Neg F] in
private theorem eq_prefixed_row (q a b : Nat) (s t : Tuple) (k : F) :
    coordinates (withCoeff k (H q (a::b::s) t)) =
      head a (coordinates (withCoeff k (H q (b::s) t))) := by
  change coordinates (withCoeff k (H q ([a] ++ b::s) t)) = _
  rw [Megaera.PrimitiveRows.H_prepend_nonempty q [a] b s t, ← coeff_prepend]
  rfl

private theorem valid_prepend (a : Nat) (s : Tuple) (hs : Valid s) : Valid ((a+1)::s) := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · omega
  · exact hs _ hx

private theorem rowSpan_head (inv : ∀ x : F, x + -x = 0) (q a : Nat) (p : Tuple → F)
    (hp : RowSpan q p) : RowSpan q (head (a+1) p) := by
  induction hp with
  | zero => rw [head_zero]; exact RowSpan.zero
  | add hp hr ih jh => rw [head_add]; exact RowSpan.add ih jh
  | neg hp ih => rw [head_neg inv]; exact RowSpan.neg ih
  | row b h t k hh ht =>
    rw [← eq_prefixed_row]
    exact RowSpan.row _ _ _ _ (valid_prepend _ _ hh) ht

private theorem row_inside (q : Nat) (t : Tuple) (ht : Valid t) (k : F) (a : Nat)
    (h : Tuple) (hh : Valid (a::h)) : HPlus q (coordinates (withCoeff k (H q (a::h) t))) := by
  induction h generalizing a with
  | nil =>
    cases a with
    | zero => have hbad := hh 0 (by simp); omega
    | succ a => rw [←root_eq_row]; exact HPlus.gen _ _ _ ht
  | cons b h ih =>
    cases a with
    | zero => have hbad := hh 0 (by simp); omega
    | succ a =>
      rw [eq_prefixed_row]
      exact HPlus.cons a (ih b (fun x hx => hh x (List.mem_cons_of_mem _ hx)))

/-- Equation (2.9), on coefficient vectors. -/
theorem rowSpan_iff (inv : ∀ x : F, x + -x = 0) (q : Nat) (p : Tuple → F) :
    RowSpan q p ↔ HPlus q p := by
  constructor
  · intro h
    induction h with
    | zero => exact HPlus.zero
    | add hp hr ih jh => exact HPlus.add ih jh
    | neg hp ih => exact HPlus.neg ih
    | row a h t k hh ht => exact row_inside _ _ ht _ _ _ hh
  · intro h
    induction h with
    | zero => exact RowSpan.zero
    | add hp hr ih jh => exact RowSpan.add ih jh
    | neg hp ih => exact RowSpan.neg ih
    | cons a hp ih => exact rowSpan_head inv _ _ _ ih
    | gen a t k ht =>
      rw [root_eq_row]
      exact RowSpan.row _ _ _ _ (valid_prepend _ _ (by simp [Valid])) ht

/-- Prefix-one reflection for the span of the actual positive-prefix
row images of H. This is Lemma 2.14(i) in its original formulation. -/
theorem rowSpan_prepend_one_iff (inv : ∀ x : F, x + -x = 0) (q : Nat) (p : Tuple → F) :
    RowSpan q (head 1 p) ↔ RowSpan q p := by
  rw [rowSpan_iff inv, rowSpan_iff inv, prepend_one_iff inv]

end Megaera.Singletons
