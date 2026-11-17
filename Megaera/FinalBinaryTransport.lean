import Megaera.FinalBinarySeries

/-! Transport binary relations to the actual coefficientwise Carlitz sums.
The scalar extension uses constant series and the Cauchy product. -/
namespace Megaera.FinalBinaryTransport
open Megaera.Finite Megaera.Carlitz Megaera.Shaped Megaera.BinaryOperators
open Megaera.FinalBinarySeries
variable {F : Type u} [Arithmetic F] [Neg F]
local instance : Arithmetic (Series F) := seriesArithmetic
local instance : Neg (Series F) := ⟨fun f n => -f n⟩

omit [Neg F] in
def constant (a : F) : Series F := fun n => if n=0 then a else 0

omit [Neg F] in
theorem constant_product (a : F) (f : Series F) (n : Nat) :
    product (constant a) f n=a*f n := by
  unfold product
  rw [List.range_succ_eq_map,total,total_map]
  have zero := Carlitz.total_zero_of_members
    (fun i => constant a (i+1)*f (n-(i+1))) (List.range n) (fun i _ => by simp [constant,zeroMul])
  change a * f n + total (fun i => constant a (i+1)*f (n-(i+1))) _=_
  rw [zero,Arithmetic.addZero]

omit [Neg F] in
theorem power_coeff (f : Series F) (n : Nat) : power f n=seriesPow f n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [power,seriesPow,ih]; exact product_comm _ _

theorem trunc_coeff (q d : Nat) (s : Tuple) :
    truncSum (inverseDenom (F:=F) q) d s = trunc q d s := by
  induction d generalizing s with
  | zero => cases s <;> rfl
  | succ d ih =>
    cases s with
    | nil => rfl
    | cons a t => rw [truncSum,trunc,power_coeff,ih,ih]; rfl

theorem level_coeff (q : Nat) (d : Int) (s : Tuple) :
    si (inverseDenom (F:=F) q) d s = Lift.degree q d s := by
  cases d with
  | ofNat d =>
    cases s with
    | nil => rfl
    | cons a t => simp only [si,level,power_coeff,trunc_coeff,Lift.degree,Lift.exactLevel]; rfl
  | negSucc d => cases d <;> cases s <;> rfl

omit [Neg F] in
def embed (p : FormalSum F) : FormalSum (Series F) := p.map (fun e => (constant e.1,e.2))

omit [Neg F] in
def pair (p : BinaryPair F) : BinaryPair (Series F) := (embed p.1,embed p.2)

theorem evaluate_coeff (q : Nat) (d : Int) (p : FormalSum F) (n : Nat) :
    evaluate (inverseDenom (F:=F) q) d (embed p) n=Lift.valueAt (Lift.degree q d) p n := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    change product (constant e.1) (si _ d e.2) n + evaluate _ d (embed p) n=_+_
    rw [constant_product,level_coeff,ih]; rfl

theorem binary_iff (q : Nat) (p : BinaryPair F) :
    Shaped.Binary (inverseDenom q) (pair p) ↔ Lift.Binary q p := by
  constructor
  · intro h d n
    have eqn := congrFun (h d) n
    change evaluate _ d (embed p.1) n + evaluate _ (d+1) (embed p.2) n=0 at eqn
    simpa only [evaluate_coeff] using eqn
  · intro h d
    funext n
    change evaluate _ d (embed p.1) n + evaluate _ (d+1) (embed p.2) n=0
    simpa only [evaluate_coeff] using h d n

omit [Neg F] in
private theorem embed_expand (f : Tuple → List Tuple) (p : FormalSum F) :
    embed (expand f p)=expand f (embed p) := by
  simp [embed,expand,List.map_flatMap,List.flatMap_map,List.map_map,Function.comp_def]

omit [Neg F] in
theorem pair_B (w : Tuple) (p : BinaryPair F) : pair (bOp w p)=bOp w (pair p) := by
  cases w with
  | nil => rfl
  | cons a w =>
    have ap (x y : FormalSum F) : embed (x++y)=embed x++embed y := List.map_append
    simp only [bOp,pair,ap,embed_expand]; rfl

omit [Neg F] in
theorem pair_C (w : Tuple) (p : BinaryPair F) : pair (cOp w p)=cOp w (pair p) := by
  cases w with
  | nil => rfl
  | cons a w =>
    have ap (x y : FormalSum F) : embed (x++y)=embed x++embed y := List.map_append
    simp only [cOp,pair,ap,embed_expand]

omit [Neg F] in
theorem pair_Bstar (w : Tuple) (p : BinaryPair F) : pair (bStar w p)=bStar w (pair p) := by
  induction w with
  | nil => rfl
  | cons a w ih => rw [bStar,pair_B,ih,bStar]

omit [Neg F] in
private theorem support_pair (p : BinaryPair F) (hp : NonemptySupport p) :
    NonemptySupport (pair p) := by
  constructor <;> intro e he <;> rcases List.mem_map.mp he with ⟨z,hz,rfl⟩
  · exact hp.1 _ hz
  · exact hp.2 _ hz

/-- All three tuple operations preserve binary relations for the concrete
Carlitz levels. Positive homogeneous weight supplies nonempty support. -/
theorem operators_binary (q : Nat) (w : Tuple) (p : BinaryPair F) (hp : NonemptySupport p)
    (h : Lift.Binary q p) :
    Lift.Binary q (bOp w p) ∧ Lift.Binary q (bStar w p) ∧ Lift.Binary q (cOp w p) := by
  have a := (binary_iff q p).mpr h
  have s := support_pair p hp
  refine ⟨(binary_iff q _).mp ?_,(binary_iff q _).mp ?_,(binary_iff q _).mp ?_⟩
  · rw [pair_B]; exact bOp_binary _ w _ s a
  · rw [pair_Bstar]; exact bStar_binary _ w _ s a
  · rw [pair_C]; exact cOp_binary _ w _ s a

end Megaera.FinalBinaryTransport
