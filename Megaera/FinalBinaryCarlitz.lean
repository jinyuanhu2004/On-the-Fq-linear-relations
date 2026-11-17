import Megaera.FinalBinaryLaurent

/-! The Laurent representatives of θ, the Carlitz denominator factors,
and the finite levels, for the actual coefficients used by Lift.Binary. -/
namespace Megaera.FinalBinaryCarlitz
open Megaera.Carlitz Megaera.Finite Megaera.Paper Megaera.FinalBinaryLaurent
open Megaera.FinalBinarySeries Megaera.FinalBinaryTransport Megaera.Shaped
variable {F : Type u} [Arithmetic F] [Neg F]
local instance : Arithmetic (Series F) := seriesArithmetic
local instance : Neg (Series F) := ⟨fun f n => -f n⟩
local instance : Std.Associative (α:=Laurent F) (·*·) := ⟨Arithmetic.mulAssoc⟩
local instance : Std.Commutative (α:=Laurent F) (·*·) := ⟨Arithmetic.mulComm⟩
local instance : Std.Associative (α:=Laurent F) (·+·) := ⟨Arithmetic.addAssoc⟩
local instance : Std.Commutative (α:=Laurent F) (·+·) := ⟨Arithmetic.addComm⟩

def theta : Laurent F := mk 1 1
def inverse (q n : Nat) : Laurent F := mk 0 (inverseDenom q n)

omit [Neg F] in
theorem theta_pow (n : Nat) : power (theta (F:=F)) n=mk n 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [power,ih]; change mk (n+1) (1*(1:Series F))=_; rw [Arithmetic.mulOne]

private theorem sum_neg (field : ConstantField F q) (a b : Laurent F) :
    a + -b + b=a := by rw [Arithmetic.addAssoc,Arithmetic.addComm (-b),negative_sum field,Arithmetic.addZero]

theorem add_cancel (field : ConstantField F q) (a b c : Laurent F) (h : a+b=a+c) : b=c := by
  have eq := congrArg (fun x => -a+x) h
  simpa only [←Arithmetic.addAssoc,show (-a)+a=0 by rw [Arithmetic.addComm,negative_sum field],zeroAdd] using eq

/-- Clearing powers of T in (θ−θ^e)/l_(d+1)=1/l_d recovers exactly the
coefficient identity proved for the recursively constructed inverse. -/
theorem factor_inverse (field : ConstantField F q) (d : Nat) :
    (theta + -power theta (q^(d+1))) * inverse (F:=F) q (d+1)=inverse q d := by
  let e := q^(d+1)
  let f := inverseDenom (F:=F) q d
  let g := inverseDenom (F:=F) q (d+1)
  have eq : shift e f=shift (e-1) g+(-g) := by
    funext n
    have h := inverseDenom_factor field d n
    change g n+shift e f n=shift (e-1) g n at h
    change shift e f n=shift (e-1) g n+(-g n)
    rw [←h,Arithmetic.addComm (g n),Arithmetic.addAssoc,field.add_neg,Arithmetic.addZero]
  have ez : 1≤e := Nat.pow_pos (Nat.lt_of_lt_of_le (by decide) field.two_le)
  let v : Series F := power T (e-1)+(- (1 : Series F))
  have repr : theta (F:=F) + -power theta e=mk e v := by
    rw [theta_pow,neg_mk field]
    change mk (1+e) (power T e*1+power T 1*(-(1 : Series F))) = mk e v
    apply Quotient.sound (s:=rel)
    change power T e*(power T e*1+power T 1*(-(1:Series F)))=power T (1+e)*v
    rw [show power (T : Series F) e*1=power T e by exact Arithmetic.mulOne _,power_add]
    simp only [v,Arithmetic.distrib]
    have one : power (T : Series F) e=power T 1*power T (e-1) := by rw [←power_add,show 1+(e-1)=e by omega]
    letI : Std.Associative (α:=Series F) (·*·) := ⟨Arithmetic.mulAssoc⟩
    letI : Std.Commutative (α:=Series F) (·*·) := ⟨Arithmetic.mulComm⟩
    congr 1
    · conv => lhs; rhs; rw [one]
      simp only [Arithmetic.mulAssoc]; rw [←Arithmetic.mulAssoc,Arithmetic.mulComm (power T e) (power T 1),Arithmetic.mulAssoc]
    · ac_rfl
  change (theta+-power theta e)*mk 0 g=mk 0 f
  rw [repr,mk_mul]
  apply Quotient.sound (s:=rel)
  change power T 0*(v*g)=power T (e+0)*f
  rw [power,oneMul,Nat.add_zero,powT_mul,eq]
  change (power T (e-1)+(-(1:Series F)))*g=_
  rw [Arithmetic.mulComm _ g,Arithmetic.distrib,Arithmetic.mulComm g (power T (e-1)),Arithmetic.mulComm g (-(1:Series F)),powT_mul]
  have neg1 : (-(1:Series F))=constant (-(1:F)) := by
    funext n; change -(if n=0 then (1:F) else 0)=if n=0 then -1 else 0
    by_cases h:n=0 <;> simp [h,Singletons.nz field.add_neg]
  rw [neg1]
  funext n; change _ + product (constant (-1)) g n=_ + (-g n)
  rw [constant_product,neg_mul field,oneMul]

omit [Neg F] in
theorem embed_power (s : Series F) (k : Nat) : power (mk 0 s) k=mk 0 (power s k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [power,power,ih,←embed_mul]

theorem inverse_trunc (q d : Nat) (s : Tuple) :
    truncSum (inverse (F:=F) q) d s=mk 0 (trunc q d s) := by
  induction d generalizing s with
  | zero => cases s <;> rfl
  | succ d ih =>
    cases s with
    | nil => rfl
    | cons a t =>
      rw [truncSum,ih,ih,trunc,inverse,embed_power,←embed_mul,←embed_add,power_coeff]; rfl

theorem inverse_degree (q : Nat) (d : Int) (s : Tuple) :
    si (inverse (F:=F) q) d s=mk 0 (Lift.degree q d s) := by
  cases d with
  | ofNat d =>
    cases s with
    | nil => rfl
    | cons a t =>
      rw [si,level,inverse_trunc,inverse,embed_power,←embed_mul,power_coeff]; rfl
  | negSucc d => cases d <;> cases s <;> rfl

def coeffs (p : FormalSum F) : FormalSum (Laurent F) := p.map fun e => (scalar e.1,e.2)
def coeffPair (p : BinaryPair F) : BinaryPair (Laurent F) := (coeffs p.1,coeffs p.2)

theorem inverse_evaluate (q : Nat) (d : Int) (p : FormalSum F) :
    Shaped.evaluate (inverse q) d (coeffs p)=mk 0 (Lift.valueAt (Lift.degree q d) p) := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    change scalar e.1*si (inverse q) d e.2+Shaped.evaluate (inverse q) d (coeffs p)=_
    rw [ih,inverse_degree,scalar,←embed_mul,←embed_add]
    apply congrArg (mk 0); funext n
    change product (constant e.1) _ n+_=_
    rw [constant_product]; rfl

theorem inverse_binary_iff (q : Nat) (p : BinaryPair F) :
    Shaped.Binary (inverse q) (coeffPair p) ↔ Lift.Binary q p := by
  constructor
  · intro h d n
    have eq := h d
    change Shaped.evaluate _ _ (coeffs p.1)+Shaped.evaluate _ _ (coeffs p.2)=0 at eq
    rw [inverse_evaluate,inverse_evaluate,←embed_add] at eq
    exact congrFun (mk_injective eq) n
  · intro h d
    change Shaped.evaluate _ _ (coeffs p.1)+Shaped.evaluate _ _ (coeffs p.2)=0
    rw [inverse_evaluate,inverse_evaluate,←embed_add]
    exact congrArg (mk 0) (funext (h d))

end Megaera.FinalBinaryCarlitz
