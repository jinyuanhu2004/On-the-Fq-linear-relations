import Megaera.FinalBinaryTransport
import Megaera.Singletons

/-! Adjoin T⁻¹ to the concrete Cauchy series ring. A representative (i,f)
stands for T⁻ⁱ f. Multiplication by T is injective on every series. -/
namespace Megaera.FinalBinaryLaurent
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.FinalBinarySeries
variable {F : Type u} [Arithmetic F]
local instance : Arithmetic (Series F) := seriesArithmetic

def T : Series F := shift 1 unitSeries

theorem T_mul (f : Series F) : T*f=shift 1 f := by
  funext n
  cases n with
  | zero => change product _ _ 0=_; rw [product_first]; exact zeroMul _
  | succ n =>
    change product T f (n+1)=shift 1 f (n+1)
    rw [product_next]
    have tail : (fun i => (T : Series F) (i+1))=unitSeries := by funext i; simp [T,shift]
    rw [tail,product_unit]
    simp [T,shift,zeroMul,zeroAdd]

theorem powT_mul (n : Nat) (f : Series F) : power T n * f=shift n f := by
  induction n generalizing f with
  | zero => funext i; rw [power,oneMul]; simp [shift]
  | succ n ih =>
    rw [power,Arithmetic.mulAssoc,T_mul,ih]
    funext i; unfold shift
    by_cases le : n+1≤i
    · simp [Nat.le_of_lt (Nat.lt_of_succ_le le),le,show 1≤i-n by omega,
        show i-n-1=i-(n+1) by omega]
    · by_cases eq : i=n
      · subst i; simp [le]
      · simp [show ¬n≤i by omega,le]

theorem cancel_pow (n : Nat) {a b : Series F}
    (eqn : power T n*a=power T n*b) : a=b := by
  rw [powT_mul,powT_mul] at eqn
  funext i
  simpa [shift] using congrFun eqn (i+n)

abbrev Raw (F : Type u) := Nat × Series F
def Equiv (a b : Raw F) : Prop := power T b.1*a.2=power T a.1*b.2
local instance : Std.Associative (α := Series F) (· * ·) := ⟨Arithmetic.mulAssoc⟩
local instance : Std.Commutative (α := Series F) (· * ·) := ⟨Arithmetic.mulComm⟩
local instance : Std.Associative (α := Series F) (· + ·) := ⟨Arithmetic.addAssoc⟩
local instance : Std.Commutative (α := Series F) (· + ·) := ⟨Arithmetic.addComm⟩

def rel : Setoid (Raw F) where
  r := Equiv
  iseqv := ⟨fun _ => rfl,fun e => e.symm,by
    intro a b c ab bc
    apply cancel_pow b.1
    calc
      _ = power T c.1*(power T b.1*a.2) := by ac_rfl
      _ = power T c.1*(power T a.1*b.2) := congrArg _ ab
      _ = power T a.1*(power T c.1*b.2) := by ac_rfl
      _ = power T a.1*(power T b.1*c.2) := congrArg _ bc
      _ = _ := by ac_rfl⟩

def Laurent (F : Type u) [Arithmetic F] := Quotient (rel (F:=F))
def mk (i : Nat) (f : Series F) : Laurent F := @Quotient.mk _ rel (i,f)

private theorem eq_mk {i j : Nat} {f g : Series F} (e : power T j*f=power T i*g) :
    mk i f=mk j g := Quotient.sound e

private def plus (a b : Raw F) : Raw F :=
  (a.1+b.1,power T b.1*a.2+power T a.1*b.2)
private def times (a b : Raw F) : Raw F := (a.1+b.1,a.2*b.2)

private theorem plus_rel {a b a' b' : Raw F} (ha : Equiv a a') (hb : Equiv b b') :
    Equiv (plus a b) (plus a' b') := by
  unfold Equiv plus
  simp only [power_add,Arithmetic.distrib]
  congr 1
  · calc
      _ = (power T b'.1*power T b.1)*(power T a'.1*a.2) := by ac_rfl
      _ = _ := by rw [ha]; ac_rfl
  · calc
      _ = (power T a'.1*power T a.1)*(power T b'.1*b.2) := by ac_rfl
      _ = _ := by rw [hb]; ac_rfl

private theorem times_rel {a b a' b' : Raw F} (ha : Equiv a a') (hb : Equiv b b') :
    Equiv (times a b) (times a' b') := by
  unfold Equiv times
  simp only [power_add]
  calc
    _ = (power T a'.1*a.2)*(power T b'.1*b.2) := by ac_rfl
    _ = _ := by rw [ha,hb]; ac_rfl

instance : Add (Laurent F) := ⟨Quotient.lift₂ (s₁:=rel) (s₂:=rel)
  (fun a b => @Quotient.mk _ rel (plus a b)) (fun _ _ _ _ ha hb => Quotient.sound (plus_rel ha hb))⟩
instance : Mul (Laurent F) := ⟨Quotient.lift₂ (s₁:=rel) (s₂:=rel)
  (fun a b => @Quotient.mk _ rel (times a b)) (fun _ _ _ _ ha hb => Quotient.sound (times_rel ha hb))⟩
instance : Zero (Laurent F) := ⟨mk 0 0⟩
instance : OfNat (Laurent F) 1 := ⟨mk 0 1⟩

@[simp] theorem mk_add (i j : Nat) (f g : Series F) :
    mk i f+mk j g=mk (i+j) (power T j*f+power T i*g) := rfl
@[simp] theorem mk_mul (i j : Nat) (f g : Series F) :
    mk i f*mk j g=mk (i+j) (f*g) := rfl

private theorem la_addAssoc (a b c : Laurent F) : a+b+c=a+(b+c) := by
  refine Quotient.inductionOn₃ a b c ?_
  rintro ⟨i,f⟩ ⟨j,g⟩ ⟨k,h⟩
  change mk ((i+j)+k) (power T k*(power T j*f+power T i*g)+power T (i+j)*h) =
    mk (i+(j+k)) (power T (j+k)*f+power T i*(power T k*g+power T j*h))
  rw [Nat.add_assoc]; apply congrArg
  simp only [Arithmetic.distrib,power_add]; ac_rfl

private theorem la_addComm (a b : Laurent F) : a+b=b+a := by
  refine Quotient.inductionOn₂ a b ?_
  rintro ⟨i,f⟩ ⟨j,g⟩
  change mk (i+j) _=mk (j+i) _
  rw [Nat.add_comm i j]; exact congrArg _ (Arithmetic.addComm ..)

private theorem la_distrib (a b c : Laurent F) : a*(b+c)=a*b+a*c := by
  refine Quotient.inductionOn₃ a b c ?_
  rintro ⟨i,f⟩ ⟨j,g⟩ ⟨k,h⟩
  apply eq_mk
  change power T ((i+j)+(i+k))*(f*(power T k*g+power T j*h)) =
    power T (i+(j+k))*(power T (i+k)*(f*g)+power T (i+j)*(f*h))
  simp only [power_add,Arithmetic.distrib]; ac_rfl

instance : Arithmetic (Laurent F) where
  addAssoc := la_addAssoc
  addComm := la_addComm
  addZero a := by
    refine Quotient.inductionOn a ?_; rintro ⟨i,f⟩
    change mk (i+0) (power T 0*f+power T i*0)=mk i f
    simp [power,oneMul,Arithmetic.mulZero,Arithmetic.addZero]
  mulAssoc a b c := by
    refine Quotient.inductionOn₃ a b c ?_; rintro ⟨i,f⟩ ⟨j,g⟩ ⟨k,h⟩
    change mk ((i+j)+k) ((f*g)*h) = mk (i+(j+k)) (f*(g*h))
    rw [Nat.add_assoc,Arithmetic.mulAssoc]
  mulComm a b := by
    refine Quotient.inductionOn₂ a b ?_; rintro ⟨i,f⟩ ⟨j,g⟩
    change mk (i+j) (f*g)=mk (j+i) (g*f)
    rw [Nat.add_comm i j,Arithmetic.mulComm f g]
  mulOne a := by
    refine Quotient.inductionOn a ?_; rintro ⟨i,f⟩
    change mk (i+0) (f*1)=mk i f; simp [Arithmetic.mulOne]
  mulZero a := by
    refine Quotient.inductionOn a ?_; rintro ⟨i,f⟩
    apply eq_mk; change power T 0*(f*0) = power T (i+0)*0
    simp [Arithmetic.mulZero]
  distrib := la_distrib

theorem mk_injective {a b : Series F} (eq : mk 0 a=mk 0 b) : a=b := by
  have h : power T 0*a=power T 0*b := Quotient.exact eq
  simpa [power,oneMul] using h

theorem embed_add (a b : Series F) : mk 0 (a+b)=mk 0 a+mk 0 b := by
  rw [mk_add]; simp [power,oneMul]

theorem embed_mul (a b : Series F) : mk 0 (a*b)=mk 0 a*mk 0 b := rfl

variable [Neg F]
local instance : Neg (Series F) := ⟨fun f n => -f n⟩

private theorem neg_rel (field : ConstantField F q) {a b : Raw F} (e : Equiv a b) :
    Equiv (a.1,-a.2) (b.1,-b.2) := by
  change power T b.1*(-a.2)=power T a.1*(-b.2)
  have compat (k : Nat) (f : Series F) : shift k (-f)=fun n => -shift k f n := by
    funext n
    by_cases h : k≤n
    · simp only [shift,if_pos h]; rfl
    · simp [shift,h,Singletons.nz field.add_neg]
  unfold Equiv at e
  simp only [powT_mul] at e ⊢
  rw [compat,compat,e]

/-- Representatives store the negative of each coefficient. Its action on
each class is verified below from the additive-group laws of the constants. -/
noncomputable instance : Neg (Laurent F) := ⟨fun x =>
  let a := Classical.choose (Quotient.exists_rep (s:=rel) x)
  mk a.1 (-a.2)⟩

theorem neg_mk (field : ConstantField F q) (i : Nat) (f : Series F) :
    -(mk i f)=mk i (-f) := by
  apply Quotient.sound (s:=rel)
  exact neg_rel field (a:=Classical.choose (Quotient.exists_rep (mk i f))) (b:=(i,f))
    (Quotient.exact (Classical.choose_spec (Quotient.exists_rep (mk i f))))

theorem negative_sum (field : ConstantField F q) (x : Laurent F) : x+(-x)=0 := by
  refine Quotient.inductionOn x ?_; rintro ⟨i,f⟩
  change mk i f + -(mk i f)=0
  rw [neg_mk field,mk_add]
  apply eq_mk
  have add : f+(-f)=0 := funext fun n => field.add_neg (f n)
  change power T 0*(power T i*f+power T i*(-f))=power T (i+i)*0
  rw [←Arithmetic.distrib,add,Arithmetic.mulZero,Arithmetic.mulZero,Arithmetic.mulZero]

def scalar (a : F) : Laurent F := mk 0 (FinalBinaryTransport.constant a)

omit [Neg F] in
theorem scalar_zero : scalar (0:F)=0 := by
  apply congrArg (mk 0)
  funext i; simp [FinalBinaryTransport.constant]; rfl

omit [Neg F] in
theorem scalar_one : scalar (1:F)=1 := rfl

omit [Neg F] in
theorem scalar_add (a b : F) : scalar (a+b)=scalar a+scalar b := by
  unfold scalar; rw [←embed_add]; apply congrArg (mk 0)
  funext i; change (if i=0 then a+b else 0)=(if i=0 then a else 0)+(if i=0 then b else 0)
  split <;> simp [Arithmetic.addZero]

omit [Neg F] in
theorem scalar_mul (a b : F) : scalar (a*b)=scalar a*scalar b := by
  unfold scalar; rw [←embed_mul]; apply congrArg (mk 0)
  funext i; rw [show (FinalBinaryTransport.constant a*FinalBinaryTransport.constant b) i=
    a*(FinalBinaryTransport.constant b i) from FinalBinaryTransport.constant_product ..]
  by_cases e : i=0 <;> simp [FinalBinaryTransport.constant,e,Arithmetic.mulZero]

theorem scalar_neg (field : ConstantField F q) (a : F) : scalar (-a) = -scalar a := by
  unfold scalar; rw [neg_mk field]; apply congrArg (mk 0)
  funext i; change (if i=0 then -a else 0) = -(if i=0 then a else 0)
  by_cases e : i=0 <;> simp [e,Singletons.nz field.add_neg]

end Megaera.FinalBinaryLaurent
