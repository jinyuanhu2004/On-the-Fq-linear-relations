import Megaera.FinalBinaryLaurent
import Megaera.SectionThreeSpaces

/-! The limiting step on p. 19 is a finite coefficient calculation. -/
namespace Megaera.FinalFirstEntry
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.Lift Megaera.SectionThreeSpaces
open Megaera.FinalBinarySeries Megaera.FinalBinaryLaurent
variable {F : Type u} [Arithmetic F] [Neg F] {q : Nat}
local instance : Arithmetic (Series F) := seriesArithmetic
local instance : Std.Associative (α := Series F) (· * ·) := ⟨Arithmetic.mulAssoc⟩
local instance : Std.Commutative (α := Series F) (· * ·) := ⟨Arithmetic.mulComm⟩

private theorem cancel_left (field : ConstantField F q) (a b c : Series F) (h : a+b=a+c) : b=c := by
  funext n
  have e : a n+b n=a n+c n := congrFun h n
  have neg : -a n+a n=0 := (Arithmetic.addComm ..).trans (field.add_neg _)
  simpa only [←Arithmetic.addAssoc,neg,zeroAdd] using congrArg ((-a n)+·) e

/-- Multiplication by 1/l_d is injective even though its inverse has a pole at infinity. -/
theorem cancel_denom (field : ConstantField F q) (d : Nat) (a b : Series F)
    (h : inverseDenom q d*a=inverseDenom q d*b) : a=b := by
  induction d with
  | zero => simpa only [inverseDenom,show (unitSeries:Series F)=1 from rfl,oneMul] using h
  | succ d ih =>
    let e := q^(d+1)
    let f := inverseDenom (F:=F) q (d+1)
    let g := inverseDenom (F:=F) q d
    have law : f+power T e*g=power T (e-1)*f := by
      rw [powT_mul,powT_mul]; exact funext (inverseDenom_factor field d)
    have rel (v : Series F) : f*v+power T e*(g*v)=power T (e-1)*(f*v) := by
      have z := congrArg (·*v) law
      simpa only [show ∀ x y : Series F,(x+y)*v=x*v+y*v from fun x y => add_product x y v,
        Arithmetic.mulAssoc] using z
    have hz := rel a
    change f*a=f*b at h
    rw [h,←rel b] at hz
    exact ih (cancel_pow e (cancel_left field _ _ _ hz))

private theorem cancel_power (field : ConstantField F q) (d m : Nat) (a b : Series F)
    (h : power (inverseDenom q d) m*a=power (inverseDenom q d) m*b) : a=b := by
  induction m with
  | zero => simpa only [power,oneMul] using h
  | succ m ih =>
    apply ih
    apply cancel_denom field d
    rw [power] at h
    calc _ = (power (inverseDenom q d) m * inverseDenom q d)*a := by ac_rfl
         _ = _ := h
         _ = _ := by ac_rfl

/-- Tail coefficients for the rows that start with n. -/
def tails (n : Nat) (p : FormalSum F) : FormalSum F :=
  p.filterMap fun (k,s) => match s with
    | [] => none
    | a::t => if a=n then some (k,t) else none

def startsAt (n : Nat) (p : FormalSum F) : Prop :=
  ∀ e ∈ p, ∃ a t, e.2=a::t ∧ n≤a

private def divided (q d n : Nat) : Tuple → Series F
  | [] => 0
  | a::t => power (inverseDenom q d) (a-n) * trunc q d t

private theorem extract (q d n : Nat) (p : FormalSum F) (hp : startsAt n p) :
    valueAt (exactLevel q d) p = power (inverseDenom q d) n * valueAt (divided q d n) p := by
  induction p with
  | nil => exact (Arithmetic.mulZero _).symm
  | cons e p ih =>
    obtain ⟨a,t,ea,le⟩ := hp e (by simp)
    have tail := ih (fun z hz => hp z (by simp [hz]))
    have head : exactLevel (F:=F) q d e.2= power (inverseDenom q d) n * divided q d n e.2 := by
      rw [ea, exactLevel,←FinalBinaryTransport.power_coeff,divided,←Arithmetic.mulAssoc,
        ←power_add,Nat.add_sub_of_le le]
      rfl
    have cons_val (g : Tuple → Series F) :
        valueAt g (e::p)=FinalBinaryTransport.constant e.1*g e.2 + valueAt g p := by
      funext i; change e.1*g e.2 i+valueAt g p i=product (FinalBinaryTransport.constant e.1) (g e.2) i+valueAt g p i
      rw [FinalBinaryTransport.constant_product]
    rw [cons_val,cons_val,head,tail,Arithmetic.distrib]
    congr 1; ac_rfl

private theorem divided_coeff (field : ConstantField F q) (p : FormalSum F) (n d j : Nat)
    (hp : startsAt n p) (hd : j<d) :
    valueAt (divided q d n) p j=valueAt (trunc q d) (tails n p) j := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    obtain ⟨k,s⟩ := e
    obtain ⟨a,t,rfl,le⟩ := hp (k,s) (by simp)
    have tail := ih (fun z hz => hp z (by simp [hz]))
    by_cases eq : a=n
    · subst a
      simp only [tails,List.filterMap_cons,if_pos rfl] at *
      change k*(power (inverseDenom (F:=F) q d) (n-n)*trunc q d t : Series F) j+valueAt (divided q d n) p j=k*trunc q d t j+_
      rw [Nat.sub_self,power,oneMul,tail]; rfl
    · have pos : 0<a-n := by omega
      have z : (power (inverseDenom (F:=F) q d) (a-n)*trunc q d t : Series F) j=0 := by
        obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt pos)
        rw [hk,power,Arithmetic.mulComm (power _ k),Arithmetic.mulAssoc]
        apply product_zero_below
        intro i hi; exact inverseDenom_below q d i field.two_le (by omega)
      change k*(power (inverseDenom (F:=F) q d) (a-n)*trunc q d t : Series F) j+_ = _
      rw [z,Arithmetic.mulZero,zeroAdd]
      simpa [tails,eq] using tail

/-- Uniform coefficient limit for the normalized sum; includes the empty tail. -/
theorem stable_tail (field : ConstantField F q) (p : FormalSum F) (n d j : Nat)
    (hp : startsAt n p) (valid : ∀ e∈p,Valid e.2) (hd : j<d) :
    valueAt (divided q d n) p j=valueAt (fun s i => trunc q (i+1) s i) (tails n p) j := by
  rw [divided_coeff field p n d j hp hd]
  unfold valueAt
  apply FinalBinarySeries.sum_congr
  intro e he
  obtain ⟨z,hz,out⟩ := List.mem_filterMap.mp he
  obtain ⟨a,t,es,_⟩ := hp z hz
  simp only [es] at out
  split at out <;> simp_all only [Option.some.injEq,reduceCtorEq]
  subst e
  exact congrArg (z.1*·) (trunc_stable q j field.two_le t
    (fun i hi => valid z hz i (es ▸ List.mem_cons_of_mem _ hi)) d (by omega))

private theorem stable_cleared (field : ConstantField F q) (n : Nat) (p r : FormalSum F)
    (hp : startsAt n p) (hr : startsAt n r) (vp : ∀ e∈p,Valid e.2) (vr : ∀ e∈r,Valid e.2)
    (fixed : ∀ d : Nat, cleared q (valueAt (exactLevel q d) p) (valueAt (exactLevel q d) r)) :
    cleared q (valueAt (fun s i => trunc q (i+1) s i) (tails n p))
      (valueAt (fun s i => trunc q (i+1) s i) (tails n r)) := by
  have normalized (d : Nat) : cleared q (valueAt (divided q d n) p) (valueAt (divided q d n) r) := by
    let P := valueAt (divided q d n) p
    let R := valueAt (divided q d n) r
    let f := power (inverseDenom (F:=F) q d) n
    have eq : power T q * valueAt (exactLevel q d) p + valueAt (exactLevel q d) r =
        power T (q-1)*valueAt (exactLevel q d) r := by
      rw [powT_mul,powT_mul]; exact funext (fixed d)
    rw [extract q d n p hp,extract q d n r hr] at eq
    change power T q*(f*P)+f*R=power T (q-1)*(f*R) at eq
    have h : f*(power T q*P+R)=f*(power T (q-1)*R) := by
      rw [Arithmetic.distrib]
      calc _ = power T q*(f*P)+f*R := by ac_rfl
           _ = _ := eq
           _ = _ := by ac_rfl
    have h' := cancel_power field d n _ _ h
    rw [powT_mul,powT_mul] at h'
    exact congrFun h'
  intro j
  have h := normalized (j+1) j
  have sp := stable_tail field p n (j+1) (j-q) hp vp (by omega)
  have sr := stable_tail field r n (j+1) (j-(q-1)) hr vr (by omega)
  have sr' := stable_tail field r n (j+1) j hr vr (by omega)
  simpa only [shift,sp,sr,sr'] using h

omit [Arithmetic F] [Neg F] in
theorem tails_mem {n w : Nat} (p : FormalSum F) (hp : homogeneous w p)
    (e : F × Tuple) (he : e ∈ tails n p) :
    Valid e.2 ∧ n+weight e.2=w := by
  obtain ⟨⟨k,s⟩,hm,out⟩ := List.mem_filterMap.mp he
  have ⟨vh,wh⟩ := hp _ hm
  cases s with
  | nil => contradiction
  | cons a t =>
    change (if a=n then some (k,t) else none)=some e at out
    split at out
    · rename_i ha
      obtain rfl := Option.some.inj out
      exact ⟨fun b hb => vh b (List.mem_cons_of_mem a hb),by simpa [←ha,weight] using wh⟩
    · contradiction

private theorem tail_value {w n : Nat} (q : Nat) (p : FormalSum F)
    (hom : homogeneous w p) (lt : n<w) :
    valueAt (fun s i => trunc q (i+1) s i) (tails n p) = Carlitz.evaluate q (tails n p) := by
  funext i
  apply FinalBinarySeries.sum_congr
  intro e he
  have h := (tails_mem p hom e he).2
  have ne : e.2≠[] := by intro z; rw [z] at h; simp [weight] at h; omega
  simp only [Carlitz.li,if_neg ne]

/-- The least-head part of a fixed degree-one relation is a relation of the
lower weight. Equality holds for every coefficient of the concrete series. -/
theorem least_tail_U (field : ConstantField F q) {w n : Nat} (lt : n<w)
    (p r : FormalSum F) (hp : homogeneous w p) (hr : homogeneous w r)
    (sp : startsAt n p) (sr : startsAt n r)
    (fixed : ∀ d : Int, cleared q (valueAt (degree q d) p) (valueAt (degree q d) r)) :
    U q (w-n) (pairCoordinates (tails n p) (tails n r)) := by
  have hom (s : FormalSum F) (hs : homogeneous w s) : homogeneous (w-n) (tails n s) := by
    intro e he; obtain ⟨v,h⟩ := tails_mem s hs e he; exact ⟨v,by omega⟩
  refine ⟨tails n p,tails n r,hom p hp,hom r hr,?_,rfl⟩
  rw [←tail_value q p hp lt,←tail_value q r hr lt]
  exact stable_cleared field n p r sp sr (fun e he => (hp e he).1)
    (fun e he => (hr e he).1) (fun d => fixed (.ofNat d))

/-- The constant-field version of least-head descent. -/
theorem least_tail_R (field : ConstantField F q) {w n : Nat} (lt : n<w)
    (p : FormalSum F) (hp : homogeneous w p) (sp : startsAt n p)
    (fixed : fixedLevels q p) : Relation q (w-n) (tails n p) := by
  refine ⟨fun e he => ?_,?_⟩
  · obtain ⟨v,h⟩ := tails_mem p hp e he; exact ⟨v,by omega⟩
  · intro j
    rw [←tail_value q p hp lt,←stable_tail field p n (j+1) j sp (fun e he => (hp e he).1) (by omega)]
    have h : valueAt (exactLevel q (j+1)) p = (0:Series F) := funext (fixed (.ofNat (j+1)))
    rw [extract q (j+1) n p sp] at h
    have z := cancel_power field (j+1) n _ (0:Series F) (h.trans (Arithmetic.mulZero _).symm)
    exact congrFun z j

end Megaera.FinalFirstEntry
