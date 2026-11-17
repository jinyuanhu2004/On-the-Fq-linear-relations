import Megaera.FinalBasisRanks
import Megaera.FinalBinaryCarlitz

/-! Kernel computation for the unprefixed fundamental lift in Lemma 3.4. -/
namespace Megaera.FinalFixedKernel
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.Lift Megaera.SectionThreeSpaces
open Megaera.FinalBinaryTransport Megaera.FinalBinaryLaurent Megaera.FinalBinaryCarlitz
open Megaera.FinalBinarySeries
variable {F : Type u} [Arithmetic F] [Neg F] {q : Nat}
local instance : Arithmetic (Series F) := seriesArithmetic

/-- The factor 1/ℓ_d is a nonzero divisor on the actual power series.
Use (θ−θ^(q^(d+1)))/ℓ_(d+1) = 1/ℓ_d in the Laurent ring. -/
theorem inverse_regular (field : ConstantField F q) (d : Nat) (g : Series F)
    (hg : inverseDenom q d * g=0) : g=0 := by
  induction d with
  | zero => exact (oneMul g).symm.trans hg
  | succ d ih =>
    apply ih
    apply mk_injective
    change mk 0 (inverseDenom q d*g)=(0 : Laurent F)
    rw [embed_mul]
    change inverse q d*mk 0 g=0
    rw [←factor_inverse field d,Arithmetic.mulAssoc]
    change _*(mk 0 (inverseDenom q (d+1)*g))=0
    rw [hg]; exact Arithmetic.mulZero _

omit [Neg F] in
private theorem unit_pow (n : Nat) : seriesPow (unitSeries (F:=F)) n=unitSeries := by
  induction n with
  | zero => rfl
  | succ n ih => rw [seriesPow,ih,product_unit]

theorem singleton_trunc_first (field : ConstantField F q) (d : Nat) :
    trunc (F:=F) q (d+1) [q-1] 0=1 := by
  have qle := field.two_le
  induction d with
  | zero =>
    simp [trunc,inverseDenom,unit_pow,product_unit,addSeries,unitSeries,zeroAdd]
  | succ d ih =>
    change trunc q (d+1) [q-1] 0 + product (seriesPow (inverseDenom q (d+1)) (q-1)) _ 0=1
    rw [ih,product_first,show q-1=(q-2)+1 by omega,seriesPow,product_first,
      inverseDenom_below q (d+1) 0 qle (by omega),zeroMul,zeroMul,Arithmetic.addZero]

omit [Neg F] in
private theorem regular_at_one (f g : Series F) (hf : f 0=1) (hg : f*g=0) : g=0 := by
  funext n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    have z : product f g n=0 := congrFun hg n
    cases n with
    | zero => simpa only [product_first,hf,oneMul] using z
    | succ i =>
      rw [product_next,hf,oneMul,product_comm (fun n => f (n+1)) g,
        product_zero_below g _ i (fun j hj => ih j (by omega)),Arithmetic.addZero] at z
      exact z

private theorem total_H (q d : Nat) (t : Tuple) :
    total (degree (F:=F) q (.ofNat d)) (H q [] t)=
    inverseDenom q d*(trunc q d [q-1]*trunc q d t) := by
  let x := inverseDenom (F:=F) q
  have lt : degree q (.ofNat d)=level x d := by
    funext t; exact (level_coeff q (.ofNat d) t).symm
  rw [lt]
  change total (level x d) (concatenate [[1]] (quasiShuffle [q-1] t))=_
  simp only [concatenate,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.cons_append,List.nil_append]
  rw [level_cons_map,stuffle_product,trunc_coeff,trunc_coeff,power,power,oneMul]

omit [Neg F] in
theorem value_weighted (f : Tuple → Series F) (p : FormalSum F) :
    valueAt f p = total (fun e : F × Tuple => constant e.1 * f e.2) p := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    funext n
    change e.1 * f e.2 n + valueAt f p n = product (constant e.1) (f e.2) n + _
    rw [constant_product,ih]

omit [Neg F] in
theorem sum_terms (f : Tuple → Series F) (a : F) (l : List Tuple) :
    total (fun e : F × Tuple => constant e.1 * f e.2) (withCoeff a l)=
    constant a * total f l := by
  induction l with
  | nil => exact (Arithmetic.mulZero _).symm
  | cons b l ih =>
    change _ + total _ (withCoeff a l)=_*(f b+total f l)
    rw [ih,Arithmetic.distrib]

/-- The second column of the unprefixed lift at any positive level is
(1/ℓ_d) Si_<d(q−1) times the truncated sum of the tail. -/
theorem high_at_degree (q d : Nat) (p : FormalSum F) :
    valueAt (degree q (.ofNat d)) (expand (H q []) p)=
      inverseDenom q d * (trunc q d [q-1]*valueAt (trunc q d) p) := by
  simp only [value_weighted]
  let a := inverseDenom (F:=F) q d
  let b := trunc (F:=F) q d [q-1]
  induction p with
  | nil => simp [expand,total,Arithmetic.mulZero]
  | cons e p ih =>
    change total _ (withCoeff e.1 (H q [] e.2)++expand (H q []) p)=
      a*(b*(constant e.1*trunc q d e.2+_))
    rw [Paper.total_append',sum_terms,total_H,ih]
    change _=a*(b*(_+_))
    rw [Arithmetic.distrib,Arithmetic.distrib]
    congr 1
    letI : Std.Associative (α:=Series F) (·*·) := ⟨Arithmetic.mulAssoc⟩
    letI : Std.Commutative (α:=Series F) (·*·) := ⟨Arithmetic.mulComm⟩
    dsimp [a,b]; ac_rfl

theorem high_zero_iff (field : ConstantField F q) (d : Nat) (p : FormalSum F) :
    valueAt (degree q (.ofNat (d+1))) (expand (H q []) p)=0 ↔
    valueAt (trunc q (d+1)) p=0 := by
  rw [high_at_degree]
  exact ⟨fun h => regular_at_one _ _ (singleton_trunc_first field d) (inverse_regular field _ _ h),
    fun h => by rw [h,Arithmetic.mulZero,Arithmetic.mulZero]⟩

private theorem high_nonpositive (q : Nat) (p : FormalSum F) (d : Int) (hd : d≤0) :
    valueAt (degree q d) (expand (H q []) p) = 0 := by
  cases d with
  | ofNat i =>
    change (i:Int)≤0 at hd
    have : i=0 := by omega
    subst i; rw [high_at_degree]
    change _*((0 : Series F)*_)=0
    rw [zeroMul,Arithmetic.mulZero]
  | negSucc i =>
    funext n; apply total_zero_of_members
    intro e he
    obtain ⟨z,_,hz⟩ := List.mem_flatMap.mp he
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hz
    obtain ⟨t,_,rt⟩ : ∃ t, t∈quasiShuffle [q-1] z.2 ∧ 1::t=s := by simpa [H,endings,concatenate] using hs
    have hs' : ∃ t, s=1::t := ⟨t,rt.symm⟩
    obtain ⟨t,rt⟩ := hs'
    subst s; cases i <;> exact Arithmetic.mulZero _


private theorem zero_base (p : FormalSum F) (w : Nat) (hp : homogeneous w p)
    (h : valueAt (trunc q 1) p=0) : valueAt (trunc q 0) p=0 := by
  by_cases hw : w=0
  · have same (e) (he : e∈p) : e.2=[] := by
      obtain ⟨hv,wt⟩ := hp e he
      cases hs : e.2 with
      | nil => rfl
      | cons a s =>
        have v := hv a (by simp [hs])
        simp [hs,weight] at wt; omega
    have eq : valueAt (trunc q 0) p=valueAt (trunc q 1) p := by
      funext n; apply Shaped.weighted_congr (fun t => trunc q 0 t n) (fun t => trunc q 1 t n)
      intro e he; rw [same e he]; rfl
    exact eq.trans h
  · funext n; apply total_zero_of_members
    intro e he
    obtain ⟨_,wt⟩ := hp e he
    cases hs : e.2 with
    | nil => simp [hs,weight] at wt; omega
    | cons a s => simp [hs,trunc,Arithmetic.mulZero]

omit [Neg F] in
private theorem value_on_support (f g : Tuple → Series F) (p : FormalSum F)
    (h : ∀ e∈p, f e.2=g e.2) : valueAt f p=valueAt g p := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    funext n
    change e.1*f e.2 n+valueAt f p n=e.1*g e.2 n+valueAt g p n
    rw [h e (by simp),ih (fun z hz => h z (by simp [hz]))]

theorem fixed_iff_truncations (q : Nat) (p : FormalSum F)
    (hp : homogeneous w p) : fixedLevels q p ↔ ∀ d : Nat, valueAt (trunc q (d+1)) p=0 := by
  have endpoint : valueAt (trunc q 0) p=valueAt (degree q (-1)) p := by
    apply value_on_support; intro e _; cases e.2 <;> rfl
  constructor
  · intro hz d
    have all (i : Nat) : valueAt (trunc q i) p=0 := by
      induction i with
      | zero => exact endpoint.trans (funext (hz (-1)))
      | succ i ih =>
        funext n; rw [Lift.eval_step,congrFun ih n]
        change 0+valueAt (degree q (.ofNat i)) p n=0
        rw [hz,Arithmetic.addZero]
    exact all (d+1)
  · intro hz
    have base := zero_base p w hp (hz 0)
    have all (i : Nat) : valueAt (trunc q i) p=0 := by cases i with
      | zero => exact base
      | succ i => exact hz i
    intro d n
    cases d with
    | ofNat d =>
      have step := eval_step (F:=F) q d p n
      rw [congrFun (all d) n,congrFun (hz d) n] at step
      change 0=0+valueAt (exactLevel q d) p n at step
      rw [zeroAdd] at step; exact step.symm
    | negSucc d =>
      cases d with
      | zero => exact congrFun (endpoint.symm.trans base) n
      | succ d => apply total_zero_of_members; intro e _; cases e.2 <;> exact Arithmetic.mulZero _

/-- Fixedness of an unprefixed fundamental lift is equivalent to fixedness
of its tail, including the weight-zero tail and the level d=−1. The
binary identity here is exactly the adjacent-level C-linear relation. -/
theorem unprefixed_fixed_iff (field : ConstantField F q) (p : FormalSum F) (hp : homogeneous w p)
    (binary : ∀ d : Int, cleared q
      (valueAt (degree q d) (expand (L q []) p))
      (valueAt (degree q (d+1)) (expand (H q []) p))) :
    (∀ d : Int, cleared q (valueAt (degree q d) (expand (L q []) p))
                          (valueAt (degree q d) (expand (H q []) p))) ↔ fixedLevels q p := by
  let hi (d : Int) := valueAt (degree q d) (expand (H q []) p)
  rw [fixed_iff_truncations q p hp]
  constructor
  · intro fixed
    have next (d : Int) : hi d=hi (d+1) :=
      FinalDegreeOne.equal_second field _ _ _ (fixed d) (binary d)
    have vanish (d : Nat) : hi (.ofNat d)=0 := by
      induction d with
      | zero => exact high_nonpositive _ _ 0 (by decide)
      | succ d ih => exact (next (.ofNat d)).symm.trans ih
    intro d; exact (high_zero_iff field d p).mp (vanish (d+1))
  · intro hz
    have vanish (d : Int) : hi d=0 := by
      cases d with
      | ofNat n =>
        cases n with
        | zero => exact high_nonpositive _ _ 0 (by decide)
        | succ n => exact (high_zero_iff field n p).mpr (hz n)
      | negSucc n => exact high_nonpositive _ _ _ (by omega)
    intro d
    change cleared q _ (hi d)
    have v : hi d=hi (d+1) := (vanish d).trans (vanish (d+1)).symm
    rw [v]; exact binary d

end Megaera.FinalFixedKernel
