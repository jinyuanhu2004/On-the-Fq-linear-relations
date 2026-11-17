import Megaera.RowEvaluation

/-! The TT reduction of Lemma 2.4. The scalar variable in the finite
expressions below acts as −D₁ = θ−θ^q on Laurent coefficients. -/
namespace Megaera.TTSpanning
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.RowEvaluation Megaera.SectionThreeSpaces
open Megaera.Splitting Megaera.Triangular

variable {F : Type u} [Arithmetic F] [Neg F] {q w : Nat}
local instance : Std.Associative (α := F) (· + ·) := ⟨Arithmetic.addAssoc⟩
local instance : Std.Commutative (α := F) (· + ·) := ⟨Arithmetic.addComm⟩

inductive Expression (F : Type u) where
  | zero
  | atom (s : Tuple)
  | plus (a b : Expression F)
  | scale (c : F) (a : Expression F)
  | variableMul (a : Expression F)

def supported (q w : Nat) : Expression F → Prop
  | .zero => True
  | .atom s => TT q s ∧ weight s = w
  | .plus x y => supported q w x ∧ supported q w y
  | .scale _ x | .variableMul x => supported q w x

def readExpr (q : Nat) (f : Tuple → Int → F) : Expression F → Int → F
  | .zero, _ => 0
  | .atom s, k => f s k
  | .plus x y, k => readExpr q f x k + readExpr q f y k
  | .scale c x, k => c * readExpr q f x k
  | .variableMul x, k => readExpr q f x (k+1) + (-(1:F))*readExpr q f x (k+q)

def delta (s t : Tuple) : F := if s = t then 1 else 0
def scalar (t s : Tuple) (k : Int) : F := if k = 0 then delta s t else 0
def value (q : Nat) (s : Tuple) : Int → F := coefficient (li q s)

/-- The specialization of the cited K-linear independence in Theorem 1.2
to finite expressions over F[θ−θ^q]. Testing against scalar t evaluates
the Laurent polynomial coefficient of Li(t) for each individual t. -/
def TTIndependent (F : Type u) [Arithmetic F] [Neg F] (q w : Nat) : Prop :=
  ∀ e : Expression F, supported q w e → (∀ k, readExpr q (value q) e k = 0) →
    ∀ t k, readExpr q (scalar t) e k = 0

omit [Neg F] in
private theorem delta_times (a : F) (s t : Tuple) :
    a * delta s t = if s = t then a else 0 := by
  by_cases h : s=t <;> simp [delta,h,Arithmetic.mulOne,Arithmetic.mulZero]

private theorem no_positive (hq : 0 < q) (e : Expression F) (t : Tuple)
    (k : Int) (hk : 0 < k) : readExpr q (scalar t) e k = 0 := by
  induction e generalizing k with
  | zero => rfl
  | atom s => simp [readExpr,scalar,show k ≠ 0 by omega]
  | plus x y ix iy => simp [readExpr,ix k hk,iy k hk,Arithmetic.addZero]
  | scale a x ix => simp [readExpr,ix k hk,Arithmetic.mulZero]
  | variableMul x ix =>
    simp [readExpr,ix (k+1) (by omega),ix (k+q) (by omega),Arithmetic.mulZero,Arithmetic.addZero]

def Bounded (c : Rows F q w) : Prop := ∀ z ∈ c, ∀ a ∈ z.2.val.1, a ≤ q

/-- A TT expansion of a Laurent series, with a witness for the difference
between the input vector and its polynomial constant term. -/
def Represented (q w : Nat) (x : Int → F) (v : Tuple → F) : Prop :=
  ∃ e : Expression F, supported q w e ∧ (∀ k, readExpr q (value q) e k = x k) ∧
    ∃ c : Rows F q w, Bounded c ∧
      ∀ t, component L c t + readExpr q (scalar t) e 0 = v t

private theorem rep_zero : Represented q w (fun _ => (0:F)) (fun _ => 0) :=
  ⟨.zero,trivial,fun _ => rfl,[],by simp [Bounded], fun _ => Arithmetic.addZero _⟩

omit [Neg F] in
private theorem sum_append {A : Type v} (f : A → F) (l r : List A) :
    total f (l++r) = total f l + total f r := by
  induction l with
  | nil => exact (zeroAdd _).symm
  | cons a l ih => simp [total,ih,Arithmetic.addAssoc]

private theorem rep_plus {x y : Int → F} {v z : Tuple → F}
    (a : Represented q w x v) (b : Represented q w y z) :
    Represented q w (fun n => x n + y n) (fun t => v t + z t) := by
  obtain ⟨e,et,ev,c,cb,cc⟩ := a
  obtain ⟨f,ft,fv,d,db,dc⟩ := b
  refine ⟨.plus e f,⟨et,ft⟩,fun n => by simp only [readExpr,ev,fv],c++d,?_,?_⟩
  · intro z hz
    exact (List.mem_append.mp hz).elim (cb z) (db z)
  · intro t
    change _ = v t + z t
    rw [← cc t,← dc t]
    unfold component
    rw [sum_append]
    change (_ + _) + (_ + _) = (_ + _) + (_ + _)
    ac_rfl

omit [Neg F] in
private theorem scaled (a : F) (c : Rows F q w) (t : Tuple) :
    component L (c.map fun e => (a*e.1,e.2)) t = a * component L c t := by
  induction c with
  | nil => exact (Arithmetic.mulZero _).symm
  | cons z c ih =>
    change (a*z.1)*_ + component L _ t = a*(z.1*_ + component L c t)
    rw [ih,Arithmetic.mulAssoc,Arithmetic.distrib]

private theorem rep_scale (a : F) {x : Int → F} {v : Tuple → F} (h : Represented q w x v) :
    Represented q w (fun n => a*x n) (fun t => a*v t) := by
  obtain ⟨e,et,ev,c,cb,cc⟩ := h
  refine ⟨.scale a e,et,fun k => congrArg (a*·) (ev k),c.map (fun z => (a*z.1,z.2)),?_,?_⟩
  · intro z hz
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hz
    exact cb u hu
  · intro t
    change _ = a * v t
    rw [scaled, ← cc t, Arithmetic.distrib]
    rfl

private theorem rep_sum {A : Type v} (l : List A) (x : A → Int → F) (v : A → Tuple → F)
    (h : ∀ a ∈ l, Represented q w (x a) (v a)) :
    Represented q w (fun k => total (fun a => x a k) l) (fun t => total (fun a => v a t) l) := by
  induction l with
  | nil => exact rep_zero
  | cons a l ih => exact rep_plus (h a (by simp)) (ih (fun b hb => h b (List.mem_cons_of_mem _ hb)))

private theorem kill (field : ConstantField F q) (a : F) : a + (-(1:F))*a = 0 := by
  calc _ = a*1 + a*(-1) := by rw [Arithmetic.mulOne, Arithmetic.mulComm a (-1)]
       _ = a*(1+(-1)) := (Arithmetic.distrib ..).symm
       _ = 0 := by rw [field.add_neg,Arithmetic.mulZero]

private theorem erase_neg (field : ConstantField F q) (a b : F) : (a+b) + (-(1:F))*b = a := by
  rw [Arithmetic.addAssoc,kill field,Arithmetic.addZero]

private theorem weight_sum (s : Tuple) : s.sum = weight s := by
  induction s with
  | nil => rfl
  | cons a s ih => simp only [List.sum_cons,weight,ih]

private theorem eval_list (q : Nat) (l : List Tuple) (k : Int) :
    coefficient (evaluate q (withCoeff (1:F) l)) k = total (fun s => value q s k) l := by
  induction l with
  | nil => cases k <;> rfl
  | cons s l ih =>
    cases k with
    | ofNat n =>
      change 1 * li q s n + evaluate q (withCoeff 1 l) n =
        li q s n + total (fun t => value q t (.ofNat n)) l
      rw [oneMul]; exact congrArg (_ + ·) (ih)
    | negSucc n =>
      change 0 = 0 + total (fun t => value q t (.negSucc n)) l
      rw [← ih]; exact (Arithmetic.addZero _).symm

omit [Neg F] in
private theorem coord_list (l : List Tuple) (t : Tuple) :
    coordinates (withCoeff (1:F) l) t = total (fun s => delta s t) l := by
  induction l with
  | nil => rfl
  | cons s l ih => exact congrArg (delta s t + ·) ih

private theorem lift_row (field : ConstantField F q) (e : Row q w)
    (law : Identity (F := F) q (withCoeff 1 (L q e.val.1 e.val.2))
      (withCoeff 1 (H q e.val.1 e.val.2))) (k : Int) :
    let x := fun n => total (fun s => value (F := F) q s n) (H q e.val.1 e.val.2)
    total (fun s => value (F := F) q s k) (L q e.val.1 e.val.2) =
    x (k+1) + (-(1:F))*x (k+q) := by
  dsimp only
  have le := (cleared_iff_laurent q (by have := field.two_le; omega) _ _).mp law k
  simp only [eval_list] at le
  rw [← le,erase_neg field]

private theorem rep_L (field : ConstantField F q) (e : Row q w) (hb : ∀ a ∈ e.val.1, a ≤ q)
    (law : Identity (F := F) q (withCoeff 1 (L q e.val.1 e.val.2))
      (withCoeff 1 (H q e.val.1 e.val.2)))
    (later : ∀ t ∈ H q e.val.1 e.val.2,
      Represented q w (value (F := F) q t) (delta t)) :
    Represented q w (fun k => total (fun s => value (F := F) q s k) (L q e.val.1 e.val.2))
      (fun t => total (fun s => delta s t) (L q e.val.1 e.val.2)) := by
  obtain ⟨z,supp,ev,_⟩ := rep_sum _ _ _ later
  refine ⟨.variableMul z,supp,?_,[(1,e)],?_,?_⟩
  · intro k
    simp only [readExpr,ev]
    exact (lift_row field e law k).symm
  · intro a ha
    obtain rfl := List.mem_singleton.mp ha
    exact hb
  · intro t
    have hq := field.two_le
    simp only [readExpr,Int.zero_add,no_positive (by omega : 0 < q) z t 1 (by decide),
      no_positive (by omega : 0 < q) z t q (by omega),Arithmetic.mulZero,Arithmetic.addZero]
    change (1:F) * coordinates (withCoeff 1 _) t + 0 = _
    rw [oneMul,Arithmetic.addZero,coord_list]

private theorem rep_atom (field : ConstantField F q)
    (law : ∀ e : Row q w, Identity (F := F) q (withCoeff 1 (L q e.val.1 e.val.2))
      (withCoeff 1 (H q e.val.1 e.val.2)))
    (s : Tuple) (hs : Valid s) (hw : weight s = w) :
    Represented q w (value (F := F) q s) (delta s) := by
  classical
  let V (s : Tuple) := vectorRank w (delta (F := F) s)
  let N := (Dimension.tuples Int.toNat w).length
  have loop : ∀ n s, Valid s → weight s = w → N - V s ≤ n →
      Represented q w (value (F := F) q s) (delta s) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro s hs hw hn
      have hq : 0 < q := by have := field.two_le; omega
      have next (t : Tuple) (h : Precedes s t) (ht : Valid t) (wt : weight t = w) :
          Represented q w (value (F := F) q t) (delta t) := by
        have mem := (Dimension.mem_unrestricted w s).2 ⟨by rw [weight_sum,hw],hs⟩
        have lt : V s < V t := vectorRank_strict w _ _ s mem
          (by simp [delta, Ne.symm field.nontrivial]) (by
            intro z hz
            by_cases eq : t=z
            · rwa [← eq]
            · simp [delta,eq] at hz)
        have bound : V t ≤ N := vectorRank_bound w _
        exact ih (N - V t) (by omega) _ ht wt (Nat.le_refl _)
      by_cases tt : TT q s
      · refine ⟨.atom s,⟨tt,hw⟩,fun _ => rfl,[],by simp [Bounded],?_⟩
        intro t
        change 0 + scalar t s 0 = delta s t
        simp [scalar,zeroAdd]
      obtain ⟨h,t,he,hv,hb,tv⟩ := canonical_source_surjective q s hs tt
      have weightRow : weight h + weight t + q = w := by
        have hwt := source_weight q h t
        rw [he,hw] at hwt
        omega
      let e : Row q w := ⟨(h,t),hv,tv,weightRow⟩
      have rl := rep_L field e hb (law e) (fun u hu =>
        next u (he ▸ source_precedes_H q h t u hu) (H_valid q field.two_le h t hv tv u hu)
          (by have hwt := H_weight q hq h t u hu; omega))
      cases t with
      | nil =>
        simp only [L,start,List.map_cons,List.map_nil,List.nil_append,total,Arithmetic.addZero,e] at rl
        exact he ▸ rl
      | cons r t =>
        let other := h ++ q::r::t
        have ov : Valid other := by
          intro a ha
          rcases List.mem_append.mp ha with ha|ha
          · exact hv a ha
          · rcases List.mem_cons.mp ha with rfl|ha
            · exact hq
            · exact tv a ha
        have ow : weight other = w := by
          simp only [other,weight_append,weight] at ⊢
          simp only [weight] at weightRow
          omega
        have ot : Precedes s other := by
          left
          rw [← he]
          simp [other,source,depth]
        have sub := rep_scale (-(1:F)) (next other ot ov ow)
        have combined := rep_plus rl sub
        change Represented q w (fun k => (value q other k + (value q (source q h (r::t)) k + 0)) +
          (-(1:F))*value q other k)
          (fun j => (delta other j + (delta (source q h (r::t)) j + 0)) + (-(1:F))*delta other j) at combined
        simp only [Arithmetic.addZero,he] at combined
        have eliminate (a b : F) : a+b+(-1)*a = b := by rw [Arithmetic.addComm a b, erase_neg field]
        simpa only [eliminate] using combined
  exact loop (N-V s) s hs hw (Nat.le_refl _)

private theorem value_sum (q : Nat) (p : FormalSum F) (k : Int) :
    total (fun e : F × Tuple => e.1 * value q e.2 k) p = coefficient (evaluate q p) k := by
  induction p with
  | nil => cases k <;> rfl
  | cons e p ih =>
    rw [total,ih]
    cases k with
    | ofNat n => rfl
    | negSucc n => exact (Arithmetic.addZero _).trans (Arithmetic.mulZero _)

omit [Neg F] in
private theorem coord_sum (p : FormalSum F) (t : Tuple) :
    total (fun e : F × Tuple => e.1 * delta e.2 t) p = coordinates p t := by
  unfold coordinates
  simp only [delta_times]

/-- Lemma 2.4, analytic inclusion. A relation is written using actual
bounded-prefix rows of its own weight. The analytic inputs are precisely
the individual lifted rows and the polynomial-coefficient specialization
of the cited TT independence theorem. -/
theorem canonical_spanning (field : ConstantField F q) (indep : TTIndependent F q w)
    (law : ∀ e : Row q w, Identity (F := F) q (withCoeff 1 (L q e.val.1 e.val.2))
      (withCoeff 1 (H q e.val.1 e.val.2)))
    (v : Tuple → F) (hv : RelationVector q w v) :
    ∃ c : Rows F q w, component L c = v ∧ ∀ z ∈ c, ∀ a ∈ z.2.val.1, a ≤ q := by
  obtain ⟨p,⟨hw,hzero⟩,rfl⟩ := hv
  have expand := rep_sum (q := q) (w := w) p
    (fun z k => z.1 * value q z.2 k) (fun z t => z.1 * delta z.2 t)
    (fun z hz => rep_scale z.1 (rep_atom field law z.2 (hw z hz).1 (hw z hz).2))
  obtain ⟨e,et,ev,c,hb,hc⟩ := expand
  have vanish (k : Int) : readExpr q (value q) e k = 0 := by
    rw [ev]
    change total (fun z : F × Tuple => z.1 * value q z.2 k) p = 0
    rw [value_sum q p k]
    cases k with
    | ofNat n => exact hzero n
    | negSucc n => rfl
  refine ⟨c,funext (fun t => ?_),hb⟩
  simpa only [indep e et vanish t 0,Arithmetic.addZero,coord_sum] using hc t

/-- A summand (a,n,s) denotes a θⁿ Li(s). Index n is a natural number.
Independence over K=F(θ) implies the statement below by restriction to
F[θ]; conversely denominators can be cleared in each finite relation. -/
abbrev PolynomialTerms (F : Type u) := List (F × Nat × Tuple)

def polynomialValue (f : Tuple → Int → F) (p : PolynomialTerms F) (k : Int) : F :=
  total (fun z => z.1 * f z.2.2 (k+z.2.1)) p

def polynomialCoefficient (p : PolynomialTerms F) (s : Tuple) (n : Nat) : F :=
  total (fun z => if z.2.2 = s ∧ z.2.1 = n then z.1 else 0) p

/-- The usual polynomial form of the independence asserted in Theorem 1.2.
It only uses tuple indices, degrees in θ and coefficients in F. -/
def TTPolynomialIndependent (F : Type u) [Arithmetic F] [Neg F] (q w : Nat) : Prop :=
  ∀ p : PolynomialTerms F, (∀ z ∈ p, TT q z.2.2 ∧ weight z.2.2 = w) →
    (∀ k, polynomialValue (value q) p k = 0) → ∀ s n, polynomialCoefficient p s n = 0

private def timesMonomial (a : F) (n : Nat) (p : PolynomialTerms F) : PolynomialTerms F :=
  p.map (fun z => (a*z.1,n+z.2.1,z.2.2))

private def flatten (q : Nat) : Expression F → PolynomialTerms F
  | .zero => []
  | .atom s => [(1,0,s)]
  | .plus x y => flatten q x ++ flatten q y
  | .scale a x => timesMonomial a 0 (flatten q x)
  | .variableMul x => timesMonomial 1 1 (flatten q x) ++ timesMonomial (-1) q (flatten q x)

omit [Neg F] in
private theorem times_value (a : F) (n : Nat) (p : PolynomialTerms F) (f : Tuple → Int → F) (k : Int) :
    polynomialValue f (timesMonomial a n p) k = a * polynomialValue f p (k+n) := by
  induction p with
  | nil => exact (Arithmetic.mulZero _).symm
  | cons z p ih =>
    change (a*z.1)*f z.2.2 (k+((n+z.2.1:Nat):Int)) + polynomialValue f (timesMonomial a n p) k =
      a*(z.1*f z.2.2 (k+n+z.2.1) + polynomialValue f p (k+n))
    rw [ih,Arithmetic.distrib,Arithmetic.mulAssoc]
    simp only [Int.natCast_add,Int.add_assoc]

omit [Neg F] in
private theorem add_value (l r : PolynomialTerms F) (f : Tuple → Int → F) (k : Int) :
    polynomialValue f (l++r) k = polynomialValue f l k + polynomialValue f r k :=
  sum_append _ _ _

private theorem flatten_eval (e : Expression F) (q : Nat) (f : Tuple → Int → F) (k : Int) :
    polynomialValue f (flatten q e) k = readExpr q f e k := by
  induction e generalizing k with
  | zero => rfl
  | atom s =>
    change 1 * f s (k+(0:Nat)) + 0 = f s k
    simp [oneMul,Arithmetic.addZero]
  | plus a b ia ib => rw [flatten,add_value,ia,ib,readExpr]
  | scale a b ib => rw [flatten,times_value]; simp [ib,readExpr]
  | variableMul a ia => rw [flatten,add_value,times_value,times_value,oneMul]; simp [ia,readExpr]

omit [Neg F] in
private theorem times_support (a : F) (n : Nat) (p : PolynomialTerms F)
    (h : ∀ z ∈ p, TT q z.2.2 ∧ weight z.2.2 = w) :
    ∀ z ∈ timesMonomial a n p, TT q z.2.2 ∧ weight z.2.2 = w := by
  intro z hz
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hz
  exact h v hv

private theorem flatten_support (e : Expression F) (h : supported q w e) :
    ∀ z ∈ flatten q e, TT q z.2.2 ∧ weight z.2.2 = w := by
  induction e with
  | zero => simp [flatten]
  | atom s =>
    intro z hz
    obtain rfl := List.mem_singleton.mp hz
    exact h
  | plus a b ia ib =>
    intro z hz; exact (List.mem_append.mp hz).elim (ia h.1 z) (ib h.2 z)
  | scale c a ih => exact times_support _ _ _ (ih h)
  | variableMul a ih =>
    intro z hz
    exact (List.mem_append.mp hz).elim (times_support _ _ _ (ih h) z) (times_support _ _ _ (ih h) z)

omit [Neg F] in
private theorem scalar_eq_coefficient (p : PolynomialTerms F) (s : Tuple) (k : Int) :
    polynomialValue (scalar s) p k = if k ≤ 0 then polynomialCoefficient p s (-k).toNat else 0 := by
  induction p with
  | nil => simp [polynomialValue,polynomialCoefficient,total]
  | cons z p ih =>
    change z.1 * scalar s z.2.2 (k+z.2.1) + polynomialValue (scalar s) p k = _
    rw [ih]
    by_cases hk : k ≤ 0
    · simp only [if_pos hk,polynomialCoefficient,total]
      apply congrArg (· + _)
      by_cases hd : k+z.2.1 = 0
      · have hz : z.2.1 = (-k).toNat := by omega
        rw [show scalar s z.2.2 (k+z.2.1) = delta z.2.2 s from if_pos hd,delta_times]
        simp [hz]
      · have hz : z.2.1 ≠ (-k).toNat := by omega
        simp [scalar,hd,hz,Arithmetic.mulZero]
    · simp [hk,scalar,show k+(z.2.1:Int)≠0 by omega,Arithmetic.mulZero,Arithmetic.addZero]

/-- Restrict the standard coefficient-by-coefficient independence theorem
to expressions in the single scalar −D₁. No independence assumption on
the reduction algorithm occurs in this implication. -/
theorem independent_of_polynomial (h : TTPolynomialIndependent F q w) : TTIndependent F q w := by
  intro e he hz s k
  have vanish := h (flatten q e) (flatten_support e he) (fun n => (flatten_eval ..).trans (hz n))
  rw [← flatten_eval,scalar_eq_coefficient]
  split
  · apply vanish
  · rfl

theorem canonical_spanning_of_theorem_1_2 (field : ConstantField F q)
    (theorem12 : TTPolynomialIndependent F q w)
    (law : ∀ e : Row q w, Identity (F := F) q (withCoeff 1 (L q e.val.1 e.val.2))
      (withCoeff 1 (H q e.val.1 e.val.2)))
    (v : Tuple → F) (hv : RelationVector q w v) :
    ∃ c : Rows F q w, component L c = v ∧ ∀ z ∈ c, ∀ a ∈ z.2.val.1, a ≤ q :=
  canonical_spanning field (independent_of_polynomial theorem12) law v hv

/-- Constant component of a relation linear in D₁, as used in Lemma 3.1.
Multiplication by θ−θ^q contributes zero to the constant term of each
polynomial coefficient in the TT expansion. -/
theorem degree_one_projection (field : ConstantField F q) (indep : TTPolynomialIndependent F q w)
    (law : ∀ e : Row q w, Identity (F:=F) q (withCoeff 1 (L q e.val.1 e.val.2))
      (withCoeff 1 (H q e.val.1 e.val.2)))
    (p r : FormalSum F) (hp : homogeneous w p) (hr : homogeneous w r)
    (eqn : Identity q p r) :
    ∃ c : Rows F q w, Bounded c ∧ component L c=coordinates p := by
  have expand (l : FormalSum F) (hl : homogeneous w l) :
      Represented q w (coefficient (evaluate q l)) (coordinates l) := by
    have h := rep_sum l (fun z k => z.1*value q z.2 k) (fun z t => z.1*delta z.2 t)
      (fun z hz => rep_scale z.1 (rep_atom field law z.2 (hl z hz).1 (hl z hz).2))
    simpa only [value_sum,coord_sum] using h
  obtain ⟨a,sa,ea,c,cb,ec⟩ := expand p hp
  obtain ⟨d,sd,ed,_⟩ := expand r hr
  let e := Expression.plus a (.scale (-1:F) (.variableMul d))
  have hq := field.two_le
  have zero (k : Int) : readExpr q (value q) e k=0 := by
    have hx := (cleared_iff_laurent q (by omega) _ _).mp eqn k
    have eqa : coefficient (evaluate q p) k =
        coefficient (evaluate q r) (k+1) + (-1)*coefficient (evaluate q r) (k+q) := by
      rw [←hx,erase_neg field]
    simp only [e,readExpr,ea,ed,eqa,neg_mul field,oneMul,field.add_neg]
  have each := independent_of_polynomial indep e ⟨sa,sd⟩ zero
  refine ⟨c,cb,funext (fun t => ?_)⟩
  have ct := each t 0
  simp only [e,readExpr,Int.zero_add,no_positive (by omega : 0<q) d t 1 (by decide),
    no_positive (by omega : 0<q) d t q (by omega),Arithmetic.mulZero,Arithmetic.addZero] at ct
  simpa only [ct,Arithmetic.addZero] using ec t

end Megaera.TTSpanning
