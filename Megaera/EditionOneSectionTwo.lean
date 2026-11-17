import Megaera.CanonicalBasis
import Megaera.ScalarKernel
import Megaera.MainTheorems
import Megaera.Singletons

/-! The explicit signed normal form and the terminal clause for f in the
proof of Theorem 2.8 of the final edition. The indexing in Theorem 2.9 is
read from the lengths of the left labels of the marked pairs. -/
namespace Megaera.EditionOneSectionTwo
open Megaera.Splitting Megaera.SplitKernel Megaera.IntegralKernel

private theorem chunk_positive_remainder (hq : 0<q) (k r : Nat) (hr : 0<r) (le : r≤q) :
    chunk q hq (q*k+r)=(k,List.replicate k q++[r]) := by
  induction k with
  | zero => simpa using chunk_small q hq r le
  | succ k ih =>
    rw [Nat.mul_succ,show q*k+q+r=q+(q*k+r) by omega,chunk_split q hq _ (by omega),ih]
    simp [List.replicate_succ]

private theorem expand_positive_remainders (hq : 0<q) (p : List (Nat × Nat))
    (hr : ∀ e∈p,0<e.2 ∧ e.2≤q) :
    expandTuple q hq (p.map (fun e => q*e.1+e.2)) =
      ((p.map Prod.fst).sum,p.flatMap (fun e => List.replicate e.1 q++[e.2])) := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    obtain ⟨h,l⟩ := hr e (by simp)
    simp only [List.map_cons,expandTuple,chunk_positive_remainder hq _ _ h l,
      ih (fun z hz => hr z (List.mem_cons_of_mem _ hz)),List.sum_cons,List.flatMap_cons]

/-- If the entries are q*kᵢ+rᵢ with 1 ≤ rᵢ ≤ q, the last remainder alone
decides whether the expansion vanishes. Otherwise its sign is the parity
of the total number of inserted q's. -/
theorem signed_normal_form (hq : 0<q) (p : List (Nat × Nat)) (k r : Nat)
    (bounds : ∀ e∈p,0<e.2 ∧ e.2≤q) (positive : 0<r) (le : r≤q) :
    normalize q hq ((p.map (fun e => q*e.1+e.2))++[q*k+r]) =
    if r=q then none else some (decide (((p.map Prod.fst).sum+k)%2=1),
      (p.flatMap (fun e => List.replicate e.1 q++[e.2]))++List.replicate k q++[r]) := by
  simp [normalize,expand_append,expand_positive_remainders hq p bounds,expandTuple,
    chunk_positive_remainder hq k r positive le,signedTerm,List.append_assoc]

/-- Euclidean decomposition with positive remainder, also at multiples of q. -/
theorem positive_remainder (hq : 0<q) (hs : 0<s) :
    s=q*((s-1)/q)+((s-1)%q+1) ∧ 0<(s-1)%q+1 ∧ (s-1)%q+1≤q := by
  have e := Nat.mod_add_div (s-1) q
  have le := Nat.mod_lt (s-1) hq
  omega

/-- Uniqueness of the positive-remainder expansion used in the formula for E. -/
theorem positive_remainder_unique (hq : 0<q) (k j r s : Nat)
    (hr : 0<r) (rq : r≤q) (hs : 0<s) (sq : s≤q) (eq : q*k+r=q*j+s) :
    k=j ∧ r=s := by
  have same := congrArg (fun n => (chunk q hq n).1) eq
  dsimp only at same
  rw [chunk_positive_remainder hq k r hr rq,chunk_positive_remainder hq j s hs sq] at same
  change k=j at same
  subst j
  exact ⟨rfl, Nat.add_left_cancel eq⟩

/-- The jth mark moves to j+1 after an earlier nonterminal split, also
for a terminal j. Positions here are one-based as in the paper. -/
theorem second_mark_after_split (h m : Tuple) (q r : Nat) :
    (h++q::r::m).length+1 = ((h++(q+r)::m).length+1)+1 := by
  simp [List.length_append]; omega

/-! The function f is a formal integral combination of marked pairs.
Its coefficients may therefore be reduced to any constant field. -/
local instance : Zero (Word Mark) := ⟨.zero⟩
local instance : Sub (Word Mark) := ⟨.minus⟩

def sectionRows (q : Nat) (hq : 0<q) : Tuple → Word Mark :=
  CanonicalBasis.extend q hq (fun _ => 0) (fun h t => .atom (h,t)) []

theorem rows_on_TT (hq : 0<q) (t : Tuple) (tt : TT q t) : sectionRows q hq t = .zero :=
  CanonicalBasis.on_TT q hq _ _ t tt

private theorem skip (hq : 0<q) (g : Tuple → Tuple → V) [Zero V] [Sub V]
    (p h t : Tuple) (hb : ∀ a∈h,a≤q) (hn : t≠[]) :
    CanonicalBasis.extend q hq (fun _ => 0) g p (h++t) =
    CanonicalBasis.extend q hq (fun _ => 0) g (p++h) t := by
  induction h generalizing p with
  | nil => simp
  | cons a h ih =>
    have ha := hb a (by simp)
    have nz : h++t≠[] := fun e => hn (List.append_eq_nil_iff.mp e).2
    rw [List.cons_append,CanonicalBasis.extend,if_neg (by omega),if_neg (fun c => nz c.2),
        ih (p++[a]) (fun x hx => hb x (by simp [hx]))]; simp

/-- The third branch in the revised definition of f. -/
theorem rows_terminal (hq : 0<q) (h : Tuple) (hb : ∀ a∈h,a≤q) :
    sectionRows q hq (h++[q]) = .atom (h,[]) := by
  unfold sectionRows
  rw [skip hq _ [] h [q] hb (by simp),List.nil_append,CanonicalBasis.extend,
    if_neg (by omega),if_pos ⟨rfl,rfl⟩]

/-- The second branch in the revised definition of f, with a genuine split. -/
theorem rows_split (hq : 0<q) (h t : Tuple) (r : Nat) (hr : 0<r) (hb : ∀ a∈h,a≤q) :
    sectionRows q hq (h++(q+r)::t) =
      .minus (.atom (h,r::t)) (sectionRows q hq (h++q::r::t)) := by
  unfold sectionRows
  rw [skip hq _ [] h ((q+r)::t) hb (by simp),skip hq _ [] h (q::r::t) hb (by simp),
    List.nil_append,CanonicalBasis.extend,if_pos (by omega),Nat.add_sub_cancel_left]
  have e : CanonicalBasis.extend q hq (fun _ => (0 : Word Mark)) (fun h t => .atom (h,t)) h (q::r::t) =
      CanonicalBasis.extend q hq (fun _ => (0 : Word Mark)) (fun h t => .atom (h,t)) (h++[q]) (r::t) := by
    rw [CanonicalBasis.extend,if_neg (by omega),if_neg (by simp)]
  rw [e]
  rfl

private theorem length_bound (s : Tuple) (valid : Valid s) : s.length≤weight s := by
  induction s with
  | nil => exact Nat.le_refl _
  | cons a t ih =>
    have pos := valid a (by simp)
    have l := ih (fun i hi => valid i (List.mem_cons_of_mem _ hi))
    simp only [weight,List.length_cons]; omega

private theorem image_sectionRows_value [Add V] [Sub V] [Zero V] [Neg V]
    (nz : -(0:V)=0) (nn : ∀ a : V, -(-a)=a)
    (self : ∀ a : V, a-a=0) (subZero : ∀ a : V, a-0=a)
    (exchange : ∀ a b c : V, (a+b)-(b-c)=a-(-c))
    (hq : 0<q) (s : Tuple) (hs : Valid s) (f : Tuple → V) :
    eval (fun ht : Mark => onRow q f ht.1 ht.2) (sectionRows q hq s) =
      f s - signedValue f (normalize q hq s) := by
  by_cases tt : TT q s
  · rw [rows_on_TT hq s tt,normalize_TT q hq s tt]
    simp [eval,signedValue,self]
  obtain ⟨h,t,he,_,hb,vt⟩ := canonical_source_surjective q s hs tt
  cases t with
  | nil =>
    change h++[q]=s at he
    rw [←he,rows_terminal hq h hb,normalize_terminal]
    simp [onRow,eval,signedValue,subZero]
  | cons r t =>
    have hr := vt r (by simp)
    change h++(q+r)::t=s at he
    have valid : Valid (h++q::r::t) := by
      intro a ha; rcases List.mem_append.mp ha with hm|hm
      · exact hs a (he ▸ List.mem_append_left _ hm)
      · exact (List.mem_cons.mp hm).elim (fun e => e ▸ hq) (vt a)
    have ih := image_sectionRows_value nz nn self subZero exchange hq (h++q::r::t) valid f
    rw [←he,rows_split hq h t r hr hb,normalize_split q hq h t r hr,signedValue_reverse nz nn]
    simp only [eval]
    rw [ih]
    exact exchange _ _ _
termination_by weight s-s.length
decreasing_by
  have d := length_bound _ valid
  rw [←he]
  simp only [weight_append,weight,List.length_append,List.length_cons] at d ⊢
  omega

/-- L f = id − E on every tuple, tested coefficientwise over the integers. -/
theorem image_sectionRows (hq : 0<q) (s : Tuple) (hs : Valid s) (x : Tuple) :
    eval (fun ht : Mark => ((L q ht.1 ht.2).map (fun t => if t=x then (1:Int) else 0)).sum)
      (sectionRows q hq s) =
      (if s=x then (1:Int) else 0) -
        signedValue (fun t => if t=x then (1:Int) else 0) (normalize q hq s) := by
  let f := fun t : Tuple => if t=x then (1:Int) else 0
  have rows : (fun ht : Mark => ((L q ht.1 ht.2).map f).sum) = (fun ht => onRow q f ht.1 ht.2) := by
    funext ⟨h,t⟩
    cases t <;> simp [L,start,onRow,Int.add_comm]
  rw [rows]
  exact image_sectionRows_value (by decide) Int.neg_neg (by intros; omega)
    (by intros; omega) (by intros; omega) hq s hs f

section
open Megaera.Finite Megaera.Carlitz Megaera.Paper
variable {F : Type u} [Arithmetic F] [Neg F]
local instance : Sub F := ⟨fun a b => a+(-b)⟩

/-- L f = id − E in the paper's coefficient field, using the coordinates
of the actual L-rows, including the one-term terminal row. -/
theorem image_sectionRows_field (field : ConstantField F q) (s : Tuple) (hs : Valid s) (x : Tuple) :
    let hq : 0<q := Nat.lt_of_lt_of_le (by decide) field.two_le
    eval (fun ht : Mark => coordinates (withCoeff (1:F) (L q ht.1 ht.2)) x) (sectionRows q hq s) =
      (if s=x then (1:F) else 0) - signedValue (fun t => if t=x then (1:F) else 0) (normalize q hq s) := by
  dsimp only
  let f := fun t : Tuple => if t=x then (1:F) else 0
  have rows : (fun ht : Mark => coordinates (withCoeff (1:F) (L q ht.1 ht.2)) x) =
      fun ht => onRow q f ht.1 ht.2 := by
    funext ⟨h,t⟩
    cases t <;> simp [coordinates,withCoeff,L,start,onRow,total,f,Arithmetic.addZero,zeroAdd,Arithmetic.addComm]
  rw [rows]
  letI : Std.Associative (α:=F) (·+·) := ⟨Arithmetic.addAssoc⟩
  letI : Std.Commutative (α:=F) (·+·) := ⟨Arithmetic.addComm⟩
  have nz := Singletons.nz field.add_neg
  refine image_sectionRows_value nz ?_ field.add_neg ?_ ?_ (Nat.lt_of_lt_of_le (by decide) field.two_le) s hs f
  · intro a
    calc
      -(-a) = -(-a)+(a+(-a)) := by rw [field.add_neg,Arithmetic.addZero]
      _ = ((-a)+(-(-a)))+a := by ac_rfl
      _ = a := by rw [field.add_neg,zeroAdd]
  · intro a; change a+(-0)=a; rw [nz,Arithmetic.addZero]
  · intro a b c; change (a+b)+(-(b+(-c)))=a+(-(-c))
    rw [Singletons.neg_add field.add_neg]
    calc _ = (a+(b+(-b)))+(-(-c)) := by ac_rfl
         _ = _ := by rw [field.add_neg,Arithmetic.addZero]
end


/-- Split at a zero-based coordinate; the terminal mark at q leaves its
tuple fixed. Only admissible coordinates occur in the identities below. -/
def splitAtSite (q : Nat) : Nat → Tuple → Tuple
  | _, [] => []
  | 0, a::s => if q<a then q::(a-q)::s else a::s
  | i+1, a::s => a::splitAtSite q i s

private theorem split_at_label (q : Nat) (h t : Tuple) (r : Nat) (hr : 0<r) :
    splitAtSite q h.length (h++(q+r)::t) = h++q::r::t := by
  induction h with
  | nil => simp [splitAtSite,hr,Nat.add_sub_cancel_left]
  | cons a h ih => simp [splitAtSite,ih]

/-- The commuting double split on p. 12, tracking the new coordinate of
the later mark. Here i and j are encoded by the two prefix lengths. -/
theorem commuting_double_split (q : Nat) (p m t : Tuple) (r c : Nat)
    (hr : 0<r) (hc : 0<c) :
    let s := p++(q+r)::(m++(q+c)::t)
    let j := (p++(q+r)::m).length
    splitAtSite q p.length (splitAtSite q j s) =
      splitAtSite q (j+1) (splitAtSite q p.length s) := by
  dsimp only
  have eq₁ := split_at_label q (p++(q+r)::m) t c hc
  have eq₂ := split_at_label q (p++q::r::m) t c hc
  have shift : (p++(q+r)::m).length+1=(p++q::r::m).length := by simp; omega
  simp only [List.append_assoc,List.cons_append,List.nil_append] at eq₁ eq₂
  rw [eq₁,split_at_label q p _ r hr,split_at_label q p _ r hr,shift,eq₂]

/-- A scalar-labelled mark in the quotient by the relations of weight w. -/
def rowClass [Zero F] [Add F] (q w : Nat) (k : F) (h t : Tuple) :
    Presented (ScalarKernel.RowsAt F q w) :=
  cls _ (.atom (k,h,t))

private theorem signed_square {A : Type} (rel : Word A → Word A → Prop)
    (a b c d : Presented rel) (sq : a+c=b+d) : a-b=d-c := by
  have cancel (u v z : Presented rel) (e : u+z=v+z) : u=v := by
    calc
      u = (u+z)-z := ((laws rel).add_sub ..).symm
      _ = (v+z)-z := congrArg (·-z) e
      _ = v := (laws rel).add_sub ..
  apply cancel _ _ b
  rw [(laws rel).sub_add]
  apply cancel _ _ c
  rw [sq]
  calc
    b+d = d+b := Std.Commutative.comm ..
    _ = ((d-c)+c)+b := by rw [(laws rel).sub_add]
    _ = ((d-c)+b)+c := by ac_rfl

/-- Corrected equation (2.4) in the square case. The four terms are
E(s), E_i(s), E_{i+1}(s^cano), and E(s^i), respectively. -/
theorem equation_2_4_split [Zero F] [Add F] (q w : Nat) (k : F) (p m t : Tuple)
    (r c : Nat) (hp : Valid p) (hm : Valid m) (ht : Valid t)
    (hr : 0<r) (hc : 0<c) (wt : weight (p++(q+r)::(m++(q+c)::t))=w) :
    rowClass q w k p (r::(m++(q+c)::t)) - rowClass q w k (p++(q+r)::m) (c::t) =
      rowClass q w k (p++q::r::m) (c::t) - rowClass q w k p (r::(m++q::c::t)) := by
  apply signed_square
  apply Quotient.sound
  apply Derives.rule
  refine ⟨ScalarKernel.Rows.square k p m t r c hp hm ht hr hc,?_,?_⟩
  all_goals
    simp only [ScalarKernel.homogeneous,ScalarKernel.markWeight,weight,weight_append] at wt ⊢
    exact ⟨by omega,by omega⟩

/-- Corrected equation (2.4) at a terminal second mark. The triangle has
no term E(s^i), while the terminal mark still shifts by one position. -/
theorem equation_2_4_terminal [Zero F] [Add F] (q w : Nat) (k : F) (p m : Tuple)
    (r : Nat) (hp : Valid p) (hm : Valid m) (hr : 0<r)
    (wt : weight (p++(q+r)::(m++[q]))=w) :
    rowClass q w k p (r::(m++[q])) - rowClass q w k (p++(q+r)::m) [] =
      rowClass q w k (p++q::r::m) [] := by
  have tri : rowClass q w k p (r::(m++[q])) =
      rowClass q w k (p++(q+r)::m) [] + rowClass q w k (p++q::r::m) [] := by
    apply Quotient.sound
    apply Derives.rule
    refine ⟨ScalarKernel.Rows.triangle k p m r hp hm hr,?_,?_⟩
    · change weight p+q+weight (r::(m++[q]))=w
      simp only [weight,weight_append] at wt ⊢
      omega
    · simp only [ScalarKernel.homogeneous,ScalarKernel.markWeight,weight,weight_append] at wt ⊢
      exact ⟨by omega,by omega⟩
  rw [tri,Std.Commutative.comm (a := rowClass q w k (p++(q+r)::m) [])
    (b := rowClass q w k (p++q::r::m) []) (op := (· + ·)),(laws _).add_sub]

end Megaera.EditionOneSectionTwo
