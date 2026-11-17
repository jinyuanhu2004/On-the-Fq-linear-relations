import Megaera.FourLambda
import Megaera.FourReduction
import Megaera.FourMinimum

/-! A family testing the invariance claim on page 24. For q ≥ 3 the
Case II data s = ∅ and t′ = (1,q+1,1) have n = 0, b = 1.
The detector therefore reads one tuple coordinate. -/
namespace Megaera.FourInvariant
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.FourLambda
open Megaera.Triangular Megaera.FourReduction
variable {F : Type u} [Arithmetic F] [Neg F]

/-- In the one-entry tail, an overflow has no earlier entry to receive it. -/
theorem one_entry (field : ConstantField F q) (x : Nat) :
    lambda (F:=F) q field.two_le 0 1 (entries []) (entries [x]) =
       if x=1 then 1 else 0 := by
  unfold lambda
  change extend (q-1) _ 0 1 1 _ x _ = _
  rw [extend]
  split
  · rename_i h; simp [shifts,Singletons.nz field.add_neg,show x≠1 by omega]
  · split <;> rfl

/-- This is the coefficient with prefix (1,1,2q) paired with λ at
b=1 and n=0. The full finite sum collapses to the tail (1). -/
def detector (q : Nat) (v : Tuple → F) := v [1,1,2*q,1]

/-- On a finite presentation, the indicator for the residue class and
the λ-weight reduce to the coordinate (1,1,2q,1). -/
theorem reads_detector (q c₀ : Nat) (field : ConstantField F q) (p : FormalSum F) :
    total (fun e => match e.2 with
      | [a,b,c,z] => if a=1 ∧ b=1 ∧ c=c₀ ∧ z%(q-1)=1%(q-1) then
          e.1 * lambda q field.two_le 0 1 (entries []) (entries [z]) else 0
      | _ => 0) p = coordinates p [1,1,c₀,1] := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    rcases e with ⟨k,t⟩
    rw [total,ih]
    change _ + _ = (if t=[1,1,c₀,1] then k else 0) + _
    apply congrArg (· + _)
    cases t with
    | nil => simp
    | cons a t =>
      cases t with
      | nil => simp
      | cons b t =>
        cases t with
        | nil => simp
        | cons c t =>
          cases t with
          | nil => simp
          | cons z t =>
            cases t with
            | cons => simp
            | nil =>
              simp only [one_entry field,List.cons.injEq,and_true]
              by_cases h : a=1 ∧ b=1 ∧ c=c₀ ∧ z=1
              · rcases h with ⟨rfl,rfl,rfl,rfl⟩; simp [Arithmetic.mulOne]
              · by_cases hz : z=1
                · subst z; simp_all [Arithmetic.mulZero,Arithmetic.mulOne]
                · simp [hz,Arithmetic.mulZero]

/-- The genuine Type II generator contributes minus one to this
coefficient, entirely from the shifted (negative) component. -/
theorem typeII_value (q : Nat) (hq : 3≤q) :
    detector q (coordinates (liftPair (generalP (K:=F) q [1] [1,1]))) = -(1:F) := by
  have neq : q ≠ 1 := by omega
  simp [detector,coordinates,liftPair,generalP,H,L,endings,incLast,concatenate,
    start,quasiShuffle,withCoeff,total,neq,Arithmetic.addZero,zeroAdd,
    show q+2 ≠ 1 by omega, show q+1 ≠ 1 by omega,
    show q-1+(q+1)=2*q by omega, show q-1≠0 by omega]

private theorem neg_one_ne_zero (field : ConstantField F q) : -(1:F) ≠ 0 := by
  intro he
  have a := field.add_neg 1
  rw [he,Arithmetic.addZero] at a
  exact field.nontrivial a.symm

private theorem least_of_unit (field : ConstantField F q) {g : Tuple → F} {s : Tuple}
    (h : FourMinimum.UnitMinimum g s) : Least g s := by
  refine ⟨fun k => field.nontrivial (k ▸ h.1), fun t ht => ?_⟩
  rcases precedes_trichotomy s t with lt | eq | lt
  · exact .inr lt
  · exact .inl eq.symm
  · exact False.elim (ht (h.2 t lt))

/-- A Type II row with minimum strictly later than the proposed cutoff,
yet with nonzero value for the actual λ-detector. -/
theorem typeII_obstruction (q : Nat) (hq : 3≤q) (field : ConstantField F q) :
    let g := liftP (F:=F) q [] [1] [1,1]
    Special F q (2*q+3) g ∧ Least g [q+2,1,q] ∧
    Precedes [q+1,q+1,1] [q+2,1,q] ∧ detector q g ≠ 0 := by
  dsimp only
  refine ⟨.general [] [1] [1,1] (by simp [Valid]) (by simp [Valid]) (by simp)
    (by simp [Valid]) (by simp [weight]; omega),?_,.inr ⟨rfl,.rel (by omega)⟩,?_⟩
  · apply least_of_unit field
    have h := FourMinimum.lemma_4_1_i_ii (F:=F) q field.two_le [] [1] [1,1] (by simp)
    simpa [FourMinimum.raiseFirst,FourMinimum.addLast,incLast,show q-1+1=q by omega,
      liftP,FourMinimum.lifted] using h
  · change detector q (coordinates (liftPair (generalP (K:=F) q [1] [1,1]))) ≠ 0
    rw [typeII_value _ hq]; exact neg_one_ne_zero field

/-- For t′=(1,q+2,1) the same singleton λ reads (1,1,2q+1,1).
Here a genuine Type III difference also gives a nonzero contribution. -/
theorem typeIII_value (q : Nat) (hq : 3≤q) (field : ConstantField F q) :
    let x : Tuple := [1,1,2*q+1,1]
    liftP (F:=F) q [] [1] [2,1] x + -liftP q [] [2,1] [1] x = -(1:F) := by
  dsimp only
  simp [liftP,coordinates,bStar,liftPair,generalP,H,L,endings,incLast,concatenate,
    start,quasiShuffle,withCoeff,total,Arithmetic.addZero,zeroAdd,Singletons.nz field.add_neg,
    show q≠1 by omega, show q≠0 by omega, show q-1≠0 by omega, show q-1+(q+2)=2*q+1 by omega]

theorem typeIII_obstruction (q : Nat) (hq : 3≤q) (field : ConstantField F q) :
    let g := fun x => liftP (F:=F) q [] [1] [2,1] x + -liftP q [] [2,1] [1] x
    Special F q (2*q+4) g ∧ Least g [q+2,q+1,1] ∧
    Precedes [q+1,q+2,1] [q+2,q+1,1] ∧ g [1,1,2*q+1,1] ≠ 0 := by
  dsimp only
  refine ⟨.difference [] [1] [1] [1] (by simp [Valid]) (by simp [Valid]) (by simp)
    (by simp [Valid]) (by simp) (by simp [Valid]) (by simp [weight]; omega),?_,
    .inr ⟨rfl,.rel (by omega)⟩,?_⟩
  · apply least_of_unit field
    have h := FourMinimum.lemma_4_1_iii q field [] [1] [1] [1] (by simp) (by simp)
    simpa [FourMinimum.raiseFirst,FourMinimum.addLast,incLast,liftP,FourMinimum.lifted] using h
  · rw [typeIII_value q hq field]; exact neg_one_ne_zero field

omit [Neg F] in
private theorem peel_shifts (d i k : Nat) (f : Coordinates → F) (x : Coordinates) :
    shifts d i f (k+1) x = shifts d (i+1) f k x + f (bump d i x) := by
  induction k with
  | zero => simp [shifts,zeroAdd]
  | succ k ih =>
    change (shifts d i f (k+1) x + _) = ((shifts d (i+1) f k x + _) + _)
    rw [ih,show i+1+k=i+(k+1) by omega]
    letI : Std.Associative (α:=F) (·+·) := ⟨Arithmetic.addAssoc⟩
    letI : Std.Commutative (α:=F) (·+·) := ⟨Arithmetic.addComm⟩
    ac_rfl

private theorem modify_at_join (p : Tuple) (a d : Nat) (t : Tuple) :
    (p ++ a::t).modify p.length (·+d) = p ++ (a+d)::t := by
  induction p with
  | nil => rfl
  | cons b p ih => simp [ih]

omit [Neg F] in
/-- Merge terms of the actual singleton stuffle realize shifts on the suffix
after p, with their multiplicities. -/
theorem merge_reading (d : Nat) (p t : Tuple) (f : Coordinates → F) :
    total (fun z => f (entries (p++z))) (FourMinimum.merges d t) =
      shifts d p.length f t.length (entries (p++t)) := by
  induction t generalizing p with
  | nil => rfl
  | cons a t ih =>
    rw [FourMinimum.merges,total_append',total_map]
    simp only [total,Arithmetic.addZero,List.length_cons,peel_shifts]
    have match₁ := ih (p++[a])
    simp only [List.length_append,List.length_cons,List.length_nil,Nat.zero_add,List.append_assoc,
      List.singleton_append] at match₁
    rw [match₁,Nat.add_comm d a,←modify_at_join,entries_modify _ _ _ (by simp)]

omit [Neg F] in
/-- Reading the layer whose depth equals that of t removes all insertion
terms and keeps every merge. The formula works for the empty suffix t too:
its unique stuffle term has depth one. -/
theorem stuffle_reading (d : Nat) (p t : Tuple) (f : Coordinates → F) :
    total (fun z => if z.length=t.length then f (entries (p++z)) else 0)
      (quasiShuffle [d] t) = shifts d p.length f t.length (entries (p++t)) := by
  obtain ⟨long,hperm,hlen⟩ := FourMinimum.stuffle_layer d t
  rw [BCPRows.permSum _ hperm,total_append']
  have restrict (s : List Tuple) (h : ∀ z∈s,z.length=t.length) :
      total (fun z => if z.length=t.length then f (entries (p++z)) else 0) s =
      total (fun z => f (entries (p++z))) s := by
    induction s with
    | nil => rfl
    | cons z s ih =>
      simp only [total,if_pos (h z (by simp)),ih (fun y hy => h y (by simp [hy]))]
  have discard (s : List Tuple) (h : ∀ z∈s,t.length<z.length) :
      total (fun z => if z.length=t.length then f (entries (p++z)) else 0) s = 0 := by
    induction s with
    | nil => rfl
    | cons z s ih =>
      simp only [total,if_neg (Nat.ne_of_gt (h z (by simp))),ih (fun y hy => h y (by simp [hy])),
        Arithmetic.addZero]
  rw [restrict _ (fun _ hv => FourMinimum.merges_length hv),discard _ hlen,Arithmetic.addZero,
    merge_reading]

/-- On the selected depth, the full singleton product is killed by λ when
p ends at the marker (p is empty here), or strictly beyond the marker
(p ends in an entry greater than one). The residue restriction is built
into λ by wrong_residue. This applies to the negative part with the
remaining tuple t=(u,q⁺v) as well as to the positive part. -/
theorem suffix_stuffle_zero (q : Nat) (field : ConstantField F q) (n b : Nat)
    (v p t : Tuple) (hlen : p.length+t.length=n+1)
    (hb : b ≤ q-1) (hx : 0 < entries (p++t) n)
    (hp : p=[] ∨ 1 < entries (p++t) (p.length-1)) :
    total (fun z => if z.length=t.length then
      lambda (F:=F) q field.two_le n b (entries v) (entries (p++z)) else 0)
      (quasiShuffle [q-1] t) = 0 := by
  rw [stuffle_reading]
  rcases hp with e | he
  · subst p
    simp only [List.length_nil,Nat.zero_add,List.nil_append] at hlen hx ⊢
    rw [hlen]
    exact full_sum field n b _ _ hb hx
  · by_cases em : t=[]
    · subst t; rfl
    · by_cases ep : p=[]
      · subst p
        simp only [List.length_nil,Nat.zero_add,List.nil_append] at hlen hx ⊢
        rw [hlen]; exact full_sum field n b _ _ hb hx
      · have pt : 0<p.length := List.length_pos_iff.mpr ep
        have tt : 0<t.length := List.length_pos_iff.mpr em
        have hv := suffix_sum field n b (p.length-1) (entries v) (entries (p++t)) hb hx
          (by omega) he
        simpa only [show p.length-1+1=p.length by omega,show n-(p.length-1)=t.length by omega] using hv

end Megaera.FourInvariant
