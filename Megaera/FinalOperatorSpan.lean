import Megaera.Convolution

/-! Corollary 2.12 as equality of the two homogeneous spans in the space
of formal pairs, before lifting. Empty seeds can be allowed in this purely
algebraic identity, independently of the nonempty primitive indices of BCP. -/
namespace Megaera.FinalOperatorSpan
open Megaera.Finite Megaera.Paper Megaera.Cuts Megaera.Convolution
variable {F : Type u} [Arithmetic F] [Neg F] {q w : Nat}

local instance : Zero (Bool → Tuple → F) := ⟨fun _ _ => 0⟩
local instance : Add (Bool → Tuple → F) := ⟨fun f g b s => f b s+g b s⟩
local instance : Sub (Bool → Tuple → F) := ⟨fun f g b s => f b s+ -g b s⟩

/-- Finite linear span of a specified two-column family at weight w. -/
inductive Span (F : Type u) [Arithmetic F] [Neg F] (q w : Nat) (emptySeed : Bool)
    (family : Tuple → Tuple → BinaryPair F) : (Bool → Tuple → F) → Prop where
  | zero : Span F q w emptySeed family 0
  | atom (s t : Tuple) (svalid : Valid s) (tvalid : Valid t)
      (seed : emptySeed=true ∨ s≠[]) (weightEq : weight s+weight t+2*q=w) :
      Span F q w emptySeed family (pairCoordinates (family s t))
  | add {f g} : Span F q w emptySeed family f → Span F q w emptySeed family g →
      Span F q w emptySeed family (f+g)
  | sub {f g} : Span F q w emptySeed family f → Span F q w emptySeed family g →
      Span F q w emptySeed family (f-g)
  | scale (a : F) {f} : Span F q w emptySeed family f →
      Span F q w emptySeed family (fun b s => a*f b s)

private theorem finite_sum {α : Type v} {e : Bool} {fam : Tuple → Tuple → BinaryPair F}
    (l : List α) (f : α → Bool → Tuple → F) (mem : ∀ a∈l,Span F q w e fam (f a)) :
    Span F q w e fam (sumRows l f) := by
  induction l with
  | nil => exact .zero
  | cons a l ih => exact .add (mem a (by simp)) (ih (fun z hz => mem z (List.mem_cons_of_mem _ hz)))

private theorem cut_label {s t x : Tuple} {p : Tuple × Tuple} {e : Bool}
    (vs : Valid s) (vt : Valid t) (seed : e=true ∨ s≠[]) (wt : weight s+weight t+2*q=w)
    (cut : p∈cuts t) (mem : x∈quasiShuffle s p.1) :
    Valid x ∧ Valid p.2 ∧ (e=true ∨ x≠[]) ∧ weight x+weight p.2+2*q=w := by
  have join := pieces_append cut
  have vp : Valid p.1 := fun a ha => vt a (join ▸ List.mem_append_left _ ha)
  have vsuf : Valid p.2 := fun a ha => vt a (join ▸ List.mem_append_right _ ha)
  have wx := weight_quasiShuffle s p.1 x mem
  have wc := congrArg weight join
  rw [weight_append] at wc
  refine ⟨valid_quasiShuffle _ _ _ vs vp mem,vsuf,?_,by omega⟩
  rcases seed with he|hs
  · exact .inl he
  · right
    intro xn
    rw [xn] at wx
    cases s with
    | nil => exact hs rfl
    | cons a s =>
      have pos := vs a (by simp)
      simp only [weight] at wx
      omega

private theorem convolution (q : Nat) (s t : Tuple) :
    pairCoordinates (cOp t (primitive (K:=F) q s)) =
    sumRows (cuts t) (fun p => sumRows (quasiShuffle s p.1) (fun x => pairCoordinates (generalP q x p.2))) :=
  read_convolution coordinates_reading (fun _ => funext (fun _ => funext (fun _ => zeroAdd _)))
    (fun _ _ _ => funext (fun _ => funext (fun _ => Arithmetic.addAssoc _ _ _))) q s t

private theorem translate_in_general {e : Bool} (s t : Tuple) (vs : Valid s) (vt : Valid t)
    (seed : e=true ∨ s≠[]) (wt : weight s+weight t+2*q=w) :
    Span F q w e (generalP q) (pairCoordinates (cOp t (primitive q s))) := by
  rw [convolution]
  apply finite_sum
  intro p hp
  apply finite_sum
  intro x hx
  obtain ⟨vx,vy,b,h⟩ := cut_label vs vt seed wt hp hx
  exact .atom _ _ vx vy b h

/-- Each individual generalized primitive pair has a homogeneous expression
in the translates of the one-argument primitive pairs. For e=true the
expression may include a translate of the empty primitive. -/
theorem general_in_translates (field : ConstantField F q) (e : Bool) (s t : Tuple)
    (vs : Valid s) (vt : Valid t) (seed : e=true ∨ s≠[]) (wt : weight s+weight t+2*q=w) :
    Span F q w e (fun a b => cOp b (primitive q a)) (pairCoordinates (generalP q s t)) := by
  induction n : t.length using Nat.strongRecOn generalizing s t with
  | ind n ih =>
    cases t with
    | nil => exact .atom _ _ vs vt seed wt
    | cons b t =>
      let read (s t : Tuple) := pairCoordinates (generalP (K:=F) q s t)
      let rest := sumRows ((cuts t).map fun p => (b::p.1,p.2))
        (fun p => sumRows (quasiShuffle s p.1) (fun x => read x p.2))
      have hrest : Span F q w e (fun a b => cOp b (primitive q a)) rest := by
        apply finite_sum
        intro p hp
        obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hp
        apply finite_sum
        intro x hx
        have iscut : (b::j.1,j.2)∈cuts (b::t) :=
          List.mem_cons_of_mem _ (List.mem_map.mpr ⟨j,hj,rfl⟩)
        obtain ⟨vx,vy,bz,h⟩ := cut_label vs vt seed wt iscut hx
        have l := congrArg List.length (pieces_append hj)
        simp only [List.length_append] at l
        simp only [List.length_cons] at n
        exact ih j.2.length (by omega) x j.2 vx vy bz h rfl
      have cv := convolution (F:=F) q s (b::t)
      have az (z : Bool→Tuple→F) : z+0=z :=
        funext (fun _ => funext (fun _ => Arithmetic.addZero _))
      simp only [cuts,sumRows,quasiShuffle_nil_right,az] at cv
      change pairCoordinates (cOp (b::t) (primitive (K:=F) q s))=read s (b::t)+rest at cv
      have z := Span.sub (Span.atom (F:=F) (family:=fun a b => cOp b (primitive q a))
        s (b::t) vs vt seed wt) hrest
      change Span _ _ _ _ _ (pairCoordinates (cOp (b::t) (primitive q s))-rest) at z
      rw [cv] at z
      have cancel : read s (b::t)+rest-rest=read s (b::t) := by
        funext side u
        change (_+rest side u)+ -rest side u=_
        rw [Arithmetic.addAssoc,field.add_neg,Arithmetic.addZero]
      rwa [cancel] at z

/-- Both directions of Corollary 2.12 before lifting. The parameter e
selects either all valid formal labels or the nonempty BCP primitive labels. -/
theorem corollary_2_12 (field : ConstantField F q) (e : Bool) (v : Bool→Tuple→F) :
    Span F q w e (generalP q) v ↔ Span F q w e (fun s t => cOp t (primitive q s)) v := by
  constructor
  · intro h
    induction h with
    | zero => exact .zero
    | atom s t vs vt se wt => exact general_in_translates field e s t vs vt se wt
    | add _ _ ih jh => exact .add ih jh
    | sub _ _ ih jh => exact .sub ih jh
    | scale a _ ih => exact .scale a ih
  · intro h
    induction h with
    | zero => exact .zero
    | atom s t vs vt se wt => exact translate_in_general s t vs vt se wt
    | add _ _ ih jh => exact .add ih jh
    | sub _ _ ih jh => exact .sub ih jh
    | scale a _ ih => exact .scale a ih

end Megaera.FinalOperatorSpan
