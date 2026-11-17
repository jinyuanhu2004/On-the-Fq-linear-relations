import Megaera.FinalRemarkB
import Megaera.FinalTranslateProducts

/-! The two generating families in Remark 1.11 span the same operators,
on arbitrary pairs with nonempty support and over the same constants. -/
namespace Megaera.FinalRemarkBSpan
open Megaera.Finite Megaera.Paper Megaera.Carlitz Megaera.BinaryOperators Megaera.Shaped
open Megaera.FinalRemarkB
variable {F : Type u} [Arithmetic F] [Neg F] {q w : Nat}

/-- A pair of readings tests the two outputs independently. -/
abbrev Operator (F : Type u) [Arithmetic F] :=
  (P : BinaryPair F) → NonemptySupport P → (Tuple→F) → (Tuple→F) → F

def row (star : Bool) (u v : Tuple) : Operator F := fun P _ f g =>
  read f g ((if star then bStar else bOp) u (cOp v P))

/-- Homogeneous linear combinations of B_u C_v (or B*_u C_v). -/
inductive Span (star : Bool) (w : Nat) : Operator F → Prop
  | zero : Span star w (fun _ _ _ _ => 0)
  | gen (u v : Tuple) (vu : Valid u) (vv : Valid v) (wt : weight u+weight v=w) :
      Span star w (row star u v)
  | add {x y} : Span star w x → Span star w y →
      Span star w (fun p h f g => x p h f g+y p h f g)
  | scale (k : F) {x} : Span star w x → Span star w (fun p h f g => k*x p h f g)

omit [Neg F] in
theorem span_sum {star w} {A : Type v} (l : List A) (x : A→Operator F)
    (mem : ∀ i∈l,Span star w (x i)) :
    Span star w (fun p h f g => total (fun i => x i p h f g) l) := by
  induction l with
  | nil => exact .zero
  | cons a l ih => exact .add (mem a (by simp)) (ih (fun i hi => mem i (by simp [hi])))

private def push (a : Nat) (x : Operator F) : Operator F := fun p h f _ =>
  x p h (fun s => tri f [a] s) (fun s => dia f [a] s+tri f [a] s)

omit [Neg F] in
private theorem cCompose (f g : Tuple→F) (u v : Tuple) (p : BinaryPair F) (h : NonemptySupport p) :
    read f g (cOp u (cOp v p)) = total (fun s => read f g (cOp s p)) (quasiShuffle u v) := by
  obtain ⟨hl,hr⟩ := FinalTranslateProducts.weighted_cOp_cOp f g u v p h
  simp only [FinalRemarkB.read,hl,hr,sum_add]

/-- The C_u C_v correction consists of the single-prefix rows indexed
by the full quasi-shuffle of u and v, counting repetitions. -/
private def correction (a : Nat) (u v : Tuple) : Operator F := fun p h f g =>
  total (fun s => row false [a] s p h f g) (quasiShuffle u v)

omit [Neg F] in
private theorem correct_mem (star : Bool) (a : Nat) (u v : Tuple) (ha : 0<a)
    (vu : Valid u) (vv : Valid v) :
    Span (F:=F) star (a+(weight u+weight v)) (correction a u v) := by
  have mem (s) (hs : s∈quasiShuffle u v) :
      Span (F:=F) star (a+(weight u+weight v)) (row star [a] s) :=
    .gen _ _ (by simpa [Valid] using ha) (valid_quasiShuffle _ _ _ vu vv hs) (by simp [weight,weight_quasiShuffle _ _ _ hs])
  have all := span_sum _ _ mem
  cases star <;> exact all

omit [Neg F] in
private theorem split_row (a b : Nat) (u v : Tuple) :
    row (F:=F) false (a::b::u) v =
      fun p h f g => push a (row false (b::u) v) p h f g + correction a (b::u) v p h f g := by
  funext p h f g
  change read f g (bOp (a::b::u) (cOp v p))=_
  rw [replacement _ _ _ _ (cOp_nonempty _ _ h),read_B a [] f g,read_B a [] f g,cCompose _ _ _ _ _ h]
  unfold correction
  congr 1
  apply congrArg (fun k => total k (quasiShuffle (b::u) v))
  funext s
  exact (read_B a [] f g (cOp s p)).symm

omit [Neg F] in
private theorem push_star (a : Nat) (u v : Tuple) :
    push a (row (F:=F) true u v)=row true (a::u) v := by
  funext p h f g; exact (read_B a [] f g (bStar u (cOp v p))).symm

omit [Neg F] in
private theorem push_empty (a : Nat) (v : Tuple) :
    push a (row (F:=F) false [] v)=row false [a] v := by
  funext p h f g; exact (read_B a [] f g (cOp v p)).symm

private theorem push_closed (field : ConstantField F q) (star : Bool) (a : Nat) (ha : 0<a)
    {x : Operator F} (h : Span star w x) : Span star (a+w) (push a x) := by
  induction h with
  | zero => exact .zero
  | add _ _ hx hy => exact .add hx hy
  | scale k _ hx => exact .scale k hx
  | gen u v hu hv wt =>
    subst w
    cases star with
    | true =>
      rw [push_star]
      exact .gen _ _ (List.forall_mem_cons.mpr ⟨ha,hu⟩) hv (by simp [weight,Nat.add_assoc])
    | false =>
      cases u with
      | nil =>
        rw [push_empty]
        exact .gen _ _ (by simpa [Valid] using ha) hv (by simp [weight])
      | cons b u =>
        have rearr : push a (row (F:=F) false (b::u) v) =
            fun p h f g => row false (a::b::u) v p h f g + (-1)*correction a (b::u) v p h f g := by
          rw [split_row]
          funext p h f g
          rw [neg_mul field,oneMul,Arithmetic.addAssoc,field.add_neg,Arithmetic.addZero]
        rw [rearr]
        exact .add (.gen _ _ (List.forall_mem_cons.mpr ⟨ha,hu⟩) hv (by simp [weight,Nat.add_assoc]))
          (.scale (-1) (correct_mem false a _ _ ha hu hv))

private theorem star_row_mem (field : ConstantField F q) (u v : Tuple) (hu : Valid u) (hv : Valid v) :
    Span false (weight u+weight v) (row (F:=F) true u v) := by
  induction u with
  | nil => exact .gen [] v hu hv rfl
  | cons a u ih =>
    rw [←push_star,weight,Nat.add_assoc]
    exact push_closed field _ _ (hu a (by simp)) (ih (fun i hi => hu i (by simp [hi])))

private theorem ordinary_row_mem (field : ConstantField F q) (u v : Tuple) (hu : Valid u) (hv : Valid v) :
    Span true (weight u+weight v) (row (F:=F) false u v) := by
  induction u with
  | nil => exact .gen [] v hu hv rfl
  | cons a u ih =>
    cases u with
    | nil => exact .gen [a] v hu hv rfl
    | cons b u =>
      have ha := hu a (by simp)
      have vu := fun i (hi : i∈b::u) => hu i (by simp [hi])
      rw [split_row,weight,Nat.add_assoc]
      exact .add (push_closed field _ _ ha (ih vu)) (correct_mem true _ _ _ ha vu hv)

/-- Remark 1.11, as equality of the two spaces of actual binary operators
of each weight. It holds before applying an operator to any primitive. -/
theorem spans_equal (field : ConstantField F q) (w : Nat) (x : Operator F) :
    Span true w x ↔ Span false w x := by
  constructor
  · intro h; induction h with
    | zero => exact .zero
    | gen u v hu hv wt => exact wt ▸ star_row_mem field u v hu hv
    | add _ _ hx hy => exact .add hx hy
    | scale k _ hx => exact .scale k hx
  · intro h; induction h with
    | zero => exact .zero
    | gen u v hu hv wt => exact wt ▸ ordinary_row_mem field u v hu hv
    | add _ _ hx hy => exact .add hx hy
    | scale k _ hx => exact .scale k hx

end Megaera.FinalRemarkBSpan
