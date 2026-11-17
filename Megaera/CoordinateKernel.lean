import Megaera.ScalarKernel
import Megaera.RowEvaluation

/-! Passing from the actual coefficient map of L to its presentation, with
no assumption that vanishing coefficients already imply a formal derivation. -/
namespace Megaera.CoordinateKernel
open Megaera.IntegralKernel Megaera.Carlitz Megaera.Finite

variable {F : Type} [Arithmetic F]

def listWord (p : List A) : Word A :=
  p.foldr (fun a b => .plus (.atom a) b) .zero

private abbrev V (F : Type) [Arithmetic F] := Presented (ScalarKernel.Collect F Tuple)

private def basis (k : F) (t : Tuple) : V F :=
  cls (ScalarKernel.Collect F Tuple) (.atom (k,t))

private theorem basis_zero (t : Tuple) : basis (0:F) t = 0 :=
  Quotient.sound (Derives.rule (ScalarKernel.Collect.zero _))

private theorem basis_add (a b : F) (t : Tuple) : basis (a+b) t = basis a t + basis b t :=
  Quotient.sound (Derives.rule (ScalarKernel.Collect.add ..))

private def totalV (f : A → V F) : List A → V F
  | [] => 0
  | x::xs => f x + totalV f xs

private theorem zero_addV (b : V F) : 0+b=b := by
  calc
    0+b=b+0 := by ac_rfl
    _=b := addZero b

private theorem totalV_add (l : List A) (f g : A → V F) :
    totalV (fun s => f s + g s) l = totalV f l + totalV g l := by
  induction l with
  | nil => exact (addZero 0).symm
  | cons a l ih => simp only [totalV,ih]; ac_rfl

private theorem totalV_zero (l : List A) : totalV (fun _ => (0 : V F)) l = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [totalV,ih,addZero]

private theorem point (l : List Tuple) (hn : l.Nodup) (s : Tuple) (z : V F) :
    totalV (fun t => if s=t then z else 0) l = if s ∈ l then z else 0 := by
  induction l with
  | nil => simp [totalV]
  | cons a l ih =>
    obtain ⟨ha,hl⟩ := List.nodup_cons.mp hn
    by_cases he : s=a
    · subst s; simp [totalV,ih hl,ha,addZero]
    · simp [totalV,ih hl,he,zero_addV]

omit [Arithmetic F] in
private theorem support (p : FormalSum F) : ∃ l : List Tuple, l.Nodup ∧ ∀ e ∈ p, e.2 ∈ l := by
  induction p with
  | nil => exact ⟨[],by simp,by simp⟩
  | cons e p ih =>
    obtain ⟨l,hn,hl⟩ := ih
    by_cases h : e.2 ∈ l
    · exact ⟨l,hn,fun z hz => (List.mem_cons.mp hz).elim (fun he => he ▸ h) (hl z)⟩
    · exact ⟨e.2::l,List.nodup_cons.mpr ⟨h,hn⟩,fun z hz =>
        (List.mem_cons.mp hz).elim (fun he => he ▸ List.mem_cons_self) (fun hm => List.mem_cons_of_mem _ (hl z hm))⟩

private theorem canonical (p : FormalSum F) (l : List Tuple) (hn : l.Nodup)
    (hs : ∀ e ∈ p, e.2 ∈ l) : totalV (fun t => basis (coordinates p t) t) l =
    cls (ScalarKernel.Collect F Tuple) (listWord p) := by
  induction p with
  | nil => simp only [coordinates,Finite.total,basis_zero,totalV_zero]; rfl
  | cons e p ih =>
    have elem (t : Tuple) : basis (coordinates (e::p) t) t =
        (if e.2=t then basis e.1 e.2 else 0) + basis (coordinates p t) t := by
      change basis ((if e.2=t then e.1 else 0) + coordinates p t) t = _
      split <;> rename_i h
      · subst t; rw [basis_add]
      · rw [basis_add,basis_zero]
    simp only [elem,totalV_add,point l hn,if_pos (hs e (by simp)),ih (fun z hz => hs z (List.mem_cons_of_mem _ hz))]
    rfl

/-- Vanishing of all tuple coefficients in the coefficient field implies
equality to zero in the presentation of the free tuple module. -/
theorem collect_of_coordinates_zero (p : FormalSum F) (hp : ∀ s, coordinates p s = 0) :
    Derives (ScalarKernel.Collect F Tuple) (listWord p) .zero := by
  obtain ⟨l,hn,hs⟩ := support p
  have h := canonical p l hn hs
  simp only [hp,basis_zero,totalV_zero] at h
  exact Quotient.exact h.symm

/-- This word is the given list of homogeneous admissible marked rows. -/
def rowWord {q w : Nat} (c : Paper.Rows F q w) : Word (F × Mark) :=
  listWord (c.map (fun z => (z.1,z.2.val)))

private theorem listWord_join (p r : FormalSum F) :
    cls (ScalarKernel.Collect F Tuple) (listWord (p++r)) =
      cls (ScalarKernel.Collect F Tuple) (listWord p) + cls (ScalarKernel.Collect F Tuple) (listWord r) := by
  induction p with
  | nil => exact (zero_addV _).symm
  | cons a p ih =>
    change basis a.1 a.2 + cls _ (listWord (p++r)) = (basis a.1 a.2 + cls _ (listWord p)) + _
    rw [ih]; ac_rfl

private theorem image_rows {q w : Nat} (c : Paper.Rows F q w) :
    cls (ScalarKernel.Collect F Tuple) (ScalarKernel.image q (rowWord c)) =
    cls (ScalarKernel.Collect F Tuple) (listWord (RowEvaluation.presentation L c)) := by
  induction c with
  | nil => rfl
  | cons e c ih =>
    obtain ⟨k,⟨⟨h,t⟩,ok⟩⟩ := e
    change cls _ (ScalarKernel.image q (.atom (k,h,t))) + cls _ (ScalarKernel.image q (rowWord c)) =
      cls _ (listWord (withCoeff k (L q h t) ++ RowEvaluation.presentation L c))
    rw [ih,listWord_join]
    apply congrArg (· + _)
    cases t with
    | nil =>
      change basis k _ = basis k _ + 0
      rw [addZero]
    | cons b t =>
      change basis k _ + basis k _ = basis k _ + (basis k _ + 0)
      rw [addZero]
      exact Std.Commutative.comm ..

/-- A kernel row in the actual weight-w tuple-coordinate module has a
derivation using only squares, triangles and coefficient laws of weight w. -/
theorem derive_kernel_rows {q w : Nat} (hq : 0<q) (c : Paper.Rows F q w)
    (hk : ∀ s, Paper.component L c s = 0) :
    Derives (ScalarKernel.RowsAt F q w) (rowWord c) .zero := by
  have supportRows : ScalarKernel.validWord (rowWord c) ∧ ScalarKernel.homogeneous F q w (rowWord c) := by
    clear hk
    induction c with
    | nil => exact ⟨True.intro,True.intro⟩
    | cons e c ih =>
      exact ⟨⟨⟨e.2.property.1,e.2.property.2.1⟩,ih.1⟩,
        ⟨by change weight e.2.val.1 + q + weight e.2.val.2 = w
            have h := e.2.property.2.2
            omega,ih.2⟩⟩
  apply ScalarKernel.kernel_spanned_at_weight F q w hq _ .zero supportRows.1 True.intro supportRows.2 True.intro
  have h := collect_of_coordinates_zero (RowEvaluation.presentation L c) (by
    intro s; rw [RowEvaluation.coordinates_presentation]; exact hk s)
  exact Quotient.exact ((image_rows c).trans (Quotient.sound h))

/-- Linear extension of the actual tuple operator H to formal marked expressions. -/
def HWord (q : Nat) : Word (F × Mark) → Word (F × Tuple)
  | .zero => .zero
  | .atom (k,h,t) => listWord (withCoeff k (H q h t))
  | .plus x y => .plus (HWord q x) (HWord q y)
  | .minus x y => .minus (HWord q x) (HWord q y)

/-- H-images of the weight-w local relations, together with coefficient
collection in the target tuple module. -/
inductive LocalH (F : Type) [Arithmetic F] (q w : Nat) :
    Word (F × Tuple) → Word (F × Tuple) → Prop
  | collect : ScalarKernel.Collect F Tuple x y → LocalH F q w x y
  | localRow : ScalarKernel.RowsAt F q w x y → LocalH F q w (HWord q x) (HWord q y)

private theorem sendH {q w : Nat} {x y : Word (F × Mark)}
    (d : Derives (ScalarKernel.RowsAt F q w) x y) :
    Derives (LocalH F q w) (HWord q x) (HWord q y) := by
  induction d with
  | refl => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ a b => exact .trans a b
  | plus _ _ a b => exact .plus a b
  | minus _ _ a b => exact .minus a b
  | assoc => exact .assoc ..
  | comm => exact .comm ..
  | addZero => exact .addZero ..
  | subAdd => exact .subAdd ..
  | addSub => exact .addSub ..
  | collect => exact .collect ..
  | rule h => exact .rule (.localRow h)

private theorem join_local {q w : Nat} (p r : FormalSum F) :
    Derives (LocalH F q w) (listWord (p++r)) (.plus (listWord p) (listWord r)) := by
  induction p with
  | nil => exact .symm (.trans (.comm _ _) (.addZero _))
  | cons a p ih => exact .trans (.plus (.refl _) ih) (.symm (.assoc ..))

private theorem HWord_rows {q w : Nat} (c : Paper.Rows F q w) :
    Derives (LocalH F q w) (listWord (RowEvaluation.presentation H c)) (HWord q (rowWord c)) := by
  induction c with
  | nil => exact .refl _
  | cons e c ih =>
    change Derives _ (listWord (withCoeff e.1 (H q _ _) ++ RowEvaluation.presentation H c)) _
    exact .trans (join_local _ _) (.plus (.refl _) ih)

/-- The H-image of an arbitrary L-kernel element is generated by the
H-images of the homogeneous local squares and terminal triangles. The
additional local rules in RowsAt simply collect coefficients at one mark.
The displayed input and output are the actual coordinate presentations
used by Paper.component. -/
theorem H_kernel_generated {q w : Nat} (hq : 0<q) (c : Paper.Rows F q w)
    (hk : ∀ s, Paper.component L c s = 0) :
    Derives (LocalH F q w) (listWord (RowEvaluation.presentation H c)) .zero :=
  .trans (HWord_rows c) (sendH (derive_kernel_rows hq c hk))

end Megaera.CoordinateKernel
