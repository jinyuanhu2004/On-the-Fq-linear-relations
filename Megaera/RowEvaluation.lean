import Megaera.Reduction
import Megaera.SectionThreeSpaces
import Megaera.BCPRows

/-! Why the induced operator preserves relations in §2.2. The input is
the evaluation identity for a single canonical row, obtained by lifting
(2.3). This module carries it through finite sums and cancels D₁ on the
actual coefficient series. -/
namespace Megaera.RowEvaluation
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.CanonicalInd
variable {F : Type u} [Arithmetic F] [Neg F] {q w : Nat}
local instance : Std.Associative (α := F) (· + ·) := ⟨Arithmetic.addAssoc⟩
local instance : Std.Commutative (α := F) (· + ·) := ⟨Arithmetic.addComm⟩

def presentation (op : Nat → Tuple → Tuple → List Tuple) (c : Rows F q w) : FormalSum F :=
  c.flatMap (fun e => withCoeff e.1 (op q e.2.val.1 e.2.val.2))

omit [Neg F] in
private theorem total_join {A : Type v} (f : A → F) (xs ys : List A) :
    total f (xs++ys) = total f xs + total f ys := by
  induction xs with
  | nil => exact (zeroAdd _).symm
  | cons x xs ih => simp [total, ih, Arithmetic.addAssoc]

omit [Neg F] in
private theorem sum_scale (m : F × Tuple → F)
    (lin : ∀ z s, m (z,s) = z * m (1,s)) (a : F) (ts : List Tuple) :
    total m (withCoeff a ts) = a * total m (withCoeff 1 ts) := by
  induction ts with
  | nil => exact (Arithmetic.mulZero _).symm
  | cons s ts ih =>
    change m (a,s) + total m (withCoeff a ts) = a * (m (1,s) + total m (withCoeff 1 ts))
    rw [lin a s,ih, Arithmetic.distrib]

omit [Neg F] in
theorem coordinates_presentation (op : Nat → Tuple → Tuple → List Tuple) (c : Rows F q w) :
    coordinates (presentation op c) = component op c := by
  funext s
  let m : F × Tuple → F := fun z => if z.2 = s then z.1 else 0
  have lin (a : F) (v : Tuple) : m (a,v) = a * m (1,v) := by
    by_cases h : v = s <;> simp [m,h,Arithmetic.mulOne,Arithmetic.mulZero]
  induction c with
  | nil => rfl
  | cons e c ih =>
    change total m (withCoeff e.1 _ ++ presentation op c) = _ + component op c s
    rw [total_join, sum_scale m lin]
    exact congrArg (_ + ·) ih

private theorem eval_cons (op : Nat → Tuple → Tuple → List Tuple) (e : F × Row q w)
    (c : Rows F q w) (n : Nat) :
    evaluate q (presentation op (e::c)) n =
      e.1 * evaluate q (withCoeff 1 (op q e.2.val.1 e.2.val.2)) n +
      evaluate q (presentation op c) n := by
  let m : F × Tuple → F := fun z => z.1 * li q z.2 n
  have lin (a : F) (s : Tuple) : m (a,s) = a * m (1,s) := by simp [m,oneMul]
  change total m (withCoeff e.1 _ ++ presentation op c) = _
  rw [total_join,sum_scale m lin]
  rfl

omit [Neg F] in
private theorem shift_linear (a : F) (m n : Nat) (f g : Series F) :
    shift m (fun i => a*f i+g i) n = a*shift m f n + shift m g n := by
  by_cases h : m ≤ n <;> simp [shift,h,Arithmetic.mulZero,Arithmetic.addZero]

/-- With T=θ⁻¹ the lifted relation L + D₁ H = 0 becomes
T^q Li(L) + Li(H) = T^(q−1) Li(H). -/
abbrev Identity (q : Nat) (l h : FormalSum F) : Prop :=
  SectionThreeSpaces.cleared q (evaluate q l) (evaluate q h)

theorem rows_identity (c : Rows F q w)
    (single : ∀ e ∈ c, Identity q (withCoeff 1 (L q e.2.val.1 e.2.val.2))
      (withCoeff 1 (H q e.2.val.1 e.2.val.2)) (F := F)) :
    Identity q (presentation L c) (presentation H c) := by
  induction c with
  | nil =>
    intro n
    have z (k : Nat) : shift k (evaluate (F := F) q []) n = 0 := by
      by_cases h : k ≤ n <;> simp [shift, h, evaluate, total]
    change shift q (evaluate q []) n + 0 = shift (q-1) (evaluate q []) n
    rw [z,z,Arithmetic.addZero]
  | cons e c ih =>
    have he := single e (by simp)
    have hc := ih (fun z hz => single z (List.mem_cons_of_mem _ hz))
    intro n
    simp only [funext (eval_cons L e c),funext (eval_cons H e c),shift_linear]
    have h := congrArg (e.1 * ·) (he n)
    simp only [Arithmetic.distrib] at h
    rw [← h, ← hc n]
    ac_rfl

omit [Neg F] in
/-- Multiplication by 1−Tᵐ is injective at zero for m>0. -/
theorem zero_of_shift (m : Nat) (hm : 0 < m) (f : Series F)
    (eqn : ∀ n, f n = shift m f n) (n : Nat) : f n = 0 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [eqn n]
    by_cases h : m ≤ n
    · rw [shift,if_pos h]; exact ih _ (by omega)
    · rw [shift,if_neg h]

private theorem valid_H (field : ConstantField F q) (c : Rows F q w) :
    ∀ z ∈ presentation H c, Valid z.2 ∧ weight z.2 = w := by
  intro z hz
  obtain ⟨e,_,ht⟩ := List.mem_flatMap.mp hz
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp ht
  obtain ⟨hh,ht,hw⟩ := e.2.property
  exact ⟨H_valid q field.two_le _ _ hh ht v hv, by
    have h := H_weight q (by have := field.two_le; omega) _ _ v hv
    change weight v = w; omega⟩

theorem relation_H_of_relation_L (field : ConstantField F q) (c : Rows F q w)
    (ident : Identity q (presentation L c) (presentation H c))
    (hv : RelationVector q w (component L c)) : RelationVector q w (component H c) := by
  obtain ⟨p,hp,hv'⟩ := hv
  have he := evaluate_congr q (presentation L c) p ((coordinates_presentation L c).trans hv'.symm)
  have Hzero : ∀ n, evaluate q (presentation H c) n = shift (q-1) (evaluate q (presentation H c)) n := by
    intro n
    have hz : shift q (evaluate q (presentation L c)) n = 0 := by
      rw [he]; by_cases h : q ≤ n <;> simp [shift,h,hp.2]
    simpa [hz,zeroAdd] using ident n
  exact ⟨presentation H c, ⟨valid_H field c,
    zero_of_shift _ (by have := field.two_le; omega) _ Hzero⟩, coordinates_presentation H c⟩

local instance : Zero (Tuple → F) := ⟨fun _ => 0⟩

/-- The single-row input is the lift of (2.3) for arbitrary positions.
Its validity implies both preservation by Ind and vanishing of H(ker L).
Thus no binary-generator or analytic preservation hypothesis is needed
in addition to the row identity and the three span assertions below. -/
theorem completeness_from_row_identity (field : ConstantField F q)
    (rowLaw : ∀ e : Row q w, Identity (F := F) q
      (withCoeff 1 (L q e.val.1 e.val.2)) (withCoeff 1 (H q e.val.1 e.val.2)))
    (canonical : ∀ v : Tuple → F, RelationVector q w v → ∃ c : Rows F q w,
      component L c = v ∧ ∀ e ∈ c, ∀ a ∈ e.2.val.1, a ≤ q)
    (kerL : ∀ v, BCPVector q w v → ∃ c : Rows F q w, component L c = 0 ∧ component H c = v)
    (kerH : ∀ c : Rows F q w, component H c = 0 → BCPVector q w (component L c))
    (p : FormalSum F) (hw : ∀ e ∈ p, Valid e.2 ∧ weight e.2 = w) :
    Relation q w p ↔ InBCP q w p := by
  have hq : 0 < q := by have := field.two_le; omega
  have rel (c : Rows F q w) := relation_H_of_relation_L field c
    (rows_identity c (fun e _ => rowLaw e.2))
  have preserves (v : Tuple → F) (hv : RelationVector q w v) :
      RelationVector q w (ind q w hq v) := by
    obtain ⟨c,hl,hb⟩ := canonical v hv
    rw [← hl,ind_components q w hq field c hb]
    exact rel c (hl ▸ hv)
  rw [relation_iff_vector q w p hw,bcp_iff_vector]
  constructor
  · apply Completeness.of_nilpotent_backward (RelationVector q w) (BCPVector q w) (ind q w hq)
    · exact ⟨[], ⟨[], by simp, fun _ => rfl⟩, rfl⟩
    · exact preserves
    · intro v hv
      exact ⟨_, Reduction.nilpotent_on_relations q w hq field preserves canonical v hv⟩
    · intro v hv hin
      obtain ⟨c,hl,hb⟩ := canonical v hv
      have hind : ind q w hq v = component H c := by rw [←hl,ind_components q w hq field c hb]
      obtain ⟨k,hkL,hkH⟩ := kerL _ hin
      obtain ⟨t,htH,htL⟩ := row_difference field c k hkL (hkH.trans hind)
      rw [← hl,← htL]
      exact kerH t htH
  · intro hb
    obtain ⟨c,hL,hH⟩ := kerL _ hb
    rw [← hH]
    apply rel
    rw [hL]
    exact ⟨[], ⟨by simp, fun _ => rfl⟩, rfl⟩

/-- Theorem 1.10, conditional on the lift of (2.3), the analytic part of
Lemma 2.4, and the remaining inclusion for ker H. The other kernel
inclusion is proved by explicit rows in BCPRows. -/
theorem theorem_1_10_from_rows (q : Nat)
    (rowLaw : ∀ w, 0 < w → ∀ e : Row q w, Identity (F := F) q
      (withCoeff 1 (L q e.val.1 e.val.2)) (withCoeff 1 (H q e.val.1 e.val.2)))
    (canonical : ∀ w, 0 < w → ∀ v : Tuple → F, RelationVector q w v → ∃ c : Rows F q w,
      component L c = v ∧ ∀ e ∈ c, ∀ a ∈ e.2.val.1, a ≤ q)
    (kerH : ∀ w, 0 < w → ∀ c : Rows F q w, component H c = 0 →
      BCPVector q w (component L c)) : Theorem_1_10 F q := by
  intro field w hw p hp
  exact completeness_from_row_identity field (rowLaw w hw) (canonical w hw)
    (BCPRows.bcp_in_H_ker_L q w field) (kerH w hw) p hp

end Megaera.RowEvaluation
