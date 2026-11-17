import Std

/-!
# Sections 2 and 3 of Megaera: the closing implications

At one fixed weight, let C be the space of formal linear combinations of
marked tuple pairs and V the space of formal linear combinations of tuples.
The two components of a row are L c and H c.  This file proves the final
algebraic implications for any such maps.  The concrete kernel computations
and the strict increase of the least tuple enter as explicit hypotheses.
-/

namespace Megaera.Completeness

universe u v a

/-- Apply the induced relation map n times. -/
def iterate {V : Type v} (ind : V → V) : Nat → V → V
  | 0, r => r
  | n + 1, r => iterate ind n (ind r)

private theorem iterate_zero {V : Type v} [Zero V] (ind : V → V)
    (h : ind 0 = 0) (n : Nat) : iterate ind n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change iterate ind n (ind 0) = 0
    rw [h, ih]

/-- Lemma 2.6. The rank can be taken to be the index of the least tuple
in the ordered list of tuples of weight w. No rank condition is imposed
on an iteration whose result is zero. -/
theorem nilpotent_of_strict_rank {V : Type v} [Zero V]
    (relation : V → Prop) (ind : V → V) (rank : V → Nat) (bound : Nat)
    (ind_zero : ind 0 = 0)
    (preserves : ∀ r, relation r → relation (ind r))
    (bounded : ∀ r, relation r → rank r ≤ bound)
    (increases : ∀ r, relation r → ind r ≠ 0 → rank r < rank (ind r)) :
    ∀ r, relation r → iterate ind (bound + 1) r = 0 := by
  have stop : ∀ n r, relation r → bound ≤ rank r + n →
      iterate ind (n + 1) r = 0 := by
    intro n
    induction n with
    | zero =>
      intro r hr hn
      change ind r = 0
      by_cases hz : ind r = 0
      · exact hz
      · have hlt := increases r hr hz
        have hub := bounded (ind r) (preserves r hr)
        omega
    | succ n ih =>
      intro r hr hn
      change iterate ind (n + 1) (ind r) = 0
      by_cases hz : ind r = 0
      · rw [hz]
        exact iterate_zero ind ind_zero (n + 1)
      · have hlt := increases r hr hz
        exact ih (ind r) (preserves r hr) (by omega)
  intro r hr
  exact stop bound r hr (by omega)

/-- Theorem 2.7. Repeated backward closure of a subspace containing zero.
Pointwise nilpotence already suffices. -/
theorem of_nilpotent_backward {V : Type v} [Zero V]
    (relation generated : V → Prop) (ind : V → V)
    (contains_zero : generated 0)
    (preserves : ∀ r, relation r → relation (ind r))
    (terminates : ∀ r, relation r → ∃ n, iterate ind n r = 0)
    (backward : ∀ r, relation r → generated (ind r) → generated r) :
    ∀ r, relation r → generated r := by
  have descend : ∀ n r, relation r → generated (iterate ind n r) →
      generated r := by
    intro n
    induction n with
    | zero =>
      intro r _ h
      exact h
    | succ n ih =>
      intro r hr h
      exact backward r hr (ih (ind r) (preserves r hr) h)
  intro r hr
  obtain ⟨n, hn⟩ := terminates r hr
  exact descend n r hr (by rw [hn]; exact contains_zero)

/-- The only linearity properties needed below are preservation of
addition and subtraction by the two component maps. -/
structure Components (C : Type u) (V : Type v) [Add C] [Sub C]
    [Add V] [Sub V] where
  L : C → V
  H : C → V
  L_add : ∀ c k, L (c + k) = L c + L k
  H_add : ∀ c k, H (c + k) = H c + H k
  L_sub : ∀ c k, L (c - k) = L c - L k
  H_sub : ∀ c k, H (c - k) = H c - H k

section Rows
variable {C : Type u} {V : Type v} [Add C] [Sub C] [Add V] [Sub V] [Zero V]

/-- Section 2.7. Choose the canonical row for r, then subtract a row
in ker L with the same H-component.  Requiring a canonical witness
avoids asserting that Ind (L c) = H c for every representative c. -/
theorem backward_from_kernels (rows : Components C V)
    (relation bcp : V → Prop) (ind : V → V)
    (sub_self : ∀ p : V, p - p = 0) (sub_zero : ∀ p : V, p - 0 = p)
    (canonical : ∀ r, relation r → ∃ c, rows.L c = r ∧ rows.H c = ind r)
    (bcp_from_ker_L : ∀ t, bcp t → ∃ k, rows.L k = 0 ∧ rows.H k = t)
    (L_of_ker_H : ∀ c, rows.H c = 0 → bcp (rows.L c)) :
    ∀ r, relation r → bcp (ind r) → bcp r := by
  intro r hr h
  obtain ⟨c, hcL, hcH⟩ := canonical r hr
  obtain ⟨k, hkL, hkH⟩ := bcp_from_ker_L (ind r) h
  have hH : rows.H (c - k) = 0 := by
    rw [rows.H_sub, hcH, hkH, sub_self]
  have hL : rows.L (c - k) = r := by
    rw [rows.L_sub, hcL, hkL, sub_zero]
  rw [← hL]
  exact L_of_ker_H (c - k) hH

/-- Final implication in Theorem 1.10, with its tuple-specific inputs.
The kernel hypotheses come from Theorem 2.13 and Corollary 2.12 with
Theorem 2.16 and Lemma 2.17. -/
theorem bcp_completeness (rows : Components C V)
    (relation bcp : V → Prop) (ind : V → V)
    (sub_self : ∀ p : V, p - p = 0) (sub_zero : ∀ p : V, p - 0 = p)
    (bcp_zero : bcp 0) (sound : ∀ t, bcp t → relation t)
    (preserves : ∀ r, relation r → relation (ind r))
    (terminates : ∀ r, relation r → ∃ n, iterate ind n r = 0)
    (canonical : ∀ r, relation r → ∃ c, rows.L c = r ∧ rows.H c = ind r)
    (bcp_from_ker_L : ∀ t, bcp t → ∃ k, rows.L k = 0 ∧ rows.H k = t)
    (L_of_ker_H : ∀ c, rows.H c = 0 → bcp (rows.L c)) :
    ∀ r, relation r ↔ bcp r := by
  have backward := backward_from_kernels rows relation bcp ind sub_self sub_zero
    canonical bcp_from_ker_L L_of_ker_H
  intro r
  exact ⟨of_nilpotent_backward relation bcp ind bcp_zero preserves terminates
    backward r, sound r⟩

/-- The coefficient pair (p,q) represents p + D₁ q.  On evaluated
values, signedScale is multiplication by -D₁. The tuple-specific
facts concern evaluation, outside this additive argument. -/
structure Evaluation (V : Type v) (A : Type a) [Sub V] [Zero V]
    [Sub A] [Zero A] where
  eval : V → A
  signedScale : A → A
  eval_zero : eval 0 = 0
  eval_sub : ∀ p q, eval (p - q) = eval p - eval q
  scale_zero : signedScale 0 = 0
  scale_sub : ∀ a b, signedScale (a - b) = signedScale a - signedScale b
  scale_injective : ∀ {a b}, signedScale a = signedScale b → a = b

variable {A : Type a} [Sub A] [Zero A]

omit [Add V] in
/-- For a zero constant coefficient, the kernel of the projection in
Corollary 3.2 consists exactly of pairs (0,q) with Li(q) = 0. -/
theorem zero_constant_iff (E : Evaluation V A) (q : V) :
    E.eval 0 = E.signedScale (E.eval q) ↔ E.eval q = 0 := by
  constructor
  · intro h
    apply E.scale_injective
    rw [E.scale_zero, ← h, E.eval_zero]
  · intro h
    rw [h, E.scale_zero, E.eval_zero]

/-- Lemma 3.1. The coefficient comparison in the paper is used only
on the TT-supported remainder. Its independence is an explicit input.
The other input is the consequence R = H(ker L) of Theorems 1.10
and 2.13. The conclusion expresses degree-one relations using the
same row c for *both* coefficients. -/
theorem degree_one_iff_joint_image (rows : Components C V) (E : Evaluation V A)
    (TTsupported : V → Prop)
    (split : ∀ p, ∃ c, TTsupported (p - rows.L c))
    (constant_independent : ∀ t s, TTsupported t →
      E.eval t = E.signedScale (E.eval s) → t = 0)
    (row_relation : ∀ c, E.eval (rows.L c) = E.signedScale (E.eval (rows.H c)))
    (ker_L_covers : ∀ r, E.eval r = 0 → ∃ k, rows.L k = 0 ∧ rows.H k = r)
    (eq_of_sub_zero : ∀ p t : V, p - t = 0 → p = t)
    (zero_add : ∀ p : V, 0 + p = p)
    (sub_add_cancel : ∀ p t : V, (p - t) + t = p) (p q : V) :
    E.eval p = E.signedScale (E.eval q) ↔
      ∃ c, rows.L c = p ∧ rows.H c = q := by
  constructor
  · intro hu
    obtain ⟨c, hTT⟩ := split p
    have residual : E.eval (p - rows.L c) = E.signedScale (E.eval (q - rows.H c)) := by
      rw [E.eval_sub, E.eval_sub, E.scale_sub, hu, row_relation]
    have hzero := constant_independent _ _ hTT residual
    have hp : p = rows.L c := eq_of_sub_zero _ _ hzero
    have hr : E.eval (q - rows.H c) = 0 :=
      (zero_constant_iff E _).mp (hzero ▸ residual)
    obtain ⟨k, hkL, hkH⟩ := ker_L_covers _ hr
    refine ⟨k + c, ?_, ?_⟩
    · rw [rows.L_add, hkL, zero_add, ← hp]
    · rw [rows.H_add, hkH, sub_add_cancel]
  · rintro ⟨c, rfl, rfl⟩
    exact row_relation c

end Rows
end Megaera.Completeness
