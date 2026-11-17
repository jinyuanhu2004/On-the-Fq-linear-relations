import Std

/-!
# Sections 3.2–3.3

These are the splitting argument of Theorem 3.3, the finite-level kernel
calculation of Lemma 3.4, and the passage to quotient spaces. The
hypotheses on evaluation identify the CMPL-specific inputs.
-/

namespace Megaera.SectionThree

universe u v

/-- In Theorem 3.3, F is the space of fixed relations whose first
entries are ≥ b, W the lower-weight relation space, and rho takes the
tail at b. The B-operator provides a section, chosen on a basis. A
section as a function suffices for this bijection. Elements of ker rho
are precisely the next filtration step (first entries ≥ b+1). -/
theorem split_first_entry {F : Type u} {W : Type v}
    [Add F] [Sub F] [Zero W] [Add W] [Sub W]
    (rho : F → W) (lift : W → F)
    (rho_add : ∀ a b, rho (a + b) = rho a + rho b)
    (rho_sub : ∀ a b, rho (a - b) = rho a - rho b)
    (takes_tail : ∀ b, rho (lift b) = b)
    (zero_add : ∀ b : W, 0 + b = b) (sub_self : ∀ b : W, b - b = 0)
    (sub_add : ∀ a b : F, a - b + b = a)
    (add_sub : ∀ a b : F, a + b - b = a) :
    ∃ (split : F → {a : F // rho a = 0} × W)
      (join : {a : F // rho a = 0} × W → F),
      (∀ a, join (split a) = a) ∧ (∀ x, split (join x) = x) := by
  let split (a : F) : {a : F // rho a = 0} × W :=
    (⟨a - lift (rho a), by rw [rho_sub, takes_tail, sub_self]⟩, rho a)
  let join (x : {a : F // rho a = 0} × W) := x.1.val + lift x.2
  refine ⟨split, join, ?_, ?_⟩
  · intro a
    exact sub_add _ _
  · rintro ⟨⟨a, ha⟩, b⟩
    have ht : rho (a + lift b) = b := by rw [rho_add, ha, takes_tail, zero_add]
    apply Prod.ext
    · apply Subtype.ext
      change a + lift b - lift (rho (a + lift b)) = a
      rw [ht, add_sub]
    · exact ht

/-- Strict sum over nonnegative levels for a positive-weight tuple. -/
def strictSum {A : Type u} [Zero A] [Add A] (term : Nat → A) : Nat → A
  | 0 => 0
  | n+1 => strictSum term n + term n

theorem strictSum_vanishes_iff {A : Type u} [Zero A] [Add A]
    (zero_add : ∀ a : A, 0 + a = a) (term : Nat → A) :
    (∀ n, strictSum term (n+1) = 0) ↔ ∀ n, term n = 0 := by
  constructor
  · intro h n
    have prev : strictSum term n = 0 := by
      cases n with
      | zero => rfl
      | succ k => exact h k
    have step := h n
    change strictSum term n + term n = 0 at step
    rwa [prev, zero_add] at step
  · intro h n
    have hz : ∀ k, strictSum term k = 0 := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        change strictSum term k + term k = 0
        rw [ih, zero_add, h]
    exact hz (n+1)

/-- The shift equality in Lemma 3.4. Si₀(N)=0 since N has depth ≥2.
When Si_{n+1}(N) factors as a nonzero scalar times a truncated tail,
its vanishing detects precisely the vanishing of that tail. -/
theorem fixed_lift_iff_truncated {A : Type u} [Zero A] [Mul A] [Sub A]
    (lift shifted tail factor : Nat → A) (D : A)
    (D_ne : D ≠ 0) (factor_ne : ∀ n, factor n ≠ 0)
    (mul_cancel_zero : ∀ a b : A, a ≠ 0 → (a * b = 0 ↔ b = 0))
    (sub_zero_iff : ∀ a b : A, a - b = 0 ↔ a = b)
    (at_zero : shifted 0 = 0)
    (binary : ∀ n, lift n = D * (shifted n - shifted (n+1)))
    (product : ∀ n, shifted (n+1) = factor n * tail n) :
    (∀ n, lift n = 0) ↔ ∀ n, tail n = 0 := by
  have adjacent : ∀ n, lift n = 0 ↔ shifted n = shifted (n+1) := by
    intro n
    rw [binary, mul_cancel_zero _ _ D_ne, sub_zero_iff]
  have detects : ∀ n, shifted (n+1) = 0 ↔ tail n = 0 := by
    intro n
    rw [product, mul_cancel_zero _ _ (factor_ne n)]
  constructor
  · intro h n
    have hz : ∀ k, shifted k = 0 := by
      intro k
      induction k with
      | zero => exact at_zero
      | succ k ih => exact ((adjacent k).mp (h k)).symm.trans ih
    exact (detects n).mp (hz (n+1))
  · intro h n
    have hz : ∀ k, shifted k = 0 := by
      intro k
      cases k with
      | zero => exact at_zero
      | succ k => exact (detects k).mpr (h k)
    exact (adjacent n).mpr ((hz n).trans (hz (n+1)).symm)

/-- Positive-weight kernel in Lemma 3.4. The factor at n is
ℓ_{n+1}⁻¹ Si_{<n+1}(q−1); nonvanishing is an explicit input. -/
theorem fixed_lift_iff_fixed_tail {A : Type u} [Zero A] [Add A] [Mul A] [Sub A]
    (lift shifted term factor : Nat → A) (D : A)
    (D_ne : D ≠ 0) (factor_ne : ∀ n, factor n ≠ 0)
    (zero_add : ∀ a : A, 0 + a = a)
    (mul_cancel_zero : ∀ a b : A, a ≠ 0 → (a * b = 0 ↔ b = 0))
    (sub_zero_iff : ∀ a b : A, a - b = 0 ↔ a = b)
    (at_zero : shifted 0 = 0)
    (binary : ∀ n, lift n = D * (shifted n - shifted (n+1)))
    (product : ∀ n, shifted (n+1) = factor n * strictSum term (n+1)) :
    (∀ n, lift n = 0) ↔ ∀ n, term n = 0 := by
  exact (fixed_lift_iff_truncated lift shifted (fun n => strictSum term (n+1))
    factor D D_ne factor_ne mul_cancel_zero sub_zero_iff at_zero binary product).trans
    (strictSum_vanishes_iff zero_add term)

/-- Boundary w=q: T is a scalar times the empty tuple, and each
positive truncation equals that same scalar. -/
theorem fixed_lift_iff_zero_scalar {A : Type u} [Zero A] [Mul A] [Sub A]
    (lift shifted factor : Nat → A) (D t : A)
    (D_ne : D ≠ 0) (factor_ne : ∀ n, factor n ≠ 0)
    (mul_cancel_zero : ∀ a b : A, a ≠ 0 → (a * b = 0 ↔ b = 0))
    (sub_zero_iff : ∀ a b : A, a - b = 0 ↔ a = b)
    (at_zero : shifted 0 = 0)
    (binary : ∀ n, lift n = D * (shifted n - shifted (n+1)))
    (product : ∀ n, shifted (n+1) = factor n * t) :
    (∀ n, lift n = 0) ↔ t = 0 := by
  have h := fixed_lift_iff_truncated lift shifted (fun _ => t) factor D D_ne
    factor_ne mul_cancel_zero sub_zero_iff at_zero binary product
  exact h.trans ⟨fun hyp => hyp 0, fun ht _ => ht⟩

/-- The quotient argument of Lemma 3.4. Both equivalence relations
say that the difference is fixed. Detection is the kernel calculation
applied to a difference. Surjectivity uses the empty-prefix
representatives for U modulo fixed relations. -/
theorem quotient_fundamental {S : Type u} {U : Type v}
    (domain : Setoid S) (codomain : Setoid U) (f : S → U)
    (detects : ∀ a b, domain.r a b ↔ codomain.r (f a) (f b))
    (onto : ∀ u, ∃ a, codomain.r (f a) u) :
    ∃ g : Quotient domain → Quotient codomain,
      (∀ a, g (Quotient.mk domain a) = Quotient.mk codomain (f a)) ∧
      (∀ x y, g x = g y → x = y) ∧ (∀ y, ∃ x, g x = y) := by
  let g : Quotient domain → Quotient codomain := Quotient.lift
    (fun a => Quotient.mk codomain (f a))
    (fun a b h => Quotient.sound ((detects a b).mp h))
  refine ⟨g, fun _ => rfl, ?_, ?_⟩
  · intro x
    refine Quotient.inductionOn x ?_
    intro a y
    refine Quotient.inductionOn y ?_
    intro b h
    exact Quotient.sound ((detects a b).mpr (Quotient.exact h))
  · intro y
    refine Quotient.inductionOn y ?_
    intro u
    obtain ⟨a, ha⟩ := onto u
    exact ⟨Quotient.mk domain a, Quotient.sound ha⟩

end Megaera.SectionThree
