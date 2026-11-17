import Megaera.Saturation
import Megaera.SingletonStability

namespace Megaera.SingletonClosure
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.Singletons Megaera.Saturation
variable {F : Type u} [Arithmetic F] [Neg F]

theorem preserves (q : Nat) (field : ConstantField F q) (v : Tuple → F) (h : HPlus q v) :
    HPlus q (star (q-1) v) := by
  have rwSpan := (rowSpan_iff field.add_neg q v).mpr h
  apply (rowSpan_iff field.add_neg q _).mp
  clear h
  induction rwSpan with
  | zero => rw [star_zero]; exact .zero
  | add a b ia ib => rw [star_add]; exact .add ia ib
  | neg a ia => rw [star_neg field.add_neg]; exact .neg ia
  | row a h t k hh ht =>
    rw [star_coeff]
    exact SingletonStability.row q field a h t hh ht k

omit [Neg F] in
/-- The coefficient operator agrees with the ordinary stuffle of finite formal sums. -/
theorem star_expand (n : Nat) (p : FormalSum F) :
    star n (coordinates p) = coordinates (expand (quasiShuffle [n]) p) := by
  induction p with
  | nil => exact star_zero _
  | cons e p ih =>
    have split : coordinates (e::p) = fun t =>
        coordinates (withCoeff e.1 [e.2]) t + coordinates p t := by
      funext t; simp [coordinates, withCoeff, total, Arithmetic.addZero]
    rw [split,star_add,star_coeff,ih]
    funext t
    rw [show expand (quasiShuffle [n]) (e::p) =
        withCoeff e.1 (quasiShuffle [n] e.2) ++ expand (quasiShuffle [n]) p from rfl,
      BCPRows.coord_append]
    simp

omit [Neg F] in
/-- A finite presentation on positive tuples has a bound for its support. -/
theorem supported_of_presentation (p : FormalSum F) (hv : PresentedValid p) :
    ∃ w, Supported w (coordinates p) := by
  induction p with
  | nil =>
    exact ⟨0, fun _ hn => False.elim (hn rfl)⟩
  | cons e p ih =>
    obtain ⟨w,hw⟩ := ih (fun z hz => hv z (List.mem_cons_of_mem _ hz))
    refine ⟨max (weight e.2) w, fun s hn => ?_⟩
    by_cases h : e.2 = s
    · rw [←h]; exact ⟨hv e (by simp),Nat.le_max_left ..⟩
    · have nz : coordinates p s ≠ 0 := by
        intro he
        apply hn
        change (if e.2 = s then e.1 else 0) + coordinates p s = 0
        rw [if_neg h,he,Arithmetic.addZero]
      have hs := hw s nz
      exact ⟨hs.1,Nat.le_trans hs.2 (Nat.le_max_right ..)⟩

/-- Lemma 2.14(ii) for any finite sum of positive tuples, including the
empty tuple. Both membership and the product use actual tuple coordinates. -/
theorem lemma_2_14_ii (q : Nat) (field : ConstantField F q) (p : FormalSum F)
    (hv : PresentedValid p) :
    HPlus q (coordinates (expand (quasiShuffle [q-1]) p)) ↔ HPlus q (coordinates p) := by
  rw [← star_expand]
  constructor
  · obtain ⟨w,hw⟩ := supported_of_presentation p hv
    exact reflect_bounded field (preserves q field) w w _ hw (above_of_supported hw)
  · exact preserves q field _

end Megaera.SingletonClosure
