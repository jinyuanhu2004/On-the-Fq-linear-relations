import Std

namespace Megaera.FinalFiniteLists

theorem perm_of_nodup {A : Type u} (xs ys : List A) (hx : xs.Nodup) (hy : ys.Nodup)
    (same : ∀ a, a∈xs ↔ a∈ys) : xs.Perm ys := by
  classical
  induction xs generalizing ys with
  | nil => cases ys with
           | nil => exact .nil
           | cons y ys => exact False.elim (List.not_mem_nil ((same y).mpr (by simp)))
  | cons a xs ih =>
    have ay := (same a).mp (by simp)
    obtain ⟨an,sub⟩ := List.nodup_cons.mp hx
    apply ((ih (ys.erase a) sub (hy.erase a) ?_).cons a).trans (List.perm_cons_erase ay).symm
    intro x
    rw [hy.mem_erase_iff]
    constructor
    · intro h
      exact ⟨fun e => an (e ▸ h),(same x).mp (by simp [h])⟩
    · rintro ⟨diff,h⟩
      simpa [diff] using (same x).mpr h

end Megaera.FinalFiniteLists
