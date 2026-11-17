import Megaera.Lambda
import Megaera.Singletons
import Megaera.GradedBCP
import Megaera.PureReplacement

namespace Megaera.SingletonStability
open Megaera.Carlitz Megaera.Finite Megaera.Paper Megaera.Singletons
variable {F : Type u} [Arithmetic F] [Neg F]

/-- The positive-prefix row space is stable under multiplying each of
its tuple terms by (q−1), including arbitrary constant coefficients. -/
theorem row (q : Nat) (field : ConstantField F q) (a : Nat) (s t : Tuple)
    (hs : Valid (a::s)) (ht : Valid t) (k : F) :
    RowSpan q (coordinates (withCoeff k ((H q (a::s) t).flatMap (quasiShuffle [q-1])))) := by
  let rows := Lambda.lambda q (a::s) t
  have good (p : Tuple × Tuple) (hp : p ∈ rows) :
      Valid p.1 ∧ Valid p.2 ∧ p.1 ≠ [] := by
    have hq := field.two_le
    have hv : Valid [q-1] := by intro i hi; obtain rfl := List.mem_singleton.mp hi; omega
    rcases List.mem_append.mp hp with h | h <;> obtain ⟨v,hv',rfl⟩ := List.mem_map.mp h
    · refine ⟨valid_quasiShuffle _ _ _ hv hs hv',ht,?_⟩
      have le := Triangular.singleton_stuffle_depth _ _ _ hv'
      intro he; change v=[] at he; rw [he] at le; simp at le
    · exact ⟨hs,valid_quasiShuffle _ _ _ hv ht hv',by simp⟩
  have h (xs : List (Tuple × Tuple)) (ok : ∀ p ∈ xs, Valid p.1 ∧ Valid p.2 ∧ p.1 ≠ []) :
      RowSpan q (coordinates (withCoeff k (xs.flatMap (fun p => H q p.1 p.2)))) := by
    induction xs with
    | nil => exact .zero
    | cons p xs ih =>
      obtain ⟨h,t⟩ := p
      obtain ⟨hh,ht,hn⟩ := ok (h,t) (by simp)
      cases h with
      | nil => exact (hn rfl).elim
      | cons b h =>
        have inrow := RowSpan.row (q := q) b h t k hh ht
        have r := RowSpan.add inrow (ih (fun p hp => ok p (by simp [hp])))
        simpa only [List.flatMap_cons,withCoeff,List.map_append,←funext (BCPRows.coord_append _ _)] using r
  have eq := BCPRows.coord_perm ((Lambda.H_lambda q (a::s) t).map (fun y => (k,y)))
  exact (funext eq) ▸ h rows good

end Megaera.SingletonStability
