import Megaera.RowEvaluation

/-! The kernel assertion used in Corollary 3.2: projection to the
constant component of P + D₁ Q has kernel D₁ R_w. -/
namespace Megaera.SectionThreeSpaces
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.Lift
variable {F : Type u} [Arithmetic F] [Neg F]

def timesD1 (v : Tuple → F) (i : Bool × Tuple) : F := if i.1 then v i.2 else 0

omit [Neg F] in
private theorem cancelD1 (q : Nat) (hq : 2 ≤ q) (A B : Series F)
    (law : cleared q A B) (zero : ∀ n, A n = 0) (n : Nat) : B n = 0 := by
  apply RowEvaluation.zero_of_shift (q-1) (by omega) B _ n
  intro k
  have h : shift q A k = 0 := by by_cases hk : q ≤ k <;> simp [shift,hk,zero]
  simpa [h,zeroAdd] using law k

omit [Neg F] in
private theorem split_coords (p r : FormalSum F) (v : Tuple → F)
    (h : pairCoordinates p r = timesD1 v) :
    coordinates p = coordinates ([] : FormalSum F) ∧ coordinates r = v := by
  exact ⟨funext (fun s => congrFun h (false,s)), funext (fun s => congrFun h (true,s))⟩

omit [Neg F] in
private theorem pure_coords (r : FormalSum F) :
    pairCoordinates [] r = timesD1 (coordinates r) := by
  funext i
  obtain ⟨b,s⟩ := i
  cases b <;> rfl

omit [Neg F] in
private theorem cleared_zero (q : Nat) (A B : Series F)
    (ha : ∀ n, A n = 0) (hb : ∀ n, B n = 0) : cleared q A B := by
  intro n
  simp [shift,ha,hb,Arithmetic.addZero]

/-- Equivalence on concrete coefficient vectors. The scalar D₁ is
cancellable on series because it is T^(-q)(1−T^(q−1)). -/
theorem projection_kernel (q w : Nat) (hq : 2 ≤ q) (v : Tuple → F) :
    U q w (timesD1 v) ↔ RelationVector q w v := by
  constructor
  · rintro ⟨p,r,_,hr,law,coords⟩
    obtain ⟨left,right⟩ := split_coords p r v coords
    have z (n : Nat) : evaluate q p n = 0 := congrFun (evaluate_congr q p [] left) n
    exact ⟨r, ⟨hr,cancelD1 q hq _ _ law z⟩, right⟩
  · rintro ⟨r,⟨hr,z⟩,rfl⟩
    exact ⟨[],r,by simp [homogeneous],hr,cleared_zero q _ _ (fun _ => rfl) z,pure_coords r⟩

/-- The same equality holds on the fixed subspaces, coefficientwise in
each integer degree. -/
theorem fixed_projection_kernel (q w : Nat) (hq : 2 ≤ q) (v : Tuple → F) :
    fixedU q w (timesD1 v) ↔ fixedR q w v := by
  constructor
  · rintro ⟨p,r,_,hr,law,levels,coords⟩
    obtain ⟨left,right⟩ := split_coords p r v coords
    have z (n : Nat) : evaluate q p n = 0 := congrFun (evaluate_congr q p [] left) n
    refine ⟨r,⟨hr,cancelD1 q hq _ _ law z⟩,?_,right⟩
    intro d n
    exact cancelD1 q hq _ _ (levels d)
      (fun j => linear_form_congr (fun s => degree q d s j) p [] left) n
  · rintro ⟨r,⟨hr,z⟩,levels,rfl⟩
    exact ⟨[],r,by simp [homogeneous],hr,cleared_zero q _ _ (fun _ => rfl) z,
      fun d => cleared_zero q _ _ (fun _ => rfl) (levels d),pure_coords r⟩

end Megaera.SectionThreeSpaces
