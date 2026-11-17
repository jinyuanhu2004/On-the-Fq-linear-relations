import Megaera.CompletenessProof
import Megaera.RevisedProducts
import Megaera.FourShapes
import Megaera.FourInvariant
import Megaera.FourSupport
import Megaera.FourBoundary

/-! Entry points for the November manuscript, Megaera (2).pdf. -/
namespace Megaera.RevisionTwo
open Megaera.Carlitz Megaera.Finite Megaera.Paper Megaera.FourReduction Megaera.Triangular
variable {F : Type u} [Arithmetic F] [Neg F]

/-- The unrestricted invariance assertion on page 24 fails as an assertion
about the actual permitted generators. Both the inadmissible shape of the
original minimum and the full signed coefficient are checked. -/
theorem page_24_obstruction (q : Nat) (hq : 3 ≤ q) (field : ConstantField F q) :
    let cutoff : Tuple := [q+1,q+1,1]
    let g := liftP (F:=F) q [] [1] [1,1]
    ¬ Legal F q (2*q+3) cutoff ∧
    (Reduces F q (2*q+3) (Precedes cutoff) g (fun _ => 0)) ∧
    FourInvariant.detector q g = -1 ∧
    FourInvariant.detector q g ≠ FourInvariant.detector q (fun _ => (0:F)) := by
  dsimp only
  obtain ⟨hg,hp,later,detect⟩ := FourInvariant.typeII_obstruction q hq field
  refine ⟨fun hl => obstruction_illegal q _ hq ((legal_iff_shape field _).mp hl),
    eliminate_generator field _ hg hp later,?_,detect⟩
  exact FourInvariant.typeII_value q hq

omit [Neg F] in
/-- For this cutoff, every nonzero coordinate of a canonical H-image has
depth at least four. Thus the offending depth-three pivot is excluded
when reductions start at the actual minimum of Ind P. -/
theorem obstruction_outside_image {q w : Nat} (xs : Rows F q w)
    (bounded : ∀ e ∈ xs, ∀ j ∈ e.2.val.1, j ≤ q)
    (first : ∀ e ∈ xs, [q+1,q+1,1] = rowSource e ∨ Precedes [q+1,q+1,1] (rowSource e)) :
    ¬ ImageWindow (component H xs) [q+2,1,q] := by
  rintro ⟨x,nz,order⟩
  have out := FourSupport.component_support xs [] [q+1,1] x 1 (by decide) bounded first nz
  have len : 3 < x.length := out.resolve_right (fun h => h.2.1 rfl)
  rcases order with rfl | lt
  · simp at len
  · rcases lt with h | ⟨h,_⟩ <;> simp [depth] at h <;> omega

/-- Theorem 1.10 for the revised B and C products, using the earlier proof. -/
theorem theorem_1_10 (q : Nat) (rowLaw : CompletenessProof.LiftedRowIdentity F q)
    (theorem12 : ∀ w, 0 < w → TTSpanning.TTPolynomialIndependent F q w)
    (field : ConstantField F q) (w : Nat) (hw : 0 < w) (p : FormalSum F)
    (hp : ∀ e ∈ p, Valid e.2 ∧ weight e.2 = w) :
    Relation q w p ↔
      ∃ rows : List (F × Tuple × Tuple × Tuple),
        (∀ e ∈ rows, Valid e.2.1 ∧ Valid e.2.2.1 ∧ Valid e.2.2.2 ∧ e.2.2.2 ≠ [] ∧
          weight e.2.1 + weight e.2.2.1 + weight e.2.2.2 + 2*q = w) ∧
        ∀ s, coordinates p s = total (fun e =>
          e.1 * coordinates (liftPair (RevisedProducts.Bstar e.2.1
            (RevisedProducts.C e.2.2.1 (primitive (K := F) q e.2.2.2)))) s) rows := by
  have pos : 0 < q := by have := field.two_le; omega
  simpa only [InBCP,RevisedProducts.generator_eq (F := F) q pos] using
    CompletenessProof.theorem_1_10 q rowLaw theorem12 field w hw p hp

end Megaera.RevisionTwo
