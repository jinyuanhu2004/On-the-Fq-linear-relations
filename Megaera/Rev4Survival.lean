import Megaera.Rev4Window
import Megaera.Rev4Positive
import Megaera.Rev4Pairing

/-! The Case II functional for reductions whose pivots lie in the window
of the actual H-image, as required by §4.1. -/
namespace Megaera.Rev4Survival
open Megaera.Finite Megaera.Paper Megaera.Carlitz Megaera.Splitting Megaera.Triangular
open Megaera.FourMinimum Megaera.FourLambda Megaera.FourReduction
open Megaera.Rev4Negative Megaera.Rev4Geometry Megaera.Rev4Window Megaera.Rev4Pairing
variable {F : Type u} [Arithmetic F] [Neg F] {q w : Nat}

private theorem raise_width (q : Nat) (v : Tuple) : (raiseFirst q v).length=width v := by
  cases v <;> simp [raiseFirst,width]

private theorem signed_reading_zero (field : ConstantField F q) (xs : Rows F q w)
    (s t h after u v target : Tuple) (c r m b : Nat) (hc : 0<c)
    (valid_h : Valid h) (valid_u : Valid u) (hu : u≠[]) (valid_v : Valid v)
    (weight_eq : weight h + weight u + weight v + 2*q=w)
    (hb : 0<b) (hb' : b≤q-1) (boundary : b=q-1 → ∃ j,target.length=j+1 ∧ entries (target++[b]) j=1)
    (bs : ∀ j∈s,j≤q) (bounded : ∀ e∈xs, ∀ j∈e.2.val.1,j≤q)
    (first : ∀ e∈xs, source q s (c::t)=rowSource e ∨ Precedes (source q s (c::t)) (rowSource e))
    (same : (c::t).length = r+1+(target++[b]).length)
    (window : ImageWindow (component H xs) (h++after))
    (le : after.length ≤ (u++raiseFirst q v).length) :
    reading w (selected field (endHead s++List.replicate r 1++[m]) (target++[b]) target.length b)
      (liftP q h u v)=0 := by
  let stem := endHead s++List.replicate r 1++[m]
  let f := selected field stem (target++[b]) target.length b
  have layer : stem.length + (target.length+1) = selectedDepth q s (c::t) := by
    have eqn := selected_layer q c r m s t (target++[b]) same
    simpa only [stem,List.length_append,List.length_cons,List.length_nil] using eqn
  have depth_bound := imageWindow_depth xs s t (h++after) c hc bounded first window
  have pos := Rev4Positive.positive_part_zero field s h u v (target++[b]) r m target.length b
    bs valid_u hu valid_v hb hb' boundary (by
      rw [←List.append_assoc]
      change stem.length + (target.length+1) ≤ _
      simp only [List.length_append,raise_width] at le depth_bound
      omega)
  have neg := negative_in_window field xs s t h after u v (target++[b]) c r m target.length b
    hc valid_h valid_v hb hb' bounded first window le layer
  change reading w f (liftP q h u v)=0
  rw [reading_lifted field w f h u v valid_h valid_u valid_v weight_eq]
  unfold lifted generalP
  rw [←List.map_flatMap,PrimitiveRows.bStar_expansion,total_append']
  change total _ (withCoeff (1:F) _) + total
    (fun e : F × Tuple => e.1 * selected field stem (target++[b]) target.length b e.2) _ = _
  rw [neg,Arithmetic.addZero]
  have positive_evaluation (l : List Tuple) :
      total (fun e : F × Tuple => e.1 * f e.2) (withCoeff (1:F) l) = total f l := by
    induction l with
    | nil => rfl
    | cons e l ih => change 1 * f e + _ = f e + _; rw [oneMul]; exact congrArg (_+·) ih
  rw [positive_evaluation,total_map]
  simpa only [f,stem,List.append_assoc] using pos

private theorem actual_pivot (field : ConstantField F q) {g : Tuple → F} {x y : Tuple}
    (hx : Least g x) (hy : UnitMinimum g y) : x=y := by
  have nz : g y ≠ 0 := fun contra => field.nontrivial (contra.symm.trans hy.1)
  rcases hx.2 y nz with eq | lt
  · exact eq.symm
  · exact (hx.1 (hy.2 x lt)).elim

private theorem inc_valid_weight (u : Tuple) (hv : Valid u) (hn : u≠[]) :
    Valid (incLast u) ∧ weight (incLast u)=weight u+1 := by
  cases u with
  | nil => contradiction
  | cons a u =>
    exact ⟨endings_valid _ hv _ (by simp [endings]),incLast_weight a u⟩

/-- Every allowed generator of one of the three types has zero reading
at a pivot in the actual image window. In type III this uses the pivot
of the difference for both constituent lifts. -/
theorem special_zero (field : ConstantField F q) (xs : Rows F q w)
    (s t target : Tuple) (c r m b : Nat) (hc : 0<c)
    (hb : 0<b) (hb' : b≤q-1) (boundary : b=q-1 → ∃ j,target.length=j+1 ∧ entries (target++[b]) j=1)
    (bs : ∀ j∈s,j≤q) (bounded : ∀ e∈xs, ∀ j∈e.2.val.1,j≤q)
    (first : ∀ e∈xs, source q s (c::t)=rowSource e ∨ Precedes (source q s (c::t)) (rowSource e))
    (same : (c::t).length = r+1+(target++[b]).length)
    {g : Tuple → F} {pivot : Tuple} (hg : Special F q w g)
    (least : Least g pivot) (window : ImageWindow (component H xs) pivot) :
    reading w (selected field (endHead s++List.replicate r 1++[m]) (target++[b]) target.length b) g = 0 := by
  cases hg with
  | general h u v vh vu hu vv hw =>
    rw [actual_pivot field least (lemma_4_1_i_ii q field.two_le h u v hu)] at window
    exact signed_reading_zero field xs s t h _ u v target c r m b hc vh vu hu vv hw
      hb hb' boundary bs bounded first same window (Nat.le_of_eq (general_suffix_depth q u v hu))
  | difference h a u z vh va ha vu hu vz hw =>
    rw [actual_pivot field least (lemma_4_1_iii q field h a u z ha hu)] at window
    obtain ⟨vA,wA⟩ := inc_valid_weight a va ha
    obtain ⟨vU,wU⟩ := inc_valid_weight u vu hu
    obtain ⟨one,two⟩ := difference_suffix_depths q a u z ha hu
    have k₁ := signed_reading_zero field xs s t h _ a (incLast u++z) target c r m b hc vh va ha
      (fun i hi => (List.mem_append.mp hi).elim (vU i) (vz i))
      (by rw [weight_append,wU]; omega) hb hb' boundary bs bounded first same window (Nat.le_of_eq one)
    have k₂ := signed_reading_zero field xs s t h _ (incLast a++u) z target c r m b hc vh
      (fun i hi => (List.mem_append.mp hi).elim (vA i) (vu i)) (by simp [hu]) vz
      (by rw [weight_append,wA]; omega) hb hb' boundary bs bounded first same window (by omega)
    let f := selected field (endHead s++List.replicate r 1++[m]) (target++[b]) target.length b
    have diff : (fun x => liftP (F:=F) q h a (incLast u++z) x + -liftP q h (incLast a++u) z x) =
        addScaled (liftP q h a (incLast u++z)) (-1:F) (liftP q h (incLast a++u) z) := by
      funext x; simp only [addScaled,neg_mul field,oneMul]
    rw [diff,reading_addScaled,k₁,k₂,Arithmetic.mulZero,Arithmetic.addZero]

/-- A nonzero initial Case II reading prevents every permitted
sequence of reductions in the image window from reaching zero. -/
theorem survives (field : ConstantField F q) (xs : Rows F q w)
    (s t target : Tuple) (c r m b : Nat) (hc : 0<c)
    (hb : 0<b) (hb' : b≤q-1) (boundary : b=q-1 → ∃ j,target.length=j+1 ∧ entries (target++[b]) j=1)
    (bs : ∀ j∈s,j≤q) (bounded : ∀ e∈xs, ∀ j∈e.2.val.1,j≤q)
    (first : ∀ e∈xs, source q s (c::t)=rowSource e ∨ Precedes (source q s (c::t)) (rowSource e))
    (same : (c::t).length = r+1+(target++[b]).length)
    (nz : reading w (selected field (endHead s++List.replicate r 1++[m]) (target++[b]) target.length b)
      (component H xs) ≠ 0) :
    ¬ Reduces F q w (ImageWindow (component H xs)) (component H xs) (fun _ => 0) := by
  let f := selected field (endHead s++List.replicate r 1++[m]) (target++[b]) target.length b
  apply survives_of_functional _ _ (reading w f) _ nz
  · intro x g pivot k hg least window
    rw [reading_addScaled,special_zero field xs s t target c r m b hc hb hb' boundary bs bounded first same hg least window,
      Arithmetic.mulZero,Arithmetic.addZero]
  · apply total_zero_of_members
    intro _ _
    exact zeroMul _

end Megaera.Rev4Survival
