import Megaera.Rev4Geometry

/-! The negative contribution to the Case II detector at a pivot in
the actual image window. -/
namespace Megaera.Rev4Window
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.Splitting
open Megaera.Triangular Megaera.FourReduction Megaera.FourMinimum
open Megaera.Rev4Negative Megaera.Rev4Geometry
variable {F : Type u} [Arithmetic F] [Neg F] {q w : Nat}

/-- The signed negative list of an eligible lift contributes zero.
The pivot is h++after. Its suffix may be shorter than the source in
the negative list, as happens for one lift in a difference. The image
window and an actual occurrence suffice to recover every prefix and
depth hypothesis required for cancellation. -/
theorem negative_in_window (field : ConstantField F q) (xs : Rows F q w)
    (s t h after u v target : Tuple) (c r m n b : Nat) (hc : 0<c)
    (valid_h : Valid h) (valid_v : Valid v) (hb₀ : 0<b) (hb : b≤q-1)
    (bounded : ∀ e∈xs, ∀ j∈e.2.val.1,j≤q)
    (first : ∀ e∈xs, source q s (c::t)=rowSource e ∨ Precedes (source q s (c::t)) (rowSource e))
    (window : ImageWindow (component H xs) (h++after))
    (suffix_le : after.length ≤ (u++raiseFirst q v).length)
    (layer : (endHead s ++ List.replicate r 1 ++ [m]).length + (n+1) = selectedDepth q s (c::t)) :
    let stem := endHead s ++ List.replicate r 1 ++ [m]
    total (fun e : F × Tuple => e.1 * selected field stem target n b e.2)
      (withCoeff (-(1:F)) (concatenate (endings h) ((L q u v).flatMap (quasiShuffle [q-1]))))=0 := by
  dsimp only
  let stem := endHead s ++ List.replicate r 1 ++ [m]
  let terms := concatenate (endings h) ((L q u v).flatMap (quasiShuffle [q-1]))
  change total (fun e : F × Tuple => e.1 * selected field stem target n b e.2)
    (withCoeff (-(1:F)) terms) = 0
  classical
  by_cases hit : ∃ tail : Tuple, tail.length=n+1 ∧ stem++tail∈terms
  · obtain ⟨tail,ht,occ⟩ := hit
    obtain ⟨_,_,p,he,hp,_⟩ := negative_list_prefix xs s t h after u v tail c r m hc valid_h
      bounded first window suffix_le (by rw [List.length_append,ht]; exact layer) occ
    exact valid_negative_contribution_zero field stem target h u v p n b
      (by simp [stem]) valid_h valid_v he (hp.trans ht) hb₀ hb
  · apply total_zero_of_members
    intro e he
    obtain ⟨x,mem,rfl⟩ := List.mem_map.mp he
    have absent : selected field stem target n b x=0 := by
      simp only [selected]
      split
      · rename_i cond
        obtain ⟨hl,eqn,_⟩ := cond
        have reconstruct : stem ++ x.drop stem.length = x := by
          conv => lhs; lhs; rw [←eqn]
          exact List.take_append_drop _ _
        exact (hit ⟨x.drop stem.length,by rw [List.length_drop]; omega,reconstruct.symm ▸ mem⟩).elim
      · rfl
    rw [absent,Arithmetic.mulZero]

/-- Pair the actual negative list with the detector for target (v₁,…,vₙ;b). -/
def negativeReading (field : ConstantField F q) (stem target : Tuple) (b : Nat)
    (h u v : Tuple) : F :=
  total (fun e : F × Tuple => e.1 * selected field stem target target.length b e.2)
    (withCoeff (-(1:F)) (concatenate (endings h) ((L q u v).flatMap (quasiShuffle [q-1]))))

private theorem source_layer (q c r m b : Nat) (s t target : Tuple)
    (same : (c::t).length = r+1+(target++[b]).length) :
    (endHead s ++ List.replicate r 1 ++ [m]).length + (target.length+1) = selectedDepth q s (c::t) := by
  have eqn := selected_layer q c r m s t (target++[b]) same
  simpa only [List.length_append,List.length_cons,List.length_nil] using eqn

/-- Both a one-argument generator and a general primitive generator use
their own minimal tuple as pivot. The right tuple v may be empty. -/
theorem general_negative_zero (field : ConstantField F q) (xs : Rows F q w)
    (s t h u v target : Tuple) (c r m b : Nat) (hc : 0<c)
    (valid_h : Valid h) (hu : u≠[]) (valid_v : Valid v) (hb₀ : 0<b) (hb : b≤q-1)
    (bounded : ∀ e∈xs, ∀ j∈e.2.val.1,j≤q)
    (first : ∀ e∈xs, source q s (c::t)=rowSource e ∨ Precedes (source q s (c::t)) (rowSource e))
    (same : (c::t).length = r+1+(target++[b]).length)
    (window : ImageWindow (component H xs) (h++(raiseFirst q (incLast u)++addLast (q-1) v))) :
    negativeReading field (endHead s++List.replicate r 1++[m]) target b h u v = 0 :=
  negative_in_window field xs s t h _ u v target c r m _ b hc valid_h valid_v hb₀ hb
    bounded first window (Nat.le_of_eq (general_suffix_depth q u v hu)) (source_layer q c r m b s t target same)

/-- Both constituent negative readings vanish at the pivot of the actual
type III difference. This also covers the case of an empty terminal t'. -/
theorem difference_negative_zero (field : ConstantField F q) (xs : Rows F q w)
    (s t h a u t' target : Tuple) (c r m b : Nat) (hc : 0<c)
    (valid_h : Valid h) (ha : a≠[]) (valid_u : Valid u) (hu : u≠[]) (valid_t : Valid t')
    (hb₀ : 0<b) (hb : b≤q-1)
    (bounded : ∀ e∈xs, ∀ j∈e.2.val.1,j≤q)
    (first : ∀ e∈xs, source q s (c::t)=rowSource e ∨ Precedes (source q s (c::t)) (rowSource e))
    (same : (c::t).length = r+1+(target++[b]).length)
    (window : ImageWindow (component H xs) (h++(raiseFirst q (incLast a)++(addLast q u++t')))) :
    let stem := endHead s++List.replicate r 1++[m]
    negativeReading field stem target b h a (incLast u++t')=0 ∧
    negativeReading field stem target b h (incLast a++u) t'=0 := by
  obtain ⟨le₁,le₂⟩ := difference_suffix_depths q a u t' ha hu
  have valid_right : Valid (incLast u++t') := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · apply endings_valid u valid_u (incLast u) _ x h
      cases u with
      | nil => contradiction
      | cons a u => simp [endings]
    · exact valid_t x h
  have layer := source_layer q c r m b s t target same
  exact ⟨negative_in_window field xs s t h _ a (incLast u++t') target c r m _ b
    hc valid_h valid_right hb₀ hb bounded first window (Nat.le_of_eq le₁) layer,
    negative_in_window field xs s t h _ (incLast a++u) t' target c r m _ b
    hc valid_h valid_t hb₀ hb bounded first window (by omega) layer⟩

end Megaera.Rev4Window
