import Megaera.FinalBinaryRows
import Megaera.FinalInduction

/-! Section 4 of the final edition, pages 24–25. The pivot of G is
its least support tuple. The algorithm stops as soon as that tuple is
illegal. The preliminary reduction of P may also remove later legal
coordinates while preserving its illegal minimum. -/
namespace Megaera.EditionOneFour
open Megaera.Finite Megaera.Paper Megaera.Carlitz Megaera.FourReduction Megaera.Triangular
open Megaera.CanonicalInd Megaera.FourMinimum
variable {F : Type u} [Arithmetic F] [Neg F] {q w : Nat}
local instance : Zero (Tuple → F) := ⟨fun _ => 0⟩

/-- Each of the three displayed generators has coefficient one at its pivot. -/
theorem pivot_coefficient (field : ConstantField F q) {g : Tuple → F} {s : Tuple}
    (hg : Special F q w g) (hs : Least g s) : g s=1 := by
  cases hg with
  | general h a t _ _ ha _ _ =>
    have m := lemma_4_1_i_ii (F:=F) q field.two_le h a t ha
    exact (equal_min hs (least_of_unit field m)).symm ▸ m.1
  | difference h a u t _ _ ha _ hu _ _ =>
    have m := lemma_4_1_iii q field h a u t ha hu
    exact (equal_min hs (least_of_unit field m)).symm ▸ m.1

private theorem subtract_minimum (field : ConstantField F q) {v g : Tuple → F} {s : Tuple}
    (hg : Special F q w g) (vg : Least v s) (gg : Least g s) :
    ∀ t,addScaled v (-(v s)) g t ≠ 0 → Precedes s t := by
  have zero : addScaled v (-(v s)) g s=0 := by
    simp only [addScaled,pivot_coefficient field hg gg,Arithmetic.mulOne,field.add_neg]
  intro t h
  have ne : t≠s := fun eq => h (eq ▸ zero)
  by_cases h' : v t=0
  · have n : g t≠0 := fun z => h (by rw [addScaled,h',z,Arithmetic.mulZero,Arithmetic.addZero])
    exact (gg.2 t n).resolve_left ne
  · exact (vg.2 t h').resolve_left ne

/-- Witness that each subtraction uses the least support tuple of its
own remainder and the coefficient prescribed on p. 25. -/
inductive LeastSteps (q w : Nat) : (Tuple → F) → (Tuple → F) → Prop
  | done (v) : LeastSteps q w v v
  | step {v g r s} : Least v s → Special F q w g → Least g s →
      LeastSteps q w (addScaled v (-(v s)) g) r → LeastSteps q w v r

theorem least_steps_end (field : ConstantField F q)
    (sound : ∀ g, Special F q w g → RelationVector q w g)
    (v : Tuple → F) (hv : RelationVector q w v) :
    ∃ r, RelationVector q w r ∧ LeastSteps q w v r ∧
      (r=0 ∨ ∃ t, Least r t ∧ ¬Legal F q w t) := by
  classical
  by_cases h0 : v=0
  · exact ⟨v,hv,.done _,.inl h0⟩
  obtain ⟨s,hv₁⟩ := least_of_nonzero v hv h0
  by_cases legal : Legal F q w s
  · obtain ⟨g,hg,first⟩ := legal
    let v' := addScaled v (-(v s)) g
    have inc := vectorRank_strict w v v' s (support_at_weight hv hv₁.1) hv₁.1
      (subtract_minimum field hg hv₁ first)
    obtain ⟨r,hr,steps,stop⟩ := least_steps_end field sound v' (relation_addScaled hv (sound _ hg) _)
    exact ⟨r,hr,.step hv₁ hg first steps,stop⟩
  · exact ⟨v,hv,.done _,.inr ⟨s,hv₁,legal⟩⟩
termination_by (Dimension.tuples Int.toNat w).length-vectorRank w v
decreasing_by
  change (Dimension.tuples Int.toNat w).length-vectorRank w v' < _
  have := vectorRank_bound w v'; omega

/-- The image cutoff used by the Case II functional is automatic at
every step, including after a change of the minimum. -/
private theorem in_window (field : ConstantField F q) {z v r : Tuple → F}
    (steps : LeastSteps q w v r)
    (start : ∀ t,v t≠0 → ImageWindow z t) :
    Reduces F q w (ImageWindow z) v r ∧ ∀ t,r t≠0 → ImageWindow z t := by
  induction steps with
  | done => exact ⟨.done _,start⟩
  | @step v g r s first hg gen _ ih =>
    have h := start s first.1
    have nextwin : ∀ t,addScaled v (-(v s)) g t≠0 → ImageWindow z t := by
      intro t ht
      have lt := subtract_minimum field hg first gen t ht
      obtain ⟨u,hu,e|h⟩ := h
      · exact ⟨u,hu,.inr (e ▸ lt)⟩
      · exact ⟨u,hu,.inr (precedes_trans h lt)⟩
    obtain ⟨moves,window⟩ := ih nextwin
    exact ⟨.step hg gen h first.1 (by
      simp only [addScaled,pivot_coefficient field hg gen,Arithmetic.mulOne,field.add_neg]) moves,window⟩

open Megaera.Rev4Geometry Megaera.Rev4Pairing Megaera.Rev4Negative Megaera.Splitting

/-- At every intermediate stage of Case II, S keeps its initial value,
and the current minimum has exactly the depth displayed on p. 24. -/
theorem case_II_pivot_depth (field : ConstantField F q) (xs : Rows F q w)
    (s t target : Tuple) (c r m b : Nat) (hc : 0<c)
    (hb : 0<b) (cap : b≤q-1) (edge : b=q-1 → ∃ j,target.length=j+1 ∧ FourLambda.entries (target++[b]) j=1)
    (bs : ∀ j∈s,j≤q) (bounded : ∀ e∈xs, ∀ j∈e.2.val.1,j≤q)
    (first : ∀ e∈xs, source q s (c::t)=rowSource e ∨ Precedes (source q s (c::t)) (rowSource e))
    (same : (c::t).length = r+1+(target++[b]).length)
    (v : Tuple → F) (pivot : Tuple) (steps : LeastSteps q w (component H xs) v) (least : Least v pivot) :
    let f := selected field (endHead s++List.replicate r 1++[m]) (target++[b]) target.length b
    reading w f (component H xs) ≠ 0 →
      reading w f v = reading w f (component H xs) ∧ pivot.length = selectedDepth q s (c::t) := by
  let stem := endHead s++List.replicate r 1++[m]
  let f := selected field stem (target++[b]) target.length b
  change reading w f (component H xs) ≠ 0 → reading w f v=reading w f (component H xs) ∧ _
  intro initial
  obtain ⟨moves,win⟩ := in_window field steps (fun t ht => ⟨t,ht,.inl rfl⟩)
  have stable {x y} (h : Reduces F q w (ImageWindow (component H xs)) x y) :
      reading w f y=reading w f x := by
    induction h with
    | done => rfl
    | step hg gmin window _ _ _ ih =>
      rw [ih,reading_addScaled,Rev4Survival.special_zero field xs s t target c r m b hc hb cap edge
        bs bounded first same hg gmin window, Arithmetic.mulZero,Arithmetic.addZero]
  have eqn := stable moves
  refine ⟨eqn, Nat.le_antisymm ?_ (imageWindow_depth xs s t pivot c hc bounded first (win _ least.1))⟩
  apply Classical.byContradiction
  intro big
  apply initial
  rw [←eqn]
  apply total_zero_of_members
  intro a _
  by_cases h : v a=0
  · simp only [h,zeroMul]
  · have pa : pivot.length ≤ a.length := by
      rcases least.2 a h with e | lt | ⟨eq,_⟩
      · rw [e]; exact Nat.le_refl _
      · exact Nat.le_of_lt lt
      · exact Nat.le_of_eq eq
    have layer := selected_layer q c r m s t (target++[b]) same
    change v a * selected field stem (target++[b]) target.length b a = 0
    rw [selected_long,Arithmetic.mulZero]
    simp only [List.length_append,List.length_cons,List.length_nil] at layer
    dsimp only [stem]
    simp only [List.length_append,List.length_cons,List.length_nil]
    omega

/-- The preliminary reduction of an illegal P keeps its least tuple and
annihilates all legal coordinates, a separate step on p. 24. -/
private theorem prepare (field : ConstantField F q)
    (sound : ∀ g, Special F q w g → RelationVector q w g) {v : Tuple → F} (hv : RelationVector q w v)
    {s : Tuple} (first : Least v s) (illegal : ¬Legal F q w s) :
    ∃ p, RelationVector q w p ∧ Reduced F q w p ∧ Least p s := by
  let after (t : Tuple) := t=s ∨ Precedes s t
  have up (t u : Tuple) (a : after t) (b : Precedes t u) : after u := by
    rcases a with rfl|a
    · exact .inr b
    · exact .inr (precedes_trans a b)
  obtain ⟨p,hp,red,allow,steps⟩ := normalize field sound after v hv first.2 up
  have keep {x y : Tuple → F} (steps : Reduces F q w after x y) : y s=x s := by
    induction steps with
    | done => rfl
    | @step x y g pivot k hg least allow _ _ _ ih =>
      have diff : pivot≠s := fun eq => illegal (eq ▸ ⟨g,hg,least⟩)
      have later := allow.resolve_left diff
      have zero : g s=0 := by
        apply Classical.byContradiction
        intro nz
        exact precedes_irrefl s (precedes_trans later ((least.2 s nz).resolve_left (Ne.symm diff)))
      rw [ih,addScaled,zero,Arithmetic.mulZero,Arithmetic.addZero]
  exact ⟨p,hp,red,⟨(keep steps).symm ▸ first.1,allow⟩⟩

private theorem no_illegal (field : ConstantField F q) (hq : 0<q)
    (sound : ∀ g, Special F q w g → RelationVector q w g)
    (nextRel : ∀ x : Tuple → F, RelationVector q w x → RelationVector q w (ind q w hq x))
    (inc : ∀ x : Tuple → F, RelationVector q w x → x ≠ 0 →
      vectorRank w x < vectorRank w (ind q w hq x))
    (survival : Survives F q w hq) (v : Tuple → F) (hv : RelationVector q w v)
    (s : Tuple) (least : Least v s) (illegal : ¬Legal F q w s) : False := by
  obtain ⟨p,hp,reduced,first⟩ := prepare field sound hv least illegal
  let z := ind q w hq p
  have nz : p≠0 := fun e => first.1 (congrFun e s)
  have above := above_of_rank p z s first (inc p hp nz)
  obtain ⟨r,hr,steps,stop⟩ := least_steps_end field sound z (nextRel p hp)
  obtain ⟨moves,win⟩ := in_window field steps (fun t ht => ⟨t,ht,.inl rfl⟩)
  rcases stop with zero|⟨t,first',bad⟩
  · rw [zero] at moves
    exact survival p hp reduced s first moves
  · have rise : vectorRank w v<vectorRank w r := by
      apply vectorRank_strict w v r s (support_at_weight hv least.1) least.1
      intro u hu
      obtain ⟨b,hb,rfl|h⟩ := win u hu
      · exact above b hb
      · exact precedes_trans (above b hb) h
    exact no_illegal field hq sound nextRel inc survival r hr t first' bad
termination_by (Dimension.tuples Int.toNat w).length-vectorRank w v
decreasing_by have := vectorRank_bound w r; omega

/-- Theorem 1.10 via the stopping rule of the final edition. No other
completeness theorem is used. Its external input is TT independence. -/
theorem theorem_1_10 (field : ConstantField F q) (tt : TTSpanning.TTPolynomialIndependent F q w)
    (p : FormalSum F) (hp : ∀ e∈p,Valid e.2 ∧ weight e.2=w) :
    Relation q w p ↔ InBCP q w p := by
  have hq : 0<q := by have := field.two_le; omega
  have law (e : Row q w) := FinalBinary.row_identity field _ _ e.property.1 e.property.2.1
  have sound := sound_of_binary (F:=F) q w field
    (fun u v s _ _ vs ns _ => FinalBinary.generator_binary field u v s vs ns)
  have special := fun g (hg : Special F q w g) => sound g (special_mem field hg)
  have survival := survival_of_cases field law tt (Rev4Completeness.case_II_survives field)
  have span := TTSpanning.canonical_spanning_of_theorem_1_2 field tt law
  have inc (v : Tuple → F) (hv : RelationVector q w v) (hn : v≠0) :
      vectorRank w v<vectorRank w (ind q w hq v) := by
    obtain ⟨c,hc,hb⟩ := span v hv
    exact Reduction.ind_rank_increases hq field v hn c hc hb
  rw [relation_iff_vector q w p hp,bcp_iff_vector]
  refine ⟨fun hv => ?_,sound _⟩
  obtain ⟨r,hr,steps,stop⟩ := least_steps_end field special _ hv
  obtain ⟨moves,_⟩ := in_window field steps (fun t ht => ⟨t,ht,.inl rfl⟩)
  rcases stop with zero|⟨s,least,bad⟩
  · exact bcp_of_reduces field (zero ▸ GradedBCP.zero_mem) moves
  · exact False.elim (no_illegal field hq special (FinalInduction.preserves field hq tt)
      inc survival r hr s least bad)

end Megaera.EditionOneFour
