import Megaera.RowEvaluation
import Megaera.BCPRows

/-! Straightening arbitrary homogeneous L-rows into bounded-prefix rows. -/
namespace Megaera.FinalCanonical
open Megaera.Finite Megaera.Paper Megaera.Carlitz Megaera.BCPRows Megaera.Splitting
variable {F : Type u} [Arithmetic F] [Neg F] {q w : Nat}

abbrev Bounded (xs : Rows F q w) := ∀ e ∈ xs, ∀ a ∈ e.2.val.1, a ≤ q

private theorem cut_large (q : Nat) (h : Tuple) (bad : ¬∀ a∈h,a≤q) :
    ∃ p a l, h=p++a::l ∧ (∀ i∈p,i≤q) ∧ q<a := by
  induction h with
  | nil => simp at bad
  | cons a h ih =>
    by_cases small : a≤q
    · obtain ⟨p,b,l,rfl,bp,large⟩ := ih (fun H => bad (List.forall_mem_cons.mpr ⟨small,H⟩))
      exact ⟨a::p,b,l,rfl,List.forall_mem_cons.mpr ⟨small,bp⟩,large⟩
    · exact ⟨[],a,h,rfl,by simp,by omega⟩

private theorem depth_bound (h : Tuple) (vh : Valid h) : h.length≤weight h := by
  induction h with
  | nil => exact Nat.le_refl _
  | cons a h ih =>
    have := vh a (by simp)
    have := ih (fun i hi => vh i (List.mem_cons_of_mem _ hi))
    simp only [weight,List.length_cons]; omega

omit [Arithmetic F] [Neg F] in
private theorem bounded_pack (k : F) (l : List (Tuple × Tuple)) (ok : ∀ z∈l,Good q w z)
    (small : ∀ z∈l,∀ a∈z.1,a≤q) : Bounded (pack k l ok) := by
  induction l with
  | nil => simp [Bounded,pack]
  | cons a l ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact small _ (by simp)
    · exact ih _ (fun z hz => small z (by simp [hz])) _ he

/-- A finite, homogeneous certificate for each individual row, for arbitrary scalar. -/
theorem straighten (field : ConstantField F q) (k : F) (h t : Tuple)
    (vh : Valid h) (vt : Valid t) (wt : weight h+weight t+q=w) :
    ∃ xs : Rows F q w, Bounded xs ∧ component L xs =
      fun x => k*coordinates (withCoeff 1 (L q h t)) x := by
  classical
  by_cases bound : ∀ a∈h,a≤q
  · exact ⟨[(k,⟨(h,t),vh,vt,wt⟩)],by simpa [Bounded],funext (fun _ => Arithmetic.addZero _)⟩
  · obtain ⟨p,a,l,rfl,bp,large⟩ := cut_large q h bound
    let r := a-q
    have ar : a=q+r := by dsimp [r]; omega
    have rp : 0<r := by omega
    have qp := field.two_le
    have vp : Valid p := fun i hi => vh i (by simp [hi])
    have vl : Valid l := fun i hi => vh i (by simp [hi])
    have newValid : Valid (p++q::r::l) := by
      intro i hi; simp only [List.mem_append,List.mem_cons] at hi
      rcases hi with hi|rfl|rfl|hi
      · exact vp _ hi
      · omega
      · exact rp
      · exact vl _ hi
    have newWeight : weight (p++q::r::l)+weight t+q=w := by
      simp only [weight_append,weight] at wt ⊢; omega
    obtain ⟨ys,byz,ey⟩ := straighten field (-k) (p++q::r::l) t newValid vt newWeight
    let terms := (L q (r::l) t).map (fun v => (p,v))
    have validR : Valid (r::l) := List.forall_mem_cons.mpr ⟨rp,vl⟩
    have ok : ∀ z∈terms,Good q w z := by
      intro z hz; obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hz
      refine ⟨vp,L_valid q (by omega) _ _ validR vt v hv,?_⟩
      have weightV := L_weight q (r::l) t v hv
      simp only [weight_append,weight] at wt weightV; dsimp; omega
    let xs := pack k terms ok
    have bounded : Bounded xs := bounded_pack k terms ok (by
      intro z hz; obtain ⟨v,_,rfl⟩ := List.mem_map.mp hz; exact bp)
    refine ⟨xs++ys,fun e he => (List.mem_append.mp he).elim (bounded e) (byz e),?_⟩
    funext x
    have perm := PrimitiveRows.prefixed_L_cancels q r p l t
    have eq := coord_perm (perm.map (fun z => (k,z))) x
    change coordinates (withCoeff k _) x=coordinates (withCoeff k _) x at eq
    simp only [start,List.flatMap_cons,List.flatMap_nil,List.append_nil] at eq
    rw [rows_append,ey,show component L xs x = _ from pack_component L k terms ok x]
    simp only [terms,List.flatMap_map,Function.comp_def]
    rw [←eq]
    simp only [withCoeff,List.map_append,coord_append]
    rw [show coordinates (List.map (fun z => (k,z)) (L q (p++q::r::l) t)) x =
      k*coordinates (withCoeff 1 (L q (p++q::r::l) t)) x from coeff_scale ..]
    rw [show coordinates (List.map (fun z => (k,z)) (L q (p++(q+r)::l) t)) x =
      k*coordinates (withCoeff 1 (L q (p++(q+r)::l) t)) x from coeff_scale ..]
    rw [neg_mul field,←ar]
    letI : Std.Commutative (α:=F) (·+·) := ⟨Arithmetic.addComm⟩
    letI : Std.Associative (α:=F) (·+·) := ⟨Arithmetic.addAssoc⟩
    calc _ = (k*coordinates (withCoeff 1 (L q (p++a::l) t)) x) + ((k*coordinates (withCoeff 1 (L q (p++q::r::l) t)) x) +
          -(k*coordinates (withCoeff 1 (L q (p++q::r::l) t)) x)) := by ac_rfl
         _ = _ := by rw [field.add_neg,Arithmetic.addZero]; rfl
termination_by weight h-h.length
decreasing_by
  subst_vars
  have d := depth_bound (p++q::r::l) newValid
  simp only [weight_append,weight,List.length_append,List.length_cons] at d ⊢
  omega

/-- Theorem 2.8, as equality of the two spans on every coefficient vector. -/
theorem theorem_2_8 (field : ConstantField F q) (v : Tuple → F) :
    (∃ xs : Rows F q w, component L xs=v) ↔
    ∃ xs : Rows F q w, Bounded xs ∧ component L xs=v := by
  constructor
  · rintro ⟨xs,rfl⟩
    induction xs with
    | nil => exact ⟨[],by simp [Bounded],rfl⟩
    | cons a xs ih =>
      obtain ⟨ys,hy,ey⟩ := ih
      obtain ⟨zs,hz,ez⟩ := straighten field a.1 _ _ a.2.property.1 a.2.property.2.1 a.2.property.2.2
      exact ⟨zs++ys,fun e he => (List.mem_append.mp he).elim (hz e) (hy e),
        funext (fun x => by rw [rows_append,ez,ey]; rfl)⟩
  · rintro ⟨xs,_,hv⟩; exact ⟨xs,hv⟩

end Megaera.FinalCanonical
