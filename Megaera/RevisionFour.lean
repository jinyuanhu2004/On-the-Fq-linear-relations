import Megaera.RevisionTwo
import Megaera.FourConclusion

/-! The signed special relation in the revised Case II support argument
(pp. 24–25 of Megaera (4)). All coefficients below are over the constant
field of order q. The computation is symbolic in q. -/
namespace Megaera.RevisionFour
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.FourLambda
open Megaera.Triangular Megaera.FourReduction
variable {F : Type u} [Arithmetic F] [Neg F]

/-- The λ-sum at n=0, b=1 reads a single coordinate after any fixed stem. -/
theorem reads_coordinate (q : Nat) (field : ConstantField F q) (stem : Tuple)
    (p : FormalSum F) :
    total (fun e => match e.2.drop stem.length with
      | [z] => if e.2.take stem.length=stem ∧ z%(q-1)=1%(q-1) then
          e.1 * lambda q field.two_le 0 1 (entries []) (entries [z]) else 0
      | _ => 0) p = coordinates p (stem++[1]) := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    rcases e with ⟨k,t⟩
    rw [total,ih]
    change _ + _ = (if t=stem++[1] then k else 0) + _
    apply congrArg (· + _)
    by_cases h : t=stem++[1]
    · subst t; simp [FourInvariant.one_entry field,Arithmetic.mulOne]
    · rw [if_neg h]
      have missing : ¬(t.take stem.length=stem ∧ t.drop stem.length=[1]) := by
        rintro ⟨h1,h2⟩
        exact h (by rw [←List.take_append_drop stem.length t,h1,h2])
      cases hd : t.drop stem.length with
      | nil => simp [hd]
      | cons z tail =>
        cases tail with
        | cons => simp [hd]
        | nil =>
          by_cases hz : z=1
          · subst z; simp_all
          · simp [hd,FourInvariant.one_entry field,hz,Arithmetic.mulZero]

omit [Neg F] in
/-- The selected H-row itself has coefficient one at the coordinate used
in the revised detector. -/
theorem selected_coefficient (q : Nat) (hq : 3≤q) :
    coordinates (withCoeff (1:F) (H q [1] [1,q+1,1])) [2,1,2*q,1] = 1 := by
  simp [coordinates,withCoeff,H,concatenate,endings,incLast,quasiShuffle,total,
    Arithmetic.addZero,zeroAdd,show q-1+(q+1)=2*q by omega,
    show q-1+1≠1 by omega,show q+1≠2*q by omega]

/-- Negative merge across a proper prefix of the selected stem. The
positive part starts in 1. The unique negative contribution is the merge
of q−1 with q+1 after the prefix (2,1). -/
theorem shorter_stem_value (q : Nat) (hq : 3≤q) :
    liftP (F:=F) q [1] [1] [1,1] [2,1,2*q,1] = -(1:F) := by
  unfold liftP generalP
  rw [←List.map_flatMap,PrimitiveRows.bStar_expansion]
  simp [coordinates,withCoeff,H,L,concatenate,start,endings,incLast,quasiShuffle,total,
    Arithmetic.addZero,zeroAdd,show q+1≠1 by omega,show q-1+1≠1 by omega,
    show q-1+(q+1)=2*q by omega,show q+1≠2*q by omega]

/-- For s=(1), t′=(1,q+1,1) this legal Type II generator satisfies the
printed pivot and exact depth restrictions. Its shifted prefix (2) is
strictly shorter than the marker (2,1,2q), and the λ-reading is nonzero. -/
theorem shorter_stem_obstruction (q : Nat) (hq : 3≤q) (field : ConstantField F q) :
    let g := liftP (F:=F) q [1] [1] [1,1]
    Special F q (2*q+4) g ∧ Least g [1,q+2,1,q] ∧
    Precedes [1,q+1,q+1,1] [1,q+2,1,q] ∧
    [1].length+[1].length+max [1,1].length 1=[1,q+1,q+1,1].length ∧
    (incLast [1]).length < [2,1,2*q].length ∧
    g [2,1,2*q,1] ≠ 0 := by
  dsimp only
  refine ⟨.general [1] [1] [1,1] (by simp [Valid]) (by simp [Valid]) (by simp)
    (by simp [Valid]) (by simp [weight]; omega),?_,.inr ⟨rfl,.cons (.rel (by omega))⟩,
    rfl,by change 1 < 3; decide,?_⟩
  · have u := FourMinimum.lemma_4_1_i_ii (F:=F) q field.two_le [1] [1] [1,1] (by simp)
    have pivot : FourMinimum.UnitMinimum (liftP (F:=F) q [1] [1] [1,1]) [1,q+2,1,q] := by
      simpa [FourMinimum.raiseFirst,FourMinimum.addLast,incLast,show q-1+1=q by omega,
        liftP,FourMinimum.lifted] using u
    refine ⟨fun h => field.nontrivial (h ▸ pivot.1),fun t ht => ?_⟩
    rcases precedes_trichotomy [1,q+2,1,q] t with lt | eq | lt
    · exact .inr lt
    · exact .inl eq.symm
    · exact False.elim (ht (pivot.2 t lt))
  · rw [shorter_stem_value q hq]
    intro h
    have hn := field.add_neg 1
    rw [h,Arithmetic.addZero] at hn
    exact field.nontrivial hn.symm

omit [Neg F] in
/-- Starting elimination at the minimum of the actual H-image excludes
this pivot for every bounded canonical presentation with the given least
source. -/
theorem shorter_stem_outside_image {q w : Nat} (xs : Rows F q w)
    (bounded : ∀ e ∈ xs, ∀ j ∈ e.2.val.1, j ≤ q)
    (first : ∀ e ∈ xs, [1,q+1,q+1,1] = rowSource e ∨ Precedes [1,q+1,q+1,1] (rowSource e)) :
    ¬ ImageWindow (component H xs) [1,q+2,1,q] := by
  rintro ⟨x,nz,order⟩
  have out := FourSupport.component_support xs [1] [q+1,1] x 1 (by decide) bounded first nz
  have upper : x.length ≤ 4 ∧ List.Lex (·<·) x [2] ∨ x.length < 4 := by
    have pivotLex : List.Lex (·<·) [1,q+2,1,q] [2] := .rel (by decide)
    rcases order with rfl | (d | ⟨d,lex⟩)
    · exact .inl ⟨Nat.le_refl _,pivotLex⟩
    · exact .inr d
    · exact .inl ⟨Nat.le_of_eq d,List.lex_trans (fun h₁ h₂ => Nat.lt_trans h₁ h₂) lex pivotLex⟩
  change 4<x.length ∨ (4=x.length ∧ _ ∧ ¬ List.Lex (·<·) x [2]) at out
  rcases upper with ⟨len,lex⟩ | len
  · rcases out with h | h
    · omega
    · exact h.2.2 lex
  · rcases out with h | ⟨h,_⟩ <;> omega

private theorem marked_head {q a : Nat} {s rest t : Tuple} (hs : Valid s) (hn : s≠[])
    (eq : a::t = FourMinimum.raiseFirst q (incLast s) ++ rest) : q<a := by
  cases s with
  | nil => contradiction
  | cons z tail =>
    have pos := hs z (by simp)
    cases tail with
    | nil =>
      have he := congrArg List.head? eq
      simp [FourMinimum.raiseFirst,incLast] at he
      omega
    | cons j tail =>
      have he := congrArg List.head? eq
      simp [FourMinimum.raiseFirst,incLast] at he
      omega

/-- Entries at most q at the start of a pivot must belong to the arbitrary
left prefix of its Lemma 4.1 shape. -/
theorem strip_bounded_head {q w a : Nat} {t : Tuple} (ha : a≤q)
    (shape : Shape q w (a::t)) : Shape q (w-a) t := by
  generalize eq : a::t=x at shape
  cases shape with
  | general h s v hh hs hn hv hw =>
    cases h with
    | nil => exact False.elim (Nat.not_lt_of_ge ha (marked_head hs hn eq))
    | cons j h =>
      obtain ⟨rfl,rfl⟩ := List.cons.inj eq
      exact .general h s v (fun i hi => hh i (by simp [hi])) hs hn hv
        (by simp only [weight] at hw; omega)
  | difference h s u v hh hs hn hu un hv hw =>
    cases h with
    | nil => exact False.elim (Nat.not_lt_of_ge ha (marked_head hs hn eq))
    | cons j h =>
      obtain ⟨rfl,rfl⟩ := List.cons.inj eq
      exact .difference h s u v (fun i hi => hh i (by simp [hi])) hs hn hu un hv
        (by simp only [weight] at hw; omega)

private theorem prefix_shape {q w a : Nat} {t : Tuple} (ha : 0<a) (shape : Shape q w t) :
    Shape q (a+w) (a::t) := by
  have pos (h : Tuple) (hh : Valid h) : Valid (a::h) := by
    intro i hi; rcases List.mem_cons.mp hi with rfl | hi
    · exact ha
    · exact hh i hi
  cases shape with
  | general h s v hh hs hn hv hw =>
    exact .general (a::h) s v (pos h hh) hs hn hv (by simp only [weight]; omega)
  | difference h s u v hh hs hn hu un hv hw =>
    exact .difference (a::h) s u v (pos h hh) hs hn hu un hv (by simp only [weight]; omega)

/-- Both tuples of the chosen L-row meet the manuscript's reduced-support
condition. This is a statement about canonical rows, without asserting that
an individual L-row is a CMPL relation. -/
theorem selected_row_reduced (q w : Nat) (hq : 3≤q) (field : ConstantField F q) :
    ∀ x∈L q [1] [1,q+1,1], ¬Legal F q w x := by
  intro x hx legal
  have shape := (legal_iff_shape field x).mp legal
  have one : 1≤q := by omega
  simp [L,start] at hx
  rcases hx with rfl | rfl
  · have shorter := strip_bounded_head one (strip_bounded_head (Nat.le_refl q) (strip_bounded_head one shape))
    exact obstruction_illegal q _ hq (prefix_shape (a:=q+1) (by omega) shorter)
  · exact obstruction_illegal q _ hq (strip_bounded_head one shape)

end Megaera.RevisionFour
