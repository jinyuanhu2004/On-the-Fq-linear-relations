import Megaera.IntegralKernel

/-! # Theorem 2.9 with coefficients

An atom (c,s) represents c copies of the basis element s, for an arbitrary
coefficient c in the additive group of the field. The relations for combining
coefficients and dropping a zero coefficient present the direct sum of copies
of that group. Every square and triangle occurs with an arbitrary scalar.
No basis of the coefficient field over its prime field is needed.
-/

namespace Megaera.ScalarKernel
open Megaera.IntegralKernel Megaera.SplitKernel

/-- Coefficient collection at any generator. -/
inductive Collect (F A : Type) [Zero F] [Add F] :
    Word (F × A) → Word (F × A) → Prop
  | zero (u : A) : Collect F A (.atom (0,u)) .zero
  | add (a b : F) (u : A) :
      Collect F A (.atom (a+b,u)) (.plus (.atom (a,u)) (.atom (b,u)))

private def rowAtom (c : F) (h t : Tuple) : Word (F × Mark) := .atom (c,(h,t))

/-- The defining relations on coefficient-labelled marked pairs. -/
inductive Rows (F : Type) [Zero F] [Add F] (q : Nat) :
    Word (F × Mark) → Word (F × Mark) → Prop
  | collect {x y} : Collect F Mark x y → Rows F q x y
  | square (k : F) (p m t : Tuple) (r c : Nat) (hp : Valid p) (hm : Valid m) (ht : Valid t)
      (hr : 0 < r) (hc : 0 < c) : Rows F q
      (.plus (rowAtom k p (r :: (m ++ (q+c)::t))) (rowAtom k p (r :: (m ++ q::c::t))))
      (.plus (rowAtom k (p ++ (q+r)::m) (c::t)) (rowAtom k (p ++ q::r::m) (c::t)))
  | triangle (k : F) (p m : Tuple) (r : Nat) (hp : Valid p) (hm : Valid m) (hr : 0 < r) :
      Rows F q (rowAtom k p (r :: (m ++ [q])))
      (.plus (rowAtom k (p ++ (q+r)::m) []) (rowAtom k (p ++ q::r::m) []))

/-- Linear image under the actual tuple formula for L. -/
def image (q : Nat) : Word (F × Mark) → Word (F × Tuple)
  | .zero => .zero
  | .atom (k,h,[]) => .atom (k,h++[q])
  | .atom (k,h,c::t) => .plus (.atom (k,h++(q+c)::t)) (.atom (k,h++q::c::t))
  | .plus x y => .plus (image q x) (image q y)
  | .minus x y => .minus (image q x) (image q y)

def validWord : Word (F × Mark) → Prop
  | .zero => True
  | .atom (_,h,t) => Valid h ∧ Valid t
  | .plus x y | .minus x y => validWord x ∧ validWord y

private theorem eval_image [Zero V] [Add V] [Sub V] (q : Nat)
    (f : F → Tuple → V) (g : F × Mark → V)
    (agree : ∀ k h t, Valid h → Valid t → onRow q (f k) h t = g (k,h,t))
    (x : Word (F × Mark)) (hx : validWord x) :
    eval (fun p : F × Tuple => f p.1 p.2) (image q x) = eval g x := by
  induction x with
  | zero => rfl
  | atom p =>
    obtain ⟨k,h,t⟩ := p
    cases t <;> exact agree _ _ _ hx.1 hx.2
  | plus x y ix iy =>
    change eval _ (image q x) + eval _ (image q y) = eval _ x + eval _ y
    rw [ix hx.1,iy hx.2]
  | minus x y ix iy =>
    change eval _ (image q x) - eval _ (image q y) = eval _ x - eval _ y
    rw [ix hx.1,iy hx.2]

private theorem potential_zero [Zero V] [Add V] [Sub V] (q : Nat) (hq : 0 < q)
    (hsub : (0:V)-0 = 0) (g : Tuple → Tuple → V) (zero : ∀ h t, g h t = 0)
    (p t : Tuple) : potential q hq g p t = 0 := by
  cases eqT : t with
  | nil => rw [potential]
  | cons a u =>
    rw [potential]
    split
    · rw [zero, potential_zero q hq hsub g zero (p++[q]) ((a-q)::u),hsub]
    · split
      · exact zero _ _
      · exact potential_zero q hq hsub g zero (p++[a]) u
termination_by (weight t,t.length)
decreasing_by
  all_goals try rw [eqT]
  all_goals simp_wf <;> simp [weight] <;> omega

private theorem potential_add [Zero V] [Add V] [Sub V] (q : Nat) (hq : 0 < q)
    (sub : Subtraction V) (zero : (0:V)+0 = 0) (g f k : Tuple → Tuple → V)
    (he : ∀ h t, g h t = f h t + k h t) (p t : Tuple) :
    potential q hq g p t = potential q hq f p t + potential q hq k p t := by
  cases eqT : t with
  | nil => simp [potential,zero]
  | cons a u =>
    by_cases ha : q < a
    · have ih := potential_add q hq sub zero g f k he (p++[q]) ((a-q)::u)
      rw [potential.eq_2 q hq g p a u, potential.eq_2 q hq f p a u,
          potential.eq_2 q hq k p a u]
      simp only [if_pos ha,he,ih]
      rw [sub.collect]
    · by_cases hend : a=q ∧ u=[]
      · simp [potential,ha,hend,he]
      · have ih := potential_add q hq sub zero g f k he (p++[a]) u
        rw [potential.eq_2 q hq g p a u, potential.eq_2 q hq f p a u,
            potential.eq_2 q hq k p a u]
        simpa only [if_neg ha,if_neg hend] using ih
termination_by (weight t,t.length)
decreasing_by
  all_goals try rw [eqT]
  all_goals simp_wf <;> simp [weight] <;> omega

variable (F : Type) [Zero F] [Add F]

private def marked (q : Nat) (k : F) (h t : Tuple) : Presented (Rows F q) :=
  cls (Rows F q) (rowAtom k h t)

private theorem marked_compatible (q : Nat) (k : F) : Compatible q (marked F q k) where
  square p m t r c hp hm ht hr hc := Quotient.sound
    (Derives.rule (Rows.square (q := q) k p m t r c hp hm ht hr hc))
  triangle p m r hp hm hr := Quotient.sound
    (Derives.rule (Rows.triangle (q := q) k p m r hp hm hr))

private theorem marked_zero (q : Nat) (h t : Tuple) : marked F q 0 h t = 0 :=
  Quotient.sound (Derives.rule (Rows.collect (Collect.zero (h,t))))

private theorem marked_add (q : Nat) (a b : F) (h t : Tuple) :
    marked F q (a+b) h t = marked F q a h t + marked F q b h t :=
  Quotient.sound (Derives.rule (Rows.collect (Collect.add a b (h,t))))

/-- Every coefficient relation in ker L is generated by scalar multiples of
the two local relations in Theorem 2.9. The hypothesis on the input is
equality of formal tuple expressions, with coefficient collection allowed. -/
theorem kernel_spanned (q : Nat) (hq : 0 < q) (x y : Word (F × Mark))
    (hx : validWord x) (hy : validWord y)
    (hker : Derives (Collect F Tuple) (image q x) (image q y)) :
    Derives (Rows F q) x y := by
  let R := Rows F q
  let g := fun p : F × Mark => cls R (.atom p)
  let f := fun k : F => potential q hq (marked F q k) []
  have agree : ∀ k h t, Valid h → Valid t → onRow q (f k) h t = g (k,h,t) := by
    intro k h t hh ht
    have eq := integrate (laws R) q hq (marked F q k) (marked_compatible F q k)
      [] h t (by simp [Valid]) hh ht
    cases t <;> exact eq
  have resp : ∀ v w, Collect F Tuple v w →
      eval (fun p : F × Tuple => f p.1 p.2) v = eval (fun p : F × Tuple => f p.1 p.2) w := by
    intro v w rel
    cases rel with
    | zero t =>
      have zsub : (0 : Presented R) - 0 = 0 := by
        have e := (laws R).add_sub 0 0
        simpa only [IntegralKernel.addZero] using e
      exact potential_zero q hq zsub _ (marked_zero F q) [] t
    | add a b t =>
      exact potential_add q hq (laws R) (IntegralKernel.addZero 0) _ _ _ (marked_add F q a b) [] t
  have eq := sound IntegralKernel.addZero (laws R) _ resp hker
  rw [eval_image q f g agree x hx,eval_image q f g agree y hy] at eq
  exact Quotient.exact ((eval_cls R x).symm.trans (eq.trans (eval_cls R y)))

/-- Conversely every scalar multiple of a local relation has zero image. -/
theorem kernel_sound (q : Nat) (x y : Word (F × Mark)) (hx : validWord x) (hy : validWord y)
    (h : Derives (Rows F q) x y) : Derives (Collect F Tuple) (image q x) (image q y) := by
  let R := Collect F Tuple
  let f := fun (k : F) (t : Tuple) => cls R (.atom (k,t))
  let g := fun p : F × Mark => onRow q (f p.1) p.2.1 p.2.2
  have zeroC (t : Tuple) : f 0 t = 0 := Quotient.sound (Derives.rule (Collect.zero t))
  have addC (a b : F) (t : Tuple) : f (a+b) t = f a t + f b t :=
    Quotient.sound (Derives.rule (Collect.add a b t))
  have resp : ∀ s t, Rows F q s t → eval g s = eval g t := by
    intro s t rel
    cases rel with
    | collect hc =>
      cases hc with
      | zero p =>
        obtain ⟨u,v⟩ := p
        cases v with
        | nil => exact zeroC _
        | cons c t =>
          change f 0 _ + f 0 _ = 0
          rw [zeroC,zeroC,IntegralKernel.addZero]
      | add a b p =>
        obtain ⟨u,v⟩ := p
        cases v with
        | nil => exact addC _ _ _
        | cons c t =>
          change f (a+b) _ + f (a+b) _ = (f a _ + f a _) + (f b _ + f b _)
          rw [addC,addC]
          ac_rfl
    | square k p m t r c hp hm ht hr hc =>
      exact (onRow_compatible q (f k)).square p m t r c hp hm ht hr hc
    | triangle k p m r hp hm hr =>
      exact (onRow_compatible q (f k)).triangle p m r hp hm hr
  have eq := sound IntegralKernel.addZero (laws R) g resp h
  have agree : ∀ k p t, Valid p → Valid t → onRow q (f k) p t = g (k,p,t) := by intros; rfl
  rw [←eval_image q f g agree x hx,←eval_image q f g agree y hy] at eq
  exact Quotient.exact ((eval_cls R (image q x)).symm.trans (eq.trans (eval_cls R (image q y))))

/-- The coefficient version of the kernel presentation in Theorem 2.9. -/
theorem coefficient_kernel_iff (q : Nat) (hq : 0 < q) (x y : Word (F × Mark))
    (hx : validWord x) (hy : validWord y) :
    Derives (Collect F Tuple) (image q x) (image q y) ↔ Derives (Rows F q) x y :=
  ⟨kernel_spanned F q hq x y hx hy, kernel_sound F q x y hx hy⟩

/-- A marked pair has the common weight of the tuples in its image under L. -/
def markWeight (q : Nat) (p : Mark) := weight p.1 + q + weight p.2

/-- Every atom of this expression has the specified weight. -/
def homogeneous (q w : Nat) : Word (F × Mark) → Prop
  | .zero => True
  | .atom p => markWeight q p.2 = w
  | .plus x y | .minus x y => homogeneous q w x ∧ homogeneous q w y

/-- Only defining relations of weight w are available for this presentation. -/
def RowsAt (q w : Nat) (x y : Word (F × Mark)) : Prop :=
  Rows F q x y ∧ homogeneous F q w x ∧ homogeneous F q w y

private theorem rows_homogeneous {q : Nat} {x y : Word (F × Mark)} (rel : Rows F q x y) :
    ∃ d, homogeneous F q d x ∧ homogeneous F q d y := by
  cases rel with
  | collect h =>
    cases h with
    | zero p => exact ⟨_,rfl,True.intro⟩
    | add a b p => exact ⟨_,rfl,rfl,rfl⟩
  | square k p m t r c hp hm ht hr hc =>
    refine ⟨weight p + q + r + weight m + q + c + weight t, ?_⟩
    simp [homogeneous,rowAtom,markWeight,weight,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
  | triangle k p m r hp hm hr =>
    refine ⟨weight p + q + r + weight m + q, ?_⟩
    simp [homogeneous,rowAtom,markWeight,weight,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

private def projectAtom (q w : Nat) (p : F × Mark) : Presented (RowsAt F q w) :=
  if markWeight q p.2 = w then cls _ (.atom p) else 0

private theorem project_eq (q w : Nat) (x : Word (F × Mark)) (h : homogeneous F q w x) :
    eval (projectAtom F q w) x = cls (RowsAt F q w) x := by
  induction x with
  | zero => rfl
  | atom p => exact if_pos h
  | plus x y ix iy =>
    change eval _ x + eval _ y = _
    rw [ix h.1,iy h.2]
    rfl
  | minus x y ix iy =>
    change eval _ x - eval _ y = _
    rw [ix h.1,iy h.2]
    rfl

private theorem project_off (q w d : Nat) (hd : d ≠ w) (x : Word (F × Mark))
    (h : homogeneous F q d x) : eval (projectAtom F q w) x = 0 := by
  induction x with
  | zero => rfl
  | atom p => exact if_neg (fun e => hd (h.symm.trans e))
  | plus x y ix iy =>
    change eval _ x + eval _ y = 0
    rw [ix h.1,iy h.2,IntegralKernel.addZero]
  | minus x y ix iy =>
    change eval _ x - eval _ y = 0
    rw [ix h.1,iy h.2]
    simpa only [IntegralKernel.addZero] using (laws (RowsAt F q w)).add_sub 0 0

/-- In fixed weight the spanning derivation uses only coefficient collection
and local squares and terminal triangles of exactly that weight. -/
theorem kernel_spanned_at_weight (q w : Nat) (hq : 0 < q) (x y : Word (F × Mark))
    (hx : validWord x) (hy : validWord y) (hwx : homogeneous F q w x) (hwy : homogeneous F q w y)
    (ker : Derives (Collect F Tuple) (image q x) (image q y)) : Derives (RowsAt F q w) x y := by
  have respects : ∀ a b, Rows F q a b → eval (projectAtom F q w) a = eval (projectAtom F q w) b := by
    intro a b rel
    obtain ⟨d,ha,hb⟩ := rows_homogeneous F rel
    by_cases hd : d=w
    · subst d
      rw [project_eq F q w a ha, project_eq F q w b hb]
      exact Quotient.sound (Derives.rule (show RowsAt F q w a b from ⟨rel,ha,hb⟩))
    · rw [project_off F q w d hd a ha,project_off F q w d hd b hb]
  have e := sound IntegralKernel.addZero (laws (RowsAt F q w)) _ respects
    (kernel_spanned F q hq x y hx hy ker)
  rw [project_eq F q w x hwx,project_eq F q w y hwy] at e
  exact Quotient.exact e

/-- Theorem 2.9 in weight w, in both directions. -/
theorem coefficient_kernel_iff_at_weight (q w : Nat) (hq : 0 < q) (x y : Word (F × Mark))
    (hx : validWord x) (hy : validWord y) (hwx : homogeneous F q w x) (hwy : homogeneous F q w y) :
    Derives (Collect F Tuple) (image q x) (image q y) ↔ Derives (RowsAt F q w) x y := by
  refine ⟨kernel_spanned_at_weight F q w hq x y hx hy hwx hwy,?_⟩
  intro h
  apply kernel_sound F q x y hx hy
  let g := fun p : F × Mark => cls (Rows F q) (.atom p)
  have respects : ∀ a b, RowsAt F q w a b → eval g a = eval g b := by
    intro a b rel
    rw [eval_cls,eval_cls]
    exact Quotient.sound (Derives.rule rel.1)
  have e := sound IntegralKernel.addZero (laws (Rows F q)) g respects h
  rw [eval_cls,eval_cls] at e
  exact Quotient.exact e

end Megaera.ScalarKernel
