import Megaera.PureWitness
import Megaera.Singletons

/-! Elimination of an H-kernel element, as in Theorem 2.16. At a fixed
left depth we process the greatest left weight first. A substitution
creates only rows of strictly greater left depth. -/
namespace Megaera.HKernelElimination
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.Singletons

variable {F : Type u} [Arithmetic F] [Neg F] {q w : Nat}
local instance : Zero (Tuple → F) := ⟨fun _ => 0⟩
local instance : Std.Associative (α := F) (· + ·) := ⟨Arithmetic.addAssoc⟩
local instance : Std.Commutative (α := F) (· + ·) := ⟨Arithmetic.addComm⟩

abbrev lhs (e : F × Row q w) := e.2.val.1
abbrev tailSum (b : Rows F q w) : FormalSum F := b.map (fun e => (e.1,e.2.val.2))

def Later (u l : Tuple) : Prop :=
  u.length < l.length ∨ (l.length = u.length ∧ weight l ≤ weight u ∧ l ≠ u)

omit [Arithmetic F] [Neg F] in
private theorem length_bound (e : F × Row q w) : (lhs e).length ≤ w := by
  have le (l : Tuple) (hv : Valid l) : l.length ≤ weight l := by
    induction l with
    | nil => exact Nat.le_refl _
    | cons a l ih =>
      have ha := hv a (by simp)
      have ih' := ih (fun b hb => hv b (List.mem_cons_of_mem _ hb))
      simp only [weight,List.length_cons]; omega
  have := le (lhs e) e.2.property.1
  have := e.2.property.2.2
  unfold lhs at *; omega

omit [Arithmetic F] [Neg F] in
private theorem wt_bound (e : F × Row q w) : weight (lhs e) ≤ w := by
  have := e.2.property.2.2; unfold lhs; omega

omit [Neg F] in
private theorem split_component (op : Nat → Tuple → Tuple → List Tuple) (u : Tuple)
    (c : Rows F q w) (x : Tuple) :
    component op c x = component op (c.filter (fun e => decide (lhs e=u))) x +
      component op (c.filter (fun e => !decide (lhs e=u))) x := by
  induction c with
  | nil => exact (Arithmetic.addZero _).symm
  | cons e c ih =>
    by_cases he : lhs e=u <;> simp only [List.filter_cons,he,decide_true,decide_false,
      Bool.not_true,Bool.not_false,Bool.false_eq_true,if_true,if_false]
    all_goals change _ + component op c x = _
    all_goals rw [ih]; unfold component; simp only [total]; ac_rfl

omit [Arithmetic F] [Neg F] in
private theorem count_drop {A : Type u} (f P : A → Bool) (l : List A) (e : A)
    (he : e ∈ l) (hp : P e) (hf : f e) :
    (l.filter (fun a => !(f a))).countP P < l.countP P := by
  have weak (s : List A) : (s.filter (fun a => !f a)).countP P ≤ s.countP P := by
    induction s with
    | nil => simp
    | cons a s ih => cases h : f a <;> cases k : P a <;> simp [h,k,List.countP_cons] <;> omega
  induction l with
  | nil => contradiction
  | cons a s ih =>
    rcases List.mem_cons.mp he with rfl | hm
    · simpa [hf,hp,List.countP_cons] using (Nat.lt_succ_of_le (weak s))
    · have h := ih hm
      cases h₁ : f a <;> cases h₂ : P a <;> simp [h₁,h₂,List.countP_cons] <;> omega

/-- A pivot condition on homogeneous rows. All same-depth competitors
have at most the pivot's weight. -/
def PivotReflection (F : Type u) [Arithmetic F] [Neg F] (q w : Nat) := ∀ (u : Tuple)
    (b r : Rows F q w), (∀ e∈b,lhs e=u) → (∀ e∈r,Later u (lhs e)) →
    (∀ x, component H b x + component H r x = 0) →
    HPlus q (coordinates (tailSum b))

theorem induction_on_kernel (pivot : PivotReflection F q w) (goal : Rows F q w → Prop)
    (base : goal [])
    (step : ∀ (u : Tuple) (b : Rows F q w), (∀ e ∈ b, lhs e = u) →
      HPlus q (coordinates (tailSum b)) →
      ∃ d : Rows F q w, (∀ e ∈ d, u.length < (lhs e).length) ∧ component H d = component H b ∧
        ∀ (r c : Rows F q w), (∀ op x, component op c x = component op b x + component op r x) →
          goal (r++d) → goal c)
    (c : Rows F q w) (ker : component H c = 0) : goal c := by
  classical
  let P (n k : Nat) (e : F × Row q w) := decide ((lhs e).length=n ∧ weight (lhs e)=k)
  let rec go (n k : Nat) (c : Rows F q w) (ker : component H c = 0)
      (bound : ∀ e∈c, n ≤ (lhs e).length ∧ ((lhs e).length=n → weight (lhs e)≤k)) :
      goal c := by
    by_cases z : c=[]
    · subst c; exact base
    have nc : n ≤ w := by
      cases c with
      | nil => contradiction
      | cons e c => exact Nat.le_trans (bound e (by simp)).1 (length_bound e)
    by_cases hx : ∃ e∈c, (lhs e).length=n ∧ weight (lhs e)=k
    · obtain ⟨e,he,hd,hw⟩ := hx
      let u := lhs e
      let f (a : F × Row q w) := decide (lhs a = u)
      let b := c.filter f
      let r := c.filter (fun a => !f a)
      have hb (a) (ha : a ∈ b) : lhs a = u := by simpa [f] using (List.mem_filter.mp ha).2
      have hr (a) (ha : a ∈ r) : Later u (lhs a) := by
        have B := bound a (List.mem_filter.mp ha).1
        have ne : lhs a ≠ u := by simpa [f] using (List.mem_filter.mp ha).2
        dsimp [Later,u]; by_cases lt : n < (lhs a).length
        · left; omega
        · right; exact ⟨by omega,(by rw [hw]; exact B.2 (by omega)), ne⟩
      have splitc (op) (x : Tuple) : component op c x = component op b x + component op r x :=
        split_component op u c x
      have hz (x : Tuple) : component H b x + component H r x = 0 := by
        rw [← splitc,ker]; rfl
      obtain ⟨d,long,subH,diff⟩ := step u b hb (pivot u b r hb hr hz)
      have k' : component H (r++d) = 0 := by
        funext x
        rw [component_append,subH,Arithmetic.addComm,hz]; rfl
      have b' (a) (ha : a∈r++d) : n ≤ (lhs a).length ∧ ((lhs a).length=n → weight (lhs a)≤k) := by
        rcases List.mem_append.mp ha with ha | ha
        · exact bound a (List.mem_filter.mp ha).1
        · have h := long a ha; change (lhs e).length < (lhs a).length at h; omega
      have decrease : (r++d).countP (P n k) < c.countP (P n k) := by
        have hnil : d.countP (P n k)=0 := by
          apply List.countP_eq_zero.mpr
          intro a ha
          have h := long a ha; change (lhs e).length < (lhs a).length at h
          simp [P,show (lhs a).length≠n by omega]
        rw [List.countP_append,hnil,Nat.add_zero]
        exact count_drop f (P n k) c e he (by simp [P,hd,hw]) (by simp [f,u])
      exact diff r c splitc (go n k (r++d) k' b')
    · cases k with
      | zero =>
        apply go (n+1) w c ker
        intro a ha
        have v := bound a ha
        have l : (lhs a).length ≠ n := fun h => hx ⟨a,ha,h,by have := v.2 h; omega⟩
        exact ⟨by omega,fun _ => wt_bound a⟩
      | succ k =>
        apply go n k c ker
        intro a ha
        have v := bound a ha
        refine ⟨v.1,fun hh => ?_⟩
        have := v.2 hh
        have ne : weight (lhs a) ≠ k+1 := fun h => hx ⟨a,ha,hh,h⟩
        omega
  termination_by (w+1-n,k,c.countP (fun e => decide ((lhs e).length=n ∧ weight (lhs e)=k)))
  decreasing_by all_goals first | exact Prod.Lex.right _ (Prod.Lex.right _ decrease) | exact Prod.Lex.left _ _ (by omega) | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega))
  exact go 0 w c ker (fun a _ => ⟨Nat.zero_le _,fun _ => wt_bound a⟩)

theorem kernel_of_pivot (field : ConstantField F q) (pivot : PivotReflection F q w)
    (c : Rows F q w) (ker : component H c = 0) : BCPVector q w (component L c) := by
  apply induction_on_kernel pivot (fun c => BCPVector q w (component L c)) GradedBCP.zero_mem _ c ker
  intro u b hb inside
  obtain ⟨d,long,subH,diff⟩ := PureWitness.replace_block field u b hb inside
  refine ⟨d,long,subH,?_⟩
  intro r c splitc ih
  have g := GradedBCP.add_mem diff ih
  have eqv : (fun x => (component L b x + (-component L d x)) + component L (r++d) x) =
      component L c := by
    funext x
    rw [splitc,component_append]
    calc _ = (component L b x + component L r x) + (component L d x + (-component L d x)) := by ac_rfl
         _ = _ := by rw [field.add_neg, Arithmetic.addZero]
  exact eqv ▸ g

end Megaera.HKernelElimination
