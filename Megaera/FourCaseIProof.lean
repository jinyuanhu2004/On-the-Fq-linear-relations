import Megaera.FourSupport
import Megaera.FourShapes

namespace Megaera.FourCaseIProof
open Megaera.FourCases Megaera.FourSupport Megaera.FourReduction Megaera.FourMinimum
open Megaera.Triangular Megaera.Splitting Megaera.Finite Megaera.Carlitz Megaera.Paper
variable {F : Type u} [Arithmetic F] [Neg F] {q w : Nat}

/-- Among positive tuples of fixed depth and weight, the tuple with
all entries 1 except possibly the last is lexicographically smallest. -/
private theorem ones_min (r z : Nat) (x : Tuple) (valid : Valid x)
    (len : x.length=r+1) (wt : weight x = weight (List.replicate r 1 ++ [z])) :
    x=List.replicate r 1 ++ [z] ∨ List.Lex (·<·) (List.replicate r 1 ++ [z]) x := by
  induction r generalizing x with
  | zero =>
    cases x with
    | nil => simp at len
    | cons a x =>
      have : x=[] := List.length_eq_zero_iff.mp (by simpa using len)
      subst x; left; simpa [weight] using wt
  | succ r ih =>
    cases x with
    | nil => simp at len
    | cons a x =>
      have ha := valid a (by simp)
      rw [List.replicate_succ,List.cons_append] at wt ⊢
      by_cases e : 1=a
      · subst a
        have h := ih x (fun b hb => valid b (List.mem_cons_of_mem _ hb)) (by simpa using len)
          (by simpa [weight] using wt)
        exact h.elim (fun e => .inl (congrArg (1::·) e)) (fun lt => .inr (.cons lt))
      · exact .inr (.rel (by omega))

/-- A prefix lower bound plus weight controls the whole Case I tuple. -/
private theorem least_at_prefix (p x : Tuple) (r z : Nat) (hv : Valid x)
    (lex : ¬ List.Lex (·<·) x p) (len : x.length=(p++(List.replicate r 1 ++ [z])).length)
    (wt : weight x = weight (p++(List.replicate r 1 ++ [z]))) :
    x=p++(List.replicate r 1 ++ [z]) ∨ List.Lex (·<·) (p++(List.replicate r 1 ++ [z])) x := by
  induction p generalizing x with
  | nil => exact ones_min r z x hv (by simpa using len) wt
  | cons a p ih =>
    cases x with
    | nil => simp at len
    | cons b x =>
      by_cases he : a=b
      · subst b
        have h := ih x (fun c hc => hv c (List.mem_cons_of_mem _ hc)) (fun hx => lex (.cons hx))
          (by simpa using len) (by simpa [weight] using wt)
        exact h.elim (fun e => .inl (congrArg (a::·) e)) (fun lt => .inr (.cons lt))
      · have lo : ¬ b<a := fun hb => lex (.rel hb)
        exact .inr (.rel (by omega))

private theorem addLast_ne_nil (k : Nat) (s : Tuple) : addLast k s ≠ [] := by
  cases s with
  | nil => simp [addLast]
  | cons b s => cases s <;> simp [addLast]

/-- In a bounded canonical prefix followed by ones, a positive generator's
marked block cannot finish strictly before the next marked entry. -/
theorem excludes_short_positive (hq : 2≤q) (s : Tuple) (r z : Nat)
    (bounded : ∀ j∈s,j≤q) (h a t : Tuple) (ha : Valid a) (an : a≠[]) (tn : t≠[]) :
    (if s=[] then [1] else incLast s) ++ (List.replicate r 1 ++ [z]) ≠
      h ++ (raiseFirst q (incLast a) ++ t) := by
  have eqr (b : Tuple) : source q [] b = raiseFirst q b := by cases b <;> rfl
  by_cases hs : s=[]
  · subst s
    simpa only [if_pos rfl,List.append_assoc,eqr] using case_I_excludes_types q hq [] 1 r z
      (by simp) (by omega) h a t ha an tn
  · have hs' := List.dropLast_concat_getLast hs
    have hb : ∀ j∈s.dropLast, j ≤ q := by
      intro j hj; apply bounded; rw [←hs']; exact List.mem_append_left _ hj
    have hz := bounded _ (List.getLast_mem hs)
    have no := case_I_excludes_types q hq s.dropLast (s.getLast hs+1) r z
      hb (by omega) h a t ha an tn
    rw [if_neg hs,(congrArg incLast hs').symm.trans (incLast_concat ..)]
    simpa only [List.append_assoc,List.singleton_append,eqr] using no

private theorem shape_impossible (field : ConstantField F q) (s : Tuple) (r z : Nat)
    (bounded : ∀ j∈s,j ≤ q) :
    ¬ Shape q w ((if s=[] then [1] else incLast s) ++ (List.replicate r 1 ++ [z])) := by
  have no := excludes_short_positive field.two_le s r z bounded
  intro shape
  generalize eqn : (if s=[] then [1] else incLast s) ++ (List.replicate r 1 ++ [z]) = y at shape
  cases shape with
  | general h a t _ ha an _ _ => exact no h a _ ha an (addLast_ne_nil (q-1) t) eqn
  | difference h a u t _ ha an _ _ _ _ =>
    exact no h a _ ha an (by simp [addLast_ne_nil]) eqn

/-- An illegal least coordinate survives every permitted elimination step. -/
theorem survives_at_illegal {v : Tuple → F} {m : Tuple} (least : Least v m)
    (illegal : ¬ Legal F q w m) :
    ¬ Reduces F q w (ImageWindow v) v (fun _ => 0) := by
  apply survives_of_functional (ImageWindow v) v (fun f => f m) rfl least.1
  intro b g t k hs first allowed
  have later : Precedes m t := by
    obtain ⟨i,hi,he⟩ := allowed
    have hm := least.2 i hi
    have mt : m=t ∨ Precedes m t := by
      rcases hm with rfl | hm <;> rcases he with rfl | he
      · exact .inl rfl
      · exact .inr he
      · exact .inr hm
      · exact .inr (precedes_trans hm he)
    rcases mt with rfl | h
    · exact (illegal ⟨g,hs,first⟩).elim
    · exact h
  have hz : g m=0 := by
    apply Classical.byContradiction
    intro hm
    rcases first.2 m hm with rfl | ht
    · exact precedes_irrefl _ later
    · exact precedes_irrefl _ (precedes_trans later ht)
  simp [addScaled,hz,Arithmetic.mulZero,Arithmetic.addZero]

/-- Case I of §4.3. The selected coordinate is the illegal minimum of
the actual H-image and survives all elimination permitted in that image. -/
theorem case_I_survives (field : ConstantField F q) (e : F × Row q w)
    (rows : Rows F q w) (r z : Nat) (nonzero : e.1 ≠ 0)
    (original : (e.2.val.2=List.replicate r 1 ++ [z] ∧ 0<z) ∨
      (e.2.val.2=[] ∧ r=0 ∧ z=0))
    (ordered : ∀ f∈rows, Precedes (rowSource e) (rowSource f))
    (bounded : ∀ f∈e::rows, ∀ i∈f.2.val.1, i≤q) :
    let s := e.2.val.1
    let target := (if s=[] then [1] else incLast s) ++ (List.replicate r 1 ++ [z+(q-1)])
    let v := component H (e::rows)
    Least v target ∧ ¬ Legal F q w target ∧ ¬ Reduces F q w (ImageWindow v) v (fun _ => 0) := by
  let s := e.2.val.1
  let t := e.2.val.2
  let p := if s=[] then [1] else incLast s
  let target := p ++ (List.replicate r 1 ++ [z+(q-1)])
  let v := component H (e::rows)
  have hit : v target ≠ 0 := by
    have coef := case_I_coefficient q w field.two_le e rows r z original ordered
      (fun f hf => bounded f (List.mem_cons_of_mem _ hf))
    exact fun hz => nonzero ((show v target=e.1 from coef).symm.trans hz)
  have grade {x : Tuple} (hx : v x ≠ 0) : Valid x ∧ weight x=w := by
    obtain ⟨f,_,hf⟩ := occurs_in_row hx
    have hw := H_weight q (by have := field.two_le; omega) _ _ x hf
    have hw' := f.2.property.2.2
    exact ⟨H_valid q field.two_le _ _ f.2.property.1 f.2.property.2.1 _ hf,by omega⟩
  have width : max 1 t.length = r+1 := by
    change (t=List.replicate r 1 ++ [z] ∧ 0<z) ∨ (t=[] ∧ r=0 ∧ z=0) at original
    rcases original with ⟨he,_⟩ | ⟨he,hr,_⟩
    · simp [he]
    · simp [he,hr]
  have orders (f) (hf : f∈e::rows) :
      source q s t = rowSource f ∨ Precedes (source q s t) (rowSource f) := by
    rcases List.mem_cons.mp hf with rfl | hf
    · exact .inl rfl
    · exact .inr (ordered f hf)
  have support (x : Tuple) (hx : v x ≠ 0) :
      (source q s t).length < x.length ∨
       ((source q s t).length=x.length ∧ s≠[] ∧ ¬List.Lex (·<·) x (incLast s)) := by
    cases et : t with
    | nil => exact component_support_terminal _ _ _ bounded (et ▸ orders) hx
    | cons c l =>
      have hvt : Valid t := e.2.property.2.1
      have hc := hvt c (et ▸ List.mem_cons_self)
      exact component_support _ s l x c hc bounded (et ▸ orders) hx
  have minimum : Least v target := by
    refine ⟨hit,?_⟩
    intro x hx
    have gx := grade hx
    have weights := gx.2.trans (grade hit).2.symm
    have hd := support x hx
    by_cases hs : s=[]
    · have sd : (source q s t).length=r+1 := by rw [source_depth,hs,width]; simp
      have td : target.length=r+2 := by simp [target,p,hs]
      have le : target.length ≤ x.length := by rcases hd with h | ⟨_,hn,_⟩ <;> first | omega | contradiction
      rcases Nat.lt_or_eq_of_le le with lt | eq
      · exact .inr (.inl lt)
      · have he : target = List.replicate (r+1) 1 ++ [z+(q-1)] := by simp [target,p,hs,List.replicate_succ]
        have hm := ones_min (r+1) (z+(q-1)) x gx.1 (by omega) (he ▸ weights)
        rw [←he] at hm
        exact hm.elim Or.inl (fun h => .inr (.inr ⟨eq,h⟩))
    · have plen : p.length=s.length := by
        dsimp only [p]; rw [if_neg hs]
        cases s with
        | nil => rfl
        | cons a u => exact incLast_length a u
      have td : target.length=(source q s t).length := by simp [target,plen,source_depth,width]
      rcases hd with h | ⟨eq,_,ge⟩
      · exact .inr (.inl (show target.length < x.length by omega))
      · have hm := least_at_prefix p x r (z+(q-1)) gx.1 (by simpa only [p,if_neg hs] using ge)
          (td.trans eq).symm weights
        exact hm.elim Or.inl (fun h => .inr (.inr ⟨td.trans eq,h⟩))
  have illegal : ¬ Legal F q w target := fun legal => shape_impossible field s r (z+(q-1))
    (bounded e (by simp)) ((legal_iff_shape field _).mp legal)
  exact ⟨minimum,illegal,survives_at_illegal minimum illegal⟩

end Megaera.FourCaseIProof
