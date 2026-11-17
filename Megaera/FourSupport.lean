import Megaera.FourMinimum
import Megaera.FourCases

/-! The first depth that can occur in Ind P for a nonempty distinguished
tail, using only the ordering of the canonical row sources. -/
namespace Megaera.FourSupport
open Megaera.Triangular Megaera.Splitting Megaera.FourCases Megaera.Finite Megaera.Carlitz Megaera.Paper

private theorem prefix_bound (q a : Nat) (s h : Tuple) (b m : Nat) (r y v : Tuple)
    (hm : q<m ∨ h.length≤s.length) (bounded : ∀ i ∈ h++[b], i≤q)
    (ord : ¬List.Lex (·<·) ((h++[b])++y) ((s++[a])++m::r)) :
    ¬List.Lex (·<·) (h++(b+1)::v) (s++[a+1]) := by
  induction s generalizing h with
  | nil =>
    cases h with
    | nil =>
      intro bad
      rcases List.cons_lex_cons_iff.mp bad with e | ⟨_,e⟩
      · exact ord (.rel (by omega))
      · cases e
    | cons c h =>
      intro bad
      rcases List.cons_lex_cons_iff.mp bad with e | ⟨_,e⟩
      · by_cases small : c<a
        · exact ord (.rel small)
        · have eqc : c=a := by omega
          subst c
          apply ord; apply List.Lex.cons
          rcases hm with gm | len
          · cases h with
            | nil => have hb := bounded b (by simp); exact .rel (by omega)
            | cons j h => have hj := bounded j (by simp); exact .rel (by omega)
          · simp at len
      · cases h <;> cases e
  | cons c s ih =>
    cases h with
    | nil =>
      intro bad
      rcases List.cons_lex_cons_iff.mp bad with e | ⟨e,_⟩ <;>
        exact ord (.rel (by omega))
    | cons j h =>
      intro bad
      rcases List.cons_lex_cons_iff.mp bad with e | ⟨e,tail⟩
      · exact ord (.rel e)
      · subst j
        exact ih h (by simpa using hm) (fun i hi => bounded i (List.mem_cons_of_mem _ hi))
          (fun z => ord (.cons z)) tail

private theorem source_join (q : Nat) (h t : Tuple) : source q h t = h++source q [] t := by
  cases t <;> rfl

private theorem ord_depth {x y : Tuple} (h : x=y ∨ Precedes x y) : x.length≤y.length := by
  rcases h with rfl | (a | ⟨a,_⟩)
  · exact Nat.le_refl _
  · exact Nat.le_of_lt a
  · exact Nat.le_of_eq a

private theorem ord_lex {x y : Tuple} (h : x=y ∨ Precedes x y) (d : x.length=y.length) :
    ¬List.Lex (·<·) y x := by
  rcases h with rfl | (a | ⟨_,a⟩)
  · exact List.lex_irrefl Nat.lt_irrefl _
  · change x.length<y.length at a; omega
  · exact fun b => List.lex_irrefl Nat.lt_irrefl _ (List.lex_trans (fun u v => Nat.lt_trans u v) a b)

/-- For a nonempty left prefix s and nonempty right tail t, every
competing H term in the source depth is lexicographically at least s⁺¹,
viewed as a prefix. In particular its first discrepancy from s⁺¹ cannot
be a decrease. -/
theorem nonempty_prefix_bound (q a c : Nat) (s t h u x : Tuple)
    (hc : 0<c) (bounded : ∀ j∈h, j≤q)
    (order : source q (s++[a]) (c::t) = source q h u ∨
      Precedes (source q (s++[a]) (c::t)) (source q h u))
    (occ : x∈ H q h u) (depth_eq : x.length=(source q (s++[a]) (c::t)).length) :
    ¬List.Lex (·<·) x (incLast (s++[a])) := by
  have le := ord_depth order
  have ge := depth_ge_source q h u x occ
  have eqd : (source q (s++[a]) (c::t)).length=(source q h u).length := by omega
  obtain ⟨p,b,v,rfl,rfl,_,_⟩ := minimal_H_parts q h u x occ (depth_eq.trans eqd)
  have ord := ord_lex order eqd
  rw [source_join q (p++[b]) u] at ord
  rw [incLast_concat]
  exact prefix_bound q a s p b (q+c) t _ v (.inl (by omega)) bounded ord

/-- At an empty distinguished prefix, a nonempty right tail gains at
least one unit of depth throughout Ind P. -/
theorem empty_prefix_depth (q c : Nat) (t h u x : Tuple) (hc : 0<c)
    (bounded : ∀ j∈h, j≤q) (order : source q [] (c::t)=source q h u ∨
      Precedes (source q [] (c::t)) (source q h u)) (occ : x∈H q h u) :
    (source q [] (c::t)).length < x.length := by
  have le := ord_depth order
  have ge := depth_ge_source q h u x occ
  apply Classical.byContradiction
  intro hno
  have eqd : (source q [] (c::t)).length=(source q h u).length := by omega
  have eqx : x.length=(source q h u).length := by omega
  obtain ⟨p,b,v,rfl,_,_,_⟩ := minimal_H_parts q h u x occ eqx
  have ord := ord_lex order eqd
  rw [source_join q (p++[b]) u] at ord
  apply ord
  cases p with
  | nil => have hb := bounded b (by simp); exact .rel (by omega)
  | cons j p => have hj := bounded j (by simp); exact .rel (by omega)


variable {F : Type u} [Arithmetic F] {q w : Nat}

theorem occurs_in_row {xs : Rows F q w} {x : Tuple} (hx : component H xs x ≠ 0) :
    ∃ e∈xs, x∈H q e.2.val.1 e.2.val.2 := by
  apply Classical.byContradiction
  intro no
  apply hx
  apply total_zero_of_members
  intro e he
  have vanish : coordinates (withCoeff (1:F) (H q e.2.val.1 e.2.val.2)) x=0 := by
    apply total_zero_of_members
    intro z hz
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hz
    exact if_neg (fun eq:v=x => no ⟨e,he,eq ▸ hv⟩)
  rw [vanish,Arithmetic.mulZero]

/-- The bound on the whole H-image after coefficient collection. For
nonempty s, at the least source depth no surviving coefficient can
precede the prefix s⁺¹. For empty s the entire layer is zero. -/
theorem component_support (xs : Rows F q w) (s t x : Tuple) (c : Nat) (hc : 0<c)
    (bounded : ∀ e∈xs, ∀ j∈e.2.val.1,j≤q)
    (first : ∀ e∈xs, source q s (c::t)=rowSource e ∨ Precedes (source q s (c::t)) (rowSource e))
    (hx : component H xs x ≠ 0) :
    (source q s (c::t)).length < x.length ∨
      ((source q s (c::t)).length = x.length ∧ s≠[] ∧ ¬List.Lex (·<·) x (incLast s)) := by
  obtain ⟨e,he,occ⟩ := occurs_in_row hx
  have ord := first e he
  have le := ord_depth ord
  have ge := depth_ge_source q e.2.val.1 e.2.val.2 x occ
  by_cases h : (source q s (c::t)).length < x.length
  · exact .inl h
  · have eq : (source q s (c::t)).length=x.length := by unfold rowSource at le; omega
    by_cases hs : s=[]
    · subst s; exact False.elim (h (empty_prefix_depth q c t _ _ x hc (bounded e he) ord occ))
    · have := List.dropLast_concat_getLast hs
      have rewriteH (a : Nat) (p : Tuple) (ht : s=p++[a]) : ¬ List.Lex (·<·) x (incLast s) := by
        subst s; exact nonempty_prefix_bound q a c p t _ _ x hc (bounded e he) ord occ eq.symm
      exact .inr ⟨eq,hs,rewriteH _ _ this.symm⟩


/-- The terminal right argument in Case I. The source has depth |s|+1,
so an equal-depth competing prefix has at most |s| entries. -/
theorem component_support_terminal (xs : Rows F q w) (s x : Tuple)
    (bounded : ∀ e∈xs, ∀ j∈e.2.val.1,j≤q)
    (first : ∀ e∈xs, source q s []=rowSource e ∨ Precedes (source q s []) (rowSource e))
    (hx : component H xs x ≠ 0) :
    (source q s []).length < x.length ∨
      ((source q s []).length = x.length ∧ s≠[] ∧ ¬List.Lex (·<·) x (incLast s)) := by
  obtain ⟨e,he,occ⟩ := occurs_in_row hx
  have ord := first e he
  have le := ord_depth ord
  have ge := depth_ge_source q e.2.val.1 e.2.val.2 x occ
  unfold rowSource at le ord
  by_cases h : (source q s []).length < x.length
  · exact .inl h
  · have eq : (source q s []).length=(source q e.2.val.1 e.2.val.2).length := by omega
    have eqx : x.length=(source q e.2.val.1 e.2.val.2).length := by omega
    obtain ⟨p,b,v,eh,ex,_,_⟩ := minimal_H_parts q _ _ _ occ eqx
    have eq' := eq
    rw [eh,source_depth,source_depth] at eq'
    simp only [List.length_nil,List.length_append,List.length_cons] at eq'
    have leLen : p.length+1≤s.length := by omega
    have ns : s≠[] := by intro h; rw [h] at leLen; simp at leLen
    refine .inr ⟨eq.trans eqx.symm,ns,?_⟩
    let l := s.dropLast
    let a := s.getLast ns
    have es : s=l++[a] := (List.dropLast_concat_getLast ns).symm
    have llen : p.length≤l.length := by
      have := congrArg List.length es; simp at this; omega
    rw [es,incLast_concat,ex]
    have ol := ord_lex ord eq
    rw [eh,es,source_join q (p++[b]) e.2.val.2] at ol
    exact prefix_bound q a l p b q [] _ v (.inr llen) (eh ▸ bounded e he) ol

end Megaera.FourSupport
