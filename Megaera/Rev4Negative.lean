import Megaera.RevisionTwo

/-! The negative term in the final argument of §4.3 of Megaera (4).
The prefix comparison needed for the cancellation is a hypothesis. -/
namespace Megaera.Rev4Negative
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.Triangular
open Megaera.FourLambda Megaera.FourMinimum
variable {F : Type u} [Arithmetic F] [Neg F]

/-- The contribution of one tuple to the chosen prefix, depth, and
last-entry residue class, before multiplying by its coefficient. -/
def selected (field : ConstantField F q) (marker target : Tuple) (n b : Nat)
    (x : Tuple) : F :=
  let tail := x.drop marker.length
  if x.length = marker.length + (n+1) ∧ x.take marker.length = marker ∧
      entries tail n % (q-1) = b % (q-1) then
    lambda q field.two_le n b (entries target) (entries tail)
  else 0

theorem selected_long (field : ConstantField F q) (marker target : Tuple)
    (n b : Nat) {x : Tuple} (h : marker.length + (n+1) < x.length) :
    selected field marker target n b x = 0 := by
  simp [selected, Nat.ne_of_gt h]

private theorem selected_after (field : ConstantField F q)
    (marker target p t z : Tuple) (n b : Nat) (hb : 0<b)
    (hlen : p.length+t.length = n+1) :
    selected field marker target n b ((marker++p)++z) =
      if z.length=t.length then
        lambda q field.two_le n b (entries target) (entries (p++z)) else 0 := by
  have len : marker.length + (p.length+z.length) = marker.length+(n+1) ↔
      z.length=t.length := by omega
  simp only [selected,List.append_assoc,List.length_append,List.take_left,List.drop_left,len,
    true_and]
  by_cases hz : z.length=t.length
  · simp only [hz, true_and, ite_true]
    split
    · rfl
    · rename_i hw
      exact (wrong_residue field n b _ _ hb hw).symm
  · simp [hz]

/-- In the displayed negative summand, every insertion and merge is
counted with its multiplicity. The equality of depths filters out the
insertions. For a nonempty overhang the last entry of the overhang is
the entry to which the suffix identity applies. -/
theorem selected_stuffle_zero (field : ConstantField F q)
    (marker target p t : Tuple) (n b : Nat)
    (hlen : p.length+t.length=n+1) (hb₀ : 0<b) (hb : b≤q-1)
    (hx : 0 < entries (p++t) n)
    (hp : p=[] ∨ 1 < entries (p++t) (p.length-1)) :
    total (fun z => selected field marker target n b ((marker++p)++z))
      (quasiShuffle [q-1] t) = 0 := by
  simp only [selected_after field marker target p t _ n b hb₀ hlen]
  exact FourInvariant.suffix_stuffle_zero q field n b target p t hlen hb hx hp

theorem tails_length (q : Nat) (u v : Tuple) {z : Tuple}
    (hz : z ∈ (L q u v).flatMap (quasiShuffle [q-1])) :
    (u++raiseFirst q v).length ≤ z.length := by
  obtain ⟨t, ht, hzt⟩ := List.mem_flatMap.mp hz
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp ht
  have h := singleton_stuffle_depth _ _ _ hzt
  cases v with
  | nil => simp [start] at ha; subst a; exact h
  | cons k v =>
    simp [start] at ha
    rcases ha with rfl | rfl <;> simp only [raiseFirst,List.length_append,List.length_cons] at * <;> omega

omit [Neg F] in
/-- Retain the full singleton product of the shortest source in L(u;v).
The second term in start and the (h,1) alternative in endings are
disposed of by depth before the lambda identity is applied. -/
private theorem shortest_negative (q : Nat) (h u v : Tuple) (f : Tuple → F)
    (deep : ∀ x : Tuple, (endHead h).length + (u++raiseFirst q v).length < x.length → f x=0) :
    total f (concatenate (endings h) ((L q u v).flatMap (quasiShuffle [q-1]))) =
      total (fun z => f (endHead h++z)) (quasiShuffle [q-1] (u++raiseFirst q v)) := by
  have first : total (fun z => f (endHead h++z)) ((L q u v).flatMap (quasiShuffle [q-1])) =
      total (fun z => f (endHead h++z)) (quasiShuffle [q-1] (u++raiseFirst q v)) := by
    cases v with
    | nil => simp [L,start,raiseFirst]
    | cons k v =>
      simp only [L,start,raiseFirst,List.map_cons,List.map_nil,List.flatMap_cons,List.flatMap_nil,
        List.append_nil,total_append]
      have vanish : total (fun z => f (endHead h++z)) (quasiShuffle [q-1] (u++q::k::v))=0 := by
        apply total_zero_of_members
        intro z hz
        have hh := singleton_stuffle_depth _ _ _ hz
        apply deep
        simp only [raiseFirst,List.length_append,List.length_cons] at *
        omega
      rw [vanish,zeroAdd]
  cases h with
  | nil =>
    simpa only [concatenate,endings,endHead,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      total_map] using first
  | cons a h =>
    simp only [concatenate,endings,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      total_append,total_map]
    have vanish : total (fun z => f (((a::h)++[1])++z))
        ((L q u v).flatMap (quasiShuffle [q-1])) = 0 := by
      apply total_zero_of_members
      intro z hz
      have hh := tails_length q u v hz
      apply deep
      simp only [endHead,incLast_length,List.length_append,List.length_cons,List.length_nil] at hh ⊢
      omega
    rw [vanish,Arithmetic.addZero]
    exact first

omit [Neg F] in
private theorem weighted_list (k : F) (f : Tuple → F) (l : List Tuple) :
    total (fun e : F × Tuple => e.1 * f e.2) (withCoeff k l) = k * total f l := by
  induction l with
  | nil => simp [withCoeff,total,Arithmetic.mulZero]
  | cons x l ih =>
    change k * f x + total (fun e : F × Tuple => e.1 * f e.2) (withCoeff k l) =
      k * (f x + total f l)
    rw [ih,Arithmetic.distrib]

/-- For the two displayed prefix possibilities on pages 24–25 the
*whole signed negative list* contributes zero at its shortest depth.
The convention for v=[] is raiseFirst q [] = [q]. -/
theorem negative_contribution_zero (field : ConstantField F q)
    (marker target h u v p : Tuple) (n b : Nat)
    (prefix_eq : endHead h = marker++p)
    (hlen : p.length + (u++raiseFirst q v).length = n+1)
    (hb₀ : 0<b) (hb : b≤q-1)
    (hx : 0 < entries (p++(u++raiseFirst q v)) n)
    (hp : p=[] ∨ 1 < entries (p++(u++raiseFirst q v)) (p.length-1)) :
    total (fun e : F × Tuple => e.1 * selected field marker target n b e.2)
      (withCoeff (-(1:F)) (concatenate (endings h) ((L q u v).flatMap (quasiShuffle [q-1])))) = 0 := by
  rw [weighted_list,shortest_negative]
  · rw [prefix_eq, selected_stuffle_zero field marker target p _ n b hlen hb₀ hb hx hp,
      Arithmetic.mulZero]
  · intro x hl
    apply selected_long
    rw [prefix_eq,List.length_append] at hl
    omega

private theorem entry_at_join (l r : Tuple) (a : Nat) :
    entries (l++a::r) l.length = a := by
  simp [entries,List.getElem?_append]

private theorem last_source_positive (hq : 1<q) (v before : Tuple) (hv : Valid v) (n : Nat)
    (hlen : before.length + (raiseFirst q v).length=n+1) :
    0 < entries (before++raiseFirst q v) n := by
  have nonempty : raiseFirst q v ≠ [] := by cases v <;> simp [raiseFirst]
  have valid : Valid (raiseFirst q v) := by
    cases v with
    | nil => simp [Valid,raiseFirst]; omega
    | cons a v =>
      intro x hx
      simp only [raiseFirst,List.mem_cons] at hx
      rcases hx with rfl | hx
      · omega
      · exact hv x (List.mem_cons_of_mem _ hx)
  obtain ⟨tail,a,eqn⟩ : ∃ tail a, raiseFirst q v = tail++[a] :=
    ⟨_,_,(List.dropLast_concat_getLast nonempty).symm⟩
  have ap := valid a (by rw [eqn]; simp)
  rw [eqn] at hlen ⊢
  simp only [List.length_append,List.length_cons,List.length_nil] at hlen
  rw [← List.append_assoc,show n=(before++tail).length by simp; omega,entry_at_join]
  exact ap

private theorem overhang_final (h marker p t : Tuple) (hm : marker≠[])
    (hv : Valid h) (eqn : endHead h=marker++p) :
    p=[] ∨ 1<entries (p++t) (p.length-1) := by
  by_cases empty : p=[]
  · exact .inl empty
  right
  obtain ⟨l,a,rfl⟩ : ∃ l a, p=l++[a] := ⟨_,_,(List.dropLast_concat_getLast empty).symm⟩
  simp only [List.append_assoc,List.cons_append,List.nil_append,List.length_append,
    List.length_cons,List.length_nil,Nat.add_sub_cancel,entry_at_join]
  cases h with
  | nil =>
    have := congrArg List.length eqn
    have hn := List.length_pos_iff.mpr hm
    simp [endHead] at this
    omega
  | cons y h =>
    obtain ⟨r,k,decomp⟩ : ∃ r k, y::h=r++[k] :=
      ⟨_,_,(List.dropLast_concat_getLast (List.cons_ne_nil y h)).symm⟩
    have hpos := hv k (by rw [decomp]; simp)
    change incLast (y::h) = marker++(l++[a]) at eqn
    rw [decomp,FourCases.incLast_concat,←List.append_assoc] at eqn
    have e := congrArg List.getLast? eqn
    simp at e
    omega

/-- For positive manuscript tuples the entry inequalities in the
two lambda cancellations follow from the domain and the raised ending.
The marker is nonempty, since it contains the distinguished entry. -/
theorem valid_negative_contribution_zero (field : ConstantField F q)
    (marker target h u v p : Tuple) (n b : Nat) (hm : marker≠[])
    (valid_h : Valid h) (valid_v : Valid v) (prefix_eq : endHead h = marker++p)
    (hlen : p.length+(u++raiseFirst q v).length = n+1) (hb₀ : 0<b) (hb : b≤q-1) :
    total (fun e : F × Tuple => e.1 * selected field marker target n b e.2)
      (withCoeff (-(1:F)) (concatenate (endings h) ((L q u v).flatMap (quasiShuffle [q-1])))) = 0 := by
  apply negative_contribution_zero field marker target h u v p n b prefix_eq hlen hb₀ hb
  · rw [← List.append_assoc]
    apply last_source_positive field.two_le v (p++u) valid_v n
    simpa only [List.length_append,Nat.add_assoc] using hlen
  · exact overhang_final h marker p _ hm valid_h prefix_eq

/-- Under the prefix comparison the selected reading of the complete
signed lift is exactly the reading of its positive part. This equality
does not assume cancellation of the positive part. -/
theorem lifted_reading (field : ConstantField F q)
    (marker target h u v p : Tuple) (n b : Nat) (hm : marker≠[])
    (valid_h : Valid h) (valid_v : Valid v) (prefix_eq : endHead h = marker++p)
    (hlen : p.length+(u++raiseFirst q v).length = n+1) (hb₀ : 0<b) (hb : b≤q-1) :
    total (fun e : F × Tuple => e.1 * selected field marker target n b e.2)
      (lifted q h u v) =
      total (fun x => selected field marker target n b (h++x)) ((H q u v).flatMap (start q)) := by
  unfold lifted generalP
  rw [←List.map_flatMap,PrimitiveRows.bStar_expansion,total_append',
    valid_negative_contribution_zero field marker target h u v p n b hm valid_h valid_v
      prefix_eq hlen hb₀ hb,Arithmetic.addZero,weighted_list,oneMul,total_map]

end Megaera.Rev4Negative
