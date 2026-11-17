import Megaera.Splitting
import Megaera.MainTheorems

/-! The strict increase in the proof of Lemma 2.6, on the tuple expansions
themselves. The right tail can be empty, as it is for a terminal split. -/

namespace Megaera.Triangular
open Megaera.Splitting

/-- The order used for the leading tuple: first depth, then lexicographic order. -/
def Precedes (s t : Tuple) : Prop :=
  depth s < depth t ∨ (depth s = depth t ∧ List.Lex (· < ·) s t)

theorem precedes_trans {s t u : Tuple} (hst : Precedes s t) (htu : Precedes t u) :
    Precedes s u := by
  rcases hst with h | ⟨h, h'⟩ <;> rcases htu with k | ⟨k,k'⟩
  · exact Or.inl (Nat.lt_trans h k)
  · exact Or.inl (k ▸ h)
  · exact Or.inl (h ▸ k)
  · exact Or.inr ⟨h.trans k, List.lex_trans (fun x y => Nat.lt_trans x y) h' k'⟩

/-- Multiplying by a singleton cannot shorten the other input. -/
theorem singleton_stuffle_depth (a : Nat) (t u : Tuple) (hu : u ∈ quasiShuffle [a] t) :
    t.length ≤ u.length := by
  induction t generalizing u with
  | nil => simp
  | cons b t ih =>
    rw [quasiShuffle] at hu
    simp only [quasiShuffle_nil_left, List.map_cons, List.map_nil, List.mem_append,
      List.mem_singleton, List.mem_map] at hu
    rcases hu with (rfl | ⟨v, hv, rfl⟩) | rfl
    · simp
    · simpa only [List.length_cons, Nat.add_le_add_iff_right] using ih v hv
    · simp

private theorem source_tail_depth (q : Nat) (t u : Tuple)
    (hu : u ∈ quasiShuffle [q-1] t) : (source q [] t).length ≤ u.length := by
  cases t with
  | nil =>
    simp only [quasiShuffle_nil_right, List.mem_singleton] at hu
    subst u
    simp [source]
  | cons b t =>
    simpa [source] using singleton_stuffle_depth (q-1) (b::t) u hu

theorem incLast_length (a : Nat) (s : Tuple) :
    (incLast (a::s)).length = (a::s).length := by
  induction s generalizing a with
  | nil => rfl
  | cons b s ih => simp only [incLast, List.length_cons, ih, List.length_cons]

/-- The increment occurs before either appended tail, so their entries play
no role in this comparison. -/
theorem incLast_append_lex (a : Nat) (h s t : Tuple) :
    List.Lex (· < ·) ((a::h) ++ s) (incLast (a::h) ++ t) := by
  induction h generalizing a with
  | nil => exact .rel (Nat.lt_succ_self a)
  | cons b h ih => exact .cons (ih b)

private theorem source_append (q : Nat) (h t : Tuple) :
    source q h t = h ++ source q [] t := by cases t <;> rfl

/-- Every term of the constant part of a cut lies strictly above the source
of its coefficient of the polynomial variable. Multiplicities are retained. -/
theorem source_precedes_H (q : Nat) (h t u : Tuple) (hu : u ∈ H q h t) :
    Precedes (source q h t) u := by
  obtain ⟨e, he, hm⟩ := List.mem_flatMap.mp hu
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hm
  have ht := source_tail_depth q t v hv
  rw [source_append]
  cases h with
  | nil =>
    simp only [endings,List.mem_singleton] at he
    subst e
    left
    simp only [depth,List.nil_append,List.length_append,List.length_cons,List.length_nil]
    omega
  | cons a h =>
    simp only [endings, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · by_cases heq : (source q [] t).length = v.length
      · right
        exact ⟨by simp only [depth,List.length_append,incLast_length,heq],
          incLast_append_lex a h _ _⟩
      · left
        simp only [depth,List.length_append,incLast_length]
        omega
    · left
      simp only [depth,List.length_append,List.length_cons,List.length_nil]
      omega

theorem precedes_irrefl (s : Tuple) : ¬ Precedes s s := by
  rintro (h | ⟨_, h⟩)
  · exact Nat.lt_irrefl _ h
  · exact List.lex_irrefl Nat.lt_irrefl _ h

open Megaera.Finite Megaera.Carlitz Megaera.Paper
variable {F : Type u} [Arithmetic F] {q w : Nat}

theorem coord_absent (ts : List Tuple) (s : Tuple) (hs : s ∉ ts) :
    coordinates (withCoeff (1:F) ts) s = 0 := by
  apply total_zero_of_members
  intro e he
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp he
  exact if_neg (fun eq : t = s => hs (eq ▸ ht))

private theorem component_absent (op : Nat → Tuple → Tuple → List Tuple)
    (rows : Rows F q w) (s : Tuple) (hs : ∀ e ∈ rows, s ∉ op q e.2.val.1 e.2.val.2) :
    component op rows s = 0 := by
  apply total_zero_of_members
  intro e he
  rw [coord_absent _ _ (hs e he), Arithmetic.mulZero]

theorem L_pivot (q : Nat) (h t : Tuple) :
    coordinates (withCoeff (1:F) (L q h t)) (source q h t) = 1 := by
  cases t with
  | nil => simp [source,coordinates,withCoeff,L,start,total,Arithmetic.addZero]
  | cons a t =>
    have hne : h ++ q :: a :: t ≠ h ++ (q+a)::t := by
      intro e
      have he := congrArg List.length e
      simp at he
    simp [source,coordinates,withCoeff,L,start,total,hne,zeroAdd,Arithmetic.addZero]

abbrev rowSource (e : F × Row q w) : Tuple := source q e.2.val.1 e.2.val.2

omit [Arithmetic F] in
private theorem later_L_absent (e : F × Row q w) (s : Tuple) (hs : Precedes s (rowSource e)) :
    s ∉ L q e.2.val.1 e.2.val.2 := by
  intro hm
  rcases source_least_depth _ _ _ _ hm with he | he
  · rw [he] at hs
    exact precedes_irrefl _ hs
  · rcases hs with h | ⟨h,_⟩ <;> change _ = depth (rowSource e) + 1 at he <;> omega

/-- The coefficient at the first source is unchanged in a combination with
one copy of its least row and all remaining row sources strictly above it. -/
theorem L_first_coefficient (e : F × Row q w) (rows : Rows F q w)
    (later : ∀ z ∈ rows, Precedes (rowSource e) (rowSource z)) :
    component L (e :: rows) (rowSource e) = e.1 := by
  have hz := component_absent L rows (rowSource e)
    (fun z hz => later_L_absent z _ (later z hz))
  change _ * coordinates _ (source _ _ _) + component L rows _ = _
  rw [L_pivot, Arithmetic.mulOne, hz, Arithmetic.addZero]

/-- All surviving coordinates of H lie above the least source, after any
cancellations in the constant field. -/
theorem H_support_after (rows : Rows F q w) (s u : Tuple)
    (least : ∀ z ∈ rows, s = rowSource z ∨ Precedes s (rowSource z))
    (hu : component H rows u ≠ 0) : Precedes s u := by
  apply Classical.byContradiction
  intro h
  apply hu
  apply component_absent
  intro z hz hmem
  have hzu := source_precedes_H q z.2.val.1 z.2.val.2 u hmem
  rcases least z hz with he | he
  · exact h (he ▸ hzu)
  · exact h (precedes_trans he hzu)

/-- Number of weight-w tuples strictly below the entire support. At a nonzero
vector of weight w this is the index of the least tuple in increasing order. -/
noncomputable def vectorRank (w : Nat) (v : Tuple → F) : Nat := by
  classical
  exact (Dimension.tuples Int.toNat w).countP
    (fun s => decide (∀ u, v u ≠ 0 → Precedes s u))

theorem vectorRank_bound (w : Nat) (v : Tuple → F) :
    vectorRank w v ≤ (Dimension.tuples Int.toNat w).length := List.countP_le_length

theorem count_mono {α : Type v} (p k : α → Bool)
    (le : ∀ x, p x = true → k x = true) (l : List α) :
    l.countP p ≤ l.countP k := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.countP_cons]
    cases hp : p a <;> cases hk : k a <;> simp_all <;> omega

private theorem count_strict {α : Type v} (p k : α → Bool)
    (le : ∀ x, p x = true → k x = true) (l : List α) (s : α)
    (hm : s ∈ l) (hp : p s = false) (hk : k s = true) :
    l.countP p < l.countP k := by
  induction l with
  | nil => simp at hm
  | cons a l ih =>
    simp only [List.countP_cons]
    rcases List.mem_cons.mp hm with rfl | hm
    · simp [hp,hk]; have h := count_mono p k le l; omega
    · specialize ih hm
      cases hp : p a <;> cases hk : k a <;> simp_all <;> omega

/-- Support comparison gives a bounded numerical rank increase without
choosing a sorting algorithm. -/
theorem vectorRank_strict (w : Nat) (v v' : Tuple → F) (s : Tuple)
    (hs : s ∈ Dimension.tuples Int.toNat w) (pivot : v s ≠ 0)
    (later : ∀ u, v' u ≠ 0 → Precedes s u) :
    vectorRank w v < vectorRank w v' := by
  classical
  unfold vectorRank
  apply count_strict _ _ _ _ s hs
  · simp only [decide_eq_false_iff_not]
    exact fun h => precedes_irrefl s (h s pivot)
  · exact decide_eq_true later
  · intro a ha
    simp only [decide_eq_true_eq] at ha ⊢
    exact fun u hu => precedes_trans (ha s pivot) (later u hu)

private theorem weight_sum (s : Tuple) : s.sum = weight s := by
  induction s with
  | nil => rfl
  | cons a s ih => simp only [List.sum_cons,weight,ih]

/-- Lemma 2.6 on a reduced presentation ordered with its least row first.
The upper bound is the number of all valid tuples of the given weight. -/
theorem canonical_rank_strict (hq : 0 < q) (e : F × Row q w) (rows : Rows F q w)
    (hn : e.1 ≠ 0) (later : ∀ z ∈ rows, Precedes (rowSource e) (rowSource z)) :
    vectorRank w (component L (e :: rows)) < vectorRank w (component H (e :: rows)) := by
  obtain ⟨hv,tv,hw⟩ := e.2.property
  have hs : rowSource e ∈ Dimension.tuples Int.toNat w := by
    apply (Dimension.mem_unrestricted _ _).2
    refine ⟨?_, L_valid q hq _ _ hv tv _ (source_L q _ _)⟩
    rw [weight_sum, rowSource, source_weight]
    omega
  apply vectorRank_strict _ _ _ _ hs
  · rwa [L_first_coefficient _ _ later]
  · intro u hu
    apply H_support_after _ _ u _ hu
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact Or.inl rfl
    · exact Or.inr (later z hz)

theorem precedes_trichotomy (s t : Tuple) :
    Precedes s t ∨ s = t ∨ Precedes t s := by
  by_cases h : depth s < depth t
  · exact Or.inl (.inl h)
  by_cases k : depth t < depth s
  · exact Or.inr (.inr (.inl k))
  have eq : depth s = depth t := by omega
  letI : Std.Irrefl (fun a b : Nat => a < b) := ⟨Nat.lt_irrefl⟩
  letI : Std.Total (fun a b : Nat => ¬ a < b) := ⟨fun a b => by omega⟩
  letI : Std.Antisymm (fun a b : Nat => ¬ a < b) := ⟨fun a b _ _ => by omega⟩
  rcases List.le_total s t with le | le
  · rcases List.le_iff_lt_or_eq.mp le with lt | e
    · exact .inl (.inr ⟨eq,lt⟩)
    · exact .inr (.inl e)
  · rcases List.le_iff_lt_or_eq.mp le with lt | e
    · exact .inr (.inr (.inr ⟨eq.symm,lt⟩))
    · exact .inr (.inl e.symm)

omit [Arithmetic F] in
/-- Both components use the same canonical index when their sources agree. -/
private theorem eq_row_of_source (a b : F × Row q w)
    (ha : ∀ i ∈ a.2.val.1, i ≤ q) (hb : ∀ i ∈ b.2.val.1, i ≤ q)
    (hs : rowSource a = rowSource b) : a.2 = b.2 := by
  obtain ⟨hh,ht⟩ := canonical_source_injective q ha hb a.2.property.2.1 b.2.property.2.1 hs
  exact Subtype.ext (Prod.ext hh ht)

private abbrev SortedRows (rows : Rows F q w) : Prop :=
  rows.Pairwise (fun a b => Precedes (rowSource a) (rowSource b))

private abbrev goodRow (a : F × Row q w) : Prop :=
  a.1 ≠ 0 ∧ ∀ i ∈ a.2.val.1, i ≤ q

private def sameComponents (xs ys : Rows F q w) : Prop :=
  ∀ op s, component op xs s = component op ys s

private theorem component_cons (op : Nat → Tuple → Tuple → List Tuple)
    (e : F × Row q w) (rows : Rows F q w) (s : Tuple) :
    component op (e::rows) s = e.1 * coordinates (withCoeff (1:F)
      (op q e.2.val.1 e.2.val.2)) s + component op rows s := rfl

private theorem insert_sorted (a : F × Row q w) (rows : Rows F q w) (ha : goodRow a)
    (sorted : SortedRows rows) (good : ∀ b ∈ rows, goodRow b)
    (below : Tuple → Prop) (ba : below (rowSource a))
    (bs : ∀ b ∈ rows, below (rowSource b)) :
    ∃ zs : Rows F q w, SortedRows zs ∧ (∀ z ∈ zs, goodRow z) ∧
      (∀ z ∈ zs, below (rowSource z)) ∧ sameComponents zs (a::rows) := by
  induction rows generalizing below with
  | nil =>
    exact ⟨[a], by simp [SortedRows], by simpa using ha, by simpa using ba, fun _ _ => rfl⟩
  | cons b rows ih =>
    obtain ⟨later,tail⟩ := List.pairwise_cons.mp sorted
    have gb := good b (by simp)
    have gt : ∀ z ∈ rows, goodRow z := fun z hz => good z (by simp [hz])
    have bb := bs b (by simp)
    have bt : ∀ z ∈ rows, below (rowSource z) := fun z hz => bs z (by simp [hz])
    rcases precedes_trichotomy (rowSource a) (rowSource b) with lt | eq | gt'
    · refine ⟨a::b::rows, List.pairwise_cons.mpr ⟨?_,sorted⟩, ?_, ?_, fun _ _ => rfl⟩
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact lt
        · exact precedes_trans lt (later z hz)
      · exact List.forall_mem_cons.mpr ⟨ha,good⟩
      · exact List.forall_mem_cons.mpr ⟨ba,bs⟩
    · have er := eq_row_of_source a b ha.2 gb.2 eq
      have merged (op : Nat → Tuple → Tuple → List Tuple) (s : Tuple) :
          component op (a::b::rows) s =
            (a.1+b.1) * coordinates (withCoeff (1:F) (op q b.2.val.1 b.2.val.2)) s +
              component op rows s := by
        rw [component_cons,component_cons,er, ← Arithmetic.addAssoc]
        congr 1
        rw [Arithmetic.mulComm (a.1+b.1), Arithmetic.distrib,
          Arithmetic.mulComm a.1,Arithmetic.mulComm b.1]
      by_cases nz : a.1+b.1 = 0
      · refine ⟨rows,tail,gt,bt,?_⟩
        intro op s
        rw [merged,nz,zeroMul,zeroAdd]
      · let c : F × Row q w := (a.1+b.1,b.2)
        exact ⟨c::rows, List.pairwise_cons.mpr ⟨later,tail⟩,
          List.forall_mem_cons.mpr ⟨⟨nz,gb.2⟩,gt⟩,
          List.forall_mem_cons.mpr ⟨bb,bt⟩, fun op s => (merged op s).symm⟩
    · obtain ⟨zs,ss,gs,bs',comp⟩ := ih tail gt
        (fun z => below z ∧ Precedes (rowSource b) z) ⟨ba,gt'⟩
        (fun z hz => ⟨bt z hz,later z hz⟩)
      refine ⟨b::zs,List.pairwise_cons.mpr ⟨fun z hz => (bs' z hz).2,ss⟩,
        List.forall_mem_cons.mpr ⟨gb,gs⟩,
        List.forall_mem_cons.mpr ⟨bb,fun z hz => (bs' z hz).1⟩,?_⟩
      intro op s
      rw [component_cons,comp,component_cons,component_cons,component_cons,
        ← Arithmetic.addAssoc,Arithmetic.addComm (_*_) (_*_), Arithmetic.addAssoc]

private theorem normalize_canonical (rows : Rows F q w)
    (bounded : ∀ e ∈ rows, ∀ i ∈ e.2.val.1, i ≤ q) :
    ∃ zs : Rows F q w, SortedRows zs ∧ (∀ z ∈ zs, goodRow z) ∧ sameComponents zs rows := by
  induction rows with
  | nil => exact ⟨[],by simp [SortedRows],by simp,fun _ _ => rfl⟩
  | cons a rows ih =>
    obtain ⟨zs,ss,good,comp⟩ := ih (fun z hz => bounded z (by simp [hz]))
    by_cases hz : a.1 = 0
    · refine ⟨zs,ss,good,?_⟩
      intro op s
      rw [comp,component_cons,hz,zeroMul,zeroAdd]
    · obtain ⟨ys,ss',good',_,eq⟩ := insert_sorted a zs ⟨hz,bounded a (by simp)⟩
        ss good (fun _ => True) trivial (by simp)
      refine ⟨ys,ss',good',?_⟩
      intro op s
      rw [eq,component_cons,comp,component_cons]

/-- Strict increase for any canonical presentation, allowing repeated indices,
arbitrary order, and coefficient cancellations. No normal-form assumption is
required. Nonvanishing of the L-vector removes the empty combination. -/
theorem canonical_components_increase (hq : 0 < q) (rows : Rows F q w)
    (bounded : ∀ e ∈ rows, ∀ i ∈ e.2.val.1, i ≤ q)
    (nonzero : ∃ s, component L rows s ≠ 0) :
    vectorRank w (component L rows) < vectorRank w (component H rows) := by
  obtain ⟨zs,sorted,good,comp⟩ := normalize_canonical rows bounded
  have eqL := funext (comp L)
  have eqH := funext (comp H)
  rw [← eqL, ← eqH]
  cases zs with
  | nil =>
    obtain ⟨s,hs⟩ := nonzero
    exact False.elim (hs ((comp L s).symm.trans rfl))
  | cons e zs =>
    exact canonical_rank_strict hq e zs (good e (by simp)).1 (List.pairwise_cons.mp sorted).1

/-- Collect equal canonical rows and order their surviving sources. -/
theorem ordered_presentation (rows : Rows F q w)
    (bounded : ∀ e∈rows, ∀ a∈e.2.val.1, a≤q) :
    ∃ zs : Rows F q w, zs.Pairwise (fun a b => Precedes (rowSource a) (rowSource b)) ∧
      (∀ e∈zs, e.1 ≠ 0 ∧ ∀ a∈e.2.val.1, a≤q) ∧ component L zs = component L rows := by
  obtain ⟨zs,ord,good,eqn⟩ := normalize_canonical rows bounded
  exact ⟨zs,ord,good,funext (eqn L)⟩

end Megaera.Triangular
