import Megaera.Rev4Negative

namespace Megaera.Rev4Initial
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.Triangular
open Megaera.FourMinimum Megaera.FourLambda Megaera.Rev4Negative
variable {F : Type u} [Arithmetic F]

/-- Read the remaining suffix after exactly r initial ones and a marker m. -/
def marker (r m : Nat) (f : Tuple → F) (t : Tuple) : F :=
  match r, t with
  | _, [] => 0
  | 0, a::x => if a=m then f x else 0
  | r+1, a::x => if a=1 then marker r m f x else 0

/-- A same-prefix row can meet the selected terms only by merging at the
marker. Before it a positive entry would exceed one; after it the input
marker would already exceed the chosen maximum m. This counts multiplicity. -/
theorem read_merges (d r m : Nat) (hd : 0 < d) (t : Tuple) (valid : Valid t)
    (maximal : ∀ a z, t = List.replicate r 1 ++ a::z → a ≤ m) (f : Tuple → F) :
    total (marker r (m+d) f) (merges d t) = marker r m f t := by
  induction r generalizing t with
  | zero =>
    cases t with
    | nil => rfl
    | cons a t =>
      have ha : a ≤ m := maximal a t rfl
      rw [merges, total_append', total_map]
      have none : total (fun z => marker 0 (m+d) f (a::z)) (merges d t) = 0 := by
        apply total_zero_of_members
        intro z _
        simp [marker, show a ≠ m+d by omega]
      rw [none, zeroAdd]
      simp only [total, Arithmetic.addZero, marker, show d+a=m+d ↔ a=m by omega]
  | succ r ih =>
    cases t with
    | nil => rfl
    | cons a t =>
      have ha : 0 < a := valid a (by simp)
      have good : Valid t := fun k hk => valid k (by simp [hk])
      rw [merges, total_append', total_map]
      simp only [total, Arithmetic.addZero, marker, if_neg (show d+a≠1 by omega)]
      by_cases eq : a=1
      · subst a
        simp only [ite_true, Arithmetic.addZero]
        apply ih t good
        intro k z hz
        exact maximal k z (by simp [List.replicate_succ,hz])
      · simp only [if_neg eq, Arithmetic.addZero]
        apply total_zero_of_members
        intro _ _
        rfl

variable [Neg F] {q : Nat}

private theorem selected_cons (field : ConstantField F q) (p v : Tuple) (a x n b : Nat)
    (z : Tuple) :
    selected field (a::p) v n b (x::z) =
      if x=a then selected field p v n b z else 0 := by
  by_cases eq : x=a
  · subst x
    simp [selected, Nat.succ_add]
  · simp [selected, eq, Nat.succ_add]

private theorem strip_common (field : ConstantField F q) (h p v : Tuple) (n b : Nat)
    (z : Tuple) :
    selected field (h++p) v n b (h++z) = selected field p v n b z := by
  induction h with
  | nil => rfl
  | cons a h ih => simp [selected_cons, ih]

private theorem strip_marker (field : ConstantField F q) (r m : Nat) (v : Tuple)
    (n b : Nat) (z : Tuple) :
    selected field (List.replicate r 1 ++ [m]) v n b z =
      marker r m (selected field [] v n b) z := by
  induction r generalizing z with
  | zero =>
    cases z with
    | nil => simp [selected,marker]
    | cons a z => simp [selected_cons,marker]
  | succ r ih =>
    cases z with
    | nil => simp [selected,marker]
    | cons a z => simp [List.replicate_succ,selected_cons,marker,ih]

omit [Neg F] in
private theorem marker_congr (r m : Nat) (t : Tuple) (f g : Tuple → F)
    (h : ∀ z, t = List.replicate r 1 ++ m::z → f z = g z) :
    marker r m f t = marker r m g t := by
  induction r generalizing t with
  | zero =>
    cases t with
    | nil => rfl
    | cons a t =>
      by_cases e : a=m
      · subst a; simpa only [marker,ite_true] using h t rfl
      · simp [marker,e]
  | succ r ih =>
    cases t with
    | nil => rfl
    | cons a t =>
      by_cases e : a=1
      · subst a; simp only [marker,ite_true]
        exact ih t (fun z hz => h z (by simp [List.replicate_succ,hz]))
      · simp [marker,e]

omit [Neg F] in
private theorem marker_delta (r m : Nat) (v t : Tuple) :
    marker r m (fun z => if z=v then (1:F) else 0) t =
      if t = List.replicate r 1 ++ m::v then 1 else 0 := by
  induction r generalizing t with
  | zero =>
    cases t with
    | nil => rfl
    | cons a t => by_cases e : a=m <;> simp [marker,e]
  | succ r ih =>
    cases t with
    | nil => simp [marker, List.replicate_succ]
    | cons a t => by_cases e : a=1 <;> simp [marker,e,List.replicate_succ,ih]

private theorem residue_injective {d a b : Nat} (ha : 0<a) (hb : 0<b)
    (ha' : a≤d) (hb' : b≤d) (eq : a%d=b%d) : a=b := by
  rcases Nat.eq_or_lt_of_le ha' with rfl|ha'
  · rcases Nat.eq_or_lt_of_le hb' with rfl|hb'
    · rfl
    · simp [Nat.mod_eq_of_lt hb'] at eq
      omega
  · rcases Nat.eq_or_lt_of_le hb' with rfl|hb'
    · simp [Nat.mod_eq_of_lt ha'] at eq
      omega
    · simpa [Nat.mod_eq_of_lt ha',Nat.mod_eq_of_lt hb'] using eq

private theorem last_entry (u : Tuple) (c : Nat) : entries (u++[c]) u.length = c := by
  induction u with
  | nil => rfl
  | cons a t ih => exact ih

private theorem earlier_entry (u : Tuple) (c j : Nat) (hj : j<u.length) :
    entries (u++[c]) j = u[j] := by
  simp [entries,List.getElem?_append_left hj,List.getElem?_eq_getElem hj]

/-- Within the positive rectangle the residue condition and the value of λ
recover the whole suffix, including the final entry when it equals q−1. -/
theorem bounded_suffix_reading (field : ConstantField F q) (v u : Tuple) (b c : Nat)
    (same : u.length=v.length) (bounds : ∀ k∈u, k≤q) (hb : 0<b ∧ b≤q-1)
    (hc : 0<c ∧ c≤q-1) :
    selected field [] (v++[b]) v.length b (u++[c]) =
      if u++[c]=v++[b] then 1 else 0 := by
  have last : entries (u++[c]) v.length = c := same ▸ last_entry u c
  have sz : (u++[c]).length=v.length+1 := by simp [same]
  simp only [selected, List.length_nil, Nat.zero_add, sz, List.take_zero, List.drop_zero,
    last, true_and]
  by_cases residue : c%(q-1)=b%(q-1)
  · have eq := residue_injective hc.1 hb.1 hc.2 hb.2 residue
    subst c
    rw [if_pos rfl, bounded_value field v.length b _ _ (fun j hj => by
      have hu : j<u.length := by omega
      rw [earlier_entry u b j hu]; exact bounds _ (List.getElem_mem _)) last]
    have test : (∀ j : Fin v.length, entries (u++[b]) j = entries (v++[b]) j) ↔ u=v := by
      constructor
      · intro all
        apply List.ext_getElem same
        intro j hu hv
        have := all ⟨j,hv⟩
        simpa only [earlier_entry u b j hu, earlier_entry v b j hv] using this
      · rintro rfl; simp
    simp [test]
  · rw [if_neg residue, if_neg]
    intro e
    have := congrArg List.getLast? e
    simp at this
    exact residue (congrArg (·%(q-1)) this)

/-- Full H-row reading on the selected depth for a competing tail of the
same length. It applies also to r=0 and to the empty common left prefix s. -/
theorem same_prefix_reading (field : ConstantField F q) (s t target : Tuple)
    (r m n b : Nat) (len : t.length = r+1+(n+1)) (valid : Valid t)
    (maximal : ∀ a z, t=List.replicate r 1++a::z → a≤m) :
    total (selected field (endHead s ++ (List.replicate r 1 ++ [m+(q-1)])) target n b)
      (H q s t) = marker r m (selected field [] target n b) t := by
  let p := List.replicate r 1 ++ [m+(q-1)]
  let read := selected field (endHead s ++ p) target n b
  have long {z : Tuple} (h : (endHead s).length+t.length < z.length) : read z=0 := by
    apply selected_long
    simp only [p, List.length_append, List.length_replicate, List.length_cons, List.length_nil]
    omega
  have head : total read (H q s t) =
      total (fun z => read (endHead s++z)) (quasiShuffle [q-1] t) := by
    cases s with
    | nil => simp [H,endings,concatenate,endHead,total_map]
    | cons a s =>
      simp only [H,endings,concatenate,List.flatMap_cons,List.flatMap_nil,List.append_nil,
        total_append',total_map]
      have extra : total (fun z => read (((a::s)++[1])++z)) (quasiShuffle [q-1] t) = 0 := by
        apply total_zero_of_members
        intro z hz
        apply long
        have depth_z := singleton_stuffle_depth _ _ _ hz
        simp only [endHead,incLast_length,List.length_append,List.length_cons,List.length_nil]
        omega
      rw [extra,Arithmetic.addZero]
      rfl
  change total read (H q s t) = _
  rw [head]
  obtain ⟨later, perm, deeper⟩ := stuffle_layer (q-1) t
  rw [BCPRows.permSum _ perm, total_append']
  have discard : total (fun z => read (endHead s++z)) later = 0 := by
    apply total_zero_of_members
    intro z hz
    apply long
    simpa using deeper z hz
  rw [discard, Arithmetic.addZero]
  simp only [read, p, strip_common, strip_marker]
  exact read_merges _ _ _ (by have := field.two_le; omega) t valid maximal _

/-- On an arbitrary same-prefix row of the selected depth, the total is
exactly the Kronecker delta at the chosen tail. The boundedness premise
only concerns tails whose marker is m; it is supplied by case_II_bounds
for a source outside the three legal shapes. -/
theorem same_prefix_delta (field : ConstantField F q) (s t v : Tuple) (r m b : Nat)
    (hb : 0<b ∧ b≤q-1) (len : t.length = r+1+(v.length+1)) (valid : Valid t)
    (maximal : ∀ a z, t=List.replicate r 1++a::z → a≤m)
    (bounds : ∀ u c, t=List.replicate r 1++m::(u++[c]) → (∀ k∈u,k≤q) ∧ c≤q-1) :
    total (selected field (endHead s ++ (List.replicate r 1 ++ [m+(q-1)]))
      (v++[b]) v.length b) (H q s t) =
      if t=List.replicate r 1++m::(v++[b]) then 1 else 0 := by
  rw [same_prefix_reading field _ _ _ _ _ _ _ len valid maximal, ← marker_delta]
  apply marker_congr
  intro z hz
  have size : z.length=v.length+1 := by
    simp only [hz,List.length_append,List.length_replicate,List.length_cons] at len
    omega
  cases e : z.reverse with
  | nil =>
    have := List.reverse_eq_nil_iff.mp e
    simp [this] at size
  | cons c l =>
    have h : z = l.reverse++[c] := by simpa using congrArg List.reverse e
    subst z
    have hz' := bounds _ _ hz
    have cp := valid c (by simp [hz])
    exact bounded_suffix_reading field _ _ _ _ (by simpa using size) hz'.1 hb ⟨cp,hz'.2⟩

end Megaera.Rev4Initial
