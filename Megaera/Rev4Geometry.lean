import Megaera.FourSupport
import Megaera.FourCompleteness
import Megaera.Rev4Negative
import Megaera.Rev4Indices

/-! The comparison of the negative prefix on pages 24–25 of Megaera (4).
The lower bound on pivots here is the minimum of the actual image Ind P. -/
namespace Megaera.Rev4Geometry
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.Splitting
open Megaera.Triangular Megaera.FourReduction Megaera.FourMinimum

variable {F : Type u} [Arithmetic F] {q w : Nat}

/-- Depth of the layer selected in Case II. At an empty left tuple the
convention ∅⁺¹ = (1) adds one entry. -/
def selectedDepth (q : Nat) (s t : Tuple) : Nat :=
  (source q s t).length + (if s=[] then 1 else 0)

/-- This depth is exactly the length of the selected tuple. In Case II
the original and distinguished source tails have equal length r+n+2. -/
theorem selected_layer (q c r marker : Nat) (s t tail : Tuple)
    (same : (c::t).length = r+1+tail.length) :
    ((endHead s ++ List.replicate r 1 ++ [marker])++tail).length =
      selectedDepth q s (c::t) := by
  cases s with
  | nil =>
    simp only [selectedDepth,FourCases.source_depth,List.length_cons,List.length_nil,
      if_true,endHead,List.length_append,List.length_replicate] at *
    omega
  | cons a s =>
    simp only [selectedDepth,FourCases.source_depth,List.length_cons,List.cons_ne_nil,
      if_false,endHead,List.length_append,List.length_replicate,incLast_length,List.length_nil] at *
    omega

private theorem raise_width (q : Nat) (v : Tuple) :
    (raiseFirst q v).length = max 1 v.length := by
  cases v <;> simp [raiseFirst]

/-- The relevant inequality is equality at the actual type I/II pivot. -/
theorem general_suffix_depth (q : Nat) (u v : Tuple) (hu : u≠[]) :
    (raiseFirst q (incLast u) ++ addLast (q-1) v).length =
      (u++raiseFirst q v).length := by
  simp only [List.length_append,Rev4Indices.raised_length q u hu,
    Rev4Indices.last_width,raise_width]

/-- Compare each constituent of type III with the *difference's* pivot.
Its prefix is h for both lifts. On the second negative list equality is
impossible when t is empty, since that source then has one extra entry. -/
theorem difference_suffix_depths (q : Nat) (s u t : Tuple) (hs : s≠[]) (hu : u≠[]) :
    let after := raiseFirst q (incLast s) ++ (addLast q u ++ t)
    after.length = (s++raiseFirst q (incLast u++t)).length ∧
    (incLast s++u++raiseFirst q t).length = after.length + (if t=[] then 1 else 0) := by
  dsimp only
  simp only [List.length_append,Rev4Indices.raised_length q s hs,Rev4Indices.inc_length u hu,
    Rev4Indices.inc_length s hs,Rev4Indices.last_width,raise_width]
  have pos := List.length_pos_iff.mpr hu
  cases t <;> simp <;> omega

theorem imageWindow_depth (xs : Rows F q w) (s t p : Tuple) (c : Nat) (hc : 0<c)
    (bounded : ∀ e∈xs, ∀ j∈e.2.val.1,j≤q)
    (first : ∀ e∈xs, source q s (c::t)=rowSource e ∨ Precedes (source q s (c::t)) (rowSource e))
    (window : ImageWindow (component H xs) p) : selectedDepth q s (c::t) ≤ p.length := by
  obtain ⟨y,nz,ord⟩ := window
  have support := FourSupport.component_support xs s t y c hc bounded first nz
  have yp : y.length ≤ p.length := by
    rcases ord with rfl | lt | ⟨eq,_⟩ <;> simp only [depth] at * <;> omega
  unfold selectedDepth
  split <;> rcases support with lt | ⟨eq,ns,_⟩ <;> first | contradiction | omega

private theorem compare_base (base pref post rest after : Tuple) (a : Nat)
    (eqn : pref ++ (a+1)::post = base ++ rest)
    (ord : ¬ List.Lex (·<·) (pref ++ a::after) base) :
    ∃ l, pref = base++l ∧ l++(a+1)::post = rest := by
  induction base generalizing pref with
  | nil => exact ⟨pref,rfl,eqn⟩
  | cons b base ih =>
    cases pref with
    | nil =>
      have eb : a+1=b := (List.cons.inj eqn).1
      exact (ord (.rel (by omega))).elim
    | cons d pref =>
      obtain ⟨eq,et⟩ := List.cons.inj eqn
      subst d
      obtain ⟨l,el,er⟩ := ih pref et (fun lt => ord (.cons lt))
      exact ⟨l,congrArg (b::·) el,er⟩

theorem compare_ones (r : Nat) (pref post tail : Tuple) (a marker : Nat) (ha : 0<a)
    (eqn : pref++(a+1)::post = List.replicate r 1 ++ marker::tail) :
    ∃ l, pref=List.replicate r 1++l ∧ l++(a+1)::post=marker::tail := by
  induction r generalizing pref with
  | zero => exact ⟨pref,rfl,eqn⟩
  | succ r ih =>
    rw [List.replicate_succ] at eqn ⊢
    cases pref with
    | nil =>
      have impossible : a+1=1 := (List.cons.inj eqn).1
      omega
    | cons b pref =>
      obtain ⟨eq,et⟩ := List.cons.inj eqn
      subst b
      obtain ⟨l,el,er⟩ := ih pref et
      exact ⟨l,congrArg (1::·) el,er⟩

/-- A pivot at the selected depth in the image window cannot precede s⁺¹
lexicographically. The last entry of the nonempty h is a. -/
theorem imageWindow_prefix (xs : Rows F q w) (s t pref after : Tuple) (c a : Nat) (hc : 0<c)
    (valid : Valid (pref++[a]))
    (bounded : ∀ e∈xs, ∀ j∈e.2.val.1,j≤q)
    (first : ∀ e∈xs, source q s (c::t)=rowSource e ∨ Precedes (source q s (c::t)) (rowSource e))
    (window : ImageWindow (component H xs) (pref++a::after))
    (short : (pref++a::after).length ≤ selectedDepth q s (c::t)) :
    ¬ List.Lex (·<·) (pref++a::after) (endHead s) := by
  cases s with
  | nil =>
    cases pref with
    | nil =>
      intro bad
      have ha := valid a (by simp)
      rcases List.cons_lex_cons_iff.mp bad with h | ⟨_,h⟩
      · omega
      · exact List.not_lex_nil h
    | cons j pref =>
      intro bad
      have hj := valid j (by simp)
      rcases List.cons_lex_cons_iff.mp bad with h | ⟨_,h⟩
      · omega
      · exact List.not_lex_nil h
  | cons b s =>
    obtain ⟨y,nz,ord⟩ := window
    have support := FourSupport.component_support xs (b::s) t y c hc bounded first nz
    simp only [selectedDepth,List.cons_ne_nil,if_false,Nat.add_zero] at short
    change ¬ List.Lex (·<·) (pref++a::after) (incLast (b::s))
    rcases ord with rfl | lt | ⟨eq,lex⟩
    · rcases support with gt | ⟨_,_,good⟩
      · omega
      · exact good
    · simp only [depth] at lt
      rcases support with gt | ⟨eq,_,_⟩ <;> omega
    · simp only [depth] at eq
      rcases support with gt | ⟨_,_,good⟩
      · omega
      · exact fun bad => good (List.lex_trans (fun u v => Nat.lt_trans u v) lex bad)

/-- Negative-prefix alternatives in the actual image window. With
h = pref ++ [a] and a nonempty remaining negative tail, h⁺¹ equals the
marked prefix or extends it by a proper nonempty prefix of the selected
tail. The last entry of that extension is a+1 ≥ 2. -/
theorem negative_prefix (xs : Rows F q w) (s t pref after post tail : Tuple)
    (c a r marker : Nat) (hc : 0<c) (valid : Valid (pref++[a]))
    (bounded : ∀ e∈xs, ∀ j∈e.2.val.1,j≤q)
    (first : ∀ e∈xs, source q s (c::t)=rowSource e ∨ Precedes (source q s (c::t)) (rowSource e))
    (window : ImageWindow (component H xs) (pref++a::after))
    (short : (pref++a::after).length ≤ selectedDepth q s (c::t))
    (post_ne : post≠[])
    (hit : incLast (pref++[a]) ++ post =
      (endHead s ++ List.replicate r 1 ++ [marker]) ++ tail) :
    let stem := endHead s ++ List.replicate r 1 ++ [marker]
    (incLast (pref++[a])=stem ∧ post=tail) ∨
    ∃ l, incLast (pref++[a])=stem++(l++[a+1]) ∧ tail=l++(a+1)::post ∧
      (l++[a+1]).length < tail.length ∧ 1<a+1 := by
  dsimp only
  have ha := valid a (by simp)
  have ord := imageWindow_prefix xs s t pref after c a hc valid bounded first window short
  rw [FourCases.incLast_concat] at hit ⊢
  simp only [List.append_assoc,List.singleton_append] at hit
  obtain ⟨k,ek,et⟩ := compare_base (endHead s) pref post _ after a hit ord
  obtain ⟨l,el,er⟩ := compare_ones r k post tail a marker ha et
  cases l with
  | nil =>
    obtain ⟨ea,ep⟩ := List.cons.inj er
    exact .inl ⟨by simp [ek,el,ea,List.append_assoc],ep⟩
  | cons j l =>
    obtain ⟨ej,ep⟩ := List.cons.inj er
    subst j
    refine .inr ⟨l,by simp [ek,el,List.append_assoc],ep.symm,?_,by omega⟩
    rw [←ep]
    cases post with
    | nil => contradiction
    | cons b post => simp

/-- Apply the prefix comparison to an occurrence in the entire negative
list of a lift. The bound on the pivot suffix allows either lift in a
type III difference. A hit forces equality in this bound and excludes
both h=∅ and the longer ending (h,1). -/
theorem negative_list_prefix (xs : Rows F q w) (s t h after u v tail : Tuple)
    (c r marker : Nat) (hc : 0<c) (valid : Valid h)
    (bounded : ∀ e∈xs, ∀ j∈e.2.val.1,j≤q)
    (first : ∀ e∈xs, source q s (c::t)=rowSource e ∨ Precedes (source q s (c::t)) (rowSource e))
    (window : ImageWindow (component H xs) (h++after))
    (suffix_le : after.length ≤ (u++raiseFirst q v).length)
    (layer : ((endHead s ++ List.replicate r 1 ++ [marker])++tail).length = selectedDepth q s (c::t))
    (occ : ((endHead s ++ List.replicate r 1 ++ [marker])++tail) ∈
      concatenate (endings h) ((L q u v).flatMap (quasiShuffle [q-1]))) :
    let stem := endHead s ++ List.replicate r 1 ++ [marker]
    h≠[] ∧ after.length = (u++raiseFirst q v).length ∧
      ∃ p, endHead h = stem++p ∧ p.length+(u++raiseFirst q v).length = tail.length ∧
        (p=[] ∨ ∃ l a, p=l++[a+1] ∧ 0<a) := by
  dsimp only
  have low := imageWindow_depth xs s t (h++after) c hc bounded first window
  obtain ⟨z,hz,mem⟩ := List.mem_flatMap.mp occ
  obtain ⟨post,hpost,hit⟩ := List.mem_map.mp mem
  have post_ge := Rev4Negative.tails_length q u v hpost
  have lena := (congrArg List.length hit).trans layer
  simp only [List.length_append] at low lena
  have hzlen : z.length = h.length ∨ z.length = h.length+1 := by
    cases h with
    | nil => simp [endings] at hz; simp [hz]
    | cons i h =>
      simp [endings] at hz
      rcases hz with rfl | rfl
      · exact .inl (incLast_length i h)
      · simp
  have same : z.length=h.length := by omega
  have minPost : post.length = (u++raiseFirst q v).length := by omega
  have pn : post ≠ [] := by
    intro ep
    cases v <;> simp [ep,raiseFirst] at minPost <;> omega
  have nz : h≠[] := by
    rintro rfl
    simp [endings] at hz
    simp [hz] at same
  have ez : z = endHead h := by
    cases h with
    | nil => contradiction
    | cons i h =>
      simp [endings] at hz
      rcases hz with rfl | rfl
      · rfl
      · simp at same
  let a := h.getLast nz
  let pref := h.dropLast
  have eh : h=pref++[a] := (List.dropLast_concat_getLast nz).symm
  have endEq : endHead h=incLast h := by cases h <;> first | contradiction | rfl
  have short : (h++after).length ≤ selectedDepth q s (c::t) := by simp; omega
  have ord := negative_prefix xs s t pref after post tail c a r marker hc (eh ▸ valid) bounded first
    (by simpa [eh,List.append_assoc] using window)
    (by simpa [eh,List.append_assoc] using short) pn (by rwa [←eh,←endEq,←ez])
  refine ⟨nz,by omega,?_⟩
  rw [←eh,←endEq] at ord
  rcases ord with ⟨he,ht⟩ | ⟨l,he,ht,_,_⟩
  · exact ⟨[],by simpa using he,by simp [←minPost,ht],.inl rfl⟩
  · refine ⟨l++[a+1],he,by simp [←minPost,ht]; omega,.inr ⟨l,a,rfl,?_⟩⟩
    exact valid a (eh ▸ List.mem_append_right _ (by simp))

end Megaera.Rev4Geometry
