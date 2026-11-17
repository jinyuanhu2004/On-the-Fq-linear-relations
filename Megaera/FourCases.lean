import Megaera.Triangular

/-! Sections 4.2 and 4.3. At the shortest depth the stuffle with a
singleton merges it into one entry, with the extra singleton case
when the input is empty. The lists retain all multiplicities. -/
namespace Megaera.FourCases
open Megaera.Splitting Megaera.Triangular

/-- Add the singleton to each position in turn. -/
def merges (k : Nat) : Tuple → List Tuple
  | [] => []
  | a::s => ((k+a)::s) :: (merges k s).map (a::·)

theorem mem_merges (k : Nat) (t x : Tuple) : x ∈ merges k t ↔
    ∃ h a v, t = h ++ a::v ∧ x = h ++ (k+a)::v := by
  induction t generalizing x with
  | nil => simp [merges]
  | cons b t ih =>
    constructor
    · intro hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨[], b, t, rfl, rfl⟩
      · obtain ⟨y,hm,rfl⟩ := List.mem_map.mp hx
        obtain ⟨h,a,v,ht,rfl⟩ := (ih y).mp hm
        exact ⟨b::h,a,v, congrArg (b::·) ht,rfl⟩
    · rintro ⟨h,a,v,ht,rfl⟩
      cases h with
      | nil => cases ht; exact .head _
      | cons c h =>
        cases List.cons.inj ht with
        | intro eq he =>
          subst c
          exact List.mem_cons_of_mem _ (List.mem_map.mpr
            ⟨_,(ih _).mpr ⟨h,a,v,he,rfl⟩,rfl⟩)

/-- Filtering by depth obtains exactly all merges. -/
theorem shortest_stuffle (k : Nat) (t : Tuple) :
    (quasiShuffle [k] t).filter (fun x => decide (x.length=t.length)) =
      (merges k t).reverse := by
  induction t with
  | nil => simp [merges]
  | cons b t ih =>
    rw [quasiShuffle.eq_3]
    simp only [quasiShuffle_nil_left,List.map_cons,List.map_nil,List.filter_append,
      List.filter_cons,List.filter_nil,List.length_cons]
    simp only [Nat.add_right_cancel_iff,Nat.succ_ne_self,decide_false,Bool.false_eq_true,
      if_false,decide_true,if_true,List.nil_append]
    rw [List.filter_map]
    simp only [Function.comp_def,List.length_cons,Nat.add_right_cancel_iff]
    simp [merges,ih,List.map_reverse]

theorem source_depth (q : Nat) (h t : Tuple) :
    (source q h t).length = h.length + max 1 t.length := by
  cases t <;> simp [source]

theorem depth_ge_source (q : Nat) (h t x : Tuple) (hx : x ∈ H q h t) :
    (source q h t).length ≤ x.length := by
  have hp := source_precedes_H q h t x hx
  rcases hp with hn | ⟨hn,_⟩ <;> simp only [depth] at hn <;> omega

/-- The corrected depth constraint for a row contributing to the selected
layer of a nonempty prefix. A terminal row has effective tail depth one. -/
theorem competing_depth (q : Nat) (h t x : Tuple) (d : Nat)
    (later : d ≤ (source q h t).length) (hx : x ∈ H q h t) (hd : x.length=d) :
    h.length + max 1 t.length = d := by
  have := depth_ge_source q h t x hx
  rw [←source_depth q h t]; omega

/-- The old depth equation in Section 4.2 fails at an empty competing
tail at every q. Both marked rows are canonical and have the same weight. -/
theorem terminal_competitor (q : Nat) (hq : 2 ≤ q) :
    (∀ a ∈ ([2,q] : Tuple), a ≤ q) ∧
    weight [1]+weight [q-1,2] = weight [2,q]+weight [] ∧
    Precedes (source q [1] [q-1,2]) (source q [2,q] []) ∧
    (incLast [1] ++ [q+1,q-1]) ∈ H q [2,q] [] ∧
    (incLast [1] ++ [q+1,q-1]).length = (source q [1] [q-1,2]).length ∧
    ([2,q] : Tuple).length + ([] : Tuple).length ≠ (source q [1] [q-1,2]).length := by
  refine ⟨?_,?_,?_,?_,rfl,by simp [source]⟩
  · simpa using hq
  · simp only [weight]; omega
  · right
    exact ⟨rfl,.rel (by decide : 1 < 2)⟩
  · simp [H,endings,incLast,concatenate]

/-- Incrementing a nonempty tuple only changes its final entry. -/
theorem incLast_concat (h : Tuple) (b : Nat) : incLast (h ++ [b]) = h ++ [b+1] := by
  induction h with
  | nil => rfl
  | cons a h ih => cases h with
    | nil => rfl
    | cons c h => exact congrArg (a::·) ih

private theorem bound_pairwise (q : Nat) {h : Tuple} (hh : ∀ a ∈ h, a ≤ q) :
    h.Pairwise (fun a b => q < a → b = 1) := by
  induction h with
  | nil => exact .nil
  | cons a t ih =>
    exact List.pairwise_cons.mpr ⟨fun b _ h => False.elim (Nat.not_lt_of_ge (hh a (by simp)) h),
      ih (fun b hb => hh b (List.mem_cons_of_mem _ hb))⟩

/-- The selected tuple in Case I cannot have any of the three leading
shapes. All three would contain the marked segment
`source q [] (incLast a)` before a nonempty right suffix. -/
theorem case_I_excludes_types (q : Nat) (hq : 2 ≤ q) (s : Tuple) (j r z : Nat)
    (hs : ∀ a ∈ s, a ≤ q) (hj : j ≤ q+1)
    (h a t : Tuple) (ha : Valid a) (hn : a ≠ []) (ht : t ≠ []) :
    (s ++ j :: (List.replicate r 1 ++ [z])) ≠
       (h ++ source q [] (incLast a) ++ t) := by
  intro eqn
  have e := congrArg List.dropLast eqn
  have left_eq : s ++ j :: (List.replicate r 1 ++ [z]) =
      (s ++ j :: List.replicate r 1) ++ [z] := by simp
  rw [left_eq,List.dropLast_concat,List.dropLast_append_of_ne_nil ht] at e
  let R := fun (a b : Nat) => q < a → b = 1
  have hb : ∀ x ∈ s ++ j :: List.replicate r 1, x ≤ q+1 := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact Nat.le_trans (hs x hx) (Nat.le_succ _)
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact hj
      · have := List.eq_of_mem_replicate hx; omega
  have hp : (s ++ j :: List.replicate r 1).Pairwise R := by
    apply List.pairwise_append.mpr
    refine ⟨bound_pairwise q hs, .cons (fun b hb _ => List.eq_of_mem_replicate hb) ?_,
      fun x hx _ _ h => False.elim (Nat.not_lt_of_ge (hs x hx) h)⟩
    simp [R]
  rw [e] at hp hb
  have pb := (List.pairwise_append.mp (List.pairwise_append.mp hp).1).2.1
  have bb (x : Nat) (hm : x ∈ source q [] (incLast a)) : x ≤ q+1 :=
    hb x (List.mem_append_left _ (List.mem_append_right _ hm))
  cases a with
  | nil => contradiction
  | cons b v =>
    have bpos := ha b (by simp)
    by_cases hv : v = []
    · subst v
      have := bb (q+(b+1)) (by simp [incLast,source])
      omega
    · let last := v.getLast hv
      have hv' : v = v.dropLast ++ [last] := (List.dropLast_concat_getLast hv).symm
      have endpos := ha last (List.mem_cons_of_mem _ (List.getLast_mem hv))
      have inc : incLast (b::v) = b::(v.dropLast ++ [last+1]) := by
        calc _ = incLast ((b::v.dropLast) ++ [last]) := congrArg incLast (congrArg (b::·) hv')
             _ = _ := incLast_concat _ _
      rw [inc] at pb
      have hrel := (List.pairwise_cons.mp pb).1 (last+1)
        (by simp [source])
      change q < q+b → last+1=1 at hrel
      have := hrel (by omega); omega

/-- The negative component in page 24 can produce a tuple with the
selected prefix even when every term of the relation is above the
comparison tuple. This family concerns the support assertion before
applying λ. Its terminal residue is 1 for every q ≥ 4. -/
theorem negative_hits_selection (q : Nat) (hq : 4 ≤ q) :
    let t' : Tuple := [2,q,3,1]
    let cutoff := source q [] t'
    let pair := generalP (K := Int) q [2] [1,2,1]
    let hit : Tuple := [1,q+1,q+1,2,1]
    weight t' + q = weight [2] + weight [1,2,1] + 2*q ∧
    (∀ e ∈ liftPair pair, Precedes cutoff e.2) ∧
    ((-1:Int),hit) ∈ pair.2 ∧
    (∀ e ∈ pair.1, e.2 ≠ hit) ∧
    (pair.2.map Prod.snd).count hit = 1 := by
  dsimp only
  have hm : q-1+2=q+1 := by omega
  have h1 : q ≠ 1 := by omega
  have h2 : q+3 ≠ 1 := by omega
  have h3 : q+2 ≠ 1 := by omega
  have h4 : q+1 ≠ 2 := by omega
  have h5 : q+1 ≠ 1 := by omega
  have h6 : q+1 ≠ q-1 := by omega
  have h7 : ¬ q+2=q+1 := by omega
  refine ⟨by simp only [weight]; omega, ?_, ?_, ?_, ?_⟩
  · have lex (a b c : Nat) : Precedes (source q [] [2,q,3,1]) [q+3,a,b,c] :=
      Or.inr ⟨rfl,.rel (by omega)⟩
    simp [generalP,H,L,liftPair,endings,incLast,concatenate,start,withCoeff,quasiShuffle.eq_3,
      lex,Precedes,depth,source,show q+2 < q+3 by omega,List.Lex.rel]
    exact ⟨.rel (by omega),.rel (by omega),.rel (by omega)⟩
  · simp [generalP,L,start,withCoeff,quasiShuffle.eq_3,hm]
  · simp [generalP,H,endings,incLast,concatenate,start,withCoeff,quasiShuffle.eq_3,h1,h2,h3]
  · simp [generalP,L,start,withCoeff,quasiShuffle.eq_3,hm,List.count_cons,
      h1,h2,h3,h4,h5,h6,h7,beq_iff_eq]

private theorem lex_append_left {s t : Tuple} (h : Tuple) (hlt : List.Lex (· < ·) s t) :
    List.Lex (· < ·) (h ++ s) (h ++ t) := by
  induction h with
  | nil => exact hlt
  | cons a h ih => exact .cons ih

private theorem peeled_row_prefix (s h v : Tuple) (a b r z : Nat)
    (hb : 0 < b) (hv : v ≠ []) (tail₀ tail : Tuple)
    (he : h ++ (b+1)::v = s ++ (a+1)::(List.replicate r 1 ++ [z]))
    (order : ¬ List.Lex (· < ·) (h ++ b::tail) (s ++ a::tail₀)) :
    h=s ∧ b=a ∧ v=List.replicate r 1 ++ [z] := by
  induction s generalizing h with
  | nil =>
    cases h with
    | nil => simp_all
    | cons c h =>
      obtain ⟨_,et⟩ := List.cons.inj he
      change h ++ (b+1)::v = List.replicate r 1 ++ [z] at et
      have shorten := congrArg List.dropLast et
      rw [show h++(b+1)::v = (h++[b+1])++v by simp,
        List.dropLast_append_of_ne_nil hv,List.dropLast_concat] at shorten
      have member : b+1 ∈ List.replicate r 1 := by rw [←shorten]; simp
      have := List.eq_of_mem_replicate member
      omega
  | cons c s ih =>
    cases h with
    | nil =>
      have eh := (List.cons.inj he).1
      exfalso
      exact order (.rel (by omega : b < c))
    | cons d h =>
      obtain ⟨rfl,et⟩ := List.cons.inj he
      obtain ⟨rfl,eb,ev⟩ := ih h et fun hx => order (.cons hx)
      exact ⟨rfl,eb,ev⟩

private theorem merge_ones {k : Nat} (hk : 0 < k) (t : Tuple) (ht : Valid t)
    (r z : Nat) (hm : List.replicate r 1 ++ [z+k] ∈ merges k t) :
    t = List.replicate r 1 ++ [z] := by
  induction r generalizing t with
  | zero =>
    obtain ⟨h,a,v,et,ep⟩ := (mem_merges ..).mp hm
    cases h with
    | nil =>
      obtain ⟨ea, ev⟩ := List.cons.inj ep
      simpa [ev.symm, show a=z by omega] using et
    | cons b h =>
      have e := congrArg List.length ep
      simp at e
  | succ r ih =>
    cases t with
    | nil => simp [merges] at hm
    | cons a t =>
      rw [List.replicate_succ, List.cons_append,merges] at hm
      rcases List.mem_cons.mp hm with eq | hm
      · have := (List.cons.inj eq).1
        have := ht a (by simp)
        omega
      · obtain ⟨w,hw,e⟩ := List.mem_map.mp hm
        obtain ⟨rfl,rfl⟩ := List.cons.inj e
        have := ih t (fun x hx => ht x (List.mem_cons_of_mem _ hx)) hw
        simp [this,List.replicate_succ]

theorem minimal_H_parts (q : Nat) (s t x : Tuple)
    (hx : x ∈ H q s t) (hd : x.length = (source q s t).length) :
    ∃ h a v, s=h++[a] ∧ x=h++(a+1)::v ∧ v ∈ quasiShuffle [q-1] t ∧
      v.length=max 1 t.length := by
  obtain ⟨u,hu,hm⟩ := List.mem_flatMap.mp hx
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hm
  have hb : max 1 t.length ≤ v.length := by
    cases t with
    | nil => have eqv : v=[q-1] := by simpa using hv
             simp [eqv]
    | cons c l => exact (by simpa using singleton_stuffle_depth (q-1) (c::l) v hv)
  rw [source_depth,List.length_append] at hd
  cases s with
  | nil =>
    have he : u=[1] := List.mem_singleton.mp hu
    subst u; simp at hd; omega
  | cons b s =>
    rcases List.mem_cons.mp hu with rfl | h
    · have e := List.dropLast_concat_getLast (List.cons_ne_nil b s)
      refine ⟨(b::s).dropLast,(b::s).getLast (by simp),v,e.symm,?_,hv,?_⟩
      · have hi := (congrArg incLast e).symm.trans (incLast_concat ..)
        rw [hi]; simp
      · rw [incLast_length] at hd; omega
    · have he : u=(b::s)++[1] := List.mem_singleton.mp h
      subst u; simp at hd; omega

private theorem source_join (q : Nat) (s t : Tuple) :
    source q s t = s ++ source q [] t := by cases t <;> rfl

/-- At a nonempty left prefix in Case I, only the original canonical row
can contribute the chosen tuple. This includes a terminal original row.
The inputs express the common weight and the ordering of the L-sources. -/
theorem case_I_isolates_row (q : Nat) (hq : 2 ≤ q) (s h t u : Tuple) (a r z : Nat)
    (hh : Valid h) (hu : Valid u)
    (original : (t=List.replicate r 1 ++ [z] ∧ 0<z) ∨ (t=[] ∧ r=0 ∧ z=0))
    (wt : weight (s++[a]) + weight t = weight h + weight u)
    (order : source q (s++[a]) t = source q h u ∨ Precedes (source q (s++[a]) t) (source q h u))
    (hits : s ++ (a+1)::(List.replicate r 1 ++ [z+(q-1)]) ∈ H q h u) :
    h=s++[a] ∧ u=t := by
  let x := s ++ (a+1)::(List.replicate r 1 ++ [z+(q-1)])
  have hd : x.length = (source q (s++[a]) t).length := by
    rw [source_depth]; rcases original with ⟨rfl,hz⟩ | ⟨rfl,rfl,rfl⟩ <;>
      simp [x,Nat.add_assoc] <;> omega
  have hle : (source q (s++[a]) t).length ≤ (source q h u).length := by
    rcases order with e | e
    · rw [e]; exact Nat.le_refl _
    · rcases e with e | ⟨e,_⟩ <;> unfold depth at e <;> omega
  have hb := depth_ge_source q h u x hits
  have heq : x.length = (source q h u).length := by omega
  obtain ⟨j,b,v,eh,ex,hv,ev⟩ := minimal_H_parts q h u x hits heq
  subst h
  have hn : v ≠ [] := by intro e; rw [e] at ev; simp at ev; omega
  have ord : ¬ List.Lex (· < ·) (j ++ b::(source q [] u)) (s ++ a::(source q [] t)) := by
    intro e
    have back : Precedes (source q (j++[b]) u) (source q (s++[a]) t) := by
      refine .inr ⟨heq.symm.trans hd,?_⟩
      rw [source_join q (j++[b]),source_join q (s++[a])]
      simpa using e
    rcases order with e | f
    · rw [e] at back; exact precedes_irrefl _ back
    · exact precedes_irrefl _ (precedes_trans back f)
  have hpos := hh b (by simp)
  obtain ⟨rfl,rfl,eqv⟩ := peeled_row_prefix s j v a b r (z+(q-1)) hpos hn
    (source q [] t) (source q [] u) ex.symm ord
  refine ⟨rfl,?_⟩
  have wt' : weight t = weight u := by omega
  rcases original with ⟨rfl,hz⟩ | ⟨rfl,rfl,rfl⟩
  · cases u with
    | nil => simp only [weight_append,weight,Nat.add_zero] at wt'; omega
    | cons c u =>
      have eqd : v.length=(c::u).length := by simpa using ev
      have mm : v ∈ merges (q-1) (c::u) := by
        have hmem : v ∈ (quasiShuffle [q-1] (c::u)).filter (fun y => decide (y.length=(c::u).length)) :=
          List.mem_filter.mpr ⟨hv,decide_eq_true eqd⟩
        rwa [shortest_stuffle,List.mem_reverse] at hmem
      exact merge_ones (by omega : 0<q-1) (c::u) hu r z (eqv ▸ mm)
  · cases u with
    | nil => rfl
    | cons c u =>
      have hc := hu c (by simp); simp only [weight] at wt'; omega

/-- The empty-prefix Case I pivot is also isolated. At equal source depth
a competing nonempty prefix starts at most at q, whereas the empty-prefix
source starts above q. At greater depth the competing row would have to
increase a positive prefix entry to a 1. -/
theorem case_I_isolates_empty_prefix (q : Nat) (hq : 2 ≤ q)
    (h t u : Tuple) (r z : Nat)
    (hh : Valid h) (hu : Valid u) (bounded : ∀ a ∈ h, a ≤ q)
    (original : (t=List.replicate r 1 ++ [z] ∧ 0<z) ∨ (t=[] ∧ r=0 ∧ z=0))
    (wt : weight t = weight h + weight u)
    (order : source q [] t = source q h u ∨ Precedes (source q [] t) (source q h u))
    (hits : 1::(List.replicate r 1 ++ [z+(q-1)]) ∈ H q h u) :
    h=[] ∧ u=t := by
  rcases original with ⟨rfl,hz⟩ | ⟨rfl,rfl,rfl⟩
  · let t := List.replicate r 1 ++ [z]
    have ht : Valid t := by
      intro a ha
      rcases List.mem_append.mp ha with m | m
      · have h := List.eq_of_mem_replicate m; omega
      · obtain rfl := List.mem_singleton.mp m; exact hz
    have hd : (source q [] t).length = r+1 := by simp [source_depth,t]
    have lo : r+1 ≤ (source q h u).length := by
      rcases order with e | e
      · exact hd ▸ Nat.le_of_eq (congrArg List.length e)
      · change Precedes (source q [] t) (source q h u) at e
        rcases e with he | ⟨he,_⟩ <;> unfold depth at he <;> omega
    cases h with
    | nil =>
      refine ⟨rfl,?_⟩
      have hv : List.replicate r 1 ++ [z+(q-1)] ∈ quasiShuffle [q-1] u := by
        simpa [H,endings,concatenate] using hits
      cases u with
      | nil => simp [weight] at wt; omega
      | cons c u =>
        have ed := singleton_stuffle_depth (q-1) (c::u) _ hv
        simp only [List.length_append,List.length_replicate,List.length_cons,List.length_nil] at ed
        rw [source_depth] at lo
        simp at lo
        have eql : (List.replicate r 1 ++ [z+(q-1)]).length = (c::u).length := by simp; omega
        have hmem : (List.replicate r 1 ++ [z+(q-1)]) ∈
            (quasiShuffle [q-1] (c::u)).filter (fun y => decide (y.length=(c::u).length)) :=
          List.mem_filter.mpr ⟨hv,decide_eq_true eql⟩
        rw [shortest_stuffle,List.mem_reverse] at hmem
        exact merge_ones (by omega : 0<q-1) _ hu _ _ hmem
    | cons c h =>
      have hc := bounded c (by simp)
      have gt : r+1 < (source q (c::h) u).length := by
        apply Classical.byContradiction
        intro no
        have eqd : (source q (c::h) u).length = (source q [] t).length := by omega
        have hcomp : List.Lex (· < ·) (source q (c::h) u) (source q [] t) := by
          have tg : t ≠ [] := by simp [t]
          cases he : t with
          | nil => contradiction
          | cons a l =>
            have ha := ht a (he ▸ List.mem_cons_self)
            rw [source_join q (c::h)]; exact .rel (by omega)
        rcases order with e | f
        · change source q [] t = _ at e
          rw [e] at hcomp
          exact List.lex_irrefl Nat.lt_irrefl _ hcomp
        · exact precedes_irrefl _ (precedes_trans (.inr ⟨eqd,hcomp⟩) f)
      have le := depth_ge_source q (c::h) u _ hits
      have hlen : (1::(List.replicate r 1 ++ [z+(q-1)])).length=r+2 := by simp
      obtain ⟨j,b,v,he,ex,hv,ev⟩ := minimal_H_parts q (c::h) u _ hits (by omega)
      have hb := hh b (he ▸ (by simp))
      have vn : v ≠ [] := by intro vv; rw [vv] at ev; simp at ev; omega
      have hd' := congrArg List.dropLast ex
      have ex1 : 1 :: (List.replicate r 1 ++ [z+(q-1)]) =
          (1 :: List.replicate r 1) ++ [z+(q-1)] := rfl
      rw [ex1,List.dropLast_concat,show j++(b+1)::v = (j++[b+1])++v by simp,
        List.dropLast_append_of_ne_nil vn] at hd'
      have member : b+1 ∈ 1 :: List.replicate r 1 := by rw [hd']; simp
      rcases List.mem_cons.mp member with m | m
      · omega
      · have := List.eq_of_mem_replicate m; omega
  · cases h with
    | cons c h => have hc := hh c (by simp); simp [weight] at wt; omega
    | nil =>
      cases u with
      | nil => exact ⟨rfl,rfl⟩
      | cons c u => have hc := hu c (by simp); simp [weight] at wt; omega

private theorem count_prepend (s t : Tuple) (l : List Tuple) :
    (l.map (s++·)).count (s++t) = l.count t := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.count_cons,ih,beq_iff_eq]

private theorem unit_merge (k : Nat) (hk : 0<k) (r z : Nat) :
    (merges k (List.replicate r 1 ++ [z])).count (List.replicate r 1 ++ [z+k]) = 1 := by
  induction r with
  | zero => simp [merges,Nat.add_comm]
  | succ r ih =>
    simp only [List.replicate_succ,List.cons_append,merges,List.count_cons]
    change (List.map (([1]:Tuple)++·) _).count ([1]++_) + _ = 1
    rw [count_prepend]
    simpa [beq_iff_eq,show k≠0 by omega] using ih

private theorem unit_tail (q r z : Nat) (hq : 2 ≤ q) (t : Tuple)
    (original : (t=List.replicate r 1 ++ [z] ∧ 0<z) ∨ (t=[] ∧ r=0 ∧ z=0)) :
    (quasiShuffle [q-1] t).count (List.replicate r 1 ++ [z+(q-1)]) = 1 := by
  rcases original with ⟨rfl,hz⟩ | ⟨rfl,rfl,rfl⟩
  · let t := List.replicate r 1 ++ [z]
    let x := List.replicate r 1 ++ [z+(q-1)]
    have eql : x.length=t.length := by simp [x,t]
    have hf := @List.count_filter Tuple _ _ (fun y : Tuple => decide (y.length=t.length)) x
      (quasiShuffle [q-1] t) (decide_eq_true eql)
    rw [shortest_stuffle,List.count_reverse] at hf
    exact hf.symm.trans (unit_merge (q-1) (by omega) r z)
  · simp

/-- The tuple isolated above has row coefficient one before passing to
any constant field. The argument counts with all stuffle multiplicities. -/
theorem case_I_pivot_count (q : Nat) (hq : 2 ≤ q) (h t : Tuple) (r z : Nat)
    (original : (t=List.replicate r 1 ++ [z] ∧ 0<z) ∨ (t=[] ∧ r=0 ∧ z=0)) :
    let pref := if h = [] then [1] else incLast h
    (H q h t).count (pref ++ (List.replicate r 1 ++ [z+(q-1)])) = 1 := by
  dsimp only
  cases h with
  | nil =>
    simp only [if_pos rfl,H,endings,concatenate,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    exact (count_prepend _ _ _).trans (unit_tail q r z hq t original)
  | cons a h =>
    let x := List.replicate r 1 ++ [z+(q-1)]
    have width : x.length = max 1 t.length := by
      rcases original with ⟨rfl,_⟩|⟨rfl,rfl,rfl⟩ <;> simp [x]
    have absent : incLast (a::h) ++ x ∉ (quasiShuffle [q-1] t).map (((a::h)++[1])++·) := by
      intro hm; obtain ⟨v,hv,he⟩ := List.mem_map.mp hm
      have vd : max 1 t.length ≤ v.length := by
        cases t with
        | nil => have eqv : v=[q-1] := by simpa using hv
                 simp [eqv]
        | cons c l => simpa using singleton_stuffle_depth (q-1) (c::l) v hv
      have := congrArg List.length he
      simp only [List.length_append,incLast_length,List.length_cons,List.length_nil,width] at this
      omega
    simp only [List.cons_ne_nil,if_false,H,endings,concatenate,List.flatMap_cons,List.flatMap_nil,
      List.append_nil,List.count_append]
    rw [List.count_eq_zero_of_not_mem absent,count_prepend,Nat.add_zero]
    exact unit_tail q r z hq t original

open Megaera.Finite Megaera.Carlitz Megaera.Paper
variable {F : Type u} [Arithmetic F]

private theorem coeff_absent (l : List Tuple) (s : Tuple) (absent : s ∉ l) :
    coordinates (withCoeff (1:F) l) s = 0 := by
  apply total_zero_of_members
  intro e he
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp he
  exact if_neg (fun ep : t=s => absent (ep ▸ ht))

private theorem coeff_one (l : List Tuple) (s : Tuple) (cnt : l.count s = 1) :
    coordinates (withCoeff (1:F) l) s = 1 := by
  induction l with
  | nil => simp at cnt
  | cons a l ih =>
    by_cases e : a=s
    · subst a
      simp [List.count_cons] at cnt
      rw [List.count_eq_zero] at cnt
      change (if s=s then (1:F) else 0) + coordinates (withCoeff 1 l) s = 1
      rw [if_pos rfl,coeff_absent _ _ cnt,Arithmetic.addZero]
    · simp [List.count_cons,beq_iff_eq,e] at cnt
      change (if a=s then (1:F) else 0) + coordinates (withCoeff 1 l) s = 1
      rw [if_neg e,zeroAdd,ih cnt]

/-- The actual selected coefficient of Ind P in Case I equals the
coefficient of the least row of P. This includes both choices of empty
tuple and all positive weights, with no independence assumption. -/
theorem case_I_coefficient (q w : Nat) (hq : 2 ≤ q) (e : F × Row q w) (rows : Rows F q w)
    (r z : Nat)
    (original : (e.2.val.2=List.replicate r 1 ++ [z] ∧ 0<z) ∨
      (e.2.val.2=[] ∧ r=0 ∧ z=0))
    (ordered : ∀ f∈rows, Precedes (rowSource e) (rowSource f))
    (bounded : ∀ f∈rows, ∀ i∈f.2.val.1, i≤q) :
    let s := e.2.val.1
    let target := (if s=[] then [1] else incLast s) ++ (List.replicate r 1 ++ [z+(q-1)])
    component H (e::rows) target = e.1 := by
  dsimp only
  let s := e.2.val.1
  let t := e.2.val.2
  let target := (if s=[] then [1] else incLast s) ++ (List.replicate r 1 ++ [z+(q-1)])
  have first : coordinates (withCoeff (1:F) (H q s t)) target = 1 :=
    coeff_one _ _ (case_I_pivot_count q hq s t r z original)
  have rest : component H rows target = 0 := by
    apply total_zero_of_members
    intro f hf
    have before := ordered f hf
    change Precedes (source q s t) (source q f.2.val.1 f.2.val.2) at before
    have weightEq : weight s + weight t = weight f.2.val.1 + weight f.2.val.2 := by
      have we := e.2.property.2.2
      have wf := f.2.property.2.2
      dsimp [s,t]; omega
    have nohit : target ∉ H q f.2.val.1 f.2.val.2 := by
      intro hits
      suffices same : f.2.val.1=s ∧ f.2.val.2=t by
        rw [same.1,same.2] at before; exact precedes_irrefl _ before
      by_cases hs : s=[]
      · have emp := case_I_isolates_empty_prefix q hq f.2.val.1 t f.2.val.2 r z
          f.2.property.1 f.2.property.2.1 (bounded f hf) original
          (by simpa [hs,weight] using weightEq) (Or.inr (hs ▸ before)) (by simpa [target,hs] using hits)
        exact ⟨emp.1.trans hs.symm,emp.2⟩
      · have last := List.dropLast_concat_getLast hs
        have iso := case_I_isolates_row q hq s.dropLast f.2.val.1 t f.2.val.2 (s.getLast hs) r z
          f.2.property.1 f.2.property.2.1 original (by simpa only [last] using weightEq)
          (Or.inr (by simpa only [last] using before)) (by
            change (if s=[] then [1] else incLast s) ++ _ ∈ _ at hits
            rw [if_neg hs, (congrArg incLast last).symm.trans (incLast_concat ..)] at hits
            simpa using hits)
        exact ⟨iso.1.trans last,iso.2⟩
    rw [coeff_absent _ _ nohit,Arithmetic.mulZero]
  change e.1 * coordinates _ target + component H rows target = _
  rw [rest,first,Arithmetic.mulOne,Arithmetic.addZero]

end Megaera.FourCases
