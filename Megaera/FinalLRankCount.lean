import Megaera.FinalCanonical
import Megaera.FinalFiniteLists
import Megaera.SectionThreeSpaces

/-! Index the bounded-prefix L rows by all weight-w tuples outside the TT list. -/
namespace Megaera.FinalLRankCount
open Megaera.Finite Megaera.Paper Megaera.Splitting Megaera.Dimension
variable {q w : Nat}

def sources (q w : Nat) : List Tuple :=
  (tuples Int.toNat w).filter (fun s => !(ttRows q w).contains s)

theorem sourceList_nodup : (sources q w).Nodup :=
  List.Pairwise.filter _ (tuples_nodup _ _)

theorem sum_weight (s : Tuple) : s.sum=weight s := by
  induction s with
  | nil => rfl
  | cons a s ih => simp [weight,ih]

theorem tt_mem (s : Tuple) : s ∈ ttRows q w ↔ weight s=w ∧ TT q s := by
  rw [mem_ttRows]
  constructor
  · rintro (⟨h,rfl⟩|⟨p,a,rfl,ha,aq,wt,hb⟩)
    · exact ⟨by simp [weight] at *; omega,Or.inl rfl⟩
    · refine ⟨?_,Or.inr ⟨p,a,rfl,fun b h => (hb b h).1,fun b h => (hb b h).2,ha,aq⟩⟩
      rw [sum_weight] at wt
      simp only [weight_append,weight,Nat.add_zero]; omega
  · rintro ⟨wt,rfl|⟨p,a,rfl,vp,bp,ha,aq⟩⟩
    · exact Or.inl ⟨by simp [weight] at wt; omega,rfl⟩
    · refine Or.inr ⟨p,a,rfl,ha,aq,?_,fun b h => ⟨vp b h,bp b h⟩⟩
      rw [sum_weight]; simp only [weight_append,weight,Nat.add_zero] at wt; omega

theorem mem_sources (s : Tuple) : s∈sources q w ↔ Valid s ∧ weight s=w ∧ ¬TT q s := by
  simp only [sources,List.mem_filter,List.contains_eq_mem,Bool.not_eq_true',decide_eq_false_iff_not,
    mem_unrestricted,tt_mem,sum_weight]
  change (((weight s : Int)=w ∧ Valid s) ∧ ¬(weight s=w ∧ TT q s)) ↔ _
  constructor
  · rintro ⟨⟨e,v⟩,outside⟩
    have ew : weight s=w := by omega
    exact ⟨v,ew,fun ht => outside ⟨ew,ht⟩⟩
  · rintro ⟨v,e,no⟩
    exact ⟨⟨by omega,v⟩,fun h => no h.2⟩



theorem sourceList_card : ((sources q w).length : Int)=tupleCount w-ttCount q w := by
  let all := tuples Int.toNat w
  let tt := ttRows q w
  have sub : ∀ s∈tt,s∈all := by
    intro s hs
    have h := (mem_ttRows q w s).mp hs
    apply (mem_unrestricted _ _).mpr
    rcases h with ⟨h,rfl⟩|⟨p,a,rfl,ha,aq,wt,b⟩
    · simp_all
    · refine ⟨?_,?_⟩
      · simp only [sum_weight,weight_append,weight,Nat.add_zero] at *; omega
      · intro j hj; rcases List.mem_append.mp hj with hj|hj
        · exact (b j hj).1
        · simpa using (List.mem_singleton.mp hj) ▸ ha
  have perm : (all.filter tt.contains).Perm tt := by
    apply FinalFiniteLists.perm_of_nodup _ _ (List.Pairwise.filter tt.contains (tuples_nodup ..)) (ttRows_nodup ..)
    intro s
    rw [List.mem_filter,List.contains_iff_mem]
    exact ⟨And.right,fun h => ⟨sub s h,h⟩⟩
  have len := (List.filter_append_perm tt.contains all).length_eq
  rw [List.length_append,perm.length_eq] at len
  change (_ : Int) = all.length- (tt.length:Int)
  change tt.length+(sources q w).length=all.length at len
  omega

theorem source_inj (i j : Fin (sources q w).length)
    (h : (sources q w).get i=(sources q w).get j) : i=j := by
  obtain ⟨a,ha⟩ := i; obtain ⟨b,hb⟩ := j
  apply Fin.ext
  have ord := List.pairwise_iff_getElem.mp (@sourceList_nodup q w)
  by_cases e : a=b
  · exact e
  · rcases Nat.lt_or_gt_of_ne e with ab|ba
    · exact False.elim (ord a b ha hb ab h)
    · exact False.elim (ord b a hb ha ba h.symm)

noncomputable def rowIndex (i : Fin (sources q w).length) : Row q w := by
  let s := (sources q w).get i
  have hs := (mem_sources s).mp (List.get_mem _ i)
  have markSome := canonical_source_surjective q s hs.1 hs.2.2
  let h := Classical.choose markSome
  let t := Classical.choose (Classical.choose_spec markSome)
  have spec := Classical.choose_spec (Classical.choose_spec markSome)
  exact ⟨(h,t),spec.2.1,spec.2.2.2,by change weight h+weight t+q=w; have := source_weight q h t; rw [spec.1,hs.2.1] at this; omega⟩

theorem row_spec (i : Fin (sources q w).length) :
    source q (rowIndex i).val.1 (rowIndex i).val.2=(sources q w).get i ∧
    ∀ a∈(rowIndex i).val.1,a≤q := by
  let hs := (mem_sources ((sources q w).get i)).mp (List.get_mem _ i)
  have ex := canonical_source_surjective q _ hs.1 hs.2.2
  have h := Classical.choose_spec (Classical.choose_spec ex)
  exact ⟨h.1,h.2.2.1⟩

theorem bounded_row_index (hq : 0<q) (p : Row q w) (bound : ∀ a∈p.val.1,a≤q) :
    ∃ i : Fin (sources q w).length,rowIndex i=p := by
  obtain ⟨⟨h,t⟩,hh,ht,wt⟩ := p
  let s := source q h t
  have valid : Valid s := by
    cases t with
    | nil => intro a ha; rcases List.mem_append.mp ha with ha|ha
             · exact hh a ha
             · simpa using (List.mem_singleton.mp ha) ▸ hq
    | cons a t =>
      intro b hb; rcases List.mem_append.mp hb with hb|hb
      · exact hh b hb
      · rcases List.mem_cons.mp hb with rfl|hb
        · omega
        · exact ht b (by simp [hb])
  have src : s∈sources q w := (mem_sources _).mpr ⟨valid,by
    rw [show weight s=weight h+q+weight t from source_weight ..]; change weight h+weight t+q=w at wt; omega,by
    intro tt
    have marked := (mark_none_iff_TT _ _ valid).mpr tt
    rw [show mark q s=some (h,t) from mark_source q _ _ bound ht] at marked
    contradiction⟩
  obtain ⟨j,hj,ej⟩ := List.getElem_of_mem src
  let i : Fin (sources q w).length := ⟨j,hj⟩
  refine ⟨i,Subtype.ext ?_⟩
  obtain ⟨eh,et⟩ := canonical_source_injective q (row_spec i).2 bound
    (rowIndex i).property.2.1 ht ((row_spec i).1.trans ej)
  exact Prod.ext eh et

end Megaera.FinalLRankCount
