import Megaera.Rev4Geometry

namespace Megaera.Rev4Rival
open Megaera.Triangular Megaera.Splitting Megaera.FourMinimum Megaera.Rev4Geometry

/-- A different canonical row hitting the distinguished layer ends
immediately before the merge at the marked entry. Its right-hand tuple
can be terminal, in which case its effective depth is one. -/
theorem rival_hit (q : Nat) (hq : 2≤q) (s t i u tail : Tuple) (c r marker : Nat)
    (valid : Valid i) (bounded : ∀ j∈i,j≤q) (distinct : i≠s)
    (ord : Precedes (source q s (c::t)) (source q i u))
    (big : q<marker) (same : (c::t).length=r+1+tail.length)
    (occ : ((endHead s++List.replicate r 1++[marker])++tail) ∈ H q i u) :
    i = (endHead s++List.replicate r 1)++[marker-1] ∧
      tail ∈ quasiShuffle [q-1] u ∧ tail.length=width u := by
  let x := (endHead s++List.replicate r 1++[marker])++tail
  have layer : x.length = selectedDepth q s (c::t) := selected_layer q c r marker s t tail same
  have occur : x∈H q i u := occ
  have long := FourCases.depth_ge_source q i u x occur
  have pres : x.length=(source q i u).length ∧ ∃ l, i=endHead s++l ∧ l≠[] := by
    cases s with
    | nil =>
      have dv : (List.replicate r 1 ++ marker::tail).length=width (c::t) := by
        simp [width] at same ⊢; omega
      have rivals := competing_empty_prefix q hq i (c::t) u (List.replicate r 1++marker::tail)
        ord valid dv (by simpa [endHead,List.append_assoc] using occ)
      rcases rivals with ⟨ei,_⟩ | ⟨j,l,ei,dd⟩
      · exact (distinct ei).elim
      · refine ⟨?_,j::l,ei,by simp⟩
        simp only [selectedDepth,FourCases.source_depth,List.length_nil,if_true,Nat.zero_add] at layer ⊢
        unfold width at dd
        omega
    | cons b s =>
      have small : (source q (b::s) (c::t)).length ≤ (source q i u).length :=
        ord.elim Nat.le_of_lt (fun he => Nat.le_of_eq he.1)
      simp only [selectedDepth,List.cons_ne_nil,if_false,Nat.add_zero] at layer
      have eqd : x.length=(source q i u).length := by omega
      have rival := competing_prefix q (b::s) i (c::t) u (List.replicate r 1++marker::tail) (by simp)
        ord (by simpa [x,endHead,List.append_assoc] using layer)
        (by simpa [endHead,List.append_assoc] using occ)
      exact ⟨eqd,rival.resolve_left distinct⟩
  obtain ⟨depth, l, el, ln⟩ := pres
  obtain ⟨p,a,z,ei,ez,hz,dz⟩ := FourCases.minimal_H_parts q i u x occur depth
  obtain ⟨k,b,elast⟩ : ∃ k b, l=k++[b] :=
    ⟨_,_,(List.dropLast_concat_getLast ln).symm⟩
  have exact_i : p++[a]=(endHead s++k)++[b] := by
    rw [←ei,el,elast,List.append_assoc]
  have ab : a=b := by simpa using congrArg List.getLast? exact_i
  subst b
  have ep : p=endHead s++k := List.append_cancel_right exact_i
  have short : k++(a+1)::z = List.replicate r 1++marker::tail := by
    apply List.append_cancel_left (as:=endHead s)
    simpa [x,ep,List.append_assoc] using ez.symm
  have av := valid a (ei ▸ by simp)
  obtain ⟨j,ej,ee⟩ := compare_ones r k z tail a marker av short
  cases j with
  | nil =>
    obtain ⟨em,et⟩ := List.cons.inj ee
    refine ⟨?_,et ▸ hz,et ▸ dz⟩
    simp only [ei,ep,ej,List.append_nil,show marker-1=a by omega]
  | cons m j =>
    have em : m=marker := (List.cons.inj ee).1
    have hm := bounded m (by rw [el,elast,ej]; simp)
    omega

open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.FourLambda Megaera.Rev4Negative
variable {F : Type u} [Arithmetic F] [Neg F] {q : Nat}

/-- Every canonical row with a different left tuple has total reading
zero. In the terminal case its only short suffix is (q−1), so it would
require both n=0 and b=q−1, contrary to the boundary condition. -/
theorem rival_reading_zero (field : ConstantField F q) (s t i u target : Tuple)
    (c r marker n b : Nat) (valid : Valid i) (valid_u : Valid u)
    (bounded : ∀ j∈i,j≤q) (distinct : i≠s)
    (ord : Precedes (source q s (c::t)) (source q i u))
    (big : q<marker) (same : (c::t).length=r+1+(n+1))
    (hb : 0<b) (hb' : b≤q-1) (boundary : b=q-1 → 0<n) :
    total (selected field (endHead s++List.replicate r 1++[marker]) target n b)
      (H q i u)=0 := by
  classical
  let base := endHead s++List.replicate r 1
  let stem := base++[marker]
  let f := selected field stem target n b
  change total f (H q i u)=0
  by_cases hit : ∃ tail : Tuple, tail.length=n+1 ∧ stem++tail∈H q i u
  · obtain ⟨tail,hlen,occ⟩ := hit
    obtain ⟨ei,_,d⟩ := rival_hit q field.two_le s t i u tail c r marker valid bounded distinct
      ord big (by rw [hlen]; exact same) occ
    have de : width u = n+1 := d.symm.trans hlen
    have ein : i≠[] := by simp [ei]
    have endi : incLast i=stem := by
      rw [ei,FourCases.incLast_concat]
      simp [stem,base,show marker-1+1=marker by omega]
    have ei_len : i.length=stem.length := by simp [ei,stem,base]
    have ends : endings i=[incLast i,i++[1]] := by cases i <;> first | contradiction | rfl
    simp only [H,ends,concatenate,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      total_append',total_map,endi]
    have longer : total (fun z => f ((i++[1])++z)) (quasiShuffle [q-1] u)=0 := by
      apply total_zero_of_members
      intro z hz
      obtain ⟨l,perm,sh,lo⟩ := shortest_layer (q-1) u
      have weak : width u≤z.length := by
        rcases List.mem_append.mp (perm.mem_iff.mp hz) with hz | hz
        · exact Nat.le_of_eq (sh z hz).symm
        · exact Nat.le_of_lt (lo z hz)
      apply selected_long
      simp only [List.length_append,List.length_cons,List.length_nil]
      omega
    rw [longer,Arithmetic.addZero]
    by_cases terminal : u=[]
    · subst u
      have n0 : n=0 := by simpa [width] using de.symm
      subst n
      have lt : b<q-1 := by
        apply Nat.lt_of_le_of_ne hb'
        exact fun eq => Nat.lt_irrefl 0 (boundary eq)
      have wrong : (q-1)%(q-1)≠b%(q-1) := by
        simpa [Nat.mod_eq_of_lt lt] using Nat.ne_of_lt hb
      have nz : 0≠b%(q-1) := by simpa using wrong
      simp [quasiShuffle,f,selected,entries,nz,total,Arithmetic.addZero]
    · have upos := List.length_pos_iff.mpr terminal
      have ul : u.length=n+1 := by unfold width at de; omega
      have within : n<u.length := by omega
      have pos : 0<entries u n := by
        simpa [entries,List.getElem?_eq_getElem within] using valid_u u[n] (List.getElem_mem ..)
      simpa [f] using selected_stuffle_zero field stem target [] u n b (by simpa using ul)
        hb hb' (by simpa using pos) (.inl rfl)
  · apply total_zero_of_members
    intro x hx
    simp only [f,selected]
    split
    · rename_i cond
      have eq : stem++x.drop stem.length=x := by
        conv => lhs; lhs; rw [←cond.2.1]
        exact List.take_append_drop _ _
      exact (hit ⟨_,by rw [List.length_drop,cond.1]; omega,eq.symm ▸ hx⟩).elim
    · rfl

end Megaera.Rev4Rival
