import Megaera.FourCaseIProof
import Megaera.Rev4Negative

/-! The positive contribution to S on the selected layer in §4.3. -/
namespace Megaera.Rev4Positive
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.Triangular Megaera.FourMinimum
open Megaera.FourLambda Megaera.Rev4Negative
variable {F : Type u} [Arithmetic F] [Neg F]

private theorem end_eq (s : Tuple) : endHead s = if s=[] then [1] else incLast s := by
  cases s <;> simp [endHead]

/-- Every positive term which meets the chosen slice contains the whole
marker before its remaining singleton-stuffle output. -/
theorem positive_prefix (hq : 2≤q) (s h u z tail : Tuple) (r m : Nat)
    (bounded : ∀ j∈s,j≤q) (valid : Valid u) (un : u≠[])
    (hit : (h++raiseFirst q (incLast u))++z =
      (endHead s++(List.replicate r 1++[m]))++tail) :
    ∃ p, h++raiseFirst q (incLast u) = (endHead s++(List.replicate r 1++[m]))++p ∧
      tail=p++z := by
  rcases List.append_eq_append_iff.mp hit with ⟨l,eq,rest⟩ | alt
  · by_cases emp : l=[]
    · subst l; exact ⟨[],by simpa using eq.symm,by simpa using rest.symm⟩
    · apply False.elim
      apply FourCaseIProof.excludes_short_positive hq s r m bounded h u l valid un emp
      simpa only [end_eq,List.append_assoc] using eq
  · exact alt

private theorem stem_last (q : Nat) (h u : Tuple) (vu : Valid u) (un : u≠[]) :
    ∃ p a, h++raiseFirst q (incLast u) = p++[a] ∧ 1<a := by
  obtain ⟨p,a,eq⟩ : ∃ p a,u=p++[a] := ⟨_,_,(List.dropLast_concat_getLast un).symm⟩
  have pos := vu a (by rw [eq]; simp)
  rw [eq,FourCases.incLast_concat]
  cases p with
  | nil => exact ⟨h,q+(a+1),rfl,by omega⟩
  | cons j p => exact ⟨h++(q+j)::p,a+1,by simp [raiseFirst],by omega⟩

private theorem final_entry (t p : Tuple) (n : Nat) (hv : Valid t) (tn : t≠[])
    (len : p.length+t.length=n+1) : 0<entries (p++t) n := by
  obtain ⟨l,a,eq⟩ : ∃ l a,t=l++[a] := ⟨_,_,(List.dropLast_concat_getLast tn).symm⟩
  have pos := hv a (by rw [eq]; simp)
  rw [eq] at len ⊢
  have en : n=(p++l).length := by simp at len ⊢; omega
  simpa [←List.append_assoc,en,entries,List.getElem?_append] using pos

private theorem split_last (p marker h u z : Tuple) (q : Nat) (vu : Valid u) (un : u≠[])
    (eq : h++raiseFirst q (incLast u) = marker++p) :
    p=[] ∨ 1<entries (p++z) (p.length-1) := by
  by_cases em : p=[]
  · exact .inl em
  · right
    obtain ⟨l,a,rfl⟩ : ∃ l a,p=l++[a] := ⟨_,_,(List.dropLast_concat_getLast em).symm⟩
    obtain ⟨k,b,eb,large⟩ := stem_last q h u vu un
    have ee := congrArg List.getLast? (eb.symm.trans eq)
    simp [←List.append_assoc] at ee
    simpa [List.append_assoc,entries,List.getElem?_append,ee] using large

private theorem selected_hit (field : ConstantField F q) (stem target x : Tuple) (n b : Nat)
    (nz : selected field stem target n b x≠0) : ∃ tail, x=stem++tail := by
  simp only [selected] at nz
  split at nz
  · rename_i cond
    exact ⟨_,by rw [←cond.2.1]; exact (List.take_append_drop _ _).symm⟩
  · contradiction

private theorem terminal_stuffle (field : ConstantField F q) (marker target p : Tuple)
    (n b : Nat) (hlen : p.length=n) (hb : 0<b) (hb' : b≤q-1)
    (boundary : b=q-1 → ∃ j,n=j+1 ∧ entries target j=1)
    (endp : p=[] ∨ 1<entries (p++[q-1]) (p.length-1)) :
    selected field marker target n b ((marker++p)++[q-1])=0 := by
  by_cases eq : b=q-1
  · obtain ⟨j,ej,v⟩ := boundary eq
    have hn : 0<p.length := by omega
    have hlast : 1<entries (p++[q-1]) j := by
      rcases endp with rfl | endp
      · simp at hn
      · simpa only [show p.length-1=j by omega] using endp
    have final : entries (p++[q-1]) (j+1)=b := by
      simp [entries,←show p.length=j+1 by omega,List.getElem?_append,eq]
    simp only [selected,List.append_assoc,List.drop_left]
    split
    · rw [ej]; exact terminal_zero field j b _ _ v hlast final
    · rfl
  · have lt : b<q-1 := by omega
    have bad : (q-1)%(q-1) ≠ b%(q-1) := by simpa [Nat.mod_eq_of_lt lt] using Nat.ne_of_lt hb
    have last : entries (p++[q-1]) n=q-1 := by simp [entries,←hlen,List.getElem?_append]
    simp only [selected,List.append_assoc,List.drop_left,last]
    rw [if_neg (fun c => bad c.2.2)]

/-- The selected sum over the full positive singleton product is zero.
The terminal right tuple uses the b=q−1 boundary clause, including the
case n=0. -/
theorem positive_stuffle_zero (field : ConstantField F q) (s h u v target : Tuple)
    (r m n b : Nat) (bounded : ∀ j∈s,j≤q) (vu : Valid u) (un : u≠[]) (vv : Valid v)
    (hb : 0<b) (hb' : b≤q-1) (boundary : b=q-1 → ∃ j,n=j+1 ∧ entries target j=1)
    (len : (h++raiseFirst q (incLast u)).length+width v =
      (endHead s++(List.replicate r 1++[m])).length+(n+1)) :
    total (fun z => selected field (endHead s++(List.replicate r 1++[m])) target n b
        ((h++raiseFirst q (incLast u))++z)) (quasiShuffle [q-1] v) = 0 := by
  let marker := endHead s++(List.replicate r 1++[m])
  let stem := h++raiseFirst q (incLast u)
  by_cases ext : ∃ p,stem=marker++p
  · obtain ⟨p,eq⟩ := ext
    have length' : p.length+width v=n+1 := by
      change stem.length+width v=marker.length+(n+1) at len
      rw [eq,List.length_append] at len; omega
    change total (fun z => selected field marker target n b (stem++z)) _=0
    rw [eq]
    by_cases em : v=[]
    · subst v
      have hp : p.length=n := by simpa [width] using length'
      simpa [quasiShuffle,total,Arithmetic.addZero] using
        terminal_stuffle field marker target p n b hp hb hb' boundary
          (split_last p marker h u _ q vu un eq)
    · have length'' : p.length+v.length=n+1 := by
        have pos := List.length_pos_iff.mpr em
        simpa [width,Nat.max_eq_right (show 1≤v.length by omega)] using length'
      exact selected_stuffle_zero field marker target p v n b length'' hb hb'
        (final_entry v p n vv em length'') (split_last p marker h u _ q vu un eq)
  · apply total_zero_of_members
    intro z _
    apply Classical.byContradiction
    intro nz
    obtain ⟨tail,hit⟩ := selected_hit field marker target (stem++z) n b nz
    exact ext (by obtain ⟨p,ep,_⟩ := positive_prefix field.two_le s h u z tail r m bounded vu un hit
                  exact ⟨p,ep⟩)

/-- The full positive list in the lifted special relation has zero reading
whenever its minimum depth is at least the selected depth. -/
theorem positive_part_zero (field : ConstantField F q) (s h u v target : Tuple)
    (r m n b : Nat) (bounded : ∀ j∈s,j≤q) (vu : Valid u) (un : u≠[]) (vv : Valid v)
    (hb : 0<b) (hb' : b≤q-1) (boundary : b=q-1 → ∃ j,n=j+1 ∧ entries target j=1)
    (le : (endHead s++(List.replicate r 1++[m])).length+(n+1) ≤ h.length+u.length+width v) :
    total (fun x => selected field (endHead s++(List.replicate r 1++[m])) target n b (h++x))
      ((H q u v).flatMap (start q)) = 0 := by
  let marker := endHead s++(List.replicate r 1++[m])
  let stem := h++raiseFirst q (incLast u)
  let f := selected field marker target n b
  change total (fun x => f (h++x)) _ = 0
  change marker.length+(n+1) ≤ h.length+u.length+width v at le
  have marked : (raiseFirst q (incLast u)).length=u.length := by
    cases u with
    | nil => contradiction
    | cons a u =>
      have il := incLast_length a u
      cases e : incLast (a::u) with
      | nil => simp [e] at il
      | cons c t => simpa [raiseFirst,e] using il
  obtain ⟨long,perm,deep⟩ := pos_layer q u v un
  rw [BCPRows.permSum _ perm,total_append',total_map]
  have vanish : total (fun x => f (h++x)) long=0 := by
    apply total_zero_of_members
    intro x hx
    apply selected_long
    have := deep x hx
    simp only [List.length_append]; omega
  rw [vanish,Arithmetic.addZero]
  simp only [←List.append_assoc]
  change total (fun z => f (stem++z)) (shortest (q-1) v)=0
  obtain ⟨more,perm',short,deep'⟩ := shortest_layer (q-1) v
  have sl : stem.length=h.length+u.length := by simp [stem,marked]
  by_cases exactDepth : stem.length+width v=marker.length+(n+1)
  · have allzero := positive_stuffle_zero field s h u v target r m n b bounded vu un vv hb hb' boundary exactDepth
    change total (fun z => f (stem++z)) (quasiShuffle [q-1] v) = 0 at allzero
    rw [BCPRows.permSum _ perm',total_append'] at allzero
    have vanish' : total (fun z => f (stem++z)) more=0 := by
      apply total_zero_of_members
      intro z hz
      apply selected_long
      have := deep' z hz
      simp only [List.length_append]; omega
    rwa [vanish',Arithmetic.addZero] at allzero
  · apply total_zero_of_members
    intro z hz
    apply selected_long
    change marker.length+(n+1)<(stem++z).length
    simp only [List.length_append,short z hz]; omega

end Megaera.Rev4Positive
