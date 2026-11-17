import Megaera.Rev4Initial
import Megaera.Rev4Rival

namespace Megaera.Rev4Readout
open Megaera.Triangular Megaera.Splitting Megaera.FourMinimum Megaera.FourLambda
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.Rev4Negative
variable {F : Type u} [Arithmetic F] [Neg F] {q w : Nat}

private theorem output_length {q : Nat} (s t z : Tuple) (hz : z ∈ H q s t) :
    (endHead s).length+t.length ≤ z.length := by
  obtain ⟨h,hh,occ⟩ := List.mem_flatMap.mp hz
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp occ
  have tail := singleton_stuffle_depth _ _ _ ha
  have head : (endHead s).length ≤ h.length := by
    cases s with
    | nil => simp [endings] at hh; simp [hh,endHead]
    | cons b s =>
      simp [endings] at hh
      rcases hh with rfl|rfl <;> simp [endHead,incLast_length]
  simp only [List.length_append]
  omega

omit [Neg F] in
private theorem single_source_sum (xs : Rows F q w) (chosen : F × Row q w)
    (ord : xs.Pairwise (fun a b => Precedes (rowSource a) (rowSource b)))
    (mem : chosen∈xs) (f : F × Row q w → F)
    (self : f chosen=chosen.1) (off : ∀ g∈xs, rowSource g ≠ rowSource chosen → f g=0) :
    total f xs = chosen.1 := by
  induction xs with
  | nil => contradiction
  | cons a l ih =>
    obtain ⟨first, later⟩ := List.pairwise_cons.mp ord
    rcases List.mem_cons.mp mem with rfl|hm
    · have zero : total f l=0 := by
        apply total_zero_of_members
        intro g hg
        exact off g (List.mem_cons_of_mem _ hg) (fun eq =>
          precedes_irrefl _ (eq ▸ first g hg))
      rw [total,self,zero,Arithmetic.addZero]
    · rw [total,off a (by simp) (fun eq => precedes_irrefl _ (eq ▸ first chosen hm)),zeroAdd]
      exact ih later hm (fun g hg => off g (List.mem_cons_of_mem _ hg))

/-- Read the complete ordered presentation. The coefficient retrieved is
that of the chosen maximal-marker row, which can occur anywhere in xs. -/
theorem initial_sum (field : ConstantField F q) (e : F × Row q w) (rows : Rows F q w)
    (chosen : F × Row q w) (s t v : Tuple) (c r m b : Nat)
    (ord : (e::rows).Pairwise (fun a b => Precedes (rowSource a) (rowSource b)))
    (left_e : e.2.val.1=s) (right_e : e.2.val.2=c::t)
    (mem : chosen∈e::rows) (left_f : chosen.2.val.1=s)
    (right_f : chosen.2.val.2=List.replicate r 1++m::(v++[b]))
    (len : (c::t).length=r+1+(v.length+1)) (mark : 1<m)
    (hb : 0<b ∧ b≤q-1) (boundary : b=q-1 → 0<v.length)
    (bounded : ∀ g∈e::rows, ∀ a∈g.2.val.1,a≤q)
    (maximal : ∀ g∈e::rows, g.2.val.1=s → g.2.val.2.length=(c::t).length →
      ∀ a z, g.2.val.2=List.replicate r 1++a::z → a≤m)
    (bounds : ∀ g∈e::rows, g.2.val.1=s → g.2.val.2.length=(c::t).length →
      ∀ u a, g.2.val.2=List.replicate r 1++m::(u++[a]) → (∀ k∈u,k≤q) ∧ a≤q-1) :
    total (fun g : F × Row q w => g.1 *
      total (selected field (endHead s ++ (List.replicate r 1 ++ [m+(q-1)]))
        (v++[b]) v.length b) (H q g.2.val.1 g.2.val.2)) (e::rows) = chosen.1 := by
  classical
  let stem := endHead s ++ (List.replicate r 1 ++ [m+(q-1)])
  let read := selected field stem (v++[b]) v.length b
  have base : rowSource e=source q s (c::t) := by simp [rowSource,left_e,right_e]
  have earlier (g : F × Row q w) (hg : g∈e::rows) :
      g=e ∨ Precedes (source q s (c::t)) (rowSource g) := by
    rcases List.mem_cons.mp hg with eq|hg
    · exact .inl eq
    · exact .inr (base ▸ (List.pairwise_cons.mp ord).1 g hg)
  have value (g : F × Row q w) (hg : g∈e::rows) :
      total read (H q g.2.val.1 g.2.val.2) =
        if g.2.val.1=s ∧ g.2.val.2=chosen.2.val.2 then 1 else 0 := by
    by_cases same : g.2.val.1=s
    · simp only [and_iff_right same]
      have minimum : (c::t).length ≤ max 1 g.2.val.2.length := by
        have depth_le : (source q s (c::t)).length ≤ (rowSource g).length := by
          rcases earlier g hg with rfl|lt
          · exact Nat.le_of_eq (congrArg List.length base).symm
          · rcases lt with h|⟨h,_⟩ <;> simp only [depth] at h <;> omega
        simpa [rowSource,same,FourCases.source_depth] using depth_le
      by_cases equal : g.2.val.2.length=(c::t).length
      · rw [right_f]
        simpa only [same,read,stem] using Rev4Initial.same_prefix_delta field s g.2.val.2
          v r m b hb (equal.trans len) g.2.property.2.1 (maximal g hg same equal)
          (bounds g hg same equal)
      · have big : (c::t).length<g.2.val.2.length := by omega
        have ne : g.2.val.2 ≠ chosen.2.val.2 := by
          intro eq
          have h := congrArg List.length (eq.trans right_f)
          simp at h
          omega
        rw [if_neg ne]
        apply total_zero_of_members
        intro z hz
        have h := output_length _ _ z hz
        rw [same] at h
        apply selected_long
        simp only [stem,List.length_append,List.length_replicate,List.length_cons,List.length_nil]
        omega
    · rw [if_neg (fun h => same h.1)]
      have before := (earlier g hg).resolve_left (fun eq => same (eq ▸ left_e))
      simpa only [read,stem,List.append_assoc] using Rev4Rival.rival_reading_zero field
        s t g.2.val.1 g.2.val.2 (v++[b]) c r (m+(q-1)) v.length b
        g.2.property.1 g.2.property.2.1 (bounded g hg) same before
        (by have := field.two_le; omega) len hb.1 hb.2 boundary
  change total (fun g : F × Row q w => g.1 * total read (H q g.2.val.1 g.2.val.2))
    (e::rows) = _
  apply single_source_sum _ _ ord mem
  · rw [value chosen mem,if_pos ⟨left_f,rfl⟩,Arithmetic.mulOne]
  · intro g hg different
    have off : ¬(g.2.val.1=s ∧ g.2.val.2=chosen.2.val.2) := by
      rintro ⟨l,h⟩
      exact different (by simp only [rowSource,l,h,left_f])
    simp [value g hg,off,Arithmetic.mulZero]

end Megaera.Rev4Readout
