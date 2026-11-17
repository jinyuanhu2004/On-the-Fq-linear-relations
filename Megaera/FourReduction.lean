import Megaera.TTSpanning
import Megaera.GradedBCP

/-! Finite elimination in §4.1 with coordinates of the actual tuple generators. -/
namespace Megaera.FourReduction
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.Triangular
variable {F : Type u} [Arithmetic F] [Neg F] {q w : Nat}

def liftP (q : Nat) (h s t : Tuple) : Tuple → F :=
  coordinates (liftPair (bStar h (generalP (K := F) q s t)))

/-- Types I (empty right argument), II, and III on pp. 21–22.
The increment u⁺¹ in type III requires u to have a last entry. -/
inductive Special (F : Type u) [Arithmetic F] [Neg F] (q w : Nat) : (Tuple → F) → Prop where
  | general (h s t) : Valid h → Valid s → s ≠ [] → Valid t →
      weight h + weight s + weight t + 2*q = w → Special F q w (liftP q h s t)
  | difference (h s u t) : Valid h → Valid s → s ≠ [] → Valid u → u ≠ [] → Valid t →
      weight h + weight s + weight u + weight t + 1 + 2*q = w →
      Special F q w (fun x => liftP q h s (incLast u ++ t) x +
        -liftP q h (incLast s ++ u) t x)

private theorem valid_inc (a : Nat) (s : Tuple) (h : Valid (a::s)) : Valid (incLast (a::s)) :=
  fun _ hi => (endings_valid (a::s) h _ (by simp [endings])) _ hi

theorem special_mem (field : ConstantField F q) {g : Tuple → F} (hg : Special F q w g) :
    BCPVector q w g := by
  cases hg with
  | general h s t hh hs hn ht hw => exact GradedBCP.generalP_mem q w field h s t hh hs ht hn hw
  | difference h s u t hh hs hn hu un ht hw =>
    cases s with
    | nil => contradiction
    | cons a s =>
      cases u with
      | nil => contradiction
      | cons b u =>
        have vs := valid_inc a s hs
        have vu := valid_inc b u hu
        have ws := incLast_weight a s
        have wu := incLast_weight b u
        apply GradedBCP.sub_mem field
        · refine GradedBCP.generalP_mem q w field _ _ _ hh hs ?_ (by simp) ?_
          · intro k hk; exact (List.mem_append.mp hk).elim (vu k) (ht k)
          · rw [weight_append,wu]; omega
        · refine GradedBCP.generalP_mem q w field _ _ _ hh ?_ ht ?_ ?_
          · intro k hk; exact (List.mem_append.mp hk).elim (vs k) (hu k)
          · simp
          · rw [weight_append,ws]; omega

/-- The nonzero coefficient at a minimum is retained explicitly. -/
def Least (v : Tuple → F) (s : Tuple) : Prop :=
  v s ≠ 0 ∧ ∀ t, v t ≠ 0 → t = s ∨ Precedes s t

def Legal (F : Type u) [Arithmetic F] [Neg F] (q w : Nat) (s : Tuple) : Prop :=
  ∃ g, Special F q w g ∧ Least g s

theorem smallest (xs : List Tuple) (p : Tuple → Prop) (h : ∃ s ∈ xs, p s) :
    ∃ s ∈ xs, p s ∧ ∀ t ∈ xs, p t → t = s ∨ Precedes s t := by
  induction xs with
  | nil => simp at h
  | cons a xs ih =>
    by_cases ht : ∃ s ∈ xs, p s
    · obtain ⟨b,hb,pb,first⟩ := ih ht
      by_cases ha : p a ∧ Precedes a b
      · refine ⟨a,by simp,ha.1,?_⟩
        intro t hm pt
        rcases List.mem_cons.mp hm with rfl | hm
        · exact .inl rfl
        · rcases first t hm pt with rfl | lt
          · exact .inr ha.2
          · exact .inr (precedes_trans ha.2 lt)
      · refine ⟨b,by simp [hb],pb,?_⟩
        intro t hm pt
        rcases List.mem_cons.mp hm with rfl | hm
        · rcases precedes_trichotomy t b with h | h | h
          · exact (ha ⟨pt,h⟩).elim
          · exact .inl h
          · exact .inr h
        · exact first t hm pt
    · obtain ⟨s,hm,ps⟩ := h
      rcases List.mem_cons.mp hm with rfl | hm
      · exact ⟨s,by simp,ps,fun t hm pt => (List.mem_cons.mp hm).elim Or.inl
          (fun mem => (ht ⟨t,mem,pt⟩).elim)⟩
      · exact (ht ⟨s,hm,ps⟩).elim

private theorem wt_sum (s : Tuple) : s.sum = weight s := by
  induction s with
  | nil => rfl
  | cons a s ih => simp [weight,ih]

theorem support_at_weight {v : Tuple → F} (hv : RelationVector q w v) {s : Tuple} (nz : v s ≠ 0) :
    s ∈ Dimension.tuples Int.toNat w := by
  obtain ⟨p,⟨hp,_⟩,rfl⟩ := hv
  apply Classical.byContradiction
  intro h
  apply nz
  apply total_zero_of_members
  intro z hz
  apply if_neg
  intro e
  have ok := hp z hz
  exact h ((Dimension.mem_unrestricted ..).mpr ⟨by rw [←e, wt_sum,ok.2], e ▸ ok.1⟩)

def addScaled (v : Tuple → F) (k : F) (g : Tuple → F) := fun t => v t + k * g t

theorem relation_addScaled {v g : Tuple → F} (vrel : RelationVector q w v)
    (grel : RelationVector q w g) (k : F) : RelationVector q w (addScaled v k g) := by
  obtain ⟨p,⟨hp,ep⟩,rfl⟩ := vrel
  obtain ⟨r,⟨hr,er⟩,rfl⟩ := grel
  let rs := r.map (fun z => (k*z.1,z.2))
  refine ⟨p++rs,⟨?_,?_⟩,?_⟩
  · intro e he
    rcases List.mem_append.mp he with ht | ht
    · exact hp e ht
    · obtain ⟨z,hz,rfl⟩ := List.mem_map.mp ht; exact hr z hz
  · intro n
    change total _ (p++rs) = 0
    rw [total_append']
    have eqn : evaluate q rs n = k*evaluate q r n := by
      apply measure_scale; intro c t; exact Arithmetic.mulAssoc .. 
    change evaluate q p n + evaluate q rs n = 0
    rw [eqn,ep,er,Arithmetic.mulZero,Arithmetic.addZero]
  · funext s
    rw [BCPRows.coord_append]
    apply congrArg (_ + ·)
    apply measure_scale
    intro c t; by_cases ht : t=s <;> simp [ht,Arithmetic.mulZero]

/-- Each step subtracts a scalar multiple of one of the three actual generators.
The predicate on the pivot records which minima are permitted during reduction. -/
inductive Reduces (F : Type u) [Arithmetic F] [Neg F] (q w : Nat) (allow : Tuple → Prop) :
    (Tuple → F) → (Tuple → F) → Prop where
  | done (v) : Reduces F q w allow v v
  | step {v r g s k} : Special F q w g → Least g s → allow s → v s ≠ 0 →
      addScaled v k g s = 0 → Reduces F q w allow (addScaled v k g) r →
      Reduces F q w allow v r

def Reduced (F : Type u) [Arithmetic F] [Neg F] (q w : Nat) (v : Tuple → F) : Prop :=
  ∀ s, Legal F q w s → v s = 0

private noncomputable def mask (F : Type u) [Arithmetic F] [Neg F] (q w : Nat) (v : Tuple → F) :=
  fun s => @ite _ (Legal F q w s) (Classical.propDecidable _) (v s) 0

theorem normalize (field : ConstantField F q)
    (sound : ∀ g, Special F q w g → RelationVector q w g)
    (allow : Tuple → Prop) (v : Tuple → F) (hv : RelationVector q w v)
    (above : ∀ t, v t ≠ 0 → allow t)
    (up : ∀ s t, allow s → Precedes s t → allow t) :
    ∃ r, RelationVector q w r ∧ Reduced F q w r ∧
      (∀ t, r t ≠ 0 → allow t) ∧ Reduces F q w allow v r := by
  classical
  by_cases normal : Reduced F q w v
  · exact ⟨v,hv,normal,above,.done _⟩
  have ex : ∃ s ∈ Dimension.tuples Int.toNat w, Legal F q w s ∧ v s ≠ 0 := by
    apply Classical.byContradiction; intro h; apply normal
    intro s hs; exact Classical.byContradiction (fun nz => h ⟨s,support_at_weight hv nz,hs,nz⟩)
  obtain ⟨s,hs,⟨⟨g,hg,first⟩,nz⟩,least⟩ := smallest _ _ ex
  have legal : Legal F q w s := ⟨g,hg,first⟩
  obtain ⟨b,hb⟩ := field.invertible _ first.1
  let k := (-v s)*b
  let v' := addScaled v k g
  have kill : v' s = 0 := by
    simp only [v',addScaled,k,Arithmetic.mulAssoc]
    rw [Arithmetic.mulComm b,hb,Arithmetic.mulOne,field.add_neg]
  have later (t : Tuple) (hl : Legal F q w t) (hn : v' t ≠ 0) : Precedes s t := by
    by_cases he : v t = 0
    · have ng : g t ≠ 0 := by
        intro hz; exact hn (by simp [v',addScaled,he,hz,Arithmetic.mulZero,Arithmetic.addZero])
      exact (first.2 t ng).resolve_left (fun eq => hn (eq ▸ kill))
    · exact (least t (support_at_weight hv he) ⟨hl,he⟩).resolve_left (fun eq => hn (eq ▸ kill))
  have next : ∀ t, v' t ≠ 0 → allow t := by
    intro t hn
    by_cases he : v t = 0
    · have ng : g t ≠ 0 := by
        intro hz; exact hn (by simp [v',addScaled,he,hz,Arithmetic.mulZero,Arithmetic.addZero])
      rcases first.2 t ng with rfl | lt
      · exact above _ nz
      · exact up s t (above _ nz) lt
    · exact above _ he
  have increase : vectorRank w (mask F q w v) < vectorRank w (mask F q w v') := by
    apply vectorRank_strict _ _ _ s hs (by simpa [mask,legal] using nz)
    intro t ht
    by_cases hl : Legal F q w t
    · exact later t hl (by simpa [mask,hl] using ht)
    · simp [mask,hl] at ht
  obtain ⟨r,hr,red,allowed,steps⟩ := normalize field sound allow v'
    (relation_addScaled hv (sound _ hg) k) next up
  exact ⟨r,hr,red,allowed,.step hg first (above _ nz) nz kill steps⟩
termination_by (Dimension.tuples Int.toNat w).length - vectorRank w (mask F q w v)
decreasing_by
  change (Dimension.tuples Int.toNat w).length - vectorRank w (mask F q w v') < _
  have := vectorRank_bound w (mask F q w v')
  omega

end Megaera.FourReduction
