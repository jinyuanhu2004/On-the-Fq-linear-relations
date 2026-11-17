import Megaera.FourConclusion
import Megaera.FourBoundary
import Megaera.Rev4Negative

/-! Choosing the marked row of §4.3 in a reduced canonical presentation. -/
namespace Megaera.Rev4Selection
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.Splitting
open Megaera.Triangular Megaera.FourReduction Megaera.FourMinimum Megaera.FourLambda
variable {F : Type u} [Arithmetic F] [Neg F] {q w : Nat}

private theorem first_marker (t : Tuple) (vt : Valid t) (hc : ¬ CaseITail t) :
    ∃ r m v b, 1<m ∧ t=List.replicate r 1++m::(v++[b]) := by
  induction t with
  | nil => exact (hc (.inl rfl)).elim
  | cons a t ih =>
    have ha := vt a (by simp)
    have rest : Valid t := fun j hj => vt j (List.mem_cons_of_mem _ hj)
    have tn : t≠[] := by
      rintro rfl; exact hc (.inr ⟨0,a,rfl,ha⟩)
    by_cases unit : a=1
    · subst a
      have bad : ¬ CaseITail t := by
        rintro (e | ⟨r,z,e,pos⟩)
        · exact tn e
        · exact hc (.inr ⟨r+1,z,by simp [List.replicate_succ,e],pos⟩)
      obtain ⟨r,m,v,b,hm,eq⟩ := ih rest bad
      exact ⟨r+1,m,v,b,hm,by rw [List.replicate_succ,eq]; rfl⟩
    · exact ⟨0,a,t.dropLast,t.getLast tn,by omega,
        congrArg (a::·) (List.dropLast_concat_getLast tn).symm⟩

private theorem max_member {A : Type u} (xs : List A) (pred : A→Prop) (score : A→Nat)
    (some : ∃ e∈xs,pred e) :
    ∃ e∈xs,pred e ∧ ∀ f∈xs,pred f → score f≤score e := by
  induction xs with
  | nil => simp at some
  | cons a xs ih =>
    by_cases tail : ∃ f∈xs,pred f
    · obtain ⟨e,mem,pe,best⟩ := ih tail
      by_cases better : pred a ∧ score e < score a
      · refine ⟨a,by simp,better.1,?_⟩
        intro f hf pf; rcases List.mem_cons.mp hf with rfl | hf
        · exact Nat.le_refl _
        · exact Nat.le_trans (best f hf pf) (Nat.le_of_lt better.2)
      · refine ⟨e,by simp [mem],pe,?_⟩
        intro f hf pf; rcases List.mem_cons.mp hf with rfl | hf
        · exact Nat.le_of_not_gt (fun larger => better ⟨pf,larger⟩)
        · exact best f hf pf
    · obtain ⟨e,mem,pe⟩ := some
      rcases List.mem_cons.mp mem with rfl | mem
      · refine ⟨e,by simp,pe,?_⟩
        intro f hf pf; rcases List.mem_cons.mp hf with rfl | hf
        · exact Nat.le_refl _
        · exact (tail ⟨f,hf,pf⟩).elim
      · exact (tail ⟨e,mem,pe⟩).elim

private theorem marker_entry (r m : Nat) (z : Tuple) :
    entries (List.replicate r 1++m::z) r=m := by
  simp [entries,List.getElem?_append]

omit [Arithmetic F] [Neg F] in
/-- A maximal m exists in the prescribed class, with a chosen actual row
of nonzero coefficient whenever all row coefficients are nonzero. -/
theorem choose_marker (e : F × Row q w) (rows : Rows F q w) (bad : ¬ CaseITail e.2.val.2) :
    ∃ r m v b, ∃ f : F × Row q w, f∈e::rows ∧ 1<m ∧ f.2.val.1=e.2.val.1 ∧
      f.2.val.2=List.replicate r 1++m::(v++[b]) ∧ e.2.val.2.length=r+1+(v.length+1) ∧
      ∀ g∈e::rows, g.2.val.1=e.2.val.1 → g.2.val.2.length=e.2.val.2.length →
        ∀ a z, g.2.val.2=List.replicate r 1++a::z → a≤m := by
  obtain ⟨r,m₀,v₀,b₀,large,eform⟩ := first_marker _ e.2.property.2.1 bad
  let pred := fun g : F × Row q w => g.2.val.1=e.2.val.1 ∧ g.2.val.2.length=e.2.val.2.length ∧
      ∃ a z,g.2.val.2=List.replicate r 1++a::z
  let score := fun g : F × Row q w => entries g.2.val.2 r
  have pe : pred e := ⟨rfl,rfl,m₀,_,eform⟩
  obtain ⟨f,mem,⟨left,len,m,z,form⟩,best⟩ := max_member (e::rows) pred score ⟨e,by simp,pe⟩
  have fm : score f=m := by simp [score,form,marker_entry]
  have em : score e=m₀ := by simp [score,eform,marker_entry]
  have old := best e (by simp) pe
  have lens := len
  rw [form,eform] at lens
  have zn : z≠[] := by rintro rfl; simp at lens
  let v := z.dropLast
  let b := z.getLast zn
  have ez : z=v++[b] := (List.dropLast_concat_getLast zn).symm
  refine ⟨r,m,v,b,f,mem,by omega,left,by rw [form,ez],?_,?_⟩
  · rw [←len,form,ez]; simp; omega
  · intro g hg h₁ h₂ a z' eq
    have best' := best g hg ⟨h₁,h₂,a,z',eq⟩
    simpa only [score,eq,marker_entry,form] using best'

omit [Neg F] in
/-- At the smallest depth, every source coefficient equals the coefficient
of its own row even if its source is lexicographically later than the
first one. Any second term in an L-row is one layer deeper. -/
theorem least_depth_coefficient (xs : Rows F q w) (f : F × Row q w) (hf : f∈xs)
    (ord : xs.Pairwise (fun a b => Precedes (rowSource a) (rowSource b)))
    (minD : ∀ g∈xs,(rowSource f).length≤(rowSource g).length) :
    component L xs (rowSource f)=f.1 := by
  have absent (g : F × Row q w) (mem : g∈xs) (diff : rowSource f≠rowSource g) :
      rowSource f ∉ L q g.2.val.1 g.2.val.2 := by
    intro hit
    rcases source_least_depth _ _ _ _ hit with eq | len
    · exact diff eq
    · have depthGe := minD g mem
      change (rowSource f).length=(rowSource g).length+1 at len
      omega
  induction xs with
  | nil => simp at hf
  | cons a xs ih =>
    obtain ⟨head,tail⟩ := List.pairwise_cons.mp ord
    rcases List.mem_cons.mp hf with rfl | mf
    · have rest : component L xs (rowSource f)=0 := by
        apply total_zero_of_members
        intro g hg
        have neq : rowSource f≠rowSource g := fun eq => precedes_irrefl _ (eq ▸ head g hg)
        rw [coord_absent _ _ (absent g (by simp [hg]) neq),Arithmetic.mulZero]
      change f.1*coordinates (withCoeff (1:F) _) (rowSource f)+component L xs _=_
      rw [rest,L_pivot,Arithmetic.mulOne,Arithmetic.addZero]
    · have neq : rowSource f≠rowSource a := fun eq => precedes_irrefl _ (eq ▸ head f mf)
      change a.1*coordinates (withCoeff (1:F) _) _+component L xs _=_
      rw [coord_absent _ _ (absent a (by simp) neq),Arithmetic.mulZero,zeroAdd]
      exact ih mf tail (fun g hg => minD g (by simp [hg])) (fun g hg => absent g (by simp [hg]))

private theorem source_mark (q r m : Nat) (s rest : Tuple) (hm : 1<m) :
    source q s (List.replicate r 1++m::rest) =
      s++(raiseFirst q (incLast (List.replicate r 1++[m-1]))++rest) := by
  rw [FourCases.incLast_concat,show m-1+1=m by omega]
  cases r with
  | zero => rfl
  | succ r => simp [List.replicate_succ,source,raiseFirst,List.append_assoc]

/-- Source illegality at the least depth gives every suffix bound needed
for the initial λ-reading and for terminal positive generators. -/
theorem bounds_of_reduced (field : ConstantField F q) (xs : Rows F q w) (f : F × Row q w)
    (hf : f∈xs) (nz : f.1≠0) (ord : xs.Pairwise (fun a b => Precedes (rowSource a) (rowSource b)))
    (minD : ∀ g∈xs,(rowSource f).length≤(rowSource g).length)
    (red : Reduced F q w (component L xs)) (r m b : Nat) (v : Tuple)
    (hm : 1<m) (form : f.2.val.2=List.replicate r 1++m::(v++[b])) :
    (∀ k∈v,k≤q) ∧ 0<b ∧ b≤q-1 ∧ (b=q-1 → ∃ j,v.length=j+1 ∧ entries (v++[b]) j=1) := by
  let u := List.replicate r 1++[m-1]
  have src : rowSource f=f.2.val.1++(raiseFirst q (incLast u)++(v++[b])) := by
    change source q _ _=_
    rw [form,source_mark q r m _ _ hm]
  have wt : weight (rowSource f)=w := by
    rw [rowSource,source_weight]; have := f.2.property.2.2; omega
  have valid := f.2.property.2.1
  rw [form] at valid
  have hv : Valid v := fun j hj => valid j (by simp [hj])
  have hb : 0<b := valid b (by simp)
  have hu : Valid u := by
    intro k hk
    rcases List.mem_append.mp hk with hk | hk
    · have := List.eq_of_mem_replicate hk; omega
    · obtain rfl := List.mem_singleton.mp hk; omega
  have no : ¬Shape q w (rowSource f) := fun shape => nz
    ((least_depth_coefficient xs f hf ord minD).symm.trans (red _ ((legal_iff_shape field _).mpr shape)))
  rw [src] at no wt
  obtain ⟨cap,last,edge⟩ := FourBoundary.case_II_bounds q field.two_le _ u v b f.2.property.1 hu
    (by simp [u]) hv hb (by rwa [wt])
  refine ⟨cap,hb,last,?_⟩
  intro e
  obtain ⟨p,rfl⟩ := edge e
  exact ⟨p.length,by simp,by simp [entries,List.getElem?_append]⟩

end Megaera.Rev4Selection
