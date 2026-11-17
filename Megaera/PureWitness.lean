import Megaera.PureReplacement
import Megaera.Singletons

namespace Megaera.PureWitness
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.Singletons Megaera.BCPRows
variable {F : Type u} [Arithmetic F] [Neg F]

private def project (w : Nat) (v : Tuple → F) (s : Tuple) : F :=
  if weight s = w then v s else 0

/-- Extract the homogeneous positive-prefix preimage supplied by (2.9). -/
theorem witness_at (q w : Nat) (field : ConstantField F q) (v : Tuple → F)
    (hv : HPlus q v) :
    ∃ c : Rows F q w, (∀ e ∈ c, e.2.val.1 ≠ []) ∧ component H c = project w v := by
  have h := (rowSpan_iff field.add_neg q v).mpr hv
  clear hv
  induction h with
  | zero => exact ⟨[],by simp,funext (fun s => by simp [project,component,total])⟩
  | add a b ia ib =>
    obtain ⟨c,cp,hc⟩ := ia; obtain ⟨d,dp,hd⟩ := ib
    refine ⟨c++d,fun e he => (List.mem_append.mp he).elim (cp e) (dp e),?_⟩
    funext s; rw [rows_append]; simp only [hc,hd,project]
    split <;> simp [Arithmetic.addZero]
  | neg a ia =>
    obtain ⟨c,cp,hc⟩ := ia
    refine ⟨negRows c,?_,?_⟩
    · intro e he; obtain ⟨z,hz,rfl⟩ := List.mem_map.mp he; exact cp z hz
    · funext s
      rw [component_neg field,hc]
      simp only [project]; split <;> simp [Singletons.nz field.add_neg]
  | row b h t k hh ht =>
    have hq : 0 < q := by have := field.two_le; omega
    by_cases heq : weight (b::h) + weight t + q = w
    · let r : Row q w := ⟨(b::h,t),hh,ht,heq⟩
      refine ⟨[(k,r)],?_,?_⟩
      · intro e he; obtain rfl := List.mem_singleton.mp he; simp [r]
      · funext s
        change k*coordinates (withCoeff 1 (H q (b::h) t)) s + 0 = _
        rw [Arithmetic.addZero,←coeff_scale]
        by_cases hw : weight s=w
        · simp [project,hw]
        · simp only [project,if_neg hw]; apply total_zero_of_members
          intro e hem; obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hem
          have h := H_weight q hq (b::h) t x hx
          change (if x=s then k else 0)=0
          exact if_neg (fun eq => hw (by subst x; omega))
    · refine ⟨[],by simp,?_⟩
      funext s
      change 0 = project w _ s
      by_cases hw : weight s=w
      · rw [project,if_pos hw]; symm; apply total_zero_of_members
        intro e hem; obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hem
        have h := H_weight q hq (b::h) t x hx
        change (if x=s then k else 0)=0
        exact if_neg (fun eq => heq (by subst x; omega))
      · simp [project,hw]

theorem witness (q w : Nat) (field : ConstantField F q) (p : FormalSum F)
    (hp : PresentedAt w p) (hv : HPlus q (coordinates p)) :
    ∃ c : Rows F q w, (∀ e ∈ c, e.2.val.1 ≠ []) ∧ component H c = coordinates p := by
  obtain ⟨c,cp,hc⟩ := witness_at q w field _ hv
  refine ⟨c,cp,?_⟩; funext s
  rw [hc]
  by_cases hw : weight s=w
  · simp [project,hw]
  · rw [project,if_neg hw]; symm
    apply total_zero_of_members
    intro z hz
    change (if z.2=s then z.1 else 0) = 0
    exact if_neg (fun e : z.2=s => hw (e ▸ hp z hz))

/-- Eliminate a whole block with the same left tuple. -/
theorem replace_block {q w : Nat} (field : ConstantField F q) (u : Tuple)
    (b : Rows F q w) (pureRows : ∀ e ∈ b, e.2.val.1=u)
    (inside : HPlus q (coordinates (b.map (fun e => (e.1,e.2.val.2))))) :
    ∃ d : Rows F q w, (∀ e ∈ d, u.length < e.2.val.1.length) ∧ component H d = component H b ∧
      BCPVector q w (fun x => component L b x + (-component L d x)) := by
  cases b with
  | nil =>
    exact ⟨[],by simp,rfl,by simpa only [show (fun x => component L ([] : Rows F q w) x +
      (-component L ([] : Rows F q w) x)) = (fun _ => (0:F)) by funext x; exact field.add_neg 0]
      using (GradedBCP.zero_mem (F := F) (q := q) (w := w))⟩
  | cons z zs =>
    have zu := pureRows z (by simp)
    have hwt := z.2.property.2.2
    rw [zu] at hwt
    let n := w-weight u-q
    have hw : weight u+n+q=w := by dsimp [n]; omega
    have pt : PresentedAt n ((z::zs).map (fun e => (e.1,e.2.val.2))) := by
      intro e he
      obtain ⟨y,hy,rfl⟩ := List.mem_map.mp he
      have h := y.2.property.2.2
      rw [pureRows y hy] at h
      change weight y.2.val.2=n; omega
    obtain ⟨c,cp,hc⟩ := witness q n field _ pt inside
    exact PureReplacement.replace_pure field u (zu ▸ z.2.property.1) hw _ pureRows c cp hc

end Megaera.PureWitness
