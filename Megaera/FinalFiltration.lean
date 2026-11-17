import Megaera.FinalFirstEntry
import Megaera.FinalDegreeOne

/-! The first-entry filtration uses a lower bound on the support, including
the zero vector in each stage. The projection deletes the entry n. -/
namespace Megaera.FinalFiltration
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.Lift Megaera.SectionThreeSpaces
open Megaera.FinalFirstEntry
variable {F : Type u} [Arithmetic F] [Neg F] {q w : Nat}

def stageR (q w n : Nat) (x : Tuple → F) : Prop :=
  fixedR q w x ∧ ∀ s, s.headD 0<n → x s=0

def stageU (q w n : Nat) (x : Bool × Tuple → F) : Prop :=
  fixedU q w x ∧ ∀ b s, s.headD 0<n → x (b,s)=0

def keep (n : Nat) (p : FormalSum F) := p.filter fun e => decide (n≤e.2.headD 0)

omit [Neg F] in
theorem keep_coords (n : Nat) (p : FormalSum F) (s : Tuple) :
    coordinates (keep n p) s = if n≤s.headD 0 then coordinates p s else 0 := by
  induction p with
  | nil => simp [keep,coordinates,total]
  | cons e p ih =>
    have rec : keep n (e::p) = if n≤e.2.headD 0 then e::keep n p else keep n p := by
      simp only [keep,List.filter_cons,decide_eq_true_eq]
    rw [rec]
    have step (r : FormalSum F) : coordinates (e::r) s=(if e.2=s then e.1 else 0)+coordinates r s := rfl
    by_cases hm : n≤e.2.headD 0 <;> by_cases hs : e.2=s <;> by_cases hn : n≤s.headD 0
    all_goals first | exact False.elim (by subst s; contradiction) | skip
    all_goals simp only [hm,hn,hs,if_true,if_false,step,ih,zeroAdd,Arithmetic.addZero]

omit [Arithmetic F] [Neg F] in
theorem keep_starts (n : Nat) (hn : 0<n) (p : FormalSum F) : startsAt n (keep n p) := by
  intro e he
  have le : n≤e.2.headD 0 := of_decide_eq_true (List.mem_filter.mp he).2
  cases eq : e.2 with
  | nil => simp [eq] at le; omega
  | cons a t => exact ⟨a,t,rfl,by simpa [eq] using le⟩

omit [Neg F] in
theorem tails_coords (n : Nat) (p : FormalSum F) (s : Tuple) :
    coordinates (tails n p) s=coordinates p (n::s) := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    obtain ⟨k, t⟩ := e
    cases t with
    | nil => simpa [tails,coordinates,total,zeroAdd] using ih
    | cons a t =>
      by_cases h : a=n
      · subst a
        simpa [tails,coordinates,total] using congrArg ((if t=s then k else 0)+·) ih
      · simpa [tails,h,coordinates,total,zeroAdd] using ih

omit [Neg F] in
private theorem keep_same (n : Nat) (p : FormalSum F) (h : ∀ s, s.headD 0<n → coordinates p s=0) :
    coordinates (keep n p)=coordinates p := by
  funext s; rw [keep_coords]; split
  · rfl
  · rename_i hn; exact (h s (by omega)).symm

omit [Neg F] in
private theorem same_level (f : Tuple → Series F) (p r : FormalSum F) (eq : coordinates p=coordinates r) :
    valueAt f p=valueAt f r := funext (fun i => linear_form_congr (fun s => f s i) p r eq)

omit [Arithmetic F] [Neg F] in
private theorem keep_hom (p : FormalSum F) (hp : homogeneous w p) (n : Nat) :
    homogeneous w (keep n p) := fun e he => hp e (List.mem_filter.mp he).1

theorem restrict_R (field : ConstantField F q) {n : Nat} (hn : 0<n) (lt : n<w)
    (x : Tuple → F) (stage : stageR q w n x) : RelationVector q (w-n) (fun t => x (n::t)) := by
  obtain ⟨⟨p,⟨hom,_⟩,fixed,rfl⟩,small⟩ := stage
  have same := keep_same n p small
  refine ⟨tails n (keep n p),least_tail_R field lt _ (keep_hom p hom n)
    (keep_starts n hn p) (fun d j => ?_),?_⟩
  · exact (congrFun (same_level _ _ _ same) j).trans (fixed d j)
  · funext s; rw [tails_coords,same]

theorem restrict_U (field : ConstantField F q) {n : Nat} (hn : 0<n) (lt : n<w)
    (x : Bool × Tuple → F) (stage : stageU q w n x) :
    U q (w-n) (fun ⟨b,t⟩ => x (b,n::t)) := by
  obtain ⟨⟨p,r,hp,hr,_,fixed,rfl⟩,small⟩ := stage
  have ep := keep_same n p (small false)
  have er := keep_same n r (small true)
  have h := least_tail_U field lt _ _ (keep_hom p hp n) (keep_hom r hr n)
    (keep_starts n hn p) (keep_starts n hn r) (fun d => by
      rw [same_level _ _ _ ep,same_level _ _ _ er]; exact fixed d)
  have eq : pairCoordinates (tails n (keep n p)) (tails n (keep n r)) =
      (fun i : Bool × Tuple => pairCoordinates p r (i.1,n::i.2)) := by
    funext ⟨b,s⟩; cases b <;> simp [pairCoordinates,tails_coords,ep,er]
  exact eq ▸ h

theorem kernel_R (n : Nat) (x : Tuple → F) (hn : 0<n) :
    stageR q w (n+1) x ↔ stageR q w n x ∧ ∀ t,x (n::t)=0 := by
  constructor
  · rintro ⟨h,b⟩; exact ⟨⟨h,fun s le => b s (by omega)⟩,fun t => b (n::t) (by simp)⟩
  · rintro ⟨⟨h,b⟩,z⟩; refine ⟨h,fun s le => ?_⟩
    by_cases lt : s.headD 0<n
    · exact b s lt
    · cases s with
      | nil => simp at lt; omega
      | cons a t =>
        simp at le lt
        have eq : a=n := by omega
        subst a; exact z t

theorem kernel_U (n : Nat) (x : Bool × Tuple → F) (hn : 0<n) :
    stageU q w (n+1) x ↔ stageU q w n x ∧ ∀ i : Bool × Tuple,x (i.1,n::i.2)=0 := by
  constructor
  · rintro ⟨h,b⟩; exact ⟨⟨h,fun j s le => b j s (by omega)⟩,
      fun ⟨j,t⟩ => b j (n::t) (by simp)⟩
  · rintro ⟨⟨h,b⟩,z⟩; refine ⟨h,fun j s le => ?_⟩
    by_cases lt : s.headD 0<n
    · exact b j s lt
    · cases s with
      | nil => simp at lt; omega
      | cons a t =>
        simp at le lt
        have eq : a=n := by omega
        subst a; exact z (j,t)

end Megaera.FinalFiltration
