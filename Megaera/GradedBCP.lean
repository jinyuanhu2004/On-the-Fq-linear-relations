import Megaera.BCPRows

namespace Megaera.GradedBCP
open Megaera.Finite Megaera.Carlitz Megaera.Paper
variable {F : Type u} [Arithmetic F] [Neg F] {q w : Nat}
local instance : Zero (Tuple → F) := ⟨fun _ => 0⟩
local instance : Add (Tuple → F) := ⟨fun x y s => x s + y s⟩
local instance : Sub (Tuple → F) := ⟨fun x y s => x s + (-y s)⟩

theorem zero_mem : BCPVector (F := F) q w 0 :=
  ⟨[], ⟨[], by simp, fun _ => rfl⟩, rfl⟩

theorem add_mem {v z : Tuple → F} (a : BCPVector q w v) (b : BCPVector q w z) :
    BCPVector q w (fun s => v s + z s) := by
  obtain ⟨p,⟨i,gi,hi⟩,rfl⟩ := a
  obtain ⟨r,⟨j,gj,hj⟩,rfl⟩ := b
  refine ⟨p++r,⟨i++j,fun e he => (List.mem_append.mp he).elim (gi e) (gj e),?_⟩,
    funext (BCPRows.coord_append p r)⟩
  intro s
  rw [BCPRows.coord_append,hi,hj,total_append']

theorem scale_mem (k : F) {v : Tuple → F} (a : BCPVector q w v) :
    BCPVector q w (fun s => k*v s) := by
  obtain ⟨p,⟨i,gi,hi⟩,rfl⟩ := a
  let scaled := p.map (fun z => (k*z.1,z.2))
  have h (s : Tuple) : coordinates scaled s = k*coordinates p s := by
    apply measure_scale
    intro c t
    by_cases ht : t = s <;> simp [ht,Arithmetic.mulZero]
  refine ⟨scaled,⟨i.map (fun z => (k*z.1,z.2)),?_,?_⟩,funext h⟩
  · intro e he; obtain ⟨x,hx,rfl⟩ := List.mem_map.mp he; exact gi x hx
  · intro s
    rw [h,hi]
    clear hi gi h
    induction i with
    | nil => exact Arithmetic.mulZero _
    | cons x i ih => simp only [total,List.map_cons,Arithmetic.distrib,ih,Arithmetic.mulAssoc]

theorem neg_mem (field : ConstantField F q) {v : Tuple → F} (hv : BCPVector q w v) :
    BCPVector q w (fun s => -v s) := by
  simpa only [neg_mul field,oneMul] using scale_mem (-1:F) hv

theorem sub_mem (field : ConstantField F q) {v z : Tuple → F}
    (hv : BCPVector q w v) (hz : BCPVector q w z) :
    BCPVector q w (fun s => v s + (-z s)) := add_mem hv (neg_mem field hz)

theorem sum_mem {A : Type v} (xs : List A) (f : A → Tuple → F)
    (inside : ∀ a ∈ xs, BCPVector q w (f a)) :
    BCPVector q w (fun s => total (fun a => f a s) xs) := by
  induction xs with
  | nil => exact zero_mem
  | cons a xs ih => exact add_mem (inside a (by simp)) (ih (fun z hz => inside z (by simp [hz])))

private theorem generator (q w : Nat) (h t s : Tuple) (hh : Valid h) (ht : Valid t)
    (hs : Valid s) (hn : s ≠ []) (hw : weight h+weight t+weight s+2*q=w) :
    BCPVector q w (coordinates (bcpGenerator (K := F) q h t s)) := by
  refine ⟨_,⟨[(1,h,t,s)],?_,?_⟩,rfl⟩
  · intro z hz; obtain rfl := List.mem_singleton.mp hz; exact ⟨hh,ht,hs,hn,hw⟩
  · intro u; simp [total,oneMul,Arithmetic.addZero]

private def restrictW (w : Nat) (v : Tuple → F) (s : Tuple) : F :=
  if weight s = w then v s else 0

omit [Neg F] in
private theorem restrict_coord (n w : Nat) (p : FormalSum F) (hp : PresentedAt n p) :
    restrictW w (coordinates p) = if n=w then coordinates p else fun _ => 0 := by
  funext s
  have absent (hn : weight s ≠ n) : coordinates p s = 0 := by
    apply total_zero_of_members
    intro z hz
    change (if z.2=s then z.1 else 0) = 0
    exact if_neg (fun e : z.2 = s => hn (e ▸ hp z hz))
  by_cases h : n = w <;> by_cases hs : weight s = w <;>
    simp_all [restrictW] <;> exact absent (Ne.symm h)

theorem generalP_mem (q w : Nat) (field : ConstantField F q) (u s t : Tuple)
    (hu : Valid u) (hs : Valid s) (ht : Valid t) (hn : s ≠ [])
    (hw : weight u + weight s + weight t + 2*q = w) :
    BCPVector q w (coordinates (liftPair (bStar u (generalP (K := F) q s t)))) := by
  let read (p : BinaryPair F) := restrictW w (coordinates (liftPair (bStar u p)))
  have ar : Convolution.AdditiveReading read := by
    constructor
    · intro p r h k; funext v
      simp only [read,restrictW,(BCPRows.prefixed_read (F := F) u v).perm p r h k]
    · funext v
      simp [read,restrictW,(BCPRows.prefixed_read (F := F) u v).empty]
      rfl
    · intro p r; funext v
      change read _ v = read p v + read r v
      unfold read
      simp only [restrictW,(BCPRows.prefixed_read (F := F) u v).append p r]
      split <;> simp [Arithmetic.addZero]
  have g := Convolution.corollary_2_12 q read ar
    (fun f => funext (fun s => zeroAdd (f s)))
    (fun f => funext (fun s => Arithmetic.addZero (f s)))
    (fun f g h => funext (fun s => Arithmetic.addAssoc (f s) (g s) (h s)))
    (fun f g => funext (fun s => show (f s+g s)+(-g s)=f s by
      rw [Arithmetic.addAssoc,field.add_neg,Arithmetic.addZero]))
    (BCPVector q w) zero_mem (fun _ _ => add_mem) (fun _ _ => sub_mem field)
  have hq : 0 < q := by have := field.two_le; omega
  have allgen (a b : Tuple) (ha : Valid a) (hn : a ≠ []) (hb : Valid b) :
      BCPVector q w (read (cOp b (primitive q a))) := by
    change BCPVector q w (restrictW w (coordinates (bcpGenerator (K := F) q u b a)))
    rw [restrict_coord _ w _ (bcpGenerator_weight (K := F) q hq u b a)]
    split
    · exact generator _ _ _ _ _ hu hb ha hn (by assumption)
    · exact zero_mem
  have v := g allgen s t hs hn ht
  have gr := bStar_weight u _ _ (generalP_weight (K := F) q hq s t)
  have pr : PresentedAt w (liftPair (bStar u (generalP (K := F) q s t))) := by
    intro e he
    have h := (List.mem_append.mp he).elim (gr.1 e) (gr.2 e)
    omega
  simpa [read,restrict_coord w w _ pr] using v

end Megaera.GradedBCP
