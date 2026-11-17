import Megaera.FinalDecomposition


/-! Existence in (2.10), grouping every block at each positive index.
The index i in Fin N denotes the positive tuple entry i+1. -/
namespace Megaera.FinalBlocks
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.Singletons Megaera.Saturation
variable {F : Type u} [Arithmetic F] [Neg F] {q : Nat}
local instance : Std.Associative (α:=F) (·+·) := ⟨Arithmetic.addAssoc⟩
local instance : Std.Commutative (α:=F) (·+·) := ⟨Arithmetic.addComm⟩

def tail (q : Nat) (b : Tuple→F) : Prop :=
  ∃ p : FormalSum F, PresentedValid p ∧ star (q-1) (coordinates p)=b

omit [Neg F] in
private theorem tzero : tail (F:=F) q (fun _ => 0) := ⟨[],by simp [PresentedValid],star_zero _⟩

omit [Neg F] in
private theorem tadd {a b : Tuple→F} (ha : tail q a) (hb : tail q b) :
    tail q (fun s => a s+b s) := by
  obtain ⟨p,v,rfl⟩ := ha; obtain ⟨r,u,rfl⟩ := hb
  refine ⟨p++r,fun z h => (List.mem_append.mp h).elim (v _) (u _),?_⟩
  rw [funext (BCPRows.coord_append p r),star_add]

private theorem tneg (field : ConstantField F q) {a : Tuple→F} (ha : tail q a) :
    tail q (fun s => -a s) := by
  obtain ⟨p,v,rfl⟩ := ha
  let r := p.map fun z => ((-1:F)*z.1,z.2)
  have eq : coordinates r=(fun s => -(coordinates p s)) := by
    funext s
    have h := measure_scale (-1:F) (fun e => if e.2=s then e.1 else 0)
      (fun k t => by by_cases eq : t=s <;> simp [eq,Arithmetic.mulZero]) p
    change coordinates r s=(-1:F)*coordinates p s at h
    rwa [neg_mul field,oneMul] at h
  refine ⟨r,?_,by rw [eq,star_neg field.add_neg]⟩
  intro z hz; obtain ⟨e,he,rfl⟩ := List.mem_map.mp hz; exact v e he

def block (i : Nat) (b c : Tuple→F) (s : Tuple) : F := root i b s+head (i+1) c s

omit [Neg F] in
private theorem block_zero (i : Nat) (s : Tuple) :
    block i (fun _ => (0:F)) (fun _ => 0) s=0 := by
  simp [block,root,head_zero,Arithmetic.addZero]

omit [Neg F] in
private theorem block_add (i : Nat) (b c b' c' : Tuple→F) (s : Tuple) :
    block i (fun t=> b t+b' t) (fun t=> c t+c' t) s = block i b c s+block i b' c' s := by
  simp only [block,root,head_add]; ac_rfl

private theorem block_neg (field : ConstantField F q) (i : Nat) (b c : Tuple→F) (s : Tuple) :
    block i (fun t => -b t) (fun t => -c t) s= -(block i b c s) := by
  simp only [block,root,head_neg field.add_neg,Singletons.neg_add field.add_neg]

private theorem neg_total (field : ConstantField F q) {A : Type v} (l : List A) (f : A→F) :
    total (fun x => -f x) l = -(total f l) := by
  induction l with
  | nil => exact (nz field.add_neg).symm
  | cons x l ih => rw [total,total,ih,Singletons.neg_add field.add_neg]

omit [Neg F] in
private theorem point (l : List Nat) (i : Nat) (v : F) (nd : l.Nodup) :
    total (fun j => if j=i then v else 0) l = if i∈l then v else 0 := by
  induction l with
  | nil => simp [total]
  | cons b l ih =>
    obtain ⟨h,hn⟩ := List.nodup_cons.mp nd
    by_cases e : b=i
    · subst b; simp [ih hn,h,total,Arithmetic.addZero]
    · simp [total,e,Ne.symm e,ih hn,zeroAdd]

def hasBlocks (q n : Nat) (A : Tuple→F) : Prop :=
  ∃ B C : Nat→Tuple→F, (∀ i,tail q (B i) ∧ HPlus q (C i)) ∧
    ∀ s,A s=total (fun i => block i (B i) (C i) s) (List.range n)

private theorem oneBlock (i n : Nat) (lt : i<n) (b c : Tuple→F) (hb : tail q b) (hc : HPlus q c) :
    hasBlocks q n (block i b c) := by
  let B := fun j : Nat => if j=i then b else fun _ => 0
  let C := fun j : Nat => if j=i then c else fun _ => 0
  refine ⟨B,C,fun j => by by_cases e : j=i <;> simp only [B,C,e,if_true,if_false] <;>
    first | exact ⟨hb,hc⟩ | exact ⟨tzero,.zero⟩,?_⟩
  intro s
  have e (j : Nat) : block j (B j) (C j) s=if j=i then block i b c s else 0 := by
    by_cases e : j=i
    · subst j; simp [B,C]
    · simp [B,C,e,block_zero]
  simp only [e,point (List.range n) i _ List.nodup_range,if_pos (List.mem_range.mpr lt)]

/-- Existence of the first-layer decomposition (2.10). There is a single
pair B_i,C_i for each index i+1 up to N, with B_i in (q−1)*S, C_i in H⁺.
Zero blocks may be inserted to use any larger N. -/
theorem exists_blocks_2_10 (field : ConstantField F q) (A : Tuple→F) (h : HPlus q A) :
    ∃ N,∀ n,N≤n→hasBlocks q n A := by
  induction h with
  | zero =>
    refine ⟨0,fun n _ => ⟨fun _ _ => 0,fun _ _ => 0,fun _ => ⟨tzero,.zero⟩,fun s => ?_⟩⟩
    exact (total_zero_of_members _ _ (fun i _ => block_zero i s)).symm
  | @add p r hp hr a b =>
    obtain ⟨i,hi⟩ := a; obtain ⟨j,hj⟩ := b
    refine ⟨max i j,fun n hn => ?_⟩
    obtain ⟨B,C,member,repr⟩ := hi n (by omega)
    obtain ⟨D,E,member',repr'⟩ := hj n (by omega)
    refine ⟨fun i s => B i s+D i s,fun i s => C i s+E i s,
      fun i => ⟨tadd (member i).1 (member' i).1,.add (member i).2 (member' i).2⟩,?_⟩
    intro s; simp only [block_add,sum_add,repr s,repr' s]
  | @neg p hp h =>
    obtain ⟨i,hi⟩ := h
    refine ⟨i,fun n hn => ?_⟩
    obtain ⟨B,C,mem,e⟩ := hi n hn
    refine ⟨fun i s => -(B i s),fun i s => -(C i s),
      fun i => ⟨tneg field (mem i).1,.neg (mem i).2⟩,?_⟩
    intro s; simp only [block_neg field,neg_total field,e s]
  | @cons a p hp ih =>
    refine ⟨a+1,fun n hn => ?_⟩
    have eq : block a (fun _ => (0:F)) p=head (a+1) p := by
      funext t; simp [block,root,head_zero,zeroAdd]
    exact eq ▸ oneBlock a n (by omega) _ p tzero hp
  | gen a t k hv =>
    let b := coordinates (withCoeff k (quasiShuffle [q-1] t))
    have hb : tail q b := ⟨withCoeff k [t],by simpa [PresentedValid,withCoeff] using hv,
      by rw [star_coeff]; simp [b]⟩
    have eq : block a b (fun _ => (0:F))=root a b := by
      funext s; simp [block,head_zero,Arithmetic.addZero]
    exact ⟨a+1,fun n le => eq ▸ oneBlock a n (by omega) b _ hb .zero⟩

end Megaera.FinalBlocks
