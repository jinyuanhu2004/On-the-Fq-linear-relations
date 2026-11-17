import Megaera.FinalRankEngine
namespace Megaera.FinalCosetRanks
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.SectionThreeSpaces
open Megaera.FinalRankEngine
variable {F : Type u} [Arithmetic F] [Neg F] {I : Type v} {J : Type z} {Z : Type w} {q : Nat}

private theorem dedup {A : Type w} (l : List A) :
    ∃ t : List A, t.Nodup ∧ ∀ a,a∈t ↔ a∈l := by
  classical
  induction l with
  | nil => exact ⟨[],by simp,fun _ => Iff.rfl⟩
  | cons a l ih =>
    obtain ⟨t,nt,ht⟩ := ih
    by_cases e : a∈t
    · refine ⟨t,nt,fun x => ?_⟩
      by_cases eq : x=a
      · subst x; simp [e]
      · simpa [eq] using ht x
    · exact ⟨a::t,List.nodup_cons.mpr ⟨e,nt⟩,fun x => by simp [ht x]⟩

/-- Every fiber of a defect profile is a translate of its kernel. -/
private theorem fiber_count (field : ConstantField F q) {S K : (I→F)→Prop}
    (lin : Linear S) (inc : ∀ x,K x→S x) (p : (I→F)→Z)
    (detect : ∀ a b,S a→S b→(p a=p b ↔ K (fun i => a i+ -b i)))
    (xs ks : List (I→F)) (nx : xs.Nodup) (nk : ks.Nodup)
    (ax : ∀ x,x∈xs ↔ S x) (ak : ∀ k,k∈ks ↔ K k) (z : Z) (hz : ∃ x,S x ∧ p x=z)
    [DecidableEq Z] : (xs.filter (fun x => decide (p x=z))).length=ks.length := by
  classical
  obtain ⟨b,hb,rfl⟩ := hz
  let add (k : I→F) := fun i => k i+b i
  let sub (x : I→F) := fun i => x i+ -b i
  have undo (k : I→F) : sub (add k)=k := by funext i; simp [sub,add,Arithmetic.addAssoc,field.add_neg,Arithmetic.addZero]
  have restore (x : I→F) : add (sub x)=x := by
    funext i
    simp only [sub,add,Arithmetic.addAssoc,Arithmetic.addComm (-b i),field.add_neg,Arithmetic.addZero]
  have ce : (xs.filter (fun x => decide (p x=p b))).length=(ks.map add).length := by
    apply same_length _ _ (List.Pairwise.filter _ nx) (List.pairwise_map.mpr
      (nk.imp (fun ne eq => ne ((undo _).symm.trans ((congrArg sub eq).trans (undo _))))))
    intro x
    rw [List.mem_filter]
    constructor
    · rintro ⟨hx,heq⟩
      exact List.mem_map.mpr ⟨sub x,(ak _).mpr ((detect x b ((ax x).mp hx) hb).mp (of_decide_eq_true heq)),restore x⟩
    · intro hx
      obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hx
      have a : S (add k) := by
        simpa only [add,oneMul] using lin.addScaled _ _ 1 (inc _ ((ak _).mp hk)) hb
      have inside : K (sub (add k)) := (undo k).symm ▸ ((ak k).mp hk)
      exact ⟨(ax _).mpr a,decide_eq_true ((detect _ _ a hb).mpr inside)⟩
  simpa using ce

private theorem partition_count {A : Type v} {B : Type w} [DecidableEq B]
    (xs : List A) (nd : xs.Nodup) (p : A→B) (zs : List B) (nz : zs.Nodup)
    (cover : ∀ x∈xs,p x∈zs) (k : Nat) (sizes : ∀ z∈zs,(xs.filter (fun x => decide (p x=z))).length=k) :
    xs.length=zs.length*k := by
  let fib (z : B) := xs.filter (fun x => decide (p x=z))
  have flat : (zs.flatMap fib).Nodup := by
    apply List.pairwise_flatMap.mpr
    constructor
    · intro z _; exact List.Pairwise.filter _ nd
    · apply nz.imp
      intro a b ne x hx y hy eq
      subst y
      exact ne ((of_decide_eq_true (List.mem_filter.mp hx).2).symm.trans (of_decide_eq_true (List.mem_filter.mp hy).2))
  have eq := same_length _ _ nd flat (fun x => by
    constructor
    · intro h; exact List.mem_flatMap.mpr ⟨p x,cover x h,List.mem_filter.mpr ⟨h,by simp⟩⟩
    · intro h; obtain ⟨_,_,hm⟩ := List.mem_flatMap.mp h; exact (List.mem_filter.mp hm).1)
  rw [eq]; clear flat eq cover nz
  induction zs with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.succ_mul]
    rw [ih (fun z hz => sizes z (by simp [hz])),show (fib a).length=k from sizes a (by simp),Nat.add_comm]

/-- Equal profile images and translation-invariant fibers give equality
of the two differences of dimensions, without a basis in the codomain. -/
theorem coset_ranks (field : ConstantField F q) {S K : (I→F)→Prop} {U V : (J→F)→Prop}
    (ls : Linear S) (lk : Linear K) (lu : Linear U) (lv : Linear V)
    (ks : ∀ x,K x→S x) (vu : ∀ x,V x→U x)
    (p : {x // S x}→Z) (v : {y // U y}→Z)
    (pk : ∀ a b,p a=p b ↔ K (fun i => a.val i+ -b.val i))
    (vk : ∀ a b,v a=v b ↔ V (fun i => a.val i+ -b.val i))
    (same : ∀ z,(∃ a,p a=z) ↔ ∃ b,v b=z)
    {s k u h : Nat} (bs : HasDimension S s) (bk : HasDimension K k)
    (bu : HasDimension U u) (bv : HasDimension V h) : s+h=u+k := by
  classical
  let pf (x : I→F) := if hx : S x then p ⟨x,hx⟩ else p ⟨_,ls.zero⟩
  let vf (x : J→F) := if hx : U x then v ⟨x,hx⟩ else v ⟨_,lu.zero⟩
  obtain ⟨xs,sx,nx,ax⟩ := count_space field ls bs
  obtain ⟨ss,sk,nk,ak⟩ := count_space field lk bk
  obtain ⟨ys,sy,ny,ay⟩ := count_space field lu bu
  obtain ⟨tt,sh,nt,at'⟩ := count_space field lv bv
  obtain ⟨zs,nz,az⟩ := dedup (xs.map pf)
  have ps (z) : z∈zs ↔ ∃ a,p a=z := by
    rw [az,List.mem_map]
    exact ⟨fun ⟨x,h,e⟩ => ⟨⟨x,(ax x).mp h⟩,by simpa [pf,(ax x).mp h] using e⟩,
      fun ⟨x,e⟩ => ⟨x.val,(ax _).mpr x.property,by simpa [pf,x.property] using e⟩⟩
  have a := partition_count xs nx pf zs nz (fun x hx =>
    (ps _).mpr ⟨⟨x,(ax x).mp hx⟩,by simp [pf,(ax x).mp hx]⟩) ss.length (by
      intro z hz
      obtain ⟨x,e⟩ := (ps _).mp hz
      apply fiber_count field ls ks pf _ xs ss nx nk ax ak z ⟨x.val,x.property,by simpa [pf,x.property] using e⟩
      intro a b ha hb; simpa [pf,ha,hb] using pk ⟨a,ha⟩ ⟨b,hb⟩)
  have b := partition_count ys ny vf zs nz (fun y hy =>
    (ps _).mpr ((same _).mpr ⟨⟨y,(ay y).mp hy⟩,by simp [vf,(ay y).mp hy]⟩)) tt.length (by
      intro z hz
      obtain ⟨y,e⟩ := (same _).mp ((ps _).mp hz)
      apply fiber_count field lu vu vf _ ys tt ny nt ay at' z ⟨y.val,y.property,by simpa [vf,y.property] using e⟩
      intro a b ha hb; simpa [vf,ha,hb] using vk ⟨a,ha⟩ ⟨b,hb⟩)
  rw [sx,sk] at a
  rw [sy,sh] at b
  have eq : q^(s+h)=q^(u+k) := by rw [Nat.pow_add,Nat.pow_add,a,b]; ac_rfl
  have gt {i j : Nat} (lt : i<j) : q^i<q^j := by
    have hq := field.two_le
    have pos := Nat.pow_pos (by omega : q>0) (n:=i)
    have e := Nat.mul_le_mul_left (q^i) hq
    have ub := Nat.pow_le_pow_right (by omega : q>0) lt
    rw [Nat.pow_succ] at ub; omega
  by_cases lt : s+h<u+k
  · have := gt lt; omega
  · by_cases le : u+k<s+h
    · have := gt le; omega
    · omega

end Megaera.FinalCosetRanks
