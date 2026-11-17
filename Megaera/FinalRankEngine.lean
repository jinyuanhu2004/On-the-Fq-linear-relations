import Megaera.FinalBasisRanks

/-! Finite-coordinate linear algebra for the concrete section-three spaces. -/
namespace Megaera.FinalRankEngine
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.SectionThreeSpaces
variable {F : Type u} [Arithmetic F] [Neg F] {q : Nat} {I : Type v} {J : Type z}

structure Linear (space : (I → F) → Prop) : Prop where
  zero : space (fun _ => 0)
  addScaled : ∀ x y a, space x → space y → space (fun i => x i+a*y i)

private theorem fin_range_split (l r : Nat) : List.finRange (l+r) =
    (List.finRange l).map (Fin.castAdd r) ++ (List.finRange r).map (Fin.natAdd l) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    apply Fin.ext
    have sz : ((List.finRange l).map (Fin.castAdd r)).length=l := by simp
    rw [List.getElem_append]
    split <;> simp [List.getElem_map,sz] <;> omega

private def synthesis {I : Type v} {n : Nat} (basis : Fin n → I → F) (c : Fin n → F) (s : I) :=
  total (fun j => c j*basis j s) (List.finRange n)

private def joinFin {A : Type v} {l r : Nat} (a : Fin l → A) (b : Fin r → A) :
    Fin (l+r) → A := Fin.addCases (motive:=fun _ => A) a b

@[simp] private theorem join_left {A : Type v} {l r : Nat} (a : Fin l → A) (b : Fin r → A)
    (i : Fin l) : joinFin a b (Fin.castAdd r i)=a i := Fin.addCases_left i

@[simp] private theorem join_right {A : Type v} {l r : Nat} (a : Fin l → A) (b : Fin r → A)
    (i : Fin r) : joinFin a b (Fin.natAdd l i)=b i := Fin.addCases_right i

omit [Neg F] in
private theorem synth_split {I : Type v} {l r : Nat} (a : Fin l → I → F) (b : Fin r → I → F)
    (c : Fin (l+r) → F) (s : I) :
    synthesis (joinFin a b) c s =
      synthesis a (fun j => c (Fin.castAdd r j)) s + synthesis b (fun j => c (Fin.natAdd l j)) s := by
  unfold synthesis
  rw [fin_range_split,total_append',total_map,total_map]
  simp only [join_left,join_right]

omit [Neg F] in
private theorem member_syn {S : (I→F)→Prop} (hl : Linear S) {n : Nat} (b : Fin n→I→F)
    (c : Fin n→F) (hb : ∀ j,S (b j)) : S (synthesis b c) := by
  unfold synthesis; generalize List.finRange n = is
  induction is with
  | nil => exact hl.zero
  | cons j is ih => simpa only [Arithmetic.addComm] using hl.addScaled _ _ (c j) ih (hb j)

/-- Rank additivity for a restriction to a family of coordinates. -/
theorem split_basis (field : ConstantField F q) {top : (I→F)→Prop} (topLin : Linear top)
    (proj : J→I) (image : (J→F)→Prop) (kernel : (I→F)→Prop)
    (image_iff : ∀ y,image y ↔ ∃ x,top x ∧ ∀ j,x (proj j)=y j)
    (kernel_iff : ∀ x,kernel x ↔ top x ∧ ∀ j,x (proj j)=0)
    {l r : Nat} (ld : HasDimension image l) (rd : HasDimension kernel r) :
    HasDimension top (l+r) := by
  classical
  obtain ⟨lb,lb_mem,lb_basis⟩ := ld
  obtain ⟨rb,rb_mem,rb_basis⟩ := rd
  have lifts (j) := (image_iff _).mp (lb_mem j)
  let ext := fun j => Classical.choose (lifts j)
  have ext_mem (j) : top (ext j) := (Classical.choose_spec (lifts j)).1
  have ep (j) (s) : ext j (proj s)=lb j s := (Classical.choose_spec (lifts j)).2 s
  have rp (j) (s) : rb j (proj s)=0 := ((kernel_iff _).mp (rb_mem j)).2 s
  have ex (a : Fin l→F) (s) : synthesis ext a (proj s)=synthesis lb a s := by simp only [synthesis,ep]
  have ez (a : Fin r→F) (s) : synthesis rb a (proj s)=0 :=
    total_zero_of_members _ _ (fun i _ => by rw [rp,Arithmetic.mulZero])
  have read_l (a : Fin (l+r)→F) (s) :
      synthesis (joinFin ext rb) a (proj s)=synthesis lb (fun j => a (Fin.castAdd r j)) s := by
    rw [synth_split,ex,ez,Arithmetic.addZero]
  refine ⟨joinFin ext rb,?_,?_⟩
  · intro i; induction i using Fin.addCases with
    | left j => simpa using ext_mem j
    | right j => simpa using ((kernel_iff _).mp (rb_mem j)).1
  · intro x hx
    obtain ⟨a,ea,ua⟩ := lb_basis _ ((image_iff _).mpr ⟨x,hx,fun _ => rfl⟩)
    let y := synthesis ext a
    let k := fun i => x i+ -(y i)
    have hy := member_syn topLin ext a ext_mem
    have hk : kernel k := (kernel_iff _).mpr ⟨by
      simpa only [k,y,neg_mul field,oneMul] using topLin.addScaled _ _ (-1) hx hy,by
      intro s; change x (proj s)+ -synthesis ext a (proj s)=0
      rw [ex,ea]; exact field.add_neg _⟩
    obtain ⟨b,eb,ub⟩ := rb_basis _ hk
    refine ⟨joinFin a b,?_,?_⟩
    · intro s; change x s=synthesis (joinFin ext rb) _ s
      rw [synth_split]; simp only [join_left,join_right]
      rw [←show k s=synthesis rb b s from eb s]
      change x s=y s+(x s+ -y s)
      rw [Arithmetic.addComm (x s),←Arithmetic.addAssoc,field.add_neg,zeroAdd]
    · intro d ed
      have dl : (fun j => d (Fin.castAdd r j))=a := ua _ (fun s => (ed (proj s)).trans (read_l d s))
      have dr : (fun j => d (Fin.natAdd l j))=b := by
        apply ub; intro s
        have e := (ed s).trans (synth_split ext rb d s)
        rw [dl] at e
        change x s+ -y s=_
        rw [e,Arithmetic.addComm (y s),Arithmetic.addAssoc,field.add_neg,Arithmetic.addZero]
        rfl
      funext i
      induction i using Fin.addCases with
      | left j => exact (congrFun dl j).trans (join_left a b j).symm
      | right j => exact (congrFun dr j).trans (join_right a b j).symm

private theorem vectors (field : ConstantField F q) (n : Nat) :
    ∃ ks : List (Fin n→F), ks.length=q^n ∧ ks.Nodup ∧ ∀ k,k∈ks := by
  obtain ⟨f,inj,surj⟩ := field.cardinality
  induction n with
  | zero =>
    refine ⟨[Fin.elim0],by simp,by simp,fun k => List.mem_singleton.mpr (funext (fun i => i.elim0))⟩
  | succ n ih =>
    obtain ⟨ts,sz,nd,all⟩ := ih
    let xs := List.ofFn f
    have nx : xs.Nodup := by
      apply List.pairwise_iff_getElem.mpr
      intro i j hi hj lt eq
      simp only [xs,List.getElem_ofFn] at eq
      have h : i=j := congrArg Fin.val (inj _ _ eq)
      omega
    let extend (a : F) (b : Fin n→F) : Fin (n+1)→F := Fin.cases a b
    let ks := xs.flatMap (fun a => ts.map (extend a))
    refine ⟨ks,?_,?_,?_⟩
    · have len (l : List F) : (l.flatMap (fun a => ts.map (extend a))).length=l.length*ts.length := by
        induction l with
        | nil => simp
        | cons a l ih => simp [ih,Nat.succ_mul,Nat.add_comm]
      simp [ks,len,xs,sz,Nat.pow_succ,Nat.mul_comm]
    · apply List.pairwise_flatMap.mpr
      constructor
      · intro a _
        apply List.pairwise_map.mpr
        apply nd.imp
        intro x y ne eq; apply ne; funext i
        exact congrFun eq i.succ
      · apply nx.imp
        intro a b ne x hx y hy eq
        obtain ⟨s,_,rfl⟩ := List.mem_map.mp hx
        obtain ⟨t,_,rfl⟩ := List.mem_map.mp hy
        exact ne (congrFun eq 0)
    · intro k; apply List.mem_flatMap.mpr
      refine ⟨k 0,List.mem_ofFn.mpr (surj _),List.mem_map.mpr ⟨fun j => k j.succ,all _,?_⟩⟩
      funext i; exact Fin.cases rfl (fun _ => rfl) i

theorem same_length {A : Type v} (xs ys : List A) (nx : xs.Nodup) (ny : ys.Nodup)
    (same : ∀ x,x∈xs ↔ x∈ys) : xs.length=ys.length := by
  classical
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons a t => exact False.elim (List.not_mem_nil ((same a).mpr (by simp)))
  | cons a xs ih =>
    obtain ⟨an,sub⟩ := List.nodup_cons.mp nx
    have ay := (same a).mp (by simp)
    have e := ih (ys.erase a) sub (ny.erase a) (by
      intro x; rw [ny.mem_erase_iff]
      constructor
      · intro hm; exact ⟨fun eq => an (eq ▸ hm),(same x).mp (by simp [hm])⟩
      · rintro ⟨ne,hm⟩; simpa [ne] using (same x).mpr hm)
    have h := List.length_erase_of_mem ay
    have hn : ys.length>0 := List.length_pos_of_mem ay
    simp only [List.length_cons]; omega

theorem count_space (field : ConstantField F q) {S : (I→F)→Prop} (lin : Linear S)
    {n : Nat} (basis : HasDimension S n) :
    ∃ xs : List (I→F), xs.length=q^n ∧ xs.Nodup ∧ ∀ x,x∈xs ↔ S x := by
  obtain ⟨b,bm,bc⟩ := basis
  obtain ⟨ls,sz,nd,all⟩ := vectors field n
  refine ⟨ls.map (synthesis b),by simpa using sz,List.pairwise_map.mpr ?_,?_⟩
  · apply nd.imp
    intro c d ne eq
    obtain ⟨k,_,uk⟩ := bc _ (member_syn lin b c bm)
    exact ne ((uk c (fun _ => rfl)).trans (uk d (congrFun eq)).symm)
  · intro x; constructor
    · intro h; obtain ⟨c,_,rfl⟩ := List.mem_map.mp h; exact member_syn lin b c bm
    · intro h; obtain ⟨c,rep,_⟩ := bc x h
      exact List.mem_map.mpr ⟨c,all _,(funext rep).symm⟩

/-- Basis size is intrinsic, since the coordinate vectors enumerate exactly q^n elements. -/
theorem dimension_unique (field : ConstantField F q) {S : (I→F)→Prop} (lin : Linear S)
    {n m : Nat} (bn : HasDimension S n) (bm : HasDimension S m) : n=m := by
  obtain ⟨xs,sx,nx,ax⟩ := count_space field lin bn
  obtain ⟨ys,sy,ny,ay⟩ := count_space field lin bm
  have eq := same_length xs ys nx ny (fun x => (ax x).trans (ay x).symm)
  rw [sx,sy] at eq
  have strict {i j : Nat} (lt : i<j) : q^i<q^j := by
    have hq := field.two_le
    have pos := Nat.pow_pos (by omega : q>0) (n:=i)
    have e := Nat.mul_le_mul_left (q^i) hq
    have h := Nat.pow_le_pow_right (by omega : q>0) lt
    rw [Nat.pow_succ] at h
    omega
  by_cases lt : n<m
  · have := strict lt; omega
  · by_cases gt : m<n
    · have := strict gt; omega
    · omega

omit [Neg F] in
theorem dimension_zero {space : (I→F)→Prop}
    (_hz : space (fun _ => 0)) (zero : ∀ x,space x → ∀ i,x i=0) : HasDimension space 0 := by
  refine ⟨Fin.elim0,fun i => i.elim0,fun x hx => ⟨Fin.elim0,?_,?_⟩⟩
  · intro i; exact zero x hx i
  · intro d _; funext j; exact j.elim0

omit [Neg F] in
private theorem dim_unit : HasDimension (fun _ : Unit→F => True) 1 := by
  refine ⟨fun _ _ => 1,fun _ => trivial,fun x _ => ⟨fun _ => x (),?_,?_⟩⟩
  · intro s; cases s; simp [List.finRange_succ,total,Arithmetic.mulOne,Arithmetic.addZero]
  · intro d eq
    have e := eq ()
    funext j; have hj : j=0 := Fin.ext (Nat.eq_zero_of_le_zero (by omega))
    simpa [hj,List.finRange_succ,total,Arithmetic.mulOne,Arithmetic.addZero] using e.symm

/-- A subspace with support in a finite list has a basis. At a nonzero
coordinate project onto the constants and eliminate that pivot. -/
theorem finite_dimension (field : ConstantField F q) {S : (I→F)→Prop} (lin : Linear S)
    (support : List I) (outside : ∀ x,S x → ∀ i,i∉support → x i=0) :
    ∃ n,n≤support.length ∧ HasDimension S n := by
  classical
  induction support generalizing S with
  | nil =>
    exact ⟨0,Nat.le_refl _,dimension_zero lin.zero (fun x hx i => outside x hx i (by simp))⟩
  | cons i t ih =>
    by_cases nonzero : ∃ x,S x ∧ x i≠0
    · obtain ⟨x,hx,ne⟩ := nonzero
      let ker := fun v : I→F => S v ∧ v i=0
      have lk : Linear ker := ⟨⟨lin.zero,rfl⟩,fun a b k ha hb =>
        ⟨lin.addScaled a b k ha.1 hb.1,by simp only [ha.2,hb.2,Arithmetic.mulZero,Arithmetic.addZero]⟩⟩
      obtain ⟨r,le,rd⟩ := ih lk (by
        intro v hv j hj
        by_cases e : j=i
        · exact e ▸ hv.2
        · exact outside v hv.1 j (by simp [e,hj]))
      obtain ⟨b,inv⟩ := field.invertible _ ne
      refine ⟨1+r,by simp; omega,split_basis field lin (fun _ : Unit => i)
        (fun _ => True) ker ?_ ?_ dim_unit rd⟩
      · intro y; constructor
        · intro _
          refine ⟨fun j => 0+(y ()*b)*x j,lin.addScaled (fun _ => 0) x (y ()*b) lin.zero hx,?_⟩
          rintro ⟨⟩
          change 0+(y ()*b)*x i=y ()
          rw [zeroAdd,Arithmetic.mulAssoc,Arithmetic.mulComm b,inv,Arithmetic.mulOne]
        · intro _; trivial
      · intro v; exact ⟨fun h => ⟨h.1,fun _ => h.2⟩,fun h => ⟨h.1,h.2 ()⟩⟩
    · obtain ⟨n,le,hn⟩ := ih lin (by
        intro x hx j hj
        by_cases e : j=i
        · subst j; exact Classical.byContradiction (fun ne => nonzero ⟨x,hx,ne⟩)
        · exact outside x hx j (by simp [e,hj]))
      exact ⟨n,by simp; omega,hn⟩

end Megaera.FinalRankEngine
