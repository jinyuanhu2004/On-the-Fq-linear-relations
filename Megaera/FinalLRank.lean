import Megaera.FinalLRankCount
import Megaera.CanonicalBasis
import Megaera.Singletons
import Megaera.Rev4Pairing

/-! The canonical L rows form a finite basis, with a dual for every row. -/
namespace Megaera.FinalLRank
open Megaera.Finite Megaera.Paper Megaera.Carlitz Megaera.SplitKernel Megaera.Splitting
open Megaera.FinalLRankCount Megaera.SectionThreeSpaces Megaera.Rev4Pairing
variable {F : Type u} [Arithmetic F] [Neg F] {q w : Nat}

local instance : Sub F := ⟨fun a b => a+ -b⟩
local instance : Std.Commutative (α:=F) (·+·) := ⟨Arithmetic.addComm⟩
local instance : Std.Associative (α:=F) (·+·) := ⟨Arithmetic.addAssoc⟩

private theorem subLaws (field : ConstantField F q) : Subtraction F := by
  constructor
  · intro a b; change (a+ -b)+b=a
    rw [Arithmetic.addAssoc,Arithmetic.addComm (-b),field.add_neg,Arithmetic.addZero]
  · intro a b; change (a+b)+ -b=a
    rw [Arithmetic.addAssoc,field.add_neg,Arithmetic.addZero]
  · intro a b c d; change (a+ -b)+(c+ -d)=(a+c)+ -(b+d)
    rw [Singletons.neg_add field.add_neg]; ac_rfl

private abbrev Index (q w : Nat) := Fin (sources q w).length

private noncomputable def basis (i : Index q w) : Tuple → F :=
  coordinates (withCoeff 1 (L q (rowIndex i).val.1 (rowIndex i).val.2))

private noncomputable def synth (c : Index q w → F) (s : Tuple) : F :=
  total (fun i => c i * basis i s) (List.finRange (sources q w).length)

private def functional (field : ConstantField F q) (i : Index q w) : Tuple → F :=
  CanonicalBasis.extend q (Nat.lt_of_lt_of_le (by decide) field.two_le) (fun _ => 0)
    (fun h t => if source q h t = (sources q w).get i then 1 else 0) []

private theorem read_basis (field : ConstantField F q) (i j : Index q w) :
    reading w (functional field i) (basis j) = if i=j then 1 else 0 := by
  let p := rowIndex j
  let f := functional field i
  have qp : 0<q := Nat.lt_of_lt_of_le (by decide) field.two_le
  change reading w f (coordinates (withCoeff 1 (L q p.val.1 p.val.2)))=_
  rw [reading_coordinates w f _ (by
    intro e he
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp he
    have wt := p.property.2.2
    have eq := L_weight q p.val.1 p.val.2 s hs
    exact ⟨L_valid q qp _ _ p.property.1 p.property.2.1 s hs,by change weight s=w; omega⟩)]
  have dual := CanonicalBasis.on_canonical (subLaws field) q qp (fun _ => 0)
    (fun h t => if source q h t=(sources q w).get i then (1:F) else 0)
    p.val.1 p.val.2 (row_spec j).2 p.property.2.1
  change onRow q f p.val.1 p.val.2=(if source q p.val.1 p.val.2=(sources q w).get i then 1 else 0) at dual
  have total_row (h t : Tuple) :
      total (fun e : F × Tuple => e.1*f e.2) (withCoeff 1 (L q h t)) = onRow q f h t := by
    cases t <;> simp [onRow,L,start,withCoeff,total,oneMul,zeroAdd,Arithmetic.addZero,Arithmetic.addComm]
  rw [total_row,dual,show source q p.val.1 p.val.2=_ from (row_spec j).1]
  by_cases e : i=j
  · simp [e]
  · rw [if_neg (fun h => e ((source_inj j i h).symm)),if_neg e]

omit [Neg F] in
private theorem one_position {n : Nat} (i : Fin n) (v : F) :
    total (fun j => if i=j then v else 0) (List.finRange n)=v := by
  have nodup : (List.finRange n).Nodup := by
    apply List.pairwise_iff_getElem.mpr
    intro a b ha hb lt eq
    have e : a=b := by simpa using congrArg Fin.val eq
    omega
  have mem : i∈List.finRange n := List.mem_ofFn.mpr ⟨i,rfl⟩
  suffices h : ∀ (xs : List (Fin n)),xs.Nodup →
      total (fun j => if i=j then v else 0) xs=(if i∈xs then v else 0) by
    simpa only [if_pos mem] using h _ nodup
  intro xs nd
  induction xs with
  | nil => simp [total]
  | cons a xs ih =>
    obtain ⟨na,d⟩ := List.nodup_cons.mp nd
    by_cases e : i=a
    · subst a; simp [total,ih d,na,Arithmetic.addZero]
    · simp [total,ih d,e,zeroAdd]

private theorem read_synth (field : ConstantField F q) (i : Index q w) (c : Index q w → F) :
    reading w (functional field i) (synth c)=c i := by
  let f := functional field i
  have expand (js : List (Index q w)) : reading w f (fun s => total (fun j => c j*basis j s) js)=
      total (fun j => c j*reading w f (basis j)) js := by
    induction js with
    | nil => exact reading_zero .. 
    | cons j js ih => simp only [total,reading_add,reading_scale,ih]
  change reading w f (fun s => total _ (List.finRange _))=_
  rw [expand]
  have entry (j : Index q w) : c j * reading w f (basis j) = if i=j then c i else 0 := by
    rw [read_basis]; by_cases e:i=j <;> simp [e,Arithmetic.mulOne,Arithmetic.mulZero]
  simp only [entry,one_position]

omit [Neg F] in
private theorem synth_increment (i : Index q w) (k : F) (c : Index q w → F) (s : Tuple) :
    synth (fun j => (if i=j then k else 0)+c j) s=k*basis i s+synth c s := by
  have term (j : Index q w) : ((if i=j then k else 0)+c j)*basis j s=
      (if i=j then k*basis i s else 0)+c j*basis j s := by
    rw [Arithmetic.mulComm _ (basis j s),Arithmetic.distrib,
      Arithmetic.mulComm (basis j s) (c j)]
    by_cases e : i=j <;> simp [e,zeroMul,Arithmetic.mulZero,Arithmetic.mulComm]
  simp only [synth,term,sum_add,one_position]

private theorem span (field : ConstantField F q) (xs : Rows F q w) (b : FinalCanonical.Bounded xs) :
    ∃ c : Index q w→F,component L xs=synth c := by
  induction xs with
  | nil =>
    refine ⟨fun _ => 0,funext fun s => ?_⟩
    exact (total_zero_of_members _ _ (fun _ _ => zeroMul _)).symm
  | cons e xs ih =>
    obtain ⟨c,hc⟩ := ih (fun a ha => b a (List.mem_cons_of_mem _ ha))
    obtain ⟨i,eq⟩ := bounded_row_index (Nat.lt_of_lt_of_le (by decide) field.two_le) e.2 (b e (by simp))
    refine ⟨fun j => (if i=j then e.1 else 0)+c j,?_⟩
    funext s
    rw [synth_increment,←hc]
    simp only [basis,eq]; rfl

/-- The rank of the actual span of L in weight w is |I_w|−|B_w^TT|. -/
theorem image_dimension (field : ConstantField F q) (w : Nat) :
    HasDimension (fun v => ∃ xs : Rows F q w,component L xs=v)
      (Dimension.tupleCount w-Dimension.ttCount q w).toNat := by
  rw [←sourceList_card]
  change HasDimension _ (sources q w).length
  refine ⟨basis,?_,?_⟩
  · intro i
    refine ⟨[(1,rowIndex i)],funext fun s => ?_⟩
    change 1*basis i s+0=basis i s
    rw [oneMul,Arithmetic.addZero]
  · intro x hx
    obtain ⟨ys,byz,ey⟩ := (FinalCanonical.theorem_2_8 field x).mp hx
    obtain ⟨c,ec⟩ := span field ys byz
    have repr := ey.symm.trans ec
    refine ⟨c,congrFun repr,?_⟩
    intro d ed
    have eq : synth d=synth c := (funext ed).symm.trans repr
    funext i
    exact (read_synth field i d).symm.trans ((congrArg (reading w (functional field i)) eq).trans (read_synth field i c))

end Megaera.FinalLRank
