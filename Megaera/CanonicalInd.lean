import Megaera.CanonicalBasis
import Megaera.MainTheorems

/-! The actual linear operator Ind of §2.2 at a fixed weight. Its matrix
columns vanish on TT indices and send each bounded-prefix L-row to the
corresponding H-row. The weight-w action sums over all valid tuples of
weight w, with the enumeration proved in Dimension. -/
namespace Megaera.CanonicalInd
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.SplitKernel
variable {F : Type u} [Arithmetic F] [Neg F]

local instance {A : Type u} [Add A] [Neg A] : Sub A := ⟨fun a b => a + (-b)⟩
local instance : Zero (Tuple → F) := ⟨fun _ => 0⟩
local instance : Std.Associative (α := F) (· + ·) := ⟨Arithmetic.addAssoc⟩
local instance : Std.Commutative (α := F) (· + ·) := ⟨Arithmetic.addComm⟩

private theorem subtraction (field : ConstantField F q) : Subtraction F := by
  have negSum (a b : F) : -(a+b) = (-a)+(-b) := by
    have h : (a+b)+((-a)+(-b))=0 := by
      calc _ = (a+(-a))+(b+(-b)) := by ac_rfl
           _ = 0 := by rw [field.add_neg,field.add_neg,Arithmetic.addZero]
    calc -(a+b) = -(a+b)+((a+b)+((-a)+(-b))) := by rw [h,Arithmetic.addZero]
         _ = ((a+b)+(-(a+b)))+((-a)+(-b)) := by ac_rfl
         _ = _ := by rw [field.add_neg,zeroAdd]
  constructor
  · intro a b
    change (a+(-b))+b=a
    calc _ = a+(b+(-b)) := by ac_rfl
         _ = a := by rw [field.add_neg,Arithmetic.addZero]
  · intro a b
    change (a+b)+(-b)=a
    rw [Arithmetic.addAssoc,field.add_neg,Arithmetic.addZero]
  · intro a b c d
    change (a+(-b))+(c+(-d))=(a+c)+(-(b+d))
    rw [negSum]
    ac_rfl

def column (q : Nat) (hq : 0 < q) (s u : Tuple) : F :=
  CanonicalBasis.extend q hq (fun _ => 0)
    (fun h t => coordinates (withCoeff 1 (H q h t)) u) [] s

def ind (q w : Nat) (hq : 0 < q) (v : Tuple → F) (u : Tuple) : F :=
  total (fun s => v s * column q hq s u) (Dimension.tuples Int.toNat w)

theorem column_TT (q : Nat) (hq : 0 < q) (s u : Tuple) (hs : TT q s) :
    column (F := F) q hq s u = 0 :=
  CanonicalBasis.on_TT q hq _ _ s hs

theorem column_canonical (q : Nat) (hq : 0 < q) (field : ConstantField F q)
    (h t u : Tuple) (bounded : ∀ a ∈ h, a ≤ q) (ht : Valid t) :
    onRow q (fun s => column (F := F) q hq s u) h t =
      coordinates (withCoeff 1 (H q h t)) u :=
  CanonicalBasis.on_canonical (subtraction field) q hq _ _ h t bounded ht

theorem ind_zero (q w : Nat) (hq : 0 < q) : ind (F := F) q w hq 0 = 0 := by
  funext u
  apply total_zero_of_members
  intro _ _
  exact zeroMul _

omit [Neg F] in
private theorem sum_add (f g : Tuple → F) (l : List Tuple) :
    total (fun i => f i + g i) l = total f l + total g l := by
  induction l with
  | nil => simp [total,Arithmetic.addZero]
  | cons a l ih => simp only [total,ih]; ac_rfl

theorem ind_add (q w : Nat) (hq : 0 < q) (v z : Tuple → F) :
    ind q w hq (fun s => v s + z s) = fun u => ind q w hq v u + ind q w hq z u := by
  funext u
  unfold ind
  simp only [Arithmetic.mulComm (_ + _) _, Arithmetic.distrib]
  rw [sum_add]
  simp only [Arithmetic.mulComm (column (F := F) q hq _ u)]

theorem ind_scale (q w : Nat) (hq : 0 < q) (a : F) (v : Tuple → F) :
    ind q w hq (fun s => a * v s) = fun u => a * ind q w hq v u := by
  funext u
  unfold ind
  simp only [Arithmetic.mulAssoc]
  apply total_scale

omit [Neg F] in
private theorem delta (l : List Tuple) (s : Tuple) (v : F) (hn : l.Nodup) :
    total (fun j => if s = j then v else 0) l = (if s ∈ l then v else 0) := by
  induction l with
  | nil => simp [total]
  | cons a l ih =>
    obtain ⟨ha,hl⟩ := List.nodup_cons.mp hn
    by_cases he : s = a
    · subst s; simp [total,ih hl,ha,Arithmetic.addZero]
    · simp [total,ih hl,he,zeroAdd]

private theorem weight_sum (s : Tuple) : weight s = s.sum := by
  induction s with
  | nil => rfl
  | cons a s ih => simp [weight,ih]

private theorem on_tuple (q w : Nat) (hq : 0 < q) (s : Tuple) (hs : Valid s)
    (hw : weight s = w) :
    ind (F := F) q w hq (fun j => if s = j then 1 else 0) = column q hq s := by
  funext u
  have inside := (Dimension.mem_unrestricted w s).mpr
    ⟨by rw [← weight_sum,hw],hs⟩
  have entry (j : Tuple) :
      ((if s=j then 1 else 0 : F) * column q hq j u) = (if s=j then column q hq s u else 0) := by
    split <;> rename_i hj
    · rw [hj,oneMul]
    · exact zeroMul _
  unfold ind
  simp only [entry,delta (F := F) _ _ _ (Dimension.tuples_nodup _ _),if_pos inside]

private theorem on_list (q w : Nat) (hq : 0 < q) (l : List Tuple)
    (hs : TermsValid l) (hw : TermsOfWeight w l) (u : Tuple) :
    ind (F := F) q w hq (coordinates (withCoeff 1 l)) u = total (fun j => column q hq j u) l := by
  induction l with
  | nil => exact congrFun (ind_zero q w hq) u
  | cons s l ih =>
    change ind q w hq (fun j => (if s=j then 1 else 0) + coordinates (withCoeff 1 l) j) u = _
    rw [ind_add,on_tuple q w hq s (hs s (by simp)) (hw s (by simp))]
    exact congrArg (column (F := F) q hq s u + ·)
      (ih (fun j hj => hs j (by simp [hj])) (fun j hj => hw j (by simp [hj])))

theorem ind_TT (q w : Nat) (hq : 0 < q) (s : Tuple) (hs : Valid s)
    (hw : weight s = w) (ht : TT q s) :
    ind (F := F) q w hq (fun j => if s = j then 1 else 0) = 0 := by
  rw [on_tuple q w hq s hs hw]
  exact funext (fun u => column_TT q hq s u ht)

theorem ind_canonical (q w : Nat) (hq : 0 < q) (field : ConstantField F q)
    (h t : Tuple) (hh : Valid h) (bounded : ∀ a ∈ h, a ≤ q) (ht : Valid t)
    (hw : weight h + q + weight t = w) :
    ind q w hq (coordinates (withCoeff (1:F) (L q h t))) =
      coordinates (withCoeff 1 (H q h t)) := by
  funext u
  rw [on_list q w hq _ (L_valid q hq h t hh ht) (hw ▸ L_weight q h t)]
  have equiv := column_canonical q hq field h t u bounded ht
  cases t with
  | nil => simpa [L,start,total,onRow,Arithmetic.addZero] using equiv
  | cons a t =>
    simpa [L,start,total,onRow,Arithmetic.addZero,zeroAdd,Arithmetic.addComm] using equiv

theorem ind_components (q w : Nat) (hq : 0 < q) (field : ConstantField F q)
    (rows : Rows F q w) (bounded : ∀ e ∈ rows, ∀ a ∈ e.2.val.1, a ≤ q) :
    ind q w hq (component L rows) = component H rows := by
  induction rows with
  | nil => exact ind_zero q w hq
  | cons e rows ih =>
    have hb := bounded e (List.mem_cons_self)
    obtain ⟨k,⟨⟨h,t⟩,hh,ht,hw⟩⟩ := e
    change weight h + weight t + q = w at hw
    change ind q w hq (fun j => k * coordinates (withCoeff 1 (L q h t)) j + component L rows j) = _
    rw [ind_add,ind_scale,ind_canonical q w hq field h t hh hb ht (by omega),
      ih (fun e he => bounded e (List.mem_cons_of_mem _ he))]
    rfl

/-- The analytic input for the canonical lift now asks only that a relation
is a combination of bounded-prefix L-rows. Its H-image is computed by Ind.
Strict rank increase and the two kernel-image statements remain inputs. -/
theorem completeness_with_ind (q w : Nat) (hq : 0 < q) (field : ConstantField F q)
    (rank : (Tuple → F) → Nat) (bound : Nat)
    (preserves : ∀ v : Tuple → F, RelationVector q w v → RelationVector q w (ind q w hq v))
    (bounded : ∀ v, RelationVector q w v → rank v ≤ bound)
    (increases : ∀ v, RelationVector q w v → ind q w hq v ≠ 0 → rank v < rank (ind q w hq v))
    (canonical : ∀ v, RelationVector q w v → ∃ rows : Rows F q w, component L rows = v ∧
      ∀ e ∈ rows, ∀ a ∈ e.2.val.1, a ≤ q)
    (kerL : ∀ v, BCPVector q w v → ∃ k : Rows F q w, component L k = 0 ∧ component H k = v)
    (kerH : ∀ c : Rows F q w, component H c = 0 → BCPVector q w (component L c))
    (binary_generators : ∀ u v s, Valid u → Valid v → Valid s → s ≠ [] →
      weight u + weight v + weight s + 2*q = w →
      Lift.Binary (F := F) q (bStar u (cOp v (primitive q s))))
    (p : FormalSum F) (hw : ∀ e ∈ p, Valid e.2 ∧ weight e.2 = w) :
    Relation q w p ↔ InBCP q w p := by
  apply completeness_at_weight q w field (ind q w hq) rank bound (ind_zero q w hq)
    preserves bounded increases _ kerL kerH binary_generators p hw
  intro v hv
  obtain ⟨rows,hl,hb⟩ := canonical v hv
  exact ⟨rows,hl,hl ▸ (ind_components q w hq field rows hb).symm⟩

end Megaera.CanonicalInd
