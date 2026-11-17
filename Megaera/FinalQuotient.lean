import Megaera.FinalFixedKernel
import Megaera.FinalBinaryProof
import Megaera.FinalBinaryCleared
import Megaera.SectionThree

/-! The map from the tail to the unprefixed fundamental lift in Lemma 3.4.
Two tuples in the domain represent the same class when their exact degree
sums agree. The target uses the Laurent-valued same-degree defect. -/
namespace Megaera.FinalQuotient
open Megaera.Carlitz Megaera.Finite Megaera.Paper Megaera.Lift Megaera.SectionThreeSpaces
open Megaera.FinalBinarySeries Megaera.FinalBinaryTransport Megaera.FinalBinaryLaurent
open Megaera.FinalBinaryCarlitz Megaera.FinalBinaryCleared Megaera.FinalFixedKernel
open Megaera.BinaryOperators Megaera.RowEvaluation
variable {F : Type u} [Arithmetic F] [Neg F] {q w : Nat}
local instance : Arithmetic (Series F) := seriesArithmetic

private theorem same_degree (q : Nat) (d : Int) (l : List Tuple) (a : Laurent F) :
    Shaped.evaluate (inverse q) d (withCoeff a l)=a*mk 0 (total (degree q d) l) := by
  induction l with
  | nil => exact (Arithmetic.mulZero _).symm
  | cons t l ih =>
    change a*si (inverse q) d t + Shaped.evaluate _ d (withCoeff a l) = a*mk 0 (_+_)
    rw [ih,inverse_degree,embed_add,Arithmetic.distrib]

private theorem unprefixed_components {K : Type v} [OfNat K 1] (q : Nat) (D : K) (t : Tuple) :
    (cOp t (fundamental q D)).1.Perm (withCoeff 1 (L q [] t)) ∧
    (cOp t (fundamental q D)).2=withCoeff D (H q [] t) := by
  cases t with
  | nil => simp [cOp,fundamental,L,H,endings,concatenate,withCoeff,quasiShuffle_nil_right,start]
  | cons a t =>
    simp [cOp,fundamental,L,H,expand,start,diamond,triangle,endings,concatenate,
      quasiShuffle_nil_left,withCoeff,List.map_map,Function.comp_def]
    exact List.Perm.swap _ _ []

/-- Binary identity of the row C_t(R₁), with the second column at d+1. -/
theorem unprefixed_row (field : ConstantField F q) (d : Int) (t : Tuple) :
    mk (F:=F) 0 (total (degree q d) (L q [] t)) +
    delta q*mk 0 (total (degree q (d+1)) (H q [] t))=0 := by
  have eqn := FinalBinary.fundamental_transformed_binary field [] t d
  obtain ⟨hl,hh⟩ := unprefixed_components q (delta (F:=F) q) t
  change Shaped.evaluate (inverse q) d (cOp t (fundamental q (delta q))).1+
    Shaped.evaluate (inverse q) (d+1) (cOp t (fundamental q (delta q))).2=0 at eqn
  rw [hh,same_degree] at eqn
  have left := BCPRows.permSum (fun e : Laurent F × Tuple => e.1*si (inverse q) d e.2) hl
  change Shaped.evaluate _ d (cOp t (fundamental q (delta q))).1=Shaped.evaluate _ d _ at left
  rw [left,same_degree,oneMul] at eqn; exact eqn

/-- A nonempty B*-prefix makes the row fixed: both columns are at degree d. -/
theorem prefixed_row (field : ConstantField F q) (d : Int) (a : Nat) (h t : Tuple) :
    mk (F:=F) 0 (total (degree q d) (L q (a::h) t)) +
    delta q*mk 0 (total (degree q d) (H q (a::h) t))=0 := by
  let R := fundamental q (delta (F:=F) q)
  have supp : NonemptySupport R := by simp [R,fundamental,NonemptySupport]
  let p := bStar (a::h) (cOp t R)
  have hi : p.2=[] := bStar_fixed .. 
  have eqn : Shaped.evaluate (inverse q) d (liftPair p)=0 := by
    have rel := FinalBinary.fundamental_transformed_binary field (a::h) t d
    change Shaped.evaluate (inverse q) d p.1 + Shaped.evaluate (inverse q) (d+1) p.2=0 at rel
    simpa only [liftPair,hi,List.append_nil,Shaped.evaluate,total,Arithmetic.addZero] using rel
  have perm := FinalDegreeOne.fundamental_row q (delta (F:=F) q) (a::h) t
  rw [RevisedProducts.C_eq _ _ supp,
    (RevisedProducts.Bstar_eq _ _ (cOp_nonempty t _ supp)).1] at perm
  have c := BCPRows.permSum (fun e : Laurent F × Tuple => e.1*si (inverse q) d e.2) perm
  change Shaped.evaluate (inverse q) d (liftPair p)=Shaped.evaluate _ d _ at c
  rw [c] at eqn
  change total _ (_++_)=0 at eqn
  rw [total_append'] at eqn
  change Shaped.evaluate _ d _+Shaped.evaluate _ d _=0 at eqn
  rw [same_degree,same_degree,oneMul] at eqn; exact eqn

/-- Same-level specialization in the coefficient language of Section 3. -/
theorem prefixed_row_fixed (field : ConstantField F q) (n : Nat) (h t : Tuple) (d : Int) :
    cleared q (valueAt (degree q d) (withCoeff (1:F) (L q (n::h) t)))
      (valueAt (degree q d) (withCoeff (1:F) (H q (n::h) t))) := by
  have one : constant (1:F)=(1 : Series F) := rfl
  simp only [value_weighted,sum_terms,one,oneMul]
  exact (cleared_iff field _ _).mp (prefixed_row field d n h t)

/-- Laurent evaluation of a homogeneous pair at two specified levels. -/
noncomputable def defect (q : Nat) (d e : Int) (p r : FormalSum F) : Laurent F :=
  mk 0 (valueAt (degree q d) p)+delta q*mk 0 (valueAt (degree q e) r)

private theorem sumLaw (q : Nat) (d : Int) (c : F) (l : List Tuple) (p : FormalSum F) :
    mk 0 (valueAt (degree q d) (withCoeff c l++p))=
    scalar c*mk 0 (total (degree q d) l)+mk 0 (valueAt (degree q d) p) := by
  rw [value_weighted,total_append',sum_terms,embed_add,embed_mul,←value_weighted]; rfl

theorem split_defect (d e : Int) (c : F) (l h : List Tuple) (p r : FormalSum F) :
    defect q d e (withCoeff c l++p) (withCoeff c h++r)=
    scalar c*(mk 0 (total (degree q d) l)+delta q*mk 0 (total (degree q e) h))+
    defect q d e p r := by
  simp only [defect,sumLaw,Arithmetic.distrib]
  letI : Std.Associative (α:=Laurent F) (·+·) := ⟨Arithmetic.addAssoc⟩
  letI : Std.Commutative (α:=Laurent F) (·+·) := ⟨Arithmetic.addComm⟩
  letI : Std.Associative (α:=Laurent F) (·*·) := ⟨Arithmetic.mulAssoc⟩
  letI : Std.Commutative (α:=Laurent F) (·*·) := ⟨Arithmetic.mulComm⟩
  ac_nf
  apply congrArg (_+·)
  rw [←Arithmetic.addAssoc,Arithmetic.addComm]

theorem unprefixed_binary (field : ConstantField F q) (p : FormalSum F) (d : Int) :
    cleared q (valueAt (degree q d) (expand (L q []) p))
              (valueAt (degree q (d+1)) (expand (H q []) p)) := by
  apply (cleared_iff field _ _).mp
  change defect q d (d+1) _ _=0
  induction p with
  | nil => change (0 : Laurent F)+delta q*0=0; rw [Arithmetic.mulZero,Arithmetic.addZero]
  | cons z p ih =>
    change defect q d (d+1) (withCoeff z.1 _++_) (withCoeff z.1 _++_)=0
    rw [split_defect,unprefixed_row field,Arithmetic.mulZero,zeroAdd]
    exact ih

/-- The kernel for the concrete lift, with no binary hypothesis. -/
theorem fixed_image_iff (field : ConstantField F q) (p : FormalSum F) (hp : homogeneous w p) :
    (∀ d, defect q d d (expand (L q []) p) (expand (H q []) p)=0) ↔ fixedLevels q p := by
  rw [←unprefixed_fixed_iff field p hp (unprefixed_binary field p)]
  exact ⟨fun h d => (cleared_iff field _ _).mp (h d),fun h d => (cleared_iff field _ _).mpr (h d)⟩

end Megaera.FinalQuotient
