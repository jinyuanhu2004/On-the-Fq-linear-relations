import Megaera.FinalBinaryCarlitz
import Megaera.FinalFiniteFrobenius

/-! The fundamental binary relation (1.1) and its two-column transforms,
Lemma 2.1 and Theorem 2.2 for the actual Carlitz inverse denominators. -/
namespace Megaera.FinalBinary
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.Shaped Megaera.BinaryOperators
open Megaera.FinalBinaryLaurent Megaera.FinalBinaryCarlitz

variable {F : Type u} [Arithmetic F] [Neg F] {q : Nat}
local instance : Std.Associative (α:=Laurent F) (·+·) := ⟨Arithmetic.addAssoc⟩
local instance : Std.Commutative (α:=Laurent F) (·+·) := ⟨Arithmetic.addComm⟩

private theorem next_factor (field : ConstantField F q) (d : Nat) :
    (theta (F:=F) + -power theta (q^((d+1)+1))) =
    power (theta + -power theta (q^(d+1))) q + (theta + -power theta q) := by
  rw [FinalFiniteFrobenius.power_subtractive field (negative_sum field) scalar
    scalar_zero scalar_one scalar_add,Fundamental.power_power,←Nat.pow_succ]
  symm
  calc
    _ = (power theta q + -power theta q) + (theta + -power theta (q^((d+1)+1))) := by ac_rfl
    _ = _ := by rw [negative_sum field,zeroAdd]

theorem fundamental_level (field : ConstantField F q) (d : Nat) :
    level (inverse (F:=F) q) d [q] =
      (theta + -power theta q)*level (inverse q) (d+1) [1,q-1] := by
  exact Fundamental.finite_identity q (by have := field.two_le; omega)
    (fun n => theta + -power theta (q^(n+1))) (inverse q) (theta + -power theta q)
    (by simp) rfl (next_factor field) (factor_inverse field) d

/-- Binary relation (1.1), including the exceptional degree −1. Here
the coefficient of the right column is D₁ = θ^q − θ. -/
theorem fundamental_binary (field : ConstantField F q) :
    Shaped.Binary (inverse (F:=F) q) (fundamental q (-(theta + -power theta q))) := by
  let c : Laurent F := theta + -power theta q
  intro d
  cases d with
  | ofNat n =>
    change (1 * level (inverse q) n [q] + 0) + ((-c) * level (inverse q) (n+1) [1,q-1] + 0) = 0
    rw [oneMul,Arithmetic.addZero,Arithmetic.addZero,fundamental_level field]
    change c * _ + (-c) * _ = 0
    rw [Arithmetic.mulComm c,Arithmetic.mulComm (-c),←Arithmetic.distrib,negative_sum field,
      Arithmetic.mulZero]
  | negSucc n =>
    cases n with
    | zero =>
      change (1 * 0 + 0) + ((-c) * (power (inverse q 0) 1 * 0) + 0) = 0
      simp only [Arithmetic.mulZero,Arithmetic.addZero]
    | succ n =>
      rw [show Int.negSucc (n+1)+1=Int.negSucc n by omega]
      cases n <;> change (1 * 0 + 0) + ((-c) * 0 + 0) = 0 <;>
        simp only [Arithmetic.mulZero,Arithmetic.addZero]

theorem fundamental_transformed_binary (field : ConstantField F q) (h t : Tuple) :
    Shaped.Binary (inverse (F:=F) q)
      (bStar h (cOp t (fundamental q (-(theta + -power theta q))))) := by
  have supp : NonemptySupport (fundamental q (-(theta (F:=F) + -power theta q))) := by
    simp [NonemptySupport,fundamental]
  exact bStar_binary _ h _ (cOp_nonempty t _ supp)
    (cOp_binary _ t _ supp (fundamental_binary field))

private theorem inverse_unit (field : ConstantField F q) (d : Nat) :
    ∃ a : Laurent F, a * inverse q d = 1 := by
  induction d with
  | zero => exact ⟨1,Arithmetic.mulOne 1⟩
  | succ n ih =>
    obtain ⟨a,h⟩ := ih
    exact ⟨a * (theta + -power theta (q^(n+1))),by rw [Arithmetic.mulAssoc,factor_inverse field,h]⟩

omit [Neg F] in
private theorem one_power (n : Nat) : power (1:Laurent F) n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [power,ih,Arithmetic.mulOne]

theorem cancel_level (field : ConstantField F q) (n : Nat) (a b : Laurent F)
    (h : level (inverse q) (n+1) [1,q-1]*a = level (inverse q) (n+1) [1,q-1]*b) : a=b := by
  obtain ⟨u,hu⟩ := inverse_unit field n
  have eq := congrArg (fun x => (theta (F:=F) + -power theta q)*x) h
  change (theta + -power theta q)*(level (inverse q) (n+1) [1,q-1]*a) =
    (theta + -power theta q)*(level (inverse q) (n+1) [1,q-1]*b) at eq
  rw [←Arithmetic.mulAssoc,←Arithmetic.mulAssoc,←fundamental_level field] at eq
  simp only [level,trunc_nil,Arithmetic.mulOne] at eq
  have eq' := congrArg (fun x => power u q*x) eq
  simpa only [←Arithmetic.mulAssoc,←Fundamental.power_mul_base,hu,one_power,oneMul] using eq'

/-- Lemma 2.1 with coefficients in the Laurent series at infinity. -/
theorem lemma_2_1 (field : ConstantField F q) (P Q : FormalSum (Laurent F))
    (nonemptyP : ∀ z ∈ P, z.2 ≠ []) (nonemptyQ : ∀ z ∈ Q, z.2 ≠ [])
    (h : Shaped.Binary (inverse q) (weightedShaped q P Q)) :
    Shaped.Binary (inverse q) (weightedShaped q (mapTuples (List.cons 1) P)
      (mapTuples (List.cons 1) Q)) ∧
    Shaped.Binary (inverse q) (weightedShaped q (mapTuples incFirst P) (mapTuples incFirst Q)) :=
  lemma_2_1_weighted _ _ _ _ _ nonemptyP nonemptyQ (fundamental_level field)
    (cancel_level field) (add_cancel field) (negative_sum field 1) h

private theorem coeff_primitive (field : ConstantField F q) (s : Tuple) :
    coeffPair (primitive (K:=F) q s)=primitive q s := by
  simp [coeffPair,coeffs,primitive,generalP,withCoeff,List.map_map,Function.comp_def,
    scalar_neg field,scalar_one]

/-- Theorem 2.2 in the original coefficientwise binary relation space. -/
theorem theorem_2_2 (field : ConstantField F q) (s : Tuple) (hs : Valid s) (hne : s≠[]) :
    Lift.Binary (F:=F) q (primitive q s) := by
  apply (inverse_binary_iff ..).mp
  rw [coeff_primitive field]
  exact primitive_binary _ _ _ (fundamental_level field) (add_cancel field)
    (negative_sum field 1) s hs hne

/-- In particular every defining generator of BCP is a binary relation
before lifting. This discharges the former generator-soundness premise. -/
theorem generator_binary (field : ConstantField F q) (u v s : Tuple)
    (hs : Valid s) (hne : s≠[]) :
    Lift.Binary (F:=F) q (bStar u (cOp v (primitive q s))) := by
  have qp : 0<q := by have := field.two_le; omega
  have supp := nonemptySupport_of_weight _ (by omega) _ (generalP_weight (K:=F) q qp s [])
  have cp := (FinalBinaryTransport.operators_binary q v _ supp (theorem_2_2 field s hs hne)).2.2
  exact (FinalBinaryTransport.operators_binary q u _ (cOp_nonempty v _ supp) cp).2.1

end Megaera.FinalBinary
