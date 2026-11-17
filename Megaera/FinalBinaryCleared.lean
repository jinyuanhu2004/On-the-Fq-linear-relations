import Megaera.FinalBinaryCarlitz
import Megaera.SectionThreeSpaces

/-! Multiplying by θ⁻q identifies the Laurent coefficient D₁ with the
cleared-series equations for the two columns in Section 3. -/
namespace Megaera.FinalBinaryCleared
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.FinalBinaryLaurent
open Megaera.FinalBinaryCarlitz Megaera.FinalBinarySeries
variable {F : Type u} [Arithmetic F] [Neg F]
local instance : Arithmetic (Series F) := seriesArithmetic
local instance : Std.Associative (α:=Laurent F) (·+·) := ⟨Arithmetic.addAssoc⟩
local instance : Std.Commutative (α:=Laurent F) (·+·) := ⟨Arithmetic.addComm⟩

/-- D₁ = θ^q − θ, the negative of the first Carlitz denominator factor. -/
noncomputable def delta (q : Nat) : Laurent F := -(theta + -power theta q)

theorem delta_add_theta (field : ConstantField F q) :
    delta (F:=F) q+theta=power theta q := by
  let x : Laurent F := power theta q
  apply add_cancel field (theta+-x)
  calc
    _ = ((theta + -x)+ -(theta + -x)) + theta := by unfold delta x; ac_rfl
    _ = theta := by rw [negative_sum field,zeroAdd]
    _ = (theta + -x)+x := by rw [Arithmetic.addAssoc,Arithmetic.addComm (-x), negative_sum field,Arithmetic.addZero]

/-- Exact change of coordinates between the Laurent relation and its
power-series form, valid for all series A and B. -/
theorem cleared_iff (field : ConstantField F q) (A B : Series F) :
    mk 0 A+delta q*mk 0 B=0 ↔ SectionThreeSpaces.cleared q A B := by
  have ringEq : mk 0 A+delta q*mk 0 B=0 ↔ mk 0 A+power theta q*mk 0 B=theta*mk 0 B := by
    have replacement : power theta q*mk 0 B=delta q*mk 0 B+theta*mk 0 B := by
      rw [←delta_add_theta field,Arithmetic.mulComm _ (mk 0 B),Arithmetic.distrib,
        Arithmetic.mulComm (mk 0 B) (delta q),Arithmetic.mulComm (mk 0 B) theta]
    rw [replacement,←Arithmetic.addAssoc]
    constructor
    · intro h; rw [h,zeroAdd]
    · intro h
      apply add_cancel field (theta*mk 0 B)
      rw [Arithmetic.addComm (theta*mk 0 B),h,Arithmetic.addZero]
  rw [ringEq,theta_pow]
  have hq := field.two_le
  have reduc : power (T : Series F) q=power T 1*power T (q-1) := by
    rw [←power_add,show 1+(q-1)=q by omega]
  change mk 0 A+(mk q 1*mk 0 B)=(mk 1 1*mk 0 B) ↔ _
  simp only [mk_mul,Nat.add_zero,oneMul,mk_add,Nat.zero_add,power,oneMul]
  constructor
  · intro h
    have e : power T 1*(power T q*A+B) = power T q*B := Quotient.exact h
    rw [show power T q*B=power T 1*(power T (q-1)*B) by rw [←Arithmetic.mulAssoc,←reduc]] at e
    have v := cancel_pow (F:=F) 1 e
    rw [powT_mul,powT_mul] at v
    exact fun n => congrFun v n
  · intro h
    apply Quotient.sound (s:=rel)
    change power T 1*(power T q*A+B)=power T q*B
    rw [show power T q*B=power T 1*(power T (q-1)*B) by rw [←Arithmetic.mulAssoc,←reduc]]
    apply congrArg (fun z : Series F => power T 1*z)
    rw [powT_mul,powT_mul]
    exact funext h

end Megaera.FinalBinaryCleared
