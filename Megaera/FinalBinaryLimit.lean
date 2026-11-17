import Megaera.FinalBinaryProof

/-! The coefficientwise lifting theorem (1.14) for a finite presentation
with arbitrary coefficients in the Laurent series field at infinity. -/
namespace Megaera.FinalBinary
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.Shaped Megaera.BinaryOperators
open Megaera.FinalBinaryLaurent Megaera.FinalBinaryCarlitz Megaera.FinalBinarySeries
variable {F : Type u} [Arithmetic F] [Neg F] {q : Nat}
local instance : Arithmetic (Series F) := seriesArithmetic

/-- With one common power of T clearing the denominators, each numerator
coefficient agrees with the stated limit for all sufficiently large d. -/
private def Stabilizes (f : Nat → Laurent F) (a : Laurent F) : Prop :=
  ∃ (i : Nat) (x : Nat → Series F) (y : Series F), (∀ d, f d=mk i (x d)) ∧ a=mk i y ∧
    ∀ n d, n<d → x d n=y n

omit [Neg F] in
private theorem stabilizes_add {f g : Nat → Laurent F} {a b : Laurent F}
    (ha : Stabilizes f a) (hb : Stabilizes g b) :
    Stabilizes (fun d => f d+g d) (a+b) := by
  obtain ⟨i,x,u,hx,rfl,sx⟩ := ha
  obtain ⟨j,y,v,hy,rfl,sy⟩ := hb
  refine ⟨i+j,fun d => power T j*x d+power T i*y d,power T j*u+power T i*v,
    fun d => by dsimp only; rw [hx,hy,mk_add], rfl,?_⟩
  intro n d nd
  simp only [powT_mul]
  change shift j (x d) n+shift i (y d) n=shift j u n+shift i v n
  unfold shift
  split <;> split <;> simp_all [sx (n-j) d (by omega),sy (n-i) d (by omega)]

omit [Neg F] in
private theorem stabilizes_zero {f : Nat → Laurent F} {a : Laurent F}
    (h : Stabilizes f a) (eqn : ∀ d, f d=0) : a=0 := by
  obtain ⟨i,x,y,hx,rfl,sx⟩ := h
  have van (d : Nat) : x d=0 := by
    have e := (hx d).symm.trans (eqn d)
    have z : power T 0*x d=power T i*0 := Quotient.exact e
    simpa only [power,oneMul,Arithmetic.mulZero] using z
  have z : y=0 := by
    funext n
    rw [←sx n (n+1) (by omega),van]
  rw [z]
  apply Quotient.sound (s:=rel)
  change power T 0*0=power T i*(0:Series F)
  rw [Arithmetic.mulZero,Arithmetic.mulZero]

private theorem stabilizes_term (hq : 2≤q) (z : Laurent F) (s : Tuple) (j : Nat)
    (v : Valid s) (pos : s≠[]) :
    Stabilizes (fun d => z*truncSum (inverse q) (d+j) s) (z*mk 0 (li q s)) := by
  refine Quotient.inductionOn z ?_
  rintro ⟨i,g⟩
  refine ⟨i,fun d => g*trunc q (d+j) s,g*li q s,?_,rfl,?_⟩
  · intro d; dsimp only; rw [inverse_trunc]; rfl
  · intro n d nd
    change total (fun k => g k*trunc q (d+j) s (n-k)) (List.range (n+1)) =
      total (fun k => g k*li q s (n-k)) (List.range (n+1))
    have eq (k : Nat) : trunc (F:=F) q (d+j) s (n-k)=li q s (n-k) :=
      (li_coeff q (n-k) (d+j) s hq v pos (by omega)).symm
    simp only [eq]

private theorem stabilizes_weighted (hq : 2≤q) (p : FormalSum (Laurent F)) (j : Nat)
    (valid : ∀ e∈p, Valid e.2 ∧ e.2≠[]) :
    Stabilizes (fun d => weighted (truncSum (inverse q) (d+j)) p)
      (weighted (fun s => mk 0 (li q s)) p) := by
  induction p with
  | nil => exact ⟨0,fun _ => 0,0,fun _ => rfl,rfl,fun _ _ _ => rfl⟩
  | cons e p ih =>
    have he := valid e (by simp)
    exact stabilizes_add (stabilizes_term hq e.1 e.2 j he.1 he.2)
      (ih (fun z hz => valid z (List.mem_cons_of_mem _ hz)))

/-- The binary-to-CMPL lift with Laurent coefficients. The cutoff is proved
using the Cauchy product and stabilization of the literal Carlitz levels. -/
theorem laurent_binary_lift (field : ConstantField F q) (p : BinaryPair (Laurent F))
    (h : Shaped.Binary (inverse q) p)
    (valid : ∀ e∈liftPair p, Valid e.2 ∧ e.2≠[]) :
    weighted (fun s => mk 0 (li q s)) (liftPair p)=0 := by
  have hl (e) (he : e∈p.1) := valid e (List.mem_append_left _ he)
  have hr (e) (he : e∈p.2) := valid e (List.mem_append_right _ he)
  have ha := stabilizes_weighted field.two_le p.1 0 hl
  have hb := stabilizes_weighted field.two_le p.2 1 hr
  rw [liftPair,weighted_append]
  exact stabilizes_zero (stabilizes_add ha hb)
    (truncated_binary _ p ⟨fun e he => (hl e he).2,fun e he => (hr e he).2⟩ h)

end Megaera.FinalBinary
