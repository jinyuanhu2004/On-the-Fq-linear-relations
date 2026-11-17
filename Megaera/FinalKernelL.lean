import Megaera.CoordinateKernel
import Megaera.GradedBCP

/-! Both directions of Theorem 2.13 in the concrete coefficient space. -/
namespace Megaera.FinalKernelL
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.BCPRows
open Megaera.IntegralKernel Megaera.CoordinateKernel
variable {F : Type} [Arithmetic F] [Neg F] {q w : Nat}
local instance : Std.Associative (α := F) (· + ·) := ⟨Arithmetic.addAssoc⟩
local instance : Std.Commutative (α := F) (· + ·) := ⟨Arithmetic.addComm⟩

private def hrow (q : Nat) (h t : Tuple) : Tuple → F :=
  coordinates (withCoeff 1 (H q h t))

private def readH (q : Nat) : Word (F × Mark) → Tuple → F
  | .zero, _ => 0
  | .atom (k,h,t), s => k*hrow q h t s
  | .plus x y, s => readH q x s + readH q y s
  | .minus x y, s => readH q x s + -(readH q y s)

/-- Evaluating a relation modulo the BCP space amounts to recording
a BCP vector which takes one side to the other by addition. -/
private def congruent (q w : Nat) (x y : Tuple → F) : Prop :=
  ∃ z, BCPVector q w z ∧ ∀ s, x s+z s=y s

private theorem of_equal {x y : Tuple → F} (e : ∀ s,x s=y s) : congruent q w x y :=
  ⟨_,GradedBCP.zero_mem,fun s => (Arithmetic.addZero _).trans (e s)⟩

private theorem cancel (field : ConstantField F q) (a b : F) : (a+b)+(-b)=a := by
  rw [Arithmetic.addAssoc,field.add_neg,Arithmetic.addZero]

private theorem sub_add (field : ConstantField F q) (a b : F) : (a+(-b))+b=a := by
  rw [Arithmetic.addAssoc,Arithmetic.addComm (-b),field.add_neg,Arithmetic.addZero]

/-- The certificate used at every local square and terminal triangle. Its
positive list moves the first mark right and its negative list keeps it left. -/
private theorem local_certificate (field : ConstantField F q) (h m v : Tuple) (r : Nat) (k : F)
    (hh : Valid h) (hm : Valid m) (hr : 0<r) (hv : Valid v)
    (hw : weight h+weight (r::m)+weight v+2*q=w) :
    congruent q w
      (fun x => k * coordinates (withCoeff 1 ((L q (r::m) v).flatMap (H q h))) x)
      (fun x => k * coordinates (withCoeff 1 ((start q (r::m)).flatMap (fun a => H q (h++a) v))) x) := by
  have vs : Valid (r::m) := by
    intro i hi; rcases List.mem_cons.mp hi with rfl | hi
    · exact hr
    · exact hm i hi
  have gen := GradedBCP.generalP_mem q w field h (r::m) v hh vs hv (by simp) hw
  refine ⟨_,GradedBCP.scale_mem k gen,?_⟩
  intro x
  have cert := coord_perm (PrimitiveRows.bStar_generalP_row_certificate (K:=F) q r h m v).2 x
  rw [←cert,coord_append,coeff_scale (-(1:F)),neg_mul field,oneMul,←Arithmetic.distrib]
  apply congrArg (k*·)
  rw [Arithmetic.addComm,sub_add field]

private theorem local_step (field : ConstantField F q) {x y : Word (F × Mark)}
    (rule : ScalarKernel.RowsAt F q w x y) : congruent q w (readH q x) (readH q y) := by
  obtain ⟨rule,wx,_⟩ := rule
  cases rule with
  | collect h =>
    apply of_equal
    intro s
    cases h with
    | zero p => rcases p with ⟨h,t⟩; exact zeroMul _
    | add a b p =>
      rcases p with ⟨h,t⟩
      change (a+b)*_ = a*_+b*_
      rw [Arithmetic.mulComm,Arithmetic.distrib]
      rw [Arithmetic.mulComm a,Arithmetic.mulComm b]
  | square k p m t r c hp hm ht hr hc =>
    have hw := wx.1
    change weight p+q+weight (r::(m++(q+c)::t))=w at hw
    have vc : Valid (c::t) := by
      intro j hj; rcases List.mem_cons.mp hj with rfl | hj
      · exact hc
      · exact ht j hj
    have eq := local_certificate (w:=w) field p m (c::t) r k hp hm hr vc
      (by simp only [weight,weight_append] at hw ⊢; omega)
    simpa only [L,start,List.map_cons,List.map_nil,List.flatMap_cons,List.flatMap_nil,
      List.append_nil,List.cons_append,withCoeff,List.map_append,coord_append,Arithmetic.distrib,
      readH,hrow,Arithmetic.addComm] using eq
  | triangle k p m r hp hm hr =>
    change weight p+q+weight (r::(m++[q]))=w at wx
    have eq := local_certificate (w:=w) field p m [] r k hp hm hr (by simp [Valid])
      (by simp only [weight,weight_append] at wx ⊢; omega)
    simpa only [L,start,List.map_cons,List.map_nil,List.flatMap_cons,List.flatMap_nil,
      List.append_nil,List.cons_append,withCoeff,List.map_append,coord_append,Arithmetic.distrib,
      readH,hrow,Arithmetic.addComm] using eq

private theorem respects (field : ConstantField F q) {x y : Word (F × Mark)}
    (d : Derives (ScalarKernel.RowsAt F q w) x y) : congruent q w (readH q x) (readH q y) := by
  induction d with
  | refl => exact of_equal (fun _ => rfl)
  | symm _ ih =>
    obtain ⟨e,inside,he⟩ := ih
    exact ⟨_,GradedBCP.neg_mem field inside,fun s => by rw [←he, cancel field]⟩
  | trans _ _ ih ik =>
    obtain ⟨a,ha,ea⟩ := ih
    obtain ⟨b,hb,eb⟩ := ik
    exact ⟨_,GradedBCP.add_mem ha hb,fun s => by rw [←Arithmetic.addAssoc,ea,eb]⟩
  | plus _ _ ih ik =>
    obtain ⟨a,ha,ea⟩ := ih
    obtain ⟨b,hb,eb⟩ := ik
    refine ⟨_,GradedBCP.add_mem ha hb,fun s => ?_⟩
    simp only [readH,←ea,←eb]; ac_rfl
  | minus _ _ ih ik =>
    obtain ⟨a,ha,ea⟩ := ih
    obtain ⟨b,hb,eb⟩ := ik
    refine ⟨_,GradedBCP.sub_mem field ha hb,fun s => ?_⟩
    simp only [readH,←ea,←eb,←neg_add field]; ac_rfl
  | assoc => exact of_equal (fun _ => Arithmetic.addAssoc ..)
  | comm => exact of_equal (fun _ => Arithmetic.addComm ..)
  | addZero => exact of_equal (fun _ => Arithmetic.addZero _)
  | subAdd => exact of_equal (fun _ => sub_add field ..)
  | addSub => exact of_equal (fun _ => cancel field ..)
  | collect =>
    apply of_equal
    intro s
    simp only [readH,←neg_add field]; ac_rfl
  | rule h => exact local_step field h

private theorem read_rows (c : Rows F q w) (s : Tuple) :
    readH q (rowWord c) s = component H c s := by
  induction c with
  | nil => rfl
  | cons e c ih =>
    rcases e with ⟨k,⟨⟨h,t⟩,valid⟩⟩
    exact congrArg (k*hrow q h t s+·) ih

/-- Every homogeneous row in the kernel of L has H-image in the BCP span. -/
theorem H_ker_L_in_bcp (field : ConstantField F q) (c : Rows F q w)
    (zeroL : ∀ s,component L c s=0) : BCPVector q w (component H c) := by
  have d := derive_kernel_rows (by have := field.two_le; omega) c zeroL
  obtain ⟨e,inside,eq⟩ := respects field d
  have same : component H c = fun s => -e s := by
    funext s
    have h := eq s
    rw [read_rows] at h
    change component H c s+e s=0 at h
    calc
      _ = (component H c s+e s)+(-e s) := (cancel field ..).symm
      _ = _ := by rw [h,zeroAdd]
  exact same ▸ GradedBCP.neg_mem field inside

/-- Theorem 2.13 as equality of membership at weight w, for the nonempty
primitive labels generating the BCP space. -/
theorem theorem_2_13 (field : ConstantField F q) (v : Tuple → F) :
    BCPVector q w v ↔ BCPRows.InImage q w v := by
  refine ⟨bcp_in_H_ker_L q w field v,?_⟩
  rintro ⟨c,h,rfl⟩
  exact H_ker_L_in_bcp field c (fun s => congrFun h s)

end Megaera.FinalKernelL
