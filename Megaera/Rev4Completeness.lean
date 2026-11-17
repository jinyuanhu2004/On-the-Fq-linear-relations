import Megaera.Rev4Selection
import Megaera.Rev4Readout
import Megaera.Rev4Survival

/-! The repaired Case II proof uses elimination beginning at the minimum
of Ind P. It applies the detector to the coefficients of the full signed
tuple combinations. -/
namespace Megaera.Rev4Completeness
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.Splitting Megaera.FourLambda
open Megaera.Triangular Megaera.FourReduction Megaera.FourMinimum
open Megaera.Rev4Selection Megaera.Rev4Negative Megaera.Rev4Pairing
variable {F : Type u} [Arithmetic F] [Neg F] {q w : Nat}

/-- Survival in Case II, for all constant fields and every weight. The
proof uses canonical rows, their order and the reduced support of the
L-component. No assumption on Case II or on the value of S appears. -/
theorem case_II_survives (field : ConstantField F q) : CaseIISurvival F q w := by
  intro e rows ord good bad _ red
  obtain ⟨r,m,v,b,f,mem,large,sameLeft,form,size,maximal⟩ := choose_marker e rows bad
  let s := e.2.val.1
  cases right : e.2.val.2 with
  | nil => exact (bad (.inl right)).elim
  | cons c t =>
    have hc := e.2.property.2.1 c (by simp [right])
    have len : (c::t).length=r+1+(v.length+1) := right ▸ size
    have bounded := fun g (hg : g∈e::rows) => (good g hg).2
    have base : rowSource e=source q s (c::t) := by simp [rowSource,s,right]
    have first (g : F × Row q w) (hg : g∈e::rows) :
        source q s (c::t)=rowSource g ∨ Precedes (source q s (c::t)) (rowSource g) := by
      rcases List.mem_cons.mp hg with rfl | hg
      · exact .inl base.symm
      · exact .inr (base ▸ (List.pairwise_cons.mp ord).1 g hg)
    have minD (a : F × Row q w) (left : a.2.val.1=s) (tail : a.2.val.2.length=(c::t).length)
        (g : F × Row q w) (hg : g∈e::rows) : (rowSource a).length≤(rowSource g).length := by
      have eq : (rowSource a).length = (source q s (c::t)).length := by
        simp only [rowSource,FourCases.source_depth,left,tail]
      rw [eq]
      rcases first g hg with eq | lt | ⟨eq,_⟩
      · rw [eq]; exact Nat.le_refl _
      · exact Nat.le_of_lt lt
      · exact Nat.le_of_eq eq
    have flen : f.2.val.2.length=(c::t).length := by
      rw [form,len]; simp; omega
    obtain ⟨_,hb,cap,edge⟩ := bounds_of_reduced field (e::rows) f mem (good f mem).1 ord
      (minD f sameLeft flen) red r m b v large form
    have initial := Rev4Readout.initial_sum field e rows f s t v c r m b ord rfl right mem
      sameLeft form len large ⟨hb,cap⟩
      (fun he => by obtain ⟨j,h,_⟩ := edge he; omega) bounded (by simpa only [right] using maximal)
      (by
        intro g hg hl ht u a eq
        obtain ⟨hcap,_,hend,_⟩ := bounds_of_reduced field (e::rows) g hg (good g hg).1 ord
          (minD g hl ht) red r m a u large eq
        exact ⟨hcap,hend⟩)
    apply Rev4Survival.survives field (e::rows) s t v c r (m+(q-1)) b hc hb cap edge
      (bounded e (by simp)) bounded first (by simpa using len)
    rw [reading_component field.two_le]
    simp only [List.append_assoc] at initial ⊢
    rw [initial]
    exact (good f mem).1

/-- Theorem 1.10 by the revised Section 4 argument. The lifted row
identity, TT independence and soundness of the BCP generators are the
earlier inputs. Both case-specific survival assertions are proved. -/
theorem theorem_1_10 (field : ConstantField F q)
    (rowLaw : ∀ e : Row q w, RowEvaluation.Identity (F:=F) q
      (withCoeff 1 (L q e.val.1 e.val.2)) (withCoeff 1 (H q e.val.1 e.val.2)))
    (tt : TTSpanning.TTPolynomialIndependent F q w)
    (sound : ∀ g : Tuple → F, BCPVector q w g → RelationVector q w g)
    (p : FormalSum F) (hp : ∀ e∈p, Valid e.2 ∧ weight e.2=w) :
    Relation q w p ↔ InBCP q w p :=
  section_four_at_weight field rowLaw tt sound (case_II_survives field) p hp

/-- The same independent proof with soundness supplied by the concrete
binary-generator identities and the lifting theorem (1.14). -/
theorem theorem_1_10_from_binary (field : ConstantField F q)
    (rowLaw : ∀ e : Row q w, RowEvaluation.Identity (F:=F) q
      (withCoeff 1 (L q e.val.1 e.val.2)) (withCoeff 1 (H q e.val.1 e.val.2)))
    (tt : TTSpanning.TTPolynomialIndependent F q w)
    (binary : ∀ u v s, Valid u → Valid v → Valid s → s≠[] →
      weight u+weight v+weight s+2*q=w → Lift.Binary (F:=F) q (bStar u (cOp v (primitive q s))))
    (p : FormalSum F) (hp : ∀ e∈p, Valid e.2 ∧ weight e.2=w) :
    Relation q w p ↔ InBCP q w p :=
  theorem_1_10 field rowLaw tt (sound_of_binary q w field binary) p hp

end Megaera.Rev4Completeness
