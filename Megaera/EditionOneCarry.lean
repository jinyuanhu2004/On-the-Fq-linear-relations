import Megaera.FinalKernelL
import Megaera.EditionOneFour

/-! Equation (1.16) and Remark 2.14, derived using the manuscript's
binary generators and marked-row identities. -/
namespace Megaera.EditionOneCarry
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.BCPRows
variable {F : Type u} [Arithmetic F] [Neg F] {q w : Nat}

/-- The right label v is r₂::t for an interior mark and [] for a terminal
mark. The two choices of the first split supply the four positive blocks.
The negative blocks combine each allowed ending of h with each allowed
split of the second mark. All shuffle multiplicities are retained. -/
def quadruple (q : Nat) (h : Tuple) (r : Nat) (m v : Tuple) : FormalSum F :=
  let tail := quasiShuffle [q-1] v
  let positive (z : Tuple) := (concatenate (endings z) tail).map (h++·)
  let negative := (start q v).flatMap fun z =>
    concatenate (endings h) (quasiShuffle [q-1] ((r::m)++z))
  withCoeff 1 (positive (q::r::m) ++ positive ((q+r)::m)) ++ withCoeff (-1) negative

/-- The quadruple-carry expression is the lifted generalized primitive,
including either choice of the right mark and an empty outer prefix. -/
theorem quadruple_eq (q : Nat) (h : Tuple) (r : Nat) (m v : Tuple) :
    (quadruple (F:=F) q h r m v).Perm (liftPair (bStar h (generalP q (r::m) v))) := by
  have cert := (PrimitiveRows.bStar_generalP_row_certificate (K:=F) q r h m v).2
  apply List.Perm.trans _ cert
  apply List.Perm.of_eq
  simp only [quadruple,start,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    L,List.flatMap_map,Function.comp_def]
  rw [PrimitiveRows.H_prepend_nonempty,PrimitiveRows.H_prepend_nonempty]; rfl

/-- Lemma 1.8, including the interior and terminal right marks. The lifted row
identity proves vanishing of the Carlitz value without TT independence. -/
theorem lemma_1_8 (field : ConstantField F q) (h : Tuple) (r : Nat) (m v : Tuple)
    (hh : Valid h) (hs : Valid (r::m)) (hv : Valid v) :
    Relation q (weight h+weight (r::m)+weight v+2*q) (quadruple (F:=F) q h r m v) := by
  let w := weight h+weight (r::m)+weight v+2*q
  have perm := quadruple_eq (F:=F) q h r m v
  have hq := field.two_le
  have val := bStar_valid h _ hh (generalP_valid (K:=F) q hq _ _ hs hv)
  have wt := bStar_weight h _ _ (generalP_weight (K:=F) q (by omega) (r::m) v)
  have hom (e : F × Tuple) (he : e∈quadruple q h r m v) : Valid e.2 ∧ weight e.2=w := by
    have mem := List.mem_append.mp (perm.mem_iff.mp he)
    have := mem.elim (wt.1 e) (wt.2 e)
    exact ⟨mem.elim (val.1 e) (val.2 e),by dsimp [w]; omega⟩
  apply (relation_iff_vector q w _ hom).mpr
  obtain ⟨c,left,right⟩ := primitive_mem q w field h (r::m) v hh hs hv (by simp) rfl
  rw [funext (coord_perm perm),← right]
  apply RowEvaluation.relation_H_of_relation_L field c
    (RowEvaluation.rows_identity c (fun e _ => FinalBinary.row_identity field _ _ e.2.property.1 e.2.property.2.1))
  rw [left]
  exact ⟨[],⟨by simp,fun _ => rfl⟩,rfl⟩

/-- The F-linear span of the actual signed lists in (1.16). -/
inductive CarrySpan (F : Type u) [Arithmetic F] [Neg F] (q w : Nat) : (Tuple → F) → Prop
  | zero : CarrySpan F q w (fun _ => 0)
  | add {a b} : CarrySpan F q w a → CarrySpan F q w b → CarrySpan F q w (fun s => a s+b s)
  | scale (k : F) {a} : CarrySpan F q w a → CarrySpan F q w (fun s => k*a s)
  | atom (h : Tuple) (r : Nat) (m v : Tuple) : Valid h → Valid (r::m) → Valid v →
      weight h+weight (r::m)+weight v+2*q=w →
      CarrySpan F q w (coordinates (quadruple q h r m v))

private theorem sum_mem {A : Type v} (l : List A) (f : A → Tuple → F)
    (mem : ∀ a∈l, CarrySpan F q w (f a)) : CarrySpan F q w (fun s => total (fun a => f a s) l) := by
  induction l with
  | nil => exact .zero
  | cons a l ih => exact .add (mem a (by simp)) (ih (fun b hb => mem b (List.mem_cons_of_mem _ hb)))

private theorem generator_in_carries (h s t : Tuple) (hh : Valid h) (vs : Valid s)
    (vt : Valid t) (ne : s≠[]) (hw : weight h+weight t+weight s+2*q=w) :
    CarrySpan F q w (coordinates (bcpGenerator q h t s)) := by
  let read (a b : Tuple) := coordinates (liftPair (bStar h (generalP (K:=F) q a b)))
  have eq : coordinates (bcpGenerator (K:=F) q h t s)=
      (fun u => total (fun p => total (fun x => read x p.2 u) (quasiShuffle s p.1)) (Cuts.cuts t)) := by
    funext u
    exact (Convolution.read_convolution (prefixed_read (F:=F) h u) zeroAdd Arithmetic.addAssoc q s t).trans
      (by simp only [BCPRows.rowsSum,read])
  rw [eq]
  apply sum_mem; intro p cut
  apply sum_mem; intro x hx
  have join := Cuts.pieces_append cut
  have vp : Valid p.1 := fun a ha => vt a (join ▸ List.mem_append_left _ ha)
  have vb : Valid p.2 := fun a ha => vt a (join ▸ List.mem_append_right _ ha)
  have vx := valid_quasiShuffle _ _ _ vs vp hx
  have wx := weight_quasiShuffle _ _ _ hx
  have wt := congrArg weight join
  rw [weight_append] at wt
  have pos : 0<weight s := by cases s with
    | nil => contradiction
    | cons a s => have := vs a (by simp); simp only [weight]; omega
  cases x with
  | nil => simp only [weight] at wx; omega
  | cons r m =>
    have same := funext (coord_perm (quadruple_eq (F:=F) q h r m p.2))
    unfold read
    rw [← same]
    exact CarrySpan.atom h r m p.2 hh vx vb (by omega)

theorem bcp_iff_carry (field : ConstantField F q) (v : Tuple → F) :
    BCPVector q w v ↔ CarrySpan F q w v := by
  constructor
  · rintro ⟨p,⟨rows,valid,rep⟩,rfl⟩
    rw [funext rep]; apply sum_mem; intro e he
    obtain ⟨hh,ht,hs,ne,wt⟩ := valid e he
    exact .scale e.1 (generator_in_carries _ _ _ hh hs ht ne wt)
  · intro h
    induction h with
    | zero => exact GradedBCP.zero_mem
    | add _ _ ia ib => exact GradedBCP.add_mem ia ib
    | scale k _ ih => exact GradedBCP.scale_mem k ih
    | atom h r m t hh hs ht wt =>
      rw [funext (coord_perm (quadruple_eq (F:=F) q h r m t))]
      exact GradedBCP.generalP_mem q w field h (r::m) t hh hs ht (by simp) wt

/-- The new assertion in Remark 2.14 is a purely algebraic span equality. -/
theorem remark_2_14 {K : Type} [Arithmetic K] [Neg K] (field : ConstantField K q) (v : Tuple → K) :
    InImage q w v ↔ CarrySpan K q w v :=
  (FinalKernelL.theorem_2_13 field v).symm.trans (bcp_iff_carry field v)

/-- The statement of 1.9(iii) follows independently from the second
completeness proof and the explicitly verified quadruple-carry expansion. -/
theorem relation_iff_carry (field : ConstantField F q) (tt : TTSpanning.TTPolynomialIndependent F q w)
    (p : FormalSum F) (hp : ∀ e∈p,Valid e.2 ∧ weight e.2=w) :
    Relation q w p ↔ CarrySpan F q w (coordinates p) :=
  (EditionOneFour.theorem_1_10 field tt p hp).trans
    ((bcp_iff_vector q w p).trans (bcp_iff_carry field _))

end Megaera.EditionOneCarry
