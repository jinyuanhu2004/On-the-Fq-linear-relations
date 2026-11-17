import Megaera.FinalDegreeOne

/-! Append lifted basis vectors for the image of the constant projection
to basis vectors for its kernel. The result includes uniqueness of all
coordinates in the concrete degree-one space. -/
namespace Megaera.FinalBasisRanks
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.SectionThreeSpaces
open Megaera.FinalDegreeOne Megaera.TTSpanning
variable {F : Type u} [Arithmetic F] [Neg F] {q w : Nat}

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

private def rowPair (c : Rows F q w) (i : Bool × Tuple) : F :=
  if i.1 then component H c i.2 else component L c i.2

private theorem u_rows (field : ConstantField F q) (rowLaw : CompletenessProof.LiftedRowIdentity F q)
    (tt : ∀ j, 0<j → TTPolynomialIndependent F q j) (hw : 0<w)
    (x : Bool × Tuple → F) : U q w x ↔ ∃ c : Rows F q w,x=rowPair c := by
  rw [lemma_3_1 field rowLaw tt hw]
  constructor
  · rintro ⟨c,eq⟩
    refine ⟨c,funext (fun ⟨b,s⟩ => ?_)⟩
    cases b
    · exact (eq s).1
    · exact (eq s).2
  · rintro ⟨c,rfl⟩; exact ⟨c,fun s => ⟨rfl,rfl⟩⟩

private theorem u_linear (field : ConstantField F q) (rowLaw : CompletenessProof.LiftedRowIdentity F q)
    (tt : ∀ j, 0<j → TTPolynomialIndependent F q j) (hw : 0<w)
    (x y : Bool × Tuple → F) (a : F) (hx : U q w x) (hy : U q w y) :
    U q w (fun i => x i+a*y i) := by
  obtain ⟨c,rfl⟩ := (u_rows field rowLaw tt hw x).mp hx
  obtain ⟨d,rfl⟩ := (u_rows field rowLaw tt hw y).mp hy
  apply (u_rows field rowLaw tt hw _).mpr
  refine ⟨c++BCPRows.scaleRows a d,funext (fun ⟨b,s⟩ => ?_)⟩
  cases b <;> simp [rowPair,component_append,BCPRows.scale_component]

private theorem u_synthesis (field : ConstantField F q) (rowLaw : CompletenessProof.LiftedRowIdentity F q)
    (tt : ∀ j, 0<j → TTPolynomialIndependent F q j) (hw : 0<w)
    {n : Nat} (basis : Fin n → Bool × Tuple → F) (c : Fin n → F) (members : ∀ j,U q w (basis j)) :
    U q w (synthesis basis c) := by
  have zero : U (F:=F) q w (fun _ => 0) :=
    (u_rows field rowLaw tt hw _).mpr ⟨[],funext (fun ⟨b,s⟩ => by cases b <;> rfl)⟩
  unfold synthesis
  generalize List.finRange n = is
  induction is with
  | nil => exact zero
  | cons j is ih =>
    simpa only [Arithmetic.addComm] using u_linear field rowLaw tt hw _ _ (c j) ih (members j)

omit [Neg F] in
private theorem pure_constant {n : Nat} (basis : Fin n → Tuple → F) (c : Fin n → F) (s : Tuple) :
    synthesis (fun j => timesD1 (basis j)) c (false,s)=0 := by
  apply total_zero_of_members
  intro j _
  exact Arithmetic.mulZero _

/-- Corollary 3.2 for basis dimensions. Given bases of L_w and R_w,
there is a basis of U_w of their combined size. -/
theorem corollary_3_2 (field : ConstantField F q) (rowLaw : CompletenessProof.LiftedRowIdentity F q)
    (tt : ∀ j, 0<j → TTPolynomialIndependent F q j) (hw : 0<w) {l r : Nat}
    (ld : HasDimension (fun v => ∃ rows : Rows F q w,component L rows=v) l)
    (rd : HasDimension (RelationVector (F:=F) q w) r) : HasDimension (U (F:=F) q w) (l+r) := by
  classical
  obtain ⟨lb,lb_mem,lb_basis⟩ := ld
  obtain ⟨rb,rb_mem,rb_basis⟩ := rd
  let lift : Fin l → Rows F q w := fun j => Classical.choose (lb_mem j)
  have left (j : Fin l) : component L (lift j)=lb j := Classical.choose_spec (lb_mem j)
  let ext := fun j => rowPair (lift j)
  let ins := fun j => timesD1 (rb j)
  have ext_mem (j : Fin l) : U q w (ext j) :=
    (u_rows field rowLaw tt hw _).mpr ⟨lift j,rfl⟩
  have ins_mem (j : Fin r) : U q w (ins j) := (projection_kernel q w field.two_le _).mpr (rb_mem j)
  have ext_const (j : Fin l) (s : Tuple) : ext j (false,s)=lb j s := congrFun (left j) s
  have proj (c : Fin l → F) (s : Tuple) : synthesis ext c (false,s)=synthesis lb c s := by
    simp only [synthesis,ext_const]
  have read_l (c : Fin (l+r) → F) (s : Tuple) :
      synthesis (joinFin ext ins) c (false,s)=synthesis lb (fun j => c (Fin.castAdd r j)) s := by
    rw [synth_split,proj,show synthesis ins _ (false,s)=0 from pure_constant ..,Arithmetic.addZero]
  have read_r (c : Fin (l+r) → F) (s : Tuple) :
      synthesis (joinFin ext ins) c (true,s)=synthesis ext (fun j => c (Fin.castAdd r j)) (true,s)+
      synthesis rb (fun j => c (Fin.natAdd l j)) s := by rw [synth_split]; rfl
  refine ⟨joinFin ext ins,?_,?_⟩
  · intro i; induction i using Fin.addCases with
    | left j => simpa using ext_mem j
    | right j => simpa using ins_mem j
  · intro x hx
    have im : ∃ rows : Rows F q w,component L rows = fun s => x (false,s) :=
      (projection_image field rowLaw tt hw _).mp ⟨x,hx,fun _ => rfl⟩
    obtain ⟨a,ea,ua⟩ := lb_basis _ im
    let y := synthesis ext a
    have hy : U q w y := u_synthesis field rowLaw tt hw ext a ext_mem
    let k := fun s => x (true,s) + -(y (true,s))
    have inKernel : U q w (timesD1 k) := by
      have eq : timesD1 k = fun i => x i+(-1)*y i := by
        funext ⟨b,s⟩
        cases b
        · change 0=x (false,s)+(-1)*synthesis ext a (false,s)
          rw [proj,ea,neg_mul field,oneMul]
          exact (field.add_neg _).symm
        · simp [k,timesD1,neg_mul field,oneMul]
      rw [eq]; exact u_linear field rowLaw tt hw _ _ _ hx hy
    obtain ⟨b,eb,ub⟩ := rb_basis _ ((projection_kernel q w field.two_le _).mp inKernel)
    refine ⟨joinFin a b,?_,?_⟩
    · rintro ⟨bit,s⟩
      cases bit
      · change _=synthesis (joinFin ext ins) _ (false,s)
        simpa only [read_l,join_left] using ea s
      · change _=synthesis (joinFin ext ins) _ (true,s)
        simp only [read_r,join_left,join_right]
        rw [←show k s=synthesis rb b s from eb s]
        change x (true,s) = y (true,s)+(x (true,s)+ -y (true,s))
        rw [Arithmetic.addComm (x (true,s)),←Arithmetic.addAssoc,field.add_neg,zeroAdd]
    · intro d ed
      have dl : (fun j => d (Fin.castAdd r j))=a := ua _ (fun s => (ed (false,s)).trans (read_l d s))
      have dr : (fun j => d (Fin.natAdd l j))=b := by
        apply ub
        intro s
        have e := (ed (true,s)).trans (read_r d s)
        rw [dl] at e
        change k s=_
        unfold k
        rw [e,Arithmetic.addComm (y (true,s)),Arithmetic.addAssoc,field.add_neg,Arithmetic.addZero]
        rfl
      funext i
      induction i using Fin.addCases with
      | left j => exact (congrFun dl j).trans (join_left a b j).symm
      | right j => exact (congrFun dr j).trans (join_right a b j).symm

end Megaera.FinalBasisRanks
