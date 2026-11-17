import Megaera.CompletenessProof

/-! The homogeneous marked-row presentation of ker H, Theorem 2.17.
A marked row is read against any tuple-valued test. Singleton indicator
tests distinguish each pair of labels, including an empty label. -/
namespace Megaera.FinalKernelH
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.Singletons Megaera.BCPRows
open Megaera.PureReplacement Megaera.HKernelElimination
variable {F : Type u} [Arithmetic F] [Neg F] {q w : Nat}

abbrev Test := Nat → Tuple → Tuple → List Tuple
abbrev Reading (F : Type u) := Test → Tuple → F
abbrev read (c : Rows F q w) : Reading F := fun op => component op c

def generator (q : Nat) (u s t : Tuple) : Reading F := fun op x =>
  coordinates (withCoeff 1 ((H q s t).flatMap (op q u))) x +
    -coordinates (withCoeff 1 ((longer q u s t).flatMap (fun p => op q p.1 p.2))) x

inductive Span (F : Type u) [Arithmetic F] [Neg F] (q w : Nat) : Reading F → Prop
  | zero : Span F q w (fun _ _ => 0)
  | add {a b} : Span F q w a → Span F q w b → Span F q w (fun op x => a op x + b op x)
  | scale (k : F) {a} : Span F q w a → Span F q w (fun op x => k * a op x)
  | row {u s t : Tuple} : Valid u → Valid s → Valid t → s ≠ [] →
      weight u+weight s+weight t+2*q=w → Span F q w (generator q u s t)

local instance : Std.Associative (α := F) (· + ·) := ⟨Arithmetic.addAssoc⟩
local instance : Std.Commutative (α := F) (· + ·) := ⟨Arithmetic.addComm⟩

private theorem single_marked (q w : Nat) (field : ConstantField F q) (u s t : Tuple)
    (hu : Valid u) (hs : Valid s) (ht : Valid t) (hn : s ≠ [])
    (hw : weight u+weight s+weight t+2*q=w) :
    ∃ d : Rows F q w, (∀ e ∈ d, u.length < e.2.val.1.length) ∧
      (∀ x, component H d x = coordinates (withCoeff 1 ((H q s t).flatMap (H q u))) x) ∧
      Span F q w (fun op x => coordinates (withCoeff 1 ((H q s t).flatMap (op q u))) x + (-component op d x)) := by
  let ok := fun z hz => (longer_info q w field.two_le u s t hu hs ht hn hw z hz).1
  let d := pack (1:F) (longer q u s t) ok
  refine ⟨d, fun e he => (longer_info _ _ field.two_le u s t hu hs ht hn hw _ (pack_members 1 _ ok e he)).2,?_,?_⟩
  · intro x
    rw [show component H d x = _ from pack_component H 1 _ ok x]
    exact coord_perm ((H_balance q u s t hn).map (fun a => ((1:F),a))) x
  · simpa only [generator, d, pack_component] using (Span.row (F:=F) hu hs ht hn hw)

private theorem replace_image_marked {q w n : Nat} (field : ConstantField F q) (u : Tuple)
    (hu : Valid u) (hw : weight u+n+q=w) (rows : Rows F q n)
    (pos : ∀ e ∈ rows, e.2.val.1 ≠ []) :
    ∃ d : Rows F q w, (∀ e ∈ d, u.length < e.2.val.1.length) ∧
      (∀ x, component H d x = Action H q u (RowEvaluation.presentation H rows) x) ∧
      Span F q w (fun op x => Action op q u (RowEvaluation.presentation H rows) x + (-component op d x)) := by
  induction rows with
  | nil =>
    refine ⟨[],by simp,fun _ => rfl,?_⟩
    simpa only [show (fun op x => Action op q u (RowEvaluation.presentation H ([] : Rows F q n)) x +
      (-component op ([] : Rows F q w) x)) = (fun _ _ => (0:F)) by funext op x; exact field.add_neg 0]
      using (Span.zero (F := F) (q := q) (w := w))
  | cons e rows ih =>
    obtain ⟨d,hd,hH,hL⟩ := ih (fun z hz => pos z (List.mem_cons_of_mem _ hz))
    obtain ⟨k,⟨⟨s,t⟩,hs,ht,hwt⟩⟩ := e
    change weight s+weight t+q=n at hwt
    have hn : s ≠ [] := pos (k,⟨(s,t),hs,ht,hwt⟩) (List.mem_cons_self ..)
    obtain ⟨r,hr,rH,rL⟩ := single_marked q w field u s t hu hs ht hn (by omega)
    refine ⟨scaleRows k r ++ d,?_,?_,?_⟩
    · intro z hz
      rcases List.mem_append.mp hz with h | h
      · obtain ⟨y,hy,rfl⟩ := List.mem_map.mp h; exact hr y hy
      · exact hd z h
    · intro x
      change component H (scaleRows k r++d) x = total _ (withCoeff k (H q s t) ++ _)
      rw [rows_append,scale_component,rH,hH,total_append']
      exact congrArg (· + _) (action_group H q u k (H q s t) x).symm
    · have mem := Span.add (Span.scale k rL) hL
      apply (show ∀ a b : Reading F, a=b → Span F q w b → Span F q w a from fun _ _ he h => he ▸ h) _ _ _ mem
      funext op x
      change total _ (withCoeff k (H q s t) ++ _) + (-component op (scaleRows k r++d) x) = _
      rw [total_append',show total _ (withCoeff k (H q s t)) = _ from action_group op q u k (H q s t) x,
        rows_append,scale_component,←neg_add field,Arithmetic.distrib]
      have eqneg : k*(-component op r x) = -(k*component op r x) := by
        rw [Arithmetic.mulComm k,neg_mul field,Arithmetic.mulComm]
      rw [eqneg]
      unfold Action RowEvaluation.presentation
      simp only [List.flatMap_def]
      ac_rfl

private theorem replace_pure_marked {q w n : Nat} (field : ConstantField F q) (u : Tuple)
    (hu : Valid u) (hw : weight u+n+q=w) (b : Rows F q w) (pureRows : ∀ e ∈ b, e.2.val.1=u)
    (rows : Rows F q n) (pos : ∀ e ∈ rows, e.2.val.1 ≠ [])
    (tails : component H rows = coordinates (b.map (fun e => (e.1,e.2.val.2)))) :
    ∃ d : Rows F q w, (∀ e ∈ d, u.length < e.2.val.1.length) ∧
      component H d = component H b ∧
      Span F q w (fun op x => component op b x + (-component op d x)) := by
  obtain ⟨d,hd,he,hl⟩ := replace_image_marked field u hu hw rows pos
  have matchRows (op) (x) : Action op q u (RowEvaluation.presentation H rows) x = component op b x := by
    rw [pure_action op u b pureRows]
    exact linear_form_congr (fun v => coordinates (withCoeff (1:F) (op q u v)) x) _ _
      ((RowEvaluation.coordinates_presentation H rows).trans tails)
  exact ⟨d,hd,funext (fun x => (he x).trans (matchRows H x)), by
    simpa only [matchRows] using hl⟩

private theorem replace_block_marked {q w : Nat} (field : ConstantField F q) (u : Tuple)
    (b : Rows F q w) (pureRows : ∀ e ∈ b, e.2.val.1=u)
    (inside : HPlus q (coordinates (b.map (fun e => (e.1,e.2.val.2))))) :
    ∃ d : Rows F q w, (∀ e ∈ d, u.length < e.2.val.1.length) ∧ component H d = component H b ∧
      Span F q w (fun op x => component op b x + (-component op d x)) := by
  cases b with
  | nil =>
    exact ⟨[],by simp,rfl,by simpa only [show (fun op x => component op ([] : Rows F q w) x +
      (-component op ([] : Rows F q w) x)) = (fun _ _ => (0:F)) by funext op x; exact field.add_neg 0]
      using (Span.zero (F := F) (q := q) (w := w))⟩
  | cons z zs =>
    have zu := pureRows z (by simp)
    have hwt := z.2.property.2.2
    rw [zu] at hwt
    let n := w-weight u-q
    have hw : weight u+n+q=w := by dsimp [n]; omega
    have pt : PresentedAt n ((z::zs).map (fun e => (e.1,e.2.val.2))) := by
      intro e he
      obtain ⟨y,hy,rfl⟩ := List.mem_map.mp he
      have h := y.2.property.2.2
      rw [pureRows y hy] at h
      change weight y.2.val.2=n; omega
    obtain ⟨c,cp,hc⟩ := PureWitness.witness q n field _ pt inside
    exact replace_pure_marked field u (zu ▸ z.2.property.1) hw _ pureRows c cp hc

/-- Equality of the kernel and the marked-generator span, before applying L. -/
theorem theorem_2_17 (field : ConstantField F q) (c : Rows F q w) :
    component H c = (fun _ => 0) ↔ Span F q w (read c) := by
  constructor
  · intro ker
    have pivot : PivotReflection F q w := HKernelPivot.pivot_from_reflection field
      (fun p hp => (SingletonClosure.lemma_2_14_ii q field p hp).mp)
    apply induction_on_kernel pivot (fun c => Span F q w (read c)) Span.zero _ c ker
    intro u b hb inside
    obtain ⟨d,long,subH,diff⟩ := replace_block_marked field u b hb inside
    refine ⟨d,long,subH,?_⟩
    intro r c splitc ih
    have v := Span.add diff ih
    have eqv : (fun op x => (component op b x + (-component op d x)) + component op (r++d) x) =
        read c := by
      funext op x
      change _ = component op c x
      rw [splitc,component_append]
      calc _ = (component op b x + component op r x) + (component op d x + (-component op d x)) := by ac_rfl
           _ = _ := by rw [field.add_neg,Arithmetic.addZero]
    exact eqv ▸ v
  · intro mem
    have vanishes {v : Reading F} (hv : Span F q w v) : ∀ x, v H x=0 := by
      induction hv with
      | zero => intro x; rfl
      | add _ _ ia ib => intro x; simp only [ia,ib,Arithmetic.addZero]
      | scale k _ ih => intro x; exact (congrArg (k * ·) (ih x)).trans (Arithmetic.mulZero _)
      | @row u s t hu hs ht hn hw =>
        intro x
        unfold generator
        have h := coord_perm ((H_balance q u s t hn).map (fun a => ((1:F),a))) x
        rw [show coordinates (withCoeff (1:F) ((longer q _ _ _).flatMap _)) x = _ from h]
        exact field.add_neg _
    exact funext (vanishes mem)

/-- Scalar coefficient of the marked basis vector (h,t). -/
def marked (c : Rows F q w) (ht : Tuple × Tuple) : F :=
  total (fun e => if e.2.val=ht then e.1 else 0) c

private def encode (ht : Tuple × Tuple) := ht.1.length::(ht.1++ht.2)
private def decode : Tuple → Tuple × Tuple
  | [] => ([],[])
  | n::s => (s.take n,s.drop n)

private theorem inverse_encode (ht : Tuple × Tuple) : decode (encode ht)=ht := by
  simp [decode,encode]

omit [Neg F] in
/-- Equality under all row readings is exactly equality of every marked-pair
coefficient. Thus the presentation in Theorem 2.17 is faithful. -/
theorem read_iff_marked (c d : Rows F q w) :
    read c=read d ↔ marked c=marked d := by
  constructor
  · intro eq
    funext ht
    let test : Test := fun _ h t => if (h,t)=ht then [[]] else []
    have test_eq (xs : Rows F q w) : component test xs []=marked xs ht := by
      induction xs with
      | nil => rfl
      | cons e xs ih =>
        change e.1*coordinates (withCoeff 1 (test q e.2.val.1 e.2.val.2)) []+component test xs []=_
        rw [show component test xs []=marked xs ht from ih]
        by_cases h : e.2.val=ht
        all_goals simp only [test,h,if_true,if_false,marked,total,
          withCoeff,List.map_cons,List.map_nil,coordinates,Arithmetic.addZero,
          Arithmetic.mulOne,Arithmetic.mulZero]
    exact (test_eq c).symm.trans (((congrFun (congrFun eq test) [])).trans (test_eq d))
  · intro eq
    let packRows (xs : Rows F q w) : FormalSum F := xs.map (fun e => (e.1,encode e.2.val))
    have co (xs : Rows F q w) (s : Tuple) : coordinates (packRows xs) s =
        if encode (decode s)=s then marked xs (decode s) else 0 := by
      induction xs with
      | nil => simp [packRows,marked,coordinates,total]
      | cons e xs ih =>
        change (if encode e.2.val=s then e.1 else 0)+coordinates (packRows xs) s=_
        rw [ih]
        by_cases h : encode e.2.val=s
        · subst s; simp [inverse_encode,marked,total]
        · by_cases canon : encode (decode s)=s
          · have ne : e.2.val≠decode s := fun v => h ((congrArg encode v).trans canon)
            simp only [h,canon,marked,total,ne,if_false,if_true]
          · simp only [h,canon,if_false,Arithmetic.addZero]
    have same : coordinates (packRows c)=coordinates (packRows d) := by
      funext s; rw [co,co,eq]
    funext op x
    let g := fun s => coordinates (withCoeff (1:F) (op q (decode s).1 (decode s).2)) x
    have resp (xs : Rows F q w) :
        component op xs x=total (fun e => e.1*g e.2) (packRows xs) := by
      induction xs with
      | nil => rfl
      | cons e xs ih =>
        change _+component op xs x=e.1*g (encode e.2.val)+_
        rw [ih]; simp only [g,inverse_encode]; rfl
    exact (resp c).trans ((linear_form_congr g _ _ same).trans (resp d).symm)

end Megaera.FinalKernelH
