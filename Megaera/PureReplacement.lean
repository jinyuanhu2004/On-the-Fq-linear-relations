import Megaera.GradedBCP
import Megaera.Lambda
import Megaera.Triangular
import Megaera.RowEvaluation

namespace Megaera.PureReplacement
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.Lambda Megaera.BCPRows
variable {F : Type u} [Arithmetic F] [Neg F]

def longer (q : Nat) (u s t : Tuple) : List (Tuple × Tuple) :=
  (endings u).flatMap fun z => (lambda q s t).map (fun p => (z++p.1,p.2))

private theorem lam_info (q : Nat) (hq : 2 ≤ q) (s t : Tuple) (hs : Valid s) (ht : Valid t)
    (p : Tuple × Tuple) (hp : p ∈ lambda q s t) :
    Valid p.1 ∧ Valid p.2 ∧ s.length ≤ p.1.length ∧
    weight p.1 + weight p.2 = weight s + weight t + (q-1) := by
  have hv : Valid [q-1] := by intro x hx; obtain rfl := List.mem_singleton.mp hx; omega
  rcases List.mem_append.mp hp with h | h <;> obtain ⟨v,hv',rfl⟩ := List.mem_map.mp h
  · refine ⟨valid_quasiShuffle _ _ _ hv hs hv',ht,Triangular.singleton_stuffle_depth _ _ _ hv',?_⟩
    have hh := weight_quasiShuffle _ _ _ hv'
    simp only [weight,Nat.add_zero] at hh
    dsimp; omega
  · refine ⟨hs,valid_quasiShuffle _ _ _ hv ht hv',Nat.le_refl _,?_⟩
    have hh := weight_quasiShuffle _ _ _ hv'
    simp only [weight,Nat.add_zero] at hh
    dsimp; omega

theorem longer_info (q w : Nat) (hq : 2 ≤ q) (u s t : Tuple) (hu : Valid u)
    (hs : Valid s) (ht : Valid t) (hn : s ≠ []) (hw : weight u+weight s+weight t+2*q=w)
    (p : Tuple × Tuple) (hp : p ∈ longer q u s t) : Good q w p ∧ u.length < p.1.length := by
  obtain ⟨z,hz,h'⟩ := List.mem_flatMap.mp hp
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp h'
  obtain ⟨hv,hv',hlen,hw'⟩ := lam_info q hq s t hs ht x hx
  have zw := endings_weight u z hz
  have zv := endings_valid u hu z hz
  have le : u.length ≤ z.length := by
    cases u with
    | nil => exact Nat.zero_le _
    | cons a l =>
      rcases (by simpa [endings] using hz : z=incLast (a::l) ∨ z=(a::l)++[1]) with rfl | rfl
      · rw [Triangular.incLast_length]; exact Nat.le_refl _
      · simp
  have sl := List.length_pos_iff.mpr hn
  refine ⟨⟨fun i hi => (List.mem_append.mp hi).elim (zv i) (hv i),hv',?_⟩,?_⟩
  · change weight (z++x.1)+weight x.2+q=w
    rw [weight_append]; omega
  · change u.length < (z++x.1).length
    rw [List.length_append]; omega

theorem H_balance (q : Nat) (u s t : Tuple) (hn : s ≠ []) :
    ((longer q u s t).flatMap (fun p => H q p.1 p.2)).Perm
      ((H q s t).flatMap (H q u)) := by
  apply List.Perm.trans _ (PrimitiveRows.collect_by_prefix (endings u) (quasiShuffle [q-1]) (H q s t)).symm
  simp only [longer,List.flatMap_assoc,List.flatMap_map,Function.comp_def,concatenate]
  generalize endings u = zs
  induction zs with
  | nil => exact .nil
  | cons z zs ih =>
    apply List.Perm.append _ ih
    have replace : ((lambda q s t).flatMap (fun p => H q (z++p.1) p.2)) =
        ((lambda q s t).flatMap (fun p => (H q p.1 p.2).map (z++·))) := by
      apply congrArg List.flatten
      apply List.map_congr_left
      intro p hp
      have hn' : p.1 ≠ [] := by
        rcases List.mem_append.mp hp with h | h <;> obtain ⟨v,hv,rfl⟩ := List.mem_map.mp h
        · have le := Triangular.singleton_stuffle_depth _ _ _ hv
          intro he; change v=[] at he; rw [he] at le
          exact hn (List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero le))
        · exact hn
      cases eq : p.1 with
      | nil => exact (hn' eq).elim
      | cons a l => exact PrimitiveRows.H_prepend_nonempty _ _ _ _ _
    dsimp only
    rw [replace,←List.map_flatMap]
    exact (H_lambda q s t).map (z++·)

omit [Arithmetic F] [Neg F] in
theorem pack_members {q w : Nat} (k : F) (xs : List (Tuple × Tuple)) (ok : ∀ z ∈ xs, Good q w z)
    (e : F × Row q w) (he : e ∈ pack k xs ok) : e.2.val ∈ xs := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    rcases List.mem_cons.mp he with rfl | he
    · simp
    · exact List.mem_cons_of_mem _ (ih _ he)

theorem single (q w : Nat) (field : ConstantField F q) (u s t : Tuple)
    (hu : Valid u) (hs : Valid s) (ht : Valid t) (hn : s ≠ [])
    (hw : weight u+weight s+weight t+2*q=w) :
    ∃ d : Rows F q w, (∀ e ∈ d, u.length < e.2.val.1.length) ∧
      (∀ x, component H d x = coordinates (withCoeff 1 ((H q s t).flatMap (H q u))) x) ∧
      BCPVector q w (fun x => coordinates (withCoeff 1 ((H q s t).flatMap (L q u))) x + (-component L d x)) := by
  let ok := fun z hz => (longer_info q w field.two_le u s t hu hs ht hn hw z hz).1
  let d := pack (1:F) (longer q u s t) ok
  refine ⟨d, fun e he => (longer_info _ _ field.two_le u s t hu hs ht hn hw _ (pack_members 1 _ ok e he)).2,?_,?_⟩
  · intro x
    rw [show component H d x = _ from pack_component H 1 _ ok x]
    exact coord_perm ((H_balance q u s t hn).map (fun a => ((1:F),a))) x
  · have eq : (fun x => coordinates (withCoeff (1:F) ((H q s t).flatMap (L q u))) x + (-component L d x)) =
        coordinates (liftPair (bStar u (generalP q s t))) := by
      funext x
      have h := coord_perm (syzygyL (K := F) q u s t) x
      rw [coord_append,coeff_scale (-(1:F)),neg_mul field,oneMul] at h
      rw [←h,show component L d x = _ from pack_component L 1 _ ok x]
      simp only [longer,List.flatMap_assoc,List.flatMap_map,Function.comp_def]
    rw [eq]
    exact GradedBCP.generalP_mem q w field u s t hu hs ht hn hw

abbrev Action (op : Nat → Tuple → Tuple → List Tuple) (q : Nat) (u : Tuple)
    (p : FormalSum F) (x : Tuple) : F :=
  total (fun e : F × Tuple => e.1 * coordinates (withCoeff (1:F) (op q u e.2)) x) p

omit [Neg F] in
theorem action_group (op : Nat → Tuple → Tuple → List Tuple) (q : Nat) (u : Tuple)
    (k : F) (ys : List Tuple) (x : Tuple) :
    Action op q u (withCoeff k ys) x = k*coordinates (withCoeff (1:F) (ys.flatMap (op q u))) x := by
  induction ys with
  | nil => exact (Arithmetic.mulZero _).symm
  | cons y ys ih =>
    simp only [List.flatMap_cons,withCoeff,List.map_append,List.map_cons]
    change k*_+Action op q u (withCoeff k ys) x = k*coordinates (_++_) x
    rw [coord_append,Arithmetic.distrib,ih]; rfl

local instance : Std.Associative (α := F) (· + ·) := ⟨Arithmetic.addAssoc⟩
local instance : Std.Commutative (α := F) (· + ·) := ⟨Arithmetic.addComm⟩

/-- Replace the left label u by strictly longer labels after choosing a positive
row preimage of its tail. The entire construction stays at weight w. -/
theorem replace_image {q w n : Nat} (field : ConstantField F q) (u : Tuple)
    (hu : Valid u) (hw : weight u+n+q=w) (rows : Rows F q n)
    (pos : ∀ e ∈ rows, e.2.val.1 ≠ []) :
    ∃ d : Rows F q w, (∀ e ∈ d, u.length < e.2.val.1.length) ∧
      (∀ x, component H d x = Action H q u (RowEvaluation.presentation H rows) x) ∧
      BCPVector q w (fun x => Action L q u (RowEvaluation.presentation H rows) x + (-component L d x)) := by
  induction rows with
  | nil =>
    refine ⟨[],by simp,fun _ => rfl,?_⟩
    simpa only [show (fun x => Action L q u (RowEvaluation.presentation H ([] : Rows F q n)) x +
      (-component L ([] : Rows F q w) x)) = (fun _ => (0:F)) by funext x; exact field.add_neg 0]
      using (GradedBCP.zero_mem (F := F) (q := q) (w := w))
  | cons e rows ih =>
    obtain ⟨d,hd,hH,hL⟩ := ih (fun z hz => pos z (List.mem_cons_of_mem _ hz))
    obtain ⟨k,⟨⟨s,t⟩,hs,ht,hwt⟩⟩ := e
    change weight s+weight t+q=n at hwt
    have hn : s ≠ [] := pos (k,⟨(s,t),hs,ht,hwt⟩) (List.mem_cons_self ..)
    obtain ⟨r,hr,rH,rL⟩ := single q w field u s t hu hs ht hn (by omega)
    refine ⟨scaleRows k r ++ d,?_,?_,?_⟩
    · intro z hz
      rcases List.mem_append.mp hz with h | h
      · obtain ⟨y,hy,rfl⟩ := List.mem_map.mp h; exact hr y hy
      · exact hd z h
    · intro x
      change component H (scaleRows k r++d) x = total _ (withCoeff k (H q s t) ++ _)
      rw [rows_append,scale_component,rH,hH,total_append']
      exact congrArg (· + _) (action_group H q u k (H q s t) x).symm
    · have mem := GradedBCP.add_mem (GradedBCP.scale_mem k rL) hL
      apply (show ∀ a b : Tuple → F, a=b → BCPVector q w b → BCPVector q w a from fun _ _ he h => he ▸ h) _ _ _ mem
      funext x
      change total _ (withCoeff k (H q s t) ++ _) + (-component L (scaleRows k r++d) x) = _
      rw [total_append',show total _ (withCoeff k (H q s t)) = _ from action_group L q u k (H q s t) x,
        rows_append,scale_component,←neg_add field,Arithmetic.distrib]
      have eqneg : k*(-component L r x) = -(k*component L r x) := by
        rw [Arithmetic.mulComm k,neg_mul field,Arithmetic.mulComm]
      rw [eqneg]
      unfold Action RowEvaluation.presentation
      simp only [List.flatMap_def]
      ac_rfl

omit [Neg F] in
theorem pure_action {q w : Nat} (op : Nat → Tuple → Tuple → List Tuple) (u : Tuple)
    (b : Rows F q w) (pureRows : ∀ e ∈ b, e.2.val.1=u) (x : Tuple) :
    component op b x = Action op q u (b.map (fun e => (e.1,e.2.val.2))) x := by
  induction b with
  | nil => rfl
  | cons e b ih =>
    change e.1*coordinates (withCoeff 1 (op q e.2.val.1 e.2.val.2)) x + component op b x =
      e.1*coordinates (withCoeff 1 (op q u e.2.val.2)) x + _
    rw [pureRows e (by simp),ih (fun z hz => pureRows z (by simp [hz]))]

theorem replace_pure {q w n : Nat} (field : ConstantField F q) (u : Tuple)
    (hu : Valid u) (hw : weight u+n+q=w) (b : Rows F q w) (pureRows : ∀ e ∈ b, e.2.val.1=u)
    (rows : Rows F q n) (pos : ∀ e ∈ rows, e.2.val.1 ≠ [])
    (tails : component H rows = coordinates (b.map (fun e => (e.1,e.2.val.2)))) :
    ∃ d : Rows F q w, (∀ e ∈ d, u.length < e.2.val.1.length) ∧
      component H d = component H b ∧
      BCPVector q w (fun x => component L b x + (-component L d x)) := by
  obtain ⟨d,hd,he,hl⟩ := replace_image field u hu hw rows pos
  have matchRows (op) (x) : Action op q u (RowEvaluation.presentation H rows) x = component op b x := by
    rw [pure_action op u b pureRows]
    exact linear_form_congr (fun v => coordinates (withCoeff (1:F) (op q u v)) x) _ _
      ((RowEvaluation.coordinates_presentation H rows).trans tails)
  exact ⟨d,hd,funext (fun x => (he x).trans (matchRows H x)), by
    simpa only [matchRows] using hl⟩

end Megaera.PureReplacement
