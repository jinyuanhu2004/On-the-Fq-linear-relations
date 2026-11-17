import Megaera.HKernelElimination

/-! Extract the least-depth pivot of an H-kernel. Reading the tuple prefix
obtained by increasing its last entry leaves exactly the singleton stuffle
of its tail block modulo the positive-prefix row span. -/
namespace Megaera.HKernelPivot
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.Singletons Megaera.HKernelElimination
open Megaera.BCPRows
variable {F : Type u} [Arithmetic F] [Neg F] {q w : Nat}
local instance : Std.Associative (α := F) (· + ·) := ⟨Arithmetic.addAssoc⟩
local instance : Std.Commutative (α := F) (· + ·) := ⟨Arithmetic.addComm⟩

private theorem inc_snoc (p : Tuple) (a : Nat) : incLast (p++[a])=p++[a+1] := by
  induction p with
  | nil => rfl
  | cons b p ih => cases p <;> simp_all [incLast]

private theorem inc_len (u : Tuple) : (incLast u).length=u.length := by
  by_cases hu : u=[]
  · simp [hu,incLast]
  · obtain ⟨p,a,h⟩ : ∃ p a, u=p++[a] :=
      ⟨u.dropLast,u.getLast hu,(List.dropLast_concat_getLast hu).symm⟩
    rw [h,inc_snoc]; simp

private theorem inc_inj (u v : Tuple) (hu : u ≠ []) (hv : v ≠ []) (he : incLast u=incLast v) : u=v := by
  obtain ⟨p,a,rfl⟩ : ∃ p a, u=p++[a] := ⟨u.dropLast,u.getLast hu,(List.dropLast_concat_getLast hu).symm⟩
  obtain ⟨t,b,rfl⟩ : ∃ t b, v=t++[b] := ⟨v.dropLast,v.getLast hv,(List.dropLast_concat_getLast hv).symm⟩
  simp only [inc_snoc] at he
  obtain ⟨rfl,e⟩ := List.append_inj' he rfl
  simp at e; rw [e]

omit [Neg F] in
private theorem coeff_slice (z p : Tuple) (hlen : p.length=z.length) (k : F) (ts : List Tuple) (x : Tuple) :
    coordinates (withCoeff k (ts.map (fun v => p++v))) (z++x) =
      if p=z then coordinates (withCoeff k ts) x else 0 := by
  induction ts with
  | nil => by_cases h : p=z <;> simp [h,coordinates,withCoeff,total]
  | cons a ts ih =>
    change (if p++a=z++x then k else 0) + coordinates (withCoeff k _) _ = if p=z then (if a=x then k else 0) + coordinates (withCoeff k ts) x else 0
    rw [ih]
    have eqv : (p++a=z++x) ↔ p=z ∧ a=x := ⟨fun h => List.append_inj h hlen,by rintro ⟨rfl,rfl⟩;rfl⟩
    by_cases h : p=z <;> simp [eqv,h,Arithmetic.addZero]

private theorem expanded_H (q : Nat) (l t : Tuple) (hn : l≠[]) :
    H q l t = (quasiShuffle [q-1] t).map (fun v => incLast l ++ v) ++
      ((quasiShuffle [q-1] t).map (List.cons 1)).map (fun v => l ++ v) := by
  cases l with
  | nil => contradiction
  | cons => simp [H,concatenate,endings,List.map_map,Function.comp_def]

omit [Neg F] in
private theorem same_depth (q : Nat) (u l t : Tuple) (hu : u≠[]) (hn : l≠[])
    (le : weight l ≤ weight u) (hlen : l.length=u.length) (k : F) (x : Tuple) :
    coordinates (withCoeff k (H q l t)) (incLast u ++ x) =
      if l=u then coordinates (withCoeff k (quasiShuffle [q-1] t)) x else 0 := by
  have incwt : weight (incLast u)=weight u+1 := by
    cases u with
    | nil => contradiction
    | cons a s => exact incLast_weight a s
  have ne : l≠incLast u := fun h => by rw [h,incwt] at le; omega
  rw [expanded_H q l t hn,Singletons.coeff_append,
    coeff_slice _ _ ((inc_len l).trans (hlen.trans (inc_len u).symm)),
    coeff_slice _ _ (hlen.trans (inc_len u).symm),if_neg ne,Arithmetic.addZero]
  by_cases h : l=u
  · subst l; simp
  · simp [h,show incLast l ≠ incLast u from fun hh => h (inc_inj _ _ hn hu hh)]

private theorem longer_row (field : ConstantField F q) (z l t : Tuple) (hh : Valid l) (ht : Valid t)
    (hd : z.length < l.length) (k : F) :
    HPlus q (fun x => coordinates (withCoeff k (H q l t)) (z++x)) := by
  let p := l.take z.length
  let d := l.drop z.length
  have plen : p.length=z.length := by simp [p,Nat.min_eq_left (Nat.le_of_lt hd)]
  have de : p++d=l := List.take_append_drop _ _
  have dn : d≠[] := by
    intro he; have := congrArg List.length de; simp only [he,List.append_nil,plen] at this; omega
  cases eq : d with
  | nil => contradiction
  | cons a s =>
    rw [eq] at de
    have vd : Valid (a::s) := fun b hb => hh b (de ▸ List.mem_append_right _ hb)
    rw [← de,PrimitiveRows.H_prepend_nonempty]
    simp only [coeff_slice z p plen]
    by_cases e : p=z
    · simp only [e,if_true]
      exact (rowSpan_iff field.add_neg q _).mp (.row a s t k vd ht)
    · simp only [if_neg e]; exact .zero

def key : Tuple → Tuple := incLast

private theorem later_slice (field : ConstantField F q) (u : Tuple) (e : F × Row q w)
    (hl : Later u (lhs e)) :
    HPlus q (fun x => e.1*coordinates (withCoeff 1 (H q (lhs e) e.2.val.2)) (key u++x)) := by
  simp only [← coeff_scale]
  rcases hl with hd | ⟨hlen,hw,ne⟩
  · apply longer_row field _ _ _ e.2.property.1 e.2.property.2.1
    simpa only [key,inc_len] using hd
  · have hn : u≠[] := by intro hu; rw [hu] at hlen ne; exact ne (List.length_eq_zero_iff.mp hlen)
    have hn' : lhs e≠[] := by
      intro he; rw [he] at hlen; exact hn (List.length_eq_zero_iff.mp hlen.symm)
    simp only [key,same_depth q _ _ _ hn hn' hw hlen,if_neg ne]; exact .zero

private theorem residual_slice (field : ConstantField F q) (u : Tuple) (r : Rows F q w)
    (hr : ∀ e∈r, Later u (lhs e)) :
    HPlus q (fun x => component H r (key u ++ x)) := by
  induction r with
  | nil => exact .zero
  | cons e r ih =>
    exact .add (later_slice field u e (hr e (by simp))) (ih (fun z hz => hr z (by simp [hz])))

omit [Neg F] in
private theorem pure_slice (u : Tuple) (hu : u≠[]) (b : Rows F q w) (hb : ∀ e∈b,lhs e=u) (x : Tuple) :
    component H b (key u ++ x) = coordinates (expand (quasiShuffle [q-1]) (tailSum b)) x := by
  induction b with
  | nil => rfl
  | cons e b ih =>
    change e.1 * coordinates (withCoeff (1:F) (H q (lhs e) e.2.val.2)) (incLast u++x) + component H b (key u++x) =
      coordinates (withCoeff e.1 _ ++ expand _ (tailSum b)) x
    rw [coord_append, ← coeff_scale, hb e (by simp),
      same_depth q u u _ hu hu (Nat.le_refl _) rfl, if_pos rfl,
      ih (fun z hz => hb z (by simp [hz]))]

omit [Neg F] in
private theorem empty_slice (b : Rows F q w) (hb : ∀ e∈b, lhs e=[]) :
    component H b = head 1 (coordinates (expand (quasiShuffle [q-1]) (tailSum b))) := by
  induction b with
  | nil => exact (Singletons.head_zero 1).symm
  | cons e b ih =>
    funext x
    change e.1 * coordinates (withCoeff (1:F) (H q (lhs e) e.2.val.2)) x + component H b x =
      head 1 (coordinates (withCoeff e.1 _ ++ expand _ (tailSum b))) x
    have h := funext (coord_append (withCoeff e.1 (quasiShuffle [q-1] e.2.val.2))
      (expand (quasiShuffle [q-1]) (tailSum b)))
    rw [h, head_add,←coeff_scale,hb e (by simp), ih (fun z hz => hb z (by simp [hz]))]
    simp [H,endings,concatenate,←coeff_prepend]

/-- The pivot equation follows from the singleton reflection on the
explicit tuple presentation. -/
theorem pivot_from_reflection (field : ConstantField F q)
    (reflect : ∀ p : FormalSum F, PresentedValid p →
      HPlus q (coordinates (expand (quasiShuffle [q-1]) p)) → HPlus q (coordinates p)) :
    PivotReflection F q w := by
  intro u b r hb hr hz
  have valid : PresentedValid (tailSum b) := by
    intro e he; obtain ⟨c,_,rfl⟩ := List.mem_map.mp he; exact c.2.property.2.1
  apply reflect _ valid
  have residual := residual_slice field u r hr
  have hp : HPlus q (fun x => component H b (key u ++ x)) := by
    have hh : (fun x => -(component H r (key u++x))) = (fun x => component H b (key u++x)) := by
      funext x
      apply Eq.symm
      calc _ = component H b (key u++x)+(component H r (key u++x)+ -component H r (key u++x)) := by
             rw [field.add_neg,Arithmetic.addZero]
           _ = _ := by rw [← Arithmetic.addAssoc,hz,zeroAdd]
    rw [← hh]; exact .neg residual
  by_cases hu : u=[]
  · subst u
    apply (prepend_one_iff field.add_neg q _).mp
    rw [← empty_slice b hb]; exact hp
  · simpa only [pure_slice u hu b hb] using hp

theorem kernel_from_reflection (field : ConstantField F q)
    (reflect : ∀ p : FormalSum F, PresentedValid p →
      HPlus q (coordinates (expand (quasiShuffle [q-1]) p)) → HPlus q (coordinates p))
    (c : Rows F q w) (hz : component H c = (fun _ => 0)) : BCPVector q w (component L c) :=
  kernel_of_pivot field (pivot_from_reflection field reflect) c hz

end Megaera.HKernelPivot
