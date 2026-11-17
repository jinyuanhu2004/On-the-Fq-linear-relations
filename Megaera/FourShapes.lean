import Megaera.FourCompleteness
import Megaera.FourMinimum

namespace Megaera.FourReduction
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.Triangular Megaera.FourMinimum
variable {F : Type u} [Arithmetic F] [Neg F] {q w : Nat}

/-- The three displayed tuple forms of Lemma 4.1 at the specified weight. -/
inductive Shape (q w : Nat) : Tuple → Prop where
  | general (h s t) : Valid h → Valid s → s ≠ [] → Valid t →
      weight h + weight s + weight t + 2*q = w →
      Shape q w (h ++ (raiseFirst q (incLast s) ++ addLast (q-1) t))
  | difference (h s u t) : Valid h → Valid s → s ≠ [] → Valid u → u ≠ [] → Valid t →
      weight h + weight s + weight u + weight t + 1 + 2*q = w →
      Shape q w (h ++ (raiseFirst q (incLast s) ++ (addLast q u ++ t)))

theorem least_of_unit (field : ConstantField F q) {v : Tuple → F} {s : Tuple}
    (h : UnitMinimum v s) : Least v s := by
  refine ⟨fun hz => field.nontrivial (hz.symm.trans h.1),?_⟩
  intro t ht
  rcases precedes_trichotomy s t with lt | eq | lt
  · exact .inr lt
  · exact .inl eq.symm
  · exact (ht (h.2 _ lt)).elim

omit [Neg F] in
theorem equal_min {g : Tuple → F} {s t : Tuple} (a : Least g s) (b : Least g t) : s=t := by
  rcases b.2 s a.1 with eq | lt
  · exact eq
  rcases a.2 t b.1 with eq | lt'
  · exact eq.symm
  · exact (precedes_irrefl _ (precedes_trans lt lt')).elim

/-- A tuple is a permitted pivot for the actual generators exactly when it
has one of the shapes in the manuscript. -/
theorem legal_iff_shape (field : ConstantField F q) (x : Tuple) :
    Legal F q w x ↔ Shape q w x := by
  constructor
  · rintro ⟨g,hg,hx⟩
    cases hg with
    | general h s t hh hs hn ht hw =>
      have hp := least_of_unit field (lemma_4_1_i_ii (F:=F) q field.two_le h s t hn)
      rw [equal_min hx hp]
      exact .general _ _ _ hh hs hn ht hw
    | difference h s u t hh hs hn hu un ht hw =>
      have hp := least_of_unit field (lemma_4_1_iii q field h s u t hn un)
      rw [equal_min hx hp]
      exact .difference _ _ _ _ hh hs hn hu un ht hw
  · intro shape
    cases shape with
    | general h s t hh hs hn ht hw =>
      exact ⟨_,.general _ _ _ hh hs hn ht hw,least_of_unit field (lemma_4_1_i_ii q field.two_le h s t hn)⟩
    | difference h s u t hh hs hn hu un ht hw =>
      exact ⟨_,.difference _ _ _ _ hh hs hn hu un ht hw,least_of_unit field (lemma_4_1_iii q field h s u t hn un)⟩

private theorem last_ge (k : Nat) (t : Tuple) :
    ∃ h a, addLast k t = h ++ [a] ∧ k ≤ a := by
  induction t with
  | nil => exact ⟨[],k,rfl,Nat.le_refl _⟩
  | cons a t ih =>
    cases t with
    | nil => exact ⟨[],k+a,rfl,by omega⟩
    | cons b t =>
      obtain ⟨h,z,he,hz⟩ := ih
      exact ⟨a::h,z,congrArg (a::·) he,hz⟩

private theorem mark_length (q : Nat) (a : Nat) (s : Tuple) :
    (raiseFirst q (incLast (a::s))).length = s.length+1 := by
  have h := incLast_length a s
  cases e : incLast (a::s) with
  | nil => simp [e] at h
  | cons b z => simpa [raiseFirst,e] using h

private theorem bumped_length (k a : Nat) (t : Tuple) :
    (addLast k (a::t)).length = t.length+1 := by
  induction t generalizing a with
  | nil => rfl
  | cons b t ih => exact congrArg (·+1) (ih b)

private theorem ends_one (h : Tuple) (a q : Nat) (he : h++[a]=[q+1,q+1,1]) : a=1 := by
  have last := congrArg List.getLast? he
  simpa using last

/-- The cutoff in the page-24 obstruction has none of the three shapes. -/
theorem obstruction_illegal (q w : Nat) (hq : 3 ≤ q) : ¬ Shape q w [q+1,q+1,1] := by
  intro hs
  generalize eqn : [q+1,q+1,1] = x at hs
  cases hs with
  | general h s t hh hs hn ht hw =>
    obtain ⟨l,z,hz,le⟩ := last_ge (q-1) t
    rw [hz] at eqn
    have eq : (h++raiseFirst q (incLast s)++l)++[z] = [q+1,q+1,1] := by
      simpa only [List.append_assoc] using eqn.symm
    have := ends_one _ _ _ eq
    omega
  | difference h s u t hh hs hn hu un ht hw =>
    cases t with
    | nil =>
      obtain ⟨l,z,hz,le⟩ := last_ge q u
      rw [hz] at eqn
      have eq : (h++raiseFirst q (incLast s)++l)++[z] = [q+1,q+1,1] := by
        simpa only [List.append_nil,List.append_assoc] using eqn.symm
      have := ends_one _ _ _ eq
      omega
    | cons d t =>
      cases s with
      | nil => contradiction
      | cons a s =>
        cases u with
        | nil => contradiction
        | cons b u =>
          have len := congrArg List.length eqn
          simp only [List.length_cons,List.length_nil,List.length_append,mark_length,bumped_length] at len
          have hs0 : s=[] := List.length_eq_zero_iff.mp (by omega)
          have hh0 : h=[] := List.length_eq_zero_iff.mp (by omega)
          subst s; subst h
          have pos := hs a (by simp)
          have head := congrArg List.head? eqn
          simp [incLast,raiseFirst] at head
          omega

/-- A generator with a permitted pivot can itself be eliminated in one step.
This tests whether a proposed functional is invariant on the reduction steps. -/
theorem eliminate_generator (field : ConstantField F q) (allow : Tuple → Prop)
    {g : Tuple → F} {p : Tuple} (hg : Special F q w g) (hp : Least g p) (ha : allow p) :
    Reduces F q w allow g (fun _ => 0) := by
  have kill (t : Tuple) : addScaled g (-1) g t = 0 := by
    simp only [addScaled,neg_mul field,oneMul,field.add_neg]
  apply Reduces.step (k := -(1:F)) hg hp ha hp.1 (kill p)
  rw [show addScaled g (-1) g = (fun _ => 0) from funext kill]
  exact .done _

end Megaera.FourReduction
