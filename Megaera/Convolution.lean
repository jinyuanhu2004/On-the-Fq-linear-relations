import Megaera.ThirdCut
import Megaera.StuffleLaws
import Megaera.MainTheorems

/-! The explicit signed-pair cut formula, Theorem 2.11. -/

namespace Megaera.Convolution
open Megaera.Cuts Megaera.ThirdCut Megaera.StuffleLaws

/-- The terms of the right side of Theorem 2.11, with repeated terms retained. -/
def pieces (K : Type u) [OfNat K 1] [Neg K] (q : Nat) (s t : Tuple) : List (BinaryPair K) :=
  (cuts t).flatMap (fun p => (quasiShuffle s p.1).map (fun x => generalP q x p.2))

private theorem start_action (q b : Nat) (r t : Tuple) (f : Tuple → Nat) :
    total (start q r) (fun x => total (diamond x (b::t)) f) +
      total (start q r) (fun x => total (triangle x (b::t)) f) =
      total (quasiShuffle r (b::t)) (fun x => total (start q x) f) := by
  cases r with
  | nil => simp [start,diamond,triangle,total,Nat.add_comm]
  | cons a r =>
    simp only [start,total,diamond,triangle,total_map,Nat.add_zero,peel,Nat.add_assoc]
    simp only [start,total,Nat.add_zero,Nat.add_assoc,sum_add]
    generalize total (quasiShuffle r (b::t)) (fun x => f ((q+a)::x)) = A
    generalize total (quasiShuffle (a::r) t) (fun x => f ((q+b)::x)) = B
    generalize total (quasiShuffle r t) (fun x => f ((q+(a+b))::x)) = C
    omega

private theorem positive (K : Type u) [OfNat K 1] [Neg K]
    (q b : Nat) (s t : Tuple) (f : K × Tuple → Nat) :
    total (cOp (b::t) (primitive q s)).1 f =
      total ((pieces K q s (b::t)).flatMap Prod.fst) f := by
  let g (x : Tuple) := f (1,x)
  have eq := total_perm (endings_append_cut q s (b::t)) (fun x => total (start q x) g)
  simp only [total_flatMap] at eq
  rw [primitive_eq_shaped]
  simp only [cOp,shapedPair,primitiveData,expand,withCoeff,total_append,total_flatMap,total_map,
    pieces,generalP]
  rw [← sum_add]
  change total (endings s) (fun e =>
      total (start q (e++[q-1])) (fun x => total (diamond x (b::t)) g) +
      total (start q (e++[q-1])) (fun x => total (triangle x (b::t)) g)) = _
  simpa only [start_action] using eq

private theorem negative (K : Type u) [OfNat K 1] [Neg K]
    (q b : Nat) (s t : Tuple) (f : K × Tuple → Nat) :
    total (cOp (b::t) (primitive q s)).2 f =
      total ((pieces K q s (b::t)).flatMap Prod.snd) f := by
  let g (x : Tuple) := f (-1,1::x)
  have eq := total_perm (append_singleton_cut s q (b::t))
    (fun x => total (quasiShuffle [q-1] x) g)
  simp only [concatenate,total_flatMap,total_map] at eq
  rw [primitive_eq_shaped]
  simp only [cOp,shapedPair,primitiveData,expand,withCoeff,total_flatMap,total_map,total,
    Nat.add_zero,triangle,pieces,generalP,L]
  exact (assoc_total [q-1] (s++[q]) (b::t) g).trans eq

private theorem count_by {A : Type u} [DecidableEq A] (a : A) (l : List A) :
    @List.count A instBEqOfDecidableEq a l = total l (fun x => if x = a then 1 else 0) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    by_cases h : x = a <;> simp_all [total,List.count_cons,instBEqOfDecidableEq,Nat.add_comm]

/-- Theorem 2.11 in the two components of the actual signed pair. Each
permutation remains valid before coefficients are collected in the field. -/
theorem theorem_2_11 (K : Type u) [OfNat K 1] [Neg K] (q : Nat) (s t : Tuple) :
    (cOp t (primitive (K := K) q s)).1.Perm ((pieces K q s t).flatMap Prod.fst) ∧
    (cOp t (primitive (K := K) q s)).2.Perm ((pieces K q s t).flatMap Prod.snd) := by
  classical
  cases t with
  | nil => simp [pieces,cuts,cOp,primitive]
  | cons b t =>
    constructor
    · apply List.perm_iff_count.mpr
      intro x
      rw [count_by,count_by]
      exact positive K q b s t _
    · apply List.perm_iff_count.mpr
      intro x
      rw [count_by,count_by]
      exact negative K q b s t _

/-- Evaluation of a formal pair in an additive target only uses these three
properties: permutation invariance, the empty pair and concatenation. -/
structure AdditiveReading {K : Type u} {V : Type v} [Zero V] [Add V]
    (read : BinaryPair K → V) : Prop where
  perm : ∀ p r, p.1.Perm r.1 → p.2.Perm r.2 → read p = read r
  empty : read ([],[]) = 0
  append : ∀ p r, read (p.1++r.1,p.2++r.2) = read p + read r

private theorem read_sum {K : Type u} {V : Type v} [Zero V] [Add V]
    {read : BinaryPair K → V} (ar : AdditiveReading read) (p : List (BinaryPair K)) :
    read (p.flatMap Prod.fst,p.flatMap Prod.snd) = sumRows p read := by
  induction p with
  | nil => exact ar.empty
  | cons a p ih => exact (ar.append a _).trans (congrArg (read a + ·) ih)

private theorem sum_append {A : Type u} {V : Type v} [Zero V] [Add V]
    (zeroAdd : ∀ a : V, 0+a=a) (assoc : ∀ a b c : V, a+b+c=a+(b+c))
    (a b : List A) (f : A → V) :
    sumRows (a++b) f = sumRows a f + sumRows b f := by
  induction a with
  | nil => exact (zeroAdd _).symm
  | cons x xs ih => simp only [List.cons_append,sumRows,ih,assoc]

private theorem sum_pieces {K : Type u} [OfNat K 1] [Neg K]
    {V : Type v} [Zero V] [Add V] (read : BinaryPair K → V)
    (zeroAdd : ∀ a : V, 0+a=a) (assoc : ∀ a b c : V, a+b+c=a+(b+c))
    (q : Nat) (s : Tuple) (ps : List (Tuple × Tuple)) :
    sumRows (ps.flatMap (fun p => (quasiShuffle s p.1).map (fun x => generalP q x p.2))) read =
      sumRows ps (fun p => sumRows (quasiShuffle s p.1) (fun x => read (generalP q x p.2))) := by
  have mapSum {A : Type} {B : Type u} (f : A → B) (g : B → V) (l : List A) :
      sumRows (l.map f) g = sumRows l (fun x => g (f x)) := by
    induction l with
    | nil => rfl
    | cons x l ih => simp only [List.map_cons,sumRows,ih]
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.flatMap_cons,sumRows,sum_append zeroAdd assoc,ih,mapSum]

/-- The cut convolution in the form required by the depth induction. -/
theorem read_convolution {K : Type u} [OfNat K 1] [Neg K] {V : Type v} [Zero V] [Add V]
    {read : BinaryPair K → V} (ar : AdditiveReading read)
    (zeroAdd : ∀ a : V, 0+a=a) (assoc : ∀ a b c : V, a+b+c=a+(b+c))
    (q : Nat) (s t : Tuple) :
    read (cOp t (primitive q s)) = sumRows (cuts t)
      (fun p => sumRows (quasiShuffle s p.1) (fun x => read (generalP q x p.2))) := by
  obtain ⟨p,n⟩ := theorem_2_11 K q s t
  exact (ar.perm _ _ p n).trans ((read_sum ar _).trans
    (sum_pieces read zeroAdd assoc q s (cuts t)))

/-- Corollary 2.12, valid after every additive reading of signed pairs. -/
theorem corollary_2_12 {K : Type u} [OfNat K 1] [Neg K] {V : Type v} [Zero V] [Add V] [Sub V]
    (q : Nat) (read : BinaryPair K → V) (ar : AdditiveReading read)
    (zeroAdd : ∀ a : V, 0+a=a) (addZero : ∀ a : V, a+0=a)
    (assoc : ∀ a b c : V, a+b+c=a+(b+c)) (cancel : ∀ a b : V, a+b-b=a)
    (G : V → Prop) (gzero : G 0) (gadd : ∀ a b, G a → G b → G (a+b))
    (gsub : ∀ a b, G a → G b → G (a-b))
    (generators : ∀ s t, Valid s → s ≠ [] → Valid t → G (read (cOp t (primitive q s)))) :
    ∀ s t, Valid s → s ≠ [] → Valid t → G (read (generalP q s t)) :=
  generalP_generated_of_cutIdentity q read G addZero cancel gzero gadd gsub generators
    (fun s t _ _ _ => read_convolution ar zeroAdd assoc q s t)

section Coordinates
open Megaera.Finite Megaera.Carlitz
variable {F : Type u} [Arithmetic F]

/-- The Boolean argument selects the first (true) or second (false) coordinate
vector of a binary pair. Repeated tuple terms are summed in F. -/
def pairCoordinates (p : BinaryPair F) (first : Bool) (s : Tuple) : F :=
  if first then coordinates p.1 s else coordinates p.2 s

local instance : Zero (Bool → Tuple → F) := ⟨fun _ _ => 0⟩
local instance : Add (Bool → Tuple → F) := ⟨fun v z b s => v b s + z b s⟩
local instance [Neg F] : Sub (Bool → Tuple → F) := ⟨fun v z b s => v b s + (-(z b s))⟩

private theorem coord_perm {p r : FormalSum F} (eq : p.Perm r) (s : Tuple) :
    coordinates p s = coordinates r s := by
  induction eq with
  | nil => rfl
  | cons a _ ih =>
    change _ + coordinates _ s = _ + coordinates _ s
    rw [ih]
  | swap a b l =>
    change _ + (_ + coordinates _ s) = _ + (_ + coordinates _ s)
    rw [← Arithmetic.addAssoc,Arithmetic.addComm (if b.2 = s then b.1 else 0)
      (if a.2 = s then a.1 else 0),Arithmetic.addAssoc]
  | trans _ _ ih jh => exact ih.trans jh

private theorem coord_add (p r : FormalSum F) (s : Tuple) :
    coordinates (p++r) s = coordinates p s + coordinates r s := by
  induction p with
  | nil => exact (Finite.zeroAdd _).symm
  | cons a p ih =>
    change _ + coordinates (p++r) s = (_ + coordinates p s) + coordinates r s
    rw [ih,Arithmetic.addAssoc]

theorem coordinates_reading : AdditiveReading (pairCoordinates (F := F)) where
  perm p r h k := by
    funext b s
    cases b
    · exact coord_perm k s
    · exact coord_perm h s
  empty := by funext b s; cases b <;> rfl
  append p r := by
    funext b s
    cases b
    · exact coord_add _ _ _
    · exact coord_add _ _ _

/-- The F-linear span of all C-translates of the original primitive pairs in
the actual free coefficient space. -/
inductive TranslateSpan (F : Type u) [Arithmetic F] [Neg F] (q : Nat) :
    (Bool → Tuple → F) → Prop where
  | zero : TranslateSpan F q 0
  | translate (s t : Tuple) (hs : Valid s) (hn : s ≠ []) (ht : Valid t) :
    TranslateSpan F q (pairCoordinates (cOp t (primitive q s)))
  | add {v z} : TranslateSpan F q v → TranslateSpan F q z → TranslateSpan F q (v+z)
  | sub {v z} : TranslateSpan F q v → TranslateSpan F q z → TranslateSpan F q (v-z)
  | scale (a : F) {v} : TranslateSpan F q v → TranslateSpan F q (fun b s => a*v b s)

/-- Corollary 2.12 in the free space of tuple pairs over the given constants. -/
theorem general_primitive_in_span [Neg F] (q : Nat) (field : Paper.ConstantField F q)
    (s t : Tuple) (hs : Valid s) (hn : s ≠ []) (ht : Valid t) :
    TranslateSpan F q (pairCoordinates (generalP q s t)) := by
  apply corollary_2_12 q pairCoordinates coordinates_reading _ _ _ _ (TranslateSpan F q)
    .zero (fun _ _ => TranslateSpan.add) (fun _ _ => TranslateSpan.sub) TranslateSpan.translate
    s t hs hn ht
  · intro v; funext b x; exact Finite.zeroAdd _
  · intro v; funext b x; exact Arithmetic.addZero _
  · intro v z r; funext b x; exact Arithmetic.addAssoc _ _ _
  · intro v z; funext b x
    change (v b x + z b x) + (-(z b x)) = v b x
    rw [Arithmetic.addAssoc,field.add_neg,Arithmetic.addZero]

end Coordinates
end Megaera.Convolution
