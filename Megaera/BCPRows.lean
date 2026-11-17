import Megaera.PrimitiveRows
import Megaera.MainTheorems
import Megaera.Convolution

/-! Weighted marked-row certificates for the inclusion BCP_w ⊆ H(ker L_w). -/
namespace Megaera.BCPRows
open Megaera.Finite Megaera.Carlitz Megaera.Paper
variable {F : Type u} [Arithmetic F]
local instance : Zero (Tuple → F) := ⟨fun _ => 0⟩
local instance : Std.Associative (α := F) (· + ·) := ⟨Arithmetic.addAssoc⟩
local instance : Std.Commutative (α := F) (· + ·) := ⟨Arithmetic.addComm⟩

private theorem appendSum {A : Type v} (f : A → F) (l r : List A) :
    total f (l ++ r) = total f l + total f r := by
  induction l with
  | nil => simp [total,zeroAdd]
  | cons a l ih => simp [total,ih,Arithmetic.addAssoc]

theorem permSum {A : Type v} (f : A → F) {l r : List A} (p : l.Perm r) :
    total f l = total f r := by
  induction p with
  | nil => rfl
  | cons a _ ih => simp [total,ih]
  | swap => simp only [total]; ac_rfl
  | trans _ _ a b => exact a.trans b

private theorem addSum {A : Type v} (f g : A → F) (l : List A) :
    total (fun a => f a + g a) l = total f l + total g l := by
  induction l with
  | nil => simp [total,Arithmetic.addZero]
  | cons a l ih => simp only [total,ih]; ac_rfl

theorem flatSum {A : Type v} {B : Type z} (f : B → F) (g : A → List B) (l : List A) :
    total f (l.flatMap g) = total (fun a => total f (g a)) l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [total,appendSum,ih]

theorem coord_append (p r : FormalSum F) (s : Tuple) :
    coordinates (p++r) s = coordinates p s + coordinates r s := appendSum _ _ _

theorem coord_perm {p r : FormalSum F} (hp : p.Perm r) (s : Tuple) :
    coordinates p s = coordinates r s := permSum _ hp

theorem coeff_scale (k : F) (l : List Tuple) (s : Tuple) :
    coordinates (withCoeff k l) s = k * coordinates (withCoeff (1:F) l) s := by
  induction l with
  | nil => exact (Arithmetic.mulZero _).symm
  | cons a l ih =>
    change (if a=s then k else 0) + coordinates (withCoeff k l) s =
      k * ((if a=s then 1 else 0) + coordinates (withCoeff 1 l) s)
    rw [Arithmetic.distrib,ih]
    split <;> simp [Arithmetic.mulOne,Arithmetic.mulZero]

abbrev Good (q w : Nat) (p : Tuple × Tuple) :=
  Valid p.1 ∧ Valid p.2 ∧ weight p.1 + weight p.2 + q = w

def pack (k : F) (l : List (Tuple × Tuple)) (valid : ∀ z ∈ l, Good q w z) :
    Rows F q w :=
  match l with
  | [] => []
  | a :: l => (k, ⟨a,valid a (by simp)⟩) :: pack k l (fun z hz => valid z (by simp [hz]))

theorem pack_component (op : Nat → Tuple → Tuple → List Tuple) (k : F)
    (l : List (Tuple × Tuple)) (valid : ∀ z ∈ l, Good q w z) (s : Tuple) :
    component op (pack k l valid) s =
      coordinates (withCoeff k (l.flatMap (fun z => op q z.1 z.2))) s := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    simp only [pack,component,total,List.flatMap_cons,withCoeff,List.map_append] at ⊢
    change k * coordinates _ s + component op (pack k l _) s = coordinates (_ ++ _) s
    rw [coord_append,ih]
    exact congrArg (· + _) (coeff_scale k (op q e.1 e.2) s).symm

theorem rows_append (op : Nat → Tuple → Tuple → List Tuple) (l r : Rows F q w)
    (s : Tuple) : component op (l++r) s = component op l s + component op r s := appendSum _ _ _

/-- An actual closed L-row presentation with a specified H-coordinate vector. -/
def InImage (q w : Nat) (v : Tuple → F) : Prop :=
  ∃ c : Rows F q w, component L c = 0 ∧ component H c = v

theorem primitive_mem [Neg F] (q w : Nat) (field : ConstantField F q) (h s t : Tuple)
    (hh : Valid h) (hs : Valid s) (ht : Valid t) (hn : s ≠ [])
    (hw : weight h + weight s + weight t + 2*q = w) :
    InImage q w (coordinates (liftPair (bStar h (generalP (K := F) q s t)))) := by
  cases s with
  | nil => contradiction
  | cons a s =>
    let pos := (start q (a::s)).map fun u => (h++u,t)
    let neg := (L q (a::s) t).map fun v => (h,v)
    have hq : 0<q := by have := field.two_le; omega
    have pv : ∀ z ∈ pos, Good q w z := by
      intro z hz
      obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hz
      have hu' : u ∈ L q [] (a::s) := by simpa [L] using hu
      have huv := L_valid q hq [] (a::s) (by simp [Valid]) hs u hu'
      have huw := start_weight q (a::s) u hu
      refine ⟨fun i hi => (List.mem_append.mp hi).elim (hh i) (huv i),ht,?_⟩
      simp only [weight_append]; omega
    have nv : ∀ z ∈ neg, Good q w z := by
      intro z hz
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hz
      refine ⟨hh,L_valid q hq (a::s) t hs ht v hv,?_⟩
      have := L_weight q (a::s) t v hv
      change weight h + weight v + q = w
      omega
    have cert := PrimitiveRows.bStar_generalP_row_certificate (K := F) q a h s t
    refine ⟨pack 1 pos pv ++ pack (-(1:F)) neg nv,?_,?_⟩
    · funext u
      rw [rows_append,pack_component,pack_component]
      simp only [pos,neg,List.flatMap_map,Function.comp_def]
      have ep : coordinates (withCoeff (1:F) _) u = coordinates (withCoeff (1:F) _) u :=
        coord_perm (cert.1.map fun v => ((1:F),v)) u
      rw [ep,coeff_scale (-(1:F))]
      let x := coordinates (withCoeff (1:F) ((L q (a::s) t).flatMap (fun v => L q h v))) u
      change x + (-(1:F))*x = 0
      calc _ = x*1 + x*(-(1:F)) := by rw [Arithmetic.mulOne,Arithmetic.mulComm x (-(1:F))]
           _ = x*(1+(-(1:F))) := (Arithmetic.distrib _ _ _).symm
           _ = 0 := by rw [field.add_neg,Arithmetic.mulZero]
    · funext u
      rw [rows_append,pack_component,pack_component,← coord_append]
      simpa only [pos,neg,List.flatMap_map,Function.comp_def] using coord_perm cert.2 u

def scaleRows (a : F) (l : Rows F q w) : Rows F q w :=
  l.map (fun e => (a*e.1,e.2))

theorem scale_component (op : Nat → Tuple → Tuple → List Tuple)
    (a : F) (l : Rows F q w) (s : Tuple) :
    component op (scaleRows a l) s = a * component op l s := by
  induction l with
  | nil => exact (Arithmetic.mulZero _).symm
  | cons e l ih =>
    change (a*e.1)*_ + component op (scaleRows a l) s = a*(e.1*_ + component op l s)
    rw [ih,Arithmetic.distrib,Arithmetic.mulAssoc]

private theorem image_add {v z : Tuple → F} (hv : InImage q w v) (hz : InImage q w z) :
    InImage q w (fun s => v s + z s) := by
  obtain ⟨l,he,hl⟩ := hv
  obtain ⟨r,ge,gr⟩ := hz
  refine ⟨l++r,?_,?_⟩ <;> funext s
  · rw [rows_append,he,ge]; exact Arithmetic.addZero _
  · rw [rows_append,hl,gr]

private theorem image_scale {v : Tuple → F} (k : F) (hv : InImage q w v) :
    InImage q w (fun s => k * v s) := by
  obtain ⟨l,he,hl⟩ := hv
  refine ⟨scaleRows k l,?_,?_⟩ <;> funext s
  · rw [scale_component,he]; exact Arithmetic.mulZero _
  · rw [scale_component,hl]

private theorem image_total {A : Type v} (l : List A) (f : A → Tuple → F)
    (h : ∀ a ∈ l, InImage q w (f a)) : InImage q w (fun s => total (fun e => f e s) l) := by
  induction l with
  | nil => exact ⟨[],rfl,rfl⟩
  | cons a l ih =>
    exact image_add (h a (by simp)) (ih (fun z hz => h z (by simp [hz])))

private def readPair (f g : F × Tuple → F) (p : BinaryPair F) : F :=
  total f p.1 + total g p.2

private theorem bstar_read (h : Tuple) (f g : F × Tuple → F) :
    ∃ k l : F × Tuple → F, ∀ p, readPair f g (bStar h p) = readPair k l p := by
  induction h generalizing f g with
  | nil => exact ⟨f,g,fun _ => rfl⟩
  | cons a h ih =>
    let ker (op : Tuple → Tuple → List Tuple) (e : F × Tuple) :=
      total f (withCoeff e.1 (op [a] e.2))
    let k := ker triangle
    let l (e : F × Tuple) := ker diamond e + ker triangle e
    have step (p : BinaryPair F) : readPair f g (bOp [a] p) = readPair k l p := by
      simp only [bOp,readPair,appendSum,expand,flatSum,total,Arithmetic.addZero]
      rw [show total l p.2 = total (ker diamond) p.2 + total (ker triangle) p.2 from addSum _ _ _]
      change (total k p.1 + total (ker diamond) p.2) + total (ker triangle) p.2 = _
      rw [Arithmetic.addAssoc]
    obtain ⟨u,v,he⟩ := ih k l
    exact ⟨u,v,fun p => (step (bStar h p)).trans (he p)⟩

theorem prefixed_read (h : Tuple) (s : Tuple) :
    Convolution.AdditiveReading (fun p : BinaryPair F => coordinates (liftPair (bStar h p)) s) := by
  let f (e : F × Tuple) := if e.2 = s then e.1 else 0
  obtain ⟨k,l,he⟩ := bstar_read h f f
  have eqp (p : BinaryPair F) : coordinates (liftPair (bStar h p)) s = readPair k l p :=
    (appendSum f _ _).trans (he p)
  constructor
  · intro p r hp hr
    rw [eqp,eqp,readPair,readPair,permSum k hp,permSum l hr]
  · rw [eqp]; exact Arithmetic.addZero _
  · intro p r
    simp only [eqp,readPair,appendSum]
    ac_rfl

theorem rowsSum {A : Type v} (l : List A) (f : A → F) :
    Cuts.sumRows l f = total f l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [Cuts.sumRows,total,ih]

/-- Every BCP generator has a homogeneous closed row witness. The C-operator
is expanded with Theorem 2.11 before the common prefix is applied. -/
theorem generator_mem [Neg F] (q w : Nat) (field : ConstantField F q) (h t s : Tuple)
    (hh : Valid h) (ht : Valid t) (hs : Valid s) (hn : s ≠ [])
    (hw : weight h + weight t + weight s + 2*q = w) :
    InImage q w (coordinates (bcpGenerator (K := F) q h t s)) := by
  let read (v : BinaryPair F) := coordinates (liftPair (bStar h v))
  have he : coordinates (bcpGenerator (K := F) q h t s) =
      (fun u => total (fun p => total (fun x => read (generalP q x p.2) u) (quasiShuffle s p.1))
        (Cuts.cuts t)) := by
    funext u
    have eqc := Convolution.read_convolution (prefixed_read (F := F) h u) zeroAdd Arithmetic.addAssoc q s t
    simpa only [rowsSum] using eqc
  rw [he]
  apply image_total
  intro p hp
  have cut := Cuts.pieces_append hp
  apply image_total
  intro x hx
  have pv : Valid p.1 := fun a ha => ht a (cut ▸ List.mem_append_left _ ha)
  have tv : Valid p.2 := fun a ha => ht a (cut ▸ List.mem_append_right _ ha)
  have xw := weight_quasiShuffle s p.1 x hx
  have pw := congrArg weight cut
  rw [weight_append] at pw
  have xpos : 0 < weight s := by
    cases s with
    | nil => contradiction
    | cons a s => have := hs a (by simp); simp only [weight]; omega
  have xn : x ≠ [] := by intro h; rw [h] at xw; simp only [weight] at xw; omega
  exact primitive_mem q w field h x p.2 hh (valid_quasiShuffle _ _ _ hs pv hx) tv xn (by omega)

/-- The full BCP inclusion in Theorem 2.13, for actual weighted Paper.Rows. -/
theorem bcp_in_H_ker_L [Neg F] (q w : Nat) (field : ConstantField F q) (v : Tuple → F)
    (hb : BCPVector q w v) :
    ∃ c : Rows F q w, component L c = 0 ∧ component H c = v := by
  obtain ⟨p,⟨l,hv,he⟩,rfl⟩ := hb
  change InImage q w (coordinates p)
  rw [funext he]
  apply image_total
  intro e hm
  obtain ⟨hh,ht,hs,hn,hw⟩ := hv e hm
  exact image_scale e.1 (generator_mem q w field _ _ _ hh ht hs hn hw)

end Megaera.BCPRows
