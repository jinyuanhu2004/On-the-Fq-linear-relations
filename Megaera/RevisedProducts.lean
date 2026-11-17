import Megaera.IntegerLevels
import Megaera.BinaryOperators

/-! The empty-input conventions and Theorem 1.5 in Megaera (2), p. 4. -/
namespace Megaera.RevisedProducts
open Megaera.Finite Megaera.BinaryOperators

def diamond : Tuple → Tuple → List Tuple
  | [], _ | _, [] => []
  | a::s, b::t => Megaera.diamond (a::s) (b::t)

def triangle (s t : Tuple) : List Tuple :=
  if t = [] then [s] else Megaera.triangle s t

theorem theorem_1_5 {K : Type u} [Arithmetic K] (x : Nat → K) (d : Nat) (s t : Tuple) :
    total (truncSum x d) (quasiShuffle s t) = truncSum x d s * truncSum x d t ∧
    total (level x d) (diamond s t) = level x d s * level x d t ∧
    total (level x d) (triangle s t) = level x d s * truncSum x d t := by
  refine ⟨stuffle_product x d s t, ?_, ?_⟩
  · cases s with
    | nil => simpa [diamond,level,total] using (zeroMul (level x d t)).symm
    | cons a s =>
      cases t with
      | nil => exact (Arithmetic.mulZero _).symm
      | cons b t => exact diamond_product .. 
  · cases t with
    | nil => simp [triangle, total, trunc_nil, Arithmetic.addZero, Arithmetic.mulOne]
    | cons b t =>
      cases s with
      | nil => exact (zeroMul _).symm
      | cons a s => exact triangle_product .. 

def B {K : Type u} (w : Tuple) (r : BinaryPair K) : BinaryPair K :=
  match w with
  | [] => r
  | a::s => (expand (triangle (a::s)) r.1 ++ expand (diamond (a::s)) r.2 ++
      expand (triangle (a::s)) r.2, [])

def C {K : Type u} (w : Tuple) (r : BinaryPair K) : BinaryPair K :=
  match w with
  | [] => r
  | a::s => (expand (fun t => diamond t (a::s)) r.1 ++
      expand (fun t => triangle t (a::s)) r.1, expand (fun t => triangle t (a::s)) r.2)

def Bstar {K : Type u} : Tuple → BinaryPair K → BinaryPair K
  | [], r => r
  | a::s, r => B [a] (Bstar s r)

private theorem expand_eq {K : Type u} (f g : Tuple → List Tuple) (p : FormalSum K)
    (h : ∀ z ∈ p, f z.2 = g z.2) : expand f p = expand g p := by
  induction p with
  | nil => rfl
  | cons z p ih =>
    simp only [expand, List.flatMap_cons]
    rw [h z (by simp)]
    exact congrArg (_ ++ ·) (ih (fun e he => h e (by simp [he])))

theorem B_eq {K : Type u} (w : Tuple) (r : BinaryPair K) (hr : NonemptySupport r) :
    B w r = bOp w r := by
  cases w with
  | nil => rfl
  | cons a s =>
    simp only [B, bOp]
    rw [expand_eq (triangle (a::s)) (Megaera.triangle (a::s)) r.1 (fun z hz => if_neg (hr.1 z hz)),
      expand_eq (diamond (a::s)) (Megaera.diamond (a::s)) r.2 (fun z hz => by
        cases ht : z.2 with
        | nil => exact (hr.2 z hz ht).elim
        | cons => rfl),
      expand_eq (triangle (a::s)) (Megaera.triangle (a::s)) r.2 (fun z hz => if_neg (hr.2 z hz))]

theorem C_eq {K : Type u} (w : Tuple) (r : BinaryPair K) (hr : NonemptySupport r) :
    C w r = cOp w r := by
  cases w with
  | nil => rfl
  | cons a s =>
    simp only [C, cOp]
    rw [expand_eq (fun t => diamond t (a::s)) (fun t => Megaera.diamond t (a::s)) r.1 (fun z hz => by
      cases ht : z.2 with
      | nil => exact (hr.1 z hz ht).elim
      | cons => rfl)]
    rfl

theorem Bstar_eq {K : Type u} (w : Tuple) (r : BinaryPair K) (hr : NonemptySupport r) :
    Bstar w r = bStar w r ∧ NonemptySupport (bStar w r) := by
  induction w with
  | nil => exact ⟨rfl,hr⟩
  | cons a s ih =>
    exact ⟨(congrArg (B [a]) ih.1).trans (B_eq _ _ ih.2), bOp_nonempty _ _ ih.2⟩

/-- Each BCP generator in the revised conventions is the one in the existing theorem. -/
theorem generator_eq {F : Type u} [OfNat F 1] [Neg F] (q : Nat) (hq : 0 < q)
    (h t s : Tuple) :
    liftPair (Bstar h (C t (primitive (K := F) q s))) = bcpGenerator q h t s := by
  have supp := nonemptySupport_of_weight _ (by omega) _ (primitive_weight (K := F) q hq s)
  rw [C_eq _ _ supp, (Bstar_eq _ _ (cOp_nonempty t _ supp)).1]
  rfl

end Megaera.RevisedProducts
