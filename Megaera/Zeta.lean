import Megaera.Carlitz

/-! Thakur sums in §1.1. A monic degree-d polynomial is represented by its
d nonleading coefficients in descending order. Supply each constant field
element exactly once in the alphabet. For a positive tuple the value at
infinity has only nonnegative powers of T=1/θ. -/
namespace Megaera.Zeta
open Megaera.Finite Megaera.Carlitz

variable {F : Type u} [Arithmetic F] [Neg F]

def monics (alphabet : List F) : Nat → List (List F)
  | 0 => [[]]
  | d+1 => alphabet.flatMap fun a => (monics alphabet d).map (a :: ·)

omit [Arithmetic F] [Neg F] in
theorem mem_monics (alphabet : List F) (d : Nat) (a : List F) :
    a ∈ monics alphabet d ↔ a.length = d ∧ ∀ b ∈ a, b ∈ alphabet := by
  induction d generalizing a with
  | zero =>
    cases a <;> simp [monics]
  | succ d ih =>
    cases a with
    | nil => simp [monics, List.mem_flatMap, List.mem_map]
    | cons c cs =>
      simp only [monics, List.mem_flatMap, List.mem_map, List.cons.injEq,
        List.length_cons, Nat.succ.injEq, List.mem_cons]
      constructor
      · rintro ⟨b,hb,t,ht,rfl,rfl⟩
        obtain ⟨hd,hs⟩ := (ih _).mp ht
        exact ⟨hd, fun b hb' => hb'.elim (fun e => e ▸ hb) (hs b)⟩
      · rintro ⟨hd,hs⟩
        exact ⟨c,hs c (Or.inl rfl),cs,(ih _).mpr ⟨hd,fun b hb => hs b (Or.inr hb)⟩,rfl,rfl⟩

/-- Inverse of the reversed monic polynomial 1+a₁T+...+a_dT^d. -/
def inverseUnit (a : List F) (n : Nat) : F :=
  match n with
  | 0 => 1
  | k+1 => - total (fun j : Fin (k+1) => a[j.val]?.getD 0 * inverseUnit a (k-j.val))
                  (List.finRange (k+1))
termination_by n
decreasing_by omega

def inverseMonic (a : List F) : Series F := shift a.length (inverseUnit a)

def powerSum (alphabet : List F) (d s : Nat) : Series F :=
  fun n => total (fun a => seriesPow (inverseMonic a) s n) (monics alphabet d)

def trunc (alphabet : List F) : Nat → Tuple → Series F
  | 0, [] => unitSeries
  | 0, _::_ => fun _ => 0
  | _+1, [] => unitSeries
  | d+1, s::t => addSeries (trunc alphabet d (s::t))
                           (product (powerSum alphabet d s) (trunc alphabet d t))

def S (alphabet : List F) : Int → Tuple → Series F
  | .negSucc 0, [] => unitSeries
  | .negSucc _, _ => fun _ => 0
  | .ofNat _, [] => fun _ => 0
  | .ofNat d, s::t => product (powerSum alphabet d s) (trunc alphabet d t)

theorem powerSum_below (alphabet : List F) (d s n : Nat) (hs : 0 < s) (hn : n < d) :
    powerSum alphabet d s n = 0 := by
  apply total_zero_of_members
  intro a ha
  have hd := ((mem_monics _ _ _).mp ha).1
  cases s with
  | zero => omega
  | succ s =>
    apply product_zero_below
    intro j hj
    simp [inverseMonic, shift, hd, show ¬d ≤ j by omega]

def zeta (alphabet : List F) (s : Tuple) : Series F :=
  if s = [] then fun _ => 0 else fun n => trunc alphabet (n+1) s n

theorem zeta_coeff (alphabet : List F) (n N : Nat) (s : Tuple) (hs : Valid s) (hne : s ≠ [])
    (hN : n+1 ≤ N) : trunc alphabet N s n = zeta alphabet s n := by
  simp only [zeta, if_neg hne]
  induction N with
  | zero => omega
  | succ d ih =>
    by_cases h : d = n
    · subst d; rfl
    have hd : n < d := by omega
    cases s with
    | nil => rfl
    | cons a s =>
      change trunc alphabet d (a::s) n + product _ _ n = _
      have hz : product (powerSum alphabet d a) (trunc alphabet d s) n = 0 :=
        product_zero_below _ _ _ (fun j hj => powerSum_below _ _ _ _ (hs a (by simp)) (by omega))
      rw [hz, Arithmetic.addZero]
      exact ih (by omega)

/-- The implication for relations in Theorem 1.1, once Hu's transfer map
and its evaluation identity are supplied. -/
theorem transfer_kernel {V W A : Type} [Zero A] (T : V → W)
    (Li : V → A) (ζ : W → A) (transfer : ∀ v, ζ (T v) = Li v) (v : V) :
    Li v = 0 ↔ ζ (T v) = 0 := by rw [transfer]

end Megaera.Zeta
