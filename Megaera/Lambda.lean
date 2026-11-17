import Megaera.ThirdCut
import Megaera.StuffleLaws
import Megaera.PrimitiveRows

namespace Megaera.Lambda
open Megaera.Cuts
def lambda (q : Nat) (s t : Tuple) : List (Tuple × Tuple) :=
  ((quasiShuffle [q-1] s).map (fun x => (x,t))) ++
    ((quasiShuffle [q-1] t).map (fun y => (s,y)))

private abbrev M (k : Nat) (s : Tuple) (f : Tuple → Nat) := total (quasiShuffle [k] s) f

private theorem mcons (k a : Nat) (s : Tuple) (f : Tuple → Nat) :
    M k (a::s) f = f (k::a::s) + M k s (fun x => f (a::x)) + f ((k+a)::s) := by
  simp only [M,StuffleLaws.peel,quasiShuffle_nil_left,total,Nat.add_zero]

private theorem join (k : Nat) (s t : Tuple) (f : Tuple → Nat) :
    M k (s++t) f + f (s++k::t) =
      M k s (fun v => f (v++t)) + M k t (fun v => f (s++v)) := by
  induction s generalizing f with
  | nil => simp [M,total,Nat.add_comm]
  | cons a s ih =>
    simp only [List.cons_append,mcons]
    have h := ih (fun v => f (a::v))
    omega

private theorem startM (q k : Nat) (t : Tuple) (f : Tuple → Nat) :
    total (start q t) (fun y => M k y f) =
      M k t (fun y => total (start q y) f) + total (start q t) (fun y => f (k::y)) := by
  cases t with
  | nil => simp [start,total,mcons,M,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
  | cons a t =>
    simp only [start,total,Nat.add_zero,mcons]
    have hadd := StuffleLaws.sum_add (quasiShuffle [k] t) (fun y => f (q::a::y))
      (fun y => f ((q+a)::y))
    simp only [M,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] at *
    omega

private theorem endingsM (k : Nat) (s : Tuple) (f : Tuple → Nat) :
    total (endings s) (fun y => M k y f) =
      M k s (fun y => total (endings y) f) + total (endings s) (fun y => f (y++[k])) := by
  have h := ThirdCut.total_perm (EndingCut.endings_cut s [k]) f
  simp only [cuts,List.map_cons,List.map_nil,total_flatMap,total_map,total,
    quasiShuffle_nil_right,List.append_nil,Nat.add_zero] at h
  simp only [M,StuffleLaws.comm_total [k]] 
  simpa only [Nat.add_comm] using h

private theorem exchange (xs : List A) (ys : List B) (f : A → B → Nat) :
    total xs (fun x => total ys (f x)) = total ys (fun y => total xs (fun x => f x y)) := by
  induction xs with
  | nil =>
    change 0 = total ys (fun _ => 0)
    induction ys with
    | nil => rfl
    | cons y ys ih => simpa only [total,Nat.zero_add] using ih
  | cons x xs ih => simp [total,StuffleLaws.sum_add,ih]

theorem L_lambda (q : Nat) (s t : Tuple) :
    ((lambda q s t).flatMap (fun p => L q p.1 p.2)).Perm ((L q s t).flatMap (quasiShuffle [q-1])) := by
  apply List.perm_iff_count.mpr
  intro a
  rw [count_total,count_total]
  generalize (fun y : Tuple => if y = a then 1 else 0) = f
  let k := q-1
  change total _ f = total _ f
  simp only [lambda,L,total_flatMap,total_append,total_map]
  rw [exchange (quasiShuffle [q-1] s) (start q t)]
  have h := startM q (q-1) t (fun y => f (s++y))
  have j : total (start q t) (fun y => M (q-1) (s++y) f + f (s++(q-1)::y)) =
      total (start q t) (fun y => M (q-1) s (fun x => f (x++y)) + M (q-1) y (fun x => f (s++x))) :=
    congrArg (total (start q t)) (funext (fun y => join (q-1) s y f))
  simp only [StuffleLaws.sum_add,M] at h j
  omega

theorem H_lambda (q : Nat) (s t : Tuple) :
    ((lambda q s t).flatMap (fun p => H q p.1 p.2)).Perm ((H q s t).flatMap (quasiShuffle [q-1])) := by
  apply List.perm_iff_count.mpr
  intro a
  rw [count_total,count_total]
  generalize (fun y : Tuple => if y = a then 1 else 0) = f
  let k := q-1
  let ys := quasiShuffle [k] t
  let es := endings s
  have je (v : Tuple) := congrArg (total ys) (funext (fun y => join k v y f))
  simp only [StuffleLaws.sum_add] at je
  have ej (y : Tuple) := endingsM k s (fun v => f (v++y))
  have a₁ := congrArg (total es) (funext je)
  have a₂ := congrArg (total ys) (funext ej)
  simp only [StuffleLaws.sum_add,List.append_assoc,List.cons_append,List.nil_append] at a₁ a₂
  simp only [lambda,H,concatenate,total_flatMap,total_append,total_map]
  change M k s (fun x => total (endings x) (fun v => total ys (fun y => f (v++y)))) +
    total ys (fun y => total es (fun v => M k y (fun x => f (v++x)))) =
    total es (fun v => total ys (fun y => M k (v++y) f))
  rw [exchange ys es]
  have p := exchange ys es (fun y v => M k v (fun x => f (x++y)))
  have p' := exchange ys es (fun y v => f (v++k::y))
  have swap : total ys (fun y => M k s (fun x => total (endings x) (fun v => f (v++y)))) =
      M k s (fun x => total (endings x) (fun v => total ys (fun y => f (v++y)))) := by
    rw [exchange ys (quasiShuffle [k] s)]
    exact congrArg (total (quasiShuffle [k] s)) (funext (fun x => exchange ys (endings x) _))
  dsimp only [es] at *
  omega

private theorem prefL (q : Nat) (z s t : Tuple) :
    L q (z++s) t = (L q s t).map (z++·) := by
  simp [L,List.map_map,Function.comp_def,List.append_assoc]

private theorem negativeL (q : Nat) (u s t : Tuple) :
    ((endings u).flatMap (fun z => (lambda q s t).flatMap (fun p => L q (z++p.1) p.2))).Perm
      (concatenate (endings u) ((L q s t).flatMap (quasiShuffle [q-1]))) := by
  unfold concatenate
  generalize endings u = zs
  induction zs with
  | nil => exact .nil
  | cons z zs ih =>
    apply List.Perm.append _ ih
    simp only [prefL, List.map_flatMap]
    simpa only [List.map_flatMap] using (L_lambda q s t).map (z++·)

/-- The signed L-image of the kernel generator in (2.17), including u empty. -/
theorem syzygyL {K : Type u} [OfNat K 1] [Neg K] (q : Nat) (u s t : Tuple) :
    (withCoeff (1:K) ((H q s t).flatMap (L q u)) ++ withCoeff (-(1:K))
      ((endings u).flatMap (fun z => (lambda q s t).flatMap (fun p => L q (z++p.1) p.2)))).Perm
    (liftPair (bStar u (generalP q s t))) := by
  unfold generalP
  rw [←List.map_flatMap, PrimitiveRows.bStar_expansion]
  apply List.Perm.append
  · rw [List.map_flatMap]; exact .refl _
  · exact (negativeL q u s t).map _

end Megaera.Lambda
