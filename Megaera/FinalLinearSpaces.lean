import Megaera.FinalFiltration
import Megaera.FinalRankEngine

namespace Megaera.FinalLinearSpaces
open Megaera.Finite Megaera.Carlitz Megaera.Paper Megaera.Lift Megaera.SectionThreeSpaces
open Megaera.FinalFiltration Megaera.FinalRankEngine
variable {F : Type u} [Arithmetic F] [Neg F] {q w : Nat}

def combine (a : F) (p r : FormalSum F) := p ++ r.map fun e => (a*e.1,e.2)

omit [Neg F] in
theorem combine_coord (a : F) (p r : FormalSum F) (s : Tuple) :
    coordinates (combine a p r) s=coordinates p s+a*coordinates r s := by
  rw [combine,BCPRows.coord_append]
  apply congrArg (_+·)
  exact measure_scale a (fun e => if e.2=s then e.1 else 0)
    (fun k t => by by_cases h:t=s <;> simp only [h,if_true,if_false,Arithmetic.mulZero]) r

omit [Neg F] in
theorem combine_val (a : F) (p r : FormalSum F) (f : Tuple → Series F) (j : Nat) :
    valueAt f (combine a p r) j=valueAt f p j+a*valueAt f r j := by
  unfold combine valueAt; rw [total_append']
  exact congrArg (_+·) (measure_scale a (fun e => e.1 * f e.2 j) (fun _ _ => Arithmetic.mulAssoc ..) r)

omit [Neg F] in
theorem combine_hom (a : F) (p r : FormalSum F) (hp : homogeneous w p) (hr : homogeneous w r) :
    homogeneous w (combine a p r) := by
  intro e he
  rcases List.mem_append.mp he with h|h
  · exact hp e h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp h; exact hr v hv

omit [Neg F] in
private theorem clear_comb (a : F) (P Q R S : Series F) (h : cleared q P Q) (g : cleared q R S) :
    cleared q (fun i => P i+a*R i) (fun i => Q i+a*S i) := by
  have sh (m j) (P R : Series F) : shift m (fun i => P i+a*R i) j=shift m P j+a*shift m R j := by
    by_cases le : m≤j <;> simp only [shift,le,if_true,if_false,Arithmetic.mulZero,Arithmetic.addZero]
  letI : Std.Associative (α:=F) (·+·) := ⟨Arithmetic.addAssoc⟩
  letI : Std.Commutative (α:=F) (·+·) := ⟨Arithmetic.addComm⟩
  intro i; rw [sh,sh,←h i,←g i,Arithmetic.distrib]; dsimp only; ac_rfl

omit [Neg F] in
private theorem clear_empty : cleared q (fun _ => (0:F)) (fun _ => 0) := by
  intro j; simp [shift,Arithmetic.addZero]

theorem rel_linear : Linear (RelationVector (F:=F) q w) where
  zero := ⟨[],⟨by simp,fun _ => rfl⟩,rfl⟩
  addScaled := by
    rintro _ _ a ⟨p,⟨hp,vp⟩,rfl⟩ ⟨r,⟨hr,vr⟩,rfl⟩
    refine ⟨combine a p r,⟨combine_hom a p r hp hr,?_⟩,funext (combine_coord a p r)⟩
    intro j; exact (combine_val a p r (li q) j).trans (by
      change evaluate q p j+a*evaluate q r j=0; rw [vp,vr,Arithmetic.mulZero,Arithmetic.addZero])

theorem fixedR_linear : Linear (fixedR (F:=F) q w) where
  zero := ⟨[],⟨by simp,fun _ => rfl⟩,fun _ _ => rfl,rfl⟩
  addScaled := by
    rintro _ _ a ⟨p,⟨hp,vp⟩,fp,rfl⟩ ⟨r,⟨hr,vr⟩,fr,rfl⟩
    refine ⟨combine a p r,⟨combine_hom a p r hp hr,?_⟩,?_,funext (combine_coord a p r)⟩
    · intro j; exact (combine_val a p r (li q) j).trans (by
        change evaluate q p j+a*evaluate q r j=0; rw [vp,vr,Arithmetic.mulZero,Arithmetic.addZero])
    · intro d j; rw [combine_val,fp d j,fr d j,Arithmetic.mulZero,Arithmetic.addZero]

omit [Neg F] in
private theorem pair_comb (a : F) (p r P R : FormalSum F) :
    pairCoordinates (combine a p P) (combine a r R) =
      fun i => pairCoordinates p r i + a*pairCoordinates P R i := by
  funext ⟨b,s⟩; cases b <;> simp only [pairCoordinates,Bool.false_eq_true,if_true,if_false,combine_coord]

omit [Neg F] in
private theorem combine_cleared (a : F) (p r P R : FormalSum F) (f : Tuple → Series F)
    (h : cleared q (valueAt f p) (valueAt f r)) (g : cleared q (valueAt f P) (valueAt f R)) :
    cleared q (valueAt f (combine a p P)) (valueAt f (combine a r R)) := by
  rw [funext (combine_val a p P f),funext (combine_val a r R f)]
  exact clear_comb a _ _ _ _ h g

theorem u_linear : Linear (U (F:=F) q w) where
  zero := ⟨[],[],by simp [homogeneous],by simp [homogeneous],clear_empty,by funext ⟨b,s⟩; cases b <;> rfl⟩
  addScaled := by
    rintro _ _ a ⟨p,r,hp,hr,h,rfl⟩ ⟨P,R,hP,hR,g,rfl⟩
    exact ⟨_,_,combine_hom a p P hp hP,combine_hom a r R hr hR,
      combine_cleared a p r P R (li q) h g,pair_comb ..⟩

theorem fixedU_linear : Linear (fixedU (F:=F) q w) where
  zero := ⟨[],[],by simp [homogeneous],by simp [homogeneous],clear_empty,fun _ => clear_empty,
    by funext ⟨b,s⟩; cases b <;> rfl⟩
  addScaled := by
    rintro _ _ a ⟨p,r,hp,hr,h,hf,rfl⟩ ⟨P,R,hP,hR,g,gf,rfl⟩
    exact ⟨_,_,combine_hom a p P hp hP,combine_hom a r R hr hR,
      combine_cleared a p r P R (li q) h g,fun d => combine_cleared a p r P R _ (hf d) (gf d),pair_comb ..⟩

theorem stageR_linear (n : Nat) : Linear (stageR (F:=F) q w n) where
  zero := ⟨fixedR_linear.zero,fun _ _ => rfl⟩
  addScaled := by
    rintro x y a ⟨hx,h⟩ ⟨hy,g⟩
    exact ⟨fixedR_linear.addScaled x y a hx hy,fun s hs => by simp only [h s hs,g s hs,Arithmetic.mulZero,Arithmetic.addZero]⟩

theorem stageU_linear (n : Nat) : Linear (stageU (F:=F) q w n) where
  zero := ⟨fixedU_linear.zero,fun _ _ _ => rfl⟩
  addScaled := by
    rintro x y a ⟨hx,h⟩ ⟨hy,g⟩
    exact ⟨fixedU_linear.addScaled x y a hx hy,fun b s hs => by simp only [h b s hs,g b s hs,Arithmetic.mulZero,Arithmetic.addZero]⟩

end Megaera.FinalLinearSpaces
