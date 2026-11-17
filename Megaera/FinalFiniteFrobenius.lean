import Megaera.MainTheorems
import Megaera.FinalFiniteLists

/-! The q-power law in an algebra over a constant field of size q.
The proof uses interpolation over all q elements of the constant field. -/
namespace Megaera.FinalFiniteFrobenius
open Megaera.Finite Megaera.Paper
variable {F : Type u} [Arithmetic F]
local instance : Std.Associative (α:=F) (·*·) := ⟨Arithmetic.mulAssoc⟩
local instance : Std.Commutative (α:=F) (·*·) := ⟨Arithmetic.mulComm⟩
local instance : Std.Associative (α:=F) (·+·) := ⟨Arithmetic.addAssoc⟩
local instance : Std.Commutative (α:=F) (·+·) := ⟨Arithmetic.addComm⟩

private theorem enumeration [Neg F] (field : ConstantField F q) :
    ∃ xs : List F, xs.length=q ∧ xs.Nodup ∧ ∀ x,x∈xs := by
  obtain ⟨f,inject,onto⟩ := field.cardinality
  refine ⟨List.ofFn f,List.length_ofFn,?_,fun x => List.mem_ofFn.mpr (onto x)⟩
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj lt eq
  simp only [List.getElem_ofFn] at eq
  have e : i=j := congrArg Fin.val (inject _ _ eq)
  omega

private theorem cancel_mul [Neg F] (field : ConstantField F q) {a b c : F} (nz : c≠0)
    (eq : a*c=b*c) : a=b := by
  obtain ⟨d,inv⟩ := field.invertible c nz
  have h := congrArg (·*d) eq
  simpa only [Arithmetic.mulAssoc,inv,Arithmetic.mulOne] using h

private theorem prod_nonzero [Neg F] (field : ConstantField F q) {a b : F}
    (ha : a≠0) (hb : b≠0) : a*b≠0 := fun eq =>
  ha (cancel_mul field hb (eq.trans (zeroMul _).symm))

private def prod : List F → F
  | [] => 1
  | a::xs => a*prod xs

private theorem prod_perm {xs ys : List F} (p : xs.Perm ys) : prod xs=prod ys := by
  induction p with
  | nil => rfl
  | cons a _ ih => exact congrArg (a*·) ih
  | swap => simp only [prod]; ac_rfl
  | trans _ _ ih jh => exact ih.trans jh

private theorem prod_scale (a : F) (xs : List F) :
    prod (xs.map (·*a)) = prod xs * power a xs.length := by
  induction xs with
  | nil => simp [prod,power,Arithmetic.mulOne]
  | cons b xs ih => simp only [List.map_cons,List.length_cons,prod,ih,power]; ac_rfl

private theorem prod_ne [Neg F] (field : ConstantField F q) (xs : List F) (nz : 0∉xs) :
    prod xs≠0 := by
  induction xs with
  | nil => exact Ne.symm field.nontrivial
  | cons a xs ih => exact prod_nonzero field (fun e => nz (by simp [e])) (ih (fun h => nz (by simp [h])))



/-- Fermat's identity, using the product of the q−1 nonzero elements. -/
theorem scalar_power [Neg F] (field : ConstantField F q) (a : F) : power a q=a := by
  classical
  obtain ⟨xs,size,nd,all⟩ := enumeration field
  let ys := xs.erase 0
  have nz : 0∉ys := nd.not_mem_erase
  have card : ys.length+1=q := by
    have eq := List.length_erase_of_mem (all 0)
    dsimp [ys]; have qpos := field.two_le; omega
  rw [←card,power]
  by_cases az : a=0
  · rw [az,Arithmetic.mulZero]
  · have yn : ys.Nodup := nd.erase _
    have mapped : (ys.map (·*a)).Nodup := List.pairwise_map.mpr
      (yn.imp (fun ne eq => ne (cancel_mul field az eq)))
    have contains (b : F) : b∈ys ↔ b≠0 := by simp [ys,nd.mem_erase_iff,all]
    have perm := FinalFiniteLists.perm_of_nodup (ys.map (·*a)) ys mapped yn (by
      intro x; rw [List.mem_map,contains]
      constructor
      · rintro ⟨b,hb,rfl⟩; exact prod_nonzero field ((contains b).mp hb) az
      · intro hx
        obtain ⟨b,ab⟩ := field.invertible a az
        have bn : b≠0 := fun z => field.nontrivial (by simpa [z,Arithmetic.mulZero] using ab)
        refine ⟨x*b,(contains _).mpr (prod_nonzero field hx bn),?_⟩
        rw [Arithmetic.mulAssoc,Arithmetic.mulComm b,ab,Arithmetic.mulOne])
    have hp := (prod_scale a ys).symm.trans (prod_perm perm)
    have unit : power a ys.length=1 := cancel_mul field (prod_ne field ys nz)
      (by simpa [Arithmetic.mulComm (power a ys.length), oneMul] using hp)
    rw [unit,oneMul]

private theorem cancel_add [Neg F] (field : ConstantField F q) {a b c : F}
    (eq : a+c=b+c) : a=b := by
  have h := congrArg (·+(-c)) eq
  simpa only [Arithmetic.addAssoc,field.add_neg,Arithmetic.addZero] using h

private theorem add_mul (x y z : F) : (x+y)*z = x*z + y*z := by
  rw [Arithmetic.mulComm,Arithmetic.distrib,Arithmetic.mulComm z x,Arithmetic.mulComm z y]

private def eval (x : F) : List F → F
  | [] => 0
  | c::xs => c+x*eval x xs

/-- Coefficients of (P(X)−P(a))/(X−a), with no division in the field. -/
private def slope (a : F) : List F → List F
  | [] | [_] => []
  | _::b::xs => eval a (b::xs)::slope a (b::xs)

private theorem slope_len (a : F) (p : List F) : (slope a p).length=p.length-1 := by
  induction p with
  | nil => rfl
  | cons b p ih =>
    cases p with
    | nil => rfl
    | cons d p => simp only [slope,List.length_cons] at *; omega

private theorem diff_eval (a x : F) (p : List F) :
    eval x p + a*eval x (slope a p)=eval a p + x*eval x (slope a p) := by
  induction p with
  | nil => simp [slope,eval,Arithmetic.mulZero]
  | cons b p ih =>
    cases p with
    | nil => simp [slope,eval,Arithmetic.mulZero]
    | cons d p =>
      let t := eval x (slope a (d::p))
      change eval x (d::p)+a*t=eval a (d::p)+x*t at ih
      change (b+x*eval x (d::p))+a*(eval a (d::p)+x*t)=
        (b+a*eval a (d::p))+x*(eval a (d::p)+x*t)
      rw [Arithmetic.distrib a,Arithmetic.distrib x]
      calc
        _ = (b+a*eval a (d::p))+x*(eval x (d::p)+a*t) := by rw [Arithmetic.distrib]; ac_rfl
        _ = _ := by rw [ih,Arithmetic.distrib]

private theorem zero_from_slope (a : F) (p : List F) (root : eval a p=0)
    (zeros : ∀ b∈slope a p,b=0) : ∀ b∈p,b=0 := by
  induction p with
  | nil => simp
  | cons b p ih =>
    have sub : eval a p=0 := by
      cases p with
      | nil => rfl
      | cons c p => exact zeros _ (by simp [slope])
    have bz : b=0 := by simpa only [eval,sub,Arithmetic.mulZero,Arithmetic.addZero] using root
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact bz
    · apply ih sub _ _ hj
      intro c hc
      apply zeros
      cases p with
      | nil => simp [slope] at hc
      | cons => simp only [slope,List.mem_cons]; exact .inr hc

/-- A polynomial with at least its coefficient count in distinct roots vanishes. -/
private theorem interpolate [Neg F] (field : ConstantField F q) (roots p : List F)
    (nd : roots.Nodup) (size : p.length≤roots.length)
    (vanishes : ∀ x∈roots,eval x p=0) : ∀ c∈p,c=0 := by
  induction roots generalizing p with
  | nil => have e : p=[] := List.length_eq_zero_iff.mp (by simpa using size)
           simp [e]
  | cons a roots ih =>
    obtain ⟨apart,smaller⟩ := List.nodup_cons.mp nd
    have az := vanishes a (by simp)
    apply zero_from_slope a p az
    apply ih _ smaller (by rw [slope_len]; simp at size; omega)
    intro x hx
    have he := diff_eval a x p
    rw [az,vanishes x (by simp [hx]),zeroAdd,zeroAdd] at he
    apply Classical.byContradiction
    intro nz
    exact apart (cancel_mul field nz he ▸ hx)

private def step (a : F) : List F → List F
  | [] => [a]
  | b::xs => (a+b)::step b xs

private def row : Nat → List F
  | 0 => [1]
  | n+1 => step 0 (row n)

private theorem step_size (a : F) (xs : List F) : (step a xs).length=xs.length+1 := by
  induction xs generalizing a with
  | nil => rfl
  | cons b xs ih => simp [step,ih]

private theorem step_last (a : F) (xs : List F) :
    ∃ ys, step a (xs++[1])=ys++[1] := by
  induction xs generalizing a with
  | nil => exact ⟨[a+1],rfl⟩
  | cons b xs ih =>
    obtain ⟨ys,eq⟩ := ih b
    exact ⟨(a+b)::ys,congrArg ((a+b)::·) eq⟩

private theorem row_form (n : Nat) :
    ∃ mid : List F, row (n+1) = 1::(mid++[1]) ∧ mid.length=n := by
  induction n with
  | zero => exact ⟨[],by simp [row,step,zeroAdd],rfl⟩
  | succ n ih =>
    obtain ⟨mid,form,len⟩ := ih
    obtain ⟨ys,eq⟩ := step_last (1:F) mid
    have sz := step_size (1:F) (mid++[1])
    refine ⟨ys,?_,?_⟩
    · change step 0 (row (n+1)) = _
      rw [form,step,eq,zeroAdd]
    · rw [eq] at sz; simp at sz; omega

private def hom (u v : F) : List F → F
  | [] => 0
  | c::xs => c*power u xs.length + v*hom u v xs

private theorem hom_step (u v a : F) (xs : List F) :
    hom u v (step a xs)=a*power u xs.length+(u+v)*hom u v xs := by
  induction xs generalizing a with
  | nil => simp [hom,step,power,Arithmetic.mulZero,Arithmetic.addZero]
  | cons b xs ih =>
    simp only [step,hom,step_size,ih,List.length_cons,power,add_mul,Arithmetic.distrib]
    ac_rfl

private theorem hom_row (u v : F) (n : Nat) : hom u v (row n)=power (u+v) n := by
  induction n with
  | zero => simp [row,hom,power,Arithmetic.mulOne,Arithmetic.mulZero,Arithmetic.addZero]
  | succ n ih =>
    rw [row,hom_step,zeroMul,zeroAdd,ih,power,Arithmetic.mulComm]

private theorem hom_append_one (u v : F) (xs : List F) :
    hom u v (xs++[1])=u*hom u v xs+power v xs.length := by
  induction xs with
  | nil => simp [hom,power,oneMul,Arithmetic.mulZero,zeroAdd,Arithmetic.addZero]
  | cons c xs ih =>
    simp only [List.cons_append,hom,List.length_append,List.length_cons,List.length_nil,
      ih,power,Arithmetic.distrib]
    ac_rfl

private theorem hom_eval (x : F) (p : List F) : hom 1 x p=eval x p := by
  have one (n : Nat) : power (1:F) n=1 := by
    induction n <;> simp_all [power,Arithmetic.mulOne]
  induction p with
  | nil => rfl
  | cons c xs ih => simp [hom,eval,one,ih,Arithmetic.mulOne]

private theorem zero_middle [Neg F] (field : ConstantField F q) :
    ∃ mid : List F, row q=1::(mid++[1]) ∧ mid.length+1=q ∧ ∀ c∈mid,c=0 := by
  classical
  have qpos := field.two_le
  obtain ⟨mid,hrow,hsize⟩ := row_form (F:=F) (q-1)
  have pred : q-1+1=q := by omega
  rw [pred] at hrow
  have size : mid.length+1=q := by omega
  refine ⟨mid,hrow,size,?_⟩
  obtain ⟨xs,len,distinct,all⟩ := enumeration field
  apply interpolate field (xs.erase 0) mid (distinct.erase _)
    (by rw [List.length_erase_of_mem (all 0),len]; omega)
  intro x mem
  have nz := (distinct.mem_erase_iff.mp mem).1
  have he := hom_row (1:F) x q
  rw [hrow,hom,hom_append_one,oneMul,List.length_append] at he
  have one (n : Nat) : power (1:F) n = 1 := by
    induction n <;> simp_all [power,Arithmetic.mulOne]
  rw [one,oneMul,hom_eval,Arithmetic.distrib,Arithmetic.mulComm x (power x mid.length),
    ←(show power x (mid.length+1)=power x mid.length*x from rfl),size,
    scalar_power field x,scalar_power field (1+x)] at he
  have zero : x*eval x mid=0 := cancel_add field (c:=1+x) (by
    calc _ = 1 + (x*eval x mid+x) := by ac_rfl
         _ = 1+x := he
         _ = 0+(1+x) := (zeroAdd _).symm)
  exact cancel_mul field nz (by simpa only [Arithmetic.mulComm (eval x mid),zeroMul] using zero)

private theorem map_step {K : Type v} [Arithmetic K] (ι : F→K)
    (add : ∀ a b,ι (a+b)=ι a+ι b) (x : F) (p : List F) :
    (step x p).map ι = step (ι x) (p.map ι) := by
  induction p generalizing x with
  | nil => rfl
  | cons c p ih => simp [step,ih,add]

private theorem map_row {K : Type v} [Arithmetic K] (ι : F→K)
    (zero : ι 0=0) (one : ι 1=1) (add : ∀ a b,ι (a+b)=ι a+ι b) (n : Nat) :
    (row n).map ι = row n := by
  induction n with
  | zero => simp [row,one]
  | succ n ih => simp only [row,map_step ι add,ih,zero]

private theorem hom_zero (u v : F) (p : List F) (zeros : ∀ c∈p,c=0) :
    hom u v p = 0 := by
  induction p with
  | nil => rfl
  | cons c p ih =>
    rw [hom,zeros c (by simp),zeroMul,ih (fun a ha => zeros a (by simp [ha])),Arithmetic.mulZero,
      Arithmetic.addZero]

/-- Freshman's dream, for every commutative algebra carrying the constants.
Only preservation of zero, one and addition by the coefficient map is needed. -/
theorem power_additive [Neg F] (field : ConstantField F q) {K : Type v} [Arithmetic K]
    (ι : F→K) (zero : ι 0=0) (one : ι 1=1) (add : ∀ a b,ι (a+b)=ι a+ι b)
    (u v : K) : power (u+v) q=power u q+power v q := by
  obtain ⟨mid,form,len,zeros⟩ := zero_middle field
  have eqn := congrArg (List.map ι) form
  simp only [map_row ι zero one add,List.map_cons,List.map_append,List.map_nil,one] at eqn
  rw [←hom_row,eqn,hom,hom_append_one,hom_zero _ _ _ (by
    intro c hc; obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hc; rw [zeros a ha,zero])]
  simp only [Arithmetic.mulZero,zeroAdd,List.length_append,List.length_map,
    List.length_cons,List.length_nil,len,oneMul,power]
  rw [Arithmetic.mulComm v,←power]
  exact congrArg (fun n => power u q+power v n) len

private theorem right_inverse_unique [Neg F] (invs : ∀ a : F,a+ -a=0) (x y : F) (h : x+y=0) :
    y = -x := by
  calc
    y = 0+y := (zeroAdd _).symm
    _ = (x+ -x)+y := by rw [invs]
    _ = (x+y)+ -x := by ac_rfl
    _ = -x := by rw [h,zeroAdd]

/-- Difference form of Frobenius, with the same cardinality q as the field. -/
theorem power_subtractive [Neg F] (field : ConstantField F q) {K : Type v} [Arithmetic K]
    [Neg K] (inv : ∀ a : K,a+ -a=0) (ι : F→K) (zero : ι 0=0) (one : ι 1=1)
    (add : ∀ a b,ι (a+b)=ι a+ι b) (u v : K) :
    power (u+ -v) q=power u q+ -(power v q) := by
  have qpos := field.two_le
  have z : power (0:K) q=0 := by
    rw [←Nat.sub_add_cancel (show 1≤q by omega),power,Arithmetic.mulZero]
  have h := (power_additive field ι zero one add v (-v)).symm
  rw [inv,z] at h
  rw [power_additive field ι zero one add, right_inverse_unique inv _ _ h]

end Megaera.FinalFiniteFrobenius
