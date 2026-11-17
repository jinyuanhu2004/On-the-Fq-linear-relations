import Megaera.GradedBCP
import Megaera.Triangular

namespace Megaera.FourMinimum
open Megaera.Triangular Megaera.Finite Megaera.Carlitz Megaera.Paper

/-- Each possible merge with a singleton, enumerated from right to left. -/
def merges (k : Nat) : Tuple → List Tuple
  | [] => []
  | a::t => ((merges k t).map (a :: ·)) ++ [(k+a)::t]

def addLast (k : Nat) : Tuple → Tuple
  | [] => [k]
  | [a] => [k+a]
  | a::b::t => a :: addLast k (b::t)

def shortest (k : Nat) (t : Tuple) := if t = [] then [[k]] else merges k t

theorem merges_length {k : Nat} {t v : Tuple} (hv : v ∈ merges k t) : v.length = t.length := by
  induction t generalizing v with
  | nil => simp [merges] at hv
  | cons a t ih =>
    simp only [merges,List.mem_append,List.mem_map,List.mem_singleton] at hv
    rcases hv with ⟨z,hz,rfl⟩ | rfl
    · simp only [List.length_cons,ih hz]
    · rfl

private theorem longer_map {d : Nat} {ts : List Tuple} (h : ∀ t∈ts,d<t.length) (a : Nat) :
    ∀ t∈ts.map (a::·), d+1<t.length := by
  intro t ht; obtain ⟨z,hz,rfl⟩ := List.mem_map.mp ht
  have := h _ hz; simp; omega

/-- All the other stuffle terms are strictly longer. Equality here counts
all multiplicities even when two insertion terms are equal. -/
theorem stuffle_layer (k : Nat) (t : Tuple) :
    ∃ longer, (quasiShuffle [k] t).Perm (merges k t ++ longer) ∧
      ∀ z∈longer, t.length < z.length := by
  induction t with
  | nil => exact ⟨[[k]], by simp [merges], by simp⟩
  | cons a t ih =>
    obtain ⟨l,perm,h⟩ := ih
    refine ⟨(k::a::t)::(l.map (a::·)),?_,?_⟩
    · rw [quasiShuffle.eq_3]
      simp only [quasiShuffle_nil_left,List.map_cons,List.map_nil,merges]
      have hp := (perm.map (a::·))
      rw [List.map_append] at hp
      apply ((hp.append_left [k::a::t]).append_right [(k+a)::t]).trans
      simp only [List.singleton_append,List.append_assoc]
      apply List.perm_iff_count.mpr
      intro x; simp only [List.count_cons,List.count_append,List.count_nil]; omega
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · simp
      · exact longer_map h a _ hz


def raiseFirst (q : Nat) : Tuple → Tuple
  | [] => [q]
  | a::t => (q+a)::t

def width (t : Tuple) := max 1 t.length

theorem shortest_layer (k : Nat) (t : Tuple) : ∃ longer,
    (quasiShuffle [k] t).Perm (shortest k t ++ longer) ∧
    (∀ v ∈ shortest k t, v.length = width t) ∧
    ∀ v ∈ longer, width t < v.length := by
  cases t with
  | nil => exact ⟨[],by simp [shortest],by simp [shortest,width],by simp⟩
  | cons b t =>
    obtain ⟨l,hp,hl⟩ := stuffle_layer k (b::t)
    exact ⟨l,by simpa [shortest] using hp,fun v hv => by
      simpa [width] using merges_length (by simpa [shortest] using hv : v ∈ merges k (b::t)),
      by simpa [width] using hl⟩

private theorem interleave {α β : Type} (vs : List α) (f g : α → β) :
    (vs.flatMap (fun v => [f v,g v])).Perm ((vs.map g) ++ (vs.map f)) := by
  induction vs with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons,List.map_cons,List.cons_append,List.nil_append]
    exact ((List.Perm.swap ..).trans ((ih.cons _).cons _)).trans
      ((List.perm_middle (a:=f a) (l₁:=l.map g) (l₂:=l.map f)).symm.cons _)

private theorem mapStart (q : Nat) (v : Tuple) (hn : v ≠ []) (l : List Tuple) :
    ((l.map (v++·)).flatMap (start q)).Perm
      (l.map (raiseFirst q v ++ ·) ++ l.map ((q::v) ++ ·)) := by
  cases v with
  | nil => contradiction
  | cons a t => simp only [List.flatMap_map]; exact interleave l _ _

private theorem rlen (q : Nat) (s : Tuple) (hn : s≠[]) : (raiseFirst q s).length=s.length := by
  cases s <;> simp_all [raiseFirst]

private theorem inc_ne (a : Nat) (s : Tuple) : incLast (a::s) ≠ [] := by
  intro h; have := incLast_length a s; rw [h] at this; simp at this

theorem pos_layer (q : Nat) (s t : Tuple) (hn : s≠[]) :
    ∃ longer, ((H q s t).flatMap (start q)).Perm
       ((shortest (q-1) t).map ((raiseFirst q (incLast s))++·) ++ longer) ∧
       ∀ v∈longer, s.length + width t < v.length := by
  cases s with
  | nil => contradiction
  | cons a s =>
    let short := shortest (q-1) t
    let allT := quasiShuffle [q-1] t
    let v := incLast (a::s)
    let b := (a::s) ++ [1]
    have hv : v≠[] := inc_ne a s
    have hb : b≠[] := by simp [b]
    have lv : v.length=(a::s).length := incLast_length a s
    obtain ⟨long,ht,hs,hl⟩ := shortest_layer (q-1) t
    have allLen (y : Tuple) (hy : y ∈ allT) : width t ≤ y.length := by
      rcases List.mem_append.mp (ht.mem_iff.mp hy) with hy | hy
      · rw [hs y hy]; exact Nat.le_refl _
      · exact Nat.le_of_lt (hl y hy)
    have one := mapStart q v hv allT
    have two := mapStart q b hb allT
    let R := raiseFirst q v
    have split := ht.map (R++·)
    rw [List.map_append] at split
    refine ⟨(long.map (R++·)) ++ allT.map ((q::v)++·) ++
        (allT.map ((raiseFirst q b)++·) ++ allT.map ((q::b)++·)), ?_,?_⟩
    · change (((allT.map (v++·) ++ (allT.map (b++·) ++ [])).flatMap (start q))).Perm _
      rw [List.append_nil,List.flatMap_append]
      apply (one.append two).trans
      simpa only [List.append_assoc] using
        ((split.append_right (allT.map ((q::v)++·))).append_right
          (allT.map ((raiseFirst q b)++·) ++ allT.map ((q::b)++·)))
    · intro y hy
      simp only [List.mem_append,List.mem_map] at hy
      rcases hy with (⟨z,hz,rfl⟩ | ⟨z,hz,rfl⟩) | (⟨z,hz,rfl⟩ | ⟨z,hz,rfl⟩)
      · have := hl z hz; simp only [List.length_append,R,rlen _ _ hv,lv]; omega
      · have := allLen z hz; simp only [List.length_append,List.length_cons,lv]; omega
      · have := allLen z hz; simp only [List.length_append,rlen _ _ hb,b,List.length_cons,List.length_nil]; omega
      · have := allLen z hz; simp only [List.length_append,b,List.length_cons,List.length_nil]; omega


variable {F : Type u} [Arithmetic F] [Neg F]

/-- Coefficients at and below a tuple of depth |h|+d with prefix h. -/
def Window (h : Tuple) (d : Nat) (x : Tuple) : Prop :=
  ∃ v : Tuple, v.length=d ∧ ¬ Precedes (h++v) x

private theorem win_length {h x : Tuple} {d : Nat} (hx : Window h d x) :
    x.length ≤ h.length+d := by
  obtain ⟨v,hv,h⟩ := hx
  exact Nat.le_of_not_gt (fun z => h (Or.inl (by simpa [depth,hv] using z)))

omit [Neg F] in
private theorem absent (k : F) (l : List Tuple) (x : Tuple) (hn : x ∉ l) :
    coordinates (withCoeff k l) x = 0 := by
  apply total_zero_of_members
  intro e he; obtain ⟨v,hv,rfl⟩ := List.mem_map.mp he
  exact if_neg (fun eq : v=x => hn (eq ▸ hv))

private theorem tails_length (q : Nat) (s t y : Tuple)
    (hy : y ∈ (L q s t).flatMap (quasiShuffle [q-1])) :
    s.length + width t ≤ y.length := by
  obtain ⟨v,hv,hv'⟩ := List.mem_flatMap.mp hy
  have hh := singleton_stuffle_depth _ _ _ hv'
  obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hv
  cases t with
  | nil => simp [start] at hz; subst z; simpa [width] using hh
  | cons a t =>
    simp [start] at hz; rcases hz with rfl | rfl <;>
      simp only [List.length_append,List.length_cons] at hh <;> simp [width] <;> omega

private theorem negative_absent (q : Nat) (h s t x : Tuple)
    (hx : Window h (s.length+width t) x) :
    x ∉ concatenate (endings h) ((L q s t).flatMap (quasiShuffle [q-1])) := by
  intro hm
  obtain ⟨z,hz,h'⟩ := List.mem_flatMap.mp hm
  obtain ⟨y,hy,rfl⟩ := List.mem_map.mp h'
  have ly := tails_length q s t y hy
  obtain ⟨v,hv,early⟩ := hx
  apply early
  cases h with
  | nil =>
    simp [endings] at hz; subst z; apply Or.inl; simp [depth,hv]; omega
  | cons a h =>
    simp [endings] at hz
    rcases hz with rfl | rfl
    · by_cases e : y.length=v.length
      · exact Or.inr ⟨by simp only [depth,List.length_append,incLast_length,e],
          incLast_append_lex a h v y⟩
      · apply Or.inl; simp only [depth,List.length_append,incLast_length]; omega
    · apply Or.inl; simp only [depth,List.length_append,List.length_cons,List.length_nil]; omega

def lifted (q : Nat) (h s t : Tuple) : FormalSum F :=
  liftPair (bStar h (generalP q s t))

/-- On the entire initial depth/lex window, the actual signed prefix lift
has exactly its positive shortest-stuffle coefficients. -/
theorem lifted_layer (q : Nat) (h s t x : Tuple) (hn : s≠[])
    (hx : Window h (s.length + width t) x) :
    coordinates (lifted (F:=F) q h s t) x =
      coordinates (withCoeff 1 ((shortest (q-1) t).map
        (fun v => h ++ (raiseFirst q (incLast s) ++ v)))) x := by
  unfold lifted generalP
  rw [←List.map_flatMap,PrimitiveRows.bStar_expansion,BCPRows.coord_append,
    absent _ _ _ (negative_absent q h s t x hx),Arithmetic.addZero]
  obtain ⟨l,perm,hL⟩ := pos_layer q s t hn
  have hp := BCPRows.coord_perm ((perm.map (h++·)).map (fun y => ((1:F),y))) x
  simp only [List.map_append,List.map_map,Function.comp_def] at hp
  change coordinates (withCoeff (1:F) _) x = _
  rw [show coordinates (withCoeff (1:F) (List.map (h++·) ((H q s t).flatMap (start q)))) x =
      coordinates (withCoeff (1:F) (((shortest (q-1) t).map (fun v => h++(raiseFirst q (incLast s)++v))) ++ (l.map (h++·)))) x by
        simpa only [withCoeff,List.map_append,List.map_map,Function.comp_def] using hp]
  rw [withCoeff,List.map_append,BCPRows.coord_append]
  have no : x ∉ l.map (h++·) := by
    intro hm; obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hm
    have := win_length hx
    simp only [List.length_append] at this
    have := hL v hv; omega
  rw [show coordinates (((l.map (h++·)).map fun t => ((1:F),t))) x = 0 from absent _ _ _ no,
    Arithmetic.addZero]
  rfl


private theorem addLast_length (k : Nat) (a : Nat) (t : Tuple) :
    (addLast k (a::t)).length=(a::t).length := by
  induction t generalizing a with
  | nil => rfl
  | cons b t ih => simp only [addLast,List.length_cons,ih]

private theorem merges_head (k : Nat) (hk : 0<k) (a : Nat) (t : Tuple) :
    ∃ l, merges k (a::t) = addLast k (a::t)::l ∧
      ∀ y∈l, List.Lex (·<·) (addLast k (a::t)) y := by
  induction t generalizing a with
  | nil => exact ⟨[],rfl,by simp⟩
  | cons b t ih =>
    obtain ⟨l,hl,hg⟩ := ih b
    refine ⟨l.map (a::·) ++ [(k+a)::b::t],?_,?_⟩
    · change (merges k (b::t)).map (a::·) ++ _ = _
      rw [hl]; rfl
    · intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hy
        exact .cons (hg _ hz)
      · obtain rfl := List.mem_singleton.mp hy
        exact .rel (by omega)

private theorem shortest_head (k : Nat) (hk : 0<k) (t : Tuple) :
    ∃ l, shortest k t = addLast k t::l ∧
      ∀ y∈l, y.length=(addLast k t).length ∧ List.Lex (·<·) (addLast k t) y := by
  cases t with
  | nil => exact ⟨[],rfl,by simp⟩
  | cons a t =>
    obtain ⟨l,hl,hg⟩ := merges_head k hk a t
    refine ⟨l,by simpa [shortest] using hl,fun y hy => ⟨?_,hg y hy⟩⟩
    rw [addLast_length]
    exact merges_length (hl ▸ List.mem_cons_of_mem _ hy)

private theorem prefix_lex (h : Tuple) {s t : Tuple} (hs : List.Lex (·<·) s t) :
    List.Lex (·<·) (h++s) (h++t) := by
  induction h with
  | nil => exact hs
  | cons a h ih => exact .cons ih

/-- The minimum in depth-lex order, with its coefficient normalized to one. -/
def UnitMinimum (v : Tuple → F) (p : Tuple) : Prop :=
  v p = 1 ∧ ∀ x, Precedes x p → v x = 0

omit [Neg F] in
private theorem unit_of_layer (p : Tuple) (l : List Tuple) (v : Tuple → F)
    (later : ∀ x∈l, Precedes p x)
    (layer : ∀ x, (x=p ∨ Precedes x p) →
      v x = coordinates (withCoeff 1 (p::l)) x) : UnitMinimum v p := by
  constructor
  · rw [layer p (.inl rfl)]
    change (if p=p then (1:F) else 0) + coordinates (withCoeff 1 l) p = 1
    rw [if_pos rfl,absent 1 l p (fun hp => precedes_irrefl p (later p hp)),Arithmetic.addZero]
  · intro x hx
    rw [layer x (.inr hx)]
    apply absent
    intro hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact precedes_irrefl _ hx
    · exact precedes_irrefl p (precedes_trans (later x hm) hx)

private theorem early_win (h u x : Tuple) (hx : x=h++u ∨ Precedes x (h++u)) :
    Window h u.length x := by
  refine ⟨u,rfl,?_⟩
  rcases hx with rfl | hx
  · exact precedes_irrefl _
  · exact fun h => precedes_irrefl _ (precedes_trans h hx)

private theorem addLast_width (k : Nat) (t : Tuple) : (addLast k t).length=width t := by
  cases t with
  | nil => rfl
  | cons a t => simpa [width] using addLast_length k a t

private theorem head_length (q : Nat) (s : Tuple) (hn : s≠[]) :
    (raiseFirst q (incLast s)).length=s.length := by
  cases s with
  | nil => contradiction
  | cons a s => rw [rlen _ _ (inc_ne a s),incLast_length]

/-- Lemma 4.1(i,ii). At an empty tail, addLast returns the singleton (q−1). -/
theorem lemma_4_1_i_ii (q : Nat) (hq : 2≤q) (h s t : Tuple) (hn : s≠[]) :
    UnitMinimum (coordinates (lifted (F:=F) q h s t))
      (h ++ (raiseFirst q (incLast s) ++ addLast (q-1) t)) := by
  obtain ⟨l,hl,hg⟩ := shortest_head (q-1) (by omega) t
  let a := raiseFirst q (incLast s)
  apply unit_of_layer _ (l.map (fun z => h++(a++z)))
  · intro x hx; obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
    exact .inr ⟨by simp only [depth,List.length_append,hg y hy |>.1];rfl,
      prefix_lex h (prefix_lex a (hg y hy).2)⟩
  · intro x hx
    have win := early_win h (a++addLast (q-1) t) x hx
    rw [List.length_append,addLast_width,show a.length=s.length from head_length q s hn] at win
    rw [lifted_layer q h s t x hn win,hl]; rfl


private theorem lifted_merge_window (q : Nat) (h s t x : Tuple) (hn : s≠[])
    (hx : Window h (s.length+t.length) x) :
    coordinates (lifted (F:=F) q h s t) x =
      coordinates (withCoeff 1 ((merges (q-1) t).map
        (fun v => h ++ (raiseFirst q (incLast s) ++ v)))) x := by
  cases t with
  | cons a t => exact (lifted_layer q h s (a::t) x hn
      (by simpa [width] using hx)).trans (by simp [shortest])
  | nil =>
    have lx := win_length hx
    have win : Window h (s.length+width []) x := by
      refine ⟨List.replicate (s.length+width []) 0,by simp,?_⟩
      rintro (h' | ⟨h',_⟩) <;> simp [width,depth] at * <;> omega
    rw [lifted_layer q h s [] x hn win]
    apply absent
    intro hm
    simp [shortest] at hm
    have := congrArg List.length hm
    simp only [List.length_append,head_length q s hn,List.length_cons,List.length_nil] at this
    simp at lx; omega

private theorem merges_append (k : Nat) (a b : Tuple) :
    merges k (a++b) =
      (merges k b).map (a++·) ++ (merges k a).map (·++b) := by
  induction a with
  | nil => simp [merges]
  | cons a l ih =>
    change ((merges k (l++b)).map (a::·)) ++ [(k+a)::l++b] = _
    rw [ih]
    simp [merges,List.map_append,List.map_map,List.append_assoc,Function.comp_def]

private theorem inc_append (a b : Tuple) (hb : b≠[]) :
    incLast (a++b) = a++incLast b := by
  induction a with
  | nil => rfl
  | cons i t ih =>
    change incLast (i::(t++b)) = _
    cases eq : t++b with
    | nil => exact False.elim (hb (List.append_eq_nil_iff.mp eq).2)
    | cons j v => simp only [incLast, List.cons_append,←eq,ih]

private theorem first_append (q : Nat) (a b : Tuple) (hn : a≠[]) :
    raiseFirst q (a++b) = raiseFirst q a ++ b := by
  cases a <;> simp_all [raiseFirst]

private theorem addLast_inc (q : Nat) (hq : 2 ≤ q) (a : Nat) (t : Tuple) :
    addLast (q-1) (incLast (a::t)) = addLast q (a::t) := by
  induction t generalizing a with
  | nil => simp [incLast,addLast]; omega
  | cons b t ih =>
    change addLast (q-1) (a::incLast (b::t)) = _
    have hn := inc_ne b t
    have e := ih b
    cases he : incLast (b::t) with
    | nil => contradiction
    | cons c u => simp only [addLast];rw [←he,e]

private theorem suffix_lex {s t : Tuple} (hs : List.Lex (·<·) s t)
    (he : s.length=t.length) (u : Tuple) : List.Lex (·<·) (s++u) (t++u) := by
  induction hs with
  | nil => simp at he
  | rel h => exact .rel h
  | cons _ ih => exact .cons (ih (by simpa using he))

private theorem neg_remove (field : ConstantField F q) (a b : F) :
    (a+b)+(-a)=b := by
  calc
    _ = (-a)+(a+b) := Arithmetic.addComm _ _
    _ = ((-a)+a)+b := (Arithmetic.addAssoc ..).symm
    _ = (a+(-a))+b := by rw [Arithmetic.addComm (-a) a]
    _ = b := by rw [field.add_neg,zeroAdd]

/-- Lemma 4.1(iii). The surviving shortest terms are precisely the merges
inside u^{+1}. All merges in the last tuple occur in both lifts. -/
theorem lemma_4_1_iii (q : Nat) (field : ConstantField F q) (h s u t : Tuple)
    (hs : s≠[]) (hu : u≠[]) :
    UnitMinimum (fun x =>
      coordinates (lifted (F:=F) q h s (incLast u++t)) x +
      (-coordinates (lifted (F:=F) q h (incLast s++u) t) x))
      (h++(raiseFirst q (incLast s)++(addLast q u++t))) := by
  let A := raiseFirst q (incLast s)
  have iu : (incLast u).length=u.length := by
    cases u with | nil => contradiction | cons a z => exact incLast_length a z
  have iS : (incLast s).length=s.length := by
    cases s with | nil => contradiction | cons a z => exact incLast_length a z
  have nS : incLast s≠[] := by
    cases s with | nil => contradiction | cons a z => exact inc_ne a z
  have nU : incLast u≠[] := by
    cases u with | nil => contradiction | cons a z => exact inc_ne a z
  have nV : incLast s++u≠[] := by simp [hu]
  have bb : raiseFirst q (incLast (incLast s++u))= A++incLast u := by
    rw [inc_append _ _ hu,first_append _ _ _ nS]
  have dA : A.length=s.length := head_length q s hs
  have du : (addLast q u).length=u.length := by
    cases u with | nil => contradiction | cons a z => exact addLast_length q a z
  have bU : addLast (q-1) (incLast u) = addLast q u := by
    cases u with | nil => contradiction | cons a t => exact addLast_inc q field.two_le a t
  obtain ⟨l,hl,lg⟩ := shortest_head (q-1) (by have := field.two_le;omega) (incLast u)
  simp [shortest,nU,bU] at hl
  apply unit_of_layer _ (l.map (fun z => h++(A++(z++t))))
  · intro x hx; obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hx
    obtain ⟨lz,gz⟩ := lg z hz
    rw [bU] at lz gz
    exact .inr ⟨by simp only [depth,List.length_append,lz];rfl,
      prefix_lex h (prefix_lex A (suffix_lex gz lz.symm t))⟩
  · intro x hx
    have win := early_win h (A++(addLast q u++t)) x hx
    simp only [List.length_append,dA,du] at win
    have one := lifted_merge_window (F:=F) q h s (incLast u++t) x hs
      (by simpa only [List.length_append,iu] using win)
    have two := lifted_merge_window (F:=F) q h (incLast s++u) t x nV
      (by simpa only [List.length_append,iS,Nat.add_assoc] using win)
    rw [one,two,merges_append,bb,hl]
    simp only [List.map_append,List.map_map,Function.comp_def,List.append_assoc,withCoeff,
      List.map_cons,BCPRows.coord_append]
    exact neg_remove field _ _


/-- Prefix comparison in §4.2. If the incremented left labels have a common
continuation, the source-order inequality excludes a strictly shorter rival. -/
theorem prefix_options (a b : Nat) (s i u v r z : Tuple)
    (eqn : incLast (a::s) ++ u = incLast (b::i) ++ v)
    (order : ¬List.Lex (·<·) ((b::i)++z) ((a::s)++r)) :
    b::i = a::s ∨ ∃ l, b::i = incLast (a::s) ++ l ∧ l≠[] := by
  induction s generalizing a b i with
  | nil =>
    cases i with
    | nil => left; have e := List.cons.inj eqn; simp [incLast] at e; simp_all
    | cons j i =>
      have eq : a+1=b := (List.cons.inj eqn).1
      exact .inr ⟨j::i, by simp [incLast,eq],by simp⟩
  | cons j s ih =>
    cases i with
    | nil =>
      have eq : a=b+1 := (List.cons.inj eqn).1
      exact False.elim (order (.rel (by omega)))
    | cons k i =>
      have ⟨eq,tail⟩ := List.cons.inj eqn
      change a=b at eq
      subst b
      have ord : ¬List.Lex (·<·) ((k::i)++z) ((j::s)++r) := fun h => order (.cons h)
      rcases ih j k i tail ord with he | ⟨l,hl,hn⟩
      · left; rw [he]
      · right; exact ⟨l,congrArg (a::·) hl,hn⟩

def endHead : Tuple → Tuple
  | [] => [1]
  | a::s => incLast (a::s)

omit [Neg F] in
/-- Unique first term of the actual H-row, with coefficient one in the constants. -/
theorem H_minimum (q : Nat) (hq : 2≤q) (s t : Tuple) :
    UnitMinimum (coordinates (withCoeff (1:F) (H q s t))) (endHead s++addLast (q-1) t) := by
  obtain ⟨l,perm,hsh,hl⟩ := shortest_layer (q-1) t
  obtain ⟨c,hc,hg⟩ := shortest_head (q-1) (by omega) t
  let d := addLast (q-1) t
  let b := endHead s
  have cert : ∃ r, (H q s t).Perm (((b++d)::r)) ∧ ∀ z∈r, Precedes (b++d) z := by
    have hp := perm.map (b++·)
    simp only [hc,List.map_append,List.map_cons] at hp
    let rest := c.map (b++·) ++ l.map (b++·)
    have gl (z : Tuple) (hz : z∈rest) : Precedes (b++d) z := by
      rcases List.mem_append.mp hz with h | h <;> obtain ⟨v,hv,rfl⟩ := List.mem_map.mp h
      · refine .inr ⟨?_,prefix_lex b (hg v hv).2⟩
        simp only [depth,List.length_append,(hg v hv).1];rfl
      · apply Or.inl
        simp only [depth,List.length_append,d,addLast_width];have := hl v hv; omega
    cases s with
    | nil =>
      exact ⟨rest, by simpa only [H,endings,concatenate,List.flatMap_cons,List.flatMap_nil,List.append_nil,
        List.cons_append] using hp, gl⟩
    | cons a s =>
      let extra := (quasiShuffle [q-1] t).map (((a::s)++[1])++·)
      refine ⟨rest++extra,?_,?_⟩
      · simpa only [H,endings,concatenate,List.flatMap_cons,List.flatMap_nil,List.append_nil,
          List.cons_append,List.append_assoc,rest,extra,b,endHead] using hp.append_right extra
      · intro z hz; rcases List.mem_append.mp hz with h | h
        · exact gl z h
        · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp h
          have g : width t ≤ v.length := by
            rcases List.mem_append.mp (perm.mem_iff.mp hv) with h | h
            · rw [hsh v h]; exact Nat.le_refl _
            · exact Nat.le_of_lt (hl v h)
          left
          simp only [depth,List.length_append,b,endHead,incLast_length,List.length_cons,
            List.length_nil,d,addLast_width]; omega
  obtain ⟨r,hr,hg⟩ := cert
  exact unit_of_layer _ r _ hg (fun x _ => BCPRows.coord_perm (hr.map (fun z => ((1:F),z))) x)


private theorem srcEq (q : Nat) (h t : Tuple) :
    Splitting.source q h t = h ++ raiseFirst q t := by cases t <;> rfl

private theorem firstWidth (q : Nat) (t : Tuple) :
    (raiseFirst q t).length = width t := by cases t <;> simp [width,raiseFirst]

private theorem tailWidth (q : Nat) (t v : Tuple) (hv : v ∈ quasiShuffle [q-1] t) :
    width t ≤ v.length := by
  cases t with
  | nil => simp at hv; subst v; simp [width]
  | cons a t => simpa [width] using singleton_stuffle_depth (q-1) (a::t) v hv

/-- Classification of the rival left prefixes when the distinguished left
tuple is nonempty. Both tails may be terminal. -/
theorem competing_prefix (q : Nat) (s i t u v : Tuple) (hn : s≠[])
    (ord : Precedes (Splitting.source q s t) (Splitting.source q i u))
    (same : (incLast s++v).length = (Splitting.source q s t).length)
    (occ : incLast s++v ∈ H q i u) :
    i=s ∨ ∃ l, i=incLast s++l ∧ l≠[] := by
  rw [srcEq,srcEq] at ord; rw [srcEq] at same
  obtain ⟨e,he,hm⟩ := List.mem_flatMap.mp occ
  obtain ⟨y,hy,eq⟩ := List.mem_map.mp hm
  have ly := tailWidth q u y hy
  have dl : (s++raiseFirst q t).length ≤ (i++raiseFirst q u).length := by
    rcases ord with h | ⟨h,_⟩ <;> change _ ≤ _ <;> simp only [depth] at * <;> omega
  have dEq := congrArg List.length eq
  simp only [List.length_append,firstWidth] at dEq dl same
  cases i with
  | nil =>
    simp only [endings,List.mem_singleton] at he
    subst e
    simp only [List.length_nil,List.length_cons] at *; omega
  | cons b i =>
    rcases List.mem_cons.mp he with he | he
    · change e=incLast (b::i) at he; subst e
      have iv := incLast_length b i
      cases s with
      | nil => contradiction
      | cons a s =>
        apply prefix_options a b s i v y (raiseFirst q t) (raiseFirst q u) eq.symm
        intro opp
        rcases ord with lt | ⟨_,lt⟩
        · simp only [depth,List.length_append,firstWidth] at lt; omega
        · exact List.lex_irrefl Nat.lt_irrefl _ (List.lex_trans (fun zm yn => Nat.lt_trans zm yn) lt opp)
    · obtain rfl := List.mem_singleton.mp he
      simp only [List.length_append,List.length_cons,List.length_nil] at dEq dl
      omega


/-- At an empty distinguished prefix, the selected tuples start with 1.
Any nonempty competing prefix must begin with 1 and have depth at least
two. The corrected depth statement uses the effective terminal width. -/
theorem competing_empty_prefix (q : Nat) (hq : 2≤q) (i t u v : Tuple)
    (ord : Precedes (Splitting.source q [] t) (Splitting.source q i u))
    (valid : Valid i) (depth_v : v.length = width t)
    (occ : 1::v ∈ H q i u) :
    (i=[] ∧ width u=width t) ∨
      (∃ j l, i=1::j::l ∧ i.length+width u=width t+1) := by
  rw [srcEq,srcEq,List.nil_append] at ord
  obtain ⟨e,he,hm⟩ := List.mem_flatMap.mp occ
  obtain ⟨z,hz,eq⟩ := List.mem_map.mp hm
  have lz := tailWidth q u z hz
  have dl : width t ≤ i.length + width u := by
    rcases ord with h | ⟨h,_⟩ <;>
      simp only [depth,List.length_append,firstWidth] at h <;> omega
  have lenEq := congrArg List.length eq
  simp only [List.length_append,List.length_cons,depth_v] at lenEq
  have bigger (a : Nat) (j : Tuple) (ha : a=1)
      (ord' : Precedes (raiseFirst q t) ((a::j)++raiseFirst q u)) :
      width t < (a::j).length+width u := by
    rcases ord' with l | ⟨_,h⟩
    · simpa only [depth,List.length_append,firstWidth] using l
    · subst a
      cases t with
      | nil => rcases List.cons_lex_cons_iff.mp h with h | ⟨h,_⟩ <;> omega
      | cons k s =>
        rcases List.cons_lex_cons_iff.mp h with h | ⟨h,_⟩ <;> omega
  cases i with
  | nil =>
    simp only [endings,List.mem_singleton] at he
    subst e; left; refine ⟨rfl,?_⟩
    simp only [List.length_nil,List.length_cons] at dl lenEq; omega
  | cons a j =>
    rcases List.mem_cons.mp he with he | he
    · change e=incLast (a::j) at he; subst e
      rw [incLast_length] at lenEq
      cases j with
      | nil =>
        have e : a+1=1 := (List.cons.inj eq).1
        have ha := valid a (by simp)
        omega
      | cons j l =>
        have ea : a=1 := (List.cons.inj eq).1
        have hi := bigger a (j::l) ea ord
        right
        exact ⟨j,l,by rw [ea],by omega⟩
    · obtain rfl := List.mem_singleton.mp he
      have ea : a=1 := (List.cons.inj eq).1
      have hi := bigger a j ea ord
      simp only [List.length_append,List.length_cons,List.length_nil] at lenEq hi
      omega

end Megaera.FourMinimum
