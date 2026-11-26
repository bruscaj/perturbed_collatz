import Lean

/-! `pad ++ [false, true]` lists one lap in reverse traversal order. The drop is
at heights one then zero in forward time. `Residue n` has modulus `q = n+1`.
Choice lists are also read from the tail first. `progression_steering` constructs
a class of targets; it does not assert that a specified integer belongs to it. -/

namespace ProgressionSteering

def height : Bool → Int
  | false => 0
  | true => 1

def forward (high : Bool) (value : Int) : Int :=
  let raw := value + height high
  (if raw % 2 = 0 then raw / 2 else (3 * raw + 1) / 2) - height high

def Branch (high odd : Bool) (parent target : Int) : Prop :=
  (parent + height high) % 2 = height odd ∧ forward high parent = target

theorem drop_branches (k : Int) :
    Branch false false (6*k+4) (3*k+2) ∧ Branch true true (4*k+2) (6*k+4) ∧
  Branch false true (2*k+1) (3*k+2) ∧ Branch true false (4*k+3) (2*k+1) ∧
  (4*k+3)-(4*k+2) = 1 := by
  simp only [Branch, forward, height]
  repeat' constructor <;> (try split) <;> omega

def evenPrefix : List Bool → Int → Int
  | [], value => value
  | high :: rest, value => evenPrefix rest (2 * value + height high)

def replay : List Bool → Int → Int
  | [], seed => seed
  | high :: rest, seed => forward high (replay rest seed)

theorem evenPrefix_affine (pad : List Bool) (value delta : Int) :
    evenPrefix pad (value + delta) = evenPrefix pad value + 2^pad.length * delta := by
  induction pad generalizing value delta with
  | nil => simp [evenPrefix]
  | cons high rest ih =>
    simp only [evenPrefix, List.length_cons, Int.pow_succ]
    rw [show 2*(value+delta)+height high = (2*value+height high)+2*delta by omega, ih]
    simp only [Int.mul_assoc]

private theorem replay_even (pad : List Bool) (value : Int) :
    replay pad (evenPrefix pad value) = value := by
  induction pad generalizing value with
  | nil => rfl
  | cons high rest ih =>
    simp only [evenPrefix, replay, ih, forward]
    split <;> omega

private theorem replay_append (first rest : List Bool) (seed : Int) :
    replay (first ++ rest) seed = replay first (replay rest seed) := by
  induction first with
  | nil => rfl
  | cons high tail ih => exact congrArg (forward high) ih

theorem lap_replay (pad : List Bool) (value k : Int) (gate : evenPrefix pad value = 3*k+2) :
  replay (pad ++ [false, true]) (4*k+2) = value ∧
  replay (pad ++ [false, true]) (4*k+3) = value := by
  obtain ⟨evenLow, oddHigh, oddLow, evenHigh, _⟩ := drop_branches k
  constructor <;> simp only [replay_append, replay, oddHigh.2, evenLow.2, evenHigh.2, oddLow.2,
    ← gate, replay_even]

abbrev Residue (n : Nat) := Fin (n+1)

def shift {n} (x : Residue n) : Residue n := ⟨(x.val+1) % (n+1), Nat.mod_lt _ (by omega)⟩

private theorem orbit {n} {C : Residue n → Prop} (x : Residue n) (hx : C x)
    (step : ∀ a, C a → C (shift a)) (y : Residue n) : C y := by
  have walk (d : Nat) : C ⟨(x.val+d) % (n+1), Nat.mod_lt _ (by omega)⟩ := by
    induction d with
    | zero => simpa [Nat.mod_eq_of_lt x.isLt] using hx
    | succ d ih => simpa [shift, Nat.mod_add_mod, Nat.add_assoc] using step _ ih
  have dist : x.val+(n+1+y.val-x.val) = y.val+(n+1) := by have := x.isLt; omega
  simpa [dist, Nat.add_mod_right, Nat.mod_eq_of_lt y.isLt] using walk (n+1+y.val-x.val)

theorem invariant_all {n} (C : Residue n → Prop) (F : Residue n → Residue n) (x : Residue n)
    (member : C x) (onto : ∀ y, C y → ∃ z, C z ∧ F z = y)
    (plus : ∀ z, C z → C (shift (F z))) : ∀ y, C y := by
  apply orbit x member
  intro y hy
  obtain ⟨z, hz, rfl⟩ := onto y hy
  exact plus z hz

private theorem size_le {α : Type} [DecidableEq α] {xs ys : List α} (nd : xs.Nodup)
    (sub : ∀ a ∈ xs, a ∈ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨fresh, tail⟩ := List.nodup_cons.mp nd
    have mem := sub a List.mem_cons_self
    have small := ih (ys := ys.erase a) tail (fun b hb =>
      (List.mem_erase_of_ne (by rintro rfl; exact fresh hb)).mpr (sub b (List.mem_cons_of_mem _ hb)))
    have := List.length_pos_of_mem mem
    rw [List.length_erase_of_mem mem] at small
    simp only [List.length_cons]; omega

private theorem range_distinct (n : Nat) : (List.finRange (n+1)).Nodup := by
  apply List.pairwise_iff_getElem.mpr
  intro i j _ _ lt eq
  exact (Nat.ne_of_lt lt) (by simpa using congrArg Fin.val eq)

private theorem full_iff {n} (xs : List (Residue n)) (nd : xs.Nodup) :
    (∀ y, y ∈ xs) ↔ xs.length = n+1 := by
  let residues := List.finRange (n+1)
  have every (y : Residue n) : y ∈ residues := List.mem_ofFn.mpr ⟨y,rfl⟩
  have bound {s : List (Residue n)} (hs : s.Nodup) : s.length ≤ n+1 := by
    simpa [residues] using size_le hs (fun y _ => every y)
  constructor
  · intro all
    exact Nat.le_antisymm (bound nd) (by simpa using size_le (range_distinct n) (fun y _ => all y))
  · intro len y
    by_cases h : y ∈ xs
    · exact h
    · have impossible := bound (List.nodup_cons.mpr ⟨h, nd⟩)
      simp [len] at impossible
      omega

def steer {n} (F : Residue n → Residue n) : List Bool → Residue n → Residue n
  | [], x => x
  | b :: bs, x => if b then shift (F (steer F bs x)) else F (steer F bs x)

theorem exact_choices {n} (F : Residue n → Residue n) (inj : ∀ a b, F a = F b → a = b)
    (x y : Residue n) : ∃ w : List Bool, w.length = n ∧ steer F w x = y := by
  have grow (t : Nat) (ht : t ≤ n) : ∃ xs : List (Residue n), xs.Nodup ∧ xs.length = t+1 ∧
      ∀ z ∈ xs, ∃ w : List Bool, w.length = t ∧ steer F w x = z := by
    induction t with
    | zero =>
      refine ⟨[x], by simp, rfl, ?_⟩
      intro z hz
      exact ⟨[], rfl, (List.mem_singleton.mp hz).symm⟩
    | succ t ih =>
      obtain ⟨xs, nd, len, paths⟩ := ih (by omega)
      let im := xs.map F
      have nd' : im.Nodup := List.pairwise_map.mpr (nd.imp fun h eq => h (inj _ _ eq))
      have len' : im.length = t+1 := by simpa [im] using len
      obtain ⟨z, hz, miss⟩ : ∃ z, z ∈ im ∧ shift z ∉ im := by
        apply Classical.byContradiction
        intro no
        obtain ⟨a, ha⟩ := List.length_pos_iff_exists_mem.mp (by omega : 0 < im.length)
        have all := orbit (C := fun v => v ∈ im) a ha (fun b hb => Classical.byContradiction (fun h => no ⟨b,hb,h⟩))
        have := (full_iff im nd').mp all
        omega
      have back {v} (hv : v ∈ im) : ∃ w : List Bool, w.length = t ∧ F (steer F w x) = v := by
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
        obtain ⟨w, hw, eq⟩ := paths a ha
        exact ⟨w, hw, congrArg F eq⟩
      refine ⟨shift z :: im, List.nodup_cons.mpr ⟨miss, nd'⟩, by simp [len'], ?_⟩
      intro v hv
      rcases List.mem_cons.mp hv with rfl | inside
      · obtain ⟨w, hw, eq⟩ := back hz
        exact ⟨true :: w, by simp [hw], congrArg shift eq⟩
      · obtain ⟨w, hw, eq⟩ := back inside
        exact ⟨false :: w, by simp [hw], eq⟩
  obtain ⟨xs, nd, len, paths⟩ := grow n (Nat.le_refl _)
  exact paths y ((full_iff xs nd).mpr len y)

def Permutes {n} (F : Residue n → Residue n) : Prop :=
  (∀ x y, F x = F y → x = y) ∧ (∀ y, ∃ x, F x = y)

private theorem perm_of_inj {n} {F : Residue n → Residue n} (inj : ∀ x y, F x = F y → x = y) :
    Permutes F := by
  refine ⟨inj, fun y => ?_⟩
  let im := (List.finRange (n+1)).map F
  have nd : im.Nodup := List.pairwise_map.mpr ((range_distinct n).imp fun h eq => h (inj _ _ eq))
  obtain ⟨x, _, eq⟩ := List.mem_map.mp ((full_iff im nd).mpr (by simp [im]) y)
  exact ⟨x, eq⟩

def reduce (n : Nat) (z : Int) : Residue n := ⟨(z % (n+1 : Nat)).toNat, by
  have pos : (0 : Int) < (↑(n+1) : Int) := by omega
  exact (Int.toNat_lt (Int.emod_nonneg _ (by omega))).mpr (Int.emod_lt_of_pos _ pos)⟩

private theorem reduce_val (n : Nat) (z : Int) : ((reduce n z).val : Int) = z % (n+1 : Nat) :=
  Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))

private theorem reduce_eq {n : Nat} {a b : Int} : reduce n a = reduce n b ↔ (↑(n+1) : Int) ∣ a-b := by
  rw [Int.dvd_iff_emod_eq_zero, ← Int.emod_eq_emod_iff_emod_sub_eq_zero]
  constructor
  · intro eq; simpa only [reduce_val] using congrArg (fun r : Residue n => (r.val : Int)) eq
  · intro eq; exact Fin.ext (congrArg Int.toNat eq)

private theorem reduce_fin {n} (x : Residue n) : reduce n x.val = x := by
  apply Fin.ext; exact Nat.mod_eq_of_lt x.isLt

def affine {n : Nat} (a : Nat) (b : Int) (x : Residue n) : Residue n := reduce n (a * (x.val : Int) + b)

private theorem affine_lift {n} (a : Nat) (b z : Int) : affine a b (reduce n z) = reduce n (a*z+b) := by
  apply reduce_eq.mpr
  rw [reduce_val, show (a : Int)*(z%(n+1:Nat))+b-(a*z+b) = a*((z%(n+1:Nat))-z) by rw [Int.mul_sub]; omega]
  exact Int.dvd_trans Int.dvd_emod_sub_self (Int.dvd_mul_left _ _)

theorem affine_permutation {n a : Nat} (b : Int) (unit : (n+1).gcd a = 1) : Permutes (affine (n := n) a b) := by
  apply perm_of_inj
  intro x y eq
  have div := reduce_eq.mp eq
  rw [show (a : Int)*x.val+b-(a*y.val+b) = a*((x.val:Int)-y.val) by rw [Int.mul_sub]; omega] at div
  have nd : n+1 ∣ a * ((x.val:Int)-y.val).natAbs := by
    simpa only [Int.natAbs_mul, Int.natAbs_ofNat] using Int.natAbs_dvd_natAbs.mpr div
  have small := Nat.dvd_gcd_mul_iff_dvd_mul.mpr nd
  rw [unit, Nat.one_mul] at small
  simpa only [reduce_fin] using (reduce_eq (n := n) (a := (x.val:Int)) (b := y.val)).mpr (Int.natAbs_dvd_natAbs.mp small)

theorem crt_lift {n m : Nat} (unit : (n+1).gcd m = 1) (base : Int) (x : Residue n) :
    ∃ c : Int, reduce n c = x ∧ (m:Int) ∣ c-base := by
  obtain ⟨r, hit⟩ := (affine_permutation base unit).2 x
  exact ⟨(m:Int)*r.val+base, hit, r.val, by omega⟩

private theorem factor_unit {n a : Nat} (unit : (n+1).gcd 6 = 1) (div : a ∣ 6) : (n+1).gcd a = 1 :=
  Nat.eq_one_of_dvd_one (by simpa only [unit] using Nat.gcd_dvd_gcd_of_dvd_right (n+1) div)

private theorem thirds {n} (unit : (n+1).gcd 6 = 1) : Permutes (affine (n := n) 3 2) :=
  affine_permutation _ (factor_unit unit (by decide))

private noncomputable def indexOfGate {n} (unit : (n+1).gcd 6 = 1) (z : Residue n) : Residue n :=
  Classical.choose ((thirds unit).2 z)

private theorem index_spec {n} (unit : (n+1).gcd 6 = 1) (z : Residue n) : affine 3 2 (indexOfGate unit z) = z :=
  Classical.choose_spec ((thirds unit).2 z)

private theorem shift_affine {n} (x : Residue n) : shift x = affine 1 1 x := by
  change shift x = reduce n (1*(x.val : Int)+1)
  rw [Int.one_mul]; rfl

noncomputable def lapMap {n} (pad : List Bool) (unit : (n+1).gcd 6 = 1) (x : Residue n) : Residue n :=
  affine 4 2 (indexOfGate unit (affine (2^pad.length) (evenPrefix pad 0) x))

theorem lap_permutations {n} (pad : List Bool) (unit : (n+1).gcd 6 = 1) :
    Permutes (lapMap pad unit) ∧ Permutes (fun x => shift (lapMap pad unit x)) := by
  have two := factor_unit (a := 2) unit (by decide)
  have four := affine_permutation (n := n) (a := 4) 2 (Nat.gcd_pow_right_of_gcd_eq_one (k := 2) two)
  have perm : Permutes (lapMap pad unit) := by
    apply perm_of_inj
    intro x y eq
    apply (affine_permutation (evenPrefix pad 0) (Nat.gcd_pow_right_of_gcd_eq_one (k := pad.length) two)).1 x y
    exact (index_spec unit _).symm.trans ((congrArg (affine 3 2) (four.1 _ _ eq)).trans (index_spec unit _))
  refine ⟨perm, perm_of_inj (fun x y eq => perm.1 _ _ ?_)⟩
  exact (affine_permutation (n := n) (a := 1) 1 (by simp)).1 _ _ (by simpa only [shift_affine] using eq)

theorem lap_projects {n} (pad : List Bool) (unit : (n+1).gcd 6 = 1) (value k : Int)
    (gate : evenPrefix pad value = 3*k+2) :
    lapMap pad unit (reduce n value) = reduce n (4*k+2) ∧
    shift (lapMap pad unit (reduce n value)) = reduce n (4*k+3) := by
  have proj : affine (2^pad.length) (evenPrefix pad 0) (reduce n value) = reduce n (evenPrefix pad value) := by
    rw [affine_lift]
    simpa [Int.natCast_pow, Int.add_comm] using congrArg (reduce n) (evenPrefix_affine pad 0 value).symm
  have idx : indexOfGate unit _ = reduce n k := (thirds unit).1 _ _ <|
    (index_spec unit _).trans (proj.trans (by rw [gate, affine_lift]; rfl))
  have first : lapMap pad unit (reduce n value) = reduce n (4*k+2) := by unfold lapMap; rw [idx, affine_lift]; rfl
  refine ⟨first, ?_⟩
  rw [first, shift_affine, affine_lift]
  exact congrArg (reduce n) (by change 1*(4*k+2)+1=4*k+3; omega)

theorem coprime_steering {n} (pad : List Bool) (unit : (n+1).gcd 6 = 1) (x y : Residue n) :
    ∃ choices : List Bool, choices.length = n ∧ steer (lapMap pad unit) choices x = y :=
  exact_choices _ (lap_permutations pad unit).1.1 x y

private theorem gate_family (pad : List Bool) (base : Int) (exp : Nat) : ∃ r k : Int, ∀ t : Int,
    evenPrefix pad (base + 2^exp*(r+3*t)) = 3*(k+2^(pad.length+exp)*t)+2 := by
  let mult := 2^(pad.length+exp)
  have form (v : Int) : evenPrefix pad (base+2^exp*v) = evenPrefix pad base + (mult : Int)*v := by
    simp only [evenPrefix_affine, mult, Nat.pow_add, Int.natCast_mul, Int.natCast_pow, Int.mul_assoc] <;> rfl
  obtain ⟨r, hr⟩ := (affine_permutation (n := 2) (a := mult) (evenPrefix pad base)
    (Nat.gcd_pow_right_of_gcd_eq_one (by decide : Nat.gcd 3 2 = 1))).2 (reduce 2 2)
  obtain ⟨k, hk⟩ := reduce_eq.mp hr
  change (mult:Int)*r.val+evenPrefix pad base-2=3*k at hk
  refine ⟨r.val,k, fun t => ?_⟩
  rw [form, show (2:Int)^(pad.length+exp) = (mult:Int) by simp [mult, Int.natCast_pow]]
  rw [Int.mul_add, Int.mul_left_comm (mult:Int) 3 t, Int.mul_add 3]; omega

def Admits (pad : List Bool) : List Bool → Int → Int → Prop
  | [], target, seed => seed = target
  | bit :: rest, target, seed => ∃ mid k : Int, Admits pad rest target mid ∧
      evenPrefix pad mid = 3*k+2 ∧ seed = 4*k+2+height bit

theorem target_le_seed {pad word : List Bool} {target seed : Int} (hn : 0 ≤ target)
    (h : Admits pad word target seed) : target ≤ seed := by
  have grow (p : List Bool) (v : Int) (hv : 0 ≤ v) : v ≤ evenPrefix p v := by
    induction p generalizing v with
    | nil => exact Int.le_refl _
    | cons high rest ih =>
      have hh : 0 ≤ height high := by cases high <;> decide
      exact Int.le_trans (by omega : v ≤ 2*v+height high) (ih _ (by omega))
  induction word generalizing seed with
  | nil => change seed = target at h; omega
  | cons bit rest ih =>
    obtain ⟨mid,k,prior,gate,rfl⟩ := h
    have lower := ih prior
    have step := grow pad mid (by omega)
    rw [gate] at step
    cases bit <;> simp only [height] <;> omega

theorem ternary_word_lift (pad word : List Bool) : ∃ target seed : Int, ∀ t : Int,
    Admits pad word (target+3^word.length*t) (seed+2^((pad.length+2)*word.length)*t) := by
  induction word with
  | nil => exact ⟨0,0,fun _ => by simp [Admits]⟩
  | cons bit rest ih =>
    obtain ⟨target, seed, family⟩ := ih
    let exp := (pad.length+2)*rest.length
    obtain ⟨r, k, gate⟩ := gate_family pad seed exp
    refine ⟨target+3^rest.length*r, 4*k+2+height bit, fun t => ?_⟩
    refine ⟨seed+2^exp*(r+3*t), k+2^(pad.length+exp)*t, ?_, gate t, ?_⟩
    · simpa only [List.length_cons, Int.pow_succ, Int.mul_add, Int.mul_assoc, Int.add_assoc] using family (r+3*t)
    · have e : (pad.length+2)*(rest.length+1) = ((pad.length+exp)+1)+1 := by dsimp [exp]; rw [Nat.mul_succ]; omega
      have scale : (2:Int)^((pad.length+2)*(rest.length+1)) = 4*2^(pad.length+exp) := by
        rw [e, Int.pow_succ, Int.pow_succ]; omega
      simp only [List.length_cons, scale, Int.mul_add, Int.mul_assoc]; omega

def replayLaps (pad : List Bool) : Nat → Int → Int
  | 0, seed => seed
  | count+1, seed => replayLaps pad count (replay (pad ++ [false,true]) seed)

theorem admits_sound {n} (pad word : List Bool) (unit : (n+1).gcd 6 = 1) {target seed : Int}
    (h : Admits pad word target seed) : replayLaps pad word.length seed = target ∧
    steer (lapMap pad unit) word (reduce n target) = reduce n seed := by
  induction word generalizing seed with
  | nil => exact ⟨h, congrArg (reduce n) (Eq.symm h)⟩
  | cons bit rest ih =>
    obtain ⟨mid,k,prior,gate,rfl⟩ := h
    obtain ⟨hit,modHit⟩ := ih prior
    obtain ⟨lo,hi⟩ := lap_replay pad mid k gate
    obtain ⟨flo,fhi⟩ := lap_projects pad unit mid k gate
    cases bit <;> simp only [height, Int.add_zero, show 4*k+2+1 = 4*k+3 by omega, List.length_cons,
      replayLaps, steer, Bool.false_eq_true, if_false, if_true, lo, hi, hit, modHit, fhi] <;> simp [flo]

theorem progression_steering {n} (pad : List Bool) (unit : (n+1).gcd 6 = 1) (x y : Residue n) :
    ∃ (word : List Bool) (c : Int), word.length = n ∧ reduce n c = x ∧
      ∀ z : Int, reduce n z = x → (3:Int)^n ∣ z-c →
        ∃ seed : Int, Admits pad word z seed ∧ reduce n seed = y ∧ replayLaps pad n seed = z := by
  obtain ⟨word, depth, steerHit⟩ := coprime_steering pad unit x y
  obtain ⟨base, _, family⟩ := ternary_word_lift pad word
  obtain ⟨c, hc, r, hr⟩ := crt_lift (m := 3^n)
    (Nat.gcd_pow_right_of_gcd_eq_one (factor_unit unit (by decide : 3 ∣ 6))) base x
  rw [Int.natCast_pow] at hr
  change c-base = (3:Int)^n*r at hr
  refine ⟨word, c, depth, hc, fun z hz ⟨t, ht⟩ => ?_⟩
  have eq : base+3^word.length*(r+t) = z := by rw [depth, Int.mul_add]; omega
  have path := family (r+t)
  rw [eq] at path
  obtain ⟨hit, residue⟩ := admits_sound pad word unit path
  rw [hz, steerHit] at residue
  exact ⟨_, path, residue.symm, by simpa only [depth] using hit⟩

end ProgressionSteering