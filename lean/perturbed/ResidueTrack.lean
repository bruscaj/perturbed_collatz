import Lean

/-! Offsets are in backward order: `chain` takes the head first, while `replay`
applies the head last. A `Track` records both boundary residues of a word.
All physical values and offsets are integers. -/

namespace ResidueTrack

def forward (d n : Int) : Int :=
  (if n % 2 = 0 then n / 2 else (3 * n + 1) / 2) + d

def even (d z : Int) : Int := 2 * (z - d)

def odd (d z : Int) : Int := (even d z - 1) / 3

def Gate (d z : Int) : Prop := even d z % 3 = 1

theorem even_forward (d z : Int) : forward d (even d z) = z := by
  have parity : even d z % 2 = 0 := by unfold even; omega
  simp only [forward, if_pos parity, even]
  omega

theorem odd_forward_iff (d n z : Int) (parity : n % 2 = 1) :
    forward d n = z ↔ even d z = 3 * n + 1 := by
  rw [forward, if_neg (by omega : n % 2 ≠ 0)]
  unfold even
  omega

theorem odd_spec (d z : Int) (gate : Gate d z) :
    odd d z % 2 = 1 ∧ forward d (odd d z) = z := by
  have eq : even d z = 3 * odd d z + 1 := by unfold Gate at gate; unfold odd; omega
  have parity : odd d z % 2 = 1 := by unfold even at eq; omega
  exact ⟨parity, (odd_forward_iff d _ z parity).2 eq⟩

theorem odd_preimage_iff_gate (d z : Int) :
    (∃ n : Int, n % 2 = 1 ∧ forward d n = z) ↔ Gate d z := by
  constructor
  · rintro ⟨n, parity, hit⟩
    unfold Gate
    rw [(odd_forward_iff d n z parity).1 hit]
    omega
  · exact fun gate => ⟨odd d z, odd_spec d z gate⟩

def Clear (r : Int) : Prop := r = 0 ∨ r = 2

theorem plus_one_pin {r s : Int} (left : Clear r) (right : Clear s)
    (edge : (r + s) % 3 = 1) : r = 2 ∧ s = 2 := by
  rcases left with hl | hl <;> rcases right with hr | hr <;> omega

inductive Track : List Int → Int → Int → Prop where
  | nil {r} (clear : Clear r) : Track [] r r
  | cons {d rest r s t} (clear : Clear r) (edge : (r + s) % 3 = d % 3)
      (tail : Track rest s t) : Track (d :: rest) r t

def Circular (word : List Int) : Prop := ∃ r, Track word r r

def chain : List Int → Int → Int
  | [], z => z
  | d :: rest, z => chain rest (even d z)

def HitsGate : List Int → Int → Prop
  | [], _ => False
  | d :: rest, z => Gate d z ∨ HitsGate rest (even d z)

def replay : List Int → Int → Int
  | [], n => n
  | d :: rest, n => forward d (replay rest n)

theorem Track.start_clear (tr : Track w r s) : Clear r := by cases tr <;> assumption

theorem Track.end_clear (tr : Track w r s) : Clear s := by induction tr <;> assumption

private theorem clear_iff_miss (d z : Int) : Clear (even d z % 3) ↔ ¬ Gate d z := by
  unfold Clear Gate
  omega

private theorem edge_iff (d z s : Int) (clear : Clear s) :
    (z % 3 + s) % 3 = d % 3 ↔ even d z % 3 = s := by
  unfold even
  rcases clear with hs | hs <;> omega

theorem Track.follow (tr : Track w r s) (z : Int) (start : z % 3 = r) :
    ¬ HitsGate w z ∧ chain w z % 3 = s := by
  induction tr generalizing z with
  | nil => exact ⟨id, start⟩
  | @cons d rest r mid t _ edge tail ih =>
    have step := (edge_iff d z mid tail.start_clear).1 (start ▸ edge)
    have miss := (clear_iff_miss d z).1 (step ▸ tail.start_clear)
    obtain ⟨noTail, finish⟩ := ih (even d z) step
    exact ⟨fun hit => hit.elim miss noTail, finish⟩

theorem track_of_scan (w : List Int) (z : Int) (start : Clear (z % 3)) (miss : ¬ HitsGate w z) :
    Track w (z % 3) (chain w z % 3) := by
  induction w generalizing z with
  | nil => exact .nil start
  | cons d rest ih =>
    have clear := (clear_iff_miss d z).2 (fun gate => miss (.inl gate))
    exact .cons start ((edge_iff d z _ clear).2 rfl)
      (ih _ clear (fun hit => miss (.inr hit)))

theorem replay_chain (w : List Int) (z : Int) : replay w (chain w z) = z := by
  induction w generalizing z with
  | nil => rfl
  | cons d rest ih => exact (congrArg (forward d) (ih (even d z))).trans (even_forward d z)

theorem unique_of_miss (w : List Int) (z n : Int) (miss : ¬ HitsGate w z) :
    replay w n = z ↔ n = chain w z := by
  constructor
  · intro hit
    induction w generalizing z with
    | nil => exact hit
    | cons d rest ih =>
      have notOdd : replay rest n % 2 ≠ 1 := fun parity =>
        miss (.inl ((odd_preimage_iff_gate d z).1 ⟨_, parity, hit⟩))
      have parity : replay rest n % 2 = 0 := by omega
      change forward d (replay rest n) = z at hit
      rw [forward, if_pos parity] at hit
      apply ih (even d z) (fun found => miss (.inr found))
      unfold even
      omega
  · rintro rfl; exact replay_chain w z

theorem gate_iff_other_preimage (w : List Int) (z : Int) :
    HitsGate w z ↔ ∃ n : Int, replay w n = z ∧ n ≠ chain w z := by
  constructor
  · intro hit
    induction w generalizing z with
    | nil => exact False.elim hit
    | cons d rest ih =>
      rcases hit with gate | later
      · obtain ⟨parity, hop⟩ := odd_spec d z gate
        refine ⟨chain rest (odd d z), (congrArg (forward d) (replay_chain rest _)).trans hop, ?_⟩
        intro same
        have eq : odd d z = even d z := by
          simpa only [chain, replay_chain] using congrArg (replay rest) same
        have evenParity : even d z % 2 = 0 := by unfold even; omega
        omega
      · obtain ⟨n, hop, ne⟩ := ih _ later
        exact ⟨n, (congrArg (forward d) hop).trans (even_forward d z), ne⟩
  · rintro ⟨n, hit, ne⟩
    exact Classical.byContradiction fun miss => ne ((unique_of_miss w z n miss).1 hit)

theorem pinned_finish {w : List Int} {r s a b : Int} (one : 1 ∈ w)
    (first : Track w r a) (second : Track w s b) : a = b := by
  induction w generalizing r s a b with
  | nil => simp at one
  | cons d rest ih =>
    cases first with | cons left edge tail =>
      cases second with | cons right edge' tail' =>
        rcases List.mem_cons.mp one with same | later
        · subst d
          have pin := (plus_one_pin left tail.start_clear edge).2
          have pin' := (plus_one_pin right tail'.start_clear edge').2
          exact (tail.follow 2 (by omega)).2.symm.trans (tail'.follow 2 (by omega)).2
        · exact ih (r := _) (s := _) (a := _) (b := _) later tail tail'

theorem circular_cons_one (rest : List Int) : Circular (1 :: rest) ↔ Track (1 :: rest) 2 2 := by
  constructor
  · rintro ⟨r, tr⟩
    have pin : r = 2 := by
      cases tr with | cons clear edge tail => exact (plus_one_pin clear tail.start_clear edge).1
    simpa only [pin] using tr
  · exact fun tr => ⟨2, tr⟩

def laps (w : List Int) : Nat → List Int
  | 0 => []
  | k + 1 => w ++ laps w k

theorem laps_length (w : List Int) (k : Nat) : (laps w k).length = k * w.length := by
  induction k with
  | zero => simp [laps]
  | succ k ih => simp [laps, ih, Nat.succ_mul, Nat.add_comm]

def AvoidsForever (w : List Int) (z : Int) : Prop := ∀ k, ¬ HitsGate (laps w k) z

theorem Track.append (first : Track u r s) (last : Track v s t) : Track (u ++ v) r t := by
  induction first with
  | nil => exact last
  | cons clear edge _ ih => exact .cons clear edge (ih last)

theorem Track.reverse (tr : Track w r s) : Track w.reverse s r := by
  induction tr with
  | nil clear => exact .nil clear
  | cons clear edge tail ih =>
    rw [List.reverse_cons]
    exact ih.append (.cons tail.start_clear (by simpa only [Int.add_comm] using edge) (.nil clear))

theorem circular_reverse (w : List Int) : Circular w.reverse ↔ Circular w := by
  constructor
  · rintro ⟨r, tr⟩; exact ⟨r, by simpa only [List.reverse_reverse] using tr.reverse⟩
  · rintro ⟨r, tr⟩; exact ⟨r, tr.reverse⟩

theorem Track.repeat_laps (tr : Track w r r) (k : Nat) : Track (laps w k) r r := by
  induction k with
  | zero => exact .nil tr.start_clear
  | succ k ih => exact tr.append ih

theorem Track.forever (tr : Track w r r) {z : Int} (start : z % 3 = r) : AvoidsForever w z :=
  fun k => ((tr.repeat_laps k).follow z start).1

theorem Track.unique_preimage (tr : Track w r r) {z : Int} (start : z % 3 = r) (k : Nat) (n : Int) :
    replay (laps w k) n = z ↔ n = chain (laps w k) z :=
  unique_of_miss _ z n (tr.forever start k)

theorem hits_append (u v : List Int) (z : Int) :
    HitsGate (u ++ v) z ↔ HitsGate u z ∨ HitsGate v (chain u z) := by
  induction u generalizing z with
  | nil => simp [HitsGate, chain]
  | cons d rest ih => simp only [List.cons_append, HitsGate, chain, ih, or_assoc]

theorem Track.unique_prefix (tr : Track w r r) {z : Int} (start : z % 3 = r) (k : Nat)
    {front back : List Int} (cut : laps w k = front ++ back) (n : Int) :
    replay front n = z ↔ n = chain front z := by
  apply unique_of_miss
  intro found
  apply tr.forever start k
  rw [cut]
  exact (hits_append front back z).2 (.inl found)

private theorem miss_succ {w z k} (miss : ¬ HitsGate (laps w (k + 1)) z) :
    ¬ HitsGate w z ∧ ¬ HitsGate (laps w k) (chain w z) :=
  ⟨fun hit => miss ((hits_append w _ z).2 (.inl hit)),
   fun hit => miss ((hits_append w _ z).2 (.inr hit))⟩

private theorem clear_finish {w : List Int} {z : Int} (one : 1 ∈ w) (miss : ¬ HitsGate w z) :
    Clear (chain w z % 3) := by
  cases w with
  | nil => simp at one
  | cons d rest =>
    have clear := (clear_iff_miss d z).2 (fun gate => miss (.inl gate))
    exact (track_of_scan rest _ clear (fun hit => miss (.inr hit))).end_clear

theorem chain_mod_iff (w : List Int) (x y : Int) :
    chain w x % 3 = chain w y % 3 ↔ x % 3 = y % 3 := by
  induction w generalizing x y with
  | nil => rfl
  | cons d rest ih => simp only [chain, ih, even]; omega

theorem miss_three_iff_track (w : List Int) (one : 1 ∈ w) (z : Int) :
    ¬ HitsGate (laps w 3) z ↔ Track w (z % 3) (z % 3) := by
  refine ⟨fun miss => ?_, fun tr => tr.forever rfl 3⟩
  obtain ⟨first, afterFirst⟩ := miss_succ (k := 2) miss
  obtain ⟨second, afterSecond⟩ := miss_succ (k := 1) afterFirst
  have third := (miss_succ (k := 0) afterSecond).1
  have middle := track_of_scan w _ (clear_finish one first) second
  have last := track_of_scan w _ middle.end_clear third
  have same := (chain_mod_iff w _ _).1 (pinned_finish one middle last)
  have start := (chain_mod_iff w _ _).1 same
  simpa only [← same, ← start] using middle

theorem avoid_iff_track (w : List Int) (one : 1 ∈ w) (z : Int) :
    AvoidsForever w z ↔ Track w (z % 3) (z % 3) :=
  ⟨fun avoid => (miss_three_iff_track w one z).1 (avoid 3), fun tr => tr.forever rfl⟩

theorem circular_iff_forever (w : List Int) (one : 1 ∈ w) :
    Circular w ↔ ∃ z : Int, AvoidsForever w z := by
  constructor
  · rintro ⟨r, tr⟩
    have start : r % 3 = r := by rcases tr.start_clear with h | h <;> omega
    exact ⟨r, tr.forever start⟩
  · rintro ⟨z, avoid⟩; exact ⟨_, (avoid_iff_track w one z).1 avoid⟩

theorem no_track_iff_three (w : List Int) (one : 1 ∈ w) :
    ¬ Circular w ↔ ∀ z : Int, HitsGate (laps w 3) z := by
  constructor
  · intro noTrack z
    exact Classical.byContradiction (fun miss => noTrack ⟨_, (miss_three_iff_track w one z).1 miss⟩)
  · intro all circular
    obtain ⟨z, avoid⟩ := (circular_iff_forever w one).1 circular
    exact avoid 3 (all z)

theorem balanced_has_one {w : List Int} (bound : ∀ d ∈ w, d ≤ 1) (balance : w.sum = 0)
    (nonzero : ∃ d ∈ w, d ≠ 0) : 1 ∈ w := by
  by_cases one : (1 : Int) ∈ w
  · exact one
  · have aux (v : List Int) (nonpos : ∀ d ∈ v, d ≤ 0) :
        v.sum ≤ 0 ∧ ∀ d ∈ v, v.sum ≤ d := by
      induction v with
      | nil => simp
      | cons d rest ih =>
        have head := nonpos d List.mem_cons_self
        obtain ⟨le, elem⟩ := ih (fun a ha => nonpos a (List.mem_cons_of_mem _ ha))
        simp only [List.sum_cons]
        refine ⟨by omega, fun a ha => ?_⟩
        rcases List.mem_cons.mp ha with rfl | inRest
        · omega
        · have := elem a inRest; omega
    have nonpos (a : Int) (ha : a ∈ w) : a ≤ 0 := by
      have upper := bound a ha
      have ne : a ≠ 1 := by rintro rfl; exact one ha
      omega
    obtain ⟨d, hd, ne⟩ := nonzero
    have lower := (aux w nonpos).2 d hd
    have upper := nonpos d hd
    omega

theorem balanced_obstruction {w : List Int} (bound : ∀ d ∈ w, d ≤ 1) (balance : w.sum = 0)
    (nonzero : ∃ d ∈ w, d ≠ 0) : (Circular w ↔ ∃ z, AvoidsForever w z) ∧
      (¬ Circular w ↔ ∀ z, HitsGate (laps w 3) z) :=
  let one := balanced_has_one bound balance nonzero
  ⟨circular_iff_forever w one, no_track_iff_three w one⟩

theorem three_laps_sharp : ¬ Circular [1, -1] ∧ ¬ HitsGate (laps [1, -1] 2) 4 := by
  constructor
  · intro circular
    have finish := (((circular_cons_one [-1]).1 circular).follow 2 rfl).2
    exact (by decide : (0 : Int) ≠ 2) finish
  · simp only [laps, List.cons_append, List.nil_append, HitsGate, Gate, even] <;> decide

theorem balanced_track_example : Track [1, -1, -1, 1] 2 2 :=
  track_of_scan [1, -1, -1, 1] 2 (Or.inr rfl) (by simp only [HitsGate, Gate, even] <;> decide)

theorem adjacent_one_odd (v z n : Int) :
    (forward v (forward (-1) n) = z ∧ n % 2 ≠ forward (-1) n % 2) ↔
      (z - v) % 3 = 2 ∧ (n = (4 * (z - v) + 1) / 3 ∨ n = (4 * (z - v) + 1) / 3 + 1) := by
  by_cases parity : n % 2 = 0 <;> simp only [forward, parity, if_true, if_false] <;> split <;> omega

theorem adjacent_one_odd_at (v z k n : Int) (offset : z - v = 3 * k + 2) :
    (forward v (forward (-1) n) = z ∧ n % 2 ≠ forward (-1) n % 2) ↔
      n = 4 * k + 3 ∨ n = 4 * k + 4 := by
  rw [adjacent_one_odd]
  omega

def displacement (coeff bias x : Int) : Int := coeff * x + bias

theorem displacement_forward (coeff bias nextBias d x : Int)
    (commute : bias - 2 * coeff * d = 2 * nextBias) :
    2 * displacement coeff nextBias (forward d x) =
      (if x % 2 = 1 then 3 else 1) * displacement coeff bias x +
      (if x % 2 = 1 then coeff - 2 * bias else 0) := by
  have raw : 2 * forward d x = (if x % 2 = 1 then 3 * x + 1 else x) + 2 * d := by
    unfold forward
    split <;> split <;> omega
  have scaled := congrArg (fun value => coeff * value) raw
  have twice (v : Int) : coeff * (2 * v) = 2 * (coeff * v) := by ac_rfl
  have thrice : coeff * (3 * x) = 3 * (coeff * x) := by ac_rfl
  rw [Int.mul_assoc] at commute
  by_cases parity : x % 2 = 1 <;>
    simp only [parity, if_true, if_false, displacement, Int.mul_add, twice, thrice,
      Int.mul_one, Int.one_mul] at scaled ⊢ <;> omega

theorem odd_step_threshold (h : Nat) (coeff bias nextBias d x : Int)
    (commute : bias - 2 * coeff * d = 2 * nextBias) (parity : x % 2 = 1)
    (correction : ¬ (3 : Int) ^ (h + 1) ∣ coeff - 2 * bias) :
    (¬ (3 : Int) ^ h ∣ displacement coeff bias x) ∨
      (¬ (3 : Int) ^ (h + 1) ∣ displacement coeff nextBias (forward d x)) := by
  by_cases before : (3 : Int) ^ h ∣ displacement coeff bias x
  · refine Or.inr fun after => correction ?_
    have raised : (3 : Int) ^ (h + 1) ∣ 3 * displacement coeff bias x := by
      obtain ⟨quotient, eq⟩ := before
      exact ⟨quotient, by rw [eq, Int.pow_succ]; ac_rfl⟩
    have step := displacement_forward coeff bias nextBias d x commute
    simp only [parity, if_true] at step
    have cancel (base delta : Int) : base + delta - base = delta := by omega
    simpa only [step, cancel] using Int.dvd_sub (Int.dvd_trans after (Int.dvd_mul_left 2 _)) raised
  · exact Or.inl before

theorem chain_difference (word : List Int) (x y : Int) :
    chain word x - chain word y = (2 : Int) ^ word.length * (x - y) := by
  induction word generalizing x y with
  | nil => simp [chain]
  | cons d rest ih =>
    have diff : even d x - even d y = 2 * (x - y) := by unfold even; omega
    simp only [chain, ih, diff, List.length_cons, Int.pow_succ, Int.mul_assoc]

theorem chain_bias_commutation (rest : List Int) (d : Int) :
    chain (rest ++ [d]) 0 - 2 * ((2 : Int) ^ (rest.length + 1) - 1) * d =
      2 * chain (d :: rest) 0 := by
  have last (word : List Int) (z : Int) : chain (word ++ [d]) z = even d (chain word z) := by
    induction word generalizing z with
    | nil => rfl
    | cons head _ ih => exact ih (even head z)
  have zero : 0 - even d 0 = 2 * d := by unfold even; omega
  have shift := chain_difference rest 0 (even d 0)
  rw [zero, ← Int.mul_assoc, ← Int.pow_succ] at shift
  rw [last]
  change 2 * (chain rest 0 - d) - _ = 2 * chain rest (even d 0)
  rw [Int.mul_assoc, Int.sub_mul, Int.one_mul]
  omega

end ResidueTrack