import Collatz.SevenStep

namespace Collatz.SevenStep
open Physical

set_option maxRecDepth 10000
set_option maxHeartbeats 16000000

private theorem entryRows :
    ∀ (i : Phase) (r : Fin 192),
      checkHit (fun _ _ => true) 6 i ⟨192,(r.val : Int)+1⟩ = true := by decide +kernel

/-- From any positive physical seed at any phase, the first visit is at most six ticks away. -/
theorem section_entry (i : Phase) (n : Int) (positive : 0 < n) :
    FirstHit (fun _ => True) (i,n) 6 := by
  let k := (n-1).toNat
  let r : Fin 192 := ⟨k%192, Nat.mod_lt _ (by decide)⟩
  let x : Affine := ⟨192,(r.val : Int)+1⟩
  have hx : x.val (k/192) = n := by simp [x, r, k, Affine.val]; omega
  rw [← hx]
  exact checkHit_sound _ _ _ (by simp) _ i x (entryRows i r)

def residual (i : Phase) (m : Nat) : Bool :=
  (i == 1 && m%2 == 0) || (i == 3 && m%4 == 3) || (i == 5 && m%8 == 2)

/-- Signed three-times-section rank; division is unnecessary for strict comparisons. -/
def signedRank (s : State) : Int := weight s.1 * z s.1 s.2

def lower (i : Phase) (b : Nat) (j : Phase) (x : Affine) : Bool :=
  weight j * x.a ≤ weight i * (3*128) &&
    weight j * z j x.b < weight i * (3*(b:Int))

def launch (i : Phase) (b : Nat) : Affine := ⟨3*128,3*(b:Int)-1+height i⟩

def cap (i : Phase) : Nat := if i = 1 then 2 else if i = 3 then 6 else 7

def returnRow (i : Phase) (b : Nat) (accept : Phase → Affine → Bool) :=
  checkHit accept (cap i - 1) (i+1) ((launch i b).advance i)

/-- For m ≥ 6 every class outside the three named families has a lower first return. -/
private theorem largeRows : ∀ (i : Phase) (r : Fin 128),
    !active i || residual i (6+r.val) || returnRow i (6+r.val) (lower i (6+r.val)) := by
  decide +kernel

def smallHit (s : State) : Nat → Bool
  | 0 => s.2 == root s.1
  | k+1 => s.2 == root s.1 || smallHit (tick s) k

theorem smallHit_sound (s : State) (k : Nat) (hit : smallHit s k) : Captured s := by
  induction k generalizing s with
  | zero => exact ⟨0,beq_iff_eq.mp hit⟩
  | succ k ih =>
    simp only [smallHit, Bool.or_eq_true, beq_iff_eq] at hit
    rcases hit with h | h
    · exact ⟨0,h⟩
    · exact reaches_prepend 1 (ih _ h : Captured (tick s))

private theorem smallRows : ∀ (i : Phase) (m : Fin 6),
    !active i || m.val == 0 || smallHit (site i m.val) 150 := by decide +kernel

theorem launch_val (i : Phase) (b q : Nat) :
    (i,(launch i b).val q) = site i (128*q+b) := by
  refine Prod.ext ?_ ?_
  · rfl
  · simp [launch, Affine.val, site]; omega

theorem lower_sound (i : Phase) (b q : Nat) (j : Phase) (x : Affine)
    (h : lower i b j x) :
    signedRank (j,x.val q) < signedRank (site i (128*q+b)) := by
  simp only [lower, Bool.and_eq_true, decide_eq_true_eq] at h
  have lin := Int.mul_le_mul_of_nonneg_right h.1 (Int.natCast_nonneg q)
  have src : z i (site i (128*q+b)).2 = 3*(128*(q:Int)+(b:Int)) := by
    simp [z, site]; omega
  change weight j * z j (x.val q) < weight i * z i (site i (128*q+b)).2
  rw [affine_z, src]
  simp only [Int.mul_add, ← Int.mul_assoc] at *
  omega

theorem residual_mod (i : Phase) (b q : Nat) :
    residual i (128*q+b) = residual i b := by
  unfold residual
  have h2 : (128*q+b)%2 = b%2 := by omega
  have h4 : (128*q+b)%4 = b%4 := by omega
  have h8 : (128*q+b)%8 = b%8 := by omega
  rw [h2,h4,h8]

theorem large_descent (i : Phase) (m : Nat) (ha : active i) (hm : 6 ≤ m)
    (exc : residual i m = false) :
    FirstHit (fun s => signedRank s < signedRank (site i m)) (tick (site i m)) (cap i - 1) := by
  let q := (m-6)/128
  let r : Fin 128 := ⟨(m-6)%128, Nat.mod_lt _ (by decide)⟩
  let b := 6+r.val
  have repr : m = 128*q+b := by dsimp [q,b,r]; omega
  have rexc : residual i b = false := by rwa [repr,residual_mod] at exc
  have row := largeRows i r
  change (!active i || residual i b || returnRow i b (lower i b)) = true at row
  simp [ha,rexc] at row
  have first := checkHit_sound _ q (fun s => signedRank s < signedRank (site i (128*q+b))) (lower_sound i b q) _ _ _ row
  have t := advance_sound i (launch i b) q (by change (384:Int)%2 = 0; decide)
  rw [launch_val] at t
  rw [repr,t]
  exact first

abbrev Section := {s : State // Marked s}

private def index (s : State) := (z s.1 s.2 / 3).toNat

private theorem site_index (i : Phase) (m : Nat) : index (site i m) = m := by
  simp [index,z,site]; omega

private theorem pos_rank (s : Section) : 0 < signedRank s.val := by
  have hz := s.property.2.2
  have hw : 0 < weight s.val.1 := by unfold weight; split <;> (try split) <;> decide
  exact Int.mul_pos hw hz

/-- Capture of B1, A3 and N03 suffices for all marked states. -/
theorem section_capture
    (B1 : ∀ t : Nat, 0 < t → Captured (site 1 (2*t)))
    (A3 : ∀ t : Nat, Captured (site 3 (4*t+3)))
    (N03 : ∀ t : Nat, Captured (site 5 (8*t+2)))
    (s : Section) : Captured s.val := by
  apply reduce_by_rank (fun x : Section => Captured x.val)
    (fun x => (signedRank x.val).toNat) (fun x => residual x.val.1 (index x.val) = true) _ _ s
  · intro x hx
    obtain ⟨m,hm,hs⟩ := marked_site x.property
    let i := x.val.1
    change x.val = site i m at hs
    have active_i := x.property.1
    change active i = true at active_i
    change ¬residual i (index x.val) = true at hx
    rw [hs,site_index] at hx
    have exf : residual i m = false := Bool.eq_false_iff.mpr hx
    by_cases small : m < 6
    · left
      have row := smallRows i ⟨m,small⟩
      have nz : m ≠ 0 := by omega
      simp [active_i,nz] at row
      change Captured x.val
      rw [hs]
      exact smallHit_sound _ _ row
    · obtain ⟨k,_,marked,lowered,_⟩ := large_descent i m active_i (by omega) exf
      let y : Section := ⟨orbit k (tick (site i m)),marked⟩
      refine Or.inr ⟨y,?_,?_⟩
      · change (signedRank y.val).toNat < (signedRank x.val).toNat
        change signedRank y.val < signedRank (site i m) at lowered
        rw [← hs] at lowered
        have := pos_rank y
        omega
      · intro done
        rw [hs]
        exact reaches_prepend (k+1) done
  · intro x exc
    obtain ⟨m,hm,hs⟩ := marked_site x.property
    let i := x.val.1
    change x.val = site i m at hs
    change residual i (index x.val) = true at exc
    rw [hs,site_index] at exc
    simp only [residual,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq] at exc
    rw [hs]
    rcases exc with ((⟨h,h₂⟩ | ⟨h,h₄⟩) | ⟨h,h₈⟩)
    · rw [h, show m = 2*(m/2) by omega]; exact B1 _ (by omega)
    · rw [h, show m = 4*(m/4)+3 by omega]; exact A3 _
    · rw [h, show m = 8*(m/8)+2 by omega]; exact N03 _

/-- The physical seven-step theorem, conditional only on three explicit capture assertions. -/
theorem global_capture_of_three
    (B1 : ∀ t : Nat, 0 < t → Captured (site 1 (2*t)))
    (A3 : ∀ t : Nat, Captured (site 3 (4*t+3)))
    (N03 : ∀ t : Nat, Captured (site 5 (8*t+2)))
    (i : Phase) (n : Int) (positive : 0 < n) : Captured (i,n) := by
  obtain ⟨k,_,marked,_,_⟩ := section_entry i n positive
  exact reaches_prepend k (section_capture B1 A3 N03 ⟨_,marked⟩)

end Collatz.SevenStep
