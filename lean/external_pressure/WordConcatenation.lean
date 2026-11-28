import WordPartitionTransport

/-! Literal finite concatenation and its exponential partition supermultiplicativity. -/
namespace ExternalBridgePressureWordConcatenation
open ExternalFiniteBridgeDraft ExternalBridgePressureDraft ExternalBridgePressureWordDraft
open ExternalFiniteBridgeEncoding ExternalBridgePressurePhase ExternalBridgePressureWordPhysical
open ExternalBridgePressureWordReward ExternalBridgePressureWordPopulation
open ExternalBridgePressureWordFiniteComparison ExternalBridgePressureWordPartitionTransport
open scoped BigOperators

 def stitchedProfile (m n : ℕ) (u : Word m) (v : Word n) : Prefix (m+n) := fun t =>
  if h : t.val≤m then wordPrefix m u ⟨t.val,by omega⟩
  else wordPrefix m u (Fin.last m)+wordPrefix n v ⟨t.val-m,by omega⟩

theorem stitched_before (m n : ℕ) (u : Word m) (v : Word n) (t : Fin (m+1)) :
    stitchedProfile m n u v ⟨t.val,by have := t.isLt; omega⟩ = wordPrefix m u t := by
  unfold stitchedProfile
  split_ifs with h
  · rfl
  · change ¬ t.val≤m at h
    have := t.isLt
    omega

theorem stitched_after (m n : ℕ) (u : Word m) (v : Word n) (t : Fin (n+1)) :
    stitchedProfile m n u v ⟨m+t.val,by have := t.isLt; omega⟩ =
      wordPrefix m u (Fin.last m)+wordPrefix n v t := by
  unfold stitchedProfile
  split_ifs with h
  · change m+t.val≤m at h
    have ht : t=0 := Fin.ext (by change t.val=0; omega)
    have he : (⟨m+t.val,by omega⟩ : Fin (m+1)) = Fin.last m := Fin.ext (by change m+t.val=m; omega)
    rw [he,ht,wordPrefix_zero,add_zero]
  · have he : (⟨m+t.val-m,by omega⟩ : Fin (n+1)) = t := Fin.ext (by change m+t.val-m=t.val; omega)
    rw [he]

theorem stitched_step (m n : ℕ) (u : Word m) (v : Word n) (i : Fin (m+n)) :
    stitchedProfile m n u v i.succ = stitchedProfile m n u v i.castSucc + (concatenate m n u v i : ℤ) := by
  by_cases hi : i.val<m
  · have hl : i.val≤m := by omega
    have hr : i.val+1≤m := by omega
    simp only [stitchedProfile,Fin.val_succ,Fin.val_castSucc,hl,hr,dite_true,
      concatenate,hi,dite_true]
    exact wordPrefix_step m u ⟨i.val,hi⟩
  · let j : Fin n := ⟨i.val-m,by have := i.isLt; omega⟩
    have hval : m+j.val=i.val := by dsimp [j]; omega
    have hl := stitched_after m n u v j.castSucc
    have hr := stitched_after m n u v j.succ
    have el : (⟨m+j.castSucc.val,by omega⟩ : Fin (m+n+1)) = i.castSucc := Fin.ext hval
    have er : (⟨m+j.succ.val,by omega⟩ : Fin (m+n+1)) = i.succ := Fin.ext (by change m+(j.val+1)=i.val+1; omega)
    rw [el] at hl
    rw [er] at hr
    rw [hl,hr]
    have hc : concatenate m n u v i = v j := by simp only [concatenate,hi,dite_false]; rfl
    rw [hc,wordPrefix_step]
    ring

theorem concatenate_prefix (m n : ℕ) (u : Word m) (v : Word n) :
    wordPrefix (m+n) (concatenate m n u v) = stitchedProfile m n u v := by
  funext t
  induction t using Fin.induction with
  | zero => simp [wordPrefix_zero,stitchedProfile]
  | succ i ih => rw [wordPrefix_step,ih,stitched_step]

theorem aux_cap_add (x : ℝ) (hx : ActualPhase x) (m n : ℕ) :
    auxCap x (m+n) = auxCap x m+auxCap (phaseShift x m) n := by
  have hy : ActualPhase (phaseShift x m) := phase_shift_bounds x m
  simpa only [actual_phase_floor x hx,actual_phase_floor _ hy] using phase_floor_add x m n

theorem concatenate_legal (x : ℝ) (m n : ℕ) (hx : ActualPhase x)
    (u : Word m) (hu : AuxWord x m u) (v : Word n) (hv : AuxWord (phaseShift x m) n v) :
    AuxWord x (m+n) (concatenate m n u v) := by
  refine ⟨by have := hu.1; omega,?_,?_,?_⟩
  · intro i
    unfold concatenate
    split_ifs with hi
    · exact hu.2.1 _
    · exact hv.2.1 _
  · rw [concatenate_prefix]
    have h := stitched_after m n u v (Fin.last n)
    change stitchedProfile m n u v (Fin.last (m+n)) = _ at h
    rw [h,hu.2.2.1,hv.2.2.1,← aux_cap_add x hx]
  · intro t
    rw [concatenate_prefix]
    unfold stitchedProfile
    split_ifs with h
    · have hb := aux_depth_nonneg x m u hu ⟨t.val,by simp only [Fin.val_castSucc] at h; omega⟩
      exact sub_nonneg.mp hb
    · change ¬ t.val≤m at h
      have hb := aux_depth_nonneg (phaseShift x m) n v hv ⟨t.val-m,by have := t.isLt; omega⟩
      rw [hu.2.2.1]
      have he : auxCap x t.val = auxCap x m+auxCap (phaseShift x m) (t.val-m) := by
        rw [← aux_cap_add x hx]
        congr 1
        omega
      change auxCap x m+wordPrefix n v ⟨t.val-m,by omega⟩ ≤ auxCap x t.val
      rw [he]
      change 0 ≤ auxCap (phaseShift x m) (t.val-m)-wordPrefix n v ⟨t.val-m,by omega⟩ at hb
      omega

theorem concatenate_first_term (x : ℝ) (m n : ℕ) (u : Word m) (v : Word n) (t : Fin m) :
    auxTerm x (m+n) (concatenate m n u v) (Fin.castAdd n t) = auxTerm x m u t := by
  unfold auxTerm
  rw [concatenate_prefix]
  have he := stitched_before m n u v t.castSucc
  change stitchedProfile m n u v (Fin.castAdd n t).castSucc = wordPrefix m u t.castSucc at he
  rw [he]
  rfl

theorem concatenate_second_term (x : ℝ) (m n : ℕ) (u : Word m) (hu : AuxWord x m u)
    (v : Word n) (t : Fin n) :
    auxTerm x (m+n) (concatenate m n u v) (Fin.natAdd m t) = auxTerm (phaseShift x m) n v t := by
  rw [aux_term_real_power,aux_term_real_power,concatenate_prefix]
  have he := stitched_after m n u v t.castSucc
  change stitchedProfile m n u v (Fin.natAdd m t).castSucc = wordPrefix m u (Fin.last m)+wordPrefix n v t.castSucc at he
  rw [he,hu.2.2.1]
  congr 1
  simp only [phaseShift,phaseTick,Int.fract,auxCap,Fin.val_natAdd]
  push_cast
  ring

theorem concatenate_reward (x : ℝ) (m n : ℕ) (u : Word m) (hu : AuxWord x m u) (v : Word n) :
    auxReward x (m+n) (concatenate m n u v) = auxReward x m u+auxReward (phaseShift x m) n v := by
  unfold auxReward
  rw [Fin.sum_univ_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro t _
    exact concatenate_first_term x m n u v t
  · apply Finset.sum_congr rfl
    intro t _
    exact concatenate_second_term x m n u hu v t

theorem concatenate_injective (x : ℝ) (m n : ℕ) :
    Function.Injective (fun p : AuxWords x m × AuxWords (phaseShift x m) n => concatenate m n p.1.val p.2.val) := by
  intro a b hab
  apply Prod.ext
  · apply Subtype.ext
    funext i
    have h := congrFun hab (Fin.castAdd n i)
    simpa only [concatenate,Fin.val_castAdd,i.isLt,dite_true] using h
  · apply Subtype.ext
    funext i
    have h := congrFun hab (Fin.natAdd m i)
    have hi : ¬m+i.val<m := by omega
    simpa only [concatenate,Fin.val_natAdd,hi,dite_false,Nat.add_sub_cancel_left] using h

theorem concatenation_transport : ConcatenationTransport := by
  intro x m n hx _ _
  exact ⟨concatenate_injective x m n,fun u hu v hv =>
    ⟨concatenate_legal x m n hx u hu v hv,concatenate_reward x m n u hu v⟩⟩

noncomputable def concatenationMap (x : ℝ) (m n : ℕ) (hx : ActualPhase x) :
    AuxWords x m × AuxWords (phaseShift x m) n → AuxWords x (m+n) := fun p =>
  ⟨concatenate m n p.1.val p.2.val,concatenate_legal x m n hx p.1.val p.1.property p.2.val p.2.property⟩

theorem partition_cocycle : PartitionCocycle := by
  intro x m n lam hx _
  have hy : ActualPhase (phaseShift x m) := phase_shift_bounds x m
  have hxc : ClosedPhase x := ⟨hx.1,le_of_lt hx.2⟩
  have hyc : ClosedPhase (phaseShift x m) := ⟨hy.1,le_of_lt hy.2⟩
  by_cases hm : m=0
  · subst m
    have hf : Int.floor x=0 := by simpa [auxCap] using actual_cap_zero x hx
    have he : phaseShift x 0=x := by
      simp only [phaseShift,phaseTick,Nat.cast_zero,zero_mul,add_zero,Int.fract,hf,Int.cast_zero,sub_zero]
    rw [he,(ExternalBridgePressureWordArithmetic.zero_volume_convention x lam).2.2.2.1]
    simp only [zero_add,le_refl]
  · by_cases hn : n=0
    · subst n
      simp [auxLogPartition,auxPartition]
    · have := aux_words_finite x m hxc
      have := aux_words_finite (phaseShift x m) n hyc
      have := aux_words_finite x (m+n) hxc
      let := Fintype.ofFinite (AuxWords x m)
      let := Fintype.ofFinite (AuxWords (phaseShift x m) n)
      let := Fintype.ofFinite (AuxWords x (m+n))
      have hz : auxPartition x m lam*auxPartition (phaseShift x m) n lam ≤ auxPartition x (m+n) lam := by
        rw [aux_partition_eq_sum x m lam (by omega),aux_partition_eq_sum (phaseShift x m) n lam (by omega),
          aux_partition_eq_sum x (m+n) lam (by omega),Finset.sum_mul]
        simp_rw [Finset.mul_sum]
        rw [← Fintype.sum_prod_type (fun p : AuxWords x m × AuxWords (phaseShift x m) n =>
          Real.exp (lam*auxReward x m p.1.val)*Real.exp (lam*auxReward (phaseShift x m) n p.2.val))]
        apply finite_sum_injection (concatenationMap x m n hx)
        · intro a b h
          exact concatenate_injective x m n (congrArg Subtype.val h)
        · intro w
          exact le_of_lt (Real.exp_pos _)
        · intro p
          change Real.exp (lam*auxReward x m p.1.val)*Real.exp (lam*auxReward (phaseShift x m) n p.2.val) ≤
            Real.exp (lam*auxReward x (m+n) (concatenate m n p.1.val p.2.val))
          rw [concatenate_reward x m n p.1.val p.1.property p.2.val,← Real.exp_add]
          apply le_of_eq
          congr 1
          ring
      have h := Real.log_le_log (mul_pos (aux_partition_positive x m hxc lam)
        (aux_partition_positive (phaseShift x m) n hyc lam)) hz
      rw [Real.log_mul (ne_of_gt (aux_partition_positive x m hxc lam))
        (ne_of_gt (aux_partition_positive (phaseShift x m) n hyc lam))] at h
      exact h

end ExternalBridgePressureWordConcatenation
