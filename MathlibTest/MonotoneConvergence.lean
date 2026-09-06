import Mathlib.Topology.Order.MonotoneConvergence.Metric
import Mathlib.Analysis.SpecificLimits.Basic

open Filter Set Topology
open scoped NNReal

-- The selected points need not themselves be monotone.
example (u : ℕ → ℝ) (hu : ∀ n, u n ∈ Icc 0 ((1 / 2 : ℝ) ^ n)) :
    Tendsto u atTop (𝓝 0) := by
  have hg : Antitone fun n : ℕ ↦ (1 / 2 : ℝ) ^ n :=
    pow_right_anti₀ (by norm_num) (by norm_num)
  have hd : Tendsto (fun n : ℕ ↦ dist (0 : ℝ) ((1 / 2 : ℝ) ^ n)) atTop (𝓝 0) := by
    simpa only [dist_self] using (tendsto_const_nhds (x := (0 : ℝ))).dist
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1))
  simpa using (monotone_const : Monotone fun _ : ℕ ↦ (0 : ℝ)).tendsto_of_mem_Icc_of_tendsto_dist
    hg (fun n ↦ by positivity) hd hu

-- The same theory applies directly to nonnegative reals.
example : (⋂ n : ℕ, Icc (0 : ℝ≥0) ((1 / 2 : ℝ≥0) ^ n)) = {0} := by
  have hg : Antitone fun n : ℕ ↦ (1 / 2 : ℝ≥0) ^ n :=
    pow_right_anti₀ (by norm_num) (by norm_num)
  have hd : Tendsto (fun n : ℕ ↦ dist (0 : ℝ≥0) ((1 / 2 : ℝ≥0) ^ n)) atTop (𝓝 0) := by
    simpa only [dist_self] using (tendsto_const_nhds (x := (0 : ℝ≥0))).dist
      (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (1 / 2 : ℝ≥0) < 1))
  simpa using
    (monotone_const : Monotone fun _ : ℕ ↦ (0 : ℝ≥0)).iInter_Icc_eq_singleton_of_tendsto_dist
      hg (fun _ ↦ zero_le) hd

-- Directed indices need not be linearly ordered, and an interval need not shrink to a point.
example : (⨆ _ : ℕ × ℕ, (0 : ℝ)) < (⨅ _ : ℕ × ℕ, (1 : ℝ)) ∧
    (⋂ _ : ℕ × ℕ, Icc (0 : ℝ) 1) = Icc 0 1 := by
  refine ⟨by simp, ?_⟩
  simpa using
    (monotone_const : Monotone fun _ : ℕ × ℕ ↦ (0 : ℝ)).iInter_Icc_eq_Icc_ciSup_ciInf
      (antitone_const : Antitone fun _ : ℕ × ℕ ↦ (1 : ℝ)) (fun _ ↦ zero_le_one)
