/-
Copyright (c) 2026 Allen Goodman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Goodman
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic

import Mathlib.Topology.Order.MonotoneConvergence.Metric

/-!
# Bisection method

For `f : ℝ → ℝ`, `Bisection.iterate f a b n` is the pair of endpoints after `n` bisection
steps starting from `(a, b)`. Each step keeps the left half if the product of its endpoint
values is nonpositive, and the right half otherwise. This handles either sign orientation.
If the midpoint is a root, the left half is retained and iteration continues.

When `a ≤ b`, the left endpoints increase, the right endpoints decrease, and the width after
`n` steps is `(b - a) / 2 ^ n`. Both endpoints converge to `Bisection.limit f a b`, defined as
the supremum of the left endpoints. The midpoint `Bisection.approximation f a b n` is within
`(b - a) / 2 ^ (n + 1)` of this limit.

If `f` is continuous on `[a, b]` and `f a * f b ≤ 0`, the limit is a root of `f`.
The main result is `Bisection.exists_root_tendsto_approximation`.
The iteration uses exact, noncomputable real arithmetic and permits `a = b`.

Convergence follows from the general theory of nested endpoints in
`Mathlib.Topology.Order.MonotoneConvergence.Metric`.
-/

@[expose] public section

noncomputable section

open Filter Set Topology

namespace Bisection

/-- One bisection step, retaining the left half when its endpoint values have nonpositive
product. -/
def step (f : ℝ → ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  if f p.1 * f ((p.1 + p.2) / 2) ≤ 0 then (p.1, (p.1 + p.2) / 2)
  else ((p.1 + p.2) / 2, p.2)

/-- The endpoints after `n` bisection steps starting from `(a, b)`. -/
def iterate (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) : ℝ × ℝ :=
  (step f)^[n] (a, b)

variable {f : ℝ → ℝ} {a b : ℝ}

@[simp]
theorem iterate_zero : iterate f a b 0 = (a, b) := rfl

theorem iterate_succ (n : ℕ) : iterate f a b (n + 1) = step f (iterate f a b n) :=
  Function.iterate_succ_apply' ..

private theorem step_bounds {p : ℝ × ℝ} (h : p.1 ≤ p.2) :
    p.1 ≤ (step f p).1 ∧ (step f p).1 ≤ (step f p).2 ∧ (step f p).2 ≤ p.2 := by
  unfold step
  split <;> dsimp <;> constructor
  · exact le_rfl
  · constructor <;> linarith
  · linarith
  · exact ⟨by linarith, le_rfl⟩

theorem iterate_fst_le_snd (hab : a ≤ b) (n : ℕ) :
    (iterate f a b n).1 ≤ (iterate f a b n).2 := by
  induction n with
  | zero => exact hab
  | succ n ih => simpa only [iterate_succ] using (step_bounds (f := f) ih).2.1

theorem monotone_fst (hab : a ≤ b) : Monotone fun n ↦ (iterate f a b n).1 := by
  refine monotone_nat_of_le_succ fun n ↦ ?_
  simpa only [iterate_succ] using (step_bounds (f := f) (iterate_fst_le_snd hab n)).1

theorem antitone_snd (hab : a ≤ b) : Antitone fun n ↦ (iterate f a b n).2 := by
  refine antitone_nat_of_succ_le fun n ↦ ?_
  simpa only [iterate_succ] using (step_bounds (f := f) (iterate_fst_le_snd hab n)).2.2

theorem fst_le_snd (hab : a ≤ b) (n m : ℕ) :
    (iterate f a b n).1 ≤ (iterate f a b m).2 :=
  (monotone_fst hab).forall_le_of_antitone (antitone_snd hab) (iterate_fst_le_snd hab) n m

theorem Icc_iterate_subset (hab : a ≤ b) (n : ℕ) :
    Icc (iterate f a b n).1 (iterate f a b n).2 ⊆ Icc a b :=
  Icc_subset_Icc (monotone_fst hab (Nat.zero_le n)) (antitone_snd hab (Nat.zero_le n))

/-- Bisection halves the width at each step. -/
theorem sub_iterate (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) :
    (iterate f a b n).2 - (iterate f a b n).1 = (b - a) / (2 : ℝ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ, step]
    split <;> dsimp <;> rw [pow_succ, ← div_div, ← ih] <;> ring

/-- Every iterate preserves a nonpositive product of endpoint values. -/
theorem mul_iterate_nonpos (h : f a * f b ≤ 0) (n : ℕ) :
    f (iterate f a b n).1 * f (iterate f a b n).2 ≤ 0 := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [iterate_succ, step]
    split
    · assumption
    · rename_i hmid
      dsimp
      rcases mul_pos_iff.mp (lt_of_not_ge hmid) with ⟨hl, hm⟩ | ⟨hl, hm⟩
      · exact mul_nonpos_of_nonneg_of_nonpos hm.le (nonpos_of_mul_nonpos_right ih hl)
      · exact mul_nonpos_of_nonpos_of_nonneg hm.le (nonneg_of_mul_nonpos_right ih hl)

/-- The midpoint after `n` bisection steps. -/
def approximation (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) : ℝ :=
  ((iterate f a b n).1 + (iterate f a b n).2) / 2

@[simp]
theorem approximation_zero : approximation f a b 0 = (a + b) / 2 := rfl

theorem approximation_mem_Icc_iterate (hab : a ≤ b) (n : ℕ) :
    approximation f a b n ∈ Icc (iterate f a b n).1 (iterate f a b n).2 := by
  have h := iterate_fst_le_snd (f := f) hab n
  constructor <;> dsimp [approximation] <;> linarith

theorem approximation_mem_Icc (hab : a ≤ b) (n : ℕ) :
    approximation f a b n ∈ Icc a b :=
  Icc_iterate_subset hab n (approximation_mem_Icc_iterate hab n)

@[simp]
theorem approximation_self (f : ℝ → ℝ) (a : ℝ) (n : ℕ) : approximation f a a n = a := by
  simpa using approximation_mem_Icc (f := f) (a := a) le_rfl n

/-- The bisection limit, defined as the supremum of the left endpoints. -/
def limit (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ⨆ n, (iterate f a b n).1

theorem bddAbove_range_fst (hab : a ≤ b) : BddAbove (range fun n ↦ (iterate f a b n).1) :=
  (monotone_fst hab).bddAbove_range_of_antitone (antitone_snd hab) (iterate_fst_le_snd hab)

theorem limit_mem_Icc_iterate (hab : a ≤ b) (n : ℕ) :
    limit f a b ∈ Icc (iterate f a b n).1 (iterate f a b n).2 :=
  mem_iInter.mp ((monotone_fst hab).ciSup_mem_iInter_Icc_of_antitone
    (antitone_snd hab) (iterate_fst_le_snd hab)) n

theorem limit_mem_Icc (hab : a ≤ b) : limit f a b ∈ Icc a b := by
  simpa using limit_mem_Icc_iterate (f := f) hab 0

@[simp]
theorem limit_self (f : ℝ → ℝ) (a : ℝ) : limit f a a = a := by
  simpa using limit_mem_Icc (f := f) (a := a) le_rfl

theorem tendsto_fst_limit (hab : a ≤ b) :
    Tendsto (fun n ↦ (iterate f a b n).1) atTop (𝓝 (limit f a b)) :=
  (monotone_fst hab).tendsto_atTop_ciSup_of_antitone (antitone_snd hab) (iterate_fst_le_snd hab)

theorem tendsto_sub_iterate_zero (f : ℝ → ℝ) (a b : ℝ) :
    Tendsto (fun n ↦ (iterate f a b n).2 - (iterate f a b n).1) atTop (𝓝 0) := by
  simpa only [sub_iterate] using tendsto_const_nhds.div_atTop
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))

theorem tendsto_dist_iterate_zero (f : ℝ → ℝ) (a b : ℝ) :
    Tendsto (fun n ↦ dist (iterate f a b n).1 (iterate f a b n).2) atTop (𝓝 0) := by
  simpa only [Real.dist_eq, abs_sub_comm, abs_zero] using (tendsto_sub_iterate_zero f a b).abs

theorem tendsto_snd_limit (hab : a ≤ b) :
    Tendsto (fun n ↦ (iterate f a b n).2) atTop (𝓝 (limit f a b)) :=
  (antitone_snd hab).tendsto_atTop_ciSup_of_tendsto_dist (monotone_fst hab)
    (iterate_fst_le_snd hab) (tendsto_dist_iterate_zero f a b)

theorem tendsto_approximation_limit (hab : a ≤ b) :
    Tendsto (approximation f a b) atTop (𝓝 (limit f a b)) :=
  (monotone_fst hab).tendsto_of_mem_Icc_of_tendsto_dist (antitone_snd hab)
    (iterate_fst_le_snd hab) (tendsto_dist_iterate_zero f a b) (approximation_mem_Icc_iterate hab)

/-- The midpoint error is at most half the width of the current interval. -/
theorem dist_approximation_limit_le (hab : a ≤ b) (n : ℕ) :
    dist (approximation f a b n) (limit f a b) ≤ (b - a) / (2 : ℝ) ^ (n + 1) := by
  obtain ⟨hl, hr⟩ := limit_mem_Icc_iterate (f := f) hab n
  rw [Real.dist_eq, approximation, pow_succ, ← div_div, ← sub_iterate f a b n, abs_le]
  constructor <;> linarith

theorem fst_mem_Icc (hab : a ≤ b) (n : ℕ) : (iterate f a b n).1 ∈ Icc a b :=
  Icc_iterate_subset hab n (left_mem_Icc.mpr (iterate_fst_le_snd hab n))

theorem snd_mem_Icc (hab : a ≤ b) (n : ℕ) : (iterate f a b n).2 ∈ Icc a b :=
  Icc_iterate_subset hab n (right_mem_Icc.mpr (iterate_fst_le_snd hab n))

/-- For a continuous function whose endpoint values have nonpositive product, the bisection limit
is a root. -/
theorem apply_limit_eq_zero (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hbracket : f a * f b ≤ 0) : f (limit f a b) = 0 := by
  have hc := (hf _ (limit_mem_Icc (f := f) hab)).tendsto
  have hl := hc.comp (tendsto_nhdsWithin_iff.mpr
    ⟨tendsto_fst_limit hab, .of_forall (fst_mem_Icc hab)⟩)
  have hr := hc.comp (tendsto_nhdsWithin_iff.mpr
    ⟨tendsto_snd_limit hab, .of_forall (snd_mem_Icc hab)⟩)
  have hsq := le_of_tendsto' (hl.mul hr) (mul_iterate_nonpos hbracket)
  exact mul_self_eq_zero.mp (le_antisymm hsq (mul_self_nonneg _))

/-- The bisection midpoints converge to a root, with error at most `(b - a) / 2 ^ (n + 1)`
after `n` steps. -/
theorem exists_root_tendsto_approximation (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hbracket : f a * f b ≤ 0) :
    ∃ x ∈ Icc a b, f x = 0 ∧ Tendsto (approximation f a b) atTop (𝓝 x) ∧
      ∀ n, dist (approximation f a b n) x ≤ (b - a) / (2 : ℝ) ^ (n + 1) :=
  ⟨limit f a b, limit_mem_Icc hab, apply_limit_eq_zero hab hf hbracket,
    tendsto_approximation_limit hab, dist_approximation_limit_le hab⟩

end Bisection
