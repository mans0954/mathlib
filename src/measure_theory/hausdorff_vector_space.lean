/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import measure_theory.hausdorff_measure
import measure_theory.lebesgue_measure

/-!
# Haudorff measure in vector spaces

-/

open set
open_locale measure_theory ennreal

variables {ι : Type*} [fintype ι] [nonempty ι]

lemma zoug : μH[fintype.card ι] (set.pi (univ : set ι) (λ i, Ico (0 : ℝ) 1)) ≤ 1 :=
begin
  have N : ℕ := sorry,
  have N_pos : 0 < N := sorry,
  have N_pos' : (0 : ℝ) < N := by exact_mod_cast N_pos,
  let t : (ι → fin N) → set (ι → ℝ) := λ a, set.pi univ (λ i, Ico (a i/N) ((a i + 1)/N)),
  have : set.pi (univ : set ι) (λ i, Ico (0 : ℝ) 1) ⊆ ⋃ (a : ι → fin N), t a,
  { assume c hc,
    simp only [mem_univ_pi, mem_Ico] at hc,
    let d : ι → ℕ := λ i, nat_floor (c i * N),
    have d_lt : ∀ i, d i < N,
    { assume i,
      rw [nat_floor_lt_iff (mul_nonneg (hc i).1 (nat.cast_nonneg _))],
      conv_rhs { rw ← one_mul (N : ℝ) },
      exact mul_lt_mul (hc i).2 le_rfl N_pos' zero_le_one },
    refine mem_Union.2 ⟨λ i, ⟨d i, d_lt i⟩, _⟩,
    simp only [mem_univ_pi, mem_Ico, fin.coe_mk, coe_coe],
    refine λ i, ⟨_, _⟩,
    { rw div_le_iff N_pos',
      exact nat_floor_le (mul_nonneg (hc i).1 (nat.cast_nonneg _)) },
    { rw lt_div_iff N_pos',
      exact lt_nat_floor_add_one _ } },
end
