/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import measure_theory.regular
import topology.semicontinuous
import measure_theory.bochner_integration
import topology.instances.ereal

open_locale ennreal nnreal

open measure_theory measure_theory.measure

variables {α : Type*} [topological_space α] [measurable_space α] [borel_space α] (μ : measure α)
  [weakly_regular μ]

/-- Given an integrable function `f`, there exists a lower semicontinuous function `g ≥ f` with
integral arbitrarily close to that of `f`. -/
lemma ennreal.exists_le_lower_semicontinuous
  (f : α → ℝ≥0∞) (hf : measurable f) {ε : ℝ≥0∞} (εpos : 0 < ε) :
  ∃ g : α → ℝ≥0∞, (∀ x, f x ≤ g x) ∧ lower_semicontinuous g ∧ (∫⁻ x, g x ∂μ ≤ ∫⁻ x, f x ∂μ + ε) :=
begin
  by_cases int_f : ∫⁻ x, f x ∂μ = ∞,
  { refine ⟨λ x, ∞, λ x, le_top, lower_semicontinuous_const, by simp [int_f]⟩ },
  sorry
end

/-- Given an integrable function `f` in a sigma-finite space, there exists a lower semicontinuous
function `g > f` with integral arbitrarily close to that of `f`. -/
lemma ennreal.exists_lt_lower_semicontinuous [sigma_finite μ]
  (f : α → ℝ≥0) (fmeas : measurable f) {ε : ℝ≥0} (εpos : 0 < ε) :
  ∃ g : α → ℝ≥0∞, (∀ x, (f x : ℝ≥0∞) < g x) ∧ lower_semicontinuous g ∧
    (∫⁻ x, g x ∂μ ≤ ∫⁻ x, f x ∂μ + ε) :=
begin
--  by_cases int_f : ∫⁻ x, f x ∂μ = ∞,
--  { refine ⟨λ x, ∞, λ x, ennreal.coe_lt_top, lower_semicontinuous_const, by simp [int_f]⟩ },
  rcases exists_integrable_pos_of_sigma_finite μ (nnreal.half_pos εpos) with ⟨w, wpos, wmeas, wint⟩,
  let f' := λ x, ((f x + w x : ℝ≥0) : ℝ≥0∞),
  rcases ennreal.exists_le_lower_semicontinuous μ f' (fmeas.add wmeas).ennreal_coe
    (ennreal.coe_pos.2 (nnreal.half_pos εpos)) with ⟨g, le_g, gcont, gint⟩,
  refine ⟨g, λ x, _, gcont, _⟩,
  { calc (f x : ℝ≥0∞) < f' x : by simpa [← ennreal.coe_lt_coe] using add_lt_add_left (wpos x) (f x)
    ... ≤ g x : le_g x },
  { calc ∫⁻ (x : α), g x ∂μ
        ≤ ∫⁻ (x : α), f x + w x ∂μ + (ε / 2 : ℝ≥0) : gint
    ... = ∫⁻ (x : α), f x ∂ μ + ∫⁻ (x : α), w x ∂ μ + (ε / 2 : ℝ≥0) :
      by rw lintegral_add fmeas.ennreal_coe wmeas.ennreal_coe
    ... ≤ ∫⁻ (x : α), f x ∂ μ + (ε / 2 : ℝ≥0) + (ε / 2 : ℝ≥0) :
      add_le_add_right (add_le_add_left wint.le _) _
    ... = ∫⁻ (x : α), f x ∂μ + ε : by rw [add_assoc, ← ennreal.coe_add, nnreal.add_halves] },
end

/-- Given an integrable function `f`, there exists an upper semicontinuous function `g ≤ f` with
integral arbitrarily close to that of `f`. -/
lemma ennreal.exists_upper_semicontinuous_le
  (f : α → ℝ≥0∞) (hf : measurable f) (int_f : ∫⁻ x, f x ∂μ < ∞) (ε : ℝ≥0∞) (εpos : 0 < ε) :
  ∃ g : α → ℝ≥0∞, (∀ x, g x ≤ f x) ∧ lower_semicontinuous g ∧ (∫⁻ x, f x ∂μ ≤ ∫⁻ x, g x ∂μ + ε) :=
begin
  sorry
end

lemma real.exists_le_lower_semicontinuous
  (f : α → ℝ) (hf : integrable f μ) (ε : ℝ) (εpos : 0 < ε) :
  ∃ g : α → ereal, (∀ x, (f x : ereal) ≤ g x) ∧ lower_semicontinuous g ∧
  (∀ᵐ x ∂ μ, g x < ⊤) ∧
  (∫ x, ereal.to_real (g x) ∂μ ≤ ∫ x, f x ∂μ + ε) :=
begin
  sorry
end



end measure_theory
