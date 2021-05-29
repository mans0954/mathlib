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

variable {μ}


lemma zoug {f : α → ℝ} (hf : integrable f μ) :
  ∫⁻ x, ennreal.of_real (f x) ∂μ < ∞ :=
begin
  refine lt_of_le_of_lt _ ((has_finite_integral_iff_norm _).1 hf.has_finite_integral),
  apply lintegral_mono,
  assume x,
  simp,
  exact le_abs_self _,
end

lemma ennreal.exists_lt_lower_semicontinuous' [sigma_finite μ] (f : α → ℝ≥0)
  (fmeas : measurable f) (fint : ∫⁻ x, f x ∂ μ < ∞) {ε : ℝ} (εpos : 0 < ε) :
  ∃ g : α → ℝ≥0∞, (∀ x, (f x : ℝ≥0∞) < g x) ∧ lower_semicontinuous g ∧ (∀ᵐ x ∂ μ, g x < ⊤)
  ∧ (integrable (λ x, (g x).to_real) μ) ∧ (∫ x, (g x).to_real ∂μ < ∫ x, f x ∂μ + ε) :=
begin
  let δ : ℝ≥0 := ⟨ε/2, (half_pos εpos).le⟩,
  have δpos : 0 < δ := half_pos εpos,
  have int_f_ne_top : ∫⁻ (a : α), (f a) ∂μ ≠ ⊤ := lt_top_iff_ne_top.1 fint,
  rcases ennreal.exists_lt_lower_semicontinuous μ f fmeas δpos with ⟨g, f_lt_g, gcont, gint⟩,
  have gint_lt : ∫⁻ (x : α), g x ∂μ < ∞ := calc
    ∫⁻ (x : α), g x ∂μ ≤ ∫⁻ (x : α), ↑(f x) ∂μ + δ : gint
      ... < ⊤ : by simpa using fint,
  have g_lt_top : ∀ᵐ (x : α) ∂μ, g x < ⊤ := ae_lt_top gcont.measurable gint_lt,
  have Ig : ∫⁻ (a : α), ennreal.of_real (g a).to_real ∂μ = ∫⁻ (a : α), g a ∂μ,
  { apply lintegral_congr_ae,
    filter_upwards [g_lt_top],
    assume x hx,
    simp only [hx.ne, ennreal.of_real_to_real, ne.def, not_false_iff] },
  refine ⟨g, f_lt_g, gcont, g_lt_top, _, _⟩,
  { refine ⟨gcont.measurable.to_real.ae_measurable, _⟩,
    simp [has_finite_integral_iff_norm, real.norm_eq_abs, abs_of_nonneg],
    convert gint_lt using 1 },
  { rw [integral_eq_lintegral_of_nonneg_ae, integral_eq_lintegral_of_nonneg_ae],
    { calc
      ennreal.to_real (∫⁻ (a : α), ennreal.of_real (g a).to_real ∂μ)
          = ennreal.to_real (∫⁻ (a : α), g a ∂μ) : by congr' 1
      ... ≤ ennreal.to_real (∫⁻ (a : α), f a ∂μ + δ) :
        begin
          apply ennreal.to_real_mono _ gint,
          simpa using int_f_ne_top,
        end
      ... = ennreal.to_real (∫⁻ (a : α), f a ∂μ) + δ :
        by rw [ennreal.to_real_add int_f_ne_top ennreal.coe_ne_top, ennreal.coe_to_real]
      ... < ennreal.to_real (∫⁻ (a : α), f a ∂μ) + ε :
        add_lt_add_left (by simp [δ, half_lt_self εpos]) _
      ... = (∫⁻ (a : α), ennreal.of_real ↑(f a) ∂μ).to_real + ε :
        by simp },
    { apply filter.eventually_of_forall (λ x, _), simp },
    { exact fmeas.nnreal_coe.ae_measurable, },
    { apply filter.eventually_of_forall (λ x, _), simp },
    { apply gcont.measurable.to_real.ae_measurable } }
end

/-- Given an integrable function `f`, there exists an upper semicontinuous function `g ≤ f` with
integral arbitrarily close to that of `f`. -/
lemma ennreal.exists_upper_semicontinuous_le
  (f : α → ℝ≥0) (hf : measurable f) (int_f : ∫⁻ x, f x ∂μ < ∞) {ε : ℝ≥0} (εpos : 0 < ε) :
  ∃ g : α → ℝ≥0, (∀ x, g x ≤ f x) ∧ upper_semicontinuous g ∧ (∫⁻ x, f x ∂μ ≤ ∫⁻ x, g x ∂μ + ε) :=
begin
  sorry
end

lemma ennreal.exists_upper_semicontinuous_le' (f : α → ℝ≥0) (hf : measurable f)
  (If : ∫⁻ x, f x ∂ μ < ∞) {ε : ℝ} (εpos : 0 < ε) :
  ∃ g : α → ℝ≥0, (∀ x, g x ≤ f x) ∧ upper_semicontinuous g
  ∧ (∫ x, (f x : ℝ) ∂μ - ε ≤ ∫ x, g x ∂μ) :=
begin
  let δ : ℝ≥0 := ⟨ε, εpos.le⟩,
  have δpos : 0 < δ := εpos,
  rcases ennreal.exists_upper_semicontinuous_le f hf If δpos with ⟨g, gf, gcont, gint⟩,
  have Ig : ∫⁻ x, g x ∂ μ < ∞,
  { apply lt_of_le_of_lt ( lintegral_mono (λ x, _)) If,
    simpa using gf x },
  refine ⟨g, gf, gcont, _⟩,
  rw [integral_eq_lintegral_of_nonneg_ae, integral_eq_lintegral_of_nonneg_ae],
  { rw sub_le_iff_le_add,
    convert ennreal.to_real_mono _ gint,
    { simp, },
    { rw ennreal.to_real_add Ig.ne ennreal.coe_ne_top, simp },
    { simpa using Ig.ne } },
  { apply filter.eventually_of_forall, simp },
  { exact gcont.measurable.nnreal_coe.ae_measurable },
  { apply filter.eventually_of_forall, simp },
  { exact hf.nnreal_coe.ae_measurable }
end


lemma integrable.of_real
  {f : α → ℝ} (hf : integrable f μ) :
  integrable (λ x, (real.to_nnreal (f x) : ℝ)) μ :=
begin
  split,
  have Z := ae_measurable.nnreal_of_real,

  apply measurable.comp_ae_measurable nnreal.measurable_coe _,
  apply hf.ae_measurable.nnreal_of_real,


  refine ⟨hf.to_real.ae_measurable, _⟩,
  rw has_finite_integral_iff_norm,
  simp only [real.norm_eq_abs, abs_of_nonneg, ennreal.to_real_nonneg],
  convert If using 1,
  apply lintegral_congr_ae,
  filter_upwards [ae_lt_top hf If],
  assume x hx,
  simp [hx.ne],
end

lemma integrable_to_real_of_lintegral_lt_top
  {f : α → ℝ≥0∞} (hf : measurable f) (If : ∫⁻ x, f x ∂μ < ∞) :
  integrable (λ x, ennreal.to_real (f x)) μ :=
begin
  refine ⟨hf.to_real.ae_measurable, _⟩,
  rw has_finite_integral_iff_norm,
  simp only [real.norm_eq_abs, abs_of_nonneg, ennreal.to_real_nonneg],
  convert If using 1,
  apply lintegral_congr_ae,
  filter_upwards [ae_lt_top hf If],
  assume x hx,
  simp [hx.ne],
end

lemma real.exists_le_lower_semicontinuous [sigma_finite μ]
  (f : α → ℝ) (fmeas : measurable f) (hf : integrable f μ) (ε : ℝ) (εpos : 0 < ε) :
  ∃ g : α → ereal, (∀ x, (f x : ereal) < g x) ∧ lower_semicontinuous g ∧
  (∀ᵐ x ∂ μ, g x < ⊤) ∧ (∫ x, ereal.to_real (g x) ∂μ < ∫ x, f x ∂μ + ε) :=
begin
  let δ : ℝ≥0 := ⟨ε, εpos.le⟩,
  have δpos : 0 < δ := εpos,
  let fp : α → ℝ≥0 := λ x, real.to_nnreal (f x),
  have : integrable (λ x, (fp x : ℝ)) μ := hf.of_real,
  have int_fp : ∫⁻ x, fp x ∂μ < ∞ := zoug hf,
  rcases ennreal.exists_lt_lower_semicontinuous' fp fmeas.nnreal_of_real int_fp δpos with
    ⟨gp, fp_lt_gp, gpcont, gp_lt_top, gp_integrable, gpint⟩,
  let fm : α → ℝ≥0 := λ x, real.to_nnreal (-f x),
  have int_fm : ∫⁻ x, fm x ∂μ < ∞ := zoug hf.neg,
  rcases ennreal.exists_upper_semicontinuous_le' fm fmeas.neg.nnreal_of_real int_fm δpos with
    ⟨gm, gm_le_fm, gmcont, gmint⟩,
  let g : α → ereal := λ x, (gp x : ereal) - (gm x),
  refine ⟨g, _, _, _, _⟩,
  show ∫ (x : α), (g x).to_real ∂μ < ∫ (x : α), f x ∂μ + ε, from calc
    ∫ (x : α), (g x).to_real ∂μ = ∫ (x : α), ereal.to_real (gp x) - ereal.to_real (gm x) ∂μ :
      sorry/-begin
        apply integral_congr_ae,
        filter_upwards [gp_lt_top],
        assume x hx,
        rw ereal.to_real_sub;
        simp [hx.ne],
      end-/
    ... = ∫ (x : α), ereal.to_real (gp x) ∂ μ - ∫ (x : α), gm x ∂μ :
      sorry/-begin
        simp only [ereal.to_real_coe_ennreal, ennreal.coe_to_real, coe_coe],
        apply integral_sub (integrable_to_real_of_lintegral_lt_top gpcont.measurable gpint_lt),
        apply hf.mono,
        apply (nnreal.continuous_coe.measurable.comp gmcont.measurable).ae_measurable,
        apply filter.eventually_of_forall (λ x, _),
        simp only [nnreal.norm_eq],
        calc (gm x : ℝ) ≤ fm x : nnreal.coe_le_coe.2 (gm_le_fm x)
        ... ≤ ∥f x∥ : by simp [fm, real.norm_eq_abs, abs_nonneg, neg_le_abs_self]
      end-/
    ... = ennreal.to_real (∫⁻ (x : α), gp x ∂ μ) - ∫ (x : α), gm x ∂μ :
    sorry/-
    begin
      congr' 1,
      rw integral_eq_lintegral_of_nonneg_ae,
      { congr' 1,
        apply lintegral_congr_ae,
        filter_upwards [gp_lt_top],
        assume x hx,
        simp [hx.ne] },
      { apply filter.eventually_of_forall (λ x, _),
        simp },
      { exact gpcont.measurable.ereal_coe_ennreal.ereal_to_real.ae_measurable },
    end-/
    ... ≤ ennreal.to_real (∫⁻ (x : α), ↑(fp x) ∂μ + ↑δ) - ∫ (x : α), gm x ∂μ :
      sub_le_sub (ennreal.to_real_mono (by simp [int_fp.ne]) gpint) (le_refl _)
    ... < ∫ (x : α), f x ∂μ + ε : sorry,
  show ∀ᵐ (x : α) ∂μ, g x < ⊤,
  { filter_upwards [gp_lt_top],
    assume x hx,
    simp [g, ereal.sub_eq_add_neg, lt_top_iff_ne_top, lt_top_iff_ne_top.1 hx] }
end

#exit
  show ∀ x, (f x : ereal) < g x,
  { assume x,
    rw ereal.coe_eq_coe_ennreal_sub_coe_ennreal (f x),
    refine ereal.sub_lt_sub_of_lt_of_le _ _ _ _,
    { simp only [ereal.coe_ennreal_lt_coe_ennreal_iff, coe_coe], exact (fp_lt_gp x) },
    { simp only [ennreal.coe_le_coe, ereal.coe_ennreal_le_coe_ennreal_iff, coe_coe],
      exact (gm_le_fm x) },
    { simp only [ereal.coe_ennreal_ne_bot, ne.def, not_false_iff, coe_coe] },
    { simp only [ereal.coe_nnreal_ne_top, ne.def, not_false_iff, coe_coe] } },
  show lower_semicontinuous g,
  { apply lower_semicontinuous.add',
    { exact ereal.continuous_coe_ennreal.comp_lower_semicontinuous gpcont
        (λ x y hxy, ereal.coe_ennreal_le_coe_ennreal_iff.2 hxy) },
    { apply ereal.continuous_neg.comp_upper_semicontinuous_antimono _
        (λ x y hxy, ereal.neg_le_neg_iff.2 hxy),
      dsimp,
      apply ereal.continuous_coe_ennreal.comp_upper_semicontinuous _
        (λ x y hxy, ereal.coe_ennreal_le_coe_ennreal_iff.2 hxy),
      exact ennreal.continuous_coe.comp_upper_semicontinuous gmcont
        (λ x y hxy, ennreal.coe_le_coe.2 hxy) },
    { assume x,
      exact ereal.continuous_at_add (by simp) (by simp) } },
  show ∫ (x : α), (g x).to_real ∂μ ≤ ∫ (x : α), f x ∂μ + ε, from calc
    ∫ (x : α), (g x).to_real ∂μ ≤ ∫ (x : α), f x ∂μ + ε : sorry

end

#exit

lemma integral_eq_lintegral_pos_part_sub_lintegral_neg_part {f : α → ℝ} (hf : integrable f μ) :
  ∫ a, f a ∂μ =
  ennreal.to_real (∫⁻ a, (ennreal.of_real $ f a) ∂μ) -
  ennreal.to_real (∫⁻ a, (ennreal.of_real $ - f a) ∂μ)

end measure_theory
