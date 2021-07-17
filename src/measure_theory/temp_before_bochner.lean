/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import measure_theory.temp_from_set_to_before_bochner

/-! # Temporary file, please remove
-/

noncomputable theory
open topological_space measure_theory measure_theory.Lp filter
open_locale nnreal ennreal topological_space big_operators measure_theory

namespace measure_theory

variables {α β γ E E' F F' G G' H 𝕜 𝕂 : Type*} {p : ℝ≥0∞}
  [is_R_or_C 𝕜] -- 𝕜 for ℝ or ℂ
  [is_R_or_C 𝕂] [measurable_space 𝕂] -- 𝕂 for ℝ or ℂ, together with a measurable_space
  [measurable_space β] -- β for a generic measurable space
  -- F for Lp submodule
  [normed_group F] [normed_space 𝕂 F] [measurable_space F] [borel_space F]
  [second_countable_topology F]
  -- F' for integrals on F
  [normed_group F'] [normed_space 𝕂 F'] [measurable_space F'] [borel_space F']
  [second_countable_topology F'] [normed_space ℝ F'] [complete_space F']
  -- G for Lp add_subgroup
  [normed_group G] [measurable_space G] [borel_space G] [second_countable_topology G]
  -- G' for integrals on G
  [normed_group G'] [measurable_space G'] [borel_space G'] [second_countable_topology G']
  [normed_space ℝ G'] [complete_space G']
  -- H for measurable space and normed group (hypotheses of mem_ℒp)
  [measurable_space H] [normed_group H]

lemma mem_set_congr_ae [measurable_space α] {μ : measure α} {s t : set α} (hst : s =ᵐ[μ] t) :
  ∀ᵐ x ∂μ, x ∈ s ↔ x ∈ t :=
hst.mono (λ x hx, by rwa [set.mem_def, set.mem_def, ← eq_iff_iff])

lemma mem_ℒ0_iff_ae_measurable [measurable_space α] {μ : measure α} {f : α → H} :
  mem_ℒp f 0 μ ↔ ae_measurable f μ :=
by { simp_rw mem_ℒp, refine and_iff_left _, simp, }

lemma simple_func.mem_range_iff_preimage_nonempty [measurable_space α] (f : simple_func α G)
  (y : G) :
  y ∈ f.range ↔ f ⁻¹' {y} ≠ ∅ :=
begin
  rw [simple_func.mem_range, set.mem_range, ne.def, set.eq_empty_iff_forall_not_mem],
  push_neg,
  simp_rw [set.mem_preimage, set.mem_singleton_iff],
end

lemma simple_func.mem_range_add_iff [measurable_space α] (f g : simple_func α G) (y : G) :
  y ∈ (f + g).range ↔ (f + g) ⁻¹' {y} ≠ ∅ :=
by { rw ← simple_func.coe_add, exact simple_func.mem_range_iff_preimage_nonempty (f + g) y, }

lemma simple_func.range_add_subset_add_range [measurable_space α] (f g : simple_func α G)
  [decidable_eq G] :
  (f + g).range ⊆ f.range + g.range :=
begin
  intro x,
  simp_rw [finset.mem_add, simple_func.mem_range, set.mem_range, simple_func.coe_add, pi.add_apply],
  rintros ⟨y, hy⟩,
  exact ⟨f y, g y, ⟨y, rfl⟩, ⟨y, rfl⟩, hy⟩,
end

/-- Indicator of as set as as `simple_func`. -/
def indicator_simple_func [measurable_space α] [has_zero γ] {s : set α} (hs : measurable_set s)
  (c : γ) :
  simple_func α γ :=
simple_func.piecewise s hs (simple_func.const α c) (simple_func.const α 0)

lemma indicator_simple_func_coe [measurable_space α] [has_zero γ] {s : set α}
  {hs : measurable_set s} {c : γ} :
  ⇑(indicator_simple_func hs c) = s.indicator (λ (_x : α), c) :=
by simp only [indicator_simple_func, simple_func.coe_const, simple_func.const_zero,
  simple_func.coe_zero, set.piecewise_eq_indicator, simple_func.coe_piecewise]

lemma indicator_simple_func_zero [measurable_space α] [has_zero γ] {s : set α}
  {hs : measurable_set s} :
  indicator_simple_func hs (0 : γ) = 0 :=
begin
  ext1,
  rw indicator_simple_func_coe,
  simp,
end

lemma indicator_simple_func_range_subset [measurable_space α] [has_zero γ] [decidable_eq γ]
  {s : set α} (hs : measurable_set s) (c : γ) :
  (indicator_simple_func hs c).range ⊆ insert (0 : γ) {c} :=
begin
  intro x,
  simp_rw [simple_func.mem_range, indicator_simple_func_coe, set.mem_range_indicator],
  simp only [set.mem_image, exists_and_distrib_right, ne.def, finset.mem_insert,
    finset.mem_singleton],
  intro h,
  cases h,
  { exact or.inl h.1, },
  { exact or.inr h.2.symm, },
end

lemma indicator_simple_func_range [measurable_space α] [has_zero γ] [decidable_eq γ] {s : set α}
  (hs : measurable_set s) (c : γ) (hs_nonempty : s.nonempty) (hs_not_univ : s ≠ set.univ) :
  (indicator_simple_func hs c).range = insert (0 : γ) {c} :=
begin
  ext1 x,
  simp_rw [simple_func.mem_range, indicator_simple_func_coe, set.mem_range_indicator],
  simp only [hs_nonempty, set.nonempty.image_const, set.mem_singleton_iff, ne.def,
    finset.mem_insert, finset.mem_singleton],
  simp [hs_not_univ],
end

lemma indicator_simple_func_univ_range [measurable_space α] [has_zero γ] [hα : nonempty α] (c : γ) :
  (indicator_simple_func (@measurable_set.univ α _) c).range = {c} :=
begin
  ext1 x,
  simp_rw [simple_func.mem_range, indicator_simple_func_coe, set.mem_range_indicator],
  simp,
end

lemma simple_func.coe_finset_sum_apply {ι} [measurable_space α] [add_comm_group γ]
  (f : ι → simple_func α γ) (s : finset ι) (x : α) :
  (∑ i in s, f i) x = ∑ i in s, f i x :=
begin
  haveI : decidable_eq ι := classical.dec_eq ι,
  refine finset.induction _ _ s,
  { simp, },
  intros j s hjs h_sum,
  rw [finset.sum_insert hjs, simple_func.coe_add, pi.add_apply, h_sum, ← finset.sum_insert hjs],
end

lemma simple_func.coe_finset_sum {ι} [measurable_space α] [add_comm_group γ]
  (f : ι → simple_func α γ) (s : finset ι) :
  ⇑(∑ i in s, f i) = ∑ i in s, f i :=
by { ext1 x, simp_rw finset.sum_apply, exact simple_func.coe_finset_sum_apply f s x, }

lemma simple_func_eq_sum_indicator [measurable_space α] [add_comm_group γ]
  (f : simple_func α γ) :
  f = ∑ y in f.range,
    indicator_simple_func (simple_func.measurable_set_fiber f y) y :=
begin
  ext,
  simp [indicator_simple_func],
  rw simple_func.coe_finset_sum_apply,
  simp_rw simple_func.piecewise_apply,
  simp only [simple_func.coe_const, function.const_apply, set.mem_preimage, set.mem_singleton_iff,
    pi.zero_apply, simple_func.coe_zero],
  haveI : decidable_eq γ := classical.dec_eq γ,
  have hfa : f a = ite (f a ∈ f.range) (f a) (0 : γ), by simp [simple_func.mem_range_self],
  have h := (finset.sum_ite_eq f.range (f a) (λ i, i)).symm,
  dsimp only at h,
  rw ← hfa at h,
  convert h,
  ext1,
  congr,
end

lemma simple_func.exists_forall_norm_le [measurable_space α] [has_norm γ] (f : simple_func α γ) :
  ∃ C, ∀ x, ∥f x∥ ≤ C :=
simple_func.exists_forall_le (simple_func.map (λ x, ∥x∥) f)

lemma snorm'_simple_func [normed_group γ] [measurable_space α] {p : ℝ} (f : simple_func α γ)
  (μ : measure α) :
  snorm' f p μ = (∑ y in f.range, (nnnorm y : ℝ≥0∞) ^ p * μ (f ⁻¹' {y})) ^ (1/p) :=
begin
  rw snorm',
  have h_map : (λ a, (nnnorm (f a) : ℝ≥0∞) ^ p)
    = simple_func.map (λ a : γ, (nnnorm a : ℝ≥0∞) ^ p) f,
  { simp, },
  simp_rw h_map,
  rw simple_func.lintegral_eq_lintegral,
  rw simple_func.map_lintegral,
end

lemma snorm_ess_sup_simple_func_lt_top [normed_group γ] [measurable_space α] (f : simple_func α γ)
  (μ : measure α) :
  snorm_ess_sup f μ < ∞ :=
begin
  rw snorm_ess_sup,
  obtain ⟨C, hfC⟩ := simple_func.exists_forall_norm_le f,
  simp_rw ← of_real_norm_eq_coe_nnnorm,
  refine (ess_sup_le_of_ae_le (ennreal.of_real C) (eventually_of_forall (λ x, _))).trans_lt
    ennreal.of_real_lt_top,
  exact ennreal.of_real_le_of_real (hfC x),
end

lemma simple_func.mem_ℒp_top [measurable_space α] (f : simple_func α H) (μ : measure α) :
  mem_ℒp f ∞ μ :=
⟨simple_func.ae_measurable f,
  by { rw snorm_exponent_top, exact snorm_ess_sup_simple_func_lt_top f μ}⟩

lemma simple_func.finite_measure_of_mem_ℒp [measurable_space α] {μ : measure α}
  (hp_pos : 0 < p) (hp_ne_top : p ≠ ∞)
  (f : simple_func α H) (hf : mem_ℒp f p μ) (y : H) (hyf : y ∈ f.range) :
  y = 0 ∨ μ (f ⁻¹' {y}) < ∞ :=
begin
  have hp_pos_real : 0 < p.to_real, from ennreal.to_real_pos_iff.mpr ⟨hp_pos, hp_ne_top⟩,
  have hf_snorm := mem_ℒp.snorm_lt_top hf,
  rw [snorm_eq_snorm' hp_pos.ne.symm hp_ne_top, snorm'_simple_func,
    ← ennreal.lt_rpow_one_div_iff] at hf_snorm,
  swap, { simp [hp_pos_real], },
  rw ennreal.top_rpow_of_pos at hf_snorm,
  swap, { simp [hp_pos_real], },
  rw ennreal.sum_lt_top_iff at hf_snorm,
  specialize hf_snorm y hyf,
  rw ennreal.mul_lt_top_iff at hf_snorm,
  cases hf_snorm,
  { exact or.inr hf_snorm.2, },
  cases hf_snorm,
  { simp only [hp_pos_real, ennreal.rpow_eq_zero_iff, and_true, ennreal.coe_ne_top, or_false,
      nnnorm_eq_zero, ennreal.coe_eq_zero, false_and] at hf_snorm,
    exact or.inl hf_snorm, },
  { simp [hf_snorm], },
end

lemma simple_func.finite_measure_of_integrable [measurable_space α] {μ : measure α}
  (f : simple_func α H) (hf : integrable f μ) (y : H) (hyf : y ∈ f.range) :
  y = 0 ∨ μ (f ⁻¹' {y}) < ∞ :=
begin
  rw ← mem_ℒp_one_iff_integrable at hf,
  exact simple_func.finite_measure_of_mem_ℒp ennreal.zero_lt_one ennreal.coe_ne_top f hf y hyf,
end

lemma simple_func.mem_ℒp_of_integrable [measurable_space α] {μ : measure α} (p : ℝ≥0∞)
  {f : simple_func α H} (hf : integrable f μ) :
  mem_ℒp f p μ :=
begin
  refine ⟨simple_func.ae_measurable f, _⟩,
  by_cases hp0 : p = 0,
  { simp [hp0], },
  rw ← ne.def at hp0,
  by_cases hp_top : p = ∞,
  { simp only [hp_top, snorm_exponent_top],
    exact snorm_ess_sup_simple_func_lt_top f μ, },
  have hp_pos : 0 < p.to_real,
    from ennreal.to_real_pos_iff.mpr ⟨lt_of_le_of_ne (zero_le _) hp0.symm, hp_top⟩,
  rw [snorm_eq_snorm' hp0 hp_top, snorm'_simple_func],
  refine ennreal.rpow_lt_top_of_nonneg _ _,
  { simp, },
  refine (ennreal.sum_lt_top (λ y hy, _)).ne,
  have hyμ := simple_func.finite_measure_of_integrable f hf y hy,
  cases hyμ,
  { simp [hyμ, hp_pos], },
  refine ennreal.mul_lt_top (ennreal.rpow_lt_top_of_nonneg ennreal.to_real_nonneg _) hyμ,
  exact ennreal.coe_ne_top,
end

lemma simple_func.mem_ℒp_of_finite_measure_range [measurable_space α] {μ : measure α} (p : ℝ≥0∞)
  {f : simple_func α H} (hf : ∀ y ∈ f.range, y = 0 ∨ μ (f ⁻¹' {y}) < ∞) :
  mem_ℒp f p μ :=
begin
  by_cases hp0 : p = 0,
  { rw [hp0, mem_ℒ0_iff_ae_measurable],
    exact simple_func.ae_measurable f, },
  rw ← ne.def at hp0,
  by_cases hp_top : p = ∞,
  { rw hp_top, exact simple_func.mem_ℒp_top f μ, },
  have hp_pos : 0 < p.to_real,
    from ennreal.to_real_pos_iff.mpr ⟨lt_of_le_of_ne (zero_le _) hp0.symm, hp_top⟩,
  refine ⟨simple_func.ae_measurable f, _⟩,
  rw snorm_eq_snorm' hp0 hp_top,
  rw snorm'_simple_func,
  refine ennreal.rpow_lt_top_of_nonneg (by simp) (ne_of_lt _),
  refine ennreal.sum_lt_top_iff.mpr (λ y hy, _),
  cases hf y hy with h h,
  { simp [h, hp_pos], },
  { refine ennreal.mul_lt_top _ h,
    exact ennreal.rpow_lt_top_of_nonneg ennreal.to_real_nonneg ennreal.coe_ne_top, },
end

lemma simple_func.mem_ℒp_iff_integrable [measurable_space α] {μ : measure α} {f : simple_func α H}
  (hp_pos : 0 < p) (hp_ne_top : p ≠ ∞) :
  mem_ℒp f p μ ↔ integrable f μ :=
begin
  refine ⟨λ h, _, simple_func.mem_ℒp_of_integrable p⟩,
  rw ← mem_ℒp_one_iff_integrable,
  refine simple_func.mem_ℒp_of_finite_measure_range 1 _,
  exact simple_func.finite_measure_of_mem_ℒp hp_pos hp_ne_top f h,
end

lemma simple_func.mem_ℒp_of_finite_measure [measurable_space α] (p : ℝ≥0∞) (f : simple_func α H)
  (μ : measure α) [finite_measure μ] :
  mem_ℒp f p μ :=
begin
  obtain ⟨C, hfC⟩ := simple_func.exists_forall_norm_le f,
  exact mem_ℒp.of_bound (simple_func.ae_measurable f) C (eventually_of_forall hfC),
end

protected lemma simple_func.integrable [measurable_space α] {μ : measure α} [finite_measure μ]
  (f : simple_func α H) :
  integrable f μ :=
mem_ℒp_one_iff_integrable.mp (simple_func.mem_ℒp_of_finite_measure 1 f μ)

lemma simple_func.measure_preimage_ne_zero_lt_top [measurable_space α]
  {μ : measure α} (f : simple_func α H) (hf : integrable f μ) {s : finset H} (hs0 : (0 : H) ∉ s) :
  μ (f ⁻¹' s) < ∞ :=
begin
  rw ← simple_func.sum_measure_preimage_singleton,
  refine ennreal.sum_lt_top (λ y hy, _),
  have hf' := simple_func.finite_measure_of_integrable f hf y,
  by_cases hyf : y ∈ f.range,
  { cases hf' hyf with hy0 hyμ,
    { rw hy0 at hy,
      exact absurd hy hs0, },
    { exact hyμ, }, },
  rw ← simple_func.preimage_eq_empty_iff f y at hyf,
  simp [hyf],
end

lemma simple_func.preimage_set [measurable_space α] (f : simple_func α γ) (s : set γ)
  [decidable_pred s] :
  f ⁻¹' s = f ⁻¹' ↑(f.range.filter s) :=
begin
  ext1 x,
  simp_rw [set.mem_preimage, finset.mem_coe, finset.mem_filter],
  simp only [true_and, set.mem_range_self, simple_func.mem_range],
  refl,
end

lemma simple_func.preimage_map_ne_zero_subset {δ} [measurable_space α] [has_zero δ] [has_zero γ]
  {f : simple_func α γ} (g : γ → δ) (hg : g 0 = 0)
  {s : finset δ} (hs0 : (0 : δ) ∉ s) [decidable_pred (λ z : γ, z ≠ 0)] :
  (f.map g) ⁻¹' s ⊆ f ⁻¹' (finset.filter (λ z, z ≠ (0 : γ)) f.range) :=
begin
  intro x,
  simp_rw [simple_func.map_preimage, set.mem_preimage, finset.mem_coe, finset.mem_filter],
  intro h,
  refine ⟨h.1, λ hf0, _⟩,
  rw [hf0, hg] at h,
  exact hs0 h.2,
end

lemma simple_func.preimage_map_ne_zero_subset' {δ} [measurable_space α] [has_zero δ] [has_zero γ]
  {f : simple_func α γ} (g : γ → δ) (hg : g 0 = 0)
  {s : set δ} (hs0 : (0 : δ) ∉ s) [decidable_pred (λ z : γ, z ≠ 0)] :
  (f.map g) ⁻¹' s ⊆ f ⁻¹' (finset.filter (λ z, z ≠ (0 : γ)) f.range) :=
begin
  haveI : decidable_pred s := classical.dec_pred s,
  have h_range : (f.map g) ⁻¹' s = (f.map g) ⁻¹' ↑((f.map g).range.filter s),
    from simple_func.preimage_set _ s,
  rw h_range,
  refine simple_func.preimage_map_ne_zero_subset g hg _,
  rw finset.mem_filter,
  push_neg,
  intro h,
  exact hs0,
end

lemma simple_func.preimage_map_singleton_ne_zero_subset {δ} [measurable_space α] [has_zero δ]
  [has_zero γ] {f : simple_func α γ} (g : γ → δ) (hg : g 0 = 0)
  {y : δ} (hy0 : y ≠ 0) [decidable_pred (λ z : γ, z ≠ 0)] :
  (f.map g) ⁻¹' {y} ⊆ f ⁻¹' (finset.filter (λ z, z ≠ (0 : γ)) f.range) :=
begin
  haveI : decidable_pred ({y} : set δ) := classical.dec_pred _,
  refine simple_func.preimage_map_ne_zero_subset' g hg (λ h, _),
  rw set.mem_singleton_iff at h,
  exact hy0 h.symm,
end

lemma simple_func.integrable_map [measurable_space α] [normed_group β] {μ : measure α}
  (f : simple_func α H) (hf : integrable f μ) (g : H → β) (hg : g 0 = 0) :
  integrable (f.map g) μ :=
begin
  have hf' := simple_func.finite_measure_of_integrable _ hf,
  refine ⟨(f.map g).ae_measurable, _⟩,
  rw has_finite_integral,
  have h_eq : (λ a, (nnnorm (f.map g a) : ℝ≥0∞)) = (f.map g).map (λ a, (nnnorm a : ℝ≥0∞)),
  { simp_rw simple_func.coe_map, },
  simp_rw h_eq,
  rw simple_func.lintegral_eq_lintegral,
  rw simple_func.lintegral,
  refine ennreal.sum_lt_top (λ z hz, _),
  rw [simple_func.range_map, finset.mem_image] at hz,
  obtain ⟨u, hu, huz⟩ := hz,
  haveI : decidable_eq β := classical.dec_eq β,
  rw [simple_func.range_map, finset.mem_image] at hu,
  obtain ⟨y, hy, hyu⟩ := hu,
  cases hf' y hy with h h,
  { rw [h, hg] at hyu,
    simp only [hyu.symm, nnnorm_zero, ennreal.coe_zero] at huz,
    simp [huz.symm], },
  { by_cases hz0 : z = 0,
    { simp [hz0], },
    nth_rewrite 0 huz.symm,
    refine ennreal.mul_lt_top ennreal.coe_lt_top _,
    have h_ss1 : ((f.map g).map (λ a, (nnnorm a : ℝ≥0∞))) ⁻¹' {z}
      ⊆ (f.map g) ⁻¹' (finset.filter (λ z, z ≠ (0 : β)) (f.map g).range),
    { refine simple_func.preimage_map_ne_zero_subset' _ _ _,
      { simp, },
      { intro h, rw set.mem_singleton_iff at h, exact hz0 h.symm, }, },
    haveI : decidable_pred (λ (z : H), z ≠ 0) := classical.dec_pred _,
    have h_ss2 : (f.map g) ⁻¹' (finset.filter (λ z, z ≠ (0 : β)) (f.map g).range)
      ⊆ f ⁻¹' (finset.filter (λ z, z ≠ (0 : H)) f.range),
    { refine simple_func.preimage_map_ne_zero_subset' g hg _,
      simp, },
    refine (measure_mono (set.subset.trans h_ss1 h_ss2)).trans_lt _,
    refine simple_func.measure_preimage_ne_zero_lt_top f hf _,
    simp, },
end

/-- Indicator of a set as an ` α →ₘ[μ] E`. -/
def indicator_const_ae [measurable_space α] (μ : measure α) {s : set α} (hs : measurable_set s)
  (c : H) :
  α →ₘ[μ] H :=
ae_eq_fun.mk (s.indicator (λ x, c)) ((ae_measurable_indicator_iff hs).mp ae_measurable_const)

lemma measurable_indicator_const_ae [measurable_space α] {s : set α} (hs : measurable_set s)
  {c : H} :
  measurable (s.indicator (λ _, c)) :=
measurable_const.indicator hs

lemma ae_measurable_indicator_const_ae [measurable_space α] (μ : measure α) {s : set α}
  (hs : measurable_set s) {c : H} :
  ae_measurable (s.indicator (λ _, c)) μ :=
(ae_measurable_indicator_iff hs).mp ae_measurable_const

lemma indicator_const_ae_coe [measurable_space α] {μ : measure α} {s : set α}
  {hs : measurable_set s} {c : H} :
  ⇑(indicator_const_ae μ hs c) =ᵐ[μ] s.indicator (λ _, c) :=
ae_eq_fun.coe_fn_mk (s.indicator (λ _, c)) (ae_measurable_indicator_const_ae μ hs)

lemma indicator_const_comp {δ} [has_zero γ] [has_zero δ] {s : set α} (c : γ) (f : γ → δ)
  (hf : f 0 = 0) :
  (λ x, f (s.indicator (λ x, c) x)) = s.indicator (λ x, f c) :=
(set.indicator_comp_of_zero hf).symm

lemma snorm_ess_sup_indicator_le [normed_group γ] [measurable_space α] {μ : measure α}
  (s : set α) (f : α → γ) :
  snorm_ess_sup (s.indicator f) μ ≤ snorm_ess_sup f μ :=
begin
  refine ess_sup_mono_ae (eventually_of_forall (λ x, _)),
  rw [ennreal.coe_le_coe, nnnorm_indicator_eq_indicator_nnnorm],
  exact set.indicator_le_self s _ x,
end

lemma snorm_ess_sup_indicator_const_le [normed_group γ] [measurable_space α] {μ : measure α}
  (s : set α) (c : γ) :
  snorm_ess_sup (s.indicator (λ x : α , c)) μ ≤ (nnnorm c : ℝ≥0∞) :=
begin
  refine (snorm_ess_sup_indicator_le s (λ x, c)).trans _,
  by_cases hμ0 : μ = 0,
  { simp [hμ0], },
  rw snorm_ess_sup_const c hμ0,
  exact le_rfl,
end

lemma snorm_ess_sup_indicator_const_eq [normed_group γ] [measurable_space α] {μ : measure α}
  (s : set α) (c : γ) (hμs : 0 < μ s) :
  snorm_ess_sup (s.indicator (λ x : α , c)) μ = (nnnorm c : ℝ≥0∞) :=
begin
  refine le_antisymm (snorm_ess_sup_indicator_const_le s c) _,
  rw snorm_ess_sup,
  by_contra h,
  push_neg at h,
  rw lt_iff_not_ge' at hμs,
  refine hμs (le_of_eq _),
  have hs_ss : s ⊆ {x | (nnnorm c : ℝ≥0∞) ≤ (nnnorm (s.indicator (λ x : α , c) x) : ℝ≥0∞)},
  { intros x hx_mem,
    simp [hx_mem], },
  refine measure_mono_null hs_ss _,
  have h' := ae_iff.mp (ae_lt_of_ess_sup_lt h),
  push_neg at h',
  exact h',
end

lemma snorm_indicator_const [normed_group γ] [measurable_space α] {μ : measure α} {s : set α}
  {c : γ} (hs : measurable_set s) (hp : 0 < p) (hp_top : p ≠ ∞) :
  snorm (s.indicator (λ x, c)) p μ = (nnnorm c) * (μ s) ^ (1 / p.to_real) :=
begin
  have hp_pos : 0 < p.to_real, from ennreal.to_real_pos_iff.mpr ⟨hp, hp_top⟩,
  rw snorm_eq_snorm' hp.ne.symm hp_top,
  rw snorm',
  simp_rw [nnnorm_indicator_eq_indicator_nnnorm, ennreal.coe_indicator],
  have h_indicator_pow : (λ a : α, s.indicator (λ (x : α), (nnnorm c : ℝ≥0∞)) a ^ p.to_real)
    = s.indicator (λ (x : α), ↑(nnnorm c) ^ p.to_real),
  { rw indicator_const_comp (nnnorm c : ℝ≥0∞) (λ x, x ^ p.to_real) _, simp [hp_pos], },
  rw [h_indicator_pow, lintegral_indicator _ hs, set_lintegral_const, ennreal.mul_rpow_of_nonneg],
  swap, { simp [hp_pos.le], },
  rw [← ennreal.rpow_mul, mul_one_div_cancel hp_pos.ne.symm, ennreal.rpow_one],
end

lemma snorm_indicator_const' [normed_group γ] [measurable_space α] {μ : measure α} {s : set α}
  {c : γ} (hs : measurable_set s) (hμs : 0 < μ s) (hp : 0 < p) :
  snorm (s.indicator (λ x, c)) p μ = (nnnorm c) * (μ s) ^ (1 / p.to_real) :=
begin
  by_cases hp_top : p = ∞,
  { simp [hp_top, snorm_ess_sup_indicator_const_eq s c hμs], },
  exact snorm_indicator_const hs hp hp_top,
end

lemma mem_ℒp_indicator_const (p : ℝ≥0∞) [measurable_space α] {μ : measure α} {s : set α}
  (hs : measurable_set s) (c : H) (hμsc : c = 0 ∨ μ s < ∞) :
  mem_ℒp (s.indicator (λ x : α , c)) p μ :=
begin
  cases hμsc with hc hμs,
  { simp only [hc, set.indicator_zero],
    refine ⟨ae_measurable_const, _⟩,
    by_cases hp0 : p = 0,
    { simp [hp0], },
    by_cases hμ0 : μ = 0,
    { simp [hμ0], },
    rw snorm_const _ hp0 hμ0,
    simp, },
  refine ⟨(ae_measurable_indicator_iff hs).mp ae_measurable_const, _⟩,
  by_cases hp0 : p = 0,
  { simp [hp0], },
  rw ← ne.def at hp0,
  by_cases hp_top : p = ∞,
  { rw [hp_top, snorm_exponent_top],
    exact (snorm_ess_sup_indicator_const_le s c).trans_lt ennreal.coe_lt_top, },
  have hp_pos : 0 < p.to_real,
    from ennreal.to_real_pos_iff.mpr ⟨lt_of_le_of_ne (zero_le _) hp0.symm, hp_top⟩,
  rw snorm_eq_snorm' hp0 hp_top,
  simp_rw snorm',
  refine ennreal.rpow_lt_top_of_nonneg _ _,
  { simp only [hp_pos.le, one_div, inv_nonneg], },
  simp_rw [nnnorm_indicator_eq_indicator_nnnorm, ennreal.coe_indicator],
  have h_indicator_pow : (λ a : α, s.indicator (λ (x : α), (nnnorm c : ℝ≥0∞)) a ^ p.to_real)
    = s.indicator (λ (x : α), ↑(nnnorm c) ^ p.to_real),
  { rw indicator_const_comp (nnnorm c : ℝ≥0∞) (λ x, x ^ p.to_real) _, simp [hp_pos], },
  rw [h_indicator_pow, lintegral_indicator _ hs],
  simp [hp_pos, hμs.ne, not_le.mpr hp_pos, not_lt.mpr hp_pos.le],
end

lemma mem_ℒp_indicator_const_ae [measurable_space α] {μ : measure α} {s : set α}
  (hs : measurable_set s) (c : H) (hμsc : c = 0 ∨ μ s < ∞) :
  mem_ℒp (indicator_const_ae μ hs c) p μ :=
by { rw mem_ℒp_congr_ae indicator_const_ae_coe, exact mem_ℒp_indicator_const p hs c hμsc }

section indicator_Lp
variables [measurable_space α] {μ : measure α} {s : set α} {hs : measurable_set s}
  {c : G} {hμsc : c = 0 ∨ μ s < ∞}

/-- Indicator of a set as an element of `Lp`. -/
def indicator_Lp (p : ℝ≥0∞) (hs : measurable_set s) (c : G) (hμsc : c = 0 ∨ μ s < ∞) : Lp G p μ :=
mem_ℒp.to_Lp (indicator_const_ae μ hs c) (mem_ℒp_indicator_const_ae hs c hμsc)

lemma indicator_Lp_coe : ⇑(indicator_Lp p hs c hμsc) =ᵐ[μ] indicator_const_ae μ hs c :=
mem_ℒp.coe_fn_to_Lp (mem_ℒp_indicator_const_ae hs c hμsc)

lemma indicator_Lp_coe_fn (p : ℝ≥0∞) (hs : measurable_set s) (c : G) (hμsc : c = 0 ∨ μ s < ∞) :
  ⇑(indicator_Lp p hs c hμsc) =ᵐ[μ] s.indicator (λ _, c) :=
indicator_Lp_coe.trans indicator_const_ae_coe

lemma indicator_Lp_coe_fn_mem : ∀ᵐ (x : α) ∂μ, x ∈ s → (indicator_Lp p hs c hμsc x) = c :=
(indicator_Lp_coe_fn p hs c hμsc).mono (λ x hx hxs, hx.trans (set.indicator_of_mem hxs _))

lemma indicator_Lp_coe_fn_nmem : ∀ᵐ (x : α) ∂μ, x ∉ s → (indicator_Lp p hs c hμsc x) = 0 :=
(indicator_Lp_coe_fn p hs c hμsc).mono (λ x hx hxs, hx.trans (set.indicator_of_not_mem hxs _))

lemma norm_indicator_Lp (hp_pos : 0 < p) (hp_ne_top : p ≠ ∞) :
  ∥indicator_Lp p hs c hμsc∥ = ∥c∥ * (μ s).to_real ^ (1 / p.to_real) :=
begin
  rw [norm_def, snorm_congr_ae (indicator_Lp_coe_fn p hs c hμsc),
    snorm_indicator_const hs hp_pos hp_ne_top, ennreal.to_real_mul, ennreal.to_real_rpow],
  congr,
end

lemma norm_indicator_Lp_top (hμs_pos : 0 < μ s) : ∥indicator_Lp ∞ hs c hμsc∥ = ∥c∥ :=
begin
  rw [norm_def, snorm_congr_ae (indicator_Lp_coe_fn ∞ hs c hμsc),
    snorm_indicator_const' hs hμs_pos ennreal.coe_lt_top],
  simp only [div_zero, ennreal.rpow_zero, mul_one, ennreal.coe_to_real, ennreal.top_to_real,
    coe_nnnorm],
end

lemma norm_indicator_Lp' (hp_pos : 0 < p) (hμs_pos : 0 < μ s) :
  ∥indicator_Lp p hs c hμsc∥ = ∥c∥ * (μ s).to_real ^ (1 / p.to_real) :=
begin
  by_cases hp_top : p = ∞,
  { simp only [hp_top, div_zero, mul_one, ennreal.top_to_real, real.rpow_zero],
    rw hp_top,
    exact norm_indicator_Lp_top hμs_pos, },
  { exact norm_indicator_Lp hp_pos hp_top, },
end

end indicator_Lp



lemma measure_finite_of_integrable_on_ae [measurable_space α] {μ : measure α} {f : α → H}
  {s : set α} (hfs : integrable_on f s μ)
  (hs : measurable_set s) (C : ℝ≥0∞) (hC : 0 < C) (hfC : ∀ᵐ x ∂μ, x ∈ s → C ≤ nnnorm (f x)) :
  μ s < ∞ :=
begin
  rw [integrable_on, integrable, has_finite_integral] at hfs,
    have hf_int_s := hfs.2,
  have hbs_int : ∫⁻ x in s, C ∂μ ≤ ∫⁻ x in s, (nnnorm (f x)) ∂μ,
  { refine lintegral_mono_ae _,
    rw ae_restrict_iff' hs,
    exact hfC, },
  rw lintegral_const at hbs_int,
  rw measure.restrict_apply_univ at hbs_int,
  have h_mul_lt_top : C * μ s < ∞, from hbs_int.trans_lt hf_int_s,
  rw ennreal.mul_lt_top_iff at h_mul_lt_top,
  cases h_mul_lt_top with h h,
  { exact h.2, },
  cases h with h h,
  { exact absurd h hC.ne.symm, },
  { rw h, exact ennreal.coe_lt_top, },
end

lemma measure_finite_of_integrable_on [measurable_space α] {μ : measure α} {f : α → H} {s : set α}
  (hfs : integrable_on f s μ)
  (hs : measurable_set s) (C : ℝ≥0∞) (hC : 0 < C) (hfC : ∀ x ∈ s, C ≤ nnnorm (f x)) :
  μ s < ∞ :=
measure_finite_of_integrable_on_ae hfs hs C hC (eventually_of_forall hfC)

lemma finite_fiber_of_integrable [measurable_space α] {μ : measure α}
  (f : α → G) (hf : integrable f μ) (y : G) (hy0 : y ≠ 0) (hfy : measurable_set (f ⁻¹' {y})) :
  μ (f ⁻¹' {y}) < ∞ :=
begin
  refine measure_finite_of_integrable_on hf.integrable_on hfy (nnnorm y : ℝ≥0∞) _ _,
  { rwa [← of_real_norm_eq_coe_nnnorm, ennreal.of_real_pos, norm_pos_iff], },
  { intros x hxy,
    rw [set.mem_preimage, set.mem_singleton_iff] at hxy,
    rw hxy,
    exact le_rfl, },
end

lemma simple_func.finite_fiber [measurable_space α] {μ : measure α}
  (f : simple_func α G) (hf : integrable f μ) (y : G) (hy0 : y ≠ 0) :
  μ (f ⁻¹' {y}) < ∞ :=
finite_fiber_of_integrable f hf y hy0 (simple_func.measurable_set_fiber _ y)

lemma simple_func.zero_or_finite_fiber [measurable_space α] (μ : measure α)
  (f : simple_func α G) (hf : integrable f μ) (y : G) :
  y = 0 ∨ μ (f ⁻¹' {y}) < ∞ :=
begin
  by_cases hy : y = 0,
  { exact or.inl hy, },
  { exact or.inr (simple_func.finite_fiber f hf y hy), },
end



protected lemma L1.integrable [measurable_space α] {μ : measure α} (f : α →₁[μ] G) :
  integrable f μ :=
by { rw ← mem_ℒp_one_iff_integrable, exact Lp.mem_ℒp _, }

lemma integrable.smul_const [measurable_space α] {μ : measure α} {f : α → ℝ} (hf : integrable f μ)
  (c : H) [borel_space H] [normed_space ℝ H] :
  integrable (λ x, f x • c) μ :=
begin
  by_cases hc0 : c = 0,
  { simp [hc0], },
  rwa integrable_smul_const hc0,
  { exact real.complete_space, },
  { exact real.borel_space, },
end

lemma integrable_on.smul_const [measurable_space α] {μ : measure α} {f : α → ℝ} {s : set α}
  (hf : integrable_on f s μ) (hs : measurable_set s) (c : H) [borel_space H] [normed_space ℝ H] :
  integrable (s.indicator (λ x, f x • c)) μ :=
begin
  by_cases hc0 : c = 0,
  { simp [hc0], },
  rw integrable_indicator_iff hs,
  rw integrable_on,
  rwa integrable_smul_const hc0,
  { exact real.complete_space, },
  { exact real.borel_space, },
end


lemma ae_all_finset {ι} [measurable_space α] {μ : measure α} (p : ι → α → Prop) (s : finset ι) :
  (∀ᵐ x ∂μ, ∀ i ∈ s, p i x) ↔ ∀ i ∈ s, ∀ᵐ x ∂μ, p i x :=
begin
  refine ⟨λ h i hi, h.mono (λ x hx, hx i hi), _⟩,
  haveI : decidable_eq ι := classical.dec_eq ι,
  refine finset.induction _ _ s,
  { simp only [eventually_true, finset.not_mem_empty, forall_false_left, implies_true_iff], },
  intros i s his hs h_insert,
  have h : ∀ (i : ι), i ∈ s → (∀ᵐ (x : α) ∂μ, p i x),
    from λ j hj, h_insert j (finset.mem_insert_of_mem hj),
  specialize hs h,
  specialize h_insert i (finset.mem_insert_self i s),
  refine h_insert.mp (hs.mono (λ x hx1 hx2, _)),
  intros j hj,
  rw finset.mem_insert at hj,
  cases hj with hji hjs,
  { rwa hji, },
  { exact hx1 j hjs, },
end

lemma eventually_eq.finset_sum {ι} [measurable_space α] [add_comm_group γ]
  {μ : measure α} (f g : ι → α → γ) (s : finset ι) (hf : ∀ i ∈ s, f i =ᵐ[μ] g i) :
  ∑ i in s, f i =ᵐ[μ] ∑ i in s, g i :=
begin
  simp_rw eventually_eq at hf,
  rw ← ae_all_finset _ s at hf,
  refine hf.mono (λ x hx, _),
  rw [finset.sum_apply, finset.sum_apply],
  exact finset.sum_congr rfl hx,
end



lemma set.preimage_zero {γ} [has_zero γ] (s : set γ) [decidable ((0 : γ) ∈ s)]:
  (0 : α → γ) ⁻¹' s = ite ((0 : γ) ∈ s) set.univ ∅ :=
by { change (λ x, (0 : γ)) ⁻¹' s = ite ((0 : γ) ∈ s) set.univ ∅,  rw set.preimage_const }

lemma set.indicator_const_preimage_self {γ} [has_zero γ] (s : set α) (c : γ) [decidable (c = 0)] :
  s.indicator (λ (_x : α), c) ⁻¹' {c} = ite (c = 0) set.univ s :=
begin
  classical,
  rw set.indicator_preimage,
  simp_rw [set.preimage_const, set.preimage_zero, set.mem_singleton_iff, eq_self_iff_true, if_true],
  by_cases hc : c = 0,
  { simp_rw [hc, eq_self_iff_true, if_true],
    simp, },
  { rw ← ne.def at hc,
    simp_rw [hc, hc.symm, if_false],
    simp, },
end


end measure_theory
