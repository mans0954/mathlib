/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import analysis.normed_space.inner_product
import measure_theory.l2_space
import measure_theory.temp_simple_func

/-! # Conditional expectation

## Implementation notes

When several `measurable_space` structures are introduced, the "default" one is the last one.
For example, when writing `{m m0 : measurable_space α} {μ : measure α}`, `μ` is a measure with
respect to `m0`.

-/

noncomputable theory
open topological_space measure_theory measure_theory.Lp filter
open_locale nnreal ennreal topological_space big_operators measure_theory

/-- Like `ae_measurable`, but the `measurable_space` structures used for the measurability
statement and for the measure are different.

TODO: change the definition of ae_measurable to use ae_measurable' ? -/
def ae_measurable' {α β} [measurable_space β] (m : measurable_space α) {m0 : measurable_space α}
  (f : α → β) (μ : measure α) :
  Prop :=
∃ g : α → β, @measurable α β m _ g ∧ f =ᵐ[μ] g

lemma measurable.ae_measurable' {α β} [measurable_space β] {m m0 : measurable_space α} {f : α → β}
  {μ : measure α} (hf : @measurable α β m _ f) :
  ae_measurable' m f μ :=
⟨f, hf, eventually_eq.rfl⟩

namespace ae_measurable'

variables {α β : Type*} [measurable_space β] {f : α → β}

lemma mono {m2 m m0 : measurable_space α} (hm : m2 ≤ m)
  {μ : measure α} (hf : ae_measurable' m2 f μ) :
  ae_measurable' m f μ :=
by { obtain ⟨g, hg_meas, hfg⟩ := hf, exact ⟨g, measurable.mono hg_meas hm le_rfl, hfg⟩, }

lemma ae_measurable {m m0 : measurable_space α} (hm : m ≤ m0)
  {μ : measure α} (hf : ae_measurable' m f μ) :
  ae_measurable f μ :=
ae_measurable'.mono hm hf

lemma ae_measurable'_of_ae_measurable'_trim {m m0 m0' : measurable_space α} (hm0 : m0 ≤ m0')
  {μ : measure α} (hf : ae_measurable' m f (μ.trim hm0)) :
  ae_measurable' m f μ :=
by { obtain ⟨g, hg_meas, hfg⟩ := hf, exact ⟨g, hg_meas, ae_eq_of_ae_eq_trim hm0 hfg⟩, }

lemma congr_ae {m m0 : measurable_space α} {μ : measure α}
  {f g : α → β} (hf : ae_measurable' m f μ) (hfg : f =ᵐ[μ] g) :
  ae_measurable' m g μ :=
by { obtain ⟨f', hf'_meas, hff'⟩ := hf, exact ⟨f', hf'_meas, hfg.symm.trans hff'⟩, }

lemma add [has_add β] [has_measurable_add₂ β] {m m0 : measurable_space α}
  {μ : measure α} {f g : α → β} (hf : ae_measurable' m f μ) (hg : ae_measurable' m g μ) :
  ae_measurable' m (f+g) μ :=
begin
  rcases hf with ⟨f', h_f'_meas, hff'⟩,
  rcases hg with ⟨g', h_g'_meas, hgg'⟩,
  refine ⟨f' + g', @measurable.add α m _ _ _ _ f' g' h_f'_meas h_g'_meas, _⟩,
  exact hff'.add hgg',
end

lemma smul {δ} [has_scalar δ β] [measurable_space δ] [has_measurable_smul δ β]
  {m m0 : measurable_space α} {μ : measure α} (c : δ) {f : α → β} (hf : ae_measurable' m f μ) :
  ae_measurable' m (c • f) μ :=
begin
  rcases hf with ⟨f', h_f'_meas, hff'⟩,
  refine ⟨c • f', @measurable.const_smul α m _ _ _ _ _ _ f' h_f'_meas c, _⟩,
  exact eventually_eq.fun_comp hff' (λ x, c • x),
end

lemma restrict {m m0 : measurable_space α}
  {μ : measure α} (hf : ae_measurable' m f μ) (s : set α) :
  ae_measurable' m f (μ.restrict s) :=
by { obtain ⟨g, hg_meas, hfg⟩ := hf, exact ⟨g, hg_meas, ae_restrict_of_ae hfg⟩, }

end ae_measurable'

namespace measure_theory

variables {α β γ E E' F F' G G' H 𝕜 𝕂 : Type*} {p : ℝ≥0∞}
  [is_R_or_C 𝕜] -- 𝕜 for ℝ or ℂ
  [is_R_or_C 𝕂] [measurable_space 𝕂] -- 𝕂 for ℝ or ℂ, together with a measurable_space
  [measurable_space β] -- β for a generic measurable space
  -- E for L2
  [inner_product_space 𝕂 E] [measurable_space E] [borel_space E] [second_countable_topology E]
  -- E' for integrals on E
  [inner_product_space 𝕂 E'] [measurable_space E'] [borel_space E'] [second_countable_topology E']
  [normed_space ℝ E'] [complete_space E'] [is_scalar_tower ℝ 𝕂 E']
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

lemma integrable.restrict [measurable_space α] {μ : measure α} {f : α → H} (hf : integrable f μ)
  (s : set α) :
  integrable f (μ.restrict s) :=
hf.integrable_on.integrable

lemma ae_measurable.restrict [measurable_space α] {f : α → β} {μ : measure α}
  (hf : ae_measurable f μ) (s : set α) :
  ae_measurable f (μ.restrict s) :=
ae_measurable'.restrict hf s

notation α ` →₂[`:25 μ `] ` E := measure_theory.Lp E 2 μ

section Lp_sub

variables (𝕂 F)
/-- Lp subspace of functions `f` verifying `ae_measurable' m f μ`. -/
def Lp_sub [opens_measurable_space 𝕂] (m : measurable_space α) [measurable_space α] (p : ℝ≥0∞)
  (μ : measure α) :
  submodule 𝕂 (Lp F p μ) :=
{ carrier   := {f : (Lp F p μ) | ae_measurable' m f μ} ,
  zero_mem' := ⟨(0 : α → F), @measurable_zero _ α _ m _, Lp.coe_fn_zero _ _ _⟩,
  add_mem'  := λ f g hf hg, (hf.add hg).congr_ae (Lp.coe_fn_add f g).symm,
  smul_mem' := λ c f hf, (hf.smul c).congr_ae (Lp.coe_fn_smul c f).symm, }
variables {𝕂 F}

variables [opens_measurable_space 𝕂]

lemma mem_Lp_sub_iff_ae_measurable' {m m0 : measurable_space α} {μ : measure α} {f : Lp F p μ} :
  f ∈ Lp_sub F 𝕂 m p μ ↔ ae_measurable' m f μ :=
by simp_rw [← set_like.mem_coe, ← submodule.mem_carrier, Lp_sub, set.mem_set_of_eq]

lemma Lp_sub.ae_measurable' {m m0 : measurable_space α} {μ : measure α} (f : Lp_sub E 𝕂 m p μ) :
  ae_measurable' m f μ :=
mem_Lp_sub_iff_ae_measurable'.mp f.mem

lemma mem_Lp_sub_self {m0 : measurable_space α} (μ : measure α) (f : Lp F p μ) :
  f ∈ Lp_sub F 𝕂 m0 p μ :=
mem_Lp_sub_iff_ae_measurable'.mpr (Lp.ae_measurable f)

lemma Lp_sub_coe {m m0 : measurable_space α} {p : ℝ≥0∞} {μ : measure α} {f : Lp_sub F 𝕂 m p μ} :
  ⇑f = (f : Lp F p μ) :=
coe_fn_coe_base f

lemma ae_measurable'_of_tendsto' {m m0 : measurable_space α} (hm : m ≤ m0) {μ : measure α}
  {ι} [nonempty ι] [semilattice_sup ι] [hp : fact (1 ≤ p)] [complete_space G]
  (f : ι → Lp G p μ) (g : ι → α → G)
  (f_lim : Lp G p μ) (hfg : ∀ n, f n =ᵐ[μ] g n) (hg : ∀ n, @measurable α _ m _ (g n))
  (h_tendsto : filter.at_top.tendsto f (𝓝 f_lim)) :
  ae_measurable' m f_lim μ :=
begin
  have hg_m0 : ∀ n, measurable (g n), from λ n, measurable.mono (hg n) hm le_rfl,
  have h_cauchy_seq := h_tendsto.cauchy_seq,
  have h_cau_g : tendsto (λ (n : ι × ι), snorm (g n.fst - g n.snd) p μ) at_top (𝓝 0),
  { rw cauchy_seq_Lp_iff_cauchy_seq_ℒp at h_cauchy_seq,
    suffices h_snorm_eq : ∀ n : ι × ι, snorm (⇑(f n.fst) - ⇑(f n.snd)) p μ
        = snorm (g n.fst - g n.snd) p μ,
      by { simp_rw h_snorm_eq at h_cauchy_seq, exact h_cauchy_seq, },
    exact λ n, snorm_congr_ae ((hfg n.fst).sub (hfg n.snd)), },
  have h_cau_g_m : tendsto (λ (n : ι × ι), @snorm α _ m _ (g n.fst - g n.snd) p (μ.trim hm))
      at_top (𝓝 0),
    { suffices h_snorm_trim : ∀ n : ι × ι, @snorm α _ m _ (g n.fst - g n.snd) p (μ.trim hm)
        = snorm (g n.fst - g n.snd) p μ,
      { simp_rw h_snorm_trim, exact h_cau_g, },
      refine λ n, snorm_trim _ _,
      exact @measurable.sub α m _ _ _ _ (g n.fst) (g n.snd) (hg n.fst) (hg n.snd), },
  have mem_Lp_g : ∀ n, @mem_ℒp α G m _ _ (g n) p (μ.trim hm),
  { refine λ n, ⟨@measurable.ae_measurable α _ m _ _ _ (hg n), _⟩,
    have h_snorm_fg : @snorm α _ m _ (g n) p (μ.trim hm) = snorm (f n) p μ,
      by { rw snorm_trim hm (hg n), exact snorm_congr_ae (hfg n).symm, },
    rw h_snorm_fg,
    exact Lp.snorm_lt_top (f n), },
  let g_Lp := λ n, @mem_ℒp.to_Lp α G m p _ _ _ _ _ (g n) (mem_Lp_g n),
  have h_g_ae_m := λ n, @mem_ℒp.coe_fn_to_Lp α G m p _ _ _ _ _ _ (mem_Lp_g n),
  have h_cau_seq_g_Lp : cauchy_seq g_Lp,
  { rw cauchy_seq_Lp_iff_cauchy_seq_ℒp,
    suffices h_eq : ∀ n : ι × ι, @snorm α _ m _ ((g_Lp n.fst) - (g_Lp n.snd)) p (μ.trim hm)
        = @snorm α _ m _ (g n.fst - g n.snd) p (μ.trim hm),
      by { simp_rw h_eq, exact h_cau_g_m, },
    exact λ n, @snorm_congr_ae α _ m _ _ _ _ _ ((h_g_ae_m n.fst).sub (h_g_ae_m n.snd)), },
  obtain ⟨g_Lp_lim, g_tendsto⟩ := cauchy_seq_tendsto_of_complete h_cau_seq_g_Lp,
  have h_g_lim_meas_m : @measurable α _ m _ g_Lp_lim,
    from @Lp.measurable α G m p (μ.trim hm) _ _ _ _ g_Lp_lim,
  refine ⟨g_Lp_lim, h_g_lim_meas_m, _⟩,
  have h_g_lim_meas : measurable g_Lp_lim, from measurable.mono h_g_lim_meas_m hm le_rfl,
  rw tendsto_Lp_iff_tendsto_ℒp' at g_tendsto h_tendsto,
  suffices h_snorm_zero : snorm (⇑f_lim - ⇑g_Lp_lim) p μ = 0,
  { rw @snorm_eq_zero_iff α G m0 p μ _ _ _ _ _ (ennreal.zero_lt_one.trans_le hp.elim).ne.symm
      at h_snorm_zero,
    { have h_add_sub : ⇑f_lim - ⇑g_Lp_lim + ⇑g_Lp_lim =ᵐ[μ] 0 + ⇑g_Lp_lim,
        from h_snorm_zero.add eventually_eq.rfl,
      simpa using h_add_sub, },
    { exact (Lp.ae_measurable f_lim).sub h_g_lim_meas.ae_measurable, }, },
  have h_tendsto' : tendsto (λ (n : ι), snorm (g n - ⇑f_lim) p μ) at_top (𝓝 0),
  { suffices h_eq : ∀ (n : ι), snorm (g n - ⇑f_lim) p μ = snorm (⇑(f n) - ⇑f_lim) p μ,
      by { simp_rw h_eq, exact h_tendsto, },
    exact λ n, snorm_congr_ae ((hfg n).symm.sub eventually_eq.rfl), },
  have g_tendsto' : tendsto (λ (n : ι), snorm (g n - ⇑g_Lp_lim) p μ) at_top (𝓝 0),
  { suffices h_eq : ∀ (n : ι), snorm (g n - ⇑g_Lp_lim) p μ
        = @snorm α _ m _ (⇑(g_Lp n) - ⇑g_Lp_lim) p (μ.trim hm),
      by { simp_rw h_eq, exact g_tendsto, },
    intro n,
    have h_eq_g : snorm (g n - ⇑g_Lp_lim) p μ = snorm (⇑(g_Lp n) - ⇑g_Lp_lim) p μ,
      from snorm_congr_ae ((ae_eq_of_ae_eq_trim hm (h_g_ae_m n).symm).sub eventually_eq.rfl),
    rw h_eq_g,
    refine (snorm_trim hm _).symm,
    refine @measurable.sub α m _ _ _ _ (g_Lp n) g_Lp_lim _ h_g_lim_meas_m,
    exact @Lp.measurable α G m p (μ.trim hm) _ _ _ _ (g_Lp n), },
  have sub_tendsto : tendsto (λ (n : ι), snorm (⇑f_lim - ⇑g_Lp_lim) p μ) at_top (𝓝 0),
  { let snorm_add := λ (n : ι), snorm (g n - ⇑f_lim) p μ + snorm (g n - ⇑g_Lp_lim) p μ,
    have h_add_tendsto : tendsto snorm_add at_top (𝓝 0),
      by { rw ← add_zero (0 : ℝ≥0∞), exact tendsto.add h_tendsto' g_tendsto', },
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_add_tendsto
      (λ n, zero_le _) _,
    have h_add : (λ n, snorm (f_lim - g_Lp_lim) p μ)
        = λ n, snorm (f_lim - g n + (g n - g_Lp_lim)) p μ,
      by { ext1 n, congr, abel, },
    simp_rw h_add,
    refine λ n, (snorm_add_le _ _ hp.elim).trans _,
    { exact ((Lp.measurable f_lim).sub (hg_m0 n)).ae_measurable, },
    { exact ((hg_m0 n).sub h_g_lim_meas).ae_measurable, },
    refine add_le_add_right (le_of_eq _) _,
    rw [← neg_sub, snorm_neg], },
  exact tendsto_nhds_unique tendsto_const_nhds sub_tendsto,
end

lemma ae_measurable'_of_tendsto {m m0 : measurable_space α} (hm : m ≤ m0) {μ : measure α}
  {ι} [nonempty ι] [semilattice_sup ι] [hp : fact (1 ≤ p)] [complete_space G]
  (f : ι → Lp G p μ) (hf : ∀ n, ae_measurable' m (f n) μ) (f_lim : Lp G p μ)
  (h_tendsto : filter.at_top.tendsto f (𝓝 f_lim)) :
  ae_measurable' m f_lim μ :=
ae_measurable'_of_tendsto' hm f (λ n, (hf n).some) f_lim (λ n, (hf n).some_spec.2)
  (λ n, (hf n).some_spec.1) h_tendsto

lemma is_seq_closed_ae_measurable' [complete_space G] {m m0 : measurable_space α} (hm : m ≤ m0)
  {μ : measure α} [hp : fact (1 ≤ p)] :
  is_seq_closed {f : Lp G p μ | ae_measurable' m f μ} :=
is_seq_closed_of_def (λ F f F_mem F_tendsto_f, ae_measurable'_of_tendsto hm F F_mem f F_tendsto_f)

lemma is_closed_ae_measurable' [complete_space G] {m m0 : measurable_space α} (hm : m ≤ m0)
  {μ : measure α} [hp : fact (1 ≤ p)] :
  is_closed {f : Lp G p μ | ae_measurable' m f μ} :=
is_seq_closed_iff_is_closed.mp (is_seq_closed_ae_measurable' hm)

instance {m m0 : measurable_space α} [hm : fact (m ≤ m0)] {μ : measure α} [complete_space F]
  [hp : fact (1 ≤ p)] : complete_space (Lp_sub F 𝕂 m p μ) :=
is_closed.complete_space_coe (is_closed_ae_measurable' hm.elim)

end Lp_sub

section is_condexp

/-- `f` is a conditional expectation of `g` with respect to the measurable space structure `m`. -/
def is_condexp (m : measurable_space α) [m0 : measurable_space α] (f g : α → F') (μ : measure α) :
  Prop :=
ae_measurable' m f μ ∧ ∀ s (hs : @measurable_set α m s), ∫ a in s, f a ∂μ = ∫ a in s, g a ∂μ

variables {m₂ m m0 : measurable_space α} {μ : measure α} {f f₁ f₂ g g₁ g₂ : α → F'}

lemma is_condexp.refl (hf : ae_measurable' m f μ) : is_condexp m f f μ := ⟨hf, λ s hs, rfl⟩

lemma is_condexp.trans (hm2 : m₂ ≤ m) (hff₂ : is_condexp m₂ f₂ f μ) (hfg : is_condexp m f g μ)  :
  is_condexp m₂ f₂ g μ :=
⟨hff₂.1, λ s hs, (hff₂.2 s hs).trans (hfg.2 s (hm2 s hs))⟩

lemma is_condexp_congr_ae_left' (hm : m ≤ m0) (hf12 : f₁ =ᵐ[μ] f₂) (hf₁ : is_condexp m f₁ g μ) :
  is_condexp m f₂ g μ :=
begin
  rcases hf₁ with ⟨⟨f, h_meas, h_eq⟩, h_int_eq⟩,
  refine ⟨⟨f, h_meas, hf12.symm.trans h_eq⟩, λ s hs, _⟩,
  rw set_integral_congr_ae (hm s hs) (hf12.mono (λ x hx hxs, hx.symm)),
  exact h_int_eq s hs,
end

lemma is_condexp_congr_ae_left (hm : m ≤ m0) (hf12 : f₁ =ᵐ[μ] f₂) :
  is_condexp m f₁ g μ ↔ is_condexp m f₂ g μ :=
⟨λ h, is_condexp_congr_ae_left' hm hf12 h, λ h, is_condexp_congr_ae_left' hm hf12.symm h⟩

lemma is_condexp_congr_ae_right' (hm : m ≤ m0) (hg12 : g₁ =ᵐ[μ] g₂) (hf₁ : is_condexp m f g₁ μ) :
  is_condexp m f g₂ μ :=
begin
  rcases hf₁ with ⟨h_meas, h_int_eq⟩,
  refine ⟨h_meas, λ s hs, _⟩,
  rw set_integral_congr_ae (hm s hs) (hg12.mono (λ x hx hxs, hx.symm)),
  exact h_int_eq s hs,
end

lemma is_condexp_congr_ae_right (hm : m ≤ m0) (hg12 : g₁ =ᵐ[μ] g₂) :
  is_condexp m f g₁ μ ↔ is_condexp m f g₂ μ :=
⟨λ h, is_condexp_congr_ae_right' hm hg12 h, λ h, is_condexp_congr_ae_right' hm hg12.symm h⟩

lemma is_condexp_congr_ae' (hm : m ≤ m0) (hf12 : f₁ =ᵐ[μ] f₂) (hg12 : g₁ =ᵐ[μ] g₂)
  (hfg₁ : is_condexp m f₁ g₁ μ) :
  is_condexp m f₂ g₂ μ :=
is_condexp_congr_ae_left' hm hf12 (is_condexp_congr_ae_right' hm hg12 hfg₁)

lemma is_condexp_congr_ae (hm : m ≤ m0) (hf12 : f₁ =ᵐ[μ] f₂) (hg12 : g₁ =ᵐ[μ] g₂) :
  is_condexp m f₁ g₁ μ ↔ is_condexp m f₂ g₂ μ :=
⟨λ h, is_condexp_congr_ae' hm hf12 hg12 h, λ h, is_condexp_congr_ae' hm hf12.symm hg12.symm h⟩

end is_condexp

section ae_eq_of_forall_set_integral_eq
variables [measurable_space α] {μ : measure α}

lemma ae_const_le_iff_forall_lt_measure_zero (f : α → ℝ) (c : ℝ) :
  (∀ᵐ x ∂μ, c ≤ f x) ↔ ∀ b < c, μ {x | f x ≤ b} = 0 :=
begin
  rw ae_iff,
  push_neg,
  have h_Union : {x | f x < c} = ⋃ (r : ℚ) (hr : ↑r < c), {x | f x ≤ r},
  { ext1 x,
    simp_rw [set.mem_Union, set.mem_set_of_eq],
    split; intro h,
    { obtain ⟨q, lt_q, q_lt⟩ := exists_rat_btwn h, exact ⟨q, q_lt, lt_q.le⟩, },
    { obtain ⟨q, q_lt, q_le⟩ := h, exact q_le.trans_lt q_lt, }, },
  rw h_Union,
  rw measure_Union_null_iff,
  split; intros h b,
  { intro hbc,
    obtain ⟨r, hr⟩ := exists_rat_btwn hbc,
    specialize h r,
    simp only [hr.right, set.Union_pos] at h,
    refine measure_mono_null (λ x hx, _) h,
    rw set.mem_set_of_eq at hx ⊢,
    exact hx.trans hr.1.le, },
  { by_cases hbc : ↑b < c,
    { simp only [hbc, set.Union_pos],
      exact h _ hbc, },
    { simp [hbc], }, },
end

/-- Use `ae_nonneg_of_forall_set_ℝ` instead. -/
private lemma ae_nonneg_of_forall_set_ℝ_measurable [finite_measure μ] (f : α → ℝ)
  (hf : integrable f μ) (hfm : measurable f)
  (hf_zero : ∀ s : set α, measurable_set s → 0 ≤ ∫ x in s, f x ∂μ) :
  0 ≤ᵐ[μ] f :=
begin
  simp_rw [eventually_le, pi.zero_apply],
  rw ae_const_le_iff_forall_lt_measure_zero,
  intros b hb_neg,
  let s := {x | f x ≤ b},
  have hs : measurable_set s, from measurable_set_le hfm measurable_const,
  have hfs : ∀ x ∈ s, f x ≤ b, from λ x hxs, hxs,
  have h_int_gt : μ s ≠ 0 → ∫ x in s, f x ∂μ ≤ b * (μ s).to_real,
  { intro h_ne_zero,
    have h_const_le : ∫ x in s, f x ∂μ ≤ ∫ x in s, b ∂μ,
    { refine set_integral_mono_ae_restrict hf.integrable_on
        (integrable_on_const.mpr (or.inr (measure_lt_top _ _))) _,
      rw [eventually_le, ae_restrict_iff hs],
      exact eventually_of_forall hfs, },
    rwa [set_integral_const, smul_eq_mul, mul_comm] at h_const_le, },
  by_contra,
  refine (lt_self_iff_false (∫ x in s, f x ∂μ)).mp ((h_int_gt h).trans_lt _),
  refine (mul_neg_iff.mpr (or.inr ⟨hb_neg, _⟩)).trans_le (hf_zero s hs),
  refine (ennreal.to_real_nonneg).lt_of_ne (λ h_eq, h _),
  cases (ennreal.to_real_eq_zero_iff _).mp h_eq.symm with hμs_to_real hμs_to_real,
  { exact hμs_to_real, },
  { exact absurd hμs_to_real (measure_ne_top _ _), },
end

lemma ae_nonneg_of_forall_set_ℝ [finite_measure μ] (f : α → ℝ) (hf : integrable f μ)
  (hf_zero : ∀ s : set α, measurable_set s → 0 ≤ ∫ x in s, f x ∂μ) :
  0 ≤ᵐ[μ] f :=
begin
  rcases hf with ⟨⟨f', hf'_meas, hf_ae⟩, hf_finite_int⟩,
  have hf'_integrable : integrable f' μ,
    from integrable.congr ⟨⟨f', hf'_meas, hf_ae⟩, hf_finite_int⟩ hf_ae,
  have hf'_zero : ∀ (s : set α), measurable_set s → 0 ≤ ∫ (x : α) in s, f' x ∂μ,
  { intros s hs,
    rw set_integral_congr_ae hs (hf_ae.mono (λ x hx hxs, hx.symm)),
    exact hf_zero s hs, },
  exact (ae_nonneg_of_forall_set_ℝ_measurable f' hf'_integrable hf'_meas hf'_zero).trans
    hf_ae.symm.le,
end

lemma ae_eq_zero_of_forall_set_ℝ [finite_measure μ] (f : α → ℝ) (hf : integrable f μ)
  (hf_zero : ∀ s : set α, measurable_set s → ∫ x in s, f x ∂μ = 0) :
  f =ᵐ[μ] 0 :=
begin
  have hf_nonneg :  ∀ s : set α, measurable_set s → 0 ≤ ∫ x in s, f x ∂μ,
    from λ s hs, (hf_zero s hs).symm.le,
  suffices h_and : f ≤ᵐ[μ] 0 ∧ 0 ≤ᵐ[μ] f,
  { refine h_and.1.mp (h_and.2.mono (λ x hx1 hx2, _)),
    exact le_antisymm hx2 hx1, },
  refine ⟨_, ae_nonneg_of_forall_set_ℝ f hf hf_nonneg⟩,
  suffices h_neg : 0 ≤ᵐ[μ] -f,
  { refine h_neg.mono (λ x hx, _),
    rw pi.neg_apply at hx,
    refine le_of_neg_le_neg _,
    simpa using hx, },
  have hf_neg : integrable (-f) μ, from hf.neg,
  have hf_nonneg_neg :  ∀ (s : set α), measurable_set s → 0 ≤ ∫ (x : α) in s, (-f) x ∂μ,
  { intros s hs,
    simp_rw pi.neg_apply,
    rw [integral_neg, neg_nonneg],
    exact (hf_zero s hs).le, },
  exact ae_nonneg_of_forall_set_ℝ (-f) hf_neg hf_nonneg_neg,
end

lemma forall_inner_eq_zero_iff [inner_product_space 𝕜 γ] (x : γ) :
  (∀ c : γ, inner c x = (0 : 𝕜)) ↔ x = 0 :=
⟨λ hx, inner_self_eq_zero.mp (hx x), λ hx, by simp [hx]⟩

lemma ae_eq_zero_of_forall_inner_ae_eq_zero [inner_product_space 𝕜 γ] [second_countable_topology γ]
  (μ : measure α) (f : α → γ) (hf : ∀ c : γ, ∀ᵐ x ∂μ, inner c (f x) = (0 : 𝕜)) :
  f =ᵐ[μ] 0 :=
begin
  let s := dense_seq γ,
  have hs : dense_range s := dense_range_dense_seq γ,
  have hfs : ∀ n : ℕ, ∀ᵐ x ∂μ, inner (s n) (f x) = (0 : 𝕜),
  { exact λ n, hf (s n), },
  have hf' : ∀ᵐ x ∂μ, ∀ n : ℕ, inner (s n) (f x) = (0 : 𝕜),
  { rwa ae_all_iff, },
  refine hf'.mono (λ x hx, _),
  rw pi.zero_apply,
  rw ← inner_self_eq_zero,
  have h_closed : is_closed {c : γ | inner c (f x) = (0 : 𝕜)},
  { refine is_closed_eq _ continuous_const,
    exact continuous.inner continuous_id continuous_const, },
  exact @is_closed_property ℕ γ _ s (λ c, inner c (f x) = (0 : 𝕜)) hs h_closed (λ n, hx n) _,
end

lemma ae_measurable.re [opens_measurable_space 𝕂] {f : α → 𝕂} (hf : ae_measurable f μ) :
  ae_measurable (λ x, is_R_or_C.re (f x)) μ :=
measurable.comp_ae_measurable is_R_or_C.continuous_re.measurable hf

lemma ae_measurable.im [opens_measurable_space 𝕂] {f : α → 𝕂} (hf : ae_measurable f μ) :
  ae_measurable (λ x, is_R_or_C.im (f x)) μ :=
measurable.comp_ae_measurable is_R_or_C.continuous_im.measurable hf

lemma integrable.re [opens_measurable_space 𝕂] {f : α → 𝕂} (hf : integrable f μ) :
  integrable (λ x, is_R_or_C.re (f x)) μ :=
begin
  have h_norm_le : ∀ a, ∥is_R_or_C.re (f a)∥ ≤ ∥f a∥,
  { intro a,
    rw [is_R_or_C.norm_eq_abs, is_R_or_C.norm_eq_abs, is_R_or_C.abs_to_real],
    exact is_R_or_C.abs_re_le_abs _, },
  exact integrable.mono hf (ae_measurable.re hf.1) (eventually_of_forall h_norm_le),
end

lemma integrable.im [opens_measurable_space 𝕂] {f : α → 𝕂} (hf : integrable f μ) :
  integrable (λ x, is_R_or_C.im (f x)) μ :=
begin
  have h_norm_le : ∀ a, ∥is_R_or_C.im (f a)∥ ≤ ∥f a∥,
  { intro a,
    rw [is_R_or_C.norm_eq_abs, is_R_or_C.norm_eq_abs, is_R_or_C.abs_to_real],
    exact is_R_or_C.abs_im_le_abs _, },
  exact integrable.mono hf (ae_measurable.im hf.1) (eventually_of_forall h_norm_le),
end

lemma integrable.const_inner [borel_space 𝕂] {f : α → E} (hf : integrable f μ) (c : E) :
  integrable (λ x, (inner c (f x) : 𝕂)) μ :=
begin
  have hf_const_mul : integrable (λ x, ∥c∥ * ∥f x∥) μ, from integrable.const_mul hf.norm (∥c∥),
  refine integrable.mono hf_const_mul (ae_measurable.inner ae_measurable_const hf.1) _,
  refine eventually_of_forall (λ x, _),
  rw is_R_or_C.norm_eq_abs,
  refine (abs_inner_le_norm _ _).trans _,
  simp,
end

lemma integral_const_inner [borel_space 𝕂] {f : α → E'} (hf : integrable f μ) (c : E') :
  ∫ x, (inner c (f x) : 𝕂) ∂μ = inner c (∫ x, f x ∂μ) :=
@continuous_linear_map.integral_comp_comm α E' 𝕂 _ _ _ μ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  (inner_right c) _ hf

lemma ae_eq_zero_of_forall_set [borel_space 𝕂] [finite_measure μ] (f : α → E') (hf : integrable f μ)
  (hf_zero : ∀ s : set α, measurable_set s → ∫ x in s, f x ∂μ = 0) :
  f =ᵐ[μ] 0 :=
begin
  refine ae_eq_zero_of_forall_inner_ae_eq_zero μ f (λ c, _),
  suffices h_re_im : (∀ᵐ (x : α) ∂μ, is_R_or_C.re (inner c (f x) : 𝕂) = 0)
    ∧ ∀ᵐ (x : α) ∂μ, is_R_or_C.im (inner c (f x) : 𝕂) = 0,
  { rw ← eventually_and at h_re_im,
    refine h_re_im.mono (λ x hx, _),
    rw is_R_or_C.ext_iff,
    simpa using hx, },
  have hf_inner_re : integrable (λ x, is_R_or_C.re (inner c (f x) : 𝕂)) μ,
    from integrable.re (integrable.const_inner hf c),
  have hf_inner_im : integrable (λ x, is_R_or_C.im (inner c (f x) : 𝕂)) μ,
    from integrable.im (integrable.const_inner hf c),
  have hf_zero_inner : ∀ s, measurable_set s → ∫ (x : α) in s, (inner c (f x) : 𝕂) ∂μ = 0,
  { intros s hs,
    rw integral_const_inner hf.integrable_on c,
    simp [hf_zero s hs], },
  have hf_zero_inner_re : ∀ s, measurable_set s → ∫ x in s, is_R_or_C.re (inner c (f x) : 𝕂) ∂μ = 0,
  { intros s hs,
    rw integral_re (integrable.const_inner hf c).integrable_on,
    rw hf_zero_inner s hs,
    simp, },
  have hf_zero_inner_im : ∀ s, measurable_set s → ∫ x in s, is_R_or_C.im (inner c (f x) : 𝕂) ∂μ = 0,
  { intros s hs,
    rw integral_im (integrable.const_inner hf c).integrable_on,
    rw hf_zero_inner s hs,
    simp, },
  exact ⟨ae_eq_zero_of_forall_set_ℝ _ hf_inner_re hf_zero_inner_re,
    ae_eq_zero_of_forall_set_ℝ _ hf_inner_im hf_zero_inner_im⟩,
end

lemma ae_eq_of_forall_set_integral_eq [borel_space 𝕂] [finite_measure μ]
  (f g : α → E') (hf : integrable f μ) (hg : integrable g μ)
  (hfg : ∀ s : set α, measurable_set s → ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ) :
  f =ᵐ[μ] g :=
begin
  suffices h_sub : f-g =ᵐ[μ] 0,
    by { refine h_sub.mono (λ x hx, _), rwa [pi.sub_apply, pi.zero_apply, sub_eq_zero] at hx, },
  have hfg' : ∀ s : set α, measurable_set s → ∫ x in s, (f - g) x ∂μ = 0,
  { intros s hs,
    rw integral_sub' hf.integrable_on hg.integrable_on,
    exact sub_eq_zero.mpr (hfg s hs), },
  exact ae_eq_zero_of_forall_set (f-g) (hf.sub hg) hfg',
end

end ae_eq_of_forall_set_integral_eq

section integral_trim

variables {m m0 : measurable_space α} {μ : measure α}

lemma integrable_trim_of_measurable (hm : m ≤ m0) [opens_measurable_space H] {f : α → H}
  (hf : @measurable _ _ m _ f) (hf_int : integrable f μ) :
  @integrable _ _ m _ _ f (μ.trim hm) :=
begin
  refine ⟨@measurable.ae_measurable α _ m _ f (μ.trim hm) hf, _⟩,
  rw [has_finite_integral, lintegral_trim hm _],
  { exact hf_int.2, },
  { exact @measurable.ennreal_coe α m _ (@measurable.nnnorm _ α _ _ _ m _ hf), },
end

lemma ae_measurable_of_ae_measurable_trim (hm : m ≤ m0) {f : α → β}
  (hf : @ae_measurable _ _ m _ f (μ.trim hm)) :
  ae_measurable f μ :=
begin
  let f' := @ae_measurable.mk _ _ m _ _ _ hf,
  have hf'_meas : @measurable _ _ m _ f', from @ae_measurable.measurable_mk _ _ m _ _ _ hf,
  have hff'_m : eventually_eq (@measure.ae  _ m (μ.trim hm)) f' f,
    from (@ae_measurable.ae_eq_mk _ _ m _ _ _ hf).symm,
  have hff' : f' =ᵐ[μ] f, from ae_eq_of_ae_eq_trim hm hff'_m,
  exact ⟨f', measurable.mono hf'_meas hm le_rfl, hff'.symm⟩,
end

lemma integrable_of_integrable_trim (hm : m ≤ m0) [opens_measurable_space H]
  {f : α → H} (hf_int : @integrable α H m _ _ f (μ.trim hm)) :
  integrable f μ :=
begin
  obtain ⟨hf_meas_ae, hf⟩ := hf_int,
  refine ⟨ae_measurable_of_ae_measurable_trim hm hf_meas_ae, _⟩,
  rw has_finite_integral at hf ⊢,
  rwa lintegral_trim_ae hm _ at hf,
  exact @ae_measurable.ennreal_coe α m _ _ (@ae_measurable.nnnorm H α _ _ _ m _ _ hf_meas_ae),
end

/-- Simple function seen as simple function of a larger measurable_space. -/
def simple_func_larger_space (hm : m ≤ m0) (f : @simple_func α m γ) : simple_func α γ :=
⟨@simple_func.to_fun α m γ f, λ x, hm _ (@simple_func.measurable_set_fiber α γ m f x),
  @simple_func.finite_range α γ m f⟩

lemma simple_func_larger_space_eq (hm : m ≤ m0) (f : @simple_func α m γ) :
  ⇑(simple_func_larger_space hm f) = f :=
rfl

lemma integral_simple_func' [measurable_space α] {μ : measure α} (f : simple_func α G')
  (hf_int : integrable f μ) :
  ∫ x, f x ∂μ = ∑ x in f.range, (ennreal.to_real (μ (f ⁻¹' {x}))) • x :=
begin
  rw [← simple_func.integral, integral_eq f hf_int, ← L1.simple_func.to_L1_eq_to_L1,
    L1.simple_func.integral_L1_eq_integral, L1.simple_func.integral_eq_integral],
  refine simple_func.integral_congr _ (L1.simple_func.to_simple_func_to_L1 _ _),
  exact L1.simple_func.integrable _,
end

lemma integral_simple_func (hm : m ≤ m0) (f : @simple_func α m G') (hf_int : integrable f μ) :
  ∫ x, f x ∂μ = ∑ x in (@simple_func.range α G' m f), (ennreal.to_real (μ (f ⁻¹' {x}))) • x :=
begin
  let f0 := simple_func_larger_space hm f,
  simp_rw ← simple_func_larger_space_eq hm f,
  have hf0_int : integrable f0 μ, by rwa simple_func_larger_space_eq,
  rw integral_simple_func' _ hf0_int,
  congr,
end

lemma integral_trim_simple_func (hm : m ≤ m0) (f : @simple_func α m G') (hf_int : integrable f μ) :
  ∫ x, f x ∂μ = @integral α G' m _ _ _ _ _ _ (μ.trim hm) f :=
begin
  have hf : @measurable _ _ m _ f, from @simple_func.measurable α G' m _ f,
  have hf_int_m := integrable_trim_of_measurable hm hf hf_int,
  rw [integral_simple_func le_rfl f hf_int_m, integral_simple_func hm f hf_int],
  congr,
  ext1 x,
  congr,
  exact (trim_measurable hm (@simple_func.measurable_set_fiber α G' m f x)).symm,
end

lemma integral_trim (hm : m ≤ m0) (f : α → G') (hf : @measurable α G' m _ f)
  (hf_int : integrable f μ) :
  ∫ x, f x ∂μ = @integral α G' m _ _ _ _ _ _ (μ.trim hm) f :=
begin
  let F := @simple_func.approx_on G' α _ _ _ m _ hf set.univ 0 (set.mem_univ 0) _,
  have hF_meas : ∀ n, @measurable _ _ m _ (F n), from λ n, @simple_func.measurable α G' m _ (F n),
  have hF_int : ∀ n, integrable (F n) μ,
    from simple_func.integrable_approx_on_univ (hf.mono hm le_rfl) hf_int,
  have hF_int_m : ∀ n, @integrable α G' m _ _ (F n) (μ.trim hm),
    from λ n, integrable_trim_of_measurable hm (hF_meas n) (hF_int n),
  have hF_eq : ∀ n, ∫ x, F n x ∂μ = @integral α G' m _ _ _ _ _ _ (μ.trim hm) (F n),
    from λ n, integral_trim_simple_func hm (F n) (hF_int n),
  have h_lim_1 : at_top.tendsto (λ n, ∫ x, F n x ∂μ) (𝓝 (∫ x, f x ∂μ)),
  { refine tendsto_integral_of_L1 f hf_int (eventually_of_forall hF_int) _,
    exact simple_func.tendsto_approx_on_univ_L1_edist (hf.mono hm le_rfl) hf_int, },
  have h_lim_2 :  at_top.tendsto (λ n, ∫ x, F n x ∂μ)
    (𝓝 (@integral α G' m _ _ _ _ _ _ (μ.trim hm) f)),
  { simp_rw hF_eq,
    refine @tendsto_integral_of_L1 α G' m _ _ _ _ _ _ (μ.trim hm) _ f
      (integrable_trim_of_measurable hm hf hf_int) _ _ (eventually_of_forall hF_int_m) _,
    exact @simple_func.tendsto_approx_on_univ_L1_edist α G' m _ _ _ _ f _ hf
      (integrable_trim_of_measurable hm hf hf_int), },
  exact tendsto_nhds_unique h_lim_1 h_lim_2,
end

lemma set_integral_trim (hm : m ≤ m0) (f : α → G') (hf : @measurable _ _ m _ f)
  (hf_int : integrable f μ) {s : set α} (hs : @measurable_set α m s) :
  ∫ x in s, f x ∂μ = @integral α G' m _ _ _ _ _ _ (@measure.restrict _ m (μ.trim hm) s) f :=
by rwa [integral_trim hm f hf (hf_int.restrict s), trim_restrict hm μ]

lemma ae_eq_trim_of_measurable [add_group β] [measurable_singleton_class β] [has_measurable_sub₂ β]
  (hm : m ≤ m0) {f g : α → β} (hf : @measurable _ _ m _ f) (hg : @measurable _ _ m _ g)
  (hfg : f =ᵐ[μ] g) :
  f =ᶠ[@measure.ae α m (μ.trim hm)] g :=
begin
  rwa [eventually_eq, ae_iff, trim_measurable hm _],
  exact (@measurable_set.compl α _ m (@measurable_set_eq_fun α m β _ _ _ _ _ _ hf hg)),
end

lemma ae_eq_trim_iff [add_group β] [measurable_singleton_class β] [has_measurable_sub₂ β]
  (hm : m ≤ m0) {f g : α → β} (hf : @measurable _ _ m _ f) (hg : @measurable _ _ m _ g) :
  f =ᶠ[@measure.ae α m (μ.trim hm)] g ↔ f =ᵐ[μ] g :=
⟨ae_eq_of_ae_eq_trim hm, ae_eq_trim_of_measurable hm hf hg⟩

instance finite_measure_trim (hm : m ≤ m0) [finite_measure μ] : @finite_measure α m (μ.trim hm) :=
{ measure_univ_lt_top :=
    by { rw trim_measurable hm (@measurable_set.univ _ m), exact measure_lt_top _ _, } }

end integral_trim

variables (𝕂)
lemma is_condexp_unique {m m0 : measurable_space α} (hm : m ≤ m0) {μ : measure α} [finite_measure μ]
  [borel_space 𝕂] {f₁ f₂ g : α → E'} (hf₁ : is_condexp m f₁ g μ)
  (h_int₁ : integrable f₁ μ) (hf₂ : is_condexp m f₂ g μ) (h_int₂ : integrable f₂ μ):
  f₁ =ᵐ[μ] f₂ :=
begin
  rcases hf₁ with ⟨⟨f₁', h_meas₁, hff'₁⟩, h_int_eq₁⟩,
  rcases hf₂ with ⟨⟨f₂', h_meas₂, hff'₂⟩, h_int_eq₂⟩,
  refine hff'₁.trans (eventually_eq.trans _ hff'₂.symm),
  have h : ∀ s : set α, @measurable_set α m s → ∫ x in s, f₁' x ∂μ = ∫ x in s, f₂' x ∂μ,
  { intros s hsm,
    have h₁ : ∫ x in s, f₁' x ∂μ = ∫ x in s, g x ∂μ,
    { rw ← h_int_eq₁ s hsm,
      exact set_integral_congr_ae (hm s hsm) (hff'₁.mono (λ x hx hxs, hx.symm)), },
    rw [h₁, ← h_int_eq₂ s hsm],
    exact set_integral_congr_ae (hm s hsm) (hff'₂.mono (λ x hx hxs, hx)), },
  refine ae_eq_of_ae_eq_trim hm _,
  have h_int₁' : integrable f₁' μ, from (integrable_congr hff'₁).mp h_int₁,
  have h_int₂' : integrable f₂' μ, from (integrable_congr hff'₂).mp h_int₂,
  refine @ae_eq_of_forall_set_integral_eq α E' 𝕂 _ _ _ _ _ _ _ _ _ m _ _ _ _ _ _ _ _,
  { exact integrable_trim_of_measurable hm h_meas₁ h_int₁', },
  { exact integrable_trim_of_measurable hm h_meas₂ h_int₂', },
  { intros s hs,
    specialize h s hs,
    rw integral_trim hm _ h_meas₁ h_int₁'.integrable_on at h,
    rw integral_trim hm _ h_meas₂ h_int₂'.integrable_on at h,
    rwa ← trim_restrict hm μ hs at h, },
end

/-- Conditional expectation of a function in L2 with respect to a sigma-algebra -/
def condexp_L2_clm [borel_space 𝕂] [complete_space E]
  {m m0 : measurable_space α} (hm : m ≤ m0) {μ : measure α} :
  (α →₂[μ] E) →L[𝕂] (Lp_sub E 𝕂 m 2 μ) :=
begin
  haveI : fact (m ≤ m0) := ⟨hm⟩,
  exact orthogonal_projection (Lp_sub E 𝕂 m 2 μ),
end
variables {𝕂}

lemma mem_Lp_sub_indicator_Lp [opens_measurable_space 𝕂] {m m0 : measurable_space α} (hm : m ≤ m0)
  {μ : measure α} {s : set α} (hs : @measurable_set α m s) {hμs : μ s < ∞} {c : F} :
  indicator_Lp p (hm s hs) hμs c ∈ Lp_sub F 𝕂 m p μ :=
begin
  refine ⟨s.indicator (λ x : α, c), _, indicator_Lp_coe_fn (hm s hs) hμs c⟩,
  exact @measurable.indicator α _ m _ _ s (λ x, c) (@measurable_const _ α _ m _) hs,
end

lemma ennreal.one_le_two : (1 : ℝ≥0∞) ≤ 2 := ennreal.coe_le_coe.2 (show (1 : ℝ≥0) ≤ 2, by norm_num)

lemma is_condexp_condexp_L2 [borel_space 𝕂] {m m0 : measurable_space α} (hm : m ≤ m0)
  {μ : measure α} [finite_measure μ] (f : Lp E' 2 μ) :
  is_condexp m ((condexp_L2_clm 𝕂 hm f) : α → E') f μ :=
begin
  haveI : fact (m ≤ m0) := ⟨hm⟩,
  refine ⟨Lp_sub.ae_measurable' (condexp_L2_clm 𝕂 hm f), λ s hs, _⟩,
  have h_inner_zero : ∀ (g : Lp E' 2 μ) (hg : g ∈ Lp_sub E' 𝕂 m 2 μ),
      inner (f - condexp_L2_clm 𝕂 hm f) g = (0 : 𝕂),
    from λ g hg, orthogonal_projection_inner_eq_zero f g hg,
  suffices h_sub : ∫ a in s, (f a - condexp_L2_clm 𝕂 hm f a) ∂μ = 0,
  { rw integral_sub at h_sub,
    { rw sub_eq_zero at h_sub,
      exact h_sub.symm, },
    { exact (Lp.integrable f ennreal.one_le_two).restrict s, },
    { exact integrable.restrict (Lp.integrable (condexp_L2_clm 𝕂 hm f)ennreal.one_le_two) s,}, },
  refine integral_zero_of_forall_integral_inner_zero _ _ _,
  { refine (integrable.sub (Lp.integrable f ennreal.one_le_two) _).restrict s,
    exact Lp.integrable (condexp_L2_clm 𝕂 hm f) ennreal.one_le_two, },
  { intro c,
    specialize h_inner_zero (indicator_Lp 2 (hm s hs) (measure_lt_top μ s) c)
      (mem_Lp_sub_indicator_Lp hm hs),
    rw [inner_eq_zero_sym, inner_indicator_Lp] at h_inner_zero,
    rw ← h_inner_zero,
    refine set_integral_congr_ae (hm s hs) _,
    refine (Lp.coe_fn_sub f (condexp_L2_clm 𝕂 hm f)).mono (λ x hx hxs, _),
    congr,
    rw [hx, pi.sub_apply, Lp_sub_coe], },
end

section coe_linear_maps

variables [measurable_space α] {μ : measure α}

lemma L1s_to_L2_add (f g : α →₁ₛ[μ] G) :
  (mem_ℒ2_simple_func_L1 (f+g)).to_Lp ⇑(f+g)
    = (mem_ℒ2_simple_func_L1 f).to_Lp f + (mem_ℒ2_simple_func_L1 g).to_Lp g :=
begin
  ext1,
  refine (mem_ℒp.coe_fn_to_Lp _).trans (eventually_eq.trans _ (Lp.coe_fn_add _ _).symm),
  refine (Lp.coe_fn_add _ _).trans _,
  have hf : f.val =ᵐ[μ] mem_ℒp.to_Lp f (mem_ℒ2_simple_func_L1 f),
  { refine eventually_eq.trans _ (mem_ℒp.coe_fn_to_Lp _).symm,
    simp only [L1.simple_func.coe_coe, subtype.val_eq_coe], },
  have hg : g.val =ᵐ[μ] mem_ℒp.to_Lp g (mem_ℒ2_simple_func_L1 g),
  { refine eventually_eq.trans _ (mem_ℒp.coe_fn_to_Lp _).symm,
    simp only [L1.simple_func.coe_coe, subtype.val_eq_coe], },
  exact hf.add hg,
end

lemma L1s_to_L2_smul [opens_measurable_space 𝕂] (c : 𝕂) (f : α →₁ₛ[μ] E) :
  mem_ℒp.to_Lp ⇑(@has_scalar.smul _ _ L1.simple_func.has_scalar c f)
      (mem_ℒ2_simple_func_L1 (@has_scalar.smul _ _ L1.simple_func.has_scalar c f))
    = c • (mem_ℒp.to_Lp f (mem_ℒ2_simple_func_L1 f)) :=
begin
  ext1,
  refine (mem_ℒp.coe_fn_to_Lp _).trans (eventually_eq.trans _ (Lp.coe_fn_smul _ _).symm),
  refine (Lp.coe_fn_smul _ _).trans _,
  suffices h : ⇑(f : Lp E 1 μ) =ᵐ[μ] (mem_ℒp.to_Lp ⇑f _),
    from eventually_eq.fun_comp h (λ x : E, c • x),
  refine eventually_eq.trans _ (mem_ℒp.coe_fn_to_Lp _).symm,
  simp,
end

/-- Linear map coercing a simple function of L1 to L2. -/
def L1s_to_L2_lm [opens_measurable_space 𝕂] : (α →₁ₛ[μ] E) →ₗ[𝕂] (α →₂[μ] E) :=
{ to_fun := λ f, mem_ℒp.to_Lp f (mem_ℒ2_simple_func_L1 f),
  map_add' := L1s_to_L2_add,
  map_smul' := L1s_to_L2_smul, }

lemma L1s_to_L2_coe_fn [opens_measurable_space 𝕂] (f : α →₁ₛ[μ] E) : L1s_to_L2_lm f =ᵐ[μ] f :=
mem_ℒp.coe_fn_to_Lp _

lemma L2_integrable_to_L1_add (f g : α →₂[μ] G) (hf : integrable f μ) (hg : integrable g μ) :
  ((mem_ℒp_congr_ae (Lp.coe_fn_add _ _)).mpr
      (mem_ℒp_one_iff_integrable.mpr (hf.add hg))).to_Lp ⇑(f+g)
    = (mem_ℒp_one_iff_integrable.mpr hf).to_Lp f + (mem_ℒp_one_iff_integrable.mpr hg).to_Lp g :=
begin
  ext1,
  refine (mem_ℒp.coe_fn_to_Lp _).trans (eventually_eq.trans _ (Lp.coe_fn_add _ _).symm),
  refine (Lp.coe_fn_add _ _).trans _,
  have hf : ⇑f =ᵐ[μ] mem_ℒp.to_Lp f (mem_ℒp_one_iff_integrable.mpr hf),
    from (mem_ℒp.coe_fn_to_Lp _).symm,
  have hg : g.val =ᵐ[μ] mem_ℒp.to_Lp g (mem_ℒp_one_iff_integrable.mpr hg),
    from (mem_ℒp.coe_fn_to_Lp _).symm,
  exact hf.add hg,
end

lemma L2_integrable_to_L1_smul [opens_measurable_space 𝕂] (c : 𝕂) (f : α →₂[μ] E)
  (hf : integrable f μ) :
  ((mem_ℒp_congr_ae (Lp.coe_fn_smul c _)).mpr
    (mem_ℒp_one_iff_integrable.mpr (hf.smul c))).to_Lp ⇑(c • f)
    = c • ((mem_ℒp_one_iff_integrable.mpr hf).to_Lp f) :=
begin
  ext1,
  refine (mem_ℒp.coe_fn_to_Lp _).trans (eventually_eq.trans _ (Lp.coe_fn_smul _ _).symm),
  refine (Lp.coe_fn_smul _ _).trans _,
  suffices h : ⇑f =ᵐ[μ] (mem_ℒp.to_Lp ⇑f _), from eventually_eq.fun_comp h (λ x : E, c • x),
  exact (mem_ℒp.coe_fn_to_Lp _).symm,
end

variables (𝕂 F μ)
def L2_integrable [opens_measurable_space 𝕂] : submodule 𝕂 (α →₂[μ] F) :=
{ carrier := {f | integrable f μ},
  zero_mem' := (integrable_congr (Lp.coe_fn_zero _ _ _).symm).mp (integrable_zero _ _ _),
  add_mem' := λ f g hf hg, (integrable_congr (Lp.coe_fn_add _ _).symm).mp (hf.add hg),
  smul_mem' := λ c f hf, (integrable_congr (Lp.coe_fn_smul _ _).symm).mp (hf.smul c), }
variables {𝕂 F μ}

lemma dist_L2_integrable [opens_measurable_space 𝕂] (f g : L2_integrable F 𝕂 μ) :
  dist f g = dist (f : α →₂[μ] F) (g : α →₂[μ] F) :=
rfl

lemma mem_L2_integrable_iff_integrable [opens_measurable_space 𝕂] {f : α →₂[μ] F} :
  f ∈ L2_integrable F 𝕂 μ ↔ integrable f μ :=
by simp_rw [← set_like.mem_coe, ← submodule.mem_carrier, L2_integrable, set.mem_set_of_eq]


lemma L2_integrable.integrable [opens_measurable_space 𝕂] (f : L2_integrable F 𝕂 μ) :
  integrable f μ :=
mem_L2_integrable_iff_integrable.mp f.mem

/-- Linear map sending an integrable function of L2 to L1. -/
def L2_integrable_to_L1_lm [opens_measurable_space 𝕂] : (L2_integrable E 𝕂 μ) →ₗ[𝕂] (α →₁[μ] E) :=
{ to_fun    := λ f, (mem_ℒp_one_iff_integrable.mpr (L2_integrable.integrable f)).to_Lp f,
  map_add'  := λ f g, L2_integrable_to_L1_add f g (L2_integrable.integrable f)
    (L2_integrable.integrable g),
  map_smul' := λ c f, L2_integrable_to_L1_smul c f (L2_integrable.integrable f), }

variables [finite_measure μ]

lemma L2_to_L1_add (f g : α →₂[μ] G) :
  (mem_ℒp.mem_ℒp_of_exponent_le (Lp.mem_ℒp (f+g)) ennreal.one_le_two).to_Lp ⇑(f+g)
    = (mem_ℒp.mem_ℒp_of_exponent_le (Lp.mem_ℒp f) ennreal.one_le_two).to_Lp f
      + (mem_ℒp.mem_ℒp_of_exponent_le (Lp.mem_ℒp g) ennreal.one_le_two).to_Lp g :=
begin
  ext1,
  refine (mem_ℒp.coe_fn_to_Lp _).trans (eventually_eq.trans _ (Lp.coe_fn_add _ _).symm),
  refine (Lp.coe_fn_add _ _).trans _,
  have hf : ⇑f =ᵐ[μ] mem_ℒp.to_Lp f
    (mem_ℒp.mem_ℒp_of_exponent_le (Lp.mem_ℒp f) ennreal.one_le_two),
  { exact (mem_ℒp.coe_fn_to_Lp _).symm, },
  have hg : g.val =ᵐ[μ] mem_ℒp.to_Lp g
    (mem_ℒp.mem_ℒp_of_exponent_le (Lp.mem_ℒp g) ennreal.one_le_two),
  { exact (mem_ℒp.coe_fn_to_Lp _).symm, },
  exact hf.add hg,
end

lemma L2_to_L1_smul [borel_space 𝕂] (c : 𝕂) (f : α →₂[μ] E) :
  (mem_ℒp.mem_ℒp_of_exponent_le (Lp.mem_ℒp (c • f)) ennreal.one_le_two).to_Lp ⇑(c • f)
    = c • ((mem_ℒp.mem_ℒp_of_exponent_le (Lp.mem_ℒp f) ennreal.one_le_two).to_Lp f) :=
begin
  ext1,
  refine (mem_ℒp.coe_fn_to_Lp _).trans (eventually_eq.trans _ (Lp.coe_fn_smul _ _).symm),
  refine (Lp.coe_fn_smul _ _).trans _,
  suffices h : ⇑f =ᵐ[μ] (mem_ℒp.to_Lp ⇑f _), from eventually_eq.fun_comp h (λ x : E, c • x),
  exact (mem_ℒp.coe_fn_to_Lp _).symm,
end

lemma continuous_L2_to_L1 : continuous (λ (f : α →₂[μ] G),
    (mem_ℒp.mem_ℒp_of_exponent_le (Lp.mem_ℒp f) ennreal.one_le_two).to_Lp f) :=
begin
  rw metric.continuous_iff,
  intros f ε hε_pos,
  simp_rw dist_def,
  by_cases hμ0 : μ = 0,
  { simp only [hμ0, exists_prop, forall_const, gt_iff_lt, ennreal.zero_to_real, snorm_measure_zero],
    exact ⟨ε, hε_pos, λ h, h⟩, },
  have h_univ_pow_pos : 0 < (μ set.univ ^ (1/(2 : ℝ))).to_real,
  { refine ennreal.to_real_pos_iff.mpr ⟨_, _⟩,
    { have hμ_univ_pos : 0 < μ set.univ,
      { refine lt_of_le_of_ne (zero_le _) (ne.symm _),
        rwa [ne.def, measure_theory.measure.measure_univ_eq_zero], },
      exact ennreal.rpow_pos hμ_univ_pos (measure_ne_top μ set.univ), },
    { refine ennreal.rpow_ne_top_of_nonneg _ (measure_ne_top μ set.univ),
      simp [zero_le_one], }, },
  refine ⟨ε / (μ set.univ ^ (1/(2 : ℝ))).to_real, div_pos hε_pos h_univ_pow_pos, λ g hfg, _⟩,
  rw lt_div_iff h_univ_pow_pos at hfg,
  refine lt_of_le_of_lt _ hfg,
  rw ← ennreal.to_real_mul,
  rw ennreal.to_real_le_to_real _ _,
  swap, { rw snorm_congr_ae (Lp.coe_fn_sub _ _).symm, exact Lp.snorm_ne_top _, },
  swap, { rw snorm_congr_ae (Lp.coe_fn_sub _ _).symm,
    refine ennreal.mul_ne_top _ _,
    exact Lp.snorm_ne_top _,
    refine ennreal.rpow_ne_top_of_nonneg _ _,
    simp [zero_le_one],
    exact measure_ne_top μ set.univ, },
  refine (le_of_eq _).trans ((snorm_le_snorm_mul_rpow_measure_univ (ennreal.one_le_two)
    ((Lp.ae_measurable g).sub (Lp.ae_measurable f))).trans (le_of_eq _)),
  { refine snorm_congr_ae _,
    exact eventually_eq.sub
      ((Lp.mem_ℒp g).mem_ℒp_of_exponent_le ennreal.one_le_two).coe_fn_to_Lp
      ((Lp.mem_ℒp f).mem_ℒp_of_exponent_le ennreal.one_le_two).coe_fn_to_Lp, },
  { congr,
    simp only [ennreal.one_to_real, ennreal.to_real_bit0, div_one],
    norm_num, },
end

/-- Continuous linear map sending a function of L2 to L1. -/
def L2_to_L1_clm [borel_space 𝕂] : (α →₂[μ] E) →L[𝕂] (α →₁[μ] E) :=
{ to_fun    := λ f, (mem_ℒp.mem_ℒp_of_exponent_le (Lp.mem_ℒp f) ennreal.one_le_two).to_Lp f,
  map_add'  := L2_to_L1_add,
  map_smul' := L2_to_L1_smul,
  cont      := continuous_L2_to_L1, }

lemma L2_to_L1_coe_fn [borel_space 𝕂] (f : α →₂[μ] E) : L2_to_L1_clm f =ᵐ[μ] f :=
mem_ℒp.coe_fn_to_Lp _

end coe_linear_maps

section condexp_L1s

variables {m m0 : measurable_space α} (hm : m ≤ m0) [complete_space E] {μ : measure α}
  [finite_measure μ] [borel_space 𝕂]

variables (𝕂)
/-- Conditional expectation as a linear map from the simple functions of L1 to L1. -/
def condexp_L1s_lm : (α →₁ₛ[μ] E) →ₗ[𝕂] (α →₁[μ] E) :=
L2_to_L1_clm.to_linear_map.comp ((Lp_sub E 𝕂 m 2 μ).subtype.comp
  ((condexp_L2_clm 𝕂 hm).to_linear_map.comp L1s_to_L2_lm))

lemma condexp_L1s_lm_neg (f : α →₁ₛ[μ] E) : condexp_L1s_lm 𝕂 hm (-f) = -condexp_L1s_lm 𝕂 hm f :=
linear_map.map_neg (condexp_L1s_lm 𝕂 hm) f
variables {𝕂}

lemma condexp_L1s_ae_eq_condexp_L2 (f : α →₁ₛ[μ] E) :
  condexp_L1s_lm 𝕂 hm f =ᵐ[μ] condexp_L2_clm 𝕂 hm (L1s_to_L2_lm f) :=
(L2_to_L1_coe_fn _).trans (by refl)

lemma is_condexp_condexp_L2_L1s_to_L2 (f : α →₁ₛ[μ] E') :
  is_condexp m (condexp_L2_clm 𝕂 hm (L1s_to_L2_lm f) : α → E') f μ :=
is_condexp_congr_ae_right' hm (L1s_to_L2_coe_fn f) (is_condexp_condexp_L2 hm _)

variables (𝕂)
lemma is_condexp_condexp_L1s (f : α →₁ₛ[μ] E') :
  is_condexp m ((condexp_L1s_lm 𝕂 hm f) : α → E') f μ :=
is_condexp_congr_ae_left' hm (condexp_L1s_ae_eq_condexp_L2 hm _).symm
  (is_condexp_condexp_L2_L1s_to_L2 hm f)

lemma integral_condexp_L1s (f : α →₁ₛ[μ] E') {s : set α} (hs : @measurable_set α m s) :
  ∫ a in s, (condexp_L1s_lm 𝕂 hm f) a ∂μ = ∫ a in s, f a ∂μ :=
(is_condexp_condexp_L1s 𝕂 hm f).2 s hs
variables {𝕂}

end condexp_L1s

section condexp_L1s_ℝ

variables {m m0 : measurable_space α} (hm : m ≤ m0) {μ : measure α} [finite_measure μ]

lemma condexp_L1s_const_le (f : α →₁ₛ[μ] ℝ) (c : ℝ) (hf : ∀ᵐ x ∂μ, c ≤ f x) :
  ∀ᵐ x ∂μ, c ≤ condexp_L1s_lm ℝ hm f x :=
begin
  refine (ae_const_le_iff_forall_lt_measure_zero _ c).mpr (λ b hb, _),
  obtain ⟨⟨f', h_meas, hff'⟩, h_int_eq⟩ := is_condexp_condexp_L1s ℝ hm f,
  have h_int : integrable (condexp_L1s_lm ℝ hm f) μ, from Lp.integrable _ le_rfl,
  have h_int' : integrable f' μ := (integrable_congr hff').mp h_int,
  let s := {x | f' x ≤ b},
  have hsm : @measurable_set _ m s,
    from @measurable_set_le _ _ _ _ _ m _ _ _ _ _ h_meas (@measurable_const _ _ _ m _),
  have hs : measurable_set s, from hm s hsm,
  have hf's : ∀ x ∈ s, f' x ≤ b, from λ x hx, hx,
  specialize h_int_eq s hsm,
  rw set_integral_congr_ae hs (hff'.mono (λ x hx hxs, hx)) at h_int_eq,
  have h_int_le : c * (μ s).to_real ≤ ∫ x in s, f' x ∂μ,
  { rw h_int_eq,
    have h_const_le : ∫ x in s, c ∂μ ≤ ∫ x in s, f x ∂μ,
      from set_integral_mono_ae_restrict (integrable_on_const.mpr (or.inr (measure_lt_top _ _)))
        (Lp.integrable _ le_rfl).integrable_on (ae_restrict_of_ae hf),
    refine le_trans _ h_const_le,
    rw [set_integral_const, smul_eq_mul, mul_comm], },
  have h_int_lt : (μ s).to_real ≠ 0 → ∫ x in s, f' x ∂μ < c * (μ s).to_real,
  { intro h_ne_zero,
    suffices h_le_b : ∫ (x : α) in s, f' x ∂μ ≤ b * (μ s).to_real,
    { refine h_le_b.trans_lt _,
      exact mul_lt_mul_of_pos_right hb (ennreal.to_real_nonneg.lt_of_ne h_ne_zero.symm), },
    have h_const_le : ∫ x in s, f' x ∂μ ≤ ∫ x in s, b ∂μ,
    { refine set_integral_mono_ae_restrict h_int'.integrable_on
        (integrable_on_const.mpr (or.inr (measure_lt_top _ _))) _,
      rw [eventually_le, ae_restrict_iff hs],
      exact eventually_of_forall hf's, },
    refine h_const_le.trans _,
    rw [set_integral_const, smul_eq_mul, mul_comm], },
  have hμs_eq_zero : μ s = 0,
  { suffices hμs0 : (μ s).to_real = 0,
    { cases (ennreal.to_real_eq_zero_iff _).mp hμs0,
      { exact h, },
      { exact absurd h (measure_ne_top _ _), }, },
    by_contra,
    exact (lt_self_iff_false (c * (μ s).to_real)).mp (h_int_le.trans_lt (h_int_lt h)), },
  rw ← hμs_eq_zero,
  refine measure_congr _,
  refine hff'.mono (λ x hx, _),
  rw [← @set.mem_def _ x {x : α | ((condexp_L1s_lm ℝ hm) f) x ≤ b}, ← @set.mem_def _ x s],
  simp only [eq_iff_iff, set.mem_set_of_eq],
  rw hx,
end

lemma condexp_L1s_le_const (f : α →₁ₛ[μ] ℝ) (c : ℝ) (hf : ∀ᵐ x ∂μ, f x ≤ c) :
  ∀ᵐ x ∂μ, condexp_L1s_lm ℝ hm f x ≤ c :=
begin
  have h_neg := condexp_L1s_const_le hm (-f) (-c) _,
  swap,
  { rw [← L1.simple_func.coe_coe, L1.simple_func.coe_neg],
    refine (Lp.coe_fn_neg (f : Lp ℝ 1 μ)).mp (hf.mono (λ x hx hfx, _)),
    rw [hfx, pi.neg_apply],
    exact neg_le_neg hx, },
  rw linear_map.map_neg at h_neg,
  refine (Lp.coe_fn_neg ((condexp_L1s_lm ℝ hm) f)).mp (h_neg.mono (λ x hx hx_neg, _)),
  rw [hx_neg, pi.neg_apply] at hx,
  exact le_of_neg_le_neg hx,
end

lemma condexp_L1s_nonneg {f : α →₁ₛ[μ] ℝ} (hf : 0 ≤ᵐ[μ] f) : 0 ≤ᵐ[μ] condexp_L1s_lm ℝ hm f :=
condexp_L1s_const_le hm f 0 hf

lemma condexp_L1s_nonpos {f : α →₁ₛ[μ] ℝ} (hf : f ≤ᵐ[μ] 0) : condexp_L1s_lm ℝ hm f ≤ᵐ[μ] 0 :=
condexp_L1s_le_const hm f 0 hf

lemma condexp_L1s_mono {f g : α →₁ₛ[μ] ℝ} (hfg : f ≤ᵐ[μ] g) :
  condexp_L1s_lm ℝ hm f ≤ᵐ[μ] condexp_L1s_lm ℝ hm g :=
begin
  suffices h_sub : condexp_L1s_lm ℝ hm (f-g) ≤ᵐ[μ] 0,
  { rw linear_map.map_sub at h_sub,
    refine (Lp.coe_fn_sub (condexp_L1s_lm ℝ hm f) (condexp_L1s_lm ℝ hm g)).mp
      (h_sub.mono (λ x hx h_sub_fg, _)),
    rw [h_sub_fg, pi.zero_apply] at hx,
    rwa ← sub_nonpos, },
  have h_sub_fg : ⇑(f - g) ≤ᵐ[μ] 0,
  { rw ← L1.simple_func.coe_coe,
    rw L1.simple_func.coe_sub,
    refine (Lp.coe_fn_sub (f : α→₁[μ] ℝ) (g: α→₁[μ] ℝ)).mp (hfg.mono (λ x hx h_sub_fg, _)),
    rwa [h_sub_fg, L1.simple_func.coe_coe, L1.simple_func.coe_coe, pi.sub_apply, pi.zero_apply,
      sub_nonpos], },
  exact condexp_L1s_nonpos hm h_sub_fg,
end

lemma condexp_L1s_R_le_abs (f : α →₁ₛ[μ] ℝ) :
  condexp_L1s_lm ℝ hm f ≤ᵐ[μ] condexp_L1s_lm ℝ hm (L1.simple_func.map abs f abs_zero) :=
condexp_L1s_mono hm ((L1.simple_func.map_coe abs f abs_zero).mono
  (λ x hx, by {rw hx, exact le_abs_self _}))

lemma condexp_L1s_R_jensen_norm (f : α →₁ₛ[μ] ℝ) :
  ∀ᵐ x ∂μ, ∥condexp_L1s_lm ℝ hm f x∥
    ≤ condexp_L1s_lm ℝ hm (L1.simple_func.map (λ x, ∥x∥) f norm_zero) x :=
begin
  simp_rw [real.norm_eq_abs, abs_le],
  refine eventually.and _ (condexp_L1s_R_le_abs hm f),
  have h := condexp_L1s_R_le_abs hm (-f),
  have h_abs_neg : L1.simple_func.map abs (-f) abs_zero = L1.simple_func.map abs f abs_zero,
  { ext1,
    refine (L1.simple_func.coe_fn_neg f).mp ((L1.simple_func.map_coe abs (-f) abs_zero).mp
      ((L1.simple_func.map_coe abs f abs_zero).mono (λ x hx1 hx2 hx3, _))),
    rw [hx1, hx2, function.comp_app, hx3, pi.neg_apply, function.comp_app, abs_neg], },
  simp_rw [h_abs_neg, condexp_L1s_lm_neg ℝ hm f] at h,
  simp_rw neg_le,
  refine h.mp ((Lp.coe_fn_neg (condexp_L1s_lm ℝ hm f)).mono (λ x hx hxh, _)),
  rwa [← pi.neg_apply, ← hx],
end

--lemma condexp_L1s_R_jensen {m m0 : measurable_space α} (hm : m ≤ m0) {μ : measure α}
--  [finite_measure μ] (f : α →₁ₛ[μ] ℝ) (F : ℝ → ℝ) (hF : convex_on (set.univ : set ℝ) F) :
--  ∀ᵐ x ∂μ, F (condexp_L1s_lm ℝ hm f x) ≤ condexp_L1s_lm ℝ hm (L1.simple_func.map F f) x :=
--begin
--  sorry
--end

lemma norm_condexp_L1s_le_R (f : α →₁ₛ[μ] ℝ) : ∥condexp_L1s_lm ℝ hm f∥ ≤ ∥f∥ :=
begin
  simp_rw [L1.simple_func.norm_eq, norm_def],
  rw ennreal.to_real_le_to_real (Lp.snorm_ne_top _) (Lp.snorm_ne_top _),
  simp_rw [snorm_eq_snorm' ennreal.zero_lt_one.ne.symm ennreal.coe_ne_top, ennreal.one_to_real,
    snorm', div_one, ennreal.rpow_one],
  let F := λ x : ℝ, ∥x∥,
  have h_left : ∫⁻ a, (nnnorm (((condexp_L1s_lm ℝ hm) f) a) : ℝ≥0∞) ∂μ
      = ∫⁻ a, ennreal.of_real (∥((condexp_L1s_lm ℝ hm) f) a∥) ∂μ,
    by { congr, ext1 x, rw ← of_real_norm_eq_coe_nnnorm, },
  have h_right : ∫⁻ a, (nnnorm ((f : Lp ℝ 1 μ) a) : ℝ≥0∞) ∂μ
      = ∫⁻ a, ennreal.of_real (∥(f : Lp ℝ 1 μ) a∥) ∂μ,
    by { congr, ext1 x, rw ← of_real_norm_eq_coe_nnnorm, },
  rw [h_left, h_right],
  have h_le : ∫⁻ a, ennreal.of_real (∥((condexp_L1s_lm ℝ hm) f) a∥) ∂μ
    ≤ ∫⁻ a, ennreal.of_real (condexp_L1s_lm ℝ hm (L1.simple_func.map F f norm_zero) a) ∂μ,
  { refine lintegral_mono_ae ((condexp_L1s_R_jensen_norm hm f).mono (λ x hx, _)),
    rwa ennreal.of_real_le_of_real_iff ((norm_nonneg _).trans hx), },
  refine h_le.trans _,
  have h_integral_eq := integral_condexp_L1s ℝ hm (L1.simple_func.map F f norm_zero)
    (@measurable_set.univ α m),
  rw [integral_univ, integral_univ] at h_integral_eq,
  rw ← (ennreal.to_real_le_to_real _ _),
  swap, { have h := Lp.snorm_ne_top (condexp_L1s_lm ℝ hm (L1.simple_func.map F f norm_zero)),
    rw [snorm_eq_snorm' (one_ne_zero) ennreal.coe_ne_top, snorm', ennreal.one_to_real, one_div_one,
      ennreal.rpow_one] at h,
    simp_rw [ennreal.rpow_one, ← of_real_norm_eq_coe_nnnorm, ← lt_top_iff_ne_top] at h,
    refine (lt_of_le_of_lt _ h).ne,
    refine lintegral_mono_ae (eventually_of_forall (λ x, ennreal.of_real_le_of_real _)),
    rw real.norm_eq_abs,
    exact le_abs_self _, },
  swap, { simp_rw of_real_norm_eq_coe_nnnorm,
    have h := Lp.snorm_ne_top (f : α →₁[μ] ℝ),
    rw [snorm_eq_snorm' (one_ne_zero) ennreal.coe_ne_top, snorm', ennreal.one_to_real, one_div_one,
      ennreal.rpow_one] at h,
    simp_rw ennreal.rpow_one at h,
    exact h, },
  rw [← integral_eq_lintegral_of_nonneg_ae _ (Lp.ae_measurable _),
    ← integral_eq_lintegral_of_nonneg_ae, h_integral_eq,
    integral_congr_ae (L1.simple_func.map_coe F f norm_zero)],
  { simp only [L1.simple_func.coe_coe], },
  { exact eventually_of_forall (by simp [norm_nonneg]), },
  { exact measurable.comp_ae_measurable measurable_norm (Lp.ae_measurable _), },
  { refine condexp_L1s_nonneg hm ((L1.simple_func.map_coe F f norm_zero).mono (λ x hx, _)),
    rw [hx, pi.zero_apply],
    simp only [norm_nonneg], },
end

lemma norm_condexp_L1s_indicator_L1s_R_le {s : set α} (hs : measurable_set s) (hμs : μ s < ∞)
  (c : ℝ) :
  ∥condexp_L1s_lm ℝ hm (indicator_L1s hs hμs c)∥ ≤ ∥c∥ * (μ s).to_real :=
(norm_condexp_L1s_le_R hm _).trans norm_indicator_L1s.le

end condexp_L1s_ℝ

section continuous_set_integral

variables [measurable_space α] {μ : measure α}

lemma Lp_to_Lp_restrict_add (f g : Lp G p μ) (s : set α) :
  ((Lp.mem_ℒp (f+g)).restrict s).to_Lp ⇑(f+g)
    = ((Lp.mem_ℒp f).restrict s).to_Lp f + ((Lp.mem_ℒp g).restrict s).to_Lp g :=
begin
  ext1,
  refine (ae_restrict_of_ae (Lp.coe_fn_add f g)).mp _,
  refine (Lp.coe_fn_add (mem_ℒp.to_Lp f ((Lp.mem_ℒp f).restrict s))
    (mem_ℒp.to_Lp g ((Lp.mem_ℒp g).restrict s))).mp _,
  refine (mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp f).restrict s)).mp _,
  refine (mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp g).restrict s)).mp _,
  refine (mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp (f+g)).restrict s)).mono (λ x hx1 hx2 hx3 hx4 hx5, _),
  rw [hx4, hx1, pi.add_apply, hx2, hx3, hx5, pi.add_apply],
end

lemma Lp_to_Lp_restrict_smul [opens_measurable_space 𝕂] (c : 𝕂) (f : Lp F p μ) (s : set α) :
  ((Lp.mem_ℒp (c • f)).restrict s).to_Lp ⇑(c • f) = c • (((Lp.mem_ℒp f).restrict s).to_Lp f) :=
begin
  ext1,
  refine (ae_restrict_of_ae (Lp.coe_fn_smul c f)).mp _,
  refine (mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp f).restrict s)).mp _,
  refine (mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp (c • f)).restrict s)).mp _,
  refine (Lp.coe_fn_smul c (mem_ℒp.to_Lp f ((Lp.mem_ℒp f).restrict s))).mono
    (λ x hx1 hx2 hx3 hx4, _),
  rw [hx2, hx1, pi.smul_apply, hx3, hx4, pi.smul_apply],
end

variables (α F 𝕂)
/-- Linear map sending a function of `Lp F p μ` to the same function in `Lp F p (μ.restrict s)`. -/
def Lp_to_Lp_restrict_lm [borel_space 𝕂] (p : ℝ≥0∞) (s : set α) :
  @linear_map 𝕂 (Lp F p μ) (Lp F p (μ.restrict s)) _ _ _ _ _ :=
{ to_fun := λ f, mem_ℒp.to_Lp f ((Lp.mem_ℒp f).restrict s),
  map_add' := λ f g, Lp_to_Lp_restrict_add f g s,
  map_smul' := λ c f, Lp_to_Lp_restrict_smul c f s, }
variables {α F 𝕂}

lemma norm_Lp_to_Lp_restrict_le (s : set α) (f : Lp G p μ) :
  ∥mem_ℒp.to_Lp f ((Lp.mem_ℒp f).restrict s)∥ ≤ ∥f∥ :=
begin
  rw [norm_def, norm_def, ennreal.to_real_le_to_real (snorm_ne_top _) (snorm_ne_top _)],
  refine (le_of_eq _).trans (snorm_mono_measure measure.restrict_le_self),
  { exact s, },
  exact snorm_congr_ae (mem_ℒp.coe_fn_to_Lp _),
end

variables (α F 𝕂)
/-- Continuous linear map sending a function of `Lp F p μ` to the same function in
`Lp F p (μ.restrict s)`. -/
def Lp_to_Lp_restrict_clm [borel_space 𝕂] (μ : measure α) (p : ℝ≥0∞) [hp : fact(1 ≤ p)]
  (s : set α) :
  @continuous_linear_map 𝕂 _ (Lp F p μ) _ _ (Lp F p (μ.restrict s)) _ _ _ _ :=
@linear_map.mk_continuous 𝕂 (Lp F p μ) (Lp F p (μ.restrict s)) _ _ _ _ _
  (Lp_to_Lp_restrict_lm α F 𝕂 p s) 1
  (by { intro f, rw one_mul, exact norm_Lp_to_Lp_restrict_le s f, })

@[continuity]
lemma continuous_Lp_to_Lp_restrict [borel_space 𝕂] (p : ℝ≥0∞) [hp : fact(1 ≤ p)] (s : set α) :
  continuous (Lp_to_Lp_restrict_clm α F 𝕂 μ p s) :=
continuous_linear_map.continuous _
variables {α F 𝕂}

variables (𝕂)
lemma Lp_to_Lp_restrict_clm_coe_fn [borel_space 𝕂] [hp : fact(1 ≤ p)] (s : set α) (f : Lp F p μ) :
  Lp_to_Lp_restrict_clm α F 𝕂 μ p s f =ᵐ[μ.restrict s] f :=
mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp f).restrict s)
variables {𝕂}

@[continuity]
lemma continuous_set_integral (s : set α) : continuous (λ f : α →₁[μ] G', ∫ x in s, f x ∂μ) :=
begin
  haveI : fact((1 : ℝ≥0∞) ≤ 1) := ⟨le_rfl⟩,
  have h_comp : (λ f : α →₁[μ] G', ∫ x in s, f x ∂μ)
    = (integral (μ.restrict s)) ∘ (λ f, Lp_to_Lp_restrict_clm α G' ℝ μ 1 s f),
  { ext1 f,
    rw [function.comp_apply, integral_congr_ae (Lp_to_Lp_restrict_clm_coe_fn ℝ s f)], },
  rw h_comp,
  exact continuous_integral.comp (continuous_Lp_to_Lp_restrict α G' ℝ 1 s),
end

end continuous_set_integral

section condexp_def

variables {m m0 : measurable_space α} (hm : m ≤ m0) {μ : measure α} [finite_measure μ]
  [borel_space 𝕂]

variables (𝕂)
lemma condexp_L1s_indicator_L1s_eq {s : set α} (hs : measurable_set s) (hμs : μ s < ∞) (c : E') :
  condexp_L1s_lm 𝕂 hm (indicator_L1s hs hμs c) =ᵐ[μ]
    λ x, (condexp_L1s_lm ℝ hm (@indicator_L1s α ℝ _ _ _ _ _ μ _ hs hμs 1) x) • c :=
begin
  refine is_condexp_unique 𝕂 hm (is_condexp_condexp_L1s 𝕂 hm _) (Lp.integrable _ le_rfl) _ _,
  swap,
  { by_cases hc : c = 0,
    { simp [hc], },
    { exact (integrable_smul_const hc).mpr (Lp.integrable _ le_rfl), }, },
  obtain ⟨⟨f₁', h_meas₁, hff'₁⟩, h_int_eq₁⟩ := is_condexp_condexp_L1s ℝ hm
    (@indicator_L1s α ℝ _ _ _ _ _ μ _ hs hμs 1),
  refine ⟨_, _⟩,
  { refine ⟨λ x, (f₁' x) • c, _, _⟩,
    { exact @measurable.smul _ m _ _ _ _ _ _ f₁' _ h_meas₁ (@measurable_const _ _ _ m c), },
    { exact eventually_eq.fun_comp hff'₁ (λ x, x • c), }, },
  { intros t ht,
    have h_smul : ∫ a in t, (indicator_L1s hs hμs c) a ∂μ
        = ∫ a in t, ((indicator_L1s hs hμs (1 : ℝ)) a) • c ∂μ,
      from set_integral_congr_ae (hm t ht)  ((indicator_L1s_eq_smul c).mono (λ x hx hxs, hx)),
    refine eq.trans _ h_smul.symm,
    rw [integral_smul_const, integral_smul_const, h_int_eq₁ t ht], },
end
variables {𝕂}

lemma norm_condexp_L1s_indicator_L1s {s : set α} (hs : measurable_set s) (hμs : μ s < ∞) (c : E') :
  ∥condexp_L1s_lm 𝕂 hm (indicator_L1s hs hμs c)∥ ≤ ∥indicator_L1s hs hμs c∥ :=
begin
  rw [L1.simple_func.norm_eq, indicator_L1s_coe,
    norm_indicator_Lp ennreal.zero_lt_one ennreal.coe_ne_top, norm_def,
    snorm_congr_ae (condexp_L1s_indicator_L1s_eq 𝕂 hm hs hμs c),
    snorm_eq_snorm' ennreal.zero_lt_one.ne.symm ennreal.coe_ne_top, snorm'],
  simp_rw [ennreal.one_to_real, div_one, ennreal.rpow_one, real.rpow_one, nnnorm_smul,
    ennreal.coe_mul],
  rw [lintegral_mul_const _ (Lp.measurable _).nnnorm.ennreal_coe, ennreal.to_real_mul, mul_comm,
    ← of_real_norm_eq_coe_nnnorm, ennreal.to_real_of_real (norm_nonneg _)],
  swap, { apply_instance, },
  refine mul_le_mul le_rfl _ ennreal.to_real_nonneg (norm_nonneg _),
  suffices h_norm : ∥(condexp_L1s_lm ℝ hm) (indicator_L1s hs hμs (1 : ℝ))∥ ≤ (μ s).to_real,
  { rw [norm_def, snorm_eq_snorm' ennreal.zero_lt_one.ne.symm ennreal.coe_ne_top,
      snorm', ennreal.one_to_real, div_one] at h_norm,
    simp_rw ennreal.rpow_one at h_norm,
    exact h_norm, },
  refine (norm_condexp_L1s_indicator_L1s_R_le hm hs hμs (1 : ℝ)).trans _,
  simp only [one_mul, norm_one],
end

lemma norm_condexp_L1s_le (f : α →₁ₛ[μ] E') : ∥condexp_L1s_lm 𝕂 hm f∥ ≤ ∥f∥ :=
begin
  rw L1.simple_func.norm_eq_integral,
  rw simple_func.map_integral _ _ (L1.simple_func.integrable _),
  swap, { exact norm_zero, },
  nth_rewrite 0 L1.simple_func_eq_sum_indicator_L1s f,
  rw linear_map.map_sum,
  refine (norm_sum_le _ _).trans _,
  refine finset.sum_le_sum (λ x hxf, (norm_condexp_L1s_indicator_L1s hm _ _ x).trans _),
  rw [smul_eq_mul, mul_comm, norm_indicator_L1s],
end

lemma continuous_condexp_L1s : continuous (@condexp_L1s_lm α E' 𝕂 _ _ _ _ _ _ m m0 hm _ μ _ _) :=
linear_map.continuous_of_bound _ 1 (λ f, (norm_condexp_L1s_le hm f).trans (one_mul _).symm.le)

variables (𝕂)
/-- Conditional expectation as a continuous linear map from the simple functions in L1 to L1. -/
def condexp_L1s_clm : (α →₁ₛ[μ] E') →L[𝕂] (α →₁[μ] E') :=
{ to_linear_map := condexp_L1s_lm 𝕂 hm,
  cont := continuous_condexp_L1s hm, }

/-- Conditional expectation as a continuous linear map from L1 to L1. -/
def condexp_L1 : (α →₁[μ] E') →L[𝕂] (α →₁[μ] E') :=
@continuous_linear_map.extend 𝕂 (α →₁ₛ[μ] E') (α →₁[μ] E') (α →₁[μ] E') _ _ _ _ _ _ _
  (condexp_L1s_clm 𝕂 hm) _ (L1.simple_func.coe_to_L1 α E' 𝕂) L1.simple_func.dense_range
  L1.simple_func.uniform_inducing

lemma condexp_L1_eq_condexp_L1s (f : α →₁ₛ[μ] E') :
  condexp_L1 𝕂 hm (f : α →₁[μ] E') = condexp_L1s_clm 𝕂 hm f :=
begin
  refine uniformly_extend_of_ind L1.simple_func.uniform_inducing L1.simple_func.dense_range _ _,
  exact @continuous_linear_map.uniform_continuous 𝕂 (α →₁ₛ[μ] E') (α →₁[μ] E') _ _ _ _ _
    (@condexp_L1s_clm α E' 𝕂 _ _ _ _ _ _ _ _ _ _ _ hm μ _ _),
end
variables {𝕂}

lemma ae_measurable'_condexp_L1 (f : α →₁[μ] E') : ae_measurable' m (condexp_L1 𝕂 hm f) μ :=
begin
  refine @is_closed_property _ (α →₁[μ] E') _ _ _ L1.simple_func.dense_range _ _ f,
  { change is_closed ((condexp_L1 𝕂 hm) ⁻¹' {x : ↥(Lp E' 1 μ) | ae_measurable' m x μ}),
    haveI : fact ((1 : ℝ≥0∞) ≤ 1) := ⟨le_rfl⟩,
    exact is_closed.preimage (continuous_linear_map.continuous _) (is_closed_ae_measurable' hm), },
  { intro fs,
    rw condexp_L1_eq_condexp_L1s,
    obtain ⟨f', hf'_meas, hf'⟩ := (is_condexp_condexp_L1s 𝕂 hm fs).1,
    refine ⟨f', hf'_meas, _⟩,
    refine eventually_eq.trans (eventually_of_forall (λ x, _)) hf',
    refl, },
end

lemma integral_eq_condexp_L1 (f : α →₁[μ] E') (s : set α) (hs : @measurable_set α m s) :
  ∫ a in s, (condexp_L1 𝕂 hm f) a ∂μ = ∫ a in s, f a ∂μ :=
begin
  refine @is_closed_property _ (α →₁[μ] E') _ _ _ L1.simple_func.dense_range (is_closed_eq _ _) _ f,
  { change continuous ((λ (g : ↥(Lp E' 1 μ)), ∫ (a : α) in s, g a ∂μ) ∘ (condexp_L1 𝕂 hm)),
    continuity, },
  { continuity, },
  { simp_rw condexp_L1_eq_condexp_L1s,
    exact λ fs, (is_condexp_condexp_L1s 𝕂 hm fs).2 s hs, },
end

lemma is_condexp_condexp_L1 (f : α →₁[μ] E') : is_condexp m (condexp_L1 𝕂 hm f) f μ :=
⟨ae_measurable'_condexp_L1 hm f, integral_eq_condexp_L1 hm f⟩

variables (𝕂)
include 𝕂 hm
/-- Conditional expectation of an integrable function. This is an `m`-measurable function such
that for all `m`-measurable sets `s`, `∫ x in s, condexp 𝕂 hm f hf x ∂μ = ∫ x in s, f x ∂μ`. -/
def condexp (f : α → E') (hf : integrable f μ) : α → E' :=
(is_condexp_condexp_L1 hm (hf.to_L1 f)).1.some
omit 𝕂 hm
variables {𝕂}

end condexp_def

section condexp_properties
include 𝕂

variables {f f₂ g : α → E'} {m₂ m m0 : measurable_space α} {hm : m ≤ m0} {μ : measure α}
  [finite_measure μ] [borel_space 𝕂]

lemma measurable_condexp (hf : integrable f μ) : @measurable _ _ m _ (condexp 𝕂 hm f hf) :=
(is_condexp_condexp_L1 hm (hf.to_L1 f)).1.some_spec.1

lemma condexp_ae_eq_condexp_L1 (hf : integrable f μ) :
  condexp 𝕂 hm f hf =ᵐ[μ] condexp_L1 𝕂 hm (hf.to_L1 f) :=
(is_condexp_condexp_L1 hm (hf.to_L1 f)).1.some_spec.2.symm

lemma is_condexp_condexp (hf : integrable f μ) : is_condexp m (condexp 𝕂 hm f hf) f μ :=
is_condexp_congr_ae' hm (condexp_ae_eq_condexp_L1 hf).symm (integrable.coe_fn_to_L1 hf)
  (is_condexp_condexp_L1 hm (hf.to_L1 f))

lemma integrable_condexp (hf : integrable f μ) : integrable (condexp 𝕂 hm f hf) μ :=
(integrable_congr (condexp_ae_eq_condexp_L1 hf)).mpr (Lp.integrable _ le_rfl)

lemma integrable_trim_condexp (hf : integrable f μ) :
  @integrable α E' m _ _ (condexp 𝕂 hm f hf) (μ.trim hm) :=
integrable_trim_of_measurable hm (measurable_condexp hf) (integrable_condexp hf)

lemma set_integral_condexp_eq (hf : integrable f μ) {s : set α} (hs : @measurable_set α m s) :
  ∫ x in s, condexp 𝕂 hm f hf x ∂μ = ∫ x in s, f x ∂μ :=
(is_condexp_condexp hf).2 s hs

lemma integral_condexp (hf : integrable f μ) : ∫ x, condexp 𝕂 hm f hf x ∂μ = ∫ x, f x ∂μ :=
by rw [← integral_univ, set_integral_condexp_eq hf (@measurable_set.univ α m), integral_univ]

lemma condexp_comp (hm2 : m₂ ≤ m) (hm : m ≤ m0) (hf : integrable f μ) :
  condexp 𝕂 (hm2.trans hm) (condexp 𝕂 hm f hf) (integrable_condexp hf)
    =ᵐ[μ] condexp 𝕂 (hm2.trans hm) f hf :=
begin
  refine is_condexp_unique 𝕂 (hm2.trans hm) _ (integrable_condexp _)
    (is_condexp_condexp hf) (integrable_condexp hf),
  exact is_condexp.trans hm2 (is_condexp_condexp _) (is_condexp_condexp hf),
end

omit 𝕂
end condexp_properties

end measure_theory
