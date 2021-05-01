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

local notation `to_simple_func` := L1.simple_func.to_simple_func
local notation `indicator_L1s` := L1.simple_func.indicator_L1s

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

lemma sub [add_group β] [has_measurable_sub₂ β] {m m0 : measurable_space α}
  {μ : measure α} {f g : α → β} (hf : ae_measurable' m f μ) (hg : ae_measurable' m g μ) :
  ae_measurable' m (f - g) μ :=
begin
  rcases hf with ⟨f', h_f'_meas, hff'⟩,
  rcases hg with ⟨g', h_g'_meas, hgg'⟩,
  refine ⟨f' - g', @measurable.sub α m _ _ _ _ f' g' h_f'_meas h_g'_meas, _⟩,
  exact hff'.sub hgg',
end

lemma neg [has_neg β] [has_measurable_neg β] {m m0 : measurable_space α}
  {μ : measure α} {f : α → β} (hf : ae_measurable' m f μ) :
  ae_measurable' m (-f) μ :=
begin
  rcases hf with ⟨f', h_f'_meas, hff'⟩,
  exact ⟨-f', @measurable.neg α m _ _ _ _ f' h_f'_meas, hff'.neg⟩,
end

lemma smul₂ {δ} [has_scalar δ β] [measurable_space δ] [has_measurable_smul₂ δ β]
  {m m0 : measurable_space α} {μ : measure α}
  {f : α → δ} (hf : ae_measurable' m f μ) {g : α → β} (hg : ae_measurable' m g μ) :
  ae_measurable' m (λ x, f x • (g x)) μ :=
begin
  obtain ⟨f', hf_meas, hff'⟩ := hf,
  obtain ⟨g', hg_meas, hgg'⟩ := hg,
  refine ⟨λ x, (f' x) • (g' x), _, eventually_eq.comp₂ hff' (λ x y, x • y) hgg'⟩,
  exact @measurable.smul _ m _ _ _ _ _ _ _ _ hf_meas hg_meas,
end

lemma const_smul {δ} [has_scalar δ β] [measurable_space δ] [has_measurable_smul δ β]
  {m m0 : measurable_space α} {μ : measure α} (c : δ) {f : α → β} (hf : ae_measurable' m f μ) :
  ae_measurable' m (c • f) μ :=
begin
  rcases hf with ⟨f', h_f'_meas, hff'⟩,
  refine ⟨c • f', @measurable.const_smul α m _ _ _ _ _ _ f' h_f'_meas c, _⟩,
  exact eventually_eq.fun_comp hff' (λ x, c • x),
end

lemma restrict {m m0 : measurable_space α} {μ : measure α} (hf : ae_measurable' m f μ) (s : set α) :
  ae_measurable' m f (μ.restrict s) :=
by { obtain ⟨g, hg_meas, hfg⟩ := hf, exact ⟨g, hg_meas, ae_restrict_of_ae hfg⟩, }

lemma indicator [has_zero β] {m m0 : measurable_space α} {μ : measure α} (hf : ae_measurable' m f μ)
  {s : set α} (hs : @measurable_set α m s) :
  ae_measurable' m (s.indicator f) μ :=
begin
  rcases hf with ⟨f', h_f'_meas, hff'⟩,
  refine ⟨s.indicator f', @measurable.indicator α _ m _ _ s _ h_f'_meas hs, _⟩,
  refine hff'.mono (λ x hx, _),
  rw [set.indicator_apply, set.indicator_apply, hx],
end

lemma const {m m0 : measurable_space α} {μ : measure α} (c : β) : ae_measurable' m (λ x : α, c) μ :=
(@measurable_const _ _ _ m c).ae_measurable'

lemma smul_const {δ} [has_scalar δ β] [measurable_space δ] [has_measurable_smul₂ δ β]
  {m m0 : measurable_space α} {μ : measure α} {f : α → δ} (hf : ae_measurable' m f μ) (c : β) :
  ae_measurable' m (λ x, f x • c) μ :=
ae_measurable'.smul₂ hf (const c)

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

lemma ae_measurable.restrict [measurable_space α] {f : α → β} {μ : measure α}
  (hf : ae_measurable f μ) (s : set α) :
  ae_measurable f (μ.restrict s) :=
ae_measurable'.restrict hf s

notation α ` →₂[`:25 μ `] ` E := measure_theory.Lp E 2 μ

section L2_integrable

variables [opens_measurable_space 𝕂] [measurable_space α] {μ : measure α}

variables (𝕂 F)
/-- Subspace of L2 containing the integrable functions of L2. -/
def L2_integrable (μ : measure α) :
  submodule 𝕂 (α →₂[μ] F) :=
{ carrier := {f | integrable f μ},
  zero_mem' := (integrable_congr (Lp.coe_fn_zero _ _ _).symm).mp (integrable_zero _ _ _),
  add_mem' := λ f g hf hg, (integrable_congr (Lp.coe_fn_add _ _).symm).mp (hf.add hg),
  smul_mem' := λ c f hf, (integrable_congr (Lp.coe_fn_smul _ _).symm).mp (hf.smul c), }
variables {𝕂 F}

lemma dist_L2_integrable (f g : L2_integrable F 𝕂 μ) :
  dist f g = dist (f : α →₂[μ] F) (g : α →₂[μ] F) :=
rfl

lemma mem_L2_integrable_iff_integrable {f : α →₂[μ] F} :
  f ∈ L2_integrable F 𝕂 μ ↔ integrable f μ :=
by simp_rw [← set_like.mem_coe, ← submodule.mem_carrier, L2_integrable, set.mem_set_of_eq]

lemma L2_integrable.integrable (f : L2_integrable F 𝕂 μ) : integrable f μ :=
mem_L2_integrable_iff_integrable.mp f.mem

end L2_integrable

section Lp_sub

variables (𝕂 F)
/-- Lp subspace of functions `f` verifying `ae_measurable' m f μ`. -/
def Lp_sub [opens_measurable_space 𝕂] (m : measurable_space α) [measurable_space α] (p : ℝ≥0∞)
  (μ : measure α) :
  submodule 𝕂 (Lp F p μ) :=
{ carrier   := {f : (Lp F p μ) | ae_measurable' m f μ} ,
  zero_mem' := ⟨(0 : α → F), @measurable_zero _ α _ m _, Lp.coe_fn_zero _ _ _⟩,
  add_mem'  := λ f g hf hg, (hf.add hg).congr_ae (Lp.coe_fn_add f g).symm,
  smul_mem' := λ c f hf, (hf.const_smul c).congr_ae (Lp.coe_fn_smul c f).symm, }
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

lemma mem_Lp_sub_indicator_Lp {m m0 : measurable_space α} (hm : m ≤ m0)
  {μ : measure α} {s : set α} (hs : @measurable_set α m s) {c : F} {hμsc : c = 0 ∨ μ s < ∞} :
  indicator_Lp p (hm s hs) c hμsc ∈ Lp_sub F 𝕂 m p μ :=
⟨s.indicator (λ x : α, c),
  @measurable.indicator α _ m _ _ s (λ x, c) (@measurable_const _ α _ m _) hs,
  indicator_Lp_coe_fn p (hm s hs) c hμsc⟩

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

def is_average_finite (m : measurable_space α) [m0 : measurable_space α] (f g : α → F')
  (μ : measure α) :
  Prop :=
∀ s (hs : @measurable_set α m s) (hμs : μ s < ∞), ∫ a in s, f a - g a ∂μ = 0

/-- Same as `is_condexp`, but integral of the difference is zero. -/
def is_condexp' (m : measurable_space α) [m0 : measurable_space α] (f g : α → F') (μ : measure α) :
  Prop :=
ae_measurable' m f μ ∧ ∀ s (hs : @measurable_set α m s), ∫ a in s, f a - g a ∂μ = 0

/-- `f` is a conditional expectation of `g` with respect to the measurable space structure `m`. -/
def is_condexp (m : measurable_space α) [m0 : measurable_space α] (f g : α → F') (μ : measure α) :
  Prop :=
ae_measurable' m f μ ∧ ∀ s (hs : @measurable_set α m s), ∫ a in s, f a ∂μ = ∫ a in s, g a ∂μ

variables {m₂ m m0 : measurable_space α} {μ : measure α} {f f₁ f₂ g g₁ g₂ : α → F'}

lemma is_condexp_iff_is_condexp'_of_integrable (hf : integrable f μ) (hg : integrable g μ) :
  is_condexp m f g μ ↔ is_condexp' m f g μ :=
by simp_rw [is_condexp, is_condexp', integral_sub hf.integrable_on hg.integrable_on, sub_eq_zero]

lemma is_condexp.refl (hf : ae_measurable' m f μ) : is_condexp m f f μ := ⟨hf, λ s hs, rfl⟩

lemma is_condexp'.refl (hf : ae_measurable' m f μ) : is_condexp' m f f μ :=
⟨hf, λ s hs, by simp only [integral_const, smul_zero, sub_self]⟩

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

lemma is_condexp'_congr_ae_left' (hm : m ≤ m0) (hf12 : f₁ =ᵐ[μ] f₂) (hf₁ : is_condexp' m f₁ g μ) :
  is_condexp' m f₂ g μ :=
begin
  rcases hf₁ with ⟨⟨f, h_meas, h_eq⟩, h_int_eq⟩,
  refine ⟨⟨f, h_meas, hf12.symm.trans h_eq⟩, λ s hs, _⟩,
  simp_rw ← pi.sub_apply,
  have h_sub_eq : f₂ - g =ᵐ[μ] f₁ - g,
  { refine hf12.mono (λ x hx, _), rw [pi.sub_apply, pi.sub_apply, hx], },
  rw set_integral_congr_ae (hm s hs) (h_sub_eq.mono (λ x hx hxs, hx)),
  exact h_int_eq s hs,
end

lemma is_condexp_congr_ae_left (hm : m ≤ m0) (hf12 : f₁ =ᵐ[μ] f₂) :
  is_condexp m f₁ g μ ↔ is_condexp m f₂ g μ :=
⟨λ h, is_condexp_congr_ae_left' hm hf12 h, λ h, is_condexp_congr_ae_left' hm hf12.symm h⟩

lemma is_condexp'_congr_ae_left (hm : m ≤ m0) (hf12 : f₁ =ᵐ[μ] f₂) :
  is_condexp' m f₁ g μ ↔ is_condexp' m f₂ g μ :=
⟨λ h, is_condexp'_congr_ae_left' hm hf12 h, λ h, is_condexp'_congr_ae_left' hm hf12.symm h⟩

lemma is_condexp_congr_ae_right' (hm : m ≤ m0) (hg12 : g₁ =ᵐ[μ] g₂) (hf₁ : is_condexp m f g₁ μ) :
  is_condexp m f g₂ μ :=
begin
  rcases hf₁ with ⟨h_meas, h_int_eq⟩,
  refine ⟨h_meas, λ s hs, _⟩,
  rw set_integral_congr_ae (hm s hs) (hg12.mono (λ x hx hxs, hx.symm)),
  exact h_int_eq s hs,
end

lemma is_condexp'_congr_ae_right' (hm : m ≤ m0) (hg12 : g₁ =ᵐ[μ] g₂) (hf₁ : is_condexp' m f g₁ μ) :
  is_condexp' m f g₂ μ :=
begin
  rcases hf₁ with ⟨h_meas, h_int_eq⟩,
  refine ⟨h_meas, λ s hs, _⟩,
  have h_sub_eq : f - g₁ =ᵐ[μ] f - g₂,
  { refine hg12.mono (λ x hx, _), rw [pi.sub_apply, pi.sub_apply, hx], },
  simp_rw ← pi.sub_apply,
  rw set_integral_congr_ae (hm s hs) (h_sub_eq.mono (λ x hx hxs, hx.symm)),
  exact h_int_eq s hs,
end

lemma is_condexp_congr_ae_right (hm : m ≤ m0) (hg12 : g₁ =ᵐ[μ] g₂) :
  is_condexp m f g₁ μ ↔ is_condexp m f g₂ μ :=
⟨λ h, is_condexp_congr_ae_right' hm hg12 h, λ h, is_condexp_congr_ae_right' hm hg12.symm h⟩

lemma is_condexp'_congr_ae_right (hm : m ≤ m0) (hg12 : g₁ =ᵐ[μ] g₂) :
  is_condexp' m f g₁ μ ↔ is_condexp' m f g₂ μ :=
⟨λ h, is_condexp'_congr_ae_right' hm hg12 h, λ h, is_condexp'_congr_ae_right' hm hg12.symm h⟩

lemma is_condexp_congr_ae' (hm : m ≤ m0) (hf12 : f₁ =ᵐ[μ] f₂) (hg12 : g₁ =ᵐ[μ] g₂)
  (hfg₁ : is_condexp m f₁ g₁ μ) :
  is_condexp m f₂ g₂ μ :=
is_condexp_congr_ae_left' hm hf12 (is_condexp_congr_ae_right' hm hg12 hfg₁)

lemma is_condexp'_congr_ae' (hm : m ≤ m0) (hf12 : f₁ =ᵐ[μ] f₂) (hg12 : g₁ =ᵐ[μ] g₂)
  (hfg₁ : is_condexp' m f₁ g₁ μ) :
  is_condexp' m f₂ g₂ μ :=
is_condexp'_congr_ae_left' hm hf12 (is_condexp'_congr_ae_right' hm hg12 hfg₁)

lemma is_condexp_congr_ae (hm : m ≤ m0) (hf12 : f₁ =ᵐ[μ] f₂) (hg12 : g₁ =ᵐ[μ] g₂) :
  is_condexp m f₁ g₁ μ ↔ is_condexp m f₂ g₂ μ :=
⟨λ h, is_condexp_congr_ae' hm hf12 hg12 h, λ h, is_condexp_congr_ae' hm hf12.symm hg12.symm h⟩

lemma is_condexp'_congr_ae (hm : m ≤ m0) (hf12 : f₁ =ᵐ[μ] f₂) (hg12 : g₁ =ᵐ[μ] g₂) :
  is_condexp' m f₁ g₁ μ ↔ is_condexp' m f₂ g₂ μ :=
⟨λ h, is_condexp'_congr_ae' hm hf12 hg12 h, λ h, is_condexp'_congr_ae' hm hf12.symm hg12.symm h⟩

lemma is_condexp.neg (hfg : is_condexp m f g μ) :
  is_condexp m (-f) (-g) μ :=
begin
  rcases hfg with ⟨h_meas, h_int_eq⟩,
  refine ⟨h_meas.neg, (λ s hs, _)⟩,
  simp_rw pi.neg_apply,
  rw [integral_neg, integral_neg, h_int_eq s hs],
end

lemma is_condexp'.neg (hfg : is_condexp' m f g μ) :
  is_condexp' m (-f) (-g) μ :=
begin
  rcases hfg with ⟨h_meas, h_int_eq⟩,
  refine ⟨h_meas.neg, (λ s hs, _)⟩,
  simp_rw [pi.neg_apply],
  specialize h_int_eq s hs,
  rw [← neg_eq_zero, ← integral_neg] at h_int_eq,
  simpa only [neg_sub_neg, neg_sub] using h_int_eq,
end

lemma is_condexp.add (hfg₁ : is_condexp m f₁ g₁ μ) (hfg₂ : is_condexp m f₂ g₂ μ)
  (hf₁ : integrable f₁ μ) (hg₁ : integrable g₁ μ) (hf₂ : integrable f₂ μ) (hg₂ : integrable g₂ μ) :
  is_condexp m (f₁ + f₂) (g₁ + g₂) μ :=
begin
  rcases hfg₁ with ⟨h_meas₁, h_int_eq₁⟩,
  rcases hfg₂ with ⟨h_meas₂, h_int_eq₂⟩,
  refine ⟨h_meas₁.add h_meas₂, (λ s hs, _)⟩,
  simp_rw pi.add_apply,
  rw [integral_add hf₁.integrable_on hf₂.integrable_on,
    integral_add hg₁.integrable_on hg₂.integrable_on, h_int_eq₁ s hs, h_int_eq₂ s hs],
end

lemma is_condexp_const_self (c : F') : is_condexp m (λ x, c) (λ x, c) μ :=
⟨(@measurable_const _ _ _ m _).ae_measurable', λ s hs, rfl⟩

lemma integrable.finset_sum {ι} {s : finset ι} (f : ι → α → F')
  (hf_int : ∀ i ∈ s, integrable (f i) μ) :
  integrable (∑ i in s, f i) μ :=
finset.sum_induction _ (λ g : α → F', integrable g μ) (λ g₁ g₂, integrable.add)
  (integrable_zero α F' μ) hf_int

lemma is_condexp.sum {ι} {s : finset ι} (f g : ι → α → F') (hf_int : ∀ i, integrable (f i) μ)
  (hg_int : ∀ i, integrable (g i) μ) (hfg : ∀ i ∈ s, is_condexp m (f i) (g i) μ) :
  is_condexp m (∑ i in s, f i) (∑ i in s, g i) μ :=
begin
  revert hfg,
  haveI : decidable_eq ι := classical.dec_eq _,
  refine finset.induction _ _ s,
  { simp_rw finset.sum_empty,
    exact λ _, is_condexp_const_self (0 : F'), },
  intros y s hys hs h_insert,
  specialize hs (λ i hi, h_insert i (finset.mem_insert_of_mem hi)),
  simp_rw finset.sum_insert hys,
  refine is_condexp.add (h_insert y (finset.mem_insert_self y s)) hs (hf_int y) (hg_int y) _ _,
  { exact integrable.finset_sum f (λ i _, hf_int i), },
  { exact integrable.finset_sum g (λ i _, hg_int i), },
end

lemma is_condexp.sub (hfg₁ : is_condexp m f₁ g₁ μ) (hfg₂ : is_condexp m f₂ g₂ μ)
  (hf₁ : integrable f₁ μ) (hg₁ : integrable g₁ μ) (hf₂ : integrable f₂ μ) (hg₂ : integrable g₂ μ) :
  is_condexp m (f₁ - f₂) (g₁ - g₂) μ :=
begin
  rcases hfg₁ with ⟨h_meas₁, h_int_eq₁⟩,
  rcases hfg₂ with ⟨h_meas₂, h_int_eq₂⟩,
  refine ⟨h_meas₁.sub h_meas₂, (λ s hs, _)⟩,
  simp_rw pi.sub_apply,
  rw [integral_sub hf₁.integrable_on hf₂.integrable_on,
    integral_sub hg₁.integrable_on hg₂.integrable_on, h_int_eq₁ s hs, h_int_eq₂ s hs],
end

lemma is_condexp.indicator (hm : m ≤ m0) (hfg : is_condexp m f g μ) {s : set α}
  (hs : @measurable_set α m s) :
  is_condexp m (s.indicator f) (s.indicator g) μ :=
begin
  rcases hfg with ⟨h_meas, h_int_eq⟩,
  refine ⟨h_meas.indicator hs, (λ t ht, _)⟩,
  specialize h_int_eq (s ∩ t) (@measurable_set.inter α m s t hs ht),
  rwa [integral_indicator (hm s hs), integral_indicator (hm s hs),
    measure.restrict_restrict (hm s hs)],
end

end is_condexp

section is_condexp_properties

variables {m m0 : measurable_space α} {μ : measure α}

lemma is_condexp.nonneg (hm : m ≤ m0) {f g : α → ℝ} (hf : 0 ≤ᵐ[μ] f) (hgf : is_condexp m g f μ)
  (hg : integrable g μ) :
  0 ≤ᵐ[μ] g :=
begin
  obtain ⟨⟨f', h_meas, hff'⟩, h_int_eq⟩ := hgf,
  have h_int' : integrable f' μ := (integrable_congr hff').mp hg,
  have h_int'_m : @integrable α _ m _ _ f' (μ.trim hm),
    from integrable_trim_of_measurable hm h_meas h_int',
  refine eventually_le.trans (ae_eq_null_of_trim hm _) hff'.symm.le,
  refine @ae_nonneg_of_forall_set_ℝ α m (μ.trim hm) f' h_int'_m (λ s hs, _),
  rw ← set_integral_trim hm f' h_meas h_int' hs,
  specialize h_int_eq s hs,
  rw set_integral_congr_ae (hm s hs) (hff'.mono (λ x hx _, hx)) at h_int_eq,
  rw h_int_eq,
  exact integral_nonneg_of_ae (ae_restrict_of_ae hf),
end

lemma is_condexp.nonpos (hm : m ≤ m0) {f g : α → ℝ} (hf : f ≤ᵐ[μ] 0) (hgf : is_condexp m g f μ)
  (hg : integrable g μ) :
  g ≤ᵐ[μ] 0 :=
begin
  have hf_neg : 0 ≤ᵐ[μ] (-f),
  { refine (hf.mono (λ x hx, _)),
    rw [pi.zero_apply, ← neg_zero] at hx,
    rwa [pi.neg_apply, pi.zero_apply, le_neg], },
  have h_neg := is_condexp.nonneg hm hf_neg (is_condexp.neg hgf) hg.neg,
  refine h_neg.mono (λ x hx, _),
  rw [pi.neg_apply, pi.zero_apply, ← neg_zero] at hx,
  exact le_of_neg_le_neg hx,
end

lemma is_condexp.mono (hm : m ≤ m0) {f g fc gc : α → ℝ} (hfg : f ≤ᵐ[μ] g)
  (hf : is_condexp m fc f μ) (hfc_int : integrable fc μ) (hf_int : integrable f μ)
  (hg : is_condexp m gc g μ) (hgc_int : integrable gc μ) (hg_int : integrable g μ) :
  fc ≤ᵐ[μ] gc :=
begin
  suffices h_sub : (fc-gc) ≤ᵐ[μ] 0,
    from (h_sub.mono (λ x hx, by rwa [pi.sub_apply, pi.zero_apply, sub_nonpos] at hx)),
  have h_sub_fg : f - g ≤ᵐ[μ] 0,
    from hfg.mono (λ x hx, by rwa [pi.sub_apply, pi.zero_apply, sub_nonpos]),
  have h_sub_condexp : is_condexp m (fc - gc) (f-g) μ,
    from is_condexp.sub hf hg hfc_int hf_int hgc_int hg_int,
  exact is_condexp.nonpos hm h_sub_fg h_sub_condexp (hfc_int.sub hgc_int),
end

variables (𝕂)
lemma is_condexp.unique (hm : m ≤ m0) [borel_space 𝕂] {f₁ f₂ g : α → E'} (hf₁ : is_condexp m f₁ g μ)
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
  refine @ae_eq_of_forall_set_integral_eq α E' 𝕂 _ _ _ _ _ _ _ _ _ m _ _ _ _ _ _ _,
  { exact integrable_trim_of_measurable hm h_meas₁ h_int₁', },
  { exact integrable_trim_of_measurable hm h_meas₂ h_int₂', },
  { intros s hs,
    specialize h s hs,
    rwa [set_integral_trim hm _ h_meas₁ h_int₁' hs,
      set_integral_trim hm _ h_meas₂ h_int₂' hs] at h, },
end
variables {𝕂}

lemma is_condexp.le_abs (hm : m ≤ m0) {f f_abs g : α → ℝ} (hfg : is_condexp m f g μ)
  (hfg_abs : is_condexp m f_abs (λ x, abs (g x)) μ) (hf : integrable f μ) (hg : integrable g μ)
  (hf_abs : integrable f_abs μ) :
  f ≤ᵐ[μ] f_abs :=
is_condexp.mono hm (eventually_of_forall (λ x, le_abs_self (g x))) hfg hf hg hfg_abs hf_abs
  (by { simp_rw [← real.norm_eq_abs], rwa integrable_norm_iff hg.1, })

/-- Replace this with a full statement of Jensen's inequality once we have the convexity results. -/
lemma is_condexp.jensen_norm (hm : m ≤ m0) {f f_abs g : α → ℝ} (hfg : is_condexp m f g μ)
  (hfg_abs : is_condexp m f_abs (λ x, abs (g x)) μ) (hf : integrable f μ) (hg : integrable g μ)
  (hf_abs : integrable f_abs μ) :
  ∀ᵐ x ∂μ, ∥f x∥ ≤ f_abs x :=
begin
  simp_rw [real.norm_eq_abs, abs_le],
  refine eventually.and _ (is_condexp.le_abs hm hfg hfg_abs hf hg hf_abs),
  simp_rw neg_le,
  refine is_condexp.le_abs hm hfg.neg _ hf.neg hg.neg hf_abs,
  simp_rw [pi.neg_apply, abs_neg],
  exact hfg_abs,
end

end is_condexp_properties

lemma ennreal.one_le_two : (1 : ℝ≥0∞) ≤ 2 := ennreal.coe_le_coe.2 (show (1 : ℝ≥0) ≤ 2, by norm_num)

section condexp_L2_clm

variables [borel_space 𝕂] {m m0 : measurable_space α} {μ : measure α}

variables (𝕂)
/-- Conditional expectation of a function in L2 with respect to a sigma-algebra -/
def condexp_L2_clm [complete_space E] (hm : m ≤ m0) :
  (α →₂[μ] E) →L[𝕂] (Lp_sub E 𝕂 m 2 μ) :=
@orthogonal_projection 𝕂 (α →₂[μ] E) _ _ (Lp_sub E 𝕂 m 2 μ)
  (by { haveI : fact (m ≤ m0) := ⟨hm⟩, exact infer_instance, })
variables {𝕂}

/-- Without a finiteness hypothesis on the measure, the integral of `condexp_L2 𝕂 hm f - f` on a
`m`-measurable set `s` is equal to 0 if `μ s < ∞`. -/
lemma integral_condexp_L2_sub_eq_of_measure_finite (hm : m ≤ m0) {f : Lp E' 2 μ} {s : set α}
  (hs : @measurable_set α m s) (hμs : μ s < ∞) :
  ∫ x in s, (condexp_L2_clm 𝕂 hm f x - f x) ∂μ = 0 :=
begin
  rw [← neg_eq_zero, ← integral_neg],
  simp_rw neg_sub,
  haveI : fact (m ≤ m0) := ⟨hm⟩,
  have h_inner_zero : ∀ (g : Lp E' 2 μ) (hg : g ∈ Lp_sub E' 𝕂 m 2 μ),
      inner (f - condexp_L2_clm 𝕂 hm f) g = (0 : 𝕂),
    from λ g hg, orthogonal_projection_inner_eq_zero f g hg,
  by_cases h_int_on : integrable (f - condexp_L2_clm 𝕂 hm f) (μ.restrict s),
  swap, { simp_rw ← pi.sub_apply f, rw integral_undef h_int_on, },
  refine integral_zero_of_forall_integral_inner_zero _ h_int_on _,
  intro c,
  specialize h_inner_zero (indicator_Lp 2 (hm s hs) c (or.inr hμs)) (mem_Lp_sub_indicator_Lp hm hs),
  rw [inner_eq_zero_sym, inner_indicator_Lp] at h_inner_zero,
  rw ← h_inner_zero,
  refine set_integral_congr_ae (hm s hs) _,
  refine (Lp.coe_fn_sub f (condexp_L2_clm 𝕂 hm f)).mono (λ x hx hxs, _),
  congr,
  rw [hx, pi.sub_apply, Lp_sub_coe],
end

lemma is_average_finite_condexp_L2 (hm : m ≤ m0) {f : Lp E' 2 μ} :
  is_average_finite m (condexp_L2_clm 𝕂 hm f) f μ :=
λ s hs hμs, integral_condexp_L2_sub_eq_of_measure_finite hm hs hμs

lemma is_condexp'_condexp_L2 (hm : m ≤ m0) [finite_measure μ] (f : Lp E' 2 μ) :
  is_condexp' m ((condexp_L2_clm 𝕂 hm f) : α → E') f μ :=
begin
  refine ⟨Lp_sub.ae_measurable' (condexp_L2_clm 𝕂 hm f), λ s hs, _⟩,
  have hμs : μ s < ∞, from measure_lt_top μ s,
  exact integral_condexp_L2_sub_eq_of_measure_finite hm hs hμs,
end

/-- Without a finiteness hypothesis on the measure, the integral of `condexp_L2` on a `m`-measurable
set `s` is equal to the integral of `f` on `s` if `μ s < ∞`. -/
lemma integral_condexp_L2_eq_of_measure_finite (hm : m ≤ m0) {f : Lp E' 2 μ}
  (hf_int : integrable f μ) (h_condexp_int : integrable (condexp_L2_clm 𝕂 hm f) μ) {s : set α}
  (hs : @measurable_set α m s) (hμs : μ s < ∞) :
  ∫ x in s, condexp_L2_clm 𝕂 hm f x ∂μ = ∫ x in s, f x ∂μ :=
begin
  haveI : fact (m ≤ m0) := ⟨hm⟩,
  have h_inner_zero : ∀ (g : Lp E' 2 μ) (hg : g ∈ Lp_sub E' 𝕂 m 2 μ),
      inner (f - condexp_L2_clm 𝕂 hm f) g = (0 : 𝕂),
    from λ g hg, orthogonal_projection_inner_eq_zero f g hg,
  suffices h_sub : ∫ a in s, (f a - condexp_L2_clm 𝕂 hm f a) ∂μ = 0,
  { rw [integral_sub (hf_int.restrict s) (h_condexp_int.restrict s), sub_eq_zero] at h_sub,
    exact h_sub.symm, },
  refine integral_zero_of_forall_integral_inner_zero _ ((hf_int.sub h_condexp_int).restrict s) _,
  intro c,
  specialize h_inner_zero (indicator_Lp 2 (hm s hs) c (or.inr hμs)) (mem_Lp_sub_indicator_Lp hm hs),
  rw [inner_eq_zero_sym, inner_indicator_Lp] at h_inner_zero,
  rw ← h_inner_zero,
  refine set_integral_congr_ae (hm s hs) _,
  refine (Lp.coe_fn_sub f (condexp_L2_clm 𝕂 hm f)).mono (λ x hx hxs, _),
  congr,
  rw [hx, pi.sub_apply, Lp_sub_coe],
end

lemma is_condexp_condexp_L2 (hm : m ≤ m0) [finite_measure μ] (f : Lp E' 2 μ) :
  is_condexp m ((condexp_L2_clm 𝕂 hm f) : α → E') f μ :=
begin
  have hf_int : integrable f μ, from Lp.integrable f ennreal.one_le_two,
  have h_condexp_int : integrable (condexp_L2_clm 𝕂 hm f) μ,
    from Lp.integrable (condexp_L2_clm 𝕂 hm f) ennreal.one_le_two,
  exact (is_condexp_iff_is_condexp'_of_integrable h_condexp_int hf_int).mpr
    (is_condexp'_condexp_L2 hm f),
end

end condexp_L2_clm

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
variables (𝕂)
def L1s_to_L2_lm [opens_measurable_space 𝕂] : (α →₁ₛ[μ] E) →ₗ[𝕂] (α →₂[μ] E) :=
{ to_fun := λ f, mem_ℒp.to_Lp f (mem_ℒ2_simple_func_L1 f),
  map_add' := L1s_to_L2_add,
  map_smul' := L1s_to_L2_smul, }
variables {𝕂}


lemma L1s_to_L2_coe_fn [opens_measurable_space 𝕂] (f : α →₁ₛ[μ] E) : L1s_to_L2_lm 𝕂 f =ᵐ[μ] f :=
mem_ℒp.coe_fn_to_Lp _

lemma integrable_L1s_to_L2 [opens_measurable_space 𝕂] (f : α →₁ₛ[μ] E) :
  integrable (L1s_to_L2_lm 𝕂 f) μ :=
(integrable_congr (L1s_to_L2_coe_fn f)).mpr (L1.integrable_coe_fn _)

/-- Linear map coercing a simple function of L1 to the subspace of integrable functions of L2. -/
def L1s_to_L2_integrable_lm [opens_measurable_space 𝕂] : (α →₁ₛ[μ] E) →ₗ[𝕂] (L2_integrable E 𝕂 μ) :=
{ to_fun := λ f, ⟨mem_ℒp.to_Lp f (mem_ℒ2_simple_func_L1 f),
    mem_L2_integrable_iff_integrable.mpr (integrable_L1s_to_L2 _)⟩,
  map_add' := λ f g,
    by { ext1, simp only [submodule.coe_add, submodule.coe_mk], exact L1s_to_L2_add f g, },
  map_smul' :=  λ c f,
    by { ext1, simp only [submodule.coe_smul, submodule.coe_mk], exact L1s_to_L2_smul c f, }, }

lemma L1s_to_L2_integrable_coe_fn [opens_measurable_space 𝕂] (f : α →₁ₛ[μ] E) :
  L1s_to_L2_integrable_lm f =ᵐ[μ] f :=
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
  have h_univ_pow_pos : 0 < (μ set.univ ^ (1 / (2 : ℝ))).to_real,
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
  ((condexp_L2_clm 𝕂 hm).to_linear_map.comp (L1s_to_L2_lm 𝕂)))

lemma condexp_L1s_lm_neg (f : α →₁ₛ[μ] E) : condexp_L1s_lm 𝕂 hm (-f) = -condexp_L1s_lm 𝕂 hm f :=
linear_map.map_neg (condexp_L1s_lm 𝕂 hm) f
variables {𝕂}

lemma condexp_L1s_ae_eq_condexp_L2 (f : α →₁ₛ[μ] E) :
  condexp_L1s_lm 𝕂 hm f =ᵐ[μ] condexp_L2_clm 𝕂 hm (L1s_to_L2_lm 𝕂 f) :=
(L2_to_L1_coe_fn _).trans (by refl)

lemma is_condexp_condexp_L2_L1s_to_L2 (f : α →₁ₛ[μ] E') :
  is_condexp m (condexp_L2_clm 𝕂 hm (L1s_to_L2_lm 𝕂 f) : α → E') f μ :=
is_condexp_congr_ae_right' hm (L1s_to_L2_coe_fn f) (is_condexp_condexp_L2 hm _)

lemma is_condexp'_condexp_L2_L1s_to_L2 (f : α →₁ₛ[μ] E') :
  is_condexp' m (condexp_L2_clm 𝕂 hm (L1s_to_L2_lm 𝕂 f) : α → E') f μ :=
is_condexp'_congr_ae_right' hm (L1s_to_L2_coe_fn f) (is_condexp'_condexp_L2 hm _)

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

lemma condexp_L1s_nonneg {f : α →₁ₛ[μ] ℝ} (hf : 0 ≤ᵐ[μ] f) : 0 ≤ᵐ[μ] condexp_L1s_lm ℝ hm f :=
is_condexp.nonneg hm hf (is_condexp_condexp_L1s ℝ hm f) (Lp.integrable _ le_rfl)

lemma condexp_L1s_nonpos {f : α →₁ₛ[μ] ℝ} (hf : f ≤ᵐ[μ] 0) : condexp_L1s_lm ℝ hm f ≤ᵐ[μ] 0 :=
is_condexp.nonpos hm hf (is_condexp_condexp_L1s ℝ hm f) (Lp.integrable _ le_rfl)

lemma condexp_L1s_mono {f g : α →₁ₛ[μ] ℝ} (hfg : f ≤ᵐ[μ] g) :
  condexp_L1s_lm ℝ hm f ≤ᵐ[μ] condexp_L1s_lm ℝ hm g :=
is_condexp.mono hm hfg (is_condexp_condexp_L1s ℝ hm f) (Lp.integrable _ le_rfl)
  (Lp.integrable _ le_rfl) (is_condexp_condexp_L1s ℝ hm g) (Lp.integrable _ le_rfl)
  (Lp.integrable _ le_rfl)

lemma condexp_L1s_R_jensen_norm (f : α →₁ₛ[μ] ℝ) :
  ∀ᵐ x ∂μ, ∥condexp_L1s_lm ℝ hm f x∥
    ≤ condexp_L1s_lm ℝ hm (L1.simple_func.map (λ x, ∥x∥) f norm_zero) x :=
begin
  have h := is_condexp_congr_ae_right' hm (L1.simple_func.map_coe (λ (x : ℝ), ∥x∥) f norm_zero)
    (is_condexp_condexp_L1s ℝ hm (L1.simple_func.map (λ (x : ℝ), ∥x∥) f norm_zero)),
  exact is_condexp.jensen_norm hm (is_condexp_condexp_L1s ℝ hm f) h
      (Lp.integrable _ le_rfl) (Lp.integrable _ le_rfl) (Lp.integrable _ le_rfl),
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

lemma norm_condexp_L1s_indicator_L1s_R_le {s : set α} (hs : measurable_set s)
  (c : ℝ) (hμsc : c = 0 ∨ μ s < ∞) :
  ∥condexp_L1s_lm ℝ hm (indicator_L1s hs c hμsc)∥ ≤ ∥c∥ * (μ s).to_real :=
(norm_condexp_L1s_le_R hm _).trans norm_indicator_L1s.le

end condexp_L1s_ℝ


section condexp_def

variables {m m0 : measurable_space α} (hm : m ≤ m0) {μ : measure α}

variables (𝕂)
include 𝕂 hm
lemma is_condexp_ℝ_smul_const {s : set α} (hs : measurable_set s) (c : E') (hμs : μ s < ∞)
  {f_ind : α → ℝ} (h_condexp : is_condexp m f_ind (indicator_L1s hs (1 : ℝ) (or.inr hμs)) μ) :
  is_condexp m (λ x, f_ind x • c) (indicator_L1s hs c (or.inr hμs)) μ :=
begin
  obtain ⟨h_meas, h_int_eq₁⟩ := h_condexp,
  refine ⟨ae_measurable'.smul_const h_meas c, λ t ht, _⟩,
  have h_smul : ∫ a in t, (indicator_L1s hs c (or.inr hμs)) a ∂μ
      = ∫ a in t, ((indicator_L1s hs (1 : ℝ) (or.inr hμs)) a) • c ∂μ,
    from set_integral_congr_ae (hm t ht) ((indicator_L1s_eq_smul c hμs).mono (λ x hx hxs, hx)),
  refine eq.trans _ h_smul.symm,
  rw [integral_smul_const, integral_smul_const, h_int_eq₁ t ht],
end
omit 𝕂 hm

lemma is_condexp.smul_const {f g : α → ℝ} (hfg : is_condexp m f g μ) (c : G') :
  is_condexp m (λ x, f x • c) (λ x, g x • c) μ :=
⟨ae_measurable'.smul_const hfg.1 c, λ s hs,
  by rw [integral_smul_const, integral_smul_const, hfg.2 s hs]⟩

lemma right_of_or_not_left {p q : Prop} (h_or : p ∨ q) (h_not : ¬p) : q :=
begin
  cases h_or,
  { exact absurd h_or h_not, },
  { exact h_or, },
end

def piece (f : α →₁ₛ[μ] G) (y : G) : α →₁ₛ[μ] G :=
  indicator_L1s (L1.simple_func.measurable_set_fiber f y) y
    (L1.simple_func.zero_or_finite_fiber f y)

lemma piece_eq_indicator_L1s (f : α →₁ₛ[μ] G) (y : G) :
  piece f y = indicator_L1s (L1.simple_func.measurable_set_fiber f y) y
    (L1.simple_func.zero_or_finite_fiber f y) :=
rfl

lemma L1.simple_func_eq_sum_pieces (f : α →₁ₛ[μ] G) :
  f = ∑ y in L1.simple_func.range_nonzero f, piece f y :=
L1.simple_func.simple_func_eq_sum_indicator_L1s f

def L1s_extension_fun [normed_space ℝ G] (T : (α →₁ₛ[μ] ℝ) →L[ℝ] α →₁[μ] ℝ) (f : α →₁ₛ[μ] G) :
  α →₁[μ] G :=
begin
  haveI : decidable_eq G := classical.dec_eq _,
  exact ∑ y in L1.simple_func.range_nonzero f,
    dite (y = 0) (λ h, (0 : α→₁[μ] G))
    (λ h, L1.indicator_fun_smul_const (T
      (indicator_L1s (L1.simple_func.measurable_set_fiber f y) (1 : ℝ)
        (or.inr (L1.simple_func.finite_fiber f y h)))) y)
end

lemma L1s_extension_fun_def [normed_space ℝ G] [decidable_eq G]
  (T : (α →₁ₛ[μ] ℝ) →L[ℝ] α →₁[μ] ℝ) (f : α →₁ₛ[μ] G) :
  L1s_extension_fun T f = ∑ y in L1.simple_func.range_nonzero f,
    dite (y = 0) (λ h, (0 : α→₁[μ] G))
    (λ h, L1.indicator_fun_smul_const (T
      (indicator_L1s (L1.simple_func.measurable_set_fiber f y) (1 : ℝ)
        (or.inr (L1.simple_func.finite_fiber f y h)))) y) :=
by { simp only [L1s_extension_fun], congr, ext1 y, congr, }

lemma finset.eq_empty_or_singleton_of_subset_singleton (s : finset γ) (c : γ) (hsc : s ⊆ {c}) :
  s = ∅ ∨ s = {c} :=
begin
  by_cases h_empty : s = ∅,
  { exact or.inl h_empty, },
  right,
  refine finset.subset.antisymm hsc _,
  rw finset.eq_empty_iff_forall_not_mem at h_empty,
  push_neg at h_empty,
  obtain ⟨y, hy⟩ := h_empty,
  have hyc : y = c, from finset.mem_singleton.mp (finset.mem_of_subset hsc hy),
  rw hyc at hy,
  intros y0 hy0,
  rw finset.mem_singleton at hy0,
  rwa hy0,
end

@[simp] lemma L1s_extension_fun_zero [normed_space ℝ G] (T : (α →₁ₛ[μ] ℝ) →L[ℝ] α →₁[μ] ℝ) :
  L1s_extension_fun T (0 : α →₁ₛ[μ] G) = 0 :=
by { rw [L1s_extension_fun, L1.simple_func.range_nonzero_zero, finset.sum_empty], }

lemma L1s_extension_indicator_of_ne_zero [normed_space ℝ G] (T : (α →₁ₛ[μ] ℝ) →L[ℝ] α →₁[μ] ℝ)
  {s : set α} (hs : measurable_set s) (hμs : μ s < ∞) (c : G) (hc0 : c ≠ 0) :
  L1s_extension_fun T (indicator_L1s hs c (or.inr hμs)) =
    L1.indicator_fun_smul_const (T (indicator_L1s hs (1 : ℝ) (or.inr hμs))) c :=
begin
  by_cases hμs0 : μ s = 0,
  { simp_rw L1.simple_func.indicator_L1s_set_measure_zero hμs0, simp, },
  rw ← ne.def at hμs0,
  have hμs_pos : 0 < μ s, from lt_of_le_of_ne (zero_le _) hμs0.symm,
  rw L1s_extension_fun,
  rw L1.simple_func.range_nonzero_indicator_L1s_eq hs c (or.inr hμs) hμs_pos hc0,
  rw finset.sum_singleton,
  simp only [hc0, dif_neg, not_false_iff],
  congr' 2,
  exact L1.simple_func.indicator_L1s_congr_ae _ _ _ _ _
    (L1.simple_func.indicator_L1s_fiber_ae_eq_self hs c (or.inr hμs) hc0),
end

--lemma L1.simple_func.nmem_range_add_iff (f g : α →₁ₛ[μ] G) [decidable_eq G] (y : G) (hμ : μ ≠ 0) :
--  y ∉ (to_simple_func (f + g)).range ↔ μ ((to_simple_func f + to_simple_func g) ⁻¹' {y}) = 0 :=
--begin
--  have h_add_ae : ⇑f + ⇑g =ᵐ[μ] to_simple_func f + to_simple_func g,
--  { exact (eventually_eq.add (L1.simple_func.to_simple_func_eq_to_fun _)
--      (L1.simple_func.to_simple_func_eq_to_fun _)).symm, },
--  rw [L1.simple_func.to_simple_func_mem_range_iff _ hμ,
--    measure_congr (L1.simple_func.preimage_congr_ae (L1.simple_func.coe_fn_add _ _) _),
--    measure_congr (L1.simple_func.preimage_congr_ae h_add_ae _), not_not],
--end

--lemma L1.simple_func.range_add_subset_add_range (f g : α →₁ₛ[μ] G) [decidable_eq G] :
--  (to_simple_func (f + g)).range ⊆ (to_simple_func f).range + (to_simple_func g).range :=
--finset.subset.trans (L1.simple_func.range_add_subset f g)
--  (simple_func.range_add_subset_add_range _ _)

lemma add_sum (op : (α →₁ₛ[μ] F') → γ) [add_comm_monoid γ]
  (h_op_add : ∀ (f : α →₁ₛ[μ] F') (s : set α) (hs : measurable_set s) (cs : F')
    (hμs : cs = 0 ∨ μ s < ∞),
    op (f + indicator_L1s hs cs hμs) = op f + op (indicator_L1s hs cs hμs))
  (sF' : finset F') (S : F' → set α) (hS : ∀ y, measurable_set (S y)) (cS : F' → F')
  (hμS : ∀ y, cS y = 0 ∨ μ (S y) < ∞)
  (f : α →₁ₛ[μ] F') :
  op (f + ∑ y in sF', indicator_L1s (hS y) (cS y) (hμS y))
    = op f + ∑ y in sF', op (indicator_L1s (hS y) (cS y) (hμS y)) :=
begin
  classical,
  refine finset.induction _ _ sF',
  { simp, },
  intros y s hys hops,
  rw [finset.sum_insert hys, add_comm (indicator_L1s (hS y) (cS y) (hμS y)), ← add_assoc, h_op_add,
    hops, finset.sum_insert hys, add_comm ( op (indicator_L1s (hS y) (cS y) (hμS y))), ← add_assoc],
end

lemma to_simple_func_add_indicator_L1s_disjoint (s : set α) (hs : measurable_set s) (cs : F')
  (hμsc : cs = 0 ∨ μ s < ∞) (t : set α) (ht : measurable_set t) (ct : F')
  (hμtc : ct = 0 ∨ μ t < ∞) (hst : disjoint s t) :
  to_simple_func (indicator_L1s hs cs hμsc + indicator_L1s ht ct hμtc)
    = to_simple_func (indicator_L1s hs cs hμsc) + to_simple_func (indicator_L1s ht ct hμtc) :=
begin
  by_cases hμs_eq_zero : μ s = 0,
  { rw L1.simple_func.indicator_L1s_set_measure_zero hμs_eq_zero,
    rw L1.simple_func.to_simple_func_zero,
    simp_rw zero_add, },
  rw ← ne.def at hμs_eq_zero,
  have hμs_pos : 0 < μ s, from lt_of_le_of_ne (zero_le _) hμs_eq_zero.symm,
  by_cases hμt_eq_zero : μ t = 0,
  { rw L1.simple_func.indicator_L1s_set_measure_zero hμt_eq_zero,
    rw L1.simple_func.to_simple_func_zero,
    simp_rw add_zero, },
  rw ← ne.def at hμt_eq_zero,
  have hμt_pos : 0 < μ t, from lt_of_le_of_ne (zero_le _) hμt_eq_zero.symm,
  rw L1.simple_func.to_simple_func_indicator hs cs hμsc hμs_pos,
  rw L1.simple_func.to_simple_func_indicator ht ct hμtc hμt_pos,
  rw L1.simple_func.to_simple_func_def,
  sorry,
end

lemma op_eq_sum_op_pieces (op : (α →₁ₛ[μ] F') → γ) [add_comm_monoid γ]
  (h_op_add : ∀ (f : α →₁ₛ[μ] F') (s : set α) (hs : measurable_set s) (cs : F')
    (hμs : cs = 0 ∨ μ s < ∞),
    op (f + indicator_L1s hs cs hμs) = op f + op (indicator_L1s hs cs hμs))
  (h_op_zero : op 0 = 0)
  (f : α →₁ₛ[μ] F') :
  op f = ∑ y in (L1.simple_func.range_nonzero f), op (piece f y) :=
begin
  nth_rewrite 0 L1.simple_func_eq_sum_pieces f,
  suffices h_zero_add : op (0 + ∑ (y : F') in (L1.simple_func.range_nonzero f), piece f y)
    = op 0 + ∑ (y : F') in (L1.simple_func.range_nonzero f), op (piece f y),
  { rwa [zero_add, h_op_zero, zero_add] at h_zero_add, },
  simp_rw piece_eq_indicator_L1s,
  rw add_sum op h_op_add,
end

lemma add_of_indicator_add (op : (α →₁ₛ[μ] F') → γ) [add_comm_monoid γ]
  (h_op_add : ∀ (f : α →₁ₛ[μ] F') (s : set α) (hs : measurable_set s) (cs : F')
    (hμs : cs = 0 ∨ μ s < ∞),
    op (f + indicator_L1s hs cs hμs) = op f + op (indicator_L1s hs cs hμs))
  (h_op_zero : op 0 = 0)
  (f g : α →₁ₛ[μ] F') :
  op (f + g) = op f + op g :=
begin
  nth_rewrite 0 L1.simple_func_eq_sum_pieces g,
  simp_rw piece_eq_indicator_L1s,
  rw add_sum op h_op_add,
  rw op_eq_sum_op_pieces op h_op_add h_op_zero g,
  simp_rw piece_eq_indicator_L1s,
end

--lemma to_simple_func_add_indicator_of_disjoint [decidable_eq G'] (f : α →₁ₛ[μ] G') (s : set α)
--  (hs : measurable_set s) (c : G') (hμsc : c = 0 ∨ μ s < ∞)
--  (hs_disj : ∀ y ∈ (to_simple_func f).range, disjoint s (to_simple_func f ⁻¹' {y})) :
--  ∃ (t : set α) (ht : measurable_set t) (hst : s =ᵐ[μ] t),
--  to_simple_func (f + indicator_L1s hs c hμsc) = to_simple_func f + indicator_simple_func ht c :=
--begin
--  sorry,
--end

lemma ennreal.eq_zero_or_pos (x : ℝ≥0∞) : x = 0 ∨ 0 < x := sorry

lemma finset.disjoint_iff [decidable_eq γ] (s t : finset γ) : disjoint s t ↔ s ∩ t ⊆ ∅ := iff.rfl

lemma L1s_extension_fun_add_indicator_L1s_of_disjoint_of_nmem (T : (α →₁ₛ[μ] ℝ) →L[ℝ] α →₁[μ] ℝ)
  (f : α →₁ₛ[μ] G') (s : set α) (hs : measurable_set s) (c : G') (hμsc : c = 0 ∨ μ s < ∞)
  (hs_disj : ∀ y ≠ 0, disjoint (f ⁻¹' {y}) s) (hc0 : c ≠ 0) (hμs : 0 < μ s)
  (hc_nmem : c ∉ L1.simple_func.range_nonzero f) :
  L1s_extension_fun T (f + indicator_L1s hs c hμsc)
    = L1s_extension_fun T f + L1s_extension_fun T (indicator_L1s hs c hμsc) :=
begin
  classical,
  simp_rw L1s_extension_fun_def T,
  rw [L1.simple_func.range_nonzero_add_indicator_of_disjoint f hs c hμsc hs_disj,
    L1.simple_func.range_nonzero_indicator_L1s_eq hs c hμsc hμs hc0, finset.sum_singleton,
    finset.sum_union],
  swap,
  { rw finset.disjoint_iff,
    intros x hx,
    rw [finset.mem_inter, finset.mem_singleton] at hx,
    cases hx with hx hx_eq_c,
    rw hx_eq_c at hx,
    exact absurd hx hc_nmem, },
  rw finset.sum_singleton, -- it looks like rfl in the goal view, but preimages in _ are different.
  have h_preim_f_add : ∀ x ∈ L1.simple_func.range_nonzero f,
    ⇑(f + indicator_L1s hs c hμsc) ⁻¹' {x} =ᵐ[μ] f ⁻¹' {x},
  { sorry, },
  have h_preim_f_add_c : ⇑(f + indicator_L1s hs c hμsc) ⁻¹' {c}
    =ᵐ[μ] (indicator_L1s hs c hμsc) ⁻¹' {c},
  { sorry, },
  sorry,
end

lemma L1s_extension_fun_add_indicator_L1s_of_disjoint_of_mem (T : (α →₁ₛ[μ] ℝ) →L[ℝ] α →₁[μ] ℝ)
  (f : α →₁ₛ[μ] G') (s : set α) (hs : measurable_set s) (c : G') (hμsc : c = 0 ∨ μ s < ∞)
  (hs_disj : ∀ y ≠ 0, disjoint (f ⁻¹' {y}) s) (hc0 : c ≠ 0) (hμs : 0 < μ s)
  (hc_nmem : c ∈ L1.simple_func.range_nonzero f) :
  L1s_extension_fun T (f + indicator_L1s hs c hμsc)
    = L1s_extension_fun T f + L1s_extension_fun T (indicator_L1s hs c hμsc) :=
begin
  classical,
  simp_rw L1s_extension_fun_def T,
  rw [L1.simple_func.range_nonzero_add_indicator_of_disjoint f hs c hμsc hs_disj,
    L1.simple_func.range_nonzero_indicator_L1s_eq hs c hμsc hμs hc0, finset.sum_singleton],
  have h_union_eq : L1.simple_func.range_nonzero f ∪ {c} = L1.simple_func.range_nonzero f,
  { sorry, },
  sorry,
end

lemma L1s_extension_fun_add_indicator_L1s_of_disjoint (T : (α →₁ₛ[μ] ℝ) →L[ℝ] α →₁[μ] ℝ)
  (f : α →₁ₛ[μ] G') (s : set α) (hs : measurable_set s) (c : G') (hμsc : c = 0 ∨ μ s < ∞)
  (hs_disj : ∀ y ≠ 0, disjoint (f ⁻¹' {y}) s) :
  L1s_extension_fun T (f + indicator_L1s hs c hμsc)
    = L1s_extension_fun T f + L1s_extension_fun T (indicator_L1s hs c hμsc) :=
begin
  classical,
  by_cases hc0 : c = 0,
  { simp_rw [hc0, L1.simple_func.indicator_L1s_zero, L1s_extension_fun_zero, add_zero], },
  cases ennreal.eq_zero_or_pos (μ s) with hμs hμs,
  { simp_rw [L1.simple_func.indicator_L1s_set_measure_zero hμs, L1s_extension_fun_zero,
      add_zero], },
  by_cases hc_mem : c ∈ L1.simple_func.range_nonzero f,
  { exact L1s_extension_fun_add_indicator_L1s_of_disjoint_of_mem T f s hs c hμsc hs_disj hc0 hμs
      hc_mem, },
  { exact L1s_extension_fun_add_indicator_L1s_of_disjoint_of_nmem T f s hs c hμsc hs_disj hc0 hμs
      hc_mem, },
end

lemma L1s_extension_fun_add_indicator_L1s_of_subset (T : (α →₁ₛ[μ] ℝ) →L[ℝ] α →₁[μ] ℝ)
  (f : α →₁ₛ[μ] G') (s : set α) (hs : measurable_set s) (c : G') (hμsc : c = 0 ∨ μ s < ∞)
  (hs_subset : ∃ y ∈ (L1.simple_func.range_nonzero f), s ⊆ (to_simple_func f ⁻¹' {y})) :
  L1s_extension_fun T (f + indicator_L1s hs c hμsc)
    = L1s_extension_fun T f + L1s_extension_fun T (indicator_L1s hs c hμsc) :=
begin
  classical,
  rcases hs_subset with ⟨ys, hys, hs_subset⟩,
  have h_eq_sum : indicator_L1s hs c hμsc = ∑ y in L1.simple_func.range_nonzero f,
    ite (ys = y) (indicator_L1s hs c hμsc) 0,
  { rw finset.sum_ite_eq,
    simp [hys], },
  nth_rewrite 0 L1.simple_func_eq_sum_pieces f,
  nth_rewrite 0 h_eq_sum,
  rw ← finset.sum_add_distrib,
  classical,
  have h_eq_sum' : L1s_extension_fun T (indicator_L1s hs c hμsc)
    = ∑ y in L1.simple_func.range_nonzero f,
      ite (ys = y) (L1s_extension_fun T (indicator_L1s hs c hμsc)) 0,
  { rw finset.sum_ite_eq,
    simp [hys], },
  rw L1s_extension_fun_def T f,
  rw h_eq_sum',
  rw ← finset.sum_add_distrib,
  sorry,
end

lemma L1s_extension_fun_add_indicator_L1s (T : (α →₁ₛ[μ] ℝ) →L[ℝ] α →₁[μ] ℝ) (f : α →₁ₛ[μ] G')
  (s : set α) (hs : measurable_set s) (c : G') (hμsc : c = 0 ∨ μ s < ∞) :
  L1s_extension_fun T (f + indicator_L1s hs c hμsc)
    = L1s_extension_fun T f + L1s_extension_fun T (indicator_L1s hs c hμsc) :=
begin
  by_cases hc0 : c = 0,
  { simp_rw [hc0, L1.simple_func.indicator_L1s_zero μ _, add_zero],
    rw [L1s_extension_fun_zero T, add_zero], },
  classical,
  have hμs := right_of_or_not_left hμsc hc0,
  rw L1s_extension_indicator_of_ne_zero T hs hμs c hc0,
  rw L1s_extension_fun,
  rw L1s_extension_fun,
  sorry,
end

lemma L1s_extension_fun_add (T : (α →₁ₛ[μ] ℝ) →L[ℝ] α →₁[μ] ℝ)
  (f g : α →₁ₛ[μ] G') :
  L1s_extension_fun T (f + g) = L1s_extension_fun T f + L1s_extension_fun T g :=
begin
  refine add_of_indicator_add (L1s_extension_fun T) _ (L1s_extension_fun_zero T) _ _,
  exact L1s_extension_fun_add_indicator_L1s T,
end

def L1s_extension_hom (T : (α →₁ₛ[μ] ℝ) →L[ℝ] α →₁[μ] ℝ) :
  (α →₁ₛ[μ] G') →+ (α →₁[μ] G') :=
{ to_fun := L1s_extension_fun T,
  map_zero' := L1s_extension_fun_zero T,
  map_add' := L1s_extension_fun_add T, }

lemma L1s_extension_fun_smul_indicator_L1s [borel_space 𝕂] [smul_comm_class 𝕂 ℝ F']
  (T : (α →₁ₛ[μ] ℝ) →L[ℝ] α →₁[μ] ℝ)
  {s : set α} (hs : measurable_set s) (x : F') (hμsx : x = 0 ∨ μ s < ∞) (c : 𝕂) :
  L1s_extension_fun T (c • (indicator_L1s hs x hμsx))
    = c • L1s_extension_fun T (indicator_L1s hs x hμsx) :=
begin
  rw const_smul_indicator_L1s,
  by_cases hx0 : x = 0,
  { simp_rw [hx0, smul_zero, L1.simple_func.indicator_L1s_zero, L1s_extension_fun_zero,
      smul_zero], },
  by_cases hc0 : c = 0,
  { simp_rw [hc0, zero_smul, L1.simple_func.indicator_L1s_zero, L1s_extension_fun_zero], },
  have hcx : c • x ≠ 0, from smul_ne_zero.mpr ⟨hc0, hx0⟩,
  have hμs := right_of_or_not_left hμsx hx0,
  rw [L1s_extension_indicator_of_ne_zero T hs hμs (c • x) hcx,
    L1s_extension_indicator_of_ne_zero T hs hμs x hx0, const_smul_indicator_fun_smul_const],
end

lemma L1s_extension_fun_smul [borel_space 𝕂] [smul_comm_class 𝕂 ℝ F']
  (T : (α →₁ₛ[μ] ℝ) →L[ℝ] α →₁[μ] ℝ) (c : 𝕂) (f : α →₁ₛ[μ] F') :
  L1s_extension_fun T (c • f) = c • L1s_extension_fun T f :=
begin
  change L1s_extension_hom T (c • f) = c • L1s_extension_hom T f,
  rw [L1.simple_func.simple_func_eq_sum_indicator_L1s f, finset.smul_sum],
  simp_rw @add_monoid_hom.map_sum F' (α →₁ₛ[μ] F') (α →₁[μ] F') _ _ (L1s_extension_hom T) _
    (L1.simple_func.range_nonzero f),
  rw finset.smul_sum,
  congr,
  ext1 x,
  exact L1s_extension_fun_smul_indicator_L1s 𝕂 T _ x _ c,
end

variables (F')
def L1s_extension_lm [borel_space 𝕂] [smul_comm_class 𝕂 ℝ F'] (T : (α →₁ₛ[μ] ℝ) →L[ℝ] α →₁[μ] ℝ) :
  (α →₁ₛ[μ] F') →ₗ[𝕂] (α →₁[μ] F') :=
{ to_fun := L1s_extension_fun T,
  map_add' := λ f g, L1s_extension_fun_add T f g,
  map_smul' := λ c f, L1s_extension_fun_smul 𝕂 T c f,  }
variables {F'}

lemma L1s_extension_lm_coe [borel_space 𝕂] [smul_comm_class 𝕂 ℝ F']
  (T : (α →₁ₛ[μ] ℝ) →L[ℝ] α →₁[μ] ℝ) :
  ⇑(L1s_extension_lm F' 𝕂 T) = L1s_extension_fun T :=
rfl

lemma L1s_extension_lm_zero [nonempty α] [borel_space 𝕂] [smul_comm_class 𝕂 ℝ F']
  (T : (α →₁ₛ[μ] ℝ) →L[ℝ] α →₁[μ] ℝ) :
  L1s_extension_lm F' 𝕂 T 0 = 0 :=
by { rw L1s_extension_lm_coe, exact L1s_extension_fun_zero T, }

lemma L1s_extension_indicator [nonempty α] [borel_space 𝕂] (T : (α →₁ₛ[μ] ℝ) →L[ℝ] α →₁[μ] ℝ)
  {s : set α} (hs : measurable_set s) (hμs : μ s < ∞) (c : F') :
  L1s_extension_fun T (indicator_L1s hs c (or.inr hμs)) =
    L1.indicator_fun_smul_const (T (indicator_L1s hs (1 : ℝ) (or.inr hμs))) c :=
begin
  by_cases hc0 : c = 0,
  { rw [hc0, L1.simple_func.indicator_L1s_zero μ hs, L1.indicator_fun_smul_const_zero],
    exact L1s_extension_fun_zero T, },
  exact L1s_extension_indicator_of_ne_zero T hs hμs c hc0,
end

lemma norm_L1s_extension_indicator [nonempty α] [borel_space 𝕂] [smul_comm_class 𝕂 ℝ F']
  (T : (α →₁ₛ[μ] ℝ) →L[ℝ] α →₁[μ] ℝ)
  {s : set α} (hs : measurable_set s) (c : F') (hμsc : c = 0 ∨ μ s < ∞) :
  ∥L1s_extension_lm F' 𝕂 T (indicator_L1s hs c hμsc)∥ ≤ ∥T∥ * ∥indicator_L1s hs c hμsc∥ :=
begin
  by_cases hc : c = 0,
  { simp_rw hc,
    simp_rw L1.simple_func.indicator_L1s_zero,
    rw [L1s_extension_lm_zero, _root_.norm_zero, _root_.norm_zero, mul_zero], },
  have hμs : μ s < ∞, from right_of_or_not_left hμsc hc,
  rw [L1s_extension_lm_coe, L1s_extension_indicator 𝕂 T hs hμs c, norm_def,
    snorm_congr_ae (L1.indicator_fun_smul_const_coe_fn _ c),
    snorm_eq_snorm' one_ne_zero ennreal.coe_ne_top, snorm'],
  simp_rw [ennreal.one_to_real, div_one, ennreal.rpow_one, nnnorm_smul, ennreal.coe_mul],
  rw [lintegral_mul_const _ (Lp.measurable _).nnnorm.ennreal_coe, ennreal.to_real_mul, mul_comm,
    ← of_real_norm_eq_coe_nnnorm, ennreal.to_real_of_real (norm_nonneg _)],
  have hT' := continuous_linear_map.le_op_norm T (indicator_L1s hs (1 : ℝ) (or.inr hμs)),
  rw [norm_def, snorm_eq_snorm' one_ne_zero ennreal.coe_ne_top, snorm'] at hT',
  simp_rw [ennreal.one_to_real, div_one, ennreal.rpow_one] at hT',
  rw [norm_indicator_L1s, real.norm_eq_abs, abs_one, one_mul] at hT',
  rw [norm_indicator_L1s, ← mul_assoc, mul_comm (∥T∥), mul_assoc],
  exact mul_le_mul le_rfl hT' ennreal.to_real_nonneg (norm_nonneg _),
  exact borel_space.opens_measurable,
end

lemma norm_L1s_extension [nonempty α] [borel_space 𝕂] [smul_comm_class 𝕂 ℝ F']
  (T : (α →₁ₛ[μ] ℝ) →L[ℝ] α →₁[μ] ℝ) (f : α →₁ₛ[μ] F') :
  ∥L1s_extension_lm F' 𝕂 T f∥ ≤ ∥T∥ * ∥f∥ :=
begin
  rw [L1.simple_func.norm_eq_integral, simple_func.map_integral _ _ (L1.simple_func.integrable _)],
  swap, { exact norm_zero, },
  nth_rewrite 0 L1.simple_func.simple_func_eq_sum_indicator_L1s f,
  rw linear_map.map_sum,
  rw finset.mul_sum,
  simp_rw measure_congr
    (L1.simple_func.preimage_congr_ae (L1.simple_func.to_simple_func_eq_to_fun f) _),
  have h_restrict_set : ∑ (x : F') in (to_simple_func f).range, ∥T∥ * (μ (f ⁻¹' {x})).to_real • ∥x∥
    = ∑ (x : F') in L1.simple_func.range_nonzero f, ∥T∥ * (μ (f ⁻¹' {x})).to_real • ∥x∥,
  { sorry, },
  rw h_restrict_set,
  refine (norm_sum_le _ _).trans (finset.sum_le_sum (λ x hxf, _)),
  refine (norm_L1s_extension_indicator 𝕂 T _ x _).trans _,
  rw [smul_eq_mul, mul_comm _ (∥x∥), norm_indicator_L1s],
end

variables (F')
def L1s_extension_clm [nonempty α] [borel_space 𝕂] [smul_comm_class 𝕂 ℝ F']
  (T : (α →₁ₛ[μ] ℝ) →L[ℝ] α →₁[μ] ℝ) :
  (α →₁ₛ[μ] F') →L[𝕂] (α →₁[μ] F') :=
{ to_linear_map := L1s_extension_lm F' 𝕂 T,
  cont := linear_map.continuous_of_bound (L1s_extension_lm F' 𝕂 T) (∥T∥)
    (λ f, norm_L1s_extension 𝕂 T f) }
variables {𝕂 F'}

lemma L1s_extension_clm_coe [nonempty α] [borel_space 𝕂] [smul_comm_class 𝕂 ℝ F']
  (T : (α →₁ₛ[μ] ℝ) →L[ℝ] α →₁[μ] ℝ) :
  ⇑(L1s_extension_clm F' 𝕂 T) = L1s_extension_fun T :=
rfl

include hm
lemma is_condexp_L1s_extension_indicator [nonempty α] [borel_space 𝕂] [smul_comm_class 𝕂 ℝ F']
  (T : (α →₁ₛ[μ] ℝ) →L[ℝ] α →₁[μ] ℝ) {s : set α} (hs : measurable_set s)
  (c : F') (hμsc : c = 0 ∨ μ s < ∞) (hT_condexp : ∀ f, is_condexp m (T f) f μ) :
  is_condexp m (L1s_extension_clm F' 𝕂 T (indicator_L1s hs c hμsc))
    (indicator_L1s hs c hμsc) μ :=
begin
  by_cases hc0 : c = 0,
  { simp [hc0, L1.simple_func.indicator_L1s_zero μ hs],
    rw [← L1.simple_func.coe_coe, L1.simple_func.coe_zero,
      is_condexp_congr_ae hm (Lp.coe_fn_zero F' 1 μ) (Lp.coe_fn_zero F' 1 μ)],
    change is_condexp m (λ x, (0 : F')) (λ x, (0 : F')) μ,
    exact is_condexp_const_self _, },
  have hμs : μ s < ∞, from right_of_or_not_left hμsc hc0,
  specialize hT_condexp (indicator_L1s hs (1 : ℝ) (or.inr hμs)),
  refine is_condexp_congr_ae_right' hm (indicator_L1s_eq_smul c hμs).symm _,
  rw [L1s_extension_clm_coe, L1s_extension_indicator 𝕂 T hs hμs],
  swap, { assumption, },
  swap, { assumption, },
  refine is_condexp_congr_ae_left' hm (L1.indicator_fun_smul_const_coe_fn _ c).symm _,
  exact is_condexp.smul_const hT_condexp c,
end
omit hm

include hm
lemma is_condexp_L1s_extension [nonempty α] [borel_space 𝕂] (T : (α →₁ₛ[μ] ℝ) →L[ℝ] α →₁[μ] ℝ)
  (hT_condexp : ∀ f, is_condexp m (T f) f μ) (f : α→₁ₛ[μ] E') :
  is_condexp m (L1s_extension_clm E' 𝕂 T f) f μ :=
begin
  rw L1.simple_func.simple_func_eq_sum_indicator_L1s f,
  rw (L1s_extension_clm E' 𝕂 T).map_sum,
  refine is_condexp_congr_ae' hm
    (Lp.coe_fn_sum _ (L1.simple_func.range_nonzero f)).symm
    (L1.simple_func.coe_finset_sum _ (L1.simple_func.range_nonzero f)).symm _,
  refine is_condexp.sum _ _ (λ i, L1.integrable _) (λ i, L1.integrable _) _,
  exact λ y hy, is_condexp_L1s_extension_indicator hm T _ y _ (λ hμs, hT_condexp _),
end
omit hm

variables [finite_measure μ] [borel_space 𝕂]

variables (𝕂)
lemma condexp_L1s_indicator_L1s_eq {s : set α} (hs : measurable_set s) (hμs : μ s < ∞) (c : E') :
  condexp_L1s_lm 𝕂 hm (indicator_L1s hs c (or.inr hμs)) =ᵐ[μ]
    λ x, (condexp_L1s_lm ℝ hm (indicator_L1s hs (1 : ℝ) (or.inr hμs)) x) • c :=
begin
  refine is_condexp.unique 𝕂 hm (is_condexp_condexp_L1s 𝕂 hm _) (Lp.integrable _ le_rfl) _ _,
  swap,
  { by_cases hc : c = 0,
    { simp [hc], },
    { exact (integrable_smul_const hc).mpr (Lp.integrable _ le_rfl), }, },
  have h_condexp := is_condexp_condexp_L1s ℝ hm (indicator_L1s hs (1 : ℝ) (or.inr hμs)),
  exact is_condexp_ℝ_smul_const 𝕂 hm hs c hμs h_condexp,
end
variables {𝕂}

lemma norm_condexp_L1s_indicator_L1s {s : set α} (hs : measurable_set s) (hμs : μ s < ∞) (c : E') :
  ∥condexp_L1s_lm 𝕂 hm (indicator_L1s hs c (or.inr hμs))∥ ≤ ∥indicator_L1s hs c (or.inr hμs)∥ :=
begin
  rw norm_indicator_L1s,
  rw [ norm_def, snorm_congr_ae (condexp_L1s_indicator_L1s_eq 𝕂 hm hs hμs c),
    snorm_eq_snorm' ennreal.zero_lt_one.ne.symm ennreal.coe_ne_top, snorm'],
  simp_rw [ennreal.one_to_real, div_one, ennreal.rpow_one, nnnorm_smul,
    ennreal.coe_mul],
  rw [lintegral_mul_const _ (Lp.measurable _).nnnorm.ennreal_coe, ennreal.to_real_mul, mul_comm,
    ← of_real_norm_eq_coe_nnnorm, ennreal.to_real_of_real (norm_nonneg _)],
  swap, { apply_instance, },
  refine mul_le_mul le_rfl _ ennreal.to_real_nonneg (norm_nonneg _),
  suffices h_norm : ∥(condexp_L1s_lm ℝ hm) (indicator_L1s hs (1 : ℝ) (or.inr hμs))∥
    ≤ (μ s).to_real,
  { rw [norm_def, snorm_eq_snorm' ennreal.zero_lt_one.ne.symm ennreal.coe_ne_top,
      snorm', ennreal.one_to_real, div_one] at h_norm,
    simp_rw ennreal.rpow_one at h_norm,
    exact h_norm, },
  refine (norm_condexp_L1s_indicator_L1s_R_le hm hs (1 : ℝ) (or.inr hμs)).trans _,
  simp only [one_mul, norm_one],
end

lemma norm_condexp_L1s_le (f : α →₁ₛ[μ] E') : ∥condexp_L1s_lm 𝕂 hm f∥ ≤ ∥f∥ :=
begin
  rw L1.simple_func.norm_eq_integral,
  rw simple_func.map_integral _ _ (L1.simple_func.integrable _),
  swap, { exact norm_zero, },
  nth_rewrite 0 L1.simple_func.simple_func_eq_sum_indicator_L1s f,
  rw linear_map.map_sum,
  simp_rw measure_congr
    (L1.simple_func.preimage_congr_ae (L1.simple_func.to_simple_func_eq_to_fun f) _),
  have h_restrict_set : ∑ (x : E') in (to_simple_func f).range, (μ (f ⁻¹' {x})).to_real • ∥x∥
    = ∑ (x : E') in L1.simple_func.range_nonzero f, (μ (f ⁻¹' {x})).to_real • ∥x∥,
  { sorry, },
  rw h_restrict_set,
  refine (norm_sum_le _ _).trans _,
  refine finset.sum_le_sum (λ x hxf, (norm_condexp_L1s_indicator_L1s hm _ _ x).trans _),
  { exact measure_lt_top _ _, },
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
  refine is_condexp.unique 𝕂 (hm2.trans hm) _ (integrable_condexp _)
    (is_condexp_condexp hf) (integrable_condexp hf),
  exact is_condexp.trans hm2 (is_condexp_condexp _) (is_condexp_condexp hf),
end

omit 𝕂
end condexp_properties

end measure_theory
