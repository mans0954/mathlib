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

lemma snorm_eq_lintegral_nnnorm [measurable_space α] {μ : measure α} [normed_group γ] {p : ℝ≥0∞}
  {f : α → γ} (hp_pos : 0 < p) (hp_ne_top : p ≠ ∞) :
  snorm f p μ = (∫⁻ x, (nnnorm (f x)) ^ p.to_real ∂μ) ^ (1 / p.to_real) :=
by rw [snorm_eq_snorm' hp_pos.ne.symm hp_ne_top, snorm']

lemma snorm_one_eq_lintegral_nnnorm [measurable_space α] {μ : measure α} [normed_group γ]
  {f : α → γ} :
  snorm f 1 μ = ∫⁻ x, nnnorm (f x) ∂μ :=
by simp_rw [snorm_eq_lintegral_nnnorm ennreal.zero_lt_one ennreal.coe_ne_top, ennreal.one_to_real,
  one_div_one, ennreal.rpow_one]

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

section complete_subspace

variables {ι : Type*} {m m0 : measurable_space α} {μ : measure α}

lemma mem_Lp_trim_of_mem_Lp_sub (hm : m ≤ m0) (f : Lp F p μ) (hf_meas : f ∈ Lp_sub F 𝕂 m p μ) :
  @mem_ℒp α F m _ _ (mem_Lp_sub_iff_ae_measurable'.mp hf_meas).some p (μ.trim hm) :=
begin
  have hf : ae_measurable' m f μ, from (mem_Lp_sub_iff_ae_measurable'.mp hf_meas),
  let g := hf.some,
  obtain ⟨hg, hfg⟩ := hf.some_spec,
  change @mem_ℒp α F m _ _ g p (μ.trim hm),
  refine ⟨@measurable.ae_measurable _ _ m _ g (μ.trim hm) hg, _⟩,
  have h_snorm_fg : @snorm α _ m _ g p (μ.trim hm) = snorm f p μ,
    by { rw snorm_trim hm hg, exact snorm_congr_ae hfg.symm, },
  rw h_snorm_fg,
  exact Lp.snorm_lt_top f,
end

lemma mem_ℒp_of_mem_ℒp_trim (hm : m ≤ m0) {f : α → G} (hf : @mem_ℒp α G m _ _ f p (μ.trim hm)) :
  mem_ℒp f p μ :=
begin
  refine ⟨ae_measurable_of_ae_measurable_trim hm hf.1, _⟩,
  have hf_snorm := hf.2,
  let g := @ae_measurable.mk _ _ m _ _ _ hf.1,
  have hg_meas : @measurable _ _ m _ g, from @ae_measurable.measurable_mk _ _ m _ _ _ hf.1,
  have hfg := @ae_measurable.ae_eq_mk _ _ m _ _ _ hf.1,
  rw @snorm_congr_ae _ _ m _ _ _ _ _ hfg at hf_snorm,
  rw snorm_congr_ae (ae_eq_of_ae_eq_trim hm hfg),
  rwa snorm_trim hm hg_meas at hf_snorm,
end

lemma mem_Lp_sub_to_Lp_of_trim (hm : m ≤ m0) (f : @Lp α F m _ _ _ _ p (μ.trim hm)) :
  (mem_ℒp_of_mem_ℒp_trim hm (@Lp.mem_ℒp _ _ m _ _ _ _ _ _ f)).to_Lp f ∈ Lp_sub F 𝕂 m p μ :=
begin
  let hf_mem_ℒp := mem_ℒp_of_mem_ℒp_trim hm (@Lp.mem_ℒp _ _ m _ _ _ _ _ _ f),
  rw mem_Lp_sub_iff_ae_measurable',
  refine ae_measurable'.congr_ae _ (mem_ℒp.coe_fn_to_Lp hf_mem_ℒp).symm,
  refine ae_measurable'.ae_measurable'_of_ae_measurable'_trim hm _,
  exact (@Lp.ae_measurable _ _ m _ _ _ _ _ _ f),
end

variables (F 𝕂 p μ)
def Lp_meas_to_Lp_trim (hm : m ≤ m0) (f : Lp_sub F 𝕂 m p μ) : @Lp α F m _ _ _ _ p (μ.trim hm) :=
@mem_ℒp.to_Lp _ _ m p (μ.trim hm) _ _ _ _ (mem_Lp_sub_iff_ae_measurable'.mp f.mem).some
  (mem_Lp_trim_of_mem_Lp_sub hm f f.mem)

def Lp_trim_to_Lp_meas (hm : m ≤ m0) (f : @Lp α F m _ _ _ _ p (μ.trim hm)) :
  Lp_sub F 𝕂 m p μ :=
⟨(mem_ℒp_of_mem_ℒp_trim hm (@Lp.mem_ℒp _ _ m _ _ _ _ _ _ f)).to_Lp f,
  mem_Lp_sub_to_Lp_of_trim hm f⟩

variables {F 𝕂 p μ}

lemma Lp_meas_to_Lp_trim_ae_eq (hm : m ≤ m0) (f : Lp_sub F 𝕂 m p μ) :
  Lp_meas_to_Lp_trim F 𝕂 p μ hm f =ᵐ[μ] f :=
(ae_eq_of_ae_eq_trim hm
    (@mem_ℒp.coe_fn_to_Lp _ _ m _ _ _ _ _ _ _ (mem_Lp_trim_of_mem_Lp_sub hm ↑f f.mem))).trans
  (mem_Lp_sub_iff_ae_measurable'.mp f.mem).some_spec.2.symm

lemma Lp_trim_to_Lp_meas_ae_eq (hm : m ≤ m0) (f : @Lp α F m _ _ _ _ p (μ.trim hm)) :
  Lp_trim_to_Lp_meas F 𝕂 p μ hm f =ᵐ[μ] f :=
mem_ℒp.coe_fn_to_Lp _

lemma Lp_meas_to_Lp_trim_right_inv (hm : m ≤ m0) :
  function.right_inverse (Lp_trim_to_Lp_meas F 𝕂 p μ hm) (Lp_meas_to_Lp_trim F 𝕂 p μ hm) :=
begin
  intro f,
  ext1,
  refine ae_eq_trim_of_measurable hm _ _ _,
  { exact @Lp.measurable _ _ m _ _ _ _ _ _ _, },
  { exact @Lp.measurable _ _ m _ _ _ _ _ _ _, },
  { exact (Lp_meas_to_Lp_trim_ae_eq hm _).trans (Lp_trim_to_Lp_meas_ae_eq hm _), },
end

lemma Lp_meas_to_Lp_trim_left_inv (hm : m ≤ m0) :
  function.left_inverse (Lp_trim_to_Lp_meas F 𝕂 p μ hm) (Lp_meas_to_Lp_trim F 𝕂 p μ hm) :=
begin
  intro f,
  ext1,
  ext1,
  rw ← Lp_sub_coe,
  exact (Lp_trim_to_Lp_meas_ae_eq hm _).trans (Lp_meas_to_Lp_trim_ae_eq hm _),
end

lemma Lp_meas_to_Lp_trim_add (hm : m ≤ m0) (f g : Lp_sub F 𝕂 m p μ) :
  Lp_meas_to_Lp_trim F 𝕂 p μ hm (f + g)
    = Lp_meas_to_Lp_trim F 𝕂 p μ hm f + Lp_meas_to_Lp_trim F 𝕂 p μ hm g :=
begin
  ext1,
  refine eventually_eq.trans _ (@Lp.coe_fn_add _ _ m _ _ _ _ _ _ _ _).symm,
  refine ae_eq_trim_of_measurable hm _ _ _,
  { exact @Lp.measurable _ _ m _ _ _ _ _ _ _, },
  { exact @measurable.add _ m _ _ _ _ _ _ (@Lp.measurable _ _ m _ _ _ _ _ _ _)
      (@Lp.measurable _ _ m _ _ _ _ _ _ _), },
  refine (Lp_meas_to_Lp_trim_ae_eq hm _).trans _,
  refine eventually_eq.trans _
    (eventually_eq.add (Lp_meas_to_Lp_trim_ae_eq hm f).symm (Lp_meas_to_Lp_trim_ae_eq hm g).symm),
  refine (Lp.coe_fn_add _ _).trans _,
  simp_rw Lp_sub_coe,
  refine eventually_of_forall (λ x, _),
  refl,
end

lemma Lp_meas_to_Lp_trim_smul (hm : m ≤ m0) (c : 𝕂) (f : Lp_sub F 𝕂 m p μ) :
  Lp_meas_to_Lp_trim F 𝕂 p μ hm (c • f) = c • Lp_meas_to_Lp_trim F 𝕂 p μ hm f :=
begin
  ext1,
  refine eventually_eq.trans _ (@Lp.coe_fn_smul _ _ m _ _ _ _ _ _ _ _ _ _ _ _ _).symm,
  refine ae_eq_trim_of_measurable hm _ _ _,
  { exact @Lp.measurable _ _ m _ _ _ _ _ _ _, },
  { exact @measurable.const_smul _ m _ _ _ _ _ _ _ (@Lp.measurable _ _ m _ _ _ _ _ _ _) c, },
  refine (Lp_meas_to_Lp_trim_ae_eq hm _).trans _,
  refine (Lp.coe_fn_smul c _).trans _,
  refine (Lp_meas_to_Lp_trim_ae_eq hm f).mono (λ x hx, _),
  rw [pi.smul_apply, pi.smul_apply, hx, Lp_sub_coe],
  refl,
end

lemma Lp_meas_to_Lp_trim_norm_map [hp : fact (1 ≤ p)] (hm : m ≤ m0) (f : Lp_sub F 𝕂 m p μ) :
  ∥Lp_meas_to_Lp_trim F 𝕂 p μ hm f∥ = ∥f∥ :=
begin
  rw [norm_def, snorm_trim hm (@Lp.measurable _ _ m _ _ _ _ _ _ _)],
  swap, { apply_instance, },
  rw [snorm_congr_ae (Lp_meas_to_Lp_trim_ae_eq hm _), Lp_sub_coe, ← norm_def],
  congr,
end

variables (F 𝕂 p μ)
def Lp_meas_to_Lp_trim_lie [hp : fact (1 ≤ p)] (hm : m ≤ m0) :
  Lp_sub F 𝕂 m p μ ≃ₗᵢ[𝕂] @Lp α F m _ _ _ _ p (μ.trim hm) :=
{ to_fun    := Lp_meas_to_Lp_trim F 𝕂 p μ hm,
  map_add'  := Lp_meas_to_Lp_trim_add hm,
  map_smul' := Lp_meas_to_Lp_trim_smul hm,
  inv_fun   := Lp_trim_to_Lp_meas F 𝕂 p μ hm,
  left_inv  := Lp_meas_to_Lp_trim_left_inv hm,
  right_inv := Lp_meas_to_Lp_trim_right_inv hm,
  norm_map' := Lp_meas_to_Lp_trim_norm_map hm, }
variables {F 𝕂 p μ}

lemma linear_isometry_equiv.range_eq_univ {R E F : Type*} [semiring R] [normed_group E]
  [normed_group F] [semimodule R E] [semimodule R F] (e : E ≃ₗᵢ[R] F) :
  set.range e = set.univ :=
by { rw ← linear_isometry_equiv.coe_to_isometric, exact isometric.range_eq_univ _, }

instance [hm : fact (m ≤ m0)] [complete_space F] [hp : fact (1 ≤ p)] :
  complete_space (Lp_sub F 𝕂 m p μ) :=
begin
  refine complete_space_of_is_complete_univ _,
  refine is_complete_of_complete_image
    (Lp_meas_to_Lp_trim_lie F 𝕂 p μ hm.elim).isometry.uniform_embedding.to_uniform_inducing _,
  rw [set.image_univ, linear_isometry_equiv.range_eq_univ, ← complete_space_iff_is_complete_univ],
  apply_instance,
end

end complete_subspace

end Lp_sub

def integral_eq_on_fin_meas (m : measurable_space α) [m0 : measurable_space α] (f g : α → F')
  (μ : measure α) :
  Prop :=
∀ s, @measurable_set α m s → μ s < ∞ → ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ

namespace integral_eq_on_fin_meas

variables {m m0 : measurable_space α} {μ : measure α} {f f₁ f₂ g g₁ g₂ : α → F'}

protected lemma rfl : integral_eq_on_fin_meas m f f μ := λ s hs hμs, rfl

protected lemma refl (f : α → F') : integral_eq_on_fin_meas m f f μ := integral_eq_on_fin_meas.rfl

protected lemma trans (hf1 : integral_eq_on_fin_meas m f f₁ μ)
  (hf2 : integral_eq_on_fin_meas m f₁ f₂ μ) :
  integral_eq_on_fin_meas m f f₂ μ :=
λ s hs hμs, (hf1 s hs hμs).trans (hf2 s hs hμs)

protected lemma symm (hfg : integral_eq_on_fin_meas m f g μ) :
  integral_eq_on_fin_meas m g f μ :=
λ s hs hμs, (hfg s hs hμs).symm

lemma congr_ae_left' (hf12 : f₁ =ᵐ[μ] f₂) (hfg1 : integral_eq_on_fin_meas m f₁ g μ) :
  integral_eq_on_fin_meas m f₂ g μ :=
begin
  intros s hs hμs,
  rw integral_congr_ae (ae_restrict_of_ae hf12.symm),
  exact hfg1 s hs hμs,
end

lemma congr_ae_left (hf12 : f₁ =ᵐ[μ] f₂) :
  integral_eq_on_fin_meas m f₁ g μ ↔ integral_eq_on_fin_meas m f₂ g μ :=
⟨λ h, congr_ae_left' hf12 h, λ h, congr_ae_left' hf12.symm h⟩

lemma congr_ae_right' (hg12 : g₁ =ᵐ[μ] g₂) (hfg1 : integral_eq_on_fin_meas m f g₁ μ) :
  integral_eq_on_fin_meas m f g₂ μ :=
begin
  intros s hs hμs,
  rw integral_congr_ae (ae_restrict_of_ae hg12.symm),
  exact hfg1 s hs hμs,
end

lemma congr_ae_right (hg12 : g₁ =ᵐ[μ] g₂) :
  integral_eq_on_fin_meas m f g₁ μ ↔ integral_eq_on_fin_meas m f g₂ μ :=
⟨λ h, congr_ae_right' hg12 h, λ h, congr_ae_right' hg12.symm h⟩

lemma congr_ae' (hf12 : f₁ =ᵐ[μ] f₂) (hg12 : g₁ =ᵐ[μ] g₂)
  (hfg₁ : integral_eq_on_fin_meas m f₁ g₁ μ) :
  integral_eq_on_fin_meas m f₂ g₂ μ :=
congr_ae_left' hf12 (congr_ae_right' hg12 hfg₁)

lemma congr_ae (hf12 : f₁ =ᵐ[μ] f₂) (hg12 : g₁ =ᵐ[μ] g₂) :
  integral_eq_on_fin_meas m f₁ g₁ μ ↔ integral_eq_on_fin_meas m f₂ g₂ μ :=
⟨λ h, congr_ae' hf12 hg12 h, λ h, congr_ae' hf12.symm hg12.symm h⟩

end integral_eq_on_fin_meas

section is_condexp

/-- `f` is a conditional expectation of `g` with respect to the measurable space structure `m`. -/
def is_condexp (m : measurable_space α) [m0 : measurable_space α] (f g : α → F') (μ : measure α) :
  Prop :=
ae_measurable' m f μ ∧ ∀ s (hs : @measurable_set α m s), ∫ a in s, f a ∂μ = ∫ a in s, g a ∂μ

variables {m₂ m m0 : measurable_space α} {μ : measure α} {f f₁ f₂ g g₁ g₂ : α → F'}

lemma is_condexp.refl (hf : ae_measurable' m f μ) : is_condexp m f f μ := ⟨hf, λ s hs, rfl⟩

lemma is_condexp.trans (hm2 : m₂ ≤ m) (hff₂ : is_condexp m₂ f₂ f μ) (hfg : is_condexp m f g μ) :
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

lemma is_condexp.neg (hfg : is_condexp m f g μ) :
  is_condexp m (-f) (-g) μ :=
begin
  rcases hfg with ⟨h_meas, h_int_eq⟩,
  refine ⟨h_meas.neg, (λ s hs, _)⟩,
  simp_rw pi.neg_apply,
  rw [integral_neg, integral_neg, h_int_eq s hs],
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

lemma is_condexp.integrable_on' (hm : m ≤ m0) {f g : α → ℝ} (hgf : is_condexp m g f μ) (s : set α)
  (hs : @measurable_set _ m s) (hfs : ∫ x in s, f x ∂μ ≠ 0) :
  integrable_on g s μ :=
by { by_contra h, refine hfs _, rw [(hgf.2 s hs).symm, ← integral_undef h], }

lemma is_condexp.integrable' (hm : m ≤ m0) {f g : α → ℝ} (hgf : is_condexp m g f μ)
  (hfs : ∫ x, f x ∂μ ≠ 0) :
  integrable g μ :=
begin
  rw ← integrable_on_univ,
  rw ← integral_univ at hfs,
  exact hgf.integrable_on' hm set.univ (@measurable_set.univ _ m) hfs,
end

lemma is_condexp.integrable_on_of_nonneg (hm : m ≤ m0) {f g : α → ℝ} (hgf : is_condexp m g f μ)
  {s : set α} (hs : @measurable_set _ m s) (hf_nonneg : 0 ≤ᵐ[μ.restrict s] f)
  (hf_int : integrable_on f s μ) (hfg_zero : f =ᵐ[μ.restrict s] 0 → g =ᵐ[μ.restrict s] 0) :
  integrable_on g s μ :=
begin
  have h_int_pos := integral_pos_iff_support_of_nonneg_ae hf_nonneg hf_int,
  by_cases h_support : 0 < μ.restrict s (function.support f),
  { refine hgf.integrable_on' hm s hs (ne_of_gt _),
    rwa [h_int_pos], },
  { have hf_zero : f =ᵐ[μ.restrict s] 0,
    { rw ← integral_eq_zero_iff_of_nonneg_ae hf_nonneg hf_int,
      refine le_antisymm _ (integral_nonneg_of_ae hf_nonneg),
      rw [← @not_not (∫ x in s, f x ∂μ ≤ 0), not_le],
      exact λ h, h_support (h_int_pos.mp h), },
    exact (integrable_congr (hfg_zero hf_zero)).mpr (integrable_zero _ _ _), },
end

lemma is_condexp.integrable_of_nonneg (hm : m ≤ m0) {f g : α → ℝ} (hgf : is_condexp m g f μ)
  (hf_nonneg : 0 ≤ᵐ[μ] f) (hf_int : integrable f μ) (hfg_zero : f =ᵐ[μ] 0 → g =ᵐ[μ] 0) :
  integrable g μ :=
begin
  rw ← integrable_on_univ at hf_int ⊢,
  refine hgf.integrable_on_of_nonneg hm (@measurable_set.univ _ m) _ hf_int _,
  { simpa using hf_nonneg, },
  { simpa using hfg_zero, },
end

lemma is_condexp.integrable_of_nonpos (hm : m ≤ m0) {f g : α → ℝ} (hgf : is_condexp m g f μ)
  (hf_nonpos : f ≤ᵐ[μ] 0) (hf_int : integrable f μ) (hfg_zero : f =ᵐ[μ] 0 → g =ᵐ[μ] 0) :
  integrable g μ :=
begin
  refine integrable_neg_iff.mp _,
  have hf_neg_nonneg : 0 ≤ᵐ[μ] -f, sorry,
  have hf_neg_int : integrable (-f) μ, from integrable_neg_iff.mpr hf_int,
  have hf_neg_zero : -f =ᵐ[μ] 0 → -g =ᵐ[μ] 0, sorry,
  have hgf_neg : is_condexp m (-g) (-f) μ, from hgf.neg,
  exact hgf_neg.integrable_of_nonneg hm hf_neg_nonneg hf_neg_int hf_neg_zero,
end

lemma nonneg_of_integral_eq (hm : m ≤ m0) {f g : α → ℝ} (hf : 0 ≤ᵐ[μ] f) (hf_int : integrable f μ)
  (hgf : integral_eq_on_fin_meas m g f μ) (hg : @measurable _ _ m _ g) :
  0 ≤ᵐ[μ] g :=
begin
  have hg_int : integrable g μ, sorry,
  have h_int_m : @integrable α _ m _ _ g (μ.trim hm),
    from integrable_trim_of_measurable hm hg hg_int,
  refine ae_eq_null_of_trim hm _,
  refine @ae_nonneg_of_forall_set_ℝ α m (μ.trim hm) g h_int_m (λ s hs hμs, _),
  rw ← set_integral_trim hm g hg hg_int hs,
  rw hgf s hs ((le_trim hm).trans_lt hμs),
  exact integral_nonneg_of_ae (ae_restrict_of_ae hf),
end

lemma is_condexp.nonneg (hm : m ≤ m0) {f g : α → ℝ} (hf : 0 ≤ᵐ[μ] f) (hgf : is_condexp m g f μ)
  (hg : integrable g μ) :
  0 ≤ᵐ[μ] g :=
begin
  obtain ⟨⟨f', h_meas, hff'⟩, h_int_eq⟩ := hgf,
  have h_int' : integrable f' μ := (integrable_congr hff').mp hg,
  have h_int'_m : @integrable α _ m _ _ f' (μ.trim hm),
    from integrable_trim_of_measurable hm h_meas h_int',
  refine eventually_le.trans (ae_eq_null_of_trim hm _) hff'.symm.le,
  refine @ae_nonneg_of_forall_set_ℝ α m (μ.trim hm) f' h_int'_m (λ s hs hμs, _),
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

lemma mem_ℒp.mem_ℒp_restrict_of_le_of_measure_finite {p q : ℝ≥0∞} (hpq : p ≤ q) {f : α → G}
  (hf : mem_ℒp f q μ) {s : set α} (hμs : μ s < ∞) :
  mem_ℒp f p (μ.restrict s) :=
begin
  have hf_meas_restrict : ae_measurable f (μ.restrict s), from (hf.restrict s).ae_measurable,
  by_cases hp_zero : p = 0,
  { rwa [hp_zero, mem_ℒp_zero_iff_ae_measurable], },
  by_cases hq_zero : q = 0,
  { rw hq_zero at hpq,
    exact absurd (le_antisymm hpq (zero_le _)) hp_zero, },
  refine ⟨hf_meas_restrict, _⟩,
  refine (snorm_le_snorm_mul_rpow_measure_univ hpq hf_meas_restrict).trans_lt _,
  refine ennreal.mul_lt_top (hf.restrict s).snorm_lt_top (ennreal.rpow_lt_top_of_nonneg _ _),
  { by_cases hq_top : q = ∞,
    { simp [hq_top], },
    by_cases hp_top : p = ∞,
    { rw hp_top at hpq,
      exact absurd (le_antisymm le_top hpq) hq_top, },
    rw [sub_nonneg, one_div_le_one_div],
    { rwa ennreal.to_real_le_to_real hp_top hq_top, },
    { exact ennreal.to_real_pos_iff.mpr ⟨(zero_le _).lt_of_ne (ne.symm hq_zero), hq_top⟩, },
    { exact ennreal.to_real_pos_iff.mpr ⟨(zero_le _).lt_of_ne (ne.symm hp_zero), hp_top⟩, }, },
  { simp only [set.univ_inter, measurable_set.univ, ne.def, measure.restrict_apply],
    exact hμs.ne, },
end

lemma integrable_on_Lp_of_measure_finite (f : Lp G p μ) (hp : 1 ≤ p) {s : set α} (hμs : μ s < ∞) :
  integrable_on f s μ :=
mem_ℒp_one_iff_integrable.mp $ mem_ℒp.mem_ℒp_restrict_of_le_of_measure_finite hp (Lp.mem_ℒp _) hμs

variables (𝕂)
/-- Conditional expectation of a function in L2 with respect to a sigma-algebra -/
def condexp_L2_clm [complete_space E] (hm : m ≤ m0) :
  (α →₂[μ] E) →L[𝕂] (Lp_sub E 𝕂 m 2 μ) :=
@orthogonal_projection 𝕂 (α →₂[μ] E) _ _ (Lp_sub E 𝕂 m 2 μ)
  (by { haveI : fact (m ≤ m0) := ⟨hm⟩, exact infer_instance, })
variables {𝕂}

lemma inner_condexp_L2_left_eq_right (hm : m ≤ m0) {f g : Lp E' 2 μ} :
  @inner 𝕂 _ _ (condexp_L2_clm 𝕂 hm f : Lp E' 2 μ) g
    = inner f (condexp_L2_clm 𝕂 hm g : Lp E' 2 μ) :=
begin
  haveI : fact (m ≤ m0) := ⟨hm⟩,
  haveI : fact ((1 : ℝ≥0∞) ≤ 2) := ⟨ennreal.one_le_two⟩,
  exact orthogonal_projection_self_adjoint _ f g,
end

variables (𝕂)
lemma inner_set_integral_eq_inner_indicator (hm : m ≤ m0) {s : set α} (hs : @measurable_set α m s)
  (hμs : μ s < ∞) (c : E') (f : Lp E' 2 μ) :
  @inner 𝕂 _ _ c (∫ x in s, f x ∂μ) = inner (indicator_Lp 2 (hm s hs) c (or.inr hμs)) f :=
begin
  rw ← integral_inner (integrable_on_Lp_of_measure_finite f ennreal.one_le_two hμs),
  simp_rw inner,
  rw ← integral_indicator (hm s hs),
  refine integral_congr_ae _,
  refine (indicator_Lp_coe_fn 2 (hm s hs) c (or.inr hμs)).mono (λ x hx, _),
  dsimp only,
  rw hx,
  simp_rw set.indicator_apply,
  by_cases hx_mem : x ∈ s; simp [hx_mem],
end
variables {𝕂}

lemma set_integral_eq_inner_indicator (hm : m ≤ m0) {s : set α} (hs : @measurable_set α m s)
  (hμs : μ s < ∞) (f : Lp ℝ 2 μ) :
  ∫ x in s, f x ∂μ = inner (indicator_Lp 2 (hm s hs) (1 : ℝ) (or.inr hμs)) f :=
begin
  rw ← inner_set_integral_eq_inner_indicator ℝ hm hs hμs (1 : ℝ) f,
  simp only [is_R_or_C.inner_apply, is_R_or_C.conj_to_real, one_mul],
end

section fin_meas_sets

variables (hm : m ≤ m0) {s t : set α} {f : Lp ℝ 2 μ}

lemma norm_condexp_L2_le_one : ∥@condexp_L2_clm α E' 𝕂 _ _ _ _ _ _ _ _ _ μ _ hm∥ ≤ 1 :=
begin
  haveI : fact (m ≤ m0) := ⟨hm⟩,
  haveI : fact ((1 : ℝ≥0∞) ≤ 2) := ⟨ennreal.one_le_two⟩,
  exact orthogonal_projection_norm_le _,
end

lemma norm_condexp_L2_apply_le (f : Lp E' 2 μ) : ∥condexp_L2_clm 𝕂 hm f∥ ≤ ∥f∥ :=
begin
  refine ((@condexp_L2_clm α E' 𝕂 _ _ _ _ _ _ _ _ _ μ _ hm).le_op_norm _).trans _,
  nth_rewrite 1 ← one_mul (∥f∥),
  exact mul_le_mul (norm_condexp_L2_le_one hm) le_rfl (norm_nonneg _) zero_le_one,
end

lemma snorm_condexp_L2_le (f : Lp E' 2 μ) : snorm (condexp_L2_clm 𝕂 hm f) 2 μ ≤ snorm f 2 μ :=
begin
  rw [Lp_sub_coe, ← ennreal.to_real_le_to_real (Lp.snorm_ne_top _) (Lp.snorm_ne_top _), ← norm_def,
    ← norm_def, submodule.norm_coe],
  exact norm_condexp_L2_apply_le hm f,
end

lemma condexp_L2_indicator_of_measurable (hs : @measurable_set _ m s) (hμs : μ s < ∞) (c : E') :
  (condexp_L2_clm 𝕂 hm (indicator_Lp 2 (hm s hs) c (or.inr hμs)) : Lp E' 2 μ)
    = indicator_Lp 2 (hm s hs) c (or.inr hμs) :=
begin
  rw condexp_L2_clm,
  haveI : fact(m ≤ m0) := ⟨hm⟩,
  have h_mem : indicator_Lp 2 (hm s hs) c (or.inr hμs) ∈ Lp_sub E' 𝕂 m 2 μ,
    from mem_Lp_sub_indicator_Lp hm hs,
  let ind := (⟨indicator_Lp 2 (hm s hs) c (or.inr hμs), h_mem⟩ : Lp_sub E' 𝕂 m 2 μ),
  have h_coe_ind : (ind : Lp E' 2 μ) = indicator_Lp 2 (hm s hs) c (or.inr hμs), by refl,
  have h_orth_mem := orthogonal_projection_mem_subspace_eq_self ind,
  rw [← h_coe_ind, h_orth_mem],
end

lemma inner_condexp_L2_eq_inner_fun (f g : Lp E' 2 μ) (hg : ae_measurable' m g μ) :
  @inner 𝕂 _ _ (↑(condexp_L2_clm 𝕂 hm f) : Lp E' 2 μ) g = inner f g :=
begin
  symmetry,
  rw [← sub_eq_zero, ← inner_sub_left, condexp_L2_clm],
  simp only [mem_Lp_sub_iff_ae_measurable'.mpr hg, orthogonal_projection_inner_eq_zero],
end

lemma integral_eq_on_fin_meas_condexp_L2 (f : Lp ℝ 2 μ) :
  integral_eq_on_fin_meas m (condexp_L2_clm ℝ hm f) f μ :=
begin
  intros s hs hμs,
  rw set_integral_eq_inner_indicator hm hs hμs,
  have h_eq_inner : ∫ x in s, condexp_L2_clm ℝ hm f x ∂μ
    = inner (indicator_Lp 2 (hm s hs) (1 : ℝ) (or.inr hμs)) (condexp_L2_clm ℝ hm f),
  { rw ← set_integral_eq_inner_indicator hm hs hμs,
    congr, },
  rw [h_eq_inner, ← inner_condexp_L2_left_eq_right, condexp_L2_indicator_of_measurable hm hs hμs],
  all_goals { apply_instance, },
end

lemma integrable_on_condexp_L2_of_measure_finite (hμs : μ s < ∞) (f : Lp E' 2 μ) :
  integrable_on (condexp_L2_clm 𝕂 hm f) s μ :=
integrable_on_Lp_of_measure_finite ((condexp_L2_clm 𝕂 hm f) : Lp E' 2 μ) ennreal.one_le_two hμs

lemma integrable_condexp_L2_of_finite_measure [finite_measure μ] {f : Lp E' 2 μ} :
  integrable (condexp_L2_clm 𝕂 hm f) μ :=
integrable_on_univ.mp $ integrable_on_condexp_L2_of_measure_finite hm (measure_lt_top _ _) f

lemma set_lintegral_compl {s : set α} (hs : measurable_set s) {f : α → ℝ≥0∞} :
  ∫⁻ x in s, f x ∂μ + ∫⁻ x in sᶜ, f x ∂μ = ∫⁻ x, f x ∂μ :=
by rw [← lintegral_add_measure, measure.restrict_add_restrict_compl hs]

lemma set_integral_compl {s : set α} (hs : measurable_set s) {f : α → F'} (hfi : integrable f μ) :
  ∫ x in s, f x ∂μ + ∫ x in sᶜ, f x ∂μ = ∫ x, f x ∂μ :=
by rw [← integral_add_measure (hfi.restrict s) (hfi.restrict sᶜ),
  measure.restrict_add_restrict_compl hs]

lemma set_lintegral_congr_fun {s : set α} (hs : measurable_set s) {f g : α → ℝ≥0∞}
  (hfg : ∀ᵐ x ∂μ, x ∈ s → f x = g x) :
  ∫⁻ x in s, f x ∂μ = ∫⁻ x in s, g x ∂μ :=
by { rw lintegral_congr_ae, rw eventually_eq, rwa ae_restrict_iff' hs, }

lemma lintegral_nnnorm_eq_pos_sub_neg (f : α → ℝ) (hf : measurable f) :
  ∫⁻ x, nnnorm (f x) ∂μ = ∫⁻ x in {x | 0 ≤ f x}, ennreal.of_real (f x) ∂μ
    + ∫⁻ x in {x | 0 ≤ f x}ᶜ, ennreal.of_real (- f x) ∂μ :=
have h_meas : measurable_set {x | 0 ≤ f x},
  from measurable_set_le measurable_const hf,
calc ∫⁻ x, nnnorm (f x) ∂μ = ∫⁻ x, ennreal.of_real (∥f x∥) ∂μ :
  by simp_rw of_real_norm_eq_coe_nnnorm
... = ∫⁻ x in {x | 0 ≤ f x}, ennreal.of_real (∥f x∥) ∂μ
      + ∫⁻ x in {x | 0 ≤ f x}ᶜ, ennreal.of_real (∥f x∥) ∂μ :
  by rw ← set_lintegral_compl h_meas
... = ∫⁻ x in {x | 0 ≤ f x}, ennreal.of_real (f x) ∂μ
      + ∫⁻ x in {x | 0 ≤ f x}ᶜ, ennreal.of_real (∥f x∥) ∂μ :
begin
  congr' 1,
  refine set_lintegral_congr_fun h_meas (eventually_of_forall (λ x hx, _)),
  congr,
  rw [real.norm_eq_abs, abs_eq_self.mpr _],
  exact hx,
end
... = ∫⁻ x in {x | 0 ≤ f x}, ennreal.of_real (f x) ∂μ
      + ∫⁻ x in {x | 0 ≤ f x}ᶜ, ennreal.of_real (- f x) ∂μ :
begin
  congr' 1,
  refine set_lintegral_congr_fun (measurable_set.compl h_meas)
    (eventually_of_forall (λ x hx, _)),
  congr,
  rw [real.norm_eq_abs, abs_eq_neg_self.mpr _],
  rw [set.mem_compl_iff, set.nmem_set_of_eq] at hx,
  linarith,
end

lemma integral_norm_eq_pos_sub_neg {f : α → ℝ} (hf : measurable f) (hfi : integrable f μ) :
  ∫ x, ∥f x∥ ∂μ = ∫ x in {x | 0 ≤ f x}, f x ∂μ - ∫ x in {x | 0 ≤ f x}ᶜ, f x ∂μ :=
have h_meas : measurable_set {x | 0 ≤ f x}, from measurable_set_le measurable_const hf,
calc ∫ x, ∥f x∥ ∂μ = ∫ x in {x | 0 ≤ f x}, ∥f x∥ ∂μ
      + ∫ x in {x | 0 ≤ f x}ᶜ, ∥f x∥ ∂μ :
  by rw ← set_integral_compl h_meas hfi.norm
... = ∫ x in {x | 0 ≤ f x}, f x ∂μ + ∫ x in {x | 0 ≤ f x}ᶜ, ∥f x∥ ∂μ :
begin
  congr' 1,
  refine set_integral_congr h_meas (λ x hx, _),
  dsimp only,
  rw [real.norm_eq_abs, abs_eq_self.mpr _],
  exact hx,
end
... = ∫ x in {x | 0 ≤ f x}, f x ∂μ - ∫ x in {x | 0 ≤ f x}ᶜ, f x ∂μ :
begin
  congr' 1,
  rw ← integral_neg,
  refine set_integral_congr h_meas.compl (λ x hx, _),
  dsimp only,
  rw [real.norm_eq_abs, abs_eq_neg_self.mpr _],
  rw [set.mem_compl_iff, set.nmem_set_of_eq] at hx,
  linarith,
end

lemma lintegral_nnnorm_eq_integral_norm {f : α → G} (hf : integrable f μ) :
  ∫⁻ x, nnnorm (f x) ∂μ = ennreal.of_real ∫ x, ∥f x∥ ∂μ :=
begin
  rw integral_eq_lintegral_of_nonneg_ae _ hf.1.norm,
  swap, { refine ae_of_all _ _, simp, },
  simp_rw of_real_norm_eq_coe_nnnorm,
  rw ennreal.of_real_to_real _,
  exact lt_top_iff_ne_top.mp hf.2,
end

lemma indicator_le_indicator_nonneg {β} [linear_order β] [has_zero β] (s : set α) (f : α → β) :
  s.indicator f ≤ {x | 0 ≤ f x}.indicator f :=
begin
  intro x,
  simp [set.indicator_apply],
  split_ifs,
  { exact le_rfl, },
  { exact (not_le.mp h_1).le, },
  { exact h_1, },
  { exact le_rfl, },
end

lemma indicator_nonpos_le_indicator {β} [linear_order β] [has_zero β] (s : set α) (f : α → β) :
  {x | f x ≤ 0}.indicator f ≤ s.indicator f :=
begin
  intro x,
  simp [set.indicator_apply],
  split_ifs,
  { exact le_rfl, },
  { exact h, },
  { exact (not_le.mp h).le, },
  { exact le_rfl, },
end

lemma set_integral_le_nonneg {s : set α} (hs : measurable_set s) {f : α → ℝ} (hf : measurable f)
  (hfi : integrable f μ) :
  ∫ x in s, f x ∂μ ≤ ∫ x in {y | 0 ≤ f y}, f x ∂μ :=
begin
  rw [← integral_indicator hs, ← integral_indicator (measurable_set_le measurable_const hf)],
  exact integral_mono (hfi.indicator hs) (hfi.indicator (measurable_set_le measurable_const hf))
    (indicator_le_indicator_nonneg s f),
end

lemma set_integral_ge_nonpos {s : set α} (hs : measurable_set s) {f : α → ℝ} (hf : measurable f)
  (hfi : integrable f μ) :
  ∫ x in {y | f y ≤ 0}, f x ∂μ ≤ ∫ x in s, f x ∂μ :=
begin
  rw [← integral_indicator hs, ← integral_indicator (measurable_set_le hf measurable_const)],
  exact integral_mono (hfi.indicator (measurable_set_le hf measurable_const)) (hfi.indicator hs)
    (indicator_nonpos_le_indicator s f),
end

lemma set_integral_neg_eq_set_integral_nonpos {f : α → ℝ} (hf : measurable f)
  (hfi : integrable f μ) :
  ∫ x in {x | f x < 0}, f x ∂μ = ∫ x in {x | f x ≤ 0}, f x ∂μ :=
begin
  have h_union : {x | f x ≤ 0} = {x | f x < 0} ∪ {x | f x = 0},
  { ext,
    simp_rw [set.mem_union_eq, set.mem_set_of_eq],
    exact le_iff_lt_or_eq, },
  rw [h_union, integral_union _ (measurable_set_lt hf measurable_const)
    (measurable_set_eq_fun hf measurable_const) hfi.integrable_on hfi.integrable_on],
  { rw ← add_zero (∫ (x : α) in {x : α | f x < 0}, f x ∂μ),  -- nth_rewrites times out
    congr,
    { rw add_zero, },
    { refine (integral_eq_zero_of_ae _).symm,
      rw [eventually_eq, ae_restrict_iff (measurable_set_eq_fun hf measurable_zero)],
      refine eventually_of_forall (λ x hx, _),
      simpa using hx, }, },
  { intros x hx,
    simp only [set.mem_inter_eq, set.mem_set_of_eq, set.inf_eq_inter] at hx,
    exact absurd hx.2 hx.1.ne, },
end

lemma integral_norm_le_on (hm : m ≤ m0) {f g : α → ℝ} (hf : measurable f)
  (hfi : integrable_on f s μ) (hg : @measurable _ _ m _ g) (hgi : integrable_on g s μ)
  (hgf : integral_eq_on_fin_meas m g f μ) (hs : @measurable_set _ m s) (hμs : μ s < ∞) :
  ∫ (x : α) in s, ∥g x∥ ∂μ ≤ ∫ (x : α) in s, ∥f x∥ ∂μ :=
begin
  rw integral_norm_eq_pos_sub_neg (hg.mono hm le_rfl) hgi,
  rw integral_norm_eq_pos_sub_neg hf hfi,
  have h_meas_nonneg_g : @measurable_set α m {x | 0 ≤ g x},
    from @measurable_set_le _ α _ _ _ m _ _ _ _ g (@measurable_const _ α _ m _) hg,
  have h_meas_nonneg_f : measurable_set {x | 0 ≤ f x},
    from measurable_set_le measurable_const hf,
  have h_meas_nonpos_g : @measurable_set α m {x | g x ≤ 0},
    from @measurable_set_le _ α _ _ _ m _ _ _ g _ hg (@measurable_const _ α _ m _),
  have h_meas_nonpos_f : measurable_set {x | f x ≤ 0},
    from measurable_set_le hf measurable_const,
  refine sub_le_sub _ _,
  { rw [measure.restrict_restrict (hm _ h_meas_nonneg_g),
      measure.restrict_restrict h_meas_nonneg_f,
      hgf _ (@measurable_set.inter α m _ _ h_meas_nonneg_g hs)
        ((measure_mono (set.inter_subset_right _ _)).trans_lt hμs),
      ← measure.restrict_restrict (hm _ h_meas_nonneg_g),
      ← measure.restrict_restrict h_meas_nonneg_f],
    exact set_integral_le_nonneg (hm _ h_meas_nonneg_g) hf hfi, },
  { have h_set_f_eq : {x : α | 0 ≤ f x}ᶜ = {x | f x < 0}, by { ext, simp, },
    have h_set_g_eq : {x : α | 0 ≤ g x}ᶜ = {x | g x < 0}, by { ext, simp, },
    simp_rw [h_set_f_eq, h_set_g_eq],
    rw set_integral_neg_eq_set_integral_nonpos hf hfi,
    rw set_integral_neg_eq_set_integral_nonpos (hg.mono hm le_rfl) hgi,
    rw [measure.restrict_restrict (hm _ h_meas_nonpos_g),
      measure.restrict_restrict h_meas_nonpos_f,
      hgf _ (@measurable_set.inter α m _ _ h_meas_nonpos_g hs)
        ((measure_mono (set.inter_subset_right _ _)).trans_lt hμs),
      ← measure.restrict_restrict (hm _ h_meas_nonpos_g),
      ← measure.restrict_restrict h_meas_nonpos_f],
    exact set_integral_ge_nonpos (hm _ h_meas_nonpos_g) hf hfi, },
end

lemma lintegral_nnnorm_le_on (hm : m ≤ m0) {f g : α → ℝ} (hf : measurable f)
  (hfi : integrable_on f s μ) (hg : @measurable _ _ m _ g) (hgi : integrable_on g s μ)
  (hgf : integral_eq_on_fin_meas m g f μ) (hs : @measurable_set _ m s) (hμs : μ s < ∞) :
  ∫⁻ x in s, nnnorm (g x) ∂μ ≤ ∫⁻ x in s, nnnorm (f x) ∂μ :=
begin
  rw [lintegral_nnnorm_eq_integral_norm hfi, lintegral_nnnorm_eq_integral_norm hgi,
    ennreal.of_real_le_of_real_iff],
  { exact integral_norm_le_on hm hf hfi hg hgi hgf hs hμs, },
  { exact integral_nonneg (λ x, norm_nonneg _), },
end

lemma lintegral_nnnorm_condexp_L2_le_on (hm : m ≤ m0) (hs : @measurable_set _ m s) (hμs : μ s < ∞)
  (f : Lp ℝ 2 μ) :
  ∫⁻ x in s, nnnorm (condexp_L2_clm ℝ hm f x) ∂μ ≤ ∫⁻ x in s, nnnorm (f x) ∂μ :=
begin
  let h_meas := Lp_sub.ae_measurable' (condexp_L2_clm ℝ hm f),
  let g := h_meas.some,
  have hg_meas : @measurable _ _ m _ g, from h_meas.some_spec.1,
  have hg_eq : g =ᵐ[μ] condexp_L2_clm ℝ hm f, from h_meas.some_spec.2.symm,
  have hg_eq_restrict : g =ᵐ[μ.restrict s] condexp_L2_clm ℝ hm f, from ae_restrict_of_ae hg_eq,
  have hg_nnnorm_eq : (λ x, (nnnorm (g x) : ℝ≥0∞))
    =ᵐ[μ.restrict s] (λ x, (nnnorm (condexp_L2_clm ℝ hm f x) : ℝ≥0∞)),
  { refine hg_eq_restrict.mono (λ x hx, _),
    dsimp only,
    rw hx, },
  rw lintegral_congr_ae hg_nnnorm_eq.symm,
  refine lintegral_nnnorm_le_on hm (Lp.measurable f) _ _ _ _ hs hμs,
  { exact integrable_on_Lp_of_measure_finite f ennreal.one_le_two hμs, },
  { exact hg_meas, },
  { rw [integrable_on, integrable_congr hg_eq_restrict],
    exact integrable_on_condexp_L2_of_measure_finite hm hμs f, },
  { exact integral_eq_on_fin_meas.congr_ae_left' hg_eq.symm (integral_eq_on_fin_meas_condexp_L2 hm f), },
end

lemma condexp_L2_zero_on (hs : @measurable_set _ m s) (hμs : μ s < ∞) {f : Lp ℝ 2 μ}
  (hf : f =ᵐ[μ.restrict s] 0) :
  condexp_L2_clm ℝ hm f =ᵐ[μ.restrict s] 0 :=
begin
  suffices h_nnnorm_eq_zero : ∫⁻ x in s, nnnorm (condexp_L2_clm ℝ hm f x) ∂μ = 0,
  { rw lintegral_eq_zero_iff at h_nnnorm_eq_zero,
    refine h_nnnorm_eq_zero.mono (λ x hx, _),
    dsimp only at hx,
    rw pi.zero_apply at hx ⊢,
    { rwa [ennreal.coe_eq_zero, nnnorm_eq_zero] at hx, },
    { refine measurable.ennreal_coe (measurable.nnnorm _),
      rw Lp_sub_coe,
      exact Lp.measurable _, }, },
  refine le_antisymm _ (zero_le _),
  refine (lintegral_nnnorm_condexp_L2_le_on hm hs hμs f).trans (le_of_eq _),
  rw lintegral_eq_zero_iff,
  { refine hf.mono (λ x hx, _),
    dsimp only,
    rw hx,
    simp, },
  { exact (Lp.measurable _).nnnorm.ennreal_coe, },
end

end fin_meas_sets

lemma ae_nonneg_indicator_Lp {s : set α} (hs : measurable_set s) (hμs : μ s < ∞) (t : set α) :
  0 ≤ᵐ[μ.restrict t] (indicator_Lp 2 hs (1 : ℝ) (or.inr hμs)) :=
begin
  have h_ae_eq_s : indicator_Lp 2 hs (1 : ℝ) (or.inr hμs) =ᵐ[μ.restrict t] s.indicator (λ _, 1),
    from ae_restrict_of_ae (indicator_Lp_coe_fn 2 hs (1 : ℝ) (or.inr hμs)),
  refine h_ae_eq_s.mono (λ x hx, _),
  rw [hx, set.indicator_apply],
  split_ifs; simp [zero_le_one],
end

lemma integrable_indicator_Lp {s : set α} (hs : measurable_set s) (c : F) (hsμc : c = 0 ∨ μ s < ∞) :
  integrable (indicator_Lp p hs c hsμc) μ :=
begin
  rw [integrable_congr (indicator_Lp_coe_fn p hs c hsμc), integrable_indicator_iff hs,
    integrable_on, integrable_const_iff],
  cases hsμc,
  { exact or.inl hsμc, },
  { right,
    simpa only [set.univ_inter, measurable_set.univ, measure.restrict_apply] using hsμc, },
end

lemma lintegral_nnnorm_le_of_bounded_on_finite [opens_measurable_space H] (hm : m ≤ m0)
  [@sigma_finite α m (μ.trim hm)] (C : ℝ≥0∞) (hC : C < ∞) (f : α → H) (hf_meas : measurable f)
  (hf : ∀ s : set α, @measurable_set _ m s → μ s < ∞ → ∫⁻ x in s, nnnorm (f x) ∂μ ≤ C) :
  ∫⁻ x, nnnorm (f x) ∂μ ≤ C :=
begin
  let S := @spanning_sets α m (μ.trim hm) _,
  have hS_meas : ∀ n, @measurable_set _ m (S n), from @measurable_spanning_sets α m (μ.trim hm) _,
  let F := λ n, (S n).indicator f,
  have h_F_lim : ∀ a, (⨆ n, (nnnorm (F n a) : ℝ≥0∞)) = nnnorm (f a),
  { refine λ a, le_antisymm (supr_le (λ n, _)) _,
    { simp_rw [F, set.indicator_apply],
      split_ifs; simp, },
    { have h_exists : ∃ n, a ∈ S n,
      { rw [← set.mem_Union, @Union_spanning_sets α m (μ.trim hm)],
        exact set.mem_univ a, },
      obtain ⟨n₀, han₀⟩ := h_exists,
      refine le_trans _ (le_supr _ n₀),
      simp_rw [F, set.indicator_apply],
      simp [han₀], }, },
  have h_eq : ∫⁻ (a : α), nnnorm (f a) ∂μ = ∫⁻ (a : α), ⨆ n, (nnnorm (F n a) : ℝ≥0∞) ∂μ,
    from lintegral_congr (λ a, (h_F_lim a).symm),
  rw [h_eq, lintegral_supr],
  { have h_F_bound : ∀ n, ∫⁻ a, nnnorm (F n a) ∂μ ≤ C,
    { intro n,
      simp_rw [F, nnnorm_indicator_eq_indicator_nnnorm, ennreal.coe_indicator],
      rw lintegral_indicator _ (hm _ (hS_meas n)),
      exact hf (S n) (hS_meas n)
        ((le_trim hm).trans_lt (@measure_spanning_sets_lt_top α m (μ.trim hm) _ n)), },
    exact supr_le h_F_bound, },
  { have h_F_meas : ∀ n, measurable (F n), from λ n, hf_meas.indicator (hm _ (hS_meas n)),
    exact λ n, (h_F_meas n).nnnorm.ennreal_coe, },
  { intros n₁ n₂ hn₁₂ a,
    simp_rw [F, set.indicator_apply],
    split_ifs,
    { exact le_rfl, },
    { have h_S_mono : monotone S, from @monotone_spanning_sets α m (μ.trim hm) _,
      exact absurd (set.mem_of_mem_of_subset h (h_S_mono hn₁₂)) h_1, },
    { simp, },
    { exact le_rfl, }, },
end

lemma integrable_of_bounded_on_finite' [opens_measurable_space H] (hm : m ≤ m0)
  [@sigma_finite α m (μ.trim hm)] (C : ℝ≥0∞) (hC : C < ∞) (f : α → H) (hf_meas : measurable f)
  (hf : ∀ s : set α, @measurable_set _ m s → μ s < ∞ → ∫⁻ x in s, nnnorm (f x) ∂μ ≤ C) :
  integrable f μ :=
begin
  refine ⟨hf_meas.ae_measurable, _⟩,
  exact (lintegral_nnnorm_le_of_bounded_on_finite hm C hC f hf_meas hf).trans_lt hC,
end

lemma integrable_of_bounded_on_finite [opens_measurable_space H] [sigma_finite μ]
  (C : ℝ≥0∞) (hC : C < ∞) (f : α → H) (hf_meas : ae_measurable f μ)
  (hf : ∀ s : set α, measurable_set s → μ s < ∞ → ∫⁻ x in s, nnnorm (f x) ∂μ ≤ C) :
  integrable f μ :=
begin
  let f' := hf_meas.mk f,
  have hf' : ∀ s : set α, measurable_set s → μ s < ∞ → ∫⁻ x in s, nnnorm (f' x) ∂μ ≤ C,
  { refine λ s hs hμs, (le_of_eq _).trans (hf s hs hμs),
    refine lintegral_congr_ae (ae_restrict_of_ae (hf_meas.ae_eq_mk.mono (λ x hx, _))),
    rw hx, },
  rw integrable_congr hf_meas.ae_eq_mk,
  haveI : sigma_finite (μ.trim le_rfl) := by rwa trim_eq_self,
  exact integrable_of_bounded_on_finite' le_rfl C hC f' hf_meas.measurable_mk hf',
end

lemma indicator_Lp_disjoint_union (s t : set α)
  (hs : measurable_set s) (ht : measurable_set t) (hst : s ∩ t = ∅) (hμs : μ s < ∞)
  (hμt : μ t < ∞) :
  (indicator_Lp 2 (hs.union ht) (1 : ℝ)
      (or.inr ((measure_union_le s t).trans_lt (ennreal.add_lt_top.mpr ⟨hμs, hμt⟩))))
    = indicator_Lp 2 hs (1 : ℝ) (or.inr hμs) + indicator_Lp 2 ht (1 : ℝ) (or.inr hμt) :=
begin
  have hs_eq := indicator_Lp_coe_fn 2 hs (1 : ℝ) (or.inr hμs),
  have ht_eq := indicator_Lp_coe_fn 2 ht (1 : ℝ) (or.inr hμt),
  ext1,
  refine eventually_eq.trans _ (Lp.coe_fn_add _ _).symm,
  refine (indicator_Lp_coe_fn 2 (hs.union ht) (1 : ℝ)
    (or.inr ((measure_union_le s t).trans_lt (ennreal.add_lt_top.mpr ⟨hμs, hμt⟩)))).trans _,
  refine eventually_eq.trans _ (eventually_eq.add hs_eq.symm ht_eq.symm),
  refine eventually_of_forall (λ x, _),
  simp_rw set.indicator_apply,
  by_cases hxs : x ∈ s,
  { simp only [hxs, if_true, true_or, ite_eq_right_iff, self_eq_add_right, one_ne_zero,
      set.mem_union_eq],
    intro hxt,
    rw [← set.mem_empty_eq x, ← hst],
    exact set.mem_inter hxs hxt, },
  { simp only [hxs, false_or, if_false, zero_add, set.mem_union_eq],
    congr, },
end

/-! ## Extension of the conditional expectation to L¹

We define `T_condexp 𝕂 hm s hs : E' →L[ℝ] α →₁[μ] E'`, which to a value `x : E'` associates the
conditional expectation of the measurable set `s` multiplies (as scalar) by `x`. -/

variables (𝕂)
include 𝕂
def condexp_smul (hm : m ≤ m0) (s : set α) (hs : measurable_set s) (hμs : μ s < ∞) (x : E') :
  α → E' :=
  λ a, condexp_L2_clm ℝ hm (indicator_Lp 2 hs (1 : ℝ) (or.inr hμs)) a • x

lemma condexp_smul_zero  (hm : m ≤ m0) (s : set α) (hs : measurable_set s) (hμs : μ s < ∞) :
  condexp_smul 𝕂 hm s hs hμs (0 : E') = 0 :=
by { rw condexp_smul, simp_rw smul_zero, refl, }

lemma measurable_condexp_smul (hm : m ≤ m0) (s : set α) (hs : measurable_set s)
  (hμs : μ s < ∞) (x : E') :
  measurable (condexp_smul 𝕂 hm s hs hμs x) :=
by { rw [condexp_smul, Lp_sub_coe], exact (Lp.measurable _).smul_const x, }

lemma integrable_on_condexp_smul (hm : m ≤ m0) (s : set α) (hs : measurable_set s) (hμs : μ s < ∞)
  (x : E') {t : set α} (ht : μ t < ∞) :
  integrable_on (condexp_smul 𝕂 hm s hs hμs x) t μ :=
begin
  by_cases hx0 : x = 0,
  { rw [hx0, condexp_smul_zero],
    exact integrable_on_zero, },
  { exact (integrable_smul_const hx0).mpr (integrable_on_condexp_L2_of_measure_finite hm ht _), },
end

lemma lintegral_nnnorm_condexp_L2_indicator_le (hm : m ≤ m0) (s : set α) (hs : measurable_set s)
  (hμs : μ s < ∞) {t : set α} (ht : @measurable_set _ m t) (hμt : μ t < ∞) :
  ∫⁻ a in t, nnnorm (condexp_L2_clm ℝ hm (indicator_Lp 2 hs (1 : ℝ) (or.inr hμs)) a) ∂μ
    ≤ μ (s ∩ t) :=
begin
  refine (lintegral_nnnorm_condexp_L2_le_on hm ht hμt _).trans (le_of_eq _),
  have h_eq : ∫⁻ (x : α) in t, (nnnorm ((indicator_Lp 2 hs (1 : ℝ) (or.inr hμs)) x)) ∂μ
    = ∫⁻ (x : α) in t, s.indicator (λ x, (1 : ℝ≥0∞)) x ∂μ,
  { refine lintegral_congr_ae (ae_restrict_of_ae _),
    refine (indicator_Lp_coe_fn 2 hs (1 : ℝ) (or.inr hμs)).mono (λ x hx, _),
    rw hx,
    simp_rw set.indicator_apply,
    split_ifs; simp, },
  rw [h_eq, lintegral_indicator _ hs, lintegral_const, measure.restrict_restrict hs],
  simp only [one_mul, set.univ_inter, measurable_set.univ, measure.restrict_apply],
end

lemma lintegral_nnnorm_condexp_smul_le' (hm : m ≤ m0) (s : set α) (hs : measurable_set s)
  (hμs : μ s < ∞) (x : E') {t : set α} (ht : @measurable_set _ m t) (hμt : μ t < ∞) :
  ∫⁻ a in t, nnnorm (condexp_smul 𝕂 hm s hs hμs x a) ∂μ ≤ μ (s ∩ t) * nnnorm x :=
begin
  simp_rw [condexp_smul, nnnorm_smul, ennreal.coe_mul],
  rw lintegral_mul_const,
  swap, { rw Lp_sub_coe, exact (Lp.measurable _).nnnorm.ennreal_coe, },
  refine ennreal.mul_le_mul _ le_rfl,
  exact lintegral_nnnorm_condexp_L2_indicator_le 𝕂 hm s hs hμs ht hμt,
end

lemma lintegral_nnnorm_condexp_smul_le (hm : m ≤ m0) [@sigma_finite α m (μ.trim hm)]
  (s : set α) (hs : measurable_set s) (hμs : μ s < ∞) (x : E') :
  ∫⁻ a, nnnorm (condexp_smul 𝕂 hm s hs hμs x a) ∂μ ≤ μ s * nnnorm x :=
begin
  refine lintegral_nnnorm_le_of_bounded_on_finite hm (μ s * nnnorm x)
    (ennreal.mul_lt_top hμs ennreal.coe_lt_top) (condexp_smul 𝕂 hm s hs hμs x)
    (measurable_condexp_smul 𝕂 hm s hs hμs x) (λ t ht hμt, _),
  refine (lintegral_nnnorm_condexp_smul_le' 𝕂 hm s hs hμs x ht hμt).trans _,
  exact ennreal.mul_le_mul (measure_mono (set.inter_subset_left _ _)) le_rfl,
end

lemma integrable_condexp_smul (hm : m ≤ m0) [@sigma_finite α m (μ.trim hm)]
  (s : set α) (hs : measurable_set s) (hμs : μ s < ∞) (x : E') :
  integrable (condexp_smul 𝕂 hm s hs hμs x) μ :=
begin
  refine ⟨(measurable_condexp_smul 𝕂 hm s hs hμs x).ae_measurable, _⟩,
  exact (lintegral_nnnorm_condexp_smul_le 𝕂 hm s hs hμs x).trans_lt
    (ennreal.mul_lt_top hμs ennreal.coe_lt_top),
end

lemma condexp_smul_add (hm : m ≤ m0) (s : set α) (hs : measurable_set s) (hμs : μ s < ∞)
  (x y : E') :
  condexp_smul 𝕂 hm s hs hμs (x + y) =
    condexp_smul 𝕂 hm s hs hμs x + condexp_smul 𝕂 hm s hs hμs y :=
by { simp_rw [condexp_smul, smul_add], refl, }

lemma condexp_smul_smul (hm : m ≤ m0) (s : set α) (hs : measurable_set s) (hμs : μ s < ∞)
  (x : E') (c : 𝕂) :
  condexp_smul 𝕂 hm s hs hμs (c • x) = c • condexp_smul 𝕂 hm s hs hμs x :=
begin
  simp_rw [condexp_smul],
  ext1 a,
  rw [pi.smul_apply, ← smul_assoc, smul_comm, smul_assoc],
end

lemma condexp_smul_smul_ℝ (hm : m ≤ m0) (s : set α) (hs : measurable_set s) (hμs : μ s < ∞)
  (x : E') (c : ℝ) :
  condexp_smul 𝕂 hm s hs hμs (c • x) = c • condexp_smul 𝕂 hm s hs hμs x :=
begin
  simp_rw [condexp_smul],
  ext1 a,
  rw [pi.smul_apply, ← smul_assoc, smul_comm, smul_assoc],
end

def T_condexp_fn (hm : m ≤ m0) (μ : measure α) [@sigma_finite α m (μ.trim hm)]
  (s : set α) (hs : measurable_set s) (x : E') :
  α →₁[μ] E' :=
dite (μ s < ∞)
  (λ hμs, (mem_ℒp_one_iff_integrable.mpr (integrable_condexp_smul 𝕂 hm s hs hμs x)).to_Lp _)
  (λ hμs, 0)

lemma T_condexp_fn_coe_of_finite (hm : m ≤ m0) (μ : measure α) [@sigma_finite α m (μ.trim hm)]
  (s : set α) (hs : measurable_set s) (hμs : μ s < ∞) (x : E') :
  T_condexp_fn 𝕂 hm μ s hs x =ᵐ[μ] condexp_smul 𝕂 hm s hs hμs x :=
by { simp only [T_condexp_fn, hμs, dif_pos], exact mem_ℒp.coe_fn_to_Lp _, }

lemma T_condexp_fn_eq_zero_of_not_finite (hm : m ≤ m0) (μ : measure α)
  [@sigma_finite α m (μ.trim hm)] (s : set α) (hs : measurable_set s) (hμs : ¬ μ s < ∞) (x : E') :
  T_condexp_fn 𝕂 hm μ s hs x = 0 :=
by simp only [T_condexp_fn, hμs, dif_neg, not_false_iff]

lemma T_condexp_fn_add (hm : m ≤ m0) [@sigma_finite α m (μ.trim hm)]
  (s : set α) (hs : measurable_set s) (x y : E') :
  T_condexp_fn 𝕂 hm μ s hs (x + y) = T_condexp_fn 𝕂 hm μ s hs x + T_condexp_fn 𝕂 hm μ s hs y :=
begin
  simp_rw T_condexp_fn,
  split_ifs,
  { rw ← mem_ℒp.to_Lp_add,
    congr,
    exact condexp_smul_add 𝕂 hm s hs h x y, },
  { rw zero_add _, },
end

lemma T_condexp_fn_smul (hm : m ≤ m0) [@sigma_finite α m (μ.trim hm)]
  (s : set α) (hs : measurable_set s) (x : E') (c : 𝕂) :
  T_condexp_fn 𝕂 hm μ s hs (c • x) = c • T_condexp_fn 𝕂 hm μ s hs x :=
begin
  simp_rw T_condexp_fn,
  split_ifs,
  { rw ← mem_ℒp.to_Lp_const_smul,
    congr,
    exact condexp_smul_smul 𝕂 hm s hs h x c, },
  { rw smul_zero _, },
end

lemma T_condexp_fn_smul_ℝ (hm : m ≤ m0) [@sigma_finite α m (μ.trim hm)]
  (s : set α) (hs : measurable_set s) (x : E') (c : ℝ) :
  T_condexp_fn 𝕂 hm μ s hs (c • x) = c • T_condexp_fn 𝕂 hm μ s hs x :=
begin
  simp_rw T_condexp_fn,
  split_ifs,
  { rw ← mem_ℒp.to_Lp_const_smul,
    congr,
    exact condexp_smul_smul_ℝ 𝕂 hm s hs h x c, },
  { rw smul_zero _, },
end

lemma norm_T_condexp_fn_le (hm : m ≤ m0) (μ : measure α) [@sigma_finite α m (μ.trim hm)]
  (s : set α) (hs : measurable_set s) (x : E') :
  ∥T_condexp_fn 𝕂 hm μ s hs x∥ ≤ (μ s).to_real * ∥x∥ :=
begin
  by_cases hμs : μ s < ∞,
  swap,
  { simp only [T_condexp_fn, hμs, measure_theory.Lp.norm_zero, dif_neg, not_false_iff],
    exact mul_nonneg ennreal.to_real_nonneg (norm_nonneg _), },
  have : 0 ≤ ∫ (a : α), ∥T_condexp_fn 𝕂 hm μ s hs x a∥ ∂μ,
    from integral_nonneg (λ a, norm_nonneg _),
  rw [L1.norm_eq_integral_norm, ← ennreal.to_real_of_real (norm_nonneg x), ← ennreal.to_real_mul,
    ← ennreal.to_real_of_real this, ennreal.to_real_le_to_real ennreal.of_real_ne_top
      (ennreal.mul_ne_top hμs.ne ennreal.of_real_ne_top),
    ← lintegral_nnnorm_eq_integral_norm],
  swap, { rw [← mem_ℒp_one_iff_integrable], exact Lp.mem_ℒp _, },
  have h_eq : ∫⁻ a, nnnorm (T_condexp_fn 𝕂 hm μ s hs x a) ∂μ
    = ∫⁻ a, nnnorm (condexp_smul 𝕂 hm s hs hμs x a) ∂μ,
  { refine lintegral_congr_ae _,
    refine (T_condexp_fn_coe_of_finite 𝕂 hm μ s hs hμs x).mono (λ z hz, _),
    dsimp only,
    rw hz, },
  rw [h_eq, of_real_norm_eq_coe_nnnorm],
  exact lintegral_nnnorm_condexp_smul_le 𝕂 hm s hs hμs x,
end

lemma continuous_T_condexp_hm (hm : m ≤ m0) (μ : measure α) [@sigma_finite α m (μ.trim hm)]
  (s : set α) (hs : measurable_set s) :
  continuous (λ x : E', T_condexp_fn 𝕂 hm μ s hs x) :=
continuous_of_linear_of_bound (T_condexp_fn_add 𝕂 hm s hs)
  (λ c x, T_condexp_fn_smul_ℝ 𝕂 hm s hs x c) (norm_T_condexp_fn_le 𝕂 hm μ s hs)

variables (E')
def T_condexp (hm : m ≤ m0) (μ : measure α) [@sigma_finite α m (μ.trim hm)]
  (s : set α) (hs : measurable_set s) :
  E' →L[ℝ] α →₁[μ] E' :=
{ to_fun := T_condexp_fn 𝕂 hm μ s hs,
  map_add' := T_condexp_fn_add 𝕂 hm s hs,
  map_smul' := λ c x, T_condexp_fn_smul_ℝ 𝕂 hm s hs x c,
  cont := continuous_T_condexp_hm 𝕂 hm μ s hs, }
variables {E'}

lemma condexp_L2_disjoint_union (hm : m ≤ m0) (s t : set α) (hs : measurable_set s)
  (ht : measurable_set t) (hst : s ∩ t = ∅) (hμs : μ s < ∞) (hμt : μ t < ∞) :
  condexp_L2_clm ℝ hm (indicator_Lp 2 (hs.union ht) (1 : ℝ)
    (or.inr ((measure_union_le s t).trans_lt (ennreal.add_lt_top.mpr ⟨hμs, hμt⟩))))
    = condexp_L2_clm ℝ hm (indicator_Lp 2 hs (1 : ℝ) (or.inr hμs))
    + condexp_L2_clm ℝ hm (indicator_Lp 2 ht (1 : ℝ) (or.inr hμt)) :=
begin
  have h_add : (indicator_Lp 2 (hs.union ht) (1 : ℝ)
      (or.inr ((measure_union_le s t).trans_lt (ennreal.add_lt_top.mpr ⟨hμs, hμt⟩))))
    = indicator_Lp 2 hs (1 : ℝ) (or.inr hμs) + indicator_Lp 2 ht (1 : ℝ) (or.inr hμt),
  from indicator_Lp_disjoint_union s t hs ht hst hμs hμt,
  rw h_add,
  rw (condexp_L2_clm ℝ hm).map_add,
end

lemma condexp_smul_disjoint_union (hm : m ≤ m0) (s t : set α) (hs : measurable_set s)
  (ht : measurable_set t) (hst : s ∩ t = ∅) (hμs : μ s < ∞) (hμt : μ t < ∞) (x : E') :
  condexp_smul 𝕂 hm (s ∪ t) (hs.union ht)
      ((measure_union_le s t).trans_lt (ennreal.add_lt_top.mpr ⟨hμs, hμt⟩)) x
    =ᵐ[μ] condexp_smul 𝕂 hm s hs hμs x + condexp_smul 𝕂 hm t ht hμt x :=
begin
  simp_rw condexp_smul,
  rw condexp_L2_disjoint_union 𝕂 hm s t hs ht hst hμs hμt,
  simp_rw pi.add_apply,
  sorry
end

lemma T_condexp_fn_disjoint_union (hm : m ≤ m0) [@sigma_finite α m (μ.trim hm)] (s t : set α)
  (hs : measurable_set s) (ht : measurable_set t) (hst : s ∩ t = ∅) (hμs : μ s < ∞)
  (hμt : μ t < ∞) (x : E') :
  T_condexp_fn 𝕂 hm μ (s ∪ t) (hs.union ht) x
    = T_condexp_fn 𝕂 hm μ s hs x + T_condexp_fn 𝕂 hm μ t ht x :=
begin
  ext1,
  have hTs := T_condexp_fn_coe_of_finite 𝕂 hm μ s hs hμs x,
  have hTt := T_condexp_fn_coe_of_finite 𝕂 hm μ t ht hμt x,
  have hT_union := T_condexp_fn_coe_of_finite 𝕂 hm μ (s ∪ t) (hs.union ht)
    ((measure_union_le s t).trans_lt (ennreal.add_lt_top.mpr ⟨hμs, hμt⟩)) x,
  refine hT_union.trans _,
  refine eventually_eq.trans _ (Lp.coe_fn_add _ _).symm,
  refine eventually_eq.trans _ (eventually_eq.add hTs.symm hTt.symm),
  exact condexp_smul_disjoint_union 𝕂 hm s t hs ht hst hμs hμt x,
end

lemma T_condexp_disjoint_union (hm : m ≤ m0) [@sigma_finite α m (μ.trim hm)] (s t : set α)
  (hs : measurable_set s) (ht : measurable_set t) (hst : s ∩ t = ∅) (hμs : μ s < ∞)
  (hμt : μ t < ∞) :
  T_condexp E' 𝕂 hm μ (s ∪ t) (hs.union ht)
    = T_condexp E' 𝕂 hm μ s hs + T_condexp E' 𝕂 hm μ t ht :=
by { ext1 x, exact T_condexp_fn_disjoint_union 𝕂 hm s t hs ht hst hμs hμt x, }

lemma T_condexp_smul (hm : m ≤ m0) [@sigma_finite α m (μ.trim hm)]
  (s : set α) (hs : measurable_set s) (x : E') (c : 𝕂) :
  T_condexp E' 𝕂 hm μ s hs (c • x) = c • T_condexp E' 𝕂 hm μ s hs x :=
T_condexp_fn_smul 𝕂 hm s hs x c

lemma norm_T_condexp_le (hm : m ≤ m0) [@sigma_finite α m (μ.trim hm)]
  (s : set α) (hs : measurable_set s) :
  ∥T_condexp E' 𝕂 hm μ s hs∥ ≤ (μ s).to_real :=
begin
  refine continuous_linear_map.op_norm_le_bound _ ennreal.to_real_nonneg (λ x, _),
  exact norm_T_condexp_fn_le 𝕂 hm μ s hs x,
end

omit 𝕂
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
  by_cases h_int_on : integrable_on (f - condexp_L2_clm 𝕂 hm f) s μ,
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

lemma integral_condexp_L2_eq_ℝ [finite_measure μ] (hm : m ≤ m0) {f : Lp ℝ 2 μ} {s : set α}
  (hs : @measurable_set α m s) :
  ∫ x in s, condexp_L2_clm ℝ hm f x ∂μ = ∫ x in s, f x ∂μ :=
integral_condexp_L2_eq_of_measure_finite_ℝ hm hs (measure_lt_top μ s)

lemma integrable_on_condexp_L2_of_measure_finite (hm : m ≤ m0) {s : set α}
  (hs : @measurable_set _ m s) (hμs : μ s < ∞) {f : Lp ℝ 2 μ} (hf : integrable_on f s μ) :
  integrable_on (condexp_L2_clm ℝ hm f) s μ :=
begin
  sorry
end

lemma condexp_L2_zero (hm : m ≤ m0) (f : Lp E' 2 μ) (hf : f =ᵐ[μ] 0) :
  condexp_L2_clm 𝕂 hm f =ᵐ[μ] 0 :=
begin
  have hf_zero : f = 0, by {ext1, exact hf.trans (coe_fn_zero E' 2 μ).symm, },
  rw [hf_zero, (condexp_L2_clm 𝕂 hm).map_zero],
  exact coe_fn_zero E' 2 μ,
end

lemma integrable_condexp_L2 (hm : m ≤ m0) (f : Lp E' 2 μ) (hf : integrable f μ) :
  integrable (condexp_L2_clm 𝕂 hm f) μ :=
begin
  sorry,
end

/-- Without a finiteness hypothesis on the measure, the integral of `condexp_L2` on a `m`-measurable
set `s` with `μ s < ∞` is equal to the integral of `f` on `s`. -/
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
  refine metric.continuous_iff.mpr (λ f ε hε_pos, _),
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
    refine ennreal.mul_ne_top (Lp.snorm_ne_top _) _,
    exact ennreal.rpow_ne_top_of_nonneg (by simp [zero_le_one]) (measure_ne_top μ set.univ), },
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

section condexp_L1s_ℝ

variables {m m0 : measurable_space α} (hm : m ≤ m0) [complete_space E] {μ : measure α}
  [borel_space 𝕂]

variables (𝕂)
/-- Conditional expectation as a linear map from the simple functions of L1 to ae_eq_fun. -/
def condexp_L1s_to_ae_eq_fun_lm : (α →₁ₛ[μ] E) →ₗ[𝕂] (α →ₘ[μ] E) :=
(Lp_submodule E 2 μ 𝕂).subtype.comp ((Lp_sub E 𝕂 m 2 μ).subtype.comp
  ((condexp_L2_clm 𝕂 hm).to_linear_map.comp (L1s_to_L2_lm 𝕂)))

lemma condexp_L1s_to_ae_eq_fun_ae_eq_condexp_L2 (f : α →₁ₛ[μ] E) :
  condexp_L1s_to_ae_eq_fun_lm 𝕂 hm f =ᵐ[μ] condexp_L2_clm 𝕂 hm (L1s_to_L2_lm 𝕂 f) :=
by refl

variables [finite_measure μ]

lemma is_condexp_condexp_L2_L1s_to_L2 (f : α →₁ₛ[μ] E') :
  is_condexp m (condexp_L2_clm 𝕂 hm (L1s_to_L2_lm 𝕂 f) : α → E') f μ :=
is_condexp_congr_ae_right' hm (L1s_to_L2_coe_fn f) (is_condexp_condexp_L2 hm _)

lemma is_condexp_condexp_L1s_to_ae_eq_fun (f : α →₁ₛ[μ] E') :
  is_condexp m ((condexp_L1s_to_ae_eq_fun_lm 𝕂 hm f) : α → E') f μ :=
is_condexp_congr_ae_left' hm (condexp_L1s_to_ae_eq_fun_ae_eq_condexp_L2 𝕂 hm _).symm
  (is_condexp_condexp_L2_L1s_to_L2 𝕂 hm f)

lemma integral_condexp_L1s_to_ae_eq_fun (f : α →₁ₛ[μ] E') {s : set α} (hs : @measurable_set α m s) :
  ∫ a in s, (condexp_L1s_to_ae_eq_fun_lm 𝕂 hm f) a ∂μ = ∫ a in s, f a ∂μ :=
(is_condexp_condexp_L1s_to_ae_eq_fun 𝕂 hm f).2 s hs

include 𝕂 hm

/-- Conditional expectation as a function from the simple functions of L1 to L1. -/
def condexp_L1s_to_L1 (f : α →₁ₛ[μ] E) : α →₁[μ] E :=
begin
  refine ⟨condexp_L1s_to_ae_eq_fun_lm 𝕂 hm f, _⟩,
  rw [mem_Lp_iff_mem_ℒp, mem_ℒp_one_iff_integrable,
    integrable_congr (condexp_L1s_to_ae_eq_fun_ae_eq_condexp_L2 𝕂 hm f)],
  exact Lp.integrable _ ennreal.one_le_two,
end

lemma condexp_L1s_to_L1_coe (f : α →₁ₛ[μ] E) :
  (condexp_L1s_to_L1 𝕂 hm f : α →ₘ[μ] E) = condexp_L1s_to_ae_eq_fun_lm 𝕂 hm f :=
rfl

lemma condexp_L1s_to_L1_ae_eq_condexp_L1s_to_ae_eq_fun (f : α →₁ₛ[μ] E) :
  condexp_L1s_to_L1 𝕂 hm f =ᵐ[μ] condexp_L1s_to_ae_eq_fun_lm 𝕂 hm f :=
begin
  sorry
end

lemma condexp_L1s_to_L1_add (f g : α →₁ₛ[μ] E) :
  condexp_L1s_to_L1 𝕂 hm (f + g) = condexp_L1s_to_L1 𝕂 hm f + condexp_L1s_to_L1 𝕂 hm g :=
begin
  refine subtype.ext _,
  push_cast,
  simp_rw condexp_L1s_to_L1_coe,
  exact (condexp_L1s_to_ae_eq_fun_lm 𝕂 hm).map_add _ _,
end

lemma condexp_L1s_to_L1_smul (c : 𝕂) (f : α →₁ₛ[μ] E) :
  condexp_L1s_to_L1 𝕂 hm (c • f) = c • condexp_L1s_to_L1 𝕂 hm f :=
begin
  refine subtype.ext _,
  simp_rw condexp_L1s_to_L1_coe,
  exact (condexp_L1s_to_ae_eq_fun_lm 𝕂 hm).map_smul _ _,
end

/-- Conditional expectation as a linear map from the simple functions of L1 to L1. -/
def condexp_L1s : (α →₁ₛ[μ] E) →ₗ[𝕂] (α →₁[μ] E) :=
{ to_fun := λ f, condexp_L1s_to_L1 𝕂 hm f,
  map_add' := condexp_L1s_to_L1_add 𝕂 hm,
  map_smul' := condexp_L1s_to_L1_smul 𝕂 hm, }

lemma is_condexp_condexp_L1s (f : α →₁ₛ[μ] E') : is_condexp m (condexp_L1s 𝕂 hm f) f μ :=
is_condexp_congr_ae_left' hm (condexp_L1s_to_L1_ae_eq_condexp_L1s_to_ae_eq_fun 𝕂 hm _).symm
  (is_condexp_condexp_L2_L1s_to_L2 𝕂 hm f)

lemma integral_condexp_L1s (f : α →₁ₛ[μ] E') {s : set α} (hs : @measurable_set α m s) :
  ∫ a in s, (condexp_L1s 𝕂 hm f) a ∂μ = ∫ a in s, f a ∂μ :=
(is_condexp_condexp_L1s 𝕂 hm f).2 s hs
omit 𝕂 hm
variables {𝕂}

lemma condexp_L1s_nonneg {f : α →₁ₛ[μ] ℝ} (hf : 0 ≤ᵐ[μ] f) : 0 ≤ᵐ[μ] condexp_L1s ℝ hm f :=
is_condexp.nonneg hm hf (is_condexp_condexp_L1s ℝ hm f) (Lp.integrable _ le_rfl)

lemma condexp_L1s_nonpos {f : α →₁ₛ[μ] ℝ} (hf : f ≤ᵐ[μ] 0) : condexp_L1s ℝ hm f ≤ᵐ[μ] 0 :=
is_condexp.nonpos hm hf (is_condexp_condexp_L1s ℝ hm f) (Lp.integrable _ le_rfl)

lemma condexp_L1s_mono {f g : α →₁ₛ[μ] ℝ} (hfg : f ≤ᵐ[μ] g) :
  condexp_L1s ℝ hm f ≤ᵐ[μ] condexp_L1s ℝ hm g :=
is_condexp.mono hm hfg (is_condexp_condexp_L1s ℝ hm f) (Lp.integrable _ le_rfl)
  (Lp.integrable _ le_rfl) (is_condexp_condexp_L1s ℝ hm g) (Lp.integrable _ le_rfl)
  (Lp.integrable _ le_rfl)

lemma condexp_L1s_R_jensen_norm (f : α →₁ₛ[μ] ℝ) :
  ∀ᵐ x ∂μ, ∥condexp_L1s ℝ hm f x∥
    ≤ condexp_L1s ℝ hm (L1.simple_func.map (λ x, ∥x∥) f norm_zero) x :=
begin
  have h := is_condexp_congr_ae_right' hm (L1.simple_func.map_coe (λ (x : ℝ), ∥x∥) f norm_zero)
    (is_condexp_condexp_L1s ℝ hm (L1.simple_func.map (λ (x : ℝ), ∥x∥) f norm_zero)),
  exact is_condexp.jensen_norm hm (is_condexp_condexp_L1s ℝ hm f) h
      (Lp.integrable _ le_rfl) (Lp.integrable _ le_rfl) (Lp.integrable _ le_rfl),
end

lemma norm_condexp_L1s_le_R (f : α →₁ₛ[μ] ℝ) : ∥condexp_L1s ℝ hm f∥ ≤ ∥f∥ :=
begin
  simp_rw [L1.simple_func.norm_eq, norm_def],
  rw ennreal.to_real_le_to_real (Lp.snorm_ne_top _) (Lp.snorm_ne_top _),
  simp_rw snorm_one_eq_lintegral_nnnorm,
  let F := λ x : ℝ, ∥x∥,
  have h_left : ∫⁻ a, (nnnorm (((condexp_L1s ℝ hm) f) a) : ℝ≥0∞) ∂μ
      = ∫⁻ a, ennreal.of_real (∥((condexp_L1s ℝ hm) f) a∥) ∂μ,
    by { congr, ext1 x, rw ← of_real_norm_eq_coe_nnnorm, },
  have h_right : ∫⁻ a, (nnnorm ((f : Lp ℝ 1 μ) a) : ℝ≥0∞) ∂μ
      = ∫⁻ a, ennreal.of_real (∥(f : Lp ℝ 1 μ) a∥) ∂μ,
    by { congr, ext1 x, rw ← of_real_norm_eq_coe_nnnorm, },
  rw [h_left, h_right],
  have h_le : ∫⁻ a, ennreal.of_real (∥((condexp_L1s ℝ hm) f) a∥) ∂μ
    ≤ ∫⁻ a, ennreal.of_real (condexp_L1s ℝ hm (L1.simple_func.map F f norm_zero) a) ∂μ,
  { refine lintegral_mono_ae ((condexp_L1s_R_jensen_norm hm f).mono (λ x hx, _)),
    rwa ennreal.of_real_le_of_real_iff ((norm_nonneg _).trans hx), },
  refine h_le.trans _,
  have h_integral_eq := integral_condexp_L1s ℝ hm (L1.simple_func.map F f norm_zero)
    (@measurable_set.univ α m),
  rw [integral_univ, integral_univ] at h_integral_eq,
  rw ← (ennreal.to_real_le_to_real _ _),
  swap, { have h := Lp.snorm_ne_top (condexp_L1s ℝ hm (L1.simple_func.map F f norm_zero)),
    rw snorm_one_eq_lintegral_nnnorm at h,
    simp_rw [← of_real_norm_eq_coe_nnnorm, ← lt_top_iff_ne_top] at h,
    refine (lt_of_le_of_lt _ h).ne,
    refine lintegral_mono_ae (eventually_of_forall (λ x, ennreal.of_real_le_of_real _)),
    rw real.norm_eq_abs,
    exact le_abs_self _, },
  swap, { simp_rw of_real_norm_eq_coe_nnnorm,
    have h := Lp.snorm_ne_top (f : α →₁[μ] ℝ),
    rw snorm_one_eq_lintegral_nnnorm at h,
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
  ∥condexp_L1s ℝ hm (indicator_L1s hs c hμsc)∥ ≤ ∥c∥ * (μ s).to_real :=
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
