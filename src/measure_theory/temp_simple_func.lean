/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import analysis.normed_space.inner_product
import measure_theory.l2_space

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


lemma mem_ℒ2_simple_func_L1 [measurable_space α] {μ : measure α} (f : α →₁ₛ[μ] G) :
  mem_ℒp f 2 μ :=
(mem_ℒp_congr_ae (L1.simple_func.to_simple_func_eq_to_fun f).symm).mpr
  (simple_func.mem_ℒp_of_integrable 2 (L1.simple_func.integrable _))

local notation `to_simple_func` := L1.simple_func.to_simple_func
local notation `indicator_L1s` := L1.simple_func.indicator_L1s

section indicator_L1s'

variables [measurable_space α] {μ : measure α} {s t : set α} {hs : measurable_set s}
  {c : G} {hμsc : c = 0 ∨ μ s < ∞}

--lemma to_simple_func_indicator_L1s_coe_fn :
--  to_simple_func (indicator_L1s hs c hμsc) =ᵐ[μ] indicator_simple_func hs c :=
--(L1.simple_func.to_simple_func_eq_to_fun _).trans
--  (L1.simple_func.indicator_L1s_coe_fn.trans indicator_simple_func_coe_ae.symm)

lemma indicator_const_eq_smul {α} [add_comm_monoid γ] [semimodule ℝ γ] (s : set α) (c : γ) :
  s.indicator (λ (_x : α), c) = λ (x : α), s.indicator (λ (_x : α), (1 : ℝ)) x • c :=
by { ext1 x, by_cases h_mem : x ∈ s; simp [h_mem], }

lemma indicator_L1s_eq_smul [normed_space ℝ G] (c : G) (hμs : μ s < ∞) :
  indicator_L1s hs c (or.inr hμs)
    =ᵐ[μ] λ x, ((indicator_L1s hs (1 : ℝ) (or.inr hμs)) x) • c :=
begin
  let hμs1 : (1:ℝ) = 0 ∨ μ s < ∞ := or.inr hμs,
  have h : (λ (x : α), (indicator_L1s hs (1:ℝ) hμs1) x • c) =ᵐ[μ] λ x,
    (s.indicator (λ _, (1:ℝ)) x) • c,
  { change (λ x, x • c) ∘ (indicator_L1s hs (1:ℝ) hμs1)
      =ᵐ[μ] λ (x : α), s.indicator (λ x, (1:ℝ)) x • c,
    exact eventually_eq.fun_comp L1.simple_func.indicator_L1s_coe_fn (λ x, x • c), },
  refine (L1.simple_func.indicator_L1s_coe_fn).trans (eventually_eq.trans _ h.symm),
  exact eventually_of_forall (λ x, by rw indicator_const_eq_smul s c),
end

lemma indicator_L1s_coe_ae_le (c : ℝ) (hμsc : c = 0 ∨ μ s < ∞) :
  ∀ᵐ x ∂μ, abs (indicator_L1s hs c hμsc x) ≤ abs c :=
begin
  refine (@L1.simple_func.indicator_L1s_coe_fn α ℝ _ _ _ _ _ μ s hs c hμsc).mono (λ x hx, _),
  rw hx,
  by_cases hx_mem : x ∈ s; simp [hx_mem, abs_nonneg c],
end

lemma norm_indicator_L1s : ∥indicator_L1s hs c hμsc∥ = ∥c∥ * (μ s).to_real :=
by rw [L1.simple_func.norm_eq, L1.simple_func.indicator_L1s_coe,
  norm_indicator_Lp ennreal.zero_lt_one ennreal.coe_ne_top, ennreal.one_to_real, div_one,
  real.rpow_one]

lemma const_smul_indicator_L1s [borel_space 𝕂] {s : set α} (hs : measurable_set s) (x : F)
  (hμsx : x = 0 ∨ μ s < ∞) (c : 𝕂) :
  c • (indicator_L1s hs x hμsx) = indicator_L1s hs (c • x)
    (by {cases hμsx, rw hμsx, exact or.inl (smul_zero _), exact or.inr hμsx, }) :=
begin
  ext1,
  rw [← L1.simple_func.coe_coe, L1.simple_func.coe_smul],
  refine (Lp.coe_fn_smul c _).trans _,
  rw L1.simple_func.coe_coe,
  refine eventually_eq.trans _ L1.simple_func.indicator_L1s_coe_fn.symm,
  refine (@L1.simple_func.indicator_L1s_coe_fn α F _ _ _ _ _ μ s hs x hμsx).mono (λ a ha, _),
  rw [pi.smul_apply, ha],
  by_cases has : a ∈ s; simp [has],
end

lemma to_simple_func_indicator_L1s_fiber_ae_eq {s : set α} (hs : measurable_set s) (c : G)
  (hμsc : c = 0 ∨ μ s < ∞) (y : G) :
  (to_simple_func (indicator_L1s hs c hμsc)) ⁻¹' {y} =ᵐ[μ] (s.indicator (λ x, c)) ⁻¹' {y} :=
begin
  refine eventually_eq.trans _ (L1.simple_func.preimage_congr_ae
    (@L1.simple_func.indicator_L1s_coe_fn α G _ _ _ _ _ μ s hs c hμsc) {y}),
  exact L1.simple_func.preimage_congr_ae (L1.simple_func.to_simple_func_eq_to_fun _) {y},
end

lemma indicator_L1s_fiber_eq_self {s : set α} (hs : measurable_set s) (hμs : μ s < ∞)
  (c : G) (hc0 : c ≠ (0 : G)) :
  (to_simple_func (indicator_L1s hs c (or.inr hμs))) ⁻¹' {c} =ᵐ[μ] s :=
begin
  have h_set_eq := to_simple_func_indicator_L1s_fiber_ae_eq hs c (or.inr hμs) c,
  refine h_set_eq.trans (eventually_of_forall (λ x, _)),
  rw [← @set.mem_def _ x s, ← @set.mem_def _ x (s.indicator (λ (x : α), c) ⁻¹' {c}), eq_iff_iff,
    set.indicator_preimage],
  change x ∈ s.ite ((λ (x : α), c) ⁻¹' {c}) ((λ x, (0 : G)) ⁻¹' {c}) ↔ x ∈ s,
  classical,
  rw [set.preimage_const, set.preimage_const],
  simp [hc0.symm],
end

lemma indicator_L1s_measure_fiber_eq_zero {s : set α} (hs : measurable_set s)
  (c : G) (hμsc : c = 0 ∨ μ s < ∞) (y : G) (hy0 : y ≠ (0 : G)) (hyc : y ≠ c) :
  μ (to_simple_func (indicator_L1s hs c hμsc) ⁻¹' {y}) = 0 :=
begin
  have h_set_eq := to_simple_func_indicator_L1s_fiber_ae_eq hs c hμsc y,
  rw [measure_congr h_set_eq, set.indicator_preimage],
  change μ (s.ite ((λ x, c) ⁻¹' {y}) ((λ x, (0 : G)) ⁻¹' {y})) = 0,
  classical,
  rw [set.preimage_const, set.preimage_const],
  simp [hy0.symm, hyc.symm],
end

lemma set.indicator_const_preimage_eq_empty [has_zero γ] (s : set α) (c x : γ) (hx0 : x ≠ 0)
  (hxc : x ≠ c) :
  s.indicator (λ (y : α), c) ⁻¹' {x} = ∅ :=
begin
  classical,
  simp_rw [set.indicator_preimage, set.preimage_const, set.preimage_zero, set.mem_singleton_iff,
    hxc.symm, hx0.symm, if_false],
  simp,
end

--lemma indicator_L1s_mem_range {s : set α} (hs : measurable_set s) (c : G)
--  (hμsc : c = 0 ∨ μ s < ∞) (x : G) (hx : x ∈ (to_simple_func (indicator_L1s hs c hμsc)).range) :
--  x = c ∨ x = 0 :=
--begin
--  classical,
--  rw [L1.simple_func.to_simple_func_mem_range_iff _ hμ,
--    measure_congr (L1.simple_func.preimage_congr_ae
--      (@L1.simple_func.indicator_L1s_coe_fn α G _ _ _ _ _ μ s hs c hμsc) {x})] at hx,
--  by_contra hxc,
--  push_neg at hxc,
--  rw set.indicator_const_preimage_eq_empty s _ _ hxc.2 hxc.1 at hx,
--  simpa using hx,
--end

--lemma L1.simple_func.measurable_set_fiber (f : α →₁ₛ[μ] G) (y : G) :
--  measurable_set (L1.simple_func.to_simple_func f ⁻¹' {y}) :=
--simple_func.measurable_set_fiber (L1.simple_func.to_simple_func f) y

end indicator_L1s'


section indicator_fun_smul_const

variables [measurable_space α] {μ : measure α}

def L1.indicator_fun_smul_const [normed_space ℝ G] (f : α →₁[μ] ℝ) (c : G) : α →₁[μ] G :=
mem_ℒp.to_Lp (λ x, f x • c)
  (mem_ℒp_one_iff_integrable.mpr (integrable.smul_const (L1.integrable _) c))

@[simp] lemma L1.indicator_fun_smul_const_zero [normed_space ℝ G] (f : α →₁[μ] ℝ) :
  L1.indicator_fun_smul_const f (0 : G) = 0 :=
by { simp [L1.indicator_fun_smul_const], exact mem_ℒp.to_Lp_zero _, }

@[simp] lemma L1.indicator_fun_smul_const_zero_fun [normed_space ℝ G] (c : G) :
  L1.indicator_fun_smul_const (0 : α →₁[μ] ℝ) c = 0 :=
begin
  ext1,
  rw L1.indicator_fun_smul_const,
  refine (mem_ℒp.coe_fn_to_Lp
    (mem_ℒp_one_iff_integrable.mpr (integrable.smul_const (L1.integrable (0 : α →₁[μ] ℝ)) c))).mp _,
  refine (Lp.coe_fn_zero ℝ 1 μ).mp ((Lp.coe_fn_zero G 1 μ).mono (λ x hx0G hx0ℝ hx, _)),
  rw [hx, hx0ℝ, hx0G, pi.zero_apply, pi.zero_apply, zero_smul],
end

lemma L1.indicator_fun_smul_const_coe_fn [normed_space ℝ G] (f : α →₁[μ] ℝ) (c : G) :
  L1.indicator_fun_smul_const f c =ᵐ[μ] (λ x, f x • c) :=
mem_ℒp.coe_fn_to_Lp (mem_ℒp_one_iff_integrable.mpr (integrable.smul_const (L1.integrable _) c))

lemma indicator_L1s_ae_eq_fun_smul_const [normed_space ℝ G] {s : set α} (hs : measurable_set s)
  (c : G) (hμs : μ s < ∞) :
  indicator_L1s hs c (or.inr hμs) =ᵐ[μ] L1.indicator_fun_smul_const
    (indicator_Lp 1 hs (1 : ℝ) (or.inr hμs)) c :=
begin
  refine L1.simple_func.indicator_L1s_coe_fn.trans _,
  refine eventually_eq.trans _ (L1.indicator_fun_smul_const_coe_fn _ c).symm,
  refine (indicator_Lp_coe_fn 1 hs (1 : ℝ) (or.inr hμs)).mono (λ x hx, _),
  dsimp only,
  rw hx,
  by_cases hxs : x ∈ s; simp [hxs],
end

lemma const_smul_indicator_fun_smul_const [borel_space 𝕂] [smul_comm_class 𝕂 ℝ F']
  (f : α →₁[μ] ℝ) (x : F') (c : 𝕂) :
  c • L1.indicator_fun_smul_const f x = L1.indicator_fun_smul_const f (c • x) :=
begin
  ext1,
  refine (Lp.coe_fn_smul c _).trans _,
  refine eventually_eq.trans _ (L1.indicator_fun_smul_const_coe_fn _ _).symm,
  refine (L1.indicator_fun_smul_const_coe_fn f x).mono (λ a ha, _),
  rw [pi.smul_apply, ha],
  rw smul_comm,
end


end indicator_fun_smul_const

lemma Lp.coe_fn_sum {ι} [measurable_space α] {μ : measure α}
  (f : ι → Lp G p μ) (s : finset ι) :
  ⇑(∑ i in s, f i) =ᵐ[μ] ∑ i in s, ⇑(f i) :=
begin
  haveI : decidable_eq ι := classical.dec_eq _,
  refine finset.induction _ _ s,
  { simp [Lp.coe_fn_zero G p μ], },
  intros i s his hsf,
  rw finset.sum_insert his,
  refine (Lp.coe_fn_add _ _).trans _,
  refine hsf.mono (λ x hx, _),
  rw [pi.add_apply, hx, finset.sum_insert his, pi.add_apply],
end

lemma L1.simple_func.sum_to_simple_func_coe {ι} [measurable_space α] {μ : measure α}
  (f : ι → α →₁ₛ[μ] G) (s : finset ι) :
  L1.simple_func.to_simple_func (∑ i in s, f i)
    =ᵐ[μ] ∑ i in s, L1.simple_func.to_simple_func (f i) :=
begin
  refine (L1.simple_func.to_simple_func_eq_to_fun _).trans _,
  refine (L1.simple_func.coe_finset_sum _ s).trans _,
  refine eventually_eq.finset_sum _ _ s (λ i his, _),
  exact (L1.simple_func.to_simple_func_eq_to_fun _).symm,
end

lemma L1.simple_func.to_L1_coe_fn [measurable_space α] {μ : measure α} (f : simple_func α G)
  (hf : integrable f μ) :
  L1.simple_func.to_L1 f hf =ᵐ[μ] f :=
by { rw [←L1.simple_func.coe_coe, L1.simple_func.to_L1_eq_to_L1], exact integrable.coe_fn_to_L1 _, }

/-- Composition of a function and a `L1.simple_func`, as a `L1.simple_func`. -/
def L1.simple_func.map [measurable_space α] {μ : measure α} (g : G → F) (f : α →₁ₛ[μ] G)
  (hg : g 0 = 0):
  (α →₁ₛ[μ] F) :=
L1.simple_func.to_L1 ((L1.simple_func.to_simple_func f).map g)
  (simple_func.integrable_map _ (L1.simple_func.integrable _) _ hg)

lemma L1.simple_func.map_coe [measurable_space α] {μ : measure α} (g : G → F) (f : α →₁ₛ[μ] G)
  (hg : g 0 = 0) :
  ⇑(L1.simple_func.map g f hg) =ᵐ[μ] g ∘ f :=
begin
  rw L1.simple_func.map,
  refine (L1.simple_func.to_L1_coe_fn _ _).trans _,
  rw simple_func.coe_map,
  exact eventually_eq.fun_comp (L1.simple_func.to_simple_func_eq_to_fun _) g,
end

lemma L1.simple_func.coe_fn_neg [measurable_space α] {μ : measure α} (f : α →₁ₛ[μ] G) :
  ⇑(-f) =ᵐ[μ] -f :=
begin
  rw [← L1.simple_func.coe_coe, ← L1.simple_func.coe_coe, L1.simple_func.coe_neg],
  exact Lp.coe_fn_neg _,
end


local notation `⟪`x`, `y`⟫` := @inner 𝕂 E _ x y
local notation `⟪`x`, `y`⟫'` := @inner 𝕂 E' _ x y

lemma inner_indicator_Lp [borel_space 𝕂] [measurable_space α] {μ : measure α} (f : Lp E 2 μ)
  {s : set α} (hs : measurable_set s) (c : E) (hμsc : c = 0 ∨ μ s < ∞) :
  inner (indicator_Lp 2 hs c hμsc) f = ∫ x in s, ⟪c, f x⟫ ∂μ :=
begin
  simp_rw L2.inner_def,
  rw ← integral_add_compl hs (L2.integrable_inner _ f),
  have h_left : ∫ x in s, ⟪(indicator_Lp 2 hs c hμsc) x, f x⟫ ∂μ = ∫ x in s, ⟪c, f x⟫ ∂μ,
  { suffices h_ae_eq : ∀ᵐ x ∂μ, x ∈ s → ⟪indicator_Lp 2 hs c hμsc x, f x⟫ = ⟪c, f x⟫,
      from set_integral_congr_ae hs h_ae_eq,
    have h_indicator : ∀ᵐ (x : α) ∂μ, x ∈ s → (indicator_Lp 2 hs c hμsc x) = c,
      from indicator_Lp_coe_fn_mem,
    refine h_indicator.mono (λ x hx hxs, _),
    congr,
    exact hx hxs, },
  have h_right : ∫ x in sᶜ, ⟪(indicator_Lp 2 hs c hμsc) x, f x⟫ ∂μ = 0,
  { suffices h_ae_eq : ∀ᵐ x ∂μ, x ∉ s → ⟪indicator_Lp 2 hs c hμsc x, f x⟫ = 0,
    { simp_rw ← set.mem_compl_iff at h_ae_eq,
      suffices h_int_zero : ∫ x in sᶜ, inner (indicator_Lp 2 hs c hμsc x) (f x) ∂μ
        = ∫ x in sᶜ, (0 : 𝕂) ∂μ,
      { rw h_int_zero,
        simp, },
      exact set_integral_congr_ae hs.compl h_ae_eq, },
    have h_indicator : ∀ᵐ (x : α) ∂μ, x ∉ s → (indicator_Lp 2 hs c hμsc x) = 0,
      from indicator_Lp_coe_fn_nmem,
    refine h_indicator.mono (λ x hx hxs, _),
    rw hx hxs,
    exact inner_zero_left, },
  rw [h_left, h_right, add_zero],
end

lemma integral_inner [borel_space 𝕂] [measurable_space α] {μ : measure α} {f : α → E'}
  (hf : integrable f μ) (c : E') :
  ∫ x, ⟪c, f x⟫' ∂μ = ⟪c, ∫ x, f x ∂μ⟫' :=
((@inner_right 𝕂 E' _ _ c).restrict_scalars ℝ).integral_comp_comm hf

lemma integral_zero_of_forall_integral_inner_zero [borel_space 𝕂] [measurable_space α]
  {μ : measure α} (f : α → E') (hf : integrable f μ) (hf_int : ∀ (c : E'), ∫ x, ⟪c, f x⟫' ∂μ = 0) :
  ∫ x, f x ∂μ = 0 :=
by { specialize hf_int (∫ x, f x ∂μ), rwa [integral_inner hf, inner_self_eq_zero] at hf_int }





section integral_trim

lemma integrable.restrict [measurable_space α] {μ : measure α} {f : α → H} (hf : integrable f μ)
  (s : set α) :
  integrable f (μ.restrict s) :=
hf.integrable_on.integrable

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
  have hff'_m : f' =ᶠ[@measure.ae  _ m (μ.trim hm)] f,
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

lemma ae_const_le_iff_forall_lt_measure_zero' (f : α → ℝ) (c : ℝ) :
  (∀ᵐ x ∂μ, c ≤ f x) ↔ ∀ (a < c) (b < c), μ {x | a ≤ f x ∧ f x ≤ b} = 0 :=
begin
  rw ae_const_le_iff_forall_lt_measure_zero,
  split; intro h,
  { intros a ha b hb,
    refine measure_mono_null _ (h b hb),
    simp, },
  { intros b hb,
    have set_eq_Union : {x : α | f x ≤ b} = ⋃ n : ℕ, {x | b-n ≤ f x ∧ f x ≤ b},
    { ext1 x,
      simp_rw [set.mem_Union, set.mem_set_of_eq],
      split; intro h,
      { sorry, },
      { cases h with i hi,
        exact hi.2, }, },
    rw set_eq_Union,
    refine le_antisymm _ (zero_le _),
    refine (measure_Union_le _).trans (le_of_eq _),
    rw tsum_eq_zero_iff _,
    { exact λ n, h (b-n) ((sub_le_self b n.cast_nonneg).trans_lt hb) b hb, },
    { exact order_topology.to_order_closed_topology, },
    { have : (λ (i : ℕ), μ {x : α | b - i ≤ f x ∧ f x ≤ b}) = λ i, 0,
      { ext1 n,
        exact h (b-n) ((sub_le_self b n.cast_nonneg).trans_lt hb) b hb, },
      rw this,
      simp, }, },
end

/-- Use `ae_nonneg_of_forall_set_ℝ` instead. -/
private lemma ae_nonneg_of_forall_set_ℝ_measurable (f : α → ℝ) (hf : integrable f μ)
  (hfm : measurable f)
  (hf_zero : ∀ (s : set α) (hs : measurable_set s) (hμs : μ s < ∞), 0 ≤ ∫ x in s, f x ∂μ) :
  0 ≤ᵐ[μ] f :=
begin
  simp_rw [eventually_le, pi.zero_apply],
  rw ae_const_le_iff_forall_lt_measure_zero,
  intros b hb_neg,
  let s := {x | f x ≤ b},
  have hs : measurable_set s, from measurable_set_le hfm measurable_const,
  have hfs : ∀ x ∈ s, f x ≤ b, from λ x hxs, hxs,
  have hμs_lt_top : μ s < ∞,
  { have hf_int_on_s : integrable_on f s μ, from hf.integrable_on,
    rw [integrable_on, integrable, has_finite_integral] at hf_int_on_s,
    have hf_int_s := hf_int_on_s.2,
    have hfs_norm : ∀ x ∈ s, (nnnorm b : ℝ≥0∞) ≤ nnnorm (f x),
    { intros x hx,
      specialize hfs x hx,
      simp_rw ← of_real_norm_eq_coe_nnnorm,
      refine ennreal.of_real_le_of_real _,
      simp_rw real.norm_eq_abs,
      rw [abs_eq_neg_self.mpr hb_neg.le, abs_eq_neg_self.mpr (hfs.trans hb_neg.le)],
      exact neg_le_neg hfs, },
    refine measure_finite_of_integrable_on hf_int_on_s hs (nnnorm b : ℝ≥0∞) _ hfs_norm,
    rwa [← of_real_norm_eq_coe_nnnorm, ennreal.of_real_pos, real.norm_eq_abs,
      abs_eq_neg_self.mpr hb_neg.le, lt_neg, neg_zero], },
  have h_int_gt : μ s ≠ 0 → ∫ x in s, f x ∂μ ≤ b * (μ s).to_real,
  { intro h_ne_zero,
    have h_const_le : ∫ x in s, f x ∂μ ≤ ∫ x in s, b ∂μ,
    { refine set_integral_mono_ae_restrict hf.integrable_on
        (integrable_on_const.mpr (or.inr hμs_lt_top)) _,
      rw [eventually_le, ae_restrict_iff hs],
      exact eventually_of_forall hfs, },
    rwa [set_integral_const, smul_eq_mul, mul_comm] at h_const_le, },
  by_contra,
  refine (lt_self_iff_false (∫ x in s, f x ∂μ)).mp ((h_int_gt h).trans_lt _),
  refine (mul_neg_iff.mpr (or.inr ⟨hb_neg, _⟩)).trans_le (hf_zero s hs hμs_lt_top),
  refine (ennreal.to_real_nonneg).lt_of_ne (λ h_eq, h _),
  cases (ennreal.to_real_eq_zero_iff _).mp h_eq.symm with hμs_to_real hμs_to_real,
  { exact hμs_to_real, },
  { exact absurd hμs_to_real hμs_lt_top.ne, },
end

lemma ae_nonneg_of_forall_set_ℝ (f : α → ℝ) (hf : integrable f μ)
  (hf_zero : ∀ (s : set α) (hs : measurable_set s) (hμs : μ s < ∞), 0 ≤ ∫ x in s, f x ∂μ) :
  0 ≤ᵐ[μ] f :=
begin
  rcases hf with ⟨⟨f', hf'_meas, hf_ae⟩, hf_finite_int⟩,
  have hf'_integrable : integrable f' μ,
    from integrable.congr ⟨⟨f', hf'_meas, hf_ae⟩, hf_finite_int⟩ hf_ae,
  have hf'_zero : ∀ (s : set α) (hs : measurable_set s) (hμs : μ s < ∞), 0 ≤ ∫ x in s, f' x ∂μ,
  { intros s hs,
    rw set_integral_congr_ae hs (hf_ae.mono (λ x hx hxs, hx.symm)),
    exact hf_zero s hs, },
  exact (ae_nonneg_of_forall_set_ℝ_measurable f' hf'_integrable hf'_meas hf'_zero).trans
    hf_ae.symm.le,
end

lemma ae_eq_zero_of_forall_set_ℝ (f : α → ℝ) (hf : integrable f μ)
  (hf_zero : ∀ (s : set α) (hs : measurable_set s) (hμs : μ s < ∞), ∫ x in s, f x ∂μ = 0) :
  f =ᵐ[μ] 0 :=
begin
  have hf_nonneg : ∀ (s : set α) (hs : measurable_set s) (hμs : μ s < ∞), 0 ≤ ∫ x in s, f x ∂μ,
    from λ s hs hμs, (hf_zero s hs hμs).symm.le,
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
  have hf_nonneg_neg : ∀ (s : set α) (hs : measurable_set s) (hμs : μ s < ∞),
    0 ≤ ∫ (x : α) in s, (-f) x ∂μ,
  { intros s hs hμs,
    simp_rw pi.neg_apply,
    rw [integral_neg, neg_nonneg],
    exact (hf_zero s hs hμs).le, },
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

lemma ae_eq_zero_of_forall_set_integral_eq_zero [borel_space 𝕂] (f : α → E') (hf : integrable f μ)
  (hf_zero : ∀ s : set α, measurable_set s → μ s < ∞ → ∫ x in s, f x ∂μ = 0) :
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
  have hf_zero_inner : ∀ s, measurable_set s → μ s < ∞ →
    ∫ (x : α) in s, (inner c (f x) : 𝕂) ∂μ = 0,
  { intros s hs hμs,
    rw integral_const_inner hf.integrable_on c,
    simp [hf_zero s hs hμs], },
  have hf_zero_inner_re : ∀ s, measurable_set s → μ s < ∞ →
    ∫ x in s, is_R_or_C.re (inner c (f x) : 𝕂) ∂μ = 0,
  { intros s hs hμs,
    rw integral_re (integrable.const_inner hf c).integrable_on,
    rw hf_zero_inner s hs hμs,
    simp, },
  have hf_zero_inner_im : ∀ s, measurable_set s → μ s < ∞ →
    ∫ x in s, is_R_or_C.im (inner c (f x) : 𝕂) ∂μ = 0,
  { intros s hs hμs,
    rw integral_im (integrable.const_inner hf c).integrable_on,
    rw hf_zero_inner s hs hμs,
    simp, },
  exact ⟨ae_eq_zero_of_forall_set_ℝ _ hf_inner_re (λ s hs hμs, hf_zero_inner_re s hs hμs),
    ae_eq_zero_of_forall_set_ℝ _ hf_inner_im (λ s hs hμs, hf_zero_inner_im s hs hμs)⟩,
end

lemma ae_eq_of_forall_set_integral_eq [borel_space 𝕂]
  (f g : α → E') (hf : integrable f μ) (hg : integrable g μ)
  (hfg : ∀ s : set α, measurable_set s → μ s < ∞ → ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ) :
  f =ᵐ[μ] g :=
begin
  suffices h_sub : f-g =ᵐ[μ] 0,
    by { refine h_sub.mono (λ x hx, _), rwa [pi.sub_apply, pi.zero_apply, sub_eq_zero] at hx, },
  have hfg' : ∀ s : set α, measurable_set s → μ s < ∞ → ∫ x in s, (f - g) x ∂μ = 0,
  { intros s hs hμs,
    rw integral_sub' hf.integrable_on hg.integrable_on,
    exact sub_eq_zero.mpr (hfg s hs hμs), },
  exact ae_eq_zero_of_forall_set_integral_eq_zero (f-g) (hf.sub hg) hfg',
end

end ae_eq_of_forall_set_integral_eq






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





end measure_theory
