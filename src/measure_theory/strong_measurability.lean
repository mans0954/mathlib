/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import analysis.normed_space.dual
import measure_theory.simple_func_dense

/-! Strong and weak notions of measurability in Banach spaces. -/

open_locale topological_space
open measure_theory normed_space topological_space filter

noncomputable theory

namespace measure_theory

local infixr ` →ₛ `:25 := simple_func

variables {α E F 𝕜 : Type*} [measurable_space α]
  [is_R_or_C 𝕜]
  [normed_group E] [normed_space 𝕜 E] [measurable_space E]
  [normed_group F] [normed_space 𝕜 F]
  {f : α → E}

local notation `⟪`x`, `y`⟫` := y x

def strong_measurable (f : α → F) : Prop :=
∃ F : ℕ → α →ₛ F, at_top.tendsto (λ n, (F n).to_fun) (𝓝 f)

def strong_measurable.mk (f : α → F) (hf : strong_measurable f) : ℕ → α →ₛ F := hf.some

lemma strong_measurable.tendsto_mk {f : α → F} (hf : strong_measurable f) :
  at_top.tendsto (λ n, (hf.mk f n).to_fun) (𝓝 f) :=
hf.some_spec

variables (𝕜)
def weak_measurable [measurable_space 𝕜] (f : α → F) : Prop :=
∀ x_star : dual 𝕜 F, measurable (λ a, ⟪f a, x_star⟫)
variables {𝕜}

lemma measurable.weak_measurable [measurable_space 𝕜] [borel_space 𝕜] [opens_measurable_space E]
  (hf : measurable f) :
  weak_measurable 𝕜 f :=
λ x_star, x_star.continuous.measurable.comp hf

namespace strong_measurable

variables [measurable_space 𝕜] [borel_space 𝕜]

lemma measurable_mk (hf : strong_measurable f) (n : ℕ) : measurable (hf.mk f n) :=
(hf.mk f n).measurable

protected lemma measurable [borel_space E] (hf : strong_measurable f) : measurable f :=
measurable_of_tendsto_metric hf.measurable_mk hf.tendsto_mk

lemma weak_measurable [borel_space E] (hf : strong_measurable f) :
  weak_measurable 𝕜 f :=
measurable.weak_measurable hf.measurable

end strong_measurable

lemma measurable.strong_measurable [borel_space E] [second_countable_topology E]
  (hf : measurable f) :
  strong_measurable f :=
begin
  refine ⟨simple_func.approx_on f hf set.univ 0 (set.mem_univ 0), _⟩,
  rw tendsto_pi,
  intro x,
  convert simple_func.tendsto_approx_on hf (set.mem_univ 0) _,
  simp only [closure_univ],
end

lemma weak_measurable.measurable [measurable_space 𝕜] [borel_space 𝕜] [borel_space E]
  [second_countable_topology E]
  (hf : weak_measurable 𝕜 f) :
  measurable f :=
begin
  sorry
end

variables (𝕜)
lemma eq_zero_of_forall_dual_eq_zero {x : F} (h : ∀ c : dual 𝕜 F, ⟪x, c⟫ = (0 : 𝕜)) :
  x = 0 :=
begin
  by_cases hx : x = 0,
  { exact hx, },
  obtain ⟨g, norm_g, gx_eq⟩ := @exists_dual_vector 𝕜 _ _ _ _ x hx,
  refine norm_eq_zero.mp _,
  rw [h, norm'_def, is_R_or_C.algebra_map_eq_of_real] at gx_eq,
  rw ← @is_R_or_C.of_real_eq_zero 𝕜,
  exact gx_eq.symm,
end
variables {𝕜}

lemma ae_eq_zero_of_forall_dual_ae_eq_zero [second_countable_topology (dual 𝕜 F)]
  (μ : measure α) (f : α → F) (hf : ∀ c : dual 𝕜 F, ∀ᵐ x ∂μ, ⟪f x, c⟫ = (0 : 𝕜)) :
  f =ᵐ[μ] 0 :=
begin
  let s := dense_seq (dual 𝕜 F),
  have hs : dense_range s := dense_range_dense_seq _,
  have hfs : ∀ n : ℕ, ∀ᵐ x ∂μ, ⟪f x, s n⟫ = (0 : 𝕜), from λ n, hf (s n),
  have hf' : ∀ᵐ x ∂μ, ∀ n : ℕ, ⟪f x, s n⟫ = (0 : 𝕜), by rwa ae_all_iff,
  refine hf'.mono (λ x hx, eq_zero_of_forall_dual_eq_zero 𝕜 (λ c, _)),
  have h_closed : is_closed {c : dual 𝕜 F | ⟪f x, c⟫ = (0 : 𝕜)},
  { refine is_closed_eq _ continuous_const,
    have h_fun_eq : (λ (c : dual 𝕜 F), c (f x)) = inclusion_in_double_dual' 𝕜 F (f x),
      by { ext1 c, rw ← dual_def 𝕜 F (f x) c, },
    rw h_fun_eq,
    continuity, },
  exact @is_closed_property ℕ (dual 𝕜 F) _ s (λ c, ⟪f x, c⟫ = (0 : 𝕜)) hs h_closed (λ n, hx n) c,
end

end measure_theory
