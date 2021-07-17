/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import measure_theory.conditional_expectation

/-!

# Martingales

-/

noncomputable theory
open topological_space measure_theory measure_theory.Lp filter
open_locale nnreal ennreal topological_space big_operators measure_theory

namespace measure_theory

variables {α ι E : Type*} [measurable_space E]

def is_filtration [preorder ι] (m : ι → measurable_space α) : Prop := monotone m

def adapted (f : ι → α → E) (m : ι → measurable_space α) : Prop :=
∀ i : ι, @measurable α E (m i) _ (f i)

def ae_adapted (f : ι → α → E) (m : ι → measurable_space α) {m0 : measurable_space α}
  (μ : measure α) :
  Prop :=
∀ i : ι, ae_measurable' (m i) (f i) μ

lemma adapted.ae_adapted {f : ι → α → E} {m : ι → measurable_space α} {m0 : measurable_space α}
  {μ : measure α} (hf : adapted f m) :
  ae_adapted f m μ :=
λ i, measurable.ae_measurable' (hf i)

def martingale [normed_group E] [borel_space E] [second_countable_topology E] [complete_space E]
  [normed_space ℝ E] [preorder ι] (f : ι → α → E) (m : ι → measurable_space α)
  {m0 : measurable_space α} {μ : measure α}
  (hf_int : ∀ i, integrable (f i) μ) (hf_adapted : ae_adapted f m μ) :
  Prop :=
∀ i j, i ≤ j → is_condexp (m i) (f i) (f j) μ

def submartingale {𝕜} [is_R_or_C 𝕜] [measurable_space 𝕜] [borel_space 𝕜] [inner_product_space 𝕜 E]
  [borel_space E] [second_countable_topology E] [complete_space E] [normed_space ℝ E]
  [is_scalar_tower ℝ 𝕜 E] [preorder E] [preorder ι]
  (f : ι → α → E) (m : ι → measurable_space α)
  {m0 : measurable_space α} {μ : measure α} [finite_measure μ] (hm_le : ∀ i, m i ≤ m0)
  (hf_int : ∀ i, integrable (f i) μ) (hf_adapted : adapted f m) :
  Prop :=
∀ i j, i ≤ j → f i ≤ᵐ[μ] condexp 𝕜 (hm_le i) (f j) (hf_int j)

def stopping_time [preorder ι] [measurable_space ι] (τ : α → ι) (m : ι → measurable_space α) :
  Prop :=
∀ t : ι, @measurable_set α (m t) (τ ⁻¹' (set.Iic t))

end measure_theory
