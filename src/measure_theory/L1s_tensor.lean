import measure_theory.temp_simple_func


noncomputable theory
open_locale classical topological_space big_operators nnreal ennreal measure_theory
  tensor_product

namespace tensor_product

section normed_space

variables {R M N : Type*} [normed_field R]
  [normed_group M] [normed_space R M]
  [normed_group N] [normed_space R N]

/-- The projective norm on a tensor product. -/
def projective_norm (x : M ⊗[R] N) : ℝ :=
⨅ (s : finset (M × N)) (hs : ∑ y in s, y.1 ⊗ₜ y.2 = x), ∑ y in s, ∥y.1∥ * ∥y.2∥

instance : has_norm (M ⊗[R] N) :=
{ norm := projective_norm }

instance : normed_group (M ⊗[R] N) :=
normed_group.of_core (M ⊗[R] N)
{ norm_eq_zero_iff := sorry,
  triangle := sorry,
  norm_neg := sorry, }

instance : normed_space R (M ⊗[R] N) :=
{ norm_smul_le := sorry, }

end normed_space

end tensor_product

namespace measure_theory
open set filter topological_space ennreal emetric

variables {α β γ δ E E' F F' G G' H 𝕜 𝕂 : Type*} {p : ℝ≥0∞}
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


namespace simple_func
local infixr ` →ₛ `:25 := simple_func

variables [measurable_space α] [normed_space ℝ G]

def to_tensor (f : α →ₛ G) : (α →ₛ ℝ) ⊗[ℝ] G :=
∑ y in f.range, (indicator_simple_func (measurable_set_fiber f y) (1 : ℝ)) ⊗ₜ y

lemma to_tensor_def (f : α →ₛ G) :
  to_tensor f = ∑ y in f.range, (indicator_simple_func (measurable_set_fiber f y) (1 : ℝ)) ⊗ₜ y :=
rfl

lemma to_tensor_zero : to_tensor (0 : α →ₛ G) = 0 :=
begin
  by_cases hα : nonempty α,
  { haveI : nonempty α := hα,
    rw [to_tensor, range_zero, finset.sum_singleton, tensor_product.tmul_zero], },
  { sorry, },
end

def to_tensor_equiv : (α →ₛ G) ≃ₗ[ℝ] (α →ₛ ℝ) ⊗[ℝ] G :=
sorry

end simple_func

namespace L1
namespace simple_func
local infixr ` →ₛ `:25 := measure_theory.simple_func

variables [measurable_space α] {μ : measure α} [borel_space 𝕂]

lemma ext_range_nonzero (f g : α →₁ₛ[μ] G) (hfg_range : range_nonzero f = range_nonzero g)
  (hfg_preimage : ∀ y ∈ range_nonzero g, f ⁻¹' {y} =ᵐ[μ] g ⁻¹' {y}) :
  f = g :=
begin
  rw [simple_func_eq_sum_indicator_L1s f, simple_func_eq_sum_indicator_L1s g, hfg_range],
  refine finset.sum_congr rfl (λ y hy, _),
  exact indicator_L1s_congr_ae _ _ _ _ _ (hfg_preimage y hy),
end

variables [normed_space ℝ G]

def to_tensor (f : α →₁ₛ[μ] G) : (α →₁ₛ[μ] ℝ) ⊗[ℝ] G :=
∑ (y : G) in range_nonzero f,
  (dite (y = 0) (λ h, (0 : α →₁ₛ[μ] ℝ))
    (λ h, indicator_L1s (measurable_set_fiber f y) (1 : ℝ) (or.inr (finite_fiber f y h))))
  ⊗ₜ[ℝ] y

lemma to_tensor_def (f : α →₁ₛ[μ] G) : to_tensor f = ∑ (y : G) in range_nonzero f,
  (dite (y = 0) (λ h, (0 : α →₁ₛ[μ] ℝ))
    (λ h, indicator_L1s (measurable_set_fiber f y) (1 : ℝ) (or.inr (finite_fiber f y h))))
  ⊗ₜ[ℝ] y :=
rfl

lemma to_tensor_zero : to_tensor (0 : α →₁ₛ[μ] G) = 0 :=
by { rw [to_tensor, range_nonzero_zero, finset.sum_empty] }

lemma to_tensor_indicator_L1s {s : set α} (hs : measurable_set s) (c : G) (hμs : μ s < ∞) :
  to_tensor (indicator_L1s hs c (or.inr hμs)) = (indicator_L1s hs (1 : ℝ) (or.inr hμs)) ⊗ₜ c :=
begin
  by_cases hc0 : c = 0,
  { simp [hc0, indicator_L1s_zero, to_tensor_zero], },
  by_cases hμs0 : μ s = 0,
  { simp_rw indicator_L1s_set_measure_zero hμs0, rw to_tensor_zero, simp, },
  rw ← ne.def at hμs0,
  have hμs_pos : 0 < μ s, from lt_of_le_of_ne (zero_le _) hμs0.symm,
  rw to_tensor,
  rw range_nonzero_indicator_L1s_eq hs c (or.inr hμs) hμs_pos hc0,
  rw finset.sum_singleton,
  simp only [hc0, dif_neg, not_false_iff],
  congr' 1,
  exact indicator_L1s_congr_ae _ _ _ _ _
    (indicator_L1s_fiber_ae_eq_self hs c (or.inr hμs) hc0),
end

lemma ennreal.eq_zero_or_pos (x : ℝ≥0∞) : x = 0 ∨ 0 < x := sorry

lemma finset.disjoint_iff [decidable_eq γ] (s t : finset γ) : disjoint s t ↔ s ∩ t ⊆ ∅ := iff.rfl

lemma preimage_add_indicator_L1s_of_nmem_const_mem_range (f : α →₁ₛ[μ] G) {s : set α}
  (hs : measurable_set s) (c : G) (hμsc : c = 0 ∨ μ s < ∞) (hc_nmem : c ∉ range_nonzero f)
  (x : G) (hx_mem : x ∈ L1.simple_func.range_nonzero f) :
  ⇑(f + indicator_L1s hs c hμsc) ⁻¹' {x} =ᵐ[μ] f ⁻¹' {x} :=
begin
  sorry
end

lemma preimage_add_indicator_L1s_of_nmem_const (f : α →₁ₛ[μ] G) {s : set α} (hs : measurable_set s)
  (c : G) (hμsc : c = 0 ∨ μ s < ∞) (hc_nmem : c ∉ range_nonzero f) :
  ⇑(f + indicator_L1s hs c hμsc) ⁻¹' {c} =ᵐ[μ] (indicator_L1s hs c hμsc) ⁻¹' {c} :=
begin
  sorry
end

lemma preimage_add_indicator_L1s_of_mem_const (f : α →₁ₛ[μ] G) {s : set α} (hs : measurable_set s)
  (c : G) (hμsc : c = 0 ∨ μ s < ∞) (hc_nmem : c ∈ range_nonzero f) :
  ⇑(f + indicator_L1s hs c hμsc) ⁻¹' {c}
    =ᵐ[μ] ((indicator_L1s hs c hμsc ⁻¹' {c}) ∪ (f ⁻¹' {c}) : set α) :=
begin
  sorry
end

lemma to_tensor_add_indicator_L1s_of_disjoint_of_nmem
  (f : α →₁ₛ[μ] G) (s : set α) (hs : measurable_set s) (c : G) (hμsc : c = 0 ∨ μ s < ∞)
  (hs_disj : ∀ y ≠ 0, disjoint (f ⁻¹' {y}) (indicator_L1s hs c hμsc ⁻¹' {c})) (hc0 : c ≠ 0)
  (hμs : 0 < μ s) (hc_nmem : c ∉ range_nonzero f) :
  to_tensor (f + indicator_L1s hs c hμsc) = to_tensor f + to_tensor (indicator_L1s hs c hμsc) :=
begin
  rw [to_tensor, range_nonzero_add_indicator_of_disjoint' f hs c hμsc hs_disj,
    finset.sum_union],
  swap,
  { rw finset.disjoint_iff,
    intros x hx,
    rw [range_nonzero_indicator_L1s_eq hs c hμsc hμs hc0, finset.mem_inter,
      finset.mem_singleton] at hx,
    cases hx with hx hx_eq_c,
    rw hx_eq_c at hx,
    exact absurd hx hc_nmem, },
  have h_preim_f_add := preimage_add_indicator_L1s_of_nmem_const_mem_range f hs c hμsc hc_nmem,
  have h_preim_f_add_c := preimage_add_indicator_L1s_of_nmem_const f hs c hμsc hc_nmem,
  rw to_tensor_def (indicator_L1s hs c hμsc),
  rw [range_nonzero_indicator_L1s_eq hs c hμsc hμs hc0, finset.sum_singleton, finset.sum_singleton],
  simp only [hc0, dif_neg, not_false_iff],
  rw indicator_L1s_congr_ae _ (measurable_set_fiber _ c) (1 : ℝ) _ (or.inr (finite_fiber _ c hc0))
    h_preim_f_add_c,
  simp, -- todo, don't know how to congr without a timeout. squeeze_simp fails.
  rw to_tensor,
  refine finset.sum_congr rfl (λ x hx_mem, _),
  have hx0 : x ≠ 0, from ne_zero_of_mem_range_nonzero f x hx_mem,
  simp only [hx0, dif_neg, not_false_iff],
  rw indicator_L1s_congr_ae _ (measurable_set_fiber _ x) (1 : ℝ) _ (or.inr (finite_fiber _ x hx0))
    (h_preim_f_add x hx_mem),
end

lemma finset.union_singleton_eq_insert [decidable_eq γ] (s : finset γ) (a : γ) :
  s ∪ {a} = insert a s :=
by { ext1 x, rw [finset.mem_union, finset.mem_insert, finset.mem_singleton, or_comm] }

lemma finset_insert_sdiff_singleton_of_mem [decidable_eq γ] (s : finset γ) (a : γ) (ha_s : a ∈ s) :
  insert a (s \ {a}) = s :=
begin
  ext1 x,
  rw [finset.mem_insert, finset.mem_sdiff, finset.mem_singleton],
  by_cases hxa : x = a; simp [hxa, ha_s],
end

lemma to_tensor_add_indicator_L1s_of_disjoint_of_mem
  (f : α →₁ₛ[μ] G') (s : set α) (hs : measurable_set s) (c : G') (hμsc : c = 0 ∨ μ s < ∞)
  (hs_disj : ∀ y ≠ 0, disjoint (f ⁻¹' {y}) (indicator_L1s hs c hμsc ⁻¹' {c})) (hc0 : c ≠ 0)
  (hμs : 0 < μ s) (hc_mem : c ∈ range_nonzero f) :
  to_tensor (f + indicator_L1s hs c hμsc) = to_tensor f + to_tensor (indicator_L1s hs c hμsc) :=
begin
  simp_rw to_tensor,
  rw [range_nonzero_add_indicator_of_disjoint' f hs c hμsc hs_disj,
    range_nonzero_indicator_L1s_eq hs c hμsc hμs hc0, finset.sum_singleton],
  have h_union_eq : range_nonzero f ∪ {c} = range_nonzero f,
    by rw [finset.union_singleton_eq_insert, finset.insert_eq_of_mem hc_mem],
  rw h_union_eq,
  rw ← finset_insert_sdiff_singleton_of_mem (range_nonzero f) c hc_mem,
  have hc_nmem_diff : c ∉ (range_nonzero f) \ {c},
  { sorry, },
  rw finset.sum_insert hc_nmem_diff,
  rw finset.sum_insert hc_nmem_diff,
  simp only [hc0, dif_neg, not_false_iff],
  rw indicator_L1s_congr_ae _ _ _ _ _ (preimage_add_indicator_L1s_of_mem_const f hs c hμsc hc_mem),
  swap, { exact measurable_set.union (measurable_set_fiber _ c) (measurable_set_fiber _ c), },
  swap, { exact or.inr ((measure_union_le _ _).trans_lt
    (ennreal.add_lt_top.mpr ⟨finite_fiber _ c hc0, finite_fiber f c hc0⟩)), },
  rw [add_assoc, add_comm],
  nth_rewrite 1 add_comm,
  rw [add_assoc, ← tensor_product.add_tmul,
    indicator_L1s_add_of_disjoint_of_eq (measurable_set_fiber _ c) (finite_fiber _ c hc0)
      (measurable_set_fiber f c) (finite_fiber f c hc0) (hs_disj c hc0).symm],
  simp,  -- todo
  refine finset.sum_congr rfl (λ y hy, _),
  have hy0 : y ≠ 0, by sorry,
  simp only [hy0, dif_neg, not_false_iff],
  sorry,
end

lemma to_tensor_add_indicator_L1s_of_disjoint
  (f : α →₁ₛ[μ] G') (s : set α) (hs : measurable_set s) (c : G') (hμsc : c = 0 ∨ μ s < ∞)
  (hs_disj : ∀ y ≠ 0, disjoint (f ⁻¹' {y}) (indicator_L1s hs c hμsc ⁻¹' {c})) (hc0 : c ≠ 0)
  (hμs : 0 < μ s) :
  to_tensor (f + indicator_L1s hs c hμsc) = to_tensor f + to_tensor (indicator_L1s hs c hμsc) :=
begin
  by_cases hc_mem : c ∈ L1.simple_func.range_nonzero f,
  { exact to_tensor_add_indicator_L1s_of_disjoint_of_mem f s hs c hμsc hs_disj hc0 hμs
      hc_mem, },
  { exact to_tensor_add_indicator_L1s_of_disjoint_of_nmem f s hs c hμsc hs_disj hc0 hμs
      hc_mem, },
end

lemma to_tensor_add_indicator_L1s_of_subset
  (f : α →₁ₛ[μ] G') (s : set α) (hs : measurable_set s) (c : G') (hμsc : c = 0 ∨ μ s < ∞)
  (hs_subset : ∃ y ∈ (L1.simple_func.range_nonzero f), s ⊆ (to_simple_func f ⁻¹' {y}))
  (hc0 : c ≠ 0) (hμs : 0 < μ s) :
  to_tensor (f + indicator_L1s hs c hμsc) = to_tensor f + to_tensor (indicator_L1s hs c hμsc) :=
begin
  classical,
  rcases hs_subset with ⟨ys, hys, hs_subset⟩,
  simp_rw to_tensor,
  rw [range_nonzero_indicator_L1s_eq hs c hμsc hμs hc0, finset.sum_singleton],
  sorry,
end

lemma measurable_set_preimage_finset [measurable_singleton_class β] (f : α → β)
  (hf : measurable f) (s : finset β) :
  measurable_set (f ⁻¹' s) :=
begin
  have hs_sum : f ⁻¹' s = ⋃ y ∈ s, f ⁻¹' {y},
  { ext1 x,
    simp_rw [set.mem_Union, set.mem_preimage, set.mem_singleton_iff, finset.mem_coe],
    simp only [exists_prop, exists_eq_right'], },
  rw hs_sum,
  refine measurable_set.bUnion _ _,
  { change countable (λ y, y ∈ s),
    change countable (s : set β),
    exact finset.countable_to_set s, },
  exact λ b hb, hf (measurable_set_singleton b),
end

lemma measurable_preimage_range_nonzero (f : α →₁ₛ[μ] G) :
  measurable_set (f ⁻¹' (range_nonzero f)) :=
measurable_set_preimage_finset f (Lp.measurable _) _

lemma indicator_L1s_eq_sum_indicator_L1s_disjoint (f : α →₁ₛ[μ] G) {s : set α}
  (hs : measurable_set s) (c : G) (hμs : μ s < ∞) :
  indicator_L1s hs c (or.inr hμs)
  = indicator_L1s (hs.diff (measurable_preimage_range_nonzero f)) c
    (or.inr ((measure_mono (set.inter_subset_left _ _)).trans_lt hμs))
  + ∑ y in range_nonzero f, indicator_L1s (hs.inter (measurable_set_fiber f y)) c
    (or.inr ((measure_mono (set.inter_subset_left _ _)).trans_lt hμs)) :=
begin
  sorry,
end

lemma to_tensor_add_indicator_L1s (f : α →₁ₛ[μ] G) {s : set α} (hs : measurable_set s) (c : G)
  (hμsc : c = 0 ∨ μ s < ∞) :
  to_tensor (f + indicator_L1s hs c hμsc) = to_tensor f + to_tensor (indicator_L1s hs c hμsc) :=
begin
  by_cases hc0 : c = 0,
  { simp_rw [hc0, indicator_L1s_zero, to_tensor_zero, add_zero], },
  cases ennreal.eq_zero_or_pos (μ s) with hμs hμs,
  { simp_rw [indicator_L1s_set_measure_zero hμs, to_tensor_zero, add_zero], },
  sorry,
end

lemma to_tensor_add_sum_indicator_L1s (s : finset G) (S : G → set α)
  (hS : ∀ y, measurable_set (S y)) (cS : G → G) (hμS : ∀ y, cS y = 0 ∨ μ (S y) < ∞)
  (f : α →₁ₛ[μ] G) :
  to_tensor (f + ∑ y in s, indicator_L1s (hS y) (cS y) (hμS y))
    = to_tensor f + ∑ y in s, to_tensor (indicator_L1s (hS y) (cS y) (hμS y)) :=
begin
  classical,
  refine finset.induction _ _ s,
  { simp, },
  intros y s hys hops,
  rw [finset.sum_insert hys, add_comm (indicator_L1s (hS y) (cS y) (hμS y)), ← add_assoc,
    to_tensor_add_indicator_L1s,
    hops, finset.sum_insert hys],
  nth_rewrite 3 add_comm,
  rw ← add_assoc,
end

lemma to_tensor_eq_sum_to_tensor_indicator_L1s (f : α →₁ₛ[μ] G) :
  to_tensor f = ∑ y in (L1.simple_func.range_nonzero f),
    to_tensor (indicator_L1s (measurable_set_fiber f y) y (zero_or_finite_fiber f y)) :=
begin
  nth_rewrite 0 simple_func_eq_sum_indicator_L1s f,
  suffices h_zero_add : to_tensor (0 + ∑ (y : G) in (L1.simple_func.range_nonzero f),
    indicator_L1s (measurable_set_fiber f y) y (zero_or_finite_fiber f y))
    = to_tensor 0 + ∑ (y : G) in (L1.simple_func.range_nonzero f),
      to_tensor (indicator_L1s (measurable_set_fiber f y) y (zero_or_finite_fiber f y)),
  { rwa [zero_add, to_tensor_zero, zero_add] at h_zero_add, },
  rw to_tensor_add_sum_indicator_L1s,
end

lemma to_tensor_add (f g : α →₁ₛ[μ] G) :
  to_tensor (f + g) = to_tensor f + to_tensor g :=
begin
  nth_rewrite 0 simple_func_eq_sum_indicator_L1s g,
  rw [to_tensor_add_sum_indicator_L1s, to_tensor_eq_sum_to_tensor_indicator_L1s g],
end

def to_tensor_hom : (α →₁ₛ[μ] G) →+ ((α →₁ₛ[μ] ℝ) ⊗[ℝ] G) :=
{ to_fun := to_tensor,
  map_zero' := to_tensor_zero,
  map_add' := to_tensor_add, }

lemma to_tensor_hom_coe : ⇑(to_tensor_hom : (α →₁ₛ[μ] G) →+ ((α →₁ₛ[μ] ℝ) ⊗[ℝ] G)) = to_tensor :=
rfl

-- todo: write it for 𝕂 and F' [smul_comm_class 𝕂 ℝ F']. Need to define has_scalar
lemma to_tensor_smul_indicator_L1s
  {s : set α} (hs : measurable_set s) (x : G) (hμsx : x = 0 ∨ μ s < ∞) (c : ℝ) :
  to_tensor (c • (indicator_L1s hs x hμsx)) = c • to_tensor (indicator_L1s hs x hμsx) :=
begin
  rw const_smul_indicator_L1s,
  by_cases hx0 : x = 0,
  { simp_rw [hx0, smul_zero, indicator_L1s_zero, to_tensor_zero, smul_zero], },
  by_cases hc0 : c = 0,
  { simp_rw [hc0, zero_smul, L1.simple_func.indicator_L1s_zero, to_tensor_zero], },
  have hcx : c • x ≠ 0, from smul_ne_zero.mpr ⟨hc0, hx0⟩,
  have hμs : μ s < ∞, by { cases hμsx, exact absurd hμsx hx0, exact hμsx, },
  rw [to_tensor_indicator_L1s hs (c • x) hμs, to_tensor_indicator_L1s hs x hμs,
    tensor_product.tmul_smul],
end

lemma to_tensor_smul (c : ℝ) (f : α →₁ₛ[μ] G) :
  to_tensor (c • f) = c • to_tensor f :=
begin
  change to_tensor_hom (c • f) = c • to_tensor_hom f,
  rw [simple_func_eq_sum_indicator_L1s f, finset.smul_sum],
  simp_rw @add_monoid_hom.map_sum G (α →₁ₛ[μ] G) ((α →₁ₛ[μ] ℝ) ⊗[ℝ] G) _ _ to_tensor_hom _
    (range_nonzero f),
  rw finset.smul_sum,
  congr,
  ext1 x,
  exact to_tensor_smul_indicator_L1s _ x _ c,
end

def to_tensor_lm : (α →₁ₛ[μ] G) →ₗ[ℝ] ((α →₁ₛ[μ] ℝ) ⊗[ℝ] G) :=
{ to_fun := to_tensor,
  map_add' := λ f g, to_tensor_add f g,
  map_smul' := λ c f, to_tensor_smul c f, }

lemma to_tensor_lm_coe : ⇑(to_tensor_lm : (α →₁ₛ[μ] G) →ₗ[ℝ] ((α →₁ₛ[μ] ℝ) ⊗[ℝ] G)) = to_tensor :=
rfl

lemma range_nonzero_eq_empty_iff (f : α →₁ₛ[μ] G) : range_nonzero f = ∅ ↔ f = 0 :=
begin
  split; intro h,
  { rw [simple_func_eq_sum_indicator_L1s f, h, finset.sum_empty], },
  { rw h,
    exact range_nonzero_zero, },
end

lemma to_tensor_eq_zero_iff (f : α →₁ₛ[μ] G) : to_tensor f = 0 ↔ f = 0 :=
begin
  split; intro h,
  swap, { rw h, exact to_tensor_zero, },
  rw to_tensor at h,
  rw ← range_nonzero_eq_empty_iff,
  by_contra h_empty,
  rw finset.eq_empty_iff_forall_not_mem at h_empty,
  push_neg at h_empty,
  obtain ⟨y, hy⟩ := h_empty,
  have hy0 : y ≠ 0, from ne_zero_of_mem_range_nonzero f y hy,
  let s := f ⁻¹' {y},
  have hs_nonzero : ¬ μ s = 0, from measure_ne_zero_of_mem_range_nonzero f y hy,
  have hsy : ∀ x ∈ s, f x = y,
  { sorry, },
  have hs0 :  ∀ᵐ x ∂μ, x ∈ s → f x = 0,
  { sorry, },
  sorry,
end

lemma to_tensor_lm_ker_eq_bot : (to_tensor_lm : (α →₁ₛ[μ] G) →ₗ[ℝ] ((α →₁ₛ[μ] ℝ) ⊗[ℝ] G)).ker = ⊥ :=
linear_map.ker_eq_bot'.mpr (λ f hf, by rwa [to_tensor_lm_coe, to_tensor_eq_zero_iff] at hf)

lemma to_tensor_injective : function.injective (to_tensor : (α →₁ₛ[μ] G) → ((α →₁ₛ[μ] ℝ) ⊗[ℝ] G)) :=
begin
  intros f g hfg,
  rw ← sub_eq_zero at hfg ⊢,
  rw [← to_tensor_lm_coe, ← linear_map.map_sub, to_tensor_lm_coe] at hfg,
  exact (to_tensor_eq_zero_iff _).mp hfg,
end

lemma span_tmul_eq_top (R M N) [comm_semiring R] [add_comm_monoid M] [add_comm_monoid N]
  [semimodule R M] [semimodule R N] :
  submodule.span R { t : M ⊗[R] N | ∃ m n, m ⊗ₜ n = t } = ⊤ :=
begin
  ext t, simp only [submodule.mem_top, iff_true],
  apply t.induction_on,
  { exact submodule.zero_mem _, },
  { intros m n, apply submodule.subset_span, use [m, n], },
  { intros t₁ t₂ ht₁ ht₂, exact submodule.add_mem _ ht₁ ht₂, },
end

lemma to_tensor_surjective :
  function.surjective (to_tensor : (α →₁ₛ[μ] G) → ((α →₁ₛ[μ] ℝ) ⊗[ℝ] G)) :=
begin
  rw [← to_tensor_lm_coe, ← linear_map.range_eq_top, eq_top_iff, ← span_tmul_eq_top,
    submodule.span_le],
  intros φ hφ,
  rw set.mem_set_of_eq at hφ,
  obtain ⟨f, x, hfx⟩ := hφ,
  rw simple_func_eq_sum_indicator_L1s f at hfx,
  rw [set_like.mem_coe, linear_map.mem_range],
  use ∑ y in range_nonzero f,
    dite (y = 0) (λ h, (0 : α →₁ₛ[μ] G))
    (λ h, indicator_L1s (measurable_set_fiber f y) (y • x) (or.inr (finite_fiber f y h))),
  rw [linear_map.map_sum, ← hfx, tensor_product.sum_tmul],
  refine finset.sum_congr rfl (λ y hy, _),
  have hy0 : y ≠ 0, from ne_zero_of_mem_range_nonzero f y hy,
  simp only [hy0, dif_neg, not_false_iff],
  rw [← const_smul_indicator_L1s _ _ (or.inr (finite_fiber f y hy0)), linear_map.map_smul,
    to_tensor_lm_coe, to_tensor_indicator_L1s, tensor_product.smul_tmul', const_smul_indicator_L1s],
  simp,
end

lemma to_tensor_bijective :
  function.bijective (to_tensor : (α →₁ₛ[μ] G) → ((α →₁ₛ[μ] ℝ) ⊗[ℝ] G)) :=
⟨to_tensor_injective, to_tensor_surjective⟩

def to_tensor_equiv : (α →₁ₛ[μ] G) ≃ₗ[ℝ] ((α →₁ₛ[μ] ℝ) ⊗[ℝ] G) :=
{ to_fun := to_tensor,
  map_add' := to_tensor_add,
  map_smul' := to_tensor_smul,
  inv_fun := function.inv_fun to_tensor,
  left_inv := function.left_inverse_inv_fun to_tensor_injective,
  right_inv := function.right_inverse_inv_fun to_tensor_surjective, }

lemma to_tensor_equiv.coe :
  ⇑(to_tensor_equiv : (α →₁ₛ[μ] G) ≃ₗ[ℝ] ((α →₁ₛ[μ] ℝ) ⊗[ℝ] G)) = to_tensor :=
rfl

def extend_lm [add_comm_monoid γ] [semimodule ℝ γ] (T : (α →₁ₛ[μ] ℝ) →ₗ[ℝ] γ) :
  ((α →₁ₛ[μ] ℝ) ⊗[ℝ] G) →ₗ[ℝ] (γ ⊗[ℝ] G) :=
linear_map.rtensor G T

section tensor_dense_in_L1

lemma indicator_fun_smul_const_add_fun (f g : α →₁[μ] ℝ) (x : G) :
  indicator_fun_smul_const (f + g) x
    = indicator_fun_smul_const f x + indicator_fun_smul_const g x :=
begin
  ext1,
  refine (indicator_fun_smul_const_coe_fn _ _).trans _,
  refine eventually_eq.trans _ (Lp.coe_fn_add _ _).symm,
  refine eventually_eq.trans _ (eventually_eq.add (indicator_fun_smul_const_coe_fn _ _).symm
    (indicator_fun_smul_const_coe_fn _ _).symm),
  refine (Lp.coe_fn_add f g).mono (λ y hy, _),
  dsimp only,
  rw [hy, pi.add_apply, add_smul],
end

lemma indicator_fun_smul_const_add_const (f : α →₁[μ] ℝ) (x y : G) :
  indicator_fun_smul_const f (x + y)
    = indicator_fun_smul_const f x + indicator_fun_smul_const f y :=
begin
  ext1,
  refine (indicator_fun_smul_const_coe_fn _ _).trans _,
  refine eventually_eq.trans _ (Lp.coe_fn_add _ _).symm,
  refine eventually_eq.trans _ (eventually_eq.add (indicator_fun_smul_const_coe_fn _ _).symm
    (indicator_fun_smul_const_coe_fn _ _).symm),
  refine eventually_of_forall (λ z, _),
  dsimp only,
  rw smul_add,
end

lemma indicator_fun_smul_const_smul_fun (c : ℝ) (f : α →₁[μ] ℝ) (x : G) :
  L1.indicator_fun_smul_const (c • f) x = c • L1.indicator_fun_smul_const f x :=
begin
  ext1,
  refine eventually_eq.trans _ (Lp.coe_fn_smul c _).symm,
  refine (L1.indicator_fun_smul_const_coe_fn _ _).trans _,
  refine (Lp.coe_fn_smul c f).mp _,
  refine (L1.indicator_fun_smul_const_coe_fn f x).mono (λ a ha hfc, _),
  rw [pi.smul_apply, ha],
  dsimp only,
  rw [hfc, pi.smul_apply, smul_smul, smul_eq_mul],
end

lemma indicator_fun_smul_const_smul_const (c : ℝ) (f : α →₁[μ] ℝ) (x : G) :
  L1.indicator_fun_smul_const f (c • x) = c • L1.indicator_fun_smul_const f x :=
begin
  ext1,
  refine eventually_eq.trans _ (Lp.coe_fn_smul c _).symm,
  refine (L1.indicator_fun_smul_const_coe_fn _ _).trans _,
  refine (L1.indicator_fun_smul_const_coe_fn f x).mono (λ a ha, _),
  rw [pi.smul_apply, ha, smul_comm],
end

def indicator_fun_smul_const_bilin : (α →₁[μ] ℝ) →ₗ[ℝ] G →ₗ[ℝ] α →₁[μ] G :=
linear_map.mk₂ ℝ indicator_fun_smul_const
  indicator_fun_smul_const_add_fun
  indicator_fun_smul_const_smul_fun
  indicator_fun_smul_const_add_const
  indicator_fun_smul_const_smul_const

def tensor_to_L1 : ((α →₁[μ] ℝ) ⊗[ℝ] G) →ₗ[ℝ] α →₁[μ] G :=
tensor_product.uncurry ℝ (α →₁[μ] ℝ) G (α →₁[μ] G) indicator_fun_smul_const_bilin

def L1s_smul_const (f : α →₁ₛ[μ] ℝ) (x : G) : α →₁ₛ[μ] G :=
⟨indicator_fun_smul_const f x, sorry⟩

lemma L1s_smul_const_coe_fn (f : α →₁ₛ[μ] ℝ) (x : G) :
  L1s_smul_const f x =ᵐ[μ] (λ y, f y • x) :=
begin
  rw ← coe_coe,
  rw ← coe_coe,
  change (indicator_fun_smul_const (f : α →₁[μ] ℝ) x) =ᵐ[μ] λ (y : α), (f : α →₁[μ] ℝ) y • x,
  exact indicator_fun_smul_const_coe_fn _ _,
end

lemma L1s_smul_const_add_fun (f g : α →₁ₛ[μ] ℝ) (x : G) :
  L1s_smul_const (f + g) x = L1s_smul_const f x + L1s_smul_const g x :=
begin
  ext1,
  refine (L1s_smul_const_coe_fn _ _).trans _,
  refine eventually_eq.trans _ (coe_fn_add _ _).symm,
  refine eventually_eq.trans _ (eventually_eq.add (L1s_smul_const_coe_fn _ _).symm
    (L1s_smul_const_coe_fn _ _).symm),
  refine (coe_fn_add f g).mono (λ y hy, _),
  dsimp only,
  rw [hy, pi.add_apply, add_smul],
end

lemma L1s_smul_const_add_const (f : α →₁ₛ[μ] ℝ) (x y : G) :
  L1s_smul_const f (x + y) = L1s_smul_const f x + L1s_smul_const f y :=
begin
  ext1,
  refine (L1s_smul_const_coe_fn _ _).trans _,
  refine eventually_eq.trans _ (coe_fn_add _ _).symm,
  refine eventually_eq.trans _ (eventually_eq.add (L1s_smul_const_coe_fn _ _).symm
    (L1s_smul_const_coe_fn _ _).symm),
  refine eventually_of_forall (λ z, _),
  dsimp only,
  rw smul_add,
end

lemma coe_fn_smul (c : 𝕂) (f : α →₁ₛ[μ] F) :
  ⇑(c • f) =ᵐ[μ] c • f :=
begin
  rw [← coe_coe, coe_smul, ← coe_coe],
  exact Lp.coe_fn_smul _ _,
end

lemma L1s_smul_const_smul_fun (c : ℝ) (f : α →₁ₛ[μ] ℝ) (x : G) :
  L1s_smul_const (c • f) x = c • L1s_smul_const f x :=
begin
  ext1,
  refine eventually_eq.trans _ (coe_fn_smul c _).symm,
  refine (L1s_smul_const_coe_fn _ _).trans _,
  refine (coe_fn_smul c f).mp _,
  refine (L1s_smul_const_coe_fn f x).mono (λ a ha hfc, _),
  rw [pi.smul_apply, ha],
  dsimp only,
  rw [hfc, pi.smul_apply, smul_smul, smul_eq_mul],
end

lemma L1s_smul_const_smul_const (c : ℝ) (f : α →₁ₛ[μ] ℝ) (x : G) :
  L1s_smul_const f (c • x) = c • L1s_smul_const f x :=
begin
  ext1,
  refine eventually_eq.trans _ (coe_fn_smul c _).symm,
  refine (L1s_smul_const_coe_fn _ _).trans _,
  refine (L1s_smul_const_coe_fn f x).mono (λ a ha, _),
  rw [pi.smul_apply, ha, smul_comm],
end

def L1s_smul_const_bilin : (α →₁ₛ[μ] ℝ) →ₗ[ℝ] G →ₗ[ℝ] α →₁ₛ[μ] G :=
linear_map.mk₂ ℝ L1s_smul_const L1s_smul_const_add_fun L1s_smul_const_smul_fun
  L1s_smul_const_add_const L1s_smul_const_smul_const

lemma L1s_smul_const_bilin_coe_fn (f : α →₁ₛ[μ] ℝ) (x : G) :
  L1s_smul_const_bilin f x = L1s_smul_const f x :=
rfl

lemma L1s_smul_const_indicator {s : set α} (hs : measurable_set s) (c : G) (hμs : μ s < ∞) :
  L1s_smul_const (indicator_L1s hs (1 : ℝ) (or.inr hμs)) c = indicator_L1s hs c (or.inr hμs) :=
begin
  ext1,
  rw ← coe_coe,
  change (indicator_fun_smul_const (indicator_L1s hs (1 : ℝ) (or.inr hμs)) c : α →₁[μ] G)
    =ᵐ[μ] ⇑(indicator_L1s hs c (or.inr hμs)),
  change indicator_fun_smul_const (indicator_Lp 1 hs (1 : ℝ) (or.inr hμs)) c
    =ᵐ[μ] ⇑(indicator_L1s hs c (or.inr hμs)),
  exact (indicator_L1s_ae_eq_fun_smul_const hs c hμs).symm,
end

def tensor_to_L1s : ((α →₁ₛ[μ] ℝ) ⊗[ℝ] G) →ₗ[ℝ] α →₁ₛ[μ] G :=
tensor_product.uncurry ℝ (α →₁ₛ[μ] ℝ) G (α →₁ₛ[μ] G) L1s_smul_const_bilin

lemma tensor_to_L1s_indicator {s : set α} (hs : measurable_set s) (c : G) (hμs : μ s < ∞) :
  tensor_to_L1s (indicator_L1s hs (1 : ℝ) (or.inr hμs) ⊗ₜ c) = indicator_L1s hs c (or.inr hμs) :=
begin
  rw [tensor_to_L1s, tensor_product.uncurry_apply, L1s_smul_const_bilin_coe_fn],
  exact L1s_smul_const_indicator hs c hμs,
end

lemma tensor_to_L1s_surjective :
  function.surjective ⇑(tensor_to_L1s : ((α →₁ₛ[μ] ℝ) ⊗[ℝ] G) →ₗ[ℝ] α →₁ₛ[μ] G) :=
begin
  intro f,
  use ∑ y in range_nonzero f, (dite (y = 0) (λ h, (0 : α →₁ₛ[μ] ℝ))
    (λ h, indicator_L1s (measurable_set_fiber f y) (1 : ℝ) (or.inr (finite_fiber f y h)))) ⊗ₜ y,
  rw linear_map.map_sum,
  nth_rewrite 1 simple_func_eq_sum_indicator_L1s f,
  refine finset.sum_congr rfl (λ y hy, _),
  have hy0 : y ≠ 0 := ne_zero_of_mem_range_nonzero f y hy,
  simp only [hy0, dif_neg, not_false_iff],
  exact tensor_to_L1s_indicator _ _ _,
end

lemma tensor_to_L1s_eq_zero_iff {φ : (α →₁ₛ[μ] ℝ) ⊗[ℝ] G} :
  tensor_to_L1s φ = 0 ↔ φ = 0 :=
begin
  refine ⟨λ h_zero, _, λ h_zero, by { rw h_zero, exact tensor_to_L1s.map_zero }⟩,
  have hφ_range := (range_nonzero_eq_empty_iff _).mpr h_zero,
  sorry,
end

lemma tensor_to_L1s_injective :
  function.injective ⇑(tensor_to_L1s : ((α →₁ₛ[μ] ℝ) ⊗[ℝ] G) →ₗ[ℝ] α →₁ₛ[μ] G) :=
begin
  intros f g hfg,
  rw ← sub_eq_zero at hfg ⊢,
  rw ← linear_map.map_sub at hfg,
  exact tensor_to_L1s_eq_zero_iff.mp hfg,
end

def tensor_to_L1s_equiv : ((α →₁ₛ[μ] ℝ) ⊗[ℝ] G) ≃ₗ[ℝ] α →₁ₛ[μ] G :=
{ to_fun := tensor_to_L1s.to_fun,
  map_add' := tensor_to_L1s.map_add',
  map_smul' := tensor_to_L1s.map_smul',
  inv_fun := function.inv_fun tensor_to_L1s.to_fun,
  left_inv := function.left_inverse_inv_fun tensor_to_L1s_injective,
  right_inv := function.right_inverse_inv_fun tensor_to_L1s_surjective, }

def L1_extend_from_ℝ (T : (α →₁ₛ[μ] ℝ) →ₗ[ℝ] (α →₁[μ] ℝ)) : (α →₁ₛ[μ] G) →ₗ[ℝ] (α →₁[μ] G) :=
tensor_to_L1.comp ((linear_map.rtensor G T).comp tensor_to_L1s_equiv.symm.to_linear_map)

lemma norm_simple_func_eq_sum_norm_indicator_L1s (f : α →₁ₛ[μ] G) :
  ∥f∥ = ∑ y in range_nonzero f,
    ∥indicator_L1s (measurable_set_fiber f y) y (zero_or_finite_fiber f y)∥ :=
begin
  simp_rw norm_indicator_L1s,
  rw norm_eq_integral,
  rw simple_func.map_integral (to_simple_func f) _ (L1.simple_func.integrable f) norm_zero,
  simp_rw smul_eq_mul,
  have h_range := range_to_simple_func_subset f,
  by_cases h0_mem : (0 : G) ∈ (to_simple_func f).range,
  swap,
  { have h_range' : (to_simple_func f).range = range_nonzero f,
    { sorry, },
    rw h_range',
    refine finset.sum_congr rfl (λ y hy, _),
    rw mul_comm,
    congr' 2,
    refine measure_congr (preimage_congr_ae _ _),
    exact to_simple_func_eq_to_fun f, },
  have h_range' : (to_simple_func f).range = insert (0 : G) (range_nonzero f),
  { sorry, },
  rw [h_range', finset.sum_insert (λ h, ne_zero_of_mem_range_nonzero f 0 h rfl), norm_zero,
    mul_zero, zero_add],
  refine finset.sum_congr rfl (λ y hy, _),
  rw mul_comm,
  congr' 2,
  refine measure_congr (preimage_congr_ae _ _),
  exact to_simple_func_eq_to_fun f,
end

lemma projective_norm_eq_norm (f : α →₁ₛ[μ] G) :
  tensor_product.projective_norm (to_tensor_equiv f) = ∥f∥ :=
sorry

end tensor_dense_in_L1

end simple_func
end L1

end measure_theory
