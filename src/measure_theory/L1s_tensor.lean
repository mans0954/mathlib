import measure_theory.temp_simple_func
import analysis.normed_space.hahn_banach

noncomputable theory
open_locale classical topological_space big_operators nnreal ennreal measure_theory
  tensor_product

namespace tensor_product

section semi_normed_space

variables {R M N : Type*} [normed_field R]
  [normed_group M] [semi_normed_space R M]
  [normed_group N] [semi_normed_space R N]

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

/-- The projective norm on a tensor product. -/
def projective_norm (x : M ⊗[R] N) : ℝ :=
Inf {u : ℝ | ∃ (s : (M × N) →₀ R) (hs : s.sum (λ y r, r • y.1 ⊗ₜ y.2) = x),
  s.sum (λ y r, ∥r∥ * ∥y.1∥ * ∥y.2∥) = u}

--variables (R M N)
--def projective_tensor_product := M ⊗[R] N
--variables {R M N}

-- todo: how do I get tmul to return an element of that type? Do I need a tmulₚ?

instance : has_norm (M ⊗[R] N) :=
{ norm := projective_norm }

lemma projective_norm_def (x : M ⊗[R] N) :
  ∥x∥ = Inf {u : ℝ | ∃ (s : (M × N) →₀ R) (hs : s.sum (λ y r, r • y.1 ⊗ₜ y.2) = x),
  s.sum (λ y r, ∥r∥ * ∥y.1∥ * ∥y.2∥) = u} :=
rfl

lemma function.surjective.surj_on_preimage {α β} {f : α → β} (hf : function.surjective f)
  (s : set β) :
  set.surj_on f (f ⁻¹' s) s :=
begin
  intros x hx,
  rw set.mem_image,
  obtain ⟨y, hyx⟩ := hf x,
  use y,
  rw [set.mem_preimage, hyx],
  exact ⟨hx, rfl⟩,
end

lemma function.bijective.bij_on_preimage {α β} {f : α → β} (hf : function.bijective f)
  (s : set β) :
  set.bij_on f (f ⁻¹' s) s :=
⟨set.maps_to_preimage _ _, function.injective.inj_on hf.injective _,
  function.surjective.surj_on_preimage hf.surjective _⟩

/-- A representation of a simple element of `M ⊗ N` -/
protected def to_prod (x : M ⊗[R] N) : M × N :=
dite (∃ (m : M) (n : N), m ⊗ₜ[R] n = x) (λ h, (⟨h.some, h.some_spec.some⟩ : M × N)) (λ h, 0)

lemma tmul_to_prod_of_is_simple (x : M ⊗[R] N) (hx : ∃ (m : M) (n : N), m ⊗ₜ[R] n = x):
  (tensor_product.to_prod x).1 ⊗ₜ[R] (tensor_product.to_prod x).2 = x :=
by simp only [tensor_product.to_prod, hx, dif_pos, hx.some_spec.some_spec]

lemma tmul_to_prod (m : M) (n : N) :
  (tensor_product.to_prod (m ⊗ₜ[R] n)).1 ⊗ₜ[R] (tensor_product.to_prod (m ⊗ₜ[R] n)).2 = m ⊗ₜ[R] n :=
tmul_to_prod_of_is_simple _ ⟨m, n, rfl⟩

lemma exists_finsupp_sum_eq (x : M ⊗[R] N) :
  ∃ (s : (M × N) →₀ R), s.sum (λ y r, r • y.1 ⊗ₜ y.2) = x :=
begin
  have h_span := span_tmul_eq_top R M N,
  rw [eq_top_iff, ← submodule.span_univ, submodule.span_le] at h_span,
  specialize h_span (set.mem_univ x),
  rw [set_like.mem_coe, mem_span_set] at h_span,
  rcases h_span with ⟨c, ⟨hc1, hc2⟩⟩,
  let is_simple := λ t, ∃ (m : M) (n : N), m ⊗ₜ[R] n = t,
  let s := c.map_domain tensor_product.to_prod,
  use s,
  rw finsupp.sum_map_domain_index,
  swap, { simp, },
  swap, { simp_rw add_smul, simp, },
  rw ← hc2,
  refine finset.sum_congr rfl (λ y hy, _),
  dsimp only,
  congr,
  refine tmul_to_prod_of_is_simple y _,
  rw ← finset.mem_coe at hy,
  exact hc1 hy,
end

lemma nonempty_norm_set (x : M ⊗[R] N) :
  set.nonempty {u : ℝ | ∃ (s : (M × N) →₀ R) (hs : s.sum (λ y r, r • y.1 ⊗ₜ y.2) = x),
  s.sum (λ y r, ∥r∥ * ∥y.1∥ * ∥y.2∥) = u} :=
begin
  suffices h_exists_s : ∃ (s : (M × N) →₀ R), s.sum (λ y r, r • y.1 ⊗ₜ y.2) = x,
  { rcases h_exists_s with ⟨s, hsx⟩,
    refine @set.nonempty_of_mem _ _ (s.sum (λ y r, ∥r∥ * ∥y.1∥ * ∥y.2∥)) _,
    use [s, hsx], },
  exact exists_finsupp_sum_eq x,
end

lemma multiset.sum_map_nonneg {β γ} [ordered_add_comm_monoid γ] {m : multiset β} {f : β → γ}
  (h : ∀ x ∈ m, 0 ≤ f x) :
  0 ≤ (m.map f).sum :=
begin
  refine multiset.sum_nonneg (λ y hy, _),
  rw multiset.mem_map at hy,
  rcases hy with ⟨z, hz⟩,
  rw ← hz.2,
  exact h z hz.1,
end

private lemma norm_nonneg' (x : M ⊗[R] N) : 0 ≤ ∥x∥ :=
begin
  refine le_cInf (nonempty_norm_set x) (λ u hu, _),
  rcases hu with ⟨s, hsx, hsu⟩,
  rw ← hsu,
  exact finset.sum_nonneg (λ y hy,
    mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)),
end

lemma cinfi_le_cinfi2 {α : Type*} {ι ι₂ : Sort*} [nonempty ι₂] {s : ι → α} {t : ι₂ → α}
  [conditionally_complete_lattice α] (hs : bdd_below (set.range s))
  (h : ∀j, ∃i, s i ≤ t j) : infi s ≤ infi t :=
le_cinfi (λ x, (cinfi_le hs _).trans (h x).some_spec)

lemma cInf_le_cInf2 {α : Type*} {s : set α} {t : set α}
  [conditionally_complete_lattice α] (hs : bdd_below s) (ht : t.nonempty)
  (h : ∀ j ∈ t, ∃ i ∈ s, i ≤ j) : Inf s ≤ Inf t :=
le_cInf ht (λ x hxt, (cInf_le hs (h x hxt).some_spec.some).trans (h x hxt).some_spec.some_spec)

lemma bdd_below_of_le {β} [preorder β] {s : set β} (y : β) (h : ∀ x ∈ s, y ≤ x) : bdd_below s :=
bdd_below_iff_subset_Ici.mpr ⟨y, λ z hzs, set.mem_Ici.mpr (h z hzs)⟩

lemma bdd_below_norm_set (x : M ⊗[R] N) :
  bdd_below {u : ℝ | ∃ (s : (M × N) →₀ R) (hs : s.sum (λ y r, r • y.1 ⊗ₜ y.2) = x),
    s.sum (λ y r, ∥r∥ * ∥y.1∥ * ∥y.2∥) = u} :=
begin
  refine bdd_below_of_le 0 (λ z h, _),
  rcases h with ⟨sh, hsh, h⟩,
  rw ← h,
  exact multiset.sum_map_nonneg (λ y hy,
    mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)),
end

lemma norm_simple_le (m : M) (n : N) : ∥m ⊗ₜ[R] n∥ ≤ ∥m∥ * ∥n∥ :=
begin
  refine cInf_le (bdd_below_norm_set _) _,
  use finsupp.single (⟨m,n⟩ : M × N) (1 : R),
  rw [finsupp.sum_single_index, finsupp.sum_single_index],
  all_goals { simp, },
end

lemma norm_sum_simple_le (s : (M × N) →₀ R) :
  ∥s.sum (λ y r, r • y.1 ⊗ₜ[R] y.2)∥ ≤ s.sum (λ y r, ∥r∥ * ∥y.1∥ * ∥y.2∥) :=
cInf_le (bdd_below_norm_set _) ⟨s, by simp⟩

private lemma norm_zero' : ∥(0 : M ⊗[R] N)∥ = 0 :=
begin
  refine le_antisymm _ (norm_nonneg' _),
  rw ← tmul_zero N (0 : M),
  refine (norm_simple_le _ _).trans _,
  simp,
end

lemma bdd_below_mul_iff (s : set ℝ) (r : ℝ) (hr : 0 < r) :
  bdd_below s ↔ bdd_below {x | ∃ y ∈ s, r * y = x} :=
begin
  rw [← not_iff_not, not_bdd_below_iff, not_bdd_below_iff],
  split; intros h x,
  { obtain ⟨y, hy_mem, hyx⟩ := h (r⁻¹ * x),
    use r * y,
    split,
    { use [y, hy_mem], },
    { field_simp at hyx,
      rwa lt_div_iff' hr at hyx, }, },
  { obtain ⟨y, hy_mem, hyx⟩ := h (r * x),
    obtain ⟨z, hz_mem, hzy⟩ := hy_mem,
    use [z, hz_mem],
    rw ← hzy at hyx,
    exact lt_of_mul_lt_mul_left hyx hr.le, },
end

lemma nonempty_mul_iff (s : set ℝ) (r : ℝ) :
  s.nonempty ↔ {x | ∃ y ∈ s, r * y = x}.nonempty :=
begin
  split; intro h_nonempty,
  { have hxr : r * h_nonempty.some ∈ {x | ∃ y ∈ s, r * y = x},
      by use [h_nonempty.some, h_nonempty.some_spec],
    exact set.nonempty_of_mem hxr, },
  { obtain ⟨y, hys, hy⟩ := h_nonempty.some_spec,
    exact set.nonempty_of_mem hys, },
end

lemma mul_Inf_eq_Inf_mul_of_nonneg (s : set ℝ) (r : ℝ) (hr : 0 ≤ r) :
  r * Inf s = Inf {x | ∃ y ∈ s, r * y = x} :=
begin
  by_cases hs_nonempty : s.nonempty,
  swap,
  { rw set.not_nonempty_iff_eq_empty at hs_nonempty,
    rw hs_nonempty,
    simp [real.Inf_empty], },
  have h_nonempty_mul : {x | ∃ y ∈ s, r * y = x}.nonempty,
    from (nonempty_mul_iff s r).mp hs_nonempty,
  by_cases hr0 : r = 0,
  { simp_rw [hr0, zero_mul],
    have h_eq_singleton : {x : ℝ | ∃ (y : ℝ) (H : y ∈ s), 0 = x} = {0},
    { ext1 x,
      simp only [exists_prop, set.mem_singleton_iff, exists_and_distrib_right, set.mem_set_of_eq],
      exact ⟨λ h, h.2.symm, λ h, ⟨hs_nonempty, h.symm⟩⟩, },
    rw h_eq_singleton,
    simp, },
  have hr_pos : 0 < r, from lt_of_le_of_ne hr (ne.symm hr0),
  by_cases hs : bdd_below s,
  swap,
  { have h_iff := not_iff_not.mpr (bdd_below_mul_iff s r hr_pos),
    rw [real.Inf_of_not_bdd_below hs, real.Inf_of_not_bdd_below (h_iff.mp hs), mul_zero], },
  refine le_antisymm _ _,
  { refine le_cInf h_nonempty_mul (λ x hx, _),
    rw ← le_div_iff' hr_pos,
    refine cInf_le hs _,
    obtain ⟨y, hys, hyx⟩ := hx,
    rw [mul_comm, ← eq_div_iff hr0] at hyx,
    rwa hyx at hys, },
  { rw ← div_le_iff' hr_pos,
    refine le_cInf hs_nonempty (λ x hx, _),
    rw div_le_iff' hr_pos,
    refine cInf_le ((bdd_below_mul_iff _ _ hr_pos).mp hs) _,
    use [x, hx], },
end

private lemma norm_smul_le' (a : R) (x : M ⊗[R] N) : ∥a • x∥ ≤ ∥a∥ * ∥x∥ :=
begin
  by_cases ha_zero : a = 0,
  { rw ha_zero,
    simp [norm_zero'], },
  simp_rw projective_norm_def,
  have h_mul : ∥a∥ * Inf {u : ℝ | ∃ (s : (M × N) →₀ R) (hs : s.sum (λ y r, r • y.1 ⊗ₜ[R] y.2) = x),
      s.sum (λ y r, ∥r∥ * ∥y.1∥ * ∥y.2∥) = u}
    = Inf {u : ℝ | ∃ (s : (M × N) →₀ R) (hs : s.sum (λ y r, r • y.1 ⊗ₜ[R] y.2) = x),
      s.sum (λ y r, ∥r∥ * ∥y.1∥ * ∥a • y.2∥) = u},
  { rw mul_Inf_eq_Inf_mul_of_nonneg _ _ (norm_nonneg _),
    congr,
    ext1 u,
    simp only [exists_prop, exists_exists_and_eq_and, eq_iff_iff, set.mem_set_of_eq],
    simp_rw [finsupp.mul_sum, norm_smul],
    split; intro h; obtain ⟨s, ⟨h1, h2⟩⟩ := h; refine ⟨s, ⟨h1, _⟩⟩; rw ← h2; congr; ext y r; ring, },
  rw h_mul,
  clear h_mul,
  refine cInf_le_cInf2 (bdd_below_norm_set _) _ (λ u hu, _),
  { suffices h_exists_s : ∃ (s : (M × N) →₀ R), s.sum (λ y r, r • y.1 ⊗ₜ[R] y.2) = x,
    { rcases h_exists_s with ⟨s, hsx⟩,
      refine @set.nonempty_of_mem _ _ (s.sum (λ y r, ∥r∥ * ∥y.1∥ * ∥a • y.2∥)) _,
      use [s, hsx], },
    exact exists_finsupp_sum_eq x, },
  rcases hu with ⟨s, hsx, hsu⟩,
  let f_smul : (M × N) → (M × N) := λ y, ⟨y.1, a⁻¹ • y.2⟩,
  have h_bij : function.bijective f_smul,
  { split,
    { intros y z hyz,
      simp_rw prod.ext_iff at hyz,
      ext,
      { exact hyz.1, },
      { suffices : a • a⁻¹ • y.snd = a • a⁻¹ • z.snd,
        by rwa [← smul_assoc, ← smul_assoc, smul_eq_mul, mul_inv_cancel ha_zero, one_smul,
          one_smul] at this,
        rw hyz.2, }, },
    { intro x,
      use ⟨x.1, a • x.2⟩,
      simp_rw f_smul,
      dsimp only,
      rw [← smul_assoc, smul_eq_mul, inv_mul_cancel ha_zero, one_smul],
      ext; dsimp only; refl, }, },
  have h_bij_on : set.bij_on f_smul (f_smul ⁻¹' ↑(s.support)) ↑(s.support),
    from function.bijective.bij_on_preimage h_bij _,
  let s_smul := s.comap_domain f_smul h_bij_on.inj_on,
  use s_smul.sum (λ y r, ∥r∥ * ∥y.fst∥ * ∥y.snd∥),
  split,
  { refine ⟨s_smul, _, rfl⟩,
    have h_comp : (λ (y : M × N) (r : R), r • y.fst ⊗ₜ[R] y.snd)
      = (λ (y : M × N) (r : R), r • y.fst ⊗ₜ[R] (a • y.snd)) ∘ f_smul,
    { ext y r,
      simp_rw [function.comp_apply, ← smul_assoc, smul_eq_mul, mul_inv_cancel ha_zero,
        one_smul], },
    rw [h_comp, finsupp.sum_comap_domain _ _ _ h_bij_on, ← hsx, finsupp.smul_sum],
    simp_rw [tmul_smul, smul_smul, mul_comm a], },
  { rw ← hsu,
    have h_comp : (λ (y : M × N) (r : R), ∥r∥ * ∥y.fst∥ * ∥y.snd∥)
      = (λ (y : M × N) (r : R), ∥r∥ * ∥y.fst∥ * ∥a • y.snd∥) ∘ f_smul,
    { ext y r,
      simp_rw [function.comp_apply, ← smul_assoc, smul_eq_mul, mul_inv_cancel ha_zero, one_smul], },
    rw [h_comp, finsupp.sum_comap_domain _ _ _ h_bij_on], },
end

private lemma norm_neg_le (x : M ⊗[R] N) : ∥-x∥ ≤ ∥x∥ :=
begin
  nth_rewrite 0 ← one_smul R x,
  rw ← neg_smul,
  refine (norm_smul_le' _ _).trans _,
  simp,
end

private lemma norm_neg' (x : M ⊗[R] N) : ∥-x∥ = ∥x∥ :=
begin
  refine le_antisymm (norm_neg_le x) _,
  nth_rewrite 0 ← neg_neg x,
  exact norm_neg_le (-x),
end

lemma exists_le_norm_add (z : M ⊗[R] N) (ε : ℝ) (hε : 0 < ε) :
  ∃ s : (M × N) →₀ R, (s.sum (λ u r, r • u.1 ⊗ₜ u.2) = z) ∧
    s.sum (λ u r, ∥r∥ * ∥u.1∥ * ∥u.2∥) ≤ ∥z∥ + ε :=
begin
  rw ← @not_not
    (∃ s : (M × N) →₀ R, (s.sum (λ u r, r • u.1 ⊗ₜ u.2) = z) ∧
    s.sum (λ u r, ∥r∥ * ∥u.1∥ * ∥u.2∥) ≤ ∥z∥ + ε),
  intro h,
  push_neg at h,
  suffices h_add_le : ∥z∥ + ε ≤ ∥z∥,
  { have h_lt : ∥z∥ < ∥z∥ + ε, from lt_add_of_pos_right _ hε,
    rw ← not_le at h_lt,
    exact h_lt h_add_le, },
  nth_rewrite 1 projective_norm_def,
  refine le_cInf (nonempty_norm_set _) (λ u hu, _),
  rcases hu with ⟨s, hsx, hsu⟩,
  rw ← hsu,
  exact (h s hsx).le,
end

lemma finsupp.prod_add_le {α M N} [add_comm_monoid M] [ordered_comm_semiring N] {f g : α →₀ M}
  {h : α → M → N} (h_zero : ∀a, h a 0 = 1) (h_nonneg : ∀ a b, 0 ≤ h a b)
  (h_add : ∀a b₁ b₂, h a (b₁ + b₂) ≤ h a b₁ * h a b₂) :
  (f + g).prod h ≤ f.prod h * g.prod h :=
begin
  have hf : f.prod h = ∏ a in f.support ∪ g.support, h a (f a),
    from f.prod_of_support_subset (finset.subset_union_left _ _) _ (λ a ha, h_zero a),
  have hg : g.prod h = ∏ a in f.support ∪ g.support, h a (g a),
    from g.prod_of_support_subset (finset.subset_union_right _ _) _ (λ a ha, h_zero a),
  have hfg : (f + g).prod h = ∏ a in f.support ∪ g.support, h a ((f + g) a),
    from (f + g).prod_of_support_subset finsupp.support_add _ (λ a ha, h_zero a),
  simp only [*, finsupp.add_apply, finset.prod_mul_distrib],
  have h_le : ∏ (a : α) in f.support ∪ g.support, h a (f a + g a)
      ≤ ∏ (a : α) in f.support ∪ g.support, (h a (f a) * h a (g a)),
   from finset.prod_le_prod (λ x _, h_nonneg x _) (λ x _, h_add x _ _),
  refine h_le.trans _,
  rw finset.prod_mul_distrib,
end

lemma finsupp.sum_add_le {α M N} [add_comm_monoid M] [ordered_add_comm_monoid N] {f g : α →₀ M}
  {h : α → M → N} (h_zero : ∀a, h a 0 = 0) (h_add : ∀a b₁ b₂, h a (b₁ + b₂) ≤ h a b₁ + h a b₂) :
  (f + g).sum h ≤ f.sum h + g.sum h :=
begin
  have hf : f.sum h = ∑ a in f.support ∪ g.support, h a (f a),
    from f.sum_of_support_subset (finset.subset_union_left _ _) _ (λ a ha, h_zero a),
  have hg : g.sum h = ∑ a in f.support ∪ g.support, h a (g a),
    from g.sum_of_support_subset (finset.subset_union_right _ _) _ (λ a ha, h_zero a),
  have hfg : (f + g).sum h = ∑ a in f.support ∪ g.support, h a ((f + g) a),
    from (f + g).sum_of_support_subset finsupp.support_add _ (λ a ha, h_zero a),
  simp only [*, finsupp.add_apply, finset.prod_mul_distrib],
  have h_le : ∑ (a : α) in f.support ∪ g.support, h a (f a + g a)
      ≤ ∑ (a : α) in f.support ∪ g.support, (h a (f a) + h a (g a)),
   from finset.sum_le_sum (λ x _, h_add x _ _),
  refine h_le.trans _,
  rw finset.sum_add_distrib,
end

private lemma triangle' (x y : M ⊗[R] N) : ∥x + y∥ ≤ ∥x∥ + ∥y∥ :=
begin
  refine le_of_forall_pos_le_add (λ ε hε, _),
  obtain ⟨sx, hx⟩ := exists_le_norm_add x (ε/2) (half_pos hε),
  obtain ⟨sy, hy⟩ := exists_le_norm_add y (ε/2) (half_pos hε),
  suffices h_le_ε_half_ε_half : ∥x + y∥ ≤ ∥x∥ + ε/2 + (∥y∥ + ε/2),
  { refine h_le_ε_half_ε_half.trans (le_of_eq _),
    rw [add_assoc, add_comm (ε/2), add_assoc, div_add_div_same, half_add_self, ← add_assoc], },
  suffices h_le_sums : ∥x + y∥
      ≤ sx.sum (λ u r, ∥r∥ * ∥u.fst∥ * ∥u.snd∥) + sy.sum (λ u r, ∥r∥ * ∥u.fst∥ * ∥u.snd∥),
    from h_le_sums.trans (add_le_add hx.2 hy.2),
  rw [← hx.1, ← hy.1],
  rw ← @finsupp.sum_add_index,
  swap, { simp, },
  swap, { intros y r1 r2, rw add_smul, },
  refine (norm_sum_simple_le _).trans _,
  refine finsupp.sum_add_le _ _,
  { simp, },
  { intros y r1 r2,
    rw [← add_mul, ← add_mul, mul_assoc, mul_assoc],
    exact mul_le_mul (norm_add_le _ _) le_rfl (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (add_nonneg (norm_nonneg _) (norm_nonneg _)), },
end

instance : semi_normed_group (M ⊗[R] N) :=
semi_normed_group.of_core (M ⊗[R] N)
{ norm_zero := norm_zero',
  triangle := triangle',
  norm_neg := norm_neg', }

instance : semi_normed_space R (M ⊗[R] N) :=
{ norm_smul_le := norm_smul_le', }

section is_R_or_C

variables {𝕂 : Type*} [is_R_or_C 𝕂] [normed_space 𝕂 M] [normed_space 𝕂 N]
  [nontrivial M] [nontrivial N]

section norm_simple

variables (𝕂)
def norm_simple_aux_cont_bilin (m : M) (n : N) : M →L[𝕂] N →L[𝕂] 𝕂 :=
@continuous_linear_map.bilinear_comp 𝕂 𝕂 𝕂 𝕂 _ _ _ _ _ _ _ M N _
    _ _ _ (continuous_linear_map.lmul 𝕂 𝕂) (@exists_dual_vector' 𝕂 _ M _ _ _ m).some
    (@exists_dual_vector' 𝕂 _ N _ _ _ n).some

def norm_simple_aux (m : M) (n : N) : M ⊗[𝕂] N →ₗ[𝕂] 𝕂 :=
begin
  let B : M →L[𝕂] N →L[𝕂] 𝕂 := norm_simple_aux_cont_bilin 𝕂 m n,
  let B_lin : M →ₗ[𝕂] N →ₗ[𝕂] 𝕂 :=
  { to_fun := λ m, B m,
    map_add' := λ m1 m2, by simp,
    map_smul' := λ r m, by simp, },
  exact tensor_product.lift B_lin,
end

lemma norm_simple_aux_apply (m : M) (n : N) (a : M) (b : N) :
  norm_simple_aux 𝕂 m n (a ⊗ₜ[𝕂] b)
    = (@exists_dual_vector' 𝕂 _ M _ _ _ m).some a * (@exists_dual_vector' 𝕂 _ N _ _ _ n).some b :=
by simp [norm_simple_aux, norm_simple_aux_cont_bilin]

lemma norm_simple_aux_le (m : M) (n : N) (a : M) (b : N) :
  ∥norm_simple_aux 𝕂 m n (a ⊗ₜ[𝕂] b)∥ ≤ ∥a∥ * ∥b∥ :=
begin
  rw norm_simple_aux_apply,
  refine (norm_mul_le _ _).trans _,
  refine mul_le_mul _ _ (norm_nonneg _) (norm_nonneg _),
  { have hm := (@exists_dual_vector' 𝕂 _ M _ _ _ m).some_spec,
    refine ((@exists_dual_vector' 𝕂 _ M _ _ _ m).some.le_op_norm _).trans _,
    rw [hm.1, one_mul], },
  { have hn := (@exists_dual_vector' 𝕂 _ N _ _ _ n).some_spec,
    refine ((@exists_dual_vector' 𝕂 _ N _ _ _ n).some.le_op_norm _).trans _,
    rw [hn.1, one_mul], },
end

lemma norm_norm_simple_aux_eq (m : M) (n : N) : ∥norm_simple_aux 𝕂 m n (m ⊗ₜ[𝕂] n)∥ = ∥m∥ * ∥n∥ :=
begin
  rw norm_simple_aux_apply 𝕂 m n m n,
  have hm := (@exists_dual_vector' 𝕂 _ M _ _ _ m).some_spec,
  have hn := (@exists_dual_vector' 𝕂 _ N _ _ _ n).some_spec,
  rw [hm.2, hn.2],
  simp only [normed_field.norm_mul, norm_norm'],
end
variables {𝕂}

lemma norm_simple (m : M) (n : N) : ∥m ⊗ₜ[𝕂] n∥ = ∥m∥ * ∥n∥ :=
begin
  refine le_antisymm (norm_simple_le m n) _,
  obtain ⟨m', hm'⟩ := @exists_dual_vector' 𝕂 _ M _ _ _ m,
  obtain ⟨n', hn'⟩ := @exists_dual_vector' 𝕂 _ N _ _ _ n,
  simp_rw norm'_def 𝕂 at hm',
  rw [← norm_norm_simple_aux_eq 𝕂 m n, projective_norm_def],
  refine le_cInf (nonempty_norm_set _) (λ u hu, _),
  obtain ⟨s, hs, hsu⟩ := hu,
  rw [← hs, (norm_simple_aux 𝕂 m n).map_finsupp_sum],
  refine (norm_sum_le _ _).trans _,
  simp_rw [(norm_simple_aux 𝕂 m n).map_smul, norm_smul],
  suffices h_le : ∑ (a : M × N) in s.support, ∥s a∥ * ∥(norm_simple_aux 𝕂 m n) (a.fst ⊗ₜ[𝕂] a.snd)∥
      ≤ ∑ (a : M × N) in s.support, ∥s a∥ * ∥a.fst∥ * ∥a.snd∥,
    from h_le.trans (le_of_eq hsu),
  refine finset.sum_le_sum (λ x hx, _),
  rw mul_assoc,
  refine mul_le_mul le_rfl _ (norm_nonneg _) (norm_nonneg _),
  exact norm_simple_aux_le 𝕂 m n _ _,
end

end norm_simple

section normed_space

private lemma norm_eq_zero_iff' (x : M ⊗[𝕂] N) : ∥x∥ = 0 ↔ x = 0 :=
begin
  split; intro h_eq_zero,
  swap, { rw h_eq_zero, exact norm_zero, },
  sorry,
end

instance : normed_group (M ⊗[𝕂] N) :=
normed_group.of_core (M ⊗[𝕂] N)
{ norm_eq_zero_iff := norm_eq_zero_iff',
  triangle := triangle',
  norm_neg := norm_neg', }

end normed_space

end is_R_or_C

end semi_normed_space

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

lemma to_tensor_surjective :
  function.surjective (to_tensor : (α →₁ₛ[μ] G) → ((α →₁ₛ[μ] ℝ) ⊗[ℝ] G)) :=
begin
  rw [← to_tensor_lm_coe, ← linear_map.range_eq_top, eq_top_iff, ← tensor_product.span_tmul_eq_top,
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

lemma indicator_fun_smul_const_smul_const [normed_space ℝ F] [smul_comm_class ℝ 𝕂 F]
  (c : 𝕂) (f : α →₁[μ] ℝ) (x : F) :
  L1.indicator_fun_smul_const f (c • x) = c • L1.indicator_fun_smul_const f x :=
begin
  ext1,
  refine eventually_eq.trans _ (Lp.coe_fn_smul c _).symm,
  refine (L1.indicator_fun_smul_const_coe_fn _ _).trans _,
  refine (L1.indicator_fun_smul_const_coe_fn f x).mono (λ a ha, _),
  rw [pi.smul_apply, ha],
  dsimp only,
  rw smul_comm,
end

def indicator_fun_smul_const_bilin : (α →₁[μ] ℝ) →ₗ[ℝ] G →ₗ[ℝ] α →₁[μ] G :=
linear_map.mk₂ ℝ indicator_fun_smul_const
  indicator_fun_smul_const_add_fun
  indicator_fun_smul_const_smul_fun
  indicator_fun_smul_const_add_const
  indicator_fun_smul_const_smul_const

def tensor_to_L1' : ((α →₁[μ] ℝ) ⊗[ℝ] G) →ₗ[ℝ] α →₁[μ] G :=
tensor_product.uncurry ℝ (α →₁[μ] ℝ) G (α →₁[μ] G) indicator_fun_smul_const_bilin

lemma tensor_to_L1'_smul_const [normed_space ℝ F] [smul_comm_class ℝ 𝕂 F]
  (c : 𝕂) (φ : (α →₁[μ] ℝ) ⊗[ℝ] F) :
  tensor_to_L1' (c • φ) = c • tensor_to_L1' φ :=
begin
  refine tensor_product.induction_on φ _ _ _,
  { rw [linear_map.map_zero, smul_zero, linear_map.map_zero, smul_zero], },
  { intros f x,
    sorry, },
  { intros η ξ hη hξ,
    rw [smul_add, tensor_to_L1'.map_add, hη, hξ, tensor_to_L1'.map_add, smul_add], },
end

def tensor_to_L1 [normed_space ℝ F] [smul_comm_class ℝ 𝕂 F] :
  ((α →₁[μ] ℝ) ⊗[ℝ] F) →ₗ[𝕂] α →₁[μ] F :=
{ to_fun := tensor_to_L1'.to_fun,
  map_add' := tensor_to_L1'.map_add',
  map_smul' := tensor_to_L1'_smul_const, }

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

lemma L1s_smul_const_smul_const [normed_space ℝ F] [smul_comm_class ℝ 𝕂 F]
  (c : 𝕂) (f : α →₁ₛ[μ] ℝ) (x : F) :
  L1s_smul_const f (c • x) = c • L1s_smul_const f x :=
begin
  ext1,
  refine eventually_eq.trans _ (coe_fn_smul c _).symm,
  refine (L1s_smul_const_coe_fn _ _).trans _,
  refine (L1s_smul_const_coe_fn f x).mono (λ a ha, _),
  rw [pi.smul_apply, ha],
  dsimp only,
  have : add_comm_group (F →ₗ[𝕂] ↥(α →₁ₛ[μ] F)),
  { exact linear_map.add_comm_group, },
  rw smul_comm,
end

variables [normed_space ℝ F] [is_scalar_tower ℝ 𝕂 F]

instance : is_scalar_tower ℝ 𝕂 (Lp F p μ) :=
{ smul_assoc := λ r c f, by { ext1,
    refine (Lp.coe_fn_smul _ _).trans _,
    refine eventually_eq.trans _ (Lp.coe_fn_smul _ _).symm,
    refine (Lp.coe_fn_smul c f).mono (λ x hx, _),
    rw [pi.smul_apply, pi.smul_apply, hx, pi.smul_apply, smul_assoc], } }

instance : is_scalar_tower ℝ 𝕂 (α →₁ₛ[μ] F) :=
{ smul_assoc := λ r c f, by { ext1,
    refine (coe_fn_smul _ _).trans _,
    refine eventually_eq.trans _ (coe_fn_smul _ _).symm,
    refine (coe_fn_smul c f).mono (λ x hx, _),
    rw [pi.smul_apply, pi.smul_apply, hx, pi.smul_apply, smul_assoc], } }

variables (𝕂)
def L1s_smul_const_bilin : (α →₁ₛ[μ] ℝ) →ₗ[ℝ] F →ₗ[𝕂] α →₁ₛ[μ] F :=
linear_map.mk₂' ℝ 𝕂 L1s_smul_const
  L1s_smul_const_add_fun L1s_smul_const_smul_fun L1s_smul_const_add_const L1s_smul_const_smul_const
variables {𝕂}

lemma L1s_smul_const_bilin_coe_fn (f : α →₁ₛ[μ] ℝ) (x : F) :
  L1s_smul_const_bilin 𝕂 f x = L1s_smul_const f x :=
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

variables (𝕂)
def tensor_to_L1s : ((α →₁ₛ[μ] ℝ) ⊗[ℝ] F) →ₗ[𝕂] α →₁ₛ[μ] F :=
tensor_product.uncurry' ℝ (α →₁ₛ[μ] ℝ) F (α →₁ₛ[μ] F) (L1s_smul_const_bilin 𝕂)
variables {𝕂}

lemma tensor_to_L1s_indicator {s : set α} (hs : measurable_set s) (c : F) (hμs : μ s < ∞) :
  tensor_to_L1s 𝕂 (indicator_L1s hs (1 : ℝ) (or.inr hμs) ⊗ₜ c) = indicator_L1s hs c (or.inr hμs) :=
begin
  rw [tensor_to_L1s, tensor_product.uncurry'_apply, L1s_smul_const_bilin_coe_fn],
  exact L1s_smul_const_indicator hs c hμs,
end

lemma tensor_to_L1s_surjective :
  function.surjective ⇑(tensor_to_L1s 𝕂 : ((α →₁ₛ[μ] ℝ) ⊗[ℝ] F) →ₗ[𝕂] α →₁ₛ[μ] F) :=
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

protected theorem tensor_product.induction_on' {R M N : Type*} [comm_semiring R] [add_comm_monoid M]
  [add_comm_monoid N] [semimodule R M] [semimodule R N]
  {C : (M ⊗[R] N) → Prop}
  (z : M ⊗[R] N)
  (C0 : C 0)
  (C1 : ∀ {m n}, C $ m ⊗ₜ[R] n)
  (Cp : ∀ {x m n}, C x → C (m ⊗ₜ n) → C (x + m ⊗ₜ n)) : C z :=
begin
  refine tensor_product.induction_on z C0 (λ m n, C1) _,
  intros x y Cx Cy,
  -- todo: rewrite y as a finite sum of simple terms, induction on the finset.
  sorry,
end

variables (α)
def finite_measurable_set (μ : measure α) : Type* :=
{s : set α // measurable_set s ∧ μ s < ∞}
variables {α}

lemma sum_indicators_simple' (f : (α →₁ₛ[μ] ℝ)) (x : F) :
  ∃ (t : ((finite_measurable_set α μ) × F) →₀ ℝ),
  f ⊗ₜ[ℝ] x = t.sum (λ s r, (indicator_L1s s.1.prop.1 (1 : ℝ) (or.inr s.1.prop.2)) ⊗ₜ s.2) :=
begin
  let t := finset.range (range_nonzero f).card,
  let range_list := (range_nonzero f).val.to_list,
  let sets := λ n, dite (n < range_list.length) (λ hn, f ⁻¹' {range_list.nth_le n hn}) (λ hn, ∅),
  let vals := λ n, dite (n < range_list.length) (λ hn, (range_list.nth_le n hn) • x) (λ hn, 0),
  sorry,
end

lemma sum_indicators_simple (f : α →₁ₛ[μ] ℝ) (x : F) :
  ∃ (t : finset ℕ) (sets : ℕ → set α) (h_meas : ∀ n, measurable_set (sets n))
  (hμ : ∀ n, μ (sets n) < ∞)  (vals : ℕ → F),
  f ⊗ₜ[ℝ] x = ∑ n in t, (indicator_L1s (h_meas n) (1 : ℝ) (or.inr (hμ n))) ⊗ₜ (vals n) :=
begin
  let t := finset.range (range_nonzero f).card,
  let range_list := (range_nonzero f).val.to_list,
  have h_range_meas : ∀ n (hn : n < range_list.length),
      measurable_set (f ⁻¹' {range_list.nth_le n hn}),
    from λ n hn, measurable_set_fiber f _,
  have h_range_finite : ∀ n (hn : n < range_list.length),  μ (f ⁻¹' {range_list.nth_le n hn}) < ∞,
  { refine λ n hn, finite_fiber f _ _,
    have hn_mem : range_list.nth_le n hn ∈ range_nonzero f,
    { have h_mem_list := range_list.nth_le_mem n hn,
      simp_rw range_list at h_mem_list,
      rw multiset.mem_to_list at h_mem_list,
      exact h_mem_list, },
    exact ne_zero_of_mem_range_nonzero f _ hn_mem, },
  let sets := λ n, dite (n < range_list.length) (λ hn, f ⁻¹' {range_list.nth_le n hn}) (λ hn, ∅),
  let vals := λ n, dite (n < range_list.length) (λ hn, (range_list.nth_le n hn) • x) (λ hn, 0),
  refine ⟨t, sets, (λ n, _), (λ n, _), vals, _⟩,
  { by_cases hn : n < range_list.length,
    { simp only [sets, hn, dif_pos],
      exact measurable_set_fiber f _, },
    { simp [sets, hn], }, },
  { by_cases hn : n < range_list.length,
    { simp only [sets, hn, dif_pos],
      exact h_range_finite n hn, },
    { simp [sets, hn], }, },
  have hf_eq : f = ∑ n in t, dite (n < range_list.length)
    (λ hn, indicator_L1s (h_range_meas n hn) (range_list.nth_le n hn)
      (or.inr (h_range_finite n hn)))
    (λ hn, (0 : α →₁ₛ[μ] ℝ)),
  { sorry, },
  sorry,
end

lemma sum_indicators (φ : (α →₁ₛ[μ] ℝ) ⊗[ℝ] F) :
  ∃ (t : finset ℕ) (sets : ℕ → set α) (h_meas : ∀ n, measurable_set (sets n))
  (hμ : ∀ n, μ (sets n) < ∞) (vals : ℕ → F),
  φ = ∑ n in t, (indicator_L1s (h_meas n) (1 : ℝ) (or.inr (hμ n))) ⊗ₜ (vals n) :=
begin
  refine tensor_product.induction_on φ _ _ _,
  { refine ⟨∅, (λ n, ∅), by simp⟩, },
  { exact sum_indicators_simple, },
  { intros η ξ hη hξ,
    obtain ⟨tη, sη, hsη, hsμη, valsη, h_eqη⟩ := hη,
    obtain ⟨tξ, sξ, hsξ, hsμξ, valsξ, h_eqξ⟩ := hξ,
    sorry, },
end

lemma sum_disjoint_indicators_of_sum_indicators (φ : (α →₁ₛ[μ] ℝ) ⊗[ℝ] F) (t : finset ℕ)
  (sets : ℕ → set α) (h_meas : ∀ n, measurable_set (sets n)) (hμ : ∀ n, μ (sets n) < ∞)
  (vals : ℕ → F)
  (hφ : φ = ∑ n in t, (indicator_L1s (h_meas n) (1 : ℝ) (or.inr (hμ n))) ⊗ₜ (vals n)) :
  ∃ (t : finset ℕ) (sets : ℕ → set α) (h_meas : ∀ n, measurable_set (sets n))
    (hμ : ∀ n, μ (sets n) < ∞) (h_disj : ∀ n m : ℕ, n ≠ m → μ (sets n ∩ sets m) = 0)
    (vals : ℕ → F),
  φ = ∑ n in t, (indicator_L1s (h_meas n) (1 : ℝ) (or.inr (hμ n))) ⊗ₜ (vals n) :=
begin
  revert t φ,
  refine finset.induction _ _,
  { intros ξ hξ,
    rw finset.sum_empty at hξ,
    refine ⟨∅, (λ n, ∅), _⟩,
    simp [hξ], },
  intros a s has hs φ hφ,
  rw finset.sum_insert has at hφ,
  let ξ := ∑ n in s, (indicator_L1s (h_meas n) (1 : ℝ) (or.inr (hμ n))) ⊗ₜ (vals n),
  specialize hs ξ rfl,
  obtain ⟨tξ, setsξ, h_measξ, hμξ, h_disjξ, valsξ, h_eqξ⟩ := hs,
  sorry,
end

lemma sum_disjoint_indicators (φ : (α →₁ₛ[μ] ℝ) ⊗[ℝ] F) :
  ∃ (t : finset ℕ) (sets : ℕ → set α) (h_meas : ∀ n, measurable_set (sets n))
  (hμ : ∀ n, μ (sets n) < ∞) (h_disj : ∀ n m : ℕ, n ≠ m → μ (sets n ∩ sets m) = 0)
  (vals : ℕ → F),
  φ = ∑ n in t, (indicator_L1s (h_meas n) (1 : ℝ) (or.inr (hμ n))) ⊗ₜ (vals n) :=
begin
  obtain ⟨t, sets, h_meas, hμ, vals, h_eq⟩ := sum_indicators φ,
  refine sum_disjoint_indicators_of_sum_indicators φ t sets h_meas hμ vals h_eq,
end

lemma sum_disjoint_support_of_sum_disjoint_indicators (φ : (α →₁ₛ[μ] ℝ) ⊗[ℝ] F) (t : finset ℕ)
  (sets : ℕ → set α) (h_meas : ∀ n, measurable_set (sets n)) (hμ : ∀ n, μ (sets n) < ∞)
  (h_disj : ∀ n m : ℕ, n ≠ m → μ (sets n ∩ sets m) = 0)
  (vals : ℕ → F)
  (hφ : φ = ∑ n in t, (indicator_L1s (h_meas n) (1 : ℝ) (or.inr (hμ n))) ⊗ₜ (vals n)) :
  ∃ (t : finset F) (s : F → set α) (hs : ∀ y, measurable_set (s y)) (hsμ : ∀ y, μ (s y) < ∞)
    (hst : ∀ y z : F, y ≠ z → μ (s y ∩ s z) = 0),
  φ = ∑ y in t, (indicator_L1s (hs y) (1 : ℝ) (or.inr (hsμ y))) ⊗ₜ y :=
begin
  use t.image vals,
  let s := λ y, ⋃ n (hn : n ∈ t.filter (λ n, vals n = y)), sets n,
  refine ⟨s, _, _, _, _⟩,
  { exact λ y, measurable_set.bUnion (finset.countable_to_set _) (λ n hn, h_meas n), },
  { intro y,
    simp_rw s,
    refine (measure_bUnion_finset_le _ _).trans_lt _,
    rw sum_lt_top_iff,
    exact λ n hn, hμ n, },
  { intros y z hyz,
    simp_rw s,
    sorry, },
  { sorry, },
end

lemma sum_disjoint_pos_support (φ : (α →₁ₛ[μ] ℝ) ⊗[ℝ] F) :
  ∃ (t : finset F) (s : F → set α) (hs : ∀ y, measurable_set (s y))
    (hsμ_pos : ∀ y, y ∈ t → 0 < μ (s y)) (hsμ : ∀ y, μ (s y) < ∞)
    (hst : ∀ y z : F, y ≠ z → μ (s y ∩ s z) = 0),
  φ = ∑ y in t, (indicator_L1s (hs y) (1 : ℝ) (or.inr (hsμ y))) ⊗ₜ y :=
begin
  obtain ⟨t', s', hs', hsμ', hst', vals', h_eq'⟩ := sum_disjoint_indicators φ,
  obtain ⟨t, s, hs, hsμ, hst, h_eq⟩ :=
    sum_disjoint_support_of_sum_disjoint_indicators φ t' s' hs' hsμ' hst' vals' h_eq',
  refine ⟨(t.filter (λ y, 0 < μ (s y))), s, hs, (λ y hy, (finset.mem_filter.mp hy).2), hsμ, hst, _⟩,
  sorry,
end

lemma sum_disjoint_pos_support_eq_zero (t : finset F) (s : F → set α)
  (hs : ∀ y, measurable_set (s y)) (hsμ_pos : ∀ y ∈ t, 0 < μ (s y)) (hsμ : ∀ y, μ (s y) < ∞)
  (hst : ∀ y z : F, y ≠ z → μ (s y ∩ s z) = 0)
  (h_zero : ∑ y in t, (indicator_L1s (hs y) y (or.inr (hsμ y))) = 0) :
  ∀ y ∈ t, y = (0 : F) :=
begin
  rw ← range_nonzero_eq_empty_iff at h_zero,
  revert hsμ_pos,
  revert h_zero,
  refine finset.induction_on t _ _,
  { simp, },
  intros a u hau hu h_insert hy_pos y hyau,
  rw finset.mem_insert at hyau,
  rw [finset.sum_insert hau, add_comm, range_nonzero_add_of_null_support] at h_insert,
  swap,
  { intros y z hy hz,
    sorry, },
  rw finset.union_eq_empty_iff at h_insert,
  specialize hu h_insert.1,
  cases hyau,
  { by_cases hy0 : y = 0,
    { exact hy0, },
    { have hy : y ∈ insert a u, by {rw hyau, exact finset.mem_insert_self a u, },
      rw  [← hyau, range_nonzero_indicator_L1s_eq (hs y) y _ (hy_pos y hy) hy0] at h_insert,
      simpa using h_insert.2, }, },
  { have hu_pos : ∀ y, y ∈ u → 0 < μ (s y), from λ y hy, hy_pos y (finset.mem_insert_of_mem hy),
    exact hu hu_pos y hyau, },
end

lemma tensor_to_L1s_eq_zero_iff {φ : (α →₁ₛ[μ] ℝ) ⊗[ℝ] F} :
  tensor_to_L1s 𝕂 φ = 0 ↔ φ = 0 :=
begin
  refine ⟨λ h_zero, _, λ h_zero, by { rw h_zero, exact (tensor_to_L1s 𝕂).map_zero }⟩,
  obtain ⟨t, s, hs, hsμ_pos, hsμ, hst, h_eq⟩ := sum_disjoint_pos_support φ,
  suffices ht_zero : ∀ y ∈ t, y = (0 : F),
  { rw h_eq,
    refine finset.sum_eq_zero (λ y hy, _),
    simp [ht_zero y hy], },
  rw [h_eq, (tensor_to_L1s 𝕂).map_sum] at h_zero,
  simp_rw tensor_to_L1s_indicator at h_zero,
  exact sum_disjoint_pos_support_eq_zero t _ _ hsμ_pos _ hst h_zero,
end

lemma tensor_to_L1s_injective :
  function.injective ⇑(tensor_to_L1s 𝕂 : ((α →₁ₛ[μ] ℝ) ⊗[ℝ] F) →ₗ[𝕂] α →₁ₛ[μ] F) :=
begin
  intros f g hfg,
  rw ← sub_eq_zero at hfg ⊢,
  rw ← linear_map.map_sub at hfg,
  exact tensor_to_L1s_eq_zero_iff.mp hfg,
end

def tensor_to_L1s_equiv : ((α →₁ₛ[μ] ℝ) ⊗[ℝ] F) ≃ₗ[𝕂] α →₁ₛ[μ] F :=
{ to_fun := (tensor_to_L1s 𝕂).to_fun,
  map_add' := (tensor_to_L1s 𝕂).map_add',
  map_smul' := (tensor_to_L1s 𝕂).map_smul',
  inv_fun := function.inv_fun (tensor_to_L1s 𝕂).to_fun,
  left_inv := function.left_inverse_inv_fun tensor_to_L1s_injective,
  right_inv := function.right_inverse_inv_fun tensor_to_L1s_surjective, }

variables (F 𝕂)
def L1_extend_from_ℝ (T : (α →₁ₛ[μ] ℝ) →ₗ[ℝ] (α →₁[μ] ℝ)) : (α →₁ₛ[μ] F) →ₗ[𝕂] (α →₁[μ] F) :=
tensor_to_L1.comp ((linear_map.rtensor' _ _ T).comp tensor_to_L1s_equiv.symm.to_linear_map)
variables {F 𝕂}

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
