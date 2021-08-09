/-
Copyright (c) 2021 Alex Kontorovich and Heather Macbeth and Marc Masdeu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth, Marc Masdeu
-/
import analysis.complex.upper_half_plane

/-!
# The action of the modular group SL(2, ℤ) on the upper half-plane

-/

open complex matrix matrix.special_linear_group
noncomputable theory

local notation `|` x `|` := _root_.abs x
local notation `SL(` n `, ` R `)`:= special_linear_group (fin n) R

open_locale upper_half_plane

local attribute [instance] fintype.card_fin_even

namespace upper_half_plane

/-- The action of `SL(2, ℤ)` on the upper half-plane, as a restriction of the `SL(2, ℝ)`-action. -/
instance int_action : mul_action SL(2, ℤ) ℍ :=
mul_action.comp_hom ℍ (map (int.cast_ring_hom ℝ))

@[simp] lemma coe_smul_int (g : SL(2, ℤ)) (z : ℍ) : ↑(g • z) = top g z / bottom g z := rfl
@[simp] lemma re_smul_int (g : SL(2, ℤ)) (z : ℍ) : (g • z).re = (top g z / bottom g z).re := rfl
@[simp] lemma smul_coe (g : SL(2, ℤ)) (z : ℍ) : (g : SL(2,ℝ)) • z = g • z := rfl

@[simp] lemma neg_smul_int (g : SL(2, ℤ)) (z : ℍ) : -g • z = g • z :=
show ↑(-g) • _ = _, by simp [neg_smul g z]

lemma im_smul_int (g : SL(2, ℤ)) (z : ℍ) : (g • z).im = (top g z / bottom g z).im := rfl

lemma im_smul_int_eq_div_norm_sq (g : SL(2, ℤ)) (z : ℍ) :
  (g • z).im = z.im / (complex.norm_sq (bottom g z)) :=
im_smul_eq_div_norm_sq g z

end upper_half_plane

open upper_half_plane

/-! It is useful to develop basic theory for an object `coprime_ints`, consisting of two integers
and a proof that they satisfy `is_coprime`. -/

@[ext] structure coprime_ints :=
(c : ℤ)
(d : ℤ)
(is_coprime : is_coprime c d)

namespace coprime_ints

instance : has_coe coprime_ints (ℤ × ℤ) := ⟨λ p, (p.c, p.d)⟩

instance : nonempty coprime_ints := ⟨⟨1, 1, is_coprime_one_left⟩⟩

@[simp] lemma fst_coe (p : coprime_ints) : (p : ℤ × ℤ).1 = p.c := rfl
@[simp] lemma snd_coe (p : coprime_ints) : (p : ℤ × ℤ).2 = p.d := rfl

lemma coe_injective : function.injective (coe : coprime_ints → ℤ × ℤ) :=
λ p q hpq, ext p q (by simpa using congr_arg prod.fst hpq) (by simpa using congr_arg prod.snd hpq)

lemma ne_zero (p : coprime_ints) : p.c ≠ 0 ∨ p.d ≠ 0 :=
begin
  rw ← not_and_distrib,
  rintros ⟨c_eq_zero, d_eq_zero⟩,
  simpa [c_eq_zero, d_eq_zero] using p.is_coprime
end

lemma ne_zero' (p : coprime_ints) : ![(p.c:ℝ),p.d] ≠ 0 :=
begin
  intros h,
  have c_eq_zero : (p.c:ℝ )=0 := congr_arg (λ (v: fin 2 → ℝ ), v 0) h,
  have d_eq_zero : (p.d:ℝ )=0 := congr_arg (λ (v: fin 2 → ℝ ), v 1) h,
  norm_cast at c_eq_zero d_eq_zero,
  exact not_and_distrib.mpr (ne_zero p) ⟨c_eq_zero, d_eq_zero⟩,
end

lemma sum_sq_ne_zero (p : coprime_ints) : p.c ^ 2 + p.d ^ 2 ≠ 0 :=
begin
  intros h,
  have c_eq_zero : p.c = 0 := by nlinarith,
  have d_eq_zero : p.d = 0 := by nlinarith,
  cases p.ne_zero with hc hd; contradiction
end

end coprime_ints

@[simps] def bottom_row (g : SL(2, ℤ)) : coprime_ints :=
{ c := g 1 0,
  d := g 1 1,
  is_coprime := begin
    use [- g 0 1, g 0 0],
    have := det_fin_two g,
    have := g.det_coe,
    simp at *,
    linarith
  end }



lemma bottom_row_surj : function.surjective bottom_row :=
begin
  intros cd,
  obtain ⟨b₀, a, gcd_eqn⟩ := cd.is_coprime,
  let A := ![![a, -b₀], ![cd.c, cd.d]],
  have det_A_1 : det A = 1,
  { convert gcd_eqn,
    simp [A, matrix.det_succ_row_zero, fin.sum_univ_succ,
      (by ring : a * cd.d + b₀ * cd.c = b₀ * cd.c + a * cd.d)] },
  use ⟨A, det_A_1⟩,
  simp only [bottom_row, A, cons_apply_one, cons_val_one, cons_val_zero, head_cons],
  ext; refl,
end

lemma bottom_eq_of_bottom_row_eq {g h : SL(2,ℤ)} (z : ℍ) (bot_eq : bottom_row g = bottom_row h) :
  bottom g z = bottom h z :=
by simp [← bottom_row_c, ← bottom_row_d, bot_eq]


section tendsto_lemmas
/-! This is an attempt to do the maximin argument using more abstract existence theory. -/

open filter continuous_linear_map

lemma finite_pairs (z : ℍ) :
  filter.tendsto (λ p : coprime_ints, ((p.c : ℂ) * z + p.d).norm_sq)
  cofinite at_top :=
begin
  let f : ℝ × ℝ →ₗ[ℝ] ℂ := (linear_map.fst ℝ ℝ ℝ).smul_right (z:ℂ)
    + (linear_map.snd ℝ ℝ ℝ).smul_right 1,
  have hf : f.ker = ⊥,
  { let g : ℂ →ₗ[ℝ] ℝ × ℝ := im_lm.prod (im_lm.comp (((z:ℂ) • conj_ae ))),
    suffices : ((z:ℂ).im⁻¹ • g).comp f = linear_map.id,
    { exact linear_map.ker_eq_bot_of_inverse this },
    apply linear_map.ext,
    rintros ⟨c₁, c₂⟩,
    have hz : 0 < (z:ℂ).im := z.2,
    have : (z:ℂ).im ≠ 0 := hz.ne.symm,
    field_simp,
    ring },
  have h₁ := (linear_equiv.closed_embedding_of_injective hf).tendsto_cocompact,
  have h₂ : tendsto (λ p : ℤ × ℤ, ((p.1 : ℝ), (p.2 : ℝ))) cofinite (cocompact _),
  { convert int.tendsto_coe_cofinite.prod_map_coprod int.tendsto_coe_cofinite;
    simp [coprod_cocompact, coprod_cofinite] },
  convert tendsto_norm_sq_cocompact_at_top.comp
    (h₁.comp (h₂.comp coprime_ints.coe_injective.tendsto_cofinite)),
  ext,
  simp [f],
end


/- generalize to arbitrary matrix index sets and move to matrix file -/
def matrix.coord (i j : fin 2) : (matrix (fin 2) (fin 2) ℝ) →ₗ[ℝ] ℝ :=
(linear_map.proj j : (fin 2 → ℝ) →ₗ[ℝ] _).comp (linear_map.proj i)

def acbd (p : coprime_ints) : (matrix (fin 2) (fin 2) ℝ) →ₗ[ℝ] ℝ :=
p.c • matrix.coord 0 0 + p.d • matrix.coord 0 1

@[simp]lemma acbd_apply (p : coprime_ints) (g : matrix (fin 2) (fin 2) ℝ) :
  acbd p g = p.c * g 0 0 + p.d * g 0 1 :=
by simp [acbd, matrix.coord]


/-- Map sending the matrix [a b; c d] to `(ac₀+bd₀ , ad₀ - bc₀, c, d)`, for some fixed `(c₀, d₀)`.
-/
def line_map (cd : coprime_ints) : (matrix (fin 2) (fin 2) ℝ) →ₗ[ℝ] ((fin 2 → ℝ) × (fin 2 → ℝ)) :=
((matrix.mul_vec_lin ![![(cd.c:ℝ), cd.d], ![cd.d,-cd.c]]).comp
  (linear_map.proj 0 : (matrix (fin 2) (fin 2) ℝ) →ₗ[ℝ] _)).prod
  (linear_map.proj 1)

lemma lin_indep_acbd (cd : coprime_ints) : (line_map cd).ker = ⊥ :=
begin
  rw linear_map.ker_eq_bot,
  have nonZ : ((cd.c)^2+(cd.d)^2:ℝ) ≠ 0,
  { norm_cast,
    exact cd.sum_sq_ne_zero },
  let F : matrix (fin 2) (fin 2) ℝ := ((cd.c)^2+(cd.d)^2:ℝ)⁻¹ • ![![cd.c, cd.d], ![cd.d, -cd.c]],
  let f₁ : (fin 2 → ℝ) → (fin 2 → ℝ) := F.mul_vec_lin,
  let f : (fin 2 → ℝ) × (fin 2 → ℝ) → matrix (fin 2) (fin 2) ℝ := λ ⟨x , cd⟩, ![f₁ x, cd],
  have : function.left_inverse f (line_map cd),
  { intros g,
    simp [line_map, f, f₁, F, vec_head, vec_tail],
    ext i j,
    fin_cases i,
    { fin_cases j,
      { change (↑(cd.c) ^ 2 + ↑(cd.d) ^ 2)⁻¹ * ↑(cd.c) * (↑(cd.c) * g 0 0 + ↑(cd.d) * g 0 1) +
          (↑(cd.c) ^ 2 + ↑(cd.d) ^ 2)⁻¹ * ↑(cd.d) * (↑(cd.d) * g 0 0 + -(↑(cd.c) * g 0 1)) = _,
        field_simp,
        ring },
      { change (↑(cd.c) ^ 2 + ↑(cd.d) ^ 2)⁻¹ * ↑(cd.d) * (↑(cd.c) * g 0 0 + ↑(cd.d) * g 0 1) +
          -((↑(cd.c) ^ 2 + ↑(cd.d) ^ 2)⁻¹ * ↑(cd.c) * (↑(cd.d) * g 0 0 + -(↑(cd.c) * g 0 1))) = _,
        field_simp,
        ring } },
    { fin_cases j; refl } },
  exact this.injective,
end

/-- Big filter theorem -/
theorem big_thm (cd : coprime_ints) :
  tendsto (λ g : bottom_row ⁻¹' {cd}, acbd cd ↑(↑g : SL(2, ℝ))) cofinite (cocompact ℝ) :=
begin
  let mB : ℝ → ((fin 2 → ℝ) × (fin 2 → ℝ)) := λ t, (![t, 1], ![(cd.c:ℝ), cd.d]),
  have hmB : continuous mB,
  { refine continuous.prod_mk (continuous_pi _) continuous_const,
    intros i,
    fin_cases i,
    { exact continuous_id },
    { simpa using continuous_const } },
  convert filter.tendsto.of_tendsto_comp _ (comap_cocompact hmB),
  let f₁ : SL(2, ℤ) → matrix (fin 2) (fin 2) ℝ :=
    λ g, matrix.map (↑g : matrix _ _ ℤ) (coe : ℤ → ℝ),
  have cocompact_ℝ_to_cofinite_ℤ_matrix :
    tendsto (λ m : matrix (fin 2) (fin 2) ℤ, matrix.map m (coe : ℤ → ℝ)) cofinite (cocompact _),
  { convert tendsto.pi_map_Coprod (λ i, tendsto.pi_map_Coprod (λ j, int.tendsto_coe_cofinite)),
    { simp [Coprod_cofinite] },
    { simp only [Coprod_cocompact],
      refl } },
  have hf₁ : tendsto f₁ cofinite (cocompact _) :=
    cocompact_ℝ_to_cofinite_ℤ_matrix.comp subtype.coe_injective.tendsto_cofinite,
  have hf₂ := (linear_equiv.closed_embedding_of_injective (lin_indep_acbd cd)).tendsto_cocompact,
  convert hf₂.comp (hf₁.comp subtype.coe_injective.tendsto_cofinite) using 1,
  funext g,
  obtain ⟨g, hg⟩ := g,
  simp [mB, f₁, line_map, matrix.coord],
  simp [bottom_row] at hg,
  split,
  { ext i,
    fin_cases i,
    { simp only [add_left_inj, add_zero, eq_self_iff_true, fin.succ_zero_eq_one,
        function.comp_app, function.eval_apply, gsmul_eq_mul, int.cast_eq_zero, int.cast_inj,
        linear_map.add_apply, linear_map.coe_comp, linear_map.coe_proj, linear_map.smul_apply,
        matrix.cons_dot_product, matrix.cons_mul_vec, matrix.cons_val_zero,
        matrix.dot_product_empty, matrix.empty_mul_vec, matrix.map_apply, mul_eq_mul_left_iff,
        neg_mul_eq_neg_mul_symm, true_or, acbd, matrix.coord, matrix.vec_head,
        matrix.vec_tail] },
    { simp only [← hg, vec_head, vec_tail, add_zero, function.comp_app, gsmul_eq_mul,
        linear_map.add_apply, linear_map.smul_apply, matrix.cons_dot_product, matrix.cons_mul_vec,
        matrix.cons_val_fin_one, matrix.cons_val_one, matrix.dot_product_empty,
        matrix.empty_mul_vec, matrix.map_apply, acbd],
      norm_cast,
      convert g.det_coe.symm using 1,
      simp only [fin.coe_succ, fin.coe_zero, fin.default_eq_zero, fin.succ_succ_above_zero,
        fin.succ_zero_eq_one, fin.sum_univ_succ, fin.zero_succ_above, finset.sum_singleton,
        matrix.det_fin_zero, matrix.det_succ_row_zero, matrix.minor_apply, matrix.minor_empty,
        matrix.special_linear_group.coe_matrix_apply, mul_one, ne.def, neg_mul_eq_neg_mul_symm,
        one_mul, pow_one, pow_zero, univ_unique, zero_add],
      ring } },
  { rw ← hg,
    ext i,
    fin_cases i; refl }
end

lemma something2 (p : coprime_ints) (z : ℍ) (g : bottom_row ⁻¹' {p}) :
  ↑((g : SL(2, ℤ)) • z) = ((acbd p ↑(↑g : SL(2, ℝ))) : ℂ ) / (p.c ^ 2 + p.d ^ 2)
    + ((p.d:ℂ )* z - p.c) / ((p.c ^ 2 + p.d ^ 2) * (p.c * z + p.d)) :=
begin
  have nonZ1 : (p.c : ℂ) ^ 2 + (p.d) ^ 2 ≠ 0 := by exact_mod_cast p.sum_sq_ne_zero,
  have nonZ2 : (p.c : ℂ) * z + p.d ≠ 0 := by simpa using linear_ne_zero _ z p.ne_zero',
  let acbdpg := acbd p ((((g: SL(2,ℤ)) : SL(2,ℝ )) : matrix (fin 2) (fin 2) ℝ)),
  field_simp [nonZ1, nonZ2, bottom_ne_zero, -upper_half_plane.bottom],
  rw (_ : (p.d:ℂ)*z - p.c = ((p.d)*z - p.c)*(g 0 0 * g 1 1 - g 0 1 * g 1 0)),
  simp,
  rw (_ : p.c = g 1 0),
  rw (_ : p.d = g 1 1),
  simp only [coe_fn_coe_base],
  ring,
  { convert bottom_row_d g,
    have : p = bottom_row g := g.2.symm,
    exact this },
  { convert bottom_row_c g,
    have : p = bottom_row g := g.2.symm,
    exact this },
  { rw (_ : (g 0 0 : ℂ) * ↑(g 1 1) - ↑(g 0 1) * ↑(g 1 0) = 1),
    { ring },
    norm_cast,
    rw ← det_fin_two g,
    exact (g : SL(2, ℤ)).det_coe_fun },
end

/- final filter lemma, deduce from previous two results -/
lemma something' (z:ℍ) (p : coprime_ints) :
  tendsto (λ g : bottom_row ⁻¹' {p}, _root_.abs (((g : SL(2, ℤ)) • z).re)) cofinite at_top :=
begin
  suffices : tendsto (λ g : bottom_row ⁻¹' {p}, (((g : SL(2, ℤ)) • z).re)) cofinite (cocompact ℝ),
  { exact tendsto_norm_cocompact_at_top.comp this },
  have : ((p.c : ℝ) ^ 2 + p.d ^ 2)⁻¹ ≠ 0,
  { apply inv_ne_zero,
    exact_mod_cast p.sum_sq_ne_zero },
  let f := homeomorph.mul_right' _ this,
  let ff := homeomorph.add_right (((p.d:ℂ)* z - p.c) / ((p.c ^ 2 + p.d ^ 2) * (p.c * z + p.d))).re,
  convert ((f.trans ff).closed_embedding.tendsto_cocompact).comp (big_thm p),
  ext g,
  change ((g : SL(2, ℤ)) • z).re = (acbd p ↑(↑g : SL(2, ℝ))) / (p.c ^ 2 + p.d ^ 2)
  + (((p.d:ℂ )* z - p.c) / ((p.c ^ 2 + p.d ^ 2) * (p.c * z + p.d))).re,
  exact_mod_cast (congr_arg complex.re (something2 p z g))
end

end tendsto_lemmas

/- the upshot of all the filter stuff is the following two lemmas -/

lemma exists_g_with_max_Im (z : ℍ) :
  ∃ g : SL(2,ℤ), ∀ g' : SL(2,ℤ), (g' • z).im ≤ (g • z).im :=
begin
  obtain ⟨p, hp⟩ := (finite_pairs z).exists_forall_le,
  obtain ⟨g, hg⟩ := bottom_row_surj p,
  use g,
  intros g',
  rw [im_smul_int_eq_div_norm_sq, im_smul_int_eq_div_norm_sq, div_le_div_left],
  { simpa [← hg] using hp (bottom_row g') },
  { exact z.im_pos },
  { exact normsq_bottom_pos g' z },
  { exact normsq_bottom_pos g z },
end

lemma exists_g_with_given_cd_and_min_re (z:ℍ) (cd : coprime_ints) :
  ∃ g : SL(2,ℤ), bottom_row g = cd ∧ (∀ g' : SL(2,ℤ), bottom_row g = bottom_row g' →
  _root_.abs ((g • z).re) ≤ _root_.abs ((g' • z).re)) :=
begin
  haveI : nonempty (bottom_row ⁻¹' {cd}) := let ⟨x, hx⟩ := bottom_row_surj cd in ⟨⟨x, hx⟩⟩,
  obtain ⟨g, hg⟩  := filter.tendsto.exists_forall_le (something' z cd),
  refine ⟨g, g.2, _⟩,
  { intros g1 hg1,
    have : g1 ∈ (bottom_row ⁻¹' {cd}),
    { rw [set.mem_preimage, set.mem_singleton_iff],
      exact eq.trans hg1.symm (set.mem_singleton_iff.mp (set.mem_preimage.mp g.2)) },
    exact hg ⟨g1, this⟩ },
end


def T : SL(2,ℤ) := ⟨![![1, 1], ![0, 1]], by simp [matrix.det_fin_two]⟩

def T' : SL(2,ℤ) := ⟨![![1, -1], ![0, 1]], by simp [matrix.det_fin_two]⟩

def S : SL(2,ℤ) := ⟨![![0, -1], ![1, 0]], by simp [matrix.det_fin_two]⟩


def fundamental_domain : set ℍ :=
{z | 1 ≤ (complex.norm_sq z) ∧ |z.re| ≤ (1 : ℝ) / 2}

notation `𝒟` := fundamental_domain

lemma im_lt_im_S {z : ℍ} (h: norm_sq z < 1) : z.im < (S • z).im :=
begin
  have : z.im < z.im / norm_sq (z:ℂ),
  { have imz : 0 < z.im := im_pos z,
    apply (lt_div_iff z.norm_sq_pos).mpr,
    nlinarith },
  convert this,
  simp only [im_smul_int_eq_div_norm_sq],
  field_simp [normsq_bottom_ne_zero, norm_sq_ne_zero, S, bottom, map_cons, comp_cons,
    cons_apply_one, cons_apply_zero],
end

lemma fun_dom_lemma₁ (z : ℍ) : ∃ g : SL(2,ℤ), g • z ∈ 𝒟 :=
begin
  -- filtery stuff tells us that we maximize im,
  obtain ⟨g₀, hg₀⟩ := exists_g_with_max_Im z,
  -- then among those, minimize re
  obtain ⟨g, hg, hg'⟩ := exists_g_with_given_cd_and_min_re z (bottom_row g₀),
  use g,
  -- `g` has same max im property as `g₀`
  have hg₀' : ∀ (g' : SL(2,ℤ)), (g' • z).im ≤ (g • z).im,
  { have hg'' : (g • z).im = (g₀ • z).im,
    { rw [im_smul_int_eq_div_norm_sq, im_smul_int_eq_div_norm_sq,
        bottom_eq_of_bottom_row_eq _ hg] },
    simpa only [hg''] using hg₀ },
  split,
  { -- Claim: `|g•z| > 1`. If not, then `S•g•z` has larger imaginary part
    contrapose! hg₀',
    use S * g,
    rw mul_action.mul_smul,
    exact im_lt_im_S hg₀' },
  { -- Claim: `|Re(g•z)| < 1/2`; if not, then either `T` or `T'` decrease |Re|.
    rw abs_le,
    split,
    { contrapose! hg',
      refine ⟨T * g, _, _⟩,
      { -- `bottom_row (T * g) = bottom_row g`.  Prove by a big (slow) `simp`
        simp only [bottom_row, T, vec_head, vec_tail, special_linear_group.coe_mul, mul_apply',
        cons_apply_one, cons_val_fin_one, cons_dot_product, dot_product_empty, function.comp_app,
        fin.succ_zero_eq_one, zero_mul, one_mul, add_zero, zero_add, eq_self_iff_true, and_self] },
      rw mul_action.mul_smul,
      change (g • z).re < _ at hg',
      have : |(g • z).re + 1| < |(g • z).re| :=
        by cases abs_cases ((g • z).re + 1); cases abs_cases (g • z).re; linarith,
      convert this,
      -- `(T • g • z).re = (g • z).re + 1`.  Prove by a big (slow) `simp`
      simp only [T, add_left_inj, complex.add_re, complex.of_real_int_cast,
        complex.of_real_one,  complex.of_real_zero, complex.one_re, div_one, int.cast_one,
        int.cast_zero, int.coe_cast_ring_hom, matrix.cons_val',
        matrix.cons_val_fin_one, matrix.cons_val_one, matrix.cons_val_zero, matrix.head_cons,
        matrix.map_apply, matrix.special_linear_group.coe_fun_coe,
        matrix.special_linear_group.coe_matrix_apply, one_mul, subtype.coe_mk,
        upper_half_plane.bottom, upper_half_plane.coe_smul_int, upper_half_plane.re_smul_int,
        upper_half_plane.top, zero_add, zero_mul], },
    { contrapose! hg',
      refine ⟨T' * g, _, _⟩,
      { -- `bottom_row (T' * g) = bottom_row g`.  Prove by a big (slow) `simp`
        simp only [bottom_row, T', vec_head, vec_tail, special_linear_group.mul_apply, mul_apply',
        cons_apply_one, cons_val_fin_one, cons_dot_product, dot_product_empty, function.comp_app,
        fin.succ_zero_eq_one, zero_mul, one_mul, add_zero, zero_add, eq_self_iff_true, and_self] },
      rw mul_action.mul_smul,
      change _ < (g • z).re at hg',
      have : |(g • z).re - 1| < |(g • z).re| :=
        by cases abs_cases ((g • z).re - 1); cases abs_cases (g • z).re; linarith,
      convert this,
      -- `(T' • g • z).re = (g • z).re - 1`.  Prove by a big (slow) `simp`
      simp only [T', add_left_inj, complex.add_re, complex.neg_re, complex.of_real_int_cast,
        complex.of_real_neg, complex.of_real_one, complex.of_real_zero, complex.one_re, div_one,
        eq_self_iff_true, int.cast_neg, int.cast_one,
        int.cast_zero, int.coe_cast_ring_hom, matrix.cons_val',
        matrix.cons_val_fin_one, matrix.cons_val_one, matrix.cons_val_zero, matrix.head_cons,
        matrix.map_apply, matrix.special_linear_group.coe_fun_coe,
        matrix.special_linear_group.coe_matrix_apply, one_mul, sub_eq_add_neg, subtype.coe_mk,
        upper_half_plane.bottom, upper_half_plane.coe_smul_int, upper_half_plane.re_smul_int,
        upper_half_plane.top, zero_add, zero_mul] } }
end
