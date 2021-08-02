/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import group_theory.group_action
import group_theory.quotient_group
import group_theory.order_of_element
import data.zmod.basic
import data.fintype.card
import data.list.rotate
import ring_theory.multiplicity
import group_theory.group_action.sub_mul_action
import group_theory.group_action.subgroup

/-!
# Sylow theorems

The Sylow theorems are the following results for every finite group `G` and every prime number `p`.

* There exists a Sylow `p`-subgroup of `G`.
* All Sylow `p`-subgroups of `G` are conjugate to each other.
* Let `nₚ` be the number of Sylow `p`-subgroups of `G`, then `nₚ` divides the index of the Sylow
  `p`-subgroup, `nₚ ≡ 1 [MOD p]`, and `nₚ` is equal to the index of the normalizer of the Sylow
  `p`-subgroup in `G`.

In this file, currently only the first of these results is proven.

## Main statements

* `exists_prime_order_of_dvd_card`: For every prime `p` dividing the order of `G` there exists an
  element of order `p` in `G`. This is known as Cauchy`s theorem.
* `exists_subgroup_card_pow_prime`: A generalisation of the first of the Sylow theorems: For every
  prime power `pⁿ` dividing `G`, there exists a subgroup of `G` of order `pⁿ`.

## TODO

* Prove the second and third of the Sylow theorems.
* Sylow theorems for infinite groups
-/

open equiv fintype finset mul_action function
open equiv.perm subgroup list quotient_group
open_locale big_operators
universes u v w
variables {G : Type u} {α : Type v} {β : Type w} [group G]

local attribute [instance, priority 10] subtype.fintype set_fintype classical.prop_decidable

namespace mul_action
variables [mul_action G α]

lemma mem_fixed_points_iff_card_orbit_eq_one {a : α}
  [fintype (orbit G a)] : a ∈ fixed_points G α ↔ card (orbit G a) = 1 :=
begin
  rw [fintype.card_eq_one_iff, mem_fixed_points],
  split,
  { exact λ h, ⟨⟨a, mem_orbit_self _⟩, λ ⟨b, ⟨x, hx⟩⟩, subtype.eq $ by simp [h x, hx.symm]⟩ },
  { assume h x,
    rcases h with ⟨⟨z, hz⟩, hz₁⟩,
    exact calc x • a = z : subtype.mk.inj (hz₁ ⟨x • a, mem_orbit _ _⟩)
      ... = a : (subtype.mk.inj (hz₁ ⟨a, mem_orbit_self _⟩)).symm }
end

variable (α)
lemma card_modeq_card_fixed_points [fintype α] [fintype G] [fintype (fixed_points G α)]
  {p : ℕ} {n : ℕ} [hp : fact p.prime] (h : card G = p ^ n) :
  card α ≡ card (fixed_points G α) [MOD p] :=
calc card α = card (Σ y : quotient (orbit_rel G α), {x // quotient.mk' x = y}) :
  card_congr (sigma_preimage_equiv (@quotient.mk' _ (orbit_rel G α))).symm
... = ∑ a : quotient (orbit_rel G α), card {x // quotient.mk' x = a} : card_sigma _
... ≡ ∑ a : fixed_points G α, 1 [MOD p] :
begin
  rw [←zmod.eq_iff_modeq_nat p, nat.cast_sum, nat.cast_sum],
  refine eq.symm (sum_bij_ne_zero (λ a _ _, quotient.mk' a.1)
    (λ _ _ _, mem_univ _)
    (λ a₁ a₂ _ _ _ _ h,
      subtype.eq ((mem_fixed_points' α).1 a₂.2 a₁.1 (quotient.exact' h)))
      (λ b, _)
      (λ a ha _, by rw [← mem_fixed_points_iff_card_orbit_eq_one.1 a.2];
        simp only [quotient.eq']; congr)),
  { refine quotient.induction_on' b (λ b _ hb, _),
    have : card (orbit G b) ∣ p ^ n,
    { rw [← h, fintype.card_congr (orbit_equiv_quotient_stabilizer G b)],
      exact card_quotient_dvd_card _ },
    rcases (nat.dvd_prime_pow hp.1).1 this with ⟨k, _, hk⟩,
    have hb' :¬ p ^ 1 ∣ p ^ k,
    { rw [pow_one, ← hk, ← nat.modeq.modeq_zero_iff, ← zmod.eq_iff_modeq_nat,
        nat.cast_zero, ← ne.def],
      exact eq.mpr (by simp only [quotient.eq']; congr) hb },
    have : k = 0 := nat.le_zero_iff.1 (nat.le_of_lt_succ (lt_of_not_ge (mt (pow_dvd_pow p) hb'))),
    refine ⟨⟨b, mem_fixed_points_iff_card_orbit_eq_one.2 $ by rw [hk, this, pow_zero]⟩,
      mem_univ _, _, rfl⟩,
    rw [nat.cast_one], exact one_ne_zero }
end
... = _ : by simp; refl

/-- If a p-group acts on `α` and the cardinality of `α` is not a multiple
  of `p` then the action has a fixed point. -/
lemma nonempty_fixed_point_of_prime_not_dvd_card
  [fintype α] [fintype G] [fintype (fixed_points G α)]
  {p : ℕ} {n : ℕ} [hp : fact p.prime] (hG : card G = p ^ n)
  (hp : ¬ p ∣ fintype.card α) :
  (fixed_points G α).nonempty :=
@set.nonempty_of_nonempty_subtype _ _ begin
  rw [← fintype.card_pos_iff, pos_iff_ne_zero],
  assume h,
  have := card_modeq_card_fixed_points α hG,
  rw [h, nat.modeq.modeq_zero_iff] at this,
  contradiction
end

/-- If a p-group acts on `α` and the cardinality of `α` is a multiple
  of `p`, and the action has one fixed point, then it has another fixed point. -/
lemma exists_fixed_point_of_prime_dvd_card_of_fixed_point
  [fintype α] [fintype G] [fintype (fixed_points G α)]
  {p : ℕ} {n : ℕ} [hp : fact p.prime] (hG : card G = p ^ n)
  (hpα : p ∣ fintype.card α) {a : α} (ha : a ∈ fixed_points G α) :
  ∃ b, b ∈ fixed_points G α ∧ a ≠ b :=
have hpf : p ∣ fintype.card (fixed_points G α),
  from nat.modeq.modeq_zero_iff.1 $
    (card_modeq_card_fixed_points α hG).symm.trans
    (nat.modeq.modeq_zero_iff.2 hpα),
have hα : 1 < fintype.card (fixed_points G α),
  from lt_of_lt_of_le
    hp.out.one_lt
    (nat.le_of_dvd (fintype.card_pos_iff.2 ⟨⟨a, ha⟩⟩) hpf),
let ⟨⟨b, hb⟩, hba⟩ := exists_ne_of_one_lt_card hα ⟨a, ha⟩ in
⟨b, hb, λ hab, hba $ by simp [hab]⟩

end mul_action

lemma quotient_group.card_preimage_mk [fintype G] (s : subgroup G)
  (t : set (quotient s)) : fintype.card (quotient_group.mk ⁻¹' t) =
  fintype.card s * fintype.card t :=
by rw [← fintype.card_prod, fintype.card_congr
  (preimage_mk_equiv_subgroup_times_set _ _)]

namespace sylow

/-- Given a vector `v` of length `n`, make a vector of length `n+1` whose product is `1`,
by consing the the inverse of the product of `v`. -/
def mk_vector_prod_eq_one (n : ℕ) (v : vector G n) : vector G (n+1) :=
v.to_list.prod⁻¹ ::ᵥ v

lemma mk_vector_prod_eq_one_injective (n : ℕ) : injective (@mk_vector_prod_eq_one G _ n) :=
λ ⟨v, _⟩ ⟨w, _⟩ h, subtype.eq (show v = w, by injection h with h; injection h)

/-- The type of vectors with terms from `G`, length `n`, and product equal to `1:G`. -/
def vectors_prod_eq_one (G : Type*) [group G] (n : ℕ) : set (vector G n) :=
{v | v.to_list.prod = 1}

lemma mem_vectors_prod_eq_one {n : ℕ} (v : vector G n) :
  v ∈ vectors_prod_eq_one G n ↔ v.to_list.prod = 1 := iff.rfl

lemma mem_vectors_prod_eq_one_iff {n : ℕ} (v : vector G (n + 1)) :
  v ∈ vectors_prod_eq_one G (n + 1) ↔ v ∈ set.range (@mk_vector_prod_eq_one G _ n) :=
⟨λ (h : v.to_list.prod = 1), ⟨v.tail,
  begin
    unfold mk_vector_prod_eq_one,
    conv {to_rhs, rw ← vector.cons_head_tail v},
    suffices : (v.tail.to_list.prod)⁻¹ = v.head,
    { rw this },
    rw [← mul_left_inj v.tail.to_list.prod, inv_mul_self, ← list.prod_cons,
      ← vector.to_list_cons, vector.cons_head_tail, h]
  end⟩,
  λ ⟨w, hw⟩, by rw [mem_vectors_prod_eq_one, ← hw, mk_vector_prod_eq_one,
    vector.to_list_cons, list.prod_cons, inv_mul_self]⟩

/-- The rotation action of `zmod n` (viewed as multiplicative group) on
`vectors_prod_eq_one G n`, where `G` is a multiplicative group. -/
def rotate_vectors_prod_eq_one (G : Type*) [group G] (n : ℕ)
  (m : multiplicative (zmod n)) (v : vectors_prod_eq_one G n) : vectors_prod_eq_one G n :=
⟨⟨v.1.to_list.rotate m.val, by simp⟩, prod_rotate_eq_one_of_prod_eq_one v.2 _⟩

instance rotate_vectors_prod_eq_one.mul_action (n : ℕ) [fact (0 < n)] :
  mul_action (multiplicative (zmod n)) (vectors_prod_eq_one G n) :=
{ smul := (rotate_vectors_prod_eq_one G n),
  one_smul :=
  begin
    intro v, apply subtype.eq, apply vector.eq _ _,
    show rotate _ (0 : zmod n).val = _, rw zmod.val_zero,
    exact rotate_zero v.1.to_list
  end,
  mul_smul := λ a b ⟨⟨v, hv₁⟩, hv₂⟩, subtype.eq $ vector.eq _ _ $
    show v.rotate ((a + b : zmod n).val) = list.rotate (list.rotate v (b.val)) (a.val),
    by rw [zmod.val_add, rotate_rotate, ← rotate_mod _ (b.val + a.val), add_comm, hv₁] }

lemma one_mem_vectors_prod_eq_one (n : ℕ) : vector.repeat (1 : G) n ∈ vectors_prod_eq_one G n :=
by simp [vector.repeat, vectors_prod_eq_one]

lemma one_mem_fixed_points_rotate (n : ℕ) [fact (0 < n)] :
  (⟨vector.repeat (1 : G) n, one_mem_vectors_prod_eq_one n⟩ : vectors_prod_eq_one G n) ∈
  fixed_points (multiplicative (zmod n)) (vectors_prod_eq_one G n) :=
λ m, subtype.eq $ vector.eq _ _ $
rotate_eq_self_iff_eq_repeat.2 ⟨(1 : G),
  show list.repeat (1 : G) n = list.repeat 1 (list.repeat (1 : G) n).length, by simp⟩ _

/-- **Cauchy's theorem** -/
lemma exists_prime_order_of_dvd_card [fintype G] (p : ℕ) [hp : fact p.prime]
  (hdvd : p ∣ card G) : ∃ x : G, order_of x = p :=
have hcard : card (vectors_prod_eq_one G p) = card G ^ (p - 1),
  by conv_lhs { rw [← nat.sub_add_cancel hp.out.pos, set.ext mem_vectors_prod_eq_one_iff,
    set.card_range_of_injective (mk_vector_prod_eq_one_injective _), card_vector] },
have hzmod : fintype.card (multiplicative (zmod p)) = p ^ 1,
  by { rw pow_one p, exact zmod.card p },
have hdvdcard : p ∣ fintype.card (vectors_prod_eq_one G p) :=
  calc p ∣ card G ^ 1 : by rwa pow_one
  ... ∣ card G ^ (p - 1) : pow_dvd_pow _ (nat.le_sub_left_of_add_le hp.out.two_le)
  ... = card (vectors_prod_eq_one G p) : hcard.symm,
let ⟨⟨⟨x, hxl⟩, hx1⟩, hx, h1x⟩ := mul_action.exists_fixed_point_of_prime_dvd_card_of_fixed_point
  (vectors_prod_eq_one G p) hzmod hdvdcard
  (one_mem_fixed_points_rotate _) in
have ∃ a, x = list.repeat a x.length := by exactI rotate_eq_self_iff_eq_repeat.1 (λ n,
  have list.rotate x (n : zmod p).val = x :=
    subtype.mk.inj (subtype.mk.inj (hx (n : zmod p))),
  by rwa [zmod.val_nat_cast, ← hxl, rotate_mod] at this),
let ⟨a, ha⟩ := this in
⟨a, have hxp1 : x.prod = 1 := hx1,
  have ha1: a ≠ 1,
    from λ h, h1x (subtype.ext $ subtype.ext $
      by rw [subtype.coe_mk, subtype.coe_mk, subtype.coe_mk, ha, hxl, h,
        vector.repeat, subtype.coe_mk]),
  have a ^ p = 1, by rwa [ha, list.prod_repeat, hxl] at hxp1,
  (hp.1.2 _ (order_of_dvd_of_pow_eq_one this)).resolve_left
    (λ h, ha1 (order_of_eq_one_iff.1 h))⟩

open subgroup submonoid mul_action

lemma mem_fixed_points_mul_left_cosets_iff_mem_normalizer {H : subgroup G}
  [fintype ((H : set G) : Type u)] {x : G} :
  (x : quotient H) ∈ fixed_points H (quotient H) ↔ x ∈ normalizer H :=
⟨λ hx, have ha : ∀ {y : quotient H}, y ∈ orbit H (x : quotient H) → y = x,
  from λ _, ((mem_fixed_points' _).1 hx _),
  (inv_mem_iff _).1 (@mem_normalizer_fintype _ _ _ _inst_2 _ (λ n (hn : n ∈ H),
    have (n⁻¹ * x)⁻¹ * x ∈ H := quotient_group.eq.1 (ha (mem_orbit _ ⟨n⁻¹, H.inv_mem hn⟩)),
    show _ ∈ H, by {rw [mul_inv_rev, inv_inv] at this, convert this, rw inv_inv}
    )),
λ (hx : ∀ (n : G), n ∈ H ↔ x * n * x⁻¹ ∈ H),
(mem_fixed_points' _).2 $ λ y, quotient.induction_on' y $ λ y hy, quotient_group.eq.2
  (let ⟨⟨b, hb₁⟩, hb₂⟩ := hy in
  have hb₂ : (b * x)⁻¹ * y ∈ H := quotient_group.eq.1 hb₂,
  (inv_mem_iff H).1 $ (hx _).2 $ (mul_mem_cancel_left H (H.inv_mem hb₁)).1
  $ by rw hx at hb₂;
    simpa [mul_inv_rev, mul_assoc] using hb₂)⟩

def fixed_points_mul_left_cosets_equiv_quotient (H : subgroup G) [fintype (H : set G)] :
  mul_action.fixed_points H (quotient H) ≃
  quotient (subgroup.comap ((normalizer H).subtype : normalizer H →* G) H) :=
@subtype_quotient_equiv_quotient_subtype G (normalizer H : set G) (id _) (id _) (fixed_points _ _)
  (λ a, (@mem_fixed_points_mul_left_cosets_iff_mem_normalizer _ _ _ _inst_2 _).symm)
  (by intros; refl)

/-- If `H` is a `p`-subgroup of `G`, then the index of `H` inside its normalizer is congruent
  mod `p` to the index of `H`.  -/
lemma card_quotient_normalizer_modeq_card_quotient [fintype G] {p : ℕ} {n : ℕ} [hp : fact p.prime]
  {H : subgroup G} (hH : fintype.card H = p ^ n) :
  card (quotient (subgroup.comap ((normalizer H).subtype : normalizer H →* G) H))
  ≡ card (quotient H) [MOD p] :=
begin
  rw [← fintype.card_congr (fixed_points_mul_left_cosets_equiv_quotient H)],
  exact (card_modeq_card_fixed_points _ hH).symm
end

/-- If `H` is a subgroup of `G` of cardinality `p ^ n`, then the cardinality of the
  normalizer of `H` is congruent mod `p ^ (n + 1)` to the cardinality of `G`.  -/
lemma card_normalizer_modeq_card [fintype G] {p : ℕ} {n : ℕ} [hp : fact p.prime]
  {H : subgroup G} (hH : fintype.card H = p ^ n) :
  card (normalizer H) ≡ card G [MOD p ^ (n + 1)] :=
have subgroup.comap ((normalizer H).subtype : normalizer H →* G) H ≃ H,
  from set.bij_on.equiv (normalizer H).subtype
    ⟨λ _, id, λ _ _ _ _ h, subtype.val_injective h,
      λ x hx, ⟨⟨x, le_normalizer hx⟩, hx, rfl⟩⟩,
begin
  rw [card_eq_card_quotient_mul_card_subgroup H,
      card_eq_card_quotient_mul_card_subgroup
        (subgroup.comap ((normalizer H).subtype : normalizer H →* G) H),
      fintype.card_congr this, hH, pow_succ],
  exact nat.modeq.modeq_mul_right' _ (card_quotient_normalizer_modeq_card_quotient hH)
end

/-- If `H` is a `p`-subgroup but not a Sylow `p`-subgroup, then `p` divides the
  index of `H` inside its normalizer. -/
lemma prime_dvd_card_quotient_normalizer [fintype G] {p : ℕ} {n : ℕ} [hp : fact p.prime]
  (hdvd : p ^ (n + 1) ∣ card G) {H : subgroup G} (hH : fintype.card H = p ^ n) :
  p ∣ card (quotient (subgroup.comap ((normalizer H).subtype : normalizer H →* G) H)) :=
let ⟨s, hs⟩ := exists_eq_mul_left_of_dvd hdvd in
have hcard : card (quotient H) = s * p :=
  (nat.mul_left_inj (show card H > 0, from fintype.card_pos_iff.2
      ⟨⟨1, H.one_mem⟩⟩)).1
    (by rwa [← card_eq_card_quotient_mul_card_subgroup H, hH, hs,
      pow_succ', mul_assoc, mul_comm p]),
have hm : s * p % p =
  card (quotient (subgroup.comap ((normalizer H).subtype : normalizer H →* G) H)) % p :=
  hcard ▸ (card_quotient_normalizer_modeq_card_quotient hH).symm,
nat.dvd_of_mod_eq_zero
  (by rwa [nat.mod_eq_zero_of_dvd (dvd_mul_left _ _), eq_comm] at hm)

/-- If `H` is a `p`-subgroup but not a Sylow `p`-subgroup of cardinality `p ^ n`,
  then `p ^ (n + 1)` divides the cardinality of the normalizer of `H`. -/
lemma prime_pow_dvd_card_normalizer [fintype G] {p : ℕ} {n : ℕ} [hp : fact p.prime]
  (hdvd : p ^ (n + 1) ∣ card G) {H : subgroup G} (hH : fintype.card H = p ^ n) :
  p ^ (n + 1) ∣ card (normalizer H) :=
nat.modeq.modeq_zero_iff.1 ((card_normalizer_modeq_card hH).trans
  (nat.modeq.modeq_zero_iff.2 hdvd))

/-- If `H` is a subgroup of `G` of cardinality `p ^ n`,
  then `H` is contained in a subgroup of cardinality `p ^ (n + 1)`
  if `p ^ (n + 1)` divides the cardinality of `G` -/
theorem exists_subgroup_card_pow_succ [fintype G] {p : ℕ} {n : ℕ} [hp : fact p.prime]
  (hdvd : p ^ (n + 1) ∣ card G) {H : subgroup G} (hH : fintype.card H = p ^ n) :
  ∃ K : subgroup G, fintype.card K = p ^ (n + 1) ∧ H ≤ K :=
let ⟨s, hs⟩ := exists_eq_mul_left_of_dvd hdvd in
have hcard : card (quotient H) = s * p :=
  (nat.mul_left_inj (show card H > 0, from fintype.card_pos_iff.2
      ⟨⟨1, H.one_mem⟩⟩)).1
    (by rwa [← card_eq_card_quotient_mul_card_subgroup H, hH, hs,
      pow_succ', mul_assoc, mul_comm p]),
have hm : s * p % p =
  card (quotient (subgroup.comap ((normalizer H).subtype : normalizer H →* G) H)) % p :=
  card_congr (fixed_points_mul_left_cosets_equiv_quotient H) ▸ hcard ▸
    @card_modeq_card_fixed_points _ _ _ _ _ _ _ p _ hp hH,
have hm' : p ∣ card (quotient (subgroup.comap ((normalizer H).subtype : normalizer H →* G) H)) :=
  nat.dvd_of_mod_eq_zero
    (by rwa [nat.mod_eq_zero_of_dvd (dvd_mul_left _ _), eq_comm] at hm),
let ⟨x, hx⟩ := @exists_prime_order_of_dvd_card _ (quotient_group.quotient.group _) _ _ hp hm' in
have hequiv : H ≃ (subgroup.comap ((normalizer H).subtype : normalizer H →* G) H) :=
  ⟨λ a, ⟨⟨a.1, le_normalizer a.2⟩, a.2⟩, λ a, ⟨a.1.1, a.2⟩,
    λ ⟨_, _⟩, rfl, λ ⟨⟨_, _⟩, _⟩, rfl⟩,
⟨subgroup.map ((normalizer H).subtype) (subgroup.comap
  (quotient_group.mk' (comap H.normalizer.subtype H)) (gpowers x)),
begin
  show card ↥(map H.normalizer.subtype
    (comap (mk' (comap H.normalizer.subtype H)) (subgroup.gpowers x))) = p ^ (n + 1),
  suffices : card ↥(subtype.val '' ((subgroup.comap (mk' (comap H.normalizer.subtype H))
    (gpowers x)) : set (↥(H.normalizer)))) = p^(n+1),
  { convert this using 2 },
  rw [set.card_image_of_injective
        (subgroup.comap (mk' (comap H.normalizer.subtype H)) (gpowers x) : set (H.normalizer))
        subtype.val_injective,
      pow_succ', ← hH, fintype.card_congr hequiv, ← hx, order_eq_card_gpowers,
      ← fintype.card_prod],
  exact @fintype.card_congr _ _ (id _) (id _) (preimage_mk_equiv_subgroup_times_set _ _)
end,
begin
  assume y hy,
  simp only [exists_prop, subgroup.coe_subtype, mk'_apply, subgroup.mem_map, subgroup.mem_comap],
  refine ⟨⟨y, le_normalizer hy⟩, ⟨0, _⟩, rfl⟩,
  rw [gpow_zero, eq_comm, quotient_group.eq_one_iff],
  simpa using hy
end⟩

/-- If `H` is a subgroup of `G` of cardinality `p ^ n`,
  then `H` is contained in a subgroup of cardinality `p ^ m`
  if `n ≤ m` and `p ^ m` divides the cardinality of `G` -/
theorem exists_subgroup_card_pow_prime_le [fintype G] (p : ℕ) : ∀ {n m : ℕ} [hp : fact p.prime]
  (hdvd : p ^ m ∣ card G) (H : subgroup G) (hH : card H = p ^ n) (hnm : n ≤ m),
  ∃ K : subgroup G, card K = p ^ m ∧ H ≤ K
| n m := λ hp hdvd H hH hnm,
  (lt_or_eq_of_le hnm).elim
    (λ hnm : n < m,
      have h0m : 0 < m, from (lt_of_le_of_lt n.zero_le hnm),
      have wf : m - 1 < m,  from nat.sub_lt h0m zero_lt_one,
      have hnm1 : n ≤ m - 1, from nat.le_sub_right_of_add_le hnm,
      let ⟨K, hK⟩ := @exists_subgroup_card_pow_prime_le n (m - 1) hp
        (nat.pow_dvd_of_le_of_pow_dvd (nat.sub_le_self _ _) hdvd) H hH hnm1 in
      have hdvd' : p ^ ((m - 1) + 1) ∣ card G, by rwa [nat.sub_add_cancel h0m],
      let ⟨K', hK'⟩ := @exists_subgroup_card_pow_succ _ _ _ _ _ hp hdvd' K hK.1 in
      ⟨K', by rw [hK'.1, nat.sub_add_cancel h0m], le_trans hK.2 hK'.2⟩)
    (λ hnm : n = m, ⟨H, by simp [hH, hnm]⟩)

/-- A generalisation of **Sylow's first theorem**. If `p ^ n` divides
  the cardinality of `G`, then there is a subgroup of cardinality `p ^ n` -/
theorem exists_subgroup_card_pow_prime [fintype G] (p : ℕ) {n : ℕ} [fact p.prime]
  (hdvd : p ^ n ∣ card G) : ∃ K : subgroup G, fintype.card K = p ^ n :=
let ⟨K, hK⟩ := exists_subgroup_card_pow_prime_le p hdvd ⊥ (by convert card_bot) n.zero_le in
⟨K, hK.1⟩

end sylow

variables {G} [fintype G] (p : ℕ)

def subgroup.is_sylow (P : subgroup G) : Prop :=
∃ n : ℕ, fintype.card P = p ^ n ∧ ∀ m, p ^ m ∣ fintype.card G → m ≤ n

variable {p}

lemma is_sylow_def {P : subgroup G} :
  P.is_sylow p ↔ ∃ n : ℕ, fintype.card P = p ^ n ∧ ∀ m, p ^ m ∣ fintype.card G → m ≤ n := iff.rfl

lemma _root_.nat.prime.pow_dvd_of_dvd_mul_right {p : ℕ} (hp : p.prime) {n a b : ℕ} (h : p ^ n ∣ a * b)
  (hpb : ¬ p ∣ b) : p ^ n ∣ a :=
begin
  induction n with n ih,
  { simp },
  { rw [pow_succ'] at *,
    rcases ih (dvd_trans (dvd_mul_right _ _) h) with ⟨c, rfl⟩,
    rw [mul_assoc] at h,
    rcases hp.dvd_mul.1 (nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos _) h)
      with ⟨d, rfl⟩|⟨d, rfl⟩,
    { rw [← mul_assoc],
      exact dvd_mul_right _ _ },
    { exact (hpb (dvd_mul_right _ _)).elim } }
end

lemma _root_.nat.prime.pow_dvd_of_dvd_mul_left {p : ℕ} (hp : p.prime) {n a b : ℕ} (h : p ^ n ∣ a * b)
  (hpb : ¬ p ∣ a) : p ^ n ∣ b :=
by rw [mul_comm] at h; exact hp.pow_dvd_of_dvd_mul_right h hpb

lemma subgroup.is_sylow_iff_not_dvd_card_quotient [fact p.prime] {P : subgroup G} :
  P.is_sylow p ↔ ¬ p ∣ fintype.card (quotient P) ∧ ∃ n : ℕ, card P = p ^ n :=
begin
  split,
  { intro hP,
    rcases hP with ⟨n, hnp, hd⟩,
    refine ⟨_, n, hnp⟩,
    rintros ⟨x, hx⟩,
    rw [card_eq_card_quotient_mul_card_subgroup (P : subgroup G), hx, hnp, mul_right_comm,
      ← pow_succ] at hd,
    exact not_le_of_gt n.lt_succ_self (hd _ (dvd_mul_right _ _)) },
  { rintros ⟨hdvd, n, hn⟩,
    use [n, hn],
    assume m hm,
    rw [card_eq_card_quotient_mul_card_subgroup (P : subgroup G), hn] at hm,
    exact (nat.pow_dvd_pow_iff_le_right (fact.out p.prime).one_lt).1
      ((fact.out p.prime).pow_dvd_of_dvd_mul_left hm hdvd) }
end

variables (G) (p)

/-- The type of Sylow-`p` subgroups of a finite group `G`. A Sylow `p` subgroup is a
  subgroup of cardinality `p ^ n`, when `n` is the maximum natural number such that
  `p ^ n` divides the cardinality of `G`. -/
def sylow_subgroup : Type* :=
{ P : subgroup G // P.is_sylow p }

namespace sylow_subgroup

instance : has_coe (sylow_subgroup G p) (subgroup G) :=
{ coe := subtype.val }

instance : mul_action G (sylow_subgroup G p) :=
{ smul := λ g P, ⟨g • (P : subgroup G),
    by simpa [subgroup.is_sylow, card_smul, set.mem_set_of_eq] using P.2⟩,
  one_smul := λ _, subtype.eq (one_smul _ _),
  mul_smul := λ x y P, subtype.eq (mul_smul _ _ P.val)  }

noncomputable instance : fintype (sylow_subgroup G p) :=
subtype.fintype _

variables {G} {p}

instance [hp : fact p.prime] : nonempty (sylow_subgroup G p) :=
have hm : multiplicity.finite p (fintype.card G),
  by simp only [multiplicity.finite_nat_iff, ne.def, hp.elim.ne_one,
    fintype.card_pos_iff, not_false_iff, true_and];
    exact ⟨1⟩,
let ⟨H, hH⟩ := sylow.exists_subgroup_card_pow_prime p
  (multiplicity.pow_multiplicity_dvd hm) in
⟨⟨H, ⟨_, hH, λ m hm, by rw [← enat.coe_le_coe, enat.coe_get];
    exact multiplicity.le_multiplicity_of_pow_dvd hm⟩⟩⟩

open quotient_group

variable {p}

@[simp] lemma coe_smul (x : G) (P : sylow_subgroup G p) :
  (↑(x • P) : subgroup G) = x • P := rfl

lemma coe_inj {P Q : sylow_subgroup G p} :
  (P : subgroup G) = Q ↔ P = Q :=
by cases P; cases Q; simp

variables (G) (p)
/-- `exponent G p` is the `n` such that `fintype.card P = p ^ n` when `P`
  is a sylow subgroup -/
def exponent [hp : fact p.prime] : ℕ :=
have hm : multiplicity.finite p (fintype.card G),
  by simp only [multiplicity.finite_nat_iff, ne.def, hp.elim.ne_one,
    fintype.card_pos_iff, not_false_iff, true_and];
    exact ⟨1⟩,
(multiplicity p (fintype.card G)).get hm

variables {G} {p}

lemma card_eq_pow_exponent [hp : fact p.prime] (P : sylow_subgroup G p) :
  fintype.card (P : subgroup G) = p ^ exponent G p :=
begin
  rcases P.property with ⟨n, hnp, hd⟩,
  erw [exponent, hnp],
  refine congr_arg _ _,
  rw [← enat.coe_inj, enat.coe_get, eq_comm, multiplicity.eq_some_iff, ← hnp],
  exact ⟨card_subgroup_dvd_card _, λ h, not_le_of_gt n.lt_succ_self (hd (n + 1) h)⟩
end

lemma le_exponent_of_dvd_pow [fact p.prime] {n : ℕ} (h : p ^ n ∣ card G) : n ≤ exponent G p :=
begin
  delta exponent,
  rw [← enat.coe_le_coe, enat.coe_get],
  exact multiplicity.le_multiplicity_of_pow_dvd h
end

lemma is_sylow_iff_card_eq_pow_exponent [fact p.prime] {P : subgroup G} :
  P.is_sylow p ↔ card P = p ^ exponent G p :=
⟨λ h, card_eq_pow_exponent ⟨_, h⟩,
  λ h, ⟨exponent G p, h, λ m, le_exponent_of_dvd_pow⟩⟩

lemma not_dvd_card_quotient_sylow [fact p.prime] (P : sylow_subgroup G p) :
  ¬ p ∣ fintype.card (quotient (P : subgroup G)) :=
(subgroup.is_sylow_iff_not_dvd_card_quotient.1 P.2).1

lemma eq_exponent_of_dvd_card_of_succ_not_dvd_card [fact p.prime] {n : ℕ}
  (h : p ^ n ∣ card G) (h2 : ¬p ^ (n + 1) ∣ card G) : n = exponent G p :=
le_antisymm (le_exponent_of_dvd_pow h)
  begin
    delta exponent,
    rw [← nat.lt_succ_iff, ← enat.coe_lt_coe, enat.coe_get],
    exact multiplicity.multiplicity_lt_iff_neg_dvd.2 h2
  end

lemma card_eq [fact p.prime] (P Q : sylow_subgroup G p) :
  fintype.card (P : subgroup G) = fintype.card (Q : subgroup G) :=
by simp [card_eq_pow_exponent]

/-- Two Sylow subgroups are equal if one is contained in the other -/
@[ext] protected lemma ext [fact p.prime] {P Q : sylow_subgroup G p}
  (h : (P : subgroup G) ≤ Q) : P = Q :=
begin
  have : (P : subgroup G).carrier = (Q : subgroup G).carrier :=
    set.eq_of_subset_of_card_le h (le_of_eq (card_eq _ _)),
  ext,
  simp [set.ext_iff, *] at *
end

/-- Two Sylow subgroups are equal iff one is contained in the other -/
protected lemma ext_iff {P Q : sylow_subgroup G p} :
  P = Q ↔ ∀ x, x ∈ (P : subgroup G) ↔ x ∈ (Q : subgroup G) :=
⟨λ h _, h ▸ iff.rfl, coe_inj.1 ∘ subgroup.ext⟩

lemma mem_smul {g h : G} {P : sylow_subgroup G p} :
  h ∈ (g • P : subgroup G) ↔ g⁻¹ * h * g ∈ (P : subgroup G) :=
mem_smul g h P

lemma stabilizer_eq_normalizer (P : sylow_subgroup G p) : stabilizer G P = normalizer P :=
begin
  rw [← stabilizer_eq_normalizer],
  ext,
  rw [mem_stabilizer_iff, mem_stabilizer_iff, ← coe_inj],
  simp
end

@[simp] lemma smul_self (P : sylow_subgroup G p) (x : P) : x • P = P :=
subtype.eq $ smul_self x

variable [fact p.prime]

section comap
variables {H : Type*} [group H] [fintype H] (h : H) (P Q : sylow_subgroup G p) (f : H →* G)

@[simps] def comap (hfi : injective f) (hf : (P : subgroup G) ≤ f.range) : sylow_subgroup H p :=
⟨(P : subgroup G).comap f, subgroup.is_sylow_iff_not_dvd_card_quotient.2 $
  have hcard : card (P : set G) = card (comap f P : set H),
    from fintype.card_congr (@set.bij_on.equiv _ _ (comap f P : set H) (P : set G) f
      ⟨λ _, id, λ _ _ _ _ h, hfi h, λ x hx, let ⟨y, hy⟩ := hf hx in
        ⟨y, mem_comap.2 (hy.symm ▸ hx), hy⟩⟩).symm,
  begin
    erw [← hcard],
    refine ⟨_, exponent G p, card_eq_pow_exponent _⟩,
    assume h,
    refine not_dvd_card_quotient_sylow P (dvd_trans h _),
    refine nat.dvd_of_mul_dvd_mul_right (show 0 < card (comap f P), from card_pos_iff.2 ⟨1⟩) _,
    erw [← card_eq_card_quotient_mul_card_subgroup, ← hcard,
      ← card_eq_card_quotient_mul_card_subgroup],
    exact card_dvd_of_injective f hfi
  end⟩

variables {P Q}
@[simp] lemma comap_inj_iff {hfi : injective f} {hP : (P : subgroup G) ≤ f.range}
  {hQ : (Q : subgroup G) ≤ f.range} : comap P f hfi hP = comap Q f hfi hQ ↔ P = Q :=
⟨λ h, sylow_subgroup.ext $ λ x hxP, begin
  simp only [← coe_inj, comap, subtype.coe_mk] at h,
  rcases hP hxP with ⟨y, rfl⟩,
  rwa [← mem_comap, ← h, mem_comap]
end, λ h, by simp [h]⟩

-- Why is this noncomputable
noncomputable def restrict {H : subgroup G} (hHP : ↑P ≤ H) : sylow_subgroup H p :=
comap P H.subtype subtype.val_injective (λ x hx, ⟨⟨_, hHP hx⟩, rfl⟩)

@[simp] lemma restrict_inj_iff {H : subgroup G} {hHP : ↑P ≤ H} {hHQ : ↑Q ≤ H} :
  restrict hHP = restrict hHQ ↔ P = Q :=
comap_inj_iff _

@[simp] lemma restrict_smul {H : subgroup G} (h : H) {hHP : ↑(h • P) ≤ H} :
  restrict hHP = h • restrict (show ↑P ≤ H,
    by erw [smul_le_iff_le_smul, subgroup.smul_self (h⁻¹)] at hHP; assumption) :=
coe_inj.1 $ comap_smul _ _ _

@[simp] lemma smul_restrict {H : subgroup G} (h : H) {hHP : ↑P ≤ H} :
  h • restrict hHP = restrict (show ↑(h • P) ≤ H,
    by erw [smul_le_iff_le_smul, subgroup.smul_self (h⁻¹)]; assumption):=
coe_inj.1 $ (comap_smul _ _ _).symm

end comap

/-- **Sylow's second theorem**. Any two Sylow subgroups are conjugate -/
lemma conjugate (P Q : sylow_subgroup G p) : ∃ g : G, g • P = Q :=
begin
  rcases mul_action.nonempty_fixed_point_of_prime_not_dvd_card (quotient (Q : subgroup G))
    (card_eq_pow_exponent P) (not_dvd_card_quotient_sylow Q) with ⟨g, hg⟩,
  induction g using quotient_group.induction_on,
  use g⁻¹,
  rw [mul_action.mem_fixed_points] at hg,
  rw [← smul_left_cancel_iff g, smul_inv_smul],
  ext,
  assume x hx,
  erw [mem_smul],
  simpa [mul_assoc] using inv_mem _ (quotient_group.eq.1 (hg ⟨x, hx⟩))
end

lemma conjugate_in_subgroup {P Q : sylow_subgroup G p} {H : subgroup G}
  (hPH : ↑P ≤ H) (hQH : ↑Q ≤ H) : ∃ g ∈ H, g • P = Q :=
begin
  cases conjugate (restrict hPH) (restrict hQH) with g hg,
  rw [smul_restrict, restrict_inj_iff] at hg,
  use [g, g.2, hg]
end

@[simp] lemma orbit_eq_univ (P : sylow_subgroup G p) : orbit G P = set.univ :=
set.eq_univ_of_forall (λ Q, mem_orbit_iff.2 (conjugate _ _))

open fintype

noncomputable def equiv_sylow_prod_normalizer (P : sylow_subgroup G p) :
  G ≃ sylow_subgroup G p × normalizer (P : subgroup G) :=
calc G ≃ quotient (normalizer (P : subgroup G)) × normalizer (P : subgroup G) :
  group_equiv_quotient_times_subgroup
... ≃ _ : prod_congr
  (calc quotient (normalizer (P : subgroup G)) ≃ quotient (stabilizer G P) :
      by rw [stabilizer_eq_normalizer]
    ... ≃ orbit G P : (orbit_equiv_quotient_stabilizer _ _).symm
    ... ≃ set.univ : by rw [orbit_eq_univ]
    ... ≃ sylow_subgroup G p : (equiv.set.univ _))
(equiv.refl _)

lemma card_eq_card_sylow_mul_card_normalizer (P : sylow_subgroup G p) :
  card G = card (sylow_subgroup G p) * card (normalizer (P : subgroup G)) :=
by rw [fintype.card_congr (equiv_sylow_prod_normalizer P)]; simp

/-- Part of **Sylow's third theorem**. The number of Sylow subgroups divides the cardinality
of the group. -/
lemma card_sylow_dvd_card : card (sylow_subgroup G p) ∣ card G :=
by rw [card_eq_card_sylow_mul_card_normalizer (classical.arbitrary (sylow_subgroup G p))];
  exact dvd_mul_right _ _

/-- Part of **Sylow's third theorem**.
The number of Sylow subgroups is the same as the index of the normalizer of any
Sylow subgroup -/
lemma card_sylow_eq_card_quotient (P : sylow_subgroup G p) :
  card (sylow_subgroup G p) = card (quotient (normalizer (P : subgroup G))) :=
(nat.mul_left_inj (show 0 < card (normalizer (P : subgroup G)), from card_pos_iff.2 ⟨1⟩)).1 $
  by rw [← card_eq_card_sylow_mul_card_normalizer, card_eq_card_quotient_mul_card_subgroup]

/-- Part of **Sylow's third theorem**. If `P` is a Sylow subgroup, then the number of Sylow
subgroups times the index of `P` in its normalizer is the index of `P` -/
lemma card_sylow_mul_card_quotient_in_normalizer_eq_card_quotient (P : sylow_subgroup G p) :
  card (sylow_subgroup G p) *
  card (quotient (subgroup.comap ((normalizer ↑P).subtype : normalizer ↑P →* G) P))
     = card (quotient (P : subgroup G)) :=
have hequiv : P ≃ (subgroup.comap ((normalizer ↑P).subtype : normalizer ↑P →* G) P) :=
  ⟨λ a, ⟨⟨a.1, le_normalizer a.2⟩, a.2⟩, λ a, ⟨a.1.1, a.2⟩,
    λ ⟨_, _⟩, rfl, λ ⟨⟨_, _⟩, _⟩, rfl⟩,
by erw [card_sylow_eq_card_quotient P, ← nat.mul_left_inj
      (show 0 < card (subgroup.comap ((normalizer ↑P).subtype : normalizer ↑P →* G) P),
       from card_pos_iff.2 ⟨1⟩),
    mul_assoc, ← card_eq_card_quotient_mul_card_subgroup,
    ← fintype.card_congr hequiv,
    ← card_eq_card_quotient_mul_card_subgroup,
    ← card_eq_card_quotient_mul_card_subgroup]

/-- Part of **Sylow's third theorem**. The number of Sylow subgroups divides
  the index of any Sylow subgroup. -/
lemma card_sylow_dvd_card_quotient (P : sylow_subgroup G p) :
  card (sylow_subgroup G p) ∣ card (quotient (P : subgroup G)) :=
by rw [← card_sylow_mul_card_quotient_in_normalizer_eq_card_quotient P];
  exact dvd_mul_right _ _

@[simp] lemma fixed_points_sylow (P : sylow_subgroup G p) :
  fixed_points P (sylow_subgroup G p) = {P} :=
set.eq_singleton_iff_unique_mem.2
  ⟨by simp, λ Q h, eq.symm $ sylow_subgroup.ext $ λ x hxP,
    have hQ : ↑P ≤ normalizer (Q : subgroup G),
      from λ x hxP, begin
        rw [mul_action.mem_fixed_points] at h,
        erw [← stabilizer_eq_normalizer, mem_stabilizer_iff, h ⟨_, hxP⟩],
      end,
    begin
      rcases conjugate_in_subgroup hQ (@le_normalizer G _ Q) with ⟨g, hg, rfl⟩,
      rw [coe_smul, normalizer_smul, subgroup.mem_smul, mul_left_inv, one_mul,
        ← stabilizer_eq_normalizer, mem_stabilizer_iff] at hg,
      rwa hg
    end⟩

lemma card_sylow_modeq_one : card (sylow_subgroup G p) ≡ 1 [MOD p] :=
have P : sylow_subgroup G p := classical.arbitrary _,
nat.modeq.trans (mul_action.card_modeq_card_fixed_points _ (card_eq_pow_exponent P)) $
  by { erw [fixed_points_sylow P], simp }

end sylow_subgroup

section pq

variables {G} {p} {q : ℕ} [fact p.prime] [fact q.prime] (hG : card G = p * q)

include hG

lemma exponent_eq_one (hpq : p ≠ q) : sylow_subgroup.exponent G p = 1 :=
eq.symm $ sylow_subgroup.eq_exponent_of_dvd_card_of_succ_not_dvd_card (by simp [hG]) $
  by rwa [pow_add, pow_one, hG, mul_dvd_mul_iff_left (fact.out p.prime).ne_zero,
      nat.prime_dvd_prime_iff_eq (fact.out p.prime) (fact.out q.prime)]

lemma card_quotient_eq (hpq : p ≠ q) (P : sylow_subgroup G p) :
  card (quotient (↑P : subgroup G)) = q :=
by erw [← nat.mul_left_inj (show 0 < card P, from fintype.card_pos_iff.2 ⟨1⟩),
    ← card_eq_card_quotient_mul_card_subgroup, sylow_subgroup.card_eq_pow_exponent,
    exponent_eq_one hG hpq, pow_one, hG, mul_comm]

lemma card_sylow_eq_one_or_q (hpq : p ≠ q) :
  (card (sylow_subgroup G p) = 1 ∨ card (sylow_subgroup G p) = q) :=
have P : sylow_subgroup G p := classical.arbitrary _,
have card_sylow_dvd : card (sylow_subgroup G p) ∣ q,
  from calc card (sylow_subgroup G p)
      ∣ card (quotient (P : subgroup G)) : P.card_sylow_dvd_card_quotient
  ... = q : card_quotient_eq hG hpq _,
(nat.dvd_prime (fact.out _)).1 card_sylow_dvd

lemma card_sylow_eq_one₁ (hqp : q < p) :
  card (sylow_subgroup G p) = 1 :=
(card_sylow_eq_one_or_q hG (ne_of_gt hqp)).elim id
  (λ h, false.elim $
      have 1 ≡ card (sylow_subgroup G p) [MOD p] := eq.symm sylow_subgroup.card_sylow_modeq_one,
      have h0q1 : 0 < q - 1, from nat.sub_pos_of_lt (fact.out q.prime).one_lt,
      begin
        rw [h, nat.modeq.modeq_iff_dvd' (fact.out q.prime).pos] at this,
        exact not_le_of_gt hqp (le_trans (nat.le_of_dvd h0q1 this) (nat.sub_le_self _ _))
      end)

lemma card_sylow_eq_one₂ (hpq : p ≠ q) (hpMODq : ¬p ≡ 1 [MOD q]) :
  card (sylow_subgroup G q) = 1 :=
(card_sylow_eq_one_or_q (show card G = q * p, from mul_comm p q ▸ hG) hpq.symm).elim id $
  (λ h, false.elim $ hpMODq $ h ▸ sylow_subgroup.card_sylow_modeq_one)

open sylow_subgroup

lemma commutative_of_card_eq_prime_mul_prime {p q : ℕ} [fact p.prime] [fact q.prime]
  (hG : card G = p * q) (hqp : q < p) (hpMODq : ¬ p ≡ 1 [MOD q]) :
  ∃ x : G, order_of x = p * q :=
have Q : sylow_subgroup G q := classical.arbitrary _,
have hp1 : card (sylow_subgroup G p) = 1, from card_sylow_eq_one₁ hG hqp,
have hq1 : card (sylow_subgroup G q) = 1, from card_sylow_eq_one₂ hG (ne_of_gt hqp) hpMODq,
have cardP : card P = p, by erw [card_eq_pow_exponent, exponent_eq_one hG (ne_of_gt hqp), pow_one],
have cardP : card Q = q, by erw [card_eq_pow_exponent, exponent_eq_one
  (hG.trans (mul_comm _ _)) (ne_of_lt hqp), pow_one],
_


end pq
