/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import number_theory.padics.padic_norm

/-!
# Multiplicative induction principles for ℕ

This file provides three (closely linked) induction principles for ℕ, commonly used for proofs
about multiplicative functions, such as the totient function and the Möbius function.

## Main definitions

* `nat.rec_on_prime_pow`: Given `P 0, P 1` and a way to extend `P a` to `P (p ^ k * a)`, you can
  define `P` for all natural numbers.
* `nat.rec_on_coprime`: Given `P 0`, `P (p ^ k)` for all prime powers, and a way to extend `P a` and
  `P b` to `P (a * b)` when `a, b` are coprime, you can define `P` for all natural numbers.
* `nat.rec_on_completely_multiplicative`: Given `P 0`, `P 1`, `P p` for all primes, and a proof that
  you can extend `P a` and `P b` to `P (a * b)`, you can define `P` for all natural numbers.

## Implementation notes

The proofs use `padic_val_nat`; however, we have `padic_val_nat p = nat.log p $ nat.gcd k (p ^ k)`
for any `p ∣ k`, which requires far less imports - the API isn't there though; however, this is why
it's in `data` even though we import `number_theory`; it's not a particularly deep theorem.

-/

namespace nat

-- REVIEWERS: should this be here? or in `nat.prime`? or should I just replace this with `haveI`?
instance fact.min_fac_prime (n : ℕ) : fact (prime (n + 2).min_fac) :=
⟨min_fac_prime $ succ_succ_ne_one n⟩

-- also not sure where these two should be
@[simp] lemma dvd_div_iff {a b c : ℕ} (hbc : c ∣ b) : a ∣ b / c ↔ a * c ∣ b :=
begin
  obtain ⟨x, rfl⟩ := hbc,
  obtain rfl | hc := eq_zero_or_pos c,
  { simp },
  { rw [mul_comm c x, mul_dvd_mul_iff_right hc.ne', nat.mul_div_cancel _ hc] },
end

@[simp] lemma one_lt_pow_iff {k n : ℕ} (h : 0 ≠ k) : 1 < n ^ k ↔ 1 < n :=
begin
  cases n,
  { cases k; simp },
  cases n,
  { rw one_pow },
  refine ⟨λ _, one_lt_succ_succ n, λ _, _⟩,
  induction k with k hk,
  { exact absurd rfl h },
  induction k with k _,
  { simp },
  exact one_lt_mul (one_lt_succ_succ _).le (hk (succ_ne_zero k).symm),
end

-- REVIEWERS: I'm also not in love with the naming - any suggestions welcome.

@[elab_as_eliminator]
def rec_on_prime_pow {P : ℕ → Sort*} (h0 : P 0) (h1 : P 1)
  (h : ∀ a p n : ℕ, p.prime → ¬ p ∣ a → P a → P (p ^ n * a)) : ∀ (a : ℕ), P a :=
λ a, nat.strong_rec_on a $ λ n,
  match n with
  | 0     := λ _, h0
  | 1     := λ _, h1
  | (k+2) := λ hk, begin
    let p := (k+2).min_fac,
    let t := padic_val_nat p (k+2),
    have hpt : p ^ t ∣ k + 2 := pow_padic_val_nat_dvd,
    have hp  : prime p := fact.out _,
    have ht  : 0 < t := one_le_padic_val_nat_of_dvd (nat.succ_ne_zero (k + 1)) (min_fac_dvd _),

    convert h ((k + 2) / p ^ t) p t hp _ _,
    { rw nat.mul_div_cancel' hpt },
    { rw nat.dvd_div_iff hpt,
      exact pow_succ_padic_val_nat_not_dvd nat.succ_pos' },

    apply hk _ (nat.div_lt_of_lt_mul _),
    rw [lt_mul_iff_one_lt_left nat.succ_pos', one_lt_pow_iff ht.ne],
    exact prime.one_lt hp
    end
  end

@[elab_as_eliminator]
def rec_on_coprime {P : ℕ → Sort*} (h0 : P 0) (hp : ∀ p n : ℕ, prime p → P (p ^ n))
  (h : ∀ a b, coprime a b → P a → P b → P (a * b)) : ∀ a, P a :=
rec_on_prime_pow h0 (hp 2 0 prime_two) $ λ a p n hp' hpa ha,
  h (p ^ n) a ((prime.coprime_pow_of_not_dvd hp' hpa).symm) (hp p n hp') ha

@[elab_as_eliminator]
def rec_on_completely_multiplicative {P : ℕ → Sort*} (h0 : P 0) (h1 : P 1)
  (hp : ∀ p, prime p → P p) (h : ∀ a b, P a → P b → P (a * b)) : ∀ a, P a :=
let hp : ∀ p n : ℕ, prime p → P (p ^ n) :=
  λ p n hp', match n with
  | 0     := h1
  | (n+1) := by exact h _ _ (hp p hp') (_match _)
  end in
rec_on_coprime h0 hp $ λ a b _, h a b

end nat
