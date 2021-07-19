import topology.metric_space.basic
import tactic.induction

universe u
open metric set

noncomputable theory

namespace besicovitch

structure package (β : Type*) (α : Type*) [metric_space α] :=
(c : β → α)
(r : β → ℝ)
(r_pos : ∀ b, 0 < r b)
(τ : ℝ)
(one_lt_tau : 1 < τ)
(N : ℕ)
(no_satellite : ∀ (c' : ℕ → α) (r' : ℕ → ℝ)
  (h_inter : ∀ i < N, (closed_ball (c' i) (r' i) ∩ closed_ball (c' N) (r' N)).nonempty)
  (h : ∀ i ≤ N, ∀ j ≤ N, i ≠ j → (r' i < dist (c' i) (c' j) ∧ r' j ≤ τ * r' i) ∨
    (r' j < dist (c' j) (c' i) ∧ r' i ≤ τ * r' j))
  (h_radius : ∀ i < N, r' i ≤ τ * r' N),
  false)


variables {α : Type*} [metric_space α] {β : Type u} [nonempty β]
(p : package β α)
include p

namespace package

/-- Define inductively centers of large balls that are not contained in the union of already
chosen balls. -/
noncomputable def f : ordinal.{u} → β
| i :=
    -- `Z` is the set of points that are covered by already constructed balls
    let Z := ⋃ (j : {j // j < i}), closed_ball (p.c (f j)) (p.r (f j)),
    -- `R` is the supremum of the radii of balls with centers not in `Z`
    R := supr (λ b : {b : β // p.c b ∉ Z}, p.r b) in
    -- return an index `b` for which the center `c b` is not in `Z`, and the radius is at
    -- least `R / τ`, if such an index exists (and garbage otherwise).
    classical.epsilon (λ b : β, p.c b ∉ Z ∧ p.r b > R / p.τ)
using_well_founded {dec_tac := `[exact j.2]}

def Union_up_to (i : ordinal.{u}) : set α :=
⋃ j < i, closed_ball (p.c (p.f j)) (p.r (p.f j))

def R (i : ordinal.{u}) : ℝ :=
supr (λ b : {b : β // p.c b ∉ p.Union_up_to i}, p.r b)

/-- Group the balls into disjoint families -/
noncomputable def index : ordinal.{u} → ℕ
| i := let A : set ℕ := ⋃ (j : {j // j < i})
          (hj : (closed_ball (p.c (p.f j)) (p.r (p.f j))
            ∩ closed_ball (p.c (p.f i)) (p.r (p.f i))).nonempty), {index j} in
       Inf (univ \ A)
using_well_founded {dec_tac := `[exact j.2]}

/-- `p.last_step` is the first ordinal where the construction stops making sense. We will only
use ordinals before this step. -/
def last_step : ordinal.{u} :=
Inf {i | ¬ ∃ (b : β), p.c b ∉ p.Union_up_to i ∧ p.r b > (p.R i) / p.τ}

lemma index_lt (i : ordinal.{u}) (hi : i < p.last_step) :
  p.index i < p.N :=
begin
  induction i using ordinal.induction with i IH,
  let A : set ℕ := ⋃ (j : {j // j < i})
         (hj : (closed_ball (p.c (p.f j)) (p.r (p.f j))
            ∩ closed_ball (p.c (p.f i)) (p.r (p.f i))).nonempty), {p.index j},
  have : p.index i = Inf (univ \ A), by rw [index],
  rw this,
  have N_mem : p.N ∈ univ \ A,
  { simp only [not_exists, true_and, exists_prop, mem_Union, mem_singleton_iff, mem_closed_ball,
      not_and, mem_univ, mem_diff, subtype.exists, subtype.coe_mk],
    assume j ji hj,
    exact (IH j ji (ji.trans hi)).ne' },
  suffices : Inf (univ \ A) ≠ p.N,
  { rcases (cInf_le (order_bot.bdd_below (univ \ A)) N_mem).lt_or_eq with H|H,
    { exact H },
    { exact (this H).elim } },
  assume Inf_eq_N,
  have : ∀ k, k < p.N → ∃ j, j < i
    ∧ (closed_ball (p.c (p.f j)) (p.r (p.f j)) ∩ closed_ball (p.c (p.f i)) (p.r (p.f i))).nonempty
    ∧ k = p.index j,
  { assume k hk,
    rw ← Inf_eq_N at hk,
    have : k ∈ A,
      by simpa only [true_and, mem_univ, not_not, mem_diff] using nat.not_mem_of_lt_Inf hk,
    simp at this,
    simpa only [exists_prop, mem_Union, mem_singleton_iff, mem_closed_ball, subtype.exists,
      subtype.coe_mk] },
  choose! g hg using this,
  let G : ℕ → ordinal := λ n, if n = p.N then i else g n,
  apply p.no_satellite (p.c ∘ p.f ∘ G) (p.r ∘ p.f ∘ G),
  { assume a ha,
    have A : G a = g a, by simp only [ha.ne, forall_false_left, ite_eq_right_iff],
    have B : G p.N = i,
      by simp only [forall_false_left, eq_self_iff_true, not_true, ite_eq_left_iff],
    simp only [A, B, function.comp_app],
    exact (hg a ha).2.1 },
  { assume a ha b hb a_ne_b,
    have G_le : G a ≤ G b, sorry,
    -- wlog G_le : G a ≤ G b := le_total (G a) (G b) using [a b, b a] tactic.skip,
    { left,
      split,

    },
    /-{ assume ha hb a_ne_b,
      rw or_comm,
      exact this hb ha a_ne_b.symm },-/

  },

end

end package

end besicovitch
