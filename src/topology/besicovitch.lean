import topology.metric_space.basic

universe u

namespace besicovitch

structure package (α : Type*)


variables {α : Type*} [metric_space α] {β : Type u} [nonempty β]
(c : β → α) (r : β → ℝ) (τ : ℝ)



include c r τ

/-- Define inductively centers of large balls that are not contained in the union of already
chosen balls. -/
noncomputable def f : ordinal.{u} → β
| i :=
    -- `Z` is the set of points that are covered by already constructed balls
    let Z := ⋃ (j : {j // j < i}), metric.ball (c (f j)) (r (f j)),
    -- `R` is the supremum of the radii of balls with centers not in `Z`
    R := supr (λ b : {b : β // c b ∉ Z}, r b) in
    -- return an index `b` for which the center `c b` is not in `Z`, and the radius is at
    -- least `R / τ`, if such an index exists (and garbage otherwise).
    classical.epsilon (λ b : β, c b ∉ Z ∧ r b > R/τ)
using_well_founded {dec_tac := `[exact j.2]}

/-- Group the balls into disjoint families -/
noncomputable def index : ordinal.{u} → ℕ
| i :=
    let A : set ℕ := ⋃ (j : {j // j < i})
      (hj : c (f c r τ i) ∈ metric.ball (c (f c r τ j)) (r (f c r τ j))), {index j} in
    Inf (set.univ \ A)
using_well_founded {dec_tac := `[exact j.2]}

/-- `last_time c r τ ` is the first ordinal where the construction stops making sense. We will only
use ordinals before this step. -/
def last_step : ordinal.{u} :=
Inf {i |
  let Z := ⋃ (j : {j // j < i}), metric.ball (c (f c r τ j)) (r (f c r τ j)),
  -- `R` is the supremum of the radii of balls with centers not in `Z`
  R := supr (λ b : {b : β // c b ∉ Z}, r b) in
  -- return an index `b` for which the center `c b` is not in `Z`, and the radius is at
  -- least `R / τ`
  ¬ ∃ (b : β), c b ∉ Z ∧ r b > R/τ}
