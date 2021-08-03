/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import data.set.intervals.ord_connected
import algebra.ordered_sub
import order.lattice_intervals

/-!
## The type of nonnegative elements

This file proves properties about `{x : α // 0 ≤ x}`, or equivalently, `Ici (0 : α)` for various
types `α`. In particular, `Ici 0` is a `canonically_linear_ordered_add_monoid` if `α` is a
`linear_ordered_ring`.

When `α` is `ℝ`, this will give us some properties about `ℝ≥0`.
-/

open set

variables {α : Type*}

-- todo: move
instance [partial_order α] [no_top_order α] {a : α} : no_top_order (Ici a) :=
⟨ λ x, let ⟨y, hy⟩ := no_top x.1 in ⟨⟨y, le_trans x.2 hy.le⟩, hy⟩ ⟩

instance [has_zero α] [preorder α] : has_zero (Ici (0 : α)) :=
⟨⟨0, le_rfl⟩⟩

@[simp] protected lemma coe_zero [has_zero α] [preorder α] : ((0 : Ici (0 : α)) : α) = 0 := rfl

@[simp] lemma mk_eq_zero [has_zero α] [preorder α] {x : α} (hx : 0 ≤ x) :
  (⟨x, hx⟩ : Ici (0 : α)) = 0 ↔ x = 0 :=
subtype.ext_iff

instance [add_zero_class α] [preorder α] [covariant_class α α (+) (≤)] :
  has_add (Ici (0 : α)) :=
⟨λ x y, ⟨x + y, add_nonneg x.2 y.2⟩⟩

@[simp] lemma mk_add_mk [add_zero_class α] [preorder α] [covariant_class α α (+) (≤)] {x y : α}
  (hx : 0 ≤ x) (hy : 0 ≤ y) : (⟨x, hx⟩ : Ici (0 : α)) + ⟨y, hy⟩ = ⟨x + y, add_nonneg hx hy⟩ :=
rfl

@[simp, norm_cast]
protected lemma coe_add [add_zero_class α] [preorder α] [covariant_class α α (+) (≤)]
  (a b : Ici (0 : α)) : ((a + b : Ici (0 : α)) : α) = a + b := rfl

instance [ordered_add_comm_monoid α] : ordered_add_comm_monoid (Ici (0 : α)) :=
subtype.coe_injective.ordered_add_comm_monoid (coe : Ici (0 : α) → α) rfl (λ x y, rfl)

instance [linear_ordered_add_comm_monoid α] : linear_ordered_add_comm_monoid (Ici (0 : α)) :=
subtype.coe_injective.linear_ordered_add_comm_monoid (coe : Ici (0 : α) → α) rfl (λ x y, rfl)

instance [ordered_cancel_add_comm_monoid α] :
  ordered_cancel_add_comm_monoid (Ici (0 : α)) :=
subtype.coe_injective.ordered_cancel_add_comm_monoid (coe : Ici (0 : α) → α) rfl (λ x y, rfl)

instance [linear_ordered_cancel_add_comm_monoid α] :
  linear_ordered_cancel_add_comm_monoid (Ici (0 : α)) :=
subtype.coe_injective.linear_ordered_cancel_add_comm_monoid
  (coe : Ici (0 : α) → α) rfl (λ x y, rfl)

instance [ordered_semiring α] : has_one (Ici (0 : α)) :=
{ one := ⟨1, zero_le_one⟩ }

@[simp] protected lemma coe_one [ordered_semiring α] : ((1 : Ici (0 : α)) : α) = 1 := rfl

@[simp] lemma mk_eq_one [ordered_semiring α] {x : α} (hx : 0 ≤ x) :
  (⟨x, hx⟩ : Ici (0 : α)) = 1 ↔ x = 1 :=
subtype.ext_iff

instance [ordered_semiring α] : has_mul (Ici (0 : α)) :=
{ mul := λ x y, ⟨x * y, mul_nonneg x.2 y.2⟩ }

@[simp, norm_cast]
protected lemma coe_mul [ordered_semiring α] (a b : Ici (0 : α)) :
  ((a * b : Ici (0 : α)) : α) = a * b := rfl

@[simp] lemma mk_mul_mk [ordered_semiring α] {x y : α} (hx : 0 ≤ x) (hy : 0 ≤ y) :
  (⟨x, hx⟩ : Ici (0 : α)) * ⟨y, hy⟩ = ⟨x * y, mul_nonneg hx hy⟩ :=
rfl

instance [ordered_semiring α] : ordered_semiring (Ici (0 : α)) :=
subtype.coe_injective.ordered_semiring
  (coe : Ici (0 : α) → α) rfl rfl (λ x y, rfl) (λ x y, rfl)

instance [ordered_comm_semiring α] : ordered_comm_semiring (Ici (0 : α)) :=
subtype.coe_injective.ordered_comm_semiring
  (coe : Ici (0 : α) → α) rfl rfl (λ x y, rfl) (λ x y, rfl)

instance [linear_ordered_semiring α] : nontrivial (Ici (0 : α)) :=
⟨ ⟨0, 1, λ h, zero_ne_one (congr_arg subtype.val h)⟩ ⟩

instance [linear_ordered_semiring α] : linear_ordered_semiring (Ici (0 : α)) :=
subtype.coe_injective.linear_ordered_semiring
  (coe : Ici (0 : α) → α) rfl rfl (λ x y, rfl) (λ x y, rfl)

instance [linear_ordered_field α] : has_inv (Ici (0 : α)) :=
{ inv := λ x, ⟨x⁻¹, inv_nonneg.mpr x.2⟩ }

@[simp, norm_cast]
protected lemma coe_inv [linear_ordered_field α] (a : Ici (0 : α)) :
  ((a⁻¹ : Ici (0 : α)) : α) = a⁻¹ := rfl

@[simp] lemma inv_mk [linear_ordered_field α] {x : α} (hx : 0 ≤ x) :
  (⟨x, hx⟩ : Ici (0 : α))⁻¹ = ⟨x⁻¹, inv_nonneg.mpr hx⟩ :=
rfl

instance [linear_ordered_field α] : has_div (Ici (0 : α)) :=
{ div := λ x y, ⟨x / y, div_nonneg x.2 y.2⟩ }

@[simp, norm_cast]
protected lemma coe_div [linear_ordered_field α] (a b : Ici (0 : α)) :
  ((a / b : Ici (0 : α)) : α) = a / b := rfl

@[simp] lemma mk_div_mk [linear_ordered_field α] {x y : α} (hx : 0 ≤ x) (hy : 0 ≤ y) :
  (⟨x, hx⟩ : Ici (0 : α)) / ⟨y, hy⟩ = ⟨x / y, div_nonneg hx hy⟩ :=
rfl

-- todo: move
lemma le_iff_exists_nonneg_add [ordered_ring α] (a b : α) :
  a ≤ b ↔ ∃ c ≥ 0, b = a + c :=
⟨λ h, ⟨b - a, sub_nonneg.mpr h, by simp⟩,
  λ ⟨c, hc, h⟩, by { rw [h, le_add_iff_nonneg_right], exact hc }⟩

instance [ordered_ring α] : canonically_ordered_add_monoid (Ici (0 : α)) :=
{ le_iff_exists_add     := λ ⟨a, ha⟩ ⟨b, hb⟩,
    by simpa only [mk_add_mk, set_coe.exists, subtype.mk_eq_mk] using le_iff_exists_nonneg_add a b,
  ..set.Ici.ordered_add_comm_monoid,
  ..set.Ici.order_bot }

instance [ordered_comm_ring α] [no_zero_divisors α] :
  canonically_ordered_comm_semiring (Ici (0 : α)) :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := by { rintro ⟨a, ha⟩ ⟨b, hb⟩, simp },
  .. set.Ici.canonically_ordered_add_monoid,
  .. set.Ici.ordered_comm_semiring }

instance [linear_ordered_ring α] :
  canonically_linear_ordered_add_monoid (Ici (0 : α)) :=
{ ..subtype.linear_order _, ..set.Ici.canonically_ordered_add_monoid }

section linear_order

variables [has_zero α] [linear_order α]

def to_nonneg (a : α) : Ici (0 : α) :=
⟨max a 0, le_max_right _ _⟩

@[simp]
lemma coe_to_nonneg {a : α} : (to_nonneg a : α) = max a 0 := rfl

@[simp]
lemma to_nonneg_of_nonneg {a : α} (h : 0 ≤ a) : to_nonneg a = ⟨a, h⟩ :=
by simp [to_nonneg, h]

@[simp]
lemma to_nonneg_coe {a : Ici (0 : α)} : to_nonneg (a : α) = a :=
by { cases a with a ha, exact to_nonneg_of_nonneg ha }

@[simp]
lemma to_nonneg_le {a : α} {b : Ici (0 : α)} : to_nonneg a ≤ b ↔ a ≤ b :=
by { cases b with b hb, simp [to_nonneg, mem_Ici.mp hb] }

@[simp]
lemma to_nonneg_lt {a : Ici (0 : α)} {b : α} : a < to_nonneg b ↔ ↑a < b :=
by { cases a with a ha, simp [to_nonneg, (mem_Ici.mp ha).not_lt] }

instance [has_sub α] : has_sub (Ici (0 : α)) :=
⟨λ x y, to_nonneg (x - y)⟩

@[simp] lemma mk_sub_mk [has_sub α] {x y : α}
  (hx : 0 ≤ x) (hy : 0 ≤ y) : (⟨x, hx⟩ : Ici (0 : α)) - ⟨y, hy⟩ = to_nonneg (x - y) :=
rfl

end linear_order

instance [linear_ordered_ring α] : has_ordered_sub (Ici (0 : α)) :=
⟨by { rintro ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩, simp [sub_le_iff_le_add] }⟩
