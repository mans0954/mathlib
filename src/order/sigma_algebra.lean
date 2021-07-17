/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import order.complete_lattice
import order.boolean_algebra
import data.set.countable

/-!
# Abstract σ-algebras

## Main declarations

## Implementation notes

## Notations

## References

## Tags

-/

set_option old_structure_cmd true

universes u v
variables {α : Type u} {w x y z : α}

/-- Same as Sup, but restricted to countable sets. -/
class has_countable_Sup (α : Type u) :=
(Supₙ : Π (s : set α), s.countable → α)

/-- Same as Inf, but restricted to countable sets. -/
class has_countable_Inf (α : Type u) :=
(Infₙ : Π (s : set α), s.countable → α)

export has_countable_Sup (Supₙ) has_countable_Inf (Infₙ)

/-- Abstract σ-algebra. Having only one of Infₙ and Supₙ is enough, but we ask for both to ensure
better definitional equalities. -/
class sigma_algebra (α : Type u) extends boolean_algebra α, has_countable_Sup α,
  has_countable_Inf α :=
(le_Supₙ : ∀ (s : set α) (hs : s.countable), ∀ x ∈ s, x ≤ Supₙ s hs)
(Supₙ_le : ∀ (s : set α) (hs : s.countable) (x : α), (∀ y ∈ s, y ≤ x) → Supₙ s hs ≤ x)
(le_Infₙ : ∀ (s : set α) (hs : s.countable) (x : α), (∀ y ∈ s, x ≤ y) → x ≤ Infₙ s hs)
(Infₙ_le : ∀ (s : set α) (hs : s.countable), ∀ x ∈ s, Infₙ s hs ≤ x)


section sigma_algebra
variables [sigma_algebra α] {s t : set α} {hs : s.countable} {ht : t.countable} {a b : α}


section Supₙ

lemma le_Supₙ : a ∈ s → a ≤ Supₙ s hs := sigma_algebra.le_Supₙ s hs a

lemma Supₙ_le : (∀b∈s, b ≤ a) → Supₙ s hs ≤ a := sigma_algebra.Supₙ_le s hs a

lemma is_lub_Supₙ (s : set α) (hs : s.countable) : is_lub s (Supₙ s hs) :=
⟨assume x, le_Supₙ, assume x, Supₙ_le⟩

lemma is_lub.Supₙ_eq (h : is_lub s a) : Supₙ s hs = a := (is_lub_Supₙ s hs).unique h

theorem le_Supₙ_of_le (hb : b ∈ s) (h : a ≤ b) : a ≤ Supₙ s hs :=
le_trans h (le_Supₙ hb)

theorem Supₙ_le_Supₙ (h : s ⊆ t) : Supₙ s hs ≤ Supₙ t ht :=
(is_lub_Supₙ s hs).mono (is_lub_Supₙ t ht) h

@[simp] theorem Supₙ_le_iff : Supₙ s hs ≤ a ↔ (∀b ∈ s, b ≤ a) :=
is_lub_le_iff (is_lub_Supₙ s hs)

lemma le_Supₙ_iff :
  a ≤ Supₙ s hs ↔ (∀ b, (∀ x ∈ s, x ≤ b) → a ≤ b) :=
⟨λ h b hb, le_trans h (Supₙ_le hb), λ hb, hb _ (λ x, le_Supₙ)⟩

theorem Supₙ_le_Supₙ_of_forall_exists_le (h : ∀ x ∈ s, ∃ y ∈ t, x ≤ y) : Supₙ s hs ≤ Supₙ t ht :=
le_of_forall_le' begin
  simp only [Supₙ_le_iff],
  introv h₀ h₁,
  rcases h _ h₁ with ⟨y,hy,hy'⟩,
  solve_by_elim [le_trans hy']
end

theorem Supₙ_singleton {a : α} : Supₙ {a} (set.countable_singleton a) = a :=
is_lub_singleton.Supₙ_eq

end Supₙ


section Infₙ

lemma Infₙ_le : a ∈ s → Infₙ s hs ≤ a := sigma_algebra.Infₙ_le s hs a

lemma le_Infₙ : (∀b∈s, a ≤ b) → a ≤ Infₙ s hs := sigma_algebra.le_Infₙ s hs a

lemma is_glb_Infₙ (s : set α) (hs : s.countable) : is_glb s (Infₙ s hs) :=
⟨assume a, Infₙ_le, assume a, le_Infₙ⟩

lemma is_glb.Infₙ_eq (h : is_glb s a) : Infₙ s hs = a := (is_glb_Infₙ s hs).unique h

theorem Infₙ_le_of_le (hb : b ∈ s) (h : b ≤ a) : Infₙ s hs ≤ a :=
le_trans (Infₙ_le hb) h

theorem Infₙ_le_Infₙ (h : s ⊆ t) : Infₙ t ht ≤ Infₙ s hs :=
(is_glb_Infₙ s hs).mono (is_glb_Infₙ t ht) h

@[simp] theorem le_Infₙ_iff : a ≤ Infₙ s hs ↔ (∀b ∈ s, a ≤ b) :=
le_is_glb_iff (is_glb_Infₙ s hs)

lemma Infₙ_le_iff :
  Infₙ s hs ≤ a ↔ (∀ b, (∀ x ∈ s, b ≤ x) → b ≤ a) :=
⟨λ h b hb, le_trans (le_Infₙ hb) h, λ hb, hb _ (λ x, Infₙ_le)⟩

theorem Infₙ_le_Infₙ_of_forall_exists_le (h : ∀ x ∈ s, ∃ y ∈ t, y ≤ x) : Infₙ t ht ≤ Infₙ s hs :=
le_of_forall_le begin
  simp only [le_Infₙ_iff],
  introv h₀ h₁,
  rcases h _ h₁ with ⟨y,hy,hy'⟩,
  solve_by_elim [le_trans _ hy']
end

theorem Infₙ_singleton {a : α} : Infₙ {a} (set.countable_singleton a) = a :=
is_glb_singleton.Infₙ_eq

end Infₙ



theorem Infₙ_le_Supₙ (hs_nonempty : s.nonempty) : Infₙ s hs ≤ Supₙ s hs :=
is_glb_le_is_lub (is_glb_Infₙ s hs) (is_lub_Supₙ s hs) hs_nonempty

theorem Supₙ_union : Supₙ (s ∪ t) (hs.union ht) = Supₙ s hs ⊔ Supₙ t ht :=
((is_lub_Supₙ s hs).union (is_lub_Supₙ t ht)).Supₙ_eq

theorem Supₙ_inter_le : Supₙ (s ∩ t) (hs.inter ht) ≤ Supₙ s hs ⊓ Supₙ t ht :=
by finish
/-
  Sup_le (assume a ⟨a_s, a_t⟩, le_inf (le_Sup a_s) (le_Sup a_t))
-/

theorem Infₙ_union : Infₙ (s ∪ t) (hs.union ht) = Infₙ s hs ⊓ Infₙ t ht :=
((is_glb_Infₙ s hs).union (is_glb_Infₙ t ht)).Infₙ_eq

theorem le_Infₙ_inter : Infₙ s hs ⊔ Infₙ t ht ≤ Infₙ (s ∩ t) (hs.inter ht) :=
@Supₙ_inter_le (order_dual α) _ _ _

@[simp] theorem Sup_empty : Sup ∅ = (⊥ : α) :=
(@is_lub_empty α _).Sup_eq

@[simp] theorem Inf_empty : Inf ∅ = (⊤ : α) :=
(@is_glb_empty α _).Inf_eq

@[simp] theorem Sup_univ : Sup univ = (⊤ : α) :=
(@is_lub_univ α _).Sup_eq

@[simp] theorem Inf_univ : Inf univ = (⊥ : α) :=
(@is_glb_univ α _).Inf_eq

-- TODO(Jeremy): get this automatically
@[simp] theorem Supₙ_insert {a : α} : Supₙ (insert a s) (hs.insert a) = a ⊔ Supₙ s hs :=
((is_lub_Supₙ s hs).insert a).Supₙ_eq

@[simp] theorem Infₙ_insert {a : α} : Infₙ (insert a s) (hs.insert a) = a ⊓ Infₙ s hs :=
((is_glb_Infₙ s hs).insert a).Infₙ_eq

theorem Supₙ_le_Supₙ_of_subset_instert_bot (h : s ⊆ insert ⊥ t) : Supₙ s hs ≤ Supₙ t ht :=
le_trans (Supₙ_le_Supₙ h) (le_of_eq (trans Supₙ_insert bot_sup_eq))

theorem Infₙ_le_Infₙ_of_subset_insert_top (h : s ⊆ insert ⊤ t) : Infₙ t ht ≤ Infₙ s hs :=
le_trans (le_of_eq (trans top_inf_eq.symm Infₙ_insert.symm)) (Infₙ_le_Infₙ h)

theorem Supₙ_pair {a b : α} : Supₙ {a, b} _ = a ⊔ b :=
(@is_lub_pair α _ a b).Supₙ_eq

theorem Inf_pair {a b : α} : Infₙ {a, b} _ = a ⊓ b :=
(@is_glb_pair α _ a b).Infₙ_eq

@[simp] theorem Infₙ_eq_top : Infₙ s hs = ⊤ ↔ (∀ a ∈ s, a = ⊤) :=
iff.intro
  (assume h a ha, top_unique $ h ▸ Infₙ_le ha)
  (assume h, top_unique $ le_Infₙ $ assume a ha, top_le_iff.2 $ h a ha)

lemma eq_singleton_top_of_Infₙ_eq_top_of_nonempty (h_inf : Infₙ s hs = ⊤) (hne : s.nonempty) :
  s = {⊤} :=
by { rw set.eq_singleton_iff_nonempty_unique_mem, rw Infₙ_eq_top at h_inf, exact ⟨hne, h_inf⟩, }

@[simp] theorem Supₙ_eq_bot : Supₙ s hs = ⊥ ↔ (∀ a ∈ s, a = ⊥) :=
@Infₙ_eq_top (order_dual α) _ _

lemma eq_singleton_bot_of_Supₙ_eq_bot_of_nonempty (h_sup : Supₙ s hs = ⊥) (hne : s.nonempty) :
  s = {⊥} :=
by { rw set.eq_singleton_iff_nonempty_unique_mem, rw Supₙ_eq_bot at h_sup, exact ⟨hne, h_sup⟩, }


end sigma_algebra
