/-
Copyright 2021 Google LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

      http : //www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
Authors :  Martin Zinkevich (modified for mathlib by Hunter Monroe)
 -/

import measure_theory.measurable_space
import measure_theory.measure_space


/-! This file defines the basic concepts in probability theory.
    There are four fundamental principles :
    1. Make theorems as readable as possible. Use Pr[A ∧ B], not μ (A ∩ B). Other examples :
       Pr[(X >ᵣ 3) ∨ (Y =ᵣ 7)]. While events are technically sets, in probability theory,
       they are better written as propositions that may or may not hold.
    2. Avoid absurd statements where possible. Don't allow Pr[A] if A is not an event,
       or Pr[X ∈ᵣ S] if S is not measurable, or Pr[∀ᵣ a in S, E a] if S is not countable.
       It is always possible to write Pr[⟨S, ...proof S is an event...⟩].
    3. Embed measurability into the objects and operations themselves. An event is measurable by
       definition. When we take the and, or, not, for all, exists, measurability should be automatic.
    4. Don't expect the reader to know measure theory, but at times it may be required by the
       author.

    Several concepts are defined in this module :
      probability_space :  a measure_space where the measure has a value of 1.
      event :  a subtype of a set that is measurable (defined based upon the measurable space).
      event :  a event on a probability space (defined based upon the probability).
      Pr[E] :  the probability of an event (note :  expectations are defined in real_random_variable).
      measurable_fun :  a subtype of a function that is measurable (denoted (M₁ →ₘ M₂)).
      random_variable :  a measurable_fun whose domain is a probability space (denoted (P →ᵣ M)).

     Also, various independence and identical definitions are specified. Some choices :
     * A and B are independent if A has zero probability.
     * an infinite family of events/random variables is independent if every finite subset
       is independent.
     * Two random variables are identical if they have equal probability on every measurable
       set. The probability spaces on which they are defined need not be equal.
      -/

open measure_theory measurable_space
open_locale big_operators classical


universe u

namespace subsemilattice_inf

structure subsemilattice_inf (α : Type u) [semilattice_inf α] : Type u :=
(carrier : set α)
(inf_mem : ∀ a b, a ∈ carrier → b ∈ carrier → a ⊓ b ∈ carrier)

variables {α : Type u} [semilattice_inf α] {S T : subsemilattice_inf α} {x : α}

protected lemma eq : ∀ {S T : subsemilattice_inf α}, S.carrier = T.carrier → S = T
| ⟨x, h1⟩ ⟨.(x), h2⟩ rfl := rfl

instance : set_like (subsemilattice_inf α) α :=
{ coe := λ S, S.carrier,
  coe_injective' := λ S T hST, subsemilattice_inf.eq hST, }

@[simp] lemma mem_carrier : x ∈ S.carrier ↔ x ∈ (S : set α) := iff.rfl

@[ext] theorem ext (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := set_like.ext h

instance : has_inf S := { inf := λ a b, ⟨a ⊓ b, S.inf_mem _ _ a.prop b.prop⟩, }

instance (S : subsemilattice_inf α) : semilattice_inf S :=
{ inf := (⊓),
  le := (≤),
  le_refl := λ a, le_rfl,
  le_trans := λ a b c hab hbc, le_trans hab hbc,
  le_antisymm := λ a b hab hba, le_antisymm hab hba,
  le_inf := λ a b c hab hac, le_inf hab hac,
  inf_le_left := λ a b, inf_le_left,
  inf_le_right := λ a b, inf_le_right, }

@[norm_cast]
lemma coe_inf (a b : S) : ↑(a ⊓ b) = (a ⊓ b : α) := rfl

end subsemilattice_inf


namespace subsemilattice_inf_bot

set_option old_structure_cmd true

structure subsemilattice_inf_bot (α : Type u) [semilattice_inf_bot α]
  extends subsemilattice_inf.subsemilattice_inf α : Type u :=
(bot_mem : ⊥ ∈ carrier)

variables {α : Type u} [semilattice_inf_bot α] {S T : subsemilattice_inf_bot α} {x : α}

protected lemma eq : ∀ {S T : subsemilattice_inf_bot α}, S.carrier = T.carrier → S = T
| ⟨x, h1, h1'⟩ ⟨.(x), h2, h2'⟩ rfl := rfl

instance : set_like (subsemilattice_inf_bot α) α :=
{ coe := λ S, S.carrier,
  coe_injective' := λ S T hST, subsemilattice_inf_bot.eq hST, }

@[simp] lemma mem_carrier : x ∈ S.carrier ↔ x ∈ (S : set α) := iff.rfl

@[ext] theorem ext (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := set_like.ext h

instance : has_bot S := { bot := ⟨⊥, S.bot_mem⟩, }

@[norm_cast]
lemma coe_bot : ((⊥ : S) : α) = (⊥ : α) := rfl

instance (S : subsemilattice_inf_bot α) : semilattice_inf_bot S :=
{ bot := ⊥,
  bot_le := λ a, by { rw [← subtype.coe_le_coe, coe_bot], exact bot_le, },
  ..subsemilattice_inf.semilattice_inf S.to_subsemilattice_inf }

@[norm_cast]
lemma coe_inf (a b : S) : ↑(a ⊓ b) = (a ⊓ b : α) := rfl

end subsemilattice_inf_bot


namespace subsemilattice_inf_top

set_option old_structure_cmd true

structure subsemilattice_inf_top (α : Type u) [semilattice_inf_top α]
  extends subsemilattice_inf.subsemilattice_inf α : Type u :=
(top_mem : ⊤ ∈ carrier)

variables {α : Type u} [semilattice_inf_top α] {S T : subsemilattice_inf_top α} {x : α}

protected lemma eq : ∀ {S T : subsemilattice_inf_top α}, S.carrier = T.carrier → S = T
| ⟨x, h1, h1'⟩ ⟨.(x), h2, h2'⟩ rfl := rfl

instance : set_like (subsemilattice_inf_top α) α :=
{ coe := λ S, S.carrier,
  coe_injective' := λ S T hST, subsemilattice_inf_top.eq hST, }

@[simp] lemma mem_carrier : x ∈ S.carrier ↔ x ∈ (S : set α) := iff.rfl

@[ext] theorem ext (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := set_like.ext h

instance : has_top S := { top := ⟨⊤, S.top_mem⟩, }

@[norm_cast]
lemma coe_top : ((⊤ : S) : α) = (⊤ : α) := rfl

instance (S : subsemilattice_inf_top α) : semilattice_inf_top S :=
{ top := ⊤,
  le_top := λ a, by { rw [← subtype.coe_le_coe, coe_top], exact le_top, },
  ..subsemilattice_inf.semilattice_inf S.to_subsemilattice_inf }

@[norm_cast]
lemma coe_inf (a b : S) : ↑(a ⊓ b) = (a ⊓ b : α) := rfl

end subsemilattice_inf_top


namespace subsemilattice_sup

structure subsemilattice_sup (α : Type u) [semilattice_sup α] : Type u :=
(carrier : set α)
(sup_mem : ∀ a b, a ∈ carrier → b ∈ carrier → a ⊔ b ∈ carrier)

variables {α : Type u} [semilattice_sup α] {S T : subsemilattice_sup α} {x : α}

lemma subsemilattice_sup.eq : ∀ {S T : subsemilattice_sup α}, S.carrier = T.carrier → S = T
| ⟨x, h1⟩ ⟨.(x), h2⟩ rfl := rfl

instance : set_like (subsemilattice_sup α) α :=
{ coe := λ S, S.carrier,
  coe_injective' := λ S T hST, subsemilattice_sup.eq hST, }

@[simp] lemma mem_carrier : x ∈ S.carrier ↔ x ∈ (S : set α) := iff.rfl

@[ext] theorem ext (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := set_like.ext h

instance : has_sup S := { sup := λ a b, ⟨a ⊔ b, S.sup_mem _ _ a.prop b.prop⟩, }

instance (S : subsemilattice_sup α) : semilattice_sup S :=
{ sup := (⊔),
  le := (≤),
  le_refl := λ a, le_rfl,
  le_trans := λ a b c hab hbc, le_trans hab hbc,
  le_antisymm := λ a b hab hba, le_antisymm hab hba,
  sup_le := λ a b c hab hac, sup_le hab hac,
  le_sup_left := λ a b, le_sup_left,
  le_sup_right := λ a b, le_sup_right, }

@[norm_cast]
lemma coe_sup (a b : S) : ↑(a ⊔ b) = (a ⊔ b : α) := rfl

end subsemilattice_sup


namespace subsemilattice_sup_bot

set_option old_structure_cmd true

structure subsemilattice_sup_bot (α : Type u) [semilattice_sup_bot α]
  extends subsemilattice_sup.subsemilattice_sup α : Type u :=
(bot_mem : ⊥ ∈ carrier)

variables {α : Type u} [semilattice_sup_bot α] {S T : subsemilattice_sup_bot α} {x : α}

protected lemma eq : ∀ {S T : subsemilattice_sup_bot α}, S.carrier = T.carrier → S = T
| ⟨x, h1, h1'⟩ ⟨.(x), h2, h2'⟩ rfl := rfl

instance : set_like (subsemilattice_sup_bot α) α :=
{ coe := λ S, S.carrier,
  coe_injective' := λ S T hST, subsemilattice_sup_bot.eq hST, }

@[simp] lemma mem_carrier : x ∈ S.carrier ↔ x ∈ (S : set α) := iff.rfl

@[ext] theorem ext (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := set_like.ext h

instance : has_bot S := { bot := ⟨⊥, S.bot_mem⟩, }

@[norm_cast]
lemma coe_bot : ((⊥ : S) : α) = (⊥ : α) := rfl

instance (S : subsemilattice_sup_bot α) : semilattice_sup_bot S :=
{ bot := ⊥,
  bot_le := λ a, by { rw [← subtype.coe_le_coe, coe_bot], exact bot_le, },
  ..subsemilattice_sup.semilattice_sup S.to_subsemilattice_sup }

@[norm_cast]
lemma coe_sup (a b : S) : ↑(a ⊔ b) = (a ⊔ b : α) := rfl

end subsemilattice_sup_bot


namespace subsemilattice_sup_top

set_option old_structure_cmd true

structure subsemilattice_sup_top (α : Type u) [semilattice_sup_top α]
  extends subsemilattice_sup.subsemilattice_sup α : Type u :=
(top_mem : ⊤ ∈ carrier)

variables {α : Type u} [semilattice_sup_top α] {S T : subsemilattice_sup_top α} {x : α}

protected lemma eq : ∀ {S T : subsemilattice_sup_top α}, S.carrier = T.carrier → S = T
| ⟨x, h1, h1'⟩ ⟨.(x), h2, h2'⟩ rfl := rfl

instance : set_like (subsemilattice_sup_top α) α :=
{ coe := λ S, S.carrier,
  coe_injective' := λ S T hST, subsemilattice_sup_top.eq hST, }

@[simp] lemma mem_carrier : x ∈ S.carrier ↔ x ∈ (S : set α) := iff.rfl

@[ext] theorem ext (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := set_like.ext h

instance : has_top S := { top := ⟨⊤, S.top_mem⟩, }

@[norm_cast]
lemma coe_top : ((⊤ : S) : α) = (⊤ : α) := rfl

instance (S : subsemilattice_sup_top α) : semilattice_sup_top S :=
{ top := ⊤,
  le_top := λ a, by { rw [← subtype.coe_le_coe, coe_top], exact le_top, },
  ..subsemilattice_sup.semilattice_sup S.to_subsemilattice_sup }

@[norm_cast]
lemma coe_sup (a b : S) : ↑(a ⊔ b) = (a ⊔ b : α) := rfl

end subsemilattice_sup_top


namespace sublattice

set_option old_structure_cmd true

structure sublattice (α : Type u) [lattice α]
  extends subsemilattice_inf.subsemilattice_inf α, subsemilattice_sup.subsemilattice_sup α : Type u

variables {α : Type u} [lattice α] {S T : sublattice α} {x : α}

lemma sublattice.eq : ∀ {S T : sublattice α}, S.carrier = T.carrier → S = T
| ⟨x, h1, h1'⟩ ⟨.(x), h2, h2'⟩ rfl := rfl

instance : set_like (sublattice α) α :=
{ coe := λ S, S.carrier,
  coe_injective' := λ S T hST, sublattice.eq hST, }

@[simp] lemma mem_carrier : x ∈ S.carrier ↔ x ∈ (S : set α) := iff.rfl

@[ext] theorem ext (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := set_like.ext h

instance (S : sublattice α) : lattice S :=
{ ..subsemilattice_inf.semilattice_inf S.to_subsemilattice_inf,
  ..subsemilattice_sup.semilattice_sup S.to_subsemilattice_sup, }

@[norm_cast]
lemma coe_inf (a b : S) : ↑(a ⊓ b) = (a ⊓ b : α) := rfl

@[norm_cast]
lemma coe_sup (a b : S) : ↑(a ⊔ b) = (a ⊔ b : α) := rfl

end sublattice


namespace subboolean_algebra

set_option old_structure_cmd true

structure subboolean_algebra (α : Type u) [boolean_algebra α] extends sublattice.sublattice α :
  Type u :=
(compl_mem : ∀ a, a ∈ carrier → aᶜ ∈ carrier)
(bot_mem : ⊥ ∈ carrier)

section subboolean_algebra_instances

variables {α : Type u} [boolean_algebra α] {S T : subboolean_algebra α} {x : α}

lemma subboolean_algebra.eq : ∀ {S T : subboolean_algebra α}, S.carrier = T.carrier → S = T
| ⟨x, h1, h1', h1'', h1'''⟩ ⟨.(x), h2, h2', h2'', h2'''⟩ rfl := rfl

instance : set_like (subboolean_algebra α) α :=
{ coe := λ S, S.carrier,
  coe_injective' := λ S T hST, subboolean_algebra.eq hST, }

@[simp] lemma mem_carrier : x ∈ S.carrier ↔ x ∈ (S : set α) := iff.rfl

@[ext] theorem ext (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := set_like.ext h

instance : has_bot S := { bot := ⟨⊥, S.bot_mem⟩, }

@[norm_cast]
lemma coe_bot : ((⊥ : S) : α) = (⊥ : α) := rfl

instance : has_compl S := { compl := λ a, ⟨aᶜ, S.compl_mem a a.prop⟩, }

@[norm_cast]
lemma coe_compl (y : S) : ↑(yᶜ) = (y : α)ᶜ := rfl

instance : has_top S := { top := ⊥ᶜ }

lemma top_def : (⊤ : S) = ⊥ᶜ := rfl

@[norm_cast]
lemma coe_top : ((⊤ : S) : α) = (⊤ : α) := by rw [top_def, coe_compl, coe_bot, compl_bot]

instance : lattice S := sublattice.lattice S.to_sublattice

@[norm_cast]
lemma coe_inf (a b : S) : ↑(a ⊓ b) = (a ⊓ b : α) := rfl

@[norm_cast]
lemma coe_sup (a b : S) : ↑(a ⊔ b) = (a ⊔ b : α) := rfl

instance : boolean_algebra S :=
boolean_algebra.of_core
{ compl := has_compl.compl,
  bot := ⊥,
  top := ⊤,
  le_top := λ a, by {rw [← subtype.coe_le_coe, coe_top], exact le_top, },
  bot_le := λ a, by {rw [← subtype.coe_le_coe, coe_bot], exact bot_le, },
  le_sup_inf := λ a b c, by { rw [← subtype.coe_le_coe], push_cast, exact le_sup_inf, },
  inf_compl_le_bot := λ x, by { rw [← subtype.coe_le_coe], push_cast, rw inf_compl_eq_bot, },
  top_le_sup_compl := λ x, by { rw [← subtype.coe_le_coe], push_cast, rw sup_compl_eq_top, },
  ..sublattice.lattice S.to_sublattice, }

@[norm_cast]
lemma coe_sdiff (a b : S) : ↑(a \ b) = (a \ b : α) :=
by { rw sdiff_eq, push_cast, rw ← sdiff_eq }

end subboolean_algebra_instances

section sub_set

variables {α : Type u} {S : subboolean_algebra (set α)} {s t : S}

instance : has_subset S := { subset := λ s t, s ≤ t, }

lemma le_eq_subset : ((≤) : S → S → Prop) = (⊆) := rfl

lemma coe_subset_coe : (s : set α) ⊆ t ↔ s ⊆ t :=
by { simp_rw [← le_eq_subset, ← set.le_eq_subset], exact subtype.coe_le_coe, }

/-- `set.univ` as an element of a sub-boolean-algebra. -/
def univ (S : subboolean_algebra (set α)) : S := ⊤

lemma top_eq_univ : ⊤ = univ S := rfl

@[norm_cast, simp] lemma coe_univ : (univ S : set α) = set.univ :=
by { rw [← set.top_eq_univ, ← top_eq_univ], push_cast, }

lemma subset_univ : s ⊆ univ S := by simp [← le_eq_subset, ← top_eq_univ, le_top]

instance : has_emptyc S := ⟨⊥⟩

@[norm_cast, simp] lemma coe_empty : ((∅ : S) : set α) = ∅ := rfl

lemma empty_subset : (∅ : S) ⊆ s := by { rw ← coe_subset_coe, simp, }

instance : has_inter S := { inter := λ s t, s ⊓ t, }

lemma inf_eq_inter : s ⊓ t = s ∩ t := rfl

instance : has_union S := { union := λ s t, s ⊔ t, }

lemma sup_eq_union : s ⊔ t = s ∪ t := rfl

end sub_set

end subboolean_algebra


open subboolean_algebra

namespace probability_theory

/-- A measurable set on a measurable space that has a probability measure is called an event. -/
def event (Ω : Type*) [measurable_space Ω] : subboolean_algebra (set Ω) :=
{ carrier := measurable_set,
  inf_mem := λ s t hs ht, hs.inter ht,
  sup_mem := λ s t hs ht, hs.union ht,
  compl_mem := λ s hs, hs.compl,
  bot_mem := measurable_set.empty, }

namespace event

section event_def_and_set_notation

variables {Ω : Type*} [measurable_space Ω] {E F : event Ω}

lemma coe_eq_coe {E F : event Ω} : (E : set Ω) = F ↔ E = F :=
set_like.coe_eq_coe

end event_def_and_set_notation


section event_const

variables {Ω : Type*} [measurable_space Ω]

def const (Ω : Type*) [measurable_space Ω] (P : Prop) : event Ω :=
⟨{ω : Ω | P}, measurable_set.const P⟩

@[norm_cast]
lemma const_coe (p : Prop) : (const Ω p : set Ω) = {ω : Ω | p} := rfl

lemma const_eq_univ (p : Prop) (h : p) : const Ω p = univ (event Ω) :=
by { rw ← event.coe_eq_coe, push_cast, simp [h], }

lemma const_eq_empty (p : Prop) (h : ¬p) : const Ω p = (∅ : event Ω) :=
by { rw ← event.coe_eq_coe, push_cast, simp [h], }

end event_const

end event

class probability_space (α : Type*) extends measure_space α :=
(volume_univ : volume (set.univ) = 1)

export probability_space (volume_univ)

instance probability_space.probability_measure {Ω : Type*} [P : probability_space Ω] :
  probability_measure P.volume :=
⟨P.volume_univ⟩

section prob_def

variables {Ω : Type*} [probability_space Ω] {E F : event Ω}

/- Probability of an event, with value in `ℝ`. -/
def prob (E : event Ω) : ℝ := (volume (E : set Ω)).to_real

notation `ℙ[`E`]` := prob E

lemma prob_def (E : event Ω) : ℙ[E] = (volume (E : set Ω)).to_real := by rw prob

lemma prob_nonneg : 0 ≤ ℙ[E] := ennreal.to_real_nonneg

lemma prob_mono (h_subset : E ⊆ F) : ℙ[E] ≤ ℙ[F] :=
begin
  simp_rw prob_def,
  refine (ennreal.to_real_le_to_real (measure_ne_top _ _) (measure_ne_top _ _)).mpr _,
  exact measure_mono h_subset,
end

@[simp] lemma prob_univ : ℙ[univ (event Ω)] = 1 :=
by { rw prob_def, push_cast, rw volume_univ, simp, }

@[simp] lemma prob_empty : ℙ[(∅ : event Ω)] = 0 := by { rw prob_def, push_cast, simp, }

lemma prob_le_one : ℙ[E] ≤ 1 := (prob_mono subset_univ).trans prob_univ.le

end prob_def


lemma prob_event_const_true {Ω : Type*} [probability_space Ω] (p : Prop) (h : p) :
  ℙ[event.const Ω p] = 1 :=
by { rw event.const_eq_univ p h, exact prob_univ, }

lemma Pr_event_const_false {Ω : Type*} [probability_space Ω] (p : Prop) (h : ¬p) :
  ℙ[event.const Ω p] = 0 :=
by { rw event.const_eq_empty p h, exact prob_empty, }


end probability_theory
