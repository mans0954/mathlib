import analysis.normed_space.basic
import algebra.big_operators.finprod

open_locale classical filter topological_space
open filter
noncomputable theory

variables {ι : Type*}

open set function

@[ext] structure partition_box (ι : Type*) :=
(lower upper : ι → ℝ)
(lower_lt_upper : ∀ i, lower i < upper i)

namespace partition_box

variables (I J : partition_box ι) {x y : ι → ℝ}

protected def Icc : set (ι → ℝ) := Icc I.lower I.upper
protected def Ioc : set (ι → ℝ) := {x | ∀ i, x i ∈ Ioc (I.lower i) (I.upper i)}

lemma Icc_def : I.Icc = Icc I.lower I.upper := rfl

lemma Ioc_def : I.Ioc = {x | ∀ i, x i ∈ Ioc (I.lower i) (I.upper i)} := rfl

lemma Icc_eq_pi : I.Icc = pi univ (λ i, Icc (I.lower i) (I.upper i)) := (pi_univ_Icc _ _).symm
lemma Ioc_eq_pi : I.Ioc = pi univ (λ i, Ioc (I.lower i) (I.upper i)) :=
by simp only [Ioc_def, pi, mem_univ, forall_true_left]

lemma lower_le_upper : I.lower ≤ I.upper := λ i, (I.lower_lt_upper i).le

@[simp] lemma upper_mem_Icc : I.upper ∈ I.Icc := right_mem_Icc.2 I.lower_le_upper
@[simp] lemma lower_mem_Icc : I.lower ∈ I.Icc := left_mem_Icc.2 I.lower_le_upper
@[simp] lemma upper_mem_Ioc : I.upper ∈ I.Ioc := λ i, right_mem_Ioc.2 $ I.lower_lt_upper i

@[simp] protected lemma closure_Ioc : closure I.Ioc = I.Icc :=
by simp only [Ioc_eq_pi, closure_pi_set, closure_Ioc (I.lower_lt_upper _), Icc_eq_pi]

instance : has_le (partition_box ι) := ⟨λ I J, I.Ioc ⊆ J.Ioc⟩

lemma le_tfae : tfae [I ≤ J, I.Ioc ⊆ J.Ioc, I.Icc ⊆ J.Icc, J.lower ≤ I.lower ∧ I.upper ≤ J.upper] :=
begin
  tfae_have : 1 ↔ 2, from iff.rfl,
  tfae_have : 2 → 3, from λ h, by simpa only [partition_box.closure_Ioc] using closure_mono h,
  tfae_have : 3 ↔ 4, from Icc_subset_Icc_iff I.lower_le_upper,
  tfae_have : 4 → 2, from λ h x hx i, Ioc_subset_Ioc (h.1 i) (h.2 i) (hx i),
  tfae_finish
end

variables {I J}

lemma le_iff_Ioc : I ≤ J ↔ I.Ioc ⊆ J.Ioc := iff.rfl
lemma le_iff_Icc : I ≤ J ↔ I.Icc ⊆ J.Icc := (le_tfae I J).out 0 2
lemma le_iff_bounds : I ≤ J ↔ J.lower ≤ I.lower ∧ I.upper ≤ J.upper := (le_tfae I J).out 0 3

lemma Ioc_injective : injective (partition_box.Ioc : partition_box ι → set (ι → ℝ)) :=
begin
  intros I J h,
  simp only [subset.antisymm_iff, ← le_iff_Ioc, le_iff_bounds] at h,
  exact ext _ _ (le_antisymm h.2.1 h.1.1) (le_antisymm h.1.2 h.2.2)
end

instance : partial_order (partition_box ι) :=
{ le := (≤),
  .. partial_order.lift (partition_box.Ioc : partition_box ι → set (ι → ℝ)) Ioc_injective }

end partition_box

@[ext, protect_proj]
structure pi_partition (I : partition_box ι) :=
(boxes : set (partition_box ι))
(finite_boxes : finite boxes)
(bUnion_boxes_Ioc : (⋃ J ∈ boxes, partition_box.Ioc J) = I.Ioc)
(disjoint_Ioc : pairwise_on boxes (disjoint on partition_box.Ioc))

namespace pi_partition

variables {I J J' : partition_box ι} (π : pi_partition I) {x : ι → ℝ}

lemma le_of_mem (hJ : J ∈ π.boxes) : J ≤ I :=
partition_box.le_iff_Ioc.2 $ π.bUnion_boxes_Ioc ▸ subset_bUnion_of_mem hJ

lemma lower_le_lower (hJ : J ∈ π.boxes) : I.lower ≤ J.lower :=
(partition_box.le_iff_bounds.1 (π.le_of_mem hJ)).1

lemma upper_le_upper (hJ : J ∈ π.boxes) : J.upper ≤ I.upper :=
(partition_box.le_iff_bounds.1 (π.le_of_mem hJ)).2

lemma eq_of_mem_Ioc (h : J ∈ π.boxes) (h' : J' ∈ π.boxes) (hx : x ∈ J.Ioc) (hx' : x ∈ J'.Ioc) :
  J = J' :=
by_contra $ λ H, π.disjoint_Ioc _ h _ h' H ⟨hx, hx'⟩

protected lemma exists_unique (hx : x ∈ I.Ioc) : ∃! J ∈ π.boxes, x ∈ partition_box.Ioc J :=
begin
  rw [← π.bUnion_boxes_Ioc, mem_bUnion_iff] at hx,
  rcases hx with ⟨J, h, hx⟩,
  exact exists_unique.intro2 J h hx (λ J' h' hx', π.eq_of_mem_Ioc h' h hx' hx),
end

lemma eq_of_le (h : J ∈ π.boxes) (h' : J' ∈ π.boxes) (hle : J ≤ J') : J = J' :=
π.eq_of_mem_Ioc h h' J.upper_mem_Ioc (hle J.upper_mem_Ioc)

instance : has_le (pi_partition I) := ⟨λ π π', ∀ ⦃I⦄, I ∈ π.boxes → ∃ I' ∈ π'.boxes, I ≤ I'⟩

instance : partial_order (pi_partition I) :=
{ le := (≤),
  le_refl := λ π I hI, ⟨I, hI, le_rfl⟩,
  le_trans := λ π₁ π₂ π₃ h₁₂ h₂₃ I₁ hI₁,
    let ⟨I₂, hI₂, hI₁₂⟩ := h₁₂ hI₁, ⟨I₃, hI₃, hI₂₃⟩ := h₂₃ hI₂ in ⟨I₃, hI₃, hI₁₂.trans hI₂₃⟩,
  le_antisymm :=
    begin
      suffices : ∀ ⦃π π' : pi_partition I⦄, π ≤ π' → π' ≤ π → ∀ J ∈ π.boxes, J ∈ π'.boxes,
        from λ π π' h h', ext _ _ (set.ext $ λ J, ⟨this h h' _, this h' h _⟩),
      intros π π' h h' J hJ,
      rcases h hJ with ⟨J', hJ', hle⟩, rcases h' hJ' with ⟨J'', hJ'', hle'⟩,
      obtain rfl : J = J'', from π.eq_of_le hJ hJ'' (hle.trans hle'),
      obtain rfl : J' = J, from le_antisymm ‹_› ‹_›,
      assumption
    end}

instance : has_top (pi_partition I) :=
{ top := { boxes := {I},
           finite_boxes := finite_singleton _,
           bUnion_boxes_Ioc := bUnion_singleton _ _,
           disjoint_Ioc := pairwise_on_singleton _ _ } }
           

@[simp] lemma top_boxes : (⊤ : pi_partition I).boxes = {I} := rfl

private def inf_boxes (π π' : pi_partition I) : set (partition_box ι) :=
⋃ (J ∈ π.boxes) (J' ∈ π'.boxes)
  (h : ∀ i, max ((J : _).lower i) (J'.lower i) < min (J.upper i) (J'.upper i)), {⟨_, _, h⟩}

private lemma mem_inf_boxes' {π π' : pi_partition I} {J'' : partition_box ι} :
  J'' ∈ inf_boxes π π' ↔ ∃ (J ∈ π.boxes) (J' ∈ π'.boxes)
    (h : ∀ i, max ((J : _).lower i) (J'.lower i) < min (J.upper i) (J'.upper i)),
    J'' = ⟨_, _, h⟩ :=
by simp only [inf_boxes, mem_Union, mem_singleton_iff]

instance : has_inf (pi_partition I) :=
⟨λ π π',
  { boxes := inf_boxes π π',
    finite_boxes := π.finite_boxes.bUnion $ λ J hJ, π'.finite_boxes.bUnion $
      λ J hJ, finite_Union_Prop $ λ h, finite_singleton _,
    bUnion_boxes_Ioc :=
      begin
        ext x,
        simp only [mem_Union, exists_prop, mem_inf_boxes'],
        refine ⟨_, λ H, _⟩,
        { rintro ⟨_, ⟨J, hJ, J', hJ', h, rfl⟩, hx⟩,
          simp only [partition_box.Ioc, mem_set_of_eq, mem_Ioc, max_lt_iff, le_min_iff] at hx,
          refine π.le_of_mem hJ (λ i, ⟨(hx i).1.1, (hx i).2.1⟩) },
        { rcases π.exists_unique H with ⟨J, ⟨hJ, hx, -⟩, -⟩,
          rcases π'.exists_unique H with ⟨J', ⟨hJ', hx', -⟩, -⟩,
          have : ∀ i, x i ∈ Ioc (max (J.lower i) (J'.lower i)) (min (J.upper i) (J'.upper i)),
            from λ i, ⟨max_lt (hx i).1 (hx' i).1, le_min (hx i).2 (hx' i).2⟩,
          exact ⟨_, ⟨J, hJ, J', hJ', λ i, (this i).1.trans_le (this i).2, rfl⟩, this⟩ }
      end,
    disjoint_Ioc :=-- λ J₁ hJ₁ J₂ hJ₂ hne x hx,
      begin
        simp only [pairwise_on, mem_inf_boxes'],
        rintro _ ⟨J₁, hJ₁, J₁', hJ₁', H₁, rfl⟩ _ ⟨J₂, hJ₂, J₂', hJ₂', H₂, rfl⟩ H x ⟨hx₁, hx₂⟩,
        simp only [partition_box.Ioc, mem_set_of_eq, mem_Ioc, max_lt_iff, le_min_iff] at hx₁ hx₂,
        obtain rfl : J₁ = J₂,
          from π.eq_of_mem_Ioc hJ₁ hJ₂ (λ i, ⟨(hx₁ i).1.1, (hx₁ i).2.1⟩)
            (λ i, ⟨(hx₂ i).1.1, (hx₂ i).2.1⟩),
        obtain rfl : J₁' = J₂',
          from π'.eq_of_mem_Ioc hJ₁' hJ₂' (λ i, ⟨(hx₁ i).1.2, (hx₁ i).2.2⟩)
            (λ i, ⟨(hx₂ i).1.2, (hx₂ i).2.2⟩),
        exact H rfl
      end }⟩

lemma mem_inf_boxes {π π' : pi_partition I} {J'' : partition_box ι} :
  J'' ∈ (π ⊓ π').boxes ↔ ∃ (J : partition_box ι) (hJ: J ∈ π.boxes)
    (J' : partition_box ι) (hJ' : J' ∈ π'.boxes)
    (h : ∀ i, max (J.lower i) (J'.lower i) < min (J.upper i) (J'.upper i)),
    J'' = ⟨_, _, h⟩ :=
mem_inf_boxes'

instance : semilattice_inf_top (pi_partition I) :=
{ le := (≤),
  top := ⊤,
  le_top := λ π J hJ, ⟨I, mem_singleton _, π.le_of_mem hJ⟩,
  inf := (⊓),
  inf_le_left := λ π π' J'' hJ'',
    begin
      rcases mem_inf_boxes.1 hJ'' with ⟨J, hJ, J', hJ', H, rfl⟩, clear hJ'',
      exact ⟨J, hJ, partition_box.le_iff_bounds.2 ⟨λ i, le_max_left _ _, λ i, min_le_left _ _⟩⟩
    end,
  inf_le_right := λ π π' J'' hJ'',
    begin
      rcases mem_inf_boxes.1 hJ'' with ⟨J, hJ, J', hJ', H, rfl⟩, clear hJ'',
      exact ⟨J', hJ', partition_box.le_iff_bounds.2 ⟨λ i, le_max_right _ _, λ i, min_le_right _ _⟩⟩
    end,
  le_inf := λ π π₁ π₂ h₁ h₂ J hJ,
    begin
      rcases h₁ hJ with ⟨J₁, mem₁, le₁⟩, rcases h₂ hJ with ⟨J₂, mem₂, le₂⟩,
      simp only [exists_prop, mem_inf_boxes],
      refine ⟨_, ⟨J₁, mem₁, J₂, mem₂, λ i, _, rfl⟩, _⟩;
        simp only [partition_box.le_iff_bounds] at *,
      calc max (J₁.lower i) (J₂.lower i) ≤ J.lower i : max_le (le₁.1 i) (le₂.1 i)
      ... < J.upper i : J.lower_lt_upper i
      ... ≤ min (J₁.upper i) (J₂.upper i) : le_min (le₁.2 i) (le₂.2 i),
      exact ⟨λ i, max_le (le₁.1 i) (le₂.1 i), λ i, le_min (le₁.2 i) (le₂.2 i)⟩
    end,
  .. pi_partition.partial_order }

def split_each (πi : Π J ∈ π.boxes, pi_partition J) : pi_partition I :=
{ boxes := ⋃ J ∈ π.boxes, (πi J ‹J ∈ π.boxes›).boxes,
  finite_boxes := π.finite_boxes.bUnion $ λ J hJ, (πi J hJ).finite_boxes,
  bUnion_boxes_Ioc := by simp only [bUnion_Union, pi_partition.bUnion_boxes_Ioc],
  disjoint_Ioc :=
    begin
      simp only [pairwise_on, mem_Union],
      rintro J₁' ⟨J₁, hJ₁, hJ₁'⟩ J₂' ⟨J₂, hJ₂, hJ₂'⟩ Hne x ⟨hx₁, hx₂⟩, apply Hne,
      obtain rfl : J₁ = J₂,
        from π.eq_of_mem_Ioc hJ₁ hJ₂ ((πi J₁ hJ₁).le_of_mem hJ₁' hx₁)
          ((πi J₂ hJ₂).le_of_mem hJ₂' hx₂),
      obtain rfl : hJ₁ = hJ₂ := rfl,
      exact (πi J₁ hJ₁).eq_of_mem_Ioc hJ₁' hJ₂' hx₁ hx₂
    end }

lemma mem_split_each_boxes {πi : Π J ∈ π.boxes, pi_partition J} :
  J ∈ (split_each π πi).boxes ↔ ∃ J' ∈ π.boxes, J ∈ (πi J' ‹J' ∈ π.boxes›).boxes :=
by simp only [split_each, mem_Union]

def split_each_axis [fintype ι] (π : pi_partition I) (s : ι → set ℝ) (hs : ∀ i, finite (s i)) :
  pi_partition I :=
{ boxes := ⋃ (L ∈ pi univ (λ i, 𝒫 (s i)))
    (H : ∀ i, Sup (insert (I.lower i) (L i)) < Inf (insert (I.upper i) (s i \ L i))), {⟨_, _, H⟩},
  finite_boxes := (finite.pi $ λ i, (hs i).finite_subsets).bUnion $ λ L hL,
    finite_Union_Prop $ λ H, finite_singleton _,
  bUnion_boxes_Ioc :=
    begin
      have : ∀ (L ∈ pi univ (λ i, 𝒫 (s i))) i, finite (L i),
        from λ L hL i, (hs i).subset (hL i trivial),
      ext x,
      simp only [mem_Union, exists_prop, mem_singleton_iff],
      refine ⟨_, λ hx, _⟩,
      { rintro ⟨J, ⟨L, hL, Hlt, rfl⟩, hx⟩ i,
        have hf : finite (insert _ (L i)) := ((hs i).subset (hL i trivial)).insert _,
        have hf' : finite (insert _ (s i \ L i)) := ((hs i).subset (diff_subset _ _)).insert _,
        exact ⟨(le_cSup hf.bdd_above (mem_insert _ _)).trans_lt (hx i).1,
          (hx i).2.trans (cInf_le hf'.bdd_below (mem_insert _ _))⟩ },
      { set L : ι → set ℝ := λ i, s i ∩ Iio (x i),
        have : ∀ i, x i ∈ Ioc (Sup (insert (I.lower i) (L i)))
          (Inf (insert (I.upper i) (s i \ L i))),
        {  },
        refine ⟨_, ⟨L, λ i _, inter_subset_left _ _, _, rfl⟩, _⟩, }
    end
}

def is_homothetic (π : pi_partition I) : Prop :=
∀ (J ∈ π.boxes), ∃ ε : ℝ, (J : partition_box ι).upper - J.lower = ε • (I.upper - I.lower)

end pi_partition

structure marked_pi_partition (I : partition_box ι) extends pi_partition I :=
(mark : Π (J ∈ boxes) (i : ι), ℝ)
(mark_mem' : ∀ J ∈ boxes, mark J ‹_› ∈ Icc I.lower I.upper)

namespace marked_pi_partition

section

variables {I : partition_box ι} (π : marked_pi_partition I)

instance : has_mem (partition_box ι) (marked_pi_partition I) := ⟨λ J π, J ∈ π.boxes⟩

lemma mark_mem {J : partition_box ι} (hJ : J ∈ π) : π.mark J hJ ∈ Icc I.lower I.upper :=
π.mark_mem' J hJ

def is_Henstock : Prop := ∀ J ∈ π, π.mark J ‹_› ∈ Icc J.lower J.upper

end

variables [fintype ι] {I : partition_box ι} (π : marked_pi_partition I)

def is_subordinate (π : marked_pi_partition I) (r : Π x ∈ I, ennreal) :=
∀ (J ∈ π.boxes) (x ∈ J), edist x (π.mark J ‹_›) ≤ r (π.mark J ‹_›) (π.mark_mem _)

lemma exists_is_subordinate (r : Π x ∈ I, ennreal) (hr : ∀ x hx, 0 < r x hx) :
  ∃ π : marked_pi_partition I, π.is_subordinate r ∧ π.is_homothetic ∧ π.is_Henstock :=
sorry

lemma is_subordinate.mono {π : marked_pi_partition I} {r r' : Π x ∈ I, ennreal}
  (h : ∀ x hx, r x hx ≤ r' x hx) (hr : π.is_subordinate r) :
  π.is_subordinate r' :=
λ J hJ x hx, (hr J hJ x hx).trans (h _ _)

lemma is_subordinate.ediam_le {π : marked_pi_partition I} {r : Π x ∈ I, ennreal}
  (h : π.is_subordinate r) {J : partition_box ι} (hJ : J ∈ π) :
  emetric.diam (J : set (ι → ℝ)) ≤ 2 * r (π.center J hJ ) (π.center_mem _) :=
emetric.diam_le_of_forall_edist_le $ λ x hx y hy,
calc edist x y ≤ edist x (π.center J hJ) + edist y (π.center J hJ) : edist_triangle_right _ _ _
... ≤ r (π.center J hJ ) (π.center_mem _) + r (π.center J hJ ) (π.center_mem _) :
  add_le_add (h _ _ _ hx) (h _ _ _ hy)
... = 2 * r (π.center J hJ ) (π.center_mem _) : (two_mul _).symm

end marked_pi_partition

namespace box_integral

variables {E F : Type*} [normed_group E] [normed_space ℝ E] [normed_group F] [normed_space ℝ F]
  [fintype ι] {I : partition_box ι} {π : marked_pi_partition I}

open marked_pi_partition

def Riemann : filter (marked_pi_partition I) :=
(⨅ (r : ennreal) (hr : 0 < r), 𝓟 {π | ∀ J ∈ π, emetric.diam (↑J : set (ι → ℝ)) ≤ r}) ⊓
  𝓟 {π | is_Henstock π}

def McShane : filter (marked_pi_partition I) :=
⨅ (r : Π x ∈ I, ennreal) (hr : ∀ x hx, 0 < r x hx), 𝓟 {π | is_subordinate π r}

def Henstock : filter (marked_pi_partition I) :=
McShane ⊓ 𝓟 {π | is_Henstock π}

def Henstock' : filter (marked_pi_partition I) :=
McShane ⊓ 𝓟 {π | π.is_homothetic ∧ is_Henstock π}

lemma has_basis_McShane :
  (@McShane _ _ I).has_basis (λ r : Π x ∈ I, ennreal, ∀ x hx, 0 < r x hx)
    (λ r, {π | π.is_subordinate r}) :=
has_basis_binfi_principal'
  (λ r hr r' hr', ⟨λ x hx, min (r x hx) (r' x hx), λ x hx, lt_min (hr x hx) (hr' x hx),
    λ π hπ, hπ.mono $ λ x hx, min_le_left _ _, λ π hπ, hπ.mono $ λ x hx, min_le_right _ _⟩)
  ⟨λ x hx, 1, λ _ _, ennreal.zero_lt_one⟩

lemma has_basis_Henstock :
  (@Henstock _ _ I).has_basis (λ r : Π x ∈ I, ennreal, ∀ x hx, 0 < r x hx)
    (λ r, {π | π.is_subordinate r ∧ π.is_Henstock }) :=
has_basis_McShane.inf_principal _

lemma has_basis_Henstock' :
  (@Henstock' _ _ I).has_basis (λ r : Π x ∈ I, ennreal, ∀ x hx, 0 < r x hx)
    (λ r, {π | π.is_subordinate r ∧ π.is_homothetic ∧ π.is_Henstock}) :=
has_basis_McShane.inf_principal _

lemma has_basis_Riemann :
  (@Riemann _ _ I).has_basis (λ r : ennreal, 0 < r)
    (λ r, {π | (∀ J ∈ π, emetric.diam (↑J : set (ι → ℝ)) ≤ r) ∧ π.is_Henstock}) :=
begin
  refine (has_basis_binfi_principal' _ _).inf_principal _,
  exact λ r hr r' hr', ⟨min r r', lt_min hr hr',
    λ π hπ J hJ, (hπ J hJ).trans $ min_le_left _ _,
    λ π hπ J hJ, (hπ J hJ).trans $ min_le_right _ _⟩,
  exact ⟨1, ennreal.zero_lt_one⟩
end

lemma Henstock_le_McShane : @Henstock _ _ I ≤ McShane := inf_le_left

lemma Henstock_le_Riemann : @Henstock _ _ I ≤ Riemann :=
begin
  refine (inf_le_inf_right _ $ le_binfi $ λ r hr, _),
  refine binfi_le_of_le (λ _ _, r / 2) (λ _ _, ennreal.half_pos hr) _,
  refine (principal_mono.2 $ λ π hπ J hJ, _),
  simpa only [two_mul, ennreal.add_halves] using hπ.ediam_le hJ
end

lemma Henstock'_le_Henstock : @Henstock' _ _ I ≤ Henstock :=
inf_le_inf_left _ $ principal_mono.2 $ inter_subset_right _ _

instance Henstock'_ne_bot : (@Henstock' _ _ I).ne_bot :=
has_basis_Henstock'.ne_bot_iff.2 $ λ r hr, exists_is_subordinate _ hr

instance Henstock_ne_bot : (@Henstock _ _ I).ne_bot := ne_bot_of_le Henstock'_le_Henstock
instance McShane_ne_bot : (@McShane _ _ I).ne_bot := ne_bot_of_le Henstock_le_McShane
instance Riemann_ne_bot : (@Riemann _ _ I).ne_bot := ne_bot_of_le Henstock_le_Riemann

def integral_sum (f : (ι → ℝ) → E) (vol : partition_box ι → (E →L[ℝ] F))
  (π : marked_pi_partition I) : F :=
π.boxes.attach.sum $ λ J, vol J $ f $ π.center J J.coe_prop

@[simp] lemma integral_sum_add (f g : (ι → ℝ) → E) (vol : partition_box ι → (E →L[ℝ] F))
  (π : marked_pi_partition I) :
  integral_sum (f + g) vol π = integral_sum f vol π + integral_sum g vol π :=
by simp only [integral_sum, finset.sum_add_distrib, pi.add_apply, (vol _).map_add]

@[simp] lemma integral_sum_neg (f : (ι → ℝ) → E) (vol : partition_box ι → (E →L[ℝ] F))
  (π : marked_pi_partition I) :
  integral_sum (-f) vol π = -integral_sum f vol π :=
by simp only [integral_sum, finset.sum_neg_distrib, pi.neg_apply, (vol _).map_neg]

@[simp] lemma integral_sum_smul (c : ℝ) (f : (ι → ℝ) → E) (vol : partition_box ι → (E →L[ℝ] F))
  (π : marked_pi_partition I) :
  integral_sum (c • f) vol π = c • integral_sum f vol π :=
by simp only [integral_sum, finset.smul_sum, pi.smul_apply, continuous_linear_map.map_smul]

def has_integral (I : partition_box ι) (l : filter (marked_pi_partition I)) (f : (ι → ℝ) → E)
  (vol : partition_box ι → (E →L[ℝ] F)) (y : F) : Prop :=
tendsto (integral_sum f vol) l (𝓝 y)

def integrable (I : partition_box ι) (l : filter (marked_pi_partition I)) (f : (ι → ℝ) → E)
  (vol : partition_box ι → (E →L[ℝ] F)) : Prop :=
∃ y, has_integral I l f vol y

def integral (I : partition_box ι) (l : filter (marked_pi_partition I)) (f : (ι → ℝ) → E)
  (vol : partition_box ι → (E →L[ℝ] F)) : F :=
if h : integrable I l f vol then classical.some h else 0

variables {l : filter (marked_pi_partition I)}
  {f g : (ι → ℝ) → E} {vol : partition_box ι → (E →L[ℝ] F)} {y y' : F}

lemma integrable_iff_Cauchy [complete_space F] [ne_bot l] :
  integrable I l f vol ↔ cauchy (l.map (integral_sum f vol)) :=
cauchy_map_iff_exists_tendsto.symm

lemma has_integral.R_to_H (h : has_integral I Riemann f vol y) :
  has_integral I Henstock f vol y :=
h.mono_left Henstock_le_Riemann

lemma has_integral.MS_to_H (h : has_integral I McShane f vol y) :
  has_integral I Henstock f vol y :=
h.mono_left Henstock_le_McShane

lemma integrable.has_integral (h : integrable I l f vol) :
  has_integral I l f vol (integral I l f vol) :=
by { rw [integral, dif_pos h], exact classical.some_spec h }

lemma has_integral.unique [ne_bot l] (h : has_integral I l f vol y)
  (h' : has_integral I l f vol y') :
  y = y' :=
tendsto_nhds_unique h h'

lemma has_integral.integrable (h : has_integral I l f vol y) : integrable I l f vol := ⟨_, h⟩

lemma has_integral.integral_eq [ne_bot l] (h : has_integral I l f vol y) :
  integral I l f vol = y :=
h.integrable.has_integral.unique h

lemma has_integral.add (h : has_integral I l f vol y) (h' : has_integral I l g vol y') :
  has_integral I l (f + g) vol (y + y') :=
by simpa only [has_integral, ← integral_sum_add] using h.add h'

lemma integrable.add (hf : integrable I l f vol) (hg : integrable I l g vol) :
  integrable I l (f + g) vol :=
(hf.has_integral.add hg.has_integral).integrable

lemma integral_add [ne_bot l] (hf : integrable I l f vol) (hg : integrable I l g vol) :
  integral I l (f + g) vol = integral I l f vol + integral I l g vol :=
(hf.has_integral.add hg.has_integral).integral_eq

lemma has_integral.neg (hf : has_integral I l f vol y) : has_integral I l (-f) vol (-y) :=
by simpa only [has_integral, ← integral_sum_neg] using hf.neg

lemma integrable.neg (hf : integrable I l f vol) : integrable I l (-f) vol :=
hf.has_integral.neg.integrable

lemma integrable.of_neg (hf : integrable I l (-f) vol) : integrable I l f vol := neg_neg f ▸ hf.neg

@[simp] lemma integrable_neg : integrable I l (-f) vol ↔ integrable I l f vol :=
⟨λ h, h.of_neg, λ h, h.neg⟩

@[simp] lemma integral_neg [ne_bot l] : integral I l (-f) vol = -integral I l f vol :=
if h : integrable I l f vol then h.has_integral.neg.integral_eq
else by rw [integral, integral, dif_neg h, dif_neg (mt integrable.of_neg h), neg_zero]

lemma has_integral.sub (h : has_integral I l f vol y) (h' : has_integral I l g vol y') :
  has_integral I l (f - g) vol (y - y') :=
by simpa only [sub_eq_add_neg] using h.add h'.neg

lemma integrable.sub (hf : integrable I l f vol) (hg : integrable I l g vol) :
  integrable I l (f - g) vol :=
(hf.has_integral.sub hg.has_integral).integrable

lemma integral_sub [ne_bot l] (hf : integrable I l f vol) (hg : integrable I l g vol) :
  integral I l (f - g) vol = integral I l f vol - integral I l g vol :=
(hf.has_integral.sub hg.has_integral).integral_eq

lemma has_integral_zero : has_integral I l (λ _, (0:E)) vol 0 :=
by { dunfold has_integral, convert tendsto_const_nhds, ext π, simp [integral_sum] }

lemma integrable_zero : integrable I l (λ _, (0:E)) vol := ⟨0, has_integral_zero⟩

@[simp] lemma integral_zero [ne_bot l] : integral I l (λ _, (0:E)) vol = 0 :=
has_integral_zero.integral_eq

lemma has_integral.smul (hf : has_integral I l f vol y) (c : ℝ) :
  has_integral I l (c • f) vol (c • y) :=
by simpa only [has_integral, ← integral_sum_smul]
  using (tendsto_const_nhds : tendsto _ _ (𝓝 c)).smul hf

lemma integrable.smul (hf : integrable I l f vol) (c : ℝ) :
  integrable I l (c • f) vol :=
(hf.has_integral.smul c).integrable

lemma integrable.of_smul {c : ℝ} (hf : integrable I l (c • f) vol) (hc : c ≠ 0) :
  integrable I l f vol :=
by { convert hf.smul c⁻¹, ext x, simp only [pi.smul_apply, inv_smul_smul' hc] }

@[simp] lemma integral_smul [ne_bot l] (c : ℝ) :
  integral I l (λ x, c • f x) vol = c • integral I l f vol :=
begin
  rcases em (c = 0) with rfl | hc, { simp },
  by_cases hf : integrable I l f vol,
  { exact (hf.has_integral.smul c).integral_eq },
  { have : ¬integrable I l (λ x, c • f x) vol, from mt (λ h, h.of_smul hc) hf,
    rw [integral, integral, dif_neg hf, dif_neg this, smul_zero] }
end

lemma Riemann_integrable_of_continuous_on (h : continuous_on f (Icc I.lower I.upper))

end box_integral
