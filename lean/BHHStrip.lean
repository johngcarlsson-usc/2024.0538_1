import Mathlib
open MeasureTheory

abbrev Pt := EuclideanSpace ℝ (Fin 2)

def unitSquare : Set Pt := {x | ∀ i, x i ∈ Set.Icc (0:ℝ) 1}

/-- Length of the shortest closed tour through the points. -/
noncomputable def tourLength {n : ℕ} (p : Fin n → Pt) : ℝ :=
  ⨅ σ : Equiv.Perm (Fin n), ∑ i, dist (p (σ i)) (p (σ (finRotate n i)))

/-- Expected optimal tour length for n independent uniform points in the unit square. -/
noncomputable def L (n : ℕ) : ℝ :=
  ∫ p, tourLength p ∂(Measure.pi fun _ : Fin n => volume.restrict unitSquare)

/-!
# Lean proof that β₂ < 0.93 (`bhh_lt_point_nine_three`)

Proof route (Beardwood–Halton–Hammersley strip construction, worked directly with
`n` uniform points — no Poisson process and no order statistics):

* Cut the square into `k ≈ √(n/3)` horizontal strips of height `h = 1/k`.
* Part A (deterministic): the serpentine strip tour gives
  `tourLength p ≤ succSum + 2 * endSum + 4`, where `succSum` sums the distances between
  x-consecutive points of the same strip and `endSum` sums the gaps between each strip's
  extreme points and the square's left/right edges.
* Part B (probability): by exchangeability, `E[succSum]` is `n(n-1)` times a double
  integral weighted by the probability `(1 - s/k)^(n-2)` that the other `n-2` points
  avoid the strip segment between the two points. `E[endSum]` is handled the same way
  with one point.
* Part C (analysis): `(1 - x)^m ≤ exp (-m x)`, rescaling by `√n`, and a certified
  numerical bound on the BHH-type integral (≈ 0.9240 < 0.926), plus `O(1)` error terms.

-/

noncomputable section
namespace BHH

open scoped Classical

/-- The law of `n` independent uniform points in the unit square. -/
def μ (n : ℕ) : Measure (Fin n → Pt) :=
  Measure.pi fun _ : Fin n => volume.restrict unitSquare

/-- Horizontal coordinate. -/
def xc (q : Pt) : ℝ := q 0

/-- Vertical coordinate. -/
def yc (q : Pt) : ℝ := q 1

/-- Index of the horizontal strip (out of `k`) containing `q`; points with `y = 1`
go into the top strip. -/
def strip (k : ℕ) (q : Pt) : ℕ := min ⌊yc q * k⌋₊ (k - 1)

/-- `j` immediately follows `i` in the left-to-right order of their common strip. -/
def IsSucc (k : ℕ) {n : ℕ} (p : Fin n → Pt) (i j : Fin n) : Prop :=
  i ≠ j ∧ strip k (p i) = strip k (p j) ∧ xc (p i) < xc (p j) ∧
    ∀ l, l ≠ i → l ≠ j → strip k (p l) = strip k (p i) →
      ¬ (xc (p i) < xc (p l) ∧ xc (p l) < xc (p j))

/-- `i` is the rightmost point of its strip. -/
def IsRightmost (k : ℕ) {n : ℕ} (p : Fin n → Pt) (i : Fin n) : Prop :=
  ∀ l, l ≠ i → strip k (p l) = strip k (p i) → xc (p l) < xc (p i)

/-- `i` is the leftmost point of its strip. -/
def IsLeftmost (k : ℕ) {n : ℕ} (p : Fin n → Pt) (i : Fin n) : Prop :=
  ∀ l, l ≠ i → strip k (p l) = strip k (p i) → xc (p i) < xc (p l)

/-- Total length of the within-strip edges of the strip tour. -/
def succSum (k : ℕ) {n : ℕ} (p : Fin n → Pt) : ℝ :=
  ∑ i, ∑ j, if IsSucc k p i j then dist (p i) (p j) else 0

/-- Gaps between each strip's extreme points and the left/right edges of the square. -/
def endSum (k : ℕ) {n : ℕ} (p : Fin n → Pt) : ℝ :=
  ∑ i, ((if IsRightmost k p i then 1 - xc (p i) else 0) +
        (if IsLeftmost k p i then xc (p i) else 0))

/-! ## Part A — deterministic tour bound -/

theorem tourLength_le_perm {n : ℕ} (p : Fin n → Pt) (σ : Equiv.Perm (Fin n)) :
    tourLength p ≤ ∑ i, dist (p (σ i)) (p (σ (finRotate n i))) :=
  ciInf_le (Finite.bddBelow_range _) σ

theorem volume_unitSquare : volume unitSquare = 1 := by
  have hpres := PiLp.volume_preserving_ofLp (Fin 2)
  have hset : unitSquare =
      (@WithLp.ofLp 2 (Fin 2 → ℝ)) ⁻¹' Set.Icc (fun _ => (0:ℝ)) (fun _ => 1) := by
    ext x
    simp [unitSquare, Set.mem_Icc, Pi.le_def, forall_and]
  rw [hset, hpres.measure_preimage measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi]
  simp

instance isProbabilityMeasure_restrict_unitSquare :
    IsProbabilityMeasure ((volume : Measure Pt).restrict unitSquare) :=
  ⟨by rw [Measure.restrict_apply_univ, volume_unitSquare]⟩

instance isProbabilityMeasure_μ (n : ℕ) : IsProbabilityMeasure (μ n) := by
  unfold μ
  infer_instance


theorem measurableSet_unitSquare : MeasurableSet unitSquare := by
  have h : unitSquare = ⋂ i : Fin 2, (fun x : Pt => x i) ⁻¹' Set.Icc (0:ℝ) 1 := by
    ext x; simp [unitSquare]
  rw [h]
  exact MeasurableSet.iInter fun i => (by fun_prop : Measurable fun x : Pt => x i) measurableSet_Icc

theorem ae_mem_unitSquare (n : ℕ) : ∀ᵐ p ∂(μ n), ∀ i, p i ∈ unitSquare := by
  rw [ae_all_iff]
  intro i
  exact Measure.tendsto_eval_ae_ae.eventually (ae_restrict_mem measurableSet_unitSquare)


theorem continuous_tourLength (n : ℕ) : Continuous (fun p : Fin n → Pt => tourLength p) := by
  have h : (fun p : Fin n → Pt => tourLength p) = fun p => Finset.univ.inf' Finset.univ_nonempty
      (fun σ : Equiv.Perm (Fin n) => ∑ i, dist (p (σ i)) (p (σ (finRotate n i)))) := by
    funext p
    rw [Finset.inf'_univ_eq_ciInf]
    rfl
  rw [h]
  exact Continuous.finset_inf'_apply _ fun σ _ =>
    continuous_finsetSum _ fun i _ => (continuous_apply _).dist (continuous_apply _)

/-- Distance bounded by the sum of coordinate gaps. -/
theorem dist_le_abs_add_abs (a b : Pt) : dist a b ≤ |xc a - xc b| + |yc a - yc b| := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  simp only [Real.dist_eq, sq_abs]
  rw [Real.sqrt_le_left (by positivity)]
  unfold xc yc
  have h1 := abs_nonneg (a 0 - b 0)
  have h2 := abs_nonneg (a 1 - b 1)
  nlinarith [sq_abs (a 0 - b 0), sq_abs (a 1 - b 1)]

theorem coord_mem {q : Pt} (hq : q ∈ unitSquare) : 0 ≤ xc q ∧ xc q ≤ 1 ∧ 0 ≤ yc q ∧ yc q ≤ 1 :=
  ⟨(hq 0).1, (hq 0).2, (hq 1).1, (hq 1).2⟩

theorem dist_le_two {a b : Pt} (ha : a ∈ unitSquare) (hb : b ∈ unitSquare) : dist a b ≤ 2 := by
  obtain ⟨a1, a2, a3, a4⟩ := coord_mem ha
  obtain ⟨b1, b2, b3, b4⟩ := coord_mem hb
  refine (dist_le_abs_add_abs a b).trans ?_
  have : |xc a - xc b| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  have : |yc a - yc b| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  linarith

theorem tourLength_nonneg {n : ℕ} (p : Fin n → Pt) : 0 ≤ tourLength p :=
  le_ciInf fun _ => Finset.sum_nonneg fun _ _ => dist_nonneg

theorem tourLength_le_two_mul {n : ℕ} (p : Fin n → Pt) (hp : ∀ i, p i ∈ unitSquare) :
    tourLength p ≤ 2 * n := by
  refine (tourLength_le_perm p 1).trans ?_
  calc ∑ i, dist (p ((1 : Equiv.Perm (Fin n)) i)) (p ((1 : Equiv.Perm (Fin n)) (finRotate n i)))
      ≤ ∑ _i : Fin n, (2 : ℝ) := Finset.sum_le_sum fun _ _ => dist_le_two (hp _) (hp _)
    _ = 2 * n := by simp [mul_comm]

theorem integrable_tourLength (n : ℕ) : Integrable (fun p : Fin n → Pt => tourLength p) (μ n) := by
  refine Integrable.of_bound (continuous_tourLength n).aestronglyMeasurable (2 * n) ?_
  filter_upwards [ae_mem_unitSquare n] with p hp
  rw [Real.norm_eq_abs, abs_of_nonneg (tourLength_nonneg p)]
  exact tourLength_le_two_mul p hp

/-! ### The serpentine strip tour -/

section StripTour

variable (k : ℕ) {n : ℕ} (p : Fin n → Pt)

/-- Contribution of `i` to `succSum`. -/
def sf (i : Fin n) : ℝ := ∑ j, if IsSucc k p i j then dist (p i) (p j) else 0

/-- Contribution of `i` to `endSum`. -/
def ef (i : Fin n) : ℝ :=
  (if IsRightmost k p i then 1 - xc (p i) else 0) + (if IsLeftmost k p i then xc (p i) else 0)

/-- Length of the open path visiting the list in order. -/
def pathLen : List (Fin n) → ℝ
  | a :: b :: t => dist (p a) (p b) + pathLen (b :: t)
  | _ => 0

/-- The points of strip `m`, sorted by increasing `x`. -/
def blk (m : ℕ) : List (Fin n) :=
  (Finset.univ.filter fun i => strip k (p i) = m).toList.mergeSort
    (fun a b => decide (xc (p a) ≤ xc (p b)))

/-- The serpentine tour through strips `0, …, m-1`; the flag records whether the last
point is the rightmost point of its strip (so the next block is traversed right to left). -/
def build : ℕ → List (Fin n) × Bool
  | 0 => ([], false)
  | m + 1 =>
    if blk k p m = [] then build m
    else if (build m).2 then ((build m).1 ++ (blk k p m).reverse, false)
    else ((build m).1 ++ blk k p m, true)

/-- Within-strip weight of strip `m`. -/
def W (m : ℕ) : ℝ := ∑ i ∈ Finset.univ.filter (fun i => strip k (p i) = m), sf k p i

/-- End-gap weight of strip `m`. -/
def Em (m : ℕ) : ℝ := ∑ i ∈ Finset.univ.filter (fun i => strip k (p i) = m), ef k p i

end StripTour

section StripLemmas

variable {k : ℕ} {n : ℕ} {p : Fin n → Pt}

theorem sf_nonneg (i : Fin n) : 0 ≤ sf k p i :=
  Finset.sum_nonneg fun j _ => by split_ifs <;> simp [dist_nonneg]

theorem ef_nonneg (hp : ∀ i, p i ∈ unitSquare) (i : Fin n) : 0 ≤ ef k p i := by
  obtain ⟨h1, h2, -, -⟩ := coord_mem (hp i)
  unfold ef
  split_ifs <;> linarith

theorem W_nonneg (m : ℕ) : 0 ≤ W k p m := Finset.sum_nonneg fun i _ => sf_nonneg i

theorem Em_nonneg (hp : ∀ i, p i ∈ unitSquare) (m : ℕ) : 0 ≤ Em k p m :=
  Finset.sum_nonneg fun i _ => ef_nonneg hp i

theorem ef_le_Em (hp : ∀ i, p i ∈ unitSquare) {i : Fin n} {m : ℕ} (hi : strip k (p i) = m) :
    ef k p i ≤ Em k p m :=
  Finset.single_le_sum (f := ef k p) (fun j _ => ef_nonneg hp j) (by simpa using hi)

theorem pathLen_single (a : Fin n) : pathLen p [a] = 0 := rfl

theorem pathLen_cons_cons (a b : Fin n) (t : List (Fin n)) :
    pathLen p (a :: b :: t) = dist (p a) (p b) + pathLen p (b :: t) := rfl

theorem pathLen_append {L B : List (Fin n)} {ℓ h : Fin n} (hL : L.getLast? = some ℓ)
    (hB : B.head? = some h) :
    pathLen p (L ++ B) = pathLen p L + dist (p ℓ) (p h) + pathLen p B := by
  induction L with
  | nil => simp at hL
  | cons a t ih =>
    cases t with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hL
      subst hL
      obtain ⟨B', rfl⟩ := List.head?_eq_some_iff.1 hB
      show pathLen p (a :: h :: B') = pathLen p [a] + dist (p a) (p h) + pathLen p (h :: B')
      rw [pathLen_cons_cons, pathLen_single]
      ring
    | cons b t' =>
      have hL' : (b :: t').getLast? = some ℓ := by
        rw [List.getLast?_cons_cons] at hL
        exact hL
      rw [List.cons_append, List.cons_append, pathLen_cons_cons, ← List.cons_append, ih hL',
        pathLen_cons_cons]
      ring

theorem pathLen_reverse (l : List (Fin n)) : pathLen p l.reverse = pathLen p l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    cases t with
    | nil => rfl
    | cons b t' =>
      rw [List.reverse_cons, pathLen_append (ℓ := b) (h := a) (by simp) rfl, ih,
        pathLen_single, pathLen_cons_cons, dist_comm]
      ring

theorem dist_le_sf {i j : Fin n} (h : IsSucc k p i j) : dist (p i) (p j) ≤ sf k p i := by
  have := Finset.single_le_sum (f := fun j => if IsSucc k p i j then dist (p i) (p j) else 0)
    (fun j _ => by split_ifs <;> simp [dist_nonneg]) (Finset.mem_univ j)
  simp only [if_pos h] at this
  exact this

theorem pathLen_le_chain : ∀ l : List (Fin n), l.Nodup → l.IsChain (IsSucc k p) →
    pathLen p l ≤ ∑ i ∈ l.toFinset, sf k p i
  | [], _, _ => by simp [pathLen]
  | [a], _, _ => by
    rw [pathLen_single]
    exact Finset.sum_nonneg fun i _ => sf_nonneg i
  | a :: b :: t, hnd, hch => by
    rw [List.isChain_cons_cons] at hch
    have hna : a ∉ (b :: t).toFinset := by
      rw [List.mem_toFinset]
      exact (List.nodup_cons.1 hnd).1
    rw [pathLen_cons_cons, List.toFinset_cons, Finset.sum_insert hna]
    have h1 := pathLen_le_chain (b :: t) (List.nodup_cons.1 hnd).2 hch.2
    have h2 := dist_le_sf hch.1
    linarith

theorem mem_blk {m : ℕ} {i : Fin n} : i ∈ blk k p m ↔ strip k (p i) = m := by
  simp [blk, List.mem_mergeSort]

theorem blk_nodup (m : ℕ) : (blk k p m).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.2 (Finset.nodup_toList _)

theorem blk_sorted (hx : Function.Injective fun i => xc (p i)) (m : ℕ) :
    (blk k p m).Pairwise (fun a b => xc (p a) < xc (p b)) := by
  have h1 := List.pairwise_mergeSort (le := fun a b => decide (xc (p a) ≤ xc (p b)))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; linarith)
    (fun a b => by simpa using le_total _ _)
    (Finset.univ.filter fun i => strip k (p i) = m).toList
  have h2 := blk_nodup (k := k) (p := p) m
  unfold blk at h2 ⊢
  refine (h1.and h2).imp fun {a b} hab => ?_
  obtain ⟨hle, hne⟩ := hab
  simp only [decide_eq_true_eq] at hle
  exact lt_of_le_of_ne hle fun h => hne (hx h)

theorem blk_chain (hx : Function.Injective fun i => xc (p i)) (m : ℕ) :
    (blk k p m).IsChain (IsSucc k p) := by
  rw [List.isChain_iff_forall_rel_of_append_cons_cons]
  intro a b l₁ l₂ heq
  have hs := blk_sorted (k := k) hx m
  have ha : a ∈ blk k p m := by rw [heq]; simp
  have hb : b ∈ blk k p m := by rw [heq]; simp
  rw [mem_blk] at ha hb
  rw [heq, List.pairwise_append, List.pairwise_cons, List.pairwise_cons] at hs
  have hab : xc (p a) < xc (p b) := hs.2.1.1 b (by simp)
  refine ⟨fun h => by subst h; exact lt_irrefl _ hab, ha.trans hb.symm, hab, ?_⟩
  intro l hla hlb hls ⟨h1, h2⟩
  have hl : l ∈ blk k p m := by rw [mem_blk, hls, ha]
  rw [heq] at hl
  simp only [List.mem_append, List.mem_cons] at hl
  rcases hl with hl | rfl | rfl | hl
  · have := hs.2.2 l hl a (by simp)
    linarith
  · exact hla rfl
  · exact hlb rfl
  · have := hs.2.1.2.1 l hl
    linarith

theorem blk_head_leftmost (hx : Function.Injective fun i => xc (p i)) {m : ℕ} {h : Fin n}
    (hh : (blk k p m).head? = some h) : IsLeftmost k p h := by
  obtain ⟨t, ht⟩ := List.head?_eq_some_iff.1 hh
  have hs := blk_sorted (k := k) hx m
  rw [ht, List.pairwise_cons] at hs
  have hhm : strip k (p h) = m := mem_blk.1 (by rw [ht]; simp)
  intro l hl hls
  have hlb : l ∈ blk k p m := mem_blk.2 (hls.trans hhm)
  rw [ht] at hlb
  rcases List.mem_cons.1 hlb with rfl | hlt
  · exact absurd rfl hl
  · exact hs.1 l hlt

theorem blk_last_rightmost (hx : Function.Injective fun i => xc (p i)) {m : ℕ} {r : Fin n}
    (hr : (blk k p m).getLast? = some r) : IsRightmost k p r := by
  obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.1 hr
  have hs := blk_sorted (k := k) hx m
  rw [hys, List.pairwise_append] at hs
  have hrm : strip k (p r) = m := mem_blk.1 (by rw [hys]; simp)
  intro l hl hls
  have hlb : l ∈ blk k p m := mem_blk.2 (hls.trans hrm)
  rw [hys] at hlb
  rcases List.mem_append.1 hlb with hly | hlr
  · exact hs.2.2 l hly r (by simp)
  · simp only [List.mem_singleton] at hlr
    exact absurd hlr hl

theorem blk_toFinset (m : ℕ) :
    (blk k p m).toFinset = Finset.univ.filter (fun i => strip k (p i) = m) := by
  ext i
  simp [mem_blk]

theorem pathLen_blk_le (hx : Function.Injective fun i => xc (p i)) (m : ℕ) :
    pathLen p (blk k p m) ≤ W k p m := by
  have := pathLen_le_chain (blk k p m) (blk_nodup m) (blk_chain hx m)
  rwa [blk_toFinset] at this

theorem strip_lt (hk : 1 ≤ k) (q : Pt) : strip k q < k :=
  lt_of_le_of_lt (min_le_right _ _) (by omega)

theorem strip_bounds (hk : 1 ≤ k) {q : Pt} (hq : q ∈ unitSquare) :
    (strip k q : ℝ) ≤ yc q * k ∧ yc q * k ≤ (strip k q : ℝ) + 1 := by
  obtain ⟨-, -, hy0, hy1⟩ := coord_mem hq
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have h0 : 0 ≤ yc q * k := by positivity
  unfold strip
  rcases le_total ⌊yc q * k⌋₊ (k - 1) with h | h
  · rw [min_eq_left h]
    exact ⟨Nat.floor_le h0, (Nat.lt_floor_add_one _).le⟩
  · rw [min_eq_right h]
    have hk1 : ((k - 1 : ℕ) : ℝ) = k - 1 := by
      rw [Nat.cast_sub hk, Nat.cast_one]
    have hfl : ((k - 1 : ℕ) : ℝ) ≤ ⌊yc q * k⌋₊ := by exact_mod_cast h
    rw [hk1] at hfl ⊢
    have := Nat.floor_le h0
    constructor
    · linarith
    · nlinarith

/-- Cost of a strip-change edge. -/
theorem conn_le (hk : 1 ≤ k) (hp : ∀ i, p i ∈ unitSquare) {ℓ h : Fin n} {m : ℕ}
    (hℓ : strip k (p ℓ) < m) (hh : strip k (p h) = m)
    (hside : (IsRightmost k p ℓ ∧ IsRightmost k p h) ∨ (IsLeftmost k p ℓ ∧ IsLeftmost k p h)) :
    dist (p ℓ) (p h) ≤ ef k p ℓ + ef k p h + ((m : ℝ) + 1 - strip k (p ℓ)) / k := by
  refine (dist_le_abs_add_abs _ _).trans (add_le_add ?_ ?_)
  · obtain ⟨a0, a1, -, -⟩ := coord_mem (hp ℓ)
    obtain ⟨b0, b1, -, -⟩ := coord_mem (hp h)
    unfold ef
    rcases hside with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [if_pos h1, if_pos h2]
      have e1 : 0 ≤ (if IsLeftmost k p ℓ then xc (p ℓ) else 0) := by split_ifs <;> linarith
      have e2 : 0 ≤ (if IsLeftmost k p h then xc (p h) else 0) := by split_ifs <;> linarith
      rw [abs_le]
      constructor <;> linarith
    · rw [if_pos h1, if_pos h2]
      have e1 : 0 ≤ (if IsRightmost k p ℓ then 1 - xc (p ℓ) else 0) := by
        split_ifs <;> linarith
      have e2 : 0 ≤ (if IsRightmost k p h then 1 - xc (p h) else 0) := by
        split_ifs <;> linarith
      rw [abs_le]
      constructor <;> linarith
  · have hkR : (0:ℝ) < k := by exact_mod_cast hk
    obtain ⟨l1, l2⟩ := strip_bounds hk (hp ℓ)
    obtain ⟨h1, h2⟩ := strip_bounds hk (hp h)
    rw [hh] at h1 h2
    have hm : (strip k (p ℓ) : ℝ) + 1 ≤ m := by exact_mod_cast hℓ
    rw [le_div_iff₀ hkR]
    have : |yc (p ℓ) - yc (p h)| * k = |yc (p ℓ) * k - yc (p h) * k| := by
      rw [← sub_mul, abs_mul, abs_of_pos hkR]
    rw [this, abs_le]
    constructor <;> linarith

/-- One step of the construction: the bookkeeping inequality. -/
theorem step_bound {S A B dl wm em e2 eh el sl m kk : ℝ}
    (hL : A + el ≤ S + (sl + m) / kk) (hconn : dl ≤ el + eh + (m + 1 - sl) / kk)
    (hB : B ≤ wm) (heh : eh ≤ em) (he : e2 ≤ em) :
    A + dl + B + e2 ≤ S + (wm + 2 * em) + (m + (m + 1)) / kk := by
  have : (sl + m) / kk + (m + 1 - sl) / kk = (m + (m + 1)) / kk := by ring
  linarith

theorem build_spec (hk : 1 ≤ k) (hp : ∀ i, p i ∈ unitSquare)
    (hx : Function.Injective fun i => xc (p i)) (m : ℕ) :
    (∀ i, i ∈ (build k p m).1 ↔ strip k (p i) < m) ∧ (build k p m).1.Nodup ∧
      ∀ ℓ, (build k p m).1.getLast? = some ℓ → strip k (p ℓ) < m ∧
        ((build k p m).2 = true → IsRightmost k p ℓ) ∧
        ((build k p m).2 = false → IsLeftmost k p ℓ) ∧
        pathLen p (build k p m).1 + ef k p ℓ ≤
          ∑ σ ∈ Finset.range m, (W k p σ + 2 * Em k p σ) + ((strip k (p ℓ) : ℝ) + m) / k := by
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  induction m with
  | zero => simp [build]
  | succ m ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    have hWE : 0 ≤ W k p m + 2 * Em k p m := by
      have := W_nonneg (k := k) (p := p) m
      have := Em_nonneg (k := k) hp m
      linarith
    have hS : 0 ≤ ∑ σ ∈ Finset.range m, (W k p σ + 2 * Em k p σ) :=
      Finset.sum_nonneg fun σ _ => by
        have := W_nonneg (k := k) (p := p) σ
        have := Em_nonneg (k := k) hp σ
        linarith
    rw [Finset.sum_range_succ]
    push_cast
    by_cases hB : blk k p m = []
    · -- empty strip: nothing changes
      have hnone : ∀ i, strip k (p i) ≠ m := fun i hi => by
        have : i ∈ blk k p m := mem_blk.2 hi
        rw [hB] at this
        simp at this
      simp only [build, if_pos hB]
      refine ⟨fun i => (ih1 i).trans ⟨fun h => by omega, fun h => ?_⟩, ih2, fun ℓ hℓ => ?_⟩
      · have := hnone i
        omega
      obtain ⟨a1, a2, a3, a4⟩ := ih3 ℓ hℓ
      refine ⟨by omega, a2, a3, ?_⟩
      have : ((strip k (p ℓ) : ℝ) + m) / k ≤ ((strip k (p ℓ) : ℝ) + (m + 1)) / k :=
        div_le_div_of_nonneg_right (by linarith) hkR.le
      linarith
    · obtain ⟨h0, hh0⟩ : ∃ h0, (blk k p m).head? = some h0 := by
        cases hb : blk k p m with
        | nil => exact absurd hb hB
        | cons a t => exact ⟨a, rfl⟩
      obtain ⟨r0, hr0⟩ : ∃ r0, (blk k p m).getLast? = some r0 := by
        cases hb : (blk k p m).getLast? with
        | none => exact absurd (List.getLast?_eq_none_iff.1 hb) hB
        | some r => exact ⟨r, rfl⟩
      have hh0m : strip k (p h0) = m := mem_blk.1 (List.mem_of_mem_head? hh0)
      have hr0m : strip k (p r0) = m := mem_blk.1 (List.mem_of_mem_getLast? hr0)
      have hdisj : ∀ i, i ∈ (build k p m).1 → i ∉ blk k p m := fun i hi hb => by
        have := (ih1 i).1 hi
        rw [mem_blk] at hb
        omega
      have hBl := pathLen_blk_le (k := k) hx m
      have hEh := ef_le_Em (k := k) hp hh0m
      have hEr := ef_le_Em (k := k) hp hr0m
      have hpos : (0:ℝ) ≤ ((m : ℝ) + (m + 1)) / k := by positivity
      have hEm0 := Em_nonneg (k := k) hp m
      by_cases hside : (build k p m).2 = true
      · -- last point is rightmost: traverse strip `m` right to left
        simp only [build, if_neg hB, if_pos hside]
        refine ⟨fun i => ?_, ?_, fun ℓ' hℓ' => ?_⟩
        · rw [List.mem_append, List.mem_reverse, ih1, mem_blk]
          omega
        · rw [List.nodup_append]
          refine ⟨ih2, List.nodup_reverse.2 (blk_nodup m), fun a ha b hb => ?_⟩
          rw [List.mem_reverse] at hb
          exact fun hab => hdisj a ha (hab ▸ hb)
        · have hℓ'eq : ℓ' = h0 := by
            have : (blk k p m).reverse.getLast? = some h0 := by
              rw [List.getLast?_reverse]; exact hh0
            rw [List.getLast?_append, this] at hℓ'
            simpa using hℓ'.symm
          subst hℓ'eq
          refine ⟨by omega, fun h => absurd h (by simp), fun _ => blk_head_leftmost hx hh0, ?_⟩
          rw [hh0m]
          cases hL : (build k p m).1.getLast? with
          | none =>
            rw [List.getLast?_eq_none_iff] at hL
            rw [hL, List.nil_append, pathLen_reverse]
            linarith
          | some ℓ =>
            obtain ⟨a1, a2, -, a4⟩ := ih3 ℓ hL
            have hhd : (blk k p m).reverse.head? = some r0 := by
              rw [List.head?_reverse]; exact hr0
            rw [pathLen_append hL hhd, pathLen_reverse]
            have hc := conn_le hk hp a1 hr0m (Or.inl ⟨a2 hside, blk_last_rightmost hx hr0⟩)
            exact step_bound a4 hc hBl hEr hEh
      · -- last point is leftmost (or no point yet): traverse strip `m` left to right
        have hside' : (build k p m).2 = false := by simpa using hside
        simp only [build, if_neg hB, if_neg hside]
        refine ⟨fun i => ?_, ?_, fun ℓ' hℓ' => ?_⟩
        · rw [List.mem_append, ih1, mem_blk]
          omega
        · rw [List.nodup_append]
          exact ⟨ih2, blk_nodup m, fun a ha b hb hab => hdisj a ha (hab ▸ hb)⟩
        · have hℓ'eq : ℓ' = r0 := by
            rw [List.getLast?_append, hr0] at hℓ'
            simpa using hℓ'.symm
          subst hℓ'eq
          refine ⟨by omega, fun _ => blk_last_rightmost hx hr0, fun h => absurd h (by simp), ?_⟩
          rw [hr0m]
          cases hL : (build k p m).1.getLast? with
          | none =>
            rw [List.getLast?_eq_none_iff] at hL
            rw [hL, List.nil_append]
            linarith
          | some ℓ =>
            obtain ⟨a1, -, a3, a4⟩ := ih3 ℓ hL
            rw [pathLen_append hL hh0]
            have hc := conn_le hk hp a1 hh0m (Or.inr ⟨a3 hside', blk_head_leftmost hx hh0⟩)
            exact step_bound a4 hc hBl hEh hEr

/-- Consecutive distances along a list. -/
theorem sum_consec (d : Fin n) : ∀ l : List (Fin n),
    ∑ i ∈ Finset.range (l.length - 1), dist (p (l.getD i d)) (p (l.getD (i + 1) d)) =
      pathLen p l
  | [] => by simp [pathLen]
  | [a] => by simp [pathLen]
  | a :: b :: t => by
    have ih := sum_consec d (b :: t)
    simp only [List.length_cons, Nat.add_sub_cancel] at ih ⊢
    rw [Finset.sum_range_succ', pathLen_cons_cons, ← ih]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring

end StripLemmas

/-- **A1.** The serpentine strip tour: within each nonempty strip visit points by
increasing or decreasing `x` (alternating between consecutive nonempty strips), then
close the tour. The within-strip edges are exactly the `IsSucc` pairs. Each connection
between strips costs at most the two end gaps plus the vertical distance, which totals
at most 2 over the whole tour. The closing edge is at most `√2 < 2`. -/
theorem tourLength_le_strip (k n : ℕ) (hk : 1 ≤ k) (p : Fin n → Pt)
    (hp : ∀ i, p i ∈ unitSquare) (hx : Function.Injective fun i => xc (p i)) :
    tourLength p ≤ succSum k p + 2 * endSum k p + 4 := by
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have hS0 : 0 ≤ succSum k p := Finset.sum_nonneg fun i _ => sf_nonneg i
  have hE0 : 0 ≤ endSum k p := Finset.sum_nonneg fun i _ => ef_nonneg hp i
  have hmaps : ∀ i ∈ (Finset.univ : Finset (Fin n)), strip k (p i) ∈ Finset.range k :=
    fun i _ => Finset.mem_range.2 (strip_lt hk _)
  have hWsum : ∑ σ ∈ Finset.range k, W k p σ = succSum k p :=
    Finset.sum_fiberwise_of_maps_to hmaps (sf k p)
  have hEsum : ∑ σ ∈ Finset.range k, Em k p σ = endSum k p :=
    Finset.sum_fiberwise_of_maps_to hmaps (ef k p)
  have hsplit : ∑ σ ∈ Finset.range k, (W k p σ + 2 * Em k p σ) =
      succSum k p + 2 * endSum k p := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hWsum, hEsum]
  obtain ⟨h1, h2, h3⟩ := build_spec hk hp hx k
  set L := (build k p k).1 with hLdef
  have hall : ∀ i, i ∈ L := fun i => (h1 i).2 (strip_lt hk _)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have := tourLength_le_perm p 1
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at this
    linarith
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have hlen : L.length = N + 1 := by
    rw [← List.toFinset_card_of_nodup h2]
    have : L.toFinset = Finset.univ := Finset.eq_univ_iff_forall.2 fun i => by simpa using hall i
    rw [this, Finset.card_univ, Fintype.card_fin]
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, L.getLast? = some ℓ := by
    cases hb : L.getLast? with
    | none =>
      rw [List.getLast?_eq_none_iff] at hb
      rw [hb] at hlen
      simp at hlen
    | some r => exact ⟨r, rfl⟩
  obtain ⟨a1, -, -, a4⟩ := h3 ℓ hℓ
  have hef := ef_nonneg (k := k) hp ℓ
  have hpot : ((strip k (p ℓ) : ℝ) + k) / k ≤ 2 := by
    rw [div_le_iff₀ hkR]
    have : (strip k (p ℓ) : ℝ) + 1 ≤ k := by exact_mod_cast a1
    linarith
  -- the permutation listing `L`
  let e := List.Nodup.getEquivOfForallMemList L h2 hall
  let σ : Equiv.Perm (Fin (N + 1)) := (finCongr hlen.symm).trans e
  have hσ : ∀ j : Fin (N + 1), σ j = L.getD j 0 := by
    intro j
    simp only [σ, e, Equiv.trans_apply, List.Nodup.getEquivOfForallMemList_apply, finCongr_apply,
      List.get_eq_getElem, Fin.val_cast]
    rw [List.getD_eq_getElem]
  have hcyc : ∑ i, dist (p (σ i)) (p (σ (finRotate (N + 1) i))) =
      pathLen p L + dist (p (L.getD N 0)) (p (L.getD 0 0)) := by
    rw [Fin.sum_univ_castSucc, finRotate_last, ← sum_consec (0 : Fin (N + 1)) L, hlen,
      Nat.add_sub_cancel, ← Fin.sum_univ_eq_sum_range]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [finRotate_apply, hσ, hσ]
      congr 3
      simp
    · rw [hσ, hσ]
      simp
  have hclose := dist_le_two (hp (L.getD N 0)) (hp (L.getD 0 0))
  have := tourLength_le_perm p σ
  rw [hcyc] at this
  linarith


/-! ## Part B machinery -/

/-- The single-point law. -/
abbrev ν : Measure Pt := volume.restrict unitSquare

theorem μ_succ (m : ℕ) : μ (m + 1) = Measure.pi fun _ : Fin (m + 1) => ν := rfl

/-- Split off coordinate `0`. -/
theorem lintegral_μ_succ (m : ℕ) (f : Pt → (Fin m → Pt) → ENNReal)
    (hf : Measurable (Function.uncurry f)) :
    ∫⁻ p, f (p 0) (Fin.tail p) ∂(μ (m + 1)) = ∫⁻ a, ∫⁻ r, f a r ∂(μ m) ∂ν := by
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => ν) 0
  have h1 : (fun p : Fin (m + 1) → Pt => f (p 0) (Fin.tail p)) =
      fun p => Function.uncurry f ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => Pt) 0) p) := by
    funext p
    simp [Function.uncurry, MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv]
  rw [μ_succ, h1, hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _),
    lintegral_prod _ hf.aemeasurable]
  rfl

/-- Integral of a product of a fixed function over independent coordinates. -/
theorem lintegral_μ_prod (g : Pt → ENNReal) (hg : Measurable g) :
    ∀ m : ℕ, ∫⁻ r, ∏ l, g (r l) ∂(μ m) = (∫⁻ a, g a ∂ν) ^ m
  | 0 => by simp only [Fin.prod_univ_zero, pow_zero, lintegral_one, measure_univ]
  | m + 1 => by
    have key := lintegral_μ_succ m (fun a r => g a * ∏ l, g (r l))
      (hg.comp measurable_fst |>.mul <| Finset.measurable_prod _ fun l _ =>
        hg.comp ((measurable_pi_apply l).comp measurable_snd))
    have h : (fun r : Fin (m + 1) → Pt => ∏ l, g (r l)) =
        fun r => g (r 0) * ∏ l, g (Fin.tail r l) := by
      funext r; rw [Fin.prod_univ_succ]; rfl
    rw [h, key]
    have hprod : Measurable fun r : Fin m → Pt => ∏ l, g (r l) :=
      Finset.measurable_prod _ fun l _ => hg.comp (measurable_pi_apply l)
    have e1 : ∀ a, ∫⁻ r, g a * ∏ l, g (r l) ∂(μ m) = g a * (∫⁻ a, g a ∂ν) ^ m := fun a => by
      rw [lintegral_const_mul _ hprod, lintegral_μ_prod g hg m]
    simp_rw [e1]
    rw [lintegral_mul_const _ hg, pow_succ']

/-- Relabelling the points. -/
theorem lintegral_μ_comp_perm (n : ℕ) (π : Equiv.Perm (Fin n)) (f : (Fin n → Pt) → ENNReal) :
    ∫⁻ p, f (p ∘ π) ∂(μ n) = ∫⁻ p, f p ∂(μ n) := by
  have hmp := measurePreserving_piCongrLeft (fun _ : Fin n => ν) π.symm
  have h : (fun p : Fin n → Pt => f (p ∘ π)) =
      fun p => f ((MeasurableEquiv.piCongrLeft (fun _ : Fin n => Pt) π.symm) p) := by
    funext p
    congr 1
    funext i
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  rw [h]
  exact hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) f

theorem measurable_xc : Measurable xc := by unfold xc; fun_prop
theorem measurable_yc : Measurable yc := by unfold yc; fun_prop

theorem measurable_strip (k : ℕ) : Measurable (strip k) := by
  have : strip k = (fun j : ℕ => min j (k - 1)) ∘ (fun q => ⌊yc q * k⌋₊) := rfl
  rw [this]
  exact measurable_from_nat.comp ((measurable_yc.mul_const _).nat_floor)

/-- The gap region between `a` and `b` in the strip of `a`. -/
def Rg (k : ℕ) (a b : Pt) : Set Pt :=
  {q | strip k q = strip k a ∧ xc a < xc q ∧ xc q < xc b}

/-- The pair weight. -/
def Fp (k : ℕ) (a b : Pt) : ℝ :=
  if strip k a = strip k b ∧ xc a < xc b then dist a b else 0

/-- One term of `succSum`. -/
def termS (k : ℕ) {n : ℕ} (p : Fin n → Pt) (i j : Fin n) : ℝ :=
  if IsSucc k p i j then dist (p i) (p j) else 0

theorem isSucc_comp (k : ℕ) {n : ℕ} (p : Fin n → Pt) (π : Equiv.Perm (Fin n)) (a b : Fin n) :
    IsSucc k (p ∘ π) a b ↔ IsSucc k p (π a) (π b) := by
  unfold IsSucc
  simp only [Function.comp_apply, ne_eq, EmbeddingLike.apply_eq_iff_eq]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, h3, fun l hl1 hl2 hs => ?_⟩
    have := h4 (π.symm l) (by rintro rfl; simp at hl1) (by rintro rfl; simp at hl2)
    simpa using this (by simpa using hs)
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, h3, fun l hl1 hl2 hs => h4 (π l) (by simpa using hl1) (by simpa using hl2) hs⟩

theorem termS_comp (k : ℕ) {n : ℕ} (p : Fin n → Pt) (π : Equiv.Perm (Fin n)) (a b : Fin n) :
    termS k (p ∘ π) a b = termS k p (π a) (π b) := by
  simp [termS, isSucc_comp]

theorem isSucc_01_iff (k m : ℕ) (p : Fin (m + 2) → Pt) :
    IsSucc k p 0 1 ↔ (strip k (p 0) = strip k (p 1) ∧ xc (p 0) < xc (p 1)) ∧
      ∀ l : Fin m, p l.succ.succ ∉ Rg k (p 0) (p 1) := by
  unfold IsSucc Rg
  simp only [Set.mem_setOf_eq, not_and]
  constructor
  · rintro ⟨-, h2, h3, h4⟩
    refine ⟨⟨h2, h3⟩, fun l hs h5 h6 => ?_⟩
    exact h4 l.succ.succ (Fin.succ_ne_zero _) (by simp [Fin.ext_iff]) hs h5 h6
  · rintro ⟨⟨h2, h3⟩, h4⟩
    refine ⟨by simp, h2, h3, fun l hl0 hl1 hs h5 h6 => ?_⟩
    obtain ⟨l', rfl⟩ := Fin.exists_succ_eq.2 hl0
    obtain ⟨l'', rfl⟩ := Fin.exists_succ_eq.2 (by rintro rfl; exact hl1 rfl : l' ≠ 0)
    exact h4 l'' hs h5 h6

theorem ofReal_termS_01 (k m : ℕ) (p : Fin (m + 2) → Pt) :
    ENNReal.ofReal (termS k p 0 1) = ENNReal.ofReal (Fp k (p 0) (p 1)) *
      ∏ l : Fin m, (Rg k (p 0) (p 1))ᶜ.indicator 1 (p l.succ.succ) := by
  by_cases h : IsSucc k p 0 1
  · have h' := (isSucc_01_iff k m p).1 h
    have hprod : ∏ l : Fin m, (Rg k (p 0) (p 1))ᶜ.indicator (1 : Pt → ENNReal) (p l.succ.succ) = 1 :=
      Finset.prod_eq_one fun l _ => Set.indicator_of_mem (h'.2 l) _
    simp [termS, h, Fp, h'.1, hprod]
  · rw [isSucc_01_iff] at h
    simp only [termS, (isSucc_01_iff k m p).not.2 h, if_false, ENNReal.ofReal_zero]
    by_cases h1 : strip k (p 0) = strip k (p 1) ∧ xc (p 0) < xc (p 1)
    · push Not at h
      obtain ⟨l, hl⟩ := h h1
      rw [Finset.prod_eq_zero (Finset.mem_univ l)]
      · simp
      · simp [Set.indicator_of_notMem (Set.notMem_compl_iff.2 hl)]
    · simp [Fp, h1]

theorem measurableSet_strip_eq (k : ℕ) {α : Type*} [MeasurableSpace α] {f g : α → Pt}
    (hf : Measurable f) (hg : Measurable g) :
    MeasurableSet {x | strip k (f x) = strip k (g x)} :=
  measurableSet_eq_fun ((measurable_strip k).comp hf) ((measurable_strip k).comp hg)

theorem measurable_Fp (k : ℕ) : Measurable (fun x : Pt × Pt => ENNReal.ofReal (Fp k x.1 x.2)) := by
  unfold Fp
  refine ENNReal.measurable_ofReal.comp (Measurable.ite ?_ (by fun_prop) measurable_const)
  exact (measurableSet_strip_eq k measurable_fst measurable_snd).inter
    (measurableSet_lt (measurable_xc.comp measurable_fst) (measurable_xc.comp measurable_snd))

theorem measurableSet_Rg (k : ℕ) :
    MeasurableSet {x : (Pt × Pt) × Pt | x.2 ∈ Rg k x.1.1 x.1.2} := by
  unfold Rg
  simp only [Set.mem_setOf_eq]
  refine (measurableSet_strip_eq k measurable_snd (measurable_fst.comp measurable_fst)).inter
    ((measurableSet_lt (measurable_xc.comp (measurable_fst.comp measurable_fst))
      (measurable_xc.comp measurable_snd)).inter
    (measurableSet_lt (measurable_xc.comp measurable_snd)
      (measurable_xc.comp (measurable_snd.comp measurable_fst))))

theorem measurable_ind (k : ℕ) :
    Measurable (fun x : (Pt × Pt) × Pt => (Rg k x.1.1 x.1.2)ᶜ.indicator (1 : Pt → ENNReal) x.2) := by
  have h : (fun x : (Pt × Pt) × Pt => (Rg k x.1.1 x.1.2)ᶜ.indicator (1 : Pt → ENNReal) x.2) =
      {x : (Pt × Pt) × Pt | x.2 ∈ Rg k x.1.1 x.1.2}ᶜ.indicator 1 := by
    funext x
    by_cases hx : x.2 ∈ Rg k x.1.1 x.1.2 <;> simp [Set.indicator, hx]
  rw [h]
  exact measurable_one.indicator (measurableSet_Rg k).compl

theorem measurableSet_Rg_section (k : ℕ) (a b : Pt) : MeasurableSet (Rg k a b) := by
  have := (measurableSet_Rg k).preimage (measurable_const.prodMk measurable_id :
    Measurable fun q : Pt => ((a, b), q))
  simpa using this


theorem measurable_Fp' (k : ℕ) {β : Type*} [MeasurableSpace β] {A B : β → Pt}
    (hA : Measurable A) (hB : Measurable B) :
    Measurable fun x => ENNReal.ofReal (Fp k (A x) (B x)) := by
  unfold Fp
  refine ENNReal.measurable_ofReal.comp (Measurable.ite ?_ (hA.dist hB) measurable_const)
  exact (measurableSet_strip_eq k hA hB).inter (measurableSet_lt (measurable_xc.comp hA)
    (measurable_xc.comp hB))

theorem measurable_ind' (k : ℕ) {β : Type*} [MeasurableSpace β] {A B C : β → Pt}
    (hA : Measurable A) (hB : Measurable B) (hC : Measurable C) :
    Measurable fun x => (Rg k (A x) (B x))ᶜ.indicator (1 : Pt → ENNReal) (C x) := by
  have hS : MeasurableSet {x | C x ∈ Rg k (A x) (B x)} := by
    unfold Rg
    simp only [Set.mem_setOf_eq]
    exact (measurableSet_strip_eq k hC hA).inter ((measurableSet_lt (measurable_xc.comp hA)
      (measurable_xc.comp hC)).inter (measurableSet_lt (measurable_xc.comp hC)
      (measurable_xc.comp hB)))
  have h : (fun x => (Rg k (A x) (B x))ᶜ.indicator (1 : Pt → ENNReal) (C x)) =
      {x | C x ∈ Rg k (A x) (B x)}ᶜ.indicator 1 := by
    funext x
    by_cases hx : C x ∈ Rg k (A x) (B x) <;> simp [Set.indicator, hx]
  rw [h]
  exact measurable_one.indicator hS.compl

theorem measurable_pairProd (k m : ℕ) {β : Type*} [MeasurableSpace β] (A B : β → Pt)
    (C : Fin m → β → Pt) (hA : Measurable A) (hB : Measurable B) (hC : ∀ l, Measurable (C l)) :
    Measurable fun x => ENNReal.ofReal (Fp k (A x) (B x)) *
      ∏ l : Fin m, (Rg k (A x) (B x))ᶜ.indicator (1 : Pt → ENNReal) (C l x) :=
  (measurable_Fp' k hA hB).mul (Finset.measurable_prod _ fun l _ => measurable_ind' k hA hB (hC l))

/-- The expectation of one `succSum` term, for the pair `(0, 1)`. -/
theorem lintegral_termS_01 (k m : ℕ) :
    ∫⁻ p, ENNReal.ofReal (termS k p 0 1) ∂(μ (m + 2)) =
      ∫⁻ a, ∫⁻ b, ENNReal.ofReal (Fp k a b) * (ν (Rg k a b)ᶜ) ^ m ∂ν ∂ν := by
  have hfm := measurable_pairProd k m (β := Pt × (Fin (m + 1) → Pt)) (fun x => x.1)
    (fun x => x.2 0) (fun l x => x.2 l.succ) measurable_fst
    ((measurable_pi_apply 0).comp measurable_snd)
    (fun l => (measurable_pi_apply l.succ).comp measurable_snd)
  have h1 : (fun p : Fin (m + 2) → Pt => ENNReal.ofReal (termS k p 0 1)) =
      fun p => (fun (a : Pt) (r : Fin (m + 1) → Pt) => ENNReal.ofReal (Fp k a (r 0)) *
        ∏ l : Fin m, (Rg k a (r 0))ᶜ.indicator (1 : Pt → ENNReal) (r l.succ)) (p 0) (Fin.tail p) := by
    funext p
    rw [ofReal_termS_01]
    rfl
  rw [h1, lintegral_μ_succ (m + 1) (fun (a : Pt) (r : Fin (m + 1) → Pt) =>
    ENNReal.ofReal (Fp k a (r 0)) *
      ∏ l : Fin m, (Rg k a (r 0))ᶜ.indicator (1 : Pt → ENNReal) (r l.succ)) hfm]
  refine lintegral_congr fun a => ?_
  have hgm := measurable_pairProd k m (β := Pt × (Fin m → Pt)) (fun _ => a)
    (fun x => x.1) (fun l x => x.2 l) measurable_const measurable_fst
    (fun l => (measurable_pi_apply l).comp measurable_snd)
  refine (lintegral_μ_succ m (fun (b : Pt) (r : Fin m → Pt) => ENNReal.ofReal (Fp k a b) *
      ∏ l : Fin m, (Rg k a b)ᶜ.indicator (1 : Pt → ENNReal) (r l)) hgm).trans ?_
  refine lintegral_congr fun b => ?_
  have hindb : Measurable ((Rg k a b)ᶜ.indicator (1 : Pt → ENNReal)) :=
    measurable_one.indicator (measurableSet_Rg_section k a b).compl
  have hpm : Measurable fun r : Fin m → Pt => ∏ l, (Rg k a b)ᶜ.indicator (1 : Pt → ENNReal) (r l) :=
    Finset.measurable_prod _ fun l _ => hindb.comp (measurable_pi_apply l)
  rw [lintegral_const_mul _ hpm, lintegral_μ_prod _ hindb m,
    lintegral_indicator_one (measurableSet_Rg_section k a b).compl]

theorem exists_perm_01 {m : ℕ} (i j : Fin (m + 2)) (h : i ≠ j) :
    ∃ π : Equiv.Perm (Fin (m + 2)), π 0 = i ∧ π 1 = j := by
  set j' := Equiv.swap 0 i j with hj'
  have hj'0 : j' ≠ 0 := by
    intro h0
    rw [hj', Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at h0
    exact h h0.symm
  refine ⟨(Equiv.swap 1 j').trans (Equiv.swap 0 i), ?_, ?_⟩
  · simp only [Equiv.trans_apply]
    rw [Equiv.swap_apply_of_ne_of_ne (by simp) hj'0.symm, Equiv.swap_apply_left]
  · simp only [Equiv.trans_apply, Equiv.swap_apply_left]
    rw [hj', Equiv.swap_apply_self]

theorem measurable_termS_01 (k m : ℕ) :
    Measurable fun p : Fin (m + 2) → Pt => ENNReal.ofReal (termS k p 0 1) := by
  have h := measurable_pairProd k m (β := Fin (m + 2) → Pt) (fun p => p 0) (fun p => p 1)
    (fun l p => p l.succ.succ) (measurable_pi_apply 0) (measurable_pi_apply 1)
    (fun l => measurable_pi_apply _)
  have e : (fun p : Fin (m + 2) → Pt => ENNReal.ofReal (termS k p 0 1)) =
      fun p => ENNReal.ofReal (Fp k (p 0) (p 1)) *
        ∏ l : Fin m, (Rg k (p 0) (p 1))ᶜ.indicator (1 : Pt → ENNReal) (p l.succ.succ) := by
    funext p; exact ofReal_termS_01 k m p
  rw [e]; exact h

theorem termS_nonneg (k : ℕ) {n : ℕ} (p : Fin n → Pt) (i j : Fin n) : 0 ≤ termS k p i j := by
  unfold termS; split_ifs <;> simp [dist_nonneg]

theorem termS_self (k : ℕ) {n : ℕ} (p : Fin n → Pt) (i : Fin n) : termS k p i i = 0 := by
  simp [termS, IsSucc]

theorem lintegral_termS_ij (k m : ℕ) (i j : Fin (m + 2)) (hij : i ≠ j) :
    ∫⁻ p, ENNReal.ofReal (termS k p i j) ∂(μ (m + 2)) =
      ∫⁻ p, ENNReal.ofReal (termS k p 0 1) ∂(μ (m + 2)) := by
  obtain ⟨π, h0, h1⟩ := exists_perm_01 i j hij
  have e : ∀ p : Fin (m + 2) → Pt, termS k p i j = termS k (p ∘ π) 0 1 := by
    intro p; rw [termS_comp, h0, h1]
  simp_rw [e]
  exact lintegral_μ_comp_perm _ π (fun p => ENNReal.ofReal (termS k p 0 1))

theorem measurable_termS_ij (k m : ℕ) (i j : Fin (m + 2)) :
    Measurable fun p : Fin (m + 2) → Pt => ENNReal.ofReal (termS k p i j) := by
  by_cases hij : i = j
  · subst hij; simp_rw [termS_self]; exact measurable_const
  · obtain ⟨π, h0, h1⟩ := exists_perm_01 i j hij
    have e : (fun p : Fin (m + 2) → Pt => ENNReal.ofReal (termS k p i j)) =
        (fun p => ENNReal.ofReal (termS k p 0 1)) ∘ (fun p => p ∘ π) := by
      funext p; simp only [Function.comp_apply]; rw [termS_comp, h0, h1]
    rw [e]
    exact (measurable_termS_01 k m).comp (measurable_pi_lambda _ fun l => measurable_pi_apply _)

theorem lintegral_succSum (k m : ℕ) :
    ∫⁻ p, ENNReal.ofReal (succSum k p) ∂(μ (m + 2)) =
      ((m + 2) * (m + 1) : ℕ) * ∫⁻ p, ENNReal.ofReal (termS k p 0 1) ∂(μ (m + 2)) := by
  have e : ∀ p : Fin (m + 2) → Pt, ENNReal.ofReal (succSum k p) =
      ∑ i, ∑ j, ENNReal.ofReal (termS k p i j) := by
    intro p
    show ENNReal.ofReal (∑ i, ∑ j, termS k p i j) = _
    rw [ENNReal.ofReal_sum_of_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => termS_nonneg k p i j]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact ENNReal.ofReal_sum_of_nonneg fun j _ => termS_nonneg k p i j
  simp_rw [e]
  rw [lintegral_finsetSum _ fun i _ =>
    Finset.measurable_sum _ fun j _ => measurable_termS_ij k m i j]
  simp_rw [lintegral_finsetSum _ fun j _ => measurable_termS_ij k m _ j]
  have e2 : ∀ i j : Fin (m + 2), ∫⁻ p, ENNReal.ofReal (termS k p i j) ∂(μ (m + 2)) =
      if i = j then 0 else ∫⁻ p, ENNReal.ofReal (termS k p 0 1) ∂(μ (m + 2)) := by
    intro i j
    split_ifs with h
    · subst h; simp [termS_self]
    · exact lintegral_termS_ij k m i j h
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => e2 i j]
  set c := ∫⁻ p, ENNReal.ofReal (termS k p 0 1) ∂(μ (m + 2))
  have hc : ∀ i : Fin (m + 2), ∑ j, (if i = j then (0 : ENNReal) else c) = ((m + 1 : ℕ) : ENNReal) * c := by
    intro i
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul]
    congr 2
    have : (Finset.univ.filter fun j : Fin (m + 2) => ¬ i = j) = Finset.univ.erase i := by
      ext j; simp [eq_comm]
    rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    rfl
  rw [Finset.sum_congr rfl fun i _ => hc i, Finset.sum_const, nsmul_eq_mul, ← mul_assoc,
    Finset.card_univ, Fintype.card_fin]
  push_cast
  ring

theorem strip_le (k : ℕ) (hk : 1 ≤ k) (q : Pt) : strip k q + 1 ≤ k := by
  have := min_le_right ⌊yc q * k⌋₊ (k - 1)
  unfold strip; omega

theorem strip_of_mem (k : ℕ) (σ : ℕ) (hσ : σ + 1 ≤ k) (q : Pt)
    (h1 : (σ : ℝ) / k < yc q) (h2 : yc q < ((σ : ℝ) + 1) / k) : strip k q = σ := by
  have hk : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hfl : ⌊yc q * k⌋₊ = σ := by
    have hy0 : 0 ≤ yc q * k := mul_nonneg (le_trans (by positivity) h1.le) hk.le
    rw [Nat.floor_eq_iff hy0]
    constructor
    · rw [div_lt_iff₀ hk] at h1; linarith
    · rw [lt_div_iff₀ hk] at h2; linarith
  unfold strip
  rw [hfl]
  omega

theorem ν_Rg_ge (k : ℕ) (hk : 1 ≤ k) (a b : Pt) (ha : a ∈ unitSquare) (hb : b ∈ unitSquare)
    (hab : xc a < xc b) : ENNReal.ofReal ((xc b - xc a) / k) ≤ ν (Rg k a b) := by
  set σ := strip k a with hσdef
  have hσ : σ + 1 ≤ k := strip_le k hk a
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hσR : ((σ : ℝ) + 1) ≤ k := by exact_mod_cast hσ
  have ha0 : 0 ≤ xc a := (ha 0).1
  have hb1 : xc b ≤ 1 := (hb 0).2
  set lo : Fin 2 → ℝ := ![xc a, (σ : ℝ) / k] with hlo
  set hi : Fin 2 → ℝ := ![xc b, ((σ : ℝ) + 1) / k] with hhi
  set B : Set Pt := (@WithLp.ofLp 2 (Fin 2 → ℝ)) ⁻¹' Set.univ.pi fun i => Set.Ioo (lo i) (hi i)
    with hB
  have hmemB : ∀ q, q ∈ B ↔ (xc a < xc q ∧ xc q < xc b) ∧
      ((σ : ℝ) / k < yc q ∧ yc q < ((σ : ℝ) + 1) / k) := by
    intro q
    simp [hB, hlo, hhi, Set.mem_pi, Fin.forall_fin_two, xc, yc]
  have hBsq : B ⊆ unitSquare := by
    intro q hq
    rw [hmemB] at hq
    have h0 : (0:ℝ) ≤ σ / k := by positivity
    have h1 : ((σ : ℝ) + 1) / k ≤ 1 := by rw [div_le_one hkR]; exact hσR
    obtain ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩ := hq
    intro i
    fin_cases i
    · exact ⟨by unfold xc at hx1 ha0; simp; linarith, by unfold xc at hx2 hb1; simp; linarith⟩
    · exact ⟨by unfold yc at hy1; simp; linarith, by unfold yc at hy2; simp; linarith⟩
  have hBR : B ⊆ Rg k a b := by
    intro q hq
    rw [hmemB] at hq
    exact ⟨strip_of_mem k σ hσ q hq.2.1 hq.2.2, hq.1.1, hq.1.2⟩
  have hvol : volume B = ENNReal.ofReal ((xc b - xc a) / k) := by
    rw [hB, (PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage
      (MeasurableSet.univ_pi fun i => measurableSet_Ioo).nullMeasurableSet, Real.volume_pi_Ioo,
      Fin.prod_univ_two]
    simp only [hlo, hhi, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← ENNReal.ofReal_mul (by linarith)]
    congr 1
    field_simp
    ring
  calc ENNReal.ofReal ((xc b - xc a) / k) = volume B := hvol.symm
    _ = ν B := (Measure.restrict_eq_self _ hBsq).symm
    _ ≤ ν (Rg k a b) := measure_mono hBR

theorem Fp_nonneg (k : ℕ) (a b : Pt) : 0 ≤ Fp k a b := by
  unfold Fp; split_ifs <;> simp [dist_nonneg]

theorem pair_bound (k m : ℕ) (hk : 1 ≤ k) (a b : Pt) (ha : a ∈ unitSquare) (hb : b ∈ unitSquare) :
    ENNReal.ofReal (Fp k a b) * (ν (Rg k a b)ᶜ) ^ m ≤
      ENNReal.ofReal (Fp k a b * (1 - (xc b - xc a) / k) ^ m) := by
  by_cases h : strip k a = strip k b ∧ xc a < xc b
  · have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hs0 : 0 ≤ (xc b - xc a) / k := div_nonneg (by linarith [h.2]) (by linarith)
    have hs1 : (xc b - xc a) / k ≤ 1 := by
      rw [div_le_one (by linarith)]
      have := (ha 0).1; have := (hb 0).2
      unfold xc; linarith
    have hc : ν (Rg k a b)ᶜ ≤ ENNReal.ofReal (1 - (xc b - xc a) / k) := by
      rw [prob_compl_eq_one_sub (measurableSet_Rg_section k a b),
        ENNReal.ofReal_sub _ hs0, ENNReal.ofReal_one]
      exact tsub_le_tsub_left (ν_Rg_ge k hk a b ha hb h.2) 1
    rw [ENNReal.ofReal_mul (Fp_nonneg k a b), ENNReal.ofReal_pow (by linarith)]
    gcongr
  · simp [Fp, h]

theorem lintegral_termS_01_le (k m : ℕ) (hk : 1 ≤ k) :
    ∫⁻ p, ENNReal.ofReal (termS k p 0 1) ∂(μ (m + 2)) ≤
      ∫⁻ a, ∫⁻ b, ENNReal.ofReal (Fp k a b * (1 - (xc b - xc a) / k) ^ m) ∂ν ∂ν := by
  rw [lintegral_termS_01]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_unitSquare] with a ha
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_unitSquare] with b hb
  exact pair_bound k m hk a b ha hb

/-- The point with coordinates `(x, y)`. -/
def mk (x y : ℝ) : Pt := WithLp.toLp 2 ![x, y]

@[simp] theorem xc_mk (x y : ℝ) : xc (mk x y) = x := by simp [xc, mk]
@[simp] theorem yc_mk (x y : ℝ) : yc (mk x y) = y := by simp [yc, mk]

theorem measurable_mk : Measurable fun z : ℝ × ℝ => mk z.1 z.2 := by
  unfold mk
  fun_prop

/-- Integrals against the uniform law on the square, in coordinates (`y` outer). -/
theorem lintegral_ν (f : Pt → ENNReal) (hf : Measurable f) :
    ∫⁻ q, f q ∂ν = ∫⁻ y in Set.Icc (0:ℝ) 1, ∫⁻ x in Set.Icc (0:ℝ) 1, f (mk x y) := by
  have hpre : (WithLp.toLp 2) ⁻¹' unitSquare = Set.univ.pi fun _ : Fin 2 => Set.Icc (0:ℝ) 1 := by
    ext v
    simp only [Set.mem_preimage, unitSquare, Set.mem_setOf_eq, Set.mem_univ_pi]
  have h1 : ∫⁻ q, f q ∂ν = ∫⁻ v in Set.univ.pi (fun _ : Fin 2 => Set.Icc (0:ℝ) 1),
      f (WithLp.toLp 2 v) := by
    rw [← hpre, (PiLp.volume_preserving_toLp (Fin 2)).setLIntegral_comp_preimage_emb
      (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).measurableEmbedding]
  have h2 : (volume : Measure (Fin 2 → ℝ)).restrict (Set.univ.pi fun _ : Fin 2 => Set.Icc (0:ℝ) 1) =
      Measure.pi fun _ : Fin 2 => volume.restrict (Set.Icc (0:ℝ) 1) := by
    rw [volume_pi]; exact Measure.restrict_pi_pi (fun _ => volume) _
  have hg : Measurable fun v : Fin 2 → ℝ => f (WithLp.toLp 2 v) :=
    hf.comp (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).measurable
  have h3 := (measurePreserving_finTwoArrow (volume.restrict (Set.Icc (0:ℝ) 1))).lintegral_comp_emb
    (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ).measurableEmbedding
    (fun z => f (WithLp.toLp 2 ((MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ).symm z)))
  simp only [MeasurableEquiv.symm_apply_apply] at h3
  have hF : Measurable fun z : ℝ × ℝ =>
      f (WithLp.toLp 2 ((MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ).symm z)) :=
    hg.comp (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ).symm.measurable
  rw [h1, h2, h3, lintegral_prod _ hF.aemeasurable, lintegral_lintegral_swap hF.aemeasurable]
  rfl

theorem lintegral_Icc_eq_ofReal (a b : ℝ) (hab : a ≤ b) (g : ℝ → ℝ) (hg : Continuous g)
    (hg0 : ∀ s ∈ Set.Icc a b, 0 ≤ g s) :
    ∫⁻ s in Set.Icc a b, ENNReal.ofReal (g s) = ENNReal.ofReal (∫ s in a..b, g s) := by
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
    ofReal_integral_eq_lintegral_ofReal (hg.integrableOn_Icc)]
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  exact hg0 s hs

/-- **X step.** The inner horizontal integral. -/
theorem lintegral_shift_le (g : ℝ → ℝ) (hg : Continuous g) (hg0 : ∀ s ∈ Set.Icc (0:ℝ) 1, 0 ≤ g s)
    (x1 : ℝ) (hx1 : x1 ∈ Set.Icc (0:ℝ) 1) :
    ∫⁻ x2 in Set.Icc (0:ℝ) 1, ENNReal.ofReal (if x1 < x2 then g (x2 - x1) else 0) ≤
      ENNReal.ofReal (∫ s in (0:ℝ)..1, g s) := by
  calc ∫⁻ x2 in Set.Icc (0:ℝ) 1, ENNReal.ofReal (if x1 < x2 then g (x2 - x1) else 0)
      ≤ ∫⁻ x2, (Set.Icc (0:ℝ) 1).indicator (fun s => ENNReal.ofReal (g s)) (x2 - x1) := by
        rw [← lintegral_indicator measurableSet_Icc]
        refine lintegral_mono fun x2 => ?_
        by_cases h1 : x2 ∈ Set.Icc (0:ℝ) 1
        · by_cases h2 : x1 < x2
          · have hm : x2 - x1 ∈ Set.Icc (0:ℝ) 1 :=
              ⟨by linarith, by linarith [h1.2, hx1.1]⟩
            simp [Set.indicator_of_mem h1, Set.indicator_of_mem hm, h2]
          · simp [Set.indicator_of_mem h1, h2]
        · simp [Set.indicator_of_notMem h1]
    _ = ∫⁻ s, (Set.Icc (0:ℝ) 1).indicator (fun s => ENNReal.ofReal (g s)) s :=
        lintegral_sub_right_eq_self _ x1
    _ = ∫⁻ s in Set.Icc (0:ℝ) 1, ENNReal.ofReal (g s) := lintegral_indicator measurableSet_Icc _
    _ = ENNReal.ofReal (∫ s in (0:ℝ)..1, g s) :=
        lintegral_Icc_eq_ofReal 0 1 zero_le_one g hg hg0

/-- For fixed `t`, integrating out the upper point of the triangle `0 ≤ t ≤ u₁ ≤ h`. -/
theorem inner_tri (h t : ℝ) (f : ℝ → ENNReal) :
    ∫⁻ u1 in Set.Icc 0 h, (Set.Icc 0 u1).indicator f t =
      (Set.Icc 0 h).indicator (fun t => f t * ENNReal.ofReal (h - t)) t := by
  by_cases ht : t ∈ Set.Icc 0 h
  · rw [Set.indicator_of_mem ht]
    have e : ∀ u1, (Set.Icc 0 u1).indicator f t = (Set.Ici t).indicator (fun _ => f t) u1 := by
      intro u1
      by_cases hu : t ≤ u1
      · rw [Set.indicator_of_mem (show t ∈ Set.Icc 0 u1 from ⟨ht.1, hu⟩),
          Set.indicator_of_mem (Set.mem_Ici.2 hu)]
      · rw [Set.indicator_of_notMem (fun hm => hu hm.2),
          Set.indicator_of_notMem (fun hm => hu (Set.mem_Ici.1 hm))]
    have hset : Set.Ici t ∩ Set.Icc 0 h = Set.Icc t h := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Icc]
      constructor
      · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨h1, ht.1.trans h1, h3⟩
    simp_rw [e]
    rw [lintegral_indicator_const measurableSet_Ici, Measure.restrict_apply measurableSet_Ici,
      hset, Real.volume_Icc]
  · rw [Set.indicator_of_notMem ht]
    calc ∫⁻ u1 in Set.Icc 0 h, (Set.Icc 0 u1).indicator f t
        = ∫⁻ _u1 in Set.Icc 0 h, (0 : ENNReal) := by
          refine setLIntegral_congr_fun measurableSet_Icc fun u1 hu1 => ?_
          exact Set.indicator_of_notMem (fun hm => ht ⟨hm.1, hm.2.trans hu1.2⟩) _
      _ = 0 := lintegral_zero

theorem measurable_tri (f : ℝ → ENNReal) (hf : Measurable f) :
    Measurable fun z : ℝ × ℝ => (Set.Icc 0 z.1).indicator f (z.1 - z.2) := by
  have e : (fun z : ℝ × ℝ => (Set.Icc 0 z.1).indicator f (z.1 - z.2)) =
      {z : ℝ × ℝ | 0 ≤ z.1 - z.2 ∧ z.1 - z.2 ≤ z.1}.indicator (fun z => f (z.1 - z.2)) := by
    funext z
    by_cases hz : 0 ≤ z.1 - z.2 ∧ z.1 - z.2 ≤ z.1
    · rw [Set.indicator_of_mem (show z.1 - z.2 ∈ Set.Icc 0 z.1 from hz),
        Set.indicator_of_mem (show z ∈ {z : ℝ × ℝ | 0 ≤ z.1 - z.2 ∧ z.1 - z.2 ≤ z.1} from hz)]
    · rw [Set.indicator_of_notMem (show z.1 - z.2 ∉ Set.Icc 0 z.1 from hz),
        Set.indicator_of_notMem (show z ∉ {z : ℝ × ℝ | 0 ≤ z.1 - z.2 ∧ z.1 - z.2 ≤ z.1} from hz)]
  rw [e]
  refine Measurable.indicator (hf.comp (measurable_fst.sub measurable_snd)) ?_
  exact (measurableSet_le measurable_const (measurable_fst.sub measurable_snd)).inter
    (measurableSet_le (measurable_fst.sub measurable_snd) measurable_fst)

/-- Half of the square. -/
theorem half_sq_le (h : ℝ) (Ψ : ℝ → ℝ) (hΨ : Continuous Ψ) (h0 : ∀ t ∈ Set.Icc 0 h, 0 ≤ Ψ t)
    (hh : 0 ≤ h) :
    ∫⁻ u1 in Set.Icc 0 h, ∫⁻ u2 in Set.Icc 0 h,
        (Set.Icc 0 u1).indicator (fun t => ENNReal.ofReal (Ψ t)) (u1 - u2) ≤
      ENNReal.ofReal (∫ t in (0:ℝ)..h, (h - t) * Ψ t) := by
  set f : ℝ → ENNReal := fun t => ENNReal.ofReal (Ψ t) with hfdef
  have hf : Measurable f := ENNReal.measurable_ofReal.comp hΨ.measurable
  calc ∫⁻ u1 in Set.Icc 0 h, ∫⁻ u2 in Set.Icc 0 h, (Set.Icc 0 u1).indicator f (u1 - u2)
      ≤ ∫⁻ u1 in Set.Icc 0 h, ∫⁻ u2, (Set.Icc 0 u1).indicator f (u1 - u2) :=
        lintegral_mono fun u1 => setLIntegral_le_lintegral _ _
    _ = ∫⁻ u1 in Set.Icc 0 h, ∫⁻ t, (Set.Icc 0 u1).indicator f t := by
        congr 1; funext u1
        exact lintegral_sub_left_eq_self (fun t => (Set.Icc 0 u1).indicator f t) u1
    _ = ∫⁻ t, ∫⁻ u1 in Set.Icc 0 h, (Set.Icc 0 u1).indicator f t := by
        refine lintegral_lintegral_swap ?_
        have := measurable_tri f hf
        have e : (Function.uncurry fun u1 t => (Set.Icc 0 u1).indicator f t) =
            (fun z : ℝ × ℝ => (Set.Icc 0 z.1).indicator f (z.1 - z.2)) ∘
              (fun z : ℝ × ℝ => (z.1, z.1 - z.2)) := by
          funext z; simp [Function.uncurry]
        rw [e]
        exact (this.comp (by fun_prop)).aemeasurable
    _ = ∫⁻ t, (Set.Icc 0 h).indicator (fun t => f t * ENNReal.ofReal (h - t)) t := by
        congr 1; funext t; exact inner_tri h t f
    _ = ∫⁻ t in Set.Icc 0 h, ENNReal.ofReal ((h - t) * Ψ t) := by
        rw [lintegral_indicator measurableSet_Icc]
        refine setLIntegral_congr_fun measurableSet_Icc fun t ht => ?_
        rw [hfdef, ← ENNReal.ofReal_mul (h0 t ht), mul_comm]
    _ = ENNReal.ofReal (∫ t in (0:ℝ)..h, (h - t) * Ψ t) :=
        lintegral_Icc_eq_ofReal 0 h hh _ (by fun_prop) fun t ht =>
          mul_nonneg (by linarith [ht.2]) (h0 t ht)

/-- **Square identity (upper bound).** For an even, nonnegative continuous `Ψ`. -/
theorem sq_le (h : ℝ) (hh : 0 ≤ h) (Ψ : ℝ → ℝ) (hΨ : Continuous Ψ)
    (h0 : ∀ t ∈ Set.Icc 0 h, 0 ≤ Ψ t) (hev : ∀ t, Ψ (-t) = Ψ t) :
    ∫⁻ u1 in Set.Icc 0 h, ∫⁻ u2 in Set.Icc 0 h, ENNReal.ofReal (Ψ (u1 - u2)) ≤
      ENNReal.ofReal (∫ t in (0:ℝ)..h, 2 * (h - t) * Ψ t) := by
  set f : ℝ → ENNReal := fun t => ENNReal.ofReal (Ψ t) with hfdef
  have hf : Measurable f := ENNReal.measurable_ofReal.comp hΨ.measurable
  set P : ℝ → ℝ → ENNReal := fun a b => (Set.Icc 0 a).indicator f (a - b) with hP
  have hPm : Measurable (Function.uncurry P) := measurable_tri f hf
  have hPm' : Measurable (Function.uncurry fun a b => P b a) :=
    hPm.comp (measurable_snd.prodMk measurable_fst)
  have hpt : ∀ u1 ∈ Set.Icc 0 h, ∀ u2 ∈ Set.Icc 0 h,
      ENNReal.ofReal (Ψ (u1 - u2)) ≤ P u1 u2 + P u2 u1 := by
    intro u1 hu1 u2 hu2
    by_cases hle : u2 ≤ u1
    · have hm : u1 - u2 ∈ Set.Icc 0 u1 := ⟨by linarith, by linarith [hu2.1]⟩
      simp only [hP, Set.indicator_of_mem hm, hfdef]
      exact le_self_add
    · have hm : u2 - u1 ∈ Set.Icc 0 u2 := ⟨by linarith, by linarith [hu1.1]⟩
      simp only [hP, Set.indicator_of_mem hm, hfdef]
      rw [show u2 - u1 = -(u1 - u2) by ring, hev]
      exact le_add_self
  have hA := half_sq_le h Ψ hΨ h0 hh
  calc ∫⁻ u1 in Set.Icc 0 h, ∫⁻ u2 in Set.Icc 0 h, ENNReal.ofReal (Ψ (u1 - u2))
      ≤ ∫⁻ u1 in Set.Icc 0 h, ∫⁻ u2 in Set.Icc 0 h, (P u1 u2 + P u2 u1) := by
        refine setLIntegral_mono' measurableSet_Icc fun u1 hu1 => ?_
        exact setLIntegral_mono' measurableSet_Icc fun u2 hu2 => hpt u1 hu1 u2 hu2
    _ = (∫⁻ u1 in Set.Icc 0 h, ∫⁻ u2 in Set.Icc 0 h, P u1 u2) +
          ∫⁻ u1 in Set.Icc 0 h, ∫⁻ u2 in Set.Icc 0 h, P u2 u1 := by
        have hm : Measurable fun u1 => ∫⁻ u2 in Set.Icc 0 h, P u1 u2 := hPm.lintegral_prod_right'
        rw [← lintegral_add_left hm]
        congr 1; funext u1
        exact lintegral_add_left (hPm.comp (measurable_const.prodMk measurable_id)) _
    _ = (∫⁻ u1 in Set.Icc 0 h, ∫⁻ u2 in Set.Icc 0 h, P u1 u2) +
          ∫⁻ u1 in Set.Icc 0 h, ∫⁻ u2 in Set.Icc 0 h, P u1 u2 := by
        congr 1
        exact lintegral_lintegral_swap hPm'.aemeasurable
    _ ≤ ENNReal.ofReal (∫ t in (0:ℝ)..h, (h - t) * Ψ t) +
          ENNReal.ofReal (∫ t in (0:ℝ)..h, (h - t) * Ψ t) := add_le_add hA hA
    _ = ENNReal.ofReal (∫ t in (0:ℝ)..h, 2 * (h - t) * Ψ t) := by
        have hI : 0 ≤ ∫ t in (0:ℝ)..h, (h - t) * Ψ t :=
          intervalIntegral.integral_nonneg hh fun t ht => mul_nonneg (by linarith [ht.2]) (h0 t ht)
        rw [← ENNReal.ofReal_add hI hI]
        congr 1
        simp_rw [mul_assoc]
        rw [intervalIntegral.integral_const_mul]
        ring

/-- The strip index of height `y`. -/
def sY (k : ℕ) (y : ℝ) : ℕ := min ⌊y * k⌋₊ (k - 1)

@[simp] theorem strip_mk (k : ℕ) (x y : ℝ) : strip k (mk x y) = sY k y := by
  simp [strip, sY]

theorem measurable_sY (k : ℕ) : Measurable (sY k) := by
  have : sY k = (fun j : ℕ => min j (k - 1)) ∘ (fun y : ℝ => ⌊y * k⌋₊) := rfl
  rw [this]
  exact measurable_from_nat.comp ((measurable_id.mul_const _).nat_floor)

theorem mem_band (k : ℕ) (hk : 1 ≤ k) (y : ℝ) (hy : y ∈ Set.Icc (0:ℝ) 1) :
    sY k y < k ∧ y ∈ Set.Icc ((sY k y : ℝ) / k) (((sY k y : ℝ) + 1) / k) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hy0 : 0 ≤ y * k := mul_nonneg hy.1 hkR.le
  refine ⟨by unfold sY; omega, ?_⟩
  rw [Set.mem_Icc, div_le_iff₀ hkR, le_div_iff₀ hkR]
  by_cases hf : ⌊y * k⌋₊ ≤ k - 1
  · have e : sY k y = ⌊y * k⌋₊ := by unfold sY; omega
    rw [e]
    exact ⟨Nat.floor_le hy0, (Nat.lt_floor_add_one _).le⟩
  · have e : sY k y = k - 1 := by unfold sY; omega
    have hk1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub hk]; simp
    rw [e, hk1]
    have hfk : (k : ℝ) ≤ y * k := by
      have : k ≤ ⌊y * k⌋₊ := by omega
      exact (Nat.le_floor_iff hy0).1 this
    constructor
    · linarith
    · nlinarith [hy.2]

/-- Translating a band to `[0, h]`. -/
theorem lintegral_Icc_shift (a h : ℝ) (F : ℝ → ENNReal) :
    ∫⁻ y in Set.Icc a (a + h), F y = ∫⁻ u in Set.Icc 0 h, F (u + a) := by
  have hpre : (fun u : ℝ => u + a) ⁻¹' Set.Icc a (a + h) = Set.Icc 0 h := by
    ext u; simp
  rw [← hpre, (measurePreserving_add_right volume a).setLIntegral_comp_preimage_emb
    (measurableEmbedding_addRight a)]

theorem sq_translate (a h : ℝ) (G : ℝ → ENNReal) :
    ∫⁻ y1 in Set.Icc a (a + h), ∫⁻ y2 in Set.Icc a (a + h), G (y1 - y2) =
      ∫⁻ u1 in Set.Icc 0 h, ∫⁻ u2 in Set.Icc 0 h, G (u1 - u2) := by
  rw [lintegral_Icc_shift a h (fun y1 => ∫⁻ y2 in Set.Icc a (a + h), G (y1 - y2))]
  congr 1; funext u1
  rw [lintegral_Icc_shift a h (fun y2 => G (u1 + a - y2))]
  congr 1; funext u2
  congr 1; ring

/-- **Y step.** Pairs of heights in the same strip. -/
theorem Y_le (k : ℕ) (hk : 1 ≤ k) (Ψ : ℝ → ℝ) (hΨ : Continuous Ψ)
    (h0 : ∀ t ∈ Set.Icc 0 (1 / (k : ℝ)), 0 ≤ Ψ t) (hev : ∀ t, Ψ (-t) = Ψ t) :
    ∫⁻ y1 in Set.Icc (0:ℝ) 1, ∫⁻ y2 in Set.Icc (0:ℝ) 1,
        (if sY k y1 = sY k y2 then ENNReal.ofReal (Ψ (y1 - y2)) else 0) ≤
      (k : ENNReal) * ENNReal.ofReal (∫ t in (0:ℝ)..(1 / (k : ℝ)), 2 * (1 / (k : ℝ) - t) * Ψ t) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  set h : ℝ := 1 / (k : ℝ) with hh
  have hh0 : 0 ≤ h := by positivity
  set B : ℕ → Set ℝ := fun σ => Set.Icc ((σ : ℝ) / k) ((σ : ℝ) / k + h) with hB
  have hBm : ∀ σ, MeasurableSet (B σ) := fun σ => measurableSet_Icc
  set g : ℝ × ℝ → ENNReal := fun z => ENNReal.ofReal (Ψ (z.1 - z.2)) with hg
  have hgm : Measurable g := ENNReal.measurable_ofReal.comp (hΨ.measurable.comp (by fun_prop))
  set Q : ℕ → ℝ × ℝ → ENNReal := fun σ => (B σ ×ˢ B σ).indicator g with hQ
  have hQm : ∀ σ, Measurable (Q σ) := fun σ => hgm.indicator ((hBm σ).prod (hBm σ))
  -- pointwise domination by the strip sum
  have hpt : ∀ y1 ∈ Set.Icc (0:ℝ) 1, ∀ y2 ∈ Set.Icc (0:ℝ) 1,
      (if sY k y1 = sY k y2 then ENNReal.ofReal (Ψ (y1 - y2)) else 0) ≤
        ∑ σ ∈ Finset.range k, Q σ (y1, y2) := by
    intro y1 hy1 y2 hy2
    split_ifs with hs
    · obtain ⟨hlt, hm1⟩ := mem_band k hk y1 hy1
      obtain ⟨-, hm2⟩ := mem_band k hk y2 hy2
      rw [← hs] at hm2
      have hBe : B (sY k y1) = Set.Icc ((sY k y1 : ℝ) / k) (((sY k y1 : ℝ) + 1) / k) := by
        simp only [hB, hh]; congr 1; field_simp
      have hmem : (y1, y2) ∈ B (sY k y1) ×ˢ B (sY k y1) := by
        rw [hBe]; exact ⟨hm1, hm2⟩
      refine le_trans ?_ (Finset.single_le_sum (fun σ _ => by positivity)
        (Finset.mem_range.2 hlt))
      simp only [hQ, Set.indicator_of_mem hmem, hg, le_refl]
    · positivity
  -- integrate
  have hinner : ∀ σ y1, ∫⁻ y2, Q σ (y1, y2) =
      (B σ).indicator (fun y1 => ∫⁻ y2 in B σ, g (y1, y2)) y1 := by
    intro σ y1
    by_cases hy1 : y1 ∈ B σ
    · rw [Set.indicator_of_mem hy1, ← lintegral_indicator (hBm σ)]
      congr 1; funext y2
      by_cases hy2 : y2 ∈ B σ
      · rw [Set.indicator_of_mem hy2]; simp only [hQ]
        rw [Set.indicator_of_mem (Set.mk_mem_prod hy1 hy2)]
      · rw [Set.indicator_of_notMem hy2]; simp only [hQ]
        rw [Set.indicator_of_notMem (fun hm => hy2 hm.2)]
    · rw [Set.indicator_of_notMem hy1]
      have : ∀ y2, Q σ (y1, y2) = 0 := fun y2 => by
        simp only [hQ]; rw [Set.indicator_of_notMem (fun hm => hy1 hm.1)]
      simp [this]
  have hT := sq_le h hh0 Ψ hΨ h0 hev
  calc ∫⁻ y1 in Set.Icc (0:ℝ) 1, ∫⁻ y2 in Set.Icc (0:ℝ) 1,
        (if sY k y1 = sY k y2 then ENNReal.ofReal (Ψ (y1 - y2)) else 0)
      ≤ ∫⁻ y1 in Set.Icc (0:ℝ) 1, ∫⁻ y2 in Set.Icc (0:ℝ) 1, ∑ σ ∈ Finset.range k, Q σ (y1, y2) := by
        refine setLIntegral_mono' measurableSet_Icc fun y1 hy1 => ?_
        exact setLIntegral_mono' measurableSet_Icc fun y2 hy2 => hpt y1 hy1 y2 hy2
    _ ≤ ∫⁻ y1, ∫⁻ y2, ∑ σ ∈ Finset.range k, Q σ (y1, y2) := by
        refine (lintegral_mono fun y1 => setLIntegral_le_lintegral _ _).trans ?_
        exact setLIntegral_le_lintegral _ _
    _ = ∑ σ ∈ Finset.range k, ∫⁻ y1, ∫⁻ y2, Q σ (y1, y2) := by
        rw [← lintegral_finsetSum _ fun σ _ => (hQm σ).lintegral_prod_right']
        congr 1; funext y1
        exact lintegral_finsetSum _ fun σ _ => (hQm σ).comp (measurable_const.prodMk measurable_id)
    _ = ∑ σ ∈ Finset.range k, ∫⁻ y1 in B σ, ∫⁻ y2 in B σ, g (y1, y2) := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        simp_rw [hinner]
        exact lintegral_indicator (hBm σ) _
    _ = ∑ σ ∈ Finset.range k, ∫⁻ u1 in Set.Icc 0 h, ∫⁻ u2 in Set.Icc 0 h,
          ENNReal.ofReal (Ψ (u1 - u2)) := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        exact sq_translate ((σ : ℝ) / k) h (fun z => ENNReal.ofReal (Ψ z))
    _ = (k : ENNReal) * ∫⁻ u1 in Set.Icc 0 h, ∫⁻ u2 in Set.Icc 0 h, ENNReal.ofReal (Ψ (u1 - u2)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (k : ENNReal) * ENNReal.ofReal (∫ t in (0:ℝ)..h, 2 * (h - t) * Ψ t) := by gcongr

theorem dist_mk (x1 y1 x2 y2 : ℝ) :
    dist (mk x1 y1) (mk x2 y2) = Real.sqrt ((x2 - x1) ^ 2 + (y1 - y2) ^ 2) := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  simp only [mk, Real.dist_eq, sq_abs]
  congr 1
  simp
  ring

theorem Fp_mk (k : ℕ) (x1 y1 x2 y2 : ℝ) :
    Fp k (mk x1 y1) (mk x2 y2) = if sY k y1 = sY k y2 ∧ x1 < x2 then
      Real.sqrt ((x2 - x1) ^ 2 + (y1 - y2) ^ 2) else 0 := by
  simp [Fp, dist_mk]

/-- The horizontal kernel. -/
def ψ (k m : ℕ) (s t : ℝ) : ℝ := Real.sqrt (s ^ 2 + t ^ 2) * (1 - s / k) ^ m

/-- The horizontal kernel integrated over the gap. -/
def Ψ (k m : ℕ) (t : ℝ) : ℝ := ∫ s in (0:ℝ)..1, ψ k m s t

theorem continuous_ψ (k m : ℕ) : Continuous fun z : ℝ × ℝ => ψ k m z.2 z.1 := by
  unfold ψ; fun_prop

theorem continuous_Ψ (k m : ℕ) : Continuous (Ψ k m) := by
  unfold Ψ
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (continuous_ψ k m) 0 1

theorem ψ_nonneg (k m : ℕ) (hk : 1 ≤ k) (s t : ℝ) (hs : s ∈ Set.Icc (0:ℝ) 1) : 0 ≤ ψ k m s t := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have : 0 ≤ 1 - s / k := by
    rw [sub_nonneg, div_le_one (by linarith)]; linarith [hs.2]
  unfold ψ; positivity

theorem Ψ_nonneg (k m : ℕ) (hk : 1 ≤ k) (t : ℝ) : 0 ≤ Ψ k m t :=
  intervalIntegral.integral_nonneg zero_le_one fun s hs => ψ_nonneg k m hk s t hs

theorem Ψ_even (k m : ℕ) (t : ℝ) : Ψ k m (-t) = Ψ k m t := by
  simp [Ψ, ψ]

theorem measurable_Fp_real (k : ℕ) {β : Type*} [MeasurableSpace β] {A B : β → Pt}
    (hA : Measurable A) (hB : Measurable B) : Measurable fun x => Fp k (A x) (B x) := by
  unfold Fp
  refine Measurable.ite ?_ (hA.dist hB) measurable_const
  exact (measurableSet_strip_eq k hA hB).inter (measurableSet_lt (measurable_xc.comp hA)
    (measurable_xc.comp hB))

/-- **J step.** The two-point integral. -/
theorem J_le (k m : ℕ) (hk : 1 ≤ k) :
    ∫⁻ a, ∫⁻ b, ENNReal.ofReal (Fp k a b * (1 - (xc b - xc a) / k) ^ m) ∂ν ∂ν ≤
      (k : ENNReal) * ENNReal.ofReal
        (∫ t in (0:ℝ)..(1 / (k : ℝ)), 2 * (1 / (k : ℝ) - t) * Ψ k m t) := by
  set F : Pt × Pt → ENNReal := fun x => ENNReal.ofReal (Fp k x.1 x.2 * (1 - (xc x.2 - xc x.1) / k) ^ m)
    with hF
  have hFm : Measurable F := by
    refine ENNReal.measurable_ofReal.comp ((measurable_Fp_real k measurable_fst measurable_snd).mul ?_)
    have hd : Measurable fun x : Pt × Pt => (xc x.2 - xc x.1) / (k : ℝ) :=
      ((measurable_xc.comp measurable_snd).sub (measurable_xc.comp measurable_fst)).div_const _
    have h1 : Measurable fun x : Pt × Pt => 1 - (xc x.2 - xc x.1) / (k : ℝ) :=
      measurable_const.sub hd
    exact h1.pow_const m
  have hF1 : ∀ a, Measurable fun b => F (a, b) := fun a => hFm.comp (measurable_const.prodMk measurable_id)
  have hF2 : Measurable fun a => ∫⁻ b, F (a, b) ∂ν := hFm.lintegral_prod_right'
  -- coordinates
  have e1 : ∫⁻ a, ∫⁻ b, F (a, b) ∂ν ∂ν = ∫⁻ y1 in Set.Icc (0:ℝ) 1, ∫⁻ x1 in Set.Icc (0:ℝ) 1,
      ∫⁻ y2 in Set.Icc (0:ℝ) 1, ∫⁻ x2 in Set.Icc (0:ℝ) 1, F (mk x1 y1, mk x2 y2) := by
    rw [lintegral_ν _ hF2]
    congr 1; funext y1; congr 1; funext x1
    exact lintegral_ν _ (hF1 _)
  -- the innermost horizontal integral
  have hX : ∀ y1, ∀ x1 ∈ Set.Icc (0:ℝ) 1, ∀ y2,
      ∫⁻ x2 in Set.Icc (0:ℝ) 1, F (mk x1 y1, mk x2 y2) ≤
        if sY k y1 = sY k y2 then ENNReal.ofReal (Ψ k m (y1 - y2)) else 0 := by
    intro y1 x1 hx1 y2
    have e : ∀ x2, F (mk x1 y1, mk x2 y2) = if sY k y1 = sY k y2 then
        ENNReal.ofReal (if x1 < x2 then ψ k m (x2 - x1) (y1 - y2) else 0) else 0 := by
      intro x2
      simp only [hF, Fp_mk, xc_mk, ψ]
      by_cases hs : sY k y1 = sY k y2 <;> by_cases hx : x1 < x2 <;> simp [hs, hx]
    simp_rw [e]
    split_ifs with hs
    · exact lintegral_shift_le (fun s => ψ k m s (y1 - y2))
        ((continuous_ψ k m).comp (continuous_const.prodMk continuous_id))
        (fun s hs => ψ_nonneg k m hk s _ hs) x1 hx1
    · simp
  rw [e1]
  calc ∫⁻ y1 in Set.Icc (0:ℝ) 1, ∫⁻ x1 in Set.Icc (0:ℝ) 1,
        ∫⁻ y2 in Set.Icc (0:ℝ) 1, ∫⁻ x2 in Set.Icc (0:ℝ) 1, F (mk x1 y1, mk x2 y2)
      ≤ ∫⁻ y1 in Set.Icc (0:ℝ) 1, ∫⁻ x1 in Set.Icc (0:ℝ) 1, ∫⁻ y2 in Set.Icc (0:ℝ) 1,
          (if sY k y1 = sY k y2 then ENNReal.ofReal (Ψ k m (y1 - y2)) else 0) := by
        refine lintegral_mono fun y1 => ?_
        refine setLIntegral_mono' measurableSet_Icc fun x1 hx1 => ?_
        exact lintegral_mono fun y2 => hX y1 x1 hx1 y2
    _ = ∫⁻ y1 in Set.Icc (0:ℝ) 1, ∫⁻ y2 in Set.Icc (0:ℝ) 1,
          (if sY k y1 = sY k y2 then ENNReal.ofReal (Ψ k m (y1 - y2)) else 0) := by
        congr 1; funext y1
        rw [setLIntegral_const, Real.volume_Icc]
        simp
    _ ≤ _ := Y_le k hk (Ψ k m) (continuous_Ψ k m) (fun t _ => Ψ_nonneg k m hk t) (Ψ_even k m)

def mainTerm (n k : ℕ) : ℝ :=
  (n : ℝ) * ((n : ℝ) - 1) * k *
    ∫ t in (0:ℝ)..(1 / (k : ℝ)), 2 * (1 / (k : ℝ) - t) *
      ∫ s in (0:ℝ)..1, Real.sqrt (s ^ 2 + t ^ 2) * (1 - s / k) ^ (n - 2)

/-- **B1.** -/
theorem lintegral_succSum_le (n k : ℕ) (hn : 2 ≤ n) (hk : 1 ≤ k) :
    ∫⁻ p, ENNReal.ofReal (succSum k p) ∂(μ n) ≤ ENNReal.ofReal (mainTerm n k) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  set I : ℝ := ∫ t in (0:ℝ)..(1 / (k : ℝ)), 2 * (1 / (k : ℝ) - t) * Ψ k m t with hI
  have hI0 : 0 ≤ I := intervalIntegral.integral_nonneg (by positivity) fun t ht =>
    mul_nonneg (mul_nonneg zero_le_two (by linarith [ht.2])) (Ψ_nonneg k m hk t)
  have hmain : mainTerm (m + 2) k = ((m + 2 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ) * k * I := by
    simp only [mainTerm, hI, Ψ, ψ, Nat.add_sub_cancel]
    push_cast
    ring
  rw [lintegral_succSum, hmain]
  calc ((m + 2) * (m + 1) : ℕ) * ∫⁻ p, ENNReal.ofReal (termS k p 0 1) ∂(μ (m + 2))
      ≤ ((m + 2) * (m + 1) : ℕ) * ((k : ENNReal) * ENNReal.ofReal I) := by
        gcongr
        exact (lintegral_termS_01_le k m hk).trans (J_le k m hk)
    _ = ENNReal.ofReal (((m + 2 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ) * k * I) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by positivity)]
        simp only [ENNReal.ofReal_natCast]
        push_cast
        ring

/-- One point and an avoidance region. -/
theorem lintegral_single (m : ℕ) (S : Set (Pt × Pt)) (hS : MeasurableSet S) (w : Pt → ℝ)
    (hw : Measurable w) :
    ∫⁻ p : Fin (m + 1) → Pt, ENNReal.ofReal
        (if ∀ l : Fin m, (p 0, p l.succ) ∉ S then w (p 0) else 0) ∂(μ (m + 1)) =
      ∫⁻ a, ENNReal.ofReal (w a) * (ν {q | (a, q) ∈ S}ᶜ) ^ m ∂ν := by
  have hsec : ∀ a, MeasurableSet {q | (a, q) ∈ S} := fun a =>
    hS.preimage (measurable_const.prodMk measurable_id)
  have hpt : ∀ p : Fin (m + 1) → Pt, ENNReal.ofReal
      (if ∀ l : Fin m, (p 0, p l.succ) ∉ S then w (p 0) else 0) =
      ENNReal.ofReal (w (p 0)) * ∏ l : Fin m, {q | (p 0, q) ∈ S}ᶜ.indicator 1 (p l.succ) := by
    intro p
    split_ifs with h
    · have h1 : ∏ l : Fin m, {q | (p 0, q) ∈ S}ᶜ.indicator (1 : Pt → ENNReal) (p l.succ) = 1 :=
        Finset.prod_eq_one fun l _ =>
          Set.indicator_of_mem (show p l.succ ∈ {q | (p 0, q) ∈ S}ᶜ from h l) _
      rw [h1, mul_one]
    · push Not at h
      obtain ⟨l, hl⟩ := h
      rw [Finset.prod_eq_zero (Finset.mem_univ l)]
      · simp
      · exact Set.indicator_of_notMem (show p l.succ ∉ {q | (p 0, q) ∈ S}ᶜ from fun hm => hm hl) _
  have hind : Measurable fun x : Pt × Pt => {q | (x.1, q) ∈ S}ᶜ.indicator (1 : Pt → ENNReal) x.2 := by
    have e : (fun x : Pt × Pt => {q | (x.1, q) ∈ S}ᶜ.indicator (1 : Pt → ENNReal) x.2) =
        Sᶜ.indicator 1 := by
      funext x
      by_cases hx : x ∈ S
      · rw [Set.indicator_of_notMem (show x.2 ∉ {q | (x.1, q) ∈ S}ᶜ from fun h => h hx),
          Set.indicator_of_notMem (show x ∉ Sᶜ from fun h => h hx)]
      · rw [Set.indicator_of_mem (show x.2 ∈ {q | (x.1, q) ∈ S}ᶜ from hx),
          Set.indicator_of_mem (show x ∈ Sᶜ from hx)]
        simp
    rw [e]; exact measurable_one.indicator hS.compl
  have hfm : Measurable (Function.uncurry fun (a : Pt) (r : Fin m → Pt) =>
      ENNReal.ofReal (w a) * ∏ l : Fin m, {q | (a, q) ∈ S}ᶜ.indicator (1 : Pt → ENNReal) (r l)) := by
    have h1 : Measurable fun x : Pt × (Fin m → Pt) => ENNReal.ofReal (w x.1) :=
      ENNReal.measurable_ofReal.comp (hw.comp measurable_fst)
    have h2 : ∀ l : Fin m, Measurable fun x : Pt × (Fin m → Pt) =>
        {q | (x.1, q) ∈ S}ᶜ.indicator (1 : Pt → ENNReal) (x.2 l) :=
      fun l => hind.comp (measurable_fst.prodMk ((measurable_pi_apply l).comp measurable_snd))
    exact h1.mul (Finset.measurable_prod _ fun l _ => h2 l)
  simp_rw [hpt]
  refine (lintegral_μ_succ m (fun (a : Pt) (r : Fin m → Pt) => ENNReal.ofReal (w a) *
    ∏ l : Fin m, {q | (a, q) ∈ S}ᶜ.indicator (1 : Pt → ENNReal) (r l)) hfm).trans ?_
  refine lintegral_congr fun a => ?_
  have hia : Measurable ({q | (a, q) ∈ S}ᶜ.indicator (1 : Pt → ENNReal)) :=
    measurable_one.indicator (hsec a).compl
  have hpm : Measurable fun r : Fin m → Pt => ∏ l, {q | (a, q) ∈ S}ᶜ.indicator (1 : Pt → ENNReal) (r l) :=
    Finset.measurable_prod _ fun l _ => hia.comp (measurable_pi_apply l)
  rw [lintegral_const_mul _ hpm, lintegral_μ_prod _ hia m, lintegral_indicator_one (hsec a).compl]

theorem ν_band_ge (k : ℕ) (hk : 1 ≤ k) (a : Pt) (x0 x1 : ℝ) (h0 : 0 ≤ x0) (h01 : x0 ≤ x1)
    (h1 : x1 ≤ 1) :
    ENNReal.ofReal ((x1 - x0) / k) ≤ ν {q | strip k q = strip k a ∧ x0 < xc q ∧ xc q < x1} := by
  set σ := strip k a with hσdef
  have hσ : σ + 1 ≤ k := strip_le k hk a
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hσR : ((σ : ℝ) + 1) ≤ k := by exact_mod_cast hσ
  set lo : Fin 2 → ℝ := ![x0, (σ : ℝ) / k] with hlo
  set hi : Fin 2 → ℝ := ![x1, ((σ : ℝ) + 1) / k] with hhi
  set B : Set Pt := (@WithLp.ofLp 2 (Fin 2 → ℝ)) ⁻¹' Set.univ.pi fun i => Set.Ioo (lo i) (hi i)
    with hB
  have hmemB : ∀ q, q ∈ B ↔ (x0 < xc q ∧ xc q < x1) ∧
      ((σ : ℝ) / k < yc q ∧ yc q < ((σ : ℝ) + 1) / k) := by
    intro q
    simp [hB, hlo, hhi, Set.mem_pi, Fin.forall_fin_two, xc, yc]
  have hBsq : B ⊆ unitSquare := by
    intro q hq
    rw [hmemB] at hq
    have hσ0 : (0:ℝ) ≤ σ / k := by positivity
    have hσ1 : ((σ : ℝ) + 1) / k ≤ 1 := by rw [div_le_one hkR]; exact hσR
    obtain ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩ := hq
    intro i
    fin_cases i
    · exact ⟨by unfold xc at hx1; simp; linarith, by unfold xc at hx2; simp; linarith⟩
    · exact ⟨by unfold yc at hy1; simp; linarith, by unfold yc at hy2; simp; linarith⟩
  have hBR : B ⊆ {q | strip k q = strip k a ∧ x0 < xc q ∧ xc q < x1} := by
    intro q hq
    rw [hmemB] at hq
    exact ⟨strip_of_mem k σ hσ q hq.2.1 hq.2.2, hq.1.1, hq.1.2⟩
  have hvol : volume B = ENNReal.ofReal ((x1 - x0) / k) := by
    rw [hB, (PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage
      (MeasurableSet.univ_pi fun i => measurableSet_Ioo).nullMeasurableSet, Real.volume_pi_Ioo,
      Fin.prod_univ_two]
    simp only [hlo, hhi, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← ENNReal.ofReal_mul (by linarith)]
    congr 1
    field_simp
    ring
  calc ENNReal.ofReal ((x1 - x0) / k) = volume B := hvol.symm
    _ = ν B := (Measure.restrict_eq_self _ hBsq).symm
    _ ≤ _ := measure_mono hBR

/-- Right avoidance region. -/
def SR (k : ℕ) : Set (Pt × Pt) := {x | strip k x.2 = strip k x.1 ∧ xc x.1 ≤ xc x.2}
/-- Left avoidance region. -/
def SL (k : ℕ) : Set (Pt × Pt) := {x | strip k x.2 = strip k x.1 ∧ xc x.2 ≤ xc x.1}

theorem measurableSet_SR (k : ℕ) : MeasurableSet (SR k) :=
  (measurableSet_strip_eq k measurable_snd measurable_fst).inter
    (measurableSet_le (measurable_xc.comp measurable_fst) (measurable_xc.comp measurable_snd))

theorem measurableSet_SL (k : ℕ) : MeasurableSet (SL k) :=
  (measurableSet_strip_eq k measurable_snd measurable_fst).inter
    (measurableSet_le (measurable_xc.comp measurable_snd) (measurable_xc.comp measurable_fst))

theorem ν_SR_ge (k : ℕ) (hk : 1 ≤ k) (a : Pt) (ha : a ∈ unitSquare) :
    ENNReal.ofReal ((1 - xc a) / k) ≤ ν {q | (a, q) ∈ SR k} := by
  refine (ν_band_ge k hk a (xc a) 1 (ha 0).1 (ha 0).2 le_rfl).trans (measure_mono ?_)
  rintro q ⟨h1, h2, -⟩
  exact ⟨h1, h2.le⟩

theorem ν_SL_ge (k : ℕ) (hk : 1 ≤ k) (a : Pt) (ha : a ∈ unitSquare) :
    ENNReal.ofReal (xc a / k) ≤ ν {q | (a, q) ∈ SL k} := by
  have := ν_band_ge k hk a 0 (xc a) le_rfl (ha 0).1 (ha 0).2
  rw [sub_zero] at this
  refine this.trans (measure_mono ?_)
  rintro q ⟨h1, -, h3⟩
  exact ⟨h1, h3.le⟩

/-- `∫⁻ ofReal (1 - x)(1 - (1-x)/k)^m` style bounds. -/
theorem single_bound (k m : ℕ) (hk : 1 ≤ k) (S : Set (Pt × Pt)) (hS : MeasurableSet S)
    (w : Pt → ℝ) (hw : Measurable w) (hwge : ∀ a ∈ unitSquare, ENNReal.ofReal (w a / k) ≤ ν {q | (a, q) ∈ S})
    (hw0 : ∀ a ∈ unitSquare, 0 ≤ w a ∧ w a ≤ 1) :
    ∫⁻ p : Fin (m + 1) → Pt, ENNReal.ofReal
        (if ∀ l : Fin m, (p 0, p l.succ) ∉ S then w (p 0) else 0) ∂(μ (m + 1)) ≤
      ∫⁻ a, ENNReal.ofReal (w a * (1 - w a / k) ^ m) ∂ν := by
  rw [lintegral_single m S hS w hw]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_unitSquare] with a ha
  have hsec : MeasurableSet {q | (a, q) ∈ S} := hS.preimage (measurable_const.prodMk measurable_id)
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hs0 : 0 ≤ w a / k := div_nonneg (hw0 a ha).1 (by linarith)
  have hs1 : w a / k ≤ 1 := by rw [div_le_one (by linarith)]; linarith [(hw0 a ha).2]
  have hc : ν {q | (a, q) ∈ S}ᶜ ≤ ENNReal.ofReal (1 - w a / k) := by
    rw [prob_compl_eq_one_sub hsec, ENNReal.ofReal_sub _ hs0, ENNReal.ofReal_one]
    exact tsub_le_tsub_left (hwge a ha) 1
  rw [ENNReal.ofReal_mul (hw0 a ha).1, ENNReal.ofReal_pow (by linarith)]
  gcongr

def endTerm (n k : ℕ) : ℝ :=
  2 * n * ∫ t in (0:ℝ)..1, t * (1 - t / k) ^ (n - 1)

theorem ofReal_sum_le' {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ENNReal.ofReal (∑ i ∈ s, f i) ≤ ∑ i ∈ s, ENNReal.ofReal (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ENNReal.ofReal_add_le.trans (by gcongr)

/-- Right end-gap term. -/
def termR (k : ℕ) {n : ℕ} (p : Fin n → Pt) (i : Fin n) : ℝ :=
  if IsRightmost k p i then 1 - xc (p i) else 0
/-- Left end-gap term. -/
def termL (k : ℕ) {n : ℕ} (p : Fin n → Pt) (i : Fin n) : ℝ :=
  if IsLeftmost k p i then xc (p i) else 0

theorem isRightmost_comp (k : ℕ) {n : ℕ} (p : Fin n → Pt) (π : Equiv.Perm (Fin n)) (a : Fin n) :
    IsRightmost k (p ∘ π) a ↔ IsRightmost k p (π a) := by
  unfold IsRightmost
  simp only [Function.comp_apply]
  constructor
  · intro h l hl hs
    have := h (π.symm l) (by rintro rfl; simp at hl)
    simpa using this (by simpa using hs)
  · intro h l hl hs
    exact h (π l) (by simpa using hl) hs

theorem isLeftmost_comp (k : ℕ) {n : ℕ} (p : Fin n → Pt) (π : Equiv.Perm (Fin n)) (a : Fin n) :
    IsLeftmost k (p ∘ π) a ↔ IsLeftmost k p (π a) := by
  unfold IsLeftmost
  simp only [Function.comp_apply]
  constructor
  · intro h l hl hs
    have := h (π.symm l) (by rintro rfl; simp at hl)
    simpa using this (by simpa using hs)
  · intro h l hl hs
    exact h (π l) (by simpa using hl) hs

theorem isRightmost_0_iff (k m : ℕ) (p : Fin (m + 1) → Pt) :
    IsRightmost k p 0 ↔ ∀ l : Fin m, (p 0, p l.succ) ∉ SR k := by
  unfold IsRightmost SR
  simp only [Set.mem_setOf_eq, not_and, not_le]
  constructor
  · intro h l hs; exact h l.succ (Fin.succ_ne_zero _) hs
  · intro h l hl hs
    obtain ⟨l', rfl⟩ := Fin.exists_succ_eq.2 hl
    exact h l' hs

theorem isLeftmost_0_iff (k m : ℕ) (p : Fin (m + 1) → Pt) :
    IsLeftmost k p 0 ↔ ∀ l : Fin m, (p 0, p l.succ) ∉ SL k := by
  unfold IsLeftmost SL
  simp only [Set.mem_setOf_eq, not_and, not_le]
  constructor
  · intro h l hs; exact h l.succ (Fin.succ_ne_zero _) hs
  · intro h l hl hs
    obtain ⟨l', rfl⟩ := Fin.exists_succ_eq.2 hl
    exact h l' hs

/-- The one-variable integral of a function of `x` against `ν`. -/
theorem lintegral_ν_x (g : ℝ → ℝ) (hg : Continuous g) (hg0 : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ g x) :
    ∫⁻ a, ENNReal.ofReal (g (xc a)) ∂ν = ENNReal.ofReal (∫ x in (0:ℝ)..1, g x) := by
  rw [lintegral_ν (fun a => ENNReal.ofReal (g (xc a)))
    (ENNReal.measurable_ofReal.comp (hg.measurable.comp measurable_xc))]
  simp only [xc_mk]
  rw [lintegral_Icc_eq_ofReal 0 1 zero_le_one g hg hg0, setLIntegral_const, Real.volume_Icc]
  simp

theorem endInt_nonneg (k m : ℕ) (hk : 1 ≤ k) :
    0 ≤ ∫ t in (0:ℝ)..1, t * (1 - t / k) ^ m := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  refine intervalIntegral.integral_nonneg zero_le_one fun t ht => ?_
  have : 0 ≤ 1 - t / k := by rw [sub_nonneg, div_le_one (by linarith)]; linarith [ht.2]
  exact mul_nonneg ht.1 (pow_nonneg this m)

theorem lintegral_termR_0 (k m : ℕ) (hk : 1 ≤ k) :
    ∫⁻ p, ENNReal.ofReal (termR k p 0) ∂(μ (m + 1)) ≤
      ENNReal.ofReal (∫ t in (0:ℝ)..1, t * (1 - t / k) ^ m) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have e : ∀ p : Fin (m + 1) → Pt, termR k p 0 =
      if ∀ l : Fin m, (p 0, p l.succ) ∉ SR k then 1 - xc (p 0) else 0 := by
    intro p; simp only [termR, isRightmost_0_iff]
  simp_rw [e]
  refine (single_bound k m hk (SR k) (measurableSet_SR k) (fun a => 1 - xc a)
    (measurable_const.sub measurable_xc) (fun a ha => ν_SR_ge k hk a ha)
    (fun a ha => ⟨by have := (ha 0).2; unfold xc; linarith,
      by have := (ha 0).1; unfold xc; linarith⟩)).trans_eq ?_
  have := lintegral_ν_x (fun x => (1 - x) * (1 - (1 - x) / k) ^ m) (by fun_prop) (fun x hx => by
    have : 0 ≤ 1 - (1 - x) / k := by
      rw [sub_nonneg, div_le_one (by linarith)]; linarith [hx.1]
    exact mul_nonneg (by linarith [hx.2]) (pow_nonneg this m))
  rw [this]
  congr 1
  have h := intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := 1)
    (fun t : ℝ => t * (1 - t / k) ^ m) 1
  simp only [sub_zero, sub_self] at h
  exact h

theorem lintegral_termL_0 (k m : ℕ) (hk : 1 ≤ k) :
    ∫⁻ p, ENNReal.ofReal (termL k p 0) ∂(μ (m + 1)) ≤
      ENNReal.ofReal (∫ t in (0:ℝ)..1, t * (1 - t / k) ^ m) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have e : ∀ p : Fin (m + 1) → Pt, termL k p 0 =
      if ∀ l : Fin m, (p 0, p l.succ) ∉ SL k then xc (p 0) else 0 := by
    intro p; simp only [termL, isLeftmost_0_iff]
  simp_rw [e]
  refine (single_bound k m hk (SL k) (measurableSet_SL k) (fun a => xc a) measurable_xc
    (fun a ha => ν_SL_ge k hk a ha) (fun a ha => ⟨(ha 0).1, (ha 0).2⟩)).trans_eq ?_
  exact lintegral_ν_x (fun x => x * (1 - x / k) ^ m) (by fun_prop) (fun x hx => by
    have : 0 ≤ 1 - x / k := by rw [sub_nonneg, div_le_one (by linarith)]; linarith [hx.2]
    exact mul_nonneg hx.1 (pow_nonneg this m))

theorem measurable_single (m : ℕ) (S : Set (Pt × Pt)) (hS : MeasurableSet S) (w : Pt → ℝ)
    (hw : Measurable w) :
    Measurable fun p : Fin (m + 1) → Pt => ENNReal.ofReal
      (if ∀ l : Fin m, (p 0, p l.succ) ∉ S then w (p 0) else 0) := by
  have hset : MeasurableSet {p : Fin (m + 1) → Pt | ∀ l : Fin m, (p 0, p l.succ) ∉ S} := by
    have : {p : Fin (m + 1) → Pt | ∀ l : Fin m, (p 0, p l.succ) ∉ S} =
        ⋂ l : Fin m, (fun p : Fin (m + 1) → Pt => (p 0, p l.succ)) ⁻¹' Sᶜ := by
      ext p; simp
    rw [this]
    exact MeasurableSet.iInter fun l =>
      ((measurable_pi_apply 0).prodMk (measurable_pi_apply _)) hS.compl
  exact ENNReal.measurable_ofReal.comp
    (Measurable.ite hset (hw.comp (measurable_pi_apply 0)) measurable_const)

theorem measurable_termR (k m : ℕ) (i : Fin (m + 1)) :
    Measurable fun p : Fin (m + 1) → Pt => ENNReal.ofReal (termR k p i) := by
  have h0 : Measurable fun p : Fin (m + 1) → Pt => ENNReal.ofReal (termR k p 0) := by
    have e : (fun p : Fin (m + 1) → Pt => ENNReal.ofReal (termR k p 0)) = fun p => ENNReal.ofReal
        (if ∀ l : Fin m, (p 0, p l.succ) ∉ SR k then 1 - xc (p 0) else 0) := by
      funext p; simp only [termR, isRightmost_0_iff]
    rw [e]
    exact measurable_single m (SR k) (measurableSet_SR k) _ (measurable_const.sub measurable_xc)
  have e : (fun p : Fin (m + 1) → Pt => ENNReal.ofReal (termR k p i)) =
      (fun p => ENNReal.ofReal (termR k p 0)) ∘ (fun p => p ∘ Equiv.swap 0 i) := by
    funext p
    simp only [Function.comp_apply, termR, isRightmost_comp, Equiv.swap_apply_left]
  rw [e]
  exact h0.comp (measurable_pi_lambda _ fun l => measurable_pi_apply _)

theorem measurable_termL (k m : ℕ) (i : Fin (m + 1)) :
    Measurable fun p : Fin (m + 1) → Pt => ENNReal.ofReal (termL k p i) := by
  have h0 : Measurable fun p : Fin (m + 1) → Pt => ENNReal.ofReal (termL k p 0) := by
    have e : (fun p : Fin (m + 1) → Pt => ENNReal.ofReal (termL k p 0)) = fun p => ENNReal.ofReal
        (if ∀ l : Fin m, (p 0, p l.succ) ∉ SL k then xc (p 0) else 0) := by
      funext p; simp only [termL, isLeftmost_0_iff]
    rw [e]
    exact measurable_single m (SL k) (measurableSet_SL k) _ measurable_xc
  have e : (fun p : Fin (m + 1) → Pt => ENNReal.ofReal (termL k p i)) =
      (fun p => ENNReal.ofReal (termL k p 0)) ∘ (fun p => p ∘ Equiv.swap 0 i) := by
    funext p
    simp only [Function.comp_apply, termL, isLeftmost_comp, Equiv.swap_apply_left]
  rw [e]
  exact h0.comp (measurable_pi_lambda _ fun l => measurable_pi_apply _)

theorem lintegral_termR_i (k m : ℕ) (i : Fin (m + 1)) :
    ∫⁻ p, ENNReal.ofReal (termR k p i) ∂(μ (m + 1)) = ∫⁻ p, ENNReal.ofReal (termR k p 0) ∂(μ (m + 1)) := by
  have e : ∀ p : Fin (m + 1) → Pt, termR k p i = termR k (p ∘ Equiv.swap 0 i) 0 := by
    intro p; simp only [termR, isRightmost_comp, Function.comp_apply, Equiv.swap_apply_left]
  simp_rw [e]
  exact lintegral_μ_comp_perm _ _ (fun p => ENNReal.ofReal (termR k p 0))

theorem lintegral_termL_i (k m : ℕ) (i : Fin (m + 1)) :
    ∫⁻ p, ENNReal.ofReal (termL k p i) ∂(μ (m + 1)) = ∫⁻ p, ENNReal.ofReal (termL k p 0) ∂(μ (m + 1)) := by
  have e : ∀ p : Fin (m + 1) → Pt, termL k p i = termL k (p ∘ Equiv.swap 0 i) 0 := by
    intro p; simp only [termL, isLeftmost_comp, Function.comp_apply, Equiv.swap_apply_left]
  simp_rw [e]
  exact lintegral_μ_comp_perm _ _ (fun p => ENNReal.ofReal (termL k p 0))

/-- **B2.** -/
theorem lintegral_endSum_le (n k : ℕ) (hn : 2 ≤ n) (hk : 1 ≤ k) :
    ∫⁻ p, ENNReal.ofReal (endSum k p) ∂(μ n) ≤ ENNReal.ofReal (endTerm n k) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set J : ℝ := ∫ t in (0:ℝ)..1, t * (1 - t / k) ^ m with hJ
  have hJ0 : 0 ≤ J := endInt_nonneg k m hk
  have hpt : ∀ p : Fin (m + 1) → Pt, ENNReal.ofReal (endSum k p) ≤
      ∑ i, (ENNReal.ofReal (termR k p i) + ENNReal.ofReal (termL k p i)) := by
    intro p
    refine (ofReal_sum_le' _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    exact ENNReal.ofReal_add_le
  calc ∫⁻ p, ENNReal.ofReal (endSum k p) ∂(μ (m + 1))
      ≤ ∫⁻ p, ∑ i, (ENNReal.ofReal (termR k p i) + ENNReal.ofReal (termL k p i)) ∂(μ (m + 1)) :=
        lintegral_mono hpt
    _ = ∑ i : Fin (m + 1), (∫⁻ p, ENNReal.ofReal (termR k p 0) ∂(μ (m + 1)) +
          ∫⁻ p, ENNReal.ofReal (termL k p 0) ∂(μ (m + 1))) := by
        have hm : ∀ i : Fin (m + 1), Measurable fun p : Fin (m + 1) → Pt =>
            ENNReal.ofReal (termR k p i) + ENNReal.ofReal (termL k p i) :=
          fun i => (measurable_termR k m i).add (measurable_termL k m i)
        rw [lintegral_finsetSum _ fun i _ => hm i]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [lintegral_add_left (measurable_termR k m i), lintegral_termR_i, lintegral_termL_i]
    _ ≤ ∑ _i : Fin (m + 1), (ENNReal.ofReal J + ENNReal.ofReal J) := by
        gcongr with i
        · exact lintegral_termR_0 k m hk
        · exact lintegral_termL_0 k m hk
    _ = ENNReal.ofReal (endTerm (m + 1) k) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_add hJ0 hJ0, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        simp only [endTerm, hJ, Nat.add_sub_cancel]
        push_cast
        ring


theorem ν_vline (c : ℝ) : ν {b | xc b = c} = 0 := by
  have hpre : {b : Pt | xc b = c} = (@WithLp.ofLp 2 (Fin 2 → ℝ)) ⁻¹' {v | v 0 = c} := by
    ext b; simp [xc]
  have h : volume {b : Pt | xc b = c} = 0 := by
    rw [hpre, (PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage
      (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const).nullMeasurableSet]
    rw [volume_pi]
    exact Measure.pi_hyperplane (fun _ : Fin 2 => (volume : Measure ℝ)) (0 : Fin 2) c
  have hle : ν {b | xc b = c} ≤ volume {b : Pt | xc b = c} := Measure.restrict_le_self _
  exact le_antisymm (hle.trans h.le) (by positivity)

theorem μ_tie01 (m : ℕ) : μ (m + 2) {p | xc (p 0) = xc (p 1)} = 0 := by
  have hS : MeasurableSet {p : Fin (m + 2) → Pt | xc (p 0) = xc (p 1)} :=
    measurableSet_eq_fun (measurable_xc.comp (measurable_pi_apply 0))
      (measurable_xc.comp (measurable_pi_apply 1))
  have hT : MeasurableSet {z : Pt × Pt | xc z.1 = xc z.2} :=
    measurableSet_eq_fun (measurable_xc.comp measurable_fst) (measurable_xc.comp measurable_snd)
  have hf : Measurable (Function.uncurry fun (a : Pt) (r : Fin (m + 1) → Pt) =>
      {z : Pt × Pt | xc z.1 = xc z.2}.indicator (1 : Pt × Pt → ENNReal) (a, r 0)) :=
    (measurable_one.indicator hT).comp (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))
  rw [← lintegral_indicator_one hS]
  have e : ({p : Fin (m + 2) → Pt | xc (p 0) = xc (p 1)}.indicator (1 : (Fin (m + 2) → Pt) → ENNReal)) =
      fun p => (fun (a : Pt) (r : Fin (m + 1) → Pt) =>
        {z : Pt × Pt | xc z.1 = xc z.2}.indicator (1 : Pt × Pt → ENNReal) (a, r 0)) (p 0) (Fin.tail p) := by
    funext p
    by_cases h : xc (p 0) = xc (p 1)
    · rw [Set.indicator_of_mem (show p ∈ {p : Fin (m + 2) → Pt | xc (p 0) = xc (p 1)} from h)]
      beta_reduce
      rw [Set.indicator_of_mem (show (p 0, Fin.tail p 0) ∈ {z : Pt × Pt | xc z.1 = xc z.2} from h)]
      rfl
    · rw [Set.indicator_of_notMem (show p ∉ {p : Fin (m + 2) → Pt | xc (p 0) = xc (p 1)} from h)]
      beta_reduce
      rw [Set.indicator_of_notMem (show (p 0, Fin.tail p 0) ∉ {z : Pt × Pt | xc z.1 = xc z.2} from h)]
  rw [e, lintegral_μ_succ (m + 1) _ hf]
  have inner : ∀ a : Pt, ∫⁻ r : Fin (m + 1) → Pt,
      {z : Pt × Pt | xc z.1 = xc z.2}.indicator (1 : Pt × Pt → ENNReal) (a, r 0) ∂(μ (m + 1)) = 0 := by
    intro a
    have hg : Measurable (Function.uncurry fun (b : Pt) (_r : Fin m → Pt) =>
        {z : Pt × Pt | xc z.1 = xc z.2}.indicator (1 : Pt × Pt → ENNReal) (a, b)) :=
      (measurable_one.indicator hT).comp (measurable_const.prodMk measurable_fst)
    refine (lintegral_μ_succ m (fun (b : Pt) (_r : Fin m → Pt) =>
      {z : Pt × Pt | xc z.1 = xc z.2}.indicator (1 : Pt × Pt → ENNReal) (a, b)) hg).trans ?_
    simp only [lintegral_const, measure_univ, mul_one]
    have e2 : (fun b : Pt => {z : Pt × Pt | xc z.1 = xc z.2}.indicator (1 : Pt × Pt → ENNReal) (a, b)) =
        {b : Pt | xc b = xc a}.indicator 1 := by
      funext b
      by_cases hb : xc a = xc b
      · rw [Set.indicator_of_mem (show (a, b) ∈ {z : Pt × Pt | xc z.1 = xc z.2} from hb),
          Set.indicator_of_mem (show b ∈ {b : Pt | xc b = xc a} from hb.symm)]; rfl
      · rw [Set.indicator_of_notMem (show (a, b) ∉ {z : Pt × Pt | xc z.1 = xc z.2} from hb),
          Set.indicator_of_notMem (show b ∉ {b : Pt | xc b = xc a} from fun h => hb h.symm)]
    rw [e2, lintegral_indicator_one (measurableSet_eq_fun measurable_xc measurable_const)]
    exact ν_vline (xc a)
  simp [inner]

theorem μ_tie (m : ℕ) (i j : Fin (m + 2)) (hij : i ≠ j) :
    μ (m + 2) {p | xc (p i) = xc (p j)} = 0 := by
  obtain ⟨π, h0, h1⟩ := exists_perm_01 i j hij
  have hS : ∀ a b : Fin (m + 2), MeasurableSet {p : Fin (m + 2) → Pt | xc (p a) = xc (p b)} :=
    fun a b => measurableSet_eq_fun (measurable_xc.comp (measurable_pi_apply a))
      (measurable_xc.comp (measurable_pi_apply b))
  rw [← lintegral_indicator_one (hS i j)]
  have e : ∀ p : Fin (m + 2) → Pt,
      {p : Fin (m + 2) → Pt | xc (p i) = xc (p j)}.indicator (1 : (Fin (m + 2) → Pt) → ENNReal) p =
        {p : Fin (m + 2) → Pt | xc (p 0) = xc (p 1)}.indicator 1 (p ∘ π) := by
    intro p
    by_cases h : xc (p i) = xc (p j)
    · rw [Set.indicator_of_mem (show p ∈ {p : Fin (m + 2) → Pt | xc (p i) = xc (p j)} from h),
        Set.indicator_of_mem (show p ∘ π ∈ {p : Fin (m + 2) → Pt | xc (p 0) = xc (p 1)} by
          simp [h0, h1, h])]
      rfl
    · rw [Set.indicator_of_notMem (show p ∉ {p : Fin (m + 2) → Pt | xc (p i) = xc (p j)} from h),
        Set.indicator_of_notMem (show p ∘ π ∉ {p : Fin (m + 2) → Pt | xc (p 0) = xc (p 1)} by
          simp [h0, h1, h])]
  simp_rw [e]
  rw [lintegral_μ_comp_perm _ π, lintegral_indicator_one (hS 0 1)]
  exact μ_tie01 m

/-- Ties in the `x`-coordinate have probability zero. -/
theorem ae_injective_xc (n : ℕ) : ∀ᵐ p ∂(μ n), Function.Injective fun i => xc (p i) := by
  by_cases hn : n < 2
  · refine Filter.Eventually.of_forall fun p i j _ => ?_
    have : Subsingleton (Fin n) := by
      constructor; intro a b; ext; omega
    exact Subsingleton.elim i j
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have h : ∀ i j : Fin (m + 2), ∀ᵐ p ∂(μ (m + 2)), i ≠ j → xc (p i) ≠ xc (p j) := by
    intro i j
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun p h => absurd hij h
    · have := (measure_eq_zero_iff_ae_notMem.1 (μ_tie m i j hij))
      filter_upwards [this] with p hp _
      exact hp
  have h2 := ae_all_iff.2 fun i => ae_all_iff.2 (h i)
  filter_upwards [h2] with p hp i j hxy
  by_contra hne
  exact hp i j hne hxy


/-! ## Part B3 — assembly of the expectation bound -/

theorem ofReal_succSum_eq (k m : ℕ) (p : Fin (m + 2) → Pt) :
    ENNReal.ofReal (succSum k p) = ∑ i, ∑ j, ENNReal.ofReal (termS k p i j) := by
  show ENNReal.ofReal (∑ i, ∑ j, termS k p i j) = _
  rw [ENNReal.ofReal_sum_of_nonneg fun i _ => Finset.sum_nonneg fun j _ => termS_nonneg k p i j]
  exact Finset.sum_congr rfl fun i _ => ENNReal.ofReal_sum_of_nonneg fun j _ => termS_nonneg k p i j

theorem lintegral_S2_le (k m : ℕ) (hk : 1 ≤ k) :
    ∫⁻ p, ∑ i, (ENNReal.ofReal (termR k p i) + ENNReal.ofReal (termL k p i)) ∂(μ (m + 1)) ≤
      ENNReal.ofReal (endTerm (m + 1) k) := by
  set J : ℝ := ∫ t in (0:ℝ)..1, t * (1 - t / k) ^ m with hJ
  have hJ0 : 0 ≤ J := endInt_nonneg k m hk
  have hm : ∀ i : Fin (m + 1), Measurable fun p : Fin (m + 1) → Pt =>
      ENNReal.ofReal (termR k p i) + ENNReal.ofReal (termL k p i) :=
    fun i => (measurable_termR k m i).add (measurable_termL k m i)
  calc ∫⁻ p, ∑ i, (ENNReal.ofReal (termR k p i) + ENNReal.ofReal (termL k p i)) ∂(μ (m + 1))
      = ∑ i : Fin (m + 1), (∫⁻ p, ENNReal.ofReal (termR k p 0) ∂(μ (m + 1)) +
          ∫⁻ p, ENNReal.ofReal (termL k p 0) ∂(μ (m + 1))) := by
        rw [lintegral_finsetSum _ fun i _ => hm i]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [lintegral_add_left (measurable_termR k m i), lintegral_termR_i, lintegral_termL_i]
    _ ≤ ∑ _i : Fin (m + 1), (ENNReal.ofReal J + ENNReal.ofReal J) := by
        gcongr with i
        · exact lintegral_termR_0 k m hk
        · exact lintegral_termL_0 k m hk
    _ = ENNReal.ofReal (endTerm (m + 1) k) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_add hJ0 hJ0, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        simp only [endTerm, hJ, Nat.add_sub_cancel]
        push_cast
        ring

theorem mainTerm_nonneg (n k : ℕ) (hn : 2 ≤ n) (hk : 1 ≤ k) : 0 ≤ mainTerm n k := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  unfold mainTerm
  refine mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by linarith)) (by positivity)) ?_
  refine intervalIntegral.integral_nonneg (by positivity) fun t ht => ?_
  refine mul_nonneg (mul_nonneg zero_le_two (by linarith [ht.2])) ?_
  refine intervalIntegral.integral_nonneg zero_le_one fun s hs => ?_
  have : 0 ≤ 1 - s / k := by rw [sub_nonneg, div_le_one (by linarith)]; linarith [hs.2]
  exact mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg this _)

theorem endTerm_nonneg (n k : ℕ) (hk : 1 ≤ k) : 0 ≤ endTerm n k :=
  mul_nonneg (by positivity) (endInt_nonneg k (n - 1) hk)

/-- **B3.** Combine A1, B1, B2. -/
theorem L_le_terms (n k : ℕ) (hn : 2 ≤ n) (hk : 1 ≤ k) :
    L n ≤ mainTerm n k + 2 * endTerm n k + 4 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  set S1 : (Fin (m + 2) → Pt) → ENNReal := fun p => ∑ i, ∑ j, ENNReal.ofReal (termS k p i j)
    with hS1
  set S2 : (Fin (m + 2) → Pt) → ENNReal :=
    fun p => ∑ i, (ENNReal.ofReal (termR k p i) + ENNReal.ofReal (termL k p i)) with hS2
  have hS1m : Measurable S1 := Finset.measurable_sum _ fun i _ =>
    Finset.measurable_sum _ fun j _ => measurable_termS_ij k m i j
  have hS2m : Measurable S2 := Finset.measurable_sum _ fun i _ =>
    (measurable_termR k (m + 1) i).add (measurable_termL k (m + 1) i)
  have hB1 : ∫⁻ p, S1 p ∂(μ (m + 2)) ≤ ENNReal.ofReal (mainTerm (m + 2) k) := by
    have h := lintegral_succSum_le (m + 2) k hn hk
    simp_rw [ofReal_succSum_eq] at h
    exact h
  have hB2 : ∫⁻ p, S2 p ∂(μ (m + 2)) ≤ ENNReal.ofReal (endTerm (m + 2) k) :=
    lintegral_S2_le k (m + 1) hk
  have hpt : ∀ᵐ p ∂(μ (m + 2)), ENNReal.ofReal (tourLength p) ≤ S1 p + 2 * S2 p + 4 := by
    filter_upwards [ae_mem_unitSquare (m + 2), ae_injective_xc (m + 2)] with p hp hx
    have hA := tourLength_le_strip k (m + 2) hk p hp hx
    have e2 : ENNReal.ofReal (endSum k p) ≤ S2 p := by
      show ENNReal.ofReal (∑ i, (termR k p i + termL k p i)) ≤ _
      exact (ofReal_sum_le' _ _).trans (Finset.sum_le_sum fun i _ => ENNReal.ofReal_add_le)
    calc ENNReal.ofReal (tourLength p)
        ≤ ENNReal.ofReal (succSum k p + 2 * endSum k p + 4) := ENNReal.ofReal_le_ofReal hA
      _ ≤ ENNReal.ofReal (succSum k p) + ENNReal.ofReal (2 * endSum k p) + ENNReal.ofReal 4 :=
          ENNReal.ofReal_add_le.trans (by gcongr; exact ENNReal.ofReal_add_le)
      _ = ENNReal.ofReal (succSum k p) + 2 * ENNReal.ofReal (endSum k p) + 4 := by
          rw [ENNReal.ofReal_mul zero_le_two]; simp
      _ ≤ S1 p + 2 * S2 p + 4 := by
          rw [ofReal_succSum_eq]; gcongr
  have hm0 := mainTerm_nonneg (m + 2) k hn hk
  have he0 := endTerm_nonneg (m + 2) k hk
  have hint : ∫⁻ p, ENNReal.ofReal (tourLength p) ∂(μ (m + 2)) ≤
      ENNReal.ofReal (mainTerm (m + 2) k + 2 * endTerm (m + 2) k + 4) := by
    calc ∫⁻ p, ENNReal.ofReal (tourLength p) ∂(μ (m + 2))
        ≤ ∫⁻ p, (S1 p + 2 * S2 p + 4) ∂(μ (m + 2)) := lintegral_mono_ae hpt
      _ = ∫⁻ p, S1 p ∂(μ (m + 2)) + 2 * ∫⁻ p, S2 p ∂(μ (m + 2)) + 4 := by
          rw [lintegral_add_right _ measurable_const, lintegral_add_left hS1m,
            lintegral_const_mul _ hS2m, lintegral_const, measure_univ, mul_one]
      _ ≤ ENNReal.ofReal (mainTerm (m + 2) k) + 2 * ENNReal.ofReal (endTerm (m + 2) k) + 4 := by
          gcongr
      _ = ENNReal.ofReal (mainTerm (m + 2) k + 2 * endTerm (m + 2) k + 4) := by
          rw [ENNReal.ofReal_add (by positivity) (by norm_num), ENNReal.ofReal_add hm0 (by positivity),
            ENNReal.ofReal_mul zero_le_two]
          simp
  have hL : L (m + 2) = ∫ p, tourLength p ∂(μ (m + 2)) := rfl
  rw [hL, integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun p => tourLength_nonneg p)
    (continuous_tourLength _).aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hint

/-! ## Part C — analysis and numerics -/

/-- The rescaled BHH integral, truncated at `u ≤ U`, with the strip parameter
`c = √n / k` bracketed in `[1.732, 1.7321]` and decay rate `c (n-2)/n ≥ 1.7319`.
For `U → ∞` its value is ≈ 0.797909. -/
def envelope (U : ℝ) : ℝ :=
  ∫ τ in (0:ℝ)..1.7321, (1.7321 - τ) *
    ∫ u in (0:ℝ)..U, Real.sqrt (u ^ 2 + τ ^ 2) * Real.exp (-(1.7319 * u))

def Qf (u K : ℝ) : ℝ := (u ^ 2 + K) / 1.7319 + 2 * u / 1.7319 ^ 2 + 2 / 1.7319 ^ 3

lemma Qf_nonneg {u K : ℝ} (hu : 0 ≤ u) (hK : 0 ≤ K) : 0 ≤ Qf u K := by
  unfold Qf; positivity

lemma sqrt_le_amgm {X w : ℝ} (hX : 0 ≤ X) (hw : 0 < w) :
    Real.sqrt X ≤ (X + w ^ 2) / (2 * w) := by
  rw [le_div_iff₀ (by positivity)]
  have h := Real.sq_sqrt hX
  nlinarith [sq_nonneg (Real.sqrt X - w), Real.sqrt_nonneg X]

lemma hasDerivAt_anti (K u : ℝ) :
    HasDerivAt (fun u => -(Real.exp (-(1.7319 * u)) * Qf u K))
      ((u ^ 2 + K) * Real.exp (-(1.7319 * u))) u := by
  have h1 : HasDerivAt (fun u : ℝ => Real.exp (-(1.7319 * u)))
      (Real.exp (-(1.7319 * u)) * (-(1.7319 : ℝ))) u := by
    have := (((hasDerivAt_id u).const_mul (1.7319 : ℝ)).neg).exp
    simpa using this
  have h2 : HasDerivAt (fun u => Qf u K) (2 * u / 1.7319 + 2 / 1.7319 ^ 2) u := by
    unfold Qf
    have := ((((hasDerivAt_pow 2 u).add_const K).div_const (1.7319 : ℝ)).add
      (((hasDerivAt_id u).const_mul (2 : ℝ)).div_const ((1.7319 : ℝ) ^ 2))).add_const
      (2 / (1.7319 : ℝ) ^ 3)
    exact this.congr_deriv (by simp)
  exact ((h1.mul h2).neg).congr_deriv (by unfold Qf; ring)

lemma integrand_cont (τ : ℝ) :
    Continuous fun u : ℝ => Real.sqrt (u ^ 2 + τ ^ 2) * Real.exp (-(1.7319 * u)) := by
  fun_prop

lemma cell_le (τ u0 u1 w : ℝ) (h01 : u0 ≤ u1) (hw : 0 < w) :
    ∫ u in u0..u1, Real.sqrt (u ^ 2 + τ ^ 2) * Real.exp (-(1.7319 * u)) ≤
      (Real.exp (-(1.7319 * u0)) * Qf u0 (τ ^ 2 + w ^ 2) -
        Real.exp (-(1.7319 * u1)) * Qf u1 (τ ^ 2 + w ^ 2)) / (2 * w) := by
  have hint : ∫ u in u0..u1, (u ^ 2 + (τ ^ 2 + w ^ 2)) * Real.exp (-(1.7319 * u)) =
      Real.exp (-(1.7319 * u0)) * Qf u0 (τ ^ 2 + w ^ 2) -
        Real.exp (-(1.7319 * u1)) * Qf u1 (τ ^ 2 + w ^ 2) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_anti _ x)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    ring
  calc ∫ u in u0..u1, Real.sqrt (u ^ 2 + τ ^ 2) * Real.exp (-(1.7319 * u))
      ≤ ∫ u in u0..u1, (u ^ 2 + (τ ^ 2 + w ^ 2)) * Real.exp (-(1.7319 * u)) / (2 * w) := by
        apply intervalIntegral.integral_mono_on h01
          ((integrand_cont τ).intervalIntegrable _ _)
          (Continuous.intervalIntegrable (by fun_prop) _ _)
        intro u _
        have h := sqrt_le_amgm (X := u ^ 2 + τ ^ 2) (by positivity) hw
        calc Real.sqrt (u ^ 2 + τ ^ 2) * Real.exp (-(1.7319 * u))
            ≤ (u ^ 2 + τ ^ 2 + w ^ 2) / (2 * w) * Real.exp (-(1.7319 * u)) :=
              mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
          _ = _ := by ring
    _ = _ := by rw [intervalIntegral.integral_div, hint]

lemma tail_le (τ u0 V w : ℝ) (hu0 : 0 ≤ u0) (h : u0 ≤ V) (hw : 0 < w) :
    ∫ u in u0..V, Real.sqrt (u ^ 2 + τ ^ 2) * Real.exp (-(1.7319 * u)) ≤
      Real.exp (-(1.7319 * u0)) * Qf u0 (τ ^ 2 + w ^ 2) / (2 * w) := by
  refine (cell_le τ u0 V w h hw).trans ?_
  have : 0 ≤ Real.exp (-(1.7319 * V)) * Qf V (τ ^ 2 + w ^ 2) :=
    mul_nonneg (Real.exp_pos _).le (Qf_nonneg (by linarith) (by positivity))
  gcongr
  linarith

/-- The inner integral up to `V ≥ u N` is bounded by the sum of cell bounds. -/
lemma inner_le (τ : ℝ) (N : ℕ) (u : ℕ → ℝ) (hu0 : u 0 = 0)
    (hmono : ∀ i < N, u i ≤ u (i + 1)) (hnn : ∀ i ≤ N, 0 ≤ u i)
    (w : ℕ → ℝ) (hw : ∀ i < N, 0 < w i) (hi lo : ℕ → ℝ)
    (hhi : ∀ i ≤ N, Real.exp (-(1.7319 * u i)) ≤ hi i)
    (hlo : ∀ i ≤ N, lo i ≤ Real.exp (-(1.7319 * u i)))
    (W : ℝ) (hW : 0 < W) (V : ℝ) (hV : u N ≤ V) :
    ∫ x in (0:ℝ)..V, Real.sqrt (x ^ 2 + τ ^ 2) * Real.exp (-(1.7319 * x)) ≤
      (∑ i ∈ Finset.range N, (hi i * Qf (u i) (τ ^ 2 + w i ^ 2) -
          lo (i + 1) * Qf (u (i + 1)) (τ ^ 2 + w i ^ 2)) / (2 * w i)) +
        hi N * Qf (u N) (τ ^ 2 + W ^ 2) / (2 * W) := by
  have hcont := integrand_cont τ
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := u N)
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  rw [← hu0, ← intervalIntegral.sum_integral_adjacent_intervals
    (fun k _ => hcont.intervalIntegrable _ _)]
  gcongr with i hiN
  · have hiN' := Finset.mem_range.1 hiN
    refine (cell_le τ _ _ _ (hmono i hiN') (hw i hiN')).trans ?_
    have hq0 := Qf_nonneg (K := τ ^ 2 + w i ^ 2) (hnn i hiN'.le) (by positivity)
    have hq1 := Qf_nonneg (K := τ ^ 2 + w i ^ 2) (hnn (i + 1) hiN') (by positivity)
    have hwi := hw i hiN'
    gcongr
    · exact hhi i hiN'.le
    · exact hlo (i + 1) hiN'
  · refine (tail_le τ _ _ _ (hnn N le_rfl) hV hW).trans ?_
    have hq := Qf_nonneg (K := τ ^ 2 + W ^ 2) (hnn N le_rfl) (by positivity)
    gcongr
    exact hhi N le_rfl

/-- Chain bound for powers. -/
lemma pow_sq_le_chain (r rU : ℝ) (hr0 : 0 ≤ r) (hrU : r ≤ rU) (N : ℕ) (hi : ℕ → ℝ)
    (h0 : 1 ≤ hi 0) (hstep : ∀ i < N, hi i * rU ^ (2 * i + 1) ≤ hi (i + 1)) :
    ∀ i ≤ N, r ^ (i ^ 2) ≤ hi i := by
  intro i
  induction i with
  | zero => intro _; simpa using h0
  | succ i ih =>
    intro hiN
    have h1 := ih (by omega)
    have hsq : (i + 1) ^ 2 = i ^ 2 + (2 * i + 1) := by ring
    rw [hsq, pow_add]
    have hh0 : 0 ≤ hi i := (pow_nonneg hr0 _).trans h1
    calc r ^ (i ^ 2) * r ^ (2 * i + 1) ≤ hi i * rU ^ (2 * i + 1) := by
          gcongr
      _ ≤ hi (i + 1) := hstep i (by omega)

lemma pow_sq_ge_chain (r rL : ℝ) (hrL0 : 0 ≤ rL) (hrL : rL ≤ r) (N : ℕ) (lo : ℕ → ℝ)
    (h0 : lo 0 ≤ 1) (hstep : ∀ i < N, lo (i + 1) ≤ lo i * rL ^ (2 * i + 1)) :
    ∀ i ≤ N, lo i ≤ r ^ (i ^ 2) := by
  intro i
  induction i with
  | zero => intro _; simpa using h0
  | succ i ih =>
    intro hiN
    have h1 := ih (by omega)
    have hsq : (i + 1) ^ 2 = i ^ 2 + (2 * i + 1) := by ring
    rw [hsq, pow_add]
    calc lo (i + 1) ≤ lo i * rL ^ (2 * i + 1) := hstep i (by omega)
      _ ≤ r ^ (i ^ 2) * r ^ (2 * i + 1) := by
          have : 0 ≤ r := hrL0.trans hrL
          gcongr


/-- The `u`-grid `u_i = i² / 75` (so `u_30 = 12`). -/
def uF (i : ℕ) : ℝ := (i : ℝ) ^ 2 / 75

/-- The `τ`-grid `t_j = 1.7321 j / 8`. -/
def tF (j : ℕ) : ℝ := 1.7321 * j / 8

/-- Antiderivative of `(1.7321 - τ) (al + be τ²)`. -/
def Gpoly (al be τ : ℝ) : ℝ :=
  1.7321 * al * τ - al * τ ^ 2 / 2 + 1.7321 * be * τ ^ 3 / 3 - be * τ ^ 4 / 4

/-! ### Generated tables (BHH/gen_numerics.py); certified total = 0.800295272 -/

def rU : ℝ := 0.977172579760417937

def rL : ℝ := 0.977172579760417931

/-- upper bounds for `exp (-(1.7319 * (i^2/75)))` -/
def hiT : ℕ → ℝ
  | 0 => 1
  | 1 => 0.97717257976042
  | 2 => 0.91176955660295
  | 3 => 0.81234674833712
  | 4 => 0.69109913466373
  | 5 => 0.56141213482268
  | 6 => 0.43547756478924
  | 7 => 0.32254648938618
  | 8 => 0.22811896723327
  | 9 => 0.15405401366168
  | 10 => 0.09934069233298
  | 11 => 0.061167945072887
  | 12 => 0.03596359867492
  | 13 => 0.020190400707993
  | 14 => 0.010823538778772
  | 15 => 0.0055403367215893
  | 16 => 0.0027079808380768
  | 17 => 0.0012638558910535
  | 18 => 0.00056323815985036
  | 19 => 0.00023967852780268
  | 20 => 0.000097388736079963
  | 21 => 0.000037785996006534
  | 22 => 0.000013998953236028
  | 23 => 0.0000049522526702744
  | 24 => 0.0000016728329358033
  | 25 => 0.0000005395663907729
  | 26 => 0.00000016618038200009
  | 27 => 0.000000048871667749701
  | 28 => 0.000000013723886255284
  | 29 => 0.0000000036799303925978
  | 30 => 0.00000000094220334449861
  | _ => 0

/-- lower bounds for `exp (-(1.7319 * (i^2/75)))` -/
def loT : ℕ → ℝ
  | 0 => 1
  | 1 => 0.97717257976041
  | 2 => 0.91176955660293
  | 3 => 0.81234674833709
  | 4 => 0.6910991346637
  | 5 => 0.56141213482264
  | 6 => 0.4354775647892
  | 7 => 0.32254648938614
  | 8 => 0.22811896723323
  | 9 => 0.15405401366164
  | 10 => 0.099340692332953
  | 11 => 0.06116794507287
  | 12 => 0.035963598674909
  | 13 => 0.020190400707986
  | 14 => 0.010823538778767
  | 15 => 0.0055403367215866
  | 16 => 0.0027079808380754
  | 17 => 0.0012638558910527
  | 18 => 0.00056323815985
  | 19 => 0.00023967852780251
  | 20 => 0.000097388736079893
  | 21 => 0.000037785996006505
  | 22 => 0.000013998953236016
  | 23 => 0.0000049522526702701
  | 24 => 0.0000016728329358017
  | 25 => 0.00000053956639077237
  | 26 => 0.00000016618038199992
  | 27 => 0.00000004887166774965
  | 28 => 0.000000013723886255269
  | 29 => 0.0000000036799303925937
  | 30 => 0.00000000094220334449755
  | _ => 0

/-- AM-GM parameters for τ-cell 0 -/
def wT0 : ℕ → ℝ
  | 0 => 0.1253
  | 1 => 0.1299
  | 2 => 0.1534
  | 3 => 0.2101
  | 4 => 0.3026
  | 5 => 0.4276
  | 6 => 0.5825
  | 7 => 0.7659
  | 8 => 0.977
  | 9 => 1.216
  | 10 => 1.481
  | 11 => 1.774
  | 12 => 2.093
  | 13 => 2.439
  | 14 => 2.812
  | 15 => 3.212
  | 16 => 3.638
  | 17 => 4.091
  | 18 => 4.571
  | 19 => 5.078
  | 20 => 5.611
  | 21 => 6.171
  | 22 => 6.757
  | 23 => 7.37
  | 24 => 8.01
  | 25 => 8.677
  | 26 => 9.37
  | 27 => 10.09
  | 28 => 10.84
  | 29 => 11.61
  | _ => 0

/-- AM-GM parameters for τ-cell 1 -/
def wT1 : ℕ → ℝ
  | 0 => 0.3309
  | 1 => 0.3327
  | 2 => 0.3425
  | 3 => 0.3714
  | 4 => 0.4305
  | 5 => 0.5259
  | 6 => 0.6581
  | 7 => 0.8248
  | 8 => 1.024
  | 9 => 1.254
  | 10 => 1.513
  | 11 => 1.8
  | 12 => 2.115
  | 13 => 2.458
  | 14 => 2.829
  | 15 => 3.226
  | 16 => 3.651
  | 17 => 4.103
  | 18 => 4.581
  | 19 => 5.087
  | 20 => 5.619
  | 21 => 6.178
  | 22 => 6.764
  | 23 => 7.377
  | 24 => 8.016
  | 25 => 8.682
  | 26 => 9.375
  | 27 => 10.1
  | 28 => 10.85
  | 29 => 11.62
  | _ => 0

/-- AM-GM parameters for τ-cell 2 -/
def wT2 : ℕ → ℝ
  | 0 => 0.545
  | 1 => 0.5461
  | 2 => 0.5521
  | 3 => 0.5705
  | 4 => 0.6106
  | 5 => 0.6813
  | 6 => 0.7878
  | 7 => 0.9316
  | 8 => 1.112
  | 9 => 1.327
  | 10 => 1.573
  | 11 => 1.851
  | 12 => 2.159
  | 13 => 2.496
  | 14 => 2.862
  | 15 => 3.255
  | 16 => 3.677
  | 17 => 4.126
  | 18 => 4.602
  | 19 => 5.105
  | 20 => 5.636
  | 21 => 6.193
  | 22 => 6.778
  | 23 => 7.39
  | 24 => 8.028
  | 25 => 8.693
  | 26 => 9.385
  | 27 => 10.11
  | 28 => 10.85
  | 29 => 11.63
  | _ => 0

/-- AM-GM parameters for τ-cell 3 -/
def wT3 : ℕ → ℝ
  | 0 => 0.7605
  | 1 => 0.7612
  | 2 => 0.7656
  | 3 => 0.7789
  | 4 => 0.8088
  | 5 => 0.8634
  | 6 => 0.9497
  | 7 => 1.072
  | 8 => 1.232
  | 9 => 1.429
  | 10 => 1.66
  | 11 => 1.926
  | 12 => 2.223
  | 13 => 2.552
  | 14 => 2.91
  | 15 => 3.298
  | 16 => 3.715
  | 17 => 4.159
  | 18 => 4.632
  | 19 => 5.133
  | 20 => 5.661
  | 21 => 6.216
  | 22 => 6.799
  | 23 => 7.409
  | 24 => 8.045
  | 25 => 8.709
  | 26 => 9.4
  | 27 => 10.12
  | 28 => 10.87
  | 29 => 11.64
  | _ => 0

/-- AM-GM parameters for τ-cell 4 -/
def wT4 : ℕ → ℝ
  | 0 => 0.9764
  | 1 => 0.977
  | 2 => 0.9804
  | 3 => 0.9908
  | 4 => 1.015
  | 5 => 1.059
  | 6 => 1.13
  | 7 => 1.235
  | 8 => 1.376
  | 9 => 1.554
  | 10 => 1.77
  | 11 => 2.021
  | 12 => 2.306
  | 13 => 2.624
  | 14 => 2.974
  | 15 => 3.355
  | 16 => 3.765
  | 17 => 4.204
  | 18 => 4.673
  | 19 => 5.169
  | 20 => 5.694
  | 21 => 6.246
  | 22 => 6.826
  | 23 => 7.434
  | 24 => 8.069
  | 25 => 8.731
  | 26 => 9.42
  | 27 => 10.14
  | 28 => 10.88
  | 29 => 11.65
  | _ => 0

/-- AM-GM parameters for τ-cell 5 -/
def wT5 : ℕ → ℝ
  | 0 => 1.193
  | 1 => 1.193
  | 2 => 1.196
  | 3 => 1.205
  | 4 => 1.224
  | 5 => 1.261
  | 6 => 1.322
  | 7 => 1.412
  | 8 => 1.537
  | 9 => 1.699
  | 10 => 1.898
  | 11 => 2.134
  | 12 => 2.406
  | 13 => 2.712
  | 14 => 3.052
  | 15 => 3.424
  | 16 => 3.827
  | 17 => 4.26
  | 18 => 4.722
  | 19 => 5.214
  | 20 => 5.735
  | 21 => 6.284
  | 22 => 6.86
  | 23 => 7.465
  | 24 => 8.098
  | 25 => 8.758
  | 26 => 9.445
  | 27 => 10.16
  | 28 => 10.91
  | 29 => 11.67
  | _ => 0

/-- AM-GM parameters for τ-cell 6 -/
def wT6 : ℕ → ℝ
  | 0 => 1.409
  | 1 => 1.41
  | 2 => 1.412
  | 3 => 1.419
  | 4 => 1.436
  | 5 => 1.467
  | 6 => 1.52
  | 7 => 1.599
  | 8 => 1.71
  | 9 => 1.857
  | 10 => 2.041
  | 11 => 2.262
  | 12 => 2.52
  | 13 => 2.814
  | 14 => 3.143
  | 15 => 3.505
  | 16 => 3.899
  | 17 => 4.325
  | 18 => 4.782
  | 19 => 5.268
  | 20 => 5.784
  | 21 => 6.328
  | 22 => 6.901
  | 23 => 7.503
  | 24 => 8.132
  | 25 => 8.79
  | 26 => 9.475
  | 27 => 10.19
  | 28 => 10.93
  | 29 => 11.7
  | _ => 0

/-- AM-GM parameters for τ-cell 7 -/
def wT7 : ℕ → ℝ
  | 0 => 1.626
  | 1 => 1.626
  | 2 => 1.628
  | 3 => 1.634
  | 4 => 1.649
  | 5 => 1.676
  | 6 => 1.722
  | 7 => 1.793
  | 8 => 1.892
  | 9 => 2.026
  | 10 => 2.195
  | 11 => 2.403
  | 12 => 2.647
  | 13 => 2.928
  | 14 => 3.246
  | 15 => 3.597
  | 16 => 3.983
  | 17 => 4.4
  | 18 => 4.85
  | 19 => 5.33
  | 20 => 5.84
  | 21 => 6.38
  | 22 => 6.949
  | 23 => 7.546
  | 24 => 8.173
  | 25 => 8.827
  | 26 => 9.509
  | 27 => 10.22
  | 28 => 10.96
  | 29 => 11.73
  | _ => 0

/-- per-cell bounds (constant part), τ-cell 0 -/
def aT0 : ℕ → ℝ
  | 0 => 0.00082886120942
  | 1 => 0.00263140921441
  | 2 => 0.00585707247039
  | 3 => 0.01203362925975
  | 4 => 0.02058176444662
  | 5 => 0.02954617727143
  | 6 => 0.03683026859977
  | 7 => 0.04088938193553
  | 8 => 0.04112320949117
  | 9 => 0.03790201744106
  | 10 => 0.0322759836288
  | 11 => 0.02554717998063
  | 12 => 0.01887986957392
  | 13 => 0.01307240038162
  | 14 => 0.00850346265136
  | 15 => 0.00520797004741
  | 16 => 0.00300845348501
  | 17 => 0.00164156028307
  | 18 => 0.00084710780348
  | 19 => 0.00041384241191
  | 20 => 0.00019156867347
  | 21 => 0.00008408782381
  | 22 => 0.00003502202197
  | 23 => 0.00001384820987
  | 24 => 0.00000520120608
  | 25 => 0.00000185635283
  | 26 => 0.00000062983819
  | 27 => 0.00000020321589
  | 28 => 0.00000006237053
  | 29 => 0.00000001821418
  | 30 => 0.00000000685759
  | _ => 0

/-- per-cell bounds (τ² part), τ-cell 0 -/
def bT0 : ℕ → ℝ
  | 0 => 0.05259602887499
  | 1 => 0.14535697101252
  | 2 => 0.18711467879754
  | 3 => 0.16660742014033
  | 4 => 0.12372991423779
  | 5 => 0.08502653074035
  | 6 => 0.0559712139329
  | 7 => 0.0355937475795
  | 8 => 0.02188594902329
  | 9 => 0.01298992657534
  | 10 => 0.00744124408728
  | 11 => 0.00410174839065
  | 12 => 0.00217569351819
  | 13 => 0.00110873947558
  | 14 => 0.00054241175948
  | 15 => 0.00025457718313
  | 16 => 0.00011460122708
  | 17 => 0.00004944231952
  | 18 => 0.00002043573695
  | 19 => 0.0000080896222
  | 20 => 0.00000306671311
  | 21 => 0.00000111283839
  | 22 => 0.00000038653026
  | 23 => 0.00000012846261
  | 24 => 0.00000004084574
  | 25 => 0.00000001242327
  | 26 => 0.00000000361442
  | 27 => 0.00000000100567
  | 28 => 0.0000000002675
  | 29 => 0.00000000006808
  | 30 => 0.00000000002267
  | _ => 0

/-- per-cell bounds (constant part), τ-cell 1 -/
def aT1 : ℕ → ℝ
  | 0 => 0.0021818978654
  | 1 => 0.00635175241381
  | 2 => 0.01048212139608
  | 3 => 0.01564760226148
  | 4 => 0.022621626018
  | 5 => 0.03050329866125
  | 6 => 0.03724581026204
  | 7 => 0.04106613124225
  | 8 => 0.04119955316423
  | 9 => 0.03793575946611
  | 10 => 0.03229119771379
  | 11 => 0.02555381051361
  | 12 => 0.01888280510912
  | 13 => 0.01307371556593
  | 14 => 0.00850406681263
  | 15 => 0.00520821478644
  | 16 => 0.00300856198225
  | 17 => 0.00164160657519
  | 18 => 0.00084712482283
  | 19 => 0.00041384900517
  | 20 => 0.00019157105057
  | 21 => 0.00008408863597
  | 22 => 0.00003502232408
  | 23 => 0.00001384831785
  | 24 => 0.00000520123758
  | 25 => 0.00000185636141
  | 26 => 0.00000062984085
  | 27 => 0.00000020321753
  | 28 => 0.00000006237101
  | 29 => 0.0000000182143
  | 30 => 0.00000000685759
  | _ => 0

/-- per-cell bounds (τ² part), τ-cell 1 -/
def bT1 : ℕ → ℝ
  | 0 => 0.01991623577527
  | 1 => 0.05675344314556
  | 2 => 0.0838055232921
  | 3 => 0.0942493779523
  | 4 => 0.08697020220292
  | 5 => 0.06913357015511
  | 6 => 0.04954145588196
  | 7 => 0.03305195352951
  | 8 => 0.02088141815991
  | 9 => 0.01259629243669
  | 10 => 0.00728386152892
  | 11 => 0.0040425009139
  | 12 => 0.00215306219081
  | 13 => 0.0011001690728
  | 14 => 0.00053915230388
  | 15 => 0.00025347238445
  | 16 => 0.00011419317013
  | 17 => 0.0000492977161
  | 18 => 0.00002039112718
  | 19 => 0.00000807530991
  | 20 => 0.00000306234691
  | 21 => 0.00000111157749
  | 22 => 0.00000038613024
  | 23 => 0.00000012834071
  | 24 => 0.00000004081517
  | 25 => 0.00000001241611
  | 26 => 0.00000000361249
  | 27 => 0.00000000100468
  | 28 => 0.00000000026726
  | 29 => 0.00000000006802
  | 30 => 0.00000000002267
  | _ => 0

/-- per-cell bounds (constant part), τ-cell 2 -/
def aT2 : ℕ → ℝ
  | 0 => 0.0035924163627
  | 1 => 0.01035388571706
  | 2 => 0.01625112614879
  | 3 => 0.02169314780596
  | 4 => 0.02744647070035
  | 5 => 0.03355684996666
  | 6 => 0.03887491388752
  | 7 => 0.0418474737244
  | 8 => 0.04155358072901
  | 9 => 0.0380916105125
  | 10 => 0.03235672897611
  | 11 => 0.02558171302394
  | 12 => 0.01889462177063
  | 13 => 0.01307863255313
  | 14 => 0.00850609845125
  | 15 => 0.00520902831267
  | 16 => 0.00300889164828
  | 17 => 0.00164173401253
  | 18 => 0.00084717353676
  | 19 => 0.0004138660327
  | 20 => 0.00019157737706
  | 21 => 0.00008409073604
  | 22 => 0.00003502303971
  | 23 => 0.00001384855115
  | 24 => 0.00000520130926
  | 25 => 0.00000185638242
  | 26 => 0.00000062984672
  | 27 => 0.00000020321937
  | 28 => 0.00000006237101
  | 29 => 0.00000001821444
  | 30 => 0.00000000685759
  | _ => 0

/-- per-cell bounds (τ² part), τ-cell 2 -/
def bT2 : ℕ → ℝ
  | 0 => 0.0120922613175
  | 1 => 0.03457584789329
  | 2 => 0.05198947967315
  | 3 => 0.06135708846886
  | 4 => 0.06131783827114
  | 5 => 0.05336466247552
  | 6 => 0.04138516389428
  | 7 => 0.0292628287582
  | 8 => 0.01922893183071
  | 9 => 0.01190335396806
  | 10 => 0.0070060282856
  | 11 => 0.00393111920314
  | 12 => 0.00210918320221
  | 13 => 0.0010834197039
  | 14 => 0.00053293566306
  | 15 => 0.00025121410514
  | 16 => 0.0001133857123
  | 17 => 0.0000490229106
  | 18 => 0.00002029807771
  | 19 => 0.00000804683673
  | 20 => 0.00000305310988
  | 21 => 0.00000110888515
  | 22 => 0.00000038533269
  | 23 => 0.00000012811494
  | 24 => 0.00000004075416
  | 25 => 0.0000000124004
  | 26 => 0.00000000360864
  | 27 => 0.00000000100368
  | 28 => 0.00000000026726
  | 29 => 0.00000000006797
  | 30 => 0.00000000002267
  | _ => 0

/-- per-cell bounds (constant part), τ-cell 3 -/
def aT3 : ℕ → ℝ
  | 0 => 0.00501242034099
  | 1 => 0.01440336748191
  | 2 => 0.02226664289825
  | 3 => 0.02852696220464
  | 4 => 0.03374358935323
  | 5 => 0.03832433935925
  | 6 => 0.04190479847197
  | 7 => 0.043520377617
  | 8 => 0.04238804519309
  | 9 => 0.03848001555301
  | 10 => 0.03252823904264
  | 11 => 0.02565576418006
  | 12 => 0.018925133559
  | 13 => 0.01309118971268
  | 14 => 0.00851100918195
  | 15 => 0.00521097585957
  | 16 => 0.00300963810077
  | 17 => 0.00164200427095
  | 18 => 0.00084727321679
  | 19 => 0.00041390259039
  | 20 => 0.0001915898033
  | 21 => 0.00008409490205
  | 22 => 0.00003502438997
  | 23 => 0.00001384896836
  | 24 => 0.00000520143047
  | 25 => 0.00000185641824
  | 26 => 0.00000062985685
  | 27 => 0.0000002032214
  | 28 => 0.00000006237214
  | 29 => 0.00000001821459
  | 30 => 0.00000000685759
  | _ => 0

/-- per-cell bounds (τ² part), τ-cell 3 -/
def bT3 : ℕ → ℝ
  | 0 => 0.00866572310064
  | 1 => 0.02480540007164
  | 2 => 0.03749136850515
  | 3 => 0.04494058155281
  | 4 => 0.04629163210727
  | 5 => 0.04210950259969
  | 6 => 0.03433003276394
  | 7 => 0.02543027170815
  | 8 => 0.01735598392512
  | 9 => 0.01105370938811
  | 10 => 0.00663884487546
  | 11 => 0.00377803823729
  | 12 => 0.00204845997911
  | 13 => 0.00105964560382
  | 14 => 0.00052414497171
  | 15 => 0.00024793872414
  | 16 => 0.00011222591228
  | 17 => 0.00004863393343
  | 18 => 0.00002016661347
  | 19 => 0.00000800294204
  | 20 => 0.00000303962679
  | 21 => 0.00000110478213
  | 22 => 0.00000038414251
  | 23 => 0.0000001277864
  | 24 => 0.00000004066804
  | 25 => 0.00000001237762
  | 26 => 0.00000000360288
  | 27 => 0.00000000100269
  | 28 => 0.00000000026677
  | 29 => 0.00000000006791
  | 30 => 0.00000000002267
  | _ => 0

/-- per-cell bounds (constant part), τ-cell 4 -/
def aT4 : ℕ → ℝ
  | 0 => 0.00643514942038
  | 1 => 0.01847134102783
  | 2 => 0.02836830354866
  | 3 => 0.03567441766562
  | 4 => 0.04076062783338
  | 5 => 0.04415521780265
  | 6 => 0.04603736116907
  | 7 => 0.04607707934792
  | 8 => 0.04378803737728
  | 9 => 0.03917489238953
  | 10 => 0.03285587844942
  | 11 => 0.0257998195201
  | 12 => 0.01898627475356
  | 13 => 0.01311604480782
  | 14 => 0.00852098646017
  | 15 => 0.00521486978293
  | 16 => 0.00301108455488
  | 17 => 0.00164253484534
  | 18 => 0.00084746556628
  | 19 => 0.00041396732154
  | 20 => 0.00019161182299
  | 21 => 0.00008410203803
  | 22 => 0.00003502660969
  | 23 => 0.00001384965416
  | 24 => 0.00000520164063
  | 25 => 0.00000185647759
  | 26 => 0.00000062987281
  | 27 => 0.00000020322606
  | 28 => 0.00000006237278
  | 29 => 0.00000001821476
  | 30 => 0.00000000685759
  | _ => 0

/-- per-cell bounds (τ² part), τ-cell 4 -/
def bT4 : ℕ → ℝ
  | 0 => 0.00674957232491
  | 1 => 0.01932637721037
  | 2 => 0.0292772253443
  | 3 => 0.03532924805358
  | 4 => 0.036887361624
  | 5 => 0.03433177010819
  | 6 => 0.0288524178017
  | 7 => 0.02207388766894
  | 8 => 0.01553966002598
  | 9 => 0.01016457575008
  | 10 => 0.00622626129562
  | 11 => 0.00360044613806
  | 12 => 0.00197472963294
  | 13 => 0.00103056996225
  | 14 => 0.00051286545651
  | 15 => 0.00024372635238
  | 16 => 0.00011073552832
  | 17 => 0.00004811335137
  | 18 => 0.0000199896755
  | 19 => 0.00000794720478
  | 20 => 0.00000302201041
  | 21 => 0.00000109947578
  | 22 => 0.00000038262305
  | 23 => 0.00000012735666
  | 24 => 0.00000004054708
  | 25 => 0.00000001234643
  | 26 => 0.00000000359523
  | 27 => 0.00000000100071
  | 28 => 0.00000000026652
  | 29 => 0.00000000006785
  | 30 => 0.00000000002267
  | _ => 0

/-- per-cell bounds (constant part), τ-cell 5 -/
def aT5 : ℕ → ℝ
  | 0 => 0.00786253239199
  | 1 => 0.02254552434294
  | 2 => 0.0345157442422
  | 3 => 0.04299594188852
  | 4 => 0.04811473625537
  | 5 => 0.05059387914383
  | 6 => 0.05096164761687
  | 7 => 0.04934674729389
  | 8 => 0.04572584002143
  | 9 => 0.04021683428465
  | 10 => 0.03336620941412
  | 11 => 0.02603461195875
  | 12 => 0.01908897153962
  | 13 => 0.01315867060385
  | 14 => 0.00853811583148
  | 15 => 0.00522148627595
  | 16 => 0.00301358215689
  | 17 => 0.00164344801322
  | 18 => 0.0008477783056
  | 19 => 0.00041407569601
  | 20 => 0.00019164793102
  | 21 => 0.00008411380299
  | 22 => 0.00003503016968
  | 23 => 0.00001385071835
  | 24 => 0.00000520195501
  | 25 => 0.00000185656631
  | 26 => 0.00000062989671
  | 27 => 0.00000020323149
  | 28 => 0.00000006237501
  | 29 => 0.00000001821513
  | 30 => 0.00000000685759
  | _ => 0

/-- per-cell bounds (τ² part), τ-cell 5 -/
def bT5 : ℕ → ℝ
  | 0 => 0.00552412608386
  | 1 => 0.01582721754781
  | 2 => 0.02399949141099
  | 3 => 0.02904914437468
  | 4 => 0.03058878435324
  | 5 => 0.02883215269197
  | 6 => 0.0246620515249
  | 7 => 0.01930683517786
  | 8 => 0.01391188822105
  | 9 => 0.00929708694268
  | 10 => 0.00580636590793
  | 11 => 0.00340979458529
  | 12 => 0.0018926544196
  | 13 => 0.00099712963899
  | 14 => 0.00049975814799
  | 15 => 0.00023881481081
  | 16 => 0.00010894153753
  | 17 => 0.00004748087539
  | 18 => 0.00001978224346
  | 19 => 0.00000787861556
  | 20 => 0.0000030004058
  | 21 => 0.00000109282714
  | 22 => 0.00000038072667
  | 23 => 0.00000012682778
  | 24 => 0.00000004040188
  | 25 => 0.00000001230837
  | 26 => 0.00000000358572
  | 27 => 0.00000000099874
  | 28 => 0.00000000026579
  | 29 => 0.00000000006773
  | 30 => 0.00000000002267
  | _ => 0

/-- per-cell bounds (constant part), τ-cell 6 -/
def aT6 : ℕ → ℝ
  | 0 => 0.00928598350008
  | 1 => 0.02663989644995
  | 2 => 0.04068714898637
  | 3 => 0.05036380484851
  | 4 => 0.05571447141928
  | 5 => 0.05741686830224
  | 6 => 0.05639319639003
  | 7 => 0.05317526299934
  | 8 => 0.04812390045323
  | 9 => 0.04157415853403
  | 10 => 0.03406989210453
  | 11 => 0.02637146864615
  | 12 => 0.0192401882585
  | 13 => 0.0132233657421
  | 14 => 0.00856448879073
  | 15 => 0.00523175560325
  | 16 => 0.00301741457484
  | 17 => 0.00164484611151
  | 18 => 0.00084828027549
  | 19 => 0.00041424498873
  | 20 => 0.00019170353273
  | 21 => 0.00008413116455
  | 22 => 0.00003503557972
  | 23 => 0.00001385234169
  | 24 => 0.00000520240691
  | 25 => 0.00000185669391
  | 26 => 0.00000062993112
  | 27 => 0.0000002032411
  | 28 => 0.00000006237675
  | 29 => 0.00000001821579
  | 30 => 0.00000000685759
  | _ => 0

/-- per-cell bounds (τ² part), τ-cell 6 -/
def bT6 : ℕ → ℝ
  | 0 => 0.00467727637902
  | 1 => 0.01339139754222
  | 2 => 0.02032818111016
  | 3 => 0.02466823042388
  | 4 => 0.02607289139858
  | 5 => 0.02478346594722
  | 6 => 0.02144949481311
  | 7 => 0.01704893763048
  | 8 => 0.01250442818465
  | 9 => 0.00850605854368
  | 10 => 0.00539955046215
  | 11 => 0.00321684422857
  | 12 => 0.00180703433872
  | 13 => 0.00096098634717
  | 14 => 0.00048528853569
  | 15 => 0.00023329583801
  | 16 => 0.00010692979331
  | 17 => 0.00004676728998
  | 18 => 0.00001953403463
  | 19 => 0.00000779785526
  | 20 => 0.00000297498742
  | 21 => 0.00000108522847
  | 22 => 0.00000037846471
  | 23 => 0.00000012618545
  | 24 => 0.00000004023296
  | 25 => 0.00000001226356
  | 26 => 0.00000000357436
  | 27 => 0.0000000009958
  | 28 => 0.0000000002653
  | 29 => 0.00000000006756
  | 30 => 0.00000000002267
  | _ => 0

/-- per-cell bounds (constant part), τ-cell 7 -/
def aT7 : ℕ → ℝ
  | 0 => 0.01071603800783
  | 1 => 0.03071619405048
  | 2 => 0.04686612377932
  | 3 => 0.05779855164738
  | 4 => 0.06343749773464
  | 5 => 0.06450669020599
  | 6 => 0.06217711589654
  | 7 => 0.05742691434044
  | 8 => 0.05090354880231
  | 9 => 0.04322251258763
  | 10 => 0.03495480429017
  | 11 => 0.02681585109535
  | 12 => 0.01944596552561
  | 13 => 0.0133130800092
  | 14 => 0.00860194478457
  | 15 => 0.0052464767127
  | 16 => 0.0030230822669
  | 17 => 0.00164689065933
  | 18 => 0.00084900180085
  | 19 => 0.00041449056141
  | 20 => 0.00019178326023
  | 21 => 0.00008415674733
  | 22 => 0.00003504343794
  | 23 => 0.00001385459592
  | 24 => 0.00000520306995
  | 25 => 0.00000185687146
  | 26 => 0.00000062997761
  | 27 => 0.00000020325244
  | 28 => 0.00000006237976
  | 29 => 0.00000001821656
  | 30 => 0.00000000685759
  | _ => 0

/-- per-cell bounds (τ² part), τ-cell 7 -/
def bT7 : ℕ → ℝ
  | 0 => 0.00405306421774
  | 1 => 0.0116124665034
  | 2 => 0.01763107599972
  | 3 => 0.02142241063127
  | 4 => 0.0227050770457
  | 5 => 0.02169292633925
  | 6 => 0.01893335198369
  | 7 => 0.01520426730125
  | 8 => 0.01130157092799
  | 9 => 0.00779652059014
  | 10 => 0.00502072095365
  | 11 => 0.00302809057221
  | 12 => 0.00172033492012
  | 13 => 0.00092357089513
  | 14 => 0.00046988966965
  | 15 => 0.00022732886078
  | 16 => 0.00010467468344
  | 17 => 0.00004597012026
  | 18 => 0.00001926015538
  | 19 => 0.0000077071485
  | 20 => 0.00000294646015
  | 21 => 0.00000107638334
  | 22 => 0.00000037585047
  | 23 => 0.00000012546639
  | 24 => 0.00000004003113
  | 25 => 0.00000001221215
  | 26 => 0.00000000356158
  | 27 => 0.00000000099288
  | 28 => 0.00000000026458
  | 29 => 0.00000000006739
  | 30 => 0.00000000002267
  | _ => 0

/-- constant coefficients of the per-τ-cell bounds -/
def alT : ℕ → ℝ
  | 0 => 0.33795412637117
  | 1 => 0.35499301406635
  | 2 => 0.38313248177772
  | 3 => 0.4187382246231
  | 4 => 0.45968392243145
  | 5 => 0.50453899899647
  | 6 => 0.55233333932075
  | 7 => 0.60241559342544
  | _ => 0

/-- τ² coefficients of the per-τ-cell bounds -/
def beT : ℕ → ℝ
  | 0 => 0.90269411702633
  | 1 => 0.54246839485116
  | 2 => 0.39158684381854
  | 3 => 0.30696502186168
  | 4 => 0.25231216982217
  | 5 => 0.21403203754988
  | 6 => 0.18571901298475
  | 7 => 0.163924860832
  | _ => 0

lemma r_bounds : rL ≤ Real.exp (-(1.7319 / 75)) ∧ Real.exp (-(1.7319 / 75)) ≤ rU := by
  have hx : |(-(1.7319 / 75 : ℝ))| ≤ 1 := by
    rw [abs_le]; constructor <;> norm_num
  have h := Real.exp_bound hx (n := 8) (by norm_num)
  rw [abs_sub_le_iff] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num [rU, rL] at h ⊢
  constructor <;> linarith [h.1, h.2]

lemma exp_uF (i : ℕ) :
    Real.exp (-(1.7319 * uF i)) = Real.exp (-(1.7319 / 75)) ^ (i ^ 2) := by
  rw [← Real.exp_nat_mul]
  congr 1
  unfold uF
  push_cast
  ring

lemma hi_spec : ∀ i ≤ 30, Real.exp (-(1.7319 * uF i)) ≤ hiT i := by
  intro i hi
  rw [exp_uF]
  refine pow_sq_le_chain _ rU (Real.exp_pos _).le r_bounds.2 30 hiT (by norm_num [hiT]) ?_ i hi
  intro i hi
  interval_cases i <;> norm_num [hiT, rU]

lemma lo_spec : ∀ i ≤ 30, loT i ≤ Real.exp (-(1.7319 * uF i)) := by
  intro i hi
  rw [exp_uF]
  refine pow_sq_ge_chain _ rL (by norm_num [rL]) r_bounds.1 30 loT (by norm_num [loT]) ?_ i hi
  intro i hi
  interval_cases i <;> norm_num [loT, rL]

/-- The inner integral (for `V ≥ 12`) is at most `al + be τ²`, given per-cell numeric bounds. -/
lemma inner_poly (τ V : ℝ) (w : ℕ → ℝ) (hw : ∀ i < 30, 0 < w i) (al be : ℝ) (aT bT : ℕ → ℝ)
    (hAi : ∀ i < 30, (hiT i * Qf (uF i) (w i ^ 2) -
        loT (i + 1) * Qf (uF (i + 1)) (w i ^ 2)) / (2 * w i) ≤ aT i)
    (hAt : hiT 30 * Qf (uF 30) (12 ^ 2) / (2 * 12) ≤ aT 30)
    (hBi : ∀ i < 30, (hiT i - loT (i + 1)) / (1.7319 * (2 * w i)) ≤ bT i)
    (hBt : hiT 30 / (1.7319 * (2 * 12)) ≤ bT 30)
    (hal : ∑ i ∈ Finset.range 31, aT i ≤ al) (hbe : ∑ i ∈ Finset.range 31, bT i ≤ be)
    (hV : 12 ≤ V) :
    ∫ x in (0:ℝ)..V, Real.sqrt (x ^ 2 + τ ^ 2) * Real.exp (-(1.7319 * x)) ≤ al + be * τ ^ 2 := by
  have hA : (∑ i ∈ Finset.range 30, (hiT i * Qf (uF i) (w i ^ 2) -
        loT (i + 1) * Qf (uF (i + 1)) (w i ^ 2)) / (2 * w i)) +
        hiT 30 * Qf (uF 30) (12 ^ 2) / (2 * 12) ≤ al := by
    rw [Finset.sum_range_succ] at hal
    have := Finset.sum_le_sum (fun i hi => hAi i (Finset.mem_range.1 hi))
    linarith
  have hB : (∑ i ∈ Finset.range 30, (hiT i - loT (i + 1)) / (1.7319 * (2 * w i))) +
        hiT 30 / (1.7319 * (2 * 12)) ≤ be := by
    rw [Finset.sum_range_succ] at hbe
    have := Finset.sum_le_sum (fun i hi => hBi i (Finset.mem_range.1 hi))
    linarith
  have h := inner_le τ 30 uF (by simp [uF])
    (fun i _ => by unfold uF; gcongr; linarith) (fun i _ => by unfold uF; positivity)
    w hw hiT loT hi_spec lo_spec 12 (by norm_num) V (by norm_num [uF]; linarith)
  have hterm : ∀ i, (hiT i * Qf (uF i) (τ ^ 2 + w i ^ 2) -
      loT (i + 1) * Qf (uF (i + 1)) (τ ^ 2 + w i ^ 2)) / (2 * w i) =
      (hiT i * Qf (uF i) (w i ^ 2) - loT (i + 1) * Qf (uF (i + 1)) (w i ^ 2)) / (2 * w i) +
        τ ^ 2 * ((hiT i - loT (i + 1)) / (1.7319 * (2 * w i))) := by
    intro i; unfold Qf; ring
  have htail : hiT 30 * Qf (uF 30) (τ ^ 2 + 12 ^ 2) / (2 * 12) =
      hiT 30 * Qf (uF 30) (12 ^ 2) / (2 * 12) + τ ^ 2 * (hiT 30 / (1.7319 * (2 * 12))) := by
    unfold Qf; ring
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib, ← Finset.mul_sum,
    htail] at h
  have hB' := mul_le_mul_of_nonneg_left hB (sq_nonneg τ)
  nlinarith

lemma hw_0 : ∀ i < 30, 0 < wT0 i := by
  intro i hi; interval_cases i <;> norm_num [wT0]

set_option maxHeartbeats 1000000 in
lemma hAi_0 : ∀ i < 30, (hiT i * Qf (uF i) (wT0 i ^ 2) -
    loT (i + 1) * Qf (uF (i + 1)) (wT0 i ^ 2)) / (2 * wT0 i) ≤ aT0 i := by
  intro i hi; interval_cases i <;> norm_num [hiT, loT, wT0, Qf, uF, aT0]

set_option maxHeartbeats 1000000 in
lemma hBi_0 : ∀ i < 30, (hiT i - loT (i + 1)) / (1.7319 * (2 * wT0 i)) ≤ bT0 i := by
  intro i hi; interval_cases i <;> norm_num [hiT, loT, wT0, bT0]

lemma inner_poly_0 (τ V : ℝ) (hV : 12 ≤ V) :
    ∫ x in (0:ℝ)..V, Real.sqrt (x ^ 2 + τ ^ 2) * Real.exp (-(1.7319 * x)) ≤
      alT 0 + beT 0 * τ ^ 2 :=
  inner_poly τ V wT0 hw_0 _ _ aT0 bT0 hAi_0
    (by norm_num [hiT, Qf, uF, aT0]) hBi_0 (by norm_num [hiT, bT0])
    (by norm_num [Finset.sum_range_succ, aT0, alT])
    (by norm_num [Finset.sum_range_succ, bT0, beT]) hV

lemma hw_1 : ∀ i < 30, 0 < wT1 i := by
  intro i hi; interval_cases i <;> norm_num [wT1]

set_option maxHeartbeats 1000000 in
lemma hAi_1 : ∀ i < 30, (hiT i * Qf (uF i) (wT1 i ^ 2) -
    loT (i + 1) * Qf (uF (i + 1)) (wT1 i ^ 2)) / (2 * wT1 i) ≤ aT1 i := by
  intro i hi; interval_cases i <;> norm_num [hiT, loT, wT1, Qf, uF, aT1]

set_option maxHeartbeats 1000000 in
lemma hBi_1 : ∀ i < 30, (hiT i - loT (i + 1)) / (1.7319 * (2 * wT1 i)) ≤ bT1 i := by
  intro i hi; interval_cases i <;> norm_num [hiT, loT, wT1, bT1]

lemma inner_poly_1 (τ V : ℝ) (hV : 12 ≤ V) :
    ∫ x in (0:ℝ)..V, Real.sqrt (x ^ 2 + τ ^ 2) * Real.exp (-(1.7319 * x)) ≤
      alT 1 + beT 1 * τ ^ 2 :=
  inner_poly τ V wT1 hw_1 _ _ aT1 bT1 hAi_1
    (by norm_num [hiT, Qf, uF, aT1]) hBi_1 (by norm_num [hiT, bT1])
    (by norm_num [Finset.sum_range_succ, aT1, alT])
    (by norm_num [Finset.sum_range_succ, bT1, beT]) hV

lemma hw_2 : ∀ i < 30, 0 < wT2 i := by
  intro i hi; interval_cases i <;> norm_num [wT2]

set_option maxHeartbeats 1000000 in
lemma hAi_2 : ∀ i < 30, (hiT i * Qf (uF i) (wT2 i ^ 2) -
    loT (i + 1) * Qf (uF (i + 1)) (wT2 i ^ 2)) / (2 * wT2 i) ≤ aT2 i := by
  intro i hi; interval_cases i <;> norm_num [hiT, loT, wT2, Qf, uF, aT2]

set_option maxHeartbeats 1000000 in
lemma hBi_2 : ∀ i < 30, (hiT i - loT (i + 1)) / (1.7319 * (2 * wT2 i)) ≤ bT2 i := by
  intro i hi; interval_cases i <;> norm_num [hiT, loT, wT2, bT2]

lemma inner_poly_2 (τ V : ℝ) (hV : 12 ≤ V) :
    ∫ x in (0:ℝ)..V, Real.sqrt (x ^ 2 + τ ^ 2) * Real.exp (-(1.7319 * x)) ≤
      alT 2 + beT 2 * τ ^ 2 :=
  inner_poly τ V wT2 hw_2 _ _ aT2 bT2 hAi_2
    (by norm_num [hiT, Qf, uF, aT2]) hBi_2 (by norm_num [hiT, bT2])
    (by norm_num [Finset.sum_range_succ, aT2, alT])
    (by norm_num [Finset.sum_range_succ, bT2, beT]) hV

lemma hw_3 : ∀ i < 30, 0 < wT3 i := by
  intro i hi; interval_cases i <;> norm_num [wT3]

set_option maxHeartbeats 1000000 in
lemma hAi_3 : ∀ i < 30, (hiT i * Qf (uF i) (wT3 i ^ 2) -
    loT (i + 1) * Qf (uF (i + 1)) (wT3 i ^ 2)) / (2 * wT3 i) ≤ aT3 i := by
  intro i hi; interval_cases i <;> norm_num [hiT, loT, wT3, Qf, uF, aT3]

set_option maxHeartbeats 1000000 in
lemma hBi_3 : ∀ i < 30, (hiT i - loT (i + 1)) / (1.7319 * (2 * wT3 i)) ≤ bT3 i := by
  intro i hi; interval_cases i <;> norm_num [hiT, loT, wT3, bT3]

lemma inner_poly_3 (τ V : ℝ) (hV : 12 ≤ V) :
    ∫ x in (0:ℝ)..V, Real.sqrt (x ^ 2 + τ ^ 2) * Real.exp (-(1.7319 * x)) ≤
      alT 3 + beT 3 * τ ^ 2 :=
  inner_poly τ V wT3 hw_3 _ _ aT3 bT3 hAi_3
    (by norm_num [hiT, Qf, uF, aT3]) hBi_3 (by norm_num [hiT, bT3])
    (by norm_num [Finset.sum_range_succ, aT3, alT])
    (by norm_num [Finset.sum_range_succ, bT3, beT]) hV

lemma hw_4 : ∀ i < 30, 0 < wT4 i := by
  intro i hi; interval_cases i <;> norm_num [wT4]

set_option maxHeartbeats 1000000 in
lemma hAi_4 : ∀ i < 30, (hiT i * Qf (uF i) (wT4 i ^ 2) -
    loT (i + 1) * Qf (uF (i + 1)) (wT4 i ^ 2)) / (2 * wT4 i) ≤ aT4 i := by
  intro i hi; interval_cases i <;> norm_num [hiT, loT, wT4, Qf, uF, aT4]

set_option maxHeartbeats 1000000 in
lemma hBi_4 : ∀ i < 30, (hiT i - loT (i + 1)) / (1.7319 * (2 * wT4 i)) ≤ bT4 i := by
  intro i hi; interval_cases i <;> norm_num [hiT, loT, wT4, bT4]

lemma inner_poly_4 (τ V : ℝ) (hV : 12 ≤ V) :
    ∫ x in (0:ℝ)..V, Real.sqrt (x ^ 2 + τ ^ 2) * Real.exp (-(1.7319 * x)) ≤
      alT 4 + beT 4 * τ ^ 2 :=
  inner_poly τ V wT4 hw_4 _ _ aT4 bT4 hAi_4
    (by norm_num [hiT, Qf, uF, aT4]) hBi_4 (by norm_num [hiT, bT4])
    (by norm_num [Finset.sum_range_succ, aT4, alT])
    (by norm_num [Finset.sum_range_succ, bT4, beT]) hV

lemma hw_5 : ∀ i < 30, 0 < wT5 i := by
  intro i hi; interval_cases i <;> norm_num [wT5]

set_option maxHeartbeats 1000000 in
lemma hAi_5 : ∀ i < 30, (hiT i * Qf (uF i) (wT5 i ^ 2) -
    loT (i + 1) * Qf (uF (i + 1)) (wT5 i ^ 2)) / (2 * wT5 i) ≤ aT5 i := by
  intro i hi; interval_cases i <;> norm_num [hiT, loT, wT5, Qf, uF, aT5]

set_option maxHeartbeats 1000000 in
lemma hBi_5 : ∀ i < 30, (hiT i - loT (i + 1)) / (1.7319 * (2 * wT5 i)) ≤ bT5 i := by
  intro i hi; interval_cases i <;> norm_num [hiT, loT, wT5, bT5]

lemma inner_poly_5 (τ V : ℝ) (hV : 12 ≤ V) :
    ∫ x in (0:ℝ)..V, Real.sqrt (x ^ 2 + τ ^ 2) * Real.exp (-(1.7319 * x)) ≤
      alT 5 + beT 5 * τ ^ 2 :=
  inner_poly τ V wT5 hw_5 _ _ aT5 bT5 hAi_5
    (by norm_num [hiT, Qf, uF, aT5]) hBi_5 (by norm_num [hiT, bT5])
    (by norm_num [Finset.sum_range_succ, aT5, alT])
    (by norm_num [Finset.sum_range_succ, bT5, beT]) hV

lemma hw_6 : ∀ i < 30, 0 < wT6 i := by
  intro i hi; interval_cases i <;> norm_num [wT6]

set_option maxHeartbeats 1000000 in
lemma hAi_6 : ∀ i < 30, (hiT i * Qf (uF i) (wT6 i ^ 2) -
    loT (i + 1) * Qf (uF (i + 1)) (wT6 i ^ 2)) / (2 * wT6 i) ≤ aT6 i := by
  intro i hi; interval_cases i <;> norm_num [hiT, loT, wT6, Qf, uF, aT6]

set_option maxHeartbeats 1000000 in
lemma hBi_6 : ∀ i < 30, (hiT i - loT (i + 1)) / (1.7319 * (2 * wT6 i)) ≤ bT6 i := by
  intro i hi; interval_cases i <;> norm_num [hiT, loT, wT6, bT6]

lemma inner_poly_6 (τ V : ℝ) (hV : 12 ≤ V) :
    ∫ x in (0:ℝ)..V, Real.sqrt (x ^ 2 + τ ^ 2) * Real.exp (-(1.7319 * x)) ≤
      alT 6 + beT 6 * τ ^ 2 :=
  inner_poly τ V wT6 hw_6 _ _ aT6 bT6 hAi_6
    (by norm_num [hiT, Qf, uF, aT6]) hBi_6 (by norm_num [hiT, bT6])
    (by norm_num [Finset.sum_range_succ, aT6, alT])
    (by norm_num [Finset.sum_range_succ, bT6, beT]) hV

lemma hw_7 : ∀ i < 30, 0 < wT7 i := by
  intro i hi; interval_cases i <;> norm_num [wT7]

set_option maxHeartbeats 1000000 in
lemma hAi_7 : ∀ i < 30, (hiT i * Qf (uF i) (wT7 i ^ 2) -
    loT (i + 1) * Qf (uF (i + 1)) (wT7 i ^ 2)) / (2 * wT7 i) ≤ aT7 i := by
  intro i hi; interval_cases i <;> norm_num [hiT, loT, wT7, Qf, uF, aT7]

set_option maxHeartbeats 1000000 in
lemma hBi_7 : ∀ i < 30, (hiT i - loT (i + 1)) / (1.7319 * (2 * wT7 i)) ≤ bT7 i := by
  intro i hi; interval_cases i <;> norm_num [hiT, loT, wT7, bT7]

lemma inner_poly_7 (τ V : ℝ) (hV : 12 ≤ V) :
    ∫ x in (0:ℝ)..V, Real.sqrt (x ^ 2 + τ ^ 2) * Real.exp (-(1.7319 * x)) ≤
      alT 7 + beT 7 * τ ^ 2 :=
  inner_poly τ V wT7 hw_7 _ _ aT7 bT7 hAi_7
    (by norm_num [hiT, Qf, uF, aT7]) hBi_7 (by norm_num [hiT, bT7])
    (by norm_num [Finset.sum_range_succ, aT7, alT])
    (by norm_num [Finset.sum_range_succ, bT7, beT]) hV

lemma inner_poly_all : ∀ j < 8, ∀ τ V : ℝ, 12 ≤ V →
    ∫ x in (0:ℝ)..V, Real.sqrt (x ^ 2 + τ ^ 2) * Real.exp (-(1.7319 * x)) ≤
      alT j + beT j * τ ^ 2 := by
  intro j hj
  interval_cases j
  exacts [inner_poly_0, inner_poly_1, inner_poly_2, inner_poly_3, inner_poly_4, inner_poly_5, inner_poly_6, inner_poly_7]

lemma hasDerivAt_Gpoly (al be x : ℝ) :
    HasDerivAt (fun τ => Gpoly al be τ) ((1.7321 - x) * (al + be * x ^ 2)) x := by
  unfold Gpoly
  have := ((((hasDerivAt_id x).const_mul (1.7321 * al)).sub
    (((hasDerivAt_pow 2 x).const_mul al).div_const 2)).add
    (((hasDerivAt_pow 3 x).const_mul (1.7321 * be)).div_const 3)).sub
    (((hasDerivAt_pow 4 x).const_mul be).div_const 4)
  exact this.congr_deriv (by simp; ring)

lemma integral_Gpoly (al be s e : ℝ) :
    ∫ τ in s..e, (1.7321 - τ) * (al + be * τ ^ 2) = Gpoly al be e - Gpoly al be s :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_Gpoly al be x)
    (Continuous.intervalIntegrable (by fun_prop) _ _)

lemma envelope_le_sum (U : ℝ) (hU : 0 ≤ U)
    (hpoly : ∀ j < 8, ∀ τ V : ℝ, 12 ≤ V →
      ∫ x in (0:ℝ)..V, Real.sqrt (x ^ 2 + τ ^ 2) * Real.exp (-(1.7319 * x)) ≤
        alT j + beT j * τ ^ 2) :
    envelope U ≤ ∑ j ∈ Finset.range 8,
      (Gpoly (alT j) (beT j) (tF (j + 1)) - Gpoly (alT j) (beT j) (tF j)) := by
  set f : ℝ → ℝ := fun τ => (1.7321 - τ) *
    ∫ u in (0:ℝ)..U, Real.sqrt (u ^ 2 + τ ^ 2) * Real.exp (-(1.7319 * u)) with hf
  have hcont : Continuous f := by
    refine (continuous_const.sub continuous_id).mul ?_
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (by fun_prop) 0 U
  have henv : envelope U = ∫ τ in (tF 0)..(tF 8), f τ := by
    have h0 : tF 0 = 0 := by simp [tF]
    have h8 : tF 8 = 1.7321 := by norm_num [tF]
    rw [h0, h8]; rfl
  rw [henv, ← intervalIntegral.sum_integral_adjacent_intervals
    (fun k _ => hcont.intervalIntegrable _ _)]
  apply Finset.sum_le_sum
  intro j hj
  have hj' := Finset.mem_range.1 hj
  have htj : tF j ≤ tF (j + 1) := by unfold tF; push_cast; linarith
  have hjc : tF (j + 1) ≤ 1.7321 := by
    unfold tF
    have : ((j : ℝ) + 1) ≤ 8 := by exact_mod_cast hj'
    push_cast; linarith
  rw [← integral_Gpoly]
  apply intervalIntegral.integral_mono_on htj (hcont.intervalIntegrable _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  intro τ hτ
  have hc : 0 ≤ 1.7321 - τ := by linarith [hτ.2]
  have hcontu := integrand_cont τ
  have hFU : ∫ u in (0:ℝ)..U, Real.sqrt (u ^ 2 + τ ^ 2) * Real.exp (-(1.7319 * u)) ≤
      ∫ u in (0:ℝ)..(max U 12), Real.sqrt (u ^ 2 + τ ^ 2) * Real.exp (-(1.7319 * u)) :=
    intervalIntegral.integral_mono_interval le_rfl hU (le_max_left _ _)
      (ae_of_all _ fun u => mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le)
      (hcontu.intervalIntegrable _ _)
  exact mul_le_mul_of_nonneg_left (hFU.trans (hpoly j hj' τ _ (le_max_right _ _))) hc

theorem envelope_le (U : ℝ) (hU : 0 ≤ U) : envelope U ≤ 0.802 := by
  refine (envelope_le_sum U hU inner_poly_all).trans ?_
  norm_num [Finset.sum_range_succ, Gpoly, tF, alT, beT]


/-- Rescaled inner integral with exponential decay. -/
def c2_G (a r τ : ℝ) : ℝ :=
  ∫ u in (0:ℝ)..r, Real.sqrt (u ^ 2 + τ ^ 2) * Real.exp (-(a * u))

/-- Unscaled inner integral with exponential decay. -/
def c2_J (b t : ℝ) : ℝ :=
  ∫ s in (0:ℝ)..1, Real.sqrt (s ^ 2 + t ^ 2) * Real.exp (-(b * s))

theorem c2_G_cont (a r : ℝ) : Continuous (c2_G a r) := by
  unfold c2_G
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (by fun_prop : Continuous fun p : ℝ × ℝ =>
      Real.sqrt (p.2 ^ 2 + p.1 ^ 2) * Real.exp (-(a * p.2))) _ _

theorem c2_J_cont (b : ℝ) : Continuous (c2_J b) := by
  unfold c2_J
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (by fun_prop : Continuous fun p : ℝ × ℝ =>
      Real.sqrt (p.2 ^ 2 + p.1 ^ 2) * Real.exp (-(b * p.2))) _ _

theorem c2_I_cont (k m : ℕ) : Continuous fun t : ℝ =>
    ∫ s in (0:ℝ)..1, Real.sqrt (s ^ 2 + t ^ 2) * (1 - s / k) ^ m := by
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (by fun_prop : Continuous fun p : ℝ × ℝ =>
      Real.sqrt (p.2 ^ 2 + p.1 ^ 2) * (1 - p.2 / k) ^ m) _ _

theorem c2_G_nonneg (a r τ : ℝ) (hr : 0 ≤ r) : 0 ≤ c2_G a r τ :=
  intervalIntegral.integral_nonneg hr fun _ _ =>
    mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le

/-- `(1 - s/k)^m ≤ exp(-(m/k) s)` inside the inner integral. -/
theorem c2_I_le_J (k m : ℕ) (hk : 1 ≤ k) (t : ℝ) :
    ∫ s in (0:ℝ)..1, Real.sqrt (s ^ 2 + t ^ 2) * (1 - s / k) ^ m ≤
      c2_J ((m : ℝ) / k) t := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  unfold c2_J
  refine intervalIntegral.integral_mono_on zero_le_one
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _) fun s hs => ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  have h0 : 0 ≤ 1 - s / k := by
    rw [sub_nonneg, div_le_one (by linarith)]; linarith [hs.2]
  have e : Real.exp (-((m : ℝ) / k * s)) = Real.exp (-(s / k)) ^ m := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [e]
  exact pow_le_pow_left₀ h0 (Real.one_sub_le_exp_neg _) m

/-- Inner substitution `s = u / r`, `t = τ / r`. -/
theorem c2_G_eq (b r τ : ℝ) (hr : 0 < r) :
    c2_G (b / r) r τ = r ^ 2 * c2_J b (τ / r) := by
  unfold c2_G c2_J
  have h := intervalIntegral.integral_comp_div
    (f := fun s => Real.sqrt (s ^ 2 + (τ / r) ^ 2) * Real.exp (-(b * s)))
    (a := 0) (b := r) hr.ne'
  simp only [zero_div, div_self hr.ne', smul_eq_mul] at h
  have e : ∀ u : ℝ, Real.sqrt (u ^ 2 + τ ^ 2) * Real.exp (-(b / r * u)) =
      r * (Real.sqrt ((u / r) ^ 2 + (τ / r) ^ 2) * Real.exp (-(b * (u / r)))) := by
    intro u
    have hs : (u / r) ^ 2 + (τ / r) ^ 2 = (u ^ 2 + τ ^ 2) / r ^ 2 := by
      field_simp
    rw [hs, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hr.le]
    field_simp
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, h]
  ring

/-- Outer substitution `t = τ / r`. -/
theorem c2_outer_eq (b r : ℝ) (k : ℝ) (hr : 0 < r) (hk : 0 < k) :
    ∫ t in (0:ℝ)..(1 / k), 2 * (1 / k - t) * c2_J b t =
      (2 / r ^ 4) * ∫ τ in (0:ℝ)..(r / k), (r / k - τ) * c2_G (b / r) r τ := by
  have h := intervalIntegral.integral_comp_div
    (f := fun t => 2 * (1 / k - t) * c2_J b t) (a := 0) (b := r / k) hr.ne'
  simp only [zero_div, smul_eq_mul] at h
  have hrk : r / k / r = 1 / k := by field_simp
  rw [hrk] at h
  have e : ∀ τ : ℝ, (r / k - τ) * c2_G (b / r) r τ =
      (r ^ 3 / 2) * (2 * (1 / k - τ / r) * c2_J b (τ / r)) := by
    intro τ
    rw [c2_G_eq b r τ hr]
    field_simp
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, h]
  field_simp

/-- Monotonicity in the parameters and extension of the `τ`-range. -/
theorem c2_le_envelope (a r c : ℝ) (ha : 1.7319 ≤ a) (hr : 0 ≤ r) (hc0 : 0 ≤ c)
    (hc : c ≤ 1.7321) :
    ∫ τ in (0:ℝ)..c, (c - τ) * c2_G a r τ ≤ envelope r := by
  have hG : ∀ τ, c2_G a r τ ≤ c2_G 1.7319 r τ := by
    intro τ
    unfold c2_G
    refine intervalIntegral.integral_mono_on hr
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _) fun u hu => ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    exact Real.exp_le_exp.2 (by nlinarith [hu.1])
  have hcont : Continuous fun τ => (1.7321 - τ) * c2_G 1.7319 r τ :=
    (by fun_prop : Continuous fun τ : ℝ => 1.7321 - τ).mul (c2_G_cont _ _)
  have h1 : ∫ τ in (0:ℝ)..c, (c - τ) * c2_G a r τ ≤
      ∫ τ in (0:ℝ)..c, (1.7321 - τ) * c2_G 1.7319 r τ := by
    refine intervalIntegral.integral_mono_on hc0
      (((by fun_prop : Continuous fun τ : ℝ => c - τ).mul (c2_G_cont _ _)).intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _) fun τ hτ => ?_
    have h0 : 0 ≤ c - τ := by linarith [hτ.2]
    calc (c - τ) * c2_G a r τ ≤ (c - τ) * c2_G 1.7319 r τ :=
          mul_le_mul_of_nonneg_left (hG τ) h0
      _ ≤ (1.7321 - τ) * c2_G 1.7319 r τ :=
          mul_le_mul_of_nonneg_right (by linarith) (c2_G_nonneg _ _ _ hr)
  have h2 : 0 ≤ ∫ τ in c..(1.7321:ℝ), (1.7321 - τ) * c2_G 1.7319 r τ :=
    intervalIntegral.integral_nonneg hc fun τ hτ =>
      mul_nonneg (by linarith [hτ.2]) (c2_G_nonneg _ _ _ hr)
  have h3 := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := volume) 0 c) (hcont.intervalIntegrable (μ := volume) c 1.7321)
  have he : envelope r = ∫ τ in (0:ℝ)..1.7321, (1.7321 - τ) * c2_G 1.7319 r τ := rfl
  rw [he, ← h3]
  linarith

theorem mainTerm_le (n k : ℕ) (hn : 4000000000 ≤ n) (hk : 1 ≤ k)
    (hc1 : (1.732 : ℝ) ≤ Real.sqrt n / k) (hc2 : Real.sqrt n / k ≤ 1.7321) :
    mainTerm n k ≤ Real.sqrt n * ((2 / 1.732) * envelope (Real.sqrt n)) := by
  set r := Real.sqrt n with hrdef
  have hnR : (4000000000 : ℝ) ≤ n := by exact_mod_cast hn
  have hr2 : r ^ 2 = n := Real.sq_sqrt (by positivity)
  have hr : 0 < r := Real.sqrt_pos.2 (by linarith)
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkr : 1.732 * (k : ℝ) ≤ r := (le_div_iff₀ hkR).1 hc1
  set b : ℝ := ((n - 2 : ℕ) : ℝ) / k with hb
  have hn2 : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  -- step 1: (1 - s/k)^(n-2) ≤ exp
  have step1 : ∫ t in (0:ℝ)..(1 / (k : ℝ)), 2 * (1 / (k : ℝ) - t) *
        ∫ s in (0:ℝ)..1, Real.sqrt (s ^ 2 + t ^ 2) * (1 - s / k) ^ (n - 2) ≤
      ∫ t in (0:ℝ)..(1 / (k : ℝ)), 2 * (1 / (k : ℝ) - t) * c2_J b t := by
    refine intervalIntegral.integral_mono_on (by positivity)
      (((by fun_prop : Continuous fun t : ℝ => 2 * (1 / (k : ℝ) - t)).mul
        (c2_I_cont k (n - 2))).intervalIntegrable _ _)
      (((by fun_prop : Continuous fun t : ℝ => 2 * (1 / (k : ℝ) - t)).mul
        (c2_J_cont b)).intervalIntegrable _ _) fun t ht => ?_
    exact mul_le_mul_of_nonneg_left (c2_I_le_J k (n - 2) hk t) (by linarith [ht.2])
  -- step 2: rescale
  rw [c2_outer_eq b r k hr hkR] at step1
  -- step 3: compare with the envelope
  have ha : 1.7319 ≤ b / r := by
    rw [hb, div_div, le_div_iff₀ (by positivity), hn2]
    have : 1.732 * (k : ℝ) * r ≤ r * r := mul_le_mul_of_nonneg_right hkr hr.le
    nlinarith
  have hc0 : 0 ≤ r / k := by positivity
  set X := ∫ τ in (0:ℝ)..(r / k), (r / k - τ) * c2_G (b / r) r τ with hX
  have hXE : X ≤ envelope r := c2_le_envelope (b / r) r (r / k) ha hr.le hc0 hc2
  have hX0 : 0 ≤ X := intervalIntegral.integral_nonneg hc0 fun τ hτ =>
    mul_nonneg (by linarith [hτ.2]) (c2_G_nonneg _ _ _ hr.le)
  have hcoef0 : 0 ≤ (n : ℝ) * ((n : ℝ) - 1) * k := by
    have : (0:ℝ) ≤ (n : ℝ) - 1 := by linarith
    positivity
  have hcoef : (n : ℝ) * ((n : ℝ) - 1) * k * (2 / r ^ 4) ≤ r * (2 / 1.732) := by
    have hr4 : r ^ 4 = (n : ℝ) ^ 2 := by rw [← hr2]; ring
    have e1 : (n : ℝ) * ((n : ℝ) - 1) * k * (2 / r ^ 4) = 2 * k * (((n : ℝ) - 1) / n) := by
      rw [hr4]; field_simp
    have e2 : ((n : ℝ) - 1) / n ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    rw [e1]
    calc 2 * (k : ℝ) * (((n : ℝ) - 1) / n) ≤ 2 * k * 1 :=
          mul_le_mul_of_nonneg_left e2 (by positivity)
      _ ≤ r * (2 / 1.732) := by linarith
  unfold mainTerm
  calc (n : ℝ) * ((n : ℝ) - 1) * k *
        ∫ t in (0:ℝ)..(1 / (k : ℝ)), 2 * (1 / (k : ℝ) - t) *
          ∫ s in (0:ℝ)..1, Real.sqrt (s ^ 2 + t ^ 2) * (1 - s / k) ^ (n - 2)
      ≤ (n : ℝ) * ((n : ℝ) - 1) * k * ((2 / r ^ 4) * X) :=
        mul_le_mul_of_nonneg_left step1 hcoef0
    _ = ((n : ℝ) * ((n : ℝ) - 1) * k * (2 / r ^ 4)) * X := by ring
    _ ≤ (r * (2 / 1.732)) * X := mul_le_mul_of_nonneg_right hcoef hX0
    _ ≤ (r * (2 / 1.732)) * envelope r := mul_le_mul_of_nonneg_left hXE (by positivity)
    _ = r * ((2 / 1.732) * envelope r) := by ring


/-- **C3.** Substitute `u = 1 - t/k`:
`∫₀¹ t (1 - t/k)^(n-1) dt = k² ∫_{1-1/k}^1 (1-u) u^(n-1) du ≤ k² ∫₀¹ (1-u) u^(n-1) du
= k² / (n (n+1))`, so `endTerm n k ≤ 2 k² / (n+1)`. Polynomial integrals only. -/
theorem endTerm_le (n k : ℕ) (hn : 2 ≤ n) (hk : 1 ≤ k) :
    endTerm n k ≤ 2 * (k : ℝ) ^ 2 / ((n : ℝ) + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hk0 : (k : ℝ) ≠ 0 := hkR.ne'
  -- antiderivative of `t (1 - t/k)^m` via `v = 1 - t/k`
  set G : ℝ → ℝ := fun t =>
    -(k : ℝ) ^ 2 * ((1 - t / k) ^ (m + 1) / ((m : ℝ) + 1) - (1 - t / k) ^ (m + 2) / ((m : ℝ) + 2))
    with hGdef
  have hG : ∀ t, HasDerivAt G (t * (1 - t / k) ^ m) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => 1 - t / k) (-(1 / (k : ℝ))) t := by
      have := ((hasDerivAt_id t).div_const (k : ℝ)).const_sub (1 : ℝ)
      simpa [one_div] using this
    have h2 := (h1.pow (m + 1)).div_const ((m : ℝ) + 1)
    have h3 := (h1.pow (m + 2)).div_const ((m : ℝ) + 2)
    refine ((h2.sub h3).const_mul (-(k : ℝ) ^ 2)).congr_deriv ?_
    rw [show m + 1 - 1 = m by omega, show m + 2 - 1 = m + 1 by omega]
    have hm1 : (m:ℝ) + 1 ≠ 0 := by positivity
    have hm2 : (m:ℝ) + 2 ≠ 0 := by positivity
    push_cast
    generalize hA : (1 - t / (k:ℝ)) = A
    have ht : t = k * (1 - A) := by rw [← hA]; field_simp; ring
    subst ht
    rw [pow_succ]
    field_simp
    ring
  have hint : ∫ t in (0:ℝ)..1, t * (1 - t / k) ^ m = G 1 - G 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hG t)
    apply Continuous.intervalIntegrable
    fun_prop
  -- `G 1 ≤ 0`: with `v = 1 - 1/k ∈ [0,1]`, `v^(m+2)/(m+2) ≤ v^(m+1)/(m+1)`
  have hv0 : (0 : ℝ) ≤ 1 - 1 / k := by
    rw [sub_nonneg, div_le_one hkR]; exact_mod_cast hk
  have hv1 : 1 - 1 / (k : ℝ) ≤ 1 := by
    have : (0 : ℝ) ≤ 1 / k := by positivity
    linarith
  have hpow : (1 - 1 / (k : ℝ)) ^ (m + 2) ≤ (1 - 1 / (k : ℝ)) ^ (m + 1) :=
    pow_le_pow_of_le_one hv0 hv1 (by omega)
  have hG1 : G 1 ≤ 0 := by
    simp only [hGdef]
    have hA : (1 - 1 / (k : ℝ)) ^ (m + 2) / ((m : ℝ) + 2) ≤
        (1 - 1 / (k : ℝ)) ^ (m + 1) / ((m : ℝ) + 1) := by
      calc (1 - 1 / (k : ℝ)) ^ (m + 2) / ((m : ℝ) + 2)
          ≤ (1 - 1 / (k : ℝ)) ^ (m + 1) / ((m : ℝ) + 2) := by
            gcongr
        _ ≤ (1 - 1 / (k : ℝ)) ^ (m + 1) / ((m : ℝ) + 1) := by
            apply div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    have hk2 : (0 : ℝ) ≤ (k : ℝ) ^ 2 := by positivity
    nlinarith
  have hG0 : G 0 = -(k : ℝ) ^ 2 * (1 / ((m : ℝ) + 1) - 1 / ((m : ℝ) + 2)) := by
    simp [hGdef]
  -- assemble: `endTerm = 2 (m+1) (G 1 - G 0) ≤ 2 (m+1) k² /((m+1)(m+2)) = 2 k²/(m+2)`
  unfold endTerm
  simp only [Nat.add_sub_cancel]
  rw [hint, hG0]
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have key : 2 * ((m + 1 : ℕ) : ℝ) * (G 1 - -(k : ℝ) ^ 2 * (1 / ((m : ℝ) + 1) - 1 / ((m : ℝ) + 2)))
      ≤ 2 * ((m + 1 : ℕ) : ℝ) * ((k : ℝ) ^ 2 * (1 / ((m : ℝ) + 1) - 1 / ((m : ℝ) + 2))) := by
    gcongr
    linarith
  calc _ ≤ _ := key
    _ = 2 * (k : ℝ) ^ 2 / (((m + 1 : ℕ) : ℝ) + 1) := by
      push_cast
      field_simp
      ring

/-- The number of strips. -/
def kOf (n : ℕ) : ℕ := ⌈Real.sqrt ((n : ℝ) / 3)⌉₊

/-- **C4.** For large `n` the strip parameter lies in the bracket. -/
theorem kOf_bounds (n : ℕ) (hn : 4000000000 ≤ n) :
    1 ≤ kOf n ∧ (1.732 : ℝ) ≤ Real.sqrt n / kOf n ∧ Real.sqrt n / kOf n ≤ 1.7321 := by
  have hnR : (4000000000 : ℝ) ≤ n := by exact_mod_cast hn
  -- `s = √(n/3)`, and `s ≤ k < s + 1`
  have hs2 : Real.sqrt ((n : ℝ) / 3) ^ 2 = (n : ℝ) / 3 := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ Real.sqrt ((n : ℝ) / 3) := Real.sqrt_nonneg _
  have hsbig : (36514 : ℝ) ≤ Real.sqrt ((n : ℝ) / 3) := by nlinarith
  have hk_ge : Real.sqrt ((n : ℝ) / 3) ≤ (kOf n : ℝ) := Nat.le_ceil _
  have hk_lt : (kOf n : ℝ) < Real.sqrt ((n : ℝ) / 3) + 1 := Nat.ceil_lt_add_one hs0
  have hkpos : (0 : ℝ) < kOf n := by linarith
  have hk2 : (kOf n : ℝ) ^ 2 ≤ (Real.sqrt ((n : ℝ) / 3) + 1) ^ 2 := by nlinarith
  have hk2' : Real.sqrt ((n : ℝ) / 3) ^ 2 ≤ (kOf n : ℝ) ^ 2 := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · have : 0 < kOf n := by exact_mod_cast hkpos
    omega
  · -- `(1.732 k)^2 ≤ 2.999824 (s+1)^2 ≤ 3 s^2 = n` for `s ≥ 36514`
    rw [le_div_iff₀ hkpos, Real.le_sqrt (by positivity) (by positivity)]
    nlinarith
  · -- `n = 3 s^2 ≤ 3 k^2 ≤ (1.7321 k)^2`
    rw [div_le_iff₀ hkpos]
    have hsq : (n : ℝ) ≤ (1.7321 * (kOf n : ℝ)) ^ 2 := by nlinarith
    calc Real.sqrt n ≤ Real.sqrt ((1.7321 * (kOf n : ℝ)) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = 1.7321 * (kOf n : ℝ) := Real.sqrt_sq (by positivity)

/-- **C5.** With `k ≈ √(n/3)` the end term is about `2/3`. -/
theorem endTerm_kOf_le (n : ℕ) (hn : 4000000000 ≤ n) : endTerm n (kOf n) ≤ 1 := by
  obtain ⟨hk, -, -⟩ := kOf_bounds n hn
  have h := endTerm_le n (kOf n) (by omega) hk
  have hnR : (4000000000 : ℝ) ≤ n := by exact_mod_cast hn
  have hs2 : Real.sqrt ((n : ℝ) / 3) ^ 2 = (n : ℝ) / 3 := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ Real.sqrt ((n : ℝ) / 3) := Real.sqrt_nonneg _
  have hs1732 : (1732 : ℝ) ≤ Real.sqrt ((n : ℝ) / 3) := by nlinarith
  have hk_lt : (kOf n : ℝ) < Real.sqrt ((n : ℝ) / 3) + 1 := Nat.ceil_lt_add_one hs0
  have hk0 : (0 : ℝ) ≤ kOf n := Nat.cast_nonneg _
  have hk2 : (kOf n : ℝ) ^ 2 ≤ (Real.sqrt ((n : ℝ) / 3) + 1) ^ 2 := by nlinarith
  calc endTerm n (kOf n) ≤ 2 * (kOf n : ℝ) ^ 2 / ((n : ℝ) + 1) := h
    _ ≤ 1 := by
      rw [div_le_one (by positivity)]
      -- `2 (s+1)^2 ≤ 3 s^2 + 1 = n + 1` once `s ≥ 5`
      nlinarith

/-- **C6.** Assembly for a fixed large `n`:
`L n ≤ (2/1.732)·0.802·√n + 6 ≤ 0.927 √n`, since `√n ≥ 63245`. -/
theorem L_le_large (n : ℕ) (hn : 4000000000 ≤ n) : L n ≤ 0.927 * Real.sqrt n := by
  obtain ⟨hk, hc1, hc2⟩ := kOf_bounds n hn
  have h1 := L_le_terms n (kOf n) (by omega) hk
  have h2 := mainTerm_le n (kOf n) hn hk hc1 hc2
  have h3 := endTerm_kOf_le n hn
  have hs0 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have h4 : Real.sqrt n * ((2 / 1.732) * envelope (Real.sqrt n)) ≤
      Real.sqrt n * ((2 / 1.732) * 0.802) :=
    mul_le_mul_of_nonneg_left (by gcongr; exact envelope_le _ hs0) hs0
  have hs : (63245 : ℝ) ≤ Real.sqrt n := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    have : (4000000000 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  nlinarith

end BHH
end

theorem bhh_lt_point_nine_three :
    ∃ c < (0.93 : ℝ), ∀ᶠ n in Filter.atTop, L n ≤ c * Real.sqrt n := by
  refine ⟨0.927, by norm_num, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 4000000000] with n hn
  exact BHH.L_le_large n hn

#print axioms bhh_lt_point_nine_three
