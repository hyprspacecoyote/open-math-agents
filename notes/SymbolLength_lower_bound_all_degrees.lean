import FormalConjectures.Other.SymbolLengthMilnorKTheory

namespace OMA.GL

open MilnorK

variable {F : Type*} [Field F]

/-- A ring map `K_*(F)/p → Λ((Z/p)^ι)` from homomorphisms `L_i : F^× → Z` satisfying the
ultrametric trichotomy jointly. -/
theorem exists_ext_hom (p : ℕ) {ι : Type*} (L : ι → Additive Fˣ →+ ℤ)
    (htri : ∀ a b : Fˣ, (a : F) + b = 1 →
      (∀ i, L i (Additive.ofMul a) = L i (Additive.ofMul b)) ∨
      (∀ i, L i (Additive.ofMul a) = 0) ∨ (∀ i, L i (Additive.ofMul b) = 0)) :
    ∃ Ψ : MilnorK F p →+* ExteriorAlgebra (ZMod p) (ι → ZMod p), ∀ a : Fˣ,
      Ψ (of p a) = ExteriorAlgebra.ι (ZMod p) (fun i ↦ ((L i (Additive.ofMul a) : ℤ) : ZMod p)) := by
  let vec : Additive Fˣ →+ (ι → ZMod p) :=
    { toFun := fun a i ↦ ((L i a : ℤ) : ZMod p)
      map_zero' := by ext; simp
      map_add' := by intro a b; ext; simp }
  let φ : Additive Fˣ →ₗ[ℤ] ExteriorAlgebra (ZMod p) (ι → ZMod p) :=
    ((ExteriorAlgebra.ι (ZMod p)).restrictScalars ℤ).comp vec.toIntLinearMap
  let T := (TensorAlgebra.lift ℤ φ).toRingHom
  have hT : ∀ u, T (TensorAlgebra.ι ℤ u) = ExteriorAlgebra.ι (ZMod p) (vec u) := by
    intro u; simp [T, φ]
  refine ⟨RingQuot.lift ⟨T, ?_⟩, ?_⟩
  · intro x y h
    cases h with
    | steinberg a b hab =>
      rw [map_mul, hT, hT, map_zero]
      rcases htri a b hab with h | h | h
      · have : vec (Additive.ofMul b) = vec (Additive.ofMul a) := by
          ext i; simp [vec, h i]
        rw [this, ExteriorAlgebra.ι_sq_zero]
      · have : vec (Additive.ofMul a) = 0 := by ext i; simp [vec, h i]
        rw [this, map_zero, zero_mul]
      · have : vec (Additive.ofMul b) = 0 := by ext i; simp [vec, h i]
        rw [this, map_zero, mul_zero]
    | natCast =>
      rw [map_natCast, map_zero,
        ← map_natCast (algebraMap (ZMod p) (ExteriorAlgebra (ZMod p) (ι → ZMod p))) p,
        ZMod.natCast_self, map_zero]
  · intro a
    rw [of, RingQuot.lift_mkRingHom_apply]
    show T _ = _
    rw [hT]; rfl

/-- The coordinate of `Λ^d` along the coordinates `τ`: a determinant. -/
theorem exists_coord (p : ℕ) {ι : Type*} {d : ℕ} (τ : Fin d → ι) :
    ∃ χ : ExteriorAlgebra (ZMod p) (ι → ZMod p) →ₗ[ZMod p] ZMod p,
      ∀ v : Fin d → (ι → ZMod p),
        χ (ExteriorAlgebra.ιMulti (ZMod p) d v) = (Matrix.of fun s r ↦ v s (τ r)).det := by
  let A : (ι → ZMod p) [⋀^Fin d]→ₗ[ZMod p] ZMod p :=
    (Matrix.detRowAlternating).compLinearMap (LinearMap.funLeft (ZMod p) (ZMod p) τ)
  let f : ∀ i, (ι → ZMod p) [⋀^Fin i]→ₗ[ZMod p] ZMod p := fun i ↦
    if h : i = d then A.domDomCongr (finCongr h.symm) else 0
  refine ⟨ExteriorAlgebra.liftAlternating f, fun v ↦ ?_⟩
  rw [ExteriorAlgebra.liftAlternating_apply_ιMulti]
  simp only [f, dif_pos rfl]
  rfl

/-- Values of these invariants on symbols. -/
theorem exists_det_map (p : ℕ) {ι : Type*} (L : ι → Additive Fˣ →+ ℤ)
    (htri : ∀ a b : Fˣ, (a : F) + b = 1 →
      (∀ i, L i (Additive.ofMul a) = L i (Additive.ofMul b)) ∨
      (∀ i, L i (Additive.ofMul a) = 0) ∨ (∀ i, L i (Additive.ofMul b) = 0))
    {d : ℕ} (τ : Fin d → ι) :
    ∃ χ : MilnorK F p →+ ZMod p, ∀ a : Fin d → Fˣ,
      χ (symbol p a) = (Matrix.of fun s r ↦ ((L (τ r) (Additive.ofMul (a s)) : ℤ) : ZMod p)).det := by
  obtain ⟨Ψ, hΨ⟩ := exists_ext_hom p L htri
  obtain ⟨χ, hχ⟩ := exists_coord p (ι := ι) τ
  refine ⟨χ.toAddMonoidHom.comp Ψ.toAddMonoidHom, fun a ↦ ?_⟩
  have : Ψ (symbol p a) = ExteriorAlgebra.ιMulti (ZMod p) d
      (fun s i ↦ ((L i (Additive.ofMul (a s)) : ℤ) : ZMod p)) := by
    rw [symbol, map_list_prod, List.map_ofFn, ExteriorAlgebra.ιMulti_apply]
    congr 1
    refine List.ofFn_inj.mpr ?_
    funext s
    simp [hΨ]
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, RingHom.toAddMonoidHom_eq_coe,
    AddMonoidHom.coe_coe, LinearMap.toAddMonoidHom_coe]
  rw [this, hχ]



open MilnorK MvPolynomial

theorem exists_hom {R F : Type*} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] (l : R → ℤ)
    (hl : ∀ f g : R, f ≠ 0 → g ≠ 0 → l (f * g) = l f + l g) :
    ∃ L : Additive Fˣ →+ ℤ, ∀ (u : Fˣ) (n d : R), d ≠ 0 →
      (u : F) * algebraMap R F d = algebraMap R F n → L (Additive.ofMul u) = l n - l d := by
  have hinj : Function.Injective (algebraMap R F) := IsFractionRing.injective R F
  have hex : ∀ u : Fˣ, ∃ nd : R × R, nd.2 ≠ 0 ∧
      (u : F) * algebraMap R F nd.2 = algebraMap R F nd.1 := by
    intro u
    obtain ⟨n, d, hd, hnd⟩ := IsFractionRing.div_surjective (A := R) (u : F)
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    refine ⟨(n, d), hd0, ?_⟩
    have : algebraMap R F d ≠ 0 := (map_ne_zero_iff _ hinj).mpr hd0
    rw [← hnd]
    field_simp
  choose nd hnd0 hndeq using hex
  have hnum : ∀ (u : Fˣ) (n d : R), d ≠ 0 → (u : F) * algebraMap R F d = algebraMap R F n →
      n ≠ 0 := by
    rintro u n d hd h rfl
    rw [map_zero] at h
    exact (mul_ne_zero u.ne_zero ((map_ne_zero_iff _ hinj).mpr hd)) h
  have key : ∀ (u : Fˣ) (n d : R), d ≠ 0 → (u : F) * algebraMap R F d = algebraMap R F n →
      l (nd u).1 - l (nd u).2 = l n - l d := by
    intro u n d hd h
    have hn : n ≠ 0 := hnum u n d hd h
    have hn' : (nd u).1 ≠ 0 := hnum u _ _ (hnd0 u) (hndeq u)
    have heq : n * (nd u).2 = (nd u).1 * d := by
      apply hinj
      rw [map_mul, map_mul, ← h, ← hndeq u]
      ring
    have := congrArg l heq
    rw [hl _ _ hn (hnd0 u), hl _ _ hn' hd] at this
    linarith
  refine ⟨AddMonoidHom.mk' (fun a => l (nd a.toMul).1 - l (nd a.toMul).2) ?_, ?_⟩
  · intro a b
    have h1 := hndeq a.toMul
    have h2 := hndeq b.toMul
    have hprod : (((a + b).toMul : Fˣ) : F) *
        algebraMap R F ((nd a.toMul).2 * (nd b.toMul).2) =
        algebraMap R F ((nd a.toMul).1 * (nd b.toMul).1) := by
      rw [map_mul, map_mul, ← h1, ← h2, toMul_add, Units.val_mul]
      ring
    have := key (a + b).toMul _ _ (mul_ne_zero (hnd0 _) (hnd0 _)) hprod
    show l (nd (a + b).toMul).1 - l (nd (a + b).toMul).2 =
      (l (nd a.toMul).1 - l (nd a.toMul).2) + (l (nd b.toMul).1 - l (nd b.toMul).2)
    rw [this, hl _ _ (hnum _ _ _ (hnd0 _) h1) (hnum _ _ _ (hnd0 _) h2),
      hl _ _ (hnd0 _) (hnd0 _)]
    ring
  · intro u n d hd h
    exact key u n d hd h

theorem rm_neg (a : ℂ) (Q : Polynomial ℂ) :
    (-Q).rootMultiplicity a = Q.rootMultiplicity a := by
  by_cases hQ : Q = 0
  · simp [hQ]
  · have h : Polynomial.C (-1 : ℂ) * Q ≠ 0 := mul_ne_zero (by simp) hQ
    have h2 := Polynomial.rootMultiplicity_mul (x := a) h
    rw [Polynomial.rootMultiplicity_C, zero_add] at h2
    rw [← h2]
    congr 1
    simp

theorem rm_add_of_lt (a : ℂ) (P Q : Polynomial ℂ) (hP : P ≠ 0) (hPQ : P + Q ≠ 0)
    (h : P.rootMultiplicity a < Q.rootMultiplicity a) :
    (P + Q).rootMultiplicity a = P.rootMultiplicity a := by
  have h1 := Polynomial.rootMultiplicity_add a hPQ
  have e : (P + Q) + (-Q) = P := by ring
  have hP' : (P + Q) + (-Q) ≠ 0 := by rw [e]; exact hP
  have h2 := Polynomial.rootMultiplicity_add a hP'
  rw [rm_neg, e] at h2
  rcases min_le_iff.mp h1 with h3 | h3 <;> rcases min_le_iff.mp h2 with h4 | h4 <;> omega

theorem tri {σ : Type*} (m : MonomialOrder σ) (a : ℂ) (f g : MvPolynomial σ (Polynomial ℂ))
    (hf : f ≠ 0) (hg : g ≠ 0) :
    (m.degree f = m.degree g ∧
      (m.leadingCoeff f).rootMultiplicity a = (m.leadingCoeff g).rootMultiplicity a) ∨
    (m.degree (f + g) = m.degree f ∧
      (m.leadingCoeff (f + g)).rootMultiplicity a = (m.leadingCoeff f).rootMultiplicity a) ∨
    (m.degree (f + g) = m.degree g ∧
      (m.leadingCoeff (f + g)).rootMultiplicity a = (m.leadingCoeff g).rootMultiplicity a) := by
  have hlf : m.leadingCoeff f ≠ 0 := m.leadingCoeff_ne_zero_iff.mpr hf
  have hlg : m.leadingCoeff g ≠ 0 := m.leadingCoeff_ne_zero_iff.mpr hg
  rcases lt_trichotomy (m.toSyn (m.degree f)) (m.toSyn (m.degree g)) with h | h | h
  · right; right
    refine ⟨m.degree_add_eq_right_of_lt h, ?_⟩
    rw [add_comm, m.leadingCoeff_add_of_lt h]
  · have hd : m.degree f = m.degree g := m.toSyn.injective h
    by_cases hc : m.leadingCoeff f + m.leadingCoeff g = 0
    · left
      refine ⟨hd, ?_⟩
      have h2 : m.leadingCoeff f = -m.leadingCoeff g := eq_neg_of_add_eq_zero_left hc
      rw [h2, rm_neg]
    · have hcoeff : (f + g).coeff (m.degree f) = m.leadingCoeff f + m.leadingCoeff g := by
        have e1 : m.leadingCoeff f = f.coeff (m.degree f) := rfl
        have e2 : m.leadingCoeff g = g.coeff (m.degree f) := by rw [hd]; rfl
        rw [coeff_add, e1, e2]
      have hdeg : m.degree (f + g) = m.degree f := by
        apply m.toSyn.injective
        apply le_antisymm
        · have h3 := m.degree_add_le (f := f) (g := g)
          rw [← h, sup_idem] at h3
          exact h3
        · apply m.le_degree
          rw [mem_support_iff, hcoeff]
          exact hc
      have hlc : m.leadingCoeff (f + g) = m.leadingCoeff f + m.leadingCoeff g := by
        rw [← hcoeff, ← hdeg]
        rfl
      rcases lt_trichotomy ((m.leadingCoeff f).rootMultiplicity a)
        ((m.leadingCoeff g).rootMultiplicity a) with h' | h' | h'
      · right; left
        refine ⟨hdeg, ?_⟩
        rw [hlc]
        exact rm_add_of_lt a _ _ hlf hc h'
      · left
        exact ⟨hd, h'⟩
      · right; right
        refine ⟨hdeg.trans hd, ?_⟩
        rw [hlc, add_comm]
        exact rm_add_of_lt a _ _ hlg (by rwa [add_comm]) h'
  · right; left
    exact ⟨m.degree_add_of_lt h, by rw [m.leadingCoeff_add_of_lt h]⟩


/-- Unit-level trichotomy for a whole family of valuation-like homomorphisms. -/
theorem vec_of_tri {R F : Type*} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] {ι : Type*} (l : ι → R → ℤ) (L : ι → Additive Fˣ →+ ℤ)
    (hL : ∀ i (u : Fˣ) (n d : R), d ≠ 0 →
      (u : F) * algebraMap R F d = algebraMap R F n → L i (Additive.ofMul u) = l i n - l i d)
    (htri : ∀ f g : R, f ≠ 0 → g ≠ 0 → f + g ≠ 0 →
      (∀ i, l i f = l i g) ∨ (∀ i, l i (f + g) = l i f) ∨ (∀ i, l i (f + g) = l i g))
    (a b : Fˣ) (hab : (a : F) + (b : F) = 1) :
    (∀ i, L i (Additive.ofMul a) = L i (Additive.ofMul b)) ∨
      (∀ i, L i (Additive.ofMul a) = 0) ∨ (∀ i, L i (Additive.ofMul b) = 0) := by
  have hinj : Function.Injective (algebraMap R F) := IsFractionRing.injective R F
  obtain ⟨n, d, hd, hnd⟩ := IsFractionRing.div_surjective (A := R) (a : F)
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hd' : algebraMap R F d ≠ 0 := (map_ne_zero_iff _ hinj).mpr hd0
  have ha : (a : F) * algebraMap R F d = algebraMap R F n := by
    rw [← hnd]; field_simp
  have hb : (b : F) * algebraMap R F d = algebraMap R F (d - n) := by
    have : (b : F) = 1 - (a : F) := by rw [← hab]; ring
    rw [this, map_sub, ← ha]; ring
  have hn0 : n ≠ 0 := by
    rintro rfl; rw [map_zero] at ha; exact (mul_ne_zero a.ne_zero hd') ha
  have hm0 : d - n ≠ 0 := by
    intro h0; rw [h0, map_zero] at hb; exact (mul_ne_zero b.ne_zero hd') hb
  have hsum : n + (d - n) = d := by ring
  have hs0 : n + (d - n) ≠ 0 := by rw [hsum]; exact hd0
  rcases htri n (d - n) hn0 hm0 hs0 with h | h | h
  · left; intro i
    rw [hL i a n d hd0 ha, hL i b (d - n) d hd0 hb, h i]
  · right; left; intro i
    rw [hL i a n d hd0 ha]
    have := h i; rw [hsum] at this; rw [this, sub_self]
  · right; right; intro i
    rw [hL i b (d - n) d hd0 hb]
    have := h i; rw [hsum] at this; rw [this, sub_self]



section dets
variable {R : Type*} [CommRing R]

/-- Indicator matrix between two sorted subsets: determinant `1` if equal, `0` otherwise. -/
theorem det_sorted_indicator {n d : ℕ} (S T : Finset (Fin n)) (hS : S.card = d) (hT : T.card = d) :
    (Matrix.of fun q q' : Fin d ↦
      if S.orderEmbOfFin hS q = T.orderEmbOfFin hT q' then (1 : R) else 0).det =
      if S = T then 1 else 0 := by
  by_cases hST : S = T
  · subst hST
    rw [if_pos rfl]
    have : (Matrix.of fun q q' : Fin d ↦
        if S.orderEmbOfFin hS q = S.orderEmbOfFin hT q' then (1 : R) else 0) = 1 := by
      ext q q'
      simp only [Matrix.of_apply, Matrix.one_apply]
      congr 1
      exact propext (S.orderEmbOfFin hS).injective.eq_iff
    rw [this, Matrix.det_one]
  · rw [if_neg hST]
    have hnot : ¬ S ⊆ T := fun h ↦ hST (Finset.eq_of_subset_of_card_le h (by omega))
    obtain ⟨x, hxS, hxT⟩ := Finset.not_subset.mp hnot
    have hx : x ∈ Set.range (S.orderEmbOfFin hS) := by
      rw [Finset.range_orderEmbOfFin]; exact hxS
    obtain ⟨q0, hq0⟩ := hx
    refine Matrix.det_eq_zero_of_row_eq_zero q0 fun q' ↦ ?_
    simp only [Matrix.of_apply]
    rw [if_neg]
    intro h
    apply hxT
    rw [← hq0, h]
    exact Finset.orderEmbOfFin_mem T hT q'

/-- If `x` is in `S` but not in the range of `u`, the indicator matrix is singular. -/
theorem det_indicator_zero {n d : ℕ} (S : Finset (Fin n)) (hS : S.card = d) (u : Fin d → Fin n)
    (x : Fin n) (hxS : x ∈ S) (hxu : ∀ q', u q' ≠ x) :
    (Matrix.of fun q q' : Fin d ↦ if S.orderEmbOfFin hS q = u q' then (1 : R) else 0).det = 0 := by
  have hx : x ∈ Set.range (S.orderEmbOfFin hS) := by
    rw [Finset.range_orderEmbOfFin]; exact hxS
  obtain ⟨q0, hq0⟩ := hx
  refine Matrix.det_eq_zero_of_row_eq_zero q0 fun q' ↦ ?_
  simp only [Matrix.of_apply]
  rw [if_neg]
  intro h
  exact hxu q' (h.symm.trans hq0)

/-- If `u` is injective with values in `S` (of the same size), the indicator matrix is invertible. -/
theorem det_indicator_ne_zero [Nontrivial R] {n d : ℕ} (S : Finset (Fin n)) (hS : S.card = d)
    (u : Fin d → Fin n) (hu : Function.Injective u) (huS : ∀ q', u q' ∈ S) :
    (Matrix.of fun q q' : Fin d ↦ if S.orderEmbOfFin hS q = u q' then (1 : R) else 0).det ≠ 0 := by
  classical
  set P := (Matrix.of fun q q' : Fin d ↦ if S.orderEmbOfFin hS q = u q' then (1 : R) else 0)
  have himg : Finset.univ.image u = S := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨q', -, rfl⟩ := Finset.mem_image.mp hx
      exact huS q'
    · rw [Finset.card_image_of_injective _ hu, Finset.card_univ, Fintype.card_fin, hS]
  have hsurj : ∀ q, ∃ q', u q' = S.orderEmbOfFin hS q := by
    intro q
    have : S.orderEmbOfFin hS q ∈ Finset.univ.image u := by
      rw [himg]; exact Finset.orderEmbOfFin_mem S hS q
    obtain ⟨q', -, h⟩ := Finset.mem_image.mp this
    exact ⟨q', h⟩
  have hPP : P * P.transpose = 1 := by
    ext q1 q2
    rw [Matrix.mul_apply, Matrix.one_apply]
    obtain ⟨q', hq'⟩ := hsurj q1
    rw [Finset.sum_eq_single q']
    · simp only [P, Matrix.transpose_apply, Matrix.of_apply, hq', if_true, one_mul]
      by_cases h : q1 = q2
      · subst h; simp [hq']
      · rw [if_neg h, if_neg]
        intro h2
        exact h ((S.orderEmbOfFin hS).injective h2).symm
    · intro b _ hb
      simp only [P, Matrix.transpose_apply, Matrix.of_apply]
      rw [if_neg, zero_mul]
      intro h
      exact hb (hu (h.symm.trans hq'.symm))
    · intro h; exact absurd (Finset.mem_univ q') h
  intro h0
  have := congrArg Matrix.det hPP
  rw [Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

end dets



open MilnorK MvPolynomial

theorem lower_bound_gen_abstract {R F : Type*} [CommRing R] [IsDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F] (n : ℕ) (e : R →+* MvPolynomial (Fin n) (Polynomial ℂ))
    (he : Function.Injective e) (g : ℂ → R)
    (hg : ∀ c, e (g c) = C (Polynomial.X - Polynomial.C c))
    (y : Fin n → R) (hy : ∀ j, e (y j) = X j) (p : ℕ) (hp : p.Prime) (d : ℕ) (hd1 : 1 ≤ d)
    (hdn : d ≤ n) (k : ℕ) (hk : k ∈ symbolLengthBounds F p (d + 1)) :
    n.choose d + n ≤ (d + 1) * k := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hinj : Function.Injective (algebraMap R F) := IsFractionRing.injective R F
  obtain ⟨m⟩ : Nonempty (MonomialOrder (Fin n)) := ⟨MonomialOrder.lex⟩
  have he0 : ∀ f : R, f ≠ 0 → e f ≠ 0 := fun f hf => (map_ne_zero_iff e he).mpr hf
  have hLw : ∀ j : Fin n, ∃ L : Additive Fˣ →+ ℤ, ∀ (u : Fˣ) (nn dd : R), dd ≠ 0 →
      (u : F) * algebraMap R F dd = algebraMap R F nn →
      L (Additive.ofMul u) = ((m.degree (e nn) j : ℕ) : ℤ) - ((m.degree (e dd) j : ℕ) : ℤ) := by
    intro j
    exact exists_hom (fun f => ((m.degree (e f) j : ℕ) : ℤ)) (by
      intro f g hf hg
      rw [map_mul, m.degree_mul (he0 f hf) (he0 g hg)]
      simp)
  have hLv : ∀ c : ℂ, ∃ L : Additive Fˣ →+ ℤ, ∀ (u : Fˣ) (nn dd : R), dd ≠ 0 →
      (u : F) * algebraMap R F dd = algebraMap R F nn →
      L (Additive.ofMul u) =
        (((m.leadingCoeff (e nn)).rootMultiplicity c : ℕ) : ℤ) -
          (((m.leadingCoeff (e dd)).rootMultiplicity c : ℕ) : ℤ) := by
    intro c
    exact exists_hom
      (fun f => (((m.leadingCoeff (e f)).rootMultiplicity c : ℕ) : ℤ)) (by
      intro f g hf hg
      have h1 : m.leadingCoeff (e f) * m.leadingCoeff (e g) ≠ 0 :=
        mul_ne_zero (m.leadingCoeff_ne_zero_iff.mpr (he0 f hf))
          (m.leadingCoeff_ne_zero_iff.mpr (he0 g hg))
      rw [map_mul, m.leadingCoeff_mul, Polynomial.rootMultiplicity_mul h1]
      simp)
  choose Lw hLw using hLw
  choose Lv hLv using hLv
  -- the valuation vector at the point `c`
  have htri : ∀ c : ℂ, ∀ a b : Fˣ, (a : F) + b = 1 →
      (∀ i, (Sum.elim Lw (fun _ : Unit ↦ Lv c)) i (Additive.ofMul a) =
        (Sum.elim Lw (fun _ : Unit ↦ Lv c)) i (Additive.ofMul b)) ∨
      (∀ i, (Sum.elim Lw (fun _ : Unit ↦ Lv c)) i (Additive.ofMul a) = 0) ∨
      (∀ i, (Sum.elim Lw (fun _ : Unit ↦ Lv c)) i (Additive.ofMul b) = 0) := by
    intro c
    refine vec_of_tri (Sum.elim (fun j f ↦ ((m.degree (e f) j : ℕ) : ℤ))
      (fun _ f ↦ (((m.leadingCoeff (e f)).rootMultiplicity c : ℕ) : ℤ)))
      (Sum.elim Lw (fun _ ↦ Lv c)) ?_ ?_
    · intro i
      rcases i with j | u
      · exact hLw j
      · exact hLv c
    · intro f g hf hg _
      rcases tri m c (e f) (e g) (he0 f hf) (he0 g hg) with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; intro i; rcases i with j | u <;> simp [h1, h2]
      · right; left; intro i; rcases i with j | u <;> simp [map_add, h1, h2]
      · right; right; intro i; rcases i with j | u <;> simp [map_add, h1, h2]
  -- the units `x_0 - c` and `x_j`
  have hg0 : ∀ c : ℂ, g c ≠ 0 := by
    intro c h
    have h1 := hg c
    rw [h, map_zero] at h1
    have h2 : (Polynomial.X - Polynomial.C c) = 0 :=
      C_injective (Fin n) (Polynomial ℂ) (h1.symm.trans (map_zero C).symm)
    exact Polynomial.X_sub_C_ne_zero _ h2
  have hy0 : ∀ l : Fin n, y l ≠ 0 := by
    intro l h
    have h1 := hy l
    rw [h, map_zero] at h1
    exact X_ne_zero l h1.symm
  obtain ⟨gu, hgu⟩ : ∃ gu : ℂ → Fˣ, ∀ c, (gu c : F) = algebraMap R F (g c) :=
    ⟨fun c => Units.mk0 _ ((map_ne_zero_iff _ hinj).mpr (hg0 c)), fun c => rfl⟩
  obtain ⟨yu, hyu⟩ : ∃ yu : Fin n → Fˣ, ∀ l, (yu l : F) = algebraMap R F (y l) :=
    ⟨fun l => Units.mk0 _ ((map_ne_zero_iff _ hinj).mpr (hy0 l)), fun l => rfl⟩
  have vw_g : ∀ j c, Lw j (Additive.ofMul (gu c)) = 0 := by
    intro j c
    rw [hLw j (gu c) (g c) 1 one_ne_zero (by rw [hgu, map_one, mul_one]), hg, map_one,
      MonomialOrder.degree_C, MonomialOrder.degree_one]
    simp
  have vw_y : ∀ j l, Lw j (Additive.ofMul (yu l)) = if l = j then 1 else 0 := by
    intro j l
    rw [hLw j (yu l) (y l) 1 one_ne_zero (by rw [hyu, map_one, mul_one]), hy, map_one,
      MonomialOrder.degree_X, MonomialOrder.degree_one, Finsupp.single_apply]
    split_ifs <;> simp
  have vv_g : ∀ c c', Lv c (Additive.ofMul (gu c')) = if c = c' then 1 else 0 := by
    intro c c'
    rw [hLv c (gu c') (g c') 1 one_ne_zero (by rw [hgu, map_one, mul_one]), hg, map_one,
      MonomialOrder.leadingCoeff_C, MonomialOrder.leadingCoeff_one,
      Polynomial.rootMultiplicity_X_sub_C, ← Polynomial.C_1, Polynomial.rootMultiplicity_C]
    split_ifs <;> simp_all
  have vv_y : ∀ c l, Lv c (Additive.ofMul (yu l)) = 0 := by
    intro c l
    rw [hLv c (yu l) (y l) 1 one_ne_zero (by rw [hyu, map_one, mul_one]), hy, map_one,
      MonomialOrder.leadingCoeff_X, MonomialOrder.leadingCoeff_one,
      ← Polynomial.C_1, Polynomial.rootMultiplicity_C]
    simp
  -- the test class
  set Sset := {S : Finset (Fin n) // S.card = d}
  set pt : Sset → ℂ := fun S ↦ ((Fintype.equivFin Sset S : ℕ) : ℂ) with hpt
  have pt_inj : Function.Injective pt := by
    intro S S' h
    have : ((Fintype.equivFin Sset S : ℕ) : ℂ) = ((Fintype.equivFin Sset S' : ℕ) : ℂ) := h
    exact (Fintype.equivFin Sset).injective (Fin.ext (by exact_mod_cast this))
  set srt : Sset → Fin d ↪o Fin n := fun S ↦ S.1.orderEmbOfFin S.2
  set σ : Sset → Fin (d + 1) → Fˣ := fun S ↦ Fin.cons (gu (pt S)) (fun q ↦ yu (srt S q))
  have hα : (∑ S, symbol p (σ S)) ∈ grade F p (d + 1) :=
    sum_mem fun S _ ↦ symbol_mem_grade F p (σ S)
  obtain ⟨k', hk', s, hs⟩ := hk _ hα
  -- functionals
  set H : Fin n ⊕ Sset → Additive Fˣ →+ ℤ := Sum.elim Lw (fun S ↦ Lv (pt S)) with hH
  -- invariance of the determinant sums for valid tuples
  have inv : ∀ (S0 : Sset) (τ : Fin (d + 1) → Fin n ⊕ Sset),
      (∀ r S', τ r = Sum.inr S' → S' = S0) →
      ∑ t, (Matrix.of fun a r ↦ ((H (τ r) (Additive.ofMul (s t a)) : ℤ) : ZMod p)).det =
        ∑ S, (Matrix.of fun a r ↦ ((H (τ r) (Additive.ofMul (σ S a)) : ℤ) : ZMod p)).det := by
    intro S0 τ hτ
    set τ' : Fin (d + 1) → Fin n ⊕ Unit := fun r ↦ Sum.elim Sum.inl (fun _ ↦ Sum.inr ()) (τ r)
    obtain ⟨χ, hχ⟩ := exists_det_map p (Sum.elim Lw (fun _ : Unit ↦ Lv (pt S0))) (htri (pt S0)) τ'
    have key : ∀ r a', (Sum.elim Lw (fun _ : Unit ↦ Lv (pt S0))) (τ' r) a' = H (τ r) a' := by
      intro r a'
      rcases h : τ r with j | S'
      · simp [τ', h, hH]
      · have := hτ r S' h
        subst this
        simp [τ', h, hH]
    have h1 := congrArg χ hs
    rw [map_sum, map_sum] at h1
    simp only [hχ, key] at h1
    exact h1.symm
  -- the matrix of the decomposition
  set M : Matrix (Fin d → Fin n ⊕ Sset) (Fin n ⊕ Sset) (ZMod p) := Matrix.of fun J L ↦
    ∑ t, (Matrix.of fun a r ↦ ((H (Fin.snoc (α := fun _ ↦ Fin n ⊕ Sset) J L r) (Additive.ofMul (s t a)) : ℤ) : ZMod p)).det
    with hM
  have hrank : M.rank ≤ k' * (d + 1) := by
    set A : Matrix (Fin d → Fin n ⊕ Sset) (Fin k' × Fin (d + 1)) (ZMod p) :=
      Matrix.of fun J ta ↦ (-1) ^ ((ta.2 : ℕ) + d) *
        (Matrix.of fun (a' r : Fin d) ↦
          ((H (J r) (Additive.ofMul (s ta.1 (ta.2.succAbove a'))) : ℤ) : ZMod p)).det
    set B : Matrix (Fin k' × Fin (d + 1)) (Fin n ⊕ Sset) (ZMod p) :=
      Matrix.of fun ta L ↦ ((H L (Additive.ofMul (s ta.1 ta.2)) : ℤ) : ZMod p)
    have hfact : M = A * B := by
      ext J L
      rw [Matrix.mul_apply, Fintype.sum_prod_type]
      simp only [hM, Matrix.of_apply]
      refine Finset.sum_congr rfl fun t _ ↦ ?_
      rw [Matrix.det_succ_column _ (Fin.last d)]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      simp only [A, B, Matrix.of_apply, Fin.snoc_last, Fin.val_last]
      have hsub : (Matrix.of fun a r ↦ ((H (Fin.snoc (α := fun _ ↦ Fin n ⊕ Sset) J L r)
          (Additive.ofMul (s t a)) : ℤ) : ZMod p)).submatrix a.succAbove (Fin.last d).succAbove =
          Matrix.of fun (a' r : Fin d) ↦
            ((H (J r) (Additive.ofMul (s t (a.succAbove a'))) : ℤ) : ZMod p) := by
        ext a' r
        simp [Matrix.submatrix_apply, Fin.succAbove_last, Fin.snoc_castSucc]
      rw [hsub]
      ring
    rw [hfact]
    calc (A * B).rank ≤ A.rank := Matrix.rank_mul_le_left _ _
      _ ≤ Fintype.card (Fin k' × Fin (d + 1)) := Matrix.rank_le_card_width _
      _ = k' * (d + 1) := by simp
  -- entries forced by the invariants
  have row0 : ∀ (τ : Fin (d + 1) → Fin n ⊕ Sset) (S'' : Sset) (r : Fin (d + 1)) (j' : Fin n),
      τ r = Sum.inl j' → ((H (τ r) (Additive.ofMul (σ S'' 0)) : ℤ) : ZMod p) = 0 := by
    intro τ S'' r j' h
    simp [h, hH, σ, vw_g]
  have hE2 : ∀ (S : Sset) (j : Fin n), M (fun q ↦ Sum.inl (srt S q)) (Sum.inl j) = 0 := by
    intro S j
    simp only [hM, Matrix.of_apply]
    rw [inv S _ (by
      intro r S' h
      refine Fin.lastCases ?_ (fun q ↦ ?_) r h <;> simp)]
    refine Finset.sum_eq_zero fun S'' _ ↦ Matrix.det_eq_zero_of_row_eq_zero 0 fun r ↦ ?_
    simp only [Matrix.of_apply]
    refine Fin.lastCases ?_ (fun q ↦ ?_) r
    · exact row0 _ S'' _ j (by simp)
    · exact row0 _ S'' _ (srt S q) (by simp)
  have hE1 : ∀ S S' : Sset, M (fun q ↦ Sum.inl (srt S q)) (Sum.inr S') =
      (-1) ^ d * (if S = S' then 1 else 0) := by
    intro S S'
    simp only [hM, Matrix.of_apply]
    rw [inv S' _ (by
      intro r S'' h
      refine Fin.lastCases ?_ (fun q ↦ ?_) r h <;> simp [eq_comm])]
    have hdet : ∀ S'' : Sset, (Matrix.of fun a r ↦ ((H (Fin.snoc (α := fun _ ↦ Fin n ⊕ Sset)
        (fun q ↦ Sum.inl (srt S q)) (Sum.inr S') r) (Additive.ofMul (σ S'' a)) : ℤ) : ZMod p)).det =
        (-1) ^ d * ((if S' = S'' then 1 else 0) * (if S'' = S then 1 else 0)) := by
      intro S''
      rw [Matrix.det_succ_row _ 0, Fin.sum_univ_castSucc]
      have hz : ∀ q : Fin d, ((H (Fin.snoc (α := fun _ ↦ Fin n ⊕ Sset)
          (fun q ↦ Sum.inl (srt S q)) (Sum.inr S') q.castSucc) (Additive.ofMul (σ S'' 0)) : ℤ) :
            ZMod p) = 0 := fun q ↦ row0 _ S'' _ (srt S q) (by simp)
      simp only [Matrix.of_apply, hz, mul_zero, zero_mul, Finset.sum_const_zero, zero_add]
      have hlast : ((H (Fin.snoc (α := fun _ ↦ Fin n ⊕ Sset) (fun q ↦ Sum.inl (srt S q))
          (Sum.inr S') (Fin.last d)) (Additive.ofMul (σ S'' 0)) : ℤ) : ZMod p) =
          if S' = S'' then 1 else 0 := by
        simp only [Fin.snoc_last, hH, Sum.elim_inr, σ, Fin.cons_zero, vv_g]
        by_cases h : S' = S''
        · subst h; simp
        · rw [if_neg (fun h' ↦ h (pt_inj h')), if_neg h]; simp
      have hminor : (Matrix.of fun a r ↦ ((H (Fin.snoc (α := fun _ ↦ Fin n ⊕ Sset)
          (fun q ↦ Sum.inl (srt S q)) (Sum.inr S') r) (Additive.ofMul (σ S'' a)) : ℤ) :
            ZMod p)).submatrix (0 : Fin (d + 1)).succAbove (Fin.last d).succAbove =
          Matrix.of fun q q' : Fin d ↦
            if S''.1.orderEmbOfFin S''.2 q = S.1.orderEmbOfFin S.2 q' then (1 : ZMod p) else 0 := by
        ext q q'
        simp only [Matrix.submatrix_apply, Matrix.of_apply, Fin.succAbove_zero, Fin.succAbove_last,
          Fin.snoc_castSucc, hH, Sum.elim_inl, σ, Fin.cons_succ, vw_y, srt]
        split_ifs <;> simp
      rw [hlast, hminor, det_sorted_indicator S''.1 S.1 S''.2 S.2]
      simp only [Fin.val_zero, Fin.val_last, zero_add]
      by_cases h : S''.1 = S.1
      · rw [if_pos h, if_pos (Subtype.ext h)]; ring
      · rw [if_neg h, if_neg (fun h' ↦ h (congrArg Subtype.val h'))]; ring
    simp only [hdet]
    rw [Finset.sum_eq_single S]
    · by_cases h : S = S'
      · subst h; simp
      · rw [if_neg (Ne.symm h), if_neg h]; simp
    · intro S'' _ h; rw [if_neg h]; simp
    · intro h; exact absurd (Finset.mem_univ S) h
  obtain ⟨d0, rfl⟩ : ∃ d0, d = d0 + 1 := ⟨d - 1, by omega⟩
  have hSj : ∀ j : Fin n, ∃ S : Sset, j ∈ S.1 := by
    intro j
    obtain ⟨S, hjS, -, hS⟩ := Finset.exists_subsuperset_card_eq (Finset.subset_univ {j})
      (by simp; omega) (by simp; omega)
    exact ⟨⟨S, hS⟩, hjS (Finset.mem_singleton_self j)⟩
  choose Sj hSj using hSj
  have hTcard : ∀ j, ((Sj j).1.erase j).card = d0 := by
    intro j; rw [Finset.card_erase_of_mem (hSj j), (Sj j).2]; rfl
  set srtT : Fin n → Fin d0 ↪o Fin n := fun j ↦ ((Sj j).1.erase j).orderEmbOfFin (hTcard j)
  set u : Fin n → Fin n → Fin (d0 + 1) → Fin n := fun j j' ↦
    Fin.snoc (α := fun _ ↦ Fin n) (srtT j) j'
  set Jrow : Fin n → Fin (d0 + 1) → Fin n ⊕ Sset := fun j ↦
    Fin.cons (Sum.inr (Sj j)) (fun q ↦ Sum.inl (srtT j q))
  have hE3 : ∀ j j', M (Jrow j) (Sum.inl j') = (Matrix.of fun q q' : Fin (d0 + 1) ↦
      if (Sj j).1.orderEmbOfFin (Sj j).2 q = u j j' q' then (1 : ZMod p) else 0).det := by
    intro j j'
    have hτ : (Fin.snoc (α := fun _ ↦ Fin n ⊕ Sset) (Jrow j) (Sum.inl j') : Fin (d0 + 2) → _) =
        Fin.cons (Sum.inr (Sj j)) (Fin.snoc (α := fun _ ↦ Fin n ⊕ Sset)
          (fun q ↦ Sum.inl (srtT j q)) (Sum.inl j')) :=
      (Fin.cons_snoc_eq_snoc_cons _ _ _).symm
    simp only [hM, Matrix.of_apply]
    rw [hτ, inv (Sj j) _ (by
      intro r S'' h
      refine Fin.cases ?_ (fun r' ↦ ?_) r h
      · simp [eq_comm]
      · refine Fin.lastCases ?_ (fun q ↦ ?_) r' <;> simp)]
    have hdet : ∀ S'' : Sset, (Matrix.of fun a r ↦ ((H ((Fin.cons (Sum.inr (Sj j))
        (Fin.snoc (α := fun _ ↦ Fin n ⊕ Sset) (fun q ↦ Sum.inl (srtT j q)) (Sum.inl j')) :
          Fin (d0 + 2) → Fin n ⊕ Sset) r) (Additive.ofMul (σ S'' a)) : ℤ) : ZMod p)).det =
        (if Sj j = S'' then 1 else 0) * (Matrix.of fun q q' : Fin (d0 + 1) ↦
          if S''.1.orderEmbOfFin S''.2 q = u j j' q' then (1 : ZMod p) else 0).det := by
      intro S''
      rw [Matrix.det_succ_row _ 0, Fin.sum_univ_succ]
      have hz : ∀ r' : Fin (d0 + 1), ((H ((Fin.cons (Sum.inr (Sj j))
          (Fin.snoc (α := fun _ ↦ Fin n ⊕ Sset) (fun q ↦ Sum.inl (srtT j q)) (Sum.inl j')) :
            Fin (d0 + 2) → Fin n ⊕ Sset) r'.succ) (Additive.ofMul (σ S'' 0)) : ℤ) : ZMod p) = 0 := by
        intro r'
        refine Fin.lastCases ?_ (fun q ↦ ?_) r'
        · exact row0 _ S'' _ j' (by simp)
        · exact row0 _ S'' _ (srtT j q) (by simp)
      simp only [Matrix.of_apply, hz, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
      have h00 : ((H ((Fin.cons (Sum.inr (Sj j))
          (Fin.snoc (α := fun _ ↦ Fin n ⊕ Sset) (fun q ↦ Sum.inl (srtT j q)) (Sum.inl j')) :
            Fin (d0 + 2) → Fin n ⊕ Sset) 0) (Additive.ofMul (σ S'' 0)) : ℤ) : ZMod p) =
          if Sj j = S'' then 1 else 0 := by
        simp only [Fin.cons_zero, hH, Sum.elim_inr, σ, vv_g]
        by_cases h : Sj j = S''
        · subst h; simp
        · rw [if_neg (fun h' ↦ h (pt_inj h')), if_neg h]; simp
      have hminor : (Matrix.of fun a r ↦ ((H ((Fin.cons (Sum.inr (Sj j))
          (Fin.snoc (α := fun _ ↦ Fin n ⊕ Sset) (fun q ↦ Sum.inl (srtT j q)) (Sum.inl j')) :
            Fin (d0 + 2) → Fin n ⊕ Sset) r) (Additive.ofMul (σ S'' a)) : ℤ) : ZMod p)).submatrix
              (0 : Fin (d0 + 2)).succAbove (0 : Fin (d0 + 2)).succAbove =
          Matrix.of fun q q' : Fin (d0 + 1) ↦
            if S''.1.orderEmbOfFin S''.2 q = u j j' q' then (1 : ZMod p) else 0 := by
        ext q q'
        simp only [Matrix.submatrix_apply, Matrix.of_apply, Fin.succAbove_zero, Fin.cons_succ, σ]
        refine Fin.lastCases ?_ (fun q0 ↦ ?_) q'
        · simp only [Fin.snoc_last, hH, Sum.elim_inl, vw_y, u, srt]
          by_cases h : S''.1.orderEmbOfFin S''.2 q = j' <;> simp only [h, if_true, if_false,
            Int.cast_one, Int.cast_zero]
        · simp only [Fin.snoc_castSucc, hH, Sum.elim_inl, vw_y, u, srt]
          by_cases h : S''.1.orderEmbOfFin S''.2 q = srtT j q0 <;> simp only [h, if_true,
            if_false, Int.cast_one, Int.cast_zero]
      rw [h00, hminor]
      simp
    simp only [hdet]
    rw [Finset.sum_eq_single (Sj j)]
    · simp
    · intro S'' _ h; rw [if_neg (Ne.symm h), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hδ : ∀ j, (Matrix.of fun q q' : Fin (d0 + 1) ↦
      if (Sj j).1.orderEmbOfFin (Sj j).2 q = u j j q' then (1 : ZMod p) else 0).det ≠ 0 := by
    intro j
    refine det_indicator_ne_zero (Sj j).1 (Sj j).2 (u j j) ?_ ?_
    · intro a b hab
      revert hab
      refine Fin.lastCases ?_ (fun a0 ↦ ?_) a <;> refine Fin.lastCases ?_ (fun b0 ↦ ?_) b <;>
        intro hab <;> simp only [u, Fin.snoc_last, Fin.snoc_castSucc] at hab
      · rfl
      · exact absurd hab.symm (Finset.ne_of_mem_erase (Finset.orderEmbOfFin_mem _ (hTcard j) b0))
      · exact absurd hab (Finset.ne_of_mem_erase (Finset.orderEmbOfFin_mem _ (hTcard j) a0))
      · rw [(srtT j).injective hab]
    · intro q'
      refine Fin.lastCases ?_ (fun q0 ↦ ?_) q'
      · simp only [u, Fin.snoc_last]; exact hSj j
      · simp only [u, Fin.snoc_castSucc]
        exact Finset.mem_of_mem_erase (Finset.orderEmbOfFin_mem _ (hTcard j) q0)
  have hoff : ∀ j j', j' ≠ j → (Matrix.of fun q q' : Fin (d0 + 1) ↦
      if (Sj j).1.orderEmbOfFin (Sj j).2 q = u j j' q' then (1 : ZMod p) else 0).det = 0 := by
    intro j j' hjj
    refine det_indicator_zero (Sj j).1 (Sj j).2 (u j j') j (hSj j) fun q' ↦ ?_
    refine Fin.lastCases ?_ (fun q0 ↦ ?_) q'
    · simp only [u, Fin.snoc_last]; exact hjj
    · simp only [u, Fin.snoc_castSucc]
      exact Finset.ne_of_mem_erase (Finset.orderEmbOfFin_mem _ (hTcard j) q0)
  -- the invertible block
  set δ : Fin n → ZMod p := fun j ↦ (Matrix.of fun q q' : Fin (d0 + 1) ↦
      if (Sj j).1.orderEmbOfFin (Sj j).2 q = u j j q' then (1 : ZMod p) else 0).det
  set rowsel : Sset ⊕ Fin n → (Fin (d0 + 1) → Fin n ⊕ Sset) :=
    Sum.elim (fun S q ↦ Sum.inl (srt S q)) Jrow
  set colsel : Sset ⊕ Fin n → Fin n ⊕ Sset := Sum.elim Sum.inr Sum.inl
  set Bm := M.submatrix rowsel colsel
  have hB : Bm = Matrix.fromBlocks (((-1 : ZMod p) ^ (d0 + 1)) • (1 : Matrix Sset Sset (ZMod p)))
      0 Bm.toBlocks₂₁ (Matrix.diagonal δ) := by
    ext (S | j) (S' | j')
    · simp only [Bm, rowsel, colsel, Matrix.submatrix_apply, Sum.elim_inl, Sum.elim_inr,
        Matrix.fromBlocks_apply₁₁, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      exact hE1 S S'
    · simp only [Bm, rowsel, colsel, Matrix.submatrix_apply, Sum.elim_inl, Sum.elim_inr,
        Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
      exact hE2 S j'
    · rfl
    · simp only [Bm, rowsel, colsel, Matrix.submatrix_apply, Sum.elim_inr,
        Matrix.fromBlocks_apply₂₂, Matrix.diagonal_apply]
      rw [hE3]
      by_cases h : j = j'
      · subst h; rw [if_pos rfl]
      · rw [if_neg h, hoff j j' (Ne.symm h)]
  have hdetB : Bm.det ≠ 0 := by
    rw [hB, Matrix.det_fromBlocks_zero₁₂, Matrix.det_smul, Matrix.det_one, mul_one,
      Matrix.det_diagonal]
    exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)))
      (Finset.prod_ne_zero_iff.mpr fun j _ ↦ hδ j)
  have hrankB : Bm.rank = n.choose (d0 + 1) + n := by
    rw [Matrix.rank_of_isUnit Bm ((Matrix.isUnit_iff_isUnit_det Bm).mpr
      (isUnit_iff_ne_zero.mpr hdetB)), Fintype.card_sum, Fintype.card_finset_len,
      Fintype.card_fin]
  calc n.choose (d0 + 1) + n = Bm.rank := hrankB.symm
    _ ≤ M.rank := Matrix.rank_submatrix_le _ _ _
    _ ≤ k' * (d0 + 1 + 1) := hrank
    _ ≤ k * (d0 + 1 + 1) := Nat.mul_le_mul_right _ hk'
    _ = (d0 + 1 + 1) * k := Nat.mul_comm _ _

/-- **Lower bound in every degree** (a degree-`d` version of Becher-Hoffmann, Prop. 4.5): for
`2 ≤ d ≤ m` and every prime `p`, any bound `k` for the symbol length of
`K_d(C(x_1, ..., x_m))/p` satisfies `C(m-1, d-1) + (m - 1) ≤ d k`. -/
theorem lower_bound_gen (m d p : ℕ) (hd : 2 ≤ d) (hdm : d ≤ m) (hp : p.Prime) :
    ∀ k ∈ symbolLengthBounds (MvRatFunc (Fin m) ℂ) p d,
      (m - 1).choose (d - 1) + (m - 1) ≤ d * k := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨d0, rfl⟩ : ∃ d0, d = d0 + 1 := ⟨d - 1, by omega⟩
  intro k hk
  simp only [Nat.add_sub_cancel]
  refine lower_bound_gen_abstract (R := MvPolynomial (Fin (n + 1)) ℂ)
    (F := MvRatFunc (Fin (n + 1)) ℂ) n
    (((renameEquiv ℂ (_root_.finSuccEquiv n)).trans (optionEquivRight ℂ (Fin n))).toAlgHom.toRingHom)
    (AlgEquiv.injective _) (fun c => X 0 - C c) ?_ (fun j => X j.succ) ?_ p hp d0 (by omega)
    (by omega) k hk
  · intro c
    simp [optionEquivRight_X_none, optionEquivRight_C]
  · intro j
    simp [optionEquivRight_X_some]

end OMA.GL

