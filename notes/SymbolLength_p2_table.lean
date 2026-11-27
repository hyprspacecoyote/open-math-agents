import FormalConjectures.Other.SymbolLengthMilnorKTheory

namespace OMA.Artin2

open MvPolynomial

variable {k : Type*} [Field k]

/-- Substitute `0` for the variables `X j` with `j < i`. -/
noncomputable def kill (N i : ℕ) : MvPolynomial (Fin N) k →ₐ[k] MvPolynomial (Fin N) k :=
  aeval fun j ↦ if (j : ℕ) < i then 0 else X j

theorem kill_succ_comp (N i : ℕ) :
    (kill (k := k) N (i + 1)).comp (kill N i) = kill N (i + 1) := by
  apply MvPolynomial.algHom_ext
  intro j
  simp only [kill, AlgHom.comp_apply, aeval_X]
  split_ifs with h1 h2 <;> simp_all
  omega

theorem ker_kill_le (N i : ℕ) :
    RingHom.ker (kill (k := k) N i) ≤ RingHom.ker (kill (k := k) N (i + 1)) := by
  intro f hf
  rw [RingHom.mem_ker] at hf ⊢
  rw [← kill_succ_comp, AlgHom.comp_apply]
  erw [hf]
  simp

theorem height_ker_kill (N : ℕ) :
    ∀ i ≤ N, (i : ℕ∞) ≤ (RingHom.ker (kill (k := k) N i)).height := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    have h1 := ih (by omega)
    have : (RingHom.ker (kill (k := k) N i)).IsPrime := RingHom.ker_isPrime _
    have : (RingHom.ker (kill (k := k) N (i + 1))).IsPrime := RingHom.ker_isPrime _
    have hlt : RingHom.ker (kill (k := k) N i) < RingHom.ker (kill (k := k) N (i + 1)) := by
      refine lt_of_le_of_ne (ker_kill_le N i) ?_
      intro h
      have hx : (X ⟨i, by omega⟩ : MvPolynomial (Fin N) k) ∈ RingHom.ker (kill (k := k) N (i + 1)) := by
        rw [RingHom.mem_ker]; simp [kill]
      rw [← h, RingHom.mem_ker] at hx
      simp [kill, X_ne_zero] at hx
    have := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    calc ((i + 1 : ℕ) : ℕ∞) = (i : ℕ∞) + 1 := by push_cast; rfl
      _ ≤ (RingHom.ker (kill (k := k) N i)).height + 1 := by gcongr
      _ ≤ _ := this

theorem mem_ker_kill_N {N : ℕ} (f : MvPolynomial (Fin N) k) :
    f ∈ RingHom.ker (kill (k := k) N N) ↔ constantCoeff f = 0 := by
  have : kill (k := k) N N = aeval 0 := by
    apply MvPolynomial.algHom_ext; intro j; simp [kill]
  rw [RingHom.mem_ker, this, aeval_zero]
  simp

/-- Over an algebraically closed field, finitely many polynomials without constant term, fewer
than the number of variables, have a common nonzero zero. -/
theorem exists_common_zero [IsAlgClosed k] {N : ℕ} (s : Finset (MvPolynomial (Fin N) k))
    (hs : s.card < N) (h0 : ∀ f ∈ s, constantCoeff f = 0) :
    ∃ v : Fin N → k, v ≠ 0 ∧ ∀ f ∈ s, eval v f = 0 := by
  by_contra hcon
  push Not at hcon
  set I : Ideal (MvPolynomial (Fin N) k) := Ideal.span (s : Set _)
  set M := RingHom.ker (kill (k := k) N N)
  have hM : M.IsPrime := RingHom.ker_isPrime _
  have hIM : I ≤ M := by
    rw [Ideal.span_le]
    intro f hf
    exact (mem_ker_kill_N f).mpr (h0 f hf)
  -- every common zero of `I` is `0`
  have hzero : ∀ v ∈ zeroLocus k I, v = 0 := by
    intro v hv
    by_contra hv0
    obtain ⟨f, hf, hfv⟩ := hcon v hv0
    apply hfv
    have := (mem_zeroLocus_iff.mp hv) f (Ideal.subset_span hf)
    simpa [aeval_eq_eval] using this
  have hMrad : M ≤ I.radical := by
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := k)]
    intro f hf v hv
    rw [hzero v hv]
    have := (mem_ker_kill_N f).mp hf
    simpa [aeval_zero] using this
  have hmin : M ∈ I.minimalPrimes := by
    refine ⟨⟨hM, hIM⟩, fun q hq hqM ↦ ?_⟩
    exact hMrad.trans ((Ideal.IsPrime.radical_le_iff hq.1).mpr hq.2)
  have h1 := Ideal.height_le_card_of_mem_minimalPrimes_span_finset hmin
  have h2 := height_ker_kill (k := k) N N le_rfl
  have : ((N : ℕ) : ℕ∞) ≤ s.card := h2.trans h1
  exact absurd (by exact_mod_cast this) (not_le.mpr hs)



theorem exists_common_zero' [IsAlgClosed k] {σ : Type*} [Fintype σ]
    (s : Finset (MvPolynomial σ k)) (hs : s.card < Fintype.card σ)
    (h0 : ∀ f ∈ s, constantCoeff f = 0) :
    ∃ v : σ → k, v ≠ 0 ∧ ∀ f ∈ s, eval v f = 0 := by
  classical
  set e := Fintype.equivFin σ
  obtain ⟨w, hw0, hw⟩ := exists_common_zero (s.image (rename e))
    (lt_of_le_of_lt Finset.card_image_le (by simpa using hs)) (by
      intro f hf
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hf
      rw [constantCoeff_rename]; exact h0 g hg)
  refine ⟨w ∘ e, ?_, ?_⟩
  · intro h; apply hw0; funext j
    have := congrFun h (e.symm j); simpa using this
  · intro f hf
    have := hw (rename e f) (Finset.mem_image_of_mem _ hf)
    rwa [eval_rename] at this

/-- The exponent of `x ^ j * y ^ l`. -/
noncomputable def mono (j l : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 j + Finsupp.single 1 l

@[simp] lemma mono_zero (j l : ℕ) : mono j l 0 = j := by simp [mono]
@[simp] lemma mono_one (j l : ℕ) : mono j l 1 = l := by simp [mono]
lemma eq_mono (m : Fin 2 →₀ ℕ) : m = mono (m 0) (m 1) := by
  ext i; fin_cases i <;> simp

lemma degreeOf_map_le' {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (n : Fin 2) (p : MvPolynomial (Fin 2) R) : degreeOf n (map f p) ≤ degreeOf n p := by
  rw [degreeOf_le_iff]
  intro m hm
  exact monomial_le_degreeOf n (support_map_subset f p hm)

/-- Lang's count for `C(x, y)`: a diagonal quadratic form in `5` variables with polynomial
coefficients has a nonzero polynomial zero. -/
theorem lang_poly (P : Fin 5 → MvPolynomial (Fin 2) ℂ) :
    ∃ W : Fin 5 → MvPolynomial (Fin 2) ℂ, W ≠ 0 ∧ ∑ i, P i * W i ^ 2 = 0 := by
  classical
  set r := ∑ i, (degreeOf 0 (P i) + degreeOf 1 (P i)) with hr
  set S := 5 * r + 5 with hS
  set E := 11 * r + 9 with hE
  have hPr : ∀ i n, degreeOf n (P i) ≤ r := by
    intro i n
    have h1 : degreeOf 0 (P i) + degreeOf 1 (P i) ≤ r :=
      Finset.single_le_sum (f := fun i ↦ degreeOf 0 (P i) + degreeOf 1 (P i))
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    fin_cases n <;> simp <;> omega
  let U := Fin 5 × Fin S × Fin S
  let V : Fin 5 → MvPolynomial (Fin 2) (MvPolynomial U ℂ) := fun i ↦
    ∑ jl : Fin S × Fin S, monomial (mono jl.1 jl.2) (X (i, jl.1, jl.2))
  let Q : MvPolynomial (Fin 2) (MvPolynomial U ℂ) := ∑ i, map C (P i) * V i ^ 2
  let eqs : Finset (MvPolynomial U ℂ) :=
    (Finset.univ : Finset (Fin E × Fin E)).image fun jl ↦ coeff (mono jl.1 jl.2) Q
  have hV : ∀ i n, degreeOf n (V i) ≤ S - 1 := by
    intro i n
    rw [degreeOf_le_iff]
    intro m hm
    obtain ⟨jl, -, hjl⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
    have := support_monomial_subset hjl
    rw [Finset.mem_singleton] at this
    subst this
    have h1 := jl.1.isLt
    have h2 := jl.2.isLt
    fin_cases n <;> simp <;> omega
  have hQ : ∀ n, degreeOf n Q ≤ r + 2 * (S - 1) := by
    intro n
    refine (degreeOf_sum_le n _ _).trans (Finset.sup_le fun i _ ↦ ?_)
    refine (degreeOf_mul_le n _ _).trans (add_le_add ((degreeOf_map_le' C n _).trans (hPr i n))
      ((degreeOf_pow_le n _ 2).trans ?_))
    exact Nat.mul_le_mul_left 2 (hV i n)
  have hcoeff : ∀ m : Fin 2 →₀ ℕ, E ≤ m 0 ∨ E ≤ m 1 → coeff m Q = 0 := by
    intro m hm
    by_contra hc
    have hsupp : m ∈ Q.support := mem_support_iff.mpr hc
    have h0 := (monomial_le_degreeOf 0 hsupp).trans (hQ 0)
    have h1 := (monomial_le_degreeOf 1 hsupp).trans (hQ 1)
    omega
  have hmap0 : map (constantCoeff : MvPolynomial U ℂ →+* ℂ) Q = 0 := by
    have : ∀ i, map (constantCoeff : MvPolynomial U ℂ →+* ℂ) (V i) = 0 := by
      intro i
      simp [V, map_sum, map_monomial]
    simp [Q, map_sum, this]
  have hcard : eqs.card < Fintype.card U := by
    refine lt_of_le_of_lt Finset.card_image_le ?_
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, U]
    nlinarith
  have h0 : ∀ f ∈ eqs, constantCoeff f = 0 := by
    intro f hf
    obtain ⟨jl, -, rfl⟩ := Finset.mem_image.mp hf
    rw [← coeff_map, hmap0, coeff_zero]
  obtain ⟨t, ht0, ht⟩ := exists_common_zero' (k := ℂ) eqs hcard h0
  let W : Fin 5 → MvPolynomial (Fin 2) ℂ := fun i ↦ map (eval t) (V i)
  have hmapQ : map (eval t) Q = ∑ i, P i * W i ^ 2 := by
    have hc : (eval t).comp (C : ℂ →+* MvPolynomial U ℂ) = RingHom.id ℂ := by
      ext; simp
    simp only [Q, W, map_sum, map_mul, map_pow, map_map, hc, map_id]
  have hQ0 : map (eval t) Q = 0 := by
    ext m
    rw [coeff_map, coeff_zero]
    by_cases hm : m 0 < E ∧ m 1 < E
    · apply ht
      refine Finset.mem_image.mpr ⟨(⟨m 0, hm.1⟩, ⟨m 1, hm.2⟩), Finset.mem_univ _, ?_⟩
      simp only
      rw [← eq_mono m]
    · rw [hcoeff m (by omega), map_zero]
  refine ⟨W, ?_, hmapQ ▸ hQ0⟩
  obtain ⟨⟨i, j, l⟩, hu⟩ := Function.ne_iff.mp ht0
  intro hW
  apply hu
  have hWi : W i = 0 := congrFun hW i
  have key : coeff (mono j l) (W i) = t (i, j, l) := by
    simp only [W, V, map_sum, map_monomial, eval_X, coeff_sum, coeff_monomial]
    rw [Finset.sum_eq_single (j, l)]
    · simp
    · rintro ⟨j', l'⟩ _ hne
      rw [if_neg]
      intro h
      apply hne
      have e0 := congrArg (fun m ↦ m 0) h
      have e1 := congrArg (fun m ↦ m 1) h
      simp only [mono_zero, mono_one] at e0 e1
      ext <;> simp [e0, e1]
    · simp
  rw [← key, hWi, coeff_zero]
  rfl



/-- Exponent vector of the monomial `∏ x_i ^ e_i`. -/
noncomputable def expo {m : ℕ} (e : Fin m → ℕ) : Fin m →₀ ℕ := Finsupp.equivFunOnFinite.symm e

@[simp] lemma expo_apply {m : ℕ} (e : Fin m → ℕ) (i : Fin m) : expo e i = e i := by
  simp [expo]

lemma expo_injective {m : ℕ} : Function.Injective (expo (m := m)) := by
  intro e e' h; funext i; simpa using congrArg (fun f ↦ f i) h

lemma degreeOf_map_le'' {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S) {m : ℕ}
    (n : Fin m) (p : MvPolynomial (Fin m) R) : degreeOf n (map f p) ≤ degreeOf n p := by
  rw [degreeOf_le_iff]
  intro d hd
  exact monomial_le_degreeOf n (support_map_subset f p hd)

/-- Lang's count over `C[x_1, ..., x_m]`, for a box of side `S`. -/
theorem lang_poly_gen {m : ℕ} {ι : Type*} [Fintype ι] (P : ι → MvPolynomial (Fin m) ℂ)
    (r S : ℕ) (hr : ∀ j n, degreeOf n (P j) ≤ r) (hS : 0 < S)
    (hcnt : (r + 2 * S - 1) ^ m < Fintype.card ι * S ^ m) :
    ∃ W : ι → MvPolynomial (Fin m) ℂ, W ≠ 0 ∧ ∑ j, P j * W j ^ 2 = 0 := by
  classical
  set E := r + 2 * S - 1 with hE
  let U := ι × (Fin m → Fin S)
  let V : ι → MvPolynomial (Fin m) (MvPolynomial U ℂ) := fun j ↦
    ∑ e : Fin m → Fin S, monomial (expo fun i ↦ (e i : ℕ)) (X (j, e))
  let Q : MvPolynomial (Fin m) (MvPolynomial U ℂ) := ∑ j, map C (P j) * V j ^ 2
  let eqs : Finset (MvPolynomial U ℂ) :=
    (Finset.univ : Finset (Fin m → Fin E)).image fun e ↦ coeff (expo fun i ↦ (e i : ℕ)) Q
  have hV : ∀ j n, degreeOf n (V j) ≤ S - 1 := by
    intro j n
    rw [degreeOf_le_iff]
    intro d hd
    obtain ⟨e, -, he⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hd)
    have := support_monomial_subset he
    rw [Finset.mem_singleton] at this
    subst this
    have := (e n).isLt
    simp only [expo_apply]
    omega
  have hQ : ∀ n, degreeOf n Q ≤ r + 2 * (S - 1) := by
    intro n
    refine (degreeOf_sum_le n _ _).trans (Finset.sup_le fun j _ ↦ ?_)
    refine (degreeOf_mul_le n _ _).trans (add_le_add ((degreeOf_map_le'' C n _).trans (hr j n))
      ((degreeOf_pow_le n _ 2).trans ?_))
    exact Nat.mul_le_mul_left 2 (hV j n)
  have hcoeff : ∀ d : Fin m →₀ ℕ, (∃ n, E ≤ d n) → coeff d Q = 0 := by
    rintro d ⟨n, hn⟩
    by_contra hc
    have := (monomial_le_degreeOf n (mem_support_iff.mpr hc)).trans (hQ n)
    omega
  have hmap0 : map (constantCoeff : MvPolynomial U ℂ →+* ℂ) Q = 0 := by
    have : ∀ j, map (constantCoeff : MvPolynomial U ℂ →+* ℂ) (V j) = 0 := by
      intro j
      simp [V, map_sum, map_monomial]
    simp [Q, map_sum, this]
  have hcard : eqs.card < Fintype.card U := by
    refine lt_of_le_of_lt Finset.card_image_le ?_
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_pi, Fintype.card_fin,
      Finset.prod_const, Finset.card_univ, U]
    simpa using hcnt
  have h0 : ∀ f ∈ eqs, constantCoeff f = 0 := by
    intro f hf
    obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp hf
    rw [← coeff_map, hmap0, coeff_zero]
  obtain ⟨t, ht0, ht⟩ := exists_common_zero' (k := ℂ) eqs hcard h0
  let W : ι → MvPolynomial (Fin m) ℂ := fun j ↦ map (eval t) (V j)
  have hmapQ : map (eval t) Q = ∑ j, P j * W j ^ 2 := by
    have hc : (eval t).comp (C : ℂ →+* MvPolynomial U ℂ) = RingHom.id ℂ := by
      ext; simp
    simp only [Q, W, map_sum, map_mul, map_pow, map_map, hc, map_id]
  have hQ0 : map (eval t) Q = 0 := by
    ext d
    rw [coeff_map, coeff_zero]
    by_cases hd : ∀ n, d n < E
    · apply ht
      refine Finset.mem_image.mpr ⟨fun n ↦ ⟨d n, hd n⟩, Finset.mem_univ _, ?_⟩
      congr 1
      ext n
      simp
    · push Not at hd
      rw [hcoeff d hd, map_zero]
  refine ⟨W, ?_, hmapQ ▸ hQ0⟩
  obtain ⟨⟨j, e⟩, hu⟩ := Function.ne_iff.mp ht0
  intro hW
  apply hu
  have hWj : W j = 0 := congrFun hW j
  have key : coeff (expo fun i ↦ (e i : ℕ)) (W j) = t (j, e) := by
    simp only [W, V, map_sum, map_monomial, eval_X, coeff_sum, coeff_monomial]
    rw [Finset.sum_eq_single e]
    · simp
    · intro e' _ hne
      rw [if_neg]
      intro h
      apply hne
      funext i
      have := congrArg (fun f ↦ f i) (expo_injective h)
      exact Fin.ext (by simpa using this)
    · simp
  rw [← key, hWj, coeff_zero]
  rfl

/-- A box side that makes Lang's count work when there are more than `2 ^ m` variables. -/
theorem exists_side (m r N : ℕ) (hN : 2 ^ m < N) :
    ∃ S, 0 < S ∧ (r + 2 * S - 1) ^ m < N * S ^ m := by
  have hlim : Filter.Tendsto (fun S : ℕ ↦ ((r : ℝ) / S + 2) ^ m) Filter.atTop
      (nhds ((0 + 2) ^ m)) :=
    ((tendsto_const_div_atTop_nhds_zero_nat (r : ℝ)).add_const 2).pow m
  have hlt : ((0 : ℝ) + 2) ^ m < N := by
    rw [zero_add]; exact_mod_cast hN
  obtain ⟨S, hS1, hS⟩ :=
    ((Filter.eventually_ge_atTop 1).and (hlim.eventually (gt_mem_nhds hlt))).exists
  refine ⟨S, hS1, ?_⟩
  have hSpos : (0 : ℝ) < S := by exact_mod_cast hS1
  have h1 : ((r + 2 * S : ℕ) : ℝ) ^ m < N * (S : ℝ) ^ m := by
    have : ((r : ℝ) / S + 2) ^ m * (S : ℝ) ^ m = ((r + 2 * S : ℕ) : ℝ) ^ m := by
      rw [← mul_pow]; congr 1; push_cast; field_simp
    rw [← this]
    exact mul_lt_mul_of_pos_right hS (pow_pos hSpos m)
  have h2 : (r + 2 * S) ^ m < N * S ^ m := by exact_mod_cast h1
  exact lt_of_le_of_lt (Nat.pow_le_pow_left (Nat.sub_le _ _) m) h2

/-- `C(x_1, ..., x_m)` has `u`-invariant at most `2 ^ m`. -/
theorem isotropic_gen {m : ℕ} {ι : Type*} [Fintype ι] (hι : 2 ^ m < Fintype.card ι)
    (q : ι → MvRatFunc (Fin m) ℂ) :
    ∃ v : ι → MvRatFunc (Fin m) ℂ, v ≠ 0 ∧ ∑ j, q j * v j ^ 2 = 0 := by
  classical
  have hex : ∀ j, ∃ nd : MvPolynomial (Fin m) ℂ × MvPolynomial (Fin m) ℂ, nd.2 ≠ 0 ∧
      q j = algebraMap _ (MvRatFunc (Fin m) ℂ) nd.1 / algebraMap _ (MvRatFunc (Fin m) ℂ) nd.2 := by
    intro j
    obtain ⟨n, d, hd, h⟩ := IsFractionRing.div_surjective (MvPolynomial (Fin m) ℂ) (q j)
    exact ⟨(n, d), nonZeroDivisors.ne_zero hd, h.symm⟩
  choose nd hd hq using hex
  have hinj : Function.Injective (algebraMap (MvPolynomial (Fin m) ℂ) (MvRatFunc (Fin m) ℂ)) :=
    IsFractionRing.injective _ _
  let P : ι → MvPolynomial (Fin m) ℂ := fun j ↦
    (nd j).1 * ∏ k ∈ Finset.univ.erase j, (nd k).2
  set r := ∑ j, ∑ n, degreeOf n (P j)
  have hr : ∀ j n, degreeOf n (P j) ≤ r := by
    intro j n
    exact (Finset.single_le_sum (f := fun n ↦ degreeOf n (P j)) (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ n)).trans (Finset.single_le_sum (f := fun j ↦ ∑ n, degreeOf n (P j))
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j))
  obtain ⟨S, hS, hcnt⟩ := exists_side m r (Fintype.card ι) hι
  obtain ⟨W, hW0, hW⟩ := lang_poly_gen P r S hr hS hcnt
  set Dn := ∏ k, (nd k).2
  have hDn : algebraMap _ (MvRatFunc (Fin m) ℂ) Dn ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr (Finset.prod_ne_zero_iff.mpr fun k _ ↦ hd k)
  have hP : ∀ j, algebraMap _ (MvRatFunc (Fin m) ℂ) (P j) =
      q j * algebraMap _ (MvRatFunc (Fin m) ℂ) Dn := by
    intro j
    have hdj : algebraMap _ (MvRatFunc (Fin m) ℂ) (nd j).2 ≠ 0 := (map_ne_zero_iff _ hinj).mpr (hd j)
    simp only [P, Dn, map_mul, map_prod, hq j]
    rw [← Finset.mul_prod_erase Finset.univ
      (fun k ↦ algebraMap _ (MvRatFunc (Fin m) ℂ) (nd k).2) (Finset.mem_univ j)]
    field_simp
  refine ⟨fun j ↦ algebraMap _ (MvRatFunc (Fin m) ℂ) (W j), ?_, ?_⟩
  · intro h
    apply hW0
    funext j
    have := congrFun h j
    simp only [Pi.zero_apply] at this ⊢
    exact (map_eq_zero_iff _ hinj).mp this
  · have := congrArg (algebraMap _ (MvRatFunc (Fin m) ℂ)) hW
    simp only [map_sum, map_mul, map_pow, map_zero, hP] at this
    have h2 : (∑ j, q j * algebraMap _ (MvRatFunc (Fin m) ℂ) (W j) ^ 2) *
        algebraMap _ (MvRatFunc (Fin m) ℂ) Dn = 0 := by
      rw [Finset.sum_mul, ← this]
      refine Finset.sum_congr rfl fun j _ ↦ by ring
    exact (mul_eq_zero.mp h2).resolve_right hDn

end OMA.Artin2


namespace OMA.Artin2K

open MilnorK

variable {F : Type*} [Field F]

theorem add_self_eq_zero (x : MilnorK F 2) : x + x = 0 := by
  have h2 : (2 : MilnorK F 2) = 0 := by exact_mod_cast natCast_eq_zero (F := F) 2
  rw [← two_mul, h2, zero_mul]

theorem neg_eq_self (x : MilnorK F 2) : -x = x := by
  rw [neg_eq_iff_add_eq_zero, add_self_eq_zero]

theorem of_sq (u : Fˣ) : of 2 (u ^ 2) = 0 := by
  rw [of_pow, two_smul, add_self_eq_zero]

theorem of_neg_one (hi : ∃ i : F, i * i = -1) : of 2 (-1 : Fˣ) = 0 := by
  obtain ⟨i, hi⟩ := hi
  have hi0 : i ≠ 0 := by
    rintro rfl; simp at hi
  have : (-1 : Fˣ) = (Units.mk0 i hi0) ^ 2 := by
    ext; simp [sq, hi]
  rw [this, of_sq]

theorem of_neg (hi : ∃ i : F, i * i = -1) (a : Fˣ) : of 2 (-a) = of 2 a := by
  rw [show -a = (-1) * a by simp, of_mul, of_neg_one hi, zero_add]

theorem of_mul_self (hi : ∃ i : F, i * i = -1) (a : Fˣ) : of 2 a * of 2 a = 0 := by
  by_cases ha : a = 1
  · simp [ha]
  have h1 : (1 : F) - a ≠ 0 := by
    intro h; apply ha; apply Units.ext; show (a : F) = 1; linear_combination -h
  have h2 : (1 : F) - (a⁻¹ : Fˣ) ≠ 0 := by
    intro h; apply ha; apply Units.ext; show (a : F) = 1
    have : ((a⁻¹ : Fˣ) : F) = 1 := by linear_combination -h
    simpa using congrArg (fun z : F ↦ z⁻¹) this
  set b := Units.mk0 _ h1
  set c := Units.mk0 _ h2
  have hb : of 2 a * of 2 b = 0 := of_mul_of_eq_zero 2 a b (by simp [b])
  have hc : of 2 a⁻¹ * of 2 c = 0 := of_mul_of_eq_zero 2 a⁻¹ c (by simp [c])
  have hc' : of 2 a * of 2 c = 0 := by
    rw [of_inv, neg_eq_self] at hc; exact hc
  have hneg : -a = b * c⁻¹ := by
    have ha0 : (a : F) ≠ 0 := a.ne_zero
    ext
    simp only [Units.val_neg, Units.val_mul, b, c, Units.val_mk0, Units.val_inv_eq_inv_val]
    field_simp
    have : (a : F) - 1 ≠ 0 := by intro h; apply h1; linear_combination -h
    field_simp
    ring
  have : of 2 a * of 2 (-a) = 0 := by
    rw [hneg, of_mul, of_inv, neg_eq_self, mul_add, hb, hc', add_zero]
  rwa [of_neg hi] at this

theorem of_comm (hi : ∃ i : F, i * i = -1) (a b : Fˣ) : of 2 a * of 2 b = of 2 b * of 2 a := by
  have h := of_mul_self hi (a * b)
  rw [of_mul, add_mul, mul_add, mul_add, of_mul_self hi a, of_mul_self hi b, zero_add,
    add_zero] at h
  rw [← neg_eq_self (of 2 b * of 2 a)]
  exact eq_neg_of_add_eq_zero_left h

/-- `{s, t} = {e, s t}` when `s + t = e`. -/
theorem steinberg2 (hi : ∃ i : F, i * i = -1) (s t e : Fˣ) (h : (s : F) + t = e) :
    of 2 s * of 2 t = of 2 e * of 2 (s * t) := by
  have hst : of 2 (s * e⁻¹) * of 2 (t * e⁻¹) = 0 :=
    of_mul_of_eq_zero 2 _ _ (by
      have he : (e : F) ≠ 0 := e.ne_zero
      simp only [Units.val_mul, Units.val_inv_eq_inv_val]
      field_simp; linear_combination h)
  simp only [of_mul, of_inv, neg_eq_self] at hst
  rw [add_mul, mul_add, mul_add, of_mul_self hi e, add_zero] at hst
  rw [of_mul, mul_add, of_comm hi e s]
  have h3 : of 2 s * of 2 t = -(of 2 s * of 2 e + of 2 e * of 2 t) :=
    eq_neg_of_add_eq_zero_left (by rw [← add_assoc]; exact hst)
  rw [h3, neg_eq_self]

/-- If `e = a x² + b y²` then `{a, b} = {e, a b}`. -/
theorem slot2 (hi : ∃ i : F, i * i = -1) (a b e : Fˣ) (x y : F) (h : (e : F) = a * x ^ 2 + b * y ^ 2) :
    of 2 a * of 2 b = of 2 e * of 2 (a * b) := by
  by_cases hx : x = 0
  · have hy : y ≠ 0 := by rintro rfl; subst hx; simp at h
    have he : e = b * (Units.mk0 y hy) ^ 2 := by ext; simp [h, hx]
    rw [he, of_mul, of_sq, add_zero, of_mul, mul_add, of_mul_self hi, add_zero, of_comm hi]
  by_cases hy : y = 0
  · have he : e = a * (Units.mk0 x hx) ^ 2 := by ext; simp [h, hy]
    rw [he, of_mul, of_sq, add_zero, of_mul, mul_add, of_mul_self hi, zero_add]
  set s := a * (Units.mk0 x hx) ^ 2
  set t := b * (Units.mk0 y hy) ^ 2
  have hst := steinberg2 hi s t e (by simp [s, t, h])
  have e1 : of 2 s = of 2 a := by simp only [s, of_mul, of_sq, add_zero]
  have e2 : of 2 t = of 2 b := by simp only [t, of_mul, of_sq, add_zero]
  have e3 : of 2 (s * t) = of 2 (a * b) := by
    simp only [s, t, of_mul, of_sq, add_zero]
  rw [e1, e2, e3] at hst
  exact hst

/-- If `u = x² + b z² ≠ 0` then `{u, b} = 0`. -/
theorem norm_slot (hi : ∃ i : F, i * i = -1) (b u : Fˣ) (x z : F) (h : (u : F) = x ^ 2 + b * z ^ 2) :
    of 2 u * of 2 b = 0 := by
  have := slot2 hi b 1 u z x (by rw [h]; simp; ring)
  rw [of_one, mul_zero, mul_one] at this
  exact this.symm

/-- If `e = a x² + b y² + a b z² ≠ 0` then `{a, b} = {e, f}` for some `f`. -/
theorem slot3 (hi : ∃ i : F, i * i = -1) (a b e : Fˣ) (x y z : F) (h : (e : F) = a * x ^ 2 + b * y ^ 2 + a * b * z ^ 2) :
    ∃ f : Fˣ, of 2 a * of 2 b = of 2 e * of 2 f := by
  by_cases hu : x ^ 2 + (b : F) * z ^ 2 = 0
  · exact ⟨a * b, slot2 hi a b e 0 y (by rw [h]; linear_combination (a : F) * hu)⟩
  set u := Units.mk0 _ hu
  have hub := norm_slot hi b u x z rfl
  refine ⟨a * u * b, ?_⟩
  have h2 := slot2 hi (a * u) b e 1 y (by rw [h]; simp [u]; ring)
  rw [of_mul 2 a u, add_mul, hub, add_zero] at h2
  exact h2

/-- If `a x² + b y² + a b z² = 0` with `(x, y, z) ≠ 0` then `{a, b} = 0`. -/
theorem slot3_zero (hi : ∃ i : F, i * i = -1) (a b : Fˣ) (x y z : F) (hne : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0)
    (h : (a : F) * x ^ 2 + b * y ^ 2 + a * b * z ^ 2 = 0) : of 2 a * of 2 b = 0 := by
  by_cases hu : x ^ 2 + (b : F) * z ^ 2 = 0
  · have hy : (b : F) * y ^ 2 = 0 := by linear_combination h - (a : F) * hu
    have hy0 : y = 0 := by
      rcases mul_eq_zero.mp hy with hb | hy
      · exact absurd hb b.ne_zero
      · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hy
    have hz : z ≠ 0 := by
      rintro rfl
      have : x = 0 := by simpa using hu
      rcases hne with h1 | h1 | h1 <;> contradiction
    have hx : x ≠ 0 := by
      rintro rfl
      have : (b : F) * z ^ 2 = 0 := by simpa using hu
      rcases mul_eq_zero.mp this with hb | hz'
      · exact b.ne_zero hb
      · exact hz (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hz')
    have hb : b = -(Units.mk0 x hx * (Units.mk0 z hz)⁻¹) ^ 2 := by
      ext
      simp only [Units.val_neg, Units.val_pow_eq_pow_val, Units.val_mul, Units.val_mk0,
        Units.val_inv_eq_inv_val]
      field_simp
      linear_combination hu
    rw [hb, of_neg hi, of_sq, mul_zero]
  · set u := Units.mk0 _ hu
    have hub := norm_slot hi b u x z rfl
    have hy : y ≠ 0 := by
      rintro rfl
      apply hu
      have : (a : F) * (x ^ 2 + b * z ^ 2) = 0 := by linear_combination h
      exact (mul_eq_zero.mp this).resolve_left a.ne_zero
    -- a u = -b y², so a = -b y² u⁻¹
    have ha : a = -(b * (Units.mk0 y hy) ^ 2 * u⁻¹) := by
      ext
      have hu0 : (u : F) ≠ 0 := u.ne_zero
      simp only [Units.val_neg, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0,
        Units.val_inv_eq_inv_val]
      field_simp
      simp only [u, Units.val_mk0]
      linear_combination h
    rw [ha, of_neg hi, of_mul, of_mul, of_sq, add_zero, of_inv, neg_eq_self, add_mul,
      of_mul_self hi, hub, add_zero]

/-- Common slot: over a field where `-1` is a square and every diagonal quadratic form in `5`
variables is isotropic, the sum of two symbols mod `2` is a symbol. -/
theorem sum_two (hi : ∃ i : F, i * i = -1) (hu : ∀ q : Fin 5 → F, ∃ v : Fin 5 → F, v ≠ 0 ∧ ∑ i, q i * v i ^ 2 = 0)
    (a b c d : Fˣ) : ∃ e f : Fˣ, of 2 a * of 2 b + of 2 c * of 2 d = of 2 e * of 2 f := by
  obtain ⟨i, hi'⟩ := hi
  obtain ⟨v, hv0, hv⟩ := hu ![a, b, a * b, c, d]
  replace hv : (a : F) * v 0 ^ 2 + b * v 1 ^ 2 + a * b * v 2 ^ 2 + c * v 3 ^ 2 + d * v 4 ^ 2 = 0 := by
    simpa [Fin.sum_univ_five] using hv
  set E : F := a * v 0 ^ 2 + b * v 1 ^ 2 + a * b * v 2 ^ 2 with hE
  by_cases hE0 : E = 0
  · have hcd : (c : F) * v 3 ^ 2 + d * v 4 ^ 2 = 0 := by linear_combination hv - hE0
    by_cases hx : v 0 ≠ 0 ∨ v 1 ≠ 0 ∨ v 2 ≠ 0
    · refine ⟨c, d, ?_⟩
      rw [slot3_zero ⟨i, hi'⟩ a b _ _ _ hx hE0, zero_add]
    · push Not at hx
      have hy : v 3 ≠ 0 ∨ v 4 ≠ 0 := by
        by_contra hy; push Not at hy
        apply hv0; funext j; fin_cases j <;> simp [hx, hy]
      refine ⟨a, b, ?_⟩
      have := slot3_zero ⟨i, hi'⟩ c d (v 3) (v 4) 0 (by tauto) (by simpa using hcd)
      rw [this, add_zero]
  · set e := Units.mk0 E hE0
    obtain ⟨f, hf⟩ := slot3 ⟨i, hi'⟩ a b e (v 0) (v 1) (v 2) rfl
    have hcd := slot2 ⟨i, hi'⟩ c d e (i * v 3) (i * v 4) (by
      simp only [e, Units.val_mk0]
      linear_combination (-(c : F) * v 3 ^ 2 - d * v 4 ^ 2) * hi' + hv)
    refine ⟨e, f * (c * d), ?_⟩
    rw [hf, hcd, ← mul_add, ← of_mul]

end OMA.Artin2K

namespace OMA.PfK

open MilnorK OMA.Artin2K

variable {F : Type*} [Field F]

/-- The class `{a_1, ..., a_n}` of a list of units. -/
noncomputable def S (l : List Fˣ) : MilnorK F 2 := (l.map (of 2)).prod

@[simp] lemma S_nil : S ([] : List Fˣ) = 1 := rfl

@[simp] lemma S_cons (a : Fˣ) (l : List Fˣ) : S (a :: l) = of 2 a * S l := by
  simp [S]

lemma commute_S (hi : ∃ i : F, i * i = -1) (a : Fˣ) (l : List Fˣ) :
    Commute (of 2 a) (S l) := by
  induction l with
  | nil => exact Commute.one_right _
  | cons b l ih => rw [S_cons]; exact Commute.mul_right (of_comm hi a b) ih

/-- Values (including `0`) of the Pfister form `<<l>>`. -/
def Qv : List Fˣ → Set F
  | [] => {y | ∃ x, y = x ^ 2}
  | a :: l => {y | ∃ q₁ ∈ Qv l, ∃ q₂ ∈ Qv l, y = q₁ + a * q₂}

/-- Values (including `0`) of the pure part of `<<l>>`. -/
def Pv : List Fˣ → Set F
  | [] => {0}
  | a :: l => {y | ∃ p ∈ Pv l, ∃ q ∈ Qv l, y = p + a * q}

/-- Values of a Pfister form are norms: `{l, q} = 0`. -/
theorem norm_Qv (hi : ∃ i : F, i * i = -1) :
    ∀ (l : List Fˣ) (q : Fˣ), (q : F) ∈ Qv l → S l * of 2 q = 0 := by
  intro l
  induction l with
  | nil =>
    rintro q ⟨x, hx⟩
    have hx0 : x ≠ 0 := by rintro rfl; exact q.ne_zero (by simpa using hx)
    have : q = (Units.mk0 x hx0) ^ 2 := by ext; simp [hx]
    rw [this, of_sq, mul_zero]
  | cons a l ih =>
    rintro q ⟨q₁, h₁, q₂, h₂, hq⟩
    have hcomm := commute_S hi a l
    rw [S_cons]
    by_cases hq₂ : q₂ = 0
    · have hq₁ : q₁ ≠ 0 := by rintro rfl; apply q.ne_zero; rw [hq, hq₂]; simp
      have hu : ((Units.mk0 q₁ hq₁ : Fˣ) : F) ∈ Qv l := by simpa using h₁
      have : q = Units.mk0 q₁ hq₁ := by ext; simp [hq, hq₂]
      rw [this, mul_assoc, ih _ hu, mul_zero]
    by_cases hq₁ : q₁ = 0
    · have hu : ((Units.mk0 q₂ hq₂ : Fˣ) : F) ∈ Qv l := by simpa using h₂
      have : q = a * Units.mk0 q₂ hq₂ := by ext; simp [hq, hq₁]
      rw [this, of_mul, mul_add]
      have t1 : of 2 a * S l * of 2 a = 0 := by
        rw [mul_assoc, ← hcomm.eq, ← mul_assoc, of_mul_self hi, zero_mul]
      have t2 : of 2 a * S l * of 2 (Units.mk0 q₂ hq₂) = 0 := by
        rw [mul_assoc, ih _ hu, mul_zero]
      rw [t1, t2, add_zero]
    set u₁ := Units.mk0 q₁ hq₁ with hu₁def
    set u₂ := Units.mk0 q₂ hq₂ with hu₂def
    have hu1 : (u₁ : F) ∈ Qv l := by simpa [hu₁def] using h₁
    have hu2 : (u₂ : F) ∈ Qv l := by simpa [hu₂def] using h₂
    set c := a * u₂ * u₁⁻¹ with hcdef
    have hw : (1 : F) + c ≠ 0 := by
      intro h
      apply q.ne_zero
      rw [hq]
      have : (q₁ : F) + a * q₂ = q₁ * (1 + c) := by
        simp only [hcdef, hu₁def, hu₂def, Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val]
        field_simp
      rw [this, h, mul_zero]
    set w := Units.mk0 _ hw with hwdef
    have hqw : q = u₁ * w := by
      ext
      simp only [hq, hwdef, hu₁def, hcdef, hu₂def, Units.val_mul, Units.val_mk0,
        Units.val_inv_eq_inv_val]
      field_simp
    have ha : a = c * u₁ * u₂⁻¹ := by
      rw [hcdef]; group
    have hcw : of 2 c * of 2 w = 0 := by
      have := of_mul_of_eq_zero 2 (-c) w (by simp only [hwdef, Units.val_neg, Units.val_mk0]; ring)
      rwa [of_neg hi] at this
    rw [hqw, of_mul, mul_add]
    have t1 : of 2 a * S l * of 2 u₁ = 0 := by rw [mul_assoc, ih u₁ hu1, mul_zero]
    have t2 : of 2 a * S l * of 2 w = 0 := by
      rw [hcomm.eq, mul_assoc]
      have hsplit : of 2 a * of 2 w = of 2 u₁ * of 2 w + of 2 u₂ * of 2 w := by
        rw [ha, of_mul, of_mul, of_inv, OMA.Artin2K.neg_eq_self, add_mul, add_mul, hcw, zero_add]
      rw [hsplit, mul_add, ← mul_assoc, ← mul_assoc, ih u₁ hu1, ih u₂ hu2, zero_mul, add_zero]
    rw [t1, t2, add_zero]

/-- Slot lemma: a nonzero value `e` of the pure part of `<<l>>` is a slot of `{l}`. -/
theorem slot_Pv (hi : ∃ i : F, i * i = -1) :
    ∀ (l : List Fˣ) (e : Fˣ), (e : F) ∈ Pv l → ∃ l' : List Fˣ, S l = of 2 e * S l' := by
  intro l
  induction l with
  | nil =>
    rintro e he
    exact absurd (show (e : F) = 0 from he) e.ne_zero
  | cons a l ih =>
    rintro e ⟨p, hp, q, hq, he⟩
    by_cases hq0 : q = 0
    · obtain ⟨l', hl'⟩ := ih e (by rw [he, hq0, mul_zero, add_zero]; exact hp)
      refine ⟨a :: l', ?_⟩
      rw [S_cons, hl', S_cons, ← mul_assoc, ← mul_assoc, of_comm hi a e]
    set uq := Units.mk0 q hq0 with huqdef
    have hnorm := norm_Qv hi l uq (by simpa [huqdef] using hq)
    have hSa : S (a :: l) = S l * of 2 (a * uq) := by
      rw [S_cons, (commute_S hi a l).eq, of_mul, mul_add, hnorm, add_zero]
    by_cases hp0 : p = 0
    · refine ⟨l, ?_⟩
      have : e = a * uq := by ext; simp [he, hp0, huqdef]
      rw [hSa, ← this, (commute_S hi e l).eq]
    set up := Units.mk0 p hp0 with hupdef
    obtain ⟨l', hl'⟩ := ih up (by simpa [hupdef] using hp)
    set c := a * uq
    have hst := steinberg2 hi up c e (by simp [hupdef, c, huqdef, he])
    refine ⟨(up * c) :: l', ?_⟩
    rw [hSa, hl', S_cons, mul_assoc, ← (commute_S hi c l').eq, ← mul_assoc, hst, mul_assoc]

/-- The coefficient `∏_{i ∈ s} a_i` of the Pfister form. -/
noncomputable def coef {n : ℕ} (a : Fin n → Fˣ) (s : Fin n → Bool) : F :=
  ∏ i, if s i then (a i : F) else 1

lemma coef_ne_zero {n : ℕ} (a : Fin n → Fˣ) (s : Fin n → Bool) : coef a s ≠ 0 := by
  unfold coef
  refine Finset.prod_ne_zero_iff.mpr fun i _ ↦ ?_
  split_ifs
  · exact (a i).ne_zero
  · exact one_ne_zero

lemma coef_false {n : ℕ} (a : Fin n → Fˣ) : coef a (fun _ ↦ false) = 1 := by
  simp [coef]

lemma coef_cons {n : ℕ} (a : Fin (n + 1) → Fˣ) (b : Bool) (t : Fin n → Bool) :
    coef a (Fin.cons b t) = (if b then (a 0 : F) else 1) * coef (fun i ↦ a i.succ) t := by
  simp [coef, Fin.prod_univ_succ]

lemma sum_cons {n : ℕ} (g : (Fin (n + 1) → Bool) → F) :
    ∑ s, g s = ∑ t : Fin n → Bool, g (Fin.cons true t) + ∑ t : Fin n → Bool, g (Fin.cons false t) := by
  rw [← Fintype.sum_equiv (Fin.consEquiv fun _ ↦ Bool) (fun p ↦ g (Fin.cons p.1 p.2)) g
    (fun _ ↦ rfl), Fintype.sum_prod_type, Fintype.sum_bool]

/-- Values of the diagonal form `∑ coef a s * x_s ^ 2` lie in `Qv`, and in `Pv` when the
coefficient of `1` is not used. -/
theorem mem_Qv_Pv : ∀ (n : ℕ) (a : Fin n → Fˣ) (x : (Fin n → Bool) → F),
    (∑ s, coef a s * x s ^ 2 ∈ Qv (List.ofFn a)) ∧
    (x (fun _ ↦ false) = 0 → ∑ s, coef a s * x s ^ 2 ∈ Pv (List.ofFn a)) := by
  intro n
  induction n with
  | zero =>
    intro a x
    have hs : ∀ s : Fin 0 → Bool, s = fun _ ↦ false := fun s ↦ funext fun i ↦ i.elim0
    have hsum : ∑ s, coef a s * x s ^ 2 = x (fun _ ↦ false) ^ 2 := by
      rw [Fintype.sum_eq_single (fun _ ↦ false) (fun s h ↦ absurd (hs s) h), coef_false, one_mul]
    refine ⟨⟨x (fun _ ↦ false), hsum⟩, fun h0 ↦ ?_⟩
    show _ = (0 : F)
    rw [hsum, h0]; ring
  | succ n ih =>
    intro a x
    rw [List.ofFn_succ]
    have hsplit : ∑ s, coef a s * x s ^ 2 =
        ∑ t, coef (fun i ↦ a i.succ) t * x (Fin.cons false t) ^ 2 +
        a 0 * ∑ t, coef (fun i ↦ a i.succ) t * x (Fin.cons true t) ^ 2 := by
      rw [sum_cons, Finset.mul_sum, add_comm]
      congr 1
      · refine Finset.sum_congr rfl fun t _ ↦ ?_
        rw [coef_cons]; simp
      · refine Finset.sum_congr rfl fun t _ ↦ ?_
        rw [coef_cons]; simp; ring
    obtain ⟨h1, h1'⟩ := ih (fun i ↦ a i.succ) (fun t ↦ x (Fin.cons false t))
    obtain ⟨h2, -⟩ := ih (fun i ↦ a i.succ) (fun t ↦ x (Fin.cons true t))
    refine ⟨⟨_, h1, _, h2, hsplit⟩, fun h0 ↦ ⟨_, h1' ?_, _, h2, hsplit⟩⟩
    have : (Fin.cons false (fun _ ↦ false) : Fin (n + 1) → Bool) = fun _ ↦ false := by
      funext i; refine Fin.cases rfl (fun j ↦ rfl) i
    simpa [this] using h0

/-- An isotropic pure part represents `1`. -/
theorem pure_universal {n : ℕ} (h2 : (2 : F) ≠ 0) (a : Fin n → Fˣ)
    (x : (Fin n → Bool) → F) (hx0 : x (fun _ ↦ false) = 0) (hx : x ≠ 0)
    (hsum : ∑ s, coef a s * x s ^ 2 = 0) :
    ∃ y : (Fin n → Bool) → F, y (fun _ ↦ false) = 0 ∧ ∑ s, coef a s * y s ^ 2 = 1 := by
  classical
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hx
  have hk0 : k ≠ fun _ ↦ false := by rintro rfl; exact hk hx0
  have hck := coef_ne_zero a k
  have hk' : x k ≠ 0 := hk
  set lam := (1 - coef a k) / (2 * coef a k * x k)
  refine ⟨fun s ↦ lam * x s + if s = k then 1 else 0, ?_, ?_⟩
  · simp [hx0, Ne.symm hk0]
  · have : ∀ s, coef a s * (lam * x s + if s = k then 1 else 0) ^ 2 =
        lam ^ 2 * (coef a s * x s ^ 2) +
          (if s = k then 2 * lam * coef a k * x k + coef a k else 0) := by
      intro s
      split_ifs with h
      · subst h; ring
      · ring
    rw [Finset.sum_congr rfl fun s _ ↦ this s, Finset.sum_add_distrib, ← Finset.mul_sum, hsum,
      mul_zero, zero_add, Finset.sum_ite_eq' Finset.univ k, if_pos (Finset.mem_univ k)]
    simp only [lam]
    field_simp
    ring

/-- `K_{m+1}/2 = 0` once `-1` is a square, `2 ≠ 0`, and forms of dimension `2^m + 1` are
isotropic: `{a_1, ..., a_m, c} = 0`. -/
theorem kill (hi : ∃ i : F, i * i = -1) (h2 : (2 : F) ≠ 0) {m : ℕ}
    (hu : ∀ q : ((Fin m → Bool) ⊕ Unit) → F, ∃ v : ((Fin m → Bool) ⊕ Unit) → F, v ≠ 0 ∧
      ∑ j, q j * v j ^ 2 = 0)
    (a : Fin m → Fˣ) (c : Fˣ) : S (List.ofFn a) * of 2 c = 0 := by
  classical
  obtain ⟨i, hi'⟩ := hi
  obtain ⟨v, hv0, hv⟩ := hu (Sum.elim (coef a) fun _ ↦ (c : F))
  rw [Fintype.sum_sum_type] at hv
  simp only [Sum.elim_inl, Sum.elim_inr, Fintype.univ_unit, Finset.sum_singleton] at hv
  set x : (Fin m → Bool) → F := fun s ↦ v (Sum.inl s)
  set z := v (Sum.inr ())
  set o : Fin m → Bool := fun _ ↦ false
  set x' := Function.update x o 0
  set E := ∑ s, coef a s * x' s ^ 2
  have hv' : ∑ s, coef a s * x s ^ 2 + c * z ^ 2 = 0 := hv
  have hx_split : ∑ s, coef a s * x s ^ 2 =
      x o ^ 2 + ∑ s ∈ Finset.univ.erase o, coef a s * x s ^ 2 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ o), coef_false, one_mul]
  have hE_split : E = ∑ s ∈ Finset.univ.erase o, coef a s * x s ^ 2 := by
    simp only [E]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ o)]
    simp only [x', Function.update_self]
    rw [zero_pow two_ne_zero, mul_zero, zero_add]
    refine Finset.sum_congr rfl fun s hs ↦ ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hs)]
  have hE : E + x o ^ 2 + c * z ^ 2 = 0 := by
    rw [hx_split] at hv'; rw [hE_split]; linear_combination hv'
  have hEP : E ∈ Pv (List.ofFn a) := (mem_Qv_Pv m a x').2 (by show x' o = 0; simp [x'])
  by_cases hE0 : E = 0
  · have hoz : x o ^ 2 + (c : F) * z ^ 2 = 0 := by linear_combination hE - hE0
    by_cases hz : z = 0
    · have hxo : x o = 0 := by simpa [hz] using hoz
      -- pure part isotropic
      have hx' : x' = x := by
        funext s; by_cases hs : s = o
        · subst hs; simp [x', hxo]
        · simp [x', Function.update_of_ne hs]
      have hxne : x ≠ 0 := by
        intro h; apply hv0; funext j
        rcases j with s | u
        · exact congrFun h s
        · cases u; exact hz
      obtain ⟨y, hy0, hy⟩ := pure_universal h2 a x hxo hxne (by rw [← hx']; exact hE0)
      have h1 : ((1 : Fˣ) : F) ∈ Pv (List.ofFn a) := by
        rw [Units.val_one, ← hy]; exact (mem_Qv_Pv m a y).2 hy0
      obtain ⟨l', hl'⟩ := slot_Pv ⟨i, hi'⟩ _ 1 h1
      rw [hl', of_one, zero_mul, zero_mul]
    · have hxo : x o ≠ 0 := by
        intro h; apply hz
        have : (c : F) * z ^ 2 = 0 := by simpa [h] using hoz
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
          ((mul_eq_zero.mp this).resolve_left c.ne_zero)
      have hc : c = -(Units.mk0 (x o) hxo * (Units.mk0 z hz)⁻¹) ^ 2 := by
        ext
        simp only [Units.val_neg, Units.val_pow_eq_pow_val, Units.val_mul, Units.val_mk0,
          Units.val_inv_eq_inv_val]
        field_simp
        linear_combination hoz
      rw [hc, of_neg ⟨i, hi'⟩, of_sq, mul_zero]
  · set e := Units.mk0 E hE0
    obtain ⟨l', hl'⟩ := slot_Pv ⟨i, hi'⟩ _ e hEP
    have hec : of 2 e * of 2 c = 0 :=
      norm_slot ⟨i, hi'⟩ c e (i * x o) (i * z) (by
        simp only [e, Units.val_mk0]
        linear_combination (-(x o) ^ 2 - (c : F) * z ^ 2) * hi' + hE)
    rw [hl', mul_assoc, ← (commute_S ⟨i, hi'⟩ c l').eq, ← mul_assoc, hec, zero_mul]

end OMA.PfK

namespace OMA.PfK

open MilnorK

theorem sqrt_neg_one (m : ℕ) : ∃ i : MvRatFunc (Fin m) ℂ, i * i = -1 :=
  ⟨algebraMap (MvPolynomial (Fin m) ℂ) _ (MvPolynomial.C Complex.I), by
    rw [← map_mul, ← MvPolynomial.C_mul, Complex.I_mul_I, MvPolynomial.C_neg,
      MvPolynomial.C_1, map_neg, map_one]⟩

theorem two_ne_zero' (m : ℕ) : (2 : MvRatFunc (Fin m) ℂ) ≠ 0 := by
  have hinj := IsFractionRing.injective (MvPolynomial (Fin m) ℂ) (MvRatFunc (Fin m) ℂ)
  have h : (MvPolynomial.C (2 : ℂ) : MvPolynomial (Fin m) ℂ) ≠ 0 := by
    rw [Ne, MvPolynomial.C_eq_zero]; norm_num
  have h' := (map_ne_zero_iff _ hinj).mpr h
  have e : (algebraMap (MvPolynomial (Fin m) ℂ) (MvRatFunc (Fin m) ℂ)) (MvPolynomial.C 2) = 2 := by
    rw [show (MvPolynomial.C (2 : ℂ) : MvPolynomial (Fin m) ℂ) = 2 from map_ofNat _ 2, map_ofNat]
  rwa [e] at h'

/-- Bass-Tate vanishing for `p = 2`: `K_{m+1}(C(x_1, ..., x_m))/2 = 0`. -/
theorem grade_succ_bot (m : ℕ) : grade (MvRatFunc (Fin m) ℂ) 2 (m + 1) = ⊥ := by
  rw [eq_bot_iff, MilnorK.grade, AddSubgroup.closure_le]
  rintro _ ⟨s, rfl⟩
  rw [SetLike.mem_coe, AddSubgroup.mem_bot, symbol_succ]
  have hS : symbol 2 (fun i ↦ s i.succ) = S (List.ofFn fun i ↦ s i.succ) := by
    simp [symbol, S, List.map_ofFn, Function.comp_def]
  rw [hS, (commute_S (sqrt_neg_one m) (s 0) _).eq]
  refine kill (sqrt_neg_one m) (two_ne_zero' m) (fun q ↦ OMA.Artin2.isotropic_gen ?_ q) _ (s 0)
  simp [Fintype.card_sum]

end OMA.PfK


namespace OMA.PfK

open MilnorK OMA.Artin2K

variable {F : Type*} [Field F]

lemma S_append (l₁ l₂ : List Fˣ) : S (l₁ ++ l₂) = S l₁ * S l₂ := by
  simp [S, List.map_append, List.prod_append]

/-- Values (including `0`) of `<<E>> ⊗ (pure part of <<A>>)`, by recursion on `A`. -/
def Rv (E : List Fˣ) : List Fˣ → Set F
  | [] => {0}
  | a :: L => {y | ∃ g₁ ∈ Rv E L, ∃ g₂ ∈ Qv (E ++ L), y = g₁ + a * g₂}

/-- Generalized slot lemma: a nonzero value `f` of `<<E>> ⊗ (pure part of <<A>>)` gives
`{E}{A} = {E}{f}{A'}` with `A'` one entry shorter. -/
theorem rel_slot (hi : ∃ i : F, i * i = -1) (E : List Fˣ) :
    ∀ (A : List Fˣ) (f : Fˣ), (f : F) ∈ Rv E A →
      ∃ A' : List Fˣ, A'.length + 1 = A.length ∧ S E * S A = S E * of 2 f * S A' := by
  intro A
  induction A with
  | nil =>
    intro f hf
    exact absurd (show (f : F) = 0 from hf) f.ne_zero
  | cons a L ih =>
    rintro f ⟨g₁, hg₁, g₂, hg₂, hf⟩
    by_cases hg₂0 : g₂ = 0
    · obtain ⟨L', hlen, hL'⟩ := ih f (by rw [hf, hg₂0, mul_zero, add_zero]; exact hg₁)
      refine ⟨a :: L', by simp [hlen], ?_⟩
      rw [S_cons, S_cons, (commute_S hi a L).eq, ← mul_assoc, hL', (commute_S hi a L').eq,
        mul_assoc, mul_assoc]
    set u₂ := Units.mk0 g₂ hg₂0 with hu₂
    have hnorm : S E * S L * of 2 u₂ = 0 := by
      rw [← S_append]; exact norm_Qv hi _ u₂ (by simpa [hu₂] using hg₂)
    set c := a * u₂ with hc
    have key : S E * S (a :: L) = S E * S L * of 2 c := by
      rw [S_cons, (commute_S hi a L).eq, hc, of_mul, mul_add, hnorm, add_zero, mul_assoc]
    by_cases hg₁0 : g₁ = 0
    · refine ⟨L, by simp, ?_⟩
      have hfc : f = c := by ext; simp [hf, hg₁0, hc, hu₂]
      rw [key, hfc, mul_assoc, ← (commute_S hi c L).eq, ← mul_assoc]
    set u₁ := Units.mk0 g₁ hg₁0 with hu₁
    obtain ⟨L', hlen, hL'⟩ := ih u₁ (by simpa [hu₁] using hg₁)
    have hst := steinberg2 hi u₁ c f (by simp [hu₁, hc, hu₂, hf])
    refine ⟨(u₁ * c) :: L', by simp [hlen], ?_⟩
    rw [key, hL', S_cons, mul_assoc (S E * of 2 u₁), ← (commute_S hi c L').eq, ← mul_assoc,
      mul_assoc (S E), hst, ← mul_assoc, mul_assoc (S E * of 2 f)]

/-- Values of `<<e>> ⊗ <<a>>` lie in `Qv (e ++ a)`. -/
theorem mem_Qv_two : ∀ (k : ℕ) (e : Fin k → Fˣ) (j : ℕ) (a : Fin j → Fˣ)
    (y : (Fin k → Bool) → (Fin j → Bool) → F),
    ∑ s, ∑ t, coef e s * coef a t * y s t ^ 2 ∈ Qv (List.ofFn e ++ List.ofFn a) := by
  intro k
  induction k with
  | zero =>
    intro e j a y
    have hs : ∀ s : Fin 0 → Bool, s = fun _ ↦ false := fun s ↦ funext fun i ↦ i.elim0
    rw [Fintype.sum_eq_single (fun _ ↦ false) (fun s h ↦ absurd (hs s) h)]
    simp only [coef_false, one_mul, List.ofFn_zero, List.nil_append]
    exact (mem_Qv_Pv j a _).1
  | succ k ih =>
    intro e j a y
    rw [List.ofFn_succ, List.cons_append, sum_cons]
    refine ⟨_, ih (fun i ↦ e i.succ) j a (fun s t ↦ y (Fin.cons false s) t), _,
      ih (fun i ↦ e i.succ) j a (fun s t ↦ y (Fin.cons true s) t), ?_⟩
    rw [Finset.mul_sum, add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun s _ ↦ Finset.sum_congr rfl fun t _ ↦ ?_
      rw [coef_cons]; simp
    · refine Finset.sum_congr rfl fun s _ ↦ ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ ↦ ?_
      rw [coef_cons]; simp; ring

/-- Values of `<<e>> ⊗ (pure part of <<a>>)` lie in `Rv`. -/
theorem mem_Rv : ∀ (j : ℕ) (k : ℕ) (e : Fin k → Fˣ) (a : Fin j → Fˣ)
    (y : (Fin k → Bool) → (Fin j → Bool) → F), (∀ s, y s (fun _ ↦ false) = 0) →
    ∑ s, ∑ t, coef e s * coef a t * y s t ^ 2 ∈ Rv (List.ofFn e) (List.ofFn a) := by
  intro j
  induction j with
  | zero =>
    intro k e a y hy
    have ht : ∀ t : Fin 0 → Bool, t = fun _ ↦ false := fun t ↦ funext fun i ↦ i.elim0
    show _ = (0 : F)
    refine Finset.sum_eq_zero fun s _ ↦ Finset.sum_eq_zero fun t _ ↦ ?_
    rw [ht t, hy]; ring
  | succ j ih =>
    intro k e a y hy
    rw [List.ofFn_succ]
    have hsplit : ∑ s, ∑ t, coef e s * coef a t * y s t ^ 2 =
        ∑ s, ∑ t, coef e s * coef (fun i ↦ a i.succ) t * y s (Fin.cons false t) ^ 2 +
        a 0 * ∑ s, ∑ t, coef e s * coef (fun i ↦ a i.succ) t * y s (Fin.cons true t) ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun s _ ↦ ?_
      rw [sum_cons, Finset.mul_sum, add_comm]
      congr 1
      · refine Finset.sum_congr rfl fun t _ ↦ ?_
        rw [coef_cons]; simp
      · refine Finset.sum_congr rfl fun t _ ↦ ?_
        rw [coef_cons]; simp; ring
    refine ⟨_, ih k e (fun i ↦ a i.succ) (fun s t ↦ y s (Fin.cons false t)) ?_, _,
      mem_Qv_two k e j (fun i ↦ a i.succ) (fun s t ↦ y s (Fin.cons true t)), hsplit⟩
    intro s
    have : (Fin.cons false (fun _ ↦ false) : Fin (j + 1) → Bool) = fun _ ↦ false := by
      funext i; refine Fin.cases rfl (fun _ ↦ rfl) i
    simpa [this] using hy s

/-- An isotropic diagonal form represents `1`, by a vector with the same zero pattern. -/
theorem univ_one {ι : Type*} [Fintype ι] [DecidableEq ι] (h2 : (2 : F) ≠ 0) (c : ι → F)
    (hc : ∀ i, c i ≠ 0) (Z : ι → Prop) (x : ι → F) (hxZ : ∀ i, Z i → x i = 0) (hx : x ≠ 0)
    (hsum : ∑ i, c i * x i ^ 2 = 0) :
    ∃ y : ι → F, (∀ i, Z i → y i = 0) ∧ ∑ i, c i * y i ^ 2 = 1 := by
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hx
  have hk' : x k ≠ 0 := hk
  have hkZ : ¬ Z k := fun h ↦ hk' (hxZ k h)
  have hck := hc k
  set lam := (1 - c k) / (2 * c k * x k)
  refine ⟨fun i ↦ lam * x i + if i = k then 1 else 0, ?_, ?_⟩
  · intro i hi
    have : i ≠ k := fun h ↦ hkZ (h ▸ hi)
    simp [hxZ i hi, this]
  · have : ∀ i, c i * (lam * x i + if i = k then 1 else 0) ^ 2 =
        lam ^ 2 * (c i * x i ^ 2) + (if i = k then 2 * lam * c k * x k + c k else 0) := by
      intro i
      split_ifs with h
      · subst h; ring
      · ring
    rw [Finset.sum_congr rfl fun i _ ↦ this i, Finset.sum_add_distrib, ← Finset.mul_sum, hsum,
      mul_zero, zero_add, Finset.sum_ite_eq' Finset.univ k, if_pos (Finset.mem_univ k)]
    simp only [lam]
    field_simp
    ring

end OMA.PfK

namespace OMA.PfK

open MilnorK OMA.Artin2K

variable {F : Type*} [Field F]

lemma list_eq_ofFn (L : List Fˣ) {j : ℕ} (h : L.length = j) :
    L = List.ofFn (fun i : Fin j ↦ L.get (Fin.cast h.symm i)) := by
  subst h; simp

lemma ofFn_cons' {n : ℕ} (x : Fˣ) (e : Fin n → Fˣ) :
    List.ofFn (Fin.cons x e : Fin (n + 1) → Fˣ) = x :: List.ofFn e := by
  simp [List.ofFn_succ]

lemma sum_X_eq {k j : ℕ} (w : (Fin k → Bool) → (Fin (j + 1) → Bool) → F)
    (v : (Fin k → Bool) × {t : Fin (j + 1) → Bool // t ≠ fun _ ↦ false} → F) :
    ∑ p, w p.1 p.2.1 * v p ^ 2 = ∑ s, ∑ t, w s t *
      (if h : t = (fun _ ↦ false) then 0 else v (s, ⟨t, h⟩)) ^ 2 := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [← Fintype.sum_subtype_add_sum_subtype (fun t : Fin (j + 1) → Bool ↦ t ≠ fun _ ↦ false)]
  have h0 : ∑ t : {t : Fin (j + 1) → Bool // ¬ t ≠ fun _ ↦ false},
      w s t.1 * (if h : t.1 = (fun _ ↦ false) then 0 else v (s, ⟨t.1, h⟩)) ^ 2 = 0 := by
    refine Finset.sum_eq_zero fun t _ ↦ ?_
    rw [dif_pos (not_not.mp t.2)]; ring
  rw [h0, add_zero]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [dif_neg t.2]

/-- If a relative form `<<e>> ⊗ (pure part of <<b>>)` is isotropic, then `{e}{b} = 0`. -/
theorem kill_of (hi : ∃ i : F, i * i = -1) (h2 : (2 : F) ≠ 0) {k j : ℕ} (e : Fin k → Fˣ)
    (b : Fin j → Fˣ) (y : (Fin k → Bool) → (Fin j → Bool) → F)
    (hy0 : ∀ s, y s (fun _ ↦ false) = 0) (hyne : y ≠ 0)
    (hsum : ∑ s, ∑ t, coef e s * coef b t * y s t ^ 2 = 0) :
    S (List.ofFn e) * S (List.ofFn b) = 0 := by
  have hsum' : ∑ p : (Fin k → Bool) × (Fin j → Bool),
      coef e p.1 * coef b p.2 * y p.1 p.2 ^ 2 = 0 := by
    rw [Fintype.sum_prod_type]; exact hsum
  have hne : (fun p : (Fin k → Bool) × (Fin j → Bool) ↦ y p.1 p.2) ≠ 0 := by
    intro h; apply hyne; funext s t; exact congrFun h (s, t)
  have hc : ∀ p : (Fin k → Bool) × (Fin j → Bool), coef e p.1 * coef b p.2 ≠ 0 :=
    fun p ↦ mul_ne_zero (coef_ne_zero e p.1) (coef_ne_zero b p.2)
  have hZ : ∀ p : (Fin k → Bool) × (Fin j → Bool), p.2 = (fun _ ↦ false) → y p.1 p.2 = 0 := by
    rintro ⟨s, t⟩ (rfl : t = _); exact hy0 s
  obtain ⟨z, hz0, hz⟩ := univ_one (ι := (Fin k → Bool) × (Fin j → Bool)) h2
    (fun p ↦ coef e p.1 * coef b p.2) hc (fun p ↦ p.2 = fun _ ↦ false) (fun p ↦ y p.1 p.2)
    hZ hne hsum'
  have hz' : ∑ s, ∑ t, coef e s * coef b t * z (s, t) ^ 2 = 1 := by
    rw [← hz, Fintype.sum_prod_type]
  have h1 : ((1 : Fˣ) : F) ∈ Rv (List.ofFn e) (List.ofFn b) := by
    have := mem_Rv j k e b (fun s t ↦ z (s, t)) (fun s ↦ hz0 (s, fun _ ↦ false) rfl)
    rw [hz'] at this
    rw [Units.val_one]
    exact this
  obtain ⟨_, -, h⟩ := rel_slot hi _ _ 1 h1
  rw [h, of_one, mul_zero, zero_mul]

/-- Turn an isotropic vector of the two relative pure forms into two coefficient arrays. -/
theorem split_vec {k j : ℕ} (wa wb : (Fin k → Bool) → (Fin (j + 1) → Bool) → F)
    (v : ((Fin k → Bool) × {t : Fin (j + 1) → Bool // t ≠ fun _ ↦ false}) ⊕
      ((Fin k → Bool) × {t : Fin (j + 1) → Bool // t ≠ fun _ ↦ false}) → F)
    (hv0 : v ≠ 0)
    (hv : ∑ p, wa p.1 p.2.1 * v (Sum.inl p) ^ 2 + ∑ p, wb p.1 p.2.1 * v (Sum.inr p) ^ 2 = 0) :
    ∃ yA yB : (Fin k → Bool) → (Fin (j + 1) → Bool) → F,
      (∀ s, yA s (fun _ ↦ false) = 0) ∧ (∀ s, yB s (fun _ ↦ false) = 0) ∧
      ∑ s, ∑ t, wa s t * yA s t ^ 2 + ∑ s, ∑ t, wb s t * yB s t ^ 2 = 0 ∧
      (yA ≠ 0 ∨ yB ≠ 0) := by
  refine ⟨fun s t ↦ if h : t = (fun _ ↦ false) then 0 else v (Sum.inl (s, ⟨t, h⟩)),
    fun s t ↦ if h : t = (fun _ ↦ false) then 0 else v (Sum.inr (s, ⟨t, h⟩)),
    fun s ↦ by simp, fun s ↦ by simp, ?_, ?_⟩
  · rw [← sum_X_eq wa (fun p ↦ v (Sum.inl p)), ← sum_X_eq wb (fun p ↦ v (Sum.inr p))]
    exact hv
  · by_contra h
    push Not at h
    apply hv0
    funext p
    rcases p with ⟨s, t⟩ | ⟨s, t⟩
    · have := congrFun (congrFun h.1 s) t.1
      simpa [t.2] using this
    · have := congrFun (congrFun h.2 s) t.1
      simpa [t.2] using this

lemma card_bound {k j m : ℕ} (hj : 1 ≤ j) (hk : k + (j + 1) = m) :
    2 ^ m < Fintype.card (((Fin k → Bool) × {t : Fin (j + 1) → Bool // t ≠ fun _ ↦ false}) ⊕
      ((Fin k → Bool) × {t : Fin (j + 1) → Bool // t ≠ fun _ ↦ false})) := by
  rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_subtype_compl]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Fintype.card_unique]
  rw [← hk]
  have hA : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hB : 2 ≤ 2 ^ j := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
  have e1 : 2 ^ (k + (j + 1)) = 2 ^ k * (2 * 2 ^ j) := by ring
  have e2 : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
  rw [e1, e2]
  zify [show 1 ≤ 2 * 2 ^ j by omega]
  push_cast
  nlinarith

theorem link_aux (hi : ∃ i : F, i * i = -1) (h2 : (2 : F) ≠ 0) {m : ℕ}
    (hu : ∀ (ι : Type) [Fintype ι], 2 ^ m < Fintype.card ι → ∀ q : ι → F,
      ∃ v : ι → F, v ≠ 0 ∧ ∑ i, q i * v i ^ 2 = 0) :
    ∀ j, 1 ≤ j → ∀ k, k + j = m → ∀ (e : Fin k → Fˣ) (a b : Fin j → Fˣ), ∃ c : Fin j → Fˣ,
      S (List.ofFn e) * S (List.ofFn a) + S (List.ofFn e) * S (List.ofFn b) =
        S (List.ofFn e) * S (List.ofFn c) := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
    intro k _ e a b
    refine ⟨fun _ ↦ a 0 * b 0, ?_⟩
    simp [List.ofFn_succ, S_cons, of_mul, mul_add]
  | succ j hj ih =>
    intro k hk e a b
    obtain ⟨v, hv0, hv⟩ := hu _ (card_bound hj hk)
      (Sum.elim (fun p ↦ coef e p.1 * coef a p.2.1) (fun p ↦ coef e p.1 * coef b p.2.1))
    rw [Fintype.sum_sum_type] at hv
    simp only [Sum.elim_inl, Sum.elim_inr] at hv
    obtain ⟨yA, yB, hA0, hB0, hsum, hne⟩ :=
      split_vec (fun s t ↦ coef e s * coef a t) (fun s t ↦ coef e s * coef b t) v hv0 hv
    clear hv hv0 v
    generalize hrA : ∑ s, ∑ t, coef e s * coef a t * yA s t ^ 2 = rA at hsum
    generalize hrB : ∑ s, ∑ t, coef e s * coef b t * yB s t ^ 2 = rB at hsum
    have hmemA : rA ∈ Rv (List.ofFn e) (List.ofFn a) := hrA ▸ mem_Rv (j + 1) k e a yA hA0
    by_cases hr0 : rA = 0
    · have hrB0 : rB = 0 := by linear_combination hsum - hr0
      rcases hne with hne | hne
      · refine ⟨b, ?_⟩
        rw [kill_of hi h2 e a yA hA0 hne (hrA.trans hr0), zero_add]
      · refine ⟨a, ?_⟩
        rw [kill_of hi h2 e b yB hB0 hne (hrB.trans hrB0), add_zero]
    · obtain ⟨i, hi'⟩ := hi
      have hfB : ((Units.mk0 rA hr0 : Fˣ) : F) ∈ Rv (List.ofFn e) (List.ofFn b) := by
        have := mem_Rv (j + 1) k e b (fun s t ↦ i * yB s t) (fun s ↦ by simp [hB0 s])
        have heq : ∑ s, ∑ t, coef e s * coef b t * (i * yB s t) ^ 2 = rA := by
          have : ∑ s, ∑ t, coef e s * coef b t * (i * yB s t) ^ 2 =
              (i * i) * ∑ s, ∑ t, coef e s * coef b t * yB s t ^ 2 := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun s _ ↦ ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun t _ ↦ ?_
            ring
          rw [this, hi', hrB]; linear_combination -1 * hsum
        rw [Units.val_mk0, ← heq]; exact this
      obtain ⟨A', hlenA, hA'⟩ := rel_slot ⟨i, hi'⟩ _ _ (Units.mk0 rA hr0) hmemA
      obtain ⟨B', hlenB, hB'⟩ := rel_slot ⟨i, hi'⟩ _ _ (Units.mk0 rA hr0) hfB
      simp only [List.length_ofFn] at hlenA hlenB
      generalize Units.mk0 rA hr0 = f at hA' hB'
      have hA'' := list_eq_ofFn A' (j := j) (by omega)
      have hB'' := list_eq_ofFn B' (j := j) (by omega)
      generalize (fun i : Fin j ↦ A'.get (Fin.cast (by omega) i)) = a' at hA''
      generalize (fun i : Fin j ↦ B'.get (Fin.cast (by omega) i)) = b' at hB''
      subst hA'' hB''
      obtain ⟨c', hc'⟩ := ih (k + 1) (by omega) (Fin.cons f e) a' b'
      refine ⟨Fin.cons f c', ?_⟩
      rw [ofFn_cons', S_cons] at hc'
      rw [ofFn_cons']
      have hcomm := (commute_S ⟨i, hi'⟩ f (List.ofFn e)).eq
      calc S (List.ofFn e) * S (List.ofFn a) + S (List.ofFn e) * S (List.ofFn b)
          = S (List.ofFn e) * of 2 f * S (List.ofFn a') +
            S (List.ofFn e) * of 2 f * S (List.ofFn b') := by rw [hA', hB']
        _ = of 2 f * S (List.ofFn e) * S (List.ofFn a') +
            of 2 f * S (List.ofFn e) * S (List.ofFn b') := by rw [← hcomm]
        _ = of 2 f * S (List.ofFn e) * S (List.ofFn c') := hc'
        _ = S (List.ofFn e) * S (f :: List.ofFn c') := by
            rw [S_cons, ← mul_assoc, hcomm]

/-- Linkage: over a field with `-1` a square, `2 ≠ 0` and `u ≤ 2^m`, the sum of two `m`-fold
symbols mod `2` is an `m`-fold symbol. -/
theorem link (hi : ∃ i : F, i * i = -1) (h2 : (2 : F) ≠ 0) {m : ℕ} (hm : 1 ≤ m)
    (hu : ∀ (ι : Type) [Fintype ι], 2 ^ m < Fintype.card ι → ∀ q : ι → F,
      ∃ v : ι → F, v ≠ 0 ∧ ∑ i, q i * v i ^ 2 = 0)
    (a b : Fin m → Fˣ) : ∃ c : Fin m → Fˣ,
      S (List.ofFn a) + S (List.ofFn b) = S (List.ofFn c) := by
  obtain ⟨c, hc⟩ := link_aux hi h2 hu m hm 0 (zero_add m) Fin.elim0 a b
  exact ⟨c, by simpa using hc⟩

lemma symbol_eq_S {n : ℕ} (s : Fin n → Fˣ) : symbol 2 s = S (List.ofFn s) := by
  simp [symbol, S, List.map_ofFn, Function.comp_def]

/-- Every class of `K_m/2` is a single symbol under the hypotheses of `link`. -/
theorem single_symbol (hi : ∃ i : F, i * i = -1) (h2 : (2 : F) ≠ 0) {m : ℕ} (hm : 1 ≤ m)
    (hu : ∀ (ι : Type) [Fintype ι], 2 ^ m < Fintype.card ι → ∀ q : ι → F,
      ∃ v : ι → F, v ≠ 0 ∧ ∑ i, q i * v i ^ 2 = 0) :
    1 ∈ symbolLengthBounds F 2 m := by
  have key : ∀ x ∈ grade F 2 m, ∃ s : Fin m → Fˣ, x = symbol 2 s := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem y hy => obtain ⟨s, rfl⟩ := hy; exact ⟨s, rfl⟩
    | zero =>
      refine ⟨fun _ ↦ 1, ?_⟩
      obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_le' hm
      rw [symbol_succ, of_one, zero_mul]
    | add y z _ _ hy hz =>
      obtain ⟨s, rfl⟩ := hy
      obtain ⟨t, rfl⟩ := hz
      obtain ⟨c, hc⟩ := link hi h2 hm hu s t
      exact ⟨c, by rw [symbol_eq_S, symbol_eq_S, symbol_eq_S, hc]⟩
    | neg y _ hy =>
      obtain ⟨s, rfl⟩ := hy
      exact ⟨s, OMA.Artin2K.neg_eq_self _⟩
  intro x hx
  obtain ⟨s, rfl⟩ := key x hx
  exact ⟨1, le_rfl, fun _ ↦ s, by simp⟩

/-- Upper bound on the diagonal: every class of `K_m(C(x_1, ..., x_m))/2` is one symbol. -/
theorem diag_upper (m : ℕ) (hm : 1 ≤ m) :
    1 ∈ symbolLengthBounds (MvRatFunc (Fin m) ℂ) 2 m :=
  single_symbol (sqrt_neg_one m) (two_ne_zero' m) hm
    (fun ι _ hι q ↦ OMA.Artin2.isotropic_gen hι q)

end OMA.PfK


namespace OMA.Low

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

end OMA.Low

namespace OMA.Low

open MilnorK MvPolynomial

variable {m : ℕ}

/-- Coordinates of the lex-leading exponent, extended to units of `C(x_1, ..., x_m)`. -/
theorem exists_L (i : Fin m) : ∃ L : Additive (MvRatFunc (Fin m) ℂ)ˣ →+ ℤ,
    ∀ (u : (MvRatFunc (Fin m) ℂ)ˣ) (n d : MvPolynomial (Fin m) ℂ), d ≠ 0 →
      (u : MvRatFunc (Fin m) ℂ) * algebraMap _ _ d = algebraMap _ _ n →
      L (Additive.ofMul u) =
        ((MonomialOrder.lex.degree n i : ℕ) : ℤ) - ((MonomialOrder.lex.degree d i : ℕ) : ℤ) :=
  exists_hom (fun f ↦ ((MonomialOrder.lex.degree f i : ℕ) : ℤ))
    (fun f g hf hg ↦ by rw [MonomialOrder.degree_mul hf hg]; simp)

/-- The ultrametric trichotomy for `a + b = 1`. -/
theorem trichotomy (L : Fin m → Additive (MvRatFunc (Fin m) ℂ)ˣ →+ ℤ)
    (hL : ∀ i (u : (MvRatFunc (Fin m) ℂ)ˣ) (n d : MvPolynomial (Fin m) ℂ), d ≠ 0 →
      (u : MvRatFunc (Fin m) ℂ) * algebraMap _ _ d = algebraMap _ _ n →
      L i (Additive.ofMul u) =
        ((MonomialOrder.lex.degree n i : ℕ) : ℤ) - ((MonomialOrder.lex.degree d i : ℕ) : ℤ))
    (a b : (MvRatFunc (Fin m) ℂ)ˣ) (hab : (a : MvRatFunc (Fin m) ℂ) + b = 1) :
    (∀ i, L i (Additive.ofMul a) = L i (Additive.ofMul b)) ∨ (∀ i, L i (Additive.ofMul a) = 0) ∨
      (∀ i, L i (Additive.ofMul b) = 0) := by
  have hinj : Function.Injective (algebraMap (MvPolynomial (Fin m) ℂ) (MvRatFunc (Fin m) ℂ)) :=
    IsFractionRing.injective _ _
  obtain ⟨n₁, d₁, hd₁, h₁⟩ := IsFractionRing.div_surjective (MvPolynomial (Fin m) ℂ)
    (a : MvRatFunc (Fin m) ℂ)
  obtain ⟨n₂, d₂, hd₂, h₂⟩ := IsFractionRing.div_surjective (MvPolynomial (Fin m) ℂ)
    (b : MvRatFunc (Fin m) ℂ)
  have hd₁0 : d₁ ≠ 0 := nonZeroDivisors.ne_zero hd₁
  have hd₂0 : d₂ ≠ 0 := nonZeroDivisors.ne_zero hd₂
  have hm₁ : algebraMap _ (MvRatFunc (Fin m) ℂ) d₁ ≠ 0 := (map_ne_zero_iff _ hinj).mpr hd₁0
  have hm₂ : algebraMap _ (MvRatFunc (Fin m) ℂ) d₂ ≠ 0 := (map_ne_zero_iff _ hinj).mpr hd₂0
  set D := d₁ * d₂
  have hD : D ≠ 0 := mul_ne_zero hd₁0 hd₂0
  have ha : (a : MvRatFunc (Fin m) ℂ) * algebraMap _ _ D = algebraMap _ _ (n₁ * d₂) := by
    rw [← h₁]; simp only [D, map_mul]; field_simp
  have hb : (b : MvRatFunc (Fin m) ℂ) * algebraMap _ _ D = algebraMap _ _ (n₂ * d₁) := by
    rw [← h₂]; simp only [D, map_mul]; field_simp
  have hsum : n₁ * d₂ + n₂ * d₁ = D := by
    apply hinj
    rw [map_add, ← ha, ← hb, ← add_mul, hab, one_mul]
  have hLa := fun i ↦ hL i a _ _ hD ha
  have hLb := fun i ↦ hL i b _ _ hD hb
  rcases lt_trichotomy (MonomialOrder.lex.toSyn (MonomialOrder.lex.degree (n₁ * d₂)))
    (MonomialOrder.lex.toSyn (MonomialOrder.lex.degree (n₂ * d₁))) with h | h | h
  · right; right
    intro i
    have : MonomialOrder.lex.degree D = MonomialOrder.lex.degree (n₂ * d₁) := by
      rw [← hsum, add_comm]; exact MonomialOrder.degree_add_of_lt h
    rw [hLb i, this, sub_self]
  · left
    intro i
    have : MonomialOrder.lex.degree (n₁ * d₂) = MonomialOrder.lex.degree (n₂ * d₁) :=
      MonomialOrder.lex.toSyn.injective h
    rw [hLa i, hLb i, this]
  · right; left
    intro i
    have : MonomialOrder.lex.degree D = MonomialOrder.lex.degree (n₁ * d₂) := by
      rw [← hsum]; exact MonomialOrder.degree_add_of_lt h
    rw [hLa i, this, sub_self]



/-- The target: `(Z/2)[ε_1, ..., ε_m]` with `ε_i ^ 2 = 0`. -/
abbrev Eps (m : ℕ) := MvPolynomial (Fin m) (ZMod 2) ⧸
  Ideal.span (Set.range fun i : Fin m ↦ (X i : MvPolynomial (Fin m) (ZMod 2)) ^ 2)

noncomputable def eps (i : Fin m) : Eps m := Ideal.Quotient.mk _ (X i)

lemma eps_sq (i : Fin m) : eps i * eps i = 0 := by
  rw [eps, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, ← sq]
  exact Ideal.subset_span ⟨i, rfl⟩

lemma two_eq_zero : (2 : Eps m) = 0 := by
  have : (2 : Eps m) = algebraMap (ZMod 2) (Eps m) 2 := (map_ofNat _ 2).symm
  rw [this, show (2 : ZMod 2) = 0 from rfl, map_zero]

lemma sq_sum_eps (c : Fin m → Eps m) : (∑ i, c i * eps i) * (∑ i, c i * eps i) = 0 := by
  have key : ∀ s : Finset (Fin m), (∑ i ∈ s, c i * eps i) * (∑ i ∈ s, c i * eps i) = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
      rw [Finset.sum_insert hj]
      have h2 : ∀ x : Eps m, x + x = 0 := fun x ↦ by rw [← two_mul, two_eq_zero, zero_mul]
      calc (c j * eps j + ∑ i ∈ s, c i * eps i) * (c j * eps j + ∑ i ∈ s, c i * eps i)
          = c j * c j * (eps j * eps j) +
            ((c j * eps j) * (∑ i ∈ s, c i * eps i) + (c j * eps j) * (∑ i ∈ s, c i * eps i)) +
            (∑ i ∈ s, c i * eps i) * (∑ i ∈ s, c i * eps i) := by ring
        _ = 0 := by rw [eps_sq, ih, h2]; ring
  exact key Finset.univ

/-- The ring map `K_*(C(x_1, ..., x_m))/2 → (Z/2)[ε]/(ε_i^2)`, `{u} ↦ ∑ L_i(u) ε_i`. -/
theorem exists_psi : ∃ Ψ : MilnorK (MvRatFunc (Fin m) ℂ) 2 →+* Eps m,
    ∀ i : Fin m, Ψ (of 2 (Units.mk0 (algebraMap (MvPolynomial (Fin m) ℂ) _ (X i))
      ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (X_ne_zero i)))) = eps i := by
  choose L hL using fun i : Fin m ↦ exists_L (m := m) i
  let φ : Additive (MvRatFunc (Fin m) ℂ)ˣ →+ Eps m :=
    ∑ i, (AddMonoidHom.mulRight (eps i)).comp ((Int.castAddHom (Eps m)).comp (L i))
  have hφ : ∀ u, φ u = ∑ i, ((L i u : ℤ) : Eps m) * eps i := by
    intro u; simp [φ]
  have hsq : ∀ u, φ u * φ u = 0 := fun u ↦ by rw [hφ]; exact sq_sum_eps _
  let T := (TensorAlgebra.lift ℤ φ.toIntLinearMap).toRingHom
  have hT : ∀ u, T (TensorAlgebra.ι ℤ u) = φ u := by
    intro u; simp [T]
  refine ⟨RingQuot.lift ⟨T, ?_⟩, ?_⟩
  · intro x y h
    cases h with
    | steinberg a b hab =>
      rw [map_mul, hT, hT, map_zero]
      rcases trichotomy L hL a b hab with h | h | h
      · have : φ (Additive.ofMul b) = φ (Additive.ofMul a) := by
          rw [hφ, hφ]; simp [h]
        rw [this, hsq]
      · have : φ (Additive.ofMul a) = 0 := by rw [hφ]; simp [h]
        rw [this, zero_mul]
      · have : φ (Additive.ofMul b) = 0 := by rw [hφ]; simp [h]
        rw [this, mul_zero]
    | natCast =>
      rw [map_natCast, map_zero]
      exact_mod_cast two_eq_zero
  · intro i
    rw [of, RingQuot.lift_mkRingHom_apply]
    show T _ = _
    rw [hT, hφ]
    have hLi : ∀ j, L j (Additive.ofMul (Units.mk0 (algebraMap (MvPolynomial (Fin m) ℂ) _ (X i))
        ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (X_ne_zero i)))) =
        if j = i then 1 else 0 := by
      intro j
      rw [hL j _ (X i) 1 one_ne_zero (by simp), MonomialOrder.degree_X,
        MonomialOrder.degree_one]
      by_cases hji : j = i
      · subst hji; simp
      · simp [hji, Finsupp.single_apply, Ne.symm hji]
    simp [hLi]

/-- `{x_1, ..., x_n} ≠ 0` in `K_n(C(x_1, ..., x_m))/2` for `n ≤ m`, so `0` is not a bound. -/
theorem zero_not_mem (n : ℕ) (hn : n ≤ m) (hn0 : 0 < n) :
    0 ∉ symbolLengthBounds (MvRatFunc (Fin m) ℂ) 2 n := by
  rw [zero_mem_symbolLengthBounds_iff]
  intro hbot
  obtain ⟨Ψ, hΨ⟩ := exists_psi (m := m)
  let s : Fin n → (MvRatFunc (Fin m) ℂ)ˣ := fun i ↦
    Units.mk0 (algebraMap (MvPolynomial (Fin m) ℂ) _ (X (Fin.castLE hn i)))
      ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (X_ne_zero _))
  have hs := symbol_mem_grade (MvRatFunc (Fin m) ℂ) 2 s
  rw [hbot, AddSubgroup.mem_bot] at hs
  have himg : Ψ (symbol 2 s) = Ideal.Quotient.mk _ (∏ i : Fin n, X (Fin.castLE hn i)) := by
    rw [symbol, map_list_prod, List.map_ofFn, map_prod]
    simp only [Function.comp_def, s, hΨ, eps]
    rw [List.prod_ofFn]
  rw [hs, map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem] at himg
  have hmono : (∏ i : Fin n, (X (Fin.castLE hn i) : MvPolynomial (Fin m) (ZMod 2))) =
      monomial (∑ i : Fin n, Finsupp.single (Fin.castLE hn i) 1) 1 := by
    rw [MvPolynomial.monomial_sum_one]
    rfl
  have hspan : (Set.range fun i : Fin m ↦ (X i : MvPolynomial (Fin m) (ZMod 2)) ^ 2) =
      (fun s ↦ monomial s (1 : ZMod 2)) '' Set.range (fun i : Fin m ↦ Finsupp.single i 2) := by
    ext p; simp [X_pow_eq_monomial]
  rw [hmono, hspan, mem_ideal_span_monomial_image] at himg
  obtain ⟨si, ⟨j, rfl⟩, hle⟩ := himg _ (by
    rw [support_monomial, if_neg one_ne_zero]; exact Finset.mem_singleton_self _)
  have h2 := hle j
  simp only [Finsupp.single_eq_same, Finsupp.coe_finsetSum, Finset.sum_apply] at h2
  have hle1 : ∑ i : Fin n, (Finsupp.single (Fin.castLE hn i) 1 : Fin m →₀ ℕ) j ≤ 1 := by
    by_cases hex : ∃ i0 : Fin n, Fin.castLE hn i0 = j
    · obtain ⟨i0, hi0⟩ := hex
      rw [Finset.sum_eq_single i0]
      · simp [hi0]
      · intro i _ hne
        rw [Finsupp.single_apply, if_neg]
        intro h
        exact hne (Fin.castLE_injective hn (h.trans hi0.symm))
      · simp
    · push Not at hex
      rw [Finset.sum_eq_zero]
      · norm_num
      · intro i _
        rw [Finsupp.single_apply, if_neg (hex i)]
  omega

end OMA.Low

namespace OMA.Low

open MilnorK

/-- If `K_n/ℓ = 0` then `K_{n+1}/ℓ = 0`. -/
theorem grade_succ_eq_bot {F : Type*} [Field F] (ℓ n : ℕ) (h : grade F ℓ n = ⊥) :
    grade F ℓ (n + 1) = ⊥ := by
  rw [eq_bot_iff, MilnorK.grade, AddSubgroup.closure_le]
  rintro _ ⟨s, rfl⟩
  have hs := symbol_mem_grade F ℓ (fun i ↦ s i.succ)
  rw [h, AddSubgroup.mem_bot] at hs
  rw [SetLike.mem_coe, AddSubgroup.mem_bot, symbol_succ, hs, mul_zero]

theorem grade_eq_bot_of_le {F : Type*} [Field F] (ℓ k : ℕ) (h : grade F ℓ k = ⊥) :
    ∀ n, k ≤ n → grade F ℓ n = ⊥ := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact grade_succ_eq_bot ℓ n ih

/-- The diagonal entry: the symbol length of `K_m(C(x_1, ..., x_m))/2` is exactly `1`. -/
theorem diag_exact (m : ℕ) (hm : 1 ≤ m) :
    IsLeast (symbolLengthBounds (MvRatFunc (Fin m) ℂ) 2 m) 1 :=
  ⟨OMA.PfK.diag_upper m hm, fun k hk ↦ Nat.one_le_iff_ne_zero.mpr fun h0 ↦
    zero_not_mem m le_rfl hm (h0 ▸ hk)⟩

/-- Every entry of the answer table at `p = 2` with `n ≤ 1` or `n ≥ m`. -/
theorem p2_rows (m n : ℕ) (h : n ≤ 1 ∨ m ≤ n) (k : ℕ) :
    k ∈ symbolLengthBounds (MvRatFunc (Fin m) ℂ) 2 n ↔
      (if n = 0 then 1 else if m < n then 0 else 1) ≤ k := by
  have key : IsLeast (symbolLengthBounds (MvRatFunc (Fin m) ℂ) 2 n)
      (if n = 0 then 1 else if m < n then 0 else 1) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa using isLeast_symbolLengthBounds_zero (MvRatFunc (Fin m) ℂ) 2 two_pos
    rw [if_neg hn.ne']
    by_cases hmn : m < n
    · rw [if_pos hmn]
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hmn
      refine ⟨?_, fun _ _ ↦ Nat.zero_le _⟩
      rw [zero_mem_symbolLengthBounds_iff]
      exact grade_eq_bot_of_le 2 (m + 1) (OMA.PfK.grade_succ_bot m) _ (by omega)
    · rw [if_neg hmn]
      rcases h with h | h
      · obtain rfl : n = 1 := by omega
        exact ⟨one_mem_symbolLengthBounds_one _ 2, fun k hk ↦ Nat.one_le_iff_ne_zero.mpr
          fun h0 ↦ zero_not_mem 1 (by omega) one_pos (h0 ▸ hk)⟩
      · obtain rfl : n = m := by omega
        exact diag_exact n hn
  exact ⟨fun hk ↦ key.2 hk, fun hk ↦ mem_symbolLengthBounds_of_le _ 2 key.1 hk⟩

end OMA.Low

