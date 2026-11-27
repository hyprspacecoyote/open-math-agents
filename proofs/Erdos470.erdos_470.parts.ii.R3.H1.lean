import OMAReductions.R_Erdos470_erdos_470_parts_ii_R3

/-! # Step H1 of Erdos470.erdos_470.parts.ii.R3

With `M = 2^(k+1)` and distinct primes `p, q > M`, the number `n = 2^k p q` is primitive weird as
soon as it is abundant and its excess `e = sigma(n) - 2n` avoids every block `[b p + c q, b p + c q + M)`
with `b, c < M`. A complement of a subset of proper divisors summing to `n` would sum to `e < p q`,
hence would have the shape `a + b p + c q` with `a, b, c` sums of distinct divisors of `2^k`, so
`a, b, c < M`. Every proper divisor of `n` is deficient because `p, q > M`.
Lemmas adapted from proofs/Erdos470.erdos_470.variants.prime_gap_imp_inf_prim_weird.lean. -/

namespace OMA.R3H1

open Finset

-- The divisors of 2^k sum to 2^(k+1) - 1.
lemma sum_divisors_two_pow (k : ℕ) : ∑ d ∈ (2 ^ k).divisors, d + 1 = 2 ^ (k + 1) := by
  rw [Nat.sum_divisors_prime_pow Nat.prime_two]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, pow_succ 2 (k + 1)]
    omega

lemma coprime_two_pow_of_prime {k r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) : Nat.Coprime (2 ^ k) r :=
  Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hr).mpr (Ne.symm hr2))

-- sigma(2^k * r) for an odd prime r.
lemma sum_divisors_two_pow_mul_prime (k r : ℕ) (hr : r.Prime) (hr2 : r ≠ 2) :
    ∑ d ∈ (2 ^ k * r).divisors, d + (r + 1) = 2 ^ (k + 1) * (r + 1) := by
  rw [Nat.Coprime.sum_divisors_mul (coprime_two_pow_of_prime hr hr2), Nat.Prime.sum_divisors hr]
  have h := sum_divisors_two_pow k
  rw [← h]
  ring

-- sigma(2^k * p * q) for distinct odd primes p, q.
lemma sum_divisors_two_pow_mul_mul (k p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2)
    (hq2 : q ≠ 2) (hpq : p ≠ q) :
    ∑ d ∈ (2 ^ k * p * q).divisors, d + (p + 1) * (q + 1) = 2 ^ (k + 1) * ((p + 1) * (q + 1)) := by
  have hcop1 : Nat.Coprime (2 ^ k) (p * q) :=
    Nat.Coprime.mul_right (coprime_two_pow_of_prime hp hp2) (coprime_two_pow_of_prime hq hq2)
  have hcop2 : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  rw [mul_assoc, Nat.Coprime.sum_divisors_mul hcop1, Nat.Coprime.sum_divisors_mul hcop2,
    Nat.Prime.sum_divisors hp, Nat.Prime.sum_divisors hq]
  have h := sum_divisors_two_pow k
  rw [← h]
  ring

-- 2^k * r is not abundant when r is an odd prime with 2^(k+1) <= r + 1.
lemma not_abundant_two_pow_mul_prime (k r : ℕ) (hr : r.Prime) (hr2 : r ≠ 2)
    (hbig : 2 ^ (k + 1) ≤ r + 1) : ¬ (2 ^ k * r).Abundant := by
  rw [Nat.abundant_iff_sum_divisors, not_lt]
  have h := sum_divisors_two_pow_mul_prime k r hr hr2
  have h2 : 2 * (2 ^ k * r) = 2 ^ (k + 1) * r := by ring
  rw [h2]
  nlinarith

-- 2^j * p * q is not abundant when p, q are distinct odd primes, both at least 2^(j+2).
lemma not_abundant_two_pow_mul_mul (j p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2)
    (hq2 : q ≠ 2) (hpq : p ≠ q) (hpbig : 2 ^ (j + 2) ≤ p) (hqbig : 2 ^ (j + 2) ≤ q) :
    ¬ (2 ^ j * p * q).Abundant := by
  rw [Nat.abundant_iff_sum_divisors, not_lt]
  have h := sum_divisors_two_pow_mul_mul j p q hp hq hp2 hq2 hpq
  set m := 2 ^ (j + 1) with hm
  have h2 : 2 * (2 ^ j * p * q) = m * (p * q) := by rw [hm]; ring
  have h4 : 2 ^ (j + 2) = 2 * m := by rw [hm]; ring
  rw [h2]
  obtain ⟨u, rfl⟩ : ∃ u, p = 2 * m + u := ⟨p - 2 * m, by omega⟩
  obtain ⟨v, rfl⟩ : ∃ v, q = 2 * m + v := ⟨q - 2 * m, by omega⟩
  nlinarith [Nat.zero_le (u * v), Nat.zero_le (m * u), Nat.zero_le (m * v), Nat.zero_le m]

-- A proper divisor of 2^k * p * q divides one of the three maximal proper divisors.
lemma dvd_cases (k p q d : ℕ) (hk : 1 ≤ k) (hp : p.Prime) (hq : q.Prime)
    (hd : d ∈ (2 ^ k * p * q).properDivisors) :
    d ∣ 2 ^ (k - 1) * p * q ∨ d ∣ 2 ^ k * q ∨ d ∣ 2 ^ k * p := by
  rw [Nat.mem_properDivisors] at hd
  obtain ⟨⟨e, he⟩, hlt⟩ := hd
  have he1 : e ≠ 1 := by
    rintro rfl
    rw [mul_one] at he
    omega
  have hen : e ∣ 2 ^ k * p * q := ⟨d, by rw [he]; ring⟩
  have hr := Nat.minFac_prime he1
  have hrn : e.minFac ∣ 2 ^ k * p * q := (Nat.minFac_dvd e).trans hen
  have hre := Nat.minFac_dvd e
  generalize e.minFac = r at hr hrn hre
  obtain ⟨e', rfl⟩ := hre
  rcases (Nat.Prime.dvd_mul hr).mp hrn with h | h
  · rcases (Nat.Prime.dvd_mul hr).mp h with h | h
    · have h2 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h)
      left
      refine ⟨e', ?_⟩
      have hk' : 2 ^ k = 2 * 2 ^ (k - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [h2, hk'] at he
      have : 2 * (2 ^ (k - 1) * p * q) = 2 * (d * e') := by rw [← mul_assoc, ← mul_assoc, he]; ring
      omega
    · have h2 := (Nat.prime_dvd_prime_iff_eq hr hp).mp h
      right; left
      refine ⟨e', ?_⟩
      rw [h2] at he
      have : p * (2 ^ k * q) = p * (d * e') := by linarith [he]
      exact Nat.eq_of_mul_eq_mul_left hp.pos this
  · have h2 := (Nat.prime_dvd_prime_iff_eq hr hq).mp h
    right; right
    refine ⟨e', ?_⟩
    rw [h2] at he
    have : q * (2 ^ k * p) = q * (d * e') := by linarith [he]
    exact Nat.eq_of_mul_eq_mul_left hq.pos this

-- A sum of d / r over a set of multiples d of r whose quotients divide 2^k is at most 2^(k+1) - 1.
lemma sum_div_le (k r : ℕ) (u : Finset ℕ) (hu : ∀ d ∈ u, r ∣ d ∧ d / r ∣ 2 ^ k) :
    ∑ d ∈ u, d / r + 1 ≤ 2 ^ (k + 1) := by
  have hinj : Set.InjOn (fun d => d / r) (u : Set ℕ) := by
    intro x hx y hy hxy
    have h1 := (hu x hx).1
    have h2 := (hu y hy).1
    simp only at hxy
    rw [← Nat.div_mul_cancel h1, ← Nat.div_mul_cancel h2, hxy]
  have e := Finset.sum_image (f := fun x : ℕ => x) (g := fun d => d / r) hinj
  simp only at e
  rw [← e]
  have hsub : u.image (fun d => d / r) ⊆ (2 ^ k).divisors := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨d, hd, rfl⟩ := hx
    exact Nat.mem_divisors.mpr ⟨(hu d hd).2, by positivity⟩
  calc ∑ x ∈ u.image (fun d => d / r), x + 1 ≤ ∑ d ∈ (2 ^ k).divisors, d + 1 :=
        Nat.add_le_add_right (Finset.sum_le_sum_of_subset hsub) 1
    _ = 2 ^ (k + 1) := sum_divisors_two_pow k

-- A set of divisors of 2^k * p * q with sum below p * q sums to A0 + p * B + q * C, where each of
-- A0, B, C is a sum of distinct divisors of 2^k, hence at most 2^(k+1) - 1.
lemma decomp (k p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (t : Finset ℕ)
    (ht : t ⊆ (2 ^ k * p * q).divisors) (hsmall : ∑ d ∈ t, d < p * q) :
    ∃ A0 B C : ℕ, ∑ d ∈ t, d = A0 + p * B + q * C ∧ A0 + 1 ≤ 2 ^ (k + 1) ∧
      B + 1 ≤ 2 ^ (k + 1) ∧ C + 1 ≤ 2 ^ (k + 1) := by
  have hno : ∀ d ∈ t, p ∣ d → ¬ q ∣ d := by
    intro d hdt h1 h2
    have hpqd : p * q ∣ d :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.coprime_primes hp hq).mpr hpq) h1 h2
    have hd0 : 0 < d := Nat.pos_of_mem_divisors (ht hdt)
    have h3 : p * q ≤ d := Nat.le_of_dvd hd0 hpqd
    have h4 : d ≤ ∑ d ∈ t, d :=
      Finset.single_le_sum (f := fun x => x) (fun _ _ => Nat.zero_le _) hdt
    omega
  have e1 : ∑ d ∈ t.filter (fun d => p ∣ d), d = p * ∑ d ∈ t.filter (fun d => p ∣ d), d / p := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mem_filter] at hd
    exact (Nat.mul_div_cancel' hd.2).symm
  have e2 : ∑ d ∈ (t.filter (fun d => ¬ p ∣ d)).filter (fun d => q ∣ d), d =
      q * ∑ d ∈ (t.filter (fun d => ¬ p ∣ d)).filter (fun d => q ∣ d), d / q := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mem_filter] at hd
    exact (Nat.mul_div_cancel' hd.2).symm
  have hsub : (t.filter (fun d => ¬ p ∣ d)).filter (fun d => ¬ q ∣ d) ⊆ (2 ^ k).divisors := by
    intro d hd
    simp only [Finset.mem_filter] at hd
    obtain ⟨⟨hdt, hnp⟩, hnq⟩ := hd
    have hdn := Nat.dvd_of_mem_divisors (ht hdt)
    have hcp : Nat.Coprime d p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnp).symm
    have hcq : Nat.Coprime d q := ((Nat.Prime.coprime_iff_not_dvd hq).mpr hnq).symm
    have h1 : d ∣ 2 ^ k * p := Nat.Coprime.dvd_of_dvd_mul_right hcq hdn
    have h2 : d ∣ 2 ^ k := Nat.Coprime.dvd_of_dvd_mul_right hcp h1
    exact Nat.mem_divisors.mpr ⟨h2, by positivity⟩
  have hB : ∀ d ∈ t.filter (fun d => p ∣ d), p ∣ d ∧ d / p ∣ 2 ^ k := by
    intro d hd
    rw [Finset.mem_filter] at hd
    obtain ⟨hdt, hpd⟩ := hd
    refine ⟨hpd, ?_⟩
    have hdn := Nat.dvd_of_mem_divisors (ht hdt)
    obtain ⟨e, rfl⟩ := hpd
    rw [Nat.mul_div_cancel_left e hp.pos]
    have h1 : p * e ∣ p * (2 ^ k * q) := by
      have : 2 ^ k * p * q = p * (2 ^ k * q) := by ring
      rw [← this]; exact hdn
    have h2 : e ∣ 2 ^ k * q := Nat.dvd_of_mul_dvd_mul_left hp.pos h1
    have hnq : ¬ q ∣ e := fun h => hno _ hdt (dvd_mul_right p e) (h.trans (dvd_mul_left e p))
    have hcq : Nat.Coprime e q := ((Nat.Prime.coprime_iff_not_dvd hq).mpr hnq).symm
    exact Nat.Coprime.dvd_of_dvd_mul_right hcq h2
  have hC : ∀ d ∈ (t.filter (fun d => ¬ p ∣ d)).filter (fun d => q ∣ d),
      q ∣ d ∧ d / q ∣ 2 ^ k := by
    intro d hd
    simp only [Finset.mem_filter] at hd
    obtain ⟨⟨hdt, hnp⟩, hqd⟩ := hd
    refine ⟨hqd, ?_⟩
    have hdn := Nat.dvd_of_mem_divisors (ht hdt)
    obtain ⟨e, rfl⟩ := hqd
    rw [Nat.mul_div_cancel_left e hq.pos]
    have h1 : q * e ∣ q * (2 ^ k * p) := by
      have : 2 ^ k * p * q = q * (2 ^ k * p) := by ring
      rw [← this]; exact hdn
    have h2 : e ∣ 2 ^ k * p := Nat.dvd_of_mul_dvd_mul_left hq.pos h1
    have hnp' : ¬ p ∣ e := fun h => hnp (h.trans (dvd_mul_left e q))
    have hcp : Nat.Coprime e p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnp').symm
    exact Nat.Coprime.dvd_of_dvd_mul_right hcp h2
  refine ⟨∑ d ∈ (t.filter (fun d => ¬ p ∣ d)).filter (fun d => ¬ q ∣ d), d,
    ∑ d ∈ t.filter (fun d => p ∣ d), d / p,
    ∑ d ∈ (t.filter (fun d => ¬ p ∣ d)).filter (fun d => q ∣ d), d / q, ?_, ?_,
    sum_div_le k p _ hB, sum_div_le k q _ hC⟩
  · rw [← Finset.sum_filter_add_sum_filter_not t (fun d => p ∣ d),
      ← Finset.sum_filter_add_sum_filter_not (t.filter (fun d => ¬ p ∣ d)) (fun d => q ∣ d),
      e1, e2]
    ring
  · calc ∑ d ∈ (t.filter (fun d => ¬ p ∣ d)).filter (fun d => ¬ q ∣ d), d + 1
        ≤ ∑ d ∈ (2 ^ k).divisors, d + 1 :=
          Nat.add_le_add_right (Finset.sum_le_sum_of_subset hsub) 1
      _ = 2 ^ (k + 1) := sum_divisors_two_pow k

/-- Step H1 of the reduction Erdos470.erdos_470.parts.ii.R3: with M = 2^(k+1), distinct primes
p, q above M, abundance of n = 2^k * p * q, and the abundance e = sigma(n) - 2n not lying in any
window [b * p + c * q, b * p + c * q + M) with b, c < M, the number n is primitive weird. -/
theorem main : ∀ k p q : ℕ, p.Prime → q.Prime → 2 ^ (k + 1) < p → 2 ^ (k + 1) < q → p ≠ q →
    2 ^ (k + 1) * p * q < (2 ^ (k + 1) - 1) * (p + 1) * (q + 1) →
    (∀ b c : ℕ, b < 2 ^ (k + 1) → c < 2 ^ (k + 1) →
      ¬ (b * p + c * q ≤ (2 ^ (k + 1) - 1) * (p + 1) * (q + 1) - 2 ^ (k + 1) * p * q ∧
        (2 ^ (k + 1) - 1) * (p + 1) * (q + 1) - 2 ^ (k + 1) * p * q < b * p + c * q + 2 ^ (k + 1))) →
    Erdos470.PrimitiveWeird (2 ^ k * p * q) := by
  intro k p q hp hq hpM hqM hpq habund hrep
  have hσ0 := sum_divisors_two_pow_mul_mul k p q hp hq
  set M := 2 ^ (k + 1) with hM
  have hM2 : 2 ≤ M := by rw [hM]; exact Nat.le_self_pow (by omega) 2
  obtain ⟨m, hm⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
  have hm1 : M - 1 = m := by omega
  rw [hm1] at habund hrep
  have hp2 : p ≠ 2 := by omega
  have hq2 : q ≠ 2 := by omega
  have hσ := hσ0 hp2 hq2 hpq
  have hσ' : ∑ d ∈ (2 ^ k * p * q).divisors, d = m * (p + 1) * (q + 1) := by
    rw [hm] at hσ
    nlinarith
  have h2n : 2 * (2 ^ k * p * q) = M * p * q := by rw [hM]; ring
  set E := m * (p + 1) * (q + 1) - M * p * q with hE
  have hEeq : E + M * p * q = m * (p + 1) * (q + 1) := Nat.sub_add_cancel (le_of_lt habund)
  have hk : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exfalso
      subst h0
      have hM2' : M = 2 := by rw [hM]; norm_num
      have hm' : m = 1 := by omega
      rw [hm', hM2'] at habund
      obtain ⟨u, rfl⟩ : ∃ u, p = 3 + u := ⟨p - 3, by omega⟩
      obtain ⟨v, rfl⟩ : ∃ v, q = 3 + v := ⟨q - 3, by omega⟩
      nlinarith [Nat.zero_le (u * v)]
    · exact h0
  have hn0 : 2 ^ k * p * q ≠ 0 :=
    Nat.mul_ne_zero (Nat.mul_ne_zero (by positivity) hp.ne_zero) hq.ne_zero
  have hEsmall : E < p * q := by
    obtain ⟨u, hu⟩ : ∃ u, p = m + 2 + u := ⟨p - (m + 2), by omega⟩
    obtain ⟨v, hv⟩ : ∃ v, q = m + 2 + v := ⟨q - (m + 2), by omega⟩
    rw [hm] at hEeq
    subst hu hv
    nlinarith [Nat.zero_le (u * v), Nat.zero_le (m * u), Nat.zero_le (m * v)]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- abundant
    rw [Nat.abundant_iff_sum_divisors, h2n, hσ']
    exact habund
  · -- not pseudoperfect
    rintro ⟨-, s, hs, hsum⟩
    have hsd := Finset.sum_sdiff hs (f := fun x => x)
    have hpd := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := 2 ^ k * p * q)
    set T := ∑ x ∈ (2 ^ k * p * q).properDivisors \ s, x with hT
    have hTeq : T = E := by linarith
    have htsub : (2 ^ k * p * q).properDivisors \ s ⊆ (2 ^ k * p * q).divisors :=
      (Finset.sdiff_subset).trans (Nat.properDivisors_subset_divisors)
    obtain ⟨A0, B, C, hABC, hA0, hB, hC⟩ :=
      decomp k p q hp hq hpq _ htsub (by rw [← hT, hTeq]; exact hEsmall)
    rw [← hM] at hA0 hB hC
    apply hrep B C (by omega) (by omega)
    constructor
    · linarith
    · linarith
  · -- primitive: every proper divisor is non-abundant
    intro d hd hw
    have hab := hw.1
    rcases dvd_cases k p q d hk hp hq hd with h | h | h
    · have hk' : k - 1 + 2 = k + 1 := by omega
      have hnot := not_abundant_two_pow_mul_mul (k - 1) p q hp hq hp2 hq2 hpq
        (by rw [hk', ← hM]; omega) (by rw [hk', ← hM]; omega)
      exact hnot (Nat.Abundant.of_dvd hab h
        (Nat.mul_ne_zero (Nat.mul_ne_zero (by positivity) hp.ne_zero) hq.ne_zero))
    · have hnot := not_abundant_two_pow_mul_prime k q hq hq2 (by rw [← hM]; omega)
      exact hnot (Nat.Abundant.of_dvd hab h (Nat.mul_ne_zero (by positivity) hq.ne_zero))
    · have hnot := not_abundant_two_pow_mul_prime k p hp hp2 (by rw [← hM]; omega)
      exact hnot (Nat.Abundant.of_dvd hab h (Nat.mul_ne_zero (by positivity) hp.ne_zero))

end OMA.R3H1

theorem R3H1 : ∀ k p q : ℕ, p.Prime → q.Prime → 2 ^ (k + 1) < p → 2 ^ (k + 1) < q → p ≠ q →
    2 ^ (k + 1) * p * q < (2 ^ (k + 1) - 1) * (p + 1) * (q + 1) →
    (∀ b c : ℕ, b < 2 ^ (k + 1) → c < 2 ^ (k + 1) →
      ¬ (b * p + c * q ≤ (2 ^ (k + 1) - 1) * (p + 1) * (q + 1) - 2 ^ (k + 1) * p * q ∧
        (2 ^ (k + 1) - 1) * (p + 1) * (q + 1) - 2 ^ (k + 1) * p * q < b * p + c * q + 2 ^ (k + 1))) →
    Erdos470.PrimitiveWeird (2 ^ k * p * q) :=
  OMA.R3H1.main

theorem OMA.solution : OMA.R_Erdos470_erdos_470_parts_ii_R3.H1 := R3H1
