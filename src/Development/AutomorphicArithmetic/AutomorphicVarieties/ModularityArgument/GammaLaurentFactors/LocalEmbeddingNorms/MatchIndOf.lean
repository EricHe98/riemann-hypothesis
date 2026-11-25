module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.MatchIndOf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitaryTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.ExistsPullback
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.Regroup
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.NormCnt
import Formalism.DoubleCosetMeasures.Statement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import ReciprocityTheory.Chebotarev.CyclotomicIrreducibleOfForallIsUnramifiedAt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CycCOfCyclic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaTildeHeckeCharSplitMulSignOfNormFormula
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResFinEqOneOfAway

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf
open GroundTheory.Global.SemiLocal
open scoped Classical

namespace UpperTheory.V.Z.Gam

namespace InductionMatchingPlacesAbove

section Primes

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

private alias natCast_mem := _root_.GlobalTheory.EtaProduct.mem_of_dvd_absNorm

private alias normV_absNorm := _root_.GlobalTheory.ToricDistribution.normV_eq

private theorem absNorm_pow (w : HeightOneSpectrum (𝓞 M)) :
    Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ (w.under (𝓞 K)).asIdeal.inertiaDeg' w.asIdeal := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  rw [Ideal.inertiaDeg'_eq_inertiaDeg, Ideal.absNorm_pow_inertiaDeg]

private theorem sum_ef (hE : Module.finrank K M = 2) (v : HeightOneSpectrum (𝓞 K)) :
    ∑ P ∈ IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 M), v.asIdeal.ramificationIdx' P * v.asIdeal.inertiaDeg' P = 2 := by
  have := v.isMaximal
  rw [← hE]
  exact Ideal.sum_ramification_inertia (𝓞 M) K M v.ne_bot

private theorem mem_over (w : HeightOneSpectrum (𝓞 M)) :
    w.asIdeal ∈ IsDedekindDomain.primesOverFinset (w.under (𝓞 K)).asIdeal (𝓞 M) := by
  rw [IsDedekindDomain.mem_primesOverFinset_iff (w.under (𝓞 K)).ne_bot]
  exact ⟨w.isPrime, ⟨rfl⟩⟩

private theorem e_pos (w : HeightOneSpectrum (𝓞 M)) : 0 < (w.under (𝓞 K)).asIdeal.ramificationIdx' w.asIdeal := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  exact Nat.pos_of_ne_zero (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver _ (w.under (𝓞 K)).ne_bot)

private theorem f_pos (w : HeightOneSpectrum (𝓞 M)) : 0 < (w.under (𝓞 K)).asIdeal.inertiaDeg' w.asIdeal := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := (w.under (𝓞 K)).isMaximal
  exact Nat.pos_of_ne_zero (Ideal.inertiaDeg'_ne_zero _ _)

private theorem f_one (hE : Module.finrank K M = 2) {w w' : HeightOneSpectrum (𝓞 M)} (hne : w' ≠ w)
    (hu : w'.under (𝓞 K) = w.under (𝓞 K)) : (w.under (𝓞 K)).asIdeal.inertiaDeg' w.asIdeal = 1 := by
  classical
  have h1 := mem_over (K := K) w
  have h2 := mem_over (K := K) w'
  rw [hu] at h2
  have hne' : w.asIdeal ≠ w'.asIdeal := fun h => hne (HeightOneSpectrum.ext h.symm)
  have hsub : ({w.asIdeal, w'.asIdeal} : Finset (Ideal (𝓞 M))) ⊆
      IsDedekindDomain.primesOverFinset (w.under (𝓞 K)).asIdeal (𝓞 M) := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hle := Finset.sum_le_sum_of_subset
    (f := fun P => (w.under (𝓞 K)).asIdeal.ramificationIdx' P * (w.under (𝓞 K)).asIdeal.inertiaDeg' P) hsub
  rw [Finset.sum_pair hne', sum_ef hE] at hle
  have a := e_pos (K := K) w
  have b := f_pos (K := K) w
  have c := e_pos (K := K) w'
  have d := f_pos (K := K) w'
  rw [hu] at c d
  have : (w.under (𝓞 K)).asIdeal.inertiaDeg' w.asIdeal ≤ 1 := by nlinarith
  omega

private theorem f_two (hE : Module.finrank K M = 2) (w : HeightOneSpectrum (𝓞 M))
    (honly : ∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 K) = w.under (𝓞 K) → w' = w)
    (he : (w.under (𝓞 K)).asIdeal.ramificationIdx' w.asIdeal = 1) :
    (w.under (𝓞 K)).asIdeal.inertiaDeg' w.asIdeal = 2 := by
  classical
  have h := sum_ef (K := K) (M := M) hE (w.under (𝓞 K))
  rw [Finset.sum_eq_single_of_mem w.asIdeal (mem_over w) (fun Q hQ hQw => ?_), he, one_mul] at h
  · exact h
  · exfalso
    apply hQw
    rw [IsDedekindDomain.mem_primesOverFinset_iff (w.under (𝓞 K)).ne_bot] at hQ
    obtain ⟨hQp, hQl⟩ := hQ
    have hQ0 : Q ≠ ⊥ := by
      rintro rfl
      apply (w.under (𝓞 K)).ne_bot
      rw [hQl.over]
      exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
    have := honly ⟨Q, hQp, hQ0⟩ (HeightOneSpectrum.ext hQl.over.symm)
    exact congrArg HeightOneSpectrum.asIdeal this

private theorem unram_bound (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] :
    ∃ N : ℕ, ∀ w : HeightOneSpectrum (𝓞 M),
    ((N.factorial : ℕ) : 𝓞 K) ∉ (w.under (𝓞 K)).asIdeal → (w.under (𝓞 K)).asIdeal.ramificationIdx' w.asIdeal = 1 := by
  obtain ⟨N, hN⟩ := ReciprocityTheory.Cheb.exists_forall_isUnramifiedAt M
  refine ⟨N, fun w hw => ?_⟩
  have h1 : 1 < Ideal.absNorm (w.under (𝓞 K)).asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm _
  have hq := Nat.minFac_prime h1.ne'
  have hqv : ((Nat.minFac (Ideal.absNorm (w.under (𝓞 K)).asIdeal) : ℕ) : 𝓞 K) ∈ (w.under (𝓞 K)).asIdeal :=
    natCast_mem _ hq (Nat.minFac_dvd _)
  have hqN : N < Nat.minFac (Ideal.absNorm (w.under (𝓞 K)).asIdeal) := by
    by_contra! hle
    apply hw
    obtain ⟨k, hk⟩ := Nat.dvd_factorial hq.pos hle
    rw [hk, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hqv
  have hqw : ((Nat.minFac (Ideal.absNorm (w.under (𝓞 K)).asIdeal) : ℕ) : 𝓞 M) ∈ w.asIdeal := by
    have : algebraMap (𝓞 K) (𝓞 M) ((Nat.minFac (Ideal.absNorm (w.under (𝓞 K)).asIdeal) : ℕ) : 𝓞 K) ∈ w.asIdeal := hqv
    rwa [map_natCast] at this
  haveI := w.isPrime
  haveI := hN _ hq hqN w.asIdeal hqw
  have hsq := ReciprocityTheory.Cheb.natCast_notMem_sq_of_isUnramifiedAt hq w.asIdeal
  apply Ideal.ramificationIdx'_spec
  · rw [pow_one, Ideal.map_le_iff_le_comap]
    exact le_rfl
  · intro h
    have h3 := h (Ideal.mem_map_of_mem (algebraMap (𝓞 K) (𝓞 M)) hqv)
    rw [map_natCast] at h3
    exact hsq (by simpa using h3)

private theorem exists_over (p : HeightOneSpectrum (𝓞 K)) :
    ∃ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 K) = p := by
  have := p.isMaximal
  obtain ⟨Q, hQm, hQl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 M) p.asIdeal
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    apply p.ne_bot
    rw [hQl.over]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  exact ⟨⟨Q, hQm.isPrime, hQ0⟩, HeightOneSpectrum.ext hQl.over.symm⟩

private theorem finite_above (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) :
    {w : HeightOneSpectrum (𝓞 M) | w.under (𝓞 K) ∈ S}.Finite := by
  classical
  have : {w : HeightOneSpectrum (𝓞 M) | w.under (𝓞 K) ∈ S} ⊆
      ⋃ p ∈ S, HeightOneSpectrum.asIdeal ⁻¹' (↑(IsDedekindDomain.primesOverFinset (p : HeightOneSpectrum (𝓞 K)).asIdeal (𝓞 M)) : Set (Ideal (𝓞 M))) := by
    intro w hw
    exact Set.mem_biUnion hw (mem_over w)
  refine (hS.biUnion fun p _ => ?_).subset this
  exact (Finset.finite_toSet _).preimage (fun a _ b _ h => HeightOneSpectrum.ext h)

private theorem ind_key (hE : Module.finrank K M = 2) (sat : HeightOneSpectrum (𝓞 M) → Multiset ℂˣ → Prop)
    (satP : HeightOneSpectrum (𝓞 K) → Multiset ℂˣ → Prop) (hI : IndSys sat satP) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∀ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 K) ∉ S →
      (Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ∧ ∃ w' : HeightOneSpectrum (𝓞 M), w' ≠ w ∧
        w'.under (𝓞 K) = w.under (𝓞 K) ∧ ∃ B B', sat w B ∧ sat w' B' ∧ satP (w.under (𝓞 K)) (B + B')) ∨
      (Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ 2 ∧
        ∃ B B' : Multiset ℂˣ, sat w (B'.map (· ^ 2)) ∧ B = B' + B'.map (fun b => -b) ∧ satP (w.under (𝓞 K)) B) := by
  classical
  obtain ⟨N, hN⟩ := unram_bound K M
  have hT := Filter.eventually_cofinite.1 hI
  have hR : {p : HeightOneSpectrum (𝓞 K) | ((N.factorial : ℕ) : 𝓞 K) ∈ p.asIdeal}.Finite := by
    have h0 : Ideal.span {((N.factorial : ℕ) : 𝓞 K)} ≠ 0 := by
      rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast (Nat.factorial_pos N).ne'
    exact (Ideal.finite_factors h0).subset fun p hp => Ideal.dvd_span_singleton.2 hp
  have hF := hR.union (hT.image fun w => w.under (𝓞 K))
  refine ⟨hF.toFinset, fun w hw => ?_⟩
  rw [Set.Finite.mem_toFinset] at hw
  have hgood := not_not.1 fun h => hw (Or.inr ⟨w, h, rfl⟩)
  have he := hN w fun h => hw (Or.inl h)
  by_cases hs : ∃ w' : HeightOneSpectrum (𝓞 M), w' ≠ w ∧ w'.under (𝓞 K) = w.under (𝓞 K)
  · obtain ⟨w', hne, hu⟩ := hs
    left
    refine ⟨?_, w', hne, hu, hgood.1 w' hne hu⟩
    rw [absNorm_pow (K := K) w, f_one hE hne hu, pow_one]
  · push Not at hs
    have honly : ∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 K) = w.under (𝓞 K) → w' = w :=
      fun w' hu => by_contra fun hne => hs w' hne hu
    have hN2 : Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ 2 := by
      rw [absNorm_pow (K := K) w, f_two hE w honly he]
    right
    refine ⟨hN2, hgood.2 ?_⟩
    rw [normV_absNorm, normV_absNorm, hN2]

end Primes

section Main


open Classical in
private def pick {X : Type} (sat : X → Multiset ℂˣ → Prop) (w : X) : Multiset ℂˣ :=
  if h : ∃ B, sat w B then h.choose else 0

private theorem pick_spec {X : Type} {sat : X → Multiset ℂˣ → Prop} {w : X} {B : Multiset ℂˣ} (h : sat w B) :
    sat w (pick sat w) := by
  have h' : ∃ B, sat w B := ⟨B, h⟩
  rw [pick, dite_eq_left h']
  exact h'.choose_spec

private theorem sat_unique {F : Type} [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] {n : ℕ} (σ : CuspSub F n)
    {w : HeightOneSpectrum (𝓞 F)} {B B' : Multiset ℂˣ} (h : (CG.mk σ).HasSat w B) (h' : (CG.mk σ).HasSat w B') : B = B' :=
  GlobalTheory.LFun.HasSatGL.unique ((CG.hasSat_mk σ w B).1 h) ((CG.hasSat_mk σ w B').1 h')

private theorem sat_card {F : Type} [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] {n : ℕ} (σ : CuspSub F n)
    {w : HeightOneSpectrum (𝓞 F)} {B : Multiset ℂˣ} (h : (CG.mk σ).HasSat w B) : Multiset.card B = n :=
  GlobalTheory.LFun.HasSatGL.card ((CG.hasSat_mk σ w B).1 h)

private theorem bound_cx {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) {B : Multiset ℂˣ} {c₀ c : ℝ}
    (hc : c₀ ≤ c) (hb : ∀ b ∈ B, ‖(b : ℂ)‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ c₀ ∧
      ‖((b⁻¹ : ℂˣ) : ℂ)‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ c₀) :
    ∀ b ∈ B.map (fun b : ℂˣ => (b : ℂ)), ‖b‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ c ∧ ‖b⁻¹‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ c := by
  have hN : (1 : ℝ) ≤ (Ideal.absNorm w.asIdeal : ℝ) := by
    have : Ideal.absNorm w.asIdeal ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot
    exact_mod_cast Nat.one_le_iff_ne_zero.2 this
  have hmono : (Ideal.absNorm w.asIdeal : ℝ) ^ c₀ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ c :=
    Real.rpow_le_rpow_of_exponent_le hN hc
  intro b hb'
  obtain ⟨b₀, hb₀, rfl⟩ := Multiset.mem_map.1 hb'
  obtain ⟨h1, h2⟩ := hb b₀ hb₀
  refine ⟨h1.trans hmono, ?_⟩
  have : ((b₀ : ℂ))⁻¹ = ((b₀⁻¹ : ℂˣ) : ℂ) := (Units.val_inv_eq_inv_val b₀).symm
  rw [this]
  exact h2.trans hmono

end Main

section Cnt

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem unr_cancel {a b : kˣ →* ℂˣ} (ha : IsUnram a) (hab : IsUnram (a * b)) : IsUnram b := fun x hx => by
  have h := hab x hx
  rwa [MonoidHom.mul_apply, ha x hx, one_mul] at h

private theorem cnt_zero (s : Multiset (IrrGL (k := k))) (a : kˣ →* ℂˣ)
    (h : ∀ ξ hξ, IrrGL.ofChar ξ hξ ∈ s → ¬ IsUnram (ξ * a)) : cnt s a = 0 := by
  unfold cnt
  rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
  rintro y hy ⟨ξ, hξ, rfl, hu⟩
  exact h ξ hξ hy hu

private theorem cnt_zero_of_unr (s : Multiset (IrrGL (k := k))) (a : kˣ →* ℂˣ) (hs : ∀ y ∈ s, y.IsUnramChar)
    (ha : ¬ IsUnram a) : cnt s a = 0 := by
  refine cnt_zero s a fun ξ hξ hy hu => ?_
  obtain ⟨μ, hμ, e⟩ := hs _ hy
  rw [IrrGL.ofChar_inj.1 e] at hu
  exact ha (unr_cancel hμ hu)

private theorem exists_bad (s : Multiset (IrrGL (k := k))) :
    ∃ T : Finset (kˣ →* ℂˣ), ∀ ξ hξ, IrrGL.ofChar ξ hξ ∈ s → ξ ∈ T := by
  let g : IrrGL (k := k) → (kˣ →* ℂˣ) := fun y => if h : ∃ ξ hξ, y = IrrGL.ofChar ξ hξ then h.choose else 1
  refine ⟨s.toFinset.image g, fun ξ hξ hy => Finset.mem_image.2 ⟨_, Multiset.mem_toFinset.2 hy, ?_⟩⟩
  have h : ∃ ξ' hξ', IrrGL.ofChar ξ hξ = IrrGL.ofChar ξ' hξ' := ⟨ξ, hξ, rfl⟩
  change (if h : ∃ ξ' hξ', IrrGL.ofChar ξ hξ = IrrGL.ofChar ξ' hξ' then h.choose else 1) = ξ
  rw [dite_eq_left h]
  obtain ⟨h1, h2⟩ := h.choose_spec
  exact (IrrGL.ofChar_inj.1 h2).symm

end Cnt

private theorem unrAt_iff {F : Type} [Field F] [NumberField F] (χ : HChar F) (w : HeightOneSpectrum (𝓞 F)) :
    χ.UnrAt w ↔ IsUnram (χ.loc w) := by
  haveI : (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  refine forall_congr' fun x => imp_congr_left ?_
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion F)) Valued.v).eq_one_iff_eq_one.symm

section Key

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

private def Key (sat : HeightOneSpectrum (𝓞 M) → Multiset ℂˣ → Prop) (satP : HeightOneSpectrum (𝓞 K) → Multiset ℂˣ → Prop)
    (w : HeightOneSpectrum (𝓞 M)) : Prop :=
  (Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ∧ ∃ w' : HeightOneSpectrum (𝓞 M), w' ≠ w ∧
    w'.under (𝓞 K) = w.under (𝓞 K) ∧ ∃ B B', sat w B ∧ sat w' B' ∧ satP (w.under (𝓞 K)) (B + B')) ∨
  (Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ 2 ∧
    ∃ B B' : Multiset ℂˣ, sat w (B'.map (· ^ 2)) ∧ B = B' + B'.map (fun b => -b) ∧ satP (w.under (𝓞 K)) B)

private theorem Key.sat {sat : HeightOneSpectrum (𝓞 M) → Multiset ℂˣ → Prop}
    {satP : HeightOneSpectrum (𝓞 K) → Multiset ℂˣ → Prop} {w : HeightOneSpectrum (𝓞 M)} (h : Key sat satP w) :
    (∃ B, sat w B) ∧ ∃ B, satP (w.under (𝓞 K)) B := by
  rcases h with ⟨-, w', -, -, B, B', h1, -, h⟩ | ⟨-, B, B', h1, -, h⟩
  · exact ⟨⟨_, h1⟩, _, h⟩
  · exact ⟨⟨_, h1⟩, _, h⟩

private theorem key_twist [_root_.NumberField.IsTotallyComplex K] [_root_.NumberField.IsTotallyComplex M] (h2 : Module.finrank K M = 2)
    {P : CuspSub K (2 * 2)} {π : CuspSub M 2} (χ : HChar K) (ξ : HChar M)
    (hξ : ∀ w : HeightOneSpectrum (𝓞 M), χ.UnrAt (w.under (𝓞 K)) →
      ξ.UnrAt w ∧ ξ.val w = χ.val (w.under (𝓞 K)) ^ (w.under (𝓞 K)).asIdeal.inertiaDeg' w.asIdeal)
    {w : HeightOneSpectrum (𝓞 M)} (hu : χ.UnrAt (w.under (𝓞 K))) (h : Key (CG.mk π).HasSat (CG.mk P).HasSat w) :
    Key (CG.mk (π.twist ξ)).HasSat (CG.mk (P.twist χ)).HasSat w := by
  simp only [← CG.twist_mk]
  rcases h with ⟨hN, w', hne, hw', B, B', hB, hB', hBP⟩ | ⟨hN, B, B', hB, rfl, hBP⟩
  · obtain ⟨u1, v1⟩ := hξ w hu
    obtain ⟨u2, v2⟩ := hξ w' (hw' ▸ hu)
    rw [f_one h2 hne hw', pow_one] at v1
    rw [f_one h2 hne.symm hw'.symm, pow_one, hw'] at v2
    refine Or.inl ⟨hN, w', hne, hw', _, _, hB.twist u1, hB'.twist u2, ?_⟩
    have hP := hBP.twist hu
    rw [Multiset.map_add (f := _)] at hP
    rwa [v1, v2]
  · obtain ⟨u1, v1⟩ := hξ w hu
    have hf : (w.under (𝓞 K)).asIdeal.inertiaDeg' w.asIdeal = 2 :=
      Nat.pow_right_injective (NumberField.HeightOneSpectrum.one_lt_absNorm (w.under (𝓞 K)))
        ((absNorm_pow (K := K) w).symm.trans hN)
    rw [hf] at v1
    refine Or.inr ⟨hN, _, B'.map (· * χ.val (w.under (𝓞 K))), ?_, rfl, ?_⟩
    · have h := hB.twist u1
      rw [v1, Multiset.map_map] at h
      rw [Multiset.map_map]
      convert h using 2
      simp [mul_pow]
    · have h := hBP.twist hu
      simpa [Multiset.map_add (f := _), Multiset.map_map, Function.comp_def] using h

private theorem norm_units (h2 : Module.finrank K M = 2) :
    (∃ T : Finset (HeightOneSpectrum (𝓞 K)), ∀ u ∉ T, ∀ (w : PlacesOver M u) (θ : (u.adicCompletion K)ˣ →* ℂˣ),
      IsSmoothChar θ → IsUnram (θ.comp (nm w)) → IsUnram θ) ∧
    ∀ (u : HeightOneSpectrum (𝓞 K)) (w : PlacesOver M u) (θ : (u.adicCompletion K)ˣ →* ℂˣ), IsUnram θ →
      IsUnram (θ.comp (nm w)) := by
  haveI : Algebra.IsQuadraticExtension K M := { finrank_eq_two' := h2 }
  obtain ⟨η, h1, h3⟩ := normCnt K M (h2 ▸ Nat.prime_two)
  refine ⟨⟨(Filter.eventually_cofinite.1 h1).toFinset, fun u hu w θ hθ hn => ?_⟩,
    fun u w θ hθ => ((h3 u w).2.2 θ (isSmoothChar_of_isUnram hθ)).2.1 hθ⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hu
  have hc := ((h3 u w).2.2 θ hθ).2.2 hn
  have hpos : 0 < ∑ w' : PlacesOver M u, fdeg w' := by
    have hw := (hu.2 w).2
    have : 0 < fdeg w := Nat.pos_of_ne_zero fun e => by rw [e, h2] at hw; omega
    exact lt_of_lt_of_le this (Finset.single_le_sum (f := fun w' : PlacesOver M u => fdeg w')
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ w))
  rw [← hc] at hpos
  obtain ⟨j, hj⟩ := Finset.card_pos.1 hpos
  have hj' := (Finset.mem_filter.1 hj).2
  have hη : IsUnram ((η ^ j).loc u) := fun x hx => by
    have e : (η ^ j).loc u x = η.loc u x ^ j := MonoidHom.pow_apply η.1 j _
    rw [e, (unrAt_iff η u).1 hu.1 x hx, one_pow]
  exact unr_cancel hη (mul_comm θ _ ▸ hj')

end Key

end InductionMatchingPlacesAbove

end UpperTheory.V.Z.Gam
