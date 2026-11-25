module

public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.FinSplit
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SplitAsm
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SplitDict
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.ExistsUpperProjectionInverseTranspose
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.InducedVanishOfVanishOnIntegral
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.PfDict
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SplitCharacterFacts
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SplitFin
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.RightOnto
public import Development.WeilBound.ThetaLifts.CartanFactorisation.CartanConj
public import Development.WeilBound.ThetaLifts.LocalTheory.UnramifiedDeterminedBySpherical
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinSplitOfNarrow
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KCoinvOfNarrow
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalMultiplicityOneIrreducibleGL
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantInducedIsAdmissible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantModulus
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CellFunctorNonscalarOffdiag
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProduct
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleUnitarySemisimple
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactOpenSubgroupsBasis
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.FullOfSoLoc
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibRepApply
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDict
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GeometricSplitting.Imports
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfActs
import Formalism.DoubleCosetMeasures.Statement
import GroundTheory.LocalFields.PadicLogSeries
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.BernsteinExponentBounds.BernAll

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothCharOfCondLE, Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinNarrowness.RamifiedMultiplicityOneOfGeometricFiltration, Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinNarrowness.BernsteinClosure.RamifiedMultiplicityOne

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothCharOfCondLE =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothCharOfCondLE", "h": "module\n\npublic import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.FinSplit\npublic import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SplitAsm\npublic import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SplitDict\npublic import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.ExistsUpperProjectionInverseTranspose\npublic import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.InducedVanishOfVanishOnIntegral\npublic import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.PfDict\npublic import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SplitCharacterFacts\npublic import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SplitFin\nimport Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfActs\nimport Formalism.DoubleCosetMeasures.Statement\nimport GroundTheory.LocalFields.PadicLogSeries\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\nimport Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinSplitOfNarrow\n\n"}
section -- clump:auto
@[expose] public section

open ValuativeRel Matrix Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitNarrow

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitFlip GlobalTheory.SplitWeil
open PositivityTheory.ThK.SplitLoc PositivityTheory.ThK.SplitDict PositivityTheory.ThK.SplitAsm

open GlobalTheory.CompanionTheory.BernBridge.Split (IndIrredLt indIrredLt_of onto_of_irredLt)

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isSmoothChar_of_condLE {ϖ : kˣ} {e : ℕ} {χ : kˣ →* ℂˣ} (h : CondLE ϖ e χ) : IsSmoothChar χ := by
  have ho : IsOpen (𝒪[k] : Set k) := Valuation.isOpen_integer
  have h1 : IsOpen (({x : kˣ | (x : k) ∈ (𝒪[k] : Set k)} ∩ {x : kˣ | ((x⁻¹ : kˣ) : k) ∈ (𝒪[k] : Set k)}) ∩
      {x : kˣ | ((x : k) - 1) * (((ϖ ^ e : kˣ) : k))⁻¹ ∈ (𝒪[k] : Set k)}) :=
    ((ho.preimage Units.continuous_val).inter (ho.preimage Units.continuous_coe_inv)).inter
      (ho.preimage ((Units.continuous_val.sub continuous_const).mul continuous_const))
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (h1.mem_nhds ?_) ?_)
  · refine ⟨⟨one_mem 𝒪[k], by simpa using one_mem 𝒪[k]⟩, ?_⟩
    simpa using zero_mem 𝒪[k]
  · rintro x ⟨⟨hx, hx'⟩, hx''⟩
    have a1 : valuation k (x : k) ≤ 1 := hx
    have a2 : valuation k ((x⁻¹ : kˣ) : k) ≤ 1 := hx'
    have a3 : valuation k (((x : k) - 1) * (((ϖ ^ e : kˣ) : k))⁻¹) ≤ 1 := hx''
    have hc : valuation k (((ϖ ^ e : kˣ) : k)) ≠ 0 := by simp
    refine h x ⟨le_antisymm a1 ?_, ?_⟩
    · rw [Units.val_inv_eq_inv_val, map_inv₀] at a2
      exact (inv_le_one₀ (zero_lt_iff.2 (by simp))).1 a2
    · rw [map_mul, map_inv₀] at a3
      have a4 := (mul_inv_le_iff₀ (zero_lt_iff.2 hc)).1 a3
      rwa [one_mul] at a4

theorem irred_of_setting (hI : IndIrredLt) {a a' : ℕ} {ϖ : kˣ} {α β ν : kˣ →* ℂˣ} (H : HidaSetting a a' ϖ α β ν)
    (N : Submodule ℂ (GL (Fin (a + a')) k → ℂ)) (hN : N ≤ indSp a a' α β) (hst : ∀ h₁, ∀ F ∈ N, rtr h₁ F ∈ N) :
    N = ⊥ ∨ N = indSp a a' α β := by
  obtain ⟨e, h1, h2⟩ := H.cond
  exact hI k a a' α β H.unitα H.unitβ (isSmoothChar_of_condLE h1) (isSmoothChar_of_condLE h2) H.lt N hN hst

end Local

section Ram

attribute [local instance 10000] GlobalTheory.SplitWeil.matrixMeasurableSpace

theorem ramMaps_of (hI : IndIrredLt) : RamMaps := by
  intro k _ _ _ _ _ _ a a' ϖ α β ν H hν
  obtain ⟨_, hα, hβ⟩ := H.cond
  exact ⟨fun _ h _ h₁ c => pRam_add H hν h h₁ c, fun _ h _ h₁ c => pRam'_add H h h₁ c, fun _ h => pRam_mem H hν h,
    fun _ h => pRam'_mem H h, fun _ h g => pRam_inv H hν h g, fun Ψ _ g => pRam'_inv Ψ g, fun Φ _ h => pRam_equiv Φ h,
    fun Ψ _ h => pRam'_equiv Ψ h,
    onto_of_irredLt hI H.unitα H.unitβ (isSmoothChar_of_condLE hα) (isSmoothChar_of_condLE hβ) H.lt _ (fun _ h _ h₁ c => pRam_add H hν h h₁ c) (fun _ h => pRam_mem H hν h)
      (fun Φ h h₁ => ⟨_, omA_mem_SB ν β 1 h₁ h, pRam_equiv Φ h₁⟩) (pRam_ne_zero H),
    onto_of_irredLt hI H.unitα H.unitβ (isSmoothChar_of_condLE hα) (isSmoothChar_of_condLE hβ) H.lt _ (fun _ h _ h₁ c => pRam'_add H h h₁ c) (fun _ h => pRam'_mem H h)
      (fun Ψ h h₁ => ⟨_, omB_mem_SB ν α 1 h₁ h, pRam'_equiv Ψ h₁⟩) (pRam'_ne_zero H)⟩

end Ram

section Fin

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open PositivityTheory.KCo PositivityTheory.ThK

attribute [local instance] PositivityTheory.ThK.SplitAsm.measFv PositivityTheory.ThK.SplitAsm.borelFv

theorem finRam_of (hR : RamMaps) (hRN : RamNonzero) (hI : IndIrredLt) (hD : Dict) (hAU : ActsUniq) (hC : ChrFacts) :
    FinRam := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v hv
  have hP : v ∈ B.P := hT.chars.sub hv
  obtain ⟨hα, hβ, hν, hcond, hram, -⟩ := hC F E B X a a' v (B.τ ⟨v, hP⟩) hT.chars
  have hS : HidaSetting a a' (unifAt v) (chrW X.α (B.τ ⟨v, hP⟩)) (chrW X.β (B.τ ⟨v, hP⟩)) (chrW X.ν (B.τ ⟨v, hP⟩)) :=
    ⟨GlobalTheory.SplitFlip.exists_isUnif.choose_spec, hα, hβ, hν, hT.geo.lt, hT.geo.even, hcond⟩
  obtain ⟨hlin, hlin', hmem, hmem', hinv, hinv', heq, heq', hon, hon'⟩ := hR (Fv F v) a a' _ _ _ _ hS (hram hv)
  obtain ⟨Φ0, hΦ0, hnz⟩ := hRN (Fv F v) a a' _ _ _ _ hS (hram hv)
  obtain ⟨b, b', c, ι, ι', gl, gl', hl, hW, hB, hbas, hvac, hvac', hRg, hRh, hRg', hRh', hhl⟩ :=
    hD F E σ B a a' G X om om' hT v (B.τ ⟨v, hP⟩)
  obtain ⟨rfl, rfl, rfl⟩ := hbas hP rfl
  obtain ⟨p, p', hp, hp', hon1, hon1', hinv1, hinv1', heq1, hnt, hirr1⟩ := core hAU v G om om' _ _ _ (indSp a a' _ _)
    (pRam a a' (unifAt v) (chrW X.ν (B.τ ⟨v, hP⟩)) (chrW X.β (B.τ ⟨v, hP⟩)))
    (pRam' a a' (chrW X.ν (B.τ ⟨v, hP⟩)) (chrW X.α (B.τ ⟨v, hP⟩)))
    (fun Φ h Φ₁ h₁ => hlin Φ h Φ₁ h₁) (fun Φ h Φ₁ h₁ => hlin' Φ h Φ₁ h₁)
    (fun Φ h => hmem Φ h) (fun Φ h => hmem' Φ h) (fun Φ h => hinv Φ h)
    (fun Φ h => hinv' Φ h) (fun Φ h => heq Φ h) (fun Φ h => heq' Φ h)
    (fun y hy => by obtain ⟨Φ, h, r⟩ := hon y hy; exact ⟨Φ, h, r⟩)
    (fun y hy => by obtain ⟨Φ, h, r⟩ := hon' y hy; exact ⟨Φ, h, r⟩) ⟨Φ0, hΦ0, hnz⟩
    (fun N hN hst => irred_of_setting hI hS N hN hst) ι ι' hW.bij hB.bij gl gl' hl hRg hRh hRg' hRh' hhl
  refine ⟨oneMaps v _ p p', ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [oneMaps_p]; exact hon1
  · rw [oneMaps_p']; exact hon1'
  · rw [oneMaps_p]; exact hinv1
  · rw [oneMaps_p']; exact hinv1'
  · rw [oneMaps_p, oneMaps_p']; exact heq1
  · exact hnt
  · rw [oneMaps_p]; exact hirr1
  · intro hv'; exact absurd hv hv'
  · intro hv' _
    refine ⟨ι, ι', hW, hB, hvac, hvac', fun φ hφ φ' hφ' => ?_⟩
    rw [oneMaps_p, oneMaps_p']
    refine ⟨fun h => ?_, fun h => Subtype.ext ?_⟩
    · have := congrArg Subtype.val h
      erw [hp φ hφ, hp' φ' hφ'] at this
      exact this
    · erw [hp φ hφ, hp' φ' hφ']
      exact h

end Fin

theorem finRam_of_narrow :
    (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ)
      (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → IsUnitaryChar χ₁ → IsUnitaryChar χ₂ →
      (a ≠ b ∨ χ₁ ≠ χ₂) → (prod₂ (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).IsIrreducible) → PositivityTheory.ThK.FinRam :=
  fun NB => finRam_of (ramMaps_of (indIrredLt_of NB)) ramified_map_ne_zero (indIrredLt_of NB) split_place_dictionary
    PositivityTheory.KCo.action_uniqueness split_character_facts

end GlobalTheory.CompanionTheory.SplitNarrow
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothCharOfCondLE =====

-- ===== clump member: Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinNarrowness.RamifiedMultiplicityOneOfGeometricFiltration =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinNarrowness.RamifiedMultiplicityOneOfGeometricFiltration", "h": "module\n\npublic import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration\npublic import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.FinSplit\npublic import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.RightOnto\npublic import Development.WeilBound.ThetaLifts.CartanFactorisation.CartanConj\npublic import Development.WeilBound.ThetaLifts.LocalTheory.UnramifiedDeterminedBySpherical\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinSplitOfNarrow\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KCoinvOfNarrow\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalMultiplicityOneIrreducibleGL\npublic import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible\n\n"}
section -- clump:auto
@[expose] public section

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinNarrowness.RamifiedMultiplicityOneOfGeometricFiltration =====

-- ===== clump member: Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinNarrowness.BernsteinClosure.RamifiedMultiplicityOne =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinNarrowness.BernsteinClosure.RamifiedMultiplicityOne", "h": "module\n\npublic import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinNarrowness.RamifiedMultiplicityOneOfGeometricFiltration\npublic import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantInducedIsAdmissible\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantModulus\npublic import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient\npublic import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CellFunctorNonscalarOffdiag\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProduct\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleUnitarySemisimple\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactOpenSubgroupsBasis\npublic import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.FinSplit\npublic import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SplitAsm\npublic import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SplitDict\npublic import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.ExistsUpperProjectionInverseTranspose\npublic import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.InducedVanishOfVanishOnIntegral\npublic import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.PfDict\npublic import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SplitCharacterFacts\npublic import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SplitFin\npublic import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.FullOfSoLoc\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibRepApply\npublic import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDict\npublic import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration\npublic import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.RightOnto\npublic import Development.WeilBound.ThetaLifts.CartanFactorisation.CartanConj\npublic import Development.WeilBound.ThetaLifts.LocalTheory.UnramifiedDeterminedBySpherical\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinSplitOfNarrow\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KCoinvOfNarrow\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalMultiplicityOneIrreducibleGL\npublic import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GeometricSplitting.Imports\nimport Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothCharOfCondLE\nimport Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.BernsteinExponentBounds.BernAll\n\n"}
section -- clump:auto
@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace PositivityTheory.BernsteinRamification.Close

theorem narrowBern : GlobalTheory.CompanionTheory.BernBridge.Split.NarrowBernstein := by
  intro k _ _ _ _ a b χ₁ χ₂ s₁ s₂ u₁ u₂ _
  exact PositivityTheory.RgUd.All.bernsteinUnitaryProductIrreducible k a b ℂ ℂ _ _
    ((isSmooth_ofChar_iff _).2 s₁.detChar) (isIrreducible_ofChar _) ((isUnitarisable_ofChar_iff _).2 fun g => u₁ _)
    ((isSmooth_ofChar_iff _).2 s₂.detChar) (isIrreducible_ofChar _) ((isUnitarisable_ofChar_iff _).2 fun g => u₂ _)

theorem kCoinv (hD : PositivityTheory.KCo.DictSt) : GlobalTheory.ThK.KCoinv :=
  GlobalTheory.CompanionTheory.KCoNarrow.kCoinv_of_narrow narrowBern hD

theorem soCoinv (hK : GlobalTheory.ThK.KFin) : PositivityTheory.ThKF.SoCoinv :=
  PositivityTheory.KCo.soCoinv_of PositivityTheory.RgUd.All.bernsteinUnitaryProductIrreducible PositivityTheory.KCo.dictionary_statement hK

theorem ramifiedMultiplicityOne : PositivityTheory.ThKG.Loc.RamifiedMultiplicityOne :=
  PositivityTheory.ThKG.LocalRamifiedLeviRestriction.ramifiedMultiplicityOne_of_bernstein
    PositivityTheory.RgUd.All.bernsteinUnitaryProductIrreducible

theorem finRam : PositivityTheory.ThK.FinRam :=
  GlobalTheory.CompanionTheory.SplitNarrow.finRam_of_narrow narrowBern

theorem finSplit : PositivityTheory.ThK.FinSplit :=
  GlobalTheory.CompanionTheory.BernBridge.Split.finSplit_of_narrow narrowBern

end PositivityTheory.BernsteinRamification.Close
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinNarrowness.BernsteinClosure.RamifiedMultiplicityOne =====
