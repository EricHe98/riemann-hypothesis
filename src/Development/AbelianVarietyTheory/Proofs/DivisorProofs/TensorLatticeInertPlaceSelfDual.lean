module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.EventuallySelfDualLatticeIndicatorIsVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.WeilBound.ThetaLifts.TowerModels.PlaneReal

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertSelfDual

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem differentIdeal_eq_top_of_unram [Algebra.Unramified (𝓞 F) (𝓞 E)] : differentIdeal (𝓞 F) (𝓞 E) = ⊤ := by
  haveI : Algebra.IsSeparable (FractionRing (𝓞 F)) (FractionRing (𝓞 E)) := inferInstance
  by_contra hne
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
  have hd : P ∣ differentIdeal (𝓞 F) (𝓞 E) := Ideal.dvd_iff_le.mpr hle
  exact (dvd_differentIdeal_iff.mp hd) inferInstance

theorem mem_of_trace [Algebra.Unramified (𝓞 F) (𝓞 E)] (x : E)
    (hx : ∀ a : 𝓞 E, Algebra.trace F E (x * a) ∈ (algebraMap (𝓞 F) F).range) : x ∈ (algebraMap (𝓞 E) E).range := by
  have h1 := coeIdeal_differentIdeal (𝓞 F) F E (𝓞 E)
  rw [differentIdeal_eq_top_of_unram, FractionalIdeal.coeIdeal_top] at h1
  have hdual : FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) = 1 := by
    rw [← inv_inv (FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)), ← h1, inv_one]
  have : x ∈ FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) := by
    rw [FractionalIdeal.mem_dual (by simp)]
    intro a ha
    obtain ⟨a', rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    rw [Algebra.traceForm_apply]
    exact hx a'
  rw [hdual, FractionalIdeal.mem_one_iff] at this
  obtain ⟨y, hy⟩ := this
  exact ⟨y, hy⟩

theorem exists_traceFamily [Algebra.Unramified (𝓞 F) (𝓞 E)] :
    ∃ (k : ℕ) (s c : Fin k → 𝓞 E), ∀ e : E, ∑ i, Algebra.trace F E ((c i : E) * e) • (s i : E) = e := by
  obtain ⟨k, s, φ, hφ, hsum⟩ := GlobalTheory.AdelicU.SelfDual.exists_dualFamily_integers (F := F) (E := E)
  let D := LinearMap.BilinForm.toDual (Algebra.traceForm F E) (traceForm_nondegenerate F E)
  have hD : ∀ j x, Algebra.trace F E (D.symm (φ j) * x) = φ j x := fun j x => by
    have := LinearMap.BilinForm.apply_toDual_symm_apply (B := Algebra.traceForm F E)
      (hB := traceForm_nondegenerate F E) (φ j) x
    rw [Algebra.traceForm_apply] at this
    exact this
  have hc : ∀ j, D.symm (φ j) ∈ (algebraMap (𝓞 E) E).range := fun j =>
    mem_of_trace _ fun a => by rw [hD]; exact hφ a j
  choose c hc' using hc
  refine ⟨k, s, c, fun e => ?_⟩
  conv_rhs => rw [← hsum e]
  refine Finset.sum_congr rfl fun j _ => ?_
  show Algebra.trace F E (algebraMap (𝓞 E) E (c j) * e) • _ = _
  rw [hc', hD]

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  first
  | exact _root_.PositivityTheory.ThKG.Tow.Pln.det_ne_zero_of_hasSig
  | (apply _root_.PositivityTheory.ThKG.Tow.Pln.det_ne_zero_of_hasSig <;> assumption)

theorem det_ne_zero_of_herm (σ : E →ₐ[F] E) (B : Base F E) {n r s : ℕ} {X : Spc F E n} (h : X.IsHerm σ B r s) :
    X.J.det ≠ 0 := by
  intro h0
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  apply det_ne_zero_of_hasSig (h.sig w)
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]

theorem det_ne_zero_of_skew (σ : E →ₐ[F] E) (B : Base F E) {n r s : ℕ} {X : Spc F E n} (h : X.IsSkew σ B r s) :
    X.J.det ≠ 0 := by
  intro h0
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  apply det_ne_zero_of_hasSig (h.sig w)
  rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero, mul_zero]

theorem exists_formFrame (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (hJ : J.det ≠ 0)
    (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.IsFullLattice E)
    (hdual : ∀ y, (∀ x ∈ L, form σ J y x ∈ (algebraMap (𝓞 E) E).range) → y ∈ L) :
    ∃ (k : ℕ) (S T : Matrix (Fin n) (Fin k) E), (∀ j, (fun i => S i j) ∈ L) ∧ (∀ j, (fun i => T i j) ∈ L) ∧
      T * (J * S.map σ)ᵀ = 1 := by
  obtain ⟨k, S, Φ, h1, hS, hΦ⟩ := GlobalTheory.AdelicU.SelfDual.exists_frame L hL
  have hJu : IsUnit J.det := Ne.isUnit hJ
  have hJtu : IsUnit Jᵀ.det := by rwa [Matrix.det_transpose]
  refine ⟨k, S, (Jᵀ)⁻¹ * (Φ.map σ)ᵀ, hS, fun j => hdual _ fun x hx => ?_, ?_⟩
  · have h2 : ((Jᵀ)⁻¹ * (Φ.map σ)ᵀ)ᵀ * J = Φ.map σ := by
      rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_nonsing_inv, Matrix.transpose_transpose,
        Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hJu, Matrix.mul_one]
    have e : form σ J (fun i => ((Jᵀ)⁻¹ * (Φ.map σ)ᵀ) i j) x = σ ((Φ *ᵥ x) j) := by
      calc form σ J (fun i => ((Jᵀ)⁻¹ * (Φ.map σ)ᵀ) i j) x
          = (((((Jᵀ)⁻¹ * (Φ.map σ)ᵀ)ᵀ * J) *ᵥ fun i => σ (x i)) j) := by
            simp only [form, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul,
              Finset.mul_sum]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
        _ = σ ((Φ *ᵥ x) j) := by

            rw [h2]; simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
    rw [e]; exact GlobalTheory.AdelicU.SelfDual.sig_mem_range σ (hΦ x hx j)
  · rw [Matrix.transpose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc _ (Φ.map σ)ᵀ, ← Matrix.transpose_mul,
      ← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.mul_one,
      Matrix.nonsing_inv_mul _ hJtu]

alias cA_inclR := _root_.Tw.VacIndic.cA_inclR

theorem trace_inclR (e : E) :
    Algebra.trace (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (inclR (F := F) (AF F) e) = algebraMap F (AF F) (Algebra.trace F E e) := by
  show Algebra.trace (AF F) (AF F ⊗[F] E) ((1 : AF F) ⊗ₜ[F] e) = _
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

theorem inclR_smul (t : F) (x : E) :
    inclR (F := F) (AF F) (t • x) = algebraMap F (AF F) t • inclR (F := F) (AF F) x := by
  show (1 : AF F) ⊗ₜ[F] (t • x) = _
  rw [TensorProduct.tmul_smul, algebraMap_smul]
  rfl

theorem trace_expand {k : ℕ} (s c : Fin k → 𝓞 E)
    (hsc : ∀ e : E, ∑ i, Algebra.trace F E ((c i : E) * e) • (s i : E) = e) (u : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    u = ∑ i, Algebra.trace (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (inclR (F := F) (AF F) (c i : E) * u) • inclR (F := F) (AF F) (s i : E) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    have h1 : a ⊗ₜ[F] e = a • inclR (F := F) (AF F) e := by
      show _ = a • ((1 : AF F) ⊗ₜ[F] e)
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h1]
    simp_rw [mul_smul_comm, map_smul, ← map_mul, trace_inclR, smul_eq_mul]
    conv_lhs => rw [← hsc e]

    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inclR_smul, smul_smul]
  | add x y hx hy =>
    conv_lhs => rw [hx, hy]
    simp only [mul_add, map_add (f := _), add_smul, Finset.sum_add_distrib]

theorem incM_mul {m n p : ℕ} (A : Matrix (Fin m) (Fin n) E) (B : Matrix (Fin n) (Fin p) E) :
    incM F (A * B) = incM F A * incM F B := Matrix.map_mul

theorem incM_one {n : ℕ} : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)

theorem decomp {n d k k' : ℕ} (T : Matrix (Fin n) (Fin k) E) (P : Matrix (Fin k) (Fin n) E)
    (T' : Matrix (Fin d) (Fin k') E) (P' : Matrix (Fin k') (Fin d) E) (h : T * P = 1) (h' : T' * P' = 1)
    (z : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    z = ∑ j, ∑ l, (incM F P * z * (incM F P')ᵀ) j l • incM F (Matrix.vecMulVec (fun i => T i j) (fun i => T' i l)) := by
  have key : incM F T * (incM F P * z * (incM F P')ᵀ) * (incM F T')ᵀ = z := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← incM_mul, h, incM_one, Matrix.one_mul, Matrix.mul_assoc,
      ← Matrix.transpose_mul, ← incM_mul, h', incM_one, Matrix.transpose_one, Matrix.mul_one]
  conv_lhs => rw [← key]
  ext a b
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.sum_apply, Matrix.smul_apply, incM, Matrix.map_apply,
    Matrix.vecMulVec_apply, map_mul, smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem hTens_frame (σ : E →ₐ[F] E) {n d k k' : ℕ} (JA : Matrix (Fin n) (Fin n) E) (JB : Matrix (Fin d) (Fin d) E)
    (S : Matrix (Fin n) (Fin k) E) (S' : Matrix (Fin d) (Fin k') E) (z : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (e : E)
    (j : Fin k) (l : Fin k') :
    hTens (cA σ) (incM F JA) (incM F JB) z (incM F (Matrix.vecMulVec (fun i => e * S i j) (fun i => S' i l))) =
      inclR (F := F) (AF F) (σ e) * (incM F (JA * S.map σ)ᵀ * z * (incM F (JB * S'.map σ)ᵀ)ᵀ) j l := by

  simp only [hTens, incM, Matrix.map_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.vecMulVec_apply,
  cA_inclR, map_mul, map_sum, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.InertSelfDual
