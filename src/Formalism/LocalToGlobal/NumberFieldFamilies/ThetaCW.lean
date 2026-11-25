module

public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCF
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SignatureConjugationInvariant
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedKfin
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeilUnr

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH

namespace Formalism.L2.Fam.ThC

open Formalism.L2.Theta

theorem sd_star (D : D7) : star D.host.sqrtMinusD = -D.host.sqrtMinusD := by
  apply D.host.φ₀.injective
  have h : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  rw [emb_star, map_neg, h, map_mul, Complex.conj_I, Complex.conj_ofReal, neg_mul]

theorem sd_ne (D : D7) : D.host.sqrtMinusD ≠ 0 := by
  intro h0
  have h : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  rw [h0, map_zero] at h
  exact mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.2
    (Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero D.host.hyp.2.1.ne_zero))).ne') h.symm

def ExpU (D : D7) : Prop :=
  ∀ (χ : (AE D)ˣ →* Circle) (τ : D.what₂.Tau) (a b : ℚ), HasInfExp D χ τ a → HasInfExp D χ τ b → a = b

end Formalism.L2.Fam.ThC

end
