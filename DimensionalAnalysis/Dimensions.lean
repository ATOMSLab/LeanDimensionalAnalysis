-- Repository of defined dimensions
import DimensionalAnalysis.Basic
universe u v

/-!
### Definition of the foundational dimensions
-/
namespace dimension
variable (α : Type u)
-- the foundational dimensions are defined on the basis of the integers. This doesn't limit they use
-- because we can coerce the exponent type to another type for a dimension. Therefore, as long as
-- the exponents coerce we can raise this to any power and get a dimension with the proper type.
-- n_volume makes use of this along with our instance of HPow.
def length [HasBaseLength α] : dimension α ℤ := Pi.single HasBaseLength.Length 1
def time [HasBaseTime α] : dimension α ℤ := Pi.single HasBaseTime.Time 1
def mass [HasBaseMass α] : dimension α ℤ := Pi.single HasBaseMass.Mass 1
def amount [HasBaseAmount α] : dimension α ℤ := Pi.single HasBaseAmount.Amount 1
def current [HasBaseCurrent α] : dimension α ℤ := Pi.single HasBaseCurrent.Current 1
def temperature [HasBaseTemperature α] : dimension α ℤ := Pi.single HasBaseTemperature.Temperature 1
def luminosity [HasBaseLuminosity α] : dimension α ℤ := Pi.single HasBaseLuminosity.Luminosity 1

/-!
### Spatial Dimensions
-/

abbrev n_volume (α : Type u) {γ : Type v} [CommRing γ] [Coe ℤ γ] (n : γ) [HasBaseLength α] := (length α)^n
abbrev area (α : Type u) {γ : Type v} [CommRing γ] [Coe ℤ γ] [HasBaseLength α] := n_volume α (2:γ)
abbrev volume (α : Type u) {γ : Type v} [CommRing γ] [Coe ℤ γ] [HasBaseLength α] := n_volume α (3:γ)


/-!
### Temporal Dimensions
-/
abbrev velocity (α) [HasBaseLength α] [HasBaseTime α] := length α/ time α
abbrev acceleration (α) [HasBaseLength α] [HasBaseTime α] := length α / ((time α) ^ 2)

/-!
### Kinematic Dimensions
-/
abbrev force (α) [HasBaseLength α] [HasBaseTime α] [HasBaseMass α] := length α / ((time α) ^ 2) * mass α

end dimension
