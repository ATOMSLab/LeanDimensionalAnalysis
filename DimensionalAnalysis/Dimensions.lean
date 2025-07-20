-- Repository of defined dimensions
import DimensionalAnalysis.Basic
universe u v

/-!
### Definition of the foundational dimensions
-/
namespace dimension
variable (α : Type u) [HasBaseLength α] [HasBaseTime α] [HasBaseMass α]
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
abbrev area := (length α)^2
abbrev volume := (length α)^3

/-!
### Temporal Dimensions
-/
abbrev velocity := length α/ time α
abbrev acceleration := length α / ((time α) ^ 2)

/-!
### Volumetric Variables
-/
abbrev mass_density := mass α / volume α

/-!
### Kinematic Dimensions
-/
abbrev force := length α / ((time α) ^ 2) * mass α
abbrev dynamic_viscocity := mass α / (length α * time α)

/-!
### Dimensionless numbers
-/
abbrev reynolds_number := mass_density α * velocity α *length α /dynamic_viscocity α
end dimension
