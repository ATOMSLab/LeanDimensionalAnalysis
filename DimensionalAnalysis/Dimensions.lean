-- Repository of defined dimensions
import DimensionalAnalysis.Basic
universe u v

/-!
### Definition of the foundational dimensions
-/
namespace dimension
variable (B : Type u)
-- the foundational dimensions are defined on the basis of the integers. This doesn't limit they use
-- because we can coerce the exponent type to another type for a dimension.
def length [HasBaseLength B] : dimension B ℤ := Pi.single HasBaseLength.Length 1
def time [HasBaseTime B] : dimension B ℤ := Pi.single HasBaseTime.Time 1
def mass [HasBaseMass B] : dimension B ℤ := Pi.single HasBaseMass.Mass 1
def amount [HasBaseAmount B] : dimension B ℤ := Pi.single HasBaseAmount.Amount 1
def current [HasBaseCurrent B] : dimension B ℤ := Pi.single HasBaseCurrent.Current 1
def temperature [HasBaseTemperature B] : dimension B ℤ := Pi.single HasBaseTemperature.Temperature 1
def luminosity [HasBaseLuminosity B] : dimension B ℤ := Pi.single HasBaseLuminosity.Luminosity 1

/-!
### Spatial Dimensions
-/
variable (B : Type u) [HasBaseLength B] [HasBaseTime B] [HasBaseMass B]
abbrev area := (length B)^2
abbrev volume := (length B)^3

/-!
### Temporal Dimensions
-/
abbrev velocity := length B/ time B
abbrev acceleration := length B / ((time B) ^ 2)

/-!
### Volumetric Variables
-/
abbrev mass_density := mass B / volume B

/-!
### Kinematic Dimensions
-/
abbrev force := length B / ((time B) ^ 2) * mass B
abbrev dynamic_viscocity := mass B / (length B * time B)

/-!
### Dimensionless numbers
-/
abbrev reynolds_number := mass_density B * velocity B *length B /dynamic_viscocity B
end dimension
