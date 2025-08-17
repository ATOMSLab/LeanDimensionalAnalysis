-- Repository of defined dimensions
import DimensionalAnalysis.Basic
universe u v

/-!
### Definition of the foundational dimensions
-/
namespace dimension
variable (B : Type u) (E : Type v) [CommRing E]
-- the foundational dimensions are defined on the basis of the integers. This doesn't limit they use
-- because we can coerce the exponent type to another type for a dimension.
def length [HasBaseLength B] : dimension B E := Pi.single HasBaseLength.Length 1
def time [HasBaseTime B] : dimension B E := Pi.single HasBaseTime.Time 1
def mass [HasBaseMass B] : dimension B E := Pi.single HasBaseMass.Mass 1
def amount [HasBaseAmount B] : dimension B E := Pi.single HasBaseAmount.Amount 1
def current [HasBaseCurrent B] : dimension B E := Pi.single HasBaseCurrent.Current 1
def temperature [HasBaseTemperature B] : dimension B E := Pi.single HasBaseTemperature.Temperature 1
def luminosity [HasBaseLuminosity B] : dimension B E := Pi.single HasBaseLuminosity.Luminosity 1

/-!
### Spatial Dimensions
-/
variable (B : Type u) (E : Type v) [CommRing E] [HasBaseLength B] [HasBaseTime B] [HasBaseMass B]
abbrev area := (length B E)^2
abbrev volume := (length B E)^3

/-!
### Temporal Dimensions
-/
abbrev velocity := length B E/time B E
abbrev acceleration := length B E / ((time B E) ^ 2)

/-!
### Volumetric Variables
-/
abbrev mass_density := mass B E / volume B E

/-!
### Kinematic Dimensions
-/
abbrev force := length B E / ((time B E) ^ 2) * mass B E
abbrev dynamic_viscocity := mass B E / (length B E * time B E)
abbrev energy := mass B E * (length B E)^2/(time B E)^2
/-!
### Dimensionless numbers
-/
abbrev reynolds_number := mass_density B E * velocity B E *length B E/dynamic_viscocity B E
end dimension
