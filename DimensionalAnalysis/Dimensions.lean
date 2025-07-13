-- Repository of defined dimensions
import DimensionalAnalysis.BasicCopy


/-!
### Definition of the base dimensions
-/
namespace dimension
variable (α) (γ) [CommRing γ] [HasBaseLength α]
def length [HasBaseLength α] : dimension α ℤ := Pi.single HasBaseLength.length 1
def time [HasBaseTime α] : dimension α ℤ := Pi.single HasBaseTime.time 1
def mass [HasBaseMass α] : dimension α ℤ := Pi.single HasBaseMass.mass 1
def amount [HasBaseAmount α] : dimension α ℤ := Pi.single HasBaseAmount.amount 1
def current [HasBaseCurrent α] : dimension α ℤ := Pi.single HasBaseCurrent.current 1
def temperature [HasBaseTemperature α] : dimension α ℤ := Pi.single HasBaseTemperature.temperature 1
def luminosity [HasBaseLuminosity α] : dimension α ℤ := Pi.single HasBaseLuminosity.luminosity 1

--instance {γ} [CommRing γ]: HPow (dimension α ℤ) γ (dimension α γ) := ⟨dimension.pow⟩


/-!
### Spatial Dimensions
-/

abbrev n_volume  {γ} [CommRing γ] [HMul γ ℤ γ] (n : γ) [HasBaseLength α] := (length α)^n
abbrev area [HasBaseLength α] := n_volume α 2
abbrev volume [HasBaseLength α] := n_volume α 3


/-!
### Temporal Dimensions
-/
def velocity (α) [HasBaseLength α] [HasBaseTime α] := length α/ time α
def acceleration (α) [HasBaseLength α] [HasBaseTime α] := length α / ((time α) ^ 2)

/-!
### Kinematic Dimensions
-/
def force (α) [HasBaseLength α] [HasBaseTime α] [HasBaseMass α] := length α / ((time α) ^ 2) * mass α

end dimension
