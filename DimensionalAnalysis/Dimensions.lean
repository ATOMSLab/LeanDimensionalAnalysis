-- Repository of defined dimensions using our definitions
import DimensionalAnalysis.Basic
--physics

/-!
### Definition of the base dimensions
-/
namespace dimension
def length (α) [HasBaseLength α] : dimension α := Pi.single HasBaseLength.length 1
def time (α) [HasBaseTime α] : dimension α := Pi.single HasBaseTime.time 1
def mass (α) [HasBaseMass α] : dimension α := Pi.single HasBaseMass.mass 1
def amount (α) [HasBaseAmount α] : dimension α :=
  Pi.single HasBaseAmount.amount 1
def current (α) [HasBaseCurrent α] : dimension α :=
  Pi.single HasBaseCurrent.current 1
def temperature (α) [HasBaseTemperature α] : dimension α :=
  Pi.single HasBaseTemperature.temperature 1
def luminosity (α) [HasBaseLuminosity α] : dimension α :=
  Pi.single HasBaseLuminosity.luminosity 1




def area (α) [HasBaseLength α] := dimension.length α^2
def volume (α) [HasBaseLength α] := dimension.length α^3
@[simp, match_pattern] theorem vol_eq_area_mul_length {α} [HasBaseLength α] : (dimension.area α * (dimension.length α)) = dimension.volume α := by
  simp[dimension.area, dimension.length, dimension.volume]
  funext x
  ring_nf
instance {α} [HasBaseLength α] : dimension.Eq (area α * length α) (volume α) := ⟨vol_eq_area_mul_length⟩


def velocity (α) [HasBaseLength α] [HasBaseTime α] : dimension α := length α / time α

def acceleration (α) [HasBaseLength α] [HasBaseTime α] : dimension α := length α / ((time α) ^ 2)

def force (α) [HasBaseLength α] [HasBaseTime α] [HasBaseMass α] : dimension α :=
  length α / ((time α) ^ 2) * mass α

theorem accel_eq_vel_div_time {α} [HasBaseLength α] [HasBaseTime α] :
  acceleration α = velocity α / (time α) := by
    simp [velocity, acceleration, time, length, div_eq_mul_inv]
    funext x
    ring_nf

theorem force_eq_mass_mul_accel {α} [HasBaseLength α] [HasBaseTime α] [HasBaseMass α] :
  force α = mass α * acceleration α := by
    simp [force, acceleration]
    funext
    ring_nf
end dimension
