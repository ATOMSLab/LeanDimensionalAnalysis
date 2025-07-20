import DimensionalAnalysis.Dimensions

-- Defining physical variables and measurements
namespace PhysicalVariable
structure measurement (α γ) [CommRing γ]  where
(value : γ)
(dim : dimension α γ)


variable {α} {γ} [CommRing γ]

-- Multiplication
def measurement.Mul :
measurement α γ →  measurement α γ → measurement α γ
| a,b => measurement.mk (a.value*b.value) (a.dim*b.dim)

instance : Mul (measurement α γ) := ⟨measurement.Mul⟩

-- Division
def measurement.Div [Div γ]:
measurement α γ →  measurement α γ → measurement α γ
| a,b => measurement.mk (a.value/b.value) (a.dim/b.dim)

instance [Div γ]: Div (measurement α γ) := ⟨measurement.Div⟩


-- Addition
noncomputable def measurement.Add : measurement α γ → measurement α γ → measurement α γ
| a,b => ⟨a.value+b.value,a.dim+b.dim⟩

noncomputable instance : Add (measurement α γ) := ⟨measurement.Add⟩

-- Subtraction
noncomputable def measurement.Sub : measurement α γ → measurement α γ → measurement α γ
| a,b => ⟨a.value-b.value,a.dim-b.dim⟩

noncomputable instance : Sub (measurement α γ) := ⟨measurement.Sub⟩

-- Powers
def measurement.Pow [Pow γ γ]:
(measurement α γ ) → γ → (measurement α γ )
| a,b => ⟨a.value^b,a.dim^b⟩

instance [Pow γ γ]: Pow (measurement α γ) γ := ⟨measurement.Pow⟩

def ofDimensionlessValue (val : γ) : measurement α γ := measurement.mk val (dimension.dimensionless α γ)

instance : OfNat (measurement α γ) n where
  ofNat := {
    value := n,
    dim   := dimension.dimensionless α γ
  }


end PhysicalVariable

namespace Units
instance : Coe ℤ ℚ := sorry

variable {α}
def meter [HasBaseLength α] : PhysicalVariable.measurement α ℚ := ⟨1,dimension.length α⟩

def centimeter [HasBaseLength α] : PhysicalVariable.measurement α ℚ :=
  meter/100

def inch [HasBaseLength α] : PhysicalVariable.measurement α ℚ := centimeter/(254/100)

def casesium133GroundStateHyperfineOscillationDuration [HasBaseTime α] : PhysicalVariable.measurement α ℚ := ⟨1, dimension.time α⟩

def second [HasBaseTime α] : PhysicalVariable.measurement α ℚ := 9192631770*casesium133GroundStateHyperfineOscillationDuration
