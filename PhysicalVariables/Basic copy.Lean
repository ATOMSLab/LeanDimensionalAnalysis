import DimensionalAnalysis.Dimensions
import DimensionalAnalysis.ISO
-- Defining physical variables and measurements
namespace PhysicalVariable
structure measurement (B V) [CommRing V]  where
(value : V)
(dim : dimension B V)


variable {B} {V} [CommRing V]

-- Multiplication
def measurement.Mul :
measurement B V →  measurement B V → measurement B V
| a,b => measurement.mk (a.value*b.value) (a.dim*b.dim)

instance : Mul (measurement B V) := ⟨measurement.Mul⟩

-- Division
def measurement.Div [Div V]:
measurement B V →  measurement B V → measurement B V
| a,b => measurement.mk (a.value/b.value) (a.dim/b.dim)

instance [Div V]: Div (measurement B V) := ⟨measurement.Div⟩


-- Addition
noncomputable def measurement.Add : measurement B V → measurement B V → measurement B V
| a,b => ⟨a.value+b.value,a.dim+b.dim⟩

noncomputable instance : Add (measurement B V) := ⟨measurement.Add⟩

-- Subtraction
noncomputable def measurement.Sub : measurement B V → measurement B V → measurement B V
| a,b => ⟨a.value-b.value,a.dim-b.dim⟩

noncomputable instance : Sub (measurement B V) := ⟨measurement.Sub⟩

-- Powers
def measurement.Pow [Pow V V]:
(measurement B V ) → V → (measurement B V )
| a,b => ⟨a.value^b,a.dim^b⟩

instance [Pow V V]: Pow (measurement B V) V := ⟨measurement.Pow⟩


instance : OfNat (measurement B V) n where
  ofNat := {
    value := n,
    dim   := dimension.dimensionless B V
  }

instance {B V : Type} [CommRing V] [OfScientific V] : OfScientific (measurement B V) where
  ofScientific := fun (m : Nat) (s : Bool) (e : Nat) =>
    {
      value := OfScientific.ofScientific m s e,
      dim   := dimension.dimensionless B V
    }

end PhysicalVariable

instance: Pow ℚ ℚ where
  pow q1 q2 := ⟨q1.num^q2.num^(1/q2.den),q1.den^q2.num^(1/q2.den),by simp [Nat.pow_eq_zero],by
    rw [Int.natAbs_pow]; exact q.reduced.pow _ _⟩
namespace Units
instance : Coe ℤ ℚ := sorry

variable {B}


def casesium133GroundStateHyperfineOscillationDuration [HasBaseTime B] : PhysicalVariable.measurement B ℚ := ⟨1, dimension.time B⟩

def second [HasBaseTime B] : PhysicalVariable.measurement B ℚ := 9192631770*casesium133GroundStateHyperfineOscillationDuration

def meter [HasBaseLength B] : PhysicalVariable.measurement B ℚ := ⟨1, dimension.length B⟩

def kilogram [HasBaseMass B] : PhysicalVariable.measurement B ℚ := ⟨1, dimension.mass B⟩

def ampere [HasBaseCurrent B] : PhysicalVariable.measurement B ℚ := ⟨1, dimension.current B⟩

def kelvin [HasBaseTemperature B] : PhysicalVariable.measurement B ℚ := ⟨1, dimension.temperature B⟩

def mole [HasBaseAmount B] : PhysicalVariable.measurement B ℚ := ⟨6.02214076e23, dimension.amount B⟩

def SpeedofLight [HasBaseLength B] [HasBaseTime B] : PhysicalVariable.measurement B ℚ := 299792458*meter/second

def PlancksConstant [HasBaseLength B] [HasBaseTime B] [HasBaseMass B] : PhysicalVariable.measurement B ℚ := 6.62607015e-34*kilogram*meter^2/second

def BoltzmannConstant [HasBaseLength B] [HasBaseTime B] [HasBaseTemperature B] : PhysicalVariable.measurement B ℚ := 1.380649e-23 meter^2/(second^2*kelvin)




def centimeter [HasBaseLength B] : PhysicalVariable.measurement B ℚ :=
  meter/100

def inch [HasBaseLength B] : PhysicalVariable.measurement B ℚ := centimeter/(254/100)


def millisecond [HasBaseTime B] : PhysicalVariable.measurement B ℚ := second/1000
