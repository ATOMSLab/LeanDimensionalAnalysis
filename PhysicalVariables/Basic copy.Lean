import DimensionalAnalysis.Dimensions

-- Defining physical variables and measurements
namespace PhysicalVariable
structure measurement (V α γ) [CommRing γ]  where
(value : V)
(dim : dimension α γ)


variable {V1 V2 V3} {α} {γ} [CommRing γ]

-- Multiplication
def measurement.Mul [HMul V1 V2 V3] :
measurement V1 α γ →  measurement V2 α γ → measurement V3 α γ
| a,b => measurement.mk (a.value*b.value) (a.dim*b.dim)

instance [HMul V1 V2 V3] :
  HMul (measurement V1 α γ) (measurement V2 α γ) (measurement V3 α γ) := ⟨measurement.Mul⟩

-- Division
def measurement.Div [HDiv V1 V2 V3] :
measurement V1 α γ →  measurement V2 α γ → measurement V3 α γ
| a,b => measurement.mk (a.value/b.value) (a.dim/b.dim)

instance [HDiv V1 V2 V3] :
  HDiv (measurement V1 α γ) (measurement V2 α γ) (measurement V3 α γ) := ⟨measurement.Div⟩


-- Addition
noncomputable def measurement.Add [HAdd V1 V2 V3]: measurement V1 α γ → measurement V2 α γ → measurement V3 α γ
| a,b => ⟨a.value+b.value,a.dim+b.dim⟩

noncomputable instance [HAdd V1 V2 V3] : HAdd (measurement V1 α γ) (measurement V2 α γ) (measurement V3 α γ ) := ⟨measurement.Add⟩

-- Subtraction
noncomputable def measurement.Sub [HSub V1 V2 V3]: measurement V1 α γ → measurement V2 α γ → measurement V3 α γ
| a,b => ⟨a.value-b.value,a.dim-b.dim⟩

noncomputable instance [HSub V1 V2 V3] : HSub (measurement V1 α γ) (measurement V2 α γ) (measurement V3 α γ ) := ⟨measurement.Sub⟩

def measurement.Pow {V1 V2 α γ β}  [CommRing γ] [CommRing V1] [CommRing V2]
[HPow V1 β V2] [HPow (dimension α γ) β (dimension α γ)]:
(measurement V1 α γ ) → β → (measurement V2 α γ )
| a,b => ⟨a.value^b,a.dim^b⟩

instance {V1 V2 α γ β} [CommRing γ] [CommRing V1] [CommRing V2]
[HPow V1 β V2] [HPow (dimension α γ) β (dimension α γ)] :
HPow (measurement V1 α γ) β (measurement V2 α γ) := ⟨measurement.Pow⟩
