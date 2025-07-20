import DimensionalAnalysis.Dimensions

-- Defining physical variables and measurements
namespace PhysicalVariable

structure measurement (V : Type u) {α γ : Type u} [CommRing γ] (dim : dimension α γ) where
  (value : V)
  deriving Inhabited

instance {V} {α} {γ} [inst : Nonempty V] [CommRing γ] {dim1 : dimension α γ} : Nonempty (measurement V dim1) := by
  rw [← exists_true_iff_nonempty]
  use (measurement.mk (Nonempty.some inst));


-- Multiplication

def measurement.Mul {V α γ} [CommRing γ] [Mul V] {dim1 dim2: dimension α γ} :
measurement V dim1 → measurement V dim2 → measurement V (dim1*dim2)
  | a,b => ⟨a.value*b.value⟩

instance {V α γ} [CommRing γ] [Mul V] {dim1 dim2 : dimension α γ}:
  HMul (measurement V dim1) (measurement V dim2) (measurement V (dim1*dim2)) := ⟨measurement.Mul⟩

-- Division
def measurement.Div {V α γ} [CommRing γ] [Div V] {dim1 dim2: dimension α γ} :
measurement V dim1 → measurement V dim2 → measurement V (dim1/dim2)
  | a,b => ⟨a.value/b.value⟩

instance {V α γ} [CommRing γ] [Div V] {dim1 dim2: dimension α γ} :
  HDiv (measurement V dim1) (measurement V dim2) (measurement V (dim1/dim2)) := ⟨measurement.Div⟩

-- Addition
def measurement.Add {V α γ} [CommRing γ] [Add V] {dim1  : dimension α γ} :
measurement V dim1 → measurement V dim1 → measurement (V) (dim1)
  | a,b => ⟨a.value+b.value⟩

instance {V α γ} [CommRing γ] [Add V] {dim1  : dimension α γ}  :
  HAdd (measurement V dim1) (measurement V dim1) (measurement V (dim1)) := ⟨measurement.Add⟩

-- Subtraction
def measurement.Sub {V α γ} [CommRing γ] [Sub V] {dim1  : dimension α γ} :
measurement V dim1 → measurement V dim1 → measurement (V) (dim1)
  | a,b => ⟨a.value-b.value⟩

instance {V α γ} [CommRing γ] [Sub V] {dim1  : dimension α γ}:
  HSub (measurement V dim1) (measurement V dim1) (measurement V (dim1)) := ⟨measurement.Sub⟩

#check
noncomputable def measurement.Pow {V1 V2 V3 α γ : Type u}
  [CommRing γ] [HPow V1 V2 V3] [Nonempty V3]
  {dim1 dim2 : dimension α γ}
  [HPow (dimension α γ) V2 (dimension α γ)] :
  measurement V dim1 → V → measurement V dim2
 :=
