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

def measurement.Mul {V1 V2 V3 α γ} [CommRing γ] [HMul V1 V2 V3]
{dim1 dim2 dim3: dimension α γ}
 [DimEq (dim1*dim2) dim3] :
measurement V1 dim1 → measurement V2 dim2 → measurement V3 dim3
  | a,b => ⟨a.value*b.value⟩

instance {V1 V2 V3 α γ} [CommRing γ] [HMul V1 V2 V3]
{dim1 dim2 dim3 : dimension α γ}
[DimEq (dim1*dim2) dim3] :
  HMul (measurement V1 dim1) (measurement V2 dim2) (measurement V3 dim3) := ⟨measurement.Mul⟩

-- Division
def measurement.Div {V1 V2 V3 α γ} [CommRing γ] [HDiv V1 V2 V3]
{dim1 dim2 dim3: dimension α γ}
 [DimEq (dim1/dim2) dim3] :
measurement V1 dim1 → measurement V2 dim2 → measurement V3 dim3
  | a,b => ⟨a.value/b.value⟩

instance {V1 V2 V3 α γ} [CommRing γ] [HDiv V1 V2 V3]
{dim1 dim2 dim3: dimension α γ}
[DimEq (dim1/dim2) dim3] :
  HDiv (measurement V1 dim1) (measurement V2 dim2) (measurement V3 dim3) := ⟨measurement.Div⟩


-- Addition
def measurement.Add {V1 V2 V3 α γ} [CommRing γ] [HAdd V1 V2 V3] {dim1  : dimension α γ} :
measurement V1 dim1 → measurement V2 dim1 → measurement (V3) (dim1)
  | a,b => ⟨a.value+b.value⟩

instance {V1 V2 V3 α γ} [CommRing γ] [HAdd V1 V2 V3] {dim1  : dimension α γ}  :
  HAdd (measurement V1 dim1) (measurement V2 dim1) (measurement V3 (dim1)) := ⟨measurement.Add⟩


-- Subtraction
def measurement.Sub {V1 V2 V3 α γ} [CommRing γ] [HSub V1 V2 V3] {dim1  : dimension α γ} :
measurement V1 dim1 → measurement V2 dim1 → measurement (V3) (dim1)
  | a,b => ⟨a.value-b.value⟩

instance {V1 V2 V3 α γ} [CommRing γ] [HSub V1 V2 V3] {dim1  : dimension α γ}:
  HSub (measurement V1 dim1) (measurement V2 dim1) (measurement V3 (dim1)) := ⟨measurement.Sub⟩



instance {V1 V2 V3 α γ : Type u} [CommRing γ] [HPow V1 V2 V3] [Nonempty V3] {dim1 dim2 : dimension α γ}
: Nonempty (measurement V1 dim1 → V2 → measurement V3 dim2) := by
  simp
  right; right;
  exact PhysicalVariable.instNonemptyMeasurement;




noncomputable def measurement.Pow2 {V1 V2 V3 α γ : Type u}
  [CommRing γ] [HPow V1 V2 V3] [Nonempty V3]
  {dim1 dim2 : dimension α γ}
  [HPow (dimension α γ) V2 (dimension α γ)]  :
  measurement V1 dim1 → V2 → measurement V3 dim2
 := Classical.epsilon $ fun f => ∀ (m1 : measurement V1 dim1) (b : V2), (DimEq (dim1 ^ b) dim2) → f m1 b = ⟨m1.value^b⟩
set_option diagnostics true


noncomputable instance {V1 V2 V3 α γ : Type u}
  [CommRing γ] [HPow V1 V2 V3] [Nonempty V3]
  {dim1 dim2 : dimension α γ}
  [HPow (dimension α γ) V2 (dimension α γ)] :
  HPow (measurement V1 dim1) V2 (measurement V3 dim2) :=
  ⟨measurement.Pow2⟩

#check instHPowMeasurementOfNonemptyOfDimension
variable {V1 V2 V3 α γ : Type u} [CommRing γ] [HPow V1 V2 V3]
  [HPow (dimension α γ) V2 (dimension α γ)]
{dim1 dim2 : dimension α γ} (a : measurement V1 dim1) (b : V2) (c : measurement V3 dim2)
[Nonempty (measurement V1 dim1 → V2 → measurement V3 dim2)] [DimEq (dim1 ^ b) dim2]

#check_failure a^b=c
