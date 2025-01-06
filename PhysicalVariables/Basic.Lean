import Mathlib.Tactic
import DimensionalAnalysis.Basic
import DimensionalAnalysis.Dimensions
import Mathlib.Data.Real.Basic
universe u u1

-- Defining physical variables and measurements
namespace PhysicalVariable
structure measurement (V) {α : Type*} (dim : dimension α) where
(value : V)



@[coe] def measurementDimensionCoe {V1 α} {dim1 dim2 : dimension α} (hDimEquality : dim1 = dim2): measurement V1 dim1 → measurement V1 dim2 := by
  intro h1
  rw [hDimEquality] at h1
  exact h1

def measurement.Mul {V1 V2 V3} [HMul V1 V2 V3] {α} {dim1 dim2 : dimension α} : measurement V1 dim1 → measurement V2 dim2 → measurement V3 (dim1*dim2)
| a,b => ⟨a.value*b.value⟩

instance {α : Type*} {V1 V2 V3} [HMul V1 V2 V3] {dim1 dim2: dimension α} :
  HMul (measurement V1 dim1) (measurement V2 dim2) (measurement V3 (dim1*dim2)) := ⟨measurement.Mul⟩



variable (β) [HasBaseLength β] (a : measurement ℝ (dimension.length β)) (b : measurement ℝ (dimension.area β)) (c : measurement ℝ (dimension.volume β))
#check a*b=c

theorem test (h: a.value*b.value = c.value): measurement.Mul b a = c := by
  rw [measurement.Mul,h]
  intro h
  rw [mul_comm,dimension.vol_eq_area_mul_length]

def measurement.Add {V1 V2 V3} [HAdd V1 V2 V3] {α} {dim1 : dimension α} : measurement V1 dim1 → measurement V2 dim1 → measurement (V3) (dim1)
| a,b => ⟨a.value+b.value⟩

instance {V1 V2 V3} [HAdd V1 V2 V3] {α} {dim1 : dimension α} : HAdd (measurement V1 dim1) (measurement V2 dim1) (measurement V3 (dim1)) := ⟨measurement.Add⟩





#check a+a
example {V α} {dim : dimension α} {a b : measurement V dim} (h : a.value = b.value) : a = b := by
  cases a
  cases b
  simp
