import DimensionalAnalysis.Dimensions

variable {α} [HasBaseLength α] [HasBaseTime α] [HasBaseMass α]
open dimension
theorem accel_eq_del_div_time : acceleration α = velocity α / time α := by
  rw[acceleration,velocity,pow_two,div_div]

theorem reynolds_eq_dimless : reynolds_number α = dimensionless α ℤ := by
  rw [reynolds_number,mass_density,volume,velocity,dynamic_viscocity, ← one_eq_dimensionless, div_eq_one]
  rw [mul_assoc,mul_comm (length α/time α),mul_div,pow_three,
  ← mul_div_assoc,mul_comm,← mul_div_assoc,mul_comm _ (length α * length α), mul_div_mul_comm,
  ← div_one (length α * length α),div_div_div_cancel_left,div_one,one_mul,div_div]
