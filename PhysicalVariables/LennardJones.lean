import PhysicalVariables.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
universe u v
variable {B : Type u} {V : Type v} [Field V]



open PhysicalVariable

structure LJparams (B V) [Field V] [HasBaseLength B] [HasBaseTime B] [HasBaseMass B] where
  (σ ε : PhysicalVariable B V)
  (dimσ : σ.dim = dimension.length B V)
  (dimε : ε.dim = dimension.energy B V)
noncomputable def LJ {B V} [Field V] [HasBaseLength B] [HasBaseTime B] [HasBaseMass B] (p : LJparams B V) (r : PhysicalVariable B V):
  PhysicalVariable B V := 4 • (p.ε * ((p.σ/r)^(12) - (p.σ/r)^6))



theorem LJ_zero_energy {B V} [Field V] [HasBaseLength B] [HasBaseTime B] [HasBaseMass B] (p : LJparams B V) (hσ : p.σ.value ≠ 0) :
  LJ p p.σ = ⟨0,dimension.energy B V⟩ := by
  unfold LJ
  change (4 • (p.ε * ((p.σ / p.σ)^12 - (p.σ / p.σ)^6))) = { value := 0, dim := dimension.energy B V }
  rw [PhysicalVariable.div_self_cancel hσ, PhysicalVariable.one_pow, PhysicalVariable.one_pow,
      ← dimension.one_eq_dimensionless, one_pow, one_pow,PhysicalVariable.sub_def]
  simp
  rw [p.dimε, dimension.energy]
  simp

-- a form that makes it easier to compute the value of LJ, I think. Need to prove it
theorem LJ_eq {B V} [Field V] [HasBaseLength B] [HasBaseTime B] [HasBaseMass B] (p : LJparams B V) {r : PhysicalVariable B V} (hr : r.dim = dimension.length B V) :
  LJ p r = ⟨4*(p.ε.value*((p.σ.value/r.value)^12-(p.σ.value/r.value)^6)),dimension.energy B V⟩ := by
  unfold LJ
  simp
  simp [p.dimε,p.dimσ,hr]

theorem LJ_eq_val {B V} [Field V] [HasBaseLength B] [HasBaseTime B] [HasBaseMass B] (p : LJparams B V) :
  PhysicalVariable.to_val_fun (LJ p) = (fun r => 4*(p.ε.value*((p.σ.value/r)^12-(p.σ.value/r)^6))) := by
  unfold LJ
  unfold PhysicalVariable.to_val_fun
  funext b
  simp


theorem LJ_deriv {B V} [NontriviallyNormedField V] [HasBaseLength B] [HasBaseTime B] [HasBaseMass B]  (p : LJparams B V)
(r : PhysicalVariable B V) (hr0 : r.value ≠ 0) (hr : r.dim = dimension.length B V) : PhysicalVariable.deriv (LJ p) r =  4• (p.ε * (-12•p.σ^12/r^13 + 6•p.σ^6/r^7)) := by
  rw [PhysicalVariable.deriv]
  simp
  constructor
  simp [LJ_eq_val]
  have h : (fun x ↦ (p.σ.value / x) ^ 12) = fun x ↦ (p.σ.value)^12 / (x) ^ 12 := by
    · funext x; rw [div_pow]
  have h2 : (fun x ↦ (p.σ.value / x) ^ 6) = fun x ↦ (p.σ.value)^6 / (x) ^ 6 := by
    · funext x; rw [div_pow]
  rw [deriv_sub, h, h2, deriv_div, deriv_div]
  left; left
  simp [deriv_const, h2]
  field_simp
  · rw [mul_assoc, mul_assoc, pow_two, ← pow_add, ← pow_add, pow_two, ← pow_add, ← pow_add, mul_comm 6 _,
    ← mul_assoc (p.σ.value^6) _ 6, ← pow_add]
    norm_num
    ring_nf
  simp
  simp
  simp [hr0]
  simp
  simp
  simp [hr0]
  simp [h]
  aesop
  aesop
  simp [dimension.derivative]
  unfold PhysicalVariable.to_dim_fun
  unfold LJ
  simp [hr, p.dimσ, p.dimε]
  funext j
  ring_nf
  have h : (fun i ↦ 6 * dimension.length B V i - 7 * dimension.length B V i) = (fun i => -(dimension.length B V i)) := by
    · funext i; ring_nf
  simp [h]
  ring_nf













-- things to add for chem community
-- if epsilon in kcal vs equiv kelvin, who makes sure its right? - show unit conversion
-- vectors/matrices?
-- [length,length,length]
-- [length,mass,force,...]
