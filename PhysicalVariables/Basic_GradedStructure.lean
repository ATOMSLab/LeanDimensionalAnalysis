import DimensionalAnalysis.Dimensions
universe u v
-- Defining physical variables and measurements
namespace PhysicalVariable
structure measurement (B : Type u) (V : Type v) [Field V]  where
(value : V)
(dim : dimension B V)


-- Multiplication
protected def measurement.Mul {B : Type u} {V : Type v} [Field V] :
measurement B V →  measurement B V → measurement B V
| a,b => measurement.mk (a.value*b.value) (a.dim*b.dim)

instance {B : Type u} {V : Type v} [Field V] : Mul (measurement B V) := ⟨measurement.Mul⟩

protected def measurement.smul {B : Type u} {V : Type v} [Field V] {M} [SMul M V]: M → measurement B V → measurement B V
| n,a => measurement.mk (n•a.value) (a.dim)

instance {B : Type u} {V : Type v} [Field V] {M} [SMul M V] : SMul M (measurement B V) := ⟨measurement.smul⟩

-- Division
protected def measurement.Div {B : Type u} {V : Type v} [Field V] :
measurement B V →  measurement B V → measurement B V
| a,b => measurement.mk (a.value/b.value) (a.dim/b.dim)

instance {B : Type u} {V : Type v} [Field V] : Div (measurement B V) := ⟨measurement.Div⟩


-- Powers
protected def measurement.Pow {B : Type u} {V : Type v} [Field V] [Pow V V]:
(measurement B V ) → V → (measurement B V )
| a,b => ⟨a.value^b,a.dim^b⟩

instance {B : Type u} {V : Type v} [Field V] [Pow V V]: Pow (measurement B V) V := ⟨measurement.Pow⟩

protected def measurement.NatPow {B : Type u} {V : Type v} [Field V] :
(measurement B V ) → ℕ → (measurement B V )
| a,b => ⟨a.value^b,a.dim^b⟩

instance {B : Type u} {V : Type v} [Field V] : Pow (measurement B V) ℕ := ⟨measurement.NatPow⟩

@[simp] protected lemma mul_def {B : Type u} {V : Type v} [Field V] (a b : measurement B V) : a*b =  ⟨a.value*b.value,a.dim*b.dim⟩ := by rfl
@[simp] protected lemma div_def {B : Type u} {V : Type v} [Field V] (a b : measurement B V) : a/b =  ⟨a.value/b.value,a.dim/b.dim⟩ := by rfl
@[simp] protected lemma pow_def {B : Type u} {V : Type v} [Field V] [Pow V V] (a : measurement B V) (b : V) : a^b =  ⟨a.value^b,a.dim^b⟩ := by rfl
@[simp] protected lemma smul_def {B : Type u} {V : Type v} [Field V] {M} [SMul M V] (a : measurement B V) (n : M) : n•a =  ⟨n•a.value,a.dim⟩ := by rfl

@[simp] protected theorem mul_comm {B : Type u} {V : Type v} [Field V] (a b : measurement B V) : a*b = b*a := by simp; and_intros; rw [mul_comm]; funext; rw [add_comm]
/-
instance {B : Type u} {V : Type v} [Field V] : OfNat (measurement B V) n where
  ofNat := {
    value := n,
    dim   := dimension.dimensionless B V
  }

instance {B V : Type} [Field V] [OfScientific V] : OfScientific (measurement B V) where
  ofScientific := fun (m : Nat) (s : Bool) (e : Nat) =>
    {
      value := OfScientific.ofScientific m s e,
      dim   := dimension.dimensionless B V
    }

-/
-- Subtype of measurements with fixed dimension d. Code level infrastructure
def measurement_of_dim {B : Type u} {V : Type v} [Field V] (d : dimension B V) :=
  { m : measurement B V // m.dim = d } -- The type of all elements m of type measurement B V such that the property m.dim = d holds.

def to_measurement_of_dim {B : Type u} {V : Type v} [Field V] {d : dimension B V} (m : measurement B V) {h : m.dim = d} :
  measurement_of_dim d := ⟨m, h⟩

lemma val_has_expected_dim {B V : Type u} [Field V] {d : dimension B V} (m : measurement_of_dim d) : m.val.dim = d :=
  m.property

lemma subtype_eta {B V : Type u} [Field V] {d : dimension B V} (m : measurement_of_dim d): ⟨m.val, m.property⟩ = m :=
  Subtype.ext rfl

lemma measurement_of_dim.get_value {B : Type u} {V : Type v} [Field V] {d : dimension B V} (v : V) : (⟨⟨v,d⟩, rfl⟩ : (measurement_of_dim d)).val.value = v := by
  simp


-- Addition of fixed dimension measurements
protected def measurement_of_dim.add {B : Type u} {V : Type v} [Field V] {d : dimension B V} :
  measurement_of_dim d → measurement_of_dim d → measurement_of_dim d
| ⟨a, ha⟩, ⟨b, hb⟩ => ⟨{ value := a.value + b.value, dim := a.dim }, ha.trans (by rfl)⟩

instance {B : Type u} {V : Type v} [Field V] {d : dimension B V} : Add (measurement_of_dim d) := ⟨measurement_of_dim.add⟩

-- Subtraction of fixed dimension measurements
protected def measurement_of_dim.sub {B : Type u} {V : Type v} [Field V] {d : dimension B V} :
  measurement_of_dim d → measurement_of_dim d → measurement_of_dim d
| ⟨a, ha⟩, ⟨b, hb⟩ => ⟨{ value := a.value - b.value, dim := a.dim }, ha.trans (by rfl)⟩

instance {B : Type u} {V : Type v} [Field V] {d : dimension B V} : Sub (measurement_of_dim d) := ⟨measurement_of_dim.sub⟩

-- Zero for fixed dimension measurements
protected def measurement_of_dim.zero {B : Type u} {V : Type v} [Field V] {d : dimension B V} : measurement_of_dim d :=
  ⟨⟨0, d⟩, rfl⟩

instance {B : Type u} {V : Type v} [Field V] {d : dimension B V} : Zero (measurement_of_dim d) := ⟨measurement_of_dim.zero⟩

-- One for fixed dimension measurements
protected def measurement_of_dim.one {B : Type u} {V : Type v} [Field V] {d : dimension B V} : measurement_of_dim d :=
  ⟨⟨1, d⟩, rfl⟩

instance {B : Type u} {V : Type v} [Field V] {d : dimension B V} : One (measurement_of_dim d) := ⟨measurement_of_dim.one⟩

-- Negative for fixed dimension measurements
protected def measurement_of_dim.neg {B : Type u} {V : Type v} [Field V] {d : dimension B V} :
  measurement_of_dim d → measurement_of_dim d
| ⟨a, ha⟩ => ⟨⟨-a.value, a.dim⟩, ha⟩

instance {B : Type u} {V : Type v} [Field V] {d : dimension B V} : Neg (measurement_of_dim d) := ⟨measurement_of_dim.neg⟩

-- Multiplication for fixed dimension measurements
protected def measurement_of_dim.mul {B : Type u} {V : Type v} [Field V] {d₁ d₂ : dimension B V} :
  measurement_of_dim d₁ → measurement_of_dim d₂ → measurement_of_dim (d₁ * d₂)
| ⟨a, ha⟩, ⟨b, hb⟩ => ⟨a * b, by rw [←ha, ←hb]; rfl⟩

instance {B : Type u} {V : Type v} [Field V] {d₁ d₂ : dimension B V} : HMul (measurement_of_dim d₁) (measurement_of_dim d₂) (measurement_of_dim (d₁ * d₂)) :=
  ⟨measurement_of_dim.mul⟩

-- Division for fixed dimension measurements
protected def measurement_of_dim.div {B : Type u} {V : Type v} [Field V] {d₁ d₂ : dimension B V}  :
  measurement_of_dim d₁ → measurement_of_dim d₂ → measurement_of_dim (d₁ / d₂)
| ⟨a, ha⟩, ⟨b, hb⟩ => ⟨a / b, by rw [←ha, ←hb]; rfl⟩

instance {B : Type u} {V : Type v} [Field V] {d₁ d₂ : dimension B V}   : HDiv (measurement_of_dim d₁) (measurement_of_dim d₂) (measurement_of_dim (d₁ / d₂)) :=
  ⟨measurement_of_dim.div⟩

--Powers for fixed dimension measurements
protected def measurement_of_dim.pow {B : Type u} {V : Type v} [Field V] [Pow V V] {d : dimension B V} (m : measurement_of_dim d) (n : V) :
  measurement_of_dim (d ^ n) :=
  ⟨m.val ^ n, by
    -- prove that the dimension of (m.val ^ n) is d ^ n
    simp
    funext
    rw [m.property]⟩

instance {B : Type u} {V : Type v} [Field V] [Pow V V] {d : dimension B V} : HPow (measurement_of_dim d) V (measurement B V) :=
  ⟨fun m n => (measurement_of_dim.pow m n).val⟩

protected def measurement_of_dim.inv {B : Type u} {V : Type v} [Field V] [Pow V V] {d : dimension B V} (m : measurement_of_dim d) :
  measurement_of_dim (1/d) :=
  ⟨m.val ^ (-1:V),by simp; funext; rw [m.property]⟩


protected def measurement_of_dim.smul {B : Type u} {V : Type v} [Field V] {M} {d : dimension B V} [SMul M V] : M → (measurement_of_dim d) → (measurement_of_dim d)
| n, ⟨a, ha⟩ => ⟨n•a, by rw [←ha]; rfl⟩

instance {B : Type u} {V : Type v} [Field V] {M} {d : dimension B V} [SMul M V] : SMul M (measurement_of_dim d) := ⟨measurement_of_dim.smul⟩


@[simp] protected lemma measurement_of_dim.add_def {B : Type u} {V : Type v} [Field V] {d : dimension B V} (a b: measurement_of_dim d) : a+b = ⟨{ value := a.val.value + b.val.value, dim := a.val.dim }, a.property.trans (by rfl)⟩ := rfl

@[simp] protected lemma measurement_of_dim.sub_def {B : Type u} {V : Type v} [Field V] {d : dimension B V} (a b: measurement_of_dim d) : a-b = ⟨{ value := a.val.value - b.val.value, dim := a.val.dim }, a.property.trans (by rfl)⟩ := rfl

@[simp] protected lemma measurement_of_dim.mul_def {B : Type u} {V : Type v} [Field V] {d1 d2 : dimension B V} (a : measurement_of_dim d1) (b : measurement_of_dim d2) : a*b = ⟨a.val * b.val, by simp; funext; rw [a.property, b.property]⟩ := rfl

@[simp] protected lemma measurement_of_dim.div_def {B : Type u} {V : Type v} [Field V]   {d1 d2 : dimension B V} (a : measurement_of_dim d1) (b : measurement_of_dim d2) : a/b = ⟨a.val / b.val, by simp; funext; rw [a.property, b.property]⟩ := rfl

@[simp] protected lemma measurement_of_dim.zero_def {B : Type u} {V : Type v} [Field V] {d : dimension B V} : measurement_of_dim.zero = (0 : measurement_of_dim d) := rfl

@[simp] protected lemma measurement_of_dim.zero_dim {B : Type u} {V : Type v} [Field V] {d : dimension B V} : (0 : measurement_of_dim d).val.dim = d := rfl

@[simp] protected lemma measurement_of_dim.smul_def {B : Type u} {V : Type v} [Field V] {M} [SMul M V] {d : dimension B V} (n : M) (a : measurement_of_dim d): n•a =  ⟨n•a.val, by simp; rw [a.property] ⟩:= rfl

protected theorem measurement_of_dim.add_assoc {B : Type u} {V : Type v} [Field V] {d : dimension B V} (a b c : measurement_of_dim d) : a+b+c = a+(b+c) := by
  simp
  congr 2
  rw [add_assoc]

protected theorem measurement_of_dim.add_comm {B : Type u} {V : Type v} [Field V] {d : dimension B V} (a b: measurement_of_dim d) : a + b = b + a:= by
  simp
  congr 2
  rw [add_comm]
  rw [a.property,b.property]

protected theorem measurement_of_dim.sub_eq_add_neg {B : Type u} {V : Type v} [Field V] {d : dimension B V} (a b: measurement_of_dim d) : a - b = a + -b:= by
  simp
  congr 2
  rw [sub_eq_add_neg]
  rfl

protected theorem measurement_of_dim.neg_add_cancel {B : Type u} {V : Type v} [Field V] {d : dimension B V} (a : measurement_of_dim d) : -a+a = 0 := by
  rw [measurement_of_dim.add_comm, ← measurement_of_dim.sub_eq_add_neg]
  simp
  congr
  rw [a.property]

protected theorem measurement_of_dim.zero_add {B : Type u} {V : Type v} [Field V] {d : dimension B V} (a : measurement_of_dim d) : 0 + a = a := by
  simp
  congr 2
  simp
  rfl
  rw [a.property];

protected theorem measurement_of_dim.add_zero {B : Type u} {V : Type v} [Field V] {d : dimension B V} (a : measurement_of_dim d) : a + 0 = a := by rw [measurement_of_dim.add_comm,measurement_of_dim.zero_add]

protected theorem measurement_of_dim.nsmul_zero {B : Type u} {V : Type v} [Field V] {d : dimension B V} (a : measurement_of_dim d) : 0•a = 0 := by
  simp
  rw [← measurement_of_dim.zero_def, measurement_of_dim.zero]
  congr
  rw [a.property]

protected theorem measurement_of_dim.nsmul_succ {B : Type u} {V : Type v} [Field V] {d : dimension B V} (n : ℕ) (a : measurement_of_dim d) : (n+1)•a = n•a+a := by
  induction n
  simp
  simp
  congr
  rw [add_one_mul]

protected theorem measurement_of_dim.zsmul_zero {B : Type u} {V : Type v} [Field V] {d : dimension B V} (a : measurement_of_dim d) : (0:ℤ)•a = 0 := by
  simp
  rw [← measurement_of_dim.zero_def, measurement_of_dim.zero]
  congr
  rw [a.property]

protected theorem measurement_of_dim.zsmul_succ {B : Type u} {V : Type v} [Field V] {d : dimension B V} (n : ℕ) (a : measurement_of_dim d) : ((n.succ):ℤ)•a = (n:ℤ)•a+a := by
  induction n
  simp
  simp
  congr
  rw [add_one_mul]

protected theorem measurement_of_dim.zsmul_neg {B : Type u} {V : Type v} [Field V] {d : dimension B V} (n : ℕ) (a : measurement_of_dim d) : ((Int.negSucc n))• a = -(((n.succ):ℤ)•a) := by
  induction n
  simp
  congr
  simp
  congr
  ring_nf


instance mul_dimensionless_left {B : Type u} {V : Type v} [Field V] {d : dimension B V} :
  HMul (measurement_of_dim d) (measurement_of_dim (dimension.dimensionless B V)) (measurement_of_dim d) :=
⟨fun x y => ⟨x.val * y.val, by simp [x.property, y.property]⟩⟩

instance div_self {B : Type u} {V : Type v} [Field V]   {d : dimension B V} :
  HDiv (measurement_of_dim d) (measurement_of_dim d) (measurement_of_dim (dimension.dimensionless B V)) :=
⟨fun x y => ⟨x.val / y.val, by simp [x.property, y.property]⟩⟩

protected theorem measurement_of_dim.div_self_cancel {B : Type u} {V : Type v} [Field V] {d : dimension B V} (a : measurement_of_dim d) (h : a.val.value ≠ 0): a/a = (1 : measurement_of_dim (dimension.dimensionless B V)) := by
  simp [div_self]
  congr 2
  rw [div_eq_mul_inv, mul_inv_cancel₀ h]

protected def measurement_of_dim.dim_cast {B : Type u} {V : Type v} [Field V] {d1 d2 : dimension B V} (h : d1 = d2) : (measurement_of_dim d1) → (measurement_of_dim d2)
| a => ⟨a.val, by rw [a.property]; funext; rw [h]⟩

instance {B : Type u} {V : Type v} [Field V] {d1 d2 : dimension B V}  : Coe (measurement_of_dim (d1*d2)) (measurement_of_dim (d2*d1)) where
coe := measurement_of_dim.dim_cast (dimension.mul_comm d1 d2)


protected theorem measurement_of_dim.mul_comm {B : Type u} {V : Type v} [inst1 : Field V] {d1 d2 : dimension B V}
(a : measurement_of_dim d1) (b : measurement_of_dim d2) : (a*b) = (b*a) := by
  -- unfold multiplication on both sides
  rw [measurement_of_dim.mul_def,measurement_of_dim.mul_def]
  simp [measurement_of_dim.dim_cast]
  congr 2
  rw [mul_comm]
  funext i
  rw [add_comm]




instance {B : Type u} {V : Type v} [Field V] {d : dimension B V} : AddCommGroup (measurement_of_dim d) where
  add := measurement_of_dim.add
  add_assoc := measurement_of_dim.add_assoc
  zero := measurement_of_dim.zero
  zero_add := measurement_of_dim.zero_add
  add_zero := measurement_of_dim.add_zero
  add_comm := measurement_of_dim.add_comm
  nsmul := measurement_of_dim.smul
  nsmul_zero := measurement_of_dim.nsmul_zero
  nsmul_succ := measurement_of_dim.nsmul_succ
  neg := measurement_of_dim.neg
  sub := measurement_of_dim.sub
  zsmul := measurement_of_dim.smul
  zsmul_zero' := measurement_of_dim.zsmul_zero
  zsmul_succ' := measurement_of_dim.zsmul_succ
  zsmul_neg' := measurement_of_dim.zsmul_neg
  sub_eq_add_neg := measurement_of_dim.sub_eq_add_neg
  neg_add_cancel := measurement_of_dim.neg_add_cancel

end PhysicalVariable

/-!
### Units
-/
namespace Units

def casesium133GroundStateHyperfineOscillationDuration {B : Type u} {V : Type v} [Field V] [HasBaseTime B] :
PhysicalVariable.measurement_of_dim (dimension.time B V) := ⟨⟨1, dimension.time B V⟩,rfl⟩

def second (B : Type u) (V : Type v) [Field V] [HasBaseTime B] : PhysicalVariable.measurement_of_dim (dimension.time B V) := 9192631770•casesium133GroundStateHyperfineOscillationDuration

def meter (B : Type u) (V : Type v) [Field V] [HasBaseLength B] : PhysicalVariable.measurement_of_dim (dimension.length B V) := ⟨⟨1, dimension.length B V⟩, rfl⟩

def kilogram (B : Type u) (V : Type v) [Field V] [HasBaseMass B] : PhysicalVariable.measurement_of_dim (dimension.mass B V) := ⟨⟨1, dimension.mass B V⟩, rfl⟩

def ampere (B : Type u) (V : Type v) [Field V] [HasBaseCurrent B] : PhysicalVariable.measurement_of_dim (dimension.current B V) := ⟨⟨1, dimension.current B V⟩, rfl⟩

def kelvin (B : Type u) (V : Type v) [Field V] [HasBaseTemperature B] : PhysicalVariable.measurement_of_dim (dimension.temperature B V) :=
  ⟨⟨1, dimension.temperature B V⟩, rfl⟩

def mole (B : Type u) (V : Type v) [Field V] [HasBaseAmount B] : PhysicalVariable.measurement_of_dim (dimension.amount B V) :=
  ⟨⟨1, dimension.amount B V⟩, rfl⟩

def candela (B : Type u) (V : Type v) [Field V] [HasBaseLuminosity B] : PhysicalVariable.measurement_of_dim (dimension.luminosity B V) :=
  ⟨⟨1, dimension.luminosity B V⟩, rfl⟩

def SpeedOfLight (B : Type u) (V : Type v) [Field V]   [HasBaseLength B] [HasBaseTime B] : PhysicalVariable.measurement_of_dim (dimension.length B V / dimension.time B V) :=
  299792458 • meter B V/second B V

def PlancksConstant (B : Type u) (V : Type v) [Field V] [HasBaseLength B] [HasBaseTime B] [HasBaseMass B] [Pow V V]   [SMul Float V]:
  PhysicalVariable.measurement_of_dim (dimension.mass B V * dimension.length B V ^ (2 : V) / dimension.time B V) :=
  6.62607015e-34•(kilogram B V * (meter B V).pow 2 / second B V)

def ElementaryCharge (B : Type u) (V : Type v) [Field V] [HasBaseCurrent B] [HasBaseTime B] [SMul Float V]:
  PhysicalVariable.measurement_of_dim (dimension.current B V * dimension.time B V) :=
  1.602176634e-19 • (ampere B V * second B V)

def BoltzmannConstant (B : Type u) (V : Type v) [Field V]
  [HasBaseLength B] [HasBaseTime B] [HasBaseTemperature B] [Pow V V]   [SMul Float V]:
  PhysicalVariable.measurement_of_dim (dimension.length B V ^ 2 / (dimension.time B V ^ 2 * dimension.temperature B V))  :=
  1.380649e-23 • ((meter B V).pow 2 / ((second B V).pow 2 * kelvin B V))

def AvogadrosNumber (B : Type u) (V : Type v) [Field V] [HasBaseAmount B] [Pow V V] [SMul Float V]:
  PhysicalVariable.measurement_of_dim ((dimension.amount B V) ⁻¹) :=
  6.02214076e23 • (mole B V).pow (-1)

def steradian (B : Type u) (V : Type v) [Field V] [HasBaseLength B] [Pow V V]  :
  PhysicalVariable.measurement_of_dim (dimension.dimensionless B V) :=
  1 • (meter B V).pow 2 / (meter B V).pow 2

-- redone once you define EM spectrum
def MonochromaticRadiation540THz (B : Type u) (V : Type v) [Field V] [Pow V V]
  [HasBaseLength B] [HasBaseTime B] [HasBaseMass B] [HasBaseLuminosity B] :
  PhysicalVariable.measurement_of_dim (dimension.luminosity B V / (dimension.mass B V * dimension.length B V ^ 2 * dimension.time B V ^ 3)) :=
  683 • (candela B V* steradian B V / (kilogram B V * (meter  B V).pow 2 * (second B V).pow 3))

def centimeter (B : Type u) (V : Type v) [Field V] [HasBaseLength B] :
  PhysicalVariable.measurement_of_dim (dimension.length B V) :=
  (1/100)•meter B V

def inch (B : Type u) (V : Type v) [Field V] [HasBaseLength B] :
  PhysicalVariable.measurement_of_dim (dimension.length B V) :=
  (100/254) • centimeter B V

def millisecond (B : Type u) (V : Type v) [Field V] [HasBaseTime B] :
  PhysicalVariable.measurement_of_dim (dimension.time B V) :=
  (1/100) • second B V
