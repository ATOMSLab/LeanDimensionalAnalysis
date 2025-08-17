import DimensionalAnalysis.Dimensions
universe u v
-- Defining physical variables and PhysicalVariables

structure PhysicalVariable (B : Type u) (V : Type v) [Field V]  where
(value : V)
(dim : dimension B V)
namespace PhysicalVariable
-- Addition
protected noncomputable def Add {B : Type u} {V : Type v} [Field V] :
PhysicalVariable B V →  PhysicalVariable B V → PhysicalVariable B V
| a,b => PhysicalVariable.mk (a.value+b.value) (a.dim+b.dim)

noncomputable instance {B : Type u} {V : Type v} [Field V] : Add (PhysicalVariable B V) := ⟨PhysicalVariable.Add⟩

-- Subtraction
protected noncomputable def Sub {B : Type u} {V : Type v} [Field V] :
PhysicalVariable B V →  PhysicalVariable B V → PhysicalVariable B V
| a,b => PhysicalVariable.mk (a.value-b.value) (a.dim-b.dim)

noncomputable instance {B : Type u} {V : Type v} [Field V] : Sub (PhysicalVariable B V) := ⟨PhysicalVariable.Sub⟩

-- Multiplication
protected def Mul {B : Type u} {V : Type v} [Field V] :
PhysicalVariable B V →  PhysicalVariable B V → PhysicalVariable B V
| a,b => PhysicalVariable.mk (a.value*b.value) (a.dim*b.dim)

instance {B : Type u} {V : Type v} [Field V] : Mul (PhysicalVariable B V) := ⟨PhysicalVariable.Mul⟩

protected def smul {B : Type u} {V : Type v} [Field V] {M} [SMul M V]: M → PhysicalVariable B V → PhysicalVariable B V
| n,a => PhysicalVariable.mk (n•a.value) (a.dim)

instance {B : Type u} {V : Type v} [Field V] {M} [SMul M V] : SMul M (PhysicalVariable B V) := ⟨PhysicalVariable.smul⟩

-- Division
protected def Div {B : Type u} {V : Type v} [Field V] :
PhysicalVariable B V →  PhysicalVariable B V → PhysicalVariable B V
| a,b => PhysicalVariable.mk (a.value/b.value) (a.dim/b.dim)

instance {B : Type u} {V : Type v} [Field V] : Div (PhysicalVariable B V) := ⟨PhysicalVariable.Div⟩

-- Powers
protected def Pow {B : Type u} {V : Type v} [Field V] [Pow V V]:
(PhysicalVariable B V ) → V → (PhysicalVariable B V )
| a,b => ⟨a.value^b,a.dim^b⟩

instance {B : Type u} {V : Type v} [Field V] [Pow V V]: Pow (PhysicalVariable B V) V := ⟨PhysicalVariable.Pow⟩

protected def NatPow {B : Type u} {V : Type v} [Field V] :
(PhysicalVariable B V ) → ℕ → (PhysicalVariable B V )
| a,b => ⟨a.value^b,a.dim^b⟩

instance {B : Type u} {V : Type v} [Field V] : Pow (PhysicalVariable B V) ℕ := ⟨PhysicalVariable.NatPow⟩

protected def IntPow {B : Type u} {V : Type v} [Field V] :
(PhysicalVariable B V ) → ℤ → (PhysicalVariable B V )
| a,b => ⟨a.value^b,a.dim^b⟩

instance {B : Type u} {V : Type v} [Field V] : Pow (PhysicalVariable B V) ℤ := ⟨PhysicalVariable.IntPow⟩

-- Neg
protected def Neg {B : Type u} {V : Type v} [Field V] :
PhysicalVariable B V →  PhysicalVariable B V
| a => PhysicalVariable.mk (-a.value) (a.dim)

instance {B : Type u} {V : Type v} [Field V] : Neg (PhysicalVariable B V) := ⟨PhysicalVariable.Neg⟩
-- Zero
protected def Zero {B : Type u} {V : Type v} [Field V] (d : dimension B V) :
PhysicalVariable B V := PhysicalVariable.mk 0 d

instance {B : Type u} {V : Type v} [Field V] {d : dimension B V} : Zero (PhysicalVariable B V) := ⟨PhysicalVariable.Zero d⟩

-- One
protected def One {B : Type u} {V : Type v} [Field V] (d : dimension B V) :
PhysicalVariable B V := PhysicalVariable.mk 1 d

instance {B : Type u} {V : Type v} [Field V] {d : dimension B V} : One (PhysicalVariable B V) := ⟨PhysicalVariable.One d⟩

protected def to_val_fun {B : Type u} {V : Type v} [Field V] (f : PhysicalVariable B V → PhysicalVariable B V) : V → V
| a => (f ⟨a,dimension.dimensionless B V⟩).value

protected def to_dim_fun {B : Type u} {V : Type v} [Field V] (f : PhysicalVariable B V → PhysicalVariable B V) : (dimension B V) → (dimension B V)
| d => (f ⟨0,d⟩).dim

protected def deriv {B : Type u} {V : Type v} [NontriviallyNormedField V] (f : PhysicalVariable B V → PhysicalVariable B V)
(x : PhysicalVariable B V) : PhysicalVariable B V :=
  let val' := deriv (PhysicalVariable.to_val_fun f) x.value
  let dim' := dimension.derivative (PhysicalVariable.to_dim_fun f) x.dim
  ⟨val', dim'⟩


-- helper lemmas for the definitions
@[simp] protected lemma add_def {B : Type u} {V : Type v} [Field V] (a b : PhysicalVariable B V) : a+b =  ⟨a.value+b.value,a.dim+b.dim⟩ := by rfl
@[simp] protected lemma sub_def {B : Type u} {V : Type v} [Field V] (a b : PhysicalVariable B V) : a-b =  ⟨a.value-b.value,a.dim-b.dim⟩ := by rfl
@[simp] protected lemma mul_def {B : Type u} {V : Type v} [Field V] (a b : PhysicalVariable B V) : a*b =  ⟨a.value*b.value,a.dim*b.dim⟩ := by rfl
@[simp] protected lemma div_def {B : Type u} {V : Type v} [Field V] (a b : PhysicalVariable B V) : a/b =  ⟨a.value/b.value,a.dim/b.dim⟩ := by rfl
@[simp] protected lemma pow_def {B : Type u} {V : Type v} [Field V] [Pow V V] (a : PhysicalVariable B V) (b : V) : a^b =  ⟨a.value^b,a.dim^b⟩ := by rfl
@[simp] protected lemma pow_def_nat {B : Type u} {V : Type v} [Field V]  (a : PhysicalVariable B V) (b : ℕ) : a^b =  ⟨a.value^b,a.dim^b⟩ := by rfl
@[simp] protected lemma smul_def {B : Type u} {V : Type v} [Field V] {M} [SMul M V] (a : PhysicalVariable B V) (n : M) : n•a =  ⟨n•a.value,a.dim⟩ := by rfl
@[simp] protected lemma neg_def {B : Type u} {V : Type v} [Field V] (a : PhysicalVariable B V) : -a =  ⟨-a.value,a.dim⟩ := by rfl
@[simp] protected lemma value_def {B : Type u} {V : Type v} [Field V] (v : V) {d : dimension B V}: (⟨v,d⟩ : PhysicalVariable B V).value = v := by simp
-- core theorems
protected theorem mul_comm {B : Type u} {V : Type v} [Field V] (a b : PhysicalVariable B V) : a*b = b*a := by simp; and_intros; rw [mul_comm]; funext; rw [add_comm]

protected theorem add_assoc {B : Type u} {V : Type v} [Field V] {a b c : PhysicalVariable B V} (h1 : a.dim = b.dim) (h2 : b.dim = c.dim): a+b+c = a+(b+c) := by
  simp
  constructor
  ring_nf
  simp [h1, h2]


protected theorem add_comm {B : Type u} {V : Type v} [Field V] {a b:  PhysicalVariable B V} (h1 : a.dim = b.dim):
  a + b = b + a:= by
  simp
  constructor
  rw [add_comm]
  simp [h1]

-- Suprisingly, this doesn't require a.dim = b.dim. I think its because subtraction and additions of dimension are equivalent so they can be exchange
protected theorem sub_eq_add_neg {B : Type u} {V : Type v} [Field V] (a b:  PhysicalVariable B V) :
  a - b = a + -b:= by
  simp
  constructor
  rw [sub_eq_add_neg]
  rfl

protected theorem neg_add_cancel {B : Type u} {V : Type v} [Field V] (a :  PhysicalVariable B V) :
  -a+a = ⟨0,a.dim⟩ := by
  rw [PhysicalVariable.add_comm, ← PhysicalVariable.sub_eq_add_neg]
  simp
  simp

protected theorem zero_add {B : Type u} {V : Type v} [Field V] (a :  PhysicalVariable B V) :
  ⟨0,a.dim⟩ + a = a := by simp

protected theorem add_zero {B : Type u} {V : Type v} [Field V] (a :  PhysicalVariable B V) :
  a + ⟨0,a.dim⟩ = a := by simp

protected theorem nsmul_zero {B : Type u} {V : Type v} [Field V] (a :  PhysicalVariable B V) :
  0•a = ⟨0,a.dim⟩ := by simp

protected theorem nsmul_succ {B : Type u} {V : Type v} [Field V]  (n : ℕ) (a :  PhysicalVariable B V) :
  (n+1)•a = n•a+a := by
  induction n
  simp
  simp
  rw [add_one_mul]

protected theorem zsmul_zero {B : Type u} {V : Type v} [Field V] (a :  PhysicalVariable B V) :
  (0:ℤ)•a = ⟨0,a.dim⟩ := by simp

protected theorem zsmul_succ {B : Type u} {V : Type v} [Field V] (n : ℕ) (a : PhysicalVariable B V) :
  ((n.succ):ℤ)•a = (n:ℤ)•a+a := by
  induction n
  simp
  simp
  rw [add_one_mul]

protected theorem zsmul_neg {B : Type u} {V : Type v} [Field V] (n : ℕ) (a : PhysicalVariable B V) : ((Int.negSucc n))• a = -(((n.succ):ℤ)•a) := by
  induction n
  simp
  simp
  ring_nf

protected theorem div_self_cancel {B : Type u} {V : Type v} [Field V] {a : PhysicalVariable B V} (h : a.value ≠ 0):
  a/a = ⟨1,dimension.dimensionless B V⟩ := by
  simp [dimension.one_eq_dimensionless]
  rw [div_eq_mul_inv, mul_inv_cancel₀ h]

protected theorem one_pow {B : Type u} {V : Type v} [Field V] (d : dimension B V) (n : ℕ):
 (⟨1,d⟩ : PhysicalVariable B V)^n = ⟨1,d^n⟩ := by simp


end PhysicalVariable

/-!
### Units
-/
namespace Units

def casesium133GroundStateHyperfineOscillationDuration (B : Type u) (V : Type v) [Field V] [HasBaseTime B] :
  PhysicalVariable B V := ⟨1, dimension.time B V⟩

def second (B : Type u) (V : Type v) [Field V] [HasBaseTime B] :
  PhysicalVariable B V := 9192631770•casesium133GroundStateHyperfineOscillationDuration B V

def meter (B : Type u) (V : Type v) [Field V] [HasBaseLength B] :
  PhysicalVariable B V := ⟨1, dimension.length B V⟩

def kilogram (B : Type u) (V : Type v) [Field V] [HasBaseMass B] :
  PhysicalVariable B V := ⟨1, dimension.mass B V⟩

def ampere (B : Type u) (V : Type v) [Field V] [HasBaseCurrent B] :
  PhysicalVariable B V := ⟨1, dimension.current B V⟩

def kelvin (B : Type u) (V : Type v) [Field V] [HasBaseTemperature B] :
  PhysicalVariable B V := ⟨1, dimension.temperature B V⟩

def mole (B : Type u) (V : Type v) [Field V] [HasBaseAmount B] :
  PhysicalVariable B V := ⟨1, dimension.amount B V⟩

def candela (B : Type u) (V : Type v) [Field V] [HasBaseLuminosity B] :
  PhysicalVariable B V := ⟨1, dimension.luminosity B V⟩

def SpeedOfLight (B : Type u) (V : Type v) [Field V]   [HasBaseLength B] [HasBaseTime B] :
  PhysicalVariable B V := 299792458 • meter B V/second B V

def PlancksConstant (B : Type u) (V : Type v) [Field V] [HasBaseLength B] [HasBaseTime B] [HasBaseMass B] [Pow V V] [SMul Float V]:
  PhysicalVariable B V := 6.62607015e-34•(kilogram B V * (meter B V)^ (2 : V) / second B V)

def ElementaryCharge (B : Type u) (V : Type v) [Field V] [HasBaseCurrent B] [HasBaseTime B] [SMul Float V]:
  PhysicalVariable B V := 1.602176634e-19 • (ampere B V * second B V)

def BoltzmannConstant (B : Type u) (V : Type v) [Field V]
  [HasBaseLength B] [HasBaseTime B] [HasBaseTemperature B] [Pow V V] [SMul Float V] :
  PhysicalVariable B V := 1.380649e-23 • ((meter B V)^(2:V) / ((second B V)^(2:V) * kelvin B V))

def AvogadrosNumber (B : Type u) (V : Type v) [Field V] [HasBaseAmount B] [Pow V V] [SMul Float V]:
  PhysicalVariable B V := 6.02214076e23 • (mole B V)^(-1:V)

def steradian (B : Type u) (V : Type v) [Field V] [HasBaseLength B] [Pow V V] :
  PhysicalVariable B V := 1 • (meter B V)^(2:V) / (meter B V)^(2:V)

-- redo once you define EM spectrum
def MonochromaticRadiation540THz (B : Type u) (V : Type v) [Field V] [Pow V V]
  [HasBaseLength B] [HasBaseTime B] [HasBaseMass B] [HasBaseLuminosity B] :
  PhysicalVariable B V := 683 • (candela B V* steradian B V / (kilogram B V * (meter  B V)^(2:V) * (second B V)^(3:V)))

def centimeter (B : Type u) (V : Type v) [Field V] [HasBaseLength B] :
  PhysicalVariable B V := (1/100)•meter B V

def inch (B : Type u) (V : Type v) [Field V] [HasBaseLength B] :
  PhysicalVariable B V := (100/254) • centimeter B V

def millisecond (B : Type u) (V : Type v) [Field V] [HasBaseTime B] :
  PhysicalVariable B V := (1/100) • second B V
