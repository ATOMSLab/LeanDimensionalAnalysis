import Mathlib.Tactic
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Rank

universe u

/-!
### Dimension type classes
-/
-- Defining each base dimension as a class where systems can chose
--which base dimensions they are considering

-- Here are the seven base dimensions that would be used by ISO:
class HasBaseTime (α : Type u) where
  [dec : DecidableEq α]
  time : α

class HasBaseLength (α : Type u) where
  [dec : DecidableEq α]
  length : α

class HasBaseMass (α : Type u) where
  [dec : DecidableEq α]
  mass : α

class HasBaseAmount (α : Type u) where
  [dec : DecidableEq α]
  amount : α

class HasBaseCurrent (α : Type u) where
  [dec : DecidableEq α]
  current : α

class HasBaseTemperature (α : Type u) where
  [dec : DecidableEq α]
  temperature : α

class HasBaseLuminosity (α : Type u) where
  [dec : DecidableEq α]
  luminosity : α

-- Here is a base dimension for currency
class HasBaseCurrency (α : Type u) where
  [dec : DecidableEq α]
  currency : α

-- This declares decidability as an atribute of each base dimension. Its basically
-- a tag for lean named "instance" and this will automatically confirm decidability
-- each time we use it. This helps speed up and simplify our proofs
attribute [instance] HasBaseTime.dec
attribute [instance] HasBaseLength.dec
attribute [instance] HasBaseMass.dec
attribute [instance] HasBaseAmount.dec
attribute [instance] HasBaseCurrent.dec
attribute [instance] HasBaseTemperature.dec
attribute [instance] HasBaseLuminosity.dec
attribute [instance] HasBaseCurrency.dec


/-!
### Def of dimensions and its properties
-/
-- Here we define a dimension as a mapping of a base dimension to a rational number which is the exponent
-- the base dimension is raised to.
def dimension (α : Type u) := α → ℚ
variable {α}


class DimEq {α} (dim1 : dimension α) (dim2 : outParam (dimension α)) where
(Eq : dim1 = dim2)

instance {α} (dim1 : dimension α) (dim2 : outParam (dimension α)) [inst: DimEq dim1 dim2] : dim1 = dim2 := inst.Eq

namespace dimension
-- The dimensionless dimension is a dimension where all the exponents are zero. It functions as the identity
-- element which is why we relate it to One in the instance function.
def dimensionless (α) : dimension α := Function.const α 0
instance {α} : One (dimension α) := ⟨dimension.dimensionless α⟩
instance {α} : Nonempty (dimension α) := One.instNonempty
noncomputable instance (α : Type u) (a b : dimension α ) : Decidable (a = b) :=
  Classical.propDecidable (a = b)

-- Here we define the algebraic operators (+,-,*,/,^,<) and how they can act on dimensions.

-- Addition and subtraction only work if both dimensions are the same and returns the same dimension
protected noncomputable def add {α}: dimension α → dimension α → dimension α :=
Classical.epsilon $ fun f => ∀ a b, a = b → f a b = a
protected noncomputable def sub {α}: dimension α → dimension α → dimension α :=
Classical.epsilon $ fun f => ∀ a b, a = b → f a b = a

-- For multiplication, all the exponents are added together. For divison, they are subtracted.
protected def mul {α} : dimension α → dimension α → dimension α
| a, b => fun i => a i + b i
protected def div {α} : dimension α → dimension α → dimension α
| a, b => fun i => a i - b i

-- Raising a dimension to a power results in multiplying each exponent by the power.
protected def pow {α} : dimension α → ℚ → dimension α
| a, n => fun i => n * (a i)

-- Inequality operators only work if the dimensions are the same.
protected def le {α} : dimension α → dimension α → Prop
| a, b => ite (a = b) true false
protected def lt {α} : dimension α → dimension α → Prop
| a, b => ite (a = b) true false

-- Here we unify our operator definitions with their respective global class.
noncomputable instance {α} : Add (dimension α) := ⟨dimension.add⟩
noncomputable instance {α} : Sub (dimension α) := ⟨dimension.sub⟩
instance {α} : Mul (dimension α) := ⟨dimension.mul⟩
instance {α} : Div (dimension α) := ⟨dimension.div⟩
instance {α} : Pow (dimension α) ℕ := ⟨fun d n => dimension.pow d n⟩
instance {α} : Pow (dimension α) ℤ := ⟨fun d z => dimension.pow d z⟩
instance {α} : Pow (dimension α) ℚ := ⟨dimension.pow⟩
instance {α} : Inv (dimension α) := ⟨fun d => dimension.pow d (-1)⟩
instance {α} : LT (dimension α) := ⟨dimension.lt⟩
instance {α} : LE (dimension α) := ⟨dimension.le⟩

-- Here we define how derivatives and integrals act on dimensions.
protected def derivative {α} (b : dimension α): dimension α → dimension α := fun a => a / b
protected def integral {α} (b : dimension α): dimension α → dimension α := fun a => a * b

-- Here we define relative operators (exp, sin, log, etc.)
protected noncomputable def relativeOperator {α} : dimension α → dimension α :=
Classical.epsilon $ fun f => ∀ a , a = dimensionless α → f a = dimensionless α

-- Here we prove several helper lemmas which have the simp attribute. These lemmas help
-- simplify our proofs and allow the simp tactic to use these lemmas.
@[simp] lemma add_def {α} (a b : dimension α) : a.add b = a + b := by rfl
@[simp] lemma add_def' {α} (a : dimension α) : a.add a = a := by
  generalize hb : a = b
  nth_rewrite 1 [(symm hb)]
  revert a b hb
  unfold dimension.add
  convert Classical.epsilon_spec ((⟨fun a _ => a, fun _ _ _ => rfl⟩ :
    ∃ (f : dimension α → dimension α → dimension α), ∀ a b, a = b → f a b = a))
  have h : ∀ (a b : dimension α), a = b → b = a := by
    intros a b h
    exact symm h
  apply h _ _
  trivial

@[simp] lemma add_def'' {α} (a : dimension α) : a + a = a := by rw [← add_def, add_def']
@[simp] lemma sub_def {α} (a b : dimension α) : a.sub b = a - b := by rfl
@[simp] lemma sub_def' {α} (a : dimension α) : a.sub a = a := by
  generalize hb : a = b
  nth_rewrite 1 [(symm hb)]
  revert a b hb
  unfold dimension.sub
  convert Classical.epsilon_spec ((⟨fun a _ => a, fun _ _ _ => rfl⟩ :
    ∃ (f : dimension α → dimension α → dimension α), ∀ a b, a = b → f a b = a))
  have h : ∀ (a b : dimension α), a = b → b = a := by
    intros a b h
    exact symm h
  apply h _ _
  trivial

@[simp] lemma sub_def'' {α} (a : dimension α)  : a - a = a := by rw [← sub_def, sub_def']
@[simp] lemma mul_def {α} (a b : dimension α) : a.mul b = a * b := by rfl
@[simp] lemma mul_def' {α} (a b : dimension α) : a * b = fun i => a i + b i := by rfl
@[simp] lemma div_def {α} (a b : dimension α) : a.div b = a / b := by rfl
@[simp] lemma div_def' {α} (a b : dimension α) : a / b = fun i => a i - b i := by rfl
@[simp] lemma pow_def {α} (a : dimension α) (b : ℚ) : a.pow b = a^b := by rfl
@[simp] lemma pow_def' {α} (a : dimension α) (b : ℚ) : a ^ b = fun i => b * (a i):= by rfl
@[simp] lemma npow_def {α} (a : dimension α) (b : ℕ) : a.pow b = a^b := by rfl
@[simp] lemma npow_def' {α} (a : dimension α) (b : ℕ) : a ^ b = fun i => b * (a i):= by rfl
@[simp] lemma zpow_def {α} (a : dimension α) (b : ℤ) : a.pow b = a^b := by rfl
@[simp] lemma zpow_def' {α} (a : dimension α) (b : ℤ) : a ^ b = fun i => b * (a i):= by rfl
@[simp] lemma inv_def {α} (a : dimension α) : a⁻¹ = fun i => (-1 : ℤ) * (a i) := by rfl
@[simp] lemma le_def {α} (a b : dimension α) : a.le b ↔ a ≤ b := by rfl
@[simp] lemma le_def' {α} (a : dimension α) : a ≤ a := by
  rw [← le_def]
  simp only [dimension.le, reduceIte]
@[simp] lemma lt_def {α} (a b : dimension α) : a.lt b ↔ a < b := by rfl
@[simp] lemma lt_def' {α} (a : dimension α) : a < a := by
  rw [← dimension.lt_def]
  simp only [dimension.lt, reduceIte]


@[simp]
lemma one_eq_dimensionless {α} : 1 = dimensionless α := by rfl

@[simp]
lemma dimensionless_def' {α} : dimensionless α = Function.const α 0 := rfl

protected theorem mul_comm {α} (a b : dimension α) : a * b = b * a := by
  simp only [mul_def']
  funext
  rw [add_comm]

protected theorem div_mul_comm {α} (a b c : dimension α) : a / c * b  = b / c * a := by
  simp only [div_def', mul_def']
  funext
  rw [sub_add_comm]

protected theorem mul_assoc {α} (a b c : dimension α) : a * b * c = a * (b * c) := by
  simp only [mul_def']
  funext
  rw [add_assoc]

protected theorem mul_one {α} (a : dimension α) : a * 1 = a := by simp only [one_eq_dimensionless,
  dimensionless_def', Function.const_zero, mul_def', Pi.zero_apply, add_zero]

protected theorem one_mul {α} (a : dimension α) : 1 * a = a := by simp only [one_eq_dimensionless,
  dimensionless_def', Function.const_zero, mul_def', Pi.zero_apply, zero_add]

protected theorem div_eq_mul_inv {α} (a b : dimension α) : a / b = a * b⁻¹ := by
  simp only [div_def', inv_def, Int.reduceNeg, Int.cast_neg, Int.cast_one, neg_mul, one_mul,
    mul_def']
  funext
  rw [sub_eq_add_neg]

protected theorem mul_left_inv {α} (a : dimension α) : a⁻¹ * a = 1 := by
  simp only [inv_def, Int.reduceNeg, Int.cast_neg, Int.cast_one, neg_mul, one_mul, mul_def',
    neg_add_cancel, one_eq_dimensionless, dimensionless_def', Function.const_zero]
  rfl

protected theorem mul_right_inv {α} (a : dimension α) : a * a⁻¹ = 1 := by
  rw [dimension.mul_comm, dimension.mul_left_inv]

protected theorem pow_zero {α} (a : dimension α) : a ^ 0 = 1 := by
  simp only [npow_def', CharP.cast_eq_zero, zero_mul, one_eq_dimensionless, dimensionless_def',
    Function.const_zero]
  rfl

protected theorem pow_succ {α} (a : dimension α) (n : ℕ) : a ^ (n + 1) = a * a^n := by
  simp only [npow_def', Nat.cast_add, Nat.cast_one, mul_def']
  funext
  rw [Rat.add_mul, add_comm, one_mul]

instance {α} : CommGroup (dimension α) where
  mul := dimension.mul
  div := dimension.div
  inv a := dimension.pow a (-1)
  mul_assoc := dimension.mul_assoc
  one := dimensionless α
  npow n a:= dimension.pow a n
  zpow z a:= dimension.pow a z
  one_mul := dimension.one_mul
  mul_one := dimension.mul_one
  mul_comm := dimension.mul_comm
  div_eq_mul_inv a := dimension.div_eq_mul_inv a
  inv_mul_cancel a := dimension.mul_left_inv a
  npow_zero := dimension.pow_zero
  npow_succ n a := by simp; funext x; rw [add_one_mul]
  zpow_neg' _ _ := by simp; rename_i x1 x2; funext x3; ring
  zpow_succ' _ _ := by simp; rename_i x1 x2; funext; rw [add_one_mul]
  zpow_zero' := dimension.pow_zero

/-!
### Other dimensions
-/






/-!
# Buckingham-Pi Theorem
-/

--Converts a list (tuple) of dimensions (the variables) into a matrix of exponent values
def dimensional_matrix {n : ℕ} {α} [Fintype α] (d : Fin n → dimension α)
  (perm : Fin (Fintype.card α) → α) : Matrix (Fin (Fintype.card α)) (Fin n) ℚ :=
    Matrix.of.toFun (fun (a : Fin (Fintype.card α)) (i : Fin n) => d i (perm a))

--Calculates the number of dimensionless parameters possible from a list of dimensions
noncomputable def number_of_dimensionless_parameters {n : ℕ} {α} [Fintype α]
  (d : Fin n → dimension α) (perm : Fin (Fintype.card α) → α) :=
    n - Matrix.rank (dimensional_matrix d perm)

--Calculates the dimensionless parameters from a list of dimensions (not unique)
def dimensionless_numbers_matrix {n : ℕ} {α} [Fintype α] (d : Fin n → dimension α)
  (perm : Fin (Fintype.card α) → α) :=
    LinearMap.ker (Matrix.toLin' (dimensional_matrix d perm))
end dimension
