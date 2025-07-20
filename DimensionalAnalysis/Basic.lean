import Mathlib.Tactic
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Rank

universe u v

/-!
### Dimension type classes
-/
-- Defining each base dimension as a class where systems can chose
--which base dimensions they are considering

-- Here are the seven base dimensions that would be used by ISO:
class HasBaseTime (α : Type u) where
  [dec : DecidableEq α]
  Time : α

class HasBaseLength (α : Type u) where
  [dec : DecidableEq α]
  Length : α

class HasBaseMass (α : Type u) where
  [dec : DecidableEq α]
  Mass : α

class HasBaseAmount (α : Type u) where
  [dec : DecidableEq α]
  Amount : α

class HasBaseCurrent (α : Type u) where
  [dec : DecidableEq α]
  Current : α

class HasBaseTemperature (α : Type u) where
  [dec : DecidableEq α]
  Temperature : α

class HasBaseLuminosity (α : Type u) where
  [dec : DecidableEq α]
  Luminosity : α

-- Here is a base dimension for currency
class HasBaseCurrency (α : Type u) where
  [dec : DecidableEq α]
  Currency : α

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
-- Here we define a dimension as a mapping of a base dimension to a number which is the exponent
-- the base dimension is raised to.
def dimension (α : Type u) (γ : Type v) [CommRing γ] := α → γ

class DimEq {α γ} [CommRing γ] (dim1 : dimension α γ) (dim2 : semiOutParam (dimension α γ)) where
(Eq : dim1 = dim2)

instance {α γ1 γ2} [CommRing γ1] [CommRing γ2] [Coe γ1 γ2] : Coe (dimension α γ1) (dimension α γ2) where
coe :=  fun f => fun x => (f x : γ2)

namespace dimension

-- The dimensionless dimension is a dimension where all the exponents are zero. It functions as the identity
-- element which is why we relate it to One in the instance function.
def dimensionless (α : Type u) (γ : Type v) [CommRing γ] : dimension α γ := Function.const α 0
instance (α : Type u) (γ : Type v)[CommRing γ] : One (dimension α γ) := ⟨dimension.dimensionless α γ⟩
instance (α : Type u) (γ : Type v) [CommRing γ] : Nonempty (dimension α γ) := One.instNonempty
noncomputable instance (α : Type u) (γ : Type v) [CommRing γ] (a b : dimension α γ ) : Decidable (a = b) :=
  Classical.propDecidable (a = b)

-- Here we define the algebraic operators (+,-,*,/,^,<) and how they can act on dimensions.

-- Addition and subtraction only work if both dimensions are the same and returns the same dimension
variable {α : Type u} {γ : Type v} [CommRing γ]

protected noncomputable def add : dimension α γ → dimension α γ → dimension α γ :=
Classical.epsilon $ fun f => ∀ a b, a = b → f a b = a
protected noncomputable def sub : dimension α γ → dimension α γ → dimension α γ :=
Classical.epsilon $ fun f => ∀ a b, a = b → f a b = a

-- For multiplication, all the exponents are added together. For divison, they are subtracted.
protected def mul  : dimension α γ → dimension α γ → dimension α γ
| a, b => fun i => a i + b i
protected def div  : dimension α γ → dimension α γ → dimension α γ
| a, b => fun i => a i - b i

-- Raising a dimension to a power results in multiplying each exponent by the power.

protected def pow {γ} [CommRing γ]: dimension α γ → γ → dimension α γ
| a, n => fun i => n * (a i)

-- Inequality operators only work if the dimensions are the same.
protected def le  : dimension α γ → dimension α γ → Prop
| a, b => ite (a = b) true false
protected def lt  : dimension α γ → dimension α γ → Prop
| a, b => ite (a = b) true false

-- Here we unify our operator definitions with their respective global class.
noncomputable instance  : Add (dimension α γ) := ⟨dimension.add⟩
noncomputable instance  : Sub (dimension α γ) := ⟨dimension.sub⟩
instance  : Mul (dimension α γ) := ⟨dimension.mul⟩
instance  : Div (dimension α γ) := ⟨dimension.div⟩
instance  {γ} [CommRing γ] : HPow (dimension α γ) γ (dimension α γ) := ⟨dimension.pow⟩
instance : Pow (dimension α γ) γ := ⟨dimension.pow⟩
instance  : Inv (dimension α γ) := ⟨fun d => d^(-1:γ)⟩
instance  : LT (dimension α γ) := ⟨dimension.lt⟩
instance  : LE (dimension α γ) := ⟨dimension.le⟩

instance {γ1 γ2} [CommRing γ1] [CommRing γ2] [Coe γ1 γ2]: HPow (dimension α γ1) γ2 (dimension α γ2) where
  hPow
  | a, n => dimension.pow (a : (dimension α γ2)) n

-- Here we define how derivatives and integrals act on dimensions.
protected def derivative  (b : dimension α γ): dimension α γ → dimension α γ := fun a => a / b
protected def integral  (b : dimension α γ): dimension α γ → dimension α γ := fun a => a * b

-- Here we define relative operators (exp, sin, log, etc.)
protected noncomputable def relativeOperator  : dimension α γ → dimension α γ :=
Classical.epsilon $ fun Operator => ∀ dim , dim = 1 → Operator dim = 1

-- Here we prove several helper lemmas which have the simp attribute. These lemmas help
-- simplify our proofs and allow the simp tactic to use these lemmas.
@[simp] lemma add_def  (a b : dimension α γ) : a.add b = a + b := by rfl
@[simp] lemma add_def'  (a : dimension α γ) : a.add a = a := by
  generalize hb : a = b
  nth_rewrite 1 [(symm hb)]
  revert a b hb
  unfold dimension.add
  convert Classical.epsilon_spec ((⟨fun a _ => a, fun _ _ _ => rfl⟩ :
    ∃ (f : dimension α γ → dimension α γ → dimension α γ), ∀ a b, a = b → f a b = a))
  have h : ∀ (a b : dimension α γ), a = b → b = a := by
    intros a b h
    exact symm h
  apply h _ _
  trivial

@[simp] lemma add_def''  (a : dimension α γ) : a + a = a := by rw [← add_def, add_def']
@[simp] lemma sub_def  (a b : dimension α γ) : a.sub b = a - b := by rfl
@[simp] lemma sub_def'  (a : dimension α γ) : a.sub a = a := by
  generalize hb : a = b
  nth_rewrite 1 [(symm hb)]
  revert a b hb
  unfold dimension.sub
  convert Classical.epsilon_spec ((⟨fun a _ => a, fun _ _ _ => rfl⟩ :
    ∃ (f : dimension α γ → dimension α γ → dimension α γ), ∀ a b, a = b → f a b = a))
  have h : ∀ (a b : dimension α γ), a = b → b = a := by
    intros a b h
    exact symm h
  apply h _ _
  trivial

@[simp] lemma sub_def''  (a : dimension α γ)  : a - a = a := by rw [← sub_def, sub_def']
@[simp] lemma mul_def  (a b : dimension α γ) : a.mul b = a * b := by rfl
@[simp] lemma mul_def'  (a b : dimension α γ) : a * b = fun i => a i + b i := by rfl
@[simp] lemma div_def  (a b : dimension α γ) : a.div b = a / b := by rfl
@[simp] lemma div_def'  (a b : dimension α γ) : a / b = fun i => a i - b i := by rfl
@[simp] lemma pow_def  (a : dimension α γ) (b : γ) : a.pow b = a^b := by rfl
@[simp] lemma pow_def'   (a : dimension α γ) (b : γ) : a ^ b = fun i => b * (a i):= by rfl
@[simp] lemma inv_def  (a : dimension α γ) : a⁻¹ = a^(-1:γ):= by rfl
@[simp] lemma le_def  (a b : dimension α γ) : a.le b ↔ a ≤ b := by rfl
@[simp] lemma le_def'  (a : dimension α γ) : a ≤ a := by
  rw [← le_def]
  simp only [dimension.le, reduceIte]
@[simp] lemma lt_def  (a b : dimension α γ) : a.lt b ↔ a < b := by rfl
@[simp] lemma lt_def'  (a : dimension α γ) : a < a := by
  rw [← dimension.lt_def]
  simp only [dimension.lt, reduceIte]


@[simp]
lemma one_eq_dimensionless  : 1 = dimensionless α γ := by rfl

@[simp]
lemma dimensionless_def'  : dimensionless α γ = Function.const α 0 := rfl

protected theorem mul_comm  (a b : dimension α γ) : a * b = b * a := by
  simp only [mul_def']
  funext
  rw [add_comm]

protected theorem div_mul_comm  (a b c : dimension α γ) : a / c * b  = b / c * a := by
  simp only [div_def', mul_def']
  funext
  rw [sub_add_comm]

protected theorem mul_assoc  (a b c : dimension α γ) : a * b * c = a * (b * c) := by
  simp only [mul_def']
  funext
  rw [add_assoc]

protected theorem mul_one  (a : dimension α γ) : a * 1 = a := by
simp only [one_eq_dimensionless, dimensionless_def', Function.const_zero, mul_def', Pi.zero_apply, add_zero]

protected theorem one_mul  (a : dimension α γ) : 1 * a = a := by simp only [one_eq_dimensionless,
  dimensionless_def', Function.const_zero, mul_def', Pi.zero_apply, zero_add]

protected theorem div_eq_mul_inv  (a b : dimension α γ) : a / b = a * b⁻¹ := by
  simp
  funext
  rw [sub_eq_add_neg]

protected theorem mul_left_inv  (a : dimension α γ) : a⁻¹ * a = 1 := by
  simp
  funext
  simp

protected theorem mul_right_inv  (a : dimension α γ) : a * a⁻¹ = 1 := by
  rw [dimension.mul_comm, dimension.mul_left_inv]

protected theorem pow_zero  (a : dimension α γ) : a ^ (0:γ) = 1 := by
  simp
  funext
  simp

protected theorem pow_succ  (a : dimension α γ) (n : γ) : a ^ (n + 1) = a * a^n := by
  simp
  funext x
  rw [add_mul,add_comm, one_mul]

instance  : CommGroup (dimension α γ) where
  mul := dimension.mul
  div := dimension.div
  inv a := dimension.pow a (-1)
  mul_assoc := dimension.mul_assoc
  one := dimensionless α γ
  npow n a := dimension.pow a ↑n
  zpow z a:= dimension.pow a ↑z
  one_mul := dimension.one_mul
  mul_one := dimension.mul_one
  mul_comm := dimension.mul_comm
  div_eq_mul_inv a := dimension.div_eq_mul_inv a
  inv_mul_cancel a := dimension.mul_left_inv a
  npow_zero := by intro x; funext x; simp
  npow_succ n a := by simp; funext x; rw [add_one_mul]
  zpow_neg' _ _ := by simp; rename_i x1 x2; funext x3; rw [← neg_add,neg_mul,add_comm]
  zpow_succ' _ _ := by simp; rename_i x1 x2; funext; rw [add_one_mul]
  zpow_zero' := by intro x; funext x; simp








/-!
# Buckingham-Pi Theorem
-/

--Converts a list (tuple) of dimensions (the variables) into a matrix of exponent values
def dimensional_matrix {n : ℕ}  [Fintype α] (d : Fin n → dimension α γ)
  (perm : Fin (Fintype.card α) → α) : Matrix (Fin (Fintype.card α)) (Fin n) γ :=
    Matrix.of.toFun (fun (a : Fin (Fintype.card α)) (i : Fin n) => d i (perm a))

--Calculates the number of dimensionless parameters possible from a list of dimensions
noncomputable def number_of_dimensionless_parameters {n : ℕ}  [Fintype α]
  (d : Fin n → dimension α γ) (perm : Fin (Fintype.card α) → α) :=
    n - Matrix.rank (dimensional_matrix d perm)

--Calculates the dimensionless parameters from a list of dimensions (not unique)
def dimensionless_numbers_matrix {n : ℕ}  [Fintype α] (d : Fin n → dimension α γ)
  (perm : Fin (Fintype.card α) → α) :=
    LinearMap.ker (Matrix.toLin' (dimensional_matrix d perm))
end dimension
