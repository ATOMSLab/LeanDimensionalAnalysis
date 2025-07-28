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
class HasBaseTime (B : Type u) where
  [dec : DecidableEq B]
  Time : B

class HasBaseLength (B : Type u) where
  [dec : DecidableEq B]
  Length : B

class HasBaseMass (B : Type u) where
  [dec : DecidableEq B]
  Mass : B

class HasBaseAmount (B : Type u) where
  [dec : DecidableEq B]
  Amount : B

class HasBaseCurrent (B : Type u) where
  [dec : DecidableEq B]
  Current : B

class HasBaseTemperature (B : Type u) where
  [dec : DecidableEq B]
  Temperature : B

class HasBaseLuminosity (B : Type u) where
  [dec : DecidableEq B]
  Luminosity : B

-- Here is a base dimension for currency
class HasBaseCurrency (B : Type u) where
  [dec : DecidableEq B]
  Currency : B

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
-- Here we define a dimension as a mapping of a base dimension to a number which is the exponent.
def dimension (B : Type u) (E : Type v) [CommRing E] := B → E

class DimEq {B E} [CommRing E] (dim1 : dimension B E) (dim2 : semiOutParam (dimension B E)) where
(Eq : dim1 = dim2)

instance {B E1 E2} [CommRing E1] [CommRing E2] [Coe E1 E2] : Coe (dimension B E1) (dimension B E2) where
coe :=  fun f => fun x => (f x : E2)

namespace dimension

-- The dimensionless dimension is a dimension where all the exponents are zero. It functions as the identity
-- element which is why we relate it to One in the instance function.
def dimensionless (B : Type u) (E : Type v) [CommRing E] : dimension B E := Function.const B 0
instance (B : Type u) (E : Type v)[CommRing E] : One (dimension B E) := ⟨dimension.dimensionless B E⟩
instance (B : Type u) (E : Type v) [CommRing E] : Nonempty (dimension B E) := One.instNonempty
noncomputable instance (B : Type u) (E : Type v) [CommRing E] (a b : dimension B E ) : Decidable (a = b) :=
  Classical.propDecidable (a = b)

-- Here we define the algebraic operators (+,-,*,/,^,<) and how they can act on dimensions.

-- Addition and subtraction only work if both dimensions are the same and returns the same dimension
variable {B : Type u} {E : Type v} [CommRing E]

protected noncomputable def add : dimension B E → dimension B E → dimension B E :=
Classical.epsilon $ fun f => ∀ a b, a = b → f a b = a
protected noncomputable def sub : dimension B E → dimension B E → dimension B E :=
Classical.epsilon $ fun f => ∀ a b, a = b → f a b = a

-- For multiplication, all the exponents are added together. For divison, they are subtracted.
protected def mul  : dimension B E → dimension B E → dimension B E
| a, b => fun i => a i + b i
protected def div  : dimension B E → dimension B E → dimension B E
| a, b => fun i => a i - b i

-- Raising a dimension to a power results in multiplying each exponent by the power.

protected def pow {E} [CommRing E]: dimension B E → E → dimension B E
| a, n => fun i => n * (a i)

-- Inequality operators only work if the dimensions are the same.
protected def le  : dimension B E → dimension B E → Prop
| a, b => ite (a = b) true false
protected def lt  : dimension B E → dimension B E → Prop
| a, b => ite (a = b) true false

-- Here we unify our operator definitions with their respective global class.
noncomputable instance  : Add (dimension B E) := ⟨dimension.add⟩
noncomputable instance  : Sub (dimension B E) := ⟨dimension.sub⟩
instance  : Mul (dimension B E) := ⟨dimension.mul⟩
instance  : Div (dimension B E) := ⟨dimension.div⟩
instance  {E} [CommRing E] : HPow (dimension B E) E (dimension B E) := ⟨dimension.pow⟩
instance : Pow (dimension B E) E := ⟨dimension.pow⟩
instance  : Inv (dimension B E) := ⟨fun d => d^(-1:E)⟩
instance  : LT (dimension B E) := ⟨dimension.lt⟩
instance  : LE (dimension B E) := ⟨dimension.le⟩

instance {E1 E2} [CommRing E1] [CommRing E2] [Coe E1 E2]: HPow (dimension B E1) E2 (dimension B E2) where
  hPow
  | a, n => dimension.pow (a : (dimension B E2)) n

-- Here we define how derivatives and integrals act on dimensions.
protected def derivative  (b : dimension B E): dimension B E → dimension B E := fun a => a / b
protected def integral  (b : dimension B E): dimension B E → dimension B E := fun a => a * b

-- Here we define relative operators (exp, sin, log, etc.)
protected noncomputable def relativeOperator  : dimension B E → dimension B E :=
Classical.epsilon $ fun Operator => ∀ dim , dim = 1 → Operator dim = 1

-- Here we prove several helper lemmas which have the simp attribute. These lemmas help
-- simplify our proofs and allow the simp tactic to use these lemmas.
@[simp] lemma add_def  (a b : dimension B E) : a.add b = a + b := by rfl
@[simp] lemma add_def'  (a : dimension B E) : a.add a = a := by
  generalize hb : a = b
  nth_rewrite 1 [(symm hb)]
  revert a b hb
  unfold dimension.add
  convert Classical.epsilon_spec ((⟨fun a _ => a, fun _ _ _ => rfl⟩ :
    ∃ (f : dimension B E → dimension B E → dimension B E), ∀ a b, a = b → f a b = a))
  have h : ∀ (a b : dimension B E), a = b → b = a := by
    intros a b h
    exact symm h
  apply h _ _
  trivial

@[simp] lemma add_def''  (a : dimension B E) : a + a = a := by rw [← add_def, add_def']
@[simp] lemma sub_def  (a b : dimension B E) : a.sub b = a - b := by rfl
@[simp] lemma sub_def'  (a : dimension B E) : a.sub a = a := by
  generalize hb : a = b
  nth_rewrite 1 [(symm hb)]
  revert a b hb
  unfold dimension.sub
  convert Classical.epsilon_spec ((⟨fun a _ => a, fun _ _ _ => rfl⟩ :
    ∃ (f : dimension B E → dimension B E → dimension B E), ∀ a b, a = b → f a b = a))
  have h : ∀ (a b : dimension B E), a = b → b = a := by
    intros a b h
    exact symm h
  apply h _ _
  trivial

@[simp] lemma sub_def''  (a : dimension B E)  : a - a = a := by rw [← sub_def, sub_def']
@[simp] lemma mul_def  (a b : dimension B E) : a.mul b = a * b := by rfl
@[simp] lemma mul_def'  (a b : dimension B E) : a * b = fun i => a i + b i := by rfl
@[simp] lemma div_def  (a b : dimension B E) : a.div b = a / b := by rfl
@[simp] lemma div_def'  (a b : dimension B E) : a / b = fun i => a i - b i := by rfl
@[simp] lemma pow_def  (a : dimension B E) (b : E) : a.pow b = a^b := by rfl
@[simp] lemma pow_def'   (a : dimension B E) (b : E) : a ^ b = fun i => b * (a i):= by rfl
@[simp] lemma inv_def  (a : dimension B E) : a⁻¹ = a^(-1:E):= by rfl
@[simp] lemma le_def  (a b : dimension B E) : a.le b ↔ a ≤ b := by rfl
@[simp] lemma le_def'  (a : dimension B E) : a ≤ a := by
  rw [← le_def]
  simp only [dimension.le, reduceIte]
@[simp] lemma lt_def  (a b : dimension B E) : a.lt b ↔ a < b := by rfl
@[simp] lemma lt_def'  (a : dimension B E) : a < a := by
  rw [← dimension.lt_def]
  simp only [dimension.lt, reduceIte]


@[simp]
lemma one_eq_dimensionless  : 1 = dimensionless B E := by rfl

@[simp]
lemma dimensionless_def'  : dimensionless B E = Function.const B 0 := rfl

protected theorem mul_comm  (a b : dimension B E) : a * b = b * a := by
  simp only [mul_def']
  funext
  rw [add_comm]

protected theorem div_mul_comm  (a b c : dimension B E) : a / c * b  = b / c * a := by
  simp only [div_def', mul_def']
  funext
  rw [sub_add_comm]

protected theorem mul_assoc  (a b c : dimension B E) : a * b * c = a * (b * c) := by
  simp only [mul_def']
  funext
  rw [add_assoc]

protected theorem mul_one  (a : dimension B E) : a * 1 = a := by
simp only [one_eq_dimensionless, dimensionless_def', Function.const_zero, mul_def', Pi.zero_apply, add_zero]

protected theorem one_mul  (a : dimension B E) : 1 * a = a := by simp only [one_eq_dimensionless,
  dimensionless_def', Function.const_zero, mul_def', Pi.zero_apply, zero_add]

protected theorem div_eq_mul_inv  (a b : dimension B E) : a / b = a * b⁻¹ := by
  simp
  funext
  rw [sub_eq_add_neg]

protected theorem mul_left_inv  (a : dimension B E) : a⁻¹ * a = 1 := by
  simp
  funext
  simp

protected theorem mul_right_inv  (a : dimension B E) : a * a⁻¹ = 1 := by
  rw [dimension.mul_comm, dimension.mul_left_inv]

protected theorem pow_zero  (a : dimension B E) : a ^ (0:E) = 1 := by
  simp
  funext
  simp

protected theorem pow_succ  (a : dimension B E) (n : E) : a ^ (n + 1) = a * a^n := by
  simp
  funext x
  rw [add_mul,add_comm, one_mul]

instance  : CommGroup (dimension B E) where
  mul := dimension.mul
  div := dimension.div
  inv a := dimension.pow a (-1)
  mul_assoc := dimension.mul_assoc
  one := dimensionless B E
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
def dimensional_matrix {n : ℕ}  [Fintype B] (d : Fin n → dimension B E)
  (perm : Fin (Fintype.card B) → B) : Matrix (Fin (Fintype.card B)) (Fin n) E :=
    Matrix.of.toFun (fun (a : Fin (Fintype.card B)) (i : Fin n) => d i (perm a))

--Calculates the number of dimensionless parameters possible from a list of dimensions
noncomputable def number_of_dimensionless_parameters {n : ℕ}  [Fintype B]
  (d : Fin n → dimension B E) (perm : Fin (Fintype.card B) → B) :=
    n - Matrix.rank (dimensional_matrix d perm)

--Calculates the dimensionless parameters from a list of dimensions (not unique)
def dimensionless_numbers_matrix {n : ℕ}  [Fintype B] (d : Fin n → dimension B E)
  (perm : Fin (Fintype.card B) → B) :=
    LinearMap.ker (Matrix.toLin' (dimensional_matrix d perm))
end dimension
