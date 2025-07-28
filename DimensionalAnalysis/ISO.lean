import DimensionalAnalysis.Basic
/- ### Defining the ISO ### -/ ---------------------------------------------------------------------

inductive ISO
| time | length | current | temperature | amount | luminosity | mass
deriving Fintype

instance ISO.DecidableEq : DecidableEq ISO
  | ISO.time, ISO.time => isTrue rfl
  | ISO.time, ISO.length => isFalse (fun h => ISO.noConfusion h)
  | ISO.time, ISO.current => isFalse (fun h => ISO.noConfusion h)
  | ISO.time, ISO.temperature => isFalse (fun h => ISO.noConfusion h)
  | ISO.time, ISO.amount => isFalse (fun h => ISO.noConfusion h)
  | ISO.time, ISO.luminosity => isFalse (fun h => ISO.noConfusion h)
  | ISO.time, ISO.mass => isFalse (fun h => ISO.noConfusion h)
  | ISO.length, ISO.time => isFalse (fun h => ISO.noConfusion h)
  | ISO.length, ISO.length => isTrue rfl
  | ISO.length, ISO.current => isFalse (fun h => ISO.noConfusion h)
  | ISO.length, ISO.temperature => isFalse (fun h => ISO.noConfusion h)
  | ISO.length, ISO.amount => isFalse (fun h => ISO.noConfusion h)
  | ISO.length, ISO.luminosity => isFalse (fun h => ISO.noConfusion h)
  | ISO.length, ISO.mass => isFalse (fun h => ISO.noConfusion h)
  | ISO.current, ISO.time => isFalse (fun h => ISO.noConfusion h)
  | ISO.current, ISO.length => isFalse (fun h => ISO.noConfusion h)
  | ISO.current, ISO.current => isTrue rfl
  | ISO.current, ISO.temperature => isFalse (fun h => ISO.noConfusion h)
  | ISO.current, ISO.amount => isFalse (fun h => ISO.noConfusion h)
  | ISO.current, ISO.luminosity => isFalse (fun h => ISO.noConfusion h)
  | ISO.current, ISO.mass => isFalse (fun h => ISO.noConfusion h)
  | ISO.temperature, ISO.time => isFalse (fun h => ISO.noConfusion h)
  | ISO.temperature, ISO.length => isFalse (fun h => ISO.noConfusion h)
  | ISO.temperature, ISO.current => isFalse (fun h => ISO.noConfusion h)
  | ISO.temperature, ISO.temperature => isTrue rfl
  | ISO.temperature, ISO.amount => isFalse (fun h => ISO.noConfusion h)
  | ISO.temperature, ISO.luminosity => isFalse (fun h => ISO.noConfusion h)
  | ISO.temperature, ISO.mass => isFalse (fun h => ISO.noConfusion h)
  | ISO.amount, ISO.time => isFalse (fun h => ISO.noConfusion h)
  | ISO.amount, ISO.length => isFalse (fun h => ISO.noConfusion h)
  | ISO.amount, ISO.current => isFalse (fun h => ISO.noConfusion h)
  | ISO.amount, ISO.temperature => isFalse (fun h => ISO.noConfusion h)
  | ISO.amount, ISO.amount => isTrue rfl
  | ISO.amount, ISO.luminosity => isFalse (fun h => ISO.noConfusion h)
  | ISO.amount, ISO.mass => isFalse (fun h => ISO.noConfusion h)
  | ISO.luminosity, ISO.time => isFalse (fun h => ISO.noConfusion h)
  | ISO.luminosity, ISO.length => isFalse (fun h => ISO.noConfusion h)
  | ISO.luminosity, ISO.current => isFalse (fun h => ISO.noConfusion h)
  | ISO.luminosity, ISO.temperature => isFalse (fun h => ISO.noConfusion h)
  | ISO.luminosity, ISO.amount => isFalse (fun h => ISO.noConfusion h)
  | ISO.luminosity, ISO.luminosity => isTrue rfl
  | ISO.luminosity, ISO.mass => isFalse (fun h => ISO.noConfusion h)
  | ISO.mass, ISO.time => isFalse (fun h => ISO.noConfusion h)
  | ISO.mass, ISO.length => isFalse (fun h => ISO.noConfusion h)
  | ISO.mass, ISO.current => isFalse (fun h => ISO.noConfusion h)
  | ISO.mass, ISO.temperature => isFalse (fun h => ISO.noConfusion h)
  | ISO.mass, ISO.amount => isFalse (fun h => ISO.noConfusion h)
  | ISO.mass, ISO.luminosity => isFalse (fun h => ISO.noConfusion h)
  | ISO.mass, ISO.mass => isTrue rfl

instance : HasBaseTime ISO := {dec := ISO.DecidableEq, Time := ISO.time}
instance : HasBaseLength ISO := {dec := ISO.DecidableEq, Length := ISO.length}
instance : HasBaseCurrent ISO := {dec := ISO.DecidableEq, Current := ISO.current}
instance : HasBaseTemperature ISO := {dec := ISO.DecidableEq, Temperature := ISO.temperature}
instance : HasBaseAmount ISO := {dec := ISO.DecidableEq, Amount := ISO.amount}
instance : HasBaseLuminosity ISO := {dec := ISO.DecidableEq, Luminosity := ISO.luminosity}
instance : HasBaseMass ISO := {dec := ISO.DecidableEq, Mass := ISO.mass}

lemma ISO_length_to_has_length : ISO.length = HasBaseLength.Length := by rfl
lemma ISO_time_to_has_time : ISO.time = HasBaseTime.Time := by rfl
lemma ISO_current_to_has_current : ISO.current = HasBaseCurrent.Current := by rfl
lemma ISO_temperature_to_has_temperature : ISO.temperature = HasBaseTemperature.Temperature := by rfl
lemma ISO_amount_to_has_amount : ISO.amount = HasBaseAmount.Amount := by rfl
lemma ISO_luminosity_to_has_luminosity : ISO.luminosity = HasBaseLuminosity.Luminosity := by rfl
lemma ISO_mass_to_has_mass : ISO.mass = HasBaseMass.Mass := by rfl

protected def ISO.repr : ISO → String
  | ISO.time => "time"
  | ISO.length => "length"
  | ISO.current => "current"
  | ISO.temperature => "temperature"
  | ISO.amount => "amount"
  | ISO.luminosity => "luminosity"
  | ISO.mass => "mass"
