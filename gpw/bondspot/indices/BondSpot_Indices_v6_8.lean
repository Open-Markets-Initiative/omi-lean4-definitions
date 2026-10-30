import Wire

/-!
# Giełda Papierów Wartościowych w Warszawie BondSpot Indices v6.8

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.GpwBondspotIndicesXdpV68

/-- Index Level Code: one byte code -/
def IndexLevelCode.codes : List UInt8 :=
  [0x31, 0x32, 0x33, 0x35, 0x38, 0x39, 0x41, 0x42, 0x43, 0x52, 0x58, 0x59]

inductive IndexLevelCode where
  | firstValueOfTheIndexAtTheSession -- First Value Of The Index At The Session
  | currentIndex -- Current Index
  | theoreticalValueOfTheIndexBeforeItsOpening -- Theoretical Value Of The Index Before Its Opening
  | closingIndexFromPreviousSessionReferenceIndex -- Closing Index From Previous Session Reference Index
  | theoreticalOpeningIndexBeforeOpeningTheSession -- Theoretical Opening Index Before Opening The Session
  | indexWithoutOpening -- Index Without Opening
  | preliminaryOpeningIndex -- Preliminary Opening Index
  | syntheticOpeningIndex100 -- Synthetic Opening Index 100%
  | finalOpeningIndex -- Final Opening Index
  | averageWeightedIndex -- Average Weighted Index
  | cancellationOfTheCurrentValuesOfTheIndex -- Cancellation Of The Current Values Of The Index
  | recalculatedCurrentValuesOfTheIndex -- Recalculated Current Values Of The Index
  | unlisted (byte : { byte : UInt8 // byte ∉ IndexLevelCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace IndexLevelCode

def toByte : IndexLevelCode → UInt8
  | .firstValueOfTheIndexAtTheSession => 0x31
  | .currentIndex => 0x32
  | .theoreticalValueOfTheIndexBeforeItsOpening => 0x33
  | .closingIndexFromPreviousSessionReferenceIndex => 0x35
  | .theoreticalOpeningIndexBeforeOpeningTheSession => 0x38
  | .indexWithoutOpening => 0x39
  | .preliminaryOpeningIndex => 0x41
  | .syntheticOpeningIndex100 => 0x42
  | .finalOpeningIndex => 0x43
  | .averageWeightedIndex => 0x52
  | .cancellationOfTheCurrentValuesOfTheIndex => 0x58
  | .recalculatedCurrentValuesOfTheIndex => 0x59
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : IndexLevelCode :=
  if byte = 0x31 then .firstValueOfTheIndexAtTheSession
  else if byte = 0x32 then .currentIndex
  else if byte = 0x33 then .theoreticalValueOfTheIndexBeforeItsOpening
  else if byte = 0x35 then .closingIndexFromPreviousSessionReferenceIndex
  else if byte = 0x38 then .theoreticalOpeningIndexBeforeOpeningTheSession
  else if byte = 0x39 then .indexWithoutOpening
  else if byte = 0x41 then .preliminaryOpeningIndex
  else if byte = 0x42 then .syntheticOpeningIndex100
  else if byte = 0x43 then .finalOpeningIndex
  else if byte = 0x52 then .averageWeightedIndex
  else if byte = 0x58 then .cancellationOfTheCurrentValuesOfTheIndex
  else .recalculatedCurrentValuesOfTheIndex

def ofByte (byte : UInt8) : IndexLevelCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : IndexLevelCode) : ofByte value.toByte = value := by
  cases value with
  | firstValueOfTheIndexAtTheSession => decide
  | currentIndex => decide
  | theoreticalValueOfTheIndexBeforeItsOpening => decide
  | closingIndexFromPreviousSessionReferenceIndex => decide
  | theoreticalOpeningIndexBeforeOpeningTheSession => decide
  | indexWithoutOpening => decide
  | preliminaryOpeningIndex => decide
  | syntheticOpeningIndex100 => decide
  | finalOpeningIndex => decide
  | averageWeightedIndex => decide
  | cancellationOfTheCurrentValuesOfTheIndex => decide
  | recalculatedCurrentValuesOfTheIndex => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : IndexLevelCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (IndexLevelCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : IndexLevelCode) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : IndexLevelCode) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : IndexLevelCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end IndexLevelCode

/-- Marker Percent Change Toi: one byte code -/
def MarkerPercentChangeToi.codes : List UInt8 :=
  [0x2B, 0x2D, 0x20]

inductive MarkerPercentChangeToi where
  | increase -- Increase
  | decrease -- Decrease
  | noChange -- No Change
  | unlisted (byte : { byte : UInt8 // byte ∉ MarkerPercentChangeToi.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarkerPercentChangeToi

def toByte : MarkerPercentChangeToi → UInt8
  | .increase => 0x2B
  | .decrease => 0x2D
  | .noChange => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarkerPercentChangeToi :=
  if byte = 0x2B then .increase
  else if byte = 0x2D then .decrease
  else .noChange

def ofByte (byte : UInt8) : MarkerPercentChangeToi :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarkerPercentChangeToi) : ofByte value.toByte = value := by
  cases value with
  | increase => decide
  | decrease => decide
  | noChange => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarkerPercentChangeToi) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarkerPercentChangeToi × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarkerPercentChangeToi) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : MarkerPercentChangeToi) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : MarkerPercentChangeToi) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarkerPercentChangeToi

/-- Marker Point Change: one byte code -/
def MarkerPointChange.codes : List UInt8 :=
  [0x2B, 0x2D, 0x20]

inductive MarkerPointChange where
  | increase -- Increase
  | decrease -- Decrease
  | noChange -- No Change
  | unlisted (byte : { byte : UInt8 // byte ∉ MarkerPointChange.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarkerPointChange

def toByte : MarkerPointChange → UInt8
  | .increase => 0x2B
  | .decrease => 0x2D
  | .noChange => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarkerPointChange :=
  if byte = 0x2B then .increase
  else if byte = 0x2D then .decrease
  else .noChange

def ofByte (byte : UInt8) : MarkerPointChange :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarkerPointChange) : ofByte value.toByte = value := by
  cases value with
  | increase => decide
  | decrease => decide
  | noChange => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarkerPointChange) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarkerPointChange × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarkerPointChange) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : MarkerPointChange) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : MarkerPointChange) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarkerPointChange

/-- Marker Difference Central Spread: one byte code -/
def MarkerDifferenceCentralSpread.codes : List UInt8 :=
  [0x2B, 0x2D, 0x20]

inductive MarkerDifferenceCentralSpread where
  | increase -- Increase
  | decrease -- Decrease
  | noChange -- No Change
  | unlisted (byte : { byte : UInt8 // byte ∉ MarkerDifferenceCentralSpread.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarkerDifferenceCentralSpread

def toByte : MarkerDifferenceCentralSpread → UInt8
  | .increase => 0x2B
  | .decrease => 0x2D
  | .noChange => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarkerDifferenceCentralSpread :=
  if byte = 0x2B then .increase
  else if byte = 0x2D then .decrease
  else .noChange

def ofByte (byte : UInt8) : MarkerDifferenceCentralSpread :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarkerDifferenceCentralSpread) : ofByte value.toByte = value := by
  cases value with
  | increase => decide
  | decrease => decide
  | noChange => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarkerDifferenceCentralSpread) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarkerDifferenceCentralSpread × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarkerDifferenceCentralSpread) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : MarkerDifferenceCentralSpread) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : MarkerDifferenceCentralSpread) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarkerDifferenceCentralSpread

/-- Dissemination Frequency Marker: one byte code -/
def DisseminationFrequencyMarker.codes : List UInt8 :=
  [0x30, 0x31]

inductive DisseminationFrequencyMarker where
  | whenTheMessageAtAParticularLevelIsPublishedRegularlyAtTheSession -- When The Message At A Particular Level Is Published Regularly At The Session
  | whenTheMessageAtAParticularLevelIsPublishedAtTheSessionOnAOneTimeBasis -- When The Message At A Particular Level Is Published At The Session On A One Time Basis
  | unlisted (byte : { byte : UInt8 // byte ∉ DisseminationFrequencyMarker.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DisseminationFrequencyMarker

def toByte : DisseminationFrequencyMarker → UInt8
  | .whenTheMessageAtAParticularLevelIsPublishedRegularlyAtTheSession => 0x30
  | .whenTheMessageAtAParticularLevelIsPublishedAtTheSessionOnAOneTimeBasis => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DisseminationFrequencyMarker :=
  if byte = 0x30 then .whenTheMessageAtAParticularLevelIsPublishedRegularlyAtTheSession
  else .whenTheMessageAtAParticularLevelIsPublishedAtTheSessionOnAOneTimeBasis

def ofByte (byte : UInt8) : DisseminationFrequencyMarker :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DisseminationFrequencyMarker) : ofByte value.toByte = value := by
  cases value with
  | whenTheMessageAtAParticularLevelIsPublishedRegularlyAtTheSession => decide
  | whenTheMessageAtAParticularLevelIsPublishedAtTheSessionOnAOneTimeBasis => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DisseminationFrequencyMarker) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DisseminationFrequencyMarker × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DisseminationFrequencyMarker) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : DisseminationFrequencyMarker) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : DisseminationFrequencyMarker) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DisseminationFrequencyMarker

/-- Marker High: one byte code -/
def MarkerHigh.codes : List UInt8 :=
  [0x2B, 0x2D, 0x20]

inductive MarkerHigh where
  | increase -- Increase
  | decrease -- Decrease
  | noChange -- No Change
  | unlisted (byte : { byte : UInt8 // byte ∉ MarkerHigh.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarkerHigh

def toByte : MarkerHigh → UInt8
  | .increase => 0x2B
  | .decrease => 0x2D
  | .noChange => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarkerHigh :=
  if byte = 0x2B then .increase
  else if byte = 0x2D then .decrease
  else .noChange

def ofByte (byte : UInt8) : MarkerHigh :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarkerHigh) : ofByte value.toByte = value := by
  cases value with
  | increase => decide
  | decrease => decide
  | noChange => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarkerHigh) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarkerHigh × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarkerHigh) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : MarkerHigh) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : MarkerHigh) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarkerHigh

/-- Marker Low: one byte code -/
def MarkerLow.codes : List UInt8 :=
  [0x2B, 0x2D, 0x20]

inductive MarkerLow where
  | increase -- Increase
  | decrease -- Decrease
  | noChange -- No Change
  | unlisted (byte : { byte : UInt8 // byte ∉ MarkerLow.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarkerLow

def toByte : MarkerLow → UInt8
  | .increase => 0x2B
  | .decrease => 0x2D
  | .noChange => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarkerLow :=
  if byte = 0x2B then .increase
  else if byte = 0x2D then .decrease
  else .noChange

def ofByte (byte : UInt8) : MarkerLow :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarkerLow) : ofByte value.toByte = value := by
  cases value with
  | increase => decide
  | decrease => decide
  | noChange => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarkerLow) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarkerLow × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarkerLow) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : MarkerLow) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : MarkerLow) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarkerLow

/-- Marker Closing Prev Session: one byte code -/
def MarkerClosingPrevSession.codes : List UInt8 :=
  [0x2B, 0x2D, 0x20]

inductive MarkerClosingPrevSession where
  | increase -- Increase
  | decrease -- Decrease
  | noChange -- No Change
  | unlisted (byte : { byte : UInt8 // byte ∉ MarkerClosingPrevSession.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarkerClosingPrevSession

def toByte : MarkerClosingPrevSession → UInt8
  | .increase => 0x2B
  | .decrease => 0x2D
  | .noChange => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarkerClosingPrevSession :=
  if byte = 0x2B then .increase
  else if byte = 0x2D then .decrease
  else .noChange

def ofByte (byte : UInt8) : MarkerClosingPrevSession :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarkerClosingPrevSession) : ofByte value.toByte = value := by
  cases value with
  | increase => decide
  | decrease => decide
  | noChange => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarkerClosingPrevSession) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarkerClosingPrevSession × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarkerClosingPrevSession) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : MarkerClosingPrevSession) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : MarkerClosingPrevSession) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarkerClosingPrevSession

/-- Marker Closing Prev Year: one byte code -/
def MarkerClosingPrevYear.codes : List UInt8 :=
  [0x2B, 0x2D, 0x20]

inductive MarkerClosingPrevYear where
  | increase -- Increase
  | decrease -- Decrease
  | noChange -- No Change
  | unlisted (byte : { byte : UInt8 // byte ∉ MarkerClosingPrevYear.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarkerClosingPrevYear

def toByte : MarkerClosingPrevYear → UInt8
  | .increase => 0x2B
  | .decrease => 0x2D
  | .noChange => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarkerClosingPrevYear :=
  if byte = 0x2B then .increase
  else if byte = 0x2D then .decrease
  else .noChange

def ofByte (byte : UInt8) : MarkerClosingPrevYear :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarkerClosingPrevYear) : ofByte value.toByte = value := by
  cases value with
  | increase => decide
  | decrease => decide
  | noChange => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarkerClosingPrevYear) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarkerClosingPrevYear × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarkerClosingPrevYear) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : MarkerClosingPrevYear) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : MarkerClosingPrevYear) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarkerClosingPrevYear

/-- Mode Index Dissemination: one byte code -/
def ModeIndexDissemination.codes : List UInt8 :=
  [0x43, 0x46]

inductive ModeIndexDissemination where
  | indexIsQuotedInDeterminedTimeIntervals -- Index Is Quoted In Determined Time Intervals
  | indexIsQuotedOnDeterminedHours -- Index Is Quoted On Determined Hours
  | unlisted (byte : { byte : UInt8 // byte ∉ ModeIndexDissemination.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ModeIndexDissemination

def toByte : ModeIndexDissemination → UInt8
  | .indexIsQuotedInDeterminedTimeIntervals => 0x43
  | .indexIsQuotedOnDeterminedHours => 0x46
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ModeIndexDissemination :=
  if byte = 0x43 then .indexIsQuotedInDeterminedTimeIntervals
  else .indexIsQuotedOnDeterminedHours

def ofByte (byte : UInt8) : ModeIndexDissemination :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ModeIndexDissemination) : ofByte value.toByte = value := by
  cases value with
  | indexIsQuotedInDeterminedTimeIntervals => decide
  | indexIsQuotedOnDeterminedHours => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ModeIndexDissemination) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ModeIndexDissemination × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ModeIndexDissemination) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ModeIndexDissemination) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ModeIndexDissemination) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ModeIndexDissemination

/-- Product Classification: one byte code -/
def ProductClassification.codes : List UInt8 :=
  [0x57, 0x5A, 0x56, 0x4D, 0x53, 0x4C]

inductive ProductClassification where
  | wseIndexFromTheMainMarket -- Wse Index From The Main Market
  | externalIndex -- External Index
  | anotherWseInformationProduct -- Another Wse Information Product
  | wseStrategyDividendPointIndex -- Wse Strategy Dividend Point Index
  | wseStrategyIndexOfShortType -- Wse Strategy Index Of Short Type
  | wseStrategyIndexOfLeverageType -- Wse Strategy Index Of Leverage Type
  | unlisted (byte : { byte : UInt8 // byte ∉ ProductClassification.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ProductClassification

def toByte : ProductClassification → UInt8
  | .wseIndexFromTheMainMarket => 0x57
  | .externalIndex => 0x5A
  | .anotherWseInformationProduct => 0x56
  | .wseStrategyDividendPointIndex => 0x4D
  | .wseStrategyIndexOfShortType => 0x53
  | .wseStrategyIndexOfLeverageType => 0x4C
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ProductClassification :=
  if byte = 0x57 then .wseIndexFromTheMainMarket
  else if byte = 0x5A then .externalIndex
  else if byte = 0x56 then .anotherWseInformationProduct
  else if byte = 0x4D then .wseStrategyDividendPointIndex
  else if byte = 0x53 then .wseStrategyIndexOfShortType
  else .wseStrategyIndexOfLeverageType

def ofByte (byte : UInt8) : ProductClassification :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ProductClassification) : ofByte value.toByte = value := by
  cases value with
  | wseIndexFromTheMainMarket => decide
  | externalIndex => decide
  | anotherWseInformationProduct => decide
  | wseStrategyDividendPointIndex => decide
  | wseStrategyIndexOfShortType => decide
  | wseStrategyIndexOfLeverageType => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ProductClassification) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ProductClassification × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ProductClassification) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ProductClassification) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ProductClassification) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ProductClassification

/-- Opening Calc Formula: one byte code -/
def OpeningCalcFormula.codes : List UInt8 :=
  [0x53, 0x4F]

inductive OpeningCalcFormula where
  | synthetic -- Synthetic
  | chronological -- Chronological
  | unlisted (byte : { byte : UInt8 // byte ∉ OpeningCalcFormula.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OpeningCalcFormula

def toByte : OpeningCalcFormula → UInt8
  | .synthetic => 0x53
  | .chronological => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OpeningCalcFormula :=
  if byte = 0x53 then .synthetic
  else .chronological

def ofByte (byte : UInt8) : OpeningCalcFormula :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OpeningCalcFormula) : ofByte value.toByte = value := by
  cases value with
  | synthetic => decide
  | chronological => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OpeningCalcFormula) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OpeningCalcFormula × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OpeningCalcFormula) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OpeningCalcFormula) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OpeningCalcFormula) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OpeningCalcFormula

/-- Toi Dissemination: one byte code -/
def ToiDissemination.codes : List UInt8 :=
  [0x59, 0x4E]

inductive ToiDissemination where
  | message546WithLevel8IsSent -- Message 546 With Level 8 Is Sent
  | message546WithLevel8IsNotSent -- Message 546 With Level 8 Is Not Sent
  | unlisted (byte : { byte : UInt8 // byte ∉ ToiDissemination.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ToiDissemination

def toByte : ToiDissemination → UInt8
  | .message546WithLevel8IsSent => 0x59
  | .message546WithLevel8IsNotSent => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ToiDissemination :=
  if byte = 0x59 then .message546WithLevel8IsSent
  else .message546WithLevel8IsNotSent

def ofByte (byte : UInt8) : ToiDissemination :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ToiDissemination) : ofByte value.toByte = value := by
  cases value with
  | message546WithLevel8IsSent => decide
  | message546WithLevel8IsNotSent => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ToiDissemination) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ToiDissemination × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ToiDissemination) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ToiDissemination) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ToiDissemination) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ToiDissemination

/-- Spread Dissemination: one byte code -/
def SpreadDissemination.codes : List UInt8 :=
  [0x59, 0x4E]

inductive SpreadDissemination where
  | spreadIndicatorsArePublished -- Spread Indicators Are Published
  | spreadIndicatorsAreNotPublished -- Spread Indicators Are Not Published
  | unlisted (byte : { byte : UInt8 // byte ∉ SpreadDissemination.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SpreadDissemination

def toByte : SpreadDissemination → UInt8
  | .spreadIndicatorsArePublished => 0x59
  | .spreadIndicatorsAreNotPublished => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SpreadDissemination :=
  if byte = 0x59 then .spreadIndicatorsArePublished
  else .spreadIndicatorsAreNotPublished

def ofByte (byte : UInt8) : SpreadDissemination :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SpreadDissemination) : ofByte value.toByte = value := by
  cases value with
  | spreadIndicatorsArePublished => decide
  | spreadIndicatorsAreNotPublished => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SpreadDissemination) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SpreadDissemination × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SpreadDissemination) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SpreadDissemination) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SpreadDissemination) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SpreadDissemination

/-- Trading Value Publication: one byte code -/
def TradingValuePublication.codes : List UInt8 :=
  [0x59, 0x4E]

inductive TradingValuePublication where
  | valueIsProvided -- Value Is Provided
  | valueIsNotProvided -- Value Is Not Provided
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingValuePublication.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingValuePublication

def toByte : TradingValuePublication → UInt8
  | .valueIsProvided => 0x59
  | .valueIsNotProvided => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingValuePublication :=
  if byte = 0x59 then .valueIsProvided
  else .valueIsNotProvided

def ofByte (byte : UInt8) : TradingValuePublication :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingValuePublication) : ofByte value.toByte = value := by
  cases value with
  | valueIsProvided => decide
  | valueIsNotProvided => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradingValuePublication) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradingValuePublication × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradingValuePublication) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TradingValuePublication) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TradingValuePublication) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradingValuePublication

/-- Message Continuation: one byte code -/
def MessageContinuation.codes : List UInt8 :=
  [0x30, 0x31]

inductive MessageContinuation where
  | theMessageIsNotTheLastMessageInformationOfTheCompositionOfTheIndexPortfolio -- The Message Is Not The Last Message Information Of The Composition Of The Index Portfolio
  | theMessageIsTheLastMessageInformationOfTheCompositionOfTheIndexPortfolio -- The Message Is The Last Message Information Of The Composition Of The Index Portfolio
  | unlisted (byte : { byte : UInt8 // byte ∉ MessageContinuation.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MessageContinuation

def toByte : MessageContinuation → UInt8
  | .theMessageIsNotTheLastMessageInformationOfTheCompositionOfTheIndexPortfolio => 0x30
  | .theMessageIsTheLastMessageInformationOfTheCompositionOfTheIndexPortfolio => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MessageContinuation :=
  if byte = 0x30 then .theMessageIsNotTheLastMessageInformationOfTheCompositionOfTheIndexPortfolio
  else .theMessageIsTheLastMessageInformationOfTheCompositionOfTheIndexPortfolio

def ofByte (byte : UInt8) : MessageContinuation :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MessageContinuation) : ofByte value.toByte = value := by
  cases value with
  | theMessageIsNotTheLastMessageInformationOfTheCompositionOfTheIndexPortfolio => decide
  | theMessageIsTheLastMessageInformationOfTheCompositionOfTheIndexPortfolio => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MessageContinuation) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MessageContinuation × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MessageContinuation) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : MessageContinuation) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : MessageContinuation) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MessageContinuation

/-- Real Time Index Message: 108 bytes -/
structure RealTimeIndexMessage where
  symbolIndex : BitVec 32
  sourceTime : BitVec 32
  sourceSeqNum : BitVec 32
  systemId : BitVec 32
  indexLevel : BitVec 32
  sessionHigh : BitVec 32
  sessionLow : BitVec 32
  indIndexOpeningPortfolio : BitVec 32
  percentChangeToi : BitVec 32
  pctChangeIndexValPrevSession : BitVec 32
  pctChangeIndexValPrevYear : BitVec 32
  toi : BitVec 32
  pointChange : BitVec 32
  valueTrading : BitVec 64
  indexValueBid : BitVec 32
  indexValueAsk : BitVec 32
  midSpreadIndex : BitVec 32
  differenceCentralSpread : BitVec 32
  numOfActiveInstruments : BitVec 16
  numOfInstrOfDecreasingQt : BitVec 16
  numOfInstrOfIncreasingQt : BitVec 16
  numOfInstrOfUnchangedQt : BitVec 16
  sourceTimeMicroSecs : BitVec 16
  levelScaleCode : BitVec 8
  timeFirstHigh : Alpha 6
  timeFirstLow : Alpha 6
  indexStatusIndicator : Alpha 2
  indexLevelCode : IndexLevelCode
  markerPercentChangeToi : MarkerPercentChangeToi
  markerPctChgIndexValPrevSess : Alpha 1
  markerPctChgIndexValPrevYear : Alpha 1
  markerPointChange : MarkerPointChange
  markerDifferenceCentralSpread : MarkerDifferenceCentralSpread
  disseminationFrequencyMarker : DisseminationFrequencyMarker
  deriving DecidableEq, Repr

namespace RealTimeIndexMessage

def encode (message : RealTimeIndexMessage) : List UInt8 :=
  encodeUInt 4 message.symbolIndex
    ++ (encodeUInt 4 message.sourceTime
    ++ (encodeUInt 4 message.sourceSeqNum
    ++ (encodeUInt 4 message.systemId
    ++ (encodeUInt 4 message.indexLevel
    ++ (encodeUInt 4 message.sessionHigh
    ++ (encodeUInt 4 message.sessionLow
    ++ (encodeUInt 4 message.indIndexOpeningPortfolio
    ++ (encodeUInt 4 message.percentChangeToi
    ++ (encodeUInt 4 message.pctChangeIndexValPrevSession
    ++ (encodeUInt 4 message.pctChangeIndexValPrevYear
    ++ (encodeUInt 4 message.toi
    ++ (encodeUInt 4 message.pointChange
    ++ (encodeUInt 8 message.valueTrading
    ++ (encodeUInt 4 message.indexValueBid
    ++ (encodeUInt 4 message.indexValueAsk
    ++ (encodeUInt 4 message.midSpreadIndex
    ++ (encodeUInt 4 message.differenceCentralSpread
    ++ (encodeUInt 2 message.numOfActiveInstruments
    ++ (encodeUInt 2 message.numOfInstrOfDecreasingQt
    ++ (encodeUInt 2 message.numOfInstrOfIncreasingQt
    ++ (encodeUInt 2 message.numOfInstrOfUnchangedQt
    ++ (encodeUInt 2 message.sourceTimeMicroSecs
    ++ (encodeUInt 1 message.levelScaleCode
    ++ (Alpha.encode message.timeFirstHigh
    ++ (Alpha.encode message.timeFirstLow
    ++ (Alpha.encode message.indexStatusIndicator
    ++ (IndexLevelCode.encode message.indexLevelCode
    ++ (MarkerPercentChangeToi.encode message.markerPercentChangeToi
    ++ (Alpha.encode message.markerPctChgIndexValPrevSess
    ++ (Alpha.encode message.markerPctChgIndexValPrevYear
    ++ (MarkerPointChange.encode message.markerPointChange
    ++ (MarkerDifferenceCentralSpread.encode message.markerDifferenceCentralSpread
    ++ (DisseminationFrequencyMarker.encode message.disseminationFrequencyMarker)))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (RealTimeIndexMessage × List UInt8) := do
  let (symbolIndex, bytes) ← decodeUInt 4 bytes
  let (sourceTime, bytes) ← decodeUInt 4 bytes
  let (sourceSeqNum, bytes) ← decodeUInt 4 bytes
  let (systemId, bytes) ← decodeUInt 4 bytes
  let (indexLevel, bytes) ← decodeUInt 4 bytes
  let (sessionHigh, bytes) ← decodeUInt 4 bytes
  let (sessionLow, bytes) ← decodeUInt 4 bytes
  let (indIndexOpeningPortfolio, bytes) ← decodeUInt 4 bytes
  let (percentChangeToi, bytes) ← decodeUInt 4 bytes
  let (pctChangeIndexValPrevSession, bytes) ← decodeUInt 4 bytes
  let (pctChangeIndexValPrevYear, bytes) ← decodeUInt 4 bytes
  let (toi, bytes) ← decodeUInt 4 bytes
  let (pointChange, bytes) ← decodeUInt 4 bytes
  let (valueTrading, bytes) ← decodeUInt 8 bytes
  let (indexValueBid, bytes) ← decodeUInt 4 bytes
  let (indexValueAsk, bytes) ← decodeUInt 4 bytes
  let (midSpreadIndex, bytes) ← decodeUInt 4 bytes
  let (differenceCentralSpread, bytes) ← decodeUInt 4 bytes
  let (numOfActiveInstruments, bytes) ← decodeUInt 2 bytes
  let (numOfInstrOfDecreasingQt, bytes) ← decodeUInt 2 bytes
  let (numOfInstrOfIncreasingQt, bytes) ← decodeUInt 2 bytes
  let (numOfInstrOfUnchangedQt, bytes) ← decodeUInt 2 bytes
  let (sourceTimeMicroSecs, bytes) ← decodeUInt 2 bytes
  let (levelScaleCode, bytes) ← decodeUInt 1 bytes
  let (timeFirstHigh, bytes) ← Alpha.decode 6 bytes
  let (timeFirstLow, bytes) ← Alpha.decode 6 bytes
  let (indexStatusIndicator, bytes) ← Alpha.decode 2 bytes
  let (indexLevelCode, bytes) ← IndexLevelCode.decode bytes
  let (markerPercentChangeToi, bytes) ← MarkerPercentChangeToi.decode bytes
  let (markerPctChgIndexValPrevSess, bytes) ← Alpha.decode 1 bytes
  let (markerPctChgIndexValPrevYear, bytes) ← Alpha.decode 1 bytes
  let (markerPointChange, bytes) ← MarkerPointChange.decode bytes
  let (markerDifferenceCentralSpread, bytes) ← MarkerDifferenceCentralSpread.decode bytes
  let (disseminationFrequencyMarker, bytes) ← DisseminationFrequencyMarker.decode bytes
  pure ({ symbolIndex, sourceTime, sourceSeqNum, systemId, indexLevel, sessionHigh, sessionLow, indIndexOpeningPortfolio, percentChangeToi, pctChangeIndexValPrevSession, pctChangeIndexValPrevYear, toi, pointChange, valueTrading, indexValueBid, indexValueAsk, midSpreadIndex, differenceCentralSpread, numOfActiveInstruments, numOfInstrOfDecreasingQt, numOfInstrOfIncreasingQt, numOfInstrOfUnchangedQt, sourceTimeMicroSecs, levelScaleCode, timeFirstHigh, timeFirstLow, indexStatusIndicator, indexLevelCode, markerPercentChangeToi, markerPctChgIndexValPrevSess, markerPctChgIndexValPrevYear, markerPointChange, markerDifferenceCentralSpread, disseminationFrequencyMarker }, bytes)

@[simp] theorem encode_length (message : RealTimeIndexMessage) : (encode message).length = 108 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, IndexLevelCode.encode_length, MarkerPercentChangeToi.encode_length, MarkerPointChange.encode_length, MarkerDifferenceCentralSpread.encode_length, DisseminationFrequencyMarker.encode_length]

theorem encode_length_pos (message : RealTimeIndexMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : RealTimeIndexMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, IndexLevelCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarkerPercentChangeToi.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarkerPointChange.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarkerDifferenceCentralSpread.decode_encode, some_bind]
  dsimp only
  rw [DisseminationFrequencyMarker.decode_encode, some_bind]
  rfl

end RealTimeIndexMessage

/-- Index Summary Message: 100 bytes -/
structure IndexSummaryMessage where
  symbolIndex : BitVec 32
  sourceTime : BitVec 32
  sourceSeqNum : BitVec 32
  systemId : BitVec 32
  closingIndexValue : BitVec 32
  indOpeningPortfolio : BitVec 32
  openingIndexValue : BitVec 32
  sessionHigh : BitVec 32
  sessionLow : BitVec 32
  pctChgHighIndexValPrevSession : BitVec 32
  pctChgLowIndexValPrevSession : BitVec 32
  pctChangeIndexValPrevSession : BitVec 32
  pctChangeIndexValPrevYear : BitVec 32
  capitalisationPortfolio : BitVec 32
  indexAdjustmentCoefficient : BitVec 32
  sourceTimeMicroSecs : BitVec 16
  levelScaleCode : BitVec 8
  capitalisationScaleCode : BitVec 8
  indexAdjustmentScaleCode : BitVec 8
  timeClosing : Alpha 6
  timeOpening : Alpha 6
  timeFullOpening : Alpha 6
  timeHigh : Alpha 6
  timeLow : Alpha 6
  markerHigh : MarkerHigh
  markerLow : MarkerLow
  markerClosingPrevSession : MarkerClosingPrevSession
  markerClosingPrevYear : MarkerClosingPrevYear
  reserved1 : Alpha 1
  deriving DecidableEq, Repr

namespace IndexSummaryMessage

def encode (message : IndexSummaryMessage) : List UInt8 :=
  encodeUInt 4 message.symbolIndex
    ++ (encodeUInt 4 message.sourceTime
    ++ (encodeUInt 4 message.sourceSeqNum
    ++ (encodeUInt 4 message.systemId
    ++ (encodeUInt 4 message.closingIndexValue
    ++ (encodeUInt 4 message.indOpeningPortfolio
    ++ (encodeUInt 4 message.openingIndexValue
    ++ (encodeUInt 4 message.sessionHigh
    ++ (encodeUInt 4 message.sessionLow
    ++ (encodeUInt 4 message.pctChgHighIndexValPrevSession
    ++ (encodeUInt 4 message.pctChgLowIndexValPrevSession
    ++ (encodeUInt 4 message.pctChangeIndexValPrevSession
    ++ (encodeUInt 4 message.pctChangeIndexValPrevYear
    ++ (encodeUInt 4 message.capitalisationPortfolio
    ++ (encodeUInt 4 message.indexAdjustmentCoefficient
    ++ (encodeUInt 2 message.sourceTimeMicroSecs
    ++ (encodeUInt 1 message.levelScaleCode
    ++ (encodeUInt 1 message.capitalisationScaleCode
    ++ (encodeUInt 1 message.indexAdjustmentScaleCode
    ++ (Alpha.encode message.timeClosing
    ++ (Alpha.encode message.timeOpening
    ++ (Alpha.encode message.timeFullOpening
    ++ (Alpha.encode message.timeHigh
    ++ (Alpha.encode message.timeLow
    ++ (MarkerHigh.encode message.markerHigh
    ++ (MarkerLow.encode message.markerLow
    ++ (MarkerClosingPrevSession.encode message.markerClosingPrevSession
    ++ (MarkerClosingPrevYear.encode message.markerClosingPrevYear
    ++ (Alpha.encode message.reserved1))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (IndexSummaryMessage × List UInt8) := do
  let (symbolIndex, bytes) ← decodeUInt 4 bytes
  let (sourceTime, bytes) ← decodeUInt 4 bytes
  let (sourceSeqNum, bytes) ← decodeUInt 4 bytes
  let (systemId, bytes) ← decodeUInt 4 bytes
  let (closingIndexValue, bytes) ← decodeUInt 4 bytes
  let (indOpeningPortfolio, bytes) ← decodeUInt 4 bytes
  let (openingIndexValue, bytes) ← decodeUInt 4 bytes
  let (sessionHigh, bytes) ← decodeUInt 4 bytes
  let (sessionLow, bytes) ← decodeUInt 4 bytes
  let (pctChgHighIndexValPrevSession, bytes) ← decodeUInt 4 bytes
  let (pctChgLowIndexValPrevSession, bytes) ← decodeUInt 4 bytes
  let (pctChangeIndexValPrevSession, bytes) ← decodeUInt 4 bytes
  let (pctChangeIndexValPrevYear, bytes) ← decodeUInt 4 bytes
  let (capitalisationPortfolio, bytes) ← decodeUInt 4 bytes
  let (indexAdjustmentCoefficient, bytes) ← decodeUInt 4 bytes
  let (sourceTimeMicroSecs, bytes) ← decodeUInt 2 bytes
  let (levelScaleCode, bytes) ← decodeUInt 1 bytes
  let (capitalisationScaleCode, bytes) ← decodeUInt 1 bytes
  let (indexAdjustmentScaleCode, bytes) ← decodeUInt 1 bytes
  let (timeClosing, bytes) ← Alpha.decode 6 bytes
  let (timeOpening, bytes) ← Alpha.decode 6 bytes
  let (timeFullOpening, bytes) ← Alpha.decode 6 bytes
  let (timeHigh, bytes) ← Alpha.decode 6 bytes
  let (timeLow, bytes) ← Alpha.decode 6 bytes
  let (markerHigh, bytes) ← MarkerHigh.decode bytes
  let (markerLow, bytes) ← MarkerLow.decode bytes
  let (markerClosingPrevSession, bytes) ← MarkerClosingPrevSession.decode bytes
  let (markerClosingPrevYear, bytes) ← MarkerClosingPrevYear.decode bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  pure ({ symbolIndex, sourceTime, sourceSeqNum, systemId, closingIndexValue, indOpeningPortfolio, openingIndexValue, sessionHigh, sessionLow, pctChgHighIndexValPrevSession, pctChgLowIndexValPrevSession, pctChangeIndexValPrevSession, pctChangeIndexValPrevYear, capitalisationPortfolio, indexAdjustmentCoefficient, sourceTimeMicroSecs, levelScaleCode, capitalisationScaleCode, indexAdjustmentScaleCode, timeClosing, timeOpening, timeFullOpening, timeHigh, timeLow, markerHigh, markerLow, markerClosingPrevSession, markerClosingPrevYear, reserved1 }, bytes)

@[simp] theorem encode_length (message : IndexSummaryMessage) : (encode message).length = 100 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, MarkerHigh.encode_length, MarkerLow.encode_length, MarkerClosingPrevSession.encode_length, MarkerClosingPrevYear.encode_length]

theorem encode_length_pos (message : IndexSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : IndexSummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarkerHigh.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarkerLow.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarkerClosingPrevSession.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarkerClosingPrevYear.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end IndexSummaryMessage

/-- Index Portfolio Component: 32 bytes -/
structure IndexPortfolioComponent where
  instrumentIsin : Alpha 12
  instrumentAbbrevName : Alpha 10
  instrumentPacket : Alpha 10
  deriving DecidableEq, Repr

namespace IndexPortfolioComponent

def encode (message : IndexPortfolioComponent) : List UInt8 :=
  Alpha.encode message.instrumentIsin
    ++ (Alpha.encode message.instrumentAbbrevName
    ++ (Alpha.encode message.instrumentPacket))

def decode (bytes : List UInt8) : Option (IndexPortfolioComponent × List UInt8) := do
  let (instrumentIsin, bytes) ← Alpha.decode 12 bytes
  let (instrumentAbbrevName, bytes) ← Alpha.decode 10 bytes
  let (instrumentPacket, bytes) ← Alpha.decode 10 bytes
  pure ({ instrumentIsin, instrumentAbbrevName, instrumentPacket }, bytes)

@[simp] theorem encode_length (message : IndexPortfolioComponent) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : IndexPortfolioComponent) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IndexPortfolioComponent) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end IndexPortfolioComponent

/-- Index Portfolio Message: 700 bytes -/
structure IndexPortfolioMessage where
  symbolIndex : BitVec 32
  sourceTime : BitVec 32
  sourceSeqNum : BitVec 32
  systemId : BitVec 32
  indexAdjustmentCoefficient : BitVec 32
  levelCashPortfolio : BitVec 32
  valueLastClosingIndex : BitVec 32
  numberOfComponents : BitVec 16
  sourceTimeMicroSecs : BitVec 16
  indexAdjustmentScaleCode : BitVec 8
  cashPortfolioScaleCode : BitVec 8
  levelScaleCode : BitVec 8
  indexPortfolioComponent : Exact 20 IndexPortfolioComponent
  dateValidity : Alpha 8
  indexCurrency : Alpha 3
  indexStatusIndicator : Alpha 2
  indexPresSeq : Alpha 2
  modeIndexDissemination : ModeIndexDissemination
  productClassification : ProductClassification
  openingCalcFormula : OpeningCalcFormula
  reserved1 : Alpha 1
  toiDissemination : ToiDissemination
  spreadDissemination : SpreadDissemination
  tradingValuePublication : TradingValuePublication
  messageContinuation : MessageContinuation
  reserved2 : Alpha 2
  deriving DecidableEq, Repr

namespace IndexPortfolioMessage

def encode (message : IndexPortfolioMessage) : List UInt8 :=
  encodeUInt 4 message.symbolIndex
    ++ (encodeUInt 4 message.sourceTime
    ++ (encodeUInt 4 message.sourceSeqNum
    ++ (encodeUInt 4 message.systemId
    ++ (encodeUInt 4 message.indexAdjustmentCoefficient
    ++ (encodeUInt 4 message.levelCashPortfolio
    ++ (encodeUInt 4 message.valueLastClosingIndex
    ++ (encodeUInt 2 message.numberOfComponents
    ++ (encodeUInt 2 message.sourceTimeMicroSecs
    ++ (encodeUInt 1 message.indexAdjustmentScaleCode
    ++ (encodeUInt 1 message.cashPortfolioScaleCode
    ++ (encodeUInt 1 message.levelScaleCode
    ++ (encodeMany IndexPortfolioComponent.encode message.indexPortfolioComponent.val
    ++ (Alpha.encode message.dateValidity
    ++ (Alpha.encode message.indexCurrency
    ++ (Alpha.encode message.indexStatusIndicator
    ++ (Alpha.encode message.indexPresSeq
    ++ (ModeIndexDissemination.encode message.modeIndexDissemination
    ++ (ProductClassification.encode message.productClassification
    ++ (OpeningCalcFormula.encode message.openingCalcFormula
    ++ (Alpha.encode message.reserved1
    ++ (ToiDissemination.encode message.toiDissemination
    ++ (SpreadDissemination.encode message.spreadDissemination
    ++ (TradingValuePublication.encode message.tradingValuePublication
    ++ (MessageContinuation.encode message.messageContinuation
    ++ (Alpha.encode message.reserved2)))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (IndexPortfolioMessage × List UInt8) := do
  let (symbolIndex, bytes) ← decodeUInt 4 bytes
  let (sourceTime, bytes) ← decodeUInt 4 bytes
  let (sourceSeqNum, bytes) ← decodeUInt 4 bytes
  let (systemId, bytes) ← decodeUInt 4 bytes
  let (indexAdjustmentCoefficient, bytes) ← decodeUInt 4 bytes
  let (levelCashPortfolio, bytes) ← decodeUInt 4 bytes
  let (valueLastClosingIndex, bytes) ← decodeUInt 4 bytes
  let (numberOfComponents, bytes) ← decodeUInt 2 bytes
  let (sourceTimeMicroSecs, bytes) ← decodeUInt 2 bytes
  let (indexAdjustmentScaleCode, bytes) ← decodeUInt 1 bytes
  let (cashPortfolioScaleCode, bytes) ← decodeUInt 1 bytes
  let (levelScaleCode, bytes) ← decodeUInt 1 bytes
  let (indexPortfolioComponent_, bytes) ← decodeMany IndexPortfolioComponent.decode 20 bytes
  let (dateValidity, bytes) ← Alpha.decode 8 bytes
  let (indexCurrency, bytes) ← Alpha.decode 3 bytes
  let (indexStatusIndicator, bytes) ← Alpha.decode 2 bytes
  let (indexPresSeq, bytes) ← Alpha.decode 2 bytes
  let (modeIndexDissemination, bytes) ← ModeIndexDissemination.decode bytes
  let (productClassification, bytes) ← ProductClassification.decode bytes
  let (openingCalcFormula, bytes) ← OpeningCalcFormula.decode bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (toiDissemination, bytes) ← ToiDissemination.decode bytes
  let (spreadDissemination, bytes) ← SpreadDissemination.decode bytes
  let (tradingValuePublication, bytes) ← TradingValuePublication.decode bytes
  let (messageContinuation, bytes) ← MessageContinuation.decode bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  if fits_indexPortfolioComponent : indexPortfolioComponent_.length = 20 then
    pure ({ symbolIndex, sourceTime, sourceSeqNum, systemId, indexAdjustmentCoefficient, levelCashPortfolio, valueLastClosingIndex, numberOfComponents, sourceTimeMicroSecs, indexAdjustmentScaleCode, cashPortfolioScaleCode, levelScaleCode, indexPortfolioComponent := ⟨indexPortfolioComponent_, fits_indexPortfolioComponent⟩, dateValidity, indexCurrency, indexStatusIndicator, indexPresSeq, modeIndexDissemination, productClassification, openingCalcFormula, reserved1, toiDissemination, spreadDissemination, tradingValuePublication, messageContinuation, reserved2 }, bytes)
  else none

@[simp] theorem encode_length (message : IndexPortfolioMessage) : (encode message).length = 700 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeMany_length_const IndexPortfolioComponent.encode 32 IndexPortfolioComponent.encode_length, message.indexPortfolioComponent.length_eq, Alpha.encode_length, ModeIndexDissemination.encode_length, ProductClassification.encode_length, OpeningCalcFormula.encode_length, ToiDissemination.encode_length, SpreadDissemination.encode_length, TradingValuePublication.encode_length, MessageContinuation.encode_length]

theorem encode_length_pos (message : IndexPortfolioMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : IndexPortfolioMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeMany_exact 20 IndexPortfolioComponent.encode IndexPortfolioComponent.decode IndexPortfolioComponent.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ModeIndexDissemination.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ProductClassification.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpeningCalcFormula.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ToiDissemination.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SpreadDissemination.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradingValuePublication.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MessageContinuation.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.indexPortfolioComponent.length_eq]
  rfl

end IndexPortfolioMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | realTimeIndexMessage (message : RealTimeIndexMessage) -- 546
  | indexSummaryMessage (message : IndexSummaryMessage) -- 547
  | indexPortfolioMessage (message : IndexPortfolioMessage) -- 548
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 16
  | .realTimeIndexMessage _ => 546
  | .indexSummaryMessage _ => 547
  | .indexPortfolioMessage _ => 548

def encode : Payload → List UInt8
  | .realTimeIndexMessage message => RealTimeIndexMessage.encode message
  | .indexSummaryMessage message => IndexSummaryMessage.encode message
  | .indexPortfolioMessage message => IndexPortfolioMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 700 := by
  cases message with
  | realTimeIndexMessage inner =>
    simp only [encode, RealTimeIndexMessage.encode_length]
    omega
  | indexSummaryMessage inner =>
    simp only [encode, IndexSummaryMessage.encode_length]
    omega
  | indexPortfolioMessage inner =>
    simp only [encode, IndexPortfolioMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 546 then (RealTimeIndexMessage.decode bytes).map fun (message, rest) => (.realTimeIndexMessage message, rest)
  else if tag = 547 then (IndexSummaryMessage.decode bytes).map fun (message, rest) => (.indexSummaryMessage message, rest)
  else if tag = 548 then (IndexPortfolioMessage.decode bytes).map fun (message, rest) => (.indexPortfolioMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message -/
structure Message where
  payload : Payload
  deriving DecidableEq, Repr

namespace Message

def encodeBody (message : Message) : List UInt8 :=
  encodeUInt 2 (Payload.tag message.payload)
    ++ (Payload.encode message.payload)

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (messageType, bytes) ← decodeUInt 2 bytes
  let (payload, bytes) ← Payload.decode messageType bytes
  pure ({ payload }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 0 < 256 ^ 2 := by
  unfold encodeBody
  cases message.payload with
  | realTimeIndexMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, RealTimeIndexMessage.encode_length]
    omega
  | indexSummaryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, IndexSummaryMessage.encode_length]
    omega
  | indexPortfolioMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, IndexPortfolioMessage.encode_length]
    omega

/-- Size rule: Message Size counts the bytes after it, so it is written from the body and checked on decode -/
def encode : Message → List UInt8 :=
  encodeFramed 2 0 encodeBody

def decode : List UInt8 → Option (Message × List UInt8) :=
  decodeFramed 2 0 decodeBody

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 2 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end Message

/-- Message Buffer -/
structure MessageBuffer (numberMsgEntries : BitVec 8) where
  message : Exact numberMsgEntries.toNat Message
  deriving DecidableEq, Repr

namespace MessageBuffer

def encode {numberMsgEntries : BitVec 8} (message : MessageBuffer numberMsgEntries) : List UInt8 :=
  encodeMany Message.encode message.message.val

def decode (numberMsgEntries : BitVec 8) (bytes : List UInt8) : Option (MessageBuffer numberMsgEntries × List UInt8) := do
  let (message_, bytes) ← decodeMany Message.decode numberMsgEntries.toNat bytes
  if fits_message : message_.length = numberMsgEntries.toNat then
    pure ({ message := ⟨message_, fits_message⟩ }, bytes)
  else none

@[simp] theorem decode_encode (numberMsgEntries : BitVec 8) (message : MessageBuffer numberMsgEntries) (rest : List UInt8) :
    decode numberMsgEntries (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeMany_exact numberMsgEntries.toNat Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_eq]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (numberMsgEntries : BitVec 8) (message : MessageBuffer numberMsgEntries) : decode numberMsgEntries (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode numberMsgEntries message []

end MessageBuffer

/-- Message Buffer -/
structure MessageBufferZlib where
  payload : List UInt8
  deriving DecidableEq, Repr

namespace MessageBufferZlib

def encode (message : MessageBufferZlib) : List UInt8 :=
  encodeMany Byte.encode message.payload

def decode (bytes : List UInt8) : Option MessageBufferZlib := do
  let payload ← decodeAll Byte.decode bytes.length bytes
  pure { payload }

theorem decode_encode (message : MessageBufferZlib) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany Byte.encode Byte.decode Byte.decode_encode Byte.encode_length_pos message.payload _ (encodeMany_length_ge Byte.encode Byte.encode_length_pos message.payload), some_bind]
  rfl

end MessageBufferZlib

/-- The Message Buffer, as bytes when Delivery Flag says it was Zlib transformed and as it lies when it says it was not -/
inductive MessageBufferBody (numberMsgEntries : BitVec 8) where
  | zlib (tag : { v : BitVec 8 // 15 < v }) (message : MessageBufferZlib) -- 15 < tag
  | plain (tag : { v : BitVec 8 // ¬ (15 < v) }) (message : MessageBuffer numberMsgEntries) -- every other value
  deriving DecidableEq, Repr

namespace MessageBufferBody

/-- The Delivery Flag each body is read by -/
def tag {numberMsgEntries : BitVec 8} : MessageBufferBody numberMsgEntries → BitVec 8
  | .zlib tag _ => tag.val
  | .plain tag _ => tag.val

def encode {numberMsgEntries : BitVec 8} : MessageBufferBody numberMsgEntries → List UInt8
  | .zlib _ message => MessageBufferZlib.encode message
  | .plain _ message => MessageBuffer.encode message

/-- Decoded from the whole of what holds it: a body that reads to its end takes it all, any other must leave nothing -/
def decode (numberMsgEntries : BitVec 8) (tag : BitVec 8) (bytes : List UInt8) : Option (MessageBufferBody numberMsgEntries) :=
  if h : 15 < tag then (MessageBufferZlib.decode bytes).map fun message => .zlib ⟨tag, h⟩ message
  else (MessageBuffer.decode numberMsgEntries bytes).bind fun (message, rest) => if rest.isEmpty then some (.plain ⟨tag, h⟩ message) else none

theorem decode_encode (numberMsgEntries : BitVec 8) (message : MessageBufferBody numberMsgEntries) :
    decode numberMsgEntries (tag message) (encode message) = some message := by
  cases message with
  | zlib t m =>
    obtain ⟨v, h⟩ := t
    simp only [tag, encode, decode, h, reduceDIte, MessageBufferZlib.decode_encode, Option.map_some]
  | plain t m =>
    obtain ⟨v, h⟩ := t
    simp only [tag, encode, decode, h, reduceDIte, MessageBuffer.decode_encode_nil]
    rfl

end MessageBufferBody

/-- Packet -/
structure Packet where
  packetLength : BitVec 16
  packetType : BitVec 16
  packetSequenceNumber : BitVec 32
  sendTime : BitVec 32
  serviceId : BitVec 16
  numberMsgEntries : BitVec 8
  messageBuffer : MessageBufferBody numberMsgEntries
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUInt 2 message.packetLength
    ++ (encodeUInt 2 message.packetType
    ++ (encodeUInt 4 message.packetSequenceNumber
    ++ (encodeUInt 4 message.sendTime
    ++ (encodeUInt 2 message.serviceId
    ++ (encodeUInt 1 (MessageBufferBody.tag message.messageBuffer)
    ++ (encodeUInt 1 message.numberMsgEntries
    ++ (MessageBufferBody.encode message.messageBuffer)))))))

def decode (bytes : List UInt8) : Option Packet := do
  let (packetLength, bytes) ← decodeUInt 2 bytes
  let (packetType, bytes) ← decodeUInt 2 bytes
  let (packetSequenceNumber, bytes) ← decodeUInt 4 bytes
  let (sendTime, bytes) ← decodeUInt 4 bytes
  let (serviceId, bytes) ← decodeUInt 2 bytes
  let (deliveryFlag, bytes) ← decodeUInt 1 bytes
  let (numberMsgEntries, bytes) ← decodeUInt 1 bytes
  let messageBuffer ← MessageBufferBody.decode numberMsgEntries deliveryFlag bytes
  pure { packetLength, packetType, packetSequenceNumber, sendTime, serviceId, numberMsgEntries, messageBuffer }

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [MessageBufferBody.decode_encode, some_bind]
  rfl

end Packet

end Omi.GpwBondspotIndicesXdpV68
