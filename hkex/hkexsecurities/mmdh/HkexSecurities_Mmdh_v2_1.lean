import Wire

/-!
# Hong Kong Exchanges and Clearing Orion Market Data Cash Mainland Market Data Hub v2.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.

Note: a News Type of any value but 4544590 or 4544579 reads Headline Utf16: the value is carried
with the proof no case lists it, so what is read is written back

Note: a News Type of any value but 4544590 or 4544579 reads News Line Utf16: the value is carried
with the proof no case lists it, so what is read is written back

Note: News Line is 160 bytes whichever arm the model names (News Line Ascii, News Line Utf16): the
field choosing it is read in another record, so it is read as News Line Utf16, which holds any bytes
of that width, and which arm applies is left to what is built on the definition.

Note: Message's Msg Length is written from its body but not checked on decode, since the body has no
bound the prefix must fit; the body is read by its content

License: MIT No Attribution
-/

namespace Omi.HkexHkexsecuritiesMmdhOmdV21

/-- Bq More Flag: one byte code -/
def BqMoreFlag.codes : List UInt8 :=
  [0x59, 0x4E]

inductive BqMoreFlag where
  | moreBrokerNumbersExistInTheQueue -- More Broker Numbers Exist In The Queue
  | noMoreExist -- No More Exist
  | unlisted (byte : { byte : UInt8 // byte ∉ BqMoreFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BqMoreFlag

def toByte : BqMoreFlag → UInt8
  | .moreBrokerNumbersExistInTheQueue => 0x59
  | .noMoreExist => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BqMoreFlag :=
  if byte = 0x59 then .moreBrokerNumbersExistInTheQueue
  else .noMoreExist

def ofByte (byte : UInt8) : BqMoreFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BqMoreFlag) : ofByte value.toByte = value := by
  cases value with
  | moreBrokerNumbersExistInTheQueue => decide
  | noMoreExist => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BqMoreFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BqMoreFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BqMoreFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : BqMoreFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : BqMoreFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BqMoreFlag

/-- Type: one byte code -/
def Type_.codes : List UInt8 :=
  [0x42, 0x53]

inductive Type_ where
  | brokerNumber -- Broker Number
  | numberOfSpread -- Number Of Spread
  | unlisted (byte : { byte : UInt8 // byte ∉ Type_.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Type_

def toByte : Type_ → UInt8
  | .brokerNumber => 0x42
  | .numberOfSpread => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Type_ :=
  if byte = 0x42 then .brokerNumber
  else .numberOfSpread

def ofByte (byte : UInt8) : Type_ :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Type_) : ofByte value.toByte = value := by
  cases value with
  | brokerNumber => decide
  | numberOfSpread => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Type_) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Type_ × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Type_) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Type_) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Type_) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Type_

/-- Index Source: one byte code -/
def IndexSource.codes : List UInt8 :=
  [0x43, 0x48, 0x53]

inductive IndexSource where
  | csiAndCes -- Csi And Ces
  | hsi -- Hsi
  | sAndP -- S And P
  | unlisted (byte : { byte : UInt8 // byte ∉ IndexSource.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace IndexSource

def toByte : IndexSource → UInt8
  | .csiAndCes => 0x43
  | .hsi => 0x48
  | .sAndP => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : IndexSource :=
  if byte = 0x43 then .csiAndCes
  else if byte = 0x48 then .hsi
  else .sAndP

def ofByte (byte : UInt8) : IndexSource :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : IndexSource) : ofByte value.toByte = value := by
  cases value with
  | csiAndCes => decide
  | hsi => decide
  | sAndP => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : IndexSource) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (IndexSource × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : IndexSource) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : IndexSource) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : IndexSource) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end IndexSource

/-- Index Status: one byte code -/
def IndexStatus.codes : List UInt8 :=
  [0x43, 0x49, 0x4F, 0x50, 0x52, 0x53, 0x54]

inductive IndexStatus where
  | closingValue -- Closing Value
  | indicative -- Indicative
  | openingIndex -- Opening Index
  | lastCloseValuePreviousSession -- Last Close Value Previous Session
  | preliminaryClose -- Preliminary Close
  | stopLossIndex -- Stop Loss Index
  | realTimeIndexValue -- Real Time Index Value
  | unlisted (byte : { byte : UInt8 // byte ∉ IndexStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace IndexStatus

def toByte : IndexStatus → UInt8
  | .closingValue => 0x43
  | .indicative => 0x49
  | .openingIndex => 0x4F
  | .lastCloseValuePreviousSession => 0x50
  | .preliminaryClose => 0x52
  | .stopLossIndex => 0x53
  | .realTimeIndexValue => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : IndexStatus :=
  if byte = 0x43 then .closingValue
  else if byte = 0x49 then .indicative
  else if byte = 0x4F then .openingIndex
  else if byte = 0x50 then .lastCloseValuePreviousSession
  else if byte = 0x52 then .preliminaryClose
  else if byte = 0x53 then .stopLossIndex
  else .realTimeIndexValue

def ofByte (byte : UInt8) : IndexStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : IndexStatus) : ofByte value.toByte = value := by
  cases value with
  | closingValue => decide
  | indicative => decide
  | openingIndex => decide
  | lastCloseValuePreviousSession => decide
  | preliminaryClose => decide
  | stopLossIndex => decide
  | realTimeIndexValue => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : IndexStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (IndexStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : IndexStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : IndexStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : IndexStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end IndexStatus

/-- Exception: one byte code -/
def Exception.codes : List UInt8 :=
  [0x23, 0x20]

inductive Exception where
  | indexWithHsilDefinedExceptionalRuleApplied -- Index With Hsil Defined Exceptional Rule Applied
  | normalIndex -- Normal Index
  | unlisted (byte : { byte : UInt8 // byte ∉ Exception.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Exception

def toByte : Exception → UInt8
  | .indexWithHsilDefinedExceptionalRuleApplied => 0x23
  | .normalIndex => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Exception :=
  if byte = 0x23 then .indexWithHsilDefinedExceptionalRuleApplied
  else .normalIndex

def ofByte (byte : UInt8) : Exception :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Exception) : ofByte value.toByte = value := by
  cases value with
  | indexWithHsilDefinedExceptionalRuleApplied => decide
  | normalIndex => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Exception) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Exception × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Exception) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Exception) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Exception) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Exception

/-- Cancel Flag: one byte code -/
def CancelFlag.codes : List UInt8 :=
  [0x59, 0x4E]

inductive CancelFlag where
  | cancelled -- Cancelled
  | notCancelled -- Not Cancelled
  | unlisted (byte : { byte : UInt8 // byte ∉ CancelFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CancelFlag

def toByte : CancelFlag → UInt8
  | .cancelled => 0x59
  | .notCancelled => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CancelFlag :=
  if byte = 0x59 then .cancelled
  else .notCancelled

def ofByte (byte : UInt8) : CancelFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CancelFlag) : ofByte value.toByte = value := by
  cases value with
  | cancelled => decide
  | notCancelled => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CancelFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CancelFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CancelFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CancelFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CancelFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CancelFlag

/-- Last Fragment: one byte code -/
def LastFragment.codes : List UInt8 :=
  [0x59, 0x4E]

inductive LastFragment where
  | complete -- Complete
  | notComplete -- Not Complete
  | unlisted (byte : { byte : UInt8 // byte ∉ LastFragment.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LastFragment

def toByte : LastFragment → UInt8
  | .complete => 0x59
  | .notComplete => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LastFragment :=
  if byte = 0x59 then .complete
  else .notComplete

def ofByte (byte : UInt8) : LastFragment :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LastFragment) : ofByte value.toByte = value := by
  cases value with
  | complete => decide
  | notComplete => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LastFragment) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LastFragment × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LastFragment) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : LastFragment) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : LastFragment) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LastFragment

/-- Order Imbalance Direction: one byte code -/
def OrderImbalanceDirection.codes : List UInt8 :=
  [0x4E, 0x42, 0x53, 0x20]

inductive OrderImbalanceDirection where
  | buyEqualsSell -- Buy Equals Sell
  | buySurplus -- Buy Surplus
  | sellSurplus -- Sell Surplus
  | notApplicableIepNotAvailable -- Not Applicable Iep Not Available
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderImbalanceDirection.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderImbalanceDirection

def toByte : OrderImbalanceDirection → UInt8
  | .buyEqualsSell => 0x4E
  | .buySurplus => 0x42
  | .sellSurplus => 0x53
  | .notApplicableIepNotAvailable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderImbalanceDirection :=
  if byte = 0x4E then .buyEqualsSell
  else if byte = 0x42 then .buySurplus
  else if byte = 0x53 then .sellSurplus
  else .notApplicableIepNotAvailable

def ofByte (byte : UInt8) : OrderImbalanceDirection :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderImbalanceDirection) : ofByte value.toByte = value := by
  cases value with
  | buyEqualsSell => decide
  | buySurplus => decide
  | sellSurplus => decide
  | notApplicableIepNotAvailable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderImbalanceDirection) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderImbalanceDirection × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderImbalanceDirection) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OrderImbalanceDirection) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OrderImbalanceDirection) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderImbalanceDirection

/-- Vcm Flag: one byte code -/
def VcmFlag.codes : List UInt8 :=
  [0x59, 0x4E]

inductive VcmFlag where
  | vcmApplicable -- Vcm Applicable
  | vcmNotApplicable -- Vcm Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ VcmFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace VcmFlag

def toByte : VcmFlag → UInt8
  | .vcmApplicable => 0x59
  | .vcmNotApplicable => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : VcmFlag :=
  if byte = 0x59 then .vcmApplicable
  else .vcmNotApplicable

def ofByte (byte : UInt8) : VcmFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : VcmFlag) : ofByte value.toByte = value := by
  cases value with
  | vcmApplicable => decide
  | vcmNotApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : VcmFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (VcmFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : VcmFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : VcmFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : VcmFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end VcmFlag

/-- Short Sell Flag: one byte code -/
def ShortSellFlag.codes : List UInt8 :=
  [0x59, 0x4E]

inductive ShortSellFlag where
  | shortSellAllowed -- Short Sell Allowed
  | shortSellNotAllowed -- Short Sell Not Allowed
  | unlisted (byte : { byte : UInt8 // byte ∉ ShortSellFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ShortSellFlag

def toByte : ShortSellFlag → UInt8
  | .shortSellAllowed => 0x59
  | .shortSellNotAllowed => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ShortSellFlag :=
  if byte = 0x59 then .shortSellAllowed
  else .shortSellNotAllowed

def ofByte (byte : UInt8) : ShortSellFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ShortSellFlag) : ofByte value.toByte = value := by
  cases value with
  | shortSellAllowed => decide
  | shortSellNotAllowed => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ShortSellFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ShortSellFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ShortSellFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ShortSellFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ShortSellFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ShortSellFlag

/-- Cas Flag: one byte code -/
def CasFlag.codes : List UInt8 :=
  [0x59, 0x4E]

inductive CasFlag where
  | casApplicable -- Cas Applicable
  | casNotApplicable -- Cas Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ CasFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CasFlag

def toByte : CasFlag → UInt8
  | .casApplicable => 0x59
  | .casNotApplicable => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CasFlag :=
  if byte = 0x59 then .casApplicable
  else .casNotApplicable

def ofByte (byte : UInt8) : CasFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CasFlag) : ofByte value.toByte = value := by
  cases value with
  | casApplicable => decide
  | casNotApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CasFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CasFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CasFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CasFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CasFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CasFlag

/-- Ccass Flag: one byte code -/
def CcassFlag.codes : List UInt8 :=
  [0x59, 0x4E]

inductive CcassFlag where
  | ccassSecurity -- Ccass Security
  | nonCcassSecurity -- Non Ccass Security
  | unlisted (byte : { byte : UInt8 // byte ∉ CcassFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CcassFlag

def toByte : CcassFlag → UInt8
  | .ccassSecurity => 0x59
  | .nonCcassSecurity => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CcassFlag :=
  if byte = 0x59 then .ccassSecurity
  else .nonCcassSecurity

def ofByte (byte : UInt8) : CcassFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CcassFlag) : ofByte value.toByte = value := by
  cases value with
  | ccassSecurity => decide
  | nonCcassSecurity => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CcassFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CcassFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CcassFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CcassFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CcassFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CcassFlag

/-- Dummy Security Flag: one byte code -/
def DummySecurityFlag.codes : List UInt8 :=
  [0x59, 0x4E]

inductive DummySecurityFlag where
  | dummySecurity -- Dummy Security
  | normalSecurity -- Normal Security
  | unlisted (byte : { byte : UInt8 // byte ∉ DummySecurityFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DummySecurityFlag

def toByte : DummySecurityFlag → UInt8
  | .dummySecurity => 0x59
  | .normalSecurity => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DummySecurityFlag :=
  if byte = 0x59 then .dummySecurity
  else .normalSecurity

def ofByte (byte : UInt8) : DummySecurityFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DummySecurityFlag) : ofByte value.toByte = value := by
  cases value with
  | dummySecurity => decide
  | normalSecurity => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DummySecurityFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DummySecurityFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DummySecurityFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : DummySecurityFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : DummySecurityFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DummySecurityFlag

/-- Stamp Duty Flag: one byte code -/
def StampDutyFlag.codes : List UInt8 :=
  [0x59, 0x4E]

inductive StampDutyFlag where
  | stampDutyRequired -- Stamp Duty Required
  | stampDutyNotRequired -- Stamp Duty Not Required
  | unlisted (byte : { byte : UInt8 // byte ∉ StampDutyFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace StampDutyFlag

def toByte : StampDutyFlag → UInt8
  | .stampDutyRequired => 0x59
  | .stampDutyNotRequired => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : StampDutyFlag :=
  if byte = 0x59 then .stampDutyRequired
  else .stampDutyNotRequired

def ofByte (byte : UInt8) : StampDutyFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : StampDutyFlag) : ofByte value.toByte = value := by
  cases value with
  | stampDutyRequired => decide
  | stampDutyNotRequired => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : StampDutyFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (StampDutyFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : StampDutyFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : StampDutyFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : StampDutyFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end StampDutyFlag

/-- Pos Flag: one byte code -/
def PosFlag.codes : List UInt8 :=
  [0x59, 0x4E]

inductive PosFlag where
  | posApplicable -- Pos Applicable
  | posNotApplicable -- Pos Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ PosFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PosFlag

def toByte : PosFlag → UInt8
  | .posApplicable => 0x59
  | .posNotApplicable => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PosFlag :=
  if byte = 0x59 then .posApplicable
  else .posNotApplicable

def ofByte (byte : UInt8) : PosFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PosFlag) : ofByte value.toByte = value := by
  cases value with
  | posApplicable => decide
  | posNotApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PosFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PosFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PosFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : PosFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : PosFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PosFlag

/-- Efn Flag: one byte code -/
def EfnFlag.codes : List UInt8 :=
  [0x59, 0x4E]

inductive EfnFlag where
  | efn -- Efn
  | nonEfn -- Non Efn
  | unlisted (byte : { byte : UInt8 // byte ∉ EfnFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EfnFlag

def toByte : EfnFlag → UInt8
  | .efn => 0x59
  | .nonEfn => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EfnFlag :=
  if byte = 0x59 then .efn
  else .nonEfn

def ofByte (byte : UInt8) : EfnFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EfnFlag) : ofByte value.toByte = value := by
  cases value with
  | efn => decide
  | nonEfn => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : EfnFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (EfnFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : EfnFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : EfnFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : EfnFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end EfnFlag

/-- Investor Type: one byte code -/
def InvestorType.codes : List UInt8 :=
  [0x52, 0x50]

inductive InvestorType where
  | retailInvestor -- Retail Investor
  | professionalInvestor -- Professional Investor
  | unlisted (byte : { byte : UInt8 // byte ∉ InvestorType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InvestorType

def toByte : InvestorType → UInt8
  | .retailInvestor => 0x52
  | .professionalInvestor => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : InvestorType :=
  if byte = 0x52 then .retailInvestor
  else .professionalInvestor

def ofByte (byte : UInt8) : InvestorType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InvestorType) : ofByte value.toByte = value := by
  cases value with
  | retailInvestor => decide
  | professionalInvestor => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : InvestorType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (InvestorType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : InvestorType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : InvestorType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : InvestorType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end InvestorType

/-- Call Put Flag: one byte code -/
def CallPutFlag.codes : List UInt8 :=
  [0x43, 0x50, 0x4F]

inductive CallPutFlag where
  | callOrBull -- Call Or Bull
  | putOrBearRange -- Put Or Bear Range
  | others -- Others
  | unlisted (byte : { byte : UInt8 // byte ∉ CallPutFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CallPutFlag

def toByte : CallPutFlag → UInt8
  | .callOrBull => 0x43
  | .putOrBearRange => 0x50
  | .others => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CallPutFlag :=
  if byte = 0x43 then .callOrBull
  else if byte = 0x50 then .putOrBearRange
  else .others

def ofByte (byte : UInt8) : CallPutFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CallPutFlag) : ofByte value.toByte = value := by
  cases value with
  | callOrBull => decide
  | putOrBearRange => decide
  | others => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CallPutFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CallPutFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CallPutFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CallPutFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CallPutFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CallPutFlag

/-- Style: one byte code -/
def Style.codes : List UInt8 :=
  [0x41, 0x45, 0x20]

inductive Style where
  | americanStyle -- American Style
  | europeanStyle -- European Style
  | other -- Other
  | unlisted (byte : { byte : UInt8 // byte ∉ Style.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Style

def toByte : Style → UInt8
  | .americanStyle => 0x41
  | .europeanStyle => 0x45
  | .other => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Style :=
  if byte = 0x41 then .americanStyle
  else if byte = 0x45 then .europeanStyle
  else .other

def ofByte (byte : UInt8) : Style :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Style) : ofByte value.toByte = value := by
  cases value with
  | americanStyle => decide
  | europeanStyle => decide
  | other => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Style) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Style × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Style) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Style) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Style) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Style

/-- Warrant Type: one byte code -/
def WarrantType.codes : List UInt8 :=
  [0x4E, 0x58, 0x30]

inductive WarrantType where
  | normalInstrument -- Normal Instrument
  | exoticInstrument -- Exotic Instrument
  | notAvailable -- Not Available
  | unlisted (byte : { byte : UInt8 // byte ∉ WarrantType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace WarrantType

def toByte : WarrantType → UInt8
  | .normalInstrument => 0x4E
  | .exoticInstrument => 0x58
  | .notAvailable => 0x30
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : WarrantType :=
  if byte = 0x4E then .normalInstrument
  else if byte = 0x58 then .exoticInstrument
  else .notAvailable

def ofByte (byte : UInt8) : WarrantType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : WarrantType) : ofByte value.toByte = value := by
  cases value with
  | normalInstrument => decide
  | exoticInstrument => decide
  | notAvailable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : WarrantType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (WarrantType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : WarrantType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : WarrantType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : WarrantType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end WarrantType

/-- Trading Ses Control Flag: one byte code -/
def TradingSesControlFlag.codes : List UInt8 :=
  [0x30, 0x31]

inductive TradingSesControlFlag where
  | automaticDefault -- Automatic Default
  | manualInvalidatesTheNormalScheduleForTheDay -- Manual Invalidates The Normal Schedule For The Day
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingSesControlFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingSesControlFlag

def toByte : TradingSesControlFlag → UInt8
  | .automaticDefault => 0x30
  | .manualInvalidatesTheNormalScheduleForTheDay => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingSesControlFlag :=
  if byte = 0x30 then .automaticDefault
  else .manualInvalidatesTheNormalScheduleForTheDay

def ofByte (byte : UInt8) : TradingSesControlFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingSesControlFlag) : ofByte value.toByte = value := by
  cases value with
  | automaticDefault => decide
  | manualInvalidatesTheNormalScheduleForTheDay => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradingSesControlFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradingSesControlFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradingSesControlFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TradingSesControlFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TradingSesControlFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradingSesControlFlag

/-- Trd Cancel Flag: one byte code -/
def TrdCancelFlag.codes : List UInt8 :=
  [0x59, 0x4E]

inductive TrdCancelFlag where
  | cancelled -- Cancelled
  | notCancelled -- Not Cancelled
  | unlisted (byte : { byte : UInt8 // byte ∉ TrdCancelFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TrdCancelFlag

def toByte : TrdCancelFlag → UInt8
  | .cancelled => 0x59
  | .notCancelled => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TrdCancelFlag :=
  if byte = 0x59 then .cancelled
  else .notCancelled

def ofByte (byte : UInt8) : TrdCancelFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TrdCancelFlag) : ofByte value.toByte = value := by
  cases value with
  | cancelled => decide
  | notCancelled => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TrdCancelFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TrdCancelFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TrdCancelFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TrdCancelFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TrdCancelFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TrdCancelFlag

/-- Add Odd Lot Order Message: 24 bytes -/
structure AddOddLotOrderMessage where
  securityCode : BitVec 32
  orderId : BitVec 64
  price : BitVec 32
  quantity : BitVec 32
  brokerId : BitVec 16
  side : BitVec 16
  deriving DecidableEq, Repr

namespace AddOddLotOrderMessage

def encode (message : AddOddLotOrderMessage) : List UInt8 :=
  encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 2 message.brokerId
    ++ (encodeUIntLE 2 message.side)))))

def decode (bytes : List UInt8) : Option (AddOddLotOrderMessage × List UInt8) := do
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (brokerId, bytes) ← decodeUIntLE 2 bytes
  let (side, bytes) ← decodeUIntLE 2 bytes
  pure ({ securityCode, orderId, price, quantity, brokerId, side }, bytes)

@[simp] theorem encode_length (message : AddOddLotOrderMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : AddOddLotOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddOddLotOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end AddOddLotOrderMessage

/-- Book Entry: 24 bytes -/
structure BookEntry where
  aggregateQuantity : BitVec 64
  price : BitVec 32
  numberOfOrders : BitVec 32
  side : BitVec 16
  priceLevel : BitVec 8
  updateAction : BitVec 8
  filler4 : Alpha 4
  deriving DecidableEq, Repr

namespace BookEntry

def encode (message : BookEntry) : List UInt8 :=
  encodeUIntLE 8 message.aggregateQuantity
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 4 message.numberOfOrders
    ++ (encodeUIntLE 2 message.side
    ++ (encodeUInt 1 message.priceLevel
    ++ (encodeUInt 1 message.updateAction
    ++ (Alpha.encode message.filler4))))))

def decode (bytes : List UInt8) : Option (BookEntry × List UInt8) := do
  let (aggregateQuantity, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (numberOfOrders, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← decodeUIntLE 2 bytes
  let (priceLevel, bytes) ← decodeUInt 1 bytes
  let (updateAction, bytes) ← decodeUInt 1 bytes
  let (filler4, bytes) ← Alpha.decode 4 bytes
  pure ({ aggregateQuantity, price, numberOfOrders, side, priceLevel, updateAction, filler4 }, bytes)

@[simp] theorem encode_length (message : BookEntry) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : BookEntry) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BookEntry) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BookEntry

/-- Aggregate Order Book Update Message -/
structure AggregateOrderBookUpdateMessage where
  securityCode : BitVec 32
  filler3 : Alpha 3
  bookEntry : Bounded 1 BookEntry
  deriving DecidableEq, Repr

namespace AggregateOrderBookUpdateMessage

def encode (message : AggregateOrderBookUpdateMessage) : List UInt8 :=
  encodeUIntLE 4 message.securityCode
    ++ (Alpha.encode message.filler3
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.bookEntry.val.length)
    ++ (encodeMany BookEntry.encode message.bookEntry.val)))

def decode (bytes : List UInt8) : Option (AggregateOrderBookUpdateMessage × List UInt8) := do
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (filler3, bytes) ← Alpha.decode 3 bytes
  let (noEntries, bytes) ← decodeUInt 1 bytes
  let (bookEntry_, bytes) ← decodeMany BookEntry.decode noEntries.toNat bytes
  if fits_bookEntry : bookEntry_.length < 256 ^ 1 then
    pure ({ securityCode, filler3, bookEntry := ⟨bookEntry_, fits_bookEntry⟩ }, bytes)
  else none

theorem encode_length_pos (message : AggregateOrderBookUpdateMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : AggregateOrderBookUpdateMessage) : (encode message).length ≤ 6128 := by
  have bound_bookEntry := message.bookEntry.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length, encodeMany_length_const BookEntry.encode 24 BookEntry.encode_length]
  omega

@[simp] theorem decode_encode (message : AggregateOrderBookUpdateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 BookEntry.encode BookEntry.decode BookEntry.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.bookEntry.length_lt]
  rfl

end AggregateOrderBookUpdateMessage

/-- Bq Item: 4 bytes -/
structure BqItem where
  item : BitVec 16
  type : Type_
  filler1 : Alpha 1
  deriving DecidableEq, Repr

namespace BqItem

def encode (message : BqItem) : List UInt8 :=
  encodeUIntLE 2 message.item
    ++ (Type_.encode message.type
    ++ (Alpha.encode message.filler1))

def decode (bytes : List UInt8) : Option (BqItem × List UInt8) := do
  let (item, bytes) ← decodeUIntLE 2 bytes
  let (type, bytes) ← Type_.decode bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  pure ({ item, type, filler1 }, bytes)

@[simp] theorem encode_length (message : BqItem) : (encode message).length = 4 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Type_.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : BqItem) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BqItem) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Type_.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BqItem

/-- Broker Queue Message -/
structure BrokerQueueMessage where
  securityCode : BitVec 32
  brokerSide : BitVec 16
  bqMoreFlag : BqMoreFlag
  bqItem : Bounded 1 BqItem
  deriving DecidableEq, Repr

namespace BrokerQueueMessage

def encode (message : BrokerQueueMessage) : List UInt8 :=
  encodeUIntLE 4 message.securityCode
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.bqItem.val.length)
    ++ (encodeUIntLE 2 message.brokerSide
    ++ (BqMoreFlag.encode message.bqMoreFlag
    ++ (encodeMany BqItem.encode message.bqItem.val))))

def decode (bytes : List UInt8) : Option (BrokerQueueMessage × List UInt8) := do
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (itemCount, bytes) ← decodeUInt 1 bytes
  let (brokerSide, bytes) ← decodeUIntLE 2 bytes
  let (bqMoreFlag, bytes) ← BqMoreFlag.decode bytes
  let (bqItem_, bytes) ← decodeMany BqItem.decode itemCount.toNat bytes
  if fits_bqItem : bqItem_.length < 256 ^ 1 then
    pure ({ securityCode, brokerSide, bqMoreFlag, bqItem := ⟨bqItem_, fits_bqItem⟩ }, bytes)
  else none

theorem encode_length_pos (message : BrokerQueueMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : BrokerQueueMessage) : (encode message).length ≤ 1028 := by
  have bound_bqItem := message.bqItem.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, BqMoreFlag.encode_length, encodeMany_length_const BqItem.encode 4 BqItem.encode_length]
  omega

@[simp] theorem decode_encode (message : BrokerQueueMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, BqMoreFlag.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 BqItem.encode BqItem.decode BqItem.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.bqItem.length_lt]
  rfl

end BrokerQueueMessage

/-- Closing Price Message: 12 bytes -/
structure ClosingPriceMessage where
  securityCode : BitVec 32
  closingPrice : BitVec 32
  filler4 : Alpha 4
  deriving DecidableEq, Repr

namespace ClosingPriceMessage

def encode (message : ClosingPriceMessage) : List UInt8 :=
  encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 4 message.closingPrice
    ++ (Alpha.encode message.filler4))

def decode (bytes : List UInt8) : Option (ClosingPriceMessage × List UInt8) := do
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (closingPrice, bytes) ← decodeUIntLE 4 bytes
  let (filler4, bytes) ← Alpha.decode 4 bytes
  pure ({ securityCode, closingPrice, filler4 }, bytes)

@[simp] theorem encode_length (message : ClosingPriceMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : ClosingPriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ClosingPriceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ClosingPriceMessage

/-- Delete Odd Lot Order Message: 16 bytes -/
structure DeleteOddLotOrderMessage where
  securityCode : BitVec 32
  orderId : BitVec 64
  brokerId : BitVec 16
  side : BitVec 16
  deriving DecidableEq, Repr

namespace DeleteOddLotOrderMessage

def encode (message : DeleteOddLotOrderMessage) : List UInt8 :=
  encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 2 message.brokerId
    ++ (encodeUIntLE 2 message.side)))

def decode (bytes : List UInt8) : Option (DeleteOddLotOrderMessage × List UInt8) := do
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (brokerId, bytes) ← decodeUIntLE 2 bytes
  let (side, bytes) ← decodeUIntLE 2 bytes
  pure ({ securityCode, orderId, brokerId, side }, bytes)

@[simp] theorem encode_length (message : DeleteOddLotOrderMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : DeleteOddLotOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DeleteOddLotOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end DeleteOddLotOrderMessage

/-- Index Definition Message: 16 bytes -/
structure IndexDefinitionMessage where
  indexCode : Alpha 11
  indexSource : IndexSource
  currencyCode : Alpha 3
  filler1 : Alpha 1
  deriving DecidableEq, Repr

namespace IndexDefinitionMessage

def encode (message : IndexDefinitionMessage) : List UInt8 :=
  Alpha.encode message.indexCode
    ++ (IndexSource.encode message.indexSource
    ++ (Alpha.encode message.currencyCode
    ++ (Alpha.encode message.filler1)))

def decode (bytes : List UInt8) : Option (IndexDefinitionMessage × List UInt8) := do
  let (indexCode, bytes) ← Alpha.decode 11 bytes
  let (indexSource, bytes) ← IndexSource.decode bytes
  let (currencyCode, bytes) ← Alpha.decode 3 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  pure ({ indexCode, indexSource, currencyCode, filler1 }, bytes)

@[simp] theorem encode_length (message : IndexDefinitionMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, IndexSource.encode_length]

theorem encode_length_pos (message : IndexDefinitionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IndexDefinitionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, IndexSource.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end IndexDefinitionMessage

/-- Index Data Message: 108 bytes -/
structure IndexDataMessage where
  indexCode : Alpha 11
  indexStatus : IndexStatus
  indexTime : BitVec 64
  indexValue : BitVec 64
  netChgPrevDay : BitVec 64
  highValue : BitVec 64
  lowValue : BitVec 64
  easValue : BitVec 64
  indexTurnover : BitVec 64
  openingValue : BitVec 64
  closingValue : BitVec 64
  previousSesClose : BitVec 64
  indexVolume : BitVec 64
  netChgPrevDayPct : BitVec 32
  exception : Exception
  filler3 : Alpha 3
  deriving DecidableEq, Repr

namespace IndexDataMessage

def encode (message : IndexDataMessage) : List UInt8 :=
  Alpha.encode message.indexCode
    ++ (IndexStatus.encode message.indexStatus
    ++ (encodeUIntLE 8 message.indexTime
    ++ (encodeUIntLE 8 message.indexValue
    ++ (encodeUIntLE 8 message.netChgPrevDay
    ++ (encodeUIntLE 8 message.highValue
    ++ (encodeUIntLE 8 message.lowValue
    ++ (encodeUIntLE 8 message.easValue
    ++ (encodeUIntLE 8 message.indexTurnover
    ++ (encodeUIntLE 8 message.openingValue
    ++ (encodeUIntLE 8 message.closingValue
    ++ (encodeUIntLE 8 message.previousSesClose
    ++ (encodeUIntLE 8 message.indexVolume
    ++ (encodeUIntLE 4 message.netChgPrevDayPct
    ++ (Exception.encode message.exception
    ++ (Alpha.encode message.filler3)))))))))))))))

def decode (bytes : List UInt8) : Option (IndexDataMessage × List UInt8) := do
  let (indexCode, bytes) ← Alpha.decode 11 bytes
  let (indexStatus, bytes) ← IndexStatus.decode bytes
  let (indexTime, bytes) ← decodeUIntLE 8 bytes
  let (indexValue, bytes) ← decodeUIntLE 8 bytes
  let (netChgPrevDay, bytes) ← decodeUIntLE 8 bytes
  let (highValue, bytes) ← decodeUIntLE 8 bytes
  let (lowValue, bytes) ← decodeUIntLE 8 bytes
  let (easValue, bytes) ← decodeUIntLE 8 bytes
  let (indexTurnover, bytes) ← decodeUIntLE 8 bytes
  let (openingValue, bytes) ← decodeUIntLE 8 bytes
  let (closingValue, bytes) ← decodeUIntLE 8 bytes
  let (previousSesClose, bytes) ← decodeUIntLE 8 bytes
  let (indexVolume, bytes) ← decodeUIntLE 8 bytes
  let (netChgPrevDayPct, bytes) ← decodeUIntLE 4 bytes
  let (exception, bytes) ← Exception.decode bytes
  let (filler3, bytes) ← Alpha.decode 3 bytes
  pure ({ indexCode, indexStatus, indexTime, indexValue, netChgPrevDay, highValue, lowValue, easValue, indexTurnover, openingValue, closingValue, previousSesClose, indexVolume, netChgPrevDayPct, exception, filler3 }, bytes)

@[simp] theorem encode_length (message : IndexDataMessage) : (encode message).length = 108 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, IndexStatus.encode_length, encodeUIntLE_length, Exception.encode_length]

theorem encode_length_pos (message : IndexDataMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IndexDataMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, IndexStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Exception.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end IndexDataMessage

/-- Indicative Equilibrium Price Message: 16 bytes -/
structure IndicativeEquilibriumPriceMessage where
  securityCode : BitVec 32
  price : BitVec 32
  aggregateQuantity : BitVec 64
  deriving DecidableEq, Repr

namespace IndicativeEquilibriumPriceMessage

def encode (message : IndicativeEquilibriumPriceMessage) : List UInt8 :=
  encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 8 message.aggregateQuantity))

def decode (bytes : List UInt8) : Option (IndicativeEquilibriumPriceMessage × List UInt8) := do
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (aggregateQuantity, bytes) ← decodeUIntLE 8 bytes
  pure ({ securityCode, price, aggregateQuantity }, bytes)

@[simp] theorem encode_length (message : IndicativeEquilibriumPriceMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : IndicativeEquilibriumPriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IndicativeEquilibriumPriceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end IndicativeEquilibriumPriceMessage

/-- Headline Ascii: 320 bytes -/
structure HeadlineAsciiValue where
  headlineAscii : Alpha 320
  deriving DecidableEq, Repr

namespace HeadlineAsciiValue

def encode (message : HeadlineAsciiValue) : List UInt8 :=
  Alpha.encode message.headlineAscii

def decode (bytes : List UInt8) : Option (HeadlineAsciiValue × List UInt8) := do
  let (headlineAscii, bytes) ← Alpha.decode 320 bytes
  pure ({ headlineAscii }, bytes)

@[simp] theorem encode_length (message : HeadlineAsciiValue) : (encode message).length = 320 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : HeadlineAsciiValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : HeadlineAsciiValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end HeadlineAsciiValue

/-- Headline Utf16: 320 bytes -/
structure HeadlineUtf16Value where
  headlineUtf16 : Alpha 320
  deriving DecidableEq, Repr

namespace HeadlineUtf16Value

def encode (message : HeadlineUtf16Value) : List UInt8 :=
  Alpha.encode message.headlineUtf16

def decode (bytes : List UInt8) : Option (HeadlineUtf16Value × List UInt8) := do
  let (headlineUtf16, bytes) ← Alpha.decode 320 bytes
  pure ({ headlineUtf16 }, bytes)

@[simp] theorem encode_length (message : HeadlineUtf16Value) : (encode message).length = 320 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : HeadlineUtf16Value) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : HeadlineUtf16Value) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end HeadlineUtf16Value

/-- Any Headline, selected by News Type -/
inductive Headline where
  | headlineAscii (message : HeadlineAsciiValue) -- "EXN" 0x45584E
  | headlineUtf16 (message : HeadlineUtf16Value) -- "EXC" 0x455843
  | headlineUtf16Default (tag : { v : BitVec 24 // v ≠ 4544590 ∧ v ≠ 4544579 }) (message : HeadlineUtf16Value) -- any other value: the bytes it states
  deriving DecidableEq, Repr

namespace Headline

/-- The News Type each message is sent under -/
def tag : Headline → BitVec 24
  | .headlineAscii _ => 4544590
  | .headlineUtf16 _ => 4544579
  | .headlineUtf16Default tag _ => tag.val

def encode : Headline → List UInt8
  | .headlineAscii message => HeadlineAsciiValue.encode message
  | .headlineUtf16 message => HeadlineUtf16Value.encode message
  | .headlineUtf16Default _ message => HeadlineUtf16Value.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Headline) : (encode message).length ≤ 320 := by
  cases message with
  | headlineAscii inner =>
    simp only [encode, HeadlineAsciiValue.encode_length]
    omega
  | headlineUtf16 inner =>
    simp only [encode, HeadlineUtf16Value.encode_length]
    omega
  | headlineUtf16Default _ inner =>
    simp only [encode, HeadlineUtf16Value.encode_length]
    omega

def decode (tag : BitVec 24) (bytes : List UInt8) : Option (Headline × List UInt8) :=
  if h0 : tag = 4544590 then (HeadlineAsciiValue.decode bytes).map fun (message, rest) => (.headlineAscii message, rest)
  else if h1 : tag = 4544579 then (HeadlineUtf16Value.decode bytes).map fun (message, rest) => (.headlineUtf16 message, rest)
  else (HeadlineUtf16Value.decode bytes).map fun (message, rest) => (.headlineUtf16Default ⟨tag, h0, h1⟩ message, rest)

@[simp] theorem decode_encode (message : Headline) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message with
  | headlineAscii m => simp [decode, encode, tag]
  | headlineUtf16 m => simp [decode, encode, tag]
  | headlineUtf16Default t m =>
    obtain ⟨v, h0, h1⟩ := t
    simp only [tag, encode, decode, h0, h1, reduceDIte, HeadlineUtf16Value.decode_encode, Option.map_some]

end Headline

/-- News Market: 4 bytes -/
structure NewsMarket where
  marketCode : Alpha 4
  deriving DecidableEq, Repr

namespace NewsMarket

def encode (message : NewsMarket) : List UInt8 :=
  Alpha.encode message.marketCode

def decode (bytes : List UInt8) : Option (NewsMarket × List UInt8) := do
  let (marketCode, bytes) ← Alpha.decode 4 bytes
  pure ({ marketCode }, bytes)

@[simp] theorem encode_length (message : NewsMarket) : (encode message).length = 4 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : NewsMarket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewsMarket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end NewsMarket

/-- News Security: 4 bytes -/
structure NewsSecurity where
  securityCode : BitVec 32
  deriving DecidableEq, Repr

namespace NewsSecurity

def encode (message : NewsSecurity) : List UInt8 :=
  encodeUIntLE 4 message.securityCode

def decode (bytes : List UInt8) : Option (NewsSecurity × List UInt8) := do
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  pure ({ securityCode }, bytes)

@[simp] theorem encode_length (message : NewsSecurity) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : NewsSecurity) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewsSecurity) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end NewsSecurity

/-- News Line Ascii: 160 bytes -/
structure NewsLineAsciiValue where
  newsLineAscii : Alpha 160
  deriving DecidableEq, Repr

namespace NewsLineAsciiValue

def encode (message : NewsLineAsciiValue) : List UInt8 :=
  Alpha.encode message.newsLineAscii

def decode (bytes : List UInt8) : Option (NewsLineAsciiValue × List UInt8) := do
  let (newsLineAscii, bytes) ← Alpha.decode 160 bytes
  pure ({ newsLineAscii }, bytes)

@[simp] theorem encode_length (message : NewsLineAsciiValue) : (encode message).length = 160 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : NewsLineAsciiValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewsLineAsciiValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end NewsLineAsciiValue

/-- News Line Utf16: 160 bytes -/
structure NewsLineUtf16Value where
  newsLineUtf16 : Alpha 160
  deriving DecidableEq, Repr

namespace NewsLineUtf16Value

def encode (message : NewsLineUtf16Value) : List UInt8 :=
  Alpha.encode message.newsLineUtf16

def decode (bytes : List UInt8) : Option (NewsLineUtf16Value × List UInt8) := do
  let (newsLineUtf16, bytes) ← Alpha.decode 160 bytes
  pure ({ newsLineUtf16 }, bytes)

@[simp] theorem encode_length (message : NewsLineUtf16Value) : (encode message).length = 160 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : NewsLineUtf16Value) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewsLineUtf16Value) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end NewsLineUtf16Value

/-- Any News Line, selected by News Type -/
inductive NewsLine where
  | newsLineAscii (message : NewsLineAsciiValue) -- "EXN" 0x45584E
  | newsLineUtf16 (message : NewsLineUtf16Value) -- "EXC" 0x455843
  | newsLineUtf16Default (tag : { v : BitVec 24 // v ≠ 4544590 ∧ v ≠ 4544579 }) (message : NewsLineUtf16Value) -- any other value: the bytes it states
  deriving DecidableEq, Repr

namespace NewsLine

/-- The News Type each message is sent under -/
def tag : NewsLine → BitVec 24
  | .newsLineAscii _ => 4544590
  | .newsLineUtf16 _ => 4544579
  | .newsLineUtf16Default tag _ => tag.val

def encode : NewsLine → List UInt8
  | .newsLineAscii message => NewsLineAsciiValue.encode message
  | .newsLineUtf16 message => NewsLineUtf16Value.encode message
  | .newsLineUtf16Default _ message => NewsLineUtf16Value.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : NewsLine) : (encode message).length ≤ 160 := by
  cases message with
  | newsLineAscii inner =>
    simp only [encode, NewsLineAsciiValue.encode_length]
    omega
  | newsLineUtf16 inner =>
    simp only [encode, NewsLineUtf16Value.encode_length]
    omega
  | newsLineUtf16Default _ inner =>
    simp only [encode, NewsLineUtf16Value.encode_length]
    omega

def decode (tag : BitVec 24) (bytes : List UInt8) : Option (NewsLine × List UInt8) :=
  if h0 : tag = 4544590 then (NewsLineAsciiValue.decode bytes).map fun (message, rest) => (.newsLineAscii message, rest)
  else if h1 : tag = 4544579 then (NewsLineUtf16Value.decode bytes).map fun (message, rest) => (.newsLineUtf16 message, rest)
  else (NewsLineUtf16Value.decode bytes).map fun (message, rest) => (.newsLineUtf16Default ⟨tag, h0, h1⟩ message, rest)

@[simp] theorem decode_encode (message : NewsLine) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message with
  | newsLineAscii m => simp [decode, encode, tag]
  | newsLineUtf16 m => simp [decode, encode, tag]
  | newsLineUtf16Default t m =>
    obtain ⟨v, h0, h1⟩ := t
    simp only [tag, encode, decode, h0, h1, reduceDIte, NewsLineUtf16Value.decode_encode, Option.map_some]

end NewsLine

/-- News Line Item: 160 bytes -/
structure NewsLineItem where
  newsLine : Alpha 160
  deriving DecidableEq, Repr

namespace NewsLineItem

def encode (message : NewsLineItem) : List UInt8 :=
  Alpha.encode message.newsLine

def decode (bytes : List UInt8) : Option (NewsLineItem × List UInt8) := do
  let (newsLine, bytes) ← Alpha.decode 160 bytes
  pure ({ newsLine }, bytes)

@[simp] theorem encode_length (message : NewsLineItem) : (encode message).length = 160 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : NewsLineItem) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewsLineItem) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end NewsLineItem

/-- News Message -/
structure NewsMessage where
  newsId : Alpha 3
  headline : Headline
  cancelFlag : CancelFlag
  lastFragment : LastFragment
  filler4 : Alpha 4
  releaseTime : BitVec 64
  filler2 : Alpha 2
  newsMarket : Bounded 2 NewsMarket
  secondFiller2 : Alpha 2
  newsSecurity : Bounded 2 NewsSecurity
  thirdFiller2 : Alpha 2
  newsLineItem : Bounded 2 NewsLineItem
  deriving DecidableEq, Repr

namespace NewsMessage

def encode (message : NewsMessage) : List UInt8 :=
  encodeUInt 3 (Headline.tag message.headline)
    ++ (Alpha.encode message.newsId
    ++ (Headline.encode message.headline
    ++ (CancelFlag.encode message.cancelFlag
    ++ (LastFragment.encode message.lastFragment
    ++ (Alpha.encode message.filler4
    ++ (encodeUIntLE 8 message.releaseTime
    ++ (Alpha.encode message.filler2
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.newsMarket.val.length)
    ++ (encodeMany NewsMarket.encode message.newsMarket.val
    ++ (Alpha.encode message.secondFiller2
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.newsSecurity.val.length)
    ++ (encodeMany NewsSecurity.encode message.newsSecurity.val
    ++ (Alpha.encode message.thirdFiller2
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.newsLineItem.val.length)
    ++ (encodeMany NewsLineItem.encode message.newsLineItem.val)))))))))))))))

def decode (bytes : List UInt8) : Option (NewsMessage × List UInt8) := do
  let (newsType, bytes) ← decodeUInt 3 bytes
  let (newsId, bytes) ← Alpha.decode 3 bytes
  let (headline, bytes) ← Headline.decode newsType bytes
  let (cancelFlag, bytes) ← CancelFlag.decode bytes
  let (lastFragment, bytes) ← LastFragment.decode bytes
  let (filler4, bytes) ← Alpha.decode 4 bytes
  let (releaseTime, bytes) ← decodeUIntLE 8 bytes
  let (filler2, bytes) ← Alpha.decode 2 bytes
  let (noMarketCodes, bytes) ← decodeUIntLE 2 bytes
  let (newsMarket_, bytes) ← decodeMany NewsMarket.decode noMarketCodes.toNat bytes
  let (secondFiller2, bytes) ← Alpha.decode 2 bytes
  let (noSecurityCodes, bytes) ← decodeUIntLE 2 bytes
  let (newsSecurity_, bytes) ← decodeMany NewsSecurity.decode noSecurityCodes.toNat bytes
  let (thirdFiller2, bytes) ← Alpha.decode 2 bytes
  let (noNewsLines, bytes) ← decodeUIntLE 2 bytes
  let (newsLineItem_, bytes) ← decodeMany NewsLineItem.decode noNewsLines.toNat bytes
  if fits_newsMarket : newsMarket_.length < 256 ^ 2 then
    if fits_newsSecurity : newsSecurity_.length < 256 ^ 2 then
      if fits_newsLineItem : newsLineItem_.length < 256 ^ 2 then
        pure ({ newsId, headline, cancelFlag, lastFragment, filler4, releaseTime, filler2, newsMarket := ⟨newsMarket_, fits_newsMarket⟩, secondFiller2, newsSecurity := ⟨newsSecurity_, fits_newsSecurity⟩, thirdFiller2, newsLineItem := ⟨newsLineItem_, fits_newsLineItem⟩ }, bytes)
      else none
    else none
  else none

theorem encode_length_pos (message : NewsMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : NewsMessage) : (encode message).length ≤ 11010232 := by
  have bound_newsMarket := message.newsMarket.length_lt
  have bound_newsSecurity := message.newsSecurity.length_lt
  have bound_newsLineItem := message.newsLineItem.length_lt
  unfold encode
  cases message.headline with
  | headlineAscii inner =>
    simp only [Headline.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, CancelFlag.encode_length, LastFragment.encode_length, encodeUIntLE_length, encodeMany_length_const NewsMarket.encode 4 NewsMarket.encode_length, encodeMany_length_const NewsSecurity.encode 4 NewsSecurity.encode_length, encodeMany_length_const NewsLineItem.encode 160 NewsLineItem.encode_length, HeadlineAsciiValue.encode_length]
    omega
  | headlineUtf16 inner =>
    simp only [Headline.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, CancelFlag.encode_length, LastFragment.encode_length, encodeUIntLE_length, encodeMany_length_const NewsMarket.encode 4 NewsMarket.encode_length, encodeMany_length_const NewsSecurity.encode 4 NewsSecurity.encode_length, encodeMany_length_const NewsLineItem.encode 160 NewsLineItem.encode_length, HeadlineUtf16Value.encode_length]
    omega
  | headlineUtf16Default _ inner =>
    simp only [Headline.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, CancelFlag.encode_length, LastFragment.encode_length, encodeUIntLE_length, encodeMany_length_const NewsMarket.encode 4 NewsMarket.encode_length, encodeMany_length_const NewsSecurity.encode 4 NewsSecurity.encode_length, encodeMany_length_const NewsLineItem.encode 160 NewsLineItem.encode_length, HeadlineUtf16Value.encode_length]
    omega

@[simp] theorem decode_encode (message : NewsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Headline.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CancelFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LastFragment.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeMany_bounded 2 NewsMarket.encode NewsMarket.decode NewsMarket.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeMany_bounded 2 NewsSecurity.encode NewsSecurity.decode NewsSecurity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 NewsLineItem.encode NewsLineItem.decode NewsLineItem.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.newsMarket.length_lt, dite_eq_left message.newsSecurity.length_lt, dite_eq_left message.newsLineItem.length_lt]
  rfl

end NewsMessage

/-- Nominal Price Message: 8 bytes -/
structure NominalPriceMessage where
  securityCode : BitVec 32
  nominalPrice : BitVec 32
  deriving DecidableEq, Repr

namespace NominalPriceMessage

def encode (message : NominalPriceMessage) : List UInt8 :=
  encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 4 message.nominalPrice)

def decode (bytes : List UInt8) : Option (NominalPriceMessage × List UInt8) := do
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (nominalPrice, bytes) ← decodeUIntLE 4 bytes
  pure ({ securityCode, nominalPrice }, bytes)

@[simp] theorem encode_length (message : NominalPriceMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : NominalPriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NominalPriceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end NominalPriceMessage

/-- Order Imbalance Message: 16 bytes -/
structure OrderImbalanceMessage where
  securityCode : BitVec 32
  orderImbalanceDirection : OrderImbalanceDirection
  filler1 : Alpha 1
  orderImbalanceQuantity : BitVec 64
  filler2 : Alpha 2
  deriving DecidableEq, Repr

namespace OrderImbalanceMessage

def encode (message : OrderImbalanceMessage) : List UInt8 :=
  encodeUIntLE 4 message.securityCode
    ++ (OrderImbalanceDirection.encode message.orderImbalanceDirection
    ++ (Alpha.encode message.filler1
    ++ (encodeUIntLE 8 message.orderImbalanceQuantity
    ++ (Alpha.encode message.filler2))))

def decode (bytes : List UInt8) : Option (OrderImbalanceMessage × List UInt8) := do
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (orderImbalanceDirection, bytes) ← OrderImbalanceDirection.decode bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (orderImbalanceQuantity, bytes) ← decodeUIntLE 8 bytes
  let (filler2, bytes) ← Alpha.decode 2 bytes
  pure ({ securityCode, orderImbalanceDirection, filler1, orderImbalanceQuantity, filler2 }, bytes)

@[simp] theorem encode_length (message : OrderImbalanceMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, OrderImbalanceDirection.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderImbalanceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderImbalanceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrderImbalanceDirection.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderImbalanceMessage

/-- Market Definition Message: 36 bytes -/
structure MarketDefinitionMessage where
  marketCode : Alpha 4
  marketName : Alpha 25
  currencyCode : Alpha 3
  numberOfSecurities : BitVec 32
  deriving DecidableEq, Repr

namespace MarketDefinitionMessage

def encode (message : MarketDefinitionMessage) : List UInt8 :=
  Alpha.encode message.marketCode
    ++ (Alpha.encode message.marketName
    ++ (Alpha.encode message.currencyCode
    ++ (encodeUIntLE 4 message.numberOfSecurities)))

def decode (bytes : List UInt8) : Option (MarketDefinitionMessage × List UInt8) := do
  let (marketCode, bytes) ← Alpha.decode 4 bytes
  let (marketName, bytes) ← Alpha.decode 25 bytes
  let (currencyCode, bytes) ← Alpha.decode 3 bytes
  let (numberOfSecurities, bytes) ← decodeUIntLE 4 bytes
  pure ({ marketCode, marketName, currencyCode, numberOfSecurities }, bytes)

@[simp] theorem encode_length (message : MarketDefinitionMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : MarketDefinitionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketDefinitionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end MarketDefinitionMessage

/-- Face Value Composite: 9 bytes -/
structure FaceValueComposite where
  faceValue : BitVec 64
  decimalsInFaceValue : BitVec 8
  deriving DecidableEq, Repr

namespace FaceValueComposite

def encode (message : FaceValueComposite) : List UInt8 :=
  encodeUIntLE 8 message.faceValue
    ++ (encodeUInt 1 message.decimalsInFaceValue)

def decode (bytes : List UInt8) : Option (FaceValueComposite × List UInt8) := do
  let (faceValue, bytes) ← decodeUIntLE 8 bytes
  let (decimalsInFaceValue, bytes) ← decodeUInt 1 bytes
  pure ({ faceValue, decimalsInFaceValue }, bytes)

@[simp] theorem encode_length (message : FaceValueComposite) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : FaceValueComposite) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FaceValueComposite) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end FaceValueComposite

/-- Call Price Composite: 5 bytes -/
structure CallPriceComposite where
  callPrice : BitVec 32
  decimalsInCallPrice : BitVec 8
  deriving DecidableEq, Repr

namespace CallPriceComposite

def encode (message : CallPriceComposite) : List UInt8 :=
  encodeUIntLE 4 message.callPrice
    ++ (encodeUInt 1 message.decimalsInCallPrice)

def decode (bytes : List UInt8) : Option (CallPriceComposite × List UInt8) := do
  let (callPrice, bytes) ← decodeUIntLE 4 bytes
  let (decimalsInCallPrice, bytes) ← decodeUInt 1 bytes
  pure ({ callPrice, decimalsInCallPrice }, bytes)

@[simp] theorem encode_length (message : CallPriceComposite) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : CallPriceComposite) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CallPriceComposite) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CallPriceComposite

/-- Entitlement Composite: 5 bytes -/
structure EntitlementComposite where
  entitlement : BitVec 32
  decimalsInEntitlement : BitVec 8
  deriving DecidableEq, Repr

namespace EntitlementComposite

def encode (message : EntitlementComposite) : List UInt8 :=
  encodeUIntLE 4 message.entitlement
    ++ (encodeUInt 1 message.decimalsInEntitlement)

def decode (bytes : List UInt8) : Option (EntitlementComposite × List UInt8) := do
  let (entitlement, bytes) ← decodeUIntLE 4 bytes
  let (decimalsInEntitlement, bytes) ← decodeUInt 1 bytes
  pure ({ entitlement, decimalsInEntitlement }, bytes)

@[simp] theorem encode_length (message : EntitlementComposite) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : EntitlementComposite) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EntitlementComposite) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end EntitlementComposite

/-- Underlying Security: 8 bytes -/
structure UnderlyingSecurity where
  underlyingSecurityCode : BitVec 32
  filler4 : Alpha 4
  deriving DecidableEq, Repr

namespace UnderlyingSecurity

def encode (message : UnderlyingSecurity) : List UInt8 :=
  encodeUIntLE 4 message.underlyingSecurityCode
    ++ (Alpha.encode message.filler4)

def decode (bytes : List UInt8) : Option (UnderlyingSecurity × List UInt8) := do
  let (underlyingSecurityCode, bytes) ← decodeUIntLE 4 bytes
  let (filler4, bytes) ← Alpha.decode 4 bytes
  pure ({ underlyingSecurityCode, filler4 }, bytes)

@[simp] theorem encode_length (message : UnderlyingSecurity) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : UnderlyingSecurity) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UnderlyingSecurity) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end UnderlyingSecurity

/-- Security Definition Message -/
structure SecurityDefinitionMessage where
  securityCode : BitVec 32
  marketCode : Alpha 4
  isinCode : Alpha 12
  instrumentType : Alpha 4
  productType : BitVec 8
  filler1 : Alpha 1
  spreadTableCode : Alpha 2
  securityShortName : Alpha 40
  currencyCode : Alpha 3
  securityNameGccs : Alpha 60
  securityNameGb : Alpha 60
  lotSize : BitVec 32
  filler4 : Alpha 4
  previousClosingPrice : BitVec 32
  vcmFlag : VcmFlag
  shortSellFlag : ShortSellFlag
  casFlag : CasFlag
  ccassFlag : CcassFlag
  dummySecurityFlag : DummySecurityFlag
  secondFiller1 : Alpha 1
  stampDutyFlag : StampDutyFlag
  thirdFiller1 : Alpha 1
  listingDate : BitVec 32
  delistingDate : BitVec 32
  freeText : Alpha 38
  filler62 : Alpha 62
  posFlag : PosFlag
  posUpperLimit : BitVec 32
  posLowerLimit : BitVec 32
  domainStmtSecurityCode : BitVec 32
  filler37 : Alpha 37
  efnFlag : EfnFlag
  accruedInterest : BitVec 32
  couponRate : BitVec 32
  fourthFiller1 : Alpha 1
  faceValueComposite : FaceValueComposite
  faceValueCurrency : Alpha 3
  bondMaturityDate : BitVec 32
  investorType : InvestorType
  filler44 : Alpha 44
  conversionRatio : BitVec 32
  strikePrice1 : BitVec 32
  strikePrice2 : BitVec 32
  warrantMaturityDate : BitVec 32
  callPutFlag : CallPutFlag
  style : Style
  filler2 : Alpha 2
  warrantType : WarrantType
  callPriceComposite : CallPriceComposite
  entitlementComposite : EntitlementComposite
  noWarrantsPerEntitlement : BitVec 32
  filler63 : Alpha 63
  underlyingSecurity : Bounded 2 UnderlyingSecurity
  deriving DecidableEq, Repr

namespace SecurityDefinitionMessage

def encode (message : SecurityDefinitionMessage) : List UInt8 :=
  encodeUIntLE 4 message.securityCode
    ++ (Alpha.encode message.marketCode
    ++ (Alpha.encode message.isinCode
    ++ (Alpha.encode message.instrumentType
    ++ (encodeUInt 1 message.productType
    ++ (Alpha.encode message.filler1
    ++ (Alpha.encode message.spreadTableCode
    ++ (Alpha.encode message.securityShortName
    ++ (Alpha.encode message.currencyCode
    ++ (Alpha.encode message.securityNameGccs
    ++ (Alpha.encode message.securityNameGb
    ++ (encodeUIntLE 4 message.lotSize
    ++ (Alpha.encode message.filler4
    ++ (encodeUIntLE 4 message.previousClosingPrice
    ++ (VcmFlag.encode message.vcmFlag
    ++ (ShortSellFlag.encode message.shortSellFlag
    ++ (CasFlag.encode message.casFlag
    ++ (CcassFlag.encode message.ccassFlag
    ++ (DummySecurityFlag.encode message.dummySecurityFlag
    ++ (Alpha.encode message.secondFiller1
    ++ (StampDutyFlag.encode message.stampDutyFlag
    ++ (Alpha.encode message.thirdFiller1
    ++ (encodeUIntLE 4 message.listingDate
    ++ (encodeUIntLE 4 message.delistingDate
    ++ (Alpha.encode message.freeText
    ++ (Alpha.encode message.filler62
    ++ (PosFlag.encode message.posFlag
    ++ (encodeUIntLE 4 message.posUpperLimit
    ++ (encodeUIntLE 4 message.posLowerLimit
    ++ (encodeUIntLE 4 message.domainStmtSecurityCode
    ++ (Alpha.encode message.filler37
    ++ (EfnFlag.encode message.efnFlag
    ++ (encodeUIntLE 4 message.accruedInterest
    ++ (encodeUIntLE 4 message.couponRate
    ++ (Alpha.encode message.fourthFiller1
    ++ (FaceValueComposite.encode message.faceValueComposite
    ++ (Alpha.encode message.faceValueCurrency
    ++ (encodeUIntLE 4 message.bondMaturityDate
    ++ (InvestorType.encode message.investorType
    ++ (Alpha.encode message.filler44
    ++ (encodeUIntLE 4 message.conversionRatio
    ++ (encodeUIntLE 4 message.strikePrice1
    ++ (encodeUIntLE 4 message.strikePrice2
    ++ (encodeUIntLE 4 message.warrantMaturityDate
    ++ (CallPutFlag.encode message.callPutFlag
    ++ (Style.encode message.style
    ++ (Alpha.encode message.filler2
    ++ (WarrantType.encode message.warrantType
    ++ (CallPriceComposite.encode message.callPriceComposite
    ++ (EntitlementComposite.encode message.entitlementComposite
    ++ (encodeUIntLE 4 message.noWarrantsPerEntitlement
    ++ (Alpha.encode message.filler63
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.underlyingSecurity.val.length)
    ++ (encodeMany UnderlyingSecurity.encode message.underlyingSecurity.val)))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SecurityDefinitionMessage × List UInt8) := do
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (marketCode, bytes) ← Alpha.decode 4 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (instrumentType, bytes) ← Alpha.decode 4 bytes
  let (productType, bytes) ← decodeUInt 1 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (spreadTableCode, bytes) ← Alpha.decode 2 bytes
  let (securityShortName, bytes) ← Alpha.decode 40 bytes
  let (currencyCode, bytes) ← Alpha.decode 3 bytes
  let (securityNameGccs, bytes) ← Alpha.decode 60 bytes
  let (securityNameGb, bytes) ← Alpha.decode 60 bytes
  let (lotSize, bytes) ← decodeUIntLE 4 bytes
  let (filler4, bytes) ← Alpha.decode 4 bytes
  let (previousClosingPrice, bytes) ← decodeUIntLE 4 bytes
  let (vcmFlag, bytes) ← VcmFlag.decode bytes
  let (shortSellFlag, bytes) ← ShortSellFlag.decode bytes
  let (casFlag, bytes) ← CasFlag.decode bytes
  let (ccassFlag, bytes) ← CcassFlag.decode bytes
  let (dummySecurityFlag, bytes) ← DummySecurityFlag.decode bytes
  let (secondFiller1, bytes) ← Alpha.decode 1 bytes
  let (stampDutyFlag, bytes) ← StampDutyFlag.decode bytes
  let (thirdFiller1, bytes) ← Alpha.decode 1 bytes
  let (listingDate, bytes) ← decodeUIntLE 4 bytes
  let (delistingDate, bytes) ← decodeUIntLE 4 bytes
  let (freeText, bytes) ← Alpha.decode 38 bytes
  let (filler62, bytes) ← Alpha.decode 62 bytes
  let (posFlag, bytes) ← PosFlag.decode bytes
  let (posUpperLimit, bytes) ← decodeUIntLE 4 bytes
  let (posLowerLimit, bytes) ← decodeUIntLE 4 bytes
  let (domainStmtSecurityCode, bytes) ← decodeUIntLE 4 bytes
  let (filler37, bytes) ← Alpha.decode 37 bytes
  let (efnFlag, bytes) ← EfnFlag.decode bytes
  let (accruedInterest, bytes) ← decodeUIntLE 4 bytes
  let (couponRate, bytes) ← decodeUIntLE 4 bytes
  let (fourthFiller1, bytes) ← Alpha.decode 1 bytes
  let (faceValueComposite, bytes) ← FaceValueComposite.decode bytes
  let (faceValueCurrency, bytes) ← Alpha.decode 3 bytes
  let (bondMaturityDate, bytes) ← decodeUIntLE 4 bytes
  let (investorType, bytes) ← InvestorType.decode bytes
  let (filler44, bytes) ← Alpha.decode 44 bytes
  let (conversionRatio, bytes) ← decodeUIntLE 4 bytes
  let (strikePrice1, bytes) ← decodeUIntLE 4 bytes
  let (strikePrice2, bytes) ← decodeUIntLE 4 bytes
  let (warrantMaturityDate, bytes) ← decodeUIntLE 4 bytes
  let (callPutFlag, bytes) ← CallPutFlag.decode bytes
  let (style, bytes) ← Style.decode bytes
  let (filler2, bytes) ← Alpha.decode 2 bytes
  let (warrantType, bytes) ← WarrantType.decode bytes
  let (callPriceComposite, bytes) ← CallPriceComposite.decode bytes
  let (entitlementComposite, bytes) ← EntitlementComposite.decode bytes
  let (noWarrantsPerEntitlement, bytes) ← decodeUIntLE 4 bytes
  let (filler63, bytes) ← Alpha.decode 63 bytes
  let (noUnderlyingSecurities, bytes) ← decodeUIntLE 2 bytes
  let (underlyingSecurity_, bytes) ← decodeMany UnderlyingSecurity.decode noUnderlyingSecurities.toNat bytes
  if fits_underlyingSecurity : underlyingSecurity_.length < 256 ^ 2 then
    pure ({ securityCode, marketCode, isinCode, instrumentType, productType, filler1, spreadTableCode, securityShortName, currencyCode, securityNameGccs, securityNameGb, lotSize, filler4, previousClosingPrice, vcmFlag, shortSellFlag, casFlag, ccassFlag, dummySecurityFlag, secondFiller1, stampDutyFlag, thirdFiller1, listingDate, delistingDate, freeText, filler62, posFlag, posUpperLimit, posLowerLimit, domainStmtSecurityCode, filler37, efnFlag, accruedInterest, couponRate, fourthFiller1, faceValueComposite, faceValueCurrency, bondMaturityDate, investorType, filler44, conversionRatio, strikePrice1, strikePrice2, warrantMaturityDate, callPutFlag, style, filler2, warrantType, callPriceComposite, entitlementComposite, noWarrantsPerEntitlement, filler63, underlyingSecurity := ⟨underlyingSecurity_, fits_underlyingSecurity⟩ }, bytes)
  else none

theorem encode_length_pos (message : SecurityDefinitionMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SecurityDefinitionMessage) : (encode message).length ≤ 524820 := by
  have bound_underlyingSecurity := message.underlyingSecurity.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length, VcmFlag.encode_length, ShortSellFlag.encode_length, CasFlag.encode_length, CcassFlag.encode_length, DummySecurityFlag.encode_length, StampDutyFlag.encode_length, PosFlag.encode_length, EfnFlag.encode_length, FaceValueComposite.encode_length, InvestorType.encode_length, CallPutFlag.encode_length, Style.encode_length, WarrantType.encode_length, CallPriceComposite.encode_length, EntitlementComposite.encode_length, encodeMany_length_const UnderlyingSecurity.encode 8 UnderlyingSecurity.encode_length]
  omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SecurityDefinitionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, VcmFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ShortSellFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CasFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CcassFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DummySecurityFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StampDutyFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PosFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, EfnFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FaceValueComposite.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, InvestorType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, CallPutFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Style.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, WarrantType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CallPriceComposite.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, EntitlementComposite.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 UnderlyingSecurity.encode UnderlyingSecurity.decode UnderlyingSecurity.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.underlyingSecurity.length_lt]
  rfl

end SecurityDefinitionMessage

/-- Liquidity Provider: 2 bytes -/
structure LiquidityProvider where
  lpBrokerNumber : BitVec 16
  deriving DecidableEq, Repr

namespace LiquidityProvider

def encode (message : LiquidityProvider) : List UInt8 :=
  encodeUIntLE 2 message.lpBrokerNumber

def decode (bytes : List UInt8) : Option (LiquidityProvider × List UInt8) := do
  let (lpBrokerNumber, bytes) ← decodeUIntLE 2 bytes
  pure ({ lpBrokerNumber }, bytes)

@[simp] theorem encode_length (message : LiquidityProvider) : (encode message).length = 2 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : LiquidityProvider) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LiquidityProvider) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end LiquidityProvider

/-- Liquidity Provider Message -/
structure LiquidityProviderMessage where
  securityCode : BitVec 32
  liquidityProvider : Bounded 2 LiquidityProvider
  deriving DecidableEq, Repr

namespace LiquidityProviderMessage

def encode (message : LiquidityProviderMessage) : List UInt8 :=
  encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.liquidityProvider.val.length)
    ++ (encodeMany LiquidityProvider.encode message.liquidityProvider.val))

def decode (bytes : List UInt8) : Option (LiquidityProviderMessage × List UInt8) := do
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (noLiquidityProviders, bytes) ← decodeUIntLE 2 bytes
  let (liquidityProvider_, bytes) ← decodeMany LiquidityProvider.decode noLiquidityProviders.toNat bytes
  if fits_liquidityProvider : liquidityProvider_.length < 256 ^ 2 then
    pure ({ securityCode, liquidityProvider := ⟨liquidityProvider_, fits_liquidityProvider⟩ }, bytes)
  else none

theorem encode_length_pos (message : LiquidityProviderMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : LiquidityProviderMessage) : (encode message).length ≤ 131076 := by
  have bound_liquidityProvider := message.liquidityProvider.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeMany_length_const LiquidityProvider.encode 2 LiquidityProvider.encode_length]
  omega

@[simp] theorem decode_encode (message : LiquidityProviderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 LiquidityProvider.encode LiquidityProvider.decode LiquidityProvider.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.liquidityProvider.length_lt]
  rfl

end LiquidityProviderMessage

/-- Currency Rate Message: 12 bytes -/
structure CurrencyRateMessage where
  currencyCode : Alpha 3
  filler1 : Alpha 1
  currencyFactor : BitVec 16
  filler2 : Alpha 2
  currencyRate : BitVec 32
  deriving DecidableEq, Repr

namespace CurrencyRateMessage

def encode (message : CurrencyRateMessage) : List UInt8 :=
  Alpha.encode message.currencyCode
    ++ (Alpha.encode message.filler1
    ++ (encodeUIntLE 2 message.currencyFactor
    ++ (Alpha.encode message.filler2
    ++ (encodeUIntLE 4 message.currencyRate))))

def decode (bytes : List UInt8) : Option (CurrencyRateMessage × List UInt8) := do
  let (currencyCode, bytes) ← Alpha.decode 3 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (currencyFactor, bytes) ← decodeUIntLE 2 bytes
  let (filler2, bytes) ← Alpha.decode 2 bytes
  let (currencyRate, bytes) ← decodeUIntLE 4 bytes
  pure ({ currencyCode, filler1, currencyFactor, filler2, currencyRate }, bytes)

@[simp] theorem encode_length (message : CurrencyRateMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : CurrencyRateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CurrencyRateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end CurrencyRateMessage

/-- Reference Price Message: 16 bytes -/
structure ReferencePriceMessage where
  securityCode : BitVec 32
  referencePrice : BitVec 32
  lowerPrice : BitVec 32
  upperPrice : BitVec 32
  deriving DecidableEq, Repr

namespace ReferencePriceMessage

def encode (message : ReferencePriceMessage) : List UInt8 :=
  encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 4 message.referencePrice
    ++ (encodeUIntLE 4 message.lowerPrice
    ++ (encodeUIntLE 4 message.upperPrice)))

def decode (bytes : List UInt8) : Option (ReferencePriceMessage × List UInt8) := do
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (referencePrice, bytes) ← decodeUIntLE 4 bytes
  let (lowerPrice, bytes) ← decodeUIntLE 4 bytes
  let (upperPrice, bytes) ← decodeUIntLE 4 bytes
  pure ({ securityCode, referencePrice, lowerPrice, upperPrice }, bytes)

@[simp] theorem encode_length (message : ReferencePriceMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : ReferencePriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReferencePriceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ReferencePriceMessage

/-- Refresh Request Message: 0 bytes -/
structure RefreshRequestMessage where
  deriving DecidableEq, Repr

namespace RefreshRequestMessage

def encode (_ : RefreshRequestMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (RefreshRequestMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : RefreshRequestMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : RefreshRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end RefreshRequestMessage

/-- Refresh Response Message: 4 bytes -/
structure RefreshResponseMessage where
  refreshStatus : BitVec 8
  filler3 : Alpha 3
  deriving DecidableEq, Repr

namespace RefreshResponseMessage

def encode (message : RefreshResponseMessage) : List UInt8 :=
  encodeUInt 1 message.refreshStatus
    ++ (Alpha.encode message.filler3)

def decode (bytes : List UInt8) : Option (RefreshResponseMessage × List UInt8) := do
  let (refreshStatus, bytes) ← decodeUInt 1 bytes
  let (filler3, bytes) ← Alpha.decode 3 bytes
  pure ({ refreshStatus, filler3 }, bytes)

@[simp] theorem encode_length (message : RefreshResponseMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : RefreshResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RefreshResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end RefreshResponseMessage

/-- Refresh Complete Message: 4 bytes -/
structure RefreshCompleteMessage where
  lastInternalSeqNum : BitVec 32
  deriving DecidableEq, Repr

namespace RefreshCompleteMessage

def encode (message : RefreshCompleteMessage) : List UInt8 :=
  encodeUIntLE 4 message.lastInternalSeqNum

def decode (bytes : List UInt8) : Option (RefreshCompleteMessage × List UInt8) := do
  let (lastInternalSeqNum, bytes) ← decodeUIntLE 4 bytes
  pure ({ lastInternalSeqNum }, bytes)

@[simp] theorem encode_length (message : RefreshCompleteMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : RefreshCompleteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RefreshCompleteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end RefreshCompleteMessage

/-- Send Key Message: 528 bytes -/
structure SendKeyMessage where
  prime : Alpha 128
  generator : Alpha 128
  primeOrderSubgroup : Alpha 128
  omdPublicKey : Alpha 144
  deriving DecidableEq, Repr

namespace SendKeyMessage

def encode (message : SendKeyMessage) : List UInt8 :=
  Alpha.encode message.prime
    ++ (Alpha.encode message.generator
    ++ (Alpha.encode message.primeOrderSubgroup
    ++ (Alpha.encode message.omdPublicKey)))

def decode (bytes : List UInt8) : Option (SendKeyMessage × List UInt8) := do
  let (prime, bytes) ← Alpha.decode 128 bytes
  let (generator, bytes) ← Alpha.decode 128 bytes
  let (primeOrderSubgroup, bytes) ← Alpha.decode 128 bytes
  let (omdPublicKey, bytes) ← Alpha.decode 144 bytes
  pure ({ prime, generator, primeOrderSubgroup, omdPublicKey }, bytes)

@[simp] theorem encode_length (message : SendKeyMessage) : (encode message).length = 528 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : SendKeyMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SendKeyMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SendKeyMessage

/-- Logon Message: 186 bytes -/
structure LogonMessage where
  username : Alpha 12
  internalSeqNum : BitVec 32
  clientPublicKey : Alpha 128
  encryptedPasswordLen : BitVec 8
  encryptedPassword : Alpha 20
  encryptedNewPasswordLen : BitVec 8
  encryptedNewPassword : Alpha 20
  deriving DecidableEq, Repr

namespace LogonMessage

def encode (message : LogonMessage) : List UInt8 :=
  Alpha.encode message.username
    ++ (encodeUIntLE 4 message.internalSeqNum
    ++ (Alpha.encode message.clientPublicKey
    ++ (encodeUInt 1 message.encryptedPasswordLen
    ++ (Alpha.encode message.encryptedPassword
    ++ (encodeUInt 1 message.encryptedNewPasswordLen
    ++ (Alpha.encode message.encryptedNewPassword))))))

def decode (bytes : List UInt8) : Option (LogonMessage × List UInt8) := do
  let (username, bytes) ← Alpha.decode 12 bytes
  let (internalSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (clientPublicKey, bytes) ← Alpha.decode 128 bytes
  let (encryptedPasswordLen, bytes) ← decodeUInt 1 bytes
  let (encryptedPassword, bytes) ← Alpha.decode 20 bytes
  let (encryptedNewPasswordLen, bytes) ← decodeUInt 1 bytes
  let (encryptedNewPassword, bytes) ← Alpha.decode 20 bytes
  pure ({ username, internalSeqNum, clientPublicKey, encryptedPasswordLen, encryptedPassword, encryptedNewPasswordLen, encryptedNewPassword }, bytes)

@[simp] theorem encode_length (message : LogonMessage) : (encode message).length = 186 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : LogonMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogonMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LogonMessage

/-- Logon Response Message: 4 bytes -/
structure LogonResponseMessage where
  heartBtInterval : BitVec 16
  sessionStatus : BitVec 8
  passwordExpiryDays : BitVec 8
  deriving DecidableEq, Repr

namespace LogonResponseMessage

def encode (message : LogonResponseMessage) : List UInt8 :=
  encodeUIntLE 2 message.heartBtInterval
    ++ (encodeUInt 1 message.sessionStatus
    ++ (encodeUInt 1 message.passwordExpiryDays))

def decode (bytes : List UInt8) : Option (LogonResponseMessage × List UInt8) := do
  let (heartBtInterval, bytes) ← decodeUIntLE 2 bytes
  let (sessionStatus, bytes) ← decodeUInt 1 bytes
  let (passwordExpiryDays, bytes) ← decodeUInt 1 bytes
  pure ({ heartBtInterval, sessionStatus, passwordExpiryDays }, bytes)

@[simp] theorem encode_length (message : LogonResponseMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : LogonResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogonResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end LogonResponseMessage

/-- Logout Message: 4 bytes -/
structure LogoutMessage where
  sessionStatus : BitVec 8
  filler3 : Alpha 3
  deriving DecidableEq, Repr

namespace LogoutMessage

def encode (message : LogoutMessage) : List UInt8 :=
  encodeUInt 1 message.sessionStatus
    ++ (Alpha.encode message.filler3)

def decode (bytes : List UInt8) : Option (LogoutMessage × List UInt8) := do
  let (sessionStatus, bytes) ← decodeUInt 1 bytes
  let (filler3, bytes) ← Alpha.decode 3 bytes
  pure ({ sessionStatus, filler3 }, bytes)

@[simp] theorem encode_length (message : LogoutMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : LogoutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogoutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LogoutMessage

/-- Statistics Message: 48 bytes -/
structure StatisticsMessage where
  securityCode : BitVec 32
  sharesTraded : BitVec 64
  turnover : BitVec 64
  highPrice : BitVec 32
  lowPrice : BitVec 32
  lastPrice : BitVec 32
  filler4 : Alpha 4
  shortSellSharesTraded : BitVec 32
  shortSellTurnover : BitVec 64
  deriving DecidableEq, Repr

namespace StatisticsMessage

def encode (message : StatisticsMessage) : List UInt8 :=
  encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.sharesTraded
    ++ (encodeUIntLE 8 message.turnover
    ++ (encodeUIntLE 4 message.highPrice
    ++ (encodeUIntLE 4 message.lowPrice
    ++ (encodeUIntLE 4 message.lastPrice
    ++ (Alpha.encode message.filler4
    ++ (encodeUIntLE 4 message.shortSellSharesTraded
    ++ (encodeUIntLE 8 message.shortSellTurnover))))))))

def decode (bytes : List UInt8) : Option (StatisticsMessage × List UInt8) := do
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (sharesTraded, bytes) ← decodeUIntLE 8 bytes
  let (turnover, bytes) ← decodeUIntLE 8 bytes
  let (highPrice, bytes) ← decodeUIntLE 4 bytes
  let (lowPrice, bytes) ← decodeUIntLE 4 bytes
  let (lastPrice, bytes) ← decodeUIntLE 4 bytes
  let (filler4, bytes) ← Alpha.decode 4 bytes
  let (shortSellSharesTraded, bytes) ← decodeUIntLE 4 bytes
  let (shortSellTurnover, bytes) ← decodeUIntLE 8 bytes
  pure ({ securityCode, sharesTraded, turnover, highPrice, lowPrice, lastPrice, filler4, shortSellSharesTraded, shortSellTurnover }, bytes)

@[simp] theorem encode_length (message : StatisticsMessage) : (encode message).length = 48 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : StatisticsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StatisticsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end StatisticsMessage

/-- Market Turnover Message: 16 bytes -/
structure MarketTurnoverMessage where
  marketCode : Alpha 4
  currencyCode : Alpha 3
  filler1 : Alpha 1
  turnover : BitVec 64
  deriving DecidableEq, Repr

namespace MarketTurnoverMessage

def encode (message : MarketTurnoverMessage) : List UInt8 :=
  Alpha.encode message.marketCode
    ++ (Alpha.encode message.currencyCode
    ++ (Alpha.encode message.filler1
    ++ (encodeUIntLE 8 message.turnover)))

def decode (bytes : List UInt8) : Option (MarketTurnoverMessage × List UInt8) := do
  let (marketCode, bytes) ← Alpha.decode 4 bytes
  let (currencyCode, bytes) ← Alpha.decode 3 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (turnover, bytes) ← decodeUIntLE 8 bytes
  pure ({ marketCode, currencyCode, filler1, turnover }, bytes)

@[simp] theorem encode_length (message : MarketTurnoverMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : MarketTurnoverMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketTurnoverMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end MarketTurnoverMessage

/-- Yield Message: 8 bytes -/
structure YieldMessage where
  securityCode : BitVec 32
  yield : BitVec 32
  deriving DecidableEq, Repr

namespace YieldMessage

def encode (message : YieldMessage) : List UInt8 :=
  encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 4 message.yield)

def decode (bytes : List UInt8) : Option (YieldMessage × List UInt8) := do
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (yield, bytes) ← decodeUIntLE 4 bytes
  pure ({ securityCode, yield }, bytes)

@[simp] theorem encode_length (message : YieldMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : YieldMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : YieldMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end YieldMessage

/-- Trading Session Status Message: 28 bytes -/
structure TradingSessionStatusMessage where
  marketCode : Alpha 4
  filler1 : Alpha 1
  tradingSessionSubId : BitVec 8
  tradingSesStatus : BitVec 8
  tradingSesControlFlag : TradingSesControlFlag
  filler4 : Alpha 4
  startDateTime : BitVec 64
  endDateTime : BitVec 64
  deriving DecidableEq, Repr

namespace TradingSessionStatusMessage

def encode (message : TradingSessionStatusMessage) : List UInt8 :=
  Alpha.encode message.marketCode
    ++ (Alpha.encode message.filler1
    ++ (encodeUInt 1 message.tradingSessionSubId
    ++ (encodeUInt 1 message.tradingSesStatus
    ++ (TradingSesControlFlag.encode message.tradingSesControlFlag
    ++ (Alpha.encode message.filler4
    ++ (encodeUIntLE 8 message.startDateTime
    ++ (encodeUIntLE 8 message.endDateTime)))))))

def decode (bytes : List UInt8) : Option (TradingSessionStatusMessage × List UInt8) := do
  let (marketCode, bytes) ← Alpha.decode 4 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (tradingSessionSubId, bytes) ← decodeUInt 1 bytes
  let (tradingSesStatus, bytes) ← decodeUInt 1 bytes
  let (tradingSesControlFlag, bytes) ← TradingSesControlFlag.decode bytes
  let (filler4, bytes) ← Alpha.decode 4 bytes
  let (startDateTime, bytes) ← decodeUIntLE 8 bytes
  let (endDateTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ marketCode, filler1, tradingSessionSubId, tradingSesStatus, tradingSesControlFlag, filler4, startDateTime, endDateTime }, bytes)

@[simp] theorem encode_length (message : TradingSessionStatusMessage) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, TradingSesControlFlag.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : TradingSessionStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradingSessionStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TradingSesControlFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradingSessionStatusMessage

/-- Security Status Message: 8 bytes -/
structure SecurityStatusMessage where
  securityCode : BitVec 32
  suspensionIndicator : BitVec 8
  filler3 : Alpha 3
  deriving DecidableEq, Repr

namespace SecurityStatusMessage

def encode (message : SecurityStatusMessage) : List UInt8 :=
  encodeUIntLE 4 message.securityCode
    ++ (encodeUInt 1 message.suspensionIndicator
    ++ (Alpha.encode message.filler3))

def decode (bytes : List UInt8) : Option (SecurityStatusMessage × List UInt8) := do
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (suspensionIndicator, bytes) ← decodeUInt 1 bytes
  let (filler3, bytes) ← Alpha.decode 3 bytes
  pure ({ securityCode, suspensionIndicator, filler3 }, bytes)

@[simp] theorem encode_length (message : SecurityStatusMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : SecurityStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SecurityStatusMessage

/-- Stock Connect Daily Quota Balance Message: 20 bytes -/
structure StockConnectDailyQuotaBalanceMessage where
  stockConnectMarket : Alpha 2
  tradingDirection : Alpha 2
  dailyQuotaBalance : BitVec 64
  dailyQuotaBalanceTime : BitVec 64
  deriving DecidableEq, Repr

namespace StockConnectDailyQuotaBalanceMessage

def encode (message : StockConnectDailyQuotaBalanceMessage) : List UInt8 :=
  Alpha.encode message.stockConnectMarket
    ++ (Alpha.encode message.tradingDirection
    ++ (encodeUIntLE 8 message.dailyQuotaBalance
    ++ (encodeUIntLE 8 message.dailyQuotaBalanceTime)))

def decode (bytes : List UInt8) : Option (StockConnectDailyQuotaBalanceMessage × List UInt8) := do
  let (stockConnectMarket, bytes) ← Alpha.decode 2 bytes
  let (tradingDirection, bytes) ← Alpha.decode 2 bytes
  let (dailyQuotaBalance, bytes) ← decodeUIntLE 8 bytes
  let (dailyQuotaBalanceTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ stockConnectMarket, tradingDirection, dailyQuotaBalance, dailyQuotaBalanceTime }, bytes)

@[simp] theorem encode_length (message : StockConnectDailyQuotaBalanceMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : StockConnectDailyQuotaBalanceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StockConnectDailyQuotaBalanceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end StockConnectDailyQuotaBalanceMessage

/-- Stock Connect Market Turnover Message: 28 bytes -/
structure StockConnectMarketTurnoverMessage where
  stockConnectMarket : Alpha 2
  tradingDirection : Alpha 2
  buyTurnover : BitVec 64
  sellTurnover : BitVec 64
  buySellTurnover : BitVec 64
  deriving DecidableEq, Repr

namespace StockConnectMarketTurnoverMessage

def encode (message : StockConnectMarketTurnoverMessage) : List UInt8 :=
  Alpha.encode message.stockConnectMarket
    ++ (Alpha.encode message.tradingDirection
    ++ (encodeUIntLE 8 message.buyTurnover
    ++ (encodeUIntLE 8 message.sellTurnover
    ++ (encodeUIntLE 8 message.buySellTurnover))))

def decode (bytes : List UInt8) : Option (StockConnectMarketTurnoverMessage × List UInt8) := do
  let (stockConnectMarket, bytes) ← Alpha.decode 2 bytes
  let (tradingDirection, bytes) ← Alpha.decode 2 bytes
  let (buyTurnover, bytes) ← decodeUIntLE 8 bytes
  let (sellTurnover, bytes) ← decodeUIntLE 8 bytes
  let (buySellTurnover, bytes) ← decodeUIntLE 8 bytes
  pure ({ stockConnectMarket, tradingDirection, buyTurnover, sellTurnover, buySellTurnover }, bytes)

@[simp] theorem encode_length (message : StockConnectMarketTurnoverMessage) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : StockConnectMarketTurnoverMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StockConnectMarketTurnoverMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end StockConnectMarketTurnoverMessage

/-- Trade Ticker Message: 32 bytes -/
structure TradeTickerMessage where
  securityCode : BitVec 32
  tickerId : BitVec 32
  price : BitVec 32
  aggregateQuantity : BitVec 64
  tradeTime : BitVec 64
  trdType : BitVec 16
  trdCancelFlag : TrdCancelFlag
  filler1 : Alpha 1
  deriving DecidableEq, Repr

namespace TradeTickerMessage

def encode (message : TradeTickerMessage) : List UInt8 :=
  encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 4 message.tickerId
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 8 message.aggregateQuantity
    ++ (encodeUIntLE 8 message.tradeTime
    ++ (encodeUIntLE 2 message.trdType
    ++ (TrdCancelFlag.encode message.trdCancelFlag
    ++ (Alpha.encode message.filler1)))))))

def decode (bytes : List UInt8) : Option (TradeTickerMessage × List UInt8) := do
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (tickerId, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (aggregateQuantity, bytes) ← decodeUIntLE 8 bytes
  let (tradeTime, bytes) ← decodeUIntLE 8 bytes
  let (trdType, bytes) ← decodeUIntLE 2 bytes
  let (trdCancelFlag, bytes) ← TrdCancelFlag.decode bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  pure ({ securityCode, tickerId, price, aggregateQuantity, tradeTime, trdType, trdCancelFlag, filler1 }, bytes)

@[simp] theorem encode_length (message : TradeTickerMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, TrdCancelFlag.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : TradeTickerMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeTickerMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TrdCancelFlag.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeTickerMessage

/-- Vcm Trigger Message: 32 bytes -/
structure VcmTriggerMessage where
  securityCode : BitVec 32
  coolingOffStartTime : BitVec 64
  coolingOffEndTime : BitVec 64
  vcmReferencePrice : BitVec 32
  vcmLowerPrice : BitVec 32
  vcmUpperPrice : BitVec 32
  deriving DecidableEq, Repr

namespace VcmTriggerMessage

def encode (message : VcmTriggerMessage) : List UInt8 :=
  encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.coolingOffStartTime
    ++ (encodeUIntLE 8 message.coolingOffEndTime
    ++ (encodeUIntLE 4 message.vcmReferencePrice
    ++ (encodeUIntLE 4 message.vcmLowerPrice
    ++ (encodeUIntLE 4 message.vcmUpperPrice)))))

def decode (bytes : List UInt8) : Option (VcmTriggerMessage × List UInt8) := do
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (coolingOffStartTime, bytes) ← decodeUIntLE 8 bytes
  let (coolingOffEndTime, bytes) ← decodeUIntLE 8 bytes
  let (vcmReferencePrice, bytes) ← decodeUIntLE 4 bytes
  let (vcmLowerPrice, bytes) ← decodeUIntLE 4 bytes
  let (vcmUpperPrice, bytes) ← decodeUIntLE 4 bytes
  pure ({ securityCode, coolingOffStartTime, coolingOffEndTime, vcmReferencePrice, vcmLowerPrice, vcmUpperPrice }, bytes)

@[simp] theorem encode_length (message : VcmTriggerMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : VcmTriggerMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : VcmTriggerMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end VcmTriggerMessage

/-- Any Payload, selected by Msg Type -/
inductive Payload where
  | addOddLotOrderMessage (message : AddOddLotOrderMessage) -- 33
  | aggregateOrderBookUpdateMessage (message : AggregateOrderBookUpdateMessage) -- 53
  | brokerQueueMessage (message : BrokerQueueMessage) -- 54
  | closingPriceMessage (message : ClosingPriceMessage) -- 62
  | deleteOddLotOrderMessage (message : DeleteOddLotOrderMessage) -- 34
  | indexDefinitionMessage (message : IndexDefinitionMessage) -- 70
  | indexDataMessage (message : IndexDataMessage) -- 71
  | indicativeEquilibriumPriceMessage (message : IndicativeEquilibriumPriceMessage) -- 41
  | newsMessage (message : NewsMessage) -- 22
  | nominalPriceMessage (message : NominalPriceMessage) -- 40
  | orderImbalanceMessage (message : OrderImbalanceMessage) -- 56
  | marketDefinitionMessage (message : MarketDefinitionMessage) -- 10
  | securityDefinitionMessage (message : SecurityDefinitionMessage) -- 11
  | liquidityProviderMessage (message : LiquidityProviderMessage) -- 13
  | currencyRateMessage (message : CurrencyRateMessage) -- 14
  | referencePriceMessage (message : ReferencePriceMessage) -- 43
  | refreshRequestMessage (message : RefreshRequestMessage) -- 1201
  | refreshResponseMessage (message : RefreshResponseMessage) -- 1202
  | refreshCompleteMessage (message : RefreshCompleteMessage) -- 203
  | sendKeyMessage (message : SendKeyMessage) -- 1105
  | logonMessage (message : LogonMessage) -- 1101
  | logonResponseMessage (message : LogonResponseMessage) -- 1102
  | logoutMessage (message : LogoutMessage) -- 1103
  | statisticsMessage (message : StatisticsMessage) -- 60
  | marketTurnoverMessage (message : MarketTurnoverMessage) -- 61
  | yieldMessage (message : YieldMessage) -- 44
  | tradingSessionStatusMessage (message : TradingSessionStatusMessage) -- 20
  | securityStatusMessage (message : SecurityStatusMessage) -- 21
  | stockConnectDailyQuotaBalanceMessage (message : StockConnectDailyQuotaBalanceMessage) -- 80
  | stockConnectMarketTurnoverMessage (message : StockConnectMarketTurnoverMessage) -- 81
  | tradeTickerMessage (message : TradeTickerMessage) -- 52
  | vcmTriggerMessage (message : VcmTriggerMessage) -- 23
  deriving DecidableEq, Repr

namespace Payload

/-- The Msg Type each message is sent under -/
def tag : Payload → BitVec 16
  | .addOddLotOrderMessage _ => 33
  | .aggregateOrderBookUpdateMessage _ => 53
  | .brokerQueueMessage _ => 54
  | .closingPriceMessage _ => 62
  | .deleteOddLotOrderMessage _ => 34
  | .indexDefinitionMessage _ => 70
  | .indexDataMessage _ => 71
  | .indicativeEquilibriumPriceMessage _ => 41
  | .newsMessage _ => 22
  | .nominalPriceMessage _ => 40
  | .orderImbalanceMessage _ => 56
  | .marketDefinitionMessage _ => 10
  | .securityDefinitionMessage _ => 11
  | .liquidityProviderMessage _ => 13
  | .currencyRateMessage _ => 14
  | .referencePriceMessage _ => 43
  | .refreshRequestMessage _ => 1201
  | .refreshResponseMessage _ => 1202
  | .refreshCompleteMessage _ => 203
  | .sendKeyMessage _ => 1105
  | .logonMessage _ => 1101
  | .logonResponseMessage _ => 1102
  | .logoutMessage _ => 1103
  | .statisticsMessage _ => 60
  | .marketTurnoverMessage _ => 61
  | .yieldMessage _ => 44
  | .tradingSessionStatusMessage _ => 20
  | .securityStatusMessage _ => 21
  | .stockConnectDailyQuotaBalanceMessage _ => 80
  | .stockConnectMarketTurnoverMessage _ => 81
  | .tradeTickerMessage _ => 52
  | .vcmTriggerMessage _ => 23

def encode : Payload → List UInt8
  | .addOddLotOrderMessage message => AddOddLotOrderMessage.encode message
  | .aggregateOrderBookUpdateMessage message => AggregateOrderBookUpdateMessage.encode message
  | .brokerQueueMessage message => BrokerQueueMessage.encode message
  | .closingPriceMessage message => ClosingPriceMessage.encode message
  | .deleteOddLotOrderMessage message => DeleteOddLotOrderMessage.encode message
  | .indexDefinitionMessage message => IndexDefinitionMessage.encode message
  | .indexDataMessage message => IndexDataMessage.encode message
  | .indicativeEquilibriumPriceMessage message => IndicativeEquilibriumPriceMessage.encode message
  | .newsMessage message => NewsMessage.encode message
  | .nominalPriceMessage message => NominalPriceMessage.encode message
  | .orderImbalanceMessage message => OrderImbalanceMessage.encode message
  | .marketDefinitionMessage message => MarketDefinitionMessage.encode message
  | .securityDefinitionMessage message => SecurityDefinitionMessage.encode message
  | .liquidityProviderMessage message => LiquidityProviderMessage.encode message
  | .currencyRateMessage message => CurrencyRateMessage.encode message
  | .referencePriceMessage message => ReferencePriceMessage.encode message
  | .refreshRequestMessage message => RefreshRequestMessage.encode message
  | .refreshResponseMessage message => RefreshResponseMessage.encode message
  | .refreshCompleteMessage message => RefreshCompleteMessage.encode message
  | .sendKeyMessage message => SendKeyMessage.encode message
  | .logonMessage message => LogonMessage.encode message
  | .logonResponseMessage message => LogonResponseMessage.encode message
  | .logoutMessage message => LogoutMessage.encode message
  | .statisticsMessage message => StatisticsMessage.encode message
  | .marketTurnoverMessage message => MarketTurnoverMessage.encode message
  | .yieldMessage message => YieldMessage.encode message
  | .tradingSessionStatusMessage message => TradingSessionStatusMessage.encode message
  | .securityStatusMessage message => SecurityStatusMessage.encode message
  | .stockConnectDailyQuotaBalanceMessage message => StockConnectDailyQuotaBalanceMessage.encode message
  | .stockConnectMarketTurnoverMessage message => StockConnectMarketTurnoverMessage.encode message
  | .tradeTickerMessage message => TradeTickerMessage.encode message
  | .vcmTriggerMessage message => VcmTriggerMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 11010232 := by
  cases message with
  | addOddLotOrderMessage inner =>
    simp only [encode, AddOddLotOrderMessage.encode_length]
    omega
  | aggregateOrderBookUpdateMessage inner =>
    have bound_inner := AggregateOrderBookUpdateMessage.encode_length_le inner
    simp only [encode]
    omega
  | brokerQueueMessage inner =>
    have bound_inner := BrokerQueueMessage.encode_length_le inner
    simp only [encode]
    omega
  | closingPriceMessage inner =>
    simp only [encode, ClosingPriceMessage.encode_length]
    omega
  | deleteOddLotOrderMessage inner =>
    simp only [encode, DeleteOddLotOrderMessage.encode_length]
    omega
  | indexDefinitionMessage inner =>
    simp only [encode, IndexDefinitionMessage.encode_length]
    omega
  | indexDataMessage inner =>
    simp only [encode, IndexDataMessage.encode_length]
    omega
  | indicativeEquilibriumPriceMessage inner =>
    simp only [encode, IndicativeEquilibriumPriceMessage.encode_length]
    omega
  | newsMessage inner =>
    have bound_inner := NewsMessage.encode_length_le inner
    simp only [encode]
    omega
  | nominalPriceMessage inner =>
    simp only [encode, NominalPriceMessage.encode_length]
    omega
  | orderImbalanceMessage inner =>
    simp only [encode, OrderImbalanceMessage.encode_length]
    omega
  | marketDefinitionMessage inner =>
    simp only [encode, MarketDefinitionMessage.encode_length]
    omega
  | securityDefinitionMessage inner =>
    have bound_inner := SecurityDefinitionMessage.encode_length_le inner
    simp only [encode]
    omega
  | liquidityProviderMessage inner =>
    have bound_inner := LiquidityProviderMessage.encode_length_le inner
    simp only [encode]
    omega
  | currencyRateMessage inner =>
    simp only [encode, CurrencyRateMessage.encode_length]
    omega
  | referencePriceMessage inner =>
    simp only [encode, ReferencePriceMessage.encode_length]
    omega
  | refreshRequestMessage inner =>
    simp only [encode, RefreshRequestMessage.encode_length]
    omega
  | refreshResponseMessage inner =>
    simp only [encode, RefreshResponseMessage.encode_length]
    omega
  | refreshCompleteMessage inner =>
    simp only [encode, RefreshCompleteMessage.encode_length]
    omega
  | sendKeyMessage inner =>
    simp only [encode, SendKeyMessage.encode_length]
    omega
  | logonMessage inner =>
    simp only [encode, LogonMessage.encode_length]
    omega
  | logonResponseMessage inner =>
    simp only [encode, LogonResponseMessage.encode_length]
    omega
  | logoutMessage inner =>
    simp only [encode, LogoutMessage.encode_length]
    omega
  | statisticsMessage inner =>
    simp only [encode, StatisticsMessage.encode_length]
    omega
  | marketTurnoverMessage inner =>
    simp only [encode, MarketTurnoverMessage.encode_length]
    omega
  | yieldMessage inner =>
    simp only [encode, YieldMessage.encode_length]
    omega
  | tradingSessionStatusMessage inner =>
    simp only [encode, TradingSessionStatusMessage.encode_length]
    omega
  | securityStatusMessage inner =>
    simp only [encode, SecurityStatusMessage.encode_length]
    omega
  | stockConnectDailyQuotaBalanceMessage inner =>
    simp only [encode, StockConnectDailyQuotaBalanceMessage.encode_length]
    omega
  | stockConnectMarketTurnoverMessage inner =>
    simp only [encode, StockConnectMarketTurnoverMessage.encode_length]
    omega
  | tradeTickerMessage inner =>
    simp only [encode, TradeTickerMessage.encode_length]
    omega
  | vcmTriggerMessage inner =>
    simp only [encode, VcmTriggerMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 33 then (AddOddLotOrderMessage.decode bytes).map fun (message, rest) => (.addOddLotOrderMessage message, rest)
  else if tag = 53 then (AggregateOrderBookUpdateMessage.decode bytes).map fun (message, rest) => (.aggregateOrderBookUpdateMessage message, rest)
  else if tag = 54 then (BrokerQueueMessage.decode bytes).map fun (message, rest) => (.brokerQueueMessage message, rest)
  else if tag = 62 then (ClosingPriceMessage.decode bytes).map fun (message, rest) => (.closingPriceMessage message, rest)
  else if tag = 34 then (DeleteOddLotOrderMessage.decode bytes).map fun (message, rest) => (.deleteOddLotOrderMessage message, rest)
  else if tag = 70 then (IndexDefinitionMessage.decode bytes).map fun (message, rest) => (.indexDefinitionMessage message, rest)
  else if tag = 71 then (IndexDataMessage.decode bytes).map fun (message, rest) => (.indexDataMessage message, rest)
  else if tag = 41 then (IndicativeEquilibriumPriceMessage.decode bytes).map fun (message, rest) => (.indicativeEquilibriumPriceMessage message, rest)
  else if tag = 22 then (NewsMessage.decode bytes).map fun (message, rest) => (.newsMessage message, rest)
  else if tag = 40 then (NominalPriceMessage.decode bytes).map fun (message, rest) => (.nominalPriceMessage message, rest)
  else if tag = 56 then (OrderImbalanceMessage.decode bytes).map fun (message, rest) => (.orderImbalanceMessage message, rest)
  else if tag = 10 then (MarketDefinitionMessage.decode bytes).map fun (message, rest) => (.marketDefinitionMessage message, rest)
  else if tag = 11 then (SecurityDefinitionMessage.decode bytes).map fun (message, rest) => (.securityDefinitionMessage message, rest)
  else if tag = 13 then (LiquidityProviderMessage.decode bytes).map fun (message, rest) => (.liquidityProviderMessage message, rest)
  else if tag = 14 then (CurrencyRateMessage.decode bytes).map fun (message, rest) => (.currencyRateMessage message, rest)
  else if tag = 43 then (ReferencePriceMessage.decode bytes).map fun (message, rest) => (.referencePriceMessage message, rest)
  else if tag = 1201 then (RefreshRequestMessage.decode bytes).map fun (message, rest) => (.refreshRequestMessage message, rest)
  else if tag = 1202 then (RefreshResponseMessage.decode bytes).map fun (message, rest) => (.refreshResponseMessage message, rest)
  else if tag = 203 then (RefreshCompleteMessage.decode bytes).map fun (message, rest) => (.refreshCompleteMessage message, rest)
  else if tag = 1105 then (SendKeyMessage.decode bytes).map fun (message, rest) => (.sendKeyMessage message, rest)
  else if tag = 1101 then (LogonMessage.decode bytes).map fun (message, rest) => (.logonMessage message, rest)
  else if tag = 1102 then (LogonResponseMessage.decode bytes).map fun (message, rest) => (.logonResponseMessage message, rest)
  else if tag = 1103 then (LogoutMessage.decode bytes).map fun (message, rest) => (.logoutMessage message, rest)
  else if tag = 60 then (StatisticsMessage.decode bytes).map fun (message, rest) => (.statisticsMessage message, rest)
  else if tag = 61 then (MarketTurnoverMessage.decode bytes).map fun (message, rest) => (.marketTurnoverMessage message, rest)
  else if tag = 44 then (YieldMessage.decode bytes).map fun (message, rest) => (.yieldMessage message, rest)
  else if tag = 20 then (TradingSessionStatusMessage.decode bytes).map fun (message, rest) => (.tradingSessionStatusMessage message, rest)
  else if tag = 21 then (SecurityStatusMessage.decode bytes).map fun (message, rest) => (.securityStatusMessage message, rest)
  else if tag = 80 then (StockConnectDailyQuotaBalanceMessage.decode bytes).map fun (message, rest) => (.stockConnectDailyQuotaBalanceMessage message, rest)
  else if tag = 81 then (StockConnectMarketTurnoverMessage.decode bytes).map fun (message, rest) => (.stockConnectMarketTurnoverMessage message, rest)
  else if tag = 52 then (TradeTickerMessage.decode bytes).map fun (message, rest) => (.tradeTickerMessage message, rest)
  else if tag = 23 then (VcmTriggerMessage.decode bytes).map fun (message, rest) => (.vcmTriggerMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message -/
structure Message where
  filler : Alpha 2
  seqNum : BitVec 32
  internalSeqNum : BitVec 32
  sendTime : BitVec 64
  msgSize : BitVec 16
  payload : Payload
  deriving DecidableEq, Repr

namespace Message

def encodeBody (message : Message) : List UInt8 :=
  Alpha.encode message.filler
    ++ (encodeUIntLE 4 message.seqNum
    ++ (encodeUIntLE 4 message.internalSeqNum
    ++ (encodeUIntLE 8 message.sendTime
    ++ (encodeUIntLE 2 message.msgSize
    ++ (encodeUIntLE 2 (Payload.tag message.payload)
    ++ (Payload.encode message.payload))))))

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (filler, bytes) ← Alpha.decode 2 bytes
  let (seqNum, bytes) ← decodeUIntLE 4 bytes
  let (internalSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (sendTime, bytes) ← decodeUIntLE 8 bytes
  let (msgSize, bytes) ← decodeUIntLE 2 bytes
  let (msgType, bytes) ← decodeUIntLE 2 bytes
  let (payload, bytes) ← Payload.decode msgType bytes
  pure ({ filler, seqNum, internalSeqNum, sendTime, msgSize, payload }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Size rule: Msg Length counts the bytes after it plus 2, so it is written from the body; the body has no bound the prefix must fit, so it is read by its content and the prefix is not checked -/
def encode (message : Message) : List UInt8 :=
  encodeUIntLE 2 (BitVec.ofNat (8 * 2) ((encodeBody message).length + 2)) ++ encodeBody message

def decode (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (_, bytes) ← decodeUIntLE 2 bytes
  decodeBody bytes

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  exact decodeBody_encodeBody message rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]
  omega

end Message

/-- Packet -/
structure Packet where
  message : Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  Message.encode message.message

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (message, bytes) ← Message.decode bytes
  pure ({ message }, bytes)

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  have positive := Message.encode_length_pos message.message
  unfold encode
  omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Message.decode_encode, some_bind]
  rfl

end Packet

end Omi.HkexHkexsecuritiesMmdhOmdV21
