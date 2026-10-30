import Wire

/-!
# Athens Exchange Group Athens Exchange Derivatives Market Relaxed Channel v5.2

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.AthexAthexderivativesRelaxedIdsV52

/-- Message Subcategory: one byte code -/
def MessageSubcategory.codes : List UInt8 :=
  [0x20, 0x42, 0x45, 0x49, 0x4E, 0x53, 0x57, 0x4F, 0x46, 0x52, 0x56]

inductive MessageSubcategory where
  | generic -- Generic
  | bond -- Bond
  | etf -- Etf
  | stockIndex -- Stock Index
  | etfIndicativeNetAssetValue -- Etf Indicative Net Asset Value
  | stockRights -- Stock Rights
  | warrant -- Warrant
  | option -- Option
  | future -- Future
  | repos -- Repos
  | standardCombinations -- Standard Combinations
  | unlisted (byte : { byte : UInt8 // byte ∉ MessageSubcategory.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MessageSubcategory

def toByte : MessageSubcategory → UInt8
  | .generic => 0x20
  | .bond => 0x42
  | .etf => 0x45
  | .stockIndex => 0x49
  | .etfIndicativeNetAssetValue => 0x4E
  | .stockRights => 0x53
  | .warrant => 0x57
  | .option => 0x4F
  | .future => 0x46
  | .repos => 0x52
  | .standardCombinations => 0x56
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MessageSubcategory :=
  if byte = 0x20 then .generic
  else if byte = 0x42 then .bond
  else if byte = 0x45 then .etf
  else if byte = 0x49 then .stockIndex
  else if byte = 0x4E then .etfIndicativeNetAssetValue
  else if byte = 0x53 then .stockRights
  else if byte = 0x57 then .warrant
  else if byte = 0x4F then .option
  else if byte = 0x46 then .future
  else if byte = 0x52 then .repos
  else .standardCombinations

def ofByte (byte : UInt8) : MessageSubcategory :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MessageSubcategory) : ofByte value.toByte = value := by
  cases value with
  | generic => decide
  | bond => decide
  | etf => decide
  | stockIndex => decide
  | etfIndicativeNetAssetValue => decide
  | stockRights => decide
  | warrant => decide
  | option => decide
  | future => decide
  | repos => decide
  | standardCombinations => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MessageSubcategory) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MessageSubcategory × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MessageSubcategory) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : MessageSubcategory) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : MessageSubcategory) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MessageSubcategory

/-- Trade Id Indicator: one byte code -/
def TradeIdIndicator.codes : List UInt8 :=
  [0x31, 0x32]

inductive TradeIdIndicator where
  | oasisTradeId -- Oasis Trade Id
  | otherVenueTradeId -- Other Venue Trade Id
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeIdIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeIdIndicator

def toByte : TradeIdIndicator → UInt8
  | .oasisTradeId => 0x31
  | .otherVenueTradeId => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeIdIndicator :=
  if byte = 0x31 then .oasisTradeId
  else .otherVenueTradeId

def ofByte (byte : UInt8) : TradeIdIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeIdIndicator) : ofByte value.toByte = value := by
  cases value with
  | oasisTradeId => decide
  | otherVenueTradeId => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeIdIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeIdIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeIdIndicator) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TradeIdIndicator) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TradeIdIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeIdIndicator

/-- Transaction To Be Cleared: one byte code -/
def TransactionToBeCleared.codes : List UInt8 :=
  [0x30, 0x31]

inductive TransactionToBeCleared where
  | false_ -- False
  | true_ -- True
  | unlisted (byte : { byte : UInt8 // byte ∉ TransactionToBeCleared.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TransactionToBeCleared

def toByte : TransactionToBeCleared → UInt8
  | .false_ => 0x30
  | .true_ => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TransactionToBeCleared :=
  if byte = 0x30 then .false_
  else .true_

def ofByte (byte : UInt8) : TransactionToBeCleared :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TransactionToBeCleared) : ofByte value.toByte = value := by
  cases value with
  | false_ => decide
  | true_ => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TransactionToBeCleared) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TransactionToBeCleared × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TransactionToBeCleared) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TransactionToBeCleared) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TransactionToBeCleared) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TransactionToBeCleared

/-- Deferral Indicator: one byte code -/
def DeferralIndicator.codes : List UInt8 :=
  [0x30, 0x31]

inductive DeferralIndicator where
  | false_ -- False
  | true_ -- True
  | unlisted (byte : { byte : UInt8 // byte ∉ DeferralIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DeferralIndicator

def toByte : DeferralIndicator → UInt8
  | .false_ => 0x30
  | .true_ => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DeferralIndicator :=
  if byte = 0x30 then .false_
  else .true_

def ofByte (byte : UInt8) : DeferralIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DeferralIndicator) : ofByte value.toByte = value := by
  cases value with
  | false_ => decide
  | true_ => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DeferralIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DeferralIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DeferralIndicator) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : DeferralIndicator) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : DeferralIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DeferralIndicator

/-- Lmtf: one byte code -/
def Lmtf.codes : List UInt8 :=
  [0x30, 0x31]

inductive Lmtf where
  | false_ -- False
  | true_ -- True
  | unlisted (byte : { byte : UInt8 // byte ∉ Lmtf.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Lmtf

def toByte : Lmtf → UInt8
  | .false_ => 0x30
  | .true_ => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Lmtf :=
  if byte = 0x30 then .false_
  else .true_

def ofByte (byte : UInt8) : Lmtf :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Lmtf) : ofByte value.toByte = value := by
  cases value with
  | false_ => decide
  | true_ => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Lmtf) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Lmtf × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Lmtf) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Lmtf) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Lmtf) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Lmtf

/-- Fulf: one byte code -/
def Fulf.codes : List UInt8 :=
  [0x30, 0x31]

inductive Fulf where
  | false_ -- False
  | true_ -- True
  | unlisted (byte : { byte : UInt8 // byte ∉ Fulf.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Fulf

def toByte : Fulf → UInt8
  | .false_ => 0x30
  | .true_ => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Fulf :=
  if byte = 0x30 then .false_
  else .true_

def ofByte (byte : UInt8) : Fulf :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Fulf) : ofByte value.toByte = value := by
  cases value with
  | false_ => decide
  | true_ => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Fulf) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Fulf × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Fulf) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Fulf) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Fulf) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Fulf

/-- Datf: one byte code -/
def Datf.codes : List UInt8 :=
  [0x30, 0x31]

inductive Datf where
  | false_ -- False
  | true_ -- True
  | unlisted (byte : { byte : UInt8 // byte ∉ Datf.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Datf

def toByte : Datf → UInt8
  | .false_ => 0x30
  | .true_ => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Datf :=
  if byte = 0x30 then .false_
  else .true_

def ofByte (byte : UInt8) : Datf :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Datf) : ofByte value.toByte = value := by
  cases value with
  | false_ => decide
  | true_ => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Datf) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Datf × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Datf) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Datf) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Datf) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Datf

/-- Fula: one byte code -/
def Fula.codes : List UInt8 :=
  [0x30, 0x31]

inductive Fula where
  | false_ -- False
  | true_ -- True
  | unlisted (byte : { byte : UInt8 // byte ∉ Fula.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Fula

def toByte : Fula → UInt8
  | .false_ => 0x30
  | .true_ => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Fula :=
  if byte = 0x30 then .false_
  else .true_

def ofByte (byte : UInt8) : Fula :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Fula) : ofByte value.toByte = value := by
  cases value with
  | false_ => decide
  | true_ => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Fula) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Fula × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Fula) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Fula) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Fula) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Fula

/-- Volo: one byte code -/
def Volo.codes : List UInt8 :=
  [0x30, 0x31]

inductive Volo where
  | false_ -- False
  | true_ -- True
  | unlisted (byte : { byte : UInt8 // byte ∉ Volo.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Volo

def toByte : Volo → UInt8
  | .false_ => 0x30
  | .true_ => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Volo :=
  if byte = 0x30 then .false_
  else .true_

def ofByte (byte : UInt8) : Volo :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Volo) : ofByte value.toByte = value := by
  cases value with
  | false_ => decide
  | true_ => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Volo) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Volo × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Volo) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Volo) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Volo) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Volo

/-- Fulv: one byte code -/
def Fulv.codes : List UInt8 :=
  [0x30, 0x31]

inductive Fulv where
  | false_ -- False
  | true_ -- True
  | unlisted (byte : { byte : UInt8 // byte ∉ Fulv.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Fulv

def toByte : Fulv → UInt8
  | .false_ => 0x30
  | .true_ => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Fulv :=
  if byte = 0x30 then .false_
  else .true_

def ofByte (byte : UInt8) : Fulv :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Fulv) : ofByte value.toByte = value := by
  cases value with
  | false_ => decide
  | true_ => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Fulv) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Fulv × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Fulv) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Fulv) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Fulv) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Fulv

/-- Fwaf: one byte code -/
def Fwaf.codes : List UInt8 :=
  [0x30, 0x31]

inductive Fwaf where
  | false_ -- False
  | true_ -- True
  | unlisted (byte : { byte : UInt8 // byte ∉ Fwaf.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Fwaf

def toByte : Fwaf → UInt8
  | .false_ => 0x30
  | .true_ => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Fwaf :=
  if byte = 0x30 then .false_
  else .true_

def ofByte (byte : UInt8) : Fwaf :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Fwaf) : ofByte value.toByte = value := by
  cases value with
  | false_ => decide
  | true_ => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Fwaf) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Fwaf × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Fwaf) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Fwaf) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Fwaf) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Fwaf

/-- Fulj: one byte code -/
def Fulj.codes : List UInt8 :=
  [0x30, 0x31]

inductive Fulj where
  | false_ -- False
  | true_ -- True
  | unlisted (byte : { byte : UInt8 // byte ∉ Fulj.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Fulj

def toByte : Fulj → UInt8
  | .false_ => 0x30
  | .true_ => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Fulj :=
  if byte = 0x30 then .false_
  else .true_

def ofByte (byte : UInt8) : Fulj :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Fulj) : ofByte value.toByte = value := by
  cases value with
  | false_ => decide
  | true_ => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Fulj) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Fulj × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Fulj) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Fulj) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Fulj) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Fulj

/-- Idaf: one byte code -/
def Idaf.codes : List UInt8 :=
  [0x30, 0x31]

inductive Idaf where
  | false_ -- False
  | true_ -- True
  | unlisted (byte : { byte : UInt8 // byte ∉ Idaf.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Idaf

def toByte : Idaf → UInt8
  | .false_ => 0x30
  | .true_ => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Idaf :=
  if byte = 0x30 then .false_
  else .true_

def ofByte (byte : UInt8) : Idaf :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Idaf) : ofByte value.toByte = value := by
  cases value with
  | false_ => decide
  | true_ => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Idaf) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Idaf × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Idaf) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Idaf) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Idaf) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Idaf

/-- Volw: one byte code -/
def Volw.codes : List UInt8 :=
  [0x30, 0x31]

inductive Volw where
  | false_ -- False
  | true_ -- True
  | unlisted (byte : { byte : UInt8 // byte ∉ Volw.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Volw

def toByte : Volw → UInt8
  | .false_ => 0x30
  | .true_ => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Volw :=
  if byte = 0x30 then .false_
  else .true_

def ofByte (byte : UInt8) : Volw :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Volw) : ofByte value.toByte = value := by
  cases value with
  | false_ => decide
  | true_ => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Volw) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Volw × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Volw) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Volw) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Volw) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Volw

/-- Coaf: one byte code -/
def Coaf.codes : List UInt8 :=
  [0x30, 0x31]

inductive Coaf where
  | false_ -- False
  | true_ -- True
  | unlisted (byte : { byte : UInt8 // byte ∉ Coaf.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Coaf

def toByte : Coaf → UInt8
  | .false_ => 0x30
  | .true_ => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Coaf :=
  if byte = 0x30 then .false_
  else .true_

def ofByte (byte : UInt8) : Coaf :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Coaf) : ofByte value.toByte = value := by
  cases value with
  | false_ => decide
  | true_ => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Coaf) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Coaf × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Coaf) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Coaf) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Coaf) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Coaf

/-- Quote Type: one byte code -/
def QuoteType.codes : List UInt8 :=
  [0x31, 0x32]

inductive QuoteType where
  | bid -- Bid
  | offer -- Offer
  | unlisted (byte : { byte : UInt8 // byte ∉ QuoteType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace QuoteType

def toByte : QuoteType → UInt8
  | .bid => 0x31
  | .offer => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : QuoteType :=
  if byte = 0x31 then .bid
  else .offer

def ofByte (byte : UInt8) : QuoteType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : QuoteType) : ofByte value.toByte = value := by
  cases value with
  | bid => decide
  | offer => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : QuoteType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (QuoteType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : QuoteType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : QuoteType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : QuoteType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end QuoteType

/-- Quote Liquidity: one byte code -/
def QuoteLiquidity.codes : List UInt8 :=
  [0x31, 0x32]

inductive QuoteLiquidity where
  | liquidMarket -- Liquid Market
  | illiquidMarket -- Illiquid Market
  | unlisted (byte : { byte : UInt8 // byte ∉ QuoteLiquidity.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace QuoteLiquidity

def toByte : QuoteLiquidity → UInt8
  | .liquidMarket => 0x31
  | .illiquidMarket => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : QuoteLiquidity :=
  if byte = 0x31 then .liquidMarket
  else .illiquidMarket

def ofByte (byte : UInt8) : QuoteLiquidity :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : QuoteLiquidity) : ofByte value.toByte = value := by
  cases value with
  | liquidMarket => decide
  | illiquidMarket => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : QuoteLiquidity) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (QuoteLiquidity × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : QuoteLiquidity) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : QuoteLiquidity) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : QuoteLiquidity) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end QuoteLiquidity

/-- Apa Post Trade Message: 699 bytes -/
structure ApaPostTradeMessage where
  reportStatus : Alpha 4
  tradingDateAndTime : Alpha 20
  tradeIdIndicator : TradeIdIndicator
  tradeId : Alpha 52
  venue : Alpha 4
  transactionToBeCleared : TransactionToBeCleared
  priceNotation : Alpha 4
  price : Alpha 18
  priceCurrency : Alpha 3
  quantity : Alpha 18
  quantityCurrency : Alpha 3
  notationOfTheQuantityInMeasurementUnit : Alpha 25
  quantityInMeasurementUnit : Alpha 18
  notionalAmount : Alpha 18
  notionalCurrency : Alpha 3
  instrumentIdType : Alpha 4
  instrumentId : Alpha 12
  instrumentFullName : Alpha 350
  instrumentClassification : Alpha 6
  priceMultiplier : Alpha 18
  underlyingInstrumentCode : Alpha 12
  underlyingIndexName : Alpha 25
  termOfTheUnderlyingIndex : Alpha 7
  optionType : Alpha 4
  strikePrice : Alpha 18
  strikePriceCurrency : Alpha 3
  strikePriceNotation : Alpha 4
  optionExerciseStyle : Alpha 4
  maturityDate : Alpha 8
  expiryDate : Alpha 8
  deliveryType : Alpha 4
  typeEmissionAllowance : Alpha 4
  otcPostTradeIndicator : Alpha 4
  deferralIndicator : DeferralIndicator
  lmtf : Lmtf
  fulf : Fulf
  datf : Datf
  fula : Fula
  volo : Volo
  fulv : Fulv
  fwaf : Fwaf
  fulj : Fulj
  idaf : Idaf
  volw : Volw
  coaf : Coaf
  deriving DecidableEq, Repr

namespace ApaPostTradeMessage

def encode (message : ApaPostTradeMessage) : List UInt8 :=
  Alpha.encode message.reportStatus
    ++ (Alpha.encode message.tradingDateAndTime
    ++ (TradeIdIndicator.encode message.tradeIdIndicator
    ++ (Alpha.encode message.tradeId
    ++ (Alpha.encode message.venue
    ++ (TransactionToBeCleared.encode message.transactionToBeCleared
    ++ (Alpha.encode message.priceNotation
    ++ (Alpha.encode message.price
    ++ (Alpha.encode message.priceCurrency
    ++ (Alpha.encode message.quantity
    ++ (Alpha.encode message.quantityCurrency
    ++ (Alpha.encode message.notationOfTheQuantityInMeasurementUnit
    ++ (Alpha.encode message.quantityInMeasurementUnit
    ++ (Alpha.encode message.notionalAmount
    ++ (Alpha.encode message.notionalCurrency
    ++ (Alpha.encode message.instrumentIdType
    ++ (Alpha.encode message.instrumentId
    ++ (Alpha.encode message.instrumentFullName
    ++ (Alpha.encode message.instrumentClassification
    ++ (Alpha.encode message.priceMultiplier
    ++ (Alpha.encode message.underlyingInstrumentCode
    ++ (Alpha.encode message.underlyingIndexName
    ++ (Alpha.encode message.termOfTheUnderlyingIndex
    ++ (Alpha.encode message.optionType
    ++ (Alpha.encode message.strikePrice
    ++ (Alpha.encode message.strikePriceCurrency
    ++ (Alpha.encode message.strikePriceNotation
    ++ (Alpha.encode message.optionExerciseStyle
    ++ (Alpha.encode message.maturityDate
    ++ (Alpha.encode message.expiryDate
    ++ (Alpha.encode message.deliveryType
    ++ (Alpha.encode message.typeEmissionAllowance
    ++ (Alpha.encode message.otcPostTradeIndicator
    ++ (DeferralIndicator.encode message.deferralIndicator
    ++ (Lmtf.encode message.lmtf
    ++ (Fulf.encode message.fulf
    ++ (Datf.encode message.datf
    ++ (Fula.encode message.fula
    ++ (Volo.encode message.volo
    ++ (Fulv.encode message.fulv
    ++ (Fwaf.encode message.fwaf
    ++ (Fulj.encode message.fulj
    ++ (Idaf.encode message.idaf
    ++ (Volw.encode message.volw
    ++ (Coaf.encode message.coaf))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ApaPostTradeMessage × List UInt8) := do
  let (reportStatus, bytes) ← Alpha.decode 4 bytes
  let (tradingDateAndTime, bytes) ← Alpha.decode 20 bytes
  let (tradeIdIndicator, bytes) ← TradeIdIndicator.decode bytes
  let (tradeId, bytes) ← Alpha.decode 52 bytes
  let (venue, bytes) ← Alpha.decode 4 bytes
  let (transactionToBeCleared, bytes) ← TransactionToBeCleared.decode bytes
  let (priceNotation, bytes) ← Alpha.decode 4 bytes
  let (price, bytes) ← Alpha.decode 18 bytes
  let (priceCurrency, bytes) ← Alpha.decode 3 bytes
  let (quantity, bytes) ← Alpha.decode 18 bytes
  let (quantityCurrency, bytes) ← Alpha.decode 3 bytes
  let (notationOfTheQuantityInMeasurementUnit, bytes) ← Alpha.decode 25 bytes
  let (quantityInMeasurementUnit, bytes) ← Alpha.decode 18 bytes
  let (notionalAmount, bytes) ← Alpha.decode 18 bytes
  let (notionalCurrency, bytes) ← Alpha.decode 3 bytes
  let (instrumentIdType, bytes) ← Alpha.decode 4 bytes
  let (instrumentId, bytes) ← Alpha.decode 12 bytes
  let (instrumentFullName, bytes) ← Alpha.decode 350 bytes
  let (instrumentClassification, bytes) ← Alpha.decode 6 bytes
  let (priceMultiplier, bytes) ← Alpha.decode 18 bytes
  let (underlyingInstrumentCode, bytes) ← Alpha.decode 12 bytes
  let (underlyingIndexName, bytes) ← Alpha.decode 25 bytes
  let (termOfTheUnderlyingIndex, bytes) ← Alpha.decode 7 bytes
  let (optionType, bytes) ← Alpha.decode 4 bytes
  let (strikePrice, bytes) ← Alpha.decode 18 bytes
  let (strikePriceCurrency, bytes) ← Alpha.decode 3 bytes
  let (strikePriceNotation, bytes) ← Alpha.decode 4 bytes
  let (optionExerciseStyle, bytes) ← Alpha.decode 4 bytes
  let (maturityDate, bytes) ← Alpha.decode 8 bytes
  let (expiryDate, bytes) ← Alpha.decode 8 bytes
  let (deliveryType, bytes) ← Alpha.decode 4 bytes
  let (typeEmissionAllowance, bytes) ← Alpha.decode 4 bytes
  let (otcPostTradeIndicator, bytes) ← Alpha.decode 4 bytes
  let (deferralIndicator, bytes) ← DeferralIndicator.decode bytes
  let (lmtf, bytes) ← Lmtf.decode bytes
  let (fulf, bytes) ← Fulf.decode bytes
  let (datf, bytes) ← Datf.decode bytes
  let (fula, bytes) ← Fula.decode bytes
  let (volo, bytes) ← Volo.decode bytes
  let (fulv, bytes) ← Fulv.decode bytes
  let (fwaf, bytes) ← Fwaf.decode bytes
  let (fulj, bytes) ← Fulj.decode bytes
  let (idaf, bytes) ← Idaf.decode bytes
  let (volw, bytes) ← Volw.decode bytes
  let (coaf, bytes) ← Coaf.decode bytes
  pure ({ reportStatus, tradingDateAndTime, tradeIdIndicator, tradeId, venue, transactionToBeCleared, priceNotation, price, priceCurrency, quantity, quantityCurrency, notationOfTheQuantityInMeasurementUnit, quantityInMeasurementUnit, notionalAmount, notionalCurrency, instrumentIdType, instrumentId, instrumentFullName, instrumentClassification, priceMultiplier, underlyingInstrumentCode, underlyingIndexName, termOfTheUnderlyingIndex, optionType, strikePrice, strikePriceCurrency, strikePriceNotation, optionExerciseStyle, maturityDate, expiryDate, deliveryType, typeEmissionAllowance, otcPostTradeIndicator, deferralIndicator, lmtf, fulf, datf, fula, volo, fulv, fwaf, fulj, idaf, volw, coaf }, bytes)

@[simp] theorem encode_length (message : ApaPostTradeMessage) : (encode message).length = 699 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, TradeIdIndicator.encode_length, TransactionToBeCleared.encode_length, DeferralIndicator.encode_length, Lmtf.encode_length, Fulf.encode_length, Datf.encode_length, Fula.encode_length, Volo.encode_length, Fulv.encode_length, Fwaf.encode_length, Fulj.encode_length, Idaf.encode_length, Volw.encode_length, Coaf.encode_length]

theorem encode_length_pos (message : ApaPostTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ApaPostTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeIdIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TransactionToBeCleared.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DeferralIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Lmtf.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Fulf.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Datf.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Fula.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Volo.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Fulv.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Fwaf.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Fulj.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Idaf.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Volw.decode_encode, some_bind]
  dsimp only
  rw [Coaf.decode_encode, some_bind]
  rfl

end ApaPostTradeMessage

/-- Apa Pre Trade Message: 699 bytes -/
structure ApaPreTradeMessage where
  reportStatus : Alpha 4
  quoteType : QuoteType
  quoteId : Alpha 52
  eventTime : Alpha 20
  quoteLiquidity : QuoteLiquidity
  venueMic : Alpha 4
  submittingEntityIdentificationCode : Alpha 20
  priceNotation : Alpha 4
  price : Alpha 18
  priceCurrency : Alpha 3
  quantity : Alpha 18
  quantityCurrency : Alpha 3
  notationOfTheQuantityInMeasurementUnit : Alpha 25
  quantityInMeasurementUnit : Alpha 18
  notionalAmount : Alpha 18
  notionalCurrency : Alpha 3
  instrumentIdType : Alpha 4
  instrumentId : Alpha 12
  instrumentFullName : Alpha 350
  instrumentClassification : Alpha 6
  priceMultiplier : Alpha 18
  underlyingInstrumentCode : Alpha 12
  underlyingIndexName : Alpha 25
  termOfTheUnderlyingIndex : Alpha 7
  optionType : Alpha 4
  strikePrice : Alpha 18
  strikePriceCurrency : Alpha 3
  strikePriceNotation : Alpha 4
  optionExerciseStyle : Alpha 4
  maturityDate : Alpha 8
  expiryDate : Alpha 8
  deliveryType : Alpha 4
  deriving DecidableEq, Repr

namespace ApaPreTradeMessage

def encode (message : ApaPreTradeMessage) : List UInt8 :=
  Alpha.encode message.reportStatus
    ++ (QuoteType.encode message.quoteType
    ++ (Alpha.encode message.quoteId
    ++ (Alpha.encode message.eventTime
    ++ (QuoteLiquidity.encode message.quoteLiquidity
    ++ (Alpha.encode message.venueMic
    ++ (Alpha.encode message.submittingEntityIdentificationCode
    ++ (Alpha.encode message.priceNotation
    ++ (Alpha.encode message.price
    ++ (Alpha.encode message.priceCurrency
    ++ (Alpha.encode message.quantity
    ++ (Alpha.encode message.quantityCurrency
    ++ (Alpha.encode message.notationOfTheQuantityInMeasurementUnit
    ++ (Alpha.encode message.quantityInMeasurementUnit
    ++ (Alpha.encode message.notionalAmount
    ++ (Alpha.encode message.notionalCurrency
    ++ (Alpha.encode message.instrumentIdType
    ++ (Alpha.encode message.instrumentId
    ++ (Alpha.encode message.instrumentFullName
    ++ (Alpha.encode message.instrumentClassification
    ++ (Alpha.encode message.priceMultiplier
    ++ (Alpha.encode message.underlyingInstrumentCode
    ++ (Alpha.encode message.underlyingIndexName
    ++ (Alpha.encode message.termOfTheUnderlyingIndex
    ++ (Alpha.encode message.optionType
    ++ (Alpha.encode message.strikePrice
    ++ (Alpha.encode message.strikePriceCurrency
    ++ (Alpha.encode message.strikePriceNotation
    ++ (Alpha.encode message.optionExerciseStyle
    ++ (Alpha.encode message.maturityDate
    ++ (Alpha.encode message.expiryDate
    ++ (Alpha.encode message.deliveryType)))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ApaPreTradeMessage × List UInt8) := do
  let (reportStatus, bytes) ← Alpha.decode 4 bytes
  let (quoteType, bytes) ← QuoteType.decode bytes
  let (quoteId, bytes) ← Alpha.decode 52 bytes
  let (eventTime, bytes) ← Alpha.decode 20 bytes
  let (quoteLiquidity, bytes) ← QuoteLiquidity.decode bytes
  let (venueMic, bytes) ← Alpha.decode 4 bytes
  let (submittingEntityIdentificationCode, bytes) ← Alpha.decode 20 bytes
  let (priceNotation, bytes) ← Alpha.decode 4 bytes
  let (price, bytes) ← Alpha.decode 18 bytes
  let (priceCurrency, bytes) ← Alpha.decode 3 bytes
  let (quantity, bytes) ← Alpha.decode 18 bytes
  let (quantityCurrency, bytes) ← Alpha.decode 3 bytes
  let (notationOfTheQuantityInMeasurementUnit, bytes) ← Alpha.decode 25 bytes
  let (quantityInMeasurementUnit, bytes) ← Alpha.decode 18 bytes
  let (notionalAmount, bytes) ← Alpha.decode 18 bytes
  let (notionalCurrency, bytes) ← Alpha.decode 3 bytes
  let (instrumentIdType, bytes) ← Alpha.decode 4 bytes
  let (instrumentId, bytes) ← Alpha.decode 12 bytes
  let (instrumentFullName, bytes) ← Alpha.decode 350 bytes
  let (instrumentClassification, bytes) ← Alpha.decode 6 bytes
  let (priceMultiplier, bytes) ← Alpha.decode 18 bytes
  let (underlyingInstrumentCode, bytes) ← Alpha.decode 12 bytes
  let (underlyingIndexName, bytes) ← Alpha.decode 25 bytes
  let (termOfTheUnderlyingIndex, bytes) ← Alpha.decode 7 bytes
  let (optionType, bytes) ← Alpha.decode 4 bytes
  let (strikePrice, bytes) ← Alpha.decode 18 bytes
  let (strikePriceCurrency, bytes) ← Alpha.decode 3 bytes
  let (strikePriceNotation, bytes) ← Alpha.decode 4 bytes
  let (optionExerciseStyle, bytes) ← Alpha.decode 4 bytes
  let (maturityDate, bytes) ← Alpha.decode 8 bytes
  let (expiryDate, bytes) ← Alpha.decode 8 bytes
  let (deliveryType, bytes) ← Alpha.decode 4 bytes
  pure ({ reportStatus, quoteType, quoteId, eventTime, quoteLiquidity, venueMic, submittingEntityIdentificationCode, priceNotation, price, priceCurrency, quantity, quantityCurrency, notationOfTheQuantityInMeasurementUnit, quantityInMeasurementUnit, notionalAmount, notionalCurrency, instrumentIdType, instrumentId, instrumentFullName, instrumentClassification, priceMultiplier, underlyingInstrumentCode, underlyingIndexName, termOfTheUnderlyingIndex, optionType, strikePrice, strikePriceCurrency, strikePriceNotation, optionExerciseStyle, maturityDate, expiryDate, deliveryType }, bytes)

@[simp] theorem encode_length (message : ApaPreTradeMessage) : (encode message).length = 699 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, QuoteType.encode_length, QuoteLiquidity.encode_length]

theorem encode_length_pos (message : ApaPreTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ApaPreTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, QuoteType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, QuoteLiquidity.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ApaPreTradeMessage

/-- Any Message Text, selected by Message Category -/
inductive MessageText where
  | apaPostTradeMessage (message : ApaPostTradeMessage) -- "U" 0x55
  | apaPreTradeMessage (message : ApaPreTradeMessage) -- "V" 0x56
  deriving DecidableEq, Repr

namespace MessageText

/-- The Message Category each message is sent under -/
def tag : MessageText → BitVec 8
  | .apaPostTradeMessage _ => 85
  | .apaPreTradeMessage _ => 86

def encode : MessageText → List UInt8
  | .apaPostTradeMessage message => ApaPostTradeMessage.encode message
  | .apaPreTradeMessage message => ApaPreTradeMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : MessageText) : (encode message).length ≤ 699 := by
  cases message with
  | apaPostTradeMessage inner =>
    simp only [encode, ApaPostTradeMessage.encode_length]
    omega
  | apaPreTradeMessage inner =>
    simp only [encode, ApaPreTradeMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (MessageText × List UInt8) :=
  if tag = 85 then (ApaPostTradeMessage.decode bytes).map fun (message, rest) => (.apaPostTradeMessage message, rest)
  else if tag = 86 then (ApaPreTradeMessage.decode bytes).map fun (message, rest) => (.apaPreTradeMessage message, rest)
  else none

@[simp] theorem decode_encode (message : MessageText) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end MessageText

/-- Packet -/
structure Packet where
  soh : BitVec 8
  vendorIdentifier : Alpha 2
  messageSubcategory : MessageSubcategory
  venueId : Alpha 4
  messageSequenceNumber : Alpha 7
  publicationTimestamp : Alpha 20
  messageText : MessageText
  etx : BitVec 8
  lrc : BitVec 8
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUInt 1 message.soh
    ++ (Alpha.encode message.vendorIdentifier
    ++ (encodeUInt 1 (MessageText.tag message.messageText)
    ++ (MessageSubcategory.encode message.messageSubcategory
    ++ (Alpha.encode message.venueId
    ++ (Alpha.encode message.messageSequenceNumber
    ++ (Alpha.encode message.publicationTimestamp
    ++ (MessageText.encode message.messageText
    ++ (encodeUInt 1 message.etx
    ++ (encodeUInt 1 message.lrc)))))))))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (soh, bytes) ← decodeUInt 1 bytes
  let (vendorIdentifier, bytes) ← Alpha.decode 2 bytes
  let (messageCategory, bytes) ← decodeUInt 1 bytes
  let (messageSubcategory, bytes) ← MessageSubcategory.decode bytes
  let (venueId, bytes) ← Alpha.decode 4 bytes
  let (messageSequenceNumber, bytes) ← Alpha.decode 7 bytes
  let (publicationTimestamp, bytes) ← Alpha.decode 20 bytes
  let (messageText, bytes) ← MessageText.decode messageCategory bytes
  let (etx, bytes) ← decodeUInt 1 bytes
  let (lrc, bytes) ← decodeUInt 1 bytes
  pure ({ soh, vendorIdentifier, messageSubcategory, venueId, messageSequenceNumber, publicationTimestamp, messageText, etx, lrc }, bytes)

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Packet) : (encode message).length ≤ 737 := by
  unfold encode
  cases message.messageText with
  | apaPostTradeMessage inner =>
    simp only [MessageText.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, MessageSubcategory.encode_length, ApaPostTradeMessage.encode_length]
    omega
  | apaPreTradeMessage inner =>
    simp only [MessageText.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, MessageSubcategory.encode_length, ApaPreTradeMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MessageSubcategory.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MessageText.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end Packet

end Omi.AthexAthexderivativesRelaxedIdsV52
