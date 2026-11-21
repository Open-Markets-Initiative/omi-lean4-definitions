import Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Global Index Data Service v1.0.i

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.

Note: a Message Count of 0 marks Heartbeat and carries no messages; the decoder reads it as a count
and the encoder never writes it

Note: a Message Count of 65535 marks End Of Session and carries no messages; the decoder reads it as
a count and the encoder never writes it

Note: Message's Message Length is written from its body but not checked on decode, since the body
has no bound the prefix must fit; the body is read by its content

License: MIT No Attribution
-/

namespace Omi.NasdaqIndexGidsItchV10I

/-- Event Code: one byte code -/
def EventCode.codes : List UInt8 :=
  [0x4F, 0x53, 0x45, 0x43, 0x51, 0x4D]

inductive EventCode where
  | startOfMessages -- Start Of Messages
  | startOfDay -- Start Of Day
  | endOfDay -- End Of Day
  | endOfMessages -- End Of Messages
  | sessionOpen -- Session Open
  | sessionClose -- Session Close
  | unlisted (byte : { byte : UInt8 // byte ∉ EventCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventCode

def toByte : EventCode → UInt8
  | .startOfMessages => 0x4F
  | .startOfDay => 0x53
  | .endOfDay => 0x45
  | .endOfMessages => 0x43
  | .sessionOpen => 0x51
  | .sessionClose => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventCode :=
  if byte = 0x4F then .startOfMessages
  else if byte = 0x53 then .startOfDay
  else if byte = 0x45 then .endOfDay
  else if byte = 0x43 then .endOfMessages
  else if byte = 0x51 then .sessionOpen
  else .sessionClose

def ofByte (byte : UInt8) : EventCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventCode) : ofByte value.toByte = value := by
  cases value with
  | startOfMessages => decide
  | startOfDay => decide
  | endOfDay => decide
  | endOfMessages => decide
  | sessionOpen => decide
  | sessionClose => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : EventCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (EventCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : EventCode) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : EventCode) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : EventCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end EventCode

/-- Dissemination Flag: one byte code -/
def DisseminationFlag.codes : List UInt8 :=
  [0x59, 0x4E]

inductive DisseminationFlag where
  | disseminated -- Disseminated
  | notDisseminated -- Not Disseminated
  | unlisted (byte : { byte : UInt8 // byte ∉ DisseminationFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DisseminationFlag

def toByte : DisseminationFlag → UInt8
  | .disseminated => 0x59
  | .notDisseminated => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DisseminationFlag :=
  if byte = 0x59 then .disseminated
  else .notDisseminated

def ofByte (byte : UInt8) : DisseminationFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DisseminationFlag) : ofByte value.toByte = value := by
  cases value with
  | disseminated => decide
  | notDisseminated => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DisseminationFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DisseminationFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DisseminationFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : DisseminationFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : DisseminationFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DisseminationFlag

/-- Financial Product Type: one byte code -/
def FinancialProductType.codes : List UInt8 :=
  [0x20, 0x49, 0x45, 0x4E, 0x46, 0x53, 0x50, 0x4C, 0x57, 0x41]

inductive FinancialProductType where
  | notSpecified -- Not Specified
  | index -- Index
  | exchangeTradedFund -- Exchange Traded Fund
  | exchangeTradedNote -- Exchange Traded Note
  | exchangeTradedManagedFund -- Exchange Traded Managed Fund
  | settlement -- Settlement
  | spot -- Spot
  | subordinatedProduct -- Subordinated Product
  | worldCurrency -- World Currency
  | alphaIndex -- Alpha Index
  | unlisted (byte : { byte : UInt8 // byte ∉ FinancialProductType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace FinancialProductType

def toByte : FinancialProductType → UInt8
  | .notSpecified => 0x20
  | .index => 0x49
  | .exchangeTradedFund => 0x45
  | .exchangeTradedNote => 0x4E
  | .exchangeTradedManagedFund => 0x46
  | .settlement => 0x53
  | .spot => 0x50
  | .subordinatedProduct => 0x4C
  | .worldCurrency => 0x57
  | .alphaIndex => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : FinancialProductType :=
  if byte = 0x20 then .notSpecified
  else if byte = 0x49 then .index
  else if byte = 0x45 then .exchangeTradedFund
  else if byte = 0x4E then .exchangeTradedNote
  else if byte = 0x46 then .exchangeTradedManagedFund
  else if byte = 0x53 then .settlement
  else if byte = 0x50 then .spot
  else if byte = 0x4C then .subordinatedProduct
  else if byte = 0x57 then .worldCurrency
  else .alphaIndex

def ofByte (byte : UInt8) : FinancialProductType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : FinancialProductType) : ofByte value.toByte = value := by
  cases value with
  | notSpecified => decide
  | index => decide
  | exchangeTradedFund => decide
  | exchangeTradedNote => decide
  | exchangeTradedManagedFund => decide
  | settlement => decide
  | spot => decide
  | subordinatedProduct => decide
  | worldCurrency => decide
  | alphaIndex => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : FinancialProductType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (FinancialProductType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : FinancialProductType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : FinancialProductType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : FinancialProductType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end FinancialProductType

/-- Market Cap Size: one byte code -/
def MarketCapSize.codes : List UInt8 :=
  [0x20, 0x41, 0x4C, 0x4D, 0x53, 0x58, 0x59]

inductive MarketCapSize where
  | notSpecified -- Not Specified
  | all -- All
  | large -- Large
  | mid -- Mid
  | small -- Small
  | largeAndMid -- Large And Mid
  | midAndSmall -- Mid And Small
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketCapSize.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketCapSize

def toByte : MarketCapSize → UInt8
  | .notSpecified => 0x20
  | .all => 0x41
  | .large => 0x4C
  | .mid => 0x4D
  | .small => 0x53
  | .largeAndMid => 0x58
  | .midAndSmall => 0x59
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketCapSize :=
  if byte = 0x20 then .notSpecified
  else if byte = 0x41 then .all
  else if byte = 0x4C then .large
  else if byte = 0x4D then .mid
  else if byte = 0x53 then .small
  else if byte = 0x58 then .largeAndMid
  else .midAndSmall

def ofByte (byte : UInt8) : MarketCapSize :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketCapSize) : ofByte value.toByte = value := by
  cases value with
  | notSpecified => decide
  | all => decide
  | large => decide
  | mid => decide
  | small => decide
  | largeAndMid => decide
  | midAndSmall => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarketCapSize) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketCapSize × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketCapSize) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : MarketCapSize) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : MarketCapSize) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarketCapSize

/-- Index Settlement Type: one byte code -/
def IndexSettlementType.codes : List UInt8 :=
  [0x20, 0x4F, 0x43, 0x4D]

inductive IndexSettlementType where
  | notSpecified -- Not Specified
  | settlesAtTheOpen -- Settles At The Open
  | settlesAtTheClose -- Settles At The Close
  | settlesAtMidDay -- Settles At Mid Day
  | unlisted (byte : { byte : UInt8 // byte ∉ IndexSettlementType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace IndexSettlementType

def toByte : IndexSettlementType → UInt8
  | .notSpecified => 0x20
  | .settlesAtTheOpen => 0x4F
  | .settlesAtTheClose => 0x43
  | .settlesAtMidDay => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : IndexSettlementType :=
  if byte = 0x20 then .notSpecified
  else if byte = 0x4F then .settlesAtTheOpen
  else if byte = 0x43 then .settlesAtTheClose
  else .settlesAtMidDay

def ofByte (byte : UInt8) : IndexSettlementType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : IndexSettlementType) : ofByte value.toByte = value := by
  cases value with
  | notSpecified => decide
  | settlesAtTheOpen => decide
  | settlesAtTheClose => decide
  | settlesAtMidDay => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : IndexSettlementType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (IndexSettlementType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : IndexSettlementType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : IndexSettlementType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : IndexSettlementType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end IndexSettlementType

/-- State: one byte code -/
def State.codes : List UInt8 :=
  [0x41, 0x48, 0x50, 0x44]

inductive State where
  | active -- Active
  | held -- Held
  | pending -- Pending
  | deleted -- Deleted
  | unlisted (byte : { byte : UInt8 // byte ∉ State.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace State

def toByte : State → UInt8
  | .active => 0x41
  | .held => 0x48
  | .pending => 0x50
  | .deleted => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : State :=
  if byte = 0x41 then .active
  else if byte = 0x48 then .held
  else if byte = 0x50 then .pending
  else .deleted

def ofByte (byte : UInt8) : State :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : State) : ofByte value.toByte = value := by
  cases value with
  | active => decide
  | held => decide
  | pending => decide
  | deleted => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : State) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (State × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : State) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : State) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : State) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end State

/-- Index Usage: one byte code -/
def IndexUsage.codes : List UInt8 :=
  [0x4C, 0x44, 0x54]

inductive IndexUsage where
  | live -- Live
  | demo -- Demo
  | test -- Test
  | unlisted (byte : { byte : UInt8 // byte ∉ IndexUsage.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace IndexUsage

def toByte : IndexUsage → UInt8
  | .live => 0x4C
  | .demo => 0x44
  | .test => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : IndexUsage :=
  if byte = 0x4C then .live
  else if byte = 0x44 then .demo
  else .test

def ofByte (byte : UInt8) : IndexUsage :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : IndexUsage) : ofByte value.toByte = value := by
  cases value with
  | live => decide
  | demo => decide
  | test => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : IndexUsage) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (IndexUsage × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : IndexUsage) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : IndexUsage) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : IndexUsage) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end IndexUsage

/-- Tick Direction: one byte code -/
def TickDirection.codes : List UInt8 :=
  [0x2B, 0x2D, 0x20]

inductive TickDirection where
  | positive -- Positive
  | negative -- Negative
  | noNetChangeCalculated -- No Net Change Calculated
  | unlisted (byte : { byte : UInt8 // byte ∉ TickDirection.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TickDirection

def toByte : TickDirection → UInt8
  | .positive => 0x2B
  | .negative => 0x2D
  | .noNetChangeCalculated => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TickDirection :=
  if byte = 0x2B then .positive
  else if byte = 0x2D then .negative
  else .noNetChangeCalculated

def ofByte (byte : UInt8) : TickDirection :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TickDirection) : ofByte value.toByte = value := by
  cases value with
  | positive => decide
  | negative => decide
  | noNetChangeCalculated => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TickDirection) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TickDirection × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TickDirection) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TickDirection) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TickDirection) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TickDirection

/-- Settlement Type: one byte code -/
def SettlementType.codes : List UInt8 :=
  [0x20, 0x4F, 0x43, 0x4D]

inductive SettlementType where
  | notSpecified -- Not Specified
  | settlesAtTheOpen -- Settles At The Open
  | settlesAtTheClose -- Settles At The Close
  | settlesAtMidDay -- Settles At Mid Day
  | unlisted (byte : { byte : UInt8 // byte ∉ SettlementType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SettlementType

def toByte : SettlementType → UInt8
  | .notSpecified => 0x20
  | .settlesAtTheOpen => 0x4F
  | .settlesAtTheClose => 0x43
  | .settlesAtMidDay => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SettlementType :=
  if byte = 0x20 then .notSpecified
  else if byte = 0x4F then .settlesAtTheOpen
  else if byte = 0x43 then .settlesAtTheClose
  else .settlesAtMidDay

def ofByte (byte : UInt8) : SettlementType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SettlementType) : ofByte value.toByte = value := by
  cases value with
  | notSpecified => decide
  | settlesAtTheOpen => decide
  | settlesAtTheClose => decide
  | settlesAtMidDay => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SettlementType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SettlementType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SettlementType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SettlementType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SettlementType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SettlementType

/-- Timestamp Seconds Message: 4 bytes -/
structure TimestampSecondsMessage where
  second : BitVec 32
  deriving DecidableEq, Repr

namespace TimestampSecondsMessage

def encode (message : TimestampSecondsMessage) : List UInt8 :=
  encodeUInt 4 message.second

def decode (bytes : List UInt8) : Option (TimestampSecondsMessage × List UInt8) := do
  let (second, bytes) ← decodeUInt 4 bytes
  pure ({ second }, bytes)

@[simp] theorem encode_length (message : TimestampSecondsMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : TimestampSecondsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TimestampSecondsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TimestampSecondsMessage

/-- System Event Message: 8 bytes -/
structure SystemEventMessage where
  nanoseconds : BitVec 32
  eventCode : EventCode
  schedule : Alpha 3
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (EventCode.encode message.eventCode
    ++ (Alpha.encode message.schedule))

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (eventCode, bytes) ← EventCode.decode bytes
  let (schedule, bytes) ← Alpha.decode 3 bytes
  pure ({ nanoseconds, eventCode, schedule }, bytes)

@[simp] theorem encode_length (message : SystemEventMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, EventCode.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : SystemEventMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemEventMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, EventCode.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SystemEventMessage

/-- Index Directory Message -/
structure IndexDirectoryMessage where
  nanoseconds : BitVec 32
  instrumentId : Alpha 18
  disseminationFlag : DisseminationFlag
  financialProductType : FinancialProductType
  brand : Alpha 2
  series : Alpha 3
  strategy : Alpha 3
  assetType : Alpha 2
  marketCapSize : MarketCapSize
  currency : Alpha 3
  geography : Alpha 4
  indexSettlementType : IndexSettlementType
  indexCalculationMethod : Alpha 3
  state : State
  indexUsage : IndexUsage
  schedule : Alpha 3
  frequency : Alpha 4
  numberOfIssueParticipationMessages : BitVec 32
  baseValue : BitVec 64
  baseDate : BitVec 32
  instrumentName : Bounded 2 UInt8
  deriving DecidableEq, Repr

namespace IndexDirectoryMessage

def encode (message : IndexDirectoryMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (Alpha.encode message.instrumentId
    ++ (DisseminationFlag.encode message.disseminationFlag
    ++ (FinancialProductType.encode message.financialProductType
    ++ (Alpha.encode message.brand
    ++ (Alpha.encode message.series
    ++ (Alpha.encode message.strategy
    ++ (Alpha.encode message.assetType
    ++ (MarketCapSize.encode message.marketCapSize
    ++ (Alpha.encode message.currency
    ++ (Alpha.encode message.geography
    ++ (IndexSettlementType.encode message.indexSettlementType
    ++ (Alpha.encode message.indexCalculationMethod
    ++ (State.encode message.state
    ++ (IndexUsage.encode message.indexUsage
    ++ (Alpha.encode message.schedule
    ++ (Alpha.encode message.frequency
    ++ (encodeUInt 4 message.numberOfIssueParticipationMessages
    ++ (encodeUInt 8 message.baseValue
    ++ (encodeUInt 4 message.baseDate
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) message.instrumentName.val.length)
    ++ (encodeMany Byte.encode message.instrumentName.val)))))))))))))))))))))

def decode (bytes : List UInt8) : Option (IndexDirectoryMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (instrumentId, bytes) ← Alpha.decode 18 bytes
  let (disseminationFlag, bytes) ← DisseminationFlag.decode bytes
  let (financialProductType, bytes) ← FinancialProductType.decode bytes
  let (brand, bytes) ← Alpha.decode 2 bytes
  let (series, bytes) ← Alpha.decode 3 bytes
  let (strategy, bytes) ← Alpha.decode 3 bytes
  let (assetType, bytes) ← Alpha.decode 2 bytes
  let (marketCapSize, bytes) ← MarketCapSize.decode bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (geography, bytes) ← Alpha.decode 4 bytes
  let (indexSettlementType, bytes) ← IndexSettlementType.decode bytes
  let (indexCalculationMethod, bytes) ← Alpha.decode 3 bytes
  let (state, bytes) ← State.decode bytes
  let (indexUsage, bytes) ← IndexUsage.decode bytes
  let (schedule, bytes) ← Alpha.decode 3 bytes
  let (frequency, bytes) ← Alpha.decode 4 bytes
  let (numberOfIssueParticipationMessages, bytes) ← decodeUInt 4 bytes
  let (baseValue, bytes) ← decodeUInt 8 bytes
  let (baseDate, bytes) ← decodeUInt 4 bytes
  let (nameLength, bytes) ← decodeUInt 2 bytes
  let (instrumentName_, bytes) ← decodeMany Byte.decode nameLength.toNat bytes
  if fits_instrumentName : instrumentName_.length < 256 ^ 2 then
    pure ({ nanoseconds, instrumentId, disseminationFlag, financialProductType, brand, series, strategy, assetType, marketCapSize, currency, geography, indexSettlementType, indexCalculationMethod, state, indexUsage, schedule, frequency, numberOfIssueParticipationMessages, baseValue, baseDate, instrumentName := ⟨instrumentName_, fits_instrumentName⟩ }, bytes)
  else none

theorem encode_length_pos (message : IndexDirectoryMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : IndexDirectoryMessage) : (encode message).length ≤ 65608 := by
  have bound_instrumentName := message.instrumentName.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, DisseminationFlag.encode_length, FinancialProductType.encode_length, MarketCapSize.encode_length, IndexSettlementType.encode_length, State.encode_length, IndexUsage.encode_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

@[simp] theorem decode_encode (message : IndexDirectoryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DisseminationFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FinancialProductType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketCapSize.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, IndexSettlementType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, State.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, IndexUsage.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Byte.encode Byte.decode Byte.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.instrumentName.length_lt]
  rfl

end IndexDirectoryMessage

/-- Issue Symbol Participation Message -/
structure IssueSymbolParticipationMessage where
  nanoseconds : BitVec 32
  instrumentId : Alpha 18
  issueSymbol : Alpha 18
  issueMic : Alpha 4
  issueName : Bounded 2 UInt8
  deriving DecidableEq, Repr

namespace IssueSymbolParticipationMessage

def encode (message : IssueSymbolParticipationMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (Alpha.encode message.instrumentId
    ++ (Alpha.encode message.issueSymbol
    ++ (Alpha.encode message.issueMic
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) message.issueName.val.length)
    ++ (encodeMany Byte.encode message.issueName.val)))))

def decode (bytes : List UInt8) : Option (IssueSymbolParticipationMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (instrumentId, bytes) ← Alpha.decode 18 bytes
  let (issueSymbol, bytes) ← Alpha.decode 18 bytes
  let (issueMic, bytes) ← Alpha.decode 4 bytes
  let (nameLength, bytes) ← decodeUInt 2 bytes
  let (issueName_, bytes) ← decodeMany Byte.decode nameLength.toNat bytes
  if fits_issueName : issueName_.length < 256 ^ 2 then
    pure ({ nanoseconds, instrumentId, issueSymbol, issueMic, issueName := ⟨issueName_, fits_issueName⟩ }, bytes)
  else none

theorem encode_length_pos (message : IssueSymbolParticipationMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : IssueSymbolParticipationMessage) : (encode message).length ≤ 65581 := by
  have bound_issueName := message.issueName.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

@[simp] theorem decode_encode (message : IssueSymbolParticipationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Byte.encode Byte.decode Byte.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.issueName.length_lt]
  rfl

end IssueSymbolParticipationMessage

/-- Intraday Index Value Message: 40 bytes -/
structure IntradayIndexValueMessage where
  nanoseconds : BitVec 32
  financialProductType : FinancialProductType
  brand : Alpha 2
  series : Alpha 3
  instrumentId : Alpha 18
  tickValue : BitVec 64
  tickDirection : TickDirection
  currency : Alpha 3
  deriving DecidableEq, Repr

namespace IntradayIndexValueMessage

def encode (message : IntradayIndexValueMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (FinancialProductType.encode message.financialProductType
    ++ (Alpha.encode message.brand
    ++ (Alpha.encode message.series
    ++ (Alpha.encode message.instrumentId
    ++ (encodeUInt 8 message.tickValue
    ++ (TickDirection.encode message.tickDirection
    ++ (Alpha.encode message.currency)))))))

def decode (bytes : List UInt8) : Option (IntradayIndexValueMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (financialProductType, bytes) ← FinancialProductType.decode bytes
  let (brand, bytes) ← Alpha.decode 2 bytes
  let (series, bytes) ← Alpha.decode 3 bytes
  let (instrumentId, bytes) ← Alpha.decode 18 bytes
  let (tickValue, bytes) ← decodeUInt 8 bytes
  let (tickDirection, bytes) ← TickDirection.decode bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  pure ({ nanoseconds, financialProductType, brand, series, instrumentId, tickValue, tickDirection, currency }, bytes)

@[simp] theorem encode_length (message : IntradayIndexValueMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, FinancialProductType.encode_length, Alpha.encode_length, TickDirection.encode_length]

theorem encode_length_pos (message : IntradayIndexValueMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IntradayIndexValueMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, FinancialProductType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TickDirection.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end IntradayIndexValueMessage

/-- Settlement Value Message: 40 bytes -/
structure SettlementValueMessage where
  nanoseconds : BitVec 32
  financialProductType : FinancialProductType
  brand : Alpha 2
  series : Alpha 3
  instrumentId : Alpha 18
  settlementValue : BitVec 64
  settlementType : SettlementType
  currency : Alpha 3
  deriving DecidableEq, Repr

namespace SettlementValueMessage

def encode (message : SettlementValueMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (FinancialProductType.encode message.financialProductType
    ++ (Alpha.encode message.brand
    ++ (Alpha.encode message.series
    ++ (Alpha.encode message.instrumentId
    ++ (encodeUInt 8 message.settlementValue
    ++ (SettlementType.encode message.settlementType
    ++ (Alpha.encode message.currency)))))))

def decode (bytes : List UInt8) : Option (SettlementValueMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (financialProductType, bytes) ← FinancialProductType.decode bytes
  let (brand, bytes) ← Alpha.decode 2 bytes
  let (series, bytes) ← Alpha.decode 3 bytes
  let (instrumentId, bytes) ← Alpha.decode 18 bytes
  let (settlementValue, bytes) ← decodeUInt 8 bytes
  let (settlementType, bytes) ← SettlementType.decode bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  pure ({ nanoseconds, financialProductType, brand, series, instrumentId, settlementValue, settlementType, currency }, bytes)

@[simp] theorem encode_length (message : SettlementValueMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, FinancialProductType.encode_length, Alpha.encode_length, SettlementType.encode_length]

theorem encode_length_pos (message : SettlementValueMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SettlementValueMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, FinancialProductType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, SettlementType.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SettlementValueMessage

/-- Equities Summary Message: 78 bytes -/
structure EquitiesSummaryMessage where
  nanoseconds : BitVec 32
  financialProductType : FinancialProductType
  brand : Alpha 2
  series : Alpha 3
  instrumentId : Alpha 18
  summaryType : Alpha 3
  sodValue : BitVec 64
  high : BitVec 64
  low : BitVec 64
  eodValue : BitVec 64
  netChange : BitVec 64
  effectiveDate : BitVec 32
  currency : Alpha 3
  deriving DecidableEq, Repr

namespace EquitiesSummaryMessage

def encode (message : EquitiesSummaryMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (FinancialProductType.encode message.financialProductType
    ++ (Alpha.encode message.brand
    ++ (Alpha.encode message.series
    ++ (Alpha.encode message.instrumentId
    ++ (Alpha.encode message.summaryType
    ++ (encodeUInt 8 message.sodValue
    ++ (encodeUInt 8 message.high
    ++ (encodeUInt 8 message.low
    ++ (encodeUInt 8 message.eodValue
    ++ (encodeUInt 8 message.netChange
    ++ (encodeUInt 4 message.effectiveDate
    ++ (Alpha.encode message.currency))))))))))))

def decode (bytes : List UInt8) : Option (EquitiesSummaryMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (financialProductType, bytes) ← FinancialProductType.decode bytes
  let (brand, bytes) ← Alpha.decode 2 bytes
  let (series, bytes) ← Alpha.decode 3 bytes
  let (instrumentId, bytes) ← Alpha.decode 18 bytes
  let (summaryType, bytes) ← Alpha.decode 3 bytes
  let (sodValue, bytes) ← decodeUInt 8 bytes
  let (high, bytes) ← decodeUInt 8 bytes
  let (low, bytes) ← decodeUInt 8 bytes
  let (eodValue, bytes) ← decodeUInt 8 bytes
  let (netChange, bytes) ← decodeUInt 8 bytes
  let (effectiveDate, bytes) ← decodeUInt 4 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  pure ({ nanoseconds, financialProductType, brand, series, instrumentId, summaryType, sodValue, high, low, eodValue, netChange, effectiveDate, currency }, bytes)

@[simp] theorem encode_length (message : EquitiesSummaryMessage) : (encode message).length = 78 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, FinancialProductType.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : EquitiesSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EquitiesSummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, FinancialProductType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end EquitiesSummaryMessage

/-- Fixed Income Summary Message: 102 bytes -/
structure FixedIncomeSummaryMessage where
  nanoseconds : BitVec 32
  financialProductType : FinancialProductType
  brand : Alpha 2
  series : Alpha 3
  instrumentId : Alpha 18
  summaryType : Alpha 3
  sodValue : BitVec 64
  high : BitVec 64
  low : BitVec 64
  eodValue : BitVec 64
  netChange : BitVec 64
  effectiveDate : BitVec 32
  yield : BitVec 64
  duration : BitVec 64
  coupon : BitVec 64
  currency : Alpha 3
  deriving DecidableEq, Repr

namespace FixedIncomeSummaryMessage

def encode (message : FixedIncomeSummaryMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (FinancialProductType.encode message.financialProductType
    ++ (Alpha.encode message.brand
    ++ (Alpha.encode message.series
    ++ (Alpha.encode message.instrumentId
    ++ (Alpha.encode message.summaryType
    ++ (encodeUInt 8 message.sodValue
    ++ (encodeUInt 8 message.high
    ++ (encodeUInt 8 message.low
    ++ (encodeUInt 8 message.eodValue
    ++ (encodeUInt 8 message.netChange
    ++ (encodeUInt 4 message.effectiveDate
    ++ (encodeUInt 8 message.yield
    ++ (encodeUInt 8 message.duration
    ++ (encodeUInt 8 message.coupon
    ++ (Alpha.encode message.currency)))))))))))))))

def decode (bytes : List UInt8) : Option (FixedIncomeSummaryMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (financialProductType, bytes) ← FinancialProductType.decode bytes
  let (brand, bytes) ← Alpha.decode 2 bytes
  let (series, bytes) ← Alpha.decode 3 bytes
  let (instrumentId, bytes) ← Alpha.decode 18 bytes
  let (summaryType, bytes) ← Alpha.decode 3 bytes
  let (sodValue, bytes) ← decodeUInt 8 bytes
  let (high, bytes) ← decodeUInt 8 bytes
  let (low, bytes) ← decodeUInt 8 bytes
  let (eodValue, bytes) ← decodeUInt 8 bytes
  let (netChange, bytes) ← decodeUInt 8 bytes
  let (effectiveDate, bytes) ← decodeUInt 4 bytes
  let (yield, bytes) ← decodeUInt 8 bytes
  let (duration, bytes) ← decodeUInt 8 bytes
  let (coupon, bytes) ← decodeUInt 8 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  pure ({ nanoseconds, financialProductType, brand, series, instrumentId, summaryType, sodValue, high, low, eodValue, netChange, effectiveDate, yield, duration, coupon, currency }, bytes)

@[simp] theorem encode_length (message : FixedIncomeSummaryMessage) : (encode message).length = 102 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, FinancialProductType.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : FixedIncomeSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FixedIncomeSummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, FinancialProductType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end FixedIncomeSummaryMessage

/-- Commodity Summary Message: 78 bytes -/
structure CommoditySummaryMessage where
  nanoseconds : BitVec 32
  financialProductType : FinancialProductType
  brand : Alpha 2
  series : Alpha 3
  instrumentId : Alpha 18
  summaryType : Alpha 3
  sodValue : BitVec 64
  high : BitVec 64
  low : BitVec 64
  eodValue : BitVec 64
  netChange : BitVec 64
  effectiveDate : BitVec 32
  currency : Alpha 3
  deriving DecidableEq, Repr

namespace CommoditySummaryMessage

def encode (message : CommoditySummaryMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (FinancialProductType.encode message.financialProductType
    ++ (Alpha.encode message.brand
    ++ (Alpha.encode message.series
    ++ (Alpha.encode message.instrumentId
    ++ (Alpha.encode message.summaryType
    ++ (encodeUInt 8 message.sodValue
    ++ (encodeUInt 8 message.high
    ++ (encodeUInt 8 message.low
    ++ (encodeUInt 8 message.eodValue
    ++ (encodeUInt 8 message.netChange
    ++ (encodeUInt 4 message.effectiveDate
    ++ (Alpha.encode message.currency))))))))))))

def decode (bytes : List UInt8) : Option (CommoditySummaryMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (financialProductType, bytes) ← FinancialProductType.decode bytes
  let (brand, bytes) ← Alpha.decode 2 bytes
  let (series, bytes) ← Alpha.decode 3 bytes
  let (instrumentId, bytes) ← Alpha.decode 18 bytes
  let (summaryType, bytes) ← Alpha.decode 3 bytes
  let (sodValue, bytes) ← decodeUInt 8 bytes
  let (high, bytes) ← decodeUInt 8 bytes
  let (low, bytes) ← decodeUInt 8 bytes
  let (eodValue, bytes) ← decodeUInt 8 bytes
  let (netChange, bytes) ← decodeUInt 8 bytes
  let (effectiveDate, bytes) ← decodeUInt 4 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  pure ({ nanoseconds, financialProductType, brand, series, instrumentId, summaryType, sodValue, high, low, eodValue, netChange, effectiveDate, currency }, bytes)

@[simp] theorem encode_length (message : CommoditySummaryMessage) : (encode message).length = 78 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, FinancialProductType.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : CommoditySummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CommoditySummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, FinancialProductType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end CommoditySummaryMessage

/-- Etp Directory And Daily Valuation Message -/
structure EtpDirectoryAndDailyValuationMessage where
  nanoseconds : BitVec 32
  financialProductType : FinancialProductType
  industryMic : Alpha 4
  etpTradingSymbol : Alpha 18
  etpIpvSymbol : Alpha 18
  schedule : Alpha 3
  frequency : Alpha 4
  state : State
  navSymbol : Alpha 18
  nav : BitVec 64
  estimatedCashPerCuSymbol : Alpha 18
  ecu : BitVec 64
  totalCashPerCuSymbol : Alpha 18
  totalCashPerCu : BitVec 64
  estimatedCashPerShareSymbol : Alpha 18
  ecs : BitVec 64
  tsoSymbol : Alpha 18
  tsoOutstanding : BitVec 64
  effectiveDate : BitVec 32
  yield : BitVec 64
  coupon : BitVec 64
  maturityDate : BitVec 32
  currency : Alpha 3
  etpName : Bounded 2 UInt8
  deriving DecidableEq, Repr

namespace EtpDirectoryAndDailyValuationMessage

def encode (message : EtpDirectoryAndDailyValuationMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (FinancialProductType.encode message.financialProductType
    ++ (Alpha.encode message.industryMic
    ++ (Alpha.encode message.etpTradingSymbol
    ++ (Alpha.encode message.etpIpvSymbol
    ++ (Alpha.encode message.schedule
    ++ (Alpha.encode message.frequency
    ++ (State.encode message.state
    ++ (Alpha.encode message.navSymbol
    ++ (encodeUInt 8 message.nav
    ++ (Alpha.encode message.estimatedCashPerCuSymbol
    ++ (encodeUInt 8 message.ecu
    ++ (Alpha.encode message.totalCashPerCuSymbol
    ++ (encodeUInt 8 message.totalCashPerCu
    ++ (Alpha.encode message.estimatedCashPerShareSymbol
    ++ (encodeUInt 8 message.ecs
    ++ (Alpha.encode message.tsoSymbol
    ++ (encodeUInt 8 message.tsoOutstanding
    ++ (encodeUInt 4 message.effectiveDate
    ++ (encodeUInt 8 message.yield
    ++ (encodeUInt 8 message.coupon
    ++ (encodeUInt 4 message.maturityDate
    ++ (Alpha.encode message.currency
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) message.etpName.val.length)
    ++ (encodeMany Byte.encode message.etpName.val))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (EtpDirectoryAndDailyValuationMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (financialProductType, bytes) ← FinancialProductType.decode bytes
  let (industryMic, bytes) ← Alpha.decode 4 bytes
  let (etpTradingSymbol, bytes) ← Alpha.decode 18 bytes
  let (etpIpvSymbol, bytes) ← Alpha.decode 18 bytes
  let (schedule, bytes) ← Alpha.decode 3 bytes
  let (frequency, bytes) ← Alpha.decode 4 bytes
  let (state, bytes) ← State.decode bytes
  let (navSymbol, bytes) ← Alpha.decode 18 bytes
  let (nav, bytes) ← decodeUInt 8 bytes
  let (estimatedCashPerCuSymbol, bytes) ← Alpha.decode 18 bytes
  let (ecu, bytes) ← decodeUInt 8 bytes
  let (totalCashPerCuSymbol, bytes) ← Alpha.decode 18 bytes
  let (totalCashPerCu, bytes) ← decodeUInt 8 bytes
  let (estimatedCashPerShareSymbol, bytes) ← Alpha.decode 18 bytes
  let (ecs, bytes) ← decodeUInt 8 bytes
  let (tsoSymbol, bytes) ← Alpha.decode 18 bytes
  let (tsoOutstanding, bytes) ← decodeUInt 8 bytes
  let (effectiveDate, bytes) ← decodeUInt 4 bytes
  let (yield, bytes) ← decodeUInt 8 bytes
  let (coupon, bytes) ← decodeUInt 8 bytes
  let (maturityDate, bytes) ← decodeUInt 4 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (etpNameLength, bytes) ← decodeUInt 2 bytes
  let (etpName_, bytes) ← decodeMany Byte.decode etpNameLength.toNat bytes
  if fits_etpName : etpName_.length < 256 ^ 2 then
    pure ({ nanoseconds, financialProductType, industryMic, etpTradingSymbol, etpIpvSymbol, schedule, frequency, state, navSymbol, nav, estimatedCashPerCuSymbol, ecu, totalCashPerCuSymbol, totalCashPerCu, estimatedCashPerShareSymbol, ecs, tsoSymbol, tsoOutstanding, effectiveDate, yield, coupon, maturityDate, currency, etpName := ⟨etpName_, fits_etpName⟩ }, bytes)
  else none

theorem encode_length_pos (message : EtpDirectoryAndDailyValuationMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : EtpDirectoryAndDailyValuationMessage) : (encode message).length ≤ 65747 := by
  have bound_etpName := message.etpName.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, FinancialProductType.encode_length, Alpha.encode_length, State.encode_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : EtpDirectoryAndDailyValuationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, FinancialProductType.decode_encode, some_bind]
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
  rw [List.append_assoc, State.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Byte.encode Byte.decode Byte.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.etpName.length_lt]
  rfl

end EtpDirectoryAndDailyValuationMessage

/-- Etp Intra Day Valuation Message: 34 bytes -/
structure EtpIntraDayValuationMessage where
  nanoseconds : BitVec 32
  financialProductType : FinancialProductType
  ipvSymbol : Alpha 18
  ipvValue : BitVec 64
  currency : Alpha 3
  deriving DecidableEq, Repr

namespace EtpIntraDayValuationMessage

def encode (message : EtpIntraDayValuationMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (FinancialProductType.encode message.financialProductType
    ++ (Alpha.encode message.ipvSymbol
    ++ (encodeUInt 8 message.ipvValue
    ++ (Alpha.encode message.currency))))

def decode (bytes : List UInt8) : Option (EtpIntraDayValuationMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (financialProductType, bytes) ← FinancialProductType.decode bytes
  let (ipvSymbol, bytes) ← Alpha.decode 18 bytes
  let (ipvValue, bytes) ← decodeUInt 8 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  pure ({ nanoseconds, financialProductType, ipvSymbol, ipvValue, currency }, bytes)

@[simp] theorem encode_length (message : EtpIntraDayValuationMessage) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, FinancialProductType.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : EtpIntraDayValuationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EtpIntraDayValuationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, FinancialProductType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end EtpIntraDayValuationMessage

/-- Etp Summary Message: 73 bytes -/
structure EtpSummaryMessage where
  nanoseconds : BitVec 32
  financialProductType : FinancialProductType
  summaryType : Alpha 3
  ipvOrIivSymbol : Alpha 18
  sodValue : BitVec 64
  high : BitVec 64
  low : BitVec 64
  eodValue : BitVec 64
  netChange : BitVec 64
  effectiveDate : BitVec 32
  currency : Alpha 3
  deriving DecidableEq, Repr

namespace EtpSummaryMessage

def encode (message : EtpSummaryMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (FinancialProductType.encode message.financialProductType
    ++ (Alpha.encode message.summaryType
    ++ (Alpha.encode message.ipvOrIivSymbol
    ++ (encodeUInt 8 message.sodValue
    ++ (encodeUInt 8 message.high
    ++ (encodeUInt 8 message.low
    ++ (encodeUInt 8 message.eodValue
    ++ (encodeUInt 8 message.netChange
    ++ (encodeUInt 4 message.effectiveDate
    ++ (Alpha.encode message.currency))))))))))

def decode (bytes : List UInt8) : Option (EtpSummaryMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (financialProductType, bytes) ← FinancialProductType.decode bytes
  let (summaryType, bytes) ← Alpha.decode 3 bytes
  let (ipvOrIivSymbol, bytes) ← Alpha.decode 18 bytes
  let (sodValue, bytes) ← decodeUInt 8 bytes
  let (high, bytes) ← decodeUInt 8 bytes
  let (low, bytes) ← decodeUInt 8 bytes
  let (eodValue, bytes) ← decodeUInt 8 bytes
  let (netChange, bytes) ← decodeUInt 8 bytes
  let (effectiveDate, bytes) ← decodeUInt 4 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  pure ({ nanoseconds, financialProductType, summaryType, ipvOrIivSymbol, sodValue, high, low, eodValue, netChange, effectiveDate, currency }, bytes)

@[simp] theorem encode_length (message : EtpSummaryMessage) : (encode message).length = 73 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, FinancialProductType.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : EtpSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EtpSummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, FinancialProductType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end EtpSummaryMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | timestampSecondsMessage (message : TimestampSecondsMessage) -- "T" 0x54
  | systemEventMessage (message : SystemEventMessage) -- "S" 0x53
  | indexDirectoryMessage (message : IndexDirectoryMessage) -- "R" 0x52
  | issueSymbolParticipationMessage (message : IssueSymbolParticipationMessage) -- "P" 0x50
  | intradayIndexValueMessage (message : IntradayIndexValueMessage) -- "I" 0x49
  | settlementValueMessage (message : SettlementValueMessage) -- "A" 0x41
  | equitiesSummaryMessage (message : EquitiesSummaryMessage) -- "F" 0x46
  | fixedIncomeSummaryMessage (message : FixedIncomeSummaryMessage) -- "B" 0x42
  | commoditySummaryMessage (message : CommoditySummaryMessage) -- "C" 0x43
  | etpDirectoryAndDailyValuationMessage (message : EtpDirectoryAndDailyValuationMessage) -- "D" 0x44
  | etpIntraDayValuationMessage (message : EtpIntraDayValuationMessage) -- "E" 0x45
  | etpSummaryMessage (message : EtpSummaryMessage) -- "V" 0x56
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .timestampSecondsMessage _ => 84
  | .systemEventMessage _ => 83
  | .indexDirectoryMessage _ => 82
  | .issueSymbolParticipationMessage _ => 80
  | .intradayIndexValueMessage _ => 73
  | .settlementValueMessage _ => 65
  | .equitiesSummaryMessage _ => 70
  | .fixedIncomeSummaryMessage _ => 66
  | .commoditySummaryMessage _ => 67
  | .etpDirectoryAndDailyValuationMessage _ => 68
  | .etpIntraDayValuationMessage _ => 69
  | .etpSummaryMessage _ => 86

def encode : Payload → List UInt8
  | .timestampSecondsMessage message => TimestampSecondsMessage.encode message
  | .systemEventMessage message => SystemEventMessage.encode message
  | .indexDirectoryMessage message => IndexDirectoryMessage.encode message
  | .issueSymbolParticipationMessage message => IssueSymbolParticipationMessage.encode message
  | .intradayIndexValueMessage message => IntradayIndexValueMessage.encode message
  | .settlementValueMessage message => SettlementValueMessage.encode message
  | .equitiesSummaryMessage message => EquitiesSummaryMessage.encode message
  | .fixedIncomeSummaryMessage message => FixedIncomeSummaryMessage.encode message
  | .commoditySummaryMessage message => CommoditySummaryMessage.encode message
  | .etpDirectoryAndDailyValuationMessage message => EtpDirectoryAndDailyValuationMessage.encode message
  | .etpIntraDayValuationMessage message => EtpIntraDayValuationMessage.encode message
  | .etpSummaryMessage message => EtpSummaryMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 65747 := by
  cases message with
  | timestampSecondsMessage inner =>
    simp only [encode, TimestampSecondsMessage.encode_length]
    omega
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega
  | indexDirectoryMessage inner =>
    have bound_inner := IndexDirectoryMessage.encode_length_le inner
    simp only [encode]
    omega
  | issueSymbolParticipationMessage inner =>
    have bound_inner := IssueSymbolParticipationMessage.encode_length_le inner
    simp only [encode]
    omega
  | intradayIndexValueMessage inner =>
    simp only [encode, IntradayIndexValueMessage.encode_length]
    omega
  | settlementValueMessage inner =>
    simp only [encode, SettlementValueMessage.encode_length]
    omega
  | equitiesSummaryMessage inner =>
    simp only [encode, EquitiesSummaryMessage.encode_length]
    omega
  | fixedIncomeSummaryMessage inner =>
    simp only [encode, FixedIncomeSummaryMessage.encode_length]
    omega
  | commoditySummaryMessage inner =>
    simp only [encode, CommoditySummaryMessage.encode_length]
    omega
  | etpDirectoryAndDailyValuationMessage inner =>
    have bound_inner := EtpDirectoryAndDailyValuationMessage.encode_length_le inner
    simp only [encode]
    omega
  | etpIntraDayValuationMessage inner =>
    simp only [encode, EtpIntraDayValuationMessage.encode_length]
    omega
  | etpSummaryMessage inner =>
    simp only [encode, EtpSummaryMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 84 then (TimestampSecondsMessage.decode bytes).map fun (message, rest) => (.timestampSecondsMessage message, rest)
  else if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 82 then (IndexDirectoryMessage.decode bytes).map fun (message, rest) => (.indexDirectoryMessage message, rest)
  else if tag = 80 then (IssueSymbolParticipationMessage.decode bytes).map fun (message, rest) => (.issueSymbolParticipationMessage message, rest)
  else if tag = 73 then (IntradayIndexValueMessage.decode bytes).map fun (message, rest) => (.intradayIndexValueMessage message, rest)
  else if tag = 65 then (SettlementValueMessage.decode bytes).map fun (message, rest) => (.settlementValueMessage message, rest)
  else if tag = 70 then (EquitiesSummaryMessage.decode bytes).map fun (message, rest) => (.equitiesSummaryMessage message, rest)
  else if tag = 66 then (FixedIncomeSummaryMessage.decode bytes).map fun (message, rest) => (.fixedIncomeSummaryMessage message, rest)
  else if tag = 67 then (CommoditySummaryMessage.decode bytes).map fun (message, rest) => (.commoditySummaryMessage message, rest)
  else if tag = 68 then (EtpDirectoryAndDailyValuationMessage.decode bytes).map fun (message, rest) => (.etpDirectoryAndDailyValuationMessage message, rest)
  else if tag = 69 then (EtpIntraDayValuationMessage.decode bytes).map fun (message, rest) => (.etpIntraDayValuationMessage message, rest)
  else if tag = 86 then (EtpSummaryMessage.decode bytes).map fun (message, rest) => (.etpSummaryMessage message, rest)
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
  encodeUInt 1 (Payload.tag message.payload)
    ++ (Payload.encode message.payload)

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (payload, bytes) ← Payload.decode messageType bytes
  pure ({ payload }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Size rule: Message Length counts the bytes after it, so it is written from the body; the body has no bound the prefix must fit, so it is read by its content and the prefix is not checked -/
def encode (message : Message) : List UInt8 :=
  encodeUInt 2 (BitVec.ofNat (8 * 2) ((encodeBody message).length + 0)) ++ encodeBody message

def decode (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (_, bytes) ← decodeUInt 2 bytes
  decodeBody bytes

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  exact decodeBody_encodeBody message rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]
  omega

end Message

/-- Packet -/
structure Packet where
  session : Alpha 10
  sequenceNumber : BitVec 64
  message : Bounded 2 Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  Alpha.encode message.session
    ++ (encodeUInt 8 message.sequenceNumber
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) message.message.val.length)
    ++ (encodeMany Message.encode message.message.val)))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (session, bytes) ← Alpha.decode 10 bytes
  let (sequenceNumber, bytes) ← decodeUInt 8 bytes
  let (messageCount, bytes) ← decodeUInt 2 bytes
  let (message_, bytes) ← decodeMany Message.decode messageCount.toNat bytes
  if fits_message : message_.length < 256 ^ 2 then
    pure ({ session, sequenceNumber, message := ⟨message_, fits_message⟩ }, bytes)
  else none

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt]
  rfl

end Packet

end Omi.NasdaqIndexGidsItchV10I
