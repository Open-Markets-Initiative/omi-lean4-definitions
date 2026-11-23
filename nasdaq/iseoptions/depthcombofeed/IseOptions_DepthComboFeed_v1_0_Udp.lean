import Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Ise Depth Combo Market Data Feed v1.0

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

Note: Price is present when Update Action Equals N Or Update Action Equals C: it is carried with the
proof that it is there exactly when that holds, and read exactly when it does

Note: Size is present when Update Action Equals N Or Update Action Equals C: it is carried with the
proof that it is there exactly when that holds, and read exactly when it does

Note: Cust Size is present when Update Action Equals N Or Update Action Equals C: it is carried with
the proof that it is there exactly when that holds, and read exactly when it does

Note: Pro Cust Size is present when Update Action Equals N Or Update Action Equals C: it is carried
with the proof that it is there exactly when that holds, and read exactly when it does

Note: Ntt Size is present when Update Action Equals N Or Update Action Equals C: it is carried with
the proof that it is there exactly when that holds, and read exactly when it does

Note: Message's Message Length is written from its body but not checked on decode, since the body
has no bound the prefix must fit; the body is read by its content

License: MIT No Attribution
-/

namespace Omi.NasdaqIseoptionsDepthcombofeedItchV10Udp

/-- Event Code: one byte code -/
def EventCode.codes : List UInt8 :=
  [0x4F, 0x53, 0x51, 0x4E, 0x4C, 0x45, 0x43, 0x57]

inductive EventCode where
  | startOfMessages -- Start Of Messages
  | startOfSystemHours -- Start Of System Hours
  | startOfOpeningProcess -- Start Of Opening Process
  | startOfNormalHoursClosingProcess -- Start Of Normal Hours Closing Process
  | startOfLateHoursClosingProcess -- Start Of Late Hours Closing Process
  | endOfSystemHours -- End Of System Hours
  | endOfMessages -- End Of Messages
  | endOfWcoEarlyClosing -- End Of Wco Early Closing
  | unlisted (byte : { byte : UInt8 // byte ∉ EventCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventCode

def toByte : EventCode → UInt8
  | .startOfMessages => 0x4F
  | .startOfSystemHours => 0x53
  | .startOfOpeningProcess => 0x51
  | .startOfNormalHoursClosingProcess => 0x4E
  | .startOfLateHoursClosingProcess => 0x4C
  | .endOfSystemHours => 0x45
  | .endOfMessages => 0x43
  | .endOfWcoEarlyClosing => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventCode :=
  if byte = 0x4F then .startOfMessages
  else if byte = 0x53 then .startOfSystemHours
  else if byte = 0x51 then .startOfOpeningProcess
  else if byte = 0x4E then .startOfNormalHoursClosingProcess
  else if byte = 0x4C then .startOfLateHoursClosingProcess
  else if byte = 0x45 then .endOfSystemHours
  else if byte = 0x43 then .endOfMessages
  else .endOfWcoEarlyClosing

def ofByte (byte : UInt8) : EventCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventCode) : ofByte value.toByte = value := by
  cases value with
  | startOfMessages => decide
  | startOfSystemHours => decide
  | startOfOpeningProcess => decide
  | startOfNormalHoursClosingProcess => decide
  | startOfLateHoursClosingProcess => decide
  | endOfSystemHours => decide
  | endOfMessages => decide
  | endOfWcoEarlyClosing => decide
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

/-- Strategy Type: one byte code -/
def StrategyType.codes : List UInt8 :=
  [0x56, 0x54, 0x44, 0x53, 0x47, 0x43, 0x52, 0x41, 0x55]

inductive StrategyType where
  | verticalSpread -- Vertical Spread
  | timeSpread -- Time Spread
  | diagonalSpread -- Diagonal Spread
  | straddle -- Straddle
  | strangle -- Strangle
  | combo -- Combo
  | riskReversal -- Risk Reversal
  | ratioSpread -- Ratio Spread
  | custom -- Custom
  | unlisted (byte : { byte : UInt8 // byte ∉ StrategyType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace StrategyType

def toByte : StrategyType → UInt8
  | .verticalSpread => 0x56
  | .timeSpread => 0x54
  | .diagonalSpread => 0x44
  | .straddle => 0x53
  | .strangle => 0x47
  | .combo => 0x43
  | .riskReversal => 0x52
  | .ratioSpread => 0x41
  | .custom => 0x55
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : StrategyType :=
  if byte = 0x56 then .verticalSpread
  else if byte = 0x54 then .timeSpread
  else if byte = 0x44 then .diagonalSpread
  else if byte = 0x53 then .straddle
  else if byte = 0x47 then .strangle
  else if byte = 0x43 then .combo
  else if byte = 0x52 then .riskReversal
  else if byte = 0x41 then .ratioSpread
  else .custom

def ofByte (byte : UInt8) : StrategyType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : StrategyType) : ofByte value.toByte = value := by
  cases value with
  | verticalSpread => decide
  | timeSpread => decide
  | diagonalSpread => decide
  | straddle => decide
  | strangle => decide
  | combo => decide
  | riskReversal => decide
  | ratioSpread => decide
  | custom => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : StrategyType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (StrategyType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : StrategyType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : StrategyType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : StrategyType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end StrategyType

/-- Option Type: one byte code -/
def OptionType.codes : List UInt8 :=
  [0x43, 0x50, 0x20]

inductive OptionType where
  | call -- Call
  | put -- Put
  | na -- Na
  | unlisted (byte : { byte : UInt8 // byte ∉ OptionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OptionType

def toByte : OptionType → UInt8
  | .call => 0x43
  | .put => 0x50
  | .na => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OptionType :=
  if byte = 0x43 then .call
  else if byte = 0x50 then .put
  else .na

def ofByte (byte : UInt8) : OptionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OptionType) : ofByte value.toByte = value := by
  cases value with
  | call => decide
  | put => decide
  | na => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OptionType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OptionType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OptionType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OptionType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OptionType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OptionType

/-- Side: one byte code -/
def Side.codes : List UInt8 :=
  [0x42, 0x53]

inductive Side where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x42 then .buy
  else .sell

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Side) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Side × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Side) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Side) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Side) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Side

/-- Current Trading State: one byte code -/
def CurrentTradingState.codes : List UInt8 :=
  [0x48, 0x54]

inductive CurrentTradingState where
  | haltInEffect -- Halt In Effect
  | trading -- Trading
  | unlisted (byte : { byte : UInt8 // byte ∉ CurrentTradingState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CurrentTradingState

def toByte : CurrentTradingState → UInt8
  | .haltInEffect => 0x48
  | .trading => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CurrentTradingState :=
  if byte = 0x48 then .haltInEffect
  else .trading

def ofByte (byte : UInt8) : CurrentTradingState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CurrentTradingState) : ofByte value.toByte = value := by
  cases value with
  | haltInEffect => decide
  | trading => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CurrentTradingState) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CurrentTradingState × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CurrentTradingState) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CurrentTradingState) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CurrentTradingState) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CurrentTradingState

/-- Open State: one byte code -/
def OpenState.codes : List UInt8 :=
  [0x59, 0x4E]

inductive OpenState where
  | open_ -- Open
  | closed -- Closed
  | unlisted (byte : { byte : UInt8 // byte ∉ OpenState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OpenState

def toByte : OpenState → UInt8
  | .open_ => 0x59
  | .closed => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OpenState :=
  if byte = 0x59 then .open_
  else .closed

def ofByte (byte : UInt8) : OpenState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OpenState) : ofByte value.toByte = value := by
  cases value with
  | open_ => decide
  | closed => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OpenState) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OpenState × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OpenState) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OpenState) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OpenState) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OpenState

/-- Quote Condition: one byte code -/
def QuoteCondition.codes : List UInt8 :=
  [0x20, 0x58]

inductive QuoteCondition where
  | regularQuote -- Regular Quote
  | halted -- Halted
  | unlisted (byte : { byte : UInt8 // byte ∉ QuoteCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace QuoteCondition

def toByte : QuoteCondition → UInt8
  | .regularQuote => 0x20
  | .halted => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : QuoteCondition :=
  if byte = 0x20 then .regularQuote
  else .halted

def ofByte (byte : UInt8) : QuoteCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : QuoteCondition) : ofByte value.toByte = value := by
  cases value with
  | regularQuote => decide
  | halted => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : QuoteCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (QuoteCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : QuoteCondition) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : QuoteCondition) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : QuoteCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end QuoteCondition

/-- Update Action: one byte code -/
def UpdateAction.codes : List UInt8 :=
  [0x4E, 0x43, 0x44, 0x46]

inductive UpdateAction where
  | new -- New
  | change -- Change
  | delete -- Delete
  | deleteFrom -- Delete From
  | unlisted (byte : { byte : UInt8 // byte ∉ UpdateAction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace UpdateAction

def toByte : UpdateAction → UInt8
  | .new => 0x4E
  | .change => 0x43
  | .delete => 0x44
  | .deleteFrom => 0x46
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : UpdateAction :=
  if byte = 0x4E then .new
  else if byte = 0x43 then .change
  else if byte = 0x44 then .delete
  else .deleteFrom

def ofByte (byte : UInt8) : UpdateAction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : UpdateAction) : ofByte value.toByte = value := by
  cases value with
  | new => decide
  | change => decide
  | delete => decide
  | deleteFrom => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : UpdateAction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (UpdateAction × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : UpdateAction) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : UpdateAction) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : UpdateAction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end UpdateAction

/-- Depth Side: one byte code -/
def DepthSide.codes : List UInt8 :=
  [0x42, 0x41]

inductive DepthSide where
  | bid -- Bid
  | ask -- Ask
  | unlisted (byte : { byte : UInt8 // byte ∉ DepthSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DepthSide

def toByte : DepthSide → UInt8
  | .bid => 0x42
  | .ask => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DepthSide :=
  if byte = 0x42 then .bid
  else .ask

def ofByte (byte : UInt8) : DepthSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DepthSide) : ofByte value.toByte = value := by
  cases value with
  | bid => decide
  | ask => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DepthSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DepthSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DepthSide) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : DepthSide) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : DepthSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DepthSide

/-- System Event Message: 13 bytes -/
structure SystemEventMessage where
  timestamp : BitVec 48
  eventCode : EventCode
  currentYear : BitVec 16
  currentMonth : BitVec 8
  currentDay : BitVec 8
  version : BitVec 8
  subVersion : BitVec 8
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  encodeUInt 6 message.timestamp
    ++ (EventCode.encode message.eventCode
    ++ (encodeUInt 2 message.currentYear
    ++ (encodeUInt 1 message.currentMonth
    ++ (encodeUInt 1 message.currentDay
    ++ (encodeUInt 1 message.version
    ++ (encodeUInt 1 message.subVersion))))))

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (eventCode, bytes) ← EventCode.decode bytes
  let (currentYear, bytes) ← decodeUInt 2 bytes
  let (currentMonth, bytes) ← decodeUInt 1 bytes
  let (currentDay, bytes) ← decodeUInt 1 bytes
  let (version, bytes) ← decodeUInt 1 bytes
  let (subVersion, bytes) ← decodeUInt 1 bytes
  pure ({ timestamp, eventCode, currentYear, currentMonth, currentDay, version, subVersion }, bytes)

@[simp] theorem encode_length (message : SystemEventMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, EventCode.encode_length]

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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SystemEventMessage

/-- Leg Information: 28 bytes -/
structure LegInformation where
  optionId : BitVec 32
  securitySymbol : Alpha 6
  legId : BitVec 8
  expirationYear : BitVec 8
  expirationMonth : BitVec 8
  expirationDay : BitVec 8
  explicitStrikePrice : BitVec 64
  optionType : OptionType
  side : Side
  legRatio : BitVec 32
  deriving DecidableEq, Repr

namespace LegInformation

def encode (message : LegInformation) : List UInt8 :=
  encodeUInt 4 message.optionId
    ++ (Alpha.encode message.securitySymbol
    ++ (encodeUInt 1 message.legId
    ++ (encodeUInt 1 message.expirationYear
    ++ (encodeUInt 1 message.expirationMonth
    ++ (encodeUInt 1 message.expirationDay
    ++ (encodeUInt 8 message.explicitStrikePrice
    ++ (OptionType.encode message.optionType
    ++ (Side.encode message.side
    ++ (encodeUInt 4 message.legRatio)))))))))

def decode (bytes : List UInt8) : Option (LegInformation × List UInt8) := do
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (securitySymbol, bytes) ← Alpha.decode 6 bytes
  let (legId, bytes) ← decodeUInt 1 bytes
  let (expirationYear, bytes) ← decodeUInt 1 bytes
  let (expirationMonth, bytes) ← decodeUInt 1 bytes
  let (expirationDay, bytes) ← decodeUInt 1 bytes
  let (explicitStrikePrice, bytes) ← decodeUInt 8 bytes
  let (optionType, bytes) ← OptionType.decode bytes
  let (side, bytes) ← Side.decode bytes
  let (legRatio, bytes) ← decodeUInt 4 bytes
  pure ({ optionId, securitySymbol, legId, expirationYear, expirationMonth, expirationDay, explicitStrikePrice, optionType, side, legRatio }, bytes)

@[simp] theorem encode_length (message : LegInformation) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, OptionType.encode_length, Side.encode_length]

theorem encode_length_pos (message : LegInformation) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LegInformation) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, OptionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end LegInformation

/-- Complex Strategy Directory Message -/
structure ComplexStrategyDirectoryMessage where
  timestamp : BitVec 48
  strategyId : BitVec 32
  strategyType : StrategyType
  source : BitVec 8
  underlyingSymbol : Alpha 13
  legInformation : Bounded 1 LegInformation
  deriving DecidableEq, Repr

namespace ComplexStrategyDirectoryMessage

def encode (message : ComplexStrategyDirectoryMessage) : List UInt8 :=
  encodeUInt 6 message.timestamp
    ++ (encodeUInt 4 message.strategyId
    ++ (StrategyType.encode message.strategyType
    ++ (encodeUInt 1 message.source
    ++ (Alpha.encode message.underlyingSymbol
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.legInformation.val.length)
    ++ (encodeMany LegInformation.encode message.legInformation.val))))))

def decode (bytes : List UInt8) : Option (ComplexStrategyDirectoryMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (strategyId, bytes) ← decodeUInt 4 bytes
  let (strategyType, bytes) ← StrategyType.decode bytes
  let (source, bytes) ← decodeUInt 1 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 13 bytes
  let (numberOfLegs, bytes) ← decodeUInt 1 bytes
  let (legInformation_, bytes) ← decodeMany LegInformation.decode numberOfLegs.toNat bytes
  if fits_legInformation : legInformation_.length < 256 ^ 1 then
    pure ({ timestamp, strategyId, strategyType, source, underlyingSymbol, legInformation := ⟨legInformation_, fits_legInformation⟩ }, bytes)
  else none

theorem encode_length_pos (message : ComplexStrategyDirectoryMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ComplexStrategyDirectoryMessage) : (encode message).length ≤ 7166 := by
  have bound_legInformation := message.legInformation.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, StrategyType.encode_length, Alpha.encode_length, encodeMany_length_const LegInformation.encode 28 LegInformation.encode_length]
  omega

@[simp] theorem decode_encode (message : ComplexStrategyDirectoryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, StrategyType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 LegInformation.encode LegInformation.decode LegInformation.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.legInformation.length_lt]
  rfl

end ComplexStrategyDirectoryMessage

/-- Strategy Trading Action Message: 11 bytes -/
structure StrategyTradingActionMessage where
  timestamp : BitVec 48
  strategyId : BitVec 32
  currentTradingState : CurrentTradingState
  deriving DecidableEq, Repr

namespace StrategyTradingActionMessage

def encode (message : StrategyTradingActionMessage) : List UInt8 :=
  encodeUInt 6 message.timestamp
    ++ (encodeUInt 4 message.strategyId
    ++ (CurrentTradingState.encode message.currentTradingState))

def decode (bytes : List UInt8) : Option (StrategyTradingActionMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (strategyId, bytes) ← decodeUInt 4 bytes
  let (currentTradingState, bytes) ← CurrentTradingState.decode bytes
  pure ({ timestamp, strategyId, currentTradingState }, bytes)

@[simp] theorem encode_length (message : StrategyTradingActionMessage) : (encode message).length = 11 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, CurrentTradingState.encode_length]

theorem encode_length_pos (message : StrategyTradingActionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyTradingActionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [CurrentTradingState.decode_encode, some_bind]
  rfl

end StrategyTradingActionMessage

/-- Strategy Open Closed Message: 11 bytes -/
structure StrategyOpenClosedMessage where
  timestamp : BitVec 48
  strategyId : BitVec 32
  openState : OpenState
  deriving DecidableEq, Repr

namespace StrategyOpenClosedMessage

def encode (message : StrategyOpenClosedMessage) : List UInt8 :=
  encodeUInt 6 message.timestamp
    ++ (encodeUInt 4 message.strategyId
    ++ (OpenState.encode message.openState))

def decode (bytes : List UInt8) : Option (StrategyOpenClosedMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (strategyId, bytes) ← decodeUInt 4 bytes
  let (openState, bytes) ← OpenState.decode bytes
  pure ({ timestamp, strategyId, openState }, bytes)

@[simp] theorem encode_length (message : StrategyOpenClosedMessage) : (encode message).length = 11 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, OpenState.encode_length]

theorem encode_length_pos (message : StrategyOpenClosedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyOpenClosedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [OpenState.decode_encode, some_bind]
  rfl

end StrategyOpenClosedMessage

/-- Depth Incrementals -/
structure DepthIncrementals where
  updateAction : UpdateAction
  depthSide : DepthSide
  level : BitVec 8
  price : When (decide (updateAction = UpdateAction.new) || decide (updateAction = UpdateAction.change)) (BitVec 32)
  size : When (decide (updateAction = UpdateAction.new) || decide (updateAction = UpdateAction.change)) (BitVec 32)
  custSize : When (decide (updateAction = UpdateAction.new) || decide (updateAction = UpdateAction.change)) (BitVec 32)
  proCustSize : When (decide (updateAction = UpdateAction.new) || decide (updateAction = UpdateAction.change)) (BitVec 32)
  nttSize : When (decide (updateAction = UpdateAction.new) || decide (updateAction = UpdateAction.change)) (BitVec 32)
  deriving DecidableEq, Repr

namespace DepthIncrementals

def encode (message : DepthIncrementals) : List UInt8 :=
  UpdateAction.encode message.updateAction
    ++ (DepthSide.encode message.depthSide
    ++ (encodeUInt 1 message.level
    ++ (encodeWhen (encodeUInt 4) message.price
    ++ (encodeWhen (encodeUInt 4) message.size
    ++ (encodeWhen (encodeUInt 4) message.custSize
    ++ (encodeWhen (encodeUInt 4) message.proCustSize
    ++ (encodeWhen (encodeUInt 4) message.nttSize)))))))

def decode (bytes : List UInt8) : Option (DepthIncrementals × List UInt8) := do
  let (updateAction, bytes) ← UpdateAction.decode bytes
  let (depthSide, bytes) ← DepthSide.decode bytes
  let (level, bytes) ← decodeUInt 1 bytes
  let (price, bytes) ← decodeWhen (decodeUInt 4) (decide (updateAction = UpdateAction.new) || decide (updateAction = UpdateAction.change)) bytes
  let (size, bytes) ← decodeWhen (decodeUInt 4) (decide (updateAction = UpdateAction.new) || decide (updateAction = UpdateAction.change)) bytes
  let (custSize, bytes) ← decodeWhen (decodeUInt 4) (decide (updateAction = UpdateAction.new) || decide (updateAction = UpdateAction.change)) bytes
  let (proCustSize, bytes) ← decodeWhen (decodeUInt 4) (decide (updateAction = UpdateAction.new) || decide (updateAction = UpdateAction.change)) bytes
  let (nttSize, bytes) ← decodeWhen (decodeUInt 4) (decide (updateAction = UpdateAction.new) || decide (updateAction = UpdateAction.change)) bytes
  pure ({ updateAction, depthSide, level, price, size, custSize, proCustSize, nttSize }, bytes)

theorem encode_length_pos (message : DepthIncrementals) : (encode message).length > 0 := by
  unfold encode
  simp only [UpdateAction.encode_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : DepthIncrementals) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, UpdateAction.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DepthSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeWhen_encodeWhen (encodeUInt 4) (decodeUInt 4) (decodeUInt_encodeUInt 4) _, some_bind]
  dsimp only
  rw [List.append_assoc, decodeWhen_encodeWhen (encodeUInt 4) (decodeUInt 4) (decodeUInt_encodeUInt 4) _, some_bind]
  dsimp only
  rw [List.append_assoc, decodeWhen_encodeWhen (encodeUInt 4) (decodeUInt 4) (decodeUInt_encodeUInt 4) _, some_bind]
  dsimp only
  rw [List.append_assoc, decodeWhen_encodeWhen (encodeUInt 4) (decodeUInt 4) (decodeUInt_encodeUInt 4) _, some_bind]
  dsimp only
  rw [decodeWhen_encodeWhen (encodeUInt 4) (decodeUInt 4) (decodeUInt_encodeUInt 4) _, some_bind]
  rfl

end DepthIncrementals

/-- Strategy Depth Incremental Message -/
structure StrategyDepthIncrementalMessage where
  timestamp : BitVec 48
  strategyId : BitVec 32
  quoteCondition : QuoteCondition
  bidMarketSize : BitVec 32
  askMarketSize : BitVec 32
  bidNttMarketSize : BitVec 32
  askNttMarketSize : BitVec 32
  depthIncrementals : Bounded 1 DepthIncrementals
  deriving DecidableEq, Repr

namespace StrategyDepthIncrementalMessage

def encode (message : StrategyDepthIncrementalMessage) : List UInt8 :=
  encodeUInt 6 message.timestamp
    ++ (encodeUInt 4 message.strategyId
    ++ (QuoteCondition.encode message.quoteCondition
    ++ (encodeUInt 4 message.bidMarketSize
    ++ (encodeUInt 4 message.askMarketSize
    ++ (encodeUInt 4 message.bidNttMarketSize
    ++ (encodeUInt 4 message.askNttMarketSize
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.depthIncrementals.val.length)
    ++ (encodeMany DepthIncrementals.encode message.depthIncrementals.val))))))))

def decode (bytes : List UInt8) : Option (StrategyDepthIncrementalMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (strategyId, bytes) ← decodeUInt 4 bytes
  let (quoteCondition, bytes) ← QuoteCondition.decode bytes
  let (bidMarketSize, bytes) ← decodeUInt 4 bytes
  let (askMarketSize, bytes) ← decodeUInt 4 bytes
  let (bidNttMarketSize, bytes) ← decodeUInt 4 bytes
  let (askNttMarketSize, bytes) ← decodeUInt 4 bytes
  let (numberOfDepthIncrementals, bytes) ← decodeUInt 1 bytes
  let (depthIncrementals_, bytes) ← decodeMany DepthIncrementals.decode numberOfDepthIncrementals.toNat bytes
  if fits_depthIncrementals : depthIncrementals_.length < 256 ^ 1 then
    pure ({ timestamp, strategyId, quoteCondition, bidMarketSize, askMarketSize, bidNttMarketSize, askNttMarketSize, depthIncrementals := ⟨depthIncrementals_, fits_depthIncrementals⟩ }, bytes)
  else none

theorem encode_length_pos (message : StrategyDepthIncrementalMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : StrategyDepthIncrementalMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, QuoteCondition.decode_encode, some_bind]
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
  rw [decodeMany_bounded 1 DepthIncrementals.encode DepthIncrementals.decode DepthIncrementals.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.depthIncrementals.length_lt]
  rfl

end StrategyDepthIncrementalMessage

/-- Complex Strategy Ticker Message: 51 bytes -/
structure ComplexStrategyTickerMessage where
  timestamp : BitVec 48
  strategyId : BitVec 32
  lastPrice : BitVec 64
  size : BitVec 32
  volume : BitVec 32
  high : BitVec 64
  low : BitVec 64
  first : BitVec 64
  tradeCondition : Alpha 1
  deriving DecidableEq, Repr

namespace ComplexStrategyTickerMessage

def encode (message : ComplexStrategyTickerMessage) : List UInt8 :=
  encodeUInt 6 message.timestamp
    ++ (encodeUInt 4 message.strategyId
    ++ (encodeUInt 8 message.lastPrice
    ++ (encodeUInt 4 message.size
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 8 message.high
    ++ (encodeUInt 8 message.low
    ++ (encodeUInt 8 message.first
    ++ (Alpha.encode message.tradeCondition))))))))

def decode (bytes : List UInt8) : Option (ComplexStrategyTickerMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 6 bytes
  let (strategyId, bytes) ← decodeUInt 4 bytes
  let (lastPrice, bytes) ← decodeUInt 8 bytes
  let (size, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (high, bytes) ← decodeUInt 8 bytes
  let (low, bytes) ← decodeUInt 8 bytes
  let (first, bytes) ← decodeUInt 8 bytes
  let (tradeCondition, bytes) ← Alpha.decode 1 bytes
  pure ({ timestamp, strategyId, lastPrice, size, volume, high, low, first, tradeCondition }, bytes)

@[simp] theorem encode_length (message : ComplexStrategyTickerMessage) : (encode message).length = 51 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : ComplexStrategyTickerMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ComplexStrategyTickerMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end ComplexStrategyTickerMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | systemEventMessage (message : SystemEventMessage) -- "S" 0x53
  | complexStrategyDirectoryMessage (message : ComplexStrategyDirectoryMessage) -- "R" 0x52
  | strategyTradingActionMessage (message : StrategyTradingActionMessage) -- "H" 0x48
  | strategyOpenClosedMessage (message : StrategyOpenClosedMessage) -- "O" 0x4F
  | strategyDepthIncrementalMessage (message : StrategyDepthIncrementalMessage) -- "K" 0x4B
  | complexStrategyTickerMessage (message : ComplexStrategyTickerMessage) -- "t" 0x74
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .systemEventMessage _ => 83
  | .complexStrategyDirectoryMessage _ => 82
  | .strategyTradingActionMessage _ => 72
  | .strategyOpenClosedMessage _ => 79
  | .strategyDepthIncrementalMessage _ => 75
  | .complexStrategyTickerMessage _ => 116

def encode : Payload → List UInt8
  | .systemEventMessage message => SystemEventMessage.encode message
  | .complexStrategyDirectoryMessage message => ComplexStrategyDirectoryMessage.encode message
  | .strategyTradingActionMessage message => StrategyTradingActionMessage.encode message
  | .strategyOpenClosedMessage message => StrategyOpenClosedMessage.encode message
  | .strategyDepthIncrementalMessage message => StrategyDepthIncrementalMessage.encode message
  | .complexStrategyTickerMessage message => ComplexStrategyTickerMessage.encode message

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 82 then (ComplexStrategyDirectoryMessage.decode bytes).map fun (message, rest) => (.complexStrategyDirectoryMessage message, rest)
  else if tag = 72 then (StrategyTradingActionMessage.decode bytes).map fun (message, rest) => (.strategyTradingActionMessage message, rest)
  else if tag = 79 then (StrategyOpenClosedMessage.decode bytes).map fun (message, rest) => (.strategyOpenClosedMessage message, rest)
  else if tag = 75 then (StrategyDepthIncrementalMessage.decode bytes).map fun (message, rest) => (.strategyDepthIncrementalMessage message, rest)
  else if tag = 116 then (ComplexStrategyTickerMessage.decode bytes).map fun (message, rest) => (.complexStrategyTickerMessage message, rest)
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

end Omi.NasdaqIseoptionsDepthcombofeedItchV10Udp
