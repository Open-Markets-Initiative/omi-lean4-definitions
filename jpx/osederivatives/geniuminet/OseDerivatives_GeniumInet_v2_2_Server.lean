import Wire

/-!
# Japan Exchange Group Genium Inet v2.2

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.JpxOsederivativesGeniuminetGlimpseV22Server

/-- Reject Reason Code: one byte code -/
def RejectReasonCode.codes : List UInt8 :=
  [0x41, 0x53]

inductive RejectReasonCode where
  | notAuthorized -- Not Authorized
  | sessionNotAvailable -- Session Not Available
  | unlisted (byte : { byte : UInt8 // byte ∉ RejectReasonCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RejectReasonCode

def toByte : RejectReasonCode → UInt8
  | .notAuthorized => 0x41
  | .sessionNotAvailable => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RejectReasonCode :=
  if byte = 0x41 then .notAuthorized
  else .sessionNotAvailable

def ofByte (byte : UInt8) : RejectReasonCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RejectReasonCode) : ofByte value.toByte = value := by
  cases value with
  | notAuthorized => decide
  | sessionNotAvailable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RejectReasonCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RejectReasonCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RejectReasonCode) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : RejectReasonCode) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : RejectReasonCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RejectReasonCode

/-- Leg Side: one byte code -/
def LegSide.codes : List UInt8 :=
  [0x42, 0x43]

inductive LegSide where
  | buyIfOnBuySideSellIfOnSellSide -- Buy If On Buy Side Sell If On Sell Side
  | sellIfOnBuySideBuyIfOnSellSide -- Sell If On Buy Side Buy If On Sell Side
  | unlisted (byte : { byte : UInt8 // byte ∉ LegSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LegSide

def toByte : LegSide → UInt8
  | .buyIfOnBuySideSellIfOnSellSide => 0x42
  | .sellIfOnBuySideBuyIfOnSellSide => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LegSide :=
  if byte = 0x42 then .buyIfOnBuySideSellIfOnSellSide
  else .sellIfOnBuySideBuyIfOnSellSide

def ofByte (byte : UInt8) : LegSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LegSide) : ofByte value.toByte = value := by
  cases value with
  | buyIfOnBuySideSellIfOnSellSide => decide
  | sellIfOnBuySideBuyIfOnSellSide => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LegSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LegSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LegSide) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : LegSide) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : LegSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LegSide

/-- Event Code: one byte code -/
def EventCode.codes : List UInt8 :=
  [0x4F, 0x43]

inductive EventCode where
  | startOfMessageTransmission -- Start Of Message Transmission
  | endOfMessageTransmission -- End Of Message Transmission
  | unlisted (byte : { byte : UInt8 // byte ∉ EventCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventCode

def toByte : EventCode → UInt8
  | .startOfMessageTransmission => 0x4F
  | .endOfMessageTransmission => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventCode :=
  if byte = 0x4F then .startOfMessageTransmission
  else .endOfMessageTransmission

def ofByte (byte : UInt8) : EventCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventCode) : ofByte value.toByte = value := by
  cases value with
  | startOfMessageTransmission => decide
  | endOfMessageTransmission => decide
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

/-- Occurred At Cross: one byte code -/
def OccurredAtCross.codes : List UInt8 :=
  [0x59, 0x4E]

inductive OccurredAtCross where
  | executionThroughAuction -- Execution Through Auction
  | executionThroughZaraba -- Execution Through Zaraba
  | unlisted (byte : { byte : UInt8 // byte ∉ OccurredAtCross.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OccurredAtCross

def toByte : OccurredAtCross → UInt8
  | .executionThroughAuction => 0x59
  | .executionThroughZaraba => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OccurredAtCross :=
  if byte = 0x59 then .executionThroughAuction
  else .executionThroughZaraba

def ofByte (byte : UInt8) : OccurredAtCross :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OccurredAtCross) : ofByte value.toByte = value := by
  cases value with
  | executionThroughAuction => decide
  | executionThroughZaraba => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OccurredAtCross) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OccurredAtCross × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OccurredAtCross) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OccurredAtCross) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OccurredAtCross) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OccurredAtCross

/-- Debug Packet -/
structure DebugPacket where
  debugText : Capped 65405
  deriving DecidableEq, Repr

namespace DebugPacket

def encode (message : DebugPacket) : List UInt8 :=
  message.debugText.val

def decode (bytes : List UInt8) : Option DebugPacket := do
  let debugText_ := bytes
  if fits_debugText : debugText_.length ≤ 65405 then
    pure { debugText := ⟨debugText_, fits_debugText⟩ }
  else none

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DebugPacket) : (encode message).length ≤ 65405 := by
  have bound_debugText := message.debugText.length_le
  unfold encode
  omega

theorem decode_encode (message : DebugPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [dite_eq_left message.debugText.length_le]
  rfl

end DebugPacket

/-- Login Accepted Packet: 30 bytes -/
structure LoginAcceptedPacket where
  acceptedSession : Alpha 10
  acceptedSequenceNumber : Alpha 20
  deriving DecidableEq, Repr

namespace LoginAcceptedPacket

def encode (message : LoginAcceptedPacket) : List UInt8 :=
  Alpha.encode message.acceptedSession
    ++ (Alpha.encode message.acceptedSequenceNumber)

def decode (bytes : List UInt8) : Option (LoginAcceptedPacket × List UInt8) := do
  let (acceptedSession, bytes) ← Alpha.decode 10 bytes
  let (acceptedSequenceNumber, bytes) ← Alpha.decode 20 bytes
  pure ({ acceptedSession, acceptedSequenceNumber }, bytes)

@[simp] theorem encode_length (message : LoginAcceptedPacket) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : LoginAcceptedPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginAcceptedPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LoginAcceptedPacket) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end LoginAcceptedPacket

/-- Login Rejected Packet: 1 bytes -/
structure LoginRejectedPacket where
  rejectReasonCode : RejectReasonCode
  deriving DecidableEq, Repr

namespace LoginRejectedPacket

def encode (message : LoginRejectedPacket) : List UInt8 :=
  RejectReasonCode.encode message.rejectReasonCode

def decode (bytes : List UInt8) : Option (LoginRejectedPacket × List UInt8) := do
  let (rejectReasonCode, bytes) ← RejectReasonCode.decode bytes
  pure ({ rejectReasonCode }, bytes)

@[simp] theorem encode_length (message : LoginRejectedPacket) : (encode message).length = 1 := by
  unfold encode
  simp only [RejectReasonCode.encode_length]

theorem encode_length_pos (message : LoginRejectedPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginRejectedPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [RejectReasonCode.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LoginRejectedPacket) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end LoginRejectedPacket

/-- Seconds Message: 4 bytes -/
structure SecondsMessage where
  second : BitVec 32
  deriving DecidableEq, Repr

namespace SecondsMessage

def encode (message : SecondsMessage) : List UInt8 :=
  encodeUInt 4 message.second

def decode (bytes : List UInt8) : Option (SecondsMessage × List UInt8) := do
  let (second, bytes) ← decodeUInt 4 bytes
  pure ({ second }, bytes)

@[simp] theorem encode_length (message : SecondsMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : SecondsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecondsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SecondsMessage

/-- Series Information Basic Message: 128 bytes -/
structure SeriesInformationBasicMessage where
  nanoseconds : BitVec 32
  orderBookId : BitVec 32
  symbol : Alpha 32
  longName : Alpha 32
  reserved12 : Alpha 12
  financialProduct : BitVec 8
  tradingCurrency : Alpha 3
  numberOfDecimalsInPrice : BitVec 16
  numberOfDecimalsInNominalValue : BitVec 16
  oddLotSize : BitVec 32
  roundLotSize : BitVec 32
  blockLotSize : BitVec 32
  nominalValue : BitVec 64
  numberOfLegs : BitVec 8
  underlyingOrderBookId : BitVec 32
  strikePrice : BitVec 32
  expirationDate : BitVec 32
  numberOfDecimalsInStrikePrice : BitVec 16
  putOrCall : BitVec 8
  deriving DecidableEq, Repr

namespace SeriesInformationBasicMessage

def encode (message : SeriesInformationBasicMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.orderBookId
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.longName
    ++ (Alpha.encode message.reserved12
    ++ (encodeUInt 1 message.financialProduct
    ++ (Alpha.encode message.tradingCurrency
    ++ (encodeUInt 2 message.numberOfDecimalsInPrice
    ++ (encodeUInt 2 message.numberOfDecimalsInNominalValue
    ++ (encodeUInt 4 message.oddLotSize
    ++ (encodeUInt 4 message.roundLotSize
    ++ (encodeUInt 4 message.blockLotSize
    ++ (encodeUInt 8 message.nominalValue
    ++ (encodeUInt 1 message.numberOfLegs
    ++ (encodeUInt 4 message.underlyingOrderBookId
    ++ (encodeUInt 4 message.strikePrice
    ++ (encodeUInt 4 message.expirationDate
    ++ (encodeUInt 2 message.numberOfDecimalsInStrikePrice
    ++ (encodeUInt 1 message.putOrCall))))))))))))))))))

def decode (bytes : List UInt8) : Option (SeriesInformationBasicMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (symbol, bytes) ← Alpha.decode 32 bytes
  let (longName, bytes) ← Alpha.decode 32 bytes
  let (reserved12, bytes) ← Alpha.decode 12 bytes
  let (financialProduct, bytes) ← decodeUInt 1 bytes
  let (tradingCurrency, bytes) ← Alpha.decode 3 bytes
  let (numberOfDecimalsInPrice, bytes) ← decodeUInt 2 bytes
  let (numberOfDecimalsInNominalValue, bytes) ← decodeUInt 2 bytes
  let (oddLotSize, bytes) ← decodeUInt 4 bytes
  let (roundLotSize, bytes) ← decodeUInt 4 bytes
  let (blockLotSize, bytes) ← decodeUInt 4 bytes
  let (nominalValue, bytes) ← decodeUInt 8 bytes
  let (numberOfLegs, bytes) ← decodeUInt 1 bytes
  let (underlyingOrderBookId, bytes) ← decodeUInt 4 bytes
  let (strikePrice, bytes) ← decodeUInt 4 bytes
  let (expirationDate, bytes) ← decodeUInt 4 bytes
  let (numberOfDecimalsInStrikePrice, bytes) ← decodeUInt 2 bytes
  let (putOrCall, bytes) ← decodeUInt 1 bytes
  pure ({ nanoseconds, orderBookId, symbol, longName, reserved12, financialProduct, tradingCurrency, numberOfDecimalsInPrice, numberOfDecimalsInNominalValue, oddLotSize, roundLotSize, blockLotSize, nominalValue, numberOfLegs, underlyingOrderBookId, strikePrice, expirationDate, numberOfDecimalsInStrikePrice, putOrCall }, bytes)

@[simp] theorem encode_length (message : SeriesInformationBasicMessage) : (encode message).length = 128 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : SeriesInformationBasicMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SeriesInformationBasicMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SeriesInformationBasicMessage

/-- Series Information Basic Combination Message: 17 bytes -/
structure SeriesInformationBasicCombinationMessage where
  nanoseconds : BitVec 32
  combinationOrderBookId : BitVec 32
  legOrderBookId : BitVec 32
  legSide : LegSide
  legRatio : BitVec 32
  deriving DecidableEq, Repr

namespace SeriesInformationBasicCombinationMessage

def encode (message : SeriesInformationBasicCombinationMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.combinationOrderBookId
    ++ (encodeUInt 4 message.legOrderBookId
    ++ (LegSide.encode message.legSide
    ++ (encodeUInt 4 message.legRatio))))

def decode (bytes : List UInt8) : Option (SeriesInformationBasicCombinationMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (combinationOrderBookId, bytes) ← decodeUInt 4 bytes
  let (legOrderBookId, bytes) ← decodeUInt 4 bytes
  let (legSide, bytes) ← LegSide.decode bytes
  let (legRatio, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, combinationOrderBookId, legOrderBookId, legSide, legRatio }, bytes)

@[simp] theorem encode_length (message : SeriesInformationBasicCombinationMessage) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, LegSide.encode_length]

theorem encode_length_pos (message : SeriesInformationBasicCombinationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SeriesInformationBasicCombinationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, LegSide.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SeriesInformationBasicCombinationMessage

/-- Tick Size Data Message: 24 bytes -/
structure TickSizeDataMessage where
  nanoseconds : BitVec 32
  orderBookId : BitVec 32
  tickSize : BitVec 64
  priceFrom : BitVec 32
  priceTo : BitVec 32
  deriving DecidableEq, Repr

namespace TickSizeDataMessage

def encode (message : TickSizeDataMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.orderBookId
    ++ (encodeUInt 8 message.tickSize
    ++ (encodeUInt 4 message.priceFrom
    ++ (encodeUInt 4 message.priceTo))))

def decode (bytes : List UInt8) : Option (TickSizeDataMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (tickSize, bytes) ← decodeUInt 8 bytes
  let (priceFrom, bytes) ← decodeUInt 4 bytes
  let (priceTo, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, orderBookId, tickSize, priceFrom, priceTo }, bytes)

@[simp] theorem encode_length (message : TickSizeDataMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : TickSizeDataMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TickSizeDataMessage) (rest : List UInt8) :
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TickSizeDataMessage

/-- System Event Data Message: 5 bytes -/
structure SystemEventDataMessage where
  nanoseconds : BitVec 32
  eventCode : EventCode
  deriving DecidableEq, Repr

namespace SystemEventDataMessage

def encode (message : SystemEventDataMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (EventCode.encode message.eventCode)

def decode (bytes : List UInt8) : Option (SystemEventDataMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (eventCode, bytes) ← EventCode.decode bytes
  pure ({ nanoseconds, eventCode }, bytes)

@[simp] theorem encode_length (message : SystemEventDataMessage) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, EventCode.encode_length]

theorem encode_length_pos (message : SystemEventDataMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemEventDataMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [EventCode.decode_encode, some_bind]
  rfl

end SystemEventDataMessage

/-- Trading Status Data Message: 28 bytes -/
structure TradingStatusDataMessage where
  nanoseconds : BitVec 32
  orderBookId : BitVec 32
  stateName : Alpha 20
  deriving DecidableEq, Repr

namespace TradingStatusDataMessage

def encode (message : TradingStatusDataMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.orderBookId
    ++ (Alpha.encode message.stateName))

def decode (bytes : List UInt8) : Option (TradingStatusDataMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (stateName, bytes) ← Alpha.decode 20 bytes
  pure ({ nanoseconds, orderBookId, stateName }, bytes)

@[simp] theorem encode_length (message : TradingStatusDataMessage) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : TradingStatusDataMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradingStatusDataMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradingStatusDataMessage

/-- New Order Message: 36 bytes -/
structure NewOrderMessage where
  nanoseconds : BitVec 32
  orderId : BitVec 64
  orderBookId : BitVec 32
  side : Side
  orderBookPosition : BitVec 32
  quantity : BitVec 64
  price : BitVec 32
  orderAttributes : BitVec 16
  lotType : BitVec 8
  deriving DecidableEq, Repr

namespace NewOrderMessage

def encode (message : NewOrderMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 8 message.orderId
    ++ (encodeUInt 4 message.orderBookId
    ++ (Side.encode message.side
    ++ (encodeUInt 4 message.orderBookPosition
    ++ (encodeUInt 8 message.quantity
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 2 message.orderAttributes
    ++ (encodeUInt 1 message.lotType))))))))

def decode (bytes : List UInt8) : Option (NewOrderMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderBookPosition, bytes) ← decodeUInt 4 bytes
  let (quantity, bytes) ← decodeUInt 8 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (orderAttributes, bytes) ← decodeUInt 2 bytes
  let (lotType, bytes) ← decodeUInt 1 bytes
  pure ({ nanoseconds, orderId, orderBookId, side, orderBookPosition, quantity, price, orderAttributes, lotType }, bytes)

@[simp] theorem encode_length (message : NewOrderMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length]

theorem encode_length_pos (message : NewOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
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

end NewOrderMessage

/-- Execution Notice Message: 51 bytes -/
structure ExecutionNoticeMessage where
  nanoseconds : BitVec 32
  orderId : BitVec 64
  orderBookId : BitVec 32
  side : Side
  executedQuantity : BitVec 64
  matchId : BitVec 64
  comboGroupId : BitVec 32
  reserved7A : Alpha 7
  reserved7B : Alpha 7
  deriving DecidableEq, Repr

namespace ExecutionNoticeMessage

def encode (message : ExecutionNoticeMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 8 message.orderId
    ++ (encodeUInt 4 message.orderBookId
    ++ (Side.encode message.side
    ++ (encodeUInt 8 message.executedQuantity
    ++ (encodeUInt 8 message.matchId
    ++ (encodeUInt 4 message.comboGroupId
    ++ (Alpha.encode message.reserved7A
    ++ (Alpha.encode message.reserved7B))))))))

def decode (bytes : List UInt8) : Option (ExecutionNoticeMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (executedQuantity, bytes) ← decodeUInt 8 bytes
  let (matchId, bytes) ← decodeUInt 8 bytes
  let (comboGroupId, bytes) ← decodeUInt 4 bytes
  let (reserved7A, bytes) ← Alpha.decode 7 bytes
  let (reserved7B, bytes) ← Alpha.decode 7 bytes
  pure ({ nanoseconds, orderId, orderBookId, side, executedQuantity, matchId, comboGroupId, reserved7A, reserved7B }, bytes)

@[simp] theorem encode_length (message : ExecutionNoticeMessage) : (encode message).length = 51 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : ExecutionNoticeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExecutionNoticeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ExecutionNoticeMessage

/-- Execution Notice With Trade Information Message: 57 bytes -/
structure ExecutionNoticeWithTradeInformationMessage where
  nanoseconds : BitVec 32
  orderId : BitVec 64
  orderBookId : BitVec 32
  side : Side
  executedQuantity : BitVec 64
  matchId : BitVec 64
  comboGroupId : BitVec 32
  reserved7A : Alpha 7
  reserved7B : Alpha 7
  tradePrice : BitVec 32
  occurredAtCross : OccurredAtCross
  printable : Alpha 1
  deriving DecidableEq, Repr

namespace ExecutionNoticeWithTradeInformationMessage

def encode (message : ExecutionNoticeWithTradeInformationMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 8 message.orderId
    ++ (encodeUInt 4 message.orderBookId
    ++ (Side.encode message.side
    ++ (encodeUInt 8 message.executedQuantity
    ++ (encodeUInt 8 message.matchId
    ++ (encodeUInt 4 message.comboGroupId
    ++ (Alpha.encode message.reserved7A
    ++ (Alpha.encode message.reserved7B
    ++ (encodeUInt 4 message.tradePrice
    ++ (OccurredAtCross.encode message.occurredAtCross
    ++ (Alpha.encode message.printable)))))))))))

def decode (bytes : List UInt8) : Option (ExecutionNoticeWithTradeInformationMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (executedQuantity, bytes) ← decodeUInt 8 bytes
  let (matchId, bytes) ← decodeUInt 8 bytes
  let (comboGroupId, bytes) ← decodeUInt 4 bytes
  let (reserved7A, bytes) ← Alpha.decode 7 bytes
  let (reserved7B, bytes) ← Alpha.decode 7 bytes
  let (tradePrice, bytes) ← decodeUInt 4 bytes
  let (occurredAtCross, bytes) ← OccurredAtCross.decode bytes
  let (printable, bytes) ← Alpha.decode 1 bytes
  pure ({ nanoseconds, orderId, orderBookId, side, executedQuantity, matchId, comboGroupId, reserved7A, reserved7B, tradePrice, occurredAtCross, printable }, bytes)

@[simp] theorem encode_length (message : ExecutionNoticeWithTradeInformationMessage) : (encode message).length = 57 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length, Alpha.encode_length, OccurredAtCross.encode_length]

theorem encode_length_pos (message : ExecutionNoticeWithTradeInformationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExecutionNoticeWithTradeInformationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OccurredAtCross.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ExecutionNoticeWithTradeInformationMessage

/-- Deleted Order Message: 17 bytes -/
structure DeletedOrderMessage where
  nanoseconds : BitVec 32
  orderId : BitVec 64
  orderBookId : BitVec 32
  side : Side
  deriving DecidableEq, Repr

namespace DeletedOrderMessage

def encode (message : DeletedOrderMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 8 message.orderId
    ++ (encodeUInt 4 message.orderBookId
    ++ (Side.encode message.side)))

def decode (bytes : List UInt8) : Option (DeletedOrderMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  pure ({ nanoseconds, orderId, orderBookId, side }, bytes)

@[simp] theorem encode_length (message : DeletedOrderMessage) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length]

theorem encode_length_pos (message : DeletedOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DeletedOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Side.decode_encode, some_bind]
  rfl

end DeletedOrderMessage

/-- Ep Message: 52 bytes -/
structure EpMessage where
  nanoseconds : BitVec 32
  orderBookId : BitVec 32
  availableBidQuantityAtEquilibriumPrice : BitVec 64
  availableAskQuantityAtEquilibriumPrice : BitVec 64
  equilibriumPrice : BitVec 32
  reserved4A : Alpha 4
  reserved4B : Alpha 4
  reserved8A : Alpha 8
  reserved8B : Alpha 8
  deriving DecidableEq, Repr

namespace EpMessage

def encode (message : EpMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.orderBookId
    ++ (encodeUInt 8 message.availableBidQuantityAtEquilibriumPrice
    ++ (encodeUInt 8 message.availableAskQuantityAtEquilibriumPrice
    ++ (encodeUInt 4 message.equilibriumPrice
    ++ (Alpha.encode message.reserved4A
    ++ (Alpha.encode message.reserved4B
    ++ (Alpha.encode message.reserved8A
    ++ (Alpha.encode message.reserved8B))))))))

def decode (bytes : List UInt8) : Option (EpMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (availableBidQuantityAtEquilibriumPrice, bytes) ← decodeUInt 8 bytes
  let (availableAskQuantityAtEquilibriumPrice, bytes) ← decodeUInt 8 bytes
  let (equilibriumPrice, bytes) ← decodeUInt 4 bytes
  let (reserved4A, bytes) ← Alpha.decode 4 bytes
  let (reserved4B, bytes) ← Alpha.decode 4 bytes
  let (reserved8A, bytes) ← Alpha.decode 8 bytes
  let (reserved8B, bytes) ← Alpha.decode 8 bytes
  pure ({ nanoseconds, orderBookId, availableBidQuantityAtEquilibriumPrice, availableAskQuantityAtEquilibriumPrice, equilibriumPrice, reserved4A, reserved4B, reserved8A, reserved8B }, bytes)

@[simp] theorem encode_length (message : EpMessage) : (encode message).length = 52 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : EpMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EpMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end EpMessage

/-- Snapshot Completion Message: 20 bytes -/
structure SnapshotCompletionMessage where
  sequence : Alpha 20
  deriving DecidableEq, Repr

namespace SnapshotCompletionMessage

def encode (message : SnapshotCompletionMessage) : List UInt8 :=
  Alpha.encode message.sequence

def decode (bytes : List UInt8) : Option (SnapshotCompletionMessage × List UInt8) := do
  let (sequence, bytes) ← Alpha.decode 20 bytes
  pure ({ sequence }, bytes)

@[simp] theorem encode_length (message : SnapshotCompletionMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : SnapshotCompletionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SnapshotCompletionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end SnapshotCompletionMessage

/-- Any Sequenced Message, selected by Sequenced Message Type -/
inductive SequencedMessage where
  | secondsMessage (message : SecondsMessage) -- "T" 0x54
  | seriesInformationBasicMessage (message : SeriesInformationBasicMessage) -- "R" 0x52
  | seriesInformationBasicCombinationMessage (message : SeriesInformationBasicCombinationMessage) -- "M" 0x4D
  | tickSizeDataMessage (message : TickSizeDataMessage) -- "L" 0x4C
  | systemEventDataMessage (message : SystemEventDataMessage) -- "S" 0x53
  | tradingStatusDataMessage (message : TradingStatusDataMessage) -- "O" 0x4F
  | newOrderMessage (message : NewOrderMessage) -- "A" 0x41
  | executionNoticeMessage (message : ExecutionNoticeMessage) -- "E" 0x45
  | executionNoticeWithTradeInformationMessage (message : ExecutionNoticeWithTradeInformationMessage) -- "C" 0x43
  | deletedOrderMessage (message : DeletedOrderMessage) -- "D" 0x44
  | epMessage (message : EpMessage) -- "Z" 0x5A
  | snapshotCompletionMessage (message : SnapshotCompletionMessage) -- "G" 0x47
  deriving DecidableEq, Repr

namespace SequencedMessage

/-- The Sequenced Message Type each message is sent under -/
def tag : SequencedMessage → BitVec 8
  | .secondsMessage _ => 84
  | .seriesInformationBasicMessage _ => 82
  | .seriesInformationBasicCombinationMessage _ => 77
  | .tickSizeDataMessage _ => 76
  | .systemEventDataMessage _ => 83
  | .tradingStatusDataMessage _ => 79
  | .newOrderMessage _ => 65
  | .executionNoticeMessage _ => 69
  | .executionNoticeWithTradeInformationMessage _ => 67
  | .deletedOrderMessage _ => 68
  | .epMessage _ => 90
  | .snapshotCompletionMessage _ => 71

def encode : SequencedMessage → List UInt8
  | .secondsMessage message => SecondsMessage.encode message
  | .seriesInformationBasicMessage message => SeriesInformationBasicMessage.encode message
  | .seriesInformationBasicCombinationMessage message => SeriesInformationBasicCombinationMessage.encode message
  | .tickSizeDataMessage message => TickSizeDataMessage.encode message
  | .systemEventDataMessage message => SystemEventDataMessage.encode message
  | .tradingStatusDataMessage message => TradingStatusDataMessage.encode message
  | .newOrderMessage message => NewOrderMessage.encode message
  | .executionNoticeMessage message => ExecutionNoticeMessage.encode message
  | .executionNoticeWithTradeInformationMessage message => ExecutionNoticeWithTradeInformationMessage.encode message
  | .deletedOrderMessage message => DeletedOrderMessage.encode message
  | .epMessage message => EpMessage.encode message
  | .snapshotCompletionMessage message => SnapshotCompletionMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : SequencedMessage) : (encode message).length ≤ 128 := by
  cases message with
  | secondsMessage inner =>
    simp only [encode, SecondsMessage.encode_length]
    omega
  | seriesInformationBasicMessage inner =>
    simp only [encode, SeriesInformationBasicMessage.encode_length]
    omega
  | seriesInformationBasicCombinationMessage inner =>
    simp only [encode, SeriesInformationBasicCombinationMessage.encode_length]
    omega
  | tickSizeDataMessage inner =>
    simp only [encode, TickSizeDataMessage.encode_length]
    omega
  | systemEventDataMessage inner =>
    simp only [encode, SystemEventDataMessage.encode_length]
    omega
  | tradingStatusDataMessage inner =>
    simp only [encode, TradingStatusDataMessage.encode_length]
    omega
  | newOrderMessage inner =>
    simp only [encode, NewOrderMessage.encode_length]
    omega
  | executionNoticeMessage inner =>
    simp only [encode, ExecutionNoticeMessage.encode_length]
    omega
  | executionNoticeWithTradeInformationMessage inner =>
    simp only [encode, ExecutionNoticeWithTradeInformationMessage.encode_length]
    omega
  | deletedOrderMessage inner =>
    simp only [encode, DeletedOrderMessage.encode_length]
    omega
  | epMessage inner =>
    simp only [encode, EpMessage.encode_length]
    omega
  | snapshotCompletionMessage inner =>
    simp only [encode, SnapshotCompletionMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (SequencedMessage × List UInt8) :=
  if tag = 84 then (SecondsMessage.decode bytes).map fun (message, rest) => (.secondsMessage message, rest)
  else if tag = 82 then (SeriesInformationBasicMessage.decode bytes).map fun (message, rest) => (.seriesInformationBasicMessage message, rest)
  else if tag = 77 then (SeriesInformationBasicCombinationMessage.decode bytes).map fun (message, rest) => (.seriesInformationBasicCombinationMessage message, rest)
  else if tag = 76 then (TickSizeDataMessage.decode bytes).map fun (message, rest) => (.tickSizeDataMessage message, rest)
  else if tag = 83 then (SystemEventDataMessage.decode bytes).map fun (message, rest) => (.systemEventDataMessage message, rest)
  else if tag = 79 then (TradingStatusDataMessage.decode bytes).map fun (message, rest) => (.tradingStatusDataMessage message, rest)
  else if tag = 65 then (NewOrderMessage.decode bytes).map fun (message, rest) => (.newOrderMessage message, rest)
  else if tag = 69 then (ExecutionNoticeMessage.decode bytes).map fun (message, rest) => (.executionNoticeMessage message, rest)
  else if tag = 67 then (ExecutionNoticeWithTradeInformationMessage.decode bytes).map fun (message, rest) => (.executionNoticeWithTradeInformationMessage message, rest)
  else if tag = 68 then (DeletedOrderMessage.decode bytes).map fun (message, rest) => (.deletedOrderMessage message, rest)
  else if tag = 90 then (EpMessage.decode bytes).map fun (message, rest) => (.epMessage message, rest)
  else if tag = 71 then (SnapshotCompletionMessage.decode bytes).map fun (message, rest) => (.snapshotCompletionMessage message, rest)
  else none

@[simp] theorem decode_encode (message : SequencedMessage) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end SequencedMessage

/-- Sequenced Data Packet -/
structure SequencedDataPacket where
  sequencedMessage : SequencedMessage
  deriving DecidableEq, Repr

namespace SequencedDataPacket

def encode (message : SequencedDataPacket) : List UInt8 :=
  encodeUInt 1 (SequencedMessage.tag message.sequencedMessage)
    ++ (SequencedMessage.encode message.sequencedMessage)

def decode (bytes : List UInt8) : Option (SequencedDataPacket × List UInt8) := do
  let (sequencedMessageType, bytes) ← decodeUInt 1 bytes
  let (sequencedMessage, bytes) ← SequencedMessage.decode sequencedMessageType bytes
  pure ({ sequencedMessage }, bytes)

theorem encode_length_pos (message : SequencedDataPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SequencedDataPacket) : (encode message).length ≤ 129 := by
  unfold encode
  cases message.sequencedMessage with
  | secondsMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, SecondsMessage.encode_length]
    omega
  | seriesInformationBasicMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, SeriesInformationBasicMessage.encode_length]
    omega
  | seriesInformationBasicCombinationMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, SeriesInformationBasicCombinationMessage.encode_length]
    omega
  | tickSizeDataMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, TickSizeDataMessage.encode_length]
    omega
  | systemEventDataMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, SystemEventDataMessage.encode_length]
    omega
  | tradingStatusDataMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, TradingStatusDataMessage.encode_length]
    omega
  | newOrderMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, NewOrderMessage.encode_length]
    omega
  | executionNoticeMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, ExecutionNoticeMessage.encode_length]
    omega
  | executionNoticeWithTradeInformationMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, ExecutionNoticeWithTradeInformationMessage.encode_length]
    omega
  | deletedOrderMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, DeletedOrderMessage.encode_length]
    omega
  | epMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, EpMessage.encode_length]
    omega
  | snapshotCompletionMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, SnapshotCompletionMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : SequencedDataPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [SequencedMessage.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SequencedDataPacket) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SequencedDataPacket

/-- Server Heartbeat: 0 bytes -/
structure ServerHeartbeat where
  deriving DecidableEq, Repr

namespace ServerHeartbeat

def encode (_ : ServerHeartbeat) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (ServerHeartbeat × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : ServerHeartbeat) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : ServerHeartbeat) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ServerHeartbeat) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ServerHeartbeat

/-- End Of Session: 0 bytes -/
structure EndOfSession where
  deriving DecidableEq, Repr

namespace EndOfSession

def encode (_ : EndOfSession) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (EndOfSession × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : EndOfSession) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : EndOfSession) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : EndOfSession) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end EndOfSession

/-- Any Server Payload, selected by Server Packet Type -/
inductive ServerPayload where
  | debugPacket (message : DebugPacket) -- "+" 0x2B
  | loginAcceptedPacket (message : LoginAcceptedPacket) -- "A" 0x41
  | loginRejectedPacket (message : LoginRejectedPacket) -- "J" 0x4A
  | sequencedDataPacket (message : SequencedDataPacket) -- "S" 0x53
  | serverHeartbeat (message : ServerHeartbeat) -- "H" 0x48
  | endOfSession (message : EndOfSession) -- "Z" 0x5A
  deriving DecidableEq, Repr

namespace ServerPayload

/-- The Server Packet Type each message is sent under -/
def tag : ServerPayload → BitVec 8
  | .debugPacket _ => 43
  | .loginAcceptedPacket _ => 65
  | .loginRejectedPacket _ => 74
  | .sequencedDataPacket _ => 83
  | .serverHeartbeat _ => 72
  | .endOfSession _ => 90

def encode : ServerPayload → List UInt8
  | .debugPacket message => DebugPacket.encode message
  | .loginAcceptedPacket message => LoginAcceptedPacket.encode message
  | .loginRejectedPacket message => LoginRejectedPacket.encode message
  | .sequencedDataPacket message => SequencedDataPacket.encode message
  | .serverHeartbeat message => ServerHeartbeat.encode message
  | .endOfSession message => EndOfSession.encode message

/-- Does the message end the session? Nothing in its packet may follow it -/
def endsSession : ServerPayload → Bool
  | .endOfSession _ => true
  | _ => false

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ServerPayload) : (encode message).length ≤ 65405 := by
  cases message with
  | debugPacket inner =>
    have bound_inner := DebugPacket.encode_length_le inner
    simp only [encode]
    omega
  | loginAcceptedPacket inner =>
    simp only [encode, LoginAcceptedPacket.encode_length]
    omega
  | loginRejectedPacket inner =>
    simp only [encode, LoginRejectedPacket.encode_length]
    omega
  | sequencedDataPacket inner =>
    have bound_inner := SequencedDataPacket.encode_length_le inner
    simp only [encode]
    omega
  | serverHeartbeat inner =>
    simp only [encode, ServerHeartbeat.encode_length]
    omega
  | endOfSession inner =>
    simp only [encode, EndOfSession.encode_length]
    omega

/-- Decoded from the whole of the frame: a message that reads to its end takes it all, any other must leave nothing -/
def decode (tag : BitVec 8) (bytes : List UInt8) : Option ServerPayload :=
  if tag = 43 then (DebugPacket.decode bytes).map fun message => .debugPacket message
  else if tag = 65 then (LoginAcceptedPacket.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.loginAcceptedPacket message) else none
  else if tag = 74 then (LoginRejectedPacket.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.loginRejectedPacket message) else none
  else if tag = 83 then (SequencedDataPacket.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.sequencedDataPacket message) else none
  else if tag = 72 then (ServerHeartbeat.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.serverHeartbeat message) else none
  else if tag = 90 then (EndOfSession.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.endOfSession message) else none
  else none

theorem decode_encode (message : ServerPayload) :
    decode (tag message) (encode message) = some message := by
  cases message with
  | debugPacket message => simp [decode, encode, tag, DebugPacket.decode_encode]
  | loginAcceptedPacket message => simp [decode, encode, tag, LoginAcceptedPacket.decode_encode_nil]
  | loginRejectedPacket message => simp [decode, encode, tag, LoginRejectedPacket.decode_encode_nil]
  | sequencedDataPacket message => simp [decode, encode, tag, SequencedDataPacket.decode_encode_nil]
  | serverHeartbeat message => simp [decode, encode, tag, ServerHeartbeat.decode_encode_nil]
  | endOfSession message => simp [decode, encode, tag, EndOfSession.decode_encode_nil]

end ServerPayload

/-- Server Soup Bin Tcp Packet -/
structure ServerSoupBinTcpPacket where
  serverPayload : ServerPayload
  deriving DecidableEq, Repr

namespace ServerSoupBinTcpPacket

def encodeBody (message : ServerSoupBinTcpPacket) : List UInt8 :=
  encodeUInt 1 (ServerPayload.tag message.serverPayload)
    ++ (ServerPayload.encode message.serverPayload)

def decodeBody (bytes : List UInt8) : Option ServerSoupBinTcpPacket := do
  let (serverPacketType, bytes) ← decodeUInt 1 bytes
  let serverPayload ← ServerPayload.decode serverPacketType bytes
  pure { serverPayload }

theorem decodeBody_encodeBody (message : ServerSoupBinTcpPacket) : decodeBody (encodeBody message) = some message := by
  unfold decodeBody encodeBody
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ServerPayload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : ServerSoupBinTcpPacket) : (encodeBody message).length + 0 < 256 ^ 2 := by
  unfold encodeBody
  cases message.serverPayload with
  | debugPacket inner =>
    have bound_inner := DebugPacket.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length]
    omega
  | loginAcceptedPacket inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length, LoginAcceptedPacket.encode_length]
    omega
  | loginRejectedPacket inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length, LoginRejectedPacket.encode_length]
    omega
  | sequencedDataPacket inner =>
    have bound_inner := SequencedDataPacket.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length]
    omega
  | serverHeartbeat inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length, ServerHeartbeat.encode_length]
    omega
  | endOfSession inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length, EndOfSession.encode_length]
    omega

/-- Size rule: Packet Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : ServerSoupBinTcpPacket → List UInt8 :=
  encodeFramed 2 0 encodeBody

def decode : List UInt8 → Option (ServerSoupBinTcpPacket × List UInt8) :=
  decodeFramedAll 2 0 decodeBody

@[simp] theorem decode_encode (message : ServerSoupBinTcpPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedAll_encodeFramed 2 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : ServerSoupBinTcpPacket) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

/-- Does the message end the session? Nothing in its packet may follow it -/
def endsSession (message : ServerSoupBinTcpPacket) : Bool :=
  ServerPayload.endsSession message.serverPayload

end ServerSoupBinTcpPacket

/-- Server Packet -/
structure ServerPacket where
  serverSoupBinTcpPacket : List ServerSoupBinTcpPacket
  serverSoupBinTcpPacket_last : endsLast ServerSoupBinTcpPacket.endsSession serverSoupBinTcpPacket = true
  deriving DecidableEq, Repr

namespace ServerPacket

def encode (message : ServerPacket) : List UInt8 :=
  encodeMany ServerSoupBinTcpPacket.encode message.serverSoupBinTcpPacket

def decode (bytes : List UInt8) : Option ServerPacket := do
  let serverSoupBinTcpPacket ← decodeAll ServerSoupBinTcpPacket.decode bytes.length bytes
  if last_serverSoupBinTcpPacket : endsLast ServerSoupBinTcpPacket.endsSession serverSoupBinTcpPacket = true then
    pure { serverSoupBinTcpPacket, serverSoupBinTcpPacket_last := last_serverSoupBinTcpPacket }
  else none

theorem decode_encode (message : ServerPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany ServerSoupBinTcpPacket.encode ServerSoupBinTcpPacket.decode ServerSoupBinTcpPacket.decode_encode ServerSoupBinTcpPacket.encode_length_pos message.serverSoupBinTcpPacket _ (encodeMany_length_ge ServerSoupBinTcpPacket.encode ServerSoupBinTcpPacket.encode_length_pos message.serverSoupBinTcpPacket), some_bind]
  rw [dite_eq_left message.serverSoupBinTcpPacket_last]
  rfl

end ServerPacket

end Omi.JpxOsederivativesGeniuminetGlimpseV22Server
