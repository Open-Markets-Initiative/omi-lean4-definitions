import Wire

/-!
# Astana International Exchange Genium Inet v3.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.

Note: Sequenced Data Packet is not framed: its length Packet Length is not an integer it reads

Note: a Server Soup Bin Tcp Packet that ends the session is the last of serverSoupBinTcpPacket: the
decoder turns away one that is followed, and the record carries the proof it is not

License: MIT No Attribution
-/

namespace Omi.AixAixmarketGeniuminetItchV30Server

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

/-- Event Code: one byte code -/
def EventCode.codes : List UInt8 :=
  [0x4F, 0x43]

inductive EventCode where
  | startOfMessages -- Start Of Messages
  | endOfMessages -- End Of Messages
  | unlisted (byte : { byte : UInt8 // byte ∉ EventCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventCode

def toByte : EventCode → UInt8
  | .startOfMessages => 0x4F
  | .endOfMessages => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventCode :=
  if byte = 0x4F then .startOfMessages
  else .endOfMessages

def ofByte (byte : UInt8) : EventCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventCode) : ofByte value.toByte = value := by
  cases value with
  | startOfMessages => decide
  | endOfMessages => decide
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
  [0x42, 0x53, 0x20]

inductive Side where
  | buyOrder -- Buy Order
  | sellOrder -- Sell Order
  | blank -- Blank
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .buyOrder => 0x42
  | .sellOrder => 0x53
  | .blank => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x42 then .buyOrder
  else if byte = 0x53 then .sellOrder
  else .blank

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | buyOrder => decide
  | sellOrder => decide
  | blank => decide
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
  | tradeOccurredAtTheCross -- Trade Occurred At The Cross
  | tradeOccurredAtContinuousMarket -- Trade Occurred At Continuous Market
  | unlisted (byte : { byte : UInt8 // byte ∉ OccurredAtCross.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OccurredAtCross

def toByte : OccurredAtCross → UInt8
  | .tradeOccurredAtTheCross => 0x59
  | .tradeOccurredAtContinuousMarket => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OccurredAtCross :=
  if byte = 0x59 then .tradeOccurredAtTheCross
  else .tradeOccurredAtContinuousMarket

def ofByte (byte : UInt8) : OccurredAtCross :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OccurredAtCross) : ofByte value.toByte = value := by
  cases value with
  | tradeOccurredAtTheCross => decide
  | tradeOccurredAtContinuousMarket => decide
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

/-- Printable: one byte code -/
def Printable.codes : List UInt8 :=
  [0x4E, 0x59]

inductive Printable where
  | nonPrintable -- Non Printable
  | printable -- Printable
  | unlisted (byte : { byte : UInt8 // byte ∉ Printable.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Printable

def toByte : Printable → UInt8
  | .nonPrintable => 0x4E
  | .printable => 0x59
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Printable :=
  if byte = 0x4E then .nonPrintable
  else .printable

def ofByte (byte : UInt8) : Printable :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Printable) : ofByte value.toByte = value := by
  cases value with
  | nonPrintable => decide
  | printable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Printable) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Printable × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Printable) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Printable) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Printable) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Printable

/-- Trade Report: one byte code -/
def TradeReport.codes : List UInt8 :=
  [0x59, 0x4E]

inductive TradeReport where
  | matchedTradeReport -- Matched Trade Report
  | standardTrade -- Standard Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeReport.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeReport

def toByte : TradeReport → UInt8
  | .matchedTradeReport => 0x59
  | .standardTrade => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeReport :=
  if byte = 0x59 then .matchedTradeReport
  else .standardTrade

def ofByte (byte : UInt8) : TradeReport :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeReport) : ofByte value.toByte = value := by
  cases value with
  | matchedTradeReport => decide
  | standardTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeReport) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeReport × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeReport) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TradeReport) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TradeReport) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeReport

/-- Debug Packet -/
structure DebugPacket where
  debugText : Capped 65404
  deriving DecidableEq, Repr

namespace DebugPacket

def encode (message : DebugPacket) : List UInt8 :=
  message.debugText.val

def decode (bytes : List UInt8) : Option DebugPacket := do
  let debugText_ := bytes
  if fits_debugText : debugText_.length ≤ 65404 then
    pure { debugText := ⟨debugText_, fits_debugText⟩ }
  else none

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DebugPacket) : (encode message).length ≤ 65404 := by
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

/-- Order Book Directory Message: 129 bytes -/
structure OrderBookDirectoryMessage where
  nanoseconds : BitVec 32
  orderBookId : BitVec 32
  symbol : Alpha 32
  longName : Alpha 32
  isin : Alpha 12
  financialProduct : BitVec 8
  tradingCurrency : Alpha 3
  numberOfDecimalsInPrice : BitVec 16
  numberOfDecimalsInNominalValue : BitVec 16
  oddLotSize : BitVec 32
  roundLotSize : BitVec 32
  blockLotSize : BitVec 32
  nominalValue : BitVec 64
  reserved1 : Alpha 1
  underlyingOrderBookId : BitVec 32
  strikePrice : BitVec 32
  expirationDate : BitVec 32
  numberOfDecimalsInStrikePrice : BitVec 16
  putOrCall : BitVec 8
  rankingType : BitVec 8
  deriving DecidableEq, Repr

namespace OrderBookDirectoryMessage

def encode (message : OrderBookDirectoryMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.orderBookId
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.longName
    ++ (Alpha.encode message.isin
    ++ (encodeUInt 1 message.financialProduct
    ++ (Alpha.encode message.tradingCurrency
    ++ (encodeUInt 2 message.numberOfDecimalsInPrice
    ++ (encodeUInt 2 message.numberOfDecimalsInNominalValue
    ++ (encodeUInt 4 message.oddLotSize
    ++ (encodeUInt 4 message.roundLotSize
    ++ (encodeUInt 4 message.blockLotSize
    ++ (encodeUInt 8 message.nominalValue
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 4 message.underlyingOrderBookId
    ++ (encodeUInt 4 message.strikePrice
    ++ (encodeUInt 4 message.expirationDate
    ++ (encodeUInt 2 message.numberOfDecimalsInStrikePrice
    ++ (encodeUInt 1 message.putOrCall
    ++ (encodeUInt 1 message.rankingType)))))))))))))))))))

def decode (bytes : List UInt8) : Option (OrderBookDirectoryMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (symbol, bytes) ← Alpha.decode 32 bytes
  let (longName, bytes) ← Alpha.decode 32 bytes
  let (isin, bytes) ← Alpha.decode 12 bytes
  let (financialProduct, bytes) ← decodeUInt 1 bytes
  let (tradingCurrency, bytes) ← Alpha.decode 3 bytes
  let (numberOfDecimalsInPrice, bytes) ← decodeUInt 2 bytes
  let (numberOfDecimalsInNominalValue, bytes) ← decodeUInt 2 bytes
  let (oddLotSize, bytes) ← decodeUInt 4 bytes
  let (roundLotSize, bytes) ← decodeUInt 4 bytes
  let (blockLotSize, bytes) ← decodeUInt 4 bytes
  let (nominalValue, bytes) ← decodeUInt 8 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (underlyingOrderBookId, bytes) ← decodeUInt 4 bytes
  let (strikePrice, bytes) ← decodeUInt 4 bytes
  let (expirationDate, bytes) ← decodeUInt 4 bytes
  let (numberOfDecimalsInStrikePrice, bytes) ← decodeUInt 2 bytes
  let (putOrCall, bytes) ← decodeUInt 1 bytes
  let (rankingType, bytes) ← decodeUInt 1 bytes
  pure ({ nanoseconds, orderBookId, symbol, longName, isin, financialProduct, tradingCurrency, numberOfDecimalsInPrice, numberOfDecimalsInNominalValue, oddLotSize, roundLotSize, blockLotSize, nominalValue, reserved1, underlyingOrderBookId, strikePrice, expirationDate, numberOfDecimalsInStrikePrice, putOrCall, rankingType }, bytes)

@[simp] theorem encode_length (message : OrderBookDirectoryMessage) : (encode message).length = 129 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderBookDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderBookDirectoryMessage) (rest : List UInt8) :
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderBookDirectoryMessage

/-- Tick Size Table Entry Message: 24 bytes -/
structure TickSizeTableEntryMessage where
  nanoseconds : BitVec 32
  orderBookId : BitVec 32
  tickSize : BitVec 64
  priceFrom : BitVec 32
  priceTo : BitVec 32
  deriving DecidableEq, Repr

namespace TickSizeTableEntryMessage

def encode (message : TickSizeTableEntryMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.orderBookId
    ++ (encodeUInt 8 message.tickSize
    ++ (encodeUInt 4 message.priceFrom
    ++ (encodeUInt 4 message.priceTo))))

def decode (bytes : List UInt8) : Option (TickSizeTableEntryMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (tickSize, bytes) ← decodeUInt 8 bytes
  let (priceFrom, bytes) ← decodeUInt 4 bytes
  let (priceTo, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, orderBookId, tickSize, priceFrom, priceTo }, bytes)

@[simp] theorem encode_length (message : TickSizeTableEntryMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : TickSizeTableEntryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TickSizeTableEntryMessage) (rest : List UInt8) :
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

end TickSizeTableEntryMessage

/-- Short Sell Status Message: 9 bytes -/
structure ShortSellStatusMessage where
  nanoseconds : BitVec 32
  orderBookId : BitVec 32
  shortSaleRestriction : BitVec 8
  deriving DecidableEq, Repr

namespace ShortSellStatusMessage

def encode (message : ShortSellStatusMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.orderBookId
    ++ (encodeUInt 1 message.shortSaleRestriction))

def decode (bytes : List UInt8) : Option (ShortSellStatusMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (shortSaleRestriction, bytes) ← decodeUInt 1 bytes
  pure ({ nanoseconds, orderBookId, shortSaleRestriction }, bytes)

@[simp] theorem encode_length (message : ShortSellStatusMessage) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : ShortSellStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ShortSellStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ShortSellStatusMessage

/-- System Event Message: 5 bytes -/
structure SystemEventMessage where
  nanoseconds : BitVec 32
  eventCode : EventCode
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (EventCode.encode message.eventCode)

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (eventCode, bytes) ← EventCode.decode bytes
  pure ({ nanoseconds, eventCode }, bytes)

@[simp] theorem encode_length (message : SystemEventMessage) : (encode message).length = 5 := by
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
  rw [EventCode.decode_encode, some_bind]
  rfl

end SystemEventMessage

/-- Order Book State Message: 28 bytes -/
structure OrderBookStateMessage where
  nanoseconds : BitVec 32
  orderBookId : BitVec 32
  stateName : Alpha 20
  deriving DecidableEq, Repr

namespace OrderBookStateMessage

def encode (message : OrderBookStateMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.orderBookId
    ++ (Alpha.encode message.stateName))

def decode (bytes : List UInt8) : Option (OrderBookStateMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (stateName, bytes) ← Alpha.decode 20 bytes
  pure ({ nanoseconds, orderBookId, stateName }, bytes)

@[simp] theorem encode_length (message : OrderBookStateMessage) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderBookStateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderBookStateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderBookStateMessage

/-- Add Order Message: 44 bytes -/
structure AddOrderMessage where
  nanoseconds : BitVec 32
  orderId : BitVec 64
  orderBookId : BitVec 32
  side : Side
  rankingSequenceNumber : BitVec 32
  quantity : BitVec 64
  price : BitVec 32
  orderAttributes : BitVec 16
  lotType : BitVec 8
  rankingTime : BitVec 64
  deriving DecidableEq, Repr

namespace AddOrderMessage

def encode (message : AddOrderMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 8 message.orderId
    ++ (encodeUInt 4 message.orderBookId
    ++ (Side.encode message.side
    ++ (encodeUInt 4 message.rankingSequenceNumber
    ++ (encodeUInt 8 message.quantity
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 2 message.orderAttributes
    ++ (encodeUInt 1 message.lotType
    ++ (encodeUInt 8 message.rankingTime)))))))))

def decode (bytes : List UInt8) : Option (AddOrderMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (rankingSequenceNumber, bytes) ← decodeUInt 4 bytes
  let (quantity, bytes) ← decodeUInt 8 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (orderAttributes, bytes) ← decodeUInt 2 bytes
  let (lotType, bytes) ← decodeUInt 1 bytes
  let (rankingTime, bytes) ← decodeUInt 8 bytes
  pure ({ nanoseconds, orderId, orderBookId, side, rankingSequenceNumber, quantity, price, orderAttributes, lotType, rankingTime }, bytes)

@[simp] theorem encode_length (message : AddOrderMessage) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length]

theorem encode_length_pos (message : AddOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddOrderMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AddOrderMessage

/-- Order Executed Message: 51 bytes -/
structure OrderExecutedMessage where
  nanoseconds : BitVec 32
  orderId : BitVec 64
  orderBookId : BitVec 32
  side : Side
  executedQuantity : BitVec 64
  matchId : BitVec 64
  reserved4 : Alpha 4
  reserved14 : Alpha 14
  deriving DecidableEq, Repr

namespace OrderExecutedMessage

def encode (message : OrderExecutedMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 8 message.orderId
    ++ (encodeUInt 4 message.orderBookId
    ++ (Side.encode message.side
    ++ (encodeUInt 8 message.executedQuantity
    ++ (encodeUInt 8 message.matchId
    ++ (Alpha.encode message.reserved4
    ++ (Alpha.encode message.reserved14)))))))

def decode (bytes : List UInt8) : Option (OrderExecutedMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (executedQuantity, bytes) ← decodeUInt 8 bytes
  let (matchId, bytes) ← decodeUInt 8 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (reserved14, bytes) ← Alpha.decode 14 bytes
  pure ({ nanoseconds, orderId, orderBookId, side, executedQuantity, matchId, reserved4, reserved14 }, bytes)

@[simp] theorem encode_length (message : OrderExecutedMessage) : (encode message).length = 51 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderExecutedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderExecutedMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderExecutedMessage

/-- Order Executed With Price Message: 57 bytes -/
structure OrderExecutedWithPriceMessage where
  nanoseconds : BitVec 32
  orderId : BitVec 64
  orderBookId : BitVec 32
  side : Side
  executedQuantity : BitVec 64
  matchId : BitVec 64
  reserved18 : Alpha 18
  tradePrice : BitVec 32
  occurredAtCross : OccurredAtCross
  printable : Printable
  deriving DecidableEq, Repr

namespace OrderExecutedWithPriceMessage

def encode (message : OrderExecutedWithPriceMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 8 message.orderId
    ++ (encodeUInt 4 message.orderBookId
    ++ (Side.encode message.side
    ++ (encodeUInt 8 message.executedQuantity
    ++ (encodeUInt 8 message.matchId
    ++ (Alpha.encode message.reserved18
    ++ (encodeUInt 4 message.tradePrice
    ++ (OccurredAtCross.encode message.occurredAtCross
    ++ (Printable.encode message.printable)))))))))

def decode (bytes : List UInt8) : Option (OrderExecutedWithPriceMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (executedQuantity, bytes) ← decodeUInt 8 bytes
  let (matchId, bytes) ← decodeUInt 8 bytes
  let (reserved18, bytes) ← Alpha.decode 18 bytes
  let (tradePrice, bytes) ← decodeUInt 4 bytes
  let (occurredAtCross, bytes) ← OccurredAtCross.decode bytes
  let (printable_, bytes) ← Printable.decode bytes
  pure ({ nanoseconds, orderId, orderBookId, side, executedQuantity, matchId, reserved18, tradePrice, occurredAtCross, printable := printable_ }, bytes)

@[simp] theorem encode_length (message : OrderExecutedWithPriceMessage) : (encode message).length = 57 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length, Alpha.encode_length, OccurredAtCross.encode_length, Printable.encode_length]

theorem encode_length_pos (message : OrderExecutedWithPriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderExecutedWithPriceMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OccurredAtCross.decode_encode, some_bind]
  dsimp only
  rw [Printable.decode_encode, some_bind]
  rfl

end OrderExecutedWithPriceMessage

/-- Order Delete Message: 17 bytes -/
structure OrderDeleteMessage where
  nanoseconds : BitVec 32
  orderId : BitVec 64
  orderBookId : BitVec 32
  side : Side
  deriving DecidableEq, Repr

namespace OrderDeleteMessage

def encode (message : OrderDeleteMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 8 message.orderId
    ++ (encodeUInt 4 message.orderBookId
    ++ (Side.encode message.side)))

def decode (bytes : List UInt8) : Option (OrderDeleteMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  pure ({ nanoseconds, orderId, orderBookId, side }, bytes)

@[simp] theorem encode_length (message : OrderDeleteMessage) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length]

theorem encode_length_pos (message : OrderDeleteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderDeleteMessage) (rest : List UInt8) :
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

end OrderDeleteMessage

/-- Order Book Flush Message: 8 bytes -/
structure OrderBookFlushMessage where
  nanoseconds : BitVec 32
  orderBookId : BitVec 32
  deriving DecidableEq, Repr

namespace OrderBookFlushMessage

def encode (message : OrderBookFlushMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.orderBookId)

def decode (bytes : List UInt8) : Option (OrderBookFlushMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, orderBookId }, bytes)

@[simp] theorem encode_length (message : OrderBookFlushMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : OrderBookFlushMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderBookFlushMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderBookFlushMessage

/-- Trade Message: 49 bytes -/
structure TradeMessage where
  nanoseconds : BitVec 32
  matchId : BitVec 64
  comboGroupId : BitVec 32
  side : Side
  quantity : BitVec 64
  orderBookId : BitVec 32
  tradePrice : BitVec 32
  tradeReport : TradeReport
  reserved13 : Alpha 13
  printable : Printable
  occurredAtCross : OccurredAtCross
  deriving DecidableEq, Repr

namespace TradeMessage

def encode (message : TradeMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 8 message.matchId
    ++ (encodeUInt 4 message.comboGroupId
    ++ (Side.encode message.side
    ++ (encodeUInt 8 message.quantity
    ++ (encodeUInt 4 message.orderBookId
    ++ (encodeUInt 4 message.tradePrice
    ++ (TradeReport.encode message.tradeReport
    ++ (Alpha.encode message.reserved13
    ++ (Printable.encode message.printable
    ++ (OccurredAtCross.encode message.occurredAtCross))))))))))

def decode (bytes : List UInt8) : Option (TradeMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (matchId, bytes) ← decodeUInt 8 bytes
  let (comboGroupId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (quantity, bytes) ← decodeUInt 8 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (tradePrice, bytes) ← decodeUInt 4 bytes
  let (tradeReport, bytes) ← TradeReport.decode bytes
  let (reserved13, bytes) ← Alpha.decode 13 bytes
  let (printable_, bytes) ← Printable.decode bytes
  let (occurredAtCross, bytes) ← OccurredAtCross.decode bytes
  pure ({ nanoseconds, matchId, comboGroupId, side, quantity, orderBookId, tradePrice, tradeReport, reserved13, printable := printable_, occurredAtCross }, bytes)

@[simp] theorem encode_length (message : TradeMessage) : (encode message).length = 49 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length, TradeReport.encode_length, Alpha.encode_length, Printable.encode_length, OccurredAtCross.encode_length]

theorem encode_length_pos (message : TradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, TradeReport.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Printable.decode_encode, some_bind]
  dsimp only
  rw [OccurredAtCross.decode_encode, some_bind]
  rfl

end TradeMessage

/-- Equilibrium Price Update Message: 52 bytes -/
structure EquilibriumPriceUpdateMessage where
  nanoseconds : BitVec 32
  orderBookId : BitVec 32
  availableBidQuantityAtEquilibriumPrice : BitVec 64
  availableAskQuantityAtEquilibriumPrice : BitVec 64
  equilibriumPrice : BitVec 32
  bestBidPrice : BitVec 32
  bestAskPrice : BitVec 32
  bestBidQuantity : BitVec 64
  bestAskQuantity : BitVec 64
  deriving DecidableEq, Repr

namespace EquilibriumPriceUpdateMessage

def encode (message : EquilibriumPriceUpdateMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.orderBookId
    ++ (encodeUInt 8 message.availableBidQuantityAtEquilibriumPrice
    ++ (encodeUInt 8 message.availableAskQuantityAtEquilibriumPrice
    ++ (encodeUInt 4 message.equilibriumPrice
    ++ (encodeUInt 4 message.bestBidPrice
    ++ (encodeUInt 4 message.bestAskPrice
    ++ (encodeUInt 8 message.bestBidQuantity
    ++ (encodeUInt 8 message.bestAskQuantity))))))))

def decode (bytes : List UInt8) : Option (EquilibriumPriceUpdateMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (availableBidQuantityAtEquilibriumPrice, bytes) ← decodeUInt 8 bytes
  let (availableAskQuantityAtEquilibriumPrice, bytes) ← decodeUInt 8 bytes
  let (equilibriumPrice, bytes) ← decodeUInt 4 bytes
  let (bestBidPrice, bytes) ← decodeUInt 4 bytes
  let (bestAskPrice, bytes) ← decodeUInt 4 bytes
  let (bestBidQuantity, bytes) ← decodeUInt 8 bytes
  let (bestAskQuantity, bytes) ← decodeUInt 8 bytes
  pure ({ nanoseconds, orderBookId, availableBidQuantityAtEquilibriumPrice, availableAskQuantityAtEquilibriumPrice, equilibriumPrice, bestBidPrice, bestAskPrice, bestBidQuantity, bestAskQuantity }, bytes)

@[simp] theorem encode_length (message : EquilibriumPriceUpdateMessage) : (encode message).length = 52 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : EquilibriumPriceUpdateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EquilibriumPriceUpdateMessage) (rest : List UInt8) :
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end EquilibriumPriceUpdateMessage

/-- Any Sequenced Message, selected by Sequenced Message Type -/
inductive SequencedMessage where
  | secondsMessage (message : SecondsMessage) -- "T" 0x54
  | orderBookDirectoryMessage (message : OrderBookDirectoryMessage) -- "R" 0x52
  | tickSizeTableEntryMessage (message : TickSizeTableEntryMessage) -- "L" 0x4C
  | shortSellStatusMessage (message : ShortSellStatusMessage) -- "V" 0x56
  | systemEventMessage (message : SystemEventMessage) -- "S" 0x53
  | orderBookStateMessage (message : OrderBookStateMessage) -- "O" 0x4F
  | addOrderMessage (message : AddOrderMessage) -- "A" 0x41
  | orderExecutedMessage (message : OrderExecutedMessage) -- "E" 0x45
  | orderExecutedWithPriceMessage (message : OrderExecutedWithPriceMessage) -- "C" 0x43
  | orderDeleteMessage (message : OrderDeleteMessage) -- "D" 0x44
  | orderBookFlushMessage (message : OrderBookFlushMessage) -- "Y" 0x59
  | tradeMessage (message : TradeMessage) -- "P" 0x50
  | equilibriumPriceUpdateMessage (message : EquilibriumPriceUpdateMessage) -- "Z" 0x5A
  deriving DecidableEq, Repr

namespace SequencedMessage

/-- The Sequenced Message Type each message is sent under -/
def tag : SequencedMessage → BitVec 8
  | .secondsMessage _ => 84
  | .orderBookDirectoryMessage _ => 82
  | .tickSizeTableEntryMessage _ => 76
  | .shortSellStatusMessage _ => 86
  | .systemEventMessage _ => 83
  | .orderBookStateMessage _ => 79
  | .addOrderMessage _ => 65
  | .orderExecutedMessage _ => 69
  | .orderExecutedWithPriceMessage _ => 67
  | .orderDeleteMessage _ => 68
  | .orderBookFlushMessage _ => 89
  | .tradeMessage _ => 80
  | .equilibriumPriceUpdateMessage _ => 90

def encode : SequencedMessage → List UInt8
  | .secondsMessage message => SecondsMessage.encode message
  | .orderBookDirectoryMessage message => OrderBookDirectoryMessage.encode message
  | .tickSizeTableEntryMessage message => TickSizeTableEntryMessage.encode message
  | .shortSellStatusMessage message => ShortSellStatusMessage.encode message
  | .systemEventMessage message => SystemEventMessage.encode message
  | .orderBookStateMessage message => OrderBookStateMessage.encode message
  | .addOrderMessage message => AddOrderMessage.encode message
  | .orderExecutedMessage message => OrderExecutedMessage.encode message
  | .orderExecutedWithPriceMessage message => OrderExecutedWithPriceMessage.encode message
  | .orderDeleteMessage message => OrderDeleteMessage.encode message
  | .orderBookFlushMessage message => OrderBookFlushMessage.encode message
  | .tradeMessage message => TradeMessage.encode message
  | .equilibriumPriceUpdateMessage message => EquilibriumPriceUpdateMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : SequencedMessage) : (encode message).length ≤ 129 := by
  cases message with
  | secondsMessage inner =>
    simp only [encode, SecondsMessage.encode_length]
    omega
  | orderBookDirectoryMessage inner =>
    simp only [encode, OrderBookDirectoryMessage.encode_length]
    omega
  | tickSizeTableEntryMessage inner =>
    simp only [encode, TickSizeTableEntryMessage.encode_length]
    omega
  | shortSellStatusMessage inner =>
    simp only [encode, ShortSellStatusMessage.encode_length]
    omega
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega
  | orderBookStateMessage inner =>
    simp only [encode, OrderBookStateMessage.encode_length]
    omega
  | addOrderMessage inner =>
    simp only [encode, AddOrderMessage.encode_length]
    omega
  | orderExecutedMessage inner =>
    simp only [encode, OrderExecutedMessage.encode_length]
    omega
  | orderExecutedWithPriceMessage inner =>
    simp only [encode, OrderExecutedWithPriceMessage.encode_length]
    omega
  | orderDeleteMessage inner =>
    simp only [encode, OrderDeleteMessage.encode_length]
    omega
  | orderBookFlushMessage inner =>
    simp only [encode, OrderBookFlushMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [encode, TradeMessage.encode_length]
    omega
  | equilibriumPriceUpdateMessage inner =>
    simp only [encode, EquilibriumPriceUpdateMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (SequencedMessage × List UInt8) :=
  if tag = 84 then (SecondsMessage.decode bytes).map fun (message, rest) => (.secondsMessage message, rest)
  else if tag = 82 then (OrderBookDirectoryMessage.decode bytes).map fun (message, rest) => (.orderBookDirectoryMessage message, rest)
  else if tag = 76 then (TickSizeTableEntryMessage.decode bytes).map fun (message, rest) => (.tickSizeTableEntryMessage message, rest)
  else if tag = 86 then (ShortSellStatusMessage.decode bytes).map fun (message, rest) => (.shortSellStatusMessage message, rest)
  else if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 79 then (OrderBookStateMessage.decode bytes).map fun (message, rest) => (.orderBookStateMessage message, rest)
  else if tag = 65 then (AddOrderMessage.decode bytes).map fun (message, rest) => (.addOrderMessage message, rest)
  else if tag = 69 then (OrderExecutedMessage.decode bytes).map fun (message, rest) => (.orderExecutedMessage message, rest)
  else if tag = 67 then (OrderExecutedWithPriceMessage.decode bytes).map fun (message, rest) => (.orderExecutedWithPriceMessage message, rest)
  else if tag = 68 then (OrderDeleteMessage.decode bytes).map fun (message, rest) => (.orderDeleteMessage message, rest)
  else if tag = 89 then (OrderBookFlushMessage.decode bytes).map fun (message, rest) => (.orderBookFlushMessage message, rest)
  else if tag = 80 then (TradeMessage.decode bytes).map fun (message, rest) => (.tradeMessage message, rest)
  else if tag = 90 then (EquilibriumPriceUpdateMessage.decode bytes).map fun (message, rest) => (.equilibriumPriceUpdateMessage message, rest)
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
theorem encode_length_le (message : SequencedDataPacket) : (encode message).length ≤ 130 := by
  unfold encode
  cases message.sequencedMessage with
  | secondsMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, SecondsMessage.encode_length]
    omega
  | orderBookDirectoryMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderBookDirectoryMessage.encode_length]
    omega
  | tickSizeTableEntryMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, TickSizeTableEntryMessage.encode_length]
    omega
  | shortSellStatusMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, ShortSellStatusMessage.encode_length]
    omega
  | systemEventMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, SystemEventMessage.encode_length]
    omega
  | orderBookStateMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderBookStateMessage.encode_length]
    omega
  | addOrderMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, AddOrderMessage.encode_length]
    omega
  | orderExecutedMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderExecutedMessage.encode_length]
    omega
  | orderExecutedWithPriceMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderExecutedWithPriceMessage.encode_length]
    omega
  | orderDeleteMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderDeleteMessage.encode_length]
    omega
  | orderBookFlushMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderBookFlushMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, TradeMessage.encode_length]
    omega
  | equilibriumPriceUpdateMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, EquilibriumPriceUpdateMessage.encode_length]
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
theorem encode_length_le (message : ServerPayload) : (encode message).length ≤ 65404 := by
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

end Omi.AixAixmarketGeniuminetItchV30Server
