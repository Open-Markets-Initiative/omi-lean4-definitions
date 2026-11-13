import Wire

/-!
# Philippine Stock Exchange Pse Equities Itch Index v2.3

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

License: MIT No Attribution
-/

namespace Omi.PsePseequitiesIndexItchV23

/-- Event Code: one byte code -/
def EventCode.codes : List UInt8 :=
  [0x4F, 0x53, 0x52, 0x51, 0x41, 0x42, 0x4C, 0x4A, 0x50, 0x4D, 0x45, 0x43]

inductive EventCode where
  | startOfMessages -- Start Of Messages
  | startOfSystemHours -- Start Of System Hours
  | preOpenNoCancellationPeriod -- Pre Open No Cancellation Period
  | startOfMarketHours -- Start Of Market Hours
  | scheduledBreakBegins -- Scheduled Break Begins
  | scheduledBreakEnds -- Scheduled Break Ends
  | preCloseCommences -- Pre Close Commences
  | preCloseNoCancellationPeriod -- Pre Close No Cancellation Period
  | tradingAtLast -- Trading At Last
  | endOfMarketHours -- End Of Market Hours
  | endOfTrading -- End Of Trading
  | endOfSystemMessages -- End Of System Messages
  | unlisted (byte : { byte : UInt8 // byte ∉ EventCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventCode

def toByte : EventCode → UInt8
  | .startOfMessages => 0x4F
  | .startOfSystemHours => 0x53
  | .preOpenNoCancellationPeriod => 0x52
  | .startOfMarketHours => 0x51
  | .scheduledBreakBegins => 0x41
  | .scheduledBreakEnds => 0x42
  | .preCloseCommences => 0x4C
  | .preCloseNoCancellationPeriod => 0x4A
  | .tradingAtLast => 0x50
  | .endOfMarketHours => 0x4D
  | .endOfTrading => 0x45
  | .endOfSystemMessages => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventCode :=
  if byte = 0x4F then .startOfMessages
  else if byte = 0x53 then .startOfSystemHours
  else if byte = 0x52 then .preOpenNoCancellationPeriod
  else if byte = 0x51 then .startOfMarketHours
  else if byte = 0x41 then .scheduledBreakBegins
  else if byte = 0x42 then .scheduledBreakEnds
  else if byte = 0x4C then .preCloseCommences
  else if byte = 0x4A then .preCloseNoCancellationPeriod
  else if byte = 0x50 then .tradingAtLast
  else if byte = 0x4D then .endOfMarketHours
  else if byte = 0x45 then .endOfTrading
  else .endOfSystemMessages

def ofByte (byte : UInt8) : EventCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventCode) : ofByte value.toByte = value := by
  cases value with
  | startOfMessages => decide
  | startOfSystemHours => decide
  | preOpenNoCancellationPeriod => decide
  | startOfMarketHours => decide
  | scheduledBreakBegins => decide
  | scheduledBreakEnds => decide
  | preCloseCommences => decide
  | preCloseNoCancellationPeriod => decide
  | tradingAtLast => decide
  | endOfMarketHours => decide
  | endOfTrading => decide
  | endOfSystemMessages => decide
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

/-- Price Type: one byte code -/
def PriceType.codes : List UInt8 :=
  [0x55, 0x50]

inductive PriceType where
  | perUnit -- Per Unit
  | percentage -- Percentage
  | unlisted (byte : { byte : UInt8 // byte ∉ PriceType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PriceType

def toByte : PriceType → UInt8
  | .perUnit => 0x55
  | .percentage => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PriceType :=
  if byte = 0x55 then .perUnit
  else .percentage

def ofByte (byte : UInt8) : PriceType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PriceType) : ofByte value.toByte = value := by
  cases value with
  | perUnit => decide
  | percentage => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PriceType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PriceType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PriceType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : PriceType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : PriceType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PriceType

/-- Instrument Type: one byte code -/
def InstrumentType.codes : List UInt8 :=
  [0x43, 0x50, 0x57, 0x45, 0x44, 0x49]

inductive InstrumentType where
  | commonStock -- Common Stock
  | preferredStock -- Preferred Stock
  | warrant -- Warrant
  | etf -- Etf
  | pdr -- Pdr
  | index -- Index
  | unlisted (byte : { byte : UInt8 // byte ∉ InstrumentType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InstrumentType

def toByte : InstrumentType → UInt8
  | .commonStock => 0x43
  | .preferredStock => 0x50
  | .warrant => 0x57
  | .etf => 0x45
  | .pdr => 0x44
  | .index => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : InstrumentType :=
  if byte = 0x43 then .commonStock
  else if byte = 0x50 then .preferredStock
  else if byte = 0x57 then .warrant
  else if byte = 0x45 then .etf
  else if byte = 0x44 then .pdr
  else .index

def ofByte (byte : UInt8) : InstrumentType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InstrumentType) : ofByte value.toByte = value := by
  cases value with
  | commonStock => decide
  | preferredStock => decide
  | warrant => decide
  | etf => decide
  | pdr => decide
  | index => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : InstrumentType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (InstrumentType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : InstrumentType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : InstrumentType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : InstrumentType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end InstrumentType

/-- Time Stamp Seconds Message: 4 bytes -/
structure TimeStampSecondsMessage where
  second : BitVec 32
  deriving DecidableEq, Repr

namespace TimeStampSecondsMessage

def encode (message : TimeStampSecondsMessage) : List UInt8 :=
  encodeUInt 4 message.second

def decode (bytes : List UInt8) : Option (TimeStampSecondsMessage × List UInt8) := do
  let (second, bytes) ← decodeUInt 4 bytes
  pure ({ second }, bytes)

@[simp] theorem encode_length (message : TimeStampSecondsMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : TimeStampSecondsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TimeStampSecondsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TimeStampSecondsMessage

/-- System Event Message: 17 bytes -/
structure SystemEventMessage where
  timestamp : BitVec 32
  group : Alpha 8
  eventCode : EventCode
  orderbook : BitVec 32
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  encodeUInt 4 message.timestamp
    ++ (Alpha.encode message.group
    ++ (EventCode.encode message.eventCode
    ++ (encodeUInt 4 message.orderbook)))

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 4 bytes
  let (group, bytes) ← Alpha.decode 8 bytes
  let (eventCode, bytes) ← EventCode.decode bytes
  let (orderbook, bytes) ← decodeUInt 4 bytes
  pure ({ timestamp, group, eventCode, orderbook }, bytes)

@[simp] theorem encode_length (message : SystemEventMessage) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, EventCode.encode_length]

theorem encode_length_pos (message : SystemEventMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemEventMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, EventCode.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SystemEventMessage

/-- Orderbook Directory Message: 89 bytes -/
structure OrderbookDirectoryMessage where
  timestamp : BitVec 32
  orderbook : BitVec 32
  priceType : PriceType
  isin : Alpha 12
  secCode : Alpha 12
  currency : Alpha 3
  group : Alpha 8
  lotSize : BitVec 64
  quantityTickSizeTableId : BitVec 32
  priceTickSizeTableId : BitVec 32
  priceDecimals : BitVec 32
  delistingDate : BitVec 32
  delistingTime : BitVec 32
  instrumentType : InstrumentType
  shares : BitVec 64
  productCode : Alpha 8
  deriving DecidableEq, Repr

namespace OrderbookDirectoryMessage

def encode (message : OrderbookDirectoryMessage) : List UInt8 :=
  encodeUInt 4 message.timestamp
    ++ (encodeUInt 4 message.orderbook
    ++ (PriceType.encode message.priceType
    ++ (Alpha.encode message.isin
    ++ (Alpha.encode message.secCode
    ++ (Alpha.encode message.currency
    ++ (Alpha.encode message.group
    ++ (encodeUInt 8 message.lotSize
    ++ (encodeUInt 4 message.quantityTickSizeTableId
    ++ (encodeUInt 4 message.priceTickSizeTableId
    ++ (encodeUInt 4 message.priceDecimals
    ++ (encodeUInt 4 message.delistingDate
    ++ (encodeUInt 4 message.delistingTime
    ++ (InstrumentType.encode message.instrumentType
    ++ (encodeUInt 8 message.shares
    ++ (Alpha.encode message.productCode)))))))))))))))

def decode (bytes : List UInt8) : Option (OrderbookDirectoryMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 4 bytes
  let (orderbook, bytes) ← decodeUInt 4 bytes
  let (priceType, bytes) ← PriceType.decode bytes
  let (isin, bytes) ← Alpha.decode 12 bytes
  let (secCode, bytes) ← Alpha.decode 12 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (group, bytes) ← Alpha.decode 8 bytes
  let (lotSize, bytes) ← decodeUInt 8 bytes
  let (quantityTickSizeTableId, bytes) ← decodeUInt 4 bytes
  let (priceTickSizeTableId, bytes) ← decodeUInt 4 bytes
  let (priceDecimals, bytes) ← decodeUInt 4 bytes
  let (delistingDate, bytes) ← decodeUInt 4 bytes
  let (delistingTime, bytes) ← decodeUInt 4 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  let (shares, bytes) ← decodeUInt 8 bytes
  let (productCode, bytes) ← Alpha.decode 8 bytes
  pure ({ timestamp, orderbook, priceType, isin, secCode, currency, group, lotSize, quantityTickSizeTableId, priceTickSizeTableId, priceDecimals, delistingDate, delistingTime, instrumentType, shares, productCode }, bytes)

@[simp] theorem encode_length (message : OrderbookDirectoryMessage) : (encode message).length = 89 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, PriceType.encode_length, Alpha.encode_length, InstrumentType.encode_length]

theorem encode_length_pos (message : OrderbookDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderbookDirectoryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, PriceType.decode_encode, some_bind]
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
  rw [List.append_assoc, InstrumentType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderbookDirectoryMessage

/-- Index Member Directory Message: 20 bytes -/
structure IndexMemberDirectoryMessage where
  timestamp : BitVec 32
  indexOrderbook : BitVec 32
  memberOrderbook : BitVec 32
  indexMemberWeight : BitVec 64
  deriving DecidableEq, Repr

namespace IndexMemberDirectoryMessage

def encode (message : IndexMemberDirectoryMessage) : List UInt8 :=
  encodeUInt 4 message.timestamp
    ++ (encodeUInt 4 message.indexOrderbook
    ++ (encodeUInt 4 message.memberOrderbook
    ++ (encodeUInt 8 message.indexMemberWeight)))

def decode (bytes : List UInt8) : Option (IndexMemberDirectoryMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 4 bytes
  let (indexOrderbook, bytes) ← decodeUInt 4 bytes
  let (memberOrderbook, bytes) ← decodeUInt 4 bytes
  let (indexMemberWeight, bytes) ← decodeUInt 8 bytes
  pure ({ timestamp, indexOrderbook, memberOrderbook, indexMemberWeight }, bytes)

@[simp] theorem encode_length (message : IndexMemberDirectoryMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : IndexMemberDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IndexMemberDirectoryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end IndexMemberDirectoryMessage

/-- Index Value Message: 16 bytes -/
structure IndexValueMessage where
  timestamp : BitVec 32
  indexOrderbook : BitVec 32
  value : BitVec 64
  deriving DecidableEq, Repr

namespace IndexValueMessage

def encode (message : IndexValueMessage) : List UInt8 :=
  encodeUInt 4 message.timestamp
    ++ (encodeUInt 4 message.indexOrderbook
    ++ (encodeUInt 8 message.value))

def decode (bytes : List UInt8) : Option (IndexValueMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 4 bytes
  let (indexOrderbook, bytes) ← decodeUInt 4 bytes
  let (value, bytes) ← decodeUInt 8 bytes
  pure ({ timestamp, indexOrderbook, value }, bytes)

@[simp] theorem encode_length (message : IndexValueMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : IndexValueMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IndexValueMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end IndexValueMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | timeStampSecondsMessage (message : TimeStampSecondsMessage) -- "T" 0x54
  | systemEventMessage (message : SystemEventMessage) -- "S" 0x53
  | orderbookDirectoryMessage (message : OrderbookDirectoryMessage) -- "R" 0x52
  | indexMemberDirectoryMessage (message : IndexMemberDirectoryMessage) -- "Y" 0x59
  | indexValueMessage (message : IndexValueMessage) -- "Z" 0x5A
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .timeStampSecondsMessage _ => 84
  | .systemEventMessage _ => 83
  | .orderbookDirectoryMessage _ => 82
  | .indexMemberDirectoryMessage _ => 89
  | .indexValueMessage _ => 90

def encode : Payload → List UInt8
  | .timeStampSecondsMessage message => TimeStampSecondsMessage.encode message
  | .systemEventMessage message => SystemEventMessage.encode message
  | .orderbookDirectoryMessage message => OrderbookDirectoryMessage.encode message
  | .indexMemberDirectoryMessage message => IndexMemberDirectoryMessage.encode message
  | .indexValueMessage message => IndexValueMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 89 := by
  cases message with
  | timeStampSecondsMessage inner =>
    simp only [encode, TimeStampSecondsMessage.encode_length]
    omega
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega
  | orderbookDirectoryMessage inner =>
    simp only [encode, OrderbookDirectoryMessage.encode_length]
    omega
  | indexMemberDirectoryMessage inner =>
    simp only [encode, IndexMemberDirectoryMessage.encode_length]
    omega
  | indexValueMessage inner =>
    simp only [encode, IndexValueMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 84 then (TimeStampSecondsMessage.decode bytes).map fun (message, rest) => (.timeStampSecondsMessage message, rest)
  else if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 82 then (OrderbookDirectoryMessage.decode bytes).map fun (message, rest) => (.orderbookDirectoryMessage message, rest)
  else if tag = 89 then (IndexMemberDirectoryMessage.decode bytes).map fun (message, rest) => (.indexMemberDirectoryMessage message, rest)
  else if tag = 90 then (IndexValueMessage.decode bytes).map fun (message, rest) => (.indexValueMessage message, rest)
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

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 0 < 256 ^ 2 := by
  unfold encodeBody
  cases message.payload with
  | timeStampSecondsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TimeStampSecondsMessage.encode_length]
    omega
  | systemEventMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SystemEventMessage.encode_length]
    omega
  | orderbookDirectoryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderbookDirectoryMessage.encode_length]
    omega
  | indexMemberDirectoryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, IndexMemberDirectoryMessage.encode_length]
    omega
  | indexValueMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, IndexValueMessage.encode_length]
    omega

/-- Size rule: Message Length counts the bytes after it, so it is written from the body and checked on decode -/
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

end Omi.PsePseequitiesIndexItchV23
