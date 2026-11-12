import Wire

/-!
# Bolsa Mexicana de Valores Bmv Market Data Product 34 v1.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.

License: MIT No Attribution
-/

namespace Omi.BmvBmvmarketdataProduct34IntraV11

/-- Origin: one byte code -/
def Origin.codes : List UInt8 :=
  [0x4D, 0x49, 0x41]

inductive Origin where
  | bmv -- Bmv
  | biva -- Biva
  | both -- Both
  | unlisted (byte : { byte : UInt8 // byte ∉ Origin.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Origin

def toByte : Origin → UInt8
  | .bmv => 0x4D
  | .biva => 0x49
  | .both => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Origin :=
  if byte = 0x4D then .bmv
  else if byte = 0x49 then .biva
  else .both

def ofByte (byte : UInt8) : Origin :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Origin) : ofByte value.toByte = value := by
  cases value with
  | bmv => decide
  | biva => decide
  | both => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Origin) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Origin × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Origin) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Origin) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Origin) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Origin

/-- Market: one byte code -/
def Market.codes : List UInt8 :=
  [0x4C, 0x47, 0x54, 0x46]

inductive Market where
  | local_ -- Local
  | global -- Global
  | etFs -- Et Fs
  | reiTs -- Rei Ts
  | unlisted (byte : { byte : UInt8 // byte ∉ Market.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Market

def toByte : Market → UInt8
  | .local_ => 0x4C
  | .global => 0x47
  | .etFs => 0x54
  | .reiTs => 0x46
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Market :=
  if byte = 0x4C then .local_
  else if byte = 0x47 then .global
  else if byte = 0x54 then .etFs
  else .reiTs

def ofByte (byte : UInt8) : Market :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Market) : ofByte value.toByte = value := by
  cases value with
  | local_ => decide
  | global => decide
  | etFs => decide
  | reiTs => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Market) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Market × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Market) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Market) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Market) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Market

/-- Big Picture Message: 37 bytes -/
structure BigPictureMessage where
  origin : Origin
  trades : BitVec 32
  volume : BitVec 64
  tradedValue : BitVec 64
  marketShareAmount : BitVec 32
  marketShareTrades : BitVec 32
  market : Market
  sector : BitVec 8
  instrumentNumber : BitVec 32
  indices : Alpha 2
  deriving DecidableEq, Repr

namespace BigPictureMessage

def encode (message : BigPictureMessage) : List UInt8 :=
  Origin.encode message.origin
    ++ (encodeUInt 4 message.trades
    ++ (encodeUInt 8 message.volume
    ++ (encodeUInt 8 message.tradedValue
    ++ (encodeUInt 4 message.marketShareAmount
    ++ (encodeUInt 4 message.marketShareTrades
    ++ (Market.encode message.market
    ++ (encodeUInt 1 message.sector
    ++ (encodeUInt 4 message.instrumentNumber
    ++ (Alpha.encode message.indices)))))))))

def decode (bytes : List UInt8) : Option (BigPictureMessage × List UInt8) := do
  let (origin, bytes) ← Origin.decode bytes
  let (trades, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 8 bytes
  let (tradedValue, bytes) ← decodeUInt 8 bytes
  let (marketShareAmount, bytes) ← decodeUInt 4 bytes
  let (marketShareTrades, bytes) ← decodeUInt 4 bytes
  let (market, bytes) ← Market.decode bytes
  let (sector, bytes) ← decodeUInt 1 bytes
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (indices, bytes) ← Alpha.decode 2 bytes
  pure ({ origin, trades, volume, tradedValue, marketShareAmount, marketShareTrades, market, sector, instrumentNumber, indices }, bytes)

@[simp] theorem encode_length (message : BigPictureMessage) : (encode message).length = 37 := by
  unfold encode
  simp only [List.length_append, Origin.encode_length, encodeUInt_length, Market.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : BigPictureMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BigPictureMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Origin.decode_encode, some_bind]
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
  rw [List.append_assoc, Market.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BigPictureMessage

/-- Benchmark Trade Message: 25 bytes -/
structure BenchmarkTradeMessage where
  origin : Origin
  averageVolume : BitVec 64
  averageTradedValue : BitVec 64
  market : Market
  sector : BitVec 8
  instrumentNumber : BitVec 32
  indices : Alpha 2
  deriving DecidableEq, Repr

namespace BenchmarkTradeMessage

def encode (message : BenchmarkTradeMessage) : List UInt8 :=
  Origin.encode message.origin
    ++ (encodeUInt 8 message.averageVolume
    ++ (encodeUInt 8 message.averageTradedValue
    ++ (Market.encode message.market
    ++ (encodeUInt 1 message.sector
    ++ (encodeUInt 4 message.instrumentNumber
    ++ (Alpha.encode message.indices))))))

def decode (bytes : List UInt8) : Option (BenchmarkTradeMessage × List UInt8) := do
  let (origin, bytes) ← Origin.decode bytes
  let (averageVolume, bytes) ← decodeUInt 8 bytes
  let (averageTradedValue, bytes) ← decodeUInt 8 bytes
  let (market, bytes) ← Market.decode bytes
  let (sector, bytes) ← decodeUInt 1 bytes
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (indices, bytes) ← Alpha.decode 2 bytes
  pure ({ origin, averageVolume, averageTradedValue, market, sector, instrumentNumber, indices }, bytes)

@[simp] theorem encode_length (message : BenchmarkTradeMessage) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, Origin.encode_length, encodeUInt_length, Market.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : BenchmarkTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BenchmarkTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Origin.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Market.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BenchmarkTradeMessage

/-- Hour Tracker Message: 53 bytes -/
structure HourTrackerMessage where
  origin : Origin
  trades : BitVec 32
  volume : BitVec 64
  tradedValue : BitVec 64
  spreadMxn : BitVec 32
  spreadBasisPoints : BitVec 32
  averageVolume : BitVec 64
  averageTradedValue : BitVec 64
  market : Market
  sector : BitVec 8
  instrumentNumber : BitVec 32
  indices : Alpha 2
  deriving DecidableEq, Repr

namespace HourTrackerMessage

def encode (message : HourTrackerMessage) : List UInt8 :=
  Origin.encode message.origin
    ++ (encodeUInt 4 message.trades
    ++ (encodeUInt 8 message.volume
    ++ (encodeUInt 8 message.tradedValue
    ++ (encodeUInt 4 message.spreadMxn
    ++ (encodeUInt 4 message.spreadBasisPoints
    ++ (encodeUInt 8 message.averageVolume
    ++ (encodeUInt 8 message.averageTradedValue
    ++ (Market.encode message.market
    ++ (encodeUInt 1 message.sector
    ++ (encodeUInt 4 message.instrumentNumber
    ++ (Alpha.encode message.indices)))))))))))

def decode (bytes : List UInt8) : Option (HourTrackerMessage × List UInt8) := do
  let (origin, bytes) ← Origin.decode bytes
  let (trades, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 8 bytes
  let (tradedValue, bytes) ← decodeUInt 8 bytes
  let (spreadMxn, bytes) ← decodeUInt 4 bytes
  let (spreadBasisPoints, bytes) ← decodeUInt 4 bytes
  let (averageVolume, bytes) ← decodeUInt 8 bytes
  let (averageTradedValue, bytes) ← decodeUInt 8 bytes
  let (market, bytes) ← Market.decode bytes
  let (sector, bytes) ← decodeUInt 1 bytes
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (indices, bytes) ← Alpha.decode 2 bytes
  pure ({ origin, trades, volume, tradedValue, spreadMxn, spreadBasisPoints, averageVolume, averageTradedValue, market, sector, instrumentNumber, indices }, bytes)

@[simp] theorem encode_length (message : HourTrackerMessage) : (encode message).length = 53 := by
  unfold encode
  simp only [List.length_append, Origin.encode_length, encodeUInt_length, Market.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : HourTrackerMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : HourTrackerMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Origin.decode_encode, some_bind]
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
  rw [List.append_assoc, Market.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end HourTrackerMessage

/-- Message Ratio Message: 37 bytes -/
structure MessageRatioMessage where
  origin : Origin
  messages : BitVec 32
  messagesBid : BitVec 32
  messagesAsk : BitVec 32
  messagesModified : BitVec 32
  messagesCanceled : BitVec 32
  trades : BitVec 32
  ratio : BitVec 32
  market : Market
  sector : BitVec 8
  instrumentNumber : BitVec 32
  indices : Alpha 2
  deriving DecidableEq, Repr

namespace MessageRatioMessage

def encode (message : MessageRatioMessage) : List UInt8 :=
  Origin.encode message.origin
    ++ (encodeUInt 4 message.messages
    ++ (encodeUInt 4 message.messagesBid
    ++ (encodeUInt 4 message.messagesAsk
    ++ (encodeUInt 4 message.messagesModified
    ++ (encodeUInt 4 message.messagesCanceled
    ++ (encodeUInt 4 message.trades
    ++ (encodeUInt 4 message.ratio
    ++ (Market.encode message.market
    ++ (encodeUInt 1 message.sector
    ++ (encodeUInt 4 message.instrumentNumber
    ++ (Alpha.encode message.indices)))))))))))

def decode (bytes : List UInt8) : Option (MessageRatioMessage × List UInt8) := do
  let (origin, bytes) ← Origin.decode bytes
  let (messages, bytes) ← decodeUInt 4 bytes
  let (messagesBid, bytes) ← decodeUInt 4 bytes
  let (messagesAsk, bytes) ← decodeUInt 4 bytes
  let (messagesModified, bytes) ← decodeUInt 4 bytes
  let (messagesCanceled, bytes) ← decodeUInt 4 bytes
  let (trades, bytes) ← decodeUInt 4 bytes
  let (ratio, bytes) ← decodeUInt 4 bytes
  let (market, bytes) ← Market.decode bytes
  let (sector, bytes) ← decodeUInt 1 bytes
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (indices, bytes) ← Alpha.decode 2 bytes
  pure ({ origin, messages, messagesBid, messagesAsk, messagesModified, messagesCanceled, trades, ratio, market, sector, instrumentNumber, indices }, bytes)

@[simp] theorem encode_length (message : MessageRatioMessage) : (encode message).length = 37 := by
  unfold encode
  simp only [List.length_append, Origin.encode_length, encodeUInt_length, Market.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : MessageRatioMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MessageRatioMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Origin.decode_encode, some_bind]
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
  rw [List.append_assoc, Market.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MessageRatioMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | bigPictureMessage (message : BigPictureMessage) -- 39
  | benchmarkTradeMessage (message : BenchmarkTradeMessage) -- 58
  | hourTrackerMessage (message : HourTrackerMessage) -- 47
  | messageRatioMessage (message : MessageRatioMessage) -- 125
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .bigPictureMessage _ => 39
  | .benchmarkTradeMessage _ => 58
  | .hourTrackerMessage _ => 47
  | .messageRatioMessage _ => 125

def encode : Payload → List UInt8
  | .bigPictureMessage message => BigPictureMessage.encode message
  | .benchmarkTradeMessage message => BenchmarkTradeMessage.encode message
  | .hourTrackerMessage message => HourTrackerMessage.encode message
  | .messageRatioMessage message => MessageRatioMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 53 := by
  cases message with
  | bigPictureMessage inner =>
    simp only [encode, BigPictureMessage.encode_length]
    omega
  | benchmarkTradeMessage inner =>
    simp only [encode, BenchmarkTradeMessage.encode_length]
    omega
  | hourTrackerMessage inner =>
    simp only [encode, HourTrackerMessage.encode_length]
    omega
  | messageRatioMessage inner =>
    simp only [encode, MessageRatioMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 39 then (BigPictureMessage.decode bytes).map fun (message, rest) => (.bigPictureMessage message, rest)
  else if tag = 58 then (BenchmarkTradeMessage.decode bytes).map fun (message, rest) => (.benchmarkTradeMessage message, rest)
  else if tag = 47 then (HourTrackerMessage.decode bytes).map fun (message, rest) => (.hourTrackerMessage message, rest)
  else if tag = 125 then (MessageRatioMessage.decode bytes).map fun (message, rest) => (.messageRatioMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message Block -/
structure MessageBlock where
  payload : Payload
  deriving DecidableEq, Repr

namespace MessageBlock

def encodeBody (message : MessageBlock) : List UInt8 :=
  encodeUInt 1 (Payload.tag message.payload)
    ++ (Payload.encode message.payload)

def decodeBody (bytes : List UInt8) : Option (MessageBlock × List UInt8) := do
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (payload, bytes) ← Payload.decode messageType bytes
  pure ({ payload }, bytes)

theorem decodeBody_encodeBody (message : MessageBlock) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : MessageBlock) : (encodeBody message).length + 0 < 256 ^ 2 := by
  unfold encodeBody
  cases message.payload with
  | bigPictureMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, BigPictureMessage.encode_length]
    omega
  | benchmarkTradeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, BenchmarkTradeMessage.encode_length]
    omega
  | hourTrackerMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, HourTrackerMessage.encode_length]
    omega
  | messageRatioMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MessageRatioMessage.encode_length]
    omega

/-- Size rule: Message Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : MessageBlock → List UInt8 :=
  encodeFramed 2 0 encodeBody

def decode : List UInt8 → Option (MessageBlock × List UInt8) :=
  decodeFramed 2 0 decodeBody

@[simp] theorem decode_encode (message : MessageBlock) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 2 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : MessageBlock) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end MessageBlock

/-- Packet -/
structure Packet where
  length : BitVec 16
  marketDataGroup : BitVec 8
  session : BitVec 8
  sequenceNumber : BitVec 32
  datetime : BitVec 64
  messageBlock : Bounded 1 MessageBlock
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUInt 2 message.length
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.messageBlock.val.length)
    ++ (encodeUInt 1 message.marketDataGroup
    ++ (encodeUInt 1 message.session
    ++ (encodeUInt 4 message.sequenceNumber
    ++ (encodeUInt 8 message.datetime
    ++ (encodeMany MessageBlock.encode message.messageBlock.val))))))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (length, bytes) ← decodeUInt 2 bytes
  let (totalMessages, bytes) ← decodeUInt 1 bytes
  let (marketDataGroup, bytes) ← decodeUInt 1 bytes
  let (session, bytes) ← decodeUInt 1 bytes
  let (sequenceNumber, bytes) ← decodeUInt 4 bytes
  let (datetime, bytes) ← decodeUInt 8 bytes
  let (messageBlock_, bytes) ← decodeMany MessageBlock.decode totalMessages.toNat bytes
  if fits_messageBlock : messageBlock_.length < 256 ^ 1 then
    pure ({ length, marketDataGroup, session, sequenceNumber, datetime, messageBlock := ⟨messageBlock_, fits_messageBlock⟩ }, bytes)
  else none

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
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
  rw [decodeMany_bounded 1 MessageBlock.encode MessageBlock.decode MessageBlock.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.messageBlock.length_lt]
  rfl

end Packet

end Omi.BmvBmvmarketdataProduct34IntraV11
