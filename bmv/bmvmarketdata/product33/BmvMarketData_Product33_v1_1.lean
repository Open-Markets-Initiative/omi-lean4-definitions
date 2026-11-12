import Wire

/-!
# Bolsa Mexicana de Valores Bmv Market Data Product 33 v1.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.

License: MIT No Attribution
-/

namespace Omi.BmvBmvmarketdataProduct33IntraV11

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

/-- Effective Spread Message: 33 bytes -/
structure EffectiveSpreadMessage where
  origin : Origin
  esMxn : BitVec 32
  esBasisPoints : BitVec 32
  esMxnBid : BitVec 32
  esBasisPointsBid : BitVec 32
  esMxnAsk : BitVec 32
  esBasisPointsAsk : BitVec 32
  market : Market
  sector : BitVec 8
  instrumentNumber : BitVec 32
  indices : Alpha 2
  deriving DecidableEq, Repr

namespace EffectiveSpreadMessage

def encode (message : EffectiveSpreadMessage) : List UInt8 :=
  Origin.encode message.origin
    ++ (encodeUInt 4 message.esMxn
    ++ (encodeUInt 4 message.esBasisPoints
    ++ (encodeUInt 4 message.esMxnBid
    ++ (encodeUInt 4 message.esBasisPointsBid
    ++ (encodeUInt 4 message.esMxnAsk
    ++ (encodeUInt 4 message.esBasisPointsAsk
    ++ (Market.encode message.market
    ++ (encodeUInt 1 message.sector
    ++ (encodeUInt 4 message.instrumentNumber
    ++ (Alpha.encode message.indices))))))))))

def decode (bytes : List UInt8) : Option (EffectiveSpreadMessage × List UInt8) := do
  let (origin, bytes) ← Origin.decode bytes
  let (esMxn, bytes) ← decodeUInt 4 bytes
  let (esBasisPoints, bytes) ← decodeUInt 4 bytes
  let (esMxnBid, bytes) ← decodeUInt 4 bytes
  let (esBasisPointsBid, bytes) ← decodeUInt 4 bytes
  let (esMxnAsk, bytes) ← decodeUInt 4 bytes
  let (esBasisPointsAsk, bytes) ← decodeUInt 4 bytes
  let (market, bytes) ← Market.decode bytes
  let (sector, bytes) ← decodeUInt 1 bytes
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (indices, bytes) ← Alpha.decode 2 bytes
  pure ({ origin, esMxn, esBasisPoints, esMxnBid, esBasisPointsBid, esMxnAsk, esBasisPointsAsk, market, sector, instrumentNumber, indices }, bytes)

@[simp] theorem encode_length (message : EffectiveSpreadMessage) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, Origin.encode_length, encodeUInt_length, Market.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : EffectiveSpreadMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EffectiveSpreadMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Market.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end EffectiveSpreadMessage

/-- Spread Quality Message: 21 bytes -/
structure SpreadQualityMessage where
  origin : Origin
  timeBestSpread : BitVec 32
  timeTieBestSpread : BitVec 32
  timeWithoutBestSpread : BitVec 32
  market : Market
  sector : BitVec 8
  instrumentNumber : BitVec 32
  indices : Alpha 2
  deriving DecidableEq, Repr

namespace SpreadQualityMessage

def encode (message : SpreadQualityMessage) : List UInt8 :=
  Origin.encode message.origin
    ++ (encodeUInt 4 message.timeBestSpread
    ++ (encodeUInt 4 message.timeTieBestSpread
    ++ (encodeUInt 4 message.timeWithoutBestSpread
    ++ (Market.encode message.market
    ++ (encodeUInt 1 message.sector
    ++ (encodeUInt 4 message.instrumentNumber
    ++ (Alpha.encode message.indices)))))))

def decode (bytes : List UInt8) : Option (SpreadQualityMessage × List UInt8) := do
  let (origin, bytes) ← Origin.decode bytes
  let (timeBestSpread, bytes) ← decodeUInt 4 bytes
  let (timeTieBestSpread, bytes) ← decodeUInt 4 bytes
  let (timeWithoutBestSpread, bytes) ← decodeUInt 4 bytes
  let (market, bytes) ← Market.decode bytes
  let (sector, bytes) ← decodeUInt 1 bytes
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (indices, bytes) ← Alpha.decode 2 bytes
  pure ({ origin, timeBestSpread, timeTieBestSpread, timeWithoutBestSpread, market, sector, instrumentNumber, indices }, bytes)

@[simp] theorem encode_length (message : SpreadQualityMessage) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, Origin.encode_length, encodeUInt_length, Market.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : SpreadQualityMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SpreadQualityMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Market.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SpreadQualityMessage

/-- Spread Message: 25 bytes -/
structure SpreadMessage where
  origin : Origin
  spreadMxn : BitVec 32
  spreadBasisPoints : BitVec 32
  spreadAverage : BitVec 32
  numberOfSpreads : BitVec 32
  market : Market
  sector : BitVec 8
  instrumentNumber : BitVec 32
  indices : Alpha 2
  deriving DecidableEq, Repr

namespace SpreadMessage

def encode (message : SpreadMessage) : List UInt8 :=
  Origin.encode message.origin
    ++ (encodeUInt 4 message.spreadMxn
    ++ (encodeUInt 4 message.spreadBasisPoints
    ++ (encodeUInt 4 message.spreadAverage
    ++ (encodeUInt 4 message.numberOfSpreads
    ++ (Market.encode message.market
    ++ (encodeUInt 1 message.sector
    ++ (encodeUInt 4 message.instrumentNumber
    ++ (Alpha.encode message.indices))))))))

def decode (bytes : List UInt8) : Option (SpreadMessage × List UInt8) := do
  let (origin, bytes) ← Origin.decode bytes
  let (spreadMxn, bytes) ← decodeUInt 4 bytes
  let (spreadBasisPoints, bytes) ← decodeUInt 4 bytes
  let (spreadAverage, bytes) ← decodeUInt 4 bytes
  let (numberOfSpreads, bytes) ← decodeUInt 4 bytes
  let (market, bytes) ← Market.decode bytes
  let (sector, bytes) ← decodeUInt 1 bytes
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (indices, bytes) ← Alpha.decode 2 bytes
  pure ({ origin, spreadMxn, spreadBasisPoints, spreadAverage, numberOfSpreads, market, sector, instrumentNumber, indices }, bytes)

@[simp] theorem encode_length (message : SpreadMessage) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, Origin.encode_length, encodeUInt_length, Market.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : SpreadMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SpreadMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Market.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SpreadMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | bigPictureMessage (message : BigPictureMessage) -- 39
  | effectiveSpreadMessage (message : EffectiveSpreadMessage) -- 61
  | spreadQualityMessage (message : SpreadQualityMessage) -- 123
  | spreadMessage (message : SpreadMessage) -- 59
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .bigPictureMessage _ => 39
  | .effectiveSpreadMessage _ => 61
  | .spreadQualityMessage _ => 123
  | .spreadMessage _ => 59

def encode : Payload → List UInt8
  | .bigPictureMessage message => BigPictureMessage.encode message
  | .effectiveSpreadMessage message => EffectiveSpreadMessage.encode message
  | .spreadQualityMessage message => SpreadQualityMessage.encode message
  | .spreadMessage message => SpreadMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 37 := by
  cases message with
  | bigPictureMessage inner =>
    simp only [encode, BigPictureMessage.encode_length]
    omega
  | effectiveSpreadMessage inner =>
    simp only [encode, EffectiveSpreadMessage.encode_length]
    omega
  | spreadQualityMessage inner =>
    simp only [encode, SpreadQualityMessage.encode_length]
    omega
  | spreadMessage inner =>
    simp only [encode, SpreadMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 39 then (BigPictureMessage.decode bytes).map fun (message, rest) => (.bigPictureMessage message, rest)
  else if tag = 61 then (EffectiveSpreadMessage.decode bytes).map fun (message, rest) => (.effectiveSpreadMessage message, rest)
  else if tag = 123 then (SpreadQualityMessage.decode bytes).map fun (message, rest) => (.spreadQualityMessage message, rest)
  else if tag = 59 then (SpreadMessage.decode bytes).map fun (message, rest) => (.spreadMessage message, rest)
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
  | effectiveSpreadMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, EffectiveSpreadMessage.encode_length]
    omega
  | spreadQualityMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SpreadQualityMessage.encode_length]
    omega
  | spreadMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SpreadMessage.encode_length]
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

end Omi.BmvBmvmarketdataProduct33IntraV11
