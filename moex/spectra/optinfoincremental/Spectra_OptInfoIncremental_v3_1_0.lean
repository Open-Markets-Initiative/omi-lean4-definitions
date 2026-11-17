import Wire

/-!
# Moscow Exchange SIMBA Spectra Options Instrument Incremental v3.1.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.

Note: Msg Flags is a bit field set, proven as its 2 byte integer rather than bit by bit

License: MIT No Attribution
-/

namespace Omi.MoexSpectraOptinfoincrementalSimbaV310

/-- Market Segment Id: one byte code -/
def MarketSegmentId.codes : List UInt8 :=
  [0x44]

inductive MarketSegmentId where
  | derivatives -- Derivatives
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketSegmentId.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketSegmentId

def toByte : MarketSegmentId → UInt8
  | .derivatives => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : MarketSegmentId :=
  .derivatives

def ofByte (byte : UInt8) : MarketSegmentId :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketSegmentId) : ofByte value.toByte = value := by
  cases value with
  | derivatives => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarketSegmentId) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketSegmentId × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketSegmentId) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : MarketSegmentId) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : MarketSegmentId) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarketSegmentId

/-- Market Data Packet Header: 16 bytes -/
structure MarketDataPacketHeader where
  msgSeqNum : BitVec 32
  msgSize : BitVec 16
  msgFlags : BitVec 16
  sendingTime : BitVec 64
  deriving DecidableEq, Repr

namespace MarketDataPacketHeader

def encode (message : MarketDataPacketHeader) : List UInt8 :=
  encodeUIntLE 4 message.msgSeqNum
    ++ (encodeUIntLE 2 message.msgSize
    ++ (encodeUIntLE 2 message.msgFlags
    ++ (encodeUIntLE 8 message.sendingTime)))

def decode (bytes : List UInt8) : Option (MarketDataPacketHeader × List UInt8) := do
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (msgSize, bytes) ← decodeUIntLE 2 bytes
  let (msgFlags, bytes) ← decodeUIntLE 2 bytes
  let (sendingTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ msgSeqNum, msgSize, msgFlags, sendingTime }, bytes)

@[simp] theorem encode_length (message : MarketDataPacketHeader) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : MarketDataPacketHeader) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketDataPacketHeader) (rest : List UInt8) :
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

end MarketDataPacketHeader

/-- Incremental Packet Header: 12 bytes -/
structure IncrementalPacketHeader where
  transactTime : BitVec 64
  exchangeTradingSessionIdOptional : BitVec 32
  deriving DecidableEq, Repr

namespace IncrementalPacketHeader

def encode (message : IncrementalPacketHeader) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 4 message.exchangeTradingSessionIdOptional)

def decode (bytes : List UInt8) : Option (IncrementalPacketHeader × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (exchangeTradingSessionIdOptional, bytes) ← decodeUIntLE 4 bytes
  pure ({ transactTime, exchangeTradingSessionIdOptional }, bytes)

@[simp] theorem encode_length (message : IncrementalPacketHeader) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : IncrementalPacketHeader) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IncrementalPacketHeader) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end IncrementalPacketHeader

/-- Heartbeat Message: 0 bytes -/
structure HeartbeatMessage where
  deriving DecidableEq, Repr

namespace HeartbeatMessage

def encode (_ : HeartbeatMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (HeartbeatMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : HeartbeatMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : HeartbeatMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end HeartbeatMessage

/-- Sequence Reset Message: 4 bytes -/
structure SequenceResetMessage where
  newSeqNo : BitVec 32
  deriving DecidableEq, Repr

namespace SequenceResetMessage

def encode (message : SequenceResetMessage) : List UInt8 :=
  encodeUIntLE 4 message.newSeqNo

def decode (bytes : List UInt8) : Option (SequenceResetMessage × List UInt8) := do
  let (newSeqNo, bytes) ← decodeUIntLE 4 bytes
  pure ({ newSeqNo }, bytes)

@[simp] theorem encode_length (message : SequenceResetMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : SequenceResetMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SequenceResetMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SequenceResetMessage

/-- Security Status Message: 70 bytes -/
structure SecurityStatusMessage where
  securityId : BitVec 32
  symbol : Alpha 25
  securityTradingStatus : BitVec 8
  highLimitPx : BitVec 64
  lowLimitPx : BitVec 64
  initialMarginOnBuy : BitVec 64
  initialMarginOnSell : BitVec 64
  initialMarginSyntetic : BitVec 64
  deriving DecidableEq, Repr

namespace SecurityStatusMessage

def encode (message : SecurityStatusMessage) : List UInt8 :=
  encodeUIntLE 4 message.securityId
    ++ (Alpha.encode message.symbol
    ++ (encodeUInt 1 message.securityTradingStatus
    ++ (encodeUIntLE 8 message.highLimitPx
    ++ (encodeUIntLE 8 message.lowLimitPx
    ++ (encodeUIntLE 8 message.initialMarginOnBuy
    ++ (encodeUIntLE 8 message.initialMarginOnSell
    ++ (encodeUIntLE 8 message.initialMarginSyntetic)))))))

def decode (bytes : List UInt8) : Option (SecurityStatusMessage × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (symbol, bytes) ← Alpha.decode 25 bytes
  let (securityTradingStatus, bytes) ← decodeUInt 1 bytes
  let (highLimitPx, bytes) ← decodeUIntLE 8 bytes
  let (lowLimitPx, bytes) ← decodeUIntLE 8 bytes
  let (initialMarginOnBuy, bytes) ← decodeUIntLE 8 bytes
  let (initialMarginOnSell, bytes) ← decodeUIntLE 8 bytes
  let (initialMarginSyntetic, bytes) ← decodeUIntLE 8 bytes
  pure ({ securityId, symbol, securityTradingStatus, highLimitPx, lowLimitPx, initialMarginOnBuy, initialMarginOnSell, initialMarginSyntetic }, bytes)

@[simp] theorem encode_length (message : SecurityStatusMessage) : (encode message).length = 70 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SecurityStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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

end SecurityStatusMessage

/-- Security Definition Update Report Message: 28 bytes -/
structure SecurityDefinitionUpdateReportMessage where
  securityId : BitVec 32
  volatility : BitVec 64
  theorPrice : BitVec 64
  theorPriceLimit : BitVec 64
  deriving DecidableEq, Repr

namespace SecurityDefinitionUpdateReportMessage

def encode (message : SecurityDefinitionUpdateReportMessage) : List UInt8 :=
  encodeUIntLE 4 message.securityId
    ++ (encodeUIntLE 8 message.volatility
    ++ (encodeUIntLE 8 message.theorPrice
    ++ (encodeUIntLE 8 message.theorPriceLimit)))

def decode (bytes : List UInt8) : Option (SecurityDefinitionUpdateReportMessage × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (volatility, bytes) ← decodeUIntLE 8 bytes
  let (theorPrice, bytes) ← decodeUIntLE 8 bytes
  let (theorPriceLimit, bytes) ← decodeUIntLE 8 bytes
  pure ({ securityId, volatility, theorPrice, theorPriceLimit }, bytes)

@[simp] theorem encode_length (message : SecurityDefinitionUpdateReportMessage) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : SecurityDefinitionUpdateReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityDefinitionUpdateReportMessage) (rest : List UInt8) :
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

end SecurityDefinitionUpdateReportMessage

/-- Trading Session Status Message: 40 bytes -/
structure TradingSessionStatusMessage where
  tradSesOpenTime : BitVec 64
  tradSesCloseTime : BitVec 64
  tradSesIntermClearingStartTime : BitVec 64
  tradSesIntermClearingEndTime : BitVec 64
  tradingSessionId : BitVec 8
  exchangeTradingSessionIdInt32NullOptional : BitVec 32
  tradSesStatus : BitVec 8
  marketSegmentId : MarketSegmentId
  tradSesEvent : BitVec 8
  deriving DecidableEq, Repr

namespace TradingSessionStatusMessage

def encode (message : TradingSessionStatusMessage) : List UInt8 :=
  encodeUIntLE 8 message.tradSesOpenTime
    ++ (encodeUIntLE 8 message.tradSesCloseTime
    ++ (encodeUIntLE 8 message.tradSesIntermClearingStartTime
    ++ (encodeUIntLE 8 message.tradSesIntermClearingEndTime
    ++ (encodeUInt 1 message.tradingSessionId
    ++ (encodeUIntLE 4 message.exchangeTradingSessionIdInt32NullOptional
    ++ (encodeUInt 1 message.tradSesStatus
    ++ (MarketSegmentId.encode message.marketSegmentId
    ++ (encodeUInt 1 message.tradSesEvent))))))))

def decode (bytes : List UInt8) : Option (TradingSessionStatusMessage × List UInt8) := do
  let (tradSesOpenTime, bytes) ← decodeUIntLE 8 bytes
  let (tradSesCloseTime, bytes) ← decodeUIntLE 8 bytes
  let (tradSesIntermClearingStartTime, bytes) ← decodeUIntLE 8 bytes
  let (tradSesIntermClearingEndTime, bytes) ← decodeUIntLE 8 bytes
  let (tradingSessionId, bytes) ← decodeUInt 1 bytes
  let (exchangeTradingSessionIdInt32NullOptional, bytes) ← decodeUIntLE 4 bytes
  let (tradSesStatus, bytes) ← decodeUInt 1 bytes
  let (marketSegmentId, bytes) ← MarketSegmentId.decode bytes
  let (tradSesEvent, bytes) ← decodeUInt 1 bytes
  pure ({ tradSesOpenTime, tradSesCloseTime, tradSesIntermClearingStartTime, tradSesIntermClearingEndTime, tradingSessionId, exchangeTradingSessionIdInt32NullOptional, tradSesStatus, marketSegmentId, tradSesEvent }, bytes)

@[simp] theorem encode_length (message : TradingSessionStatusMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, MarketSegmentId.encode_length]

theorem encode_length_pos (message : TradingSessionStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradingSessionStatusMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MarketSegmentId.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TradingSessionStatusMessage

/-- Any Payload, selected by Template Id -/
inductive Payload where
  | heartbeatMessage (message : HeartbeatMessage) -- 1
  | sequenceResetMessage (message : SequenceResetMessage) -- 2
  | securityStatusMessage (message : SecurityStatusMessage) -- 9
  | securityDefinitionUpdateReportMessage (message : SecurityDefinitionUpdateReportMessage) -- 10
  | tradingSessionStatusMessage (message : TradingSessionStatusMessage) -- 11
  deriving DecidableEq, Repr

namespace Payload

/-- The Template Id each message is sent under -/
def tag : Payload → BitVec 16
  | .heartbeatMessage _ => 1
  | .sequenceResetMessage _ => 2
  | .securityStatusMessage _ => 9
  | .securityDefinitionUpdateReportMessage _ => 10
  | .tradingSessionStatusMessage _ => 11

def encode : Payload → List UInt8
  | .heartbeatMessage message => HeartbeatMessage.encode message
  | .sequenceResetMessage message => SequenceResetMessage.encode message
  | .securityStatusMessage message => SecurityStatusMessage.encode message
  | .securityDefinitionUpdateReportMessage message => SecurityDefinitionUpdateReportMessage.encode message
  | .tradingSessionStatusMessage message => TradingSessionStatusMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 70 := by
  cases message with
  | heartbeatMessage inner =>
    simp only [encode, HeartbeatMessage.encode_length]
    omega
  | sequenceResetMessage inner =>
    simp only [encode, SequenceResetMessage.encode_length]
    omega
  | securityStatusMessage inner =>
    simp only [encode, SecurityStatusMessage.encode_length]
    omega
  | securityDefinitionUpdateReportMessage inner =>
    simp only [encode, SecurityDefinitionUpdateReportMessage.encode_length]
    omega
  | tradingSessionStatusMessage inner =>
    simp only [encode, TradingSessionStatusMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 1 then (HeartbeatMessage.decode bytes).map fun (message, rest) => (.heartbeatMessage message, rest)
  else if tag = 2 then (SequenceResetMessage.decode bytes).map fun (message, rest) => (.sequenceResetMessage message, rest)
  else if tag = 9 then (SecurityStatusMessage.decode bytes).map fun (message, rest) => (.securityStatusMessage message, rest)
  else if tag = 10 then (SecurityDefinitionUpdateReportMessage.decode bytes).map fun (message, rest) => (.securityDefinitionUpdateReportMessage message, rest)
  else if tag = 11 then (TradingSessionStatusMessage.decode bytes).map fun (message, rest) => (.tradingSessionStatusMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message -/
structure Message where
  blockLength : BitVec 16
  schemaId : BitVec 16
  version : BitVec 16
  payload : Payload
  deriving DecidableEq, Repr

namespace Message

def encode (message : Message) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUIntLE 2 (Payload.tag message.payload)
    ++ (encodeUIntLE 2 message.schemaId
    ++ (encodeUIntLE 2 message.version
    ++ (Payload.encode message.payload))))

def decode (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (templateId, bytes) ← decodeUIntLE 2 bytes
  let (schemaId, bytes) ← decodeUIntLE 2 bytes
  let (version, bytes) ← decodeUIntLE 2 bytes
  let (payload, bytes) ← Payload.decode templateId bytes
  pure ({ blockLength, schemaId, version, payload }, bytes)

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Message) : (encode message).length ≤ 78 := by
  unfold encode
  cases message.payload with
  | heartbeatMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, HeartbeatMessage.encode_length]
    omega
  | sequenceResetMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, SequenceResetMessage.encode_length]
    omega
  | securityStatusMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, SecurityStatusMessage.encode_length]
    omega
  | securityDefinitionUpdateReportMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, SecurityDefinitionUpdateReportMessage.encode_length]
    omega
  | tradingSessionStatusMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, TradingSessionStatusMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
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
  rw [Payload.decode_encode, some_bind]
  rfl

end Message

/-- Udp Packet -/
structure UdpPacket where
  marketDataPacketHeader : MarketDataPacketHeader
  incrementalPacketHeader : IncrementalPacketHeader
  message : List Message
  deriving DecidableEq, Repr

namespace UdpPacket

def encode (message : UdpPacket) : List UInt8 :=
  MarketDataPacketHeader.encode message.marketDataPacketHeader
    ++ (IncrementalPacketHeader.encode message.incrementalPacketHeader
    ++ (encodeMany Message.encode message.message))

def decode (bytes : List UInt8) : Option UdpPacket := do
  let (marketDataPacketHeader, bytes) ← MarketDataPacketHeader.decode bytes
  let (incrementalPacketHeader, bytes) ← IncrementalPacketHeader.decode bytes
  let message ← decodeAll Message.decode bytes.length bytes
  pure { marketDataPacketHeader, incrementalPacketHeader, message }

theorem encode_length_pos (message : UdpPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [MarketDataPacketHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

theorem decode_encode (message : UdpPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [MarketDataPacketHeader.decode_encode, some_bind]
  dsimp only
  rw [IncrementalPacketHeader.decode_encode, some_bind]
  dsimp only
  rw [decodeAll_encodeMany Message.encode Message.decode Message.decode_encode Message.encode_length_pos message.message _ (encodeMany_length_ge Message.encode Message.encode_length_pos message.message), some_bind]
  rfl

end UdpPacket

end Omi.MoexSpectraOptinfoincrementalSimbaV310
