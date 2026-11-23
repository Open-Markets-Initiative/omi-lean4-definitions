import Wire

/-!
# Moscow Exchange TWIME Spectra Order Entry v9.12.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.

Note: Flags is a bit field set, proven as its 8 byte integer rather than bit by bit

Note: Flags 2 is a bit field set, proven as its 8 byte integer rather than bit by bit

Note: Server Message is not framed: its size rule is not the length plus a constant the frame proof
covers

License: MIT No Attribution
-/

namespace Omi.MoexSpectraOrderentryTwimeV9120Server

/-- Compliance Id: one byte code -/
def ComplianceId.codes : List UInt8 :=
  [0x20, 0x4D, 0x53, 0x52, 0x41, 0x44]

inductive ComplianceId where
  | notAvailable -- Not Available
  | manual -- Manual
  | stopLoss -- Stop Loss
  | algorithm -- Algorithm
  | autofollow -- Autofollow
  | marginCall -- Margin Call
  | unlisted (byte : { byte : UInt8 // byte ∉ ComplianceId.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ComplianceId

def toByte : ComplianceId → UInt8
  | .notAvailable => 0x20
  | .manual => 0x4D
  | .stopLoss => 0x53
  | .algorithm => 0x52
  | .autofollow => 0x41
  | .marginCall => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ComplianceId :=
  if byte = 0x20 then .notAvailable
  else if byte = 0x4D then .manual
  else if byte = 0x53 then .stopLoss
  else if byte = 0x52 then .algorithm
  else if byte = 0x41 then .autofollow
  else .marginCall

def ofByte (byte : UInt8) : ComplianceId :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ComplianceId) : ofByte value.toByte = value := by
  cases value with
  | notAvailable => decide
  | manual => decide
  | stopLoss => decide
  | algorithm => decide
  | autofollow => decide
  | marginCall => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ComplianceId) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ComplianceId × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ComplianceId) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ComplianceId) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ComplianceId) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ComplianceId

/-- Establishment Ack Message: 20 bytes -/
structure EstablishmentAckMessage where
  requestTimestamp : BitVec 64
  keepaliveInterval : BitVec 32
  nextSeqNo : BitVec 64
  deriving DecidableEq, Repr

namespace EstablishmentAckMessage

def encode (message : EstablishmentAckMessage) : List UInt8 :=
  encodeUIntLE 8 message.requestTimestamp
    ++ (encodeUIntLE 4 message.keepaliveInterval
    ++ (encodeUIntLE 8 message.nextSeqNo))

def decode (bytes : List UInt8) : Option (EstablishmentAckMessage × List UInt8) := do
  let (requestTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (keepaliveInterval, bytes) ← decodeUIntLE 4 bytes
  let (nextSeqNo, bytes) ← decodeUIntLE 8 bytes
  pure ({ requestTimestamp, keepaliveInterval, nextSeqNo }, bytes)

@[simp] theorem encode_length (message : EstablishmentAckMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : EstablishmentAckMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EstablishmentAckMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end EstablishmentAckMessage

/-- Establishment Reject Message: 9 bytes -/
structure EstablishmentRejectMessage where
  requestTimestamp : BitVec 64
  establishmentRejectCode : BitVec 8
  deriving DecidableEq, Repr

namespace EstablishmentRejectMessage

def encode (message : EstablishmentRejectMessage) : List UInt8 :=
  encodeUIntLE 8 message.requestTimestamp
    ++ (encodeUInt 1 message.establishmentRejectCode)

def decode (bytes : List UInt8) : Option (EstablishmentRejectMessage × List UInt8) := do
  let (requestTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (establishmentRejectCode, bytes) ← decodeUInt 1 bytes
  pure ({ requestTimestamp, establishmentRejectCode }, bytes)

@[simp] theorem encode_length (message : EstablishmentRejectMessage) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : EstablishmentRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EstablishmentRejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end EstablishmentRejectMessage

/-- Terminate Message: 1 bytes -/
structure TerminateMessage where
  terminationCode : BitVec 8
  deriving DecidableEq, Repr

namespace TerminateMessage

def encode (message : TerminateMessage) : List UInt8 :=
  encodeUInt 1 message.terminationCode

def decode (bytes : List UInt8) : Option (TerminateMessage × List UInt8) := do
  let (terminationCode, bytes) ← decodeUInt 1 bytes
  pure ({ terminationCode }, bytes)

@[simp] theorem encode_length (message : TerminateMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : TerminateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TerminateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TerminateMessage

/-- Retransmission Message: 20 bytes -/
structure RetransmissionMessage where
  nextSeqNo : BitVec 64
  requestTimestamp : BitVec 64
  count : BitVec 32
  deriving DecidableEq, Repr

namespace RetransmissionMessage

def encode (message : RetransmissionMessage) : List UInt8 :=
  encodeUIntLE 8 message.nextSeqNo
    ++ (encodeUIntLE 8 message.requestTimestamp
    ++ (encodeUIntLE 4 message.count))

def decode (bytes : List UInt8) : Option (RetransmissionMessage × List UInt8) := do
  let (nextSeqNo, bytes) ← decodeUIntLE 8 bytes
  let (requestTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (count, bytes) ← decodeUIntLE 4 bytes
  pure ({ nextSeqNo, requestTimestamp, count }, bytes)

@[simp] theorem encode_length (message : RetransmissionMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : RetransmissionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RetransmissionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end RetransmissionMessage

/-- Sequence Message: 8 bytes -/
structure SequenceMessage where
  nextSeqNo : BitVec 64
  deriving DecidableEq, Repr

namespace SequenceMessage

def encode (message : SequenceMessage) : List UInt8 :=
  encodeUIntLE 8 message.nextSeqNo

def decode (bytes : List UInt8) : Option (SequenceMessage × List UInt8) := do
  let (nextSeqNo, bytes) ← decodeUIntLE 8 bytes
  pure ({ nextSeqNo }, bytes)

@[simp] theorem encode_length (message : SequenceMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : SequenceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SequenceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SequenceMessage

/-- Flood Reject Message: 16 bytes -/
structure FloodRejectMessage where
  clOrdId : BitVec 64
  queueSize : BitVec 32
  penaltyRemain : BitVec 32
  deriving DecidableEq, Repr

namespace FloodRejectMessage

def encode (message : FloodRejectMessage) : List UInt8 :=
  encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 4 message.queueSize
    ++ (encodeUIntLE 4 message.penaltyRemain))

def decode (bytes : List UInt8) : Option (FloodRejectMessage × List UInt8) := do
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (queueSize, bytes) ← decodeUIntLE 4 bytes
  let (penaltyRemain, bytes) ← decodeUIntLE 4 bytes
  pure ({ clOrdId, queueSize, penaltyRemain }, bytes)

@[simp] theorem encode_length (message : FloodRejectMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : FloodRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FloodRejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end FloodRejectMessage

/-- Session Reject Message: 13 bytes -/
structure SessionRejectMessage where
  clOrdId : BitVec 64
  refTagId : BitVec 32
  sessionRejectReason : BitVec 8
  deriving DecidableEq, Repr

namespace SessionRejectMessage

def encode (message : SessionRejectMessage) : List UInt8 :=
  encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 4 message.refTagId
    ++ (encodeUInt 1 message.sessionRejectReason))

def decode (bytes : List UInt8) : Option (SessionRejectMessage × List UInt8) := do
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (refTagId, bytes) ← decodeUIntLE 4 bytes
  let (sessionRejectReason, bytes) ← decodeUInt 1 bytes
  pure ({ clOrdId, refTagId, sessionRejectReason }, bytes)

@[simp] theorem encode_length (message : SessionRejectMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : SessionRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SessionRejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SessionRejectMessage

/-- Business Message Reject Message: 20 bytes -/
structure BusinessMessageRejectMessage where
  clOrdId : BitVec 64
  timestamp : BitVec 64
  ordRejReason : BitVec 32
  deriving DecidableEq, Repr

namespace BusinessMessageRejectMessage

def encode (message : BusinessMessageRejectMessage) : List UInt8 :=
  encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 4 message.ordRejReason))

def decode (bytes : List UInt8) : Option (BusinessMessageRejectMessage × List UInt8) := do
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (ordRejReason, bytes) ← decodeUIntLE 4 bytes
  pure ({ clOrdId, timestamp, ordRejReason }, bytes)

@[simp] theorem encode_length (message : BusinessMessageRejectMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : BusinessMessageRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BusinessMessageRejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end BusinessMessageRejectMessage

/-- New Order Single Response Message: 74 bytes -/
structure NewOrderSingleResponseMessage where
  clOrdId : BitVec 64
  timestamp : BitVec 64
  expireDate : BitVec 64
  orderId : BitVec 64
  flags : BitVec 64
  flags2 : BitVec 64
  price : BitVec 64
  securityId : BitVec 32
  orderQty : BitVec 32
  tradingSessionId : BitVec 32
  clOrdLinkId : BitVec 32
  side : BitVec 8
  complianceId : ComplianceId
  deriving DecidableEq, Repr

namespace NewOrderSingleResponseMessage

def encode (message : NewOrderSingleResponseMessage) : List UInt8 :=
  encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.expireDate
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.flags
    ++ (encodeUIntLE 8 message.flags2
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.securityId
    ++ (encodeUIntLE 4 message.orderQty
    ++ (encodeUIntLE 4 message.tradingSessionId
    ++ (encodeUIntLE 4 message.clOrdLinkId
    ++ (encodeUInt 1 message.side
    ++ (ComplianceId.encode message.complianceId))))))))))))

def decode (bytes : List UInt8) : Option (NewOrderSingleResponseMessage × List UInt8) := do
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (expireDate, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (flags, bytes) ← decodeUIntLE 8 bytes
  let (flags2, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (tradingSessionId, bytes) ← decodeUIntLE 4 bytes
  let (clOrdLinkId, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (complianceId, bytes) ← ComplianceId.decode bytes
  pure ({ clOrdId, timestamp, expireDate, orderId, flags, flags2, price, securityId, orderQty, tradingSessionId, clOrdLinkId, side, complianceId }, bytes)

@[simp] theorem encode_length (message : NewOrderSingleResponseMessage) : (encode message).length = 74 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, ComplianceId.encode_length]

theorem encode_length_pos (message : NewOrderSingleResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewOrderSingleResponseMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ComplianceId.decode_encode, some_bind]
  rfl

end NewOrderSingleResponseMessage

/-- New Order Iceberg Response Message: 90 bytes -/
structure NewOrderIcebergResponseMessage where
  clOrdId : BitVec 64
  timestamp : BitVec 64
  expireDate : BitVec 64
  orderId : BitVec 64
  displayOrderId : BitVec 64
  flags : BitVec 64
  flags2 : BitVec 64
  price : BitVec 64
  securityId : BitVec 32
  orderQty : BitVec 32
  displayQty : BitVec 32
  displayVarianceQty : BitVec 32
  tradingSessionId : BitVec 32
  clOrdLinkId : BitVec 32
  side : BitVec 8
  complianceId : ComplianceId
  deriving DecidableEq, Repr

namespace NewOrderIcebergResponseMessage

def encode (message : NewOrderIcebergResponseMessage) : List UInt8 :=
  encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.expireDate
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.displayOrderId
    ++ (encodeUIntLE 8 message.flags
    ++ (encodeUIntLE 8 message.flags2
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.securityId
    ++ (encodeUIntLE 4 message.orderQty
    ++ (encodeUIntLE 4 message.displayQty
    ++ (encodeUIntLE 4 message.displayVarianceQty
    ++ (encodeUIntLE 4 message.tradingSessionId
    ++ (encodeUIntLE 4 message.clOrdLinkId
    ++ (encodeUInt 1 message.side
    ++ (ComplianceId.encode message.complianceId)))))))))))))))

def decode (bytes : List UInt8) : Option (NewOrderIcebergResponseMessage × List UInt8) := do
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (expireDate, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (displayOrderId, bytes) ← decodeUIntLE 8 bytes
  let (flags, bytes) ← decodeUIntLE 8 bytes
  let (flags2, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (displayQty, bytes) ← decodeUIntLE 4 bytes
  let (displayVarianceQty, bytes) ← decodeUIntLE 4 bytes
  let (tradingSessionId, bytes) ← decodeUIntLE 4 bytes
  let (clOrdLinkId, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (complianceId, bytes) ← ComplianceId.decode bytes
  pure ({ clOrdId, timestamp, expireDate, orderId, displayOrderId, flags, flags2, price, securityId, orderQty, displayQty, displayVarianceQty, tradingSessionId, clOrdLinkId, side, complianceId }, bytes)

@[simp] theorem encode_length (message : NewOrderIcebergResponseMessage) : (encode message).length = 90 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, ComplianceId.encode_length]

theorem encode_length_pos (message : NewOrderIcebergResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewOrderIcebergResponseMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ComplianceId.decode_encode, some_bind]
  rfl

end NewOrderIcebergResponseMessage

/-- Order Cancel Response Message: 52 bytes -/
structure OrderCancelResponseMessage where
  clOrdId : BitVec 64
  timestamp : BitVec 64
  orderId : BitVec 64
  flags : BitVec 64
  flags2 : BitVec 64
  orderQty : BitVec 32
  tradingSessionId : BitVec 32
  clOrdLinkId : BitVec 32
  deriving DecidableEq, Repr

namespace OrderCancelResponseMessage

def encode (message : OrderCancelResponseMessage) : List UInt8 :=
  encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.flags
    ++ (encodeUIntLE 8 message.flags2
    ++ (encodeUIntLE 4 message.orderQty
    ++ (encodeUIntLE 4 message.tradingSessionId
    ++ (encodeUIntLE 4 message.clOrdLinkId)))))))

def decode (bytes : List UInt8) : Option (OrderCancelResponseMessage × List UInt8) := do
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (flags, bytes) ← decodeUIntLE 8 bytes
  let (flags2, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (tradingSessionId, bytes) ← decodeUIntLE 4 bytes
  let (clOrdLinkId, bytes) ← decodeUIntLE 4 bytes
  pure ({ clOrdId, timestamp, orderId, flags, flags2, orderQty, tradingSessionId, clOrdLinkId }, bytes)

@[simp] theorem encode_length (message : OrderCancelResponseMessage) : (encode message).length = 52 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderCancelResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancelResponseMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderCancelResponseMessage

/-- Order Replace Response Message: 69 bytes -/
structure OrderReplaceResponseMessage where
  clOrdId : BitVec 64
  timestamp : BitVec 64
  orderId : BitVec 64
  prevOrderId : BitVec 64
  flags : BitVec 64
  flags2 : BitVec 64
  price : BitVec 64
  orderQty : BitVec 32
  tradingSessionId : BitVec 32
  clOrdLinkId : BitVec 32
  complianceId : ComplianceId
  deriving DecidableEq, Repr

namespace OrderReplaceResponseMessage

def encode (message : OrderReplaceResponseMessage) : List UInt8 :=
  encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.prevOrderId
    ++ (encodeUIntLE 8 message.flags
    ++ (encodeUIntLE 8 message.flags2
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.orderQty
    ++ (encodeUIntLE 4 message.tradingSessionId
    ++ (encodeUIntLE 4 message.clOrdLinkId
    ++ (ComplianceId.encode message.complianceId))))))))))

def decode (bytes : List UInt8) : Option (OrderReplaceResponseMessage × List UInt8) := do
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (prevOrderId, bytes) ← decodeUIntLE 8 bytes
  let (flags, bytes) ← decodeUIntLE 8 bytes
  let (flags2, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (tradingSessionId, bytes) ← decodeUIntLE 4 bytes
  let (clOrdLinkId, bytes) ← decodeUIntLE 4 bytes
  let (complianceId, bytes) ← ComplianceId.decode bytes
  pure ({ clOrdId, timestamp, orderId, prevOrderId, flags, flags2, price, orderQty, tradingSessionId, clOrdLinkId, complianceId }, bytes)

@[simp] theorem encode_length (message : OrderReplaceResponseMessage) : (encode message).length = 69 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, ComplianceId.encode_length]

theorem encode_length_pos (message : OrderReplaceResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderReplaceResponseMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [ComplianceId.decode_encode, some_bind]
  rfl

end OrderReplaceResponseMessage

/-- Order Mass Cancel Response Message: 20 bytes -/
structure OrderMassCancelResponseMessage where
  clOrdId : BitVec 64
  timestamp : BitVec 64
  totalAffectedOrders : BitVec 32
  deriving DecidableEq, Repr

namespace OrderMassCancelResponseMessage

def encode (message : OrderMassCancelResponseMessage) : List UInt8 :=
  encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 4 message.totalAffectedOrders))

def decode (bytes : List UInt8) : Option (OrderMassCancelResponseMessage × List UInt8) := do
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (totalAffectedOrders, bytes) ← decodeUIntLE 4 bytes
  pure ({ clOrdId, timestamp, totalAffectedOrders }, bytes)

@[simp] theorem encode_length (message : OrderMassCancelResponseMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderMassCancelResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderMassCancelResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderMassCancelResponseMessage

/-- Execution Single Report Message: 77 bytes -/
structure ExecutionSingleReportMessage where
  clOrdId : BitVec 64
  timestamp : BitVec 64
  orderId : BitVec 64
  trdMatchId : BitVec 64
  flags : BitVec 64
  flags2 : BitVec 64
  lastPx : BitVec 64
  lastQty : BitVec 32
  orderQty : BitVec 32
  tradingSessionId : BitVec 32
  clOrdLinkId : BitVec 32
  securityId : BitVec 32
  side : BitVec 8
  deriving DecidableEq, Repr

namespace ExecutionSingleReportMessage

def encode (message : ExecutionSingleReportMessage) : List UInt8 :=
  encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.trdMatchId
    ++ (encodeUIntLE 8 message.flags
    ++ (encodeUIntLE 8 message.flags2
    ++ (encodeUIntLE 8 message.lastPx
    ++ (encodeUIntLE 4 message.lastQty
    ++ (encodeUIntLE 4 message.orderQty
    ++ (encodeUIntLE 4 message.tradingSessionId
    ++ (encodeUIntLE 4 message.clOrdLinkId
    ++ (encodeUIntLE 4 message.securityId
    ++ (encodeUInt 1 message.side))))))))))))

def decode (bytes : List UInt8) : Option (ExecutionSingleReportMessage × List UInt8) := do
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (trdMatchId, bytes) ← decodeUIntLE 8 bytes
  let (flags, bytes) ← decodeUIntLE 8 bytes
  let (flags2, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 4 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (tradingSessionId, bytes) ← decodeUIntLE 4 bytes
  let (clOrdLinkId, bytes) ← decodeUIntLE 4 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  pure ({ clOrdId, timestamp, orderId, trdMatchId, flags, flags2, lastPx, lastQty, orderQty, tradingSessionId, clOrdLinkId, securityId, side }, bytes)

@[simp] theorem encode_length (message : ExecutionSingleReportMessage) : (encode message).length = 77 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : ExecutionSingleReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExecutionSingleReportMessage) (rest : List UInt8) :
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ExecutionSingleReportMessage

/-- Execution Multileg Report Message: 85 bytes -/
structure ExecutionMultilegReportMessage where
  clOrdId : BitVec 64
  timestamp : BitVec 64
  orderId : BitVec 64
  trdMatchId : BitVec 64
  flags : BitVec 64
  flags2 : BitVec 64
  lastPx : BitVec 64
  legPrice : BitVec 64
  lastQty : BitVec 32
  orderQty : BitVec 32
  tradingSessionId : BitVec 32
  clOrdLinkId : BitVec 32
  securityId : BitVec 32
  side : BitVec 8
  deriving DecidableEq, Repr

namespace ExecutionMultilegReportMessage

def encode (message : ExecutionMultilegReportMessage) : List UInt8 :=
  encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.trdMatchId
    ++ (encodeUIntLE 8 message.flags
    ++ (encodeUIntLE 8 message.flags2
    ++ (encodeUIntLE 8 message.lastPx
    ++ (encodeUIntLE 8 message.legPrice
    ++ (encodeUIntLE 4 message.lastQty
    ++ (encodeUIntLE 4 message.orderQty
    ++ (encodeUIntLE 4 message.tradingSessionId
    ++ (encodeUIntLE 4 message.clOrdLinkId
    ++ (encodeUIntLE 4 message.securityId
    ++ (encodeUInt 1 message.side)))))))))))))

def decode (bytes : List UInt8) : Option (ExecutionMultilegReportMessage × List UInt8) := do
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (trdMatchId, bytes) ← decodeUIntLE 8 bytes
  let (flags, bytes) ← decodeUIntLE 8 bytes
  let (flags2, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (legPrice, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 4 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (tradingSessionId, bytes) ← decodeUIntLE 4 bytes
  let (clOrdLinkId, bytes) ← decodeUIntLE 4 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  pure ({ clOrdId, timestamp, orderId, trdMatchId, flags, flags2, lastPx, legPrice, lastQty, orderQty, tradingSessionId, clOrdLinkId, securityId, side }, bytes)

@[simp] theorem encode_length (message : ExecutionMultilegReportMessage) : (encode message).length = 85 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : ExecutionMultilegReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExecutionMultilegReportMessage) (rest : List UInt8) :
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ExecutionMultilegReportMessage

/-- Empty Book Message: 12 bytes -/
structure EmptyBookMessage where
  timestamp : BitVec 64
  tradingSessionId : BitVec 32
  deriving DecidableEq, Repr

namespace EmptyBookMessage

def encode (message : EmptyBookMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 4 message.tradingSessionId)

def decode (bytes : List UInt8) : Option (EmptyBookMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (tradingSessionId, bytes) ← decodeUIntLE 4 bytes
  pure ({ timestamp, tradingSessionId }, bytes)

@[simp] theorem encode_length (message : EmptyBookMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : EmptyBookMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EmptyBookMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end EmptyBookMessage

/-- System Event Message: 21 bytes -/
structure SystemEventMessage where
  timestamp : BitVec 64
  eventId : BitVec 64
  tradingSessionId : BitVec 32
  tradSesEvent : BitVec 8
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.eventId
    ++ (encodeUIntLE 4 message.tradingSessionId
    ++ (encodeUInt 1 message.tradSesEvent)))

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (eventId, bytes) ← decodeUIntLE 8 bytes
  let (tradingSessionId, bytes) ← decodeUIntLE 4 bytes
  let (tradSesEvent, bytes) ← decodeUInt 1 bytes
  pure ({ timestamp, eventId, tradingSessionId, tradSesEvent }, bytes)

@[simp] theorem encode_length (message : SystemEventMessage) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : SystemEventMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemEventMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SystemEventMessage

/-- Any Server Payload, selected by Template Id -/
inductive ServerPayload where
  | establishmentAckMessage (message : EstablishmentAckMessage) -- 5001
  | establishmentRejectMessage (message : EstablishmentRejectMessage) -- 5002
  | terminateMessage (message : TerminateMessage) -- 5003
  | retransmissionMessage (message : RetransmissionMessage) -- 5005
  | sequenceMessage (message : SequenceMessage) -- 5006
  | floodRejectMessage (message : FloodRejectMessage) -- 5007
  | sessionRejectMessage (message : SessionRejectMessage) -- 5008
  | businessMessageRejectMessage (message : BusinessMessageRejectMessage) -- 5009
  | newOrderSingleResponseMessage (message : NewOrderSingleResponseMessage) -- 7015
  | newOrderIcebergResponseMessage (message : NewOrderIcebergResponseMessage) -- 7016
  | orderCancelResponseMessage (message : OrderCancelResponseMessage) -- 7017
  | orderReplaceResponseMessage (message : OrderReplaceResponseMessage) -- 7018
  | orderMassCancelResponseMessage (message : OrderMassCancelResponseMessage) -- 7007
  | executionSingleReportMessage (message : ExecutionSingleReportMessage) -- 7019
  | executionMultilegReportMessage (message : ExecutionMultilegReportMessage) -- 7020
  | emptyBookMessage (message : EmptyBookMessage) -- 7010
  | systemEventMessage (message : SystemEventMessage) -- 7014
  deriving DecidableEq, Repr

namespace ServerPayload

/-- The Template Id each message is sent under -/
def tag : ServerPayload → BitVec 16
  | .establishmentAckMessage _ => 5001
  | .establishmentRejectMessage _ => 5002
  | .terminateMessage _ => 5003
  | .retransmissionMessage _ => 5005
  | .sequenceMessage _ => 5006
  | .floodRejectMessage _ => 5007
  | .sessionRejectMessage _ => 5008
  | .businessMessageRejectMessage _ => 5009
  | .newOrderSingleResponseMessage _ => 7015
  | .newOrderIcebergResponseMessage _ => 7016
  | .orderCancelResponseMessage _ => 7017
  | .orderReplaceResponseMessage _ => 7018
  | .orderMassCancelResponseMessage _ => 7007
  | .executionSingleReportMessage _ => 7019
  | .executionMultilegReportMessage _ => 7020
  | .emptyBookMessage _ => 7010
  | .systemEventMessage _ => 7014

def encode : ServerPayload → List UInt8
  | .establishmentAckMessage message => EstablishmentAckMessage.encode message
  | .establishmentRejectMessage message => EstablishmentRejectMessage.encode message
  | .terminateMessage message => TerminateMessage.encode message
  | .retransmissionMessage message => RetransmissionMessage.encode message
  | .sequenceMessage message => SequenceMessage.encode message
  | .floodRejectMessage message => FloodRejectMessage.encode message
  | .sessionRejectMessage message => SessionRejectMessage.encode message
  | .businessMessageRejectMessage message => BusinessMessageRejectMessage.encode message
  | .newOrderSingleResponseMessage message => NewOrderSingleResponseMessage.encode message
  | .newOrderIcebergResponseMessage message => NewOrderIcebergResponseMessage.encode message
  | .orderCancelResponseMessage message => OrderCancelResponseMessage.encode message
  | .orderReplaceResponseMessage message => OrderReplaceResponseMessage.encode message
  | .orderMassCancelResponseMessage message => OrderMassCancelResponseMessage.encode message
  | .executionSingleReportMessage message => ExecutionSingleReportMessage.encode message
  | .executionMultilegReportMessage message => ExecutionMultilegReportMessage.encode message
  | .emptyBookMessage message => EmptyBookMessage.encode message
  | .systemEventMessage message => SystemEventMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ServerPayload) : (encode message).length ≤ 90 := by
  cases message with
  | establishmentAckMessage inner =>
    simp only [encode, EstablishmentAckMessage.encode_length]
    omega
  | establishmentRejectMessage inner =>
    simp only [encode, EstablishmentRejectMessage.encode_length]
    omega
  | terminateMessage inner =>
    simp only [encode, TerminateMessage.encode_length]
    omega
  | retransmissionMessage inner =>
    simp only [encode, RetransmissionMessage.encode_length]
    omega
  | sequenceMessage inner =>
    simp only [encode, SequenceMessage.encode_length]
    omega
  | floodRejectMessage inner =>
    simp only [encode, FloodRejectMessage.encode_length]
    omega
  | sessionRejectMessage inner =>
    simp only [encode, SessionRejectMessage.encode_length]
    omega
  | businessMessageRejectMessage inner =>
    simp only [encode, BusinessMessageRejectMessage.encode_length]
    omega
  | newOrderSingleResponseMessage inner =>
    simp only [encode, NewOrderSingleResponseMessage.encode_length]
    omega
  | newOrderIcebergResponseMessage inner =>
    simp only [encode, NewOrderIcebergResponseMessage.encode_length]
    omega
  | orderCancelResponseMessage inner =>
    simp only [encode, OrderCancelResponseMessage.encode_length]
    omega
  | orderReplaceResponseMessage inner =>
    simp only [encode, OrderReplaceResponseMessage.encode_length]
    omega
  | orderMassCancelResponseMessage inner =>
    simp only [encode, OrderMassCancelResponseMessage.encode_length]
    omega
  | executionSingleReportMessage inner =>
    simp only [encode, ExecutionSingleReportMessage.encode_length]
    omega
  | executionMultilegReportMessage inner =>
    simp only [encode, ExecutionMultilegReportMessage.encode_length]
    omega
  | emptyBookMessage inner =>
    simp only [encode, EmptyBookMessage.encode_length]
    omega
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (ServerPayload × List UInt8) :=
  if tag = 5001 then (EstablishmentAckMessage.decode bytes).map fun (message, rest) => (.establishmentAckMessage message, rest)
  else if tag = 5002 then (EstablishmentRejectMessage.decode bytes).map fun (message, rest) => (.establishmentRejectMessage message, rest)
  else if tag = 5003 then (TerminateMessage.decode bytes).map fun (message, rest) => (.terminateMessage message, rest)
  else if tag = 5005 then (RetransmissionMessage.decode bytes).map fun (message, rest) => (.retransmissionMessage message, rest)
  else if tag = 5006 then (SequenceMessage.decode bytes).map fun (message, rest) => (.sequenceMessage message, rest)
  else if tag = 5007 then (FloodRejectMessage.decode bytes).map fun (message, rest) => (.floodRejectMessage message, rest)
  else if tag = 5008 then (SessionRejectMessage.decode bytes).map fun (message, rest) => (.sessionRejectMessage message, rest)
  else if tag = 5009 then (BusinessMessageRejectMessage.decode bytes).map fun (message, rest) => (.businessMessageRejectMessage message, rest)
  else if tag = 7015 then (NewOrderSingleResponseMessage.decode bytes).map fun (message, rest) => (.newOrderSingleResponseMessage message, rest)
  else if tag = 7016 then (NewOrderIcebergResponseMessage.decode bytes).map fun (message, rest) => (.newOrderIcebergResponseMessage message, rest)
  else if tag = 7017 then (OrderCancelResponseMessage.decode bytes).map fun (message, rest) => (.orderCancelResponseMessage message, rest)
  else if tag = 7018 then (OrderReplaceResponseMessage.decode bytes).map fun (message, rest) => (.orderReplaceResponseMessage message, rest)
  else if tag = 7007 then (OrderMassCancelResponseMessage.decode bytes).map fun (message, rest) => (.orderMassCancelResponseMessage message, rest)
  else if tag = 7019 then (ExecutionSingleReportMessage.decode bytes).map fun (message, rest) => (.executionSingleReportMessage message, rest)
  else if tag = 7020 then (ExecutionMultilegReportMessage.decode bytes).map fun (message, rest) => (.executionMultilegReportMessage message, rest)
  else if tag = 7010 then (EmptyBookMessage.decode bytes).map fun (message, rest) => (.emptyBookMessage message, rest)
  else if tag = 7014 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else none

@[simp] theorem decode_encode (message : ServerPayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ServerPayload

/-- Server Message -/
structure ServerMessage where
  blockLength : BitVec 16
  schemaId : BitVec 16
  version : BitVec 16
  serverPayload : ServerPayload
  deriving DecidableEq, Repr

namespace ServerMessage

def encode (message : ServerMessage) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUIntLE 2 (ServerPayload.tag message.serverPayload)
    ++ (encodeUIntLE 2 message.schemaId
    ++ (encodeUIntLE 2 message.version
    ++ (ServerPayload.encode message.serverPayload))))

def decode (bytes : List UInt8) : Option (ServerMessage × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (templateId, bytes) ← decodeUIntLE 2 bytes
  let (schemaId, bytes) ← decodeUIntLE 2 bytes
  let (version, bytes) ← decodeUIntLE 2 bytes
  let (serverPayload, bytes) ← ServerPayload.decode templateId bytes
  pure ({ blockLength, schemaId, version, serverPayload }, bytes)

theorem encode_length_pos (message : ServerMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ServerMessage) : (encode message).length ≤ 98 := by
  unfold encode
  cases message.serverPayload with
  | establishmentAckMessage inner =>
    simp only [ServerPayload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, EstablishmentAckMessage.encode_length]
    omega
  | establishmentRejectMessage inner =>
    simp only [ServerPayload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, EstablishmentRejectMessage.encode_length]
    omega
  | terminateMessage inner =>
    simp only [ServerPayload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, TerminateMessage.encode_length]
    omega
  | retransmissionMessage inner =>
    simp only [ServerPayload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, RetransmissionMessage.encode_length]
    omega
  | sequenceMessage inner =>
    simp only [ServerPayload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, SequenceMessage.encode_length]
    omega
  | floodRejectMessage inner =>
    simp only [ServerPayload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, FloodRejectMessage.encode_length]
    omega
  | sessionRejectMessage inner =>
    simp only [ServerPayload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, SessionRejectMessage.encode_length]
    omega
  | businessMessageRejectMessage inner =>
    simp only [ServerPayload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, BusinessMessageRejectMessage.encode_length]
    omega
  | newOrderSingleResponseMessage inner =>
    simp only [ServerPayload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, NewOrderSingleResponseMessage.encode_length]
    omega
  | newOrderIcebergResponseMessage inner =>
    simp only [ServerPayload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, NewOrderIcebergResponseMessage.encode_length]
    omega
  | orderCancelResponseMessage inner =>
    simp only [ServerPayload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OrderCancelResponseMessage.encode_length]
    omega
  | orderReplaceResponseMessage inner =>
    simp only [ServerPayload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OrderReplaceResponseMessage.encode_length]
    omega
  | orderMassCancelResponseMessage inner =>
    simp only [ServerPayload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OrderMassCancelResponseMessage.encode_length]
    omega
  | executionSingleReportMessage inner =>
    simp only [ServerPayload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, ExecutionSingleReportMessage.encode_length]
    omega
  | executionMultilegReportMessage inner =>
    simp only [ServerPayload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, ExecutionMultilegReportMessage.encode_length]
    omega
  | emptyBookMessage inner =>
    simp only [ServerPayload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, EmptyBookMessage.encode_length]
    omega
  | systemEventMessage inner =>
    simp only [ServerPayload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, SystemEventMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : ServerMessage) (rest : List UInt8) :
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
  rw [ServerPayload.decode_encode, some_bind]
  rfl

end ServerMessage

/-- Server Packet -/
structure ServerPacket where
  serverMessage : List ServerMessage
  deriving DecidableEq, Repr

namespace ServerPacket

def encode (message : ServerPacket) : List UInt8 :=
  encodeMany ServerMessage.encode message.serverMessage

def decode (bytes : List UInt8) : Option ServerPacket := do
  let serverMessage ← decodeAll ServerMessage.decode bytes.length bytes
  pure { serverMessage }

theorem decode_encode (message : ServerPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany ServerMessage.encode ServerMessage.decode ServerMessage.decode_encode ServerMessage.encode_length_pos message.serverMessage _ (encodeMany_length_ge ServerMessage.encode ServerMessage.encode_length_pos message.serverMessage), some_bind]
  rfl

end ServerPacket

end Omi.MoexSpectraOrderentryTwimeV9120Server
