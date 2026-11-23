import Wire

/-!
# Moscow Exchange TWIME Spectra Order Entry v9.12.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.

Note: Client Flags is a bit field set, proven as its 1 byte integer rather than bit by bit

Note: Security Type is a bit field set, proven as its 1 byte integer rather than bit by bit

Note: Client Message is not framed: its size rule is not the length plus a constant the frame proof
covers

License: MIT No Attribution
-/

namespace Omi.MoexSpectraOrderentryTwimeV9120Client

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

/-- Establish Message: 32 bytes -/
structure EstablishMessage where
  timestamp : BitVec 64
  keepaliveInterval : BitVec 32
  credentials : Alpha 20
  deriving DecidableEq, Repr

namespace EstablishMessage

def encode (message : EstablishMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 4 message.keepaliveInterval
    ++ (Alpha.encode message.credentials))

def decode (bytes : List UInt8) : Option (EstablishMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (keepaliveInterval, bytes) ← decodeUIntLE 4 bytes
  let (credentials, bytes) ← Alpha.decode 20 bytes
  pure ({ timestamp, keepaliveInterval, credentials }, bytes)

@[simp] theorem encode_length (message : EstablishMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : EstablishMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EstablishMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end EstablishMessage

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

/-- Retransmit Request Message: 20 bytes -/
structure RetransmitRequestMessage where
  timestamp : BitVec 64
  fromSeqNo : BitVec 64
  count : BitVec 32
  deriving DecidableEq, Repr

namespace RetransmitRequestMessage

def encode (message : RetransmitRequestMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.fromSeqNo
    ++ (encodeUIntLE 4 message.count))

def decode (bytes : List UInt8) : Option (RetransmitRequestMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (fromSeqNo, bytes) ← decodeUIntLE 8 bytes
  let (count, bytes) ← decodeUIntLE 4 bytes
  pure ({ timestamp, fromSeqNo, count }, bytes)

@[simp] theorem encode_length (message : RetransmitRequestMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : RetransmitRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RetransmitRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end RetransmitRequestMessage

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

/-- New Order Single Message: 47 bytes -/
structure NewOrderSingleMessage where
  clOrdId : BitVec 64
  expireDate : BitVec 64
  price : BitVec 64
  securityId : BitVec 32
  clOrdLinkId : BitVec 32
  orderQty : BitVec 32
  complianceId : ComplianceId
  timeInForce : BitVec 8
  side : BitVec 8
  clientFlags : BitVec 8
  account : Alpha 7
  deriving DecidableEq, Repr

namespace NewOrderSingleMessage

def encode (message : NewOrderSingleMessage) : List UInt8 :=
  encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.expireDate
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.securityId
    ++ (encodeUIntLE 4 message.clOrdLinkId
    ++ (encodeUIntLE 4 message.orderQty
    ++ (ComplianceId.encode message.complianceId
    ++ (encodeUInt 1 message.timeInForce
    ++ (encodeUInt 1 message.side
    ++ (encodeUIntLE 1 message.clientFlags
    ++ (Alpha.encode message.account))))))))))

def decode (bytes : List UInt8) : Option (NewOrderSingleMessage × List UInt8) := do
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (expireDate, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (clOrdLinkId, bytes) ← decodeUIntLE 4 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (complianceId, bytes) ← ComplianceId.decode bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (clientFlags, bytes) ← decodeUIntLE 1 bytes
  let (account, bytes) ← Alpha.decode 7 bytes
  pure ({ clOrdId, expireDate, price, securityId, clOrdLinkId, orderQty, complianceId, timeInForce, side, clientFlags, account }, bytes)

@[simp] theorem encode_length (message : NewOrderSingleMessage) : (encode message).length = 47 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, ComplianceId.encode_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : NewOrderSingleMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewOrderSingleMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, ComplianceId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end NewOrderSingleMessage

/-- New Order Iceberg Message: 54 bytes -/
structure NewOrderIcebergMessage where
  clOrdId : BitVec 64
  expireDate : BitVec 64
  price : BitVec 64
  securityId : BitVec 32
  clOrdLinkId : BitVec 32
  displayQty : BitVec 32
  displayVarianceQty : BitVec 32
  orderQty : BitVec 32
  complianceId : ComplianceId
  side : BitVec 8
  clientFlags : BitVec 8
  account : Alpha 7
  deriving DecidableEq, Repr

namespace NewOrderIcebergMessage

def encode (message : NewOrderIcebergMessage) : List UInt8 :=
  encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.expireDate
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.securityId
    ++ (encodeUIntLE 4 message.clOrdLinkId
    ++ (encodeUIntLE 4 message.displayQty
    ++ (encodeUIntLE 4 message.displayVarianceQty
    ++ (encodeUIntLE 4 message.orderQty
    ++ (ComplianceId.encode message.complianceId
    ++ (encodeUInt 1 message.side
    ++ (encodeUIntLE 1 message.clientFlags
    ++ (Alpha.encode message.account)))))))))))

def decode (bytes : List UInt8) : Option (NewOrderIcebergMessage × List UInt8) := do
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (expireDate, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (clOrdLinkId, bytes) ← decodeUIntLE 4 bytes
  let (displayQty, bytes) ← decodeUIntLE 4 bytes
  let (displayVarianceQty, bytes) ← decodeUIntLE 4 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (complianceId, bytes) ← ComplianceId.decode bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (clientFlags, bytes) ← decodeUIntLE 1 bytes
  let (account, bytes) ← Alpha.decode 7 bytes
  pure ({ clOrdId, expireDate, price, securityId, clOrdLinkId, displayQty, displayVarianceQty, orderQty, complianceId, side, clientFlags, account }, bytes)

@[simp] theorem encode_length (message : NewOrderIcebergMessage) : (encode message).length = 54 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, ComplianceId.encode_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : NewOrderIcebergMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewOrderIcebergMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, ComplianceId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end NewOrderIcebergMessage

/-- New Order Iceberg X Message: 55 bytes -/
structure NewOrderIcebergXMessage where
  clOrdId : BitVec 64
  expireDate : BitVec 64
  price : BitVec 64
  securityId : BitVec 32
  clOrdLinkId : BitVec 32
  displayQty : BitVec 32
  displayVarianceQty : BitVec 32
  orderQty : BitVec 32
  complianceId : ComplianceId
  timeInForce : BitVec 8
  side : BitVec 8
  clientFlags : BitVec 8
  account : Alpha 7
  deriving DecidableEq, Repr

namespace NewOrderIcebergXMessage

def encode (message : NewOrderIcebergXMessage) : List UInt8 :=
  encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.expireDate
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.securityId
    ++ (encodeUIntLE 4 message.clOrdLinkId
    ++ (encodeUIntLE 4 message.displayQty
    ++ (encodeUIntLE 4 message.displayVarianceQty
    ++ (encodeUIntLE 4 message.orderQty
    ++ (ComplianceId.encode message.complianceId
    ++ (encodeUInt 1 message.timeInForce
    ++ (encodeUInt 1 message.side
    ++ (encodeUIntLE 1 message.clientFlags
    ++ (Alpha.encode message.account))))))))))))

def decode (bytes : List UInt8) : Option (NewOrderIcebergXMessage × List UInt8) := do
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (expireDate, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (clOrdLinkId, bytes) ← decodeUIntLE 4 bytes
  let (displayQty, bytes) ← decodeUIntLE 4 bytes
  let (displayVarianceQty, bytes) ← decodeUIntLE 4 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (complianceId, bytes) ← ComplianceId.decode bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (clientFlags, bytes) ← decodeUIntLE 1 bytes
  let (account, bytes) ← Alpha.decode 7 bytes
  pure ({ clOrdId, expireDate, price, securityId, clOrdLinkId, displayQty, displayVarianceQty, orderQty, complianceId, timeInForce, side, clientFlags, account }, bytes)

@[simp] theorem encode_length (message : NewOrderIcebergXMessage) : (encode message).length = 55 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, ComplianceId.encode_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : NewOrderIcebergXMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewOrderIcebergXMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, ComplianceId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end NewOrderIcebergXMessage

/-- Order Cancel Request Message: 28 bytes -/
structure OrderCancelRequestMessage where
  clOrdId : BitVec 64
  orderId : BitVec 64
  securityId : BitVec 32
  clientFlags : BitVec 8
  account : Alpha 7
  deriving DecidableEq, Repr

namespace OrderCancelRequestMessage

def encode (message : OrderCancelRequestMessage) : List UInt8 :=
  encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 4 message.securityId
    ++ (encodeUIntLE 1 message.clientFlags
    ++ (Alpha.encode message.account))))

def decode (bytes : List UInt8) : Option (OrderCancelRequestMessage × List UInt8) := do
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (clientFlags, bytes) ← decodeUIntLE 1 bytes
  let (account, bytes) ← Alpha.decode 7 bytes
  pure ({ clOrdId, orderId, securityId, clientFlags, account }, bytes)

@[simp] theorem encode_length (message : OrderCancelRequestMessage) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderCancelRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancelRequestMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderCancelRequestMessage

/-- Order Iceberg Cancel Request Message: 28 bytes -/
structure OrderIcebergCancelRequestMessage where
  clOrdId : BitVec 64
  orderId : BitVec 64
  securityId : BitVec 32
  clientFlags : BitVec 8
  account : Alpha 7
  deriving DecidableEq, Repr

namespace OrderIcebergCancelRequestMessage

def encode (message : OrderIcebergCancelRequestMessage) : List UInt8 :=
  encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 4 message.securityId
    ++ (encodeUIntLE 1 message.clientFlags
    ++ (Alpha.encode message.account))))

def decode (bytes : List UInt8) : Option (OrderIcebergCancelRequestMessage × List UInt8) := do
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (clientFlags, bytes) ← decodeUIntLE 1 bytes
  let (account, bytes) ← Alpha.decode 7 bytes
  pure ({ clOrdId, orderId, securityId, clientFlags, account }, bytes)

@[simp] theorem encode_length (message : OrderIcebergCancelRequestMessage) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderIcebergCancelRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderIcebergCancelRequestMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderIcebergCancelRequestMessage

/-- Order Replace Request Message: 46 bytes -/
structure OrderReplaceRequestMessage where
  clOrdId : BitVec 64
  orderId : BitVec 64
  price : BitVec 64
  orderQty : BitVec 32
  clOrdLinkId : BitVec 32
  securityId : BitVec 32
  complianceId : ComplianceId
  mode : BitVec 8
  clientFlags : BitVec 8
  account : Alpha 7
  deriving DecidableEq, Repr

namespace OrderReplaceRequestMessage

def encode (message : OrderReplaceRequestMessage) : List UInt8 :=
  encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.orderQty
    ++ (encodeUIntLE 4 message.clOrdLinkId
    ++ (encodeUIntLE 4 message.securityId
    ++ (ComplianceId.encode message.complianceId
    ++ (encodeUInt 1 message.mode
    ++ (encodeUIntLE 1 message.clientFlags
    ++ (Alpha.encode message.account)))))))))

def decode (bytes : List UInt8) : Option (OrderReplaceRequestMessage × List UInt8) := do
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (clOrdLinkId, bytes) ← decodeUIntLE 4 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (complianceId, bytes) ← ComplianceId.decode bytes
  let (mode, bytes) ← decodeUInt 1 bytes
  let (clientFlags, bytes) ← decodeUIntLE 1 bytes
  let (account, bytes) ← Alpha.decode 7 bytes
  pure ({ clOrdId, orderId, price, orderQty, clOrdLinkId, securityId, complianceId, mode, clientFlags, account }, bytes)

@[simp] theorem encode_length (message : OrderReplaceRequestMessage) : (encode message).length = 46 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, ComplianceId.encode_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderReplaceRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderReplaceRequestMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, ComplianceId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderReplaceRequestMessage

/-- Order Iceberg Replace Request Message: 41 bytes -/
structure OrderIcebergReplaceRequestMessage where
  clOrdId : BitVec 64
  orderId : BitVec 64
  price : BitVec 64
  clOrdLinkId : BitVec 32
  securityId : BitVec 32
  complianceId : ComplianceId
  clientFlags : BitVec 8
  account : Alpha 7
  deriving DecidableEq, Repr

namespace OrderIcebergReplaceRequestMessage

def encode (message : OrderIcebergReplaceRequestMessage) : List UInt8 :=
  encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.clOrdLinkId
    ++ (encodeUIntLE 4 message.securityId
    ++ (ComplianceId.encode message.complianceId
    ++ (encodeUIntLE 1 message.clientFlags
    ++ (Alpha.encode message.account)))))))

def decode (bytes : List UInt8) : Option (OrderIcebergReplaceRequestMessage × List UInt8) := do
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (clOrdLinkId, bytes) ← decodeUIntLE 4 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (complianceId, bytes) ← ComplianceId.decode bytes
  let (clientFlags, bytes) ← decodeUIntLE 1 bytes
  let (account, bytes) ← Alpha.decode 7 bytes
  pure ({ clOrdId, orderId, price, clOrdLinkId, securityId, complianceId, clientFlags, account }, bytes)

@[simp] theorem encode_length (message : OrderIcebergReplaceRequestMessage) : (encode message).length = 41 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, ComplianceId.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderIcebergReplaceRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderIcebergReplaceRequestMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, ComplianceId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderIcebergReplaceRequestMessage

/-- Order Mass Cancel Request Message: 50 bytes -/
structure OrderMassCancelRequestMessage where
  clOrdId : BitVec 64
  clOrdLinkId : BitVec 32
  securityId : BitVec 32
  securityType : BitVec 8
  side : BitVec 8
  account : Alpha 7
  securityGroup : Alpha 25
  deriving DecidableEq, Repr

namespace OrderMassCancelRequestMessage

def encode (message : OrderMassCancelRequestMessage) : List UInt8 :=
  encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 4 message.clOrdLinkId
    ++ (encodeUIntLE 4 message.securityId
    ++ (encodeUIntLE 1 message.securityType
    ++ (encodeUInt 1 message.side
    ++ (Alpha.encode message.account
    ++ (Alpha.encode message.securityGroup))))))

def decode (bytes : List UInt8) : Option (OrderMassCancelRequestMessage × List UInt8) := do
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdLinkId, bytes) ← decodeUIntLE 4 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (securityType, bytes) ← decodeUIntLE 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (account, bytes) ← Alpha.decode 7 bytes
  let (securityGroup, bytes) ← Alpha.decode 25 bytes
  pure ({ clOrdId, clOrdLinkId, securityId, securityType, side, account, securityGroup }, bytes)

@[simp] theorem encode_length (message : OrderMassCancelRequestMessage) : (encode message).length = 50 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderMassCancelRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderMassCancelRequestMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderMassCancelRequestMessage

/-- Order Mass Cancel By Bf Limit Request Message: 15 bytes -/
structure OrderMassCancelByBfLimitRequestMessage where
  clOrdId : BitVec 64
  account : Alpha 7
  deriving DecidableEq, Repr

namespace OrderMassCancelByBfLimitRequestMessage

def encode (message : OrderMassCancelByBfLimitRequestMessage) : List UInt8 :=
  encodeUIntLE 8 message.clOrdId
    ++ (Alpha.encode message.account)

def decode (bytes : List UInt8) : Option (OrderMassCancelByBfLimitRequestMessage × List UInt8) := do
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (account, bytes) ← Alpha.decode 7 bytes
  pure ({ clOrdId, account }, bytes)

@[simp] theorem encode_length (message : OrderMassCancelByBfLimitRequestMessage) : (encode message).length = 15 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderMassCancelByBfLimitRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderMassCancelByBfLimitRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderMassCancelByBfLimitRequestMessage

/-- Any Client Payload, selected by Template Id -/
inductive ClientPayload where
  | establishMessage (message : EstablishMessage) -- 5000
  | terminateMessage (message : TerminateMessage) -- 5003
  | retransmitRequestMessage (message : RetransmitRequestMessage) -- 5004
  | sequenceMessage (message : SequenceMessage) -- 5006
  | newOrderSingleMessage (message : NewOrderSingleMessage) -- 6000
  | newOrderIcebergMessage (message : NewOrderIcebergMessage) -- 6008
  | newOrderIcebergXMessage (message : NewOrderIcebergXMessage) -- 6011
  | orderCancelRequestMessage (message : OrderCancelRequestMessage) -- 6006
  | orderIcebergCancelRequestMessage (message : OrderIcebergCancelRequestMessage) -- 6009
  | orderReplaceRequestMessage (message : OrderReplaceRequestMessage) -- 6007
  | orderIcebergReplaceRequestMessage (message : OrderIcebergReplaceRequestMessage) -- 6010
  | orderMassCancelRequestMessage (message : OrderMassCancelRequestMessage) -- 6004
  | orderMassCancelByBfLimitRequestMessage (message : OrderMassCancelByBfLimitRequestMessage) -- 6005
  deriving DecidableEq, Repr

namespace ClientPayload

/-- The Template Id each message is sent under -/
def tag : ClientPayload → BitVec 16
  | .establishMessage _ => 5000
  | .terminateMessage _ => 5003
  | .retransmitRequestMessage _ => 5004
  | .sequenceMessage _ => 5006
  | .newOrderSingleMessage _ => 6000
  | .newOrderIcebergMessage _ => 6008
  | .newOrderIcebergXMessage _ => 6011
  | .orderCancelRequestMessage _ => 6006
  | .orderIcebergCancelRequestMessage _ => 6009
  | .orderReplaceRequestMessage _ => 6007
  | .orderIcebergReplaceRequestMessage _ => 6010
  | .orderMassCancelRequestMessage _ => 6004
  | .orderMassCancelByBfLimitRequestMessage _ => 6005

def encode : ClientPayload → List UInt8
  | .establishMessage message => EstablishMessage.encode message
  | .terminateMessage message => TerminateMessage.encode message
  | .retransmitRequestMessage message => RetransmitRequestMessage.encode message
  | .sequenceMessage message => SequenceMessage.encode message
  | .newOrderSingleMessage message => NewOrderSingleMessage.encode message
  | .newOrderIcebergMessage message => NewOrderIcebergMessage.encode message
  | .newOrderIcebergXMessage message => NewOrderIcebergXMessage.encode message
  | .orderCancelRequestMessage message => OrderCancelRequestMessage.encode message
  | .orderIcebergCancelRequestMessage message => OrderIcebergCancelRequestMessage.encode message
  | .orderReplaceRequestMessage message => OrderReplaceRequestMessage.encode message
  | .orderIcebergReplaceRequestMessage message => OrderIcebergReplaceRequestMessage.encode message
  | .orderMassCancelRequestMessage message => OrderMassCancelRequestMessage.encode message
  | .orderMassCancelByBfLimitRequestMessage message => OrderMassCancelByBfLimitRequestMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ClientPayload) : (encode message).length ≤ 55 := by
  cases message with
  | establishMessage inner =>
    simp only [encode, EstablishMessage.encode_length]
    omega
  | terminateMessage inner =>
    simp only [encode, TerminateMessage.encode_length]
    omega
  | retransmitRequestMessage inner =>
    simp only [encode, RetransmitRequestMessage.encode_length]
    omega
  | sequenceMessage inner =>
    simp only [encode, SequenceMessage.encode_length]
    omega
  | newOrderSingleMessage inner =>
    simp only [encode, NewOrderSingleMessage.encode_length]
    omega
  | newOrderIcebergMessage inner =>
    simp only [encode, NewOrderIcebergMessage.encode_length]
    omega
  | newOrderIcebergXMessage inner =>
    simp only [encode, NewOrderIcebergXMessage.encode_length]
    omega
  | orderCancelRequestMessage inner =>
    simp only [encode, OrderCancelRequestMessage.encode_length]
    omega
  | orderIcebergCancelRequestMessage inner =>
    simp only [encode, OrderIcebergCancelRequestMessage.encode_length]
    omega
  | orderReplaceRequestMessage inner =>
    simp only [encode, OrderReplaceRequestMessage.encode_length]
    omega
  | orderIcebergReplaceRequestMessage inner =>
    simp only [encode, OrderIcebergReplaceRequestMessage.encode_length]
    omega
  | orderMassCancelRequestMessage inner =>
    simp only [encode, OrderMassCancelRequestMessage.encode_length]
    omega
  | orderMassCancelByBfLimitRequestMessage inner =>
    simp only [encode, OrderMassCancelByBfLimitRequestMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (ClientPayload × List UInt8) :=
  if tag = 5000 then (EstablishMessage.decode bytes).map fun (message, rest) => (.establishMessage message, rest)
  else if tag = 5003 then (TerminateMessage.decode bytes).map fun (message, rest) => (.terminateMessage message, rest)
  else if tag = 5004 then (RetransmitRequestMessage.decode bytes).map fun (message, rest) => (.retransmitRequestMessage message, rest)
  else if tag = 5006 then (SequenceMessage.decode bytes).map fun (message, rest) => (.sequenceMessage message, rest)
  else if tag = 6000 then (NewOrderSingleMessage.decode bytes).map fun (message, rest) => (.newOrderSingleMessage message, rest)
  else if tag = 6008 then (NewOrderIcebergMessage.decode bytes).map fun (message, rest) => (.newOrderIcebergMessage message, rest)
  else if tag = 6011 then (NewOrderIcebergXMessage.decode bytes).map fun (message, rest) => (.newOrderIcebergXMessage message, rest)
  else if tag = 6006 then (OrderCancelRequestMessage.decode bytes).map fun (message, rest) => (.orderCancelRequestMessage message, rest)
  else if tag = 6009 then (OrderIcebergCancelRequestMessage.decode bytes).map fun (message, rest) => (.orderIcebergCancelRequestMessage message, rest)
  else if tag = 6007 then (OrderReplaceRequestMessage.decode bytes).map fun (message, rest) => (.orderReplaceRequestMessage message, rest)
  else if tag = 6010 then (OrderIcebergReplaceRequestMessage.decode bytes).map fun (message, rest) => (.orderIcebergReplaceRequestMessage message, rest)
  else if tag = 6004 then (OrderMassCancelRequestMessage.decode bytes).map fun (message, rest) => (.orderMassCancelRequestMessage message, rest)
  else if tag = 6005 then (OrderMassCancelByBfLimitRequestMessage.decode bytes).map fun (message, rest) => (.orderMassCancelByBfLimitRequestMessage message, rest)
  else none

@[simp] theorem decode_encode (message : ClientPayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ClientPayload

/-- Client Message -/
structure ClientMessage where
  blockLength : BitVec 16
  schemaId : BitVec 16
  version : BitVec 16
  clientPayload : ClientPayload
  deriving DecidableEq, Repr

namespace ClientMessage

def encode (message : ClientMessage) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUIntLE 2 (ClientPayload.tag message.clientPayload)
    ++ (encodeUIntLE 2 message.schemaId
    ++ (encodeUIntLE 2 message.version
    ++ (ClientPayload.encode message.clientPayload))))

def decode (bytes : List UInt8) : Option (ClientMessage × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (templateId, bytes) ← decodeUIntLE 2 bytes
  let (schemaId, bytes) ← decodeUIntLE 2 bytes
  let (version, bytes) ← decodeUIntLE 2 bytes
  let (clientPayload, bytes) ← ClientPayload.decode templateId bytes
  pure ({ blockLength, schemaId, version, clientPayload }, bytes)

theorem encode_length_pos (message : ClientMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ClientMessage) : (encode message).length ≤ 63 := by
  unfold encode
  cases message.clientPayload with
  | establishMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, EstablishMessage.encode_length]
    omega
  | terminateMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, TerminateMessage.encode_length]
    omega
  | retransmitRequestMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, RetransmitRequestMessage.encode_length]
    omega
  | sequenceMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, SequenceMessage.encode_length]
    omega
  | newOrderSingleMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, NewOrderSingleMessage.encode_length]
    omega
  | newOrderIcebergMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, NewOrderIcebergMessage.encode_length]
    omega
  | newOrderIcebergXMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, NewOrderIcebergXMessage.encode_length]
    omega
  | orderCancelRequestMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OrderCancelRequestMessage.encode_length]
    omega
  | orderIcebergCancelRequestMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OrderIcebergCancelRequestMessage.encode_length]
    omega
  | orderReplaceRequestMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OrderReplaceRequestMessage.encode_length]
    omega
  | orderIcebergReplaceRequestMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OrderIcebergReplaceRequestMessage.encode_length]
    omega
  | orderMassCancelRequestMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OrderMassCancelRequestMessage.encode_length]
    omega
  | orderMassCancelByBfLimitRequestMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OrderMassCancelByBfLimitRequestMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : ClientMessage) (rest : List UInt8) :
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
  rw [ClientPayload.decode_encode, some_bind]
  rfl

end ClientMessage

/-- Client Packet -/
structure ClientPacket where
  clientMessage : List ClientMessage
  deriving DecidableEq, Repr

namespace ClientPacket

def encode (message : ClientPacket) : List UInt8 :=
  encodeMany ClientMessage.encode message.clientMessage

def decode (bytes : List UInt8) : Option ClientPacket := do
  let clientMessage ← decodeAll ClientMessage.decode bytes.length bytes
  pure { clientMessage }

theorem decode_encode (message : ClientPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany ClientMessage.encode ClientMessage.decode ClientMessage.decode_encode ClientMessage.encode_length_pos message.clientMessage _ (encodeMany_length_ge ClientMessage.encode ClientMessage.encode_length_pos message.clientMessage), some_bind]
  rfl

end ClientPacket

end Omi.MoexSpectraOrderentryTwimeV9120Client
