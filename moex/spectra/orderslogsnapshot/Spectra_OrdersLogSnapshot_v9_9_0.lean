import Wire

/-!
# Moscow Exchange SIMBA Spectra Orders Log Snapshot v9.9.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.MoexSpectraOrderslogsnapshotSimbaV990

/-- Md Entry Type: one byte code -/
def MdEntryType.codes : List UInt8 :=
  [0x30, 0x31, 0x4A]

inductive MdEntryType where
  | bid -- Bid
  | offer -- Offer
  | emptyBook -- Empty Book
  | unlisted (byte : { byte : UInt8 // byte ∉ MdEntryType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MdEntryType

def toByte : MdEntryType → UInt8
  | .bid => 0x30
  | .offer => 0x31
  | .emptyBook => 0x4A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MdEntryType :=
  if byte = 0x30 then .bid
  else if byte = 0x31 then .offer
  else .emptyBook

def ofByte (byte : UInt8) : MdEntryType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MdEntryType) : ofByte value.toByte = value := by
  cases value with
  | bid => decide
  | offer => decide
  | emptyBook => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MdEntryType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MdEntryType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MdEntryType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : MdEntryType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : MdEntryType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MdEntryType

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

/-- Order Book Snapshot Message No M D Entries Group: 57 bytes -/
structure OrderBookSnapshotMessageNoMDEntriesGroup where
  mdEntryIdInt64NullOptional : BitVec 64
  transactTime : BitVec 64
  mdEntryPxDecimal5NullOptional : BitVec 64
  mdEntrySizeInt64NullOptional : BitVec 64
  tradeIdInt64NullOptional : BitVec 64
  mdFlags : BitVec 64
  mdFlags2 : BitVec 64
  mdEntryType : MdEntryType
  deriving DecidableEq, Repr

namespace OrderBookSnapshotMessageNoMDEntriesGroup

def encode (message : OrderBookSnapshotMessageNoMDEntriesGroup) : List UInt8 :=
  encodeUIntLE 8 message.mdEntryIdInt64NullOptional
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.mdEntryPxDecimal5NullOptional
    ++ (encodeUIntLE 8 message.mdEntrySizeInt64NullOptional
    ++ (encodeUIntLE 8 message.tradeIdInt64NullOptional
    ++ (encodeUIntLE 8 message.mdFlags
    ++ (encodeUIntLE 8 message.mdFlags2
    ++ (MdEntryType.encode message.mdEntryType)))))))

def decode (bytes : List UInt8) : Option (OrderBookSnapshotMessageNoMDEntriesGroup × List UInt8) := do
  let (mdEntryIdInt64NullOptional, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (mdEntryPxDecimal5NullOptional, bytes) ← decodeUIntLE 8 bytes
  let (mdEntrySizeInt64NullOptional, bytes) ← decodeUIntLE 8 bytes
  let (tradeIdInt64NullOptional, bytes) ← decodeUIntLE 8 bytes
  let (mdFlags, bytes) ← decodeUIntLE 8 bytes
  let (mdFlags2, bytes) ← decodeUIntLE 8 bytes
  let (mdEntryType, bytes) ← MdEntryType.decode bytes
  pure ({ mdEntryIdInt64NullOptional, transactTime, mdEntryPxDecimal5NullOptional, mdEntrySizeInt64NullOptional, tradeIdInt64NullOptional, mdFlags, mdFlags2, mdEntryType }, bytes)

@[simp] theorem encode_length (message : OrderBookSnapshotMessageNoMDEntriesGroup) : (encode message).length = 57 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, MdEntryType.encode_length]

theorem encode_length_pos (message : OrderBookSnapshotMessageNoMDEntriesGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderBookSnapshotMessageNoMDEntriesGroup) (rest : List UInt8) :
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
  rw [MdEntryType.decode_encode, some_bind]
  rfl

end OrderBookSnapshotMessageNoMDEntriesGroup

/-- Order Book Snapshot Message No M D Entries Groups -/
structure OrderBookSnapshotMessageNoMDEntriesGroups where
  blockLength : BitVec 16
  orderBookSnapshotMessageNoMDEntriesGroup : Bounded 1 OrderBookSnapshotMessageNoMDEntriesGroup
  deriving DecidableEq, Repr

namespace OrderBookSnapshotMessageNoMDEntriesGroups

def encode (message : OrderBookSnapshotMessageNoMDEntriesGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.orderBookSnapshotMessageNoMDEntriesGroup.val.length)
    ++ (encodeMany OrderBookSnapshotMessageNoMDEntriesGroup.encode message.orderBookSnapshotMessageNoMDEntriesGroup.val))

def decode (bytes : List UInt8) : Option (OrderBookSnapshotMessageNoMDEntriesGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroupUint8, bytes) ← decodeUInt 1 bytes
  let (orderBookSnapshotMessageNoMDEntriesGroup_, bytes) ← decodeMany OrderBookSnapshotMessageNoMDEntriesGroup.decode numInGroupUint8.toNat bytes
  if fits_orderBookSnapshotMessageNoMDEntriesGroup : orderBookSnapshotMessageNoMDEntriesGroup_.length < 256 ^ 1 then
    pure ({ blockLength, orderBookSnapshotMessageNoMDEntriesGroup := ⟨orderBookSnapshotMessageNoMDEntriesGroup_, fits_orderBookSnapshotMessageNoMDEntriesGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : OrderBookSnapshotMessageNoMDEntriesGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrderBookSnapshotMessageNoMDEntriesGroups) : (encode message).length ≤ 14538 := by
  have bound_orderBookSnapshotMessageNoMDEntriesGroup := message.orderBookSnapshotMessageNoMDEntriesGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const OrderBookSnapshotMessageNoMDEntriesGroup.encode 57 OrderBookSnapshotMessageNoMDEntriesGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : OrderBookSnapshotMessageNoMDEntriesGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 OrderBookSnapshotMessageNoMDEntriesGroup.encode OrderBookSnapshotMessageNoMDEntriesGroup.decode OrderBookSnapshotMessageNoMDEntriesGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.orderBookSnapshotMessageNoMDEntriesGroup.length_lt]
  rfl

end OrderBookSnapshotMessageNoMDEntriesGroups

/-- Order Book Snapshot Message -/
structure OrderBookSnapshotMessage where
  securityId : BitVec 32
  lastMsgSeqNumProcessedUInt32 : BitVec 32
  rptSeq : BitVec 32
  exchangeTradingSessionId : BitVec 32
  orderBookSnapshotMessageNoMDEntriesGroups : OrderBookSnapshotMessageNoMDEntriesGroups
  deriving DecidableEq, Repr

namespace OrderBookSnapshotMessage

def encode (message : OrderBookSnapshotMessage) : List UInt8 :=
  encodeUIntLE 4 message.securityId
    ++ (encodeUIntLE 4 message.lastMsgSeqNumProcessedUInt32
    ++ (encodeUIntLE 4 message.rptSeq
    ++ (encodeUIntLE 4 message.exchangeTradingSessionId
    ++ (OrderBookSnapshotMessageNoMDEntriesGroups.encode message.orderBookSnapshotMessageNoMDEntriesGroups))))

def decode (bytes : List UInt8) : Option (OrderBookSnapshotMessage × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (lastMsgSeqNumProcessedUInt32, bytes) ← decodeUIntLE 4 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  let (exchangeTradingSessionId, bytes) ← decodeUIntLE 4 bytes
  let (orderBookSnapshotMessageNoMDEntriesGroups, bytes) ← OrderBookSnapshotMessageNoMDEntriesGroups.decode bytes
  pure ({ securityId, lastMsgSeqNumProcessedUInt32, rptSeq, exchangeTradingSessionId, orderBookSnapshotMessageNoMDEntriesGroups }, bytes)

theorem encode_length_pos (message : OrderBookSnapshotMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrderBookSnapshotMessage) : (encode message).length ≤ 14554 := by
  have bound_orderBookSnapshotMessageNoMDEntriesGroups := OrderBookSnapshotMessageNoMDEntriesGroups.encode_length_le message.orderBookSnapshotMessageNoMDEntriesGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
  omega

@[simp] theorem decode_encode (message : OrderBookSnapshotMessage) (rest : List UInt8) :
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
  rw [OrderBookSnapshotMessageNoMDEntriesGroups.decode_encode, some_bind]
  rfl

end OrderBookSnapshotMessage

/-- Any Payload, selected by Template Id -/
inductive Payload where
  | heartbeatMessage (message : HeartbeatMessage) -- 1
  | sequenceResetMessage (message : SequenceResetMessage) -- 2
  | orderBookSnapshotMessage (message : OrderBookSnapshotMessage) -- 17
  deriving DecidableEq, Repr

namespace Payload

/-- The Template Id each message is sent under -/
def tag : Payload → BitVec 16
  | .heartbeatMessage _ => 1
  | .sequenceResetMessage _ => 2
  | .orderBookSnapshotMessage _ => 17

def encode : Payload → List UInt8
  | .heartbeatMessage message => HeartbeatMessage.encode message
  | .sequenceResetMessage message => SequenceResetMessage.encode message
  | .orderBookSnapshotMessage message => OrderBookSnapshotMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 14554 := by
  cases message with
  | heartbeatMessage inner =>
    simp only [encode, HeartbeatMessage.encode_length]
    omega
  | sequenceResetMessage inner =>
    simp only [encode, SequenceResetMessage.encode_length]
    omega
  | orderBookSnapshotMessage inner =>
    have bound_inner := OrderBookSnapshotMessage.encode_length_le inner
    simp only [encode]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 1 then (HeartbeatMessage.decode bytes).map fun (message, rest) => (.heartbeatMessage message, rest)
  else if tag = 2 then (SequenceResetMessage.decode bytes).map fun (message, rest) => (.sequenceResetMessage message, rest)
  else if tag = 17 then (OrderBookSnapshotMessage.decode bytes).map fun (message, rest) => (.orderBookSnapshotMessage message, rest)
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
theorem encode_length_le (message : Message) : (encode message).length ≤ 14562 := by
  unfold encode
  cases message.payload with
  | heartbeatMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, HeartbeatMessage.encode_length]
    omega
  | sequenceResetMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, SequenceResetMessage.encode_length]
    omega
  | orderBookSnapshotMessage inner =>
    have bound_inner := OrderBookSnapshotMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
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
  message : List Message
  deriving DecidableEq, Repr

namespace UdpPacket

def encode (message : UdpPacket) : List UInt8 :=
  MarketDataPacketHeader.encode message.marketDataPacketHeader
    ++ (encodeMany Message.encode message.message)

def decode (bytes : List UInt8) : Option UdpPacket := do
  let (marketDataPacketHeader, bytes) ← MarketDataPacketHeader.decode bytes
  let message ← decodeAll Message.decode bytes.length bytes
  pure { marketDataPacketHeader, message }

theorem encode_length_pos (message : UdpPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [MarketDataPacketHeader.encode_length, List.length_append]
  omega

theorem decode_encode (message : UdpPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [MarketDataPacketHeader.decode_encode, some_bind]
  dsimp only
  rw [decodeAll_encodeMany Message.encode Message.decode Message.decode_encode Message.encode_length_pos message.message _ (encodeMany_length_ge Message.encode Message.encode_length_pos message.message), some_bind]
  rfl

end UdpPacket

end Omi.MoexSpectraOrderslogsnapshotSimbaV990
