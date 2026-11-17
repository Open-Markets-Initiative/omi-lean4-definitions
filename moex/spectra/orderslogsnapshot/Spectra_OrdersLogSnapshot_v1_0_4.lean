import Wire

/-!
# Moscow Exchange SIMBA Spectra Orders Log Snapshot v1.0.4

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.

Note: Msg Flags is a bit field set, proven as its 2 byte integer rather than bit by bit

Note: Md Flags is a bit field set, proven as its 8 byte integer rather than bit by bit

License: MIT No Attribution
-/

namespace Omi.MoexSpectraOrderslogsnapshotSimbaV104

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

/-- Order Book Snapshot Message No Md Entries Group: 49 bytes -/
structure OrderBookSnapshotMessageNoMdEntriesGroup where
  mdEntryIdOptional : BitVec 64
  transactTime : BitVec 64
  mdEntryPxOptional : BitVec 64
  mdEntrySizeOptional : BitVec 64
  tradeIdOptional : BitVec 64
  mdFlags : BitVec 64
  mdEntryType : MdEntryType
  deriving DecidableEq, Repr

namespace OrderBookSnapshotMessageNoMdEntriesGroup

def encode (message : OrderBookSnapshotMessageNoMdEntriesGroup) : List UInt8 :=
  encodeUIntLE 8 message.mdEntryIdOptional
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.mdEntryPxOptional
    ++ (encodeUIntLE 8 message.mdEntrySizeOptional
    ++ (encodeUIntLE 8 message.tradeIdOptional
    ++ (encodeUIntLE 8 message.mdFlags
    ++ (MdEntryType.encode message.mdEntryType))))))

def decode (bytes : List UInt8) : Option (OrderBookSnapshotMessageNoMdEntriesGroup × List UInt8) := do
  let (mdEntryIdOptional, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (mdEntryPxOptional, bytes) ← decodeUIntLE 8 bytes
  let (mdEntrySizeOptional, bytes) ← decodeUIntLE 8 bytes
  let (tradeIdOptional, bytes) ← decodeUIntLE 8 bytes
  let (mdFlags, bytes) ← decodeUIntLE 8 bytes
  let (mdEntryType, bytes) ← MdEntryType.decode bytes
  pure ({ mdEntryIdOptional, transactTime, mdEntryPxOptional, mdEntrySizeOptional, tradeIdOptional, mdFlags, mdEntryType }, bytes)

@[simp] theorem encode_length (message : OrderBookSnapshotMessageNoMdEntriesGroup) : (encode message).length = 49 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, MdEntryType.encode_length]

theorem encode_length_pos (message : OrderBookSnapshotMessageNoMdEntriesGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderBookSnapshotMessageNoMdEntriesGroup) (rest : List UInt8) :
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
  rw [MdEntryType.decode_encode, some_bind]
  rfl

end OrderBookSnapshotMessageNoMdEntriesGroup

/-- Order Book Snapshot Message No Md Entries Groups -/
structure OrderBookSnapshotMessageNoMdEntriesGroups where
  blockLength : BitVec 16
  orderBookSnapshotMessageNoMdEntriesGroup : Bounded 1 OrderBookSnapshotMessageNoMdEntriesGroup
  deriving DecidableEq, Repr

namespace OrderBookSnapshotMessageNoMdEntriesGroups

def encode (message : OrderBookSnapshotMessageNoMdEntriesGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.orderBookSnapshotMessageNoMdEntriesGroup.val.length)
    ++ (encodeMany OrderBookSnapshotMessageNoMdEntriesGroup.encode message.orderBookSnapshotMessageNoMdEntriesGroup.val))

def decode (bytes : List UInt8) : Option (OrderBookSnapshotMessageNoMdEntriesGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (orderBookSnapshotMessageNoMdEntriesGroup_, bytes) ← decodeMany OrderBookSnapshotMessageNoMdEntriesGroup.decode numInGroup.toNat bytes
  if fits_orderBookSnapshotMessageNoMdEntriesGroup : orderBookSnapshotMessageNoMdEntriesGroup_.length < 256 ^ 1 then
    pure ({ blockLength, orderBookSnapshotMessageNoMdEntriesGroup := ⟨orderBookSnapshotMessageNoMdEntriesGroup_, fits_orderBookSnapshotMessageNoMdEntriesGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : OrderBookSnapshotMessageNoMdEntriesGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrderBookSnapshotMessageNoMdEntriesGroups) : (encode message).length ≤ 12498 := by
  have bound_orderBookSnapshotMessageNoMdEntriesGroup := message.orderBookSnapshotMessageNoMdEntriesGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const OrderBookSnapshotMessageNoMdEntriesGroup.encode 49 OrderBookSnapshotMessageNoMdEntriesGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : OrderBookSnapshotMessageNoMdEntriesGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 OrderBookSnapshotMessageNoMdEntriesGroup.encode OrderBookSnapshotMessageNoMdEntriesGroup.decode OrderBookSnapshotMessageNoMdEntriesGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.orderBookSnapshotMessageNoMdEntriesGroup.length_lt]
  rfl

end OrderBookSnapshotMessageNoMdEntriesGroups

/-- Order Book Snapshot Message -/
structure OrderBookSnapshotMessage where
  securityId : BitVec 32
  lastMsgSeqNumProcessed : BitVec 32
  rptSeq : BitVec 32
  exchangeTradingSessionId : BitVec 32
  orderBookSnapshotMessageNoMdEntriesGroups : OrderBookSnapshotMessageNoMdEntriesGroups
  deriving DecidableEq, Repr

namespace OrderBookSnapshotMessage

def encode (message : OrderBookSnapshotMessage) : List UInt8 :=
  encodeUIntLE 4 message.securityId
    ++ (encodeUIntLE 4 message.lastMsgSeqNumProcessed
    ++ (encodeUIntLE 4 message.rptSeq
    ++ (encodeUIntLE 4 message.exchangeTradingSessionId
    ++ (OrderBookSnapshotMessageNoMdEntriesGroups.encode message.orderBookSnapshotMessageNoMdEntriesGroups))))

def decode (bytes : List UInt8) : Option (OrderBookSnapshotMessage × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (lastMsgSeqNumProcessed, bytes) ← decodeUIntLE 4 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  let (exchangeTradingSessionId, bytes) ← decodeUIntLE 4 bytes
  let (orderBookSnapshotMessageNoMdEntriesGroups, bytes) ← OrderBookSnapshotMessageNoMdEntriesGroups.decode bytes
  pure ({ securityId, lastMsgSeqNumProcessed, rptSeq, exchangeTradingSessionId, orderBookSnapshotMessageNoMdEntriesGroups }, bytes)

theorem encode_length_pos (message : OrderBookSnapshotMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrderBookSnapshotMessage) : (encode message).length ≤ 12514 := by
  have bound_orderBookSnapshotMessageNoMdEntriesGroups := OrderBookSnapshotMessageNoMdEntriesGroups.encode_length_le message.orderBookSnapshotMessageNoMdEntriesGroups
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
  rw [OrderBookSnapshotMessageNoMdEntriesGroups.decode_encode, some_bind]
  rfl

end OrderBookSnapshotMessage

/-- Any Payload, selected by Template Id -/
inductive Payload where
  | heartbeatMessage (message : HeartbeatMessage) -- 1
  | sequenceResetMessage (message : SequenceResetMessage) -- 2
  | orderBookSnapshotMessage (message : OrderBookSnapshotMessage) -- 7
  deriving DecidableEq, Repr

namespace Payload

/-- The Template Id each message is sent under -/
def tag : Payload → BitVec 16
  | .heartbeatMessage _ => 1
  | .sequenceResetMessage _ => 2
  | .orderBookSnapshotMessage _ => 7

def encode : Payload → List UInt8
  | .heartbeatMessage message => HeartbeatMessage.encode message
  | .sequenceResetMessage message => SequenceResetMessage.encode message
  | .orderBookSnapshotMessage message => OrderBookSnapshotMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 12514 := by
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
  else if tag = 7 then (OrderBookSnapshotMessage.decode bytes).map fun (message, rest) => (.orderBookSnapshotMessage message, rest)
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
theorem encode_length_le (message : Message) : (encode message).length ≤ 12522 := by
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

end Omi.MoexSpectraOrderslogsnapshotSimbaV104
