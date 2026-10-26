import Wire

/-!
# Moscow Exchange SIMBA Spectra Orders Log Incremental v9.9.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.MoexSpectraOrderslogincrementalSimbaV990

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

/-- Incremental Packet Header: 12 bytes -/
structure IncrementalPacketHeader where
  transactTime : BitVec 64
  exchangeTradingSessionId : BitVec 32
  deriving DecidableEq, Repr

namespace IncrementalPacketHeader

def encode (message : IncrementalPacketHeader) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 4 message.exchangeTradingSessionId)

def decode (bytes : List UInt8) : Option (IncrementalPacketHeader × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (exchangeTradingSessionId, bytes) ← decodeUIntLE 4 bytes
  pure ({ transactTime, exchangeTradingSessionId }, bytes)

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

/-- Best Prices Message No M D Entries Group: 36 bytes -/
structure BestPricesMessageNoMDEntriesGroup where
  mktBidPx : BitVec 64
  mktOfferPx : BitVec 64
  mktBidSize : BitVec 64
  mktOfferSize : BitVec 64
  securityId : BitVec 32
  deriving DecidableEq, Repr

namespace BestPricesMessageNoMDEntriesGroup

def encode (message : BestPricesMessageNoMDEntriesGroup) : List UInt8 :=
  encodeUIntLE 8 message.mktBidPx
    ++ (encodeUIntLE 8 message.mktOfferPx
    ++ (encodeUIntLE 8 message.mktBidSize
    ++ (encodeUIntLE 8 message.mktOfferSize
    ++ (encodeUIntLE 4 message.securityId))))

def decode (bytes : List UInt8) : Option (BestPricesMessageNoMDEntriesGroup × List UInt8) := do
  let (mktBidPx, bytes) ← decodeUIntLE 8 bytes
  let (mktOfferPx, bytes) ← decodeUIntLE 8 bytes
  let (mktBidSize, bytes) ← decodeUIntLE 8 bytes
  let (mktOfferSize, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  pure ({ mktBidPx, mktOfferPx, mktBidSize, mktOfferSize, securityId }, bytes)

@[simp] theorem encode_length (message : BestPricesMessageNoMDEntriesGroup) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : BestPricesMessageNoMDEntriesGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BestPricesMessageNoMDEntriesGroup) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end BestPricesMessageNoMDEntriesGroup

/-- Best Prices Message No M D Entries Groups -/
structure BestPricesMessageNoMDEntriesGroups where
  blockLength : BitVec 16
  bestPricesMessageNoMDEntriesGroup : Bounded 1 BestPricesMessageNoMDEntriesGroup
  deriving DecidableEq, Repr

namespace BestPricesMessageNoMDEntriesGroups

def encode (message : BestPricesMessageNoMDEntriesGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.bestPricesMessageNoMDEntriesGroup.val.length)
    ++ (encodeMany BestPricesMessageNoMDEntriesGroup.encode message.bestPricesMessageNoMDEntriesGroup.val))

def decode (bytes : List UInt8) : Option (BestPricesMessageNoMDEntriesGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroupUint8, bytes) ← decodeUInt 1 bytes
  let (bestPricesMessageNoMDEntriesGroup_, bytes) ← decodeMany BestPricesMessageNoMDEntriesGroup.decode numInGroupUint8.toNat bytes
  if fits_bestPricesMessageNoMDEntriesGroup : bestPricesMessageNoMDEntriesGroup_.length < 256 ^ 1 then
    pure ({ blockLength, bestPricesMessageNoMDEntriesGroup := ⟨bestPricesMessageNoMDEntriesGroup_, fits_bestPricesMessageNoMDEntriesGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : BestPricesMessageNoMDEntriesGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : BestPricesMessageNoMDEntriesGroups) : (encode message).length ≤ 9183 := by
  have bound_bestPricesMessageNoMDEntriesGroup := message.bestPricesMessageNoMDEntriesGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const BestPricesMessageNoMDEntriesGroup.encode 36 BestPricesMessageNoMDEntriesGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : BestPricesMessageNoMDEntriesGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 BestPricesMessageNoMDEntriesGroup.encode BestPricesMessageNoMDEntriesGroup.decode BestPricesMessageNoMDEntriesGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.bestPricesMessageNoMDEntriesGroup.length_lt]
  rfl

end BestPricesMessageNoMDEntriesGroups

/-- Best Prices Message -/
structure BestPricesMessage where
  bestPricesMessageNoMDEntriesGroups : BestPricesMessageNoMDEntriesGroups
  deriving DecidableEq, Repr

namespace BestPricesMessage

def encode (message : BestPricesMessage) : List UInt8 :=
  BestPricesMessageNoMDEntriesGroups.encode message.bestPricesMessageNoMDEntriesGroups

def decode (bytes : List UInt8) : Option (BestPricesMessage × List UInt8) := do
  let (bestPricesMessageNoMDEntriesGroups, bytes) ← BestPricesMessageNoMDEntriesGroups.decode bytes
  pure ({ bestPricesMessageNoMDEntriesGroups }, bytes)

theorem encode_length_pos (message : BestPricesMessage) : (encode message).length > 0 := by
  have positive := BestPricesMessageNoMDEntriesGroups.encode_length_pos message.bestPricesMessageNoMDEntriesGroups
  unfold encode
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : BestPricesMessage) : (encode message).length ≤ 9183 := by
  have bound_bestPricesMessageNoMDEntriesGroups := BestPricesMessageNoMDEntriesGroups.encode_length_le message.bestPricesMessageNoMDEntriesGroups
  unfold encode
  omega

@[simp] theorem decode_encode (message : BestPricesMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [BestPricesMessageNoMDEntriesGroups.decode_encode, some_bind]
  rfl

end BestPricesMessage

/-- Empty Book Message: 4 bytes -/
structure EmptyBookMessage where
  lastMsgSeqNumProcessedUInt32NullOptional : BitVec 32
  deriving DecidableEq, Repr

namespace EmptyBookMessage

def encode (message : EmptyBookMessage) : List UInt8 :=
  encodeUIntLE 4 message.lastMsgSeqNumProcessedUInt32NullOptional

def decode (bytes : List UInt8) : Option (EmptyBookMessage × List UInt8) := do
  let (lastMsgSeqNumProcessedUInt32NullOptional, bytes) ← decodeUIntLE 4 bytes
  pure ({ lastMsgSeqNumProcessedUInt32NullOptional }, bytes)

@[simp] theorem encode_length (message : EmptyBookMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : EmptyBookMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EmptyBookMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end EmptyBookMessage

/-- Order Update Message: 50 bytes -/
structure OrderUpdateMessage where
  mdEntryIdInt64 : BitVec 64
  mdEntryPxDecimal5 : BitVec 64
  mdEntrySizeInt64 : BitVec 64
  mdFlags : BitVec 64
  mdFlags2 : BitVec 64
  securityId : BitVec 32
  rptSeq : BitVec 32
  mdUpdateAction : BitVec 8
  mdEntryType : MdEntryType
  deriving DecidableEq, Repr

namespace OrderUpdateMessage

def encode (message : OrderUpdateMessage) : List UInt8 :=
  encodeUIntLE 8 message.mdEntryIdInt64
    ++ (encodeUIntLE 8 message.mdEntryPxDecimal5
    ++ (encodeUIntLE 8 message.mdEntrySizeInt64
    ++ (encodeUIntLE 8 message.mdFlags
    ++ (encodeUIntLE 8 message.mdFlags2
    ++ (encodeUIntLE 4 message.securityId
    ++ (encodeUIntLE 4 message.rptSeq
    ++ (encodeUInt 1 message.mdUpdateAction
    ++ (MdEntryType.encode message.mdEntryType))))))))

def decode (bytes : List UInt8) : Option (OrderUpdateMessage × List UInt8) := do
  let (mdEntryIdInt64, bytes) ← decodeUIntLE 8 bytes
  let (mdEntryPxDecimal5, bytes) ← decodeUIntLE 8 bytes
  let (mdEntrySizeInt64, bytes) ← decodeUIntLE 8 bytes
  let (mdFlags, bytes) ← decodeUIntLE 8 bytes
  let (mdFlags2, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  let (mdUpdateAction, bytes) ← decodeUInt 1 bytes
  let (mdEntryType, bytes) ← MdEntryType.decode bytes
  pure ({ mdEntryIdInt64, mdEntryPxDecimal5, mdEntrySizeInt64, mdFlags, mdFlags2, securityId, rptSeq, mdUpdateAction, mdEntryType }, bytes)

@[simp] theorem encode_length (message : OrderUpdateMessage) : (encode message).length = 50 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, MdEntryType.encode_length]

theorem encode_length_pos (message : OrderUpdateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderUpdateMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [MdEntryType.decode_encode, some_bind]
  rfl

end OrderUpdateMessage

/-- Order Execution Message: 74 bytes -/
structure OrderExecutionMessage where
  mdEntryIdInt64 : BitVec 64
  mdEntryPxDecimal5NullOptional : BitVec 64
  mdEntrySizeInt64NullOptional : BitVec 64
  lastPx : BitVec 64
  lastQty : BitVec 64
  tradeIdInt64 : BitVec 64
  mdFlags : BitVec 64
  mdFlags2 : BitVec 64
  securityId : BitVec 32
  rptSeq : BitVec 32
  mdUpdateAction : BitVec 8
  mdEntryType : MdEntryType
  deriving DecidableEq, Repr

namespace OrderExecutionMessage

def encode (message : OrderExecutionMessage) : List UInt8 :=
  encodeUIntLE 8 message.mdEntryIdInt64
    ++ (encodeUIntLE 8 message.mdEntryPxDecimal5NullOptional
    ++ (encodeUIntLE 8 message.mdEntrySizeInt64NullOptional
    ++ (encodeUIntLE 8 message.lastPx
    ++ (encodeUIntLE 8 message.lastQty
    ++ (encodeUIntLE 8 message.tradeIdInt64
    ++ (encodeUIntLE 8 message.mdFlags
    ++ (encodeUIntLE 8 message.mdFlags2
    ++ (encodeUIntLE 4 message.securityId
    ++ (encodeUIntLE 4 message.rptSeq
    ++ (encodeUInt 1 message.mdUpdateAction
    ++ (MdEntryType.encode message.mdEntryType)))))))))))

def decode (bytes : List UInt8) : Option (OrderExecutionMessage × List UInt8) := do
  let (mdEntryIdInt64, bytes) ← decodeUIntLE 8 bytes
  let (mdEntryPxDecimal5NullOptional, bytes) ← decodeUIntLE 8 bytes
  let (mdEntrySizeInt64NullOptional, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 8 bytes
  let (tradeIdInt64, bytes) ← decodeUIntLE 8 bytes
  let (mdFlags, bytes) ← decodeUIntLE 8 bytes
  let (mdFlags2, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (rptSeq, bytes) ← decodeUIntLE 4 bytes
  let (mdUpdateAction, bytes) ← decodeUInt 1 bytes
  let (mdEntryType, bytes) ← MdEntryType.decode bytes
  pure ({ mdEntryIdInt64, mdEntryPxDecimal5NullOptional, mdEntrySizeInt64NullOptional, lastPx, lastQty, tradeIdInt64, mdFlags, mdFlags2, securityId, rptSeq, mdUpdateAction, mdEntryType }, bytes)

@[simp] theorem encode_length (message : OrderExecutionMessage) : (encode message).length = 74 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, MdEntryType.encode_length]

theorem encode_length_pos (message : OrderExecutionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderExecutionMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [MdEntryType.decode_encode, some_bind]
  rfl

end OrderExecutionMessage

/-- Any Payload, selected by Template Id -/
inductive Payload where
  | heartbeatMessage (message : HeartbeatMessage) -- 1
  | sequenceResetMessage (message : SequenceResetMessage) -- 2
  | bestPricesMessage (message : BestPricesMessage) -- 14
  | emptyBookMessage (message : EmptyBookMessage) -- 4
  | orderUpdateMessage (message : OrderUpdateMessage) -- 15
  | orderExecutionMessage (message : OrderExecutionMessage) -- 16
  deriving DecidableEq, Repr

namespace Payload

/-- The Template Id each message is sent under -/
def tag : Payload → BitVec 16
  | .heartbeatMessage _ => 1
  | .sequenceResetMessage _ => 2
  | .bestPricesMessage _ => 14
  | .emptyBookMessage _ => 4
  | .orderUpdateMessage _ => 15
  | .orderExecutionMessage _ => 16

def encode : Payload → List UInt8
  | .heartbeatMessage message => HeartbeatMessage.encode message
  | .sequenceResetMessage message => SequenceResetMessage.encode message
  | .bestPricesMessage message => BestPricesMessage.encode message
  | .emptyBookMessage message => EmptyBookMessage.encode message
  | .orderUpdateMessage message => OrderUpdateMessage.encode message
  | .orderExecutionMessage message => OrderExecutionMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 9183 := by
  cases message with
  | heartbeatMessage inner =>
    simp only [encode, HeartbeatMessage.encode_length]
    omega
  | sequenceResetMessage inner =>
    simp only [encode, SequenceResetMessage.encode_length]
    omega
  | bestPricesMessage inner =>
    have bound_inner := BestPricesMessage.encode_length_le inner
    simp only [encode]
    omega
  | emptyBookMessage inner =>
    simp only [encode, EmptyBookMessage.encode_length]
    omega
  | orderUpdateMessage inner =>
    simp only [encode, OrderUpdateMessage.encode_length]
    omega
  | orderExecutionMessage inner =>
    simp only [encode, OrderExecutionMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 1 then (HeartbeatMessage.decode bytes).map fun (message, rest) => (.heartbeatMessage message, rest)
  else if tag = 2 then (SequenceResetMessage.decode bytes).map fun (message, rest) => (.sequenceResetMessage message, rest)
  else if tag = 14 then (BestPricesMessage.decode bytes).map fun (message, rest) => (.bestPricesMessage message, rest)
  else if tag = 4 then (EmptyBookMessage.decode bytes).map fun (message, rest) => (.emptyBookMessage message, rest)
  else if tag = 15 then (OrderUpdateMessage.decode bytes).map fun (message, rest) => (.orderUpdateMessage message, rest)
  else if tag = 16 then (OrderExecutionMessage.decode bytes).map fun (message, rest) => (.orderExecutionMessage message, rest)
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
theorem encode_length_le (message : Message) : (encode message).length ≤ 9191 := by
  unfold encode
  cases message.payload with
  | heartbeatMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, HeartbeatMessage.encode_length]
    omega
  | sequenceResetMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, SequenceResetMessage.encode_length]
    omega
  | bestPricesMessage inner =>
    have bound_inner := BestPricesMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | emptyBookMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, EmptyBookMessage.encode_length]
    omega
  | orderUpdateMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OrderUpdateMessage.encode_length]
    omega
  | orderExecutionMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OrderExecutionMessage.encode_length]
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

end Omi.MoexSpectraOrderslogincrementalSimbaV990
