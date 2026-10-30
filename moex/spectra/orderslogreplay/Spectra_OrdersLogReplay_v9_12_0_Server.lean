import Wire
import Std.Tactic.BVDecide

/-!
# Moscow Exchange SIMBA Spectra Orders Log Historical Replay v9.12.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.MoexSpectraOrderslogreplaySimbaV9120Server

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

/-- Logon Message: 0 bytes -/
structure LogonMessage where
  deriving DecidableEq, Repr

namespace LogonMessage

def encode (_ : LogonMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (LogonMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : LogonMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : LogonMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end LogonMessage

/-- Logout Message: 256 bytes -/
structure LogoutMessage where
  text : Alpha 256
  deriving DecidableEq, Repr

namespace LogoutMessage

def encode (message : LogoutMessage) : List UInt8 :=
  Alpha.encode message.text

def decode (bytes : List UInt8) : Option (LogoutMessage × List UInt8) := do
  let (text, bytes) ← Alpha.decode 256 bytes
  pure ({ text }, bytes)

@[simp] theorem encode_length (message : LogoutMessage) : (encode message).length = 256 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : LogoutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogoutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end LogoutMessage

/-- Any Server Session Payload, selected by Template Id -/
inductive ServerSessionPayload where
  | heartbeatMessage (message : HeartbeatMessage) -- 1
  | logonMessage (message : LogonMessage) -- 1000
  | logoutMessage (message : LogoutMessage) -- 1001
  deriving DecidableEq, Repr

namespace ServerSessionPayload

/-- The Template Id each message is sent under -/
def tag : ServerSessionPayload → BitVec 16
  | .heartbeatMessage _ => 1
  | .logonMessage _ => 1000
  | .logoutMessage _ => 1001

def encode : ServerSessionPayload → List UInt8
  | .heartbeatMessage message => HeartbeatMessage.encode message
  | .logonMessage message => LogonMessage.encode message
  | .logoutMessage message => LogoutMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ServerSessionPayload) : (encode message).length ≤ 256 := by
  cases message with
  | heartbeatMessage inner =>
    simp only [encode, HeartbeatMessage.encode_length]
    omega
  | logonMessage inner =>
    simp only [encode, LogonMessage.encode_length]
    omega
  | logoutMessage inner =>
    simp only [encode, LogoutMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (ServerSessionPayload × List UInt8) :=
  if tag = 1 then (HeartbeatMessage.decode bytes).map fun (message, rest) => (.heartbeatMessage message, rest)
  else if tag = 1000 then (LogonMessage.decode bytes).map fun (message, rest) => (.logonMessage message, rest)
  else if tag = 1001 then (LogoutMessage.decode bytes).map fun (message, rest) => (.logoutMessage message, rest)
  else none

@[simp] theorem decode_encode (message : ServerSessionPayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ServerSessionPayload

/-- Server Session -/
structure ServerSession where
  blockLength : BitVec 16
  schemaId : BitVec 16
  version : BitVec 16
  serverSessionPayload : ServerSessionPayload
  deriving DecidableEq, Repr

namespace ServerSession

def encode (message : ServerSession) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUIntLE 2 (ServerSessionPayload.tag message.serverSessionPayload)
    ++ (encodeUIntLE 2 message.schemaId
    ++ (encodeUIntLE 2 message.version
    ++ (ServerSessionPayload.encode message.serverSessionPayload))))

def decode (bytes : List UInt8) : Option (ServerSession × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (templateId, bytes) ← decodeUIntLE 2 bytes
  let (schemaId, bytes) ← decodeUIntLE 2 bytes
  let (version, bytes) ← decodeUIntLE 2 bytes
  let (serverSessionPayload, bytes) ← ServerSessionPayload.decode templateId bytes
  pure ({ blockLength, schemaId, version, serverSessionPayload }, bytes)

theorem encode_length_pos (message : ServerSession) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ServerSession) : (encode message).length ≤ 264 := by
  unfold encode
  cases message.serverSessionPayload with
  | heartbeatMessage inner =>
    simp only [ServerSessionPayload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, HeartbeatMessage.encode_length]
    omega
  | logonMessage inner =>
    simp only [ServerSessionPayload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, LogonMessage.encode_length]
    omega
  | logoutMessage inner =>
    simp only [ServerSessionPayload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, LogoutMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : ServerSession) (rest : List UInt8) :
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
  rw [ServerSessionPayload.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ServerSession) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ServerSession

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

/-- Any Server Replay Payload, selected by Template Id -/
inductive ServerReplayPayload where
  | heartbeatMessage (message : HeartbeatMessage) -- 1
  | bestPricesMessage (message : BestPricesMessage) -- 14
  | emptyBookMessage (message : EmptyBookMessage) -- 4
  | orderUpdateMessage (message : OrderUpdateMessage) -- 15
  | orderExecutionMessage (message : OrderExecutionMessage) -- 16
  deriving DecidableEq, Repr

namespace ServerReplayPayload

/-- The Template Id each message is sent under -/
def tag : ServerReplayPayload → BitVec 16
  | .heartbeatMessage _ => 1
  | .bestPricesMessage _ => 14
  | .emptyBookMessage _ => 4
  | .orderUpdateMessage _ => 15
  | .orderExecutionMessage _ => 16

def encode : ServerReplayPayload → List UInt8
  | .heartbeatMessage message => HeartbeatMessage.encode message
  | .bestPricesMessage message => BestPricesMessage.encode message
  | .emptyBookMessage message => EmptyBookMessage.encode message
  | .orderUpdateMessage message => OrderUpdateMessage.encode message
  | .orderExecutionMessage message => OrderExecutionMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ServerReplayPayload) : (encode message).length ≤ 9183 := by
  cases message with
  | heartbeatMessage inner =>
    simp only [encode, HeartbeatMessage.encode_length]
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

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (ServerReplayPayload × List UInt8) :=
  if tag = 1 then (HeartbeatMessage.decode bytes).map fun (message, rest) => (.heartbeatMessage message, rest)
  else if tag = 14 then (BestPricesMessage.decode bytes).map fun (message, rest) => (.bestPricesMessage message, rest)
  else if tag = 4 then (EmptyBookMessage.decode bytes).map fun (message, rest) => (.emptyBookMessage message, rest)
  else if tag = 15 then (OrderUpdateMessage.decode bytes).map fun (message, rest) => (.orderUpdateMessage message, rest)
  else if tag = 16 then (OrderExecutionMessage.decode bytes).map fun (message, rest) => (.orderExecutionMessage message, rest)
  else none

@[simp] theorem decode_encode (message : ServerReplayPayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ServerReplayPayload

/-- Server Replay Message -/
structure ServerReplayMessage where
  blockLength : BitVec 16
  schemaId : BitVec 16
  version : BitVec 16
  serverReplayPayload : ServerReplayPayload
  deriving DecidableEq, Repr

namespace ServerReplayMessage

def encode (message : ServerReplayMessage) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUIntLE 2 (ServerReplayPayload.tag message.serverReplayPayload)
    ++ (encodeUIntLE 2 message.schemaId
    ++ (encodeUIntLE 2 message.version
    ++ (ServerReplayPayload.encode message.serverReplayPayload))))

def decode (bytes : List UInt8) : Option (ServerReplayMessage × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (templateId, bytes) ← decodeUIntLE 2 bytes
  let (schemaId, bytes) ← decodeUIntLE 2 bytes
  let (version, bytes) ← decodeUIntLE 2 bytes
  let (serverReplayPayload, bytes) ← ServerReplayPayload.decode templateId bytes
  pure ({ blockLength, schemaId, version, serverReplayPayload }, bytes)

theorem encode_length_pos (message : ServerReplayMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ServerReplayMessage) : (encode message).length ≤ 9191 := by
  unfold encode
  cases message.serverReplayPayload with
  | heartbeatMessage inner =>
    simp only [ServerReplayPayload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, HeartbeatMessage.encode_length]
    omega
  | bestPricesMessage inner =>
    have bound_inner := BestPricesMessage.encode_length_le inner
    simp only [ServerReplayPayload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | emptyBookMessage inner =>
    simp only [ServerReplayPayload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, EmptyBookMessage.encode_length]
    omega
  | orderUpdateMessage inner =>
    simp only [ServerReplayPayload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OrderUpdateMessage.encode_length]
    omega
  | orderExecutionMessage inner =>
    simp only [ServerReplayPayload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OrderExecutionMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : ServerReplayMessage) (rest : List UInt8) :
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
  rw [ServerReplayPayload.decode_encode, some_bind]
  rfl

end ServerReplayMessage

/-- Server Replay -/
structure ServerReplay where
  incrementalPacketHeader : IncrementalPacketHeader
  serverReplayMessage : List ServerReplayMessage
  deriving DecidableEq, Repr

namespace ServerReplay

def encode (message : ServerReplay) : List UInt8 :=
  IncrementalPacketHeader.encode message.incrementalPacketHeader
    ++ (encodeMany ServerReplayMessage.encode message.serverReplayMessage)

def decode (bytes : List UInt8) : Option ServerReplay := do
  let (incrementalPacketHeader, bytes) ← IncrementalPacketHeader.decode bytes
  let serverReplayMessage ← decodeAll ServerReplayMessage.decode bytes.length bytes
  pure { incrementalPacketHeader, serverReplayMessage }

theorem encode_length_pos (message : ServerReplay) : (encode message).length > 0 := by
  unfold encode
  simp only [IncrementalPacketHeader.encode_length, List.length_append]
  omega

theorem decode_encode (message : ServerReplay) : decode (encode message) = some message := by
  unfold decode encode
  rw [IncrementalPacketHeader.decode_encode, some_bind]
  dsimp only
  rw [decodeAll_encodeMany ServerReplayMessage.encode ServerReplayMessage.decode ServerReplayMessage.decode_encode ServerReplayMessage.encode_length_pos message.serverReplayMessage _ (encodeMany_length_ge ServerReplayMessage.encode ServerReplayMessage.encode_length_pos message.serverReplayMessage), some_bind]
  rfl

end ServerReplay

/-- Any Server Body, selected by Msg Flags -/
inductive ServerBody where
  | serverSession (message : ServerSession) -- 0
  | serverReplay (message : ServerReplay) -- 8
  deriving DecidableEq, Repr

namespace ServerBody

/-- The Msg Flags each message is sent under -/
def tag : ServerBody → BitVec 16
  | .serverSession _ => 0
  | .serverReplay _ => 8

/-- The tag is written into its own bits of the field that carries it, and no others -/
theorem tag_inside (message : ServerBody) : tag message &&& 65527 = 0 := by
  cases message <;> (simp only [tag]; decide)

def encode : ServerBody → List UInt8
  | .serverSession message => ServerSession.encode message
  | .serverReplay message => ServerReplay.encode message

/-- Decoded from the whole of the frame: a message that reads to its end takes it all, any other must leave nothing -/
def decode (tag : BitVec 16) (bytes : List UInt8) : Option ServerBody :=
  if tag = 0 then (ServerSession.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.serverSession message) else none
  else if tag = 8 then (ServerReplay.decode bytes).map fun message => .serverReplay message
  else none

theorem decode_encode (message : ServerBody) :
    decode (tag message) (encode message) = some message := by
  cases message with
  | serverSession message => simp [decode, encode, tag, ServerSession.decode_encode_nil]
  | serverReplay message => simp [decode, encode, tag, ServerReplay.decode_encode]

end ServerBody

/-- Server Frame: the body, which the record carries with the proof it fits its frame -/
structure ServerFrameBody where
  msgSeqNum : BitVec 32
  msgFlags : Masked 16 8
  sendingTime : BitVec 64
  serverBody : ServerBody
  deriving DecidableEq, Repr

namespace ServerFrameBody

def encodeBody (message : ServerFrameBody) : List UInt8 :=
  encodeUIntLE 2 (message.msgFlags.val ||| ServerBody.tag message.serverBody)
    ++ (encodeUIntLE 8 message.sendingTime
    ++ (ServerBody.encode message.serverBody))

def decodeBody (msgSeqNum : BitVec 32) (bytes : List UInt8) : Option ServerFrameBody := do
  let (msgFlags_, bytes) ← decodeUIntLE 2 bytes
  let (sendingTime, bytes) ← decodeUIntLE 8 bytes
  let serverBody ← ServerBody.decode (msgFlags_ &&& 8) bytes
  if fits_msgFlags : (msgFlags_ &&& 65527) &&& 8 = 0 then
    pure { msgSeqNum, msgFlags := ⟨msgFlags_ &&& 65527, fits_msgFlags⟩, sendingTime, serverBody }
  else none

theorem decodeBody_encodeBody (message : ServerFrameBody) : decodeBody message.msgSeqNum (encodeBody message) = some message := by
  unfold decodeBody encodeBody
  generalize written_msgFlags_eq : (message.msgFlags.val ||| ServerBody.tag message.serverBody) = written_msgFlags
  have selected_msgFlags : written_msgFlags &&& 8 = ServerBody.tag message.serverBody := by
    rw [← written_msgFlags_eq]
    have clear := message.msgFlags.property
    have inside := ServerBody.tag_inside message.serverBody
    bv_decide
  have carried_msgFlags : written_msgFlags &&& 65527 = message.msgFlags.val := by
    rw [← written_msgFlags_eq]
    have clear := message.msgFlags.property
    have inside := ServerBody.tag_inside message.serverBody
    bv_decide
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [selected_msgFlags]
  rw [ServerBody.decode_encode, some_bind]
  rw [dite_eq_left (by rw [carried_msgFlags]; exact message.msgFlags.property)]
  simp only [carried_msgFlags]
  rfl

end ServerFrameBody

/-- Server Frame: the body with the proof its encoding fits Msg Size, whose 2 bytes no bound of the fields fits -/
abbrev ServerFrame := Fitting ServerFrameBody.encodeBody 6 65536

namespace ServerFrame

def encode (message : ServerFrame) : List UInt8 :=
  encodeUIntLE 4 message.val.msgSeqNum
    ++ (encodeFramedLE 2 6 ServerFrameBody.encodeBody message.val)

def decode (bytes : List UInt8) : Option (ServerFrame × List UInt8) := do
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  decodeFittingAllLE 2 6 ServerFrameBody.encodeBody (ServerFrameBody.decodeBody msgSeqNum) bytes

@[simp] theorem decode_encode (message : ServerFrame) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  exact decodeFittingAllLE_encodeFramedLE 2 6 ServerFrameBody.encodeBody (ServerFrameBody.decodeBody message.val.msgSeqNum) message (ServerFrameBody.decodeBody_encodeBody message.val) rest

theorem encode_length_pos (message : ServerFrame) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, encodeFramedLE_length]
  omega

/-- The most bytes an encoding can take: what the prefix can count, by the fit the message carries -/
theorem encode_length_le (message : ServerFrame) : (encode message).length ≤ 65535 := by
  have fits := message.fits
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, encodeFramedLE_length]
  omega

end ServerFrame

/-- Server Packet -/
structure ServerPacket where
  serverFrame : List ServerFrame
  deriving DecidableEq, Repr

namespace ServerPacket

def encode (message : ServerPacket) : List UInt8 :=
  encodeMany ServerFrame.encode message.serverFrame

def decode (bytes : List UInt8) : Option ServerPacket := do
  let serverFrame ← decodeAll ServerFrame.decode bytes.length bytes
  pure { serverFrame }

theorem decode_encode (message : ServerPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany ServerFrame.encode ServerFrame.decode ServerFrame.decode_encode ServerFrame.encode_length_pos message.serverFrame _ (encodeMany_length_ge ServerFrame.encode ServerFrame.encode_length_pos message.serverFrame), some_bind]
  rfl

end ServerPacket

end Omi.MoexSpectraOrderslogreplaySimbaV9120Server
