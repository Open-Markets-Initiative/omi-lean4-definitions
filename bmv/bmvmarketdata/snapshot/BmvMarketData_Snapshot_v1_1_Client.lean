import Wire

/-!
# Bolsa Mexicana de Valores Bmv Market Data Snapshot v1.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.

License: MIT No Attribution
-/

namespace Omi.BmvBmvmarketdataSnapshotIntraV11Client

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

/-- Login Message: 17 bytes -/
structure LoginMessage where
  marketDataGroup : BitVec 8
  user : Alpha 6
  password : Alpha 10
  deriving DecidableEq, Repr

namespace LoginMessage

def encode (message : LoginMessage) : List UInt8 :=
  encodeUInt 1 message.marketDataGroup
    ++ (Alpha.encode message.user
    ++ (Alpha.encode message.password))

def decode (bytes : List UInt8) : Option (LoginMessage × List UInt8) := do
  let (marketDataGroup, bytes) ← decodeUInt 1 bytes
  let (user, bytes) ← Alpha.decode 6 bytes
  let (password, bytes) ← Alpha.decode 10 bytes
  pure ({ marketDataGroup, user, password }, bytes)

@[simp] theorem encode_length (message : LoginMessage) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : LoginMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LoginMessage

/-- Replay Request Message: 7 bytes -/
structure ReplayRequestMessage where
  marketDataGroup : BitVec 8
  firstMessage : BitVec 32
  quantity : BitVec 16
  deriving DecidableEq, Repr

namespace ReplayRequestMessage

def encode (message : ReplayRequestMessage) : List UInt8 :=
  encodeUInt 1 message.marketDataGroup
    ++ (encodeUInt 4 message.firstMessage
    ++ (encodeUInt 2 message.quantity))

def decode (bytes : List UInt8) : Option (ReplayRequestMessage × List UInt8) := do
  let (marketDataGroup, bytes) ← decodeUInt 1 bytes
  let (firstMessage, bytes) ← decodeUInt 4 bytes
  let (quantity, bytes) ← decodeUInt 2 bytes
  pure ({ marketDataGroup, firstMessage, quantity }, bytes)

@[simp] theorem encode_length (message : ReplayRequestMessage) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : ReplayRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReplayRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ReplayRequestMessage

/-- Snapshot Request Message: 6 bytes -/
structure SnapshotRequestMessage where
  marketDataGroup : BitVec 8
  instrumentId : BitVec 32
  snapshotType : BitVec 8
  deriving DecidableEq, Repr

namespace SnapshotRequestMessage

def encode (message : SnapshotRequestMessage) : List UInt8 :=
  encodeUInt 1 message.marketDataGroup
    ++ (encodeUInt 4 message.instrumentId
    ++ (encodeUInt 1 message.snapshotType))

def decode (bytes : List UInt8) : Option (SnapshotRequestMessage × List UInt8) := do
  let (marketDataGroup, bytes) ← decodeUInt 1 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (snapshotType, bytes) ← decodeUInt 1 bytes
  pure ({ marketDataGroup, instrumentId, snapshotType }, bytes)

@[simp] theorem encode_length (message : SnapshotRequestMessage) : (encode message).length = 6 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : SnapshotRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SnapshotRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SnapshotRequestMessage

/-- Snapshot Indices Request Message: 11 bytes -/
structure SnapshotIndicesRequestMessage where
  marketDataGroup : BitVec 8
  component : Alpha 2
  recoveryHour : BitVec 64
  deriving DecidableEq, Repr

namespace SnapshotIndicesRequestMessage

def encode (message : SnapshotIndicesRequestMessage) : List UInt8 :=
  encodeUInt 1 message.marketDataGroup
    ++ (Alpha.encode message.component
    ++ (encodeUInt 8 message.recoveryHour))

def decode (bytes : List UInt8) : Option (SnapshotIndicesRequestMessage × List UInt8) := do
  let (marketDataGroup, bytes) ← decodeUInt 1 bytes
  let (component, bytes) ← Alpha.decode 2 bytes
  let (recoveryHour, bytes) ← decodeUInt 8 bytes
  pure ({ marketDataGroup, component, recoveryHour }, bytes)

@[simp] theorem encode_length (message : SnapshotIndicesRequestMessage) : (encode message).length = 11 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : SnapshotIndicesRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SnapshotIndicesRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SnapshotIndicesRequestMessage

/-- Snapshot Consolidated Feed Request Message: 7 bytes -/
structure SnapshotConsolidatedFeedRequestMessage where
  marketDataGroup : BitVec 8
  instrumentId : BitVec 32
  snapshotType : BitVec 8
  origin : Origin
  deriving DecidableEq, Repr

namespace SnapshotConsolidatedFeedRequestMessage

def encode (message : SnapshotConsolidatedFeedRequestMessage) : List UInt8 :=
  encodeUInt 1 message.marketDataGroup
    ++ (encodeUInt 4 message.instrumentId
    ++ (encodeUInt 1 message.snapshotType
    ++ (Origin.encode message.origin)))

def decode (bytes : List UInt8) : Option (SnapshotConsolidatedFeedRequestMessage × List UInt8) := do
  let (marketDataGroup, bytes) ← decodeUInt 1 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (snapshotType, bytes) ← decodeUInt 1 bytes
  let (origin, bytes) ← Origin.decode bytes
  pure ({ marketDataGroup, instrumentId, snapshotType, origin }, bytes)

@[simp] theorem encode_length (message : SnapshotConsolidatedFeedRequestMessage) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Origin.encode_length]

theorem encode_length_pos (message : SnapshotConsolidatedFeedRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SnapshotConsolidatedFeedRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Origin.decode_encode, some_bind]
  rfl

end SnapshotConsolidatedFeedRequestMessage

/-- Any Client Payload, selected by Client Message Type -/
inductive ClientPayload where
  | loginMessage (message : LoginMessage) -- 33
  | replayRequestMessage (message : ReplayRequestMessage) -- 35
  | snapshotRequestMessage (message : SnapshotRequestMessage) -- 36
  | snapshotIndicesRequestMessage (message : SnapshotIndicesRequestMessage) -- 45
  | snapshotConsolidatedFeedRequestMessage (message : SnapshotConsolidatedFeedRequestMessage) -- 95
  deriving DecidableEq, Repr

namespace ClientPayload

/-- The Client Message Type each message is sent under -/
def tag : ClientPayload → BitVec 8
  | .loginMessage _ => 33
  | .replayRequestMessage _ => 35
  | .snapshotRequestMessage _ => 36
  | .snapshotIndicesRequestMessage _ => 45
  | .snapshotConsolidatedFeedRequestMessage _ => 95

def encode : ClientPayload → List UInt8
  | .loginMessage message => LoginMessage.encode message
  | .replayRequestMessage message => ReplayRequestMessage.encode message
  | .snapshotRequestMessage message => SnapshotRequestMessage.encode message
  | .snapshotIndicesRequestMessage message => SnapshotIndicesRequestMessage.encode message
  | .snapshotConsolidatedFeedRequestMessage message => SnapshotConsolidatedFeedRequestMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ClientPayload) : (encode message).length ≤ 17 := by
  cases message with
  | loginMessage inner =>
    simp only [encode, LoginMessage.encode_length]
    omega
  | replayRequestMessage inner =>
    simp only [encode, ReplayRequestMessage.encode_length]
    omega
  | snapshotRequestMessage inner =>
    simp only [encode, SnapshotRequestMessage.encode_length]
    omega
  | snapshotIndicesRequestMessage inner =>
    simp only [encode, SnapshotIndicesRequestMessage.encode_length]
    omega
  | snapshotConsolidatedFeedRequestMessage inner =>
    simp only [encode, SnapshotConsolidatedFeedRequestMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (ClientPayload × List UInt8) :=
  if tag = 33 then (LoginMessage.decode bytes).map fun (message, rest) => (.loginMessage message, rest)
  else if tag = 35 then (ReplayRequestMessage.decode bytes).map fun (message, rest) => (.replayRequestMessage message, rest)
  else if tag = 36 then (SnapshotRequestMessage.decode bytes).map fun (message, rest) => (.snapshotRequestMessage message, rest)
  else if tag = 45 then (SnapshotIndicesRequestMessage.decode bytes).map fun (message, rest) => (.snapshotIndicesRequestMessage message, rest)
  else if tag = 95 then (SnapshotConsolidatedFeedRequestMessage.decode bytes).map fun (message, rest) => (.snapshotConsolidatedFeedRequestMessage message, rest)
  else none

@[simp] theorem decode_encode (message : ClientPayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ClientPayload

/-- Client Message -/
structure ClientMessage where
  clientPayload : ClientPayload
  deriving DecidableEq, Repr

namespace ClientMessage

def encodeBody (message : ClientMessage) : List UInt8 :=
  encodeUInt 1 (ClientPayload.tag message.clientPayload)
    ++ (ClientPayload.encode message.clientPayload)

def decodeBody (bytes : List UInt8) : Option (ClientMessage × List UInt8) := do
  let (clientMessageType, bytes) ← decodeUInt 1 bytes
  let (clientPayload, bytes) ← ClientPayload.decode clientMessageType bytes
  pure ({ clientPayload }, bytes)

theorem decodeBody_encodeBody (message : ClientMessage) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ClientPayload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : ClientMessage) : (encodeBody message).length + 1 < 256 ^ 1 := by
  unfold encodeBody
  cases message.clientPayload with
  | loginMessage inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUInt_length, LoginMessage.encode_length]
    omega
  | replayRequestMessage inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUInt_length, ReplayRequestMessage.encode_length]
    omega
  | snapshotRequestMessage inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUInt_length, SnapshotRequestMessage.encode_length]
    omega
  | snapshotIndicesRequestMessage inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUInt_length, SnapshotIndicesRequestMessage.encode_length]
    omega
  | snapshotConsolidatedFeedRequestMessage inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUInt_length, SnapshotConsolidatedFeedRequestMessage.encode_length]
    omega

/-- Size rule: Client Length counts the bytes after it plus 1, so it is written from the body and checked on decode -/
def encode : ClientMessage → List UInt8 :=
  encodeFramed 1 1 encodeBody

def decode : List UInt8 → Option (ClientMessage × List UInt8) :=
  decodeFramed 1 1 decodeBody

@[simp] theorem decode_encode (message : ClientMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 1 1 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : ClientMessage) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

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

end Omi.BmvBmvmarketdataSnapshotIntraV11Client
