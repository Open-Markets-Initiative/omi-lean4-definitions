import Wire

/-!
# TMX Group Quantum Feed Level 1 Recovery v2.8

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.

Note: Num Body counts Admin Body from outside Heartbeat Body: it is handed down to the decoder, and
the list holds exactly as many as it says

Note: Heartbeat Body's Msg Length is written from its body but not checked on decode, since the body
has no bound the prefix must fit; the body is read by its content

Note: Num Body counts Replay Range from outside Replay Request: it is handed down to the decoder,
and the list holds exactly as many as it says

Note: Replay Request's Msg Length is written from its body but not checked on decode, since the body
has no bound the prefix must fit; the body is read by its content

Note: Client Body is keyed on Msg Type, which Heartbeat Body holds 2 bytes in, behind what frames
it: that byte is read where it lies without taking it, 48 reading Heartbeat Body, 49 reading Login
Request, 51 reading Logout, 53 reading Replay Request and nothing read on any other, each carrying
the proof of what its encoding holds there

Note: Client Frame's body has no bound its 2 byte Message Length must fit, so every message carries
the proof its own encoding fits: the record is its body with that proof, checked as the frame is
read

License: MIT No Attribution
-/

namespace Omi.TmxTsxQuantumfeedlevel1recoveryXmtV28Client

/-- Ack Required Poss Dup: one byte code -/
def AckRequiredPossDup.codes : List UInt8 :=
  [0x41, 0x44]

inductive AckRequiredPossDup where
  | ackRequired -- Ack Required
  | possDup -- Poss Dup
  | unlisted (byte : { byte : UInt8 // byte ∉ AckRequiredPossDup.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AckRequiredPossDup

def toByte : AckRequiredPossDup → UInt8
  | .ackRequired => 0x41
  | .possDup => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AckRequiredPossDup :=
  if byte = 0x41 then .ackRequired
  else .possDup

def ofByte (byte : UInt8) : AckRequiredPossDup :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AckRequiredPossDup) : ofByte value.toByte = value := by
  cases value with
  | ackRequired => decide
  | possDup => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AckRequiredPossDup) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AckRequiredPossDup × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AckRequiredPossDup) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : AckRequiredPossDup) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : AckRequiredPossDup) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AckRequiredPossDup

/-- Source Id: one byte code -/
def SourceId.codes : List UInt8 :=
  [0x30, 0x51, 0x56, 0x41]

inductive SourceId where
  | nonSourceRelated -- Non Source Related
  | tsx -- TSX
  | tsxVenture -- TSX Venture
  | alpha -- Alpha
  | unlisted (byte : { byte : UInt8 // byte ∉ SourceId.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SourceId

def toByte : SourceId → UInt8
  | .nonSourceRelated => 0x30
  | .tsx => 0x51
  | .tsxVenture => 0x56
  | .alpha => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SourceId :=
  if byte = 0x30 then .nonSourceRelated
  else if byte = 0x51 then .tsx
  else if byte = 0x56 then .tsxVenture
  else .alpha

def ofByte (byte : UInt8) : SourceId :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SourceId) : ofByte value.toByte = value := by
  cases value with
  | nonSourceRelated => decide
  | tsx => decide
  | tsxVenture => decide
  | alpha => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SourceId) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SourceId × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SourceId) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SourceId) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SourceId) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SourceId

/-- Admin Body: 8 bytes -/
structure AdminBody where
  sourceId : SourceId
  streamId : BitVec 16
  sequence0 : BitVec 8
  sequence1 : BitVec 32
  deriving DecidableEq, Repr

namespace AdminBody

def encode (message : AdminBody) : List UInt8 :=
  SourceId.encode message.sourceId
    ++ (encodeUIntLE 2 message.streamId
    ++ (encodeUInt 1 message.sequence0
    ++ (encodeUIntLE 4 message.sequence1)))

def decode (bytes : List UInt8) : Option (AdminBody × List UInt8) := do
  let (sourceId, bytes) ← SourceId.decode bytes
  let (streamId, bytes) ← decodeUIntLE 2 bytes
  let (sequence0, bytes) ← decodeUInt 1 bytes
  let (sequence1, bytes) ← decodeUIntLE 4 bytes
  pure ({ sourceId, streamId, sequence0, sequence1 }, bytes)

@[simp] theorem encode_length (message : AdminBody) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, SourceId.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : AdminBody) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AdminBody) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, SourceId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end AdminBody

/-- Heartbeat Body -/
structure HeartbeatBody (numBody : BitVec 8) where
  msgType : BitVec 8
  adminId : BitVec 8
  hbInterval : BitVec 16
  adminBody : Exact numBody.toNat AdminBody
  deriving DecidableEq, Repr

namespace HeartbeatBody

def encodeBody {numBody : BitVec 8} (message : HeartbeatBody numBody) : List UInt8 :=
  encodeUInt 1 message.msgType
    ++ (encodeUInt 1 message.adminId
    ++ (encodeUIntLE 2 message.hbInterval
    ++ (encodeMany AdminBody.encode message.adminBody.val)))

def decodeBody (numBody : BitVec 8) (bytes : List UInt8) : Option (HeartbeatBody numBody × List UInt8) := do
  let (msgType, bytes) ← decodeUInt 1 bytes
  let (adminId, bytes) ← decodeUInt 1 bytes
  let (hbInterval, bytes) ← decodeUIntLE 2 bytes
  let (adminBody_, bytes) ← decodeMany AdminBody.decode numBody.toNat bytes
  if fits_adminBody : adminBody_.length = numBody.toNat then
    pure ({ msgType, adminId, hbInterval, adminBody := ⟨adminBody_, fits_adminBody⟩ }, bytes)
  else none

theorem decodeBody_encodeBody (numBody : BitVec 8) (message : HeartbeatBody numBody) (rest : List UInt8) :
    decodeBody numBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_exact numBody.toNat AdminBody.encode AdminBody.decode AdminBody.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.adminBody.length_eq]
  rfl

/-- Size rule: Msg Length counts the bytes after it plus 2, so it is written from the body; the body has no bound the prefix must fit, so it is read by its content and the prefix is not checked -/
def encode {numBody : BitVec 8} (message : HeartbeatBody numBody) : List UInt8 :=
  encodeUIntLE 2 (BitVec.ofNat (8 * 2) ((encodeBody message).length + 2)) ++ encodeBody message

def decode (numBody : BitVec 8) (bytes : List UInt8) : Option (HeartbeatBody numBody × List UInt8) := do
  let (_, bytes) ← decodeUIntLE 2 bytes
  (decodeBody numBody) bytes

@[simp] theorem decode_encode (numBody : BitVec 8) (message : HeartbeatBody numBody) (rest : List UInt8) :
    decode numBody (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  exact decodeBody_encodeBody numBody message rest

theorem encode_length_pos {numBody : BitVec 8} (message : HeartbeatBody numBody) : (encode message).length > 0 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]
  omega

end HeartbeatBody

/-- Login Request -/
structure LoginRequest where
  msgType : BitVec 8
  adminId : BitVec 8
  hbInterval : BitVec 16
  replayWinSize : BitVec 16
  replayWinNum : BitVec 16
  credits : BitVec 16
  deriving DecidableEq, Repr

namespace LoginRequest

def encodeBody (message : LoginRequest) : List UInt8 :=
  encodeUInt 1 message.msgType
    ++ (encodeUInt 1 message.adminId
    ++ (encodeUIntLE 2 message.hbInterval
    ++ (encodeUIntLE 2 message.replayWinSize
    ++ (encodeUIntLE 2 message.replayWinNum
    ++ (encodeUIntLE 2 message.credits)))))

def decodeBody (bytes : List UInt8) : Option (LoginRequest × List UInt8) := do
  let (msgType, bytes) ← decodeUInt 1 bytes
  let (adminId, bytes) ← decodeUInt 1 bytes
  let (hbInterval, bytes) ← decodeUIntLE 2 bytes
  let (replayWinSize, bytes) ← decodeUIntLE 2 bytes
  let (replayWinNum, bytes) ← decodeUIntLE 2 bytes
  let (credits, bytes) ← decodeUIntLE 2 bytes
  pure ({ msgType, adminId, hbInterval, replayWinSize, replayWinNum, credits }, bytes)

theorem decodeBody_encodeBody (message : LoginRequest) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : LoginRequest) : (encodeBody message).length + 2 < 256 ^ 2 := by
  unfold encodeBody
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length]
  omega

/-- Size rule: Msg Length counts the bytes after it plus 2, so it is written from the body and checked on decode -/
def encode : LoginRequest → List UInt8 :=
  encodeFramedLE 2 2 encodeBody

def decode : List UInt8 → Option (LoginRequest × List UInt8) :=
  decodeFramedLE 2 2 decodeBody

@[simp] theorem decode_encode (message : LoginRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 2 2 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : LoginRequest) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end LoginRequest

/-- Logout -/
structure Logout where
  msgType : BitVec 8
  adminId : BitVec 8
  deriving DecidableEq, Repr

namespace Logout

def encodeBody (message : Logout) : List UInt8 :=
  encodeUInt 1 message.msgType
    ++ (encodeUInt 1 message.adminId)

def decodeBody (bytes : List UInt8) : Option (Logout × List UInt8) := do
  let (msgType, bytes) ← decodeUInt 1 bytes
  let (adminId, bytes) ← decodeUInt 1 bytes
  pure ({ msgType, adminId }, bytes)

theorem decodeBody_encodeBody (message : Logout) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Logout) : (encodeBody message).length + 2 < 256 ^ 2 := by
  unfold encodeBody
  simp only [List.length_append, encodeUInt_length]
  omega

/-- Size rule: Msg Length counts the bytes after it plus 2, so it is written from the body and checked on decode -/
def encode : Logout → List UInt8 :=
  encodeFramedLE 2 2 encodeBody

def decode : List UInt8 → Option (Logout × List UInt8) :=
  decodeFramedLE 2 2 decodeBody

@[simp] theorem decode_encode (message : Logout) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 2 2 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : Logout) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end Logout

/-- Replay Range: 12 bytes -/
structure ReplayRange where
  sourceId : SourceId
  streamId : BitVec 16
  sequence0 : BitVec 8
  sequence1Start : BitVec 32
  sequence1End : BitVec 32
  deriving DecidableEq, Repr

namespace ReplayRange

def encode (message : ReplayRange) : List UInt8 :=
  SourceId.encode message.sourceId
    ++ (encodeUIntLE 2 message.streamId
    ++ (encodeUInt 1 message.sequence0
    ++ (encodeUIntLE 4 message.sequence1Start
    ++ (encodeUIntLE 4 message.sequence1End))))

def decode (bytes : List UInt8) : Option (ReplayRange × List UInt8) := do
  let (sourceId, bytes) ← SourceId.decode bytes
  let (streamId, bytes) ← decodeUIntLE 2 bytes
  let (sequence0, bytes) ← decodeUInt 1 bytes
  let (sequence1Start, bytes) ← decodeUIntLE 4 bytes
  let (sequence1End, bytes) ← decodeUIntLE 4 bytes
  pure ({ sourceId, streamId, sequence0, sequence1Start, sequence1End }, bytes)

@[simp] theorem encode_length (message : ReplayRange) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, SourceId.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : ReplayRange) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReplayRange) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, SourceId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ReplayRange

/-- Replay Request -/
structure ReplayRequest (numBody : BitVec 8) where
  msgType : BitVec 8
  adminId : BitVec 8
  replaySessionId : BitVec 32
  replayRange : Exact numBody.toNat ReplayRange
  deriving DecidableEq, Repr

namespace ReplayRequest

def encodeBody {numBody : BitVec 8} (message : ReplayRequest numBody) : List UInt8 :=
  encodeUInt 1 message.msgType
    ++ (encodeUInt 1 message.adminId
    ++ (encodeUIntLE 4 message.replaySessionId
    ++ (encodeMany ReplayRange.encode message.replayRange.val)))

def decodeBody (numBody : BitVec 8) (bytes : List UInt8) : Option (ReplayRequest numBody × List UInt8) := do
  let (msgType, bytes) ← decodeUInt 1 bytes
  let (adminId, bytes) ← decodeUInt 1 bytes
  let (replaySessionId, bytes) ← decodeUIntLE 4 bytes
  let (replayRange_, bytes) ← decodeMany ReplayRange.decode numBody.toNat bytes
  if fits_replayRange : replayRange_.length = numBody.toNat then
    pure ({ msgType, adminId, replaySessionId, replayRange := ⟨replayRange_, fits_replayRange⟩ }, bytes)
  else none

theorem decodeBody_encodeBody (numBody : BitVec 8) (message : ReplayRequest numBody) (rest : List UInt8) :
    decodeBody numBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_exact numBody.toNat ReplayRange.encode ReplayRange.decode ReplayRange.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.replayRange.length_eq]
  rfl

/-- Size rule: Msg Length counts the bytes after it plus 2, so it is written from the body; the body has no bound the prefix must fit, so it is read by its content and the prefix is not checked -/
def encode {numBody : BitVec 8} (message : ReplayRequest numBody) : List UInt8 :=
  encodeUIntLE 2 (BitVec.ofNat (8 * 2) ((encodeBody message).length + 2)) ++ encodeBody message

def decode (numBody : BitVec 8) (bytes : List UInt8) : Option (ReplayRequest numBody × List UInt8) := do
  let (_, bytes) ← decodeUIntLE 2 bytes
  (decodeBody numBody) bytes

@[simp] theorem decode_encode (numBody : BitVec 8) (message : ReplayRequest numBody) (rest : List UInt8) :
    decode numBody (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  exact decodeBody_encodeBody numBody message rest

theorem encode_length_pos {numBody : BitVec 8} (message : ReplayRequest numBody) : (encode message).length > 0 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]
  omega

end ReplayRequest

/-- Client Body -/
structure ClientBodyPresent (numBody : BitVec 8) where
  clientBody : Peeked (HeartbeatBody numBody) (Peeked (LoginRequest) (Peeked (Logout) (Keyed (ReplayRequest.encode : ReplayRequest numBody → List UInt8) 2 [53]) Logout.encode (Keyed.encode (ReplayRequest.encode : ReplayRequest numBody → List UInt8)) 2 [51]) LoginRequest.encode (encodePeek Logout.encode (Keyed.encode (ReplayRequest.encode : ReplayRequest numBody → List UInt8))) 2 [49]) (HeartbeatBody.encode : HeartbeatBody numBody → List UInt8) (encodePeek LoginRequest.encode (encodePeek Logout.encode (Keyed.encode (ReplayRequest.encode : ReplayRequest numBody → List UInt8)))) 2 [48]
  deriving DecidableEq, Repr

namespace ClientBodyPresent

def encode {numBody : BitVec 8} (message : ClientBodyPresent numBody) : List UInt8 :=
  encodePeek (HeartbeatBody.encode : HeartbeatBody numBody → List UInt8) (encodePeek LoginRequest.encode (encodePeek Logout.encode (Keyed.encode (ReplayRequest.encode : ReplayRequest numBody → List UInt8)))) message.clientBody

def decode (numBody : BitVec 8) (bytes : List UInt8) : Option (ClientBodyPresent numBody × List UInt8) := do
  let (clientBody, bytes) ← decodePeek 2 [48] (decodeKeyed (HeartbeatBody.encode : HeartbeatBody numBody → List UInt8) (HeartbeatBody.decode numBody) 2 [48]) (decodeUnkeyed (encodePeek LoginRequest.encode (encodePeek Logout.encode (Keyed.encode (ReplayRequest.encode : ReplayRequest numBody → List UInt8)))) (decodePeek 2 [49] (decodeKeyed LoginRequest.encode LoginRequest.decode 2 [49]) (decodeUnkeyed (encodePeek Logout.encode (Keyed.encode (ReplayRequest.encode : ReplayRequest numBody → List UInt8))) (decodePeek 2 [51] (decodeKeyed Logout.encode Logout.decode 2 [51]) (decodeUnkeyed (Keyed.encode (ReplayRequest.encode : ReplayRequest numBody → List UInt8)) (decodeKeyed (ReplayRequest.encode : ReplayRequest numBody → List UInt8) (ReplayRequest.decode numBody) 2 [53]) 2 [51])) 2 [49])) 2 [48]) bytes
  pure ({ clientBody }, bytes)

theorem encode_length_pos {numBody : BitVec 8} (message : ClientBodyPresent numBody) : (encode message).length > 0 := by
  have positive := encodePeek_length_pos message.clientBody
  unfold encode
  omega

@[simp] theorem decode_encode (numBody : BitVec 8) (message : ClientBodyPresent numBody) (rest : List UInt8) :
    decode numBody (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodePeek_encodePeek (HeartbeatBody.encode : HeartbeatBody numBody → List UInt8) (HeartbeatBody.decode numBody) (encodePeek LoginRequest.encode (encodePeek Logout.encode (Keyed.encode (ReplayRequest.encode : ReplayRequest numBody → List UInt8)))) (decodePeek 2 [49] (decodeKeyed LoginRequest.encode LoginRequest.decode 2 [49]) (decodeUnkeyed (encodePeek Logout.encode (Keyed.encode (ReplayRequest.encode : ReplayRequest numBody → List UInt8))) (decodePeek 2 [51] (decodeKeyed Logout.encode Logout.decode 2 [51]) (decodeUnkeyed (Keyed.encode (ReplayRequest.encode : ReplayRequest numBody → List UInt8)) (decodeKeyed (ReplayRequest.encode : ReplayRequest numBody → List UInt8) (ReplayRequest.decode numBody) 2 [53]) 2 [51])) 2 [49])) 2 [48] (HeartbeatBody.decode_encode numBody) (decodePeek_encodePeek LoginRequest.encode LoginRequest.decode (encodePeek Logout.encode (Keyed.encode (ReplayRequest.encode : ReplayRequest numBody → List UInt8))) (decodePeek 2 [51] (decodeKeyed Logout.encode Logout.decode 2 [51]) (decodeUnkeyed (Keyed.encode (ReplayRequest.encode : ReplayRequest numBody → List UInt8)) (decodeKeyed (ReplayRequest.encode : ReplayRequest numBody → List UInt8) (ReplayRequest.decode numBody) 2 [53]) 2 [51])) 2 [49] LoginRequest.decode_encode (decodePeek_encodePeek Logout.encode Logout.decode (Keyed.encode (ReplayRequest.encode : ReplayRequest numBody → List UInt8)) (decodeKeyed (ReplayRequest.encode : ReplayRequest numBody → List UInt8) (ReplayRequest.decode numBody) 2 [53]) 2 [51] Logout.decode_encode (decodeKeyed_encodeKeyed (ReplayRequest.encode : ReplayRequest numBody → List UInt8) (ReplayRequest.decode numBody) 2 [53] (ReplayRequest.decode_encode numBody)))), some_bind]
  rfl

end ClientBodyPresent

/-- Client Frame: the body, which the record carries with the proof it fits its frame -/
structure ClientFrameBody where
  startOfFrame : BitVec 8
  protocolName : Alpha 1
  protocolVersion : Alpha 1
  sessionId : BitVec 32
  ackRequiredPossDup : AckRequiredPossDup
  numBody : BitVec 8
  clientBody : Option (ClientBodyPresent numBody)
  deriving DecidableEq, Repr

namespace ClientFrameBody

def encodeBody (message : ClientFrameBody) : List UInt8 :=
  encodeUIntLE 4 message.sessionId
    ++ (AckRequiredPossDup.encode message.ackRequiredPossDup
    ++ (encodeUInt 1 message.numBody
    ++ (encodeOptional (ClientBodyPresent.encode) message.clientBody)))

def decodeBody (startOfFrame : BitVec 8) (protocolName : Alpha 1) (protocolVersion : Alpha 1) (bytes : List UInt8) : Option ClientFrameBody := do
  let (sessionId, bytes) ← decodeUIntLE 4 bytes
  let (ackRequiredPossDup, bytes) ← AckRequiredPossDup.decode bytes
  let (numBody, bytes) ← decodeUInt 1 bytes
  let clientBody ← decodeRemaining (ClientBodyPresent.decode numBody) bytes
  pure { startOfFrame, protocolName, protocolVersion, sessionId, ackRequiredPossDup, numBody, clientBody }

theorem decodeBody_encodeBody (message : ClientFrameBody) : decodeBody message.startOfFrame message.protocolName message.protocolVersion (encodeBody message) = some message := by
  unfold decodeBody encodeBody
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [AckRequiredPossDup.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeRemaining_encodeOptional (ClientBodyPresent.encode) (ClientBodyPresent.decode message.numBody) (ClientBodyPresent.decode_encode message.numBody) (ClientBodyPresent.encode_length_pos), some_bind]
  rfl

end ClientFrameBody

/-- Client Frame: the body with the proof its encoding fits Message Length, whose 2 bytes no bound of the fields fits -/
abbrev ClientFrame := Fitting ClientFrameBody.encodeBody 0 65536

namespace ClientFrame

def encode (message : ClientFrame) : List UInt8 :=
  encodeUInt 1 message.val.startOfFrame
    ++ (Alpha.encode message.val.protocolName
    ++ (Alpha.encode message.val.protocolVersion
    ++ (encodeFramedLE 2 0 ClientFrameBody.encodeBody message.val)))

def decode (bytes : List UInt8) : Option (ClientFrame × List UInt8) := do
  let (startOfFrame, bytes) ← decodeUInt 1 bytes
  let (protocolName, bytes) ← Alpha.decode 1 bytes
  let (protocolVersion, bytes) ← Alpha.decode 1 bytes
  decodeFittingAllLE 2 0 ClientFrameBody.encodeBody (ClientFrameBody.decodeBody startOfFrame protocolName protocolVersion) bytes

@[simp] theorem decode_encode (message : ClientFrame) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  exact decodeFittingAllLE_encodeFramedLE 2 0 ClientFrameBody.encodeBody (ClientFrameBody.decodeBody message.val.startOfFrame message.val.protocolName message.val.protocolVersion) message (ClientFrameBody.decodeBody_encodeBody message.val) rest

theorem encode_length_pos (message : ClientFrame) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, Alpha.encode_length, List.length_append, ← Nat.add_assoc, encodeFramedLE_length]
  omega

/-- The most bytes an encoding can take: what the prefix can count, by the fit the message carries -/
theorem encode_length_le (message : ClientFrame) : (encode message).length ≤ 65540 := by
  have fits := message.fits
  unfold encode
  simp only [encodeUInt_length, Alpha.encode_length, List.length_append, ← Nat.add_assoc, encodeFramedLE_length]
  omega

end ClientFrame

/-- Client Packet -/
structure ClientPacket where
  clientFrame : List ClientFrame
  deriving DecidableEq, Repr

namespace ClientPacket

def encode (message : ClientPacket) : List UInt8 :=
  encodeMany ClientFrame.encode message.clientFrame

def decode (bytes : List UInt8) : Option ClientPacket := do
  let clientFrame ← decodeAll ClientFrame.decode bytes.length bytes
  pure { clientFrame }

theorem decode_encode (message : ClientPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany ClientFrame.encode ClientFrame.decode ClientFrame.decode_encode ClientFrame.encode_length_pos message.clientFrame _ (encodeMany_length_ge ClientFrame.encode ClientFrame.encode_length_pos message.clientFrame), some_bind]
  rfl

end ClientPacket

end Omi.TmxTsxQuantumfeedlevel1recoveryXmtV28Client
