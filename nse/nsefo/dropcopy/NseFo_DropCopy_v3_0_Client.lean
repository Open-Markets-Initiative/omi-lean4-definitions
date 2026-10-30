import Wire

/-!
# National Stock Exchange of India Ltd Drop Copy v3.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NseNsefoDropcopyNnfdcV30Client

/-- Gr Request Message: 0 bytes -/
structure GrRequestMessage where
  deriving DecidableEq, Repr

namespace GrRequestMessage

def encode (_ : GrRequestMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (GrRequestMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : GrRequestMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : GrRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end GrRequestMessage

/-- Gr Secure User Registration Request Message: 0 bytes -/
structure GrSecureUserRegistrationRequestMessage where
  deriving DecidableEq, Repr

namespace GrSecureUserRegistrationRequestMessage

def encode (_ : GrSecureUserRegistrationRequestMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (GrSecureUserRegistrationRequestMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : GrSecureUserRegistrationRequestMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : GrSecureUserRegistrationRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end GrSecureUserRegistrationRequestMessage

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

/-- Dc Signon In Message: 16 bytes -/
structure DcSignonInMessage where
  password : Alpha 8
  sessionKey : Alpha 8
  deriving DecidableEq, Repr

namespace DcSignonInMessage

def encode (message : DcSignonInMessage) : List UInt8 :=
  Alpha.encode message.password
    ++ (Alpha.encode message.sessionKey)

def decode (bytes : List UInt8) : Option (DcSignonInMessage × List UInt8) := do
  let (password, bytes) ← Alpha.decode 8 bytes
  let (sessionKey, bytes) ← Alpha.decode 8 bytes
  pure ({ password, sessionKey }, bytes)

@[simp] theorem encode_length (message : DcSignonInMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : DcSignonInMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DcSignonInMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end DcSignonInMessage

/-- Dc Trd Subscription Request Message: 8 bytes -/
structure DcTrdSubscriptionRequestMessage where
  sequenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace DcTrdSubscriptionRequestMessage

def encode (message : DcTrdSubscriptionRequestMessage) : List UInt8 :=
  encodeUInt 8 message.sequenceNumber

def decode (bytes : List UInt8) : Option (DcTrdSubscriptionRequestMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ sequenceNumber }, bytes)

@[simp] theorem encode_length (message : DcTrdSubscriptionRequestMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : DcTrdSubscriptionRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DcTrdSubscriptionRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end DcTrdSubscriptionRequestMessage

/-- Dc Ont Subscription Request Message: 8 bytes -/
structure DcOntSubscriptionRequestMessage where
  sequenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace DcOntSubscriptionRequestMessage

def encode (message : DcOntSubscriptionRequestMessage) : List UInt8 :=
  encodeUInt 8 message.sequenceNumber

def decode (bytes : List UInt8) : Option (DcOntSubscriptionRequestMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ sequenceNumber }, bytes)

@[simp] theorem encode_length (message : DcOntSubscriptionRequestMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : DcOntSubscriptionRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DcOntSubscriptionRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end DcOntSubscriptionRequestMessage

/-- Any Client Message Payload, selected by Transaction Code -/
inductive ClientMessagePayload where
  | grRequestMessage (message : GrRequestMessage) -- 2400
  | grSecureUserRegistrationRequestMessage (message : GrSecureUserRegistrationRequestMessage) -- 23008
  | heartbeatMessage (message : HeartbeatMessage) -- 23506
  | dcSignonInMessage (message : DcSignonInMessage) -- 2500
  | dcTrdSubscriptionRequestMessage (message : DcTrdSubscriptionRequestMessage) -- 8000
  | dcOntSubscriptionRequestMessage (message : DcOntSubscriptionRequestMessage) -- 9000
  deriving DecidableEq, Repr

namespace ClientMessagePayload

/-- The Transaction Code each message is sent under -/
def tag : ClientMessagePayload → BitVec 16
  | .grRequestMessage _ => 2400
  | .grSecureUserRegistrationRequestMessage _ => 23008
  | .heartbeatMessage _ => 23506
  | .dcSignonInMessage _ => 2500
  | .dcTrdSubscriptionRequestMessage _ => 8000
  | .dcOntSubscriptionRequestMessage _ => 9000

def encode : ClientMessagePayload → List UInt8
  | .grRequestMessage message => GrRequestMessage.encode message
  | .grSecureUserRegistrationRequestMessage message => GrSecureUserRegistrationRequestMessage.encode message
  | .heartbeatMessage message => HeartbeatMessage.encode message
  | .dcSignonInMessage message => DcSignonInMessage.encode message
  | .dcTrdSubscriptionRequestMessage message => DcTrdSubscriptionRequestMessage.encode message
  | .dcOntSubscriptionRequestMessage message => DcOntSubscriptionRequestMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ClientMessagePayload) : (encode message).length ≤ 16 := by
  cases message with
  | grRequestMessage inner =>
    simp only [encode, GrRequestMessage.encode_length]
    omega
  | grSecureUserRegistrationRequestMessage inner =>
    simp only [encode, GrSecureUserRegistrationRequestMessage.encode_length]
    omega
  | heartbeatMessage inner =>
    simp only [encode, HeartbeatMessage.encode_length]
    omega
  | dcSignonInMessage inner =>
    simp only [encode, DcSignonInMessage.encode_length]
    omega
  | dcTrdSubscriptionRequestMessage inner =>
    simp only [encode, DcTrdSubscriptionRequestMessage.encode_length]
    omega
  | dcOntSubscriptionRequestMessage inner =>
    simp only [encode, DcOntSubscriptionRequestMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (ClientMessagePayload × List UInt8) :=
  if tag = 2400 then (GrRequestMessage.decode bytes).map fun (message, rest) => (.grRequestMessage message, rest)
  else if tag = 23008 then (GrSecureUserRegistrationRequestMessage.decode bytes).map fun (message, rest) => (.grSecureUserRegistrationRequestMessage message, rest)
  else if tag = 23506 then (HeartbeatMessage.decode bytes).map fun (message, rest) => (.heartbeatMessage message, rest)
  else if tag = 2500 then (DcSignonInMessage.decode bytes).map fun (message, rest) => (.dcSignonInMessage message, rest)
  else if tag = 8000 then (DcTrdSubscriptionRequestMessage.decode bytes).map fun (message, rest) => (.dcTrdSubscriptionRequestMessage message, rest)
  else if tag = 9000 then (DcOntSubscriptionRequestMessage.decode bytes).map fun (message, rest) => (.dcOntSubscriptionRequestMessage message, rest)
  else none

@[simp] theorem decode_encode (message : ClientMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ClientMessagePayload

/-- Client Drop Copy Packet -/
structure ClientDropCopyPacket where
  packetSequenceNumber : BitVec 32
  checksum : Alpha 16
  traderId : BitVec 32
  requestSequenceNumber : BitVec 64
  partitionId : Alpha 6
  concurrentLoginId : BitVec 16
  funcIndc : Alpha 1
  reserve : Alpha 1
  clientMessagePayload : ClientMessagePayload
  deriving DecidableEq, Repr

namespace ClientDropCopyPacket

def encodeBody (message : ClientDropCopyPacket) : List UInt8 :=
  encodeUInt 4 message.packetSequenceNumber
    ++ (Alpha.encode message.checksum
    ++ (encodeUInt 2 (ClientMessagePayload.tag message.clientMessagePayload)
    ++ (encodeUInt 4 message.traderId
    ++ (encodeUInt 8 message.requestSequenceNumber
    ++ (Alpha.encode message.partitionId
    ++ (encodeUInt 2 message.concurrentLoginId
    ++ (Alpha.encode message.funcIndc
    ++ (Alpha.encode message.reserve
    ++ (ClientMessagePayload.encode message.clientMessagePayload)))))))))

def decodeBody (bytes : List UInt8) : Option (ClientDropCopyPacket × List UInt8) := do
  let (packetSequenceNumber, bytes) ← decodeUInt 4 bytes
  let (checksum, bytes) ← Alpha.decode 16 bytes
  let (transactionCode, bytes) ← decodeUInt 2 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (requestSequenceNumber, bytes) ← decodeUInt 8 bytes
  let (partitionId, bytes) ← Alpha.decode 6 bytes
  let (concurrentLoginId, bytes) ← decodeUInt 2 bytes
  let (funcIndc, bytes) ← Alpha.decode 1 bytes
  let (reserve, bytes) ← Alpha.decode 1 bytes
  let (clientMessagePayload, bytes) ← ClientMessagePayload.decode transactionCode bytes
  pure ({ packetSequenceNumber, checksum, traderId, requestSequenceNumber, partitionId, concurrentLoginId, funcIndc, reserve, clientMessagePayload }, bytes)

theorem decodeBody_encodeBody (message : ClientDropCopyPacket) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [ClientMessagePayload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : ClientDropCopyPacket) : (encodeBody message).length + 2 < 256 ^ 2 := by
  unfold encodeBody
  cases message.clientMessagePayload with
  | grRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, GrRequestMessage.encode_length]
    omega
  | grSecureUserRegistrationRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, GrSecureUserRegistrationRequestMessage.encode_length]
    omega
  | heartbeatMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, HeartbeatMessage.encode_length]
    omega
  | dcSignonInMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, DcSignonInMessage.encode_length]
    omega
  | dcTrdSubscriptionRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, DcTrdSubscriptionRequestMessage.encode_length]
    omega
  | dcOntSubscriptionRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, DcOntSubscriptionRequestMessage.encode_length]
    omega

/-- Size rule: Packet Length counts the bytes after it plus 2, so it is written from the body and checked on decode -/
def encode : ClientDropCopyPacket → List UInt8 :=
  encodeFramed 2 2 encodeBody

def decode : List UInt8 → Option (ClientDropCopyPacket × List UInt8) :=
  decodeFramed 2 2 decodeBody

@[simp] theorem decode_encode (message : ClientDropCopyPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 2 2 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : ClientDropCopyPacket) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end ClientDropCopyPacket

/-- Client Packet -/
structure ClientPacket where
  clientDropCopyPacket : List ClientDropCopyPacket
  deriving DecidableEq, Repr

namespace ClientPacket

def encode (message : ClientPacket) : List UInt8 :=
  encodeMany ClientDropCopyPacket.encode message.clientDropCopyPacket

def decode (bytes : List UInt8) : Option ClientPacket := do
  let clientDropCopyPacket ← decodeAll ClientDropCopyPacket.decode bytes.length bytes
  pure { clientDropCopyPacket }

theorem decode_encode (message : ClientPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany ClientDropCopyPacket.encode ClientDropCopyPacket.decode ClientDropCopyPacket.decode_encode ClientDropCopyPacket.encode_length_pos message.clientDropCopyPacket _ (encodeMany_length_ge ClientDropCopyPacket.encode ClientDropCopyPacket.encode_length_pos message.clientDropCopyPacket), some_bind]
  rfl

end ClientPacket

end Omi.NseNsefoDropcopyNnfdcV30Client
