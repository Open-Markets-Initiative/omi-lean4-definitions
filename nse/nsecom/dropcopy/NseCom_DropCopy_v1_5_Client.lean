import Wire

/-!
# National Stock Exchange of India Ltd Drop Copy v1.5

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NseNsecomDropcopyNnfdirectV15Client

/-- Signon In Message: 238 bytes -/
structure SignonInMessage where
  userId : BitVec 32
  reserved8 : Alpha 8
  password : Alpha 8
  secondReserved8 : Alpha 8
  reserved38 : Alpha 38
  brokerId : Alpha 5
  reserved119 : Alpha 119
  reserved16 : Alpha 16
  secondReserved16 : Alpha 16
  thirdReserved16 : Alpha 16
  deriving DecidableEq, Repr

namespace SignonInMessage

def encode (message : SignonInMessage) : List UInt8 :=
  encodeUInt 4 message.userId
    ++ (Alpha.encode message.reserved8
    ++ (Alpha.encode message.password
    ++ (Alpha.encode message.secondReserved8
    ++ (Alpha.encode message.reserved38
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.reserved119
    ++ (Alpha.encode message.reserved16
    ++ (Alpha.encode message.secondReserved16
    ++ (Alpha.encode message.thirdReserved16)))))))))

def decode (bytes : List UInt8) : Option (SignonInMessage × List UInt8) := do
  let (userId, bytes) ← decodeUInt 4 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  let (password, bytes) ← Alpha.decode 8 bytes
  let (secondReserved8, bytes) ← Alpha.decode 8 bytes
  let (reserved38, bytes) ← Alpha.decode 38 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (reserved119, bytes) ← Alpha.decode 119 bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  let (secondReserved16, bytes) ← Alpha.decode 16 bytes
  let (thirdReserved16, bytes) ← Alpha.decode 16 bytes
  pure ({ userId, reserved8, password, secondReserved8, reserved38, brokerId, reserved119, reserved16, secondReserved16, thirdReserved16 }, bytes)

@[simp] theorem encode_length (message : SignonInMessage) : (encode message).length = 238 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : SignonInMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SignonInMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SignonInMessage

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

/-- Dc Download Request Message: 8 bytes -/
structure DcDownloadRequestMessage where
  sequenceNumber : Alpha 8
  deriving DecidableEq, Repr

namespace DcDownloadRequestMessage

def encode (message : DcDownloadRequestMessage) : List UInt8 :=
  Alpha.encode message.sequenceNumber

def decode (bytes : List UInt8) : Option (DcDownloadRequestMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ sequenceNumber }, bytes)

@[simp] theorem encode_length (message : DcDownloadRequestMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : DcDownloadRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DcDownloadRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end DcDownloadRequestMessage

/-- Any Client Message Payload, selected by Transaction Code -/
inductive ClientMessagePayload where
  | signonInMessage (message : SignonInMessage) -- 2300
  | heartbeatMessage (message : HeartbeatMessage) -- 23506
  | dcDownloadRequestMessage (message : DcDownloadRequestMessage) -- 8000
  deriving DecidableEq, Repr

namespace ClientMessagePayload

/-- The Transaction Code each message is sent under -/
def tag : ClientMessagePayload → BitVec 16
  | .signonInMessage _ => 2300
  | .heartbeatMessage _ => 23506
  | .dcDownloadRequestMessage _ => 8000

def encode : ClientMessagePayload → List UInt8
  | .signonInMessage message => SignonInMessage.encode message
  | .heartbeatMessage message => HeartbeatMessage.encode message
  | .dcDownloadRequestMessage message => DcDownloadRequestMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ClientMessagePayload) : (encode message).length ≤ 238 := by
  cases message with
  | signonInMessage inner =>
    simp only [encode, SignonInMessage.encode_length]
    omega
  | heartbeatMessage inner =>
    simp only [encode, HeartbeatMessage.encode_length]
    omega
  | dcDownloadRequestMessage inner =>
    simp only [encode, DcDownloadRequestMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (ClientMessagePayload × List UInt8) :=
  if tag = 2300 then (SignonInMessage.decode bytes).map fun (message, rest) => (.signonInMessage message, rest)
  else if tag = 23506 then (HeartbeatMessage.decode bytes).map fun (message, rest) => (.heartbeatMessage message, rest)
  else if tag = 8000 then (DcDownloadRequestMessage.decode bytes).map fun (message, rest) => (.dcDownloadRequestMessage message, rest)
  else none

@[simp] theorem decode_encode (message : ClientMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ClientMessagePayload

/-- Client Direct Packet -/
structure ClientDirectPacket where
  packetSequenceNumber : BitVec 32
  checksum : Alpha 16
  logTime : BitVec 32
  alphaChar : Alpha 2
  traderId : BitVec 32
  errorCode : BitVec 16
  headerTimestamp : BitVec 64
  timeStamp1 : Alpha 8
  timeStamp2 : Alpha 8
  messageLength : BitVec 16
  clientMessagePayload : ClientMessagePayload
  deriving DecidableEq, Repr

namespace ClientDirectPacket

def encodeBody (message : ClientDirectPacket) : List UInt8 :=
  encodeUInt 4 message.packetSequenceNumber
    ++ (Alpha.encode message.checksum
    ++ (encodeUInt 2 (ClientMessagePayload.tag message.clientMessagePayload)
    ++ (encodeUInt 4 message.logTime
    ++ (Alpha.encode message.alphaChar
    ++ (encodeUInt 4 message.traderId
    ++ (encodeUInt 2 message.errorCode
    ++ (encodeUInt 8 message.headerTimestamp
    ++ (Alpha.encode message.timeStamp1
    ++ (Alpha.encode message.timeStamp2
    ++ (encodeUInt 2 message.messageLength
    ++ (ClientMessagePayload.encode message.clientMessagePayload)))))))))))

def decodeBody (bytes : List UInt8) : Option (ClientDirectPacket × List UInt8) := do
  let (packetSequenceNumber, bytes) ← decodeUInt 4 bytes
  let (checksum, bytes) ← Alpha.decode 16 bytes
  let (transactionCode, bytes) ← decodeUInt 2 bytes
  let (logTime, bytes) ← decodeUInt 4 bytes
  let (alphaChar, bytes) ← Alpha.decode 2 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (errorCode, bytes) ← decodeUInt 2 bytes
  let (headerTimestamp, bytes) ← decodeUInt 8 bytes
  let (timeStamp1, bytes) ← Alpha.decode 8 bytes
  let (timeStamp2, bytes) ← Alpha.decode 8 bytes
  let (messageLength, bytes) ← decodeUInt 2 bytes
  let (clientMessagePayload, bytes) ← ClientMessagePayload.decode transactionCode bytes
  pure ({ packetSequenceNumber, checksum, logTime, alphaChar, traderId, errorCode, headerTimestamp, timeStamp1, timeStamp2, messageLength, clientMessagePayload }, bytes)

theorem decodeBody_encodeBody (message : ClientDirectPacket) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ClientMessagePayload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : ClientDirectPacket) : (encodeBody message).length + 2 < 256 ^ 2 := by
  unfold encodeBody
  cases message.clientMessagePayload with
  | signonInMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, SignonInMessage.encode_length]
    omega
  | heartbeatMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, HeartbeatMessage.encode_length]
    omega
  | dcDownloadRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, DcDownloadRequestMessage.encode_length]
    omega

/-- Size rule: Packet Length counts the bytes after it plus 2, so it is written from the body and checked on decode -/
def encode : ClientDirectPacket → List UInt8 :=
  encodeFramed 2 2 encodeBody

def decode : List UInt8 → Option (ClientDirectPacket × List UInt8) :=
  decodeFramed 2 2 decodeBody

@[simp] theorem decode_encode (message : ClientDirectPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 2 2 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : ClientDirectPacket) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end ClientDirectPacket

/-- Client Packet -/
structure ClientPacket where
  clientDirectPacket : List ClientDirectPacket
  deriving DecidableEq, Repr

namespace ClientPacket

def encode (message : ClientPacket) : List UInt8 :=
  encodeMany ClientDirectPacket.encode message.clientDirectPacket

def decode (bytes : List UInt8) : Option ClientPacket := do
  let clientDirectPacket ← decodeAll ClientDirectPacket.decode bytes.length bytes
  pure { clientDirectPacket }

theorem decode_encode (message : ClientPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany ClientDirectPacket.encode ClientDirectPacket.decode ClientDirectPacket.decode_encode ClientDirectPacket.encode_length_pos message.clientDirectPacket _ (encodeMany_length_ge ClientDirectPacket.encode ClientDirectPacket.encode_length_pos message.clientDirectPacket), some_bind]
  rfl

end ClientPacket

end Omi.NseNsecomDropcopyNnfdirectV15Client
