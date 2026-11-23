import Wire

/-!
# National Stock Exchange of India Ltd Drop Copy v1.6

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.

Note: Client Packet Body is keyed on Transaction Code, which Client Registration Packet holds 16
bytes in, behind what frames it: those 2 bytes are read where they lie without taking them, 23008
reading Client Registration Packet and any other Client Session Packet, each carrying the proof of
what its encoding holds there

Note: Client Direct Packet's Packet Length is written from its body but not checked on decode, since
the body has no bound the prefix must fit; the body is read by its content

License: MIT No Attribution
-/

namespace Omi.NseNseixDropcopyNnfdirectV16Client

/-- Signon In Message: 174 bytes -/
structure SignonInMessage where
  userId : BitVec 32
  password : Alpha 8
  reserved8 : Alpha 8
  reserved30 : Alpha 30
  brokerId : Alpha 5
  reserved119 : Alpha 119
  deriving DecidableEq, Repr

namespace SignonInMessage

def encode (message : SignonInMessage) : List UInt8 :=
  encodeUInt 4 message.userId
    ++ (Alpha.encode message.password
    ++ (Alpha.encode message.reserved8
    ++ (Alpha.encode message.reserved30
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.reserved119)))))

def decode (bytes : List UInt8) : Option (SignonInMessage × List UInt8) := do
  let (userId, bytes) ← decodeUInt 4 bytes
  let (password, bytes) ← Alpha.decode 8 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  let (reserved30, bytes) ← Alpha.decode 30 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (reserved119, bytes) ← Alpha.decode 119 bytes
  pure ({ userId, password, reserved8, reserved30, brokerId, reserved119 }, bytes)

@[simp] theorem encode_length (message : SignonInMessage) : (encode message).length = 174 := by
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

/-- Dc Order Request Message: 8 bytes -/
structure DcOrderRequestMessage where
  orderSequenceNumber : Alpha 8
  deriving DecidableEq, Repr

namespace DcOrderRequestMessage

def encode (message : DcOrderRequestMessage) : List UInt8 :=
  Alpha.encode message.orderSequenceNumber

def decode (bytes : List UInt8) : Option (DcOrderRequestMessage × List UInt8) := do
  let (orderSequenceNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ orderSequenceNumber }, bytes)

@[simp] theorem encode_length (message : DcOrderRequestMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : DcOrderRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DcOrderRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end DcOrderRequestMessage

/-- Dc Ord Trd Request Message: 8 bytes -/
structure DcOrdTrdRequestMessage where
  orderTradeSequenceNumber : Alpha 8
  deriving DecidableEq, Repr

namespace DcOrdTrdRequestMessage

def encode (message : DcOrdTrdRequestMessage) : List UInt8 :=
  Alpha.encode message.orderTradeSequenceNumber

def decode (bytes : List UInt8) : Option (DcOrdTrdRequestMessage × List UInt8) := do
  let (orderTradeSequenceNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ orderTradeSequenceNumber }, bytes)

@[simp] theorem encode_length (message : DcOrdTrdRequestMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : DcOrdTrdRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DcOrdTrdRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end DcOrdTrdRequestMessage

/-- Any Client Message Payload, selected by Transaction Code -/
inductive ClientMessagePayload where
  | signonInMessage (message : SignonInMessage) -- 2300
  | heartbeatMessage (message : HeartbeatMessage) -- 23506
  | dcDownloadRequestMessage (message : DcDownloadRequestMessage) -- 8000
  | dcOrderRequestMessage (message : DcOrderRequestMessage) -- 8400
  | dcOrdTrdRequestMessage (message : DcOrdTrdRequestMessage) -- 8500
  deriving DecidableEq, Repr

namespace ClientMessagePayload

/-- The Transaction Code each message is sent under -/
def tag : ClientMessagePayload → BitVec 16
  | .signonInMessage _ => 2300
  | .heartbeatMessage _ => 23506
  | .dcDownloadRequestMessage _ => 8000
  | .dcOrderRequestMessage _ => 8400
  | .dcOrdTrdRequestMessage _ => 8500

def encode : ClientMessagePayload → List UInt8
  | .signonInMessage message => SignonInMessage.encode message
  | .heartbeatMessage message => HeartbeatMessage.encode message
  | .dcDownloadRequestMessage message => DcDownloadRequestMessage.encode message
  | .dcOrderRequestMessage message => DcOrderRequestMessage.encode message
  | .dcOrdTrdRequestMessage message => DcOrdTrdRequestMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ClientMessagePayload) : (encode message).length ≤ 174 := by
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
  | dcOrderRequestMessage inner =>
    simp only [encode, DcOrderRequestMessage.encode_length]
    omega
  | dcOrdTrdRequestMessage inner =>
    simp only [encode, DcOrdTrdRequestMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (ClientMessagePayload × List UInt8) :=
  if tag = 2300 then (SignonInMessage.decode bytes).map fun (message, rest) => (.signonInMessage message, rest)
  else if tag = 23506 then (HeartbeatMessage.decode bytes).map fun (message, rest) => (.heartbeatMessage message, rest)
  else if tag = 8000 then (DcDownloadRequestMessage.decode bytes).map fun (message, rest) => (.dcDownloadRequestMessage message, rest)
  else if tag = 8400 then (DcOrderRequestMessage.decode bytes).map fun (message, rest) => (.dcOrderRequestMessage message, rest)
  else if tag = 8500 then (DcOrdTrdRequestMessage.decode bytes).map fun (message, rest) => (.dcOrdTrdRequestMessage message, rest)
  else none

@[simp] theorem decode_encode (message : ClientMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ClientMessagePayload

/-- Client Registration Packet -/
structure ClientRegistrationPacket where
  registrationChecksum : Alpha 16
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

namespace ClientRegistrationPacket

def encode (message : ClientRegistrationPacket) : List UInt8 :=
  Alpha.encode message.registrationChecksum
    ++ (encodeUInt 2 (ClientMessagePayload.tag message.clientMessagePayload)
    ++ (encodeUInt 4 message.logTime
    ++ (Alpha.encode message.alphaChar
    ++ (encodeUInt 4 message.traderId
    ++ (encodeUInt 2 message.errorCode
    ++ (encodeUInt 8 message.headerTimestamp
    ++ (Alpha.encode message.timeStamp1
    ++ (Alpha.encode message.timeStamp2
    ++ (encodeUInt 2 message.messageLength
    ++ (ClientMessagePayload.encode message.clientMessagePayload))))))))))

def decode (bytes : List UInt8) : Option (ClientRegistrationPacket × List UInt8) := do
  let (registrationChecksum, bytes) ← Alpha.decode 16 bytes
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
  pure ({ registrationChecksum, logTime, alphaChar, traderId, errorCode, headerTimestamp, timeStamp1, timeStamp2, messageLength, clientMessagePayload }, bytes)

theorem encode_length_pos (message : ClientRegistrationPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ClientRegistrationPacket) : (encode message).length ≤ 230 := by
  unfold encode
  cases message.clientMessagePayload with
  | signonInMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, SignonInMessage.encode_length]
    omega
  | heartbeatMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, HeartbeatMessage.encode_length]
    omega
  | dcDownloadRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, DcDownloadRequestMessage.encode_length]
    omega
  | dcOrderRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, DcOrderRequestMessage.encode_length]
    omega
  | dcOrdTrdRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, DcOrdTrdRequestMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : ClientRegistrationPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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

end ClientRegistrationPacket

/-- Client Message Data -/
structure ClientMessageData where
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

namespace ClientMessageData

def encode (message : ClientMessageData) : List UInt8 :=
  encodeUInt 2 (ClientMessagePayload.tag message.clientMessagePayload)
    ++ (encodeUInt 4 message.logTime
    ++ (Alpha.encode message.alphaChar
    ++ (encodeUInt 4 message.traderId
    ++ (encodeUInt 2 message.errorCode
    ++ (encodeUInt 8 message.headerTimestamp
    ++ (Alpha.encode message.timeStamp1
    ++ (Alpha.encode message.timeStamp2
    ++ (encodeUInt 2 message.messageLength
    ++ (ClientMessagePayload.encode message.clientMessagePayload)))))))))

def decode (bytes : List UInt8) : Option (ClientMessageData × List UInt8) := do
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
  pure ({ logTime, alphaChar, traderId, errorCode, headerTimestamp, timeStamp1, timeStamp2, messageLength, clientMessagePayload }, bytes)

theorem encode_length_pos (message : ClientMessageData) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ClientMessageData) : (encode message).length ≤ 214 := by
  unfold encode
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
  | dcOrderRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, DcOrderRequestMessage.encode_length]
    omega
  | dcOrdTrdRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, DcOrdTrdRequestMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : ClientMessageData) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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

end ClientMessageData

/-- Client Session Packet -/
structure ClientSessionPacket where
  checksum : Alpha 16
  clientMessageData : ClientMessageData
  deriving DecidableEq, Repr

namespace ClientSessionPacket

def encode (message : ClientSessionPacket) : List UInt8 :=
  Alpha.encode message.checksum
    ++ (ClientMessageData.encode message.clientMessageData)

def decode (bytes : List UInt8) : Option (ClientSessionPacket × List UInt8) := do
  let (checksum, bytes) ← Alpha.decode 16 bytes
  let (clientMessageData, bytes) ← ClientMessageData.decode bytes
  pure ({ checksum, clientMessageData }, bytes)

theorem encode_length_pos (message : ClientSessionPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

@[simp] theorem decode_encode (message : ClientSessionPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [ClientMessageData.decode_encode, some_bind]
  rfl

end ClientSessionPacket

/-- Client Direct Packet -/
structure ClientDirectPacket where
  packetSequenceNumber : BitVec 32
  clientPacketBody : Peeked (ClientRegistrationPacket) (ClientSessionPacket) ClientRegistrationPacket.encode ClientSessionPacket.encode 16 [89, 224]
  deriving DecidableEq, Repr

namespace ClientDirectPacket

def encodeBody (message : ClientDirectPacket) : List UInt8 :=
  encodeUInt 4 message.packetSequenceNumber
    ++ (encodePeek ClientRegistrationPacket.encode ClientSessionPacket.encode message.clientPacketBody)

def decodeBody (bytes : List UInt8) : Option (ClientDirectPacket × List UInt8) := do
  let (packetSequenceNumber, bytes) ← decodeUInt 4 bytes
  let (clientPacketBody, bytes) ← decodePeek 16 [89, 224] (decodeKeyed ClientRegistrationPacket.encode ClientRegistrationPacket.decode 16 [89, 224]) (decodeUnkeyed ClientSessionPacket.encode ClientSessionPacket.decode 16 [89, 224]) bytes
  pure ({ packetSequenceNumber, clientPacketBody }, bytes)

theorem decodeBody_encodeBody (message : ClientDirectPacket) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodePeek_encodePeek ClientRegistrationPacket.encode ClientRegistrationPacket.decode ClientSessionPacket.encode ClientSessionPacket.decode 16 [89, 224] ClientRegistrationPacket.decode_encode ClientSessionPacket.decode_encode, some_bind]
  rfl

/-- Size rule: Packet Length counts the bytes after it plus 2, so it is written from the body; the body has no bound the prefix must fit, so it is read by its content and the prefix is not checked -/
def encode (message : ClientDirectPacket) : List UInt8 :=
  encodeUInt 2 (BitVec.ofNat (8 * 2) ((encodeBody message).length + 2)) ++ encodeBody message

def decode (bytes : List UInt8) : Option (ClientDirectPacket × List UInt8) := do
  let (_, bytes) ← decodeUInt 2 bytes
  decodeBody bytes

@[simp] theorem decode_encode (message : ClientDirectPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  exact decodeBody_encodeBody message rest

theorem encode_length_pos (message : ClientDirectPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]
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

end Omi.NseNseixDropcopyNnfdirectV16Client
