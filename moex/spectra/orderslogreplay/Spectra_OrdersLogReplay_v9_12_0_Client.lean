import Wire

/-!
# Moscow Exchange SIMBA Spectra Orders Log Historical Replay v9.12.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.MoexSpectraOrderslogreplaySimbaV9120Client

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

/-- Market Data Request Message: 8 bytes -/
structure MarketDataRequestMessage where
  applBegSeqNum : BitVec 32
  applEndSeqNum : BitVec 32
  deriving DecidableEq, Repr

namespace MarketDataRequestMessage

def encode (message : MarketDataRequestMessage) : List UInt8 :=
  encodeUIntLE 4 message.applBegSeqNum
    ++ (encodeUIntLE 4 message.applEndSeqNum)

def decode (bytes : List UInt8) : Option (MarketDataRequestMessage × List UInt8) := do
  let (applBegSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (applEndSeqNum, bytes) ← decodeUIntLE 4 bytes
  pure ({ applBegSeqNum, applEndSeqNum }, bytes)

@[simp] theorem encode_length (message : MarketDataRequestMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : MarketDataRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketDataRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end MarketDataRequestMessage

/-- Any Client Payload, selected by Template Id -/
inductive ClientPayload where
  | logonMessage (message : LogonMessage) -- 1000
  | logoutMessage (message : LogoutMessage) -- 1001
  | marketDataRequestMessage (message : MarketDataRequestMessage) -- 1002
  deriving DecidableEq, Repr

namespace ClientPayload

/-- The Template Id each message is sent under -/
def tag : ClientPayload → BitVec 16
  | .logonMessage _ => 1000
  | .logoutMessage _ => 1001
  | .marketDataRequestMessage _ => 1002

def encode : ClientPayload → List UInt8
  | .logonMessage message => LogonMessage.encode message
  | .logoutMessage message => LogoutMessage.encode message
  | .marketDataRequestMessage message => MarketDataRequestMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ClientPayload) : (encode message).length ≤ 256 := by
  cases message with
  | logonMessage inner =>
    simp only [encode, LogonMessage.encode_length]
    omega
  | logoutMessage inner =>
    simp only [encode, LogoutMessage.encode_length]
    omega
  | marketDataRequestMessage inner =>
    simp only [encode, MarketDataRequestMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (ClientPayload × List UInt8) :=
  if tag = 1000 then (LogonMessage.decode bytes).map fun (message, rest) => (.logonMessage message, rest)
  else if tag = 1001 then (LogoutMessage.decode bytes).map fun (message, rest) => (.logoutMessage message, rest)
  else if tag = 1002 then (MarketDataRequestMessage.decode bytes).map fun (message, rest) => (.marketDataRequestMessage message, rest)
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
theorem encode_length_le (message : ClientMessage) : (encode message).length ≤ 264 := by
  unfold encode
  cases message.clientPayload with
  | logonMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, LogonMessage.encode_length]
    omega
  | logoutMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, LogoutMessage.encode_length]
    omega
  | marketDataRequestMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, MarketDataRequestMessage.encode_length]
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

/-- Client Frame -/
structure ClientFrame where
  msgSeqNum : BitVec 32
  msgFlags : BitVec 16
  sendingTime : BitVec 64
  clientMessage : ClientMessage
  deriving DecidableEq, Repr

namespace ClientFrame

def encodeBody (message : ClientFrame) : List UInt8 :=
  encodeUIntLE 2 message.msgFlags
    ++ (encodeUIntLE 8 message.sendingTime
    ++ (ClientMessage.encode message.clientMessage))

def decodeBody (msgSeqNum : BitVec 32) (bytes : List UInt8) : Option (ClientFrame × List UInt8) := do
  let (msgFlags, bytes) ← decodeUIntLE 2 bytes
  let (sendingTime, bytes) ← decodeUIntLE 8 bytes
  let (clientMessage, bytes) ← ClientMessage.decode bytes
  pure ({ msgSeqNum, msgFlags, sendingTime, clientMessage }, bytes)

theorem decodeBody_encodeBody (message : ClientFrame) (rest : List UInt8) :
    decodeBody message.msgSeqNum (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [ClientMessage.decode_encode, some_bind]
  rfl

/-- Size rule: Msg Size counts the bytes after it plus 6, so it is written from the body; the body has no bound the prefix must fit, so it is read by its content and the prefix is not checked; Msg Seq Num is read ahead of it -/
def encode (message : ClientFrame) : List UInt8 :=
  encodeUIntLE 4 message.msgSeqNum
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) ((encodeBody message).length + 6)) ++ encodeBody message)

def decode (bytes : List UInt8) : Option (ClientFrame × List UInt8) := do
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (_, bytes) ← decodeUIntLE 2 bytes
  (decodeBody msgSeqNum) bytes

@[simp] theorem decode_encode (message : ClientFrame) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  exact decodeBody_encodeBody message rest

theorem encode_length_pos (message : ClientFrame) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
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

end Omi.MoexSpectraOrderslogreplaySimbaV9120Client
