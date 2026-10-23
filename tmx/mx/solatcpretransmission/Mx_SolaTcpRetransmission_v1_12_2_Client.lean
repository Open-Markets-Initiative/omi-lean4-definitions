import Wire

/-!
# TMX Group Sola Tcp Retransmission v1.12.2

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.TmxMxSolatcpretransmissionHsvfV1122Client

/-- Login Message: 40 bytes -/
structure LoginMessage where
  user : Alpha 16
  pwd : Alpha 16
  loginTimestamp : Alpha 6
  protocol : Alpha 2
  deriving DecidableEq, Repr

namespace LoginMessage

def encode (message : LoginMessage) : List UInt8 :=
  Alpha.encode message.user
    ++ (Alpha.encode message.pwd
    ++ (Alpha.encode message.loginTimestamp
    ++ (Alpha.encode message.protocol)))

def decode (bytes : List UInt8) : Option (LoginMessage × List UInt8) := do
  let (user, bytes) ← Alpha.decode 16 bytes
  let (pwd, bytes) ← Alpha.decode 16 bytes
  let (loginTimestamp, bytes) ← Alpha.decode 6 bytes
  let (protocol, bytes) ← Alpha.decode 2 bytes
  pure ({ user, pwd, loginTimestamp, protocol }, bytes)

@[simp] theorem encode_length (message : LoginMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : LoginMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LoginMessage

/-- Logout Message: 0 bytes -/
structure LogoutMessage where
  deriving DecidableEq, Repr

namespace LogoutMessage

def encode (_ : LogoutMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (LogoutMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : LogoutMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : LogoutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end LogoutMessage

/-- Retransmission Request Message: 20 bytes -/
structure RetransmissionRequestMessage where
  line : Alpha 2
  start : Alpha 9
  end_ : Alpha 9
  deriving DecidableEq, Repr

namespace RetransmissionRequestMessage

def encode (message : RetransmissionRequestMessage) : List UInt8 :=
  Alpha.encode message.line
    ++ (Alpha.encode message.start
    ++ (Alpha.encode message.end_))

def decode (bytes : List UInt8) : Option (RetransmissionRequestMessage × List UInt8) := do
  let (line, bytes) ← Alpha.decode 2 bytes
  let (start, bytes) ← Alpha.decode 9 bytes
  let (end_, bytes) ← Alpha.decode 9 bytes
  pure ({ line, start, end_ }, bytes)

@[simp] theorem encode_length (message : RetransmissionRequestMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : RetransmissionRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RetransmissionRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end RetransmissionRequestMessage

/-- Any Client Message Body, selected by Client Message Type -/
inductive ClientMessageBody where
  | loginMessage (message : LoginMessage) -- "LI" 0x4C49
  | logoutMessage (message : LogoutMessage) -- "LO" 0x4C4F
  | retransmissionRequestMessage (message : RetransmissionRequestMessage) -- "RT" 0x5254
  deriving DecidableEq, Repr

namespace ClientMessageBody

/-- The Client Message Type each message is sent under -/
def tag : ClientMessageBody → BitVec 16
  | .loginMessage _ => 19529
  | .logoutMessage _ => 19535
  | .retransmissionRequestMessage _ => 21076

def encode : ClientMessageBody → List UInt8
  | .loginMessage message => LoginMessage.encode message
  | .logoutMessage message => LogoutMessage.encode message
  | .retransmissionRequestMessage message => RetransmissionRequestMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ClientMessageBody) : (encode message).length ≤ 40 := by
  cases message with
  | loginMessage inner =>
    simp only [encode, LoginMessage.encode_length]
    omega
  | logoutMessage inner =>
    simp only [encode, LogoutMessage.encode_length]
    omega
  | retransmissionRequestMessage inner =>
    simp only [encode, RetransmissionRequestMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (ClientMessageBody × List UInt8) :=
  if tag = 19529 then (LoginMessage.decode bytes).map fun (message, rest) => (.loginMessage message, rest)
  else if tag = 19535 then (LogoutMessage.decode bytes).map fun (message, rest) => (.logoutMessage message, rest)
  else if tag = 21076 then (RetransmissionRequestMessage.decode bytes).map fun (message, rest) => (.retransmissionRequestMessage message, rest)
  else none

@[simp] theorem decode_encode (message : ClientMessageBody) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ClientMessageBody

/-- Client Frame -/
structure ClientFrame where
  hsvfStx : BitVec 8
  sequenceNumber : Alpha 9
  clientMessageBody : ClientMessageBody
  hsvfEtx : BitVec 8
  deriving DecidableEq, Repr

namespace ClientFrame

def encode (message : ClientFrame) : List UInt8 :=
  encodeUInt 1 message.hsvfStx
    ++ (Alpha.encode message.sequenceNumber
    ++ (encodeUInt 2 (ClientMessageBody.tag message.clientMessageBody)
    ++ (ClientMessageBody.encode message.clientMessageBody
    ++ (encodeUInt 1 message.hsvfEtx))))

def decode (bytes : List UInt8) : Option (ClientFrame × List UInt8) := do
  let (hsvfStx, bytes) ← decodeUInt 1 bytes
  let (sequenceNumber, bytes) ← Alpha.decode 9 bytes
  let (clientMessageType, bytes) ← decodeUInt 2 bytes
  let (clientMessageBody, bytes) ← ClientMessageBody.decode clientMessageType bytes
  let (hsvfEtx, bytes) ← decodeUInt 1 bytes
  pure ({ hsvfStx, sequenceNumber, clientMessageBody, hsvfEtx }, bytes)

theorem encode_length_pos (message : ClientFrame) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ClientFrame) : (encode message).length ≤ 53 := by
  unfold encode
  cases message.clientMessageBody with
  | loginMessage inner =>
    simp only [ClientMessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, LoginMessage.encode_length]
    omega
  | logoutMessage inner =>
    simp only [ClientMessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, LogoutMessage.encode_length]
    omega
  | retransmissionRequestMessage inner =>
    simp only [ClientMessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, RetransmissionRequestMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : ClientFrame) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ClientMessageBody.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

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

end Omi.TmxMxSolatcpretransmissionHsvfV1122Client
