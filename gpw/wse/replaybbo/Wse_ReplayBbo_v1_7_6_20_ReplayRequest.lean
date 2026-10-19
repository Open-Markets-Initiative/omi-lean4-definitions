import Wire

/-!
# Giełda Papierów Wartościowych w Warszawie Warsaw Stock Exchange BBO Replay v1.7.6

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.GpwWseReplaybboWatsV17620ReplayRequest

/-- Replay Request: 9 bytes -/
structure ReplayRequest where
  seqNum : BitVec 32
  endSeqNum : BitVec 32
  streamId : BitVec 8
  deriving DecidableEq, Repr

namespace ReplayRequest

def encode (message : ReplayRequest) : List UInt8 :=
  encodeUIntLE 4 message.seqNum
    ++ (encodeUIntLE 4 message.endSeqNum
    ++ (encodeUIntLE 1 message.streamId))

def decode (bytes : List UInt8) : Option (ReplayRequest × List UInt8) := do
  let (seqNum, bytes) ← decodeUIntLE 4 bytes
  let (endSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (streamId, bytes) ← decodeUIntLE 1 bytes
  pure ({ seqNum, endSeqNum, streamId }, bytes)

@[simp] theorem encode_length (message : ReplayRequest) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : ReplayRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReplayRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ReplayRequest

/-- Any Replay Request Payload, selected by Replay Message Type -/
inductive ReplayRequestPayload where
  | replayRequest (message : ReplayRequest) -- 1
  deriving DecidableEq, Repr

namespace ReplayRequestPayload

/-- The Replay Message Type each message is sent under -/
def tag : ReplayRequestPayload → BitVec 16
  | .replayRequest _ => 1

def encode : ReplayRequestPayload → List UInt8
  | .replayRequest message => ReplayRequest.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ReplayRequestPayload) : (encode message).length ≤ 9 := by
  cases message with
  | replayRequest inner =>
    simp only [encode, ReplayRequest.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (ReplayRequestPayload × List UInt8) :=
  if tag = 1 then (ReplayRequest.decode bytes).map fun (message, rest) => (.replayRequest message, rest)
  else none

@[simp] theorem decode_encode (message : ReplayRequestPayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ReplayRequestPayload

/-- Replay Request Message -/
structure ReplayRequestMessage where
  replayMessageLength : BitVec 16
  replayRequestPayload : ReplayRequestPayload
  deriving DecidableEq, Repr

namespace ReplayRequestMessage

def encode (message : ReplayRequestMessage) : List UInt8 :=
  encodeUIntLE 2 message.replayMessageLength
    ++ (encodeUIntLE 2 (ReplayRequestPayload.tag message.replayRequestPayload)
    ++ (ReplayRequestPayload.encode message.replayRequestPayload))

def decode (bytes : List UInt8) : Option (ReplayRequestMessage × List UInt8) := do
  let (replayMessageLength, bytes) ← decodeUIntLE 2 bytes
  let (replayMessageType, bytes) ← decodeUIntLE 2 bytes
  let (replayRequestPayload, bytes) ← ReplayRequestPayload.decode replayMessageType bytes
  pure ({ replayMessageLength, replayRequestPayload }, bytes)

theorem encode_length_pos (message : ReplayRequestMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ReplayRequestMessage) : (encode message).length ≤ 13 := by
  unfold encode
  cases message.replayRequestPayload with
  | replayRequest inner =>
    simp only [ReplayRequestPayload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, ReplayRequest.encode_length]
    omega

@[simp] theorem decode_encode (message : ReplayRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [ReplayRequestPayload.decode_encode, some_bind]
  rfl

end ReplayRequestMessage

/-- Replay Request Packet -/
structure ReplayRequestPacket where
  replayRequestMessage : List ReplayRequestMessage
  deriving DecidableEq, Repr

namespace ReplayRequestPacket

def encode (message : ReplayRequestPacket) : List UInt8 :=
  encodeMany ReplayRequestMessage.encode message.replayRequestMessage

def decode (bytes : List UInt8) : Option ReplayRequestPacket := do
  let replayRequestMessage ← decodeAll ReplayRequestMessage.decode bytes.length bytes
  pure { replayRequestMessage }

theorem decode_encode (message : ReplayRequestPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany ReplayRequestMessage.encode ReplayRequestMessage.decode ReplayRequestMessage.decode_encode ReplayRequestMessage.encode_length_pos message.replayRequestMessage _ (encodeMany_length_ge ReplayRequestMessage.encode ReplayRequestMessage.encode_length_pos message.replayRequestMessage), some_bind]
  rfl

end ReplayRequestPacket

end Omi.GpwWseReplaybboWatsV17620ReplayRequest
