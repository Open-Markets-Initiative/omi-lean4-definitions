import Wire

/-!
# Japan Exchange Group Rewind v2.2

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.JpxOsederivativesRewindItchV22

/-- Rewind Request Packet: 20 bytes -/
structure RewindRequestPacket where
  session : Alpha 10
  sequenceNumber : BitVec 64
  requestedMessageCount : BitVec 16
  deriving DecidableEq, Repr

namespace RewindRequestPacket

def encode (message : RewindRequestPacket) : List UInt8 :=
  Alpha.encode message.session
    ++ (encodeUInt 8 message.sequenceNumber
    ++ (encodeUInt 2 message.requestedMessageCount))

def decode (bytes : List UInt8) : Option (RewindRequestPacket × List UInt8) := do
  let (session, bytes) ← Alpha.decode 10 bytes
  let (sequenceNumber, bytes) ← decodeUInt 8 bytes
  let (requestedMessageCount, bytes) ← decodeUInt 2 bytes
  pure ({ session, sequenceNumber, requestedMessageCount }, bytes)

@[simp] theorem encode_length (message : RewindRequestPacket) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : RewindRequestPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RewindRequestPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end RewindRequestPacket

end Omi.JpxOsederivativesRewindItchV22
