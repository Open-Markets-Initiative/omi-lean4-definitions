import Wire

/-!
# Databento Normalized v3

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.

Note: Control Fields is read up to the first 10 and carries the proof it holds none itself, which is
what lets it be written back with the one that closes it

License: MIT No Attribution
-/

namespace Omi.DatabentoMarketdataNormalizedDbnV3ClientStream

/-- Control Message -/
structure ControlMessage where
  controlFields : Terminated 10
  deriving DecidableEq, Repr

namespace ControlMessage

def encode (message : ControlMessage) : List UInt8 :=
  encodeTerminated 10 message.controlFields

def decode (bytes : List UInt8) : Option (ControlMessage × List UInt8) := do
  let (controlFields, bytes) ← decodeTerminated 10 bytes
  pure ({ controlFields }, bytes)

theorem encode_length_pos (message : ControlMessage) : (encode message).length > 0 := by
  have positive := encodeTerminated_length_pos 10 message.controlFields
  unfold encode
  omega

@[simp] theorem decode_encode (message : ControlMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeTerminated_encodeTerminated 10, some_bind]
  rfl

end ControlMessage

/-- Client Stream -/
structure ClientStream where
  controlMessage : List ControlMessage
  deriving DecidableEq, Repr

namespace ClientStream

def encode (message : ClientStream) : List UInt8 :=
  encodeMany ControlMessage.encode message.controlMessage

def decode (bytes : List UInt8) : Option ClientStream := do
  let controlMessage ← decodeAll ControlMessage.decode bytes.length bytes
  pure { controlMessage }

theorem decode_encode (message : ClientStream) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany ControlMessage.encode ControlMessage.decode ControlMessage.decode_encode ControlMessage.encode_length_pos message.controlMessage _ (encodeMany_length_ge ControlMessage.encode ControlMessage.encode_length_pos message.controlMessage), some_bind]
  rfl

end ClientStream

end Omi.DatabentoMarketdataNormalizedDbnV3ClientStream
