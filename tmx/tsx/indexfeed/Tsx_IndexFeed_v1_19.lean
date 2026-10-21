import Wire

/-!
# TMX Group Index Feed v1.19

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.TmxTsxIndexfeedQrtmdV119

/-- Retransmission Identifier: one byte code -/
def RetransmissionIdentifier.codes : List UInt8 :=
  [0x30]

inductive RetransmissionIdentifier where
  | normalTransmission -- Normal Transmission
  | unlisted (byte : { byte : UInt8 // byte ∉ RetransmissionIdentifier.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RetransmissionIdentifier

def toByte : RetransmissionIdentifier → UInt8
  | .normalTransmission => 0x30
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : RetransmissionIdentifier :=
  .normalTransmission

def ofByte (byte : UInt8) : RetransmissionIdentifier :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RetransmissionIdentifier) : ofByte value.toByte = value := by
  cases value with
  | normalTransmission => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RetransmissionIdentifier) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RetransmissionIdentifier × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RetransmissionIdentifier) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : RetransmissionIdentifier) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : RetransmissionIdentifier) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RetransmissionIdentifier

/-- Continuation Identifier: one byte code -/
def ContinuationIdentifier.codes : List UInt8 :=
  [0x30]

inductive ContinuationIdentifier where
  | standAloneMessage -- Stand Alone Message
  | unlisted (byte : { byte : UInt8 // byte ∉ ContinuationIdentifier.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ContinuationIdentifier

def toByte : ContinuationIdentifier → UInt8
  | .standAloneMessage => 0x30
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : ContinuationIdentifier :=
  .standAloneMessage

def ofByte (byte : UInt8) : ContinuationIdentifier :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ContinuationIdentifier) : ofByte value.toByte = value := by
  cases value with
  | standAloneMessage => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ContinuationIdentifier) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ContinuationIdentifier × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ContinuationIdentifier) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ContinuationIdentifier) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ContinuationIdentifier) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ContinuationIdentifier

/-- Markers: one byte code -/
def Markers.codes : List UInt8 :=
  [0x43]

inductive Markers where
  | close -- Close
  | unlisted (byte : { byte : UInt8 // byte ∉ Markers.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Markers

def toByte : Markers → UInt8
  | .close => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : Markers :=
  .close

def ofByte (byte : UInt8) : Markers :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Markers) : ofByte value.toByte = value := by
  cases value with
  | close => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Markers) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Markers × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Markers) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Markers) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Markers) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Markers

/-- S And P Tsx Official Index Level Message: 122 bytes -/
structure SAndPTsxOfficialIndexLevelMessage where
  time : Alpha 6
  indexId : Alpha 4
  lastLevel : Alpha 8
  netChange : Alpha 7
  volume : Alpha 11
  value : Alpha 12
  openLevel : Alpha 8
  settlementValue : Alpha 8
  specialOpeningQuote : Alpha 8
  percentTrading : Alpha 7
  highLevel : Alpha 8
  lowLevel : Alpha 8
  pe : Alpha 7
  yield : Alpha 5
  markers : Markers
  bidPrice : Alpha 7
  askPrice : Alpha 7
  deriving DecidableEq, Repr

namespace SAndPTsxOfficialIndexLevelMessage

def encode (message : SAndPTsxOfficialIndexLevelMessage) : List UInt8 :=
  Alpha.encode message.time
    ++ (Alpha.encode message.indexId
    ++ (Alpha.encode message.lastLevel
    ++ (Alpha.encode message.netChange
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.value
    ++ (Alpha.encode message.openLevel
    ++ (Alpha.encode message.settlementValue
    ++ (Alpha.encode message.specialOpeningQuote
    ++ (Alpha.encode message.percentTrading
    ++ (Alpha.encode message.highLevel
    ++ (Alpha.encode message.lowLevel
    ++ (Alpha.encode message.pe
    ++ (Alpha.encode message.yield
    ++ (Markers.encode message.markers
    ++ (Alpha.encode message.bidPrice
    ++ (Alpha.encode message.askPrice))))))))))))))))

def decode (bytes : List UInt8) : Option (SAndPTsxOfficialIndexLevelMessage × List UInt8) := do
  let (time, bytes) ← Alpha.decode 6 bytes
  let (indexId, bytes) ← Alpha.decode 4 bytes
  let (lastLevel, bytes) ← Alpha.decode 8 bytes
  let (netChange, bytes) ← Alpha.decode 7 bytes
  let (volume, bytes) ← Alpha.decode 11 bytes
  let (value, bytes) ← Alpha.decode 12 bytes
  let (openLevel, bytes) ← Alpha.decode 8 bytes
  let (settlementValue, bytes) ← Alpha.decode 8 bytes
  let (specialOpeningQuote, bytes) ← Alpha.decode 8 bytes
  let (percentTrading, bytes) ← Alpha.decode 7 bytes
  let (highLevel, bytes) ← Alpha.decode 8 bytes
  let (lowLevel, bytes) ← Alpha.decode 8 bytes
  let (pe, bytes) ← Alpha.decode 7 bytes
  let (yield, bytes) ← Alpha.decode 5 bytes
  let (markers, bytes) ← Markers.decode bytes
  let (bidPrice, bytes) ← Alpha.decode 7 bytes
  let (askPrice, bytes) ← Alpha.decode 7 bytes
  pure ({ time, indexId, lastLevel, netChange, volume, value, openLevel, settlementValue, specialOpeningQuote, percentTrading, highLevel, lowLevel, pe, yield, markers, bidPrice, askPrice }, bytes)

@[simp] theorem encode_length (message : SAndPTsxOfficialIndexLevelMessage) : (encode message).length = 122 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, Markers.encode_length]

theorem encode_length_pos (message : SAndPTsxOfficialIndexLevelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SAndPTsxOfficialIndexLevelMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Markers.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SAndPTsxOfficialIndexLevelMessage

/-- Beginning Of Index Summary Message: 0 bytes -/
structure BeginningOfIndexSummaryMessage where
  deriving DecidableEq, Repr

namespace BeginningOfIndexSummaryMessage

def encode (_ : BeginningOfIndexSummaryMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (BeginningOfIndexSummaryMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : BeginningOfIndexSummaryMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : BeginningOfIndexSummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end BeginningOfIndexSummaryMessage

/-- Any Message Body, selected by Message Type -/
inductive MessageBody where
  | sAndPTsxOfficialIndexLevelMessage (message : SAndPTsxOfficialIndexLevelMessage) -- "K " 0x4B20
  | beginningOfIndexSummaryMessage (message : BeginningOfIndexSummaryMessage) -- "PA" 0x5041
  deriving DecidableEq, Repr

namespace MessageBody

/-- The Message Type each message is sent under -/
def tag : MessageBody → BitVec 16
  | .sAndPTsxOfficialIndexLevelMessage _ => 19232
  | .beginningOfIndexSummaryMessage _ => 20545

def encode : MessageBody → List UInt8
  | .sAndPTsxOfficialIndexLevelMessage message => SAndPTsxOfficialIndexLevelMessage.encode message
  | .beginningOfIndexSummaryMessage message => BeginningOfIndexSummaryMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : MessageBody) : (encode message).length ≤ 122 := by
  cases message with
  | sAndPTsxOfficialIndexLevelMessage inner =>
    simp only [encode, SAndPTsxOfficialIndexLevelMessage.encode_length]
    omega
  | beginningOfIndexSummaryMessage inner =>
    simp only [encode, BeginningOfIndexSummaryMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (MessageBody × List UInt8) :=
  if tag = 19232 then (SAndPTsxOfficialIndexLevelMessage.decode bytes).map fun (message, rest) => (.sAndPTsxOfficialIndexLevelMessage message, rest)
  else if tag = 20545 then (BeginningOfIndexSummaryMessage.decode bytes).map fun (message, rest) => (.beginningOfIndexSummaryMessage message, rest)
  else none

@[simp] theorem decode_encode (message : MessageBody) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end MessageBody

/-- Packet -/
structure Packet where
  qrtmdStx : BitVec 8
  messageLength : Alpha 4
  sequenceNumber : Alpha 9
  serviceIdentifier : Alpha 3
  retransmissionIdentifier : RetransmissionIdentifier
  continuationIdentifier : ContinuationIdentifier
  exchangeIdentifier : Alpha 2
  messageBody : MessageBody
  qrtmdEtx : BitVec 8
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUInt 1 message.qrtmdStx
    ++ (Alpha.encode message.messageLength
    ++ (Alpha.encode message.sequenceNumber
    ++ (Alpha.encode message.serviceIdentifier
    ++ (RetransmissionIdentifier.encode message.retransmissionIdentifier
    ++ (ContinuationIdentifier.encode message.continuationIdentifier
    ++ (encodeUInt 2 (MessageBody.tag message.messageBody)
    ++ (Alpha.encode message.exchangeIdentifier
    ++ (MessageBody.encode message.messageBody
    ++ (encodeUInt 1 message.qrtmdEtx)))))))))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (qrtmdStx, bytes) ← decodeUInt 1 bytes
  let (messageLength, bytes) ← Alpha.decode 4 bytes
  let (sequenceNumber, bytes) ← Alpha.decode 9 bytes
  let (serviceIdentifier, bytes) ← Alpha.decode 3 bytes
  let (retransmissionIdentifier, bytes) ← RetransmissionIdentifier.decode bytes
  let (continuationIdentifier, bytes) ← ContinuationIdentifier.decode bytes
  let (messageType, bytes) ← decodeUInt 2 bytes
  let (exchangeIdentifier, bytes) ← Alpha.decode 2 bytes
  let (messageBody, bytes) ← MessageBody.decode messageType bytes
  let (qrtmdEtx, bytes) ← decodeUInt 1 bytes
  pure ({ qrtmdStx, messageLength, sequenceNumber, serviceIdentifier, retransmissionIdentifier, continuationIdentifier, exchangeIdentifier, messageBody, qrtmdEtx }, bytes)

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Packet) : (encode message).length ≤ 146 := by
  unfold encode
  cases message.messageBody with
  | sAndPTsxOfficialIndexLevelMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, RetransmissionIdentifier.encode_length, ContinuationIdentifier.encode_length, SAndPTsxOfficialIndexLevelMessage.encode_length]
    omega
  | beginningOfIndexSummaryMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, RetransmissionIdentifier.encode_length, ContinuationIdentifier.encode_length, BeginningOfIndexSummaryMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
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
  rw [List.append_assoc, RetransmissionIdentifier.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ContinuationIdentifier.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MessageBody.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end Packet

end Omi.TmxTsxIndexfeedQrtmdV119
