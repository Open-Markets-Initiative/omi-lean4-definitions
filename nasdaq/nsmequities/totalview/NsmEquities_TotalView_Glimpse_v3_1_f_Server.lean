import Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) TotalView Itch v3.1.f

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.

Note: Server Frame is closed by soupLf, so its body is read as the bytes ahead of the first 10 and
carries the proof it holds none itself, which is what lets the body be written back with the byte
that closes it

License: MIT No Attribution
-/

namespace Omi.NasdaqNsmequitiesTotalviewGlimpseV31FServer

/-- Event Code: one byte code -/
def EventCode.codes : List UInt8 :=
  [0x4F, 0x53, 0x51, 0x4D, 0x45, 0x43, 0x41, 0x52, 0x42]

inductive EventCode where
  | startOfMessages -- Start Of Messages
  | startOfSystemHours -- Start Of System Hours
  | startOfMarketHours -- Start Of Market Hours
  | endOfMarketHours -- End Of Market Hours
  | endOfSystemHours -- End Of System Hours
  | endOfMessages -- End Of Messages
  | emergencyMarketConditionHalt -- Emergency Market Condition Halt
  | emergencyMarketConditionQuoteOnlyPeriod -- Emergency Market Condition Quote Only Period
  | emergencyMarketConditionResumption -- Emergency Market Condition Resumption
  | unlisted (byte : { byte : UInt8 // byte ∉ EventCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventCode

def toByte : EventCode → UInt8
  | .startOfMessages => 0x4F
  | .startOfSystemHours => 0x53
  | .startOfMarketHours => 0x51
  | .endOfMarketHours => 0x4D
  | .endOfSystemHours => 0x45
  | .endOfMessages => 0x43
  | .emergencyMarketConditionHalt => 0x41
  | .emergencyMarketConditionQuoteOnlyPeriod => 0x52
  | .emergencyMarketConditionResumption => 0x42
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventCode :=
  if byte = 0x4F then .startOfMessages
  else if byte = 0x53 then .startOfSystemHours
  else if byte = 0x51 then .startOfMarketHours
  else if byte = 0x4D then .endOfMarketHours
  else if byte = 0x45 then .endOfSystemHours
  else if byte = 0x43 then .endOfMessages
  else if byte = 0x41 then .emergencyMarketConditionHalt
  else if byte = 0x52 then .emergencyMarketConditionQuoteOnlyPeriod
  else .emergencyMarketConditionResumption

def ofByte (byte : UInt8) : EventCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventCode) : ofByte value.toByte = value := by
  cases value with
  | startOfMessages => decide
  | startOfSystemHours => decide
  | startOfMarketHours => decide
  | endOfMarketHours => decide
  | endOfSystemHours => decide
  | endOfMessages => decide
  | emergencyMarketConditionHalt => decide
  | emergencyMarketConditionQuoteOnlyPeriod => decide
  | emergencyMarketConditionResumption => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : EventCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (EventCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : EventCode) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : EventCode) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : EventCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end EventCode

/-- Buy Sell Indicator: one byte code -/
def BuySellIndicator.codes : List UInt8 :=
  [0x42, 0x53]

inductive BuySellIndicator where
  | buyOrder -- Buy Order
  | sellOrder -- Sell Order
  | unlisted (byte : { byte : UInt8 // byte ∉ BuySellIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BuySellIndicator

def toByte : BuySellIndicator → UInt8
  | .buyOrder => 0x42
  | .sellOrder => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BuySellIndicator :=
  if byte = 0x42 then .buyOrder
  else .sellOrder

def ofByte (byte : UInt8) : BuySellIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BuySellIndicator) : ofByte value.toByte = value := by
  cases value with
  | buyOrder => decide
  | sellOrder => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BuySellIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BuySellIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BuySellIndicator) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : BuySellIndicator) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : BuySellIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BuySellIndicator

/-- Display: one byte code -/
def Display.codes : List UInt8 :=
  [0x59, 0x53]

inductive Display where
  | displayable -- Displayable
  | flashOrder -- Flash Order
  | unlisted (byte : { byte : UInt8 // byte ∉ Display.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Display

def toByte : Display → UInt8
  | .displayable => 0x59
  | .flashOrder => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Display :=
  if byte = 0x59 then .displayable
  else .flashOrder

def ofByte (byte : UInt8) : Display :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Display) : ofByte value.toByte = value := by
  cases value with
  | displayable => decide
  | flashOrder => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Display) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Display × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Display) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Display) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Display) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Display

/-- Debug Packet -/
structure DebugPacket where
  text : List UInt8
  deriving DecidableEq, Repr

namespace DebugPacket

def encode (message : DebugPacket) : List UInt8 :=
  encodeMany Byte.encode message.text

def decode (bytes : List UInt8) : Option DebugPacket := do
  let text ← decodeAll Byte.decode bytes.length bytes
  pure { text }

theorem decode_encode (message : DebugPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany Byte.encode Byte.decode Byte.decode_encode Byte.encode_length_pos message.text _ (encodeMany_length_ge Byte.encode Byte.encode_length_pos message.text), some_bind]
  rfl

end DebugPacket

/-- Login Accepted Packet: 30 bytes -/
structure LoginAcceptedPacket where
  acceptedSession : Alpha 10
  acceptedSequenceNumber : Alpha 20
  deriving DecidableEq, Repr

namespace LoginAcceptedPacket

def encode (message : LoginAcceptedPacket) : List UInt8 :=
  Alpha.encode message.acceptedSession
    ++ (Alpha.encode message.acceptedSequenceNumber)

def decode (bytes : List UInt8) : Option (LoginAcceptedPacket × List UInt8) := do
  let (acceptedSession, bytes) ← Alpha.decode 10 bytes
  let (acceptedSequenceNumber, bytes) ← Alpha.decode 20 bytes
  pure ({ acceptedSession, acceptedSequenceNumber }, bytes)

@[simp] theorem encode_length (message : LoginAcceptedPacket) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : LoginAcceptedPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginAcceptedPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LoginAcceptedPacket) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end LoginAcceptedPacket

/-- Login Rejected Packet: 1 bytes -/
structure LoginRejectedPacket where
  rejectReasonCode : Alpha 1
  deriving DecidableEq, Repr

namespace LoginRejectedPacket

def encode (message : LoginRejectedPacket) : List UInt8 :=
  Alpha.encode message.rejectReasonCode

def decode (bytes : List UInt8) : Option (LoginRejectedPacket × List UInt8) := do
  let (rejectReasonCode, bytes) ← Alpha.decode 1 bytes
  pure ({ rejectReasonCode }, bytes)

@[simp] theorem encode_length (message : LoginRejectedPacket) : (encode message).length = 1 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : LoginRejectedPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginRejectedPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LoginRejectedPacket) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end LoginRejectedPacket

/-- Seconds Message: 5 bytes -/
structure SecondsMessage where
  second : Alpha 5
  deriving DecidableEq, Repr

namespace SecondsMessage

def encode (message : SecondsMessage) : List UInt8 :=
  Alpha.encode message.second

def decode (bytes : List UInt8) : Option (SecondsMessage × List UInt8) := do
  let (second, bytes) ← Alpha.decode 5 bytes
  pure ({ second }, bytes)

@[simp] theorem encode_length (message : SecondsMessage) : (encode message).length = 5 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : SecondsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecondsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end SecondsMessage

/-- Milliseconds Message: 3 bytes -/
structure MillisecondsMessage where
  millisecond : Alpha 3
  deriving DecidableEq, Repr

namespace MillisecondsMessage

def encode (message : MillisecondsMessage) : List UInt8 :=
  Alpha.encode message.millisecond

def decode (bytes : List UInt8) : Option (MillisecondsMessage × List UInt8) := do
  let (millisecond, bytes) ← Alpha.decode 3 bytes
  pure ({ millisecond }, bytes)

@[simp] theorem encode_length (message : MillisecondsMessage) : (encode message).length = 3 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : MillisecondsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MillisecondsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end MillisecondsMessage

/-- System Event Message: 1 bytes -/
structure SystemEventMessage where
  eventCode : EventCode
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  EventCode.encode message.eventCode

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (eventCode, bytes) ← EventCode.decode bytes
  pure ({ eventCode }, bytes)

@[simp] theorem encode_length (message : SystemEventMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [EventCode.encode_length]

theorem encode_length_pos (message : SystemEventMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemEventMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [EventCode.decode_encode, some_bind]
  rfl

end SystemEventMessage

/-- Add Order Message: 36 bytes -/
structure AddOrderMessage where
  orderReferenceNumber : Alpha 12
  buySellIndicator : BuySellIndicator
  shares : Alpha 6
  stock : Alpha 6
  price : Alpha 10
  display : Display
  deriving DecidableEq, Repr

namespace AddOrderMessage

def encode (message : AddOrderMessage) : List UInt8 :=
  Alpha.encode message.orderReferenceNumber
    ++ (BuySellIndicator.encode message.buySellIndicator
    ++ (Alpha.encode message.shares
    ++ (Alpha.encode message.stock
    ++ (Alpha.encode message.price
    ++ (Display.encode message.display)))))

def decode (bytes : List UInt8) : Option (AddOrderMessage × List UInt8) := do
  let (orderReferenceNumber, bytes) ← Alpha.decode 12 bytes
  let (buySellIndicator, bytes) ← BuySellIndicator.decode bytes
  let (shares, bytes) ← Alpha.decode 6 bytes
  let (stock, bytes) ← Alpha.decode 6 bytes
  let (price, bytes) ← Alpha.decode 10 bytes
  let (display, bytes) ← Display.decode bytes
  pure ({ orderReferenceNumber, buySellIndicator, shares, stock, price, display }, bytes)

@[simp] theorem encode_length (message : AddOrderMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, BuySellIndicator.encode_length, Display.encode_length]

theorem encode_length_pos (message : AddOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BuySellIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Display.decode_encode, some_bind]
  rfl

end AddOrderMessage

/-- Add Order Mpid Attribution Message: 39 bytes -/
structure AddOrderMpidAttributionMessage where
  orderReferenceNumber : Alpha 12
  buySellIndicator : BuySellIndicator
  shares : Alpha 6
  stock : Alpha 6
  price : Alpha 10
  attribution : Alpha 4
  deriving DecidableEq, Repr

namespace AddOrderMpidAttributionMessage

def encode (message : AddOrderMpidAttributionMessage) : List UInt8 :=
  Alpha.encode message.orderReferenceNumber
    ++ (BuySellIndicator.encode message.buySellIndicator
    ++ (Alpha.encode message.shares
    ++ (Alpha.encode message.stock
    ++ (Alpha.encode message.price
    ++ (Alpha.encode message.attribution)))))

def decode (bytes : List UInt8) : Option (AddOrderMpidAttributionMessage × List UInt8) := do
  let (orderReferenceNumber, bytes) ← Alpha.decode 12 bytes
  let (buySellIndicator, bytes) ← BuySellIndicator.decode bytes
  let (shares, bytes) ← Alpha.decode 6 bytes
  let (stock, bytes) ← Alpha.decode 6 bytes
  let (price, bytes) ← Alpha.decode 10 bytes
  let (attribution, bytes) ← Alpha.decode 4 bytes
  pure ({ orderReferenceNumber, buySellIndicator, shares, stock, price, attribution }, bytes)

@[simp] theorem encode_length (message : AddOrderMpidAttributionMessage) : (encode message).length = 39 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, BuySellIndicator.encode_length]

theorem encode_length_pos (message : AddOrderMpidAttributionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddOrderMpidAttributionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BuySellIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end AddOrderMpidAttributionMessage

/-- End Of Snapshot Message: 20 bytes -/
structure EndOfSnapshotMessage where
  itchSequenceNumber : Alpha 20
  deriving DecidableEq, Repr

namespace EndOfSnapshotMessage

def encode (message : EndOfSnapshotMessage) : List UInt8 :=
  Alpha.encode message.itchSequenceNumber

def decode (bytes : List UInt8) : Option (EndOfSnapshotMessage × List UInt8) := do
  let (itchSequenceNumber, bytes) ← Alpha.decode 20 bytes
  pure ({ itchSequenceNumber }, bytes)

@[simp] theorem encode_length (message : EndOfSnapshotMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : EndOfSnapshotMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EndOfSnapshotMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end EndOfSnapshotMessage

/-- Any Sequenced Message, selected by Message Type -/
inductive SequencedMessage where
  | secondsMessage (message : SecondsMessage) -- "T" 0x54
  | millisecondsMessage (message : MillisecondsMessage) -- "M" 0x4D
  | systemEventMessage (message : SystemEventMessage) -- "S" 0x53
  | addOrderMessage (message : AddOrderMessage) -- "A" 0x41
  | addOrderMpidAttributionMessage (message : AddOrderMpidAttributionMessage) -- "F" 0x46
  | endOfSnapshotMessage (message : EndOfSnapshotMessage) -- "G" 0x47
  deriving DecidableEq, Repr

namespace SequencedMessage

/-- The Message Type each message is sent under -/
def tag : SequencedMessage → BitVec 8
  | .secondsMessage _ => 84
  | .millisecondsMessage _ => 77
  | .systemEventMessage _ => 83
  | .addOrderMessage _ => 65
  | .addOrderMpidAttributionMessage _ => 70
  | .endOfSnapshotMessage _ => 71

def encode : SequencedMessage → List UInt8
  | .secondsMessage message => SecondsMessage.encode message
  | .millisecondsMessage message => MillisecondsMessage.encode message
  | .systemEventMessage message => SystemEventMessage.encode message
  | .addOrderMessage message => AddOrderMessage.encode message
  | .addOrderMpidAttributionMessage message => AddOrderMpidAttributionMessage.encode message
  | .endOfSnapshotMessage message => EndOfSnapshotMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : SequencedMessage) : (encode message).length ≤ 39 := by
  cases message with
  | secondsMessage inner =>
    simp only [encode, SecondsMessage.encode_length]
    omega
  | millisecondsMessage inner =>
    simp only [encode, MillisecondsMessage.encode_length]
    omega
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega
  | addOrderMessage inner =>
    simp only [encode, AddOrderMessage.encode_length]
    omega
  | addOrderMpidAttributionMessage inner =>
    simp only [encode, AddOrderMpidAttributionMessage.encode_length]
    omega
  | endOfSnapshotMessage inner =>
    simp only [encode, EndOfSnapshotMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (SequencedMessage × List UInt8) :=
  if tag = 84 then (SecondsMessage.decode bytes).map fun (message, rest) => (.secondsMessage message, rest)
  else if tag = 77 then (MillisecondsMessage.decode bytes).map fun (message, rest) => (.millisecondsMessage message, rest)
  else if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 65 then (AddOrderMessage.decode bytes).map fun (message, rest) => (.addOrderMessage message, rest)
  else if tag = 70 then (AddOrderMpidAttributionMessage.decode bytes).map fun (message, rest) => (.addOrderMpidAttributionMessage message, rest)
  else if tag = 71 then (EndOfSnapshotMessage.decode bytes).map fun (message, rest) => (.endOfSnapshotMessage message, rest)
  else none

@[simp] theorem decode_encode (message : SequencedMessage) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end SequencedMessage

/-- Sequenced Data Packet -/
structure SequencedDataPacket where
  sequencedMessage : SequencedMessage
  deriving DecidableEq, Repr

namespace SequencedDataPacket

def encode (message : SequencedDataPacket) : List UInt8 :=
  encodeUInt 1 (SequencedMessage.tag message.sequencedMessage)
    ++ (SequencedMessage.encode message.sequencedMessage)

def decode (bytes : List UInt8) : Option (SequencedDataPacket × List UInt8) := do
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (sequencedMessage, bytes) ← SequencedMessage.decode messageType bytes
  pure ({ sequencedMessage }, bytes)

theorem encode_length_pos (message : SequencedDataPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SequencedDataPacket) : (encode message).length ≤ 40 := by
  unfold encode
  cases message.sequencedMessage with
  | secondsMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, SecondsMessage.encode_length]
    omega
  | millisecondsMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, MillisecondsMessage.encode_length]
    omega
  | systemEventMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, SystemEventMessage.encode_length]
    omega
  | addOrderMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, AddOrderMessage.encode_length]
    omega
  | addOrderMpidAttributionMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, AddOrderMpidAttributionMessage.encode_length]
    omega
  | endOfSnapshotMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, EndOfSnapshotMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : SequencedDataPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [SequencedMessage.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SequencedDataPacket) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SequencedDataPacket

/-- Any Server Payload, selected by Server Packet Type -/
inductive ServerPayload where
  | debugPacket (message : DebugPacket) -- "+" 0x2B
  | loginAcceptedPacket (message : LoginAcceptedPacket) -- "A" 0x41
  | loginRejectedPacket (message : LoginRejectedPacket) -- "J" 0x4A
  | sequencedDataPacket (message : SequencedDataPacket) -- "S" 0x53
  deriving DecidableEq, Repr

namespace ServerPayload

/-- The Server Packet Type each message is sent under -/
def tag : ServerPayload → BitVec 8
  | .debugPacket _ => 43
  | .loginAcceptedPacket _ => 65
  | .loginRejectedPacket _ => 74
  | .sequencedDataPacket _ => 83

def encode : ServerPayload → List UInt8
  | .debugPacket message => DebugPacket.encode message
  | .loginAcceptedPacket message => LoginAcceptedPacket.encode message
  | .loginRejectedPacket message => LoginRejectedPacket.encode message
  | .sequencedDataPacket message => SequencedDataPacket.encode message

/-- Decoded from the whole of the frame: a message that reads to its end takes it all, any other must leave nothing -/
def decode (tag : BitVec 8) (bytes : List UInt8) : Option ServerPayload :=
  if tag = 43 then (DebugPacket.decode bytes).map fun message => .debugPacket message
  else if tag = 65 then (LoginAcceptedPacket.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.loginAcceptedPacket message) else none
  else if tag = 74 then (LoginRejectedPacket.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.loginRejectedPacket message) else none
  else if tag = 83 then (SequencedDataPacket.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.sequencedDataPacket message) else none
  else none

theorem decode_encode (message : ServerPayload) :
    decode (tag message) (encode message) = some message := by
  cases message with
  | debugPacket message => simp [decode, encode, tag, DebugPacket.decode_encode]
  | loginAcceptedPacket message => simp [decode, encode, tag, LoginAcceptedPacket.decode_encode_nil]
  | loginRejectedPacket message => simp [decode, encode, tag, LoginRejectedPacket.decode_encode_nil]
  | sequencedDataPacket message => simp [decode, encode, tag, SequencedDataPacket.decode_encode_nil]

end ServerPayload

/-- Server Frame -/
structure ServerFrameBody where
  serverPayload : ServerPayload
  deriving DecidableEq, Repr

namespace ServerFrameBody

def encodeBody (message : ServerFrameBody) : List UInt8 :=
  encodeUInt 1 (ServerPayload.tag message.serverPayload)
    ++ (ServerPayload.encode message.serverPayload)

def decodeBody (bytes : List UInt8) : Option ServerFrameBody := do
  let (serverPacketType, bytes) ← decodeUInt 1 bytes
  let serverPayload ← ServerPayload.decode serverPacketType bytes
  pure { serverPayload }

theorem decodeBody_encodeBody (message : ServerFrameBody) : decodeBody (encodeBody message) = some message := by
  unfold decodeBody encodeBody
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ServerPayload.decode_encode, some_bind]
  rfl

end ServerFrameBody

/-- Server Frame: the body, which the record carries with the proof it holds no soupLf -/
abbrev ServerFrame := Closed ServerFrameBody.encodeBody 10

namespace ServerFrame

def encode (message : ServerFrame) : List UInt8 :=
  encodeClosed 10 ServerFrameBody.encodeBody message.val

def decode : List UInt8 → Option (ServerFrame × List UInt8) :=
  decodeClosing 10 ServerFrameBody.encodeBody ServerFrameBody.decodeBody

@[simp] theorem decode_encode (message : ServerFrame) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeClosing_encodeClosed 10 ServerFrameBody.encodeBody ServerFrameBody.decodeBody message (ServerFrameBody.decodeBody_encodeBody message.val) rest

/-- Every encoding is at least the byte that closes it -/
theorem encode_length_pos (message : ServerFrame) : (encode message).length > 0 := by
  unfold encode
  exact encodeClosed_length_pos 10 ServerFrameBody.encodeBody message.val

end ServerFrame

/-- Server Packet -/
structure ServerPacket where
  serverFrame : List ServerFrame
  deriving DecidableEq, Repr

namespace ServerPacket

def encode (message : ServerPacket) : List UInt8 :=
  encodeMany ServerFrame.encode message.serverFrame

def decode (bytes : List UInt8) : Option ServerPacket := do
  let serverFrame ← decodeAll ServerFrame.decode bytes.length bytes
  pure { serverFrame }

theorem decode_encode (message : ServerPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany ServerFrame.encode ServerFrame.decode ServerFrame.decode_encode ServerFrame.encode_length_pos message.serverFrame _ (encodeMany_length_ge ServerFrame.encode ServerFrame.encode_length_pos message.serverFrame), some_bind]
  rfl

end ServerPacket

end Omi.NasdaqNsmequitiesTotalviewGlimpseV31FServer
