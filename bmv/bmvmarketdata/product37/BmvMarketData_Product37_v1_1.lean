import Wire

/-!
# Bolsa Mexicana de Valores Bmv Market Data Product 37 v1.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.

License: MIT No Attribution
-/

namespace Omi.BmvBmvmarketdataProduct37IntraV11

/-- Direction: one byte code -/
def Direction.codes : List UInt8 :=
  [0x43, 0x56]

inductive Direction where
  | bid -- Bid
  | ask -- Ask
  | unlisted (byte : { byte : UInt8 // byte ∉ Direction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Direction

def toByte : Direction → UInt8
  | .bid => 0x43
  | .ask => 0x56
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Direction :=
  if byte = 0x43 then .bid
  else .ask

def ofByte (byte : UInt8) : Direction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Direction) : ofByte value.toByte = value := by
  cases value with
  | bid => decide
  | ask => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Direction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Direction × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Direction) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Direction) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Direction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Direction

/-- Operation Type: one byte code -/
def OperationType.codes : List UInt8 :=
  [0x48, 0x44, 0x50, 0x28, 0x29]

inductive OperationType where
  | atClose -- At Close
  | afterClose -- After Close
  | averagePrice -- Average Price
  | inavAtClose -- Inav At Close
  | inavAfterClose -- Inav After Close
  | unlisted (byte : { byte : UInt8 // byte ∉ OperationType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OperationType

def toByte : OperationType → UInt8
  | .atClose => 0x48
  | .afterClose => 0x44
  | .averagePrice => 0x50
  | .inavAtClose => 0x28
  | .inavAfterClose => 0x29
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OperationType :=
  if byte = 0x48 then .atClose
  else if byte = 0x44 then .afterClose
  else if byte = 0x50 then .averagePrice
  else if byte = 0x28 then .inavAtClose
  else .inavAfterClose

def ofByte (byte : UInt8) : OperationType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OperationType) : ofByte value.toByte = value := by
  cases value with
  | atClose => decide
  | afterClose => decide
  | averagePrice => decide
  | inavAtClose => decide
  | inavAfterClose => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OperationType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OperationType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OperationType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OperationType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OperationType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OperationType

/-- Order Adition Message: 35 bytes -/
structure OrderAditionMessage where
  idInstrument : BitVec 32
  dateAndHour : BitVec 64
  folio : BitVec 32
  direction : Direction
  volume : BitVec 32
  price : BitVec 64
  participant : Alpha 5
  operationType : OperationType
  deriving DecidableEq, Repr

namespace OrderAditionMessage

def encode (message : OrderAditionMessage) : List UInt8 :=
  encodeUInt 4 message.idInstrument
    ++ (encodeUInt 8 message.dateAndHour
    ++ (encodeUInt 4 message.folio
    ++ (Direction.encode message.direction
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 8 message.price
    ++ (Alpha.encode message.participant
    ++ (OperationType.encode message.operationType)))))))

def decode (bytes : List UInt8) : Option (OrderAditionMessage × List UInt8) := do
  let (idInstrument, bytes) ← decodeUInt 4 bytes
  let (dateAndHour, bytes) ← decodeUInt 8 bytes
  let (folio, bytes) ← decodeUInt 4 bytes
  let (direction, bytes) ← Direction.decode bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (participant, bytes) ← Alpha.decode 5 bytes
  let (operationType, bytes) ← OperationType.decode bytes
  pure ({ idInstrument, dateAndHour, folio, direction, volume, price, participant, operationType }, bytes)

@[simp] theorem encode_length (message : OrderAditionMessage) : (encode message).length = 35 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Direction.encode_length, Alpha.encode_length, OperationType.encode_length]

theorem encode_length_pos (message : OrderAditionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderAditionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Direction.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [OperationType.decode_encode, some_bind]
  rfl

end OrderAditionMessage

/-- Execution Of Orders Message: 33 bytes -/
structure ExecutionOfOrdersMessage where
  idInstrument : BitVec 32
  date : BitVec 64
  folio : BitVec 32
  volume : BitVec 32
  tradeNumber : BitVec 32
  executionPrice : BitVec 64
  operationType : OperationType
  deriving DecidableEq, Repr

namespace ExecutionOfOrdersMessage

def encode (message : ExecutionOfOrdersMessage) : List UInt8 :=
  encodeUInt 4 message.idInstrument
    ++ (encodeUInt 8 message.date
    ++ (encodeUInt 4 message.folio
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 4 message.tradeNumber
    ++ (encodeUInt 8 message.executionPrice
    ++ (OperationType.encode message.operationType))))))

def decode (bytes : List UInt8) : Option (ExecutionOfOrdersMessage × List UInt8) := do
  let (idInstrument, bytes) ← decodeUInt 4 bytes
  let (date, bytes) ← decodeUInt 8 bytes
  let (folio, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (tradeNumber, bytes) ← decodeUInt 4 bytes
  let (executionPrice, bytes) ← decodeUInt 8 bytes
  let (operationType, bytes) ← OperationType.decode bytes
  pure ({ idInstrument, date, folio, volume, tradeNumber, executionPrice, operationType }, bytes)

@[simp] theorem encode_length (message : ExecutionOfOrdersMessage) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, OperationType.encode_length]

theorem encode_length_pos (message : ExecutionOfOrdersMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExecutionOfOrdersMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [OperationType.decode_encode, some_bind]
  rfl

end ExecutionOfOrdersMessage

/-- Order Cancellation Message: 17 bytes -/
structure OrderCancellationMessage where
  idInstrument : BitVec 32
  date : BitVec 64
  folio : BitVec 32
  operationType : OperationType
  deriving DecidableEq, Repr

namespace OrderCancellationMessage

def encode (message : OrderCancellationMessage) : List UInt8 :=
  encodeUInt 4 message.idInstrument
    ++ (encodeUInt 8 message.date
    ++ (encodeUInt 4 message.folio
    ++ (OperationType.encode message.operationType)))

def decode (bytes : List UInt8) : Option (OrderCancellationMessage × List UInt8) := do
  let (idInstrument, bytes) ← decodeUInt 4 bytes
  let (date, bytes) ← decodeUInt 8 bytes
  let (folio, bytes) ← decodeUInt 4 bytes
  let (operationType, bytes) ← OperationType.decode bytes
  pure ({ idInstrument, date, folio, operationType }, bytes)

@[simp] theorem encode_length (message : OrderCancellationMessage) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, OperationType.encode_length]

theorem encode_length_pos (message : OrderCancellationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancellationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [OperationType.decode_encode, some_bind]
  rfl

end OrderCancellationMessage

/-- Order Change Message: 42 bytes -/
structure OrderChangeMessage where
  idInstrument : BitVec 32
  originalDate : BitVec 64
  originalFolio : BitVec 32
  newDate : BitVec 64
  newFolio : BitVec 32
  direction : Direction
  volume : BitVec 32
  price : BitVec 64
  operationType : OperationType
  deriving DecidableEq, Repr

namespace OrderChangeMessage

def encode (message : OrderChangeMessage) : List UInt8 :=
  encodeUInt 4 message.idInstrument
    ++ (encodeUInt 8 message.originalDate
    ++ (encodeUInt 4 message.originalFolio
    ++ (encodeUInt 8 message.newDate
    ++ (encodeUInt 4 message.newFolio
    ++ (Direction.encode message.direction
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 8 message.price
    ++ (OperationType.encode message.operationType))))))))

def decode (bytes : List UInt8) : Option (OrderChangeMessage × List UInt8) := do
  let (idInstrument, bytes) ← decodeUInt 4 bytes
  let (originalDate, bytes) ← decodeUInt 8 bytes
  let (originalFolio, bytes) ← decodeUInt 4 bytes
  let (newDate, bytes) ← decodeUInt 8 bytes
  let (newFolio, bytes) ← decodeUInt 4 bytes
  let (direction, bytes) ← Direction.decode bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (operationType, bytes) ← OperationType.decode bytes
  pure ({ idInstrument, originalDate, originalFolio, newDate, newFolio, direction, volume, price, operationType }, bytes)

@[simp] theorem encode_length (message : OrderChangeMessage) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Direction.encode_length, OperationType.encode_length]

theorem encode_length_pos (message : OrderChangeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderChangeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Direction.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [OperationType.decode_encode, some_bind]
  rfl

end OrderChangeMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | orderAditionMessage (message : OrderAditionMessage) -- 16707
  | executionOfOrdersMessage (message : ExecutionOfOrdersMessage) -- 17219
  | orderCancellationMessage (message : OrderCancellationMessage) -- 17475
  | orderChangeMessage (message : OrderChangeMessage) -- 17987
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 16
  | .orderAditionMessage _ => 16707
  | .executionOfOrdersMessage _ => 17219
  | .orderCancellationMessage _ => 17475
  | .orderChangeMessage _ => 17987

def encode : Payload → List UInt8
  | .orderAditionMessage message => OrderAditionMessage.encode message
  | .executionOfOrdersMessage message => ExecutionOfOrdersMessage.encode message
  | .orderCancellationMessage message => OrderCancellationMessage.encode message
  | .orderChangeMessage message => OrderChangeMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 42 := by
  cases message with
  | orderAditionMessage inner =>
    simp only [encode, OrderAditionMessage.encode_length]
    omega
  | executionOfOrdersMessage inner =>
    simp only [encode, ExecutionOfOrdersMessage.encode_length]
    omega
  | orderCancellationMessage inner =>
    simp only [encode, OrderCancellationMessage.encode_length]
    omega
  | orderChangeMessage inner =>
    simp only [encode, OrderChangeMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 16707 then (OrderAditionMessage.decode bytes).map fun (message, rest) => (.orderAditionMessage message, rest)
  else if tag = 17219 then (ExecutionOfOrdersMessage.decode bytes).map fun (message, rest) => (.executionOfOrdersMessage message, rest)
  else if tag = 17475 then (OrderCancellationMessage.decode bytes).map fun (message, rest) => (.orderCancellationMessage message, rest)
  else if tag = 17987 then (OrderChangeMessage.decode bytes).map fun (message, rest) => (.orderChangeMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message Block -/
structure MessageBlock where
  payload : Payload
  deriving DecidableEq, Repr

namespace MessageBlock

def encodeBody (message : MessageBlock) : List UInt8 :=
  encodeUInt 2 (Payload.tag message.payload)
    ++ (Payload.encode message.payload)

def decodeBody (bytes : List UInt8) : Option (MessageBlock × List UInt8) := do
  let (messageType, bytes) ← decodeUInt 2 bytes
  let (payload, bytes) ← Payload.decode messageType bytes
  pure ({ payload }, bytes)

theorem decodeBody_encodeBody (message : MessageBlock) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : MessageBlock) : (encodeBody message).length + 0 < 256 ^ 2 := by
  unfold encodeBody
  cases message.payload with
  | orderAditionMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderAditionMessage.encode_length]
    omega
  | executionOfOrdersMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ExecutionOfOrdersMessage.encode_length]
    omega
  | orderCancellationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderCancellationMessage.encode_length]
    omega
  | orderChangeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderChangeMessage.encode_length]
    omega

/-- Size rule: Message Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : MessageBlock → List UInt8 :=
  encodeFramed 2 0 encodeBody

def decode : List UInt8 → Option (MessageBlock × List UInt8) :=
  decodeFramed 2 0 decodeBody

@[simp] theorem decode_encode (message : MessageBlock) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 2 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : MessageBlock) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end MessageBlock

/-- Packet -/
structure Packet where
  length : BitVec 16
  marketDataGroup : BitVec 8
  session : BitVec 8
  sequenceNumber : BitVec 32
  datetime : BitVec 64
  messageBlock : Bounded 1 MessageBlock
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUInt 2 message.length
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.messageBlock.val.length)
    ++ (encodeUInt 1 message.marketDataGroup
    ++ (encodeUInt 1 message.session
    ++ (encodeUInt 4 message.sequenceNumber
    ++ (encodeUInt 8 message.datetime
    ++ (encodeMany MessageBlock.encode message.messageBlock.val))))))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (length, bytes) ← decodeUInt 2 bytes
  let (totalMessages, bytes) ← decodeUInt 1 bytes
  let (marketDataGroup, bytes) ← decodeUInt 1 bytes
  let (session, bytes) ← decodeUInt 1 bytes
  let (sequenceNumber, bytes) ← decodeUInt 4 bytes
  let (datetime, bytes) ← decodeUInt 8 bytes
  let (messageBlock_, bytes) ← decodeMany MessageBlock.decode totalMessages.toNat bytes
  if fits_messageBlock : messageBlock_.length < 256 ^ 1 then
    pure ({ length, marketDataGroup, session, sequenceNumber, datetime, messageBlock := ⟨messageBlock_, fits_messageBlock⟩ }, bytes)
  else none

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 MessageBlock.encode MessageBlock.decode MessageBlock.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.messageBlock.length_lt]
  rfl

end Packet

end Omi.BmvBmvmarketdataProduct37IntraV11
