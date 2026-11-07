import Wire

/-!
# Hong Kong Exchanges and Clearing Orion Market Data Cash Index Refresh v1.46

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.

License: MIT No Attribution
-/

namespace Omi.HkexHkexsecuritiesIndexrefreshOmdV146

/-- Index Source: one byte code -/
def IndexSource.codes : List UInt8 :=
  [0x43, 0x48, 0x58]

inductive IndexSource where
  | csiAndCes -- Csi And Ces
  | hsi -- Hsi
  | hkex -- Hkex
  | unlisted (byte : { byte : UInt8 // byte ∉ IndexSource.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace IndexSource

def toByte : IndexSource → UInt8
  | .csiAndCes => 0x43
  | .hsi => 0x48
  | .hkex => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : IndexSource :=
  if byte = 0x43 then .csiAndCes
  else if byte = 0x48 then .hsi
  else .hkex

def ofByte (byte : UInt8) : IndexSource :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : IndexSource) : ofByte value.toByte = value := by
  cases value with
  | csiAndCes => decide
  | hsi => decide
  | hkex => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : IndexSource) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (IndexSource × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : IndexSource) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : IndexSource) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : IndexSource) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end IndexSource

/-- Index Status: one byte code -/
def IndexStatus.codes : List UInt8 :=
  [0x43, 0x49, 0x4F, 0x50, 0x52, 0x53, 0x54]

inductive IndexStatus where
  | closingValue -- Closing Value
  | indicative -- Indicative
  | openingIndex -- Opening Index
  | lastCloseValuePreviousSession -- Last Close Value Previous Session
  | preliminaryClose -- Preliminary Close
  | stopLossIndex -- Stop Loss Index
  | realTimeIndexValue -- Real Time Index Value
  | unlisted (byte : { byte : UInt8 // byte ∉ IndexStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace IndexStatus

def toByte : IndexStatus → UInt8
  | .closingValue => 0x43
  | .indicative => 0x49
  | .openingIndex => 0x4F
  | .lastCloseValuePreviousSession => 0x50
  | .preliminaryClose => 0x52
  | .stopLossIndex => 0x53
  | .realTimeIndexValue => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : IndexStatus :=
  if byte = 0x43 then .closingValue
  else if byte = 0x49 then .indicative
  else if byte = 0x4F then .openingIndex
  else if byte = 0x50 then .lastCloseValuePreviousSession
  else if byte = 0x52 then .preliminaryClose
  else if byte = 0x53 then .stopLossIndex
  else .realTimeIndexValue

def ofByte (byte : UInt8) : IndexStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : IndexStatus) : ofByte value.toByte = value := by
  cases value with
  | closingValue => decide
  | indicative => decide
  | openingIndex => decide
  | lastCloseValuePreviousSession => decide
  | preliminaryClose => decide
  | stopLossIndex => decide
  | realTimeIndexValue => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : IndexStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (IndexStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : IndexStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : IndexStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : IndexStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end IndexStatus

/-- Exception: one byte code -/
def Exception.codes : List UInt8 :=
  [0x23, 0x20]

inductive Exception where
  | indexWithHsilDefinedExceptionalRuleApplied -- Index With Hsil Defined Exceptional Rule Applied
  | normalIndex -- Normal Index
  | unlisted (byte : { byte : UInt8 // byte ∉ Exception.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Exception

def toByte : Exception → UInt8
  | .indexWithHsilDefinedExceptionalRuleApplied => 0x23
  | .normalIndex => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Exception :=
  if byte = 0x23 then .indexWithHsilDefinedExceptionalRuleApplied
  else .normalIndex

def ofByte (byte : UInt8) : Exception :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Exception) : ofByte value.toByte = value := by
  cases value with
  | indexWithHsilDefinedExceptionalRuleApplied => decide
  | normalIndex => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Exception) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Exception × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Exception) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Exception) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Exception) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Exception

/-- Index Definition Message: 16 bytes -/
structure IndexDefinitionMessage where
  indexCode : Alpha 11
  indexSource : IndexSource
  currencyCode : Alpha 3
  filler1 : Alpha 1
  deriving DecidableEq, Repr

namespace IndexDefinitionMessage

def encode (message : IndexDefinitionMessage) : List UInt8 :=
  Alpha.encode message.indexCode
    ++ (IndexSource.encode message.indexSource
    ++ (Alpha.encode message.currencyCode
    ++ (Alpha.encode message.filler1)))

def decode (bytes : List UInt8) : Option (IndexDefinitionMessage × List UInt8) := do
  let (indexCode, bytes) ← Alpha.decode 11 bytes
  let (indexSource, bytes) ← IndexSource.decode bytes
  let (currencyCode, bytes) ← Alpha.decode 3 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  pure ({ indexCode, indexSource, currencyCode, filler1 }, bytes)

@[simp] theorem encode_length (message : IndexDefinitionMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, IndexSource.encode_length]

theorem encode_length_pos (message : IndexDefinitionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IndexDefinitionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, IndexSource.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end IndexDefinitionMessage

/-- Index Data Message: 108 bytes -/
structure IndexDataMessage where
  indexCode : Alpha 11
  indexStatus : IndexStatus
  indexTime : BitVec 64
  indexValue : BitVec 64
  netChgPrevDay : BitVec 64
  highValue : BitVec 64
  lowValue : BitVec 64
  easValue : BitVec 64
  indexTurnover : BitVec 64
  openingValue : BitVec 64
  closingValue : BitVec 64
  previousSesClose : BitVec 64
  indexVolume : BitVec 64
  netChgPrevDayPct : BitVec 32
  exception : Exception
  filler3 : Alpha 3
  deriving DecidableEq, Repr

namespace IndexDataMessage

def encode (message : IndexDataMessage) : List UInt8 :=
  Alpha.encode message.indexCode
    ++ (IndexStatus.encode message.indexStatus
    ++ (encodeUIntLE 8 message.indexTime
    ++ (encodeUIntLE 8 message.indexValue
    ++ (encodeUIntLE 8 message.netChgPrevDay
    ++ (encodeUIntLE 8 message.highValue
    ++ (encodeUIntLE 8 message.lowValue
    ++ (encodeUIntLE 8 message.easValue
    ++ (encodeUIntLE 8 message.indexTurnover
    ++ (encodeUIntLE 8 message.openingValue
    ++ (encodeUIntLE 8 message.closingValue
    ++ (encodeUIntLE 8 message.previousSesClose
    ++ (encodeUIntLE 8 message.indexVolume
    ++ (encodeUIntLE 4 message.netChgPrevDayPct
    ++ (Exception.encode message.exception
    ++ (Alpha.encode message.filler3)))))))))))))))

def decode (bytes : List UInt8) : Option (IndexDataMessage × List UInt8) := do
  let (indexCode, bytes) ← Alpha.decode 11 bytes
  let (indexStatus, bytes) ← IndexStatus.decode bytes
  let (indexTime, bytes) ← decodeUIntLE 8 bytes
  let (indexValue, bytes) ← decodeUIntLE 8 bytes
  let (netChgPrevDay, bytes) ← decodeUIntLE 8 bytes
  let (highValue, bytes) ← decodeUIntLE 8 bytes
  let (lowValue, bytes) ← decodeUIntLE 8 bytes
  let (easValue, bytes) ← decodeUIntLE 8 bytes
  let (indexTurnover, bytes) ← decodeUIntLE 8 bytes
  let (openingValue, bytes) ← decodeUIntLE 8 bytes
  let (closingValue, bytes) ← decodeUIntLE 8 bytes
  let (previousSesClose, bytes) ← decodeUIntLE 8 bytes
  let (indexVolume, bytes) ← decodeUIntLE 8 bytes
  let (netChgPrevDayPct, bytes) ← decodeUIntLE 4 bytes
  let (exception, bytes) ← Exception.decode bytes
  let (filler3, bytes) ← Alpha.decode 3 bytes
  pure ({ indexCode, indexStatus, indexTime, indexValue, netChgPrevDay, highValue, lowValue, easValue, indexTurnover, openingValue, closingValue, previousSesClose, indexVolume, netChgPrevDayPct, exception, filler3 }, bytes)

@[simp] theorem encode_length (message : IndexDataMessage) : (encode message).length = 108 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, IndexStatus.encode_length, encodeUIntLE_length, Exception.encode_length]

theorem encode_length_pos (message : IndexDataMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IndexDataMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, IndexStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Exception.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end IndexDataMessage

/-- Refresh Complete Message: 4 bytes -/
structure RefreshCompleteMessage where
  lastSeqNum : BitVec 32
  deriving DecidableEq, Repr

namespace RefreshCompleteMessage

def encode (message : RefreshCompleteMessage) : List UInt8 :=
  encodeUIntLE 4 message.lastSeqNum

def decode (bytes : List UInt8) : Option (RefreshCompleteMessage × List UInt8) := do
  let (lastSeqNum, bytes) ← decodeUIntLE 4 bytes
  pure ({ lastSeqNum }, bytes)

@[simp] theorem encode_length (message : RefreshCompleteMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : RefreshCompleteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RefreshCompleteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end RefreshCompleteMessage

/-- Any Payload, selected by Msg Type -/
inductive Payload where
  | indexDefinitionMessage (message : IndexDefinitionMessage) -- 70
  | indexDataMessage (message : IndexDataMessage) -- 71
  | refreshCompleteMessage (message : RefreshCompleteMessage) -- 203
  deriving DecidableEq, Repr

namespace Payload

/-- The Msg Type each message is sent under -/
def tag : Payload → BitVec 16
  | .indexDefinitionMessage _ => 70
  | .indexDataMessage _ => 71
  | .refreshCompleteMessage _ => 203

def encode : Payload → List UInt8
  | .indexDefinitionMessage message => IndexDefinitionMessage.encode message
  | .indexDataMessage message => IndexDataMessage.encode message
  | .refreshCompleteMessage message => RefreshCompleteMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 108 := by
  cases message with
  | indexDefinitionMessage inner =>
    simp only [encode, IndexDefinitionMessage.encode_length]
    omega
  | indexDataMessage inner =>
    simp only [encode, IndexDataMessage.encode_length]
    omega
  | refreshCompleteMessage inner =>
    simp only [encode, RefreshCompleteMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 70 then (IndexDefinitionMessage.decode bytes).map fun (message, rest) => (.indexDefinitionMessage message, rest)
  else if tag = 71 then (IndexDataMessage.decode bytes).map fun (message, rest) => (.indexDataMessage message, rest)
  else if tag = 203 then (RefreshCompleteMessage.decode bytes).map fun (message, rest) => (.refreshCompleteMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message -/
structure Message where
  payload : Payload
  deriving DecidableEq, Repr

namespace Message

def encodeBody (message : Message) : List UInt8 :=
  encodeUIntLE 2 (Payload.tag message.payload)
    ++ (Payload.encode message.payload)

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (msgType, bytes) ← decodeUIntLE 2 bytes
  let (payload, bytes) ← Payload.decode msgType bytes
  pure ({ payload }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 2 < 256 ^ 2 := by
  unfold encodeBody
  cases message.payload with
  | indexDefinitionMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, IndexDefinitionMessage.encode_length]
    omega
  | indexDataMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, IndexDataMessage.encode_length]
    omega
  | refreshCompleteMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, RefreshCompleteMessage.encode_length]
    omega

/-- Size rule: Msg Size counts the bytes after it plus 2, so it is written from the body and checked on decode -/
def encode : Message → List UInt8 :=
  encodeFramedLE 2 2 encodeBody

def decode : List UInt8 → Option (Message × List UInt8) :=
  decodeFramedLE 2 2 decodeBody

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 2 2 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end Message

/-- Packet -/
structure Packet where
  pktSize : BitVec 16
  filler : Alpha 1
  seqNum : BitVec 32
  sendTime : BitVec 64
  message : Bounded 1 Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUIntLE 2 message.pktSize
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.message.val.length)
    ++ (Alpha.encode message.filler
    ++ (encodeUIntLE 4 message.seqNum
    ++ (encodeUIntLE 8 message.sendTime
    ++ (encodeMany Message.encode message.message.val)))))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (pktSize, bytes) ← decodeUIntLE 2 bytes
  let (msgCount, bytes) ← decodeUInt 1 bytes
  let (filler, bytes) ← Alpha.decode 1 bytes
  let (seqNum, bytes) ← decodeUIntLE 4 bytes
  let (sendTime, bytes) ← decodeUIntLE 8 bytes
  let (message_, bytes) ← decodeMany Message.decode msgCount.toNat bytes
  if fits_message : message_.length < 256 ^ 1 then
    pure ({ pktSize, filler, seqNum, sendTime, message := ⟨message_, fits_message⟩ }, bytes)
  else none

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt]
  rfl

end Packet

end Omi.HkexHkexsecuritiesIndexrefreshOmdV146
