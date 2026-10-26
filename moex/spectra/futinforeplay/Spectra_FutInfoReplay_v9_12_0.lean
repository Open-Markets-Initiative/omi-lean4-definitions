import Wire

/-!
# Moscow Exchange SIMBA Spectra Futures Instrument Replay v9.12.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.MoexSpectraFutinforeplaySimbaV9120

/-- Security Alt Id Source: one byte code -/
def SecurityAltIdSource.codes : List UInt8 :=
  [0x34, 0x38]

inductive SecurityAltIdSource where
  | isin -- Isin
  | exchangeSymbol -- Exchange Symbol
  | unlisted (byte : { byte : UInt8 // byte ∉ SecurityAltIdSource.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SecurityAltIdSource

def toByte : SecurityAltIdSource → UInt8
  | .isin => 0x34
  | .exchangeSymbol => 0x38
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SecurityAltIdSource :=
  if byte = 0x34 then .isin
  else .exchangeSymbol

def ofByte (byte : UInt8) : SecurityAltIdSource :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SecurityAltIdSource) : ofByte value.toByte = value := by
  cases value with
  | isin => decide
  | exchangeSymbol => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SecurityAltIdSource) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SecurityAltIdSource × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SecurityAltIdSource) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SecurityAltIdSource) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SecurityAltIdSource) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SecurityAltIdSource

/-- Market Segment Id: one byte code -/
def MarketSegmentId.codes : List UInt8 :=
  [0x44]

inductive MarketSegmentId where
  | derivatives -- Derivatives
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketSegmentId.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketSegmentId

def toByte : MarketSegmentId → UInt8
  | .derivatives => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : MarketSegmentId :=
  .derivatives

def ofByte (byte : UInt8) : MarketSegmentId :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketSegmentId) : ofByte value.toByte = value := by
  cases value with
  | derivatives => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarketSegmentId) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketSegmentId × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketSegmentId) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : MarketSegmentId) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : MarketSegmentId) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarketSegmentId

/-- Market Data Packet Header: 16 bytes -/
structure MarketDataPacketHeader where
  msgSeqNum : BitVec 32
  msgSize : BitVec 16
  msgFlags : BitVec 16
  sendingTime : BitVec 64
  deriving DecidableEq, Repr

namespace MarketDataPacketHeader

def encode (message : MarketDataPacketHeader) : List UInt8 :=
  encodeUIntLE 4 message.msgSeqNum
    ++ (encodeUIntLE 2 message.msgSize
    ++ (encodeUIntLE 2 message.msgFlags
    ++ (encodeUIntLE 8 message.sendingTime)))

def decode (bytes : List UInt8) : Option (MarketDataPacketHeader × List UInt8) := do
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (msgSize, bytes) ← decodeUIntLE 2 bytes
  let (msgFlags, bytes) ← decodeUIntLE 2 bytes
  let (sendingTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ msgSeqNum, msgSize, msgFlags, sendingTime }, bytes)

@[simp] theorem encode_length (message : MarketDataPacketHeader) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : MarketDataPacketHeader) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketDataPacketHeader) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end MarketDataPacketHeader

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

/-- Sequence Reset Message: 4 bytes -/
structure SequenceResetMessage where
  newSeqNo : BitVec 32
  deriving DecidableEq, Repr

namespace SequenceResetMessage

def encode (message : SequenceResetMessage) : List UInt8 :=
  encodeUIntLE 4 message.newSeqNo

def decode (bytes : List UInt8) : Option (SequenceResetMessage × List UInt8) := do
  let (newSeqNo, bytes) ← decodeUIntLE 4 bytes
  pure ({ newSeqNo }, bytes)

@[simp] theorem encode_length (message : SequenceResetMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : SequenceResetMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SequenceResetMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SequenceResetMessage

/-- Security Definition Message No M D Feed Types Group: 33 bytes -/
structure SecurityDefinitionMessageNoMDFeedTypesGroup where
  mdFeedType : Alpha 25
  marketDepth : BitVec 32
  mdBookType : BitVec 32
  deriving DecidableEq, Repr

namespace SecurityDefinitionMessageNoMDFeedTypesGroup

def encode (message : SecurityDefinitionMessageNoMDFeedTypesGroup) : List UInt8 :=
  Alpha.encode message.mdFeedType
    ++ (encodeUIntLE 4 message.marketDepth
    ++ (encodeUIntLE 4 message.mdBookType))

def decode (bytes : List UInt8) : Option (SecurityDefinitionMessageNoMDFeedTypesGroup × List UInt8) := do
  let (mdFeedType, bytes) ← Alpha.decode 25 bytes
  let (marketDepth, bytes) ← decodeUIntLE 4 bytes
  let (mdBookType, bytes) ← decodeUIntLE 4 bytes
  pure ({ mdFeedType, marketDepth, mdBookType }, bytes)

@[simp] theorem encode_length (message : SecurityDefinitionMessageNoMDFeedTypesGroup) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : SecurityDefinitionMessageNoMDFeedTypesGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityDefinitionMessageNoMDFeedTypesGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SecurityDefinitionMessageNoMDFeedTypesGroup

/-- Security Definition Message No M D Feed Types Groups -/
structure SecurityDefinitionMessageNoMDFeedTypesGroups where
  blockLength : BitVec 16
  securityDefinitionMessageNoMDFeedTypesGroup : Bounded 1 SecurityDefinitionMessageNoMDFeedTypesGroup
  deriving DecidableEq, Repr

namespace SecurityDefinitionMessageNoMDFeedTypesGroups

def encode (message : SecurityDefinitionMessageNoMDFeedTypesGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.securityDefinitionMessageNoMDFeedTypesGroup.val.length)
    ++ (encodeMany SecurityDefinitionMessageNoMDFeedTypesGroup.encode message.securityDefinitionMessageNoMDFeedTypesGroup.val))

def decode (bytes : List UInt8) : Option (SecurityDefinitionMessageNoMDFeedTypesGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroupUint8, bytes) ← decodeUInt 1 bytes
  let (securityDefinitionMessageNoMDFeedTypesGroup_, bytes) ← decodeMany SecurityDefinitionMessageNoMDFeedTypesGroup.decode numInGroupUint8.toNat bytes
  if fits_securityDefinitionMessageNoMDFeedTypesGroup : securityDefinitionMessageNoMDFeedTypesGroup_.length < 256 ^ 1 then
    pure ({ blockLength, securityDefinitionMessageNoMDFeedTypesGroup := ⟨securityDefinitionMessageNoMDFeedTypesGroup_, fits_securityDefinitionMessageNoMDFeedTypesGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : SecurityDefinitionMessageNoMDFeedTypesGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SecurityDefinitionMessageNoMDFeedTypesGroups) : (encode message).length ≤ 8418 := by
  have bound_securityDefinitionMessageNoMDFeedTypesGroup := message.securityDefinitionMessageNoMDFeedTypesGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const SecurityDefinitionMessageNoMDFeedTypesGroup.encode 33 SecurityDefinitionMessageNoMDFeedTypesGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : SecurityDefinitionMessageNoMDFeedTypesGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 SecurityDefinitionMessageNoMDFeedTypesGroup.encode SecurityDefinitionMessageNoMDFeedTypesGroup.decode SecurityDefinitionMessageNoMDFeedTypesGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.securityDefinitionMessageNoMDFeedTypesGroup.length_lt]
  rfl

end SecurityDefinitionMessageNoMDFeedTypesGroups

/-- Security Definition Message No Underlyings Group: 37 bytes -/
structure SecurityDefinitionMessageNoUnderlyingsGroup where
  underlyingSymbol : Alpha 25
  underlyingBoard : Alpha 4
  underlyingSecurityId : BitVec 32
  underlyingFutureId : BitVec 32
  deriving DecidableEq, Repr

namespace SecurityDefinitionMessageNoUnderlyingsGroup

def encode (message : SecurityDefinitionMessageNoUnderlyingsGroup) : List UInt8 :=
  Alpha.encode message.underlyingSymbol
    ++ (Alpha.encode message.underlyingBoard
    ++ (encodeUIntLE 4 message.underlyingSecurityId
    ++ (encodeUIntLE 4 message.underlyingFutureId)))

def decode (bytes : List UInt8) : Option (SecurityDefinitionMessageNoUnderlyingsGroup × List UInt8) := do
  let (underlyingSymbol, bytes) ← Alpha.decode 25 bytes
  let (underlyingBoard, bytes) ← Alpha.decode 4 bytes
  let (underlyingSecurityId, bytes) ← decodeUIntLE 4 bytes
  let (underlyingFutureId, bytes) ← decodeUIntLE 4 bytes
  pure ({ underlyingSymbol, underlyingBoard, underlyingSecurityId, underlyingFutureId }, bytes)

@[simp] theorem encode_length (message : SecurityDefinitionMessageNoUnderlyingsGroup) : (encode message).length = 37 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : SecurityDefinitionMessageNoUnderlyingsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityDefinitionMessageNoUnderlyingsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SecurityDefinitionMessageNoUnderlyingsGroup

/-- Security Definition Message No Underlyings Groups -/
structure SecurityDefinitionMessageNoUnderlyingsGroups where
  blockLength : BitVec 16
  securityDefinitionMessageNoUnderlyingsGroup : Bounded 1 SecurityDefinitionMessageNoUnderlyingsGroup
  deriving DecidableEq, Repr

namespace SecurityDefinitionMessageNoUnderlyingsGroups

def encode (message : SecurityDefinitionMessageNoUnderlyingsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.securityDefinitionMessageNoUnderlyingsGroup.val.length)
    ++ (encodeMany SecurityDefinitionMessageNoUnderlyingsGroup.encode message.securityDefinitionMessageNoUnderlyingsGroup.val))

def decode (bytes : List UInt8) : Option (SecurityDefinitionMessageNoUnderlyingsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroupUint8, bytes) ← decodeUInt 1 bytes
  let (securityDefinitionMessageNoUnderlyingsGroup_, bytes) ← decodeMany SecurityDefinitionMessageNoUnderlyingsGroup.decode numInGroupUint8.toNat bytes
  if fits_securityDefinitionMessageNoUnderlyingsGroup : securityDefinitionMessageNoUnderlyingsGroup_.length < 256 ^ 1 then
    pure ({ blockLength, securityDefinitionMessageNoUnderlyingsGroup := ⟨securityDefinitionMessageNoUnderlyingsGroup_, fits_securityDefinitionMessageNoUnderlyingsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : SecurityDefinitionMessageNoUnderlyingsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SecurityDefinitionMessageNoUnderlyingsGroups) : (encode message).length ≤ 9438 := by
  have bound_securityDefinitionMessageNoUnderlyingsGroup := message.securityDefinitionMessageNoUnderlyingsGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const SecurityDefinitionMessageNoUnderlyingsGroup.encode 37 SecurityDefinitionMessageNoUnderlyingsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : SecurityDefinitionMessageNoUnderlyingsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 SecurityDefinitionMessageNoUnderlyingsGroup.encode SecurityDefinitionMessageNoUnderlyingsGroup.decode SecurityDefinitionMessageNoUnderlyingsGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.securityDefinitionMessageNoUnderlyingsGroup.length_lt]
  rfl

end SecurityDefinitionMessageNoUnderlyingsGroups

/-- Security Definition Message No Legs Group: 33 bytes -/
structure SecurityDefinitionMessageNoLegsGroup where
  legSymbol : Alpha 25
  legSecurityId : BitVec 32
  legRatioQty : BitVec 32
  deriving DecidableEq, Repr

namespace SecurityDefinitionMessageNoLegsGroup

def encode (message : SecurityDefinitionMessageNoLegsGroup) : List UInt8 :=
  Alpha.encode message.legSymbol
    ++ (encodeUIntLE 4 message.legSecurityId
    ++ (encodeUIntLE 4 message.legRatioQty))

def decode (bytes : List UInt8) : Option (SecurityDefinitionMessageNoLegsGroup × List UInt8) := do
  let (legSymbol, bytes) ← Alpha.decode 25 bytes
  let (legSecurityId, bytes) ← decodeUIntLE 4 bytes
  let (legRatioQty, bytes) ← decodeUIntLE 4 bytes
  pure ({ legSymbol, legSecurityId, legRatioQty }, bytes)

@[simp] theorem encode_length (message : SecurityDefinitionMessageNoLegsGroup) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : SecurityDefinitionMessageNoLegsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityDefinitionMessageNoLegsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SecurityDefinitionMessageNoLegsGroup

/-- Security Definition Message No Legs Groups -/
structure SecurityDefinitionMessageNoLegsGroups where
  blockLength : BitVec 16
  securityDefinitionMessageNoLegsGroup : Bounded 1 SecurityDefinitionMessageNoLegsGroup
  deriving DecidableEq, Repr

namespace SecurityDefinitionMessageNoLegsGroups

def encode (message : SecurityDefinitionMessageNoLegsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.securityDefinitionMessageNoLegsGroup.val.length)
    ++ (encodeMany SecurityDefinitionMessageNoLegsGroup.encode message.securityDefinitionMessageNoLegsGroup.val))

def decode (bytes : List UInt8) : Option (SecurityDefinitionMessageNoLegsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroupUint8, bytes) ← decodeUInt 1 bytes
  let (securityDefinitionMessageNoLegsGroup_, bytes) ← decodeMany SecurityDefinitionMessageNoLegsGroup.decode numInGroupUint8.toNat bytes
  if fits_securityDefinitionMessageNoLegsGroup : securityDefinitionMessageNoLegsGroup_.length < 256 ^ 1 then
    pure ({ blockLength, securityDefinitionMessageNoLegsGroup := ⟨securityDefinitionMessageNoLegsGroup_, fits_securityDefinitionMessageNoLegsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : SecurityDefinitionMessageNoLegsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SecurityDefinitionMessageNoLegsGroups) : (encode message).length ≤ 8418 := by
  have bound_securityDefinitionMessageNoLegsGroup := message.securityDefinitionMessageNoLegsGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const SecurityDefinitionMessageNoLegsGroup.encode 33 SecurityDefinitionMessageNoLegsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : SecurityDefinitionMessageNoLegsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 SecurityDefinitionMessageNoLegsGroup.encode SecurityDefinitionMessageNoLegsGroup.decode SecurityDefinitionMessageNoLegsGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.securityDefinitionMessageNoLegsGroup.length_lt]
  rfl

end SecurityDefinitionMessageNoLegsGroups

/-- Security Definition Message No Instr Attrib Group: 35 bytes -/
structure SecurityDefinitionMessageNoInstrAttribGroup where
  instrAttribType : BitVec 32
  instrAttribValue : Alpha 31
  deriving DecidableEq, Repr

namespace SecurityDefinitionMessageNoInstrAttribGroup

def encode (message : SecurityDefinitionMessageNoInstrAttribGroup) : List UInt8 :=
  encodeUIntLE 4 message.instrAttribType
    ++ (Alpha.encode message.instrAttribValue)

def decode (bytes : List UInt8) : Option (SecurityDefinitionMessageNoInstrAttribGroup × List UInt8) := do
  let (instrAttribType, bytes) ← decodeUIntLE 4 bytes
  let (instrAttribValue, bytes) ← Alpha.decode 31 bytes
  pure ({ instrAttribType, instrAttribValue }, bytes)

@[simp] theorem encode_length (message : SecurityDefinitionMessageNoInstrAttribGroup) : (encode message).length = 35 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : SecurityDefinitionMessageNoInstrAttribGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityDefinitionMessageNoInstrAttribGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SecurityDefinitionMessageNoInstrAttribGroup

/-- Security Definition Message No Instr Attrib Groups -/
structure SecurityDefinitionMessageNoInstrAttribGroups where
  blockLength : BitVec 16
  securityDefinitionMessageNoInstrAttribGroup : Bounded 1 SecurityDefinitionMessageNoInstrAttribGroup
  deriving DecidableEq, Repr

namespace SecurityDefinitionMessageNoInstrAttribGroups

def encode (message : SecurityDefinitionMessageNoInstrAttribGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.securityDefinitionMessageNoInstrAttribGroup.val.length)
    ++ (encodeMany SecurityDefinitionMessageNoInstrAttribGroup.encode message.securityDefinitionMessageNoInstrAttribGroup.val))

def decode (bytes : List UInt8) : Option (SecurityDefinitionMessageNoInstrAttribGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroupUint8, bytes) ← decodeUInt 1 bytes
  let (securityDefinitionMessageNoInstrAttribGroup_, bytes) ← decodeMany SecurityDefinitionMessageNoInstrAttribGroup.decode numInGroupUint8.toNat bytes
  if fits_securityDefinitionMessageNoInstrAttribGroup : securityDefinitionMessageNoInstrAttribGroup_.length < 256 ^ 1 then
    pure ({ blockLength, securityDefinitionMessageNoInstrAttribGroup := ⟨securityDefinitionMessageNoInstrAttribGroup_, fits_securityDefinitionMessageNoInstrAttribGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : SecurityDefinitionMessageNoInstrAttribGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SecurityDefinitionMessageNoInstrAttribGroups) : (encode message).length ≤ 8928 := by
  have bound_securityDefinitionMessageNoInstrAttribGroup := message.securityDefinitionMessageNoInstrAttribGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const SecurityDefinitionMessageNoInstrAttribGroup.encode 35 SecurityDefinitionMessageNoInstrAttribGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : SecurityDefinitionMessageNoInstrAttribGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 SecurityDefinitionMessageNoInstrAttribGroup.encode SecurityDefinitionMessageNoInstrAttribGroup.decode SecurityDefinitionMessageNoInstrAttribGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.securityDefinitionMessageNoInstrAttribGroup.length_lt]
  rfl

end SecurityDefinitionMessageNoInstrAttribGroups

/-- Security Definition Message No Events Group: 16 bytes -/
structure SecurityDefinitionMessageNoEventsGroup where
  eventType : BitVec 32
  eventDate : BitVec 32
  eventTime : BitVec 64
  deriving DecidableEq, Repr

namespace SecurityDefinitionMessageNoEventsGroup

def encode (message : SecurityDefinitionMessageNoEventsGroup) : List UInt8 :=
  encodeUIntLE 4 message.eventType
    ++ (encodeUIntLE 4 message.eventDate
    ++ (encodeUIntLE 8 message.eventTime))

def decode (bytes : List UInt8) : Option (SecurityDefinitionMessageNoEventsGroup × List UInt8) := do
  let (eventType, bytes) ← decodeUIntLE 4 bytes
  let (eventDate, bytes) ← decodeUIntLE 4 bytes
  let (eventTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ eventType, eventDate, eventTime }, bytes)

@[simp] theorem encode_length (message : SecurityDefinitionMessageNoEventsGroup) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : SecurityDefinitionMessageNoEventsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityDefinitionMessageNoEventsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SecurityDefinitionMessageNoEventsGroup

/-- Security Definition Message No Events Groups -/
structure SecurityDefinitionMessageNoEventsGroups where
  blockLength : BitVec 16
  securityDefinitionMessageNoEventsGroup : Bounded 1 SecurityDefinitionMessageNoEventsGroup
  deriving DecidableEq, Repr

namespace SecurityDefinitionMessageNoEventsGroups

def encode (message : SecurityDefinitionMessageNoEventsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.securityDefinitionMessageNoEventsGroup.val.length)
    ++ (encodeMany SecurityDefinitionMessageNoEventsGroup.encode message.securityDefinitionMessageNoEventsGroup.val))

def decode (bytes : List UInt8) : Option (SecurityDefinitionMessageNoEventsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroupUint8, bytes) ← decodeUInt 1 bytes
  let (securityDefinitionMessageNoEventsGroup_, bytes) ← decodeMany SecurityDefinitionMessageNoEventsGroup.decode numInGroupUint8.toNat bytes
  if fits_securityDefinitionMessageNoEventsGroup : securityDefinitionMessageNoEventsGroup_.length < 256 ^ 1 then
    pure ({ blockLength, securityDefinitionMessageNoEventsGroup := ⟨securityDefinitionMessageNoEventsGroup_, fits_securityDefinitionMessageNoEventsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : SecurityDefinitionMessageNoEventsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SecurityDefinitionMessageNoEventsGroups) : (encode message).length ≤ 4083 := by
  have bound_securityDefinitionMessageNoEventsGroup := message.securityDefinitionMessageNoEventsGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const SecurityDefinitionMessageNoEventsGroup.encode 16 SecurityDefinitionMessageNoEventsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : SecurityDefinitionMessageNoEventsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 SecurityDefinitionMessageNoEventsGroup.encode SecurityDefinitionMessageNoEventsGroup.decode SecurityDefinitionMessageNoEventsGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.securityDefinitionMessageNoEventsGroup.length_lt]
  rfl

end SecurityDefinitionMessageNoEventsGroups

/-- Security Desc -/
structure SecurityDesc where
  securityDescData : Bounded 2 UInt8
  deriving DecidableEq, Repr

namespace SecurityDesc

def encode (message : SecurityDesc) : List UInt8 :=
  encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.securityDescData.val.length)
    ++ (encodeMany Byte.encode message.securityDescData.val)

def decode (bytes : List UInt8) : Option (SecurityDesc × List UInt8) := do
  let (securityDescLength, bytes) ← decodeUIntLE 2 bytes
  let (securityDescData_, bytes) ← decodeMany Byte.decode securityDescLength.toNat bytes
  if fits_securityDescData : securityDescData_.length < 256 ^ 2 then
    pure ({ securityDescData := ⟨securityDescData_, fits_securityDescData⟩ }, bytes)
  else none

theorem encode_length_pos (message : SecurityDesc) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SecurityDesc) : (encode message).length ≤ 65537 := by
  have bound_securityDescData := message.securityDescData.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

@[simp] theorem decode_encode (message : SecurityDesc) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Byte.encode Byte.decode Byte.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.securityDescData.length_lt]
  rfl

end SecurityDesc

/-- Quotation List -/
structure QuotationList where
  quotationListData : Bounded 2 UInt8
  deriving DecidableEq, Repr

namespace QuotationList

def encode (message : QuotationList) : List UInt8 :=
  encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.quotationListData.val.length)
    ++ (encodeMany Byte.encode message.quotationListData.val)

def decode (bytes : List UInt8) : Option (QuotationList × List UInt8) := do
  let (quotationListLength, bytes) ← decodeUIntLE 2 bytes
  let (quotationListData_, bytes) ← decodeMany Byte.decode quotationListLength.toNat bytes
  if fits_quotationListData : quotationListData_.length < 256 ^ 2 then
    pure ({ quotationListData := ⟨quotationListData_, fits_quotationListData⟩ }, bytes)
  else none

theorem encode_length_pos (message : QuotationList) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : QuotationList) : (encode message).length ≤ 65537 := by
  have bound_quotationListData := message.quotationListData.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

@[simp] theorem decode_encode (message : QuotationList) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Byte.encode Byte.decode Byte.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.quotationListData.length_lt]
  rfl

end QuotationList

/-- Security Definition Message -/
structure SecurityDefinitionMessage where
  totNumReports : BitVec 32
  symbol : Alpha 25
  securityId : BitVec 32
  securityAltId : Alpha 25
  securityAltIdSource : SecurityAltIdSource
  securityType : Alpha 4
  cfiCode : Alpha 6
  strikePrice : BitVec 64
  contractMultiplier : BitVec 64
  securityTradingStatus : BitVec 8
  currency : Alpha 3
  marketSegmentId : MarketSegmentId
  tradingSessionId : BitVec 8
  exchangeTradingSessionIdInt32NullOptional : BitVec 32
  volatility : BitVec 64
  highLimitPx : BitVec 64
  lowLimitPx : BitVec 64
  minPriceIncrement : BitVec 64
  minPriceIncrementAmount : BitVec 64
  initialMarginOnBuy : BitVec 64
  initialMarginOnSell : BitVec 64
  initialMarginSyntetic : BitVec 64
  theorPrice : BitVec 64
  theorPriceLimit : BitVec 64
  underlyingQty : BitVec 64
  underlyingCurrency : Alpha 3
  flags : BitVec 64
  minPriceIncrementAmountCurr : BitVec 64
  settlPriceOpen : BitVec 64
  valuationMethod : Alpha 4
  riskFreeRate : Alpha 8
  fixedSpotDiscount : Alpha 8
  projectedSpotDiscount : Alpha 8
  settlCurrency : Alpha 3
  negativePrices : BitVec 8
  derivativeContractMultiplier : BitVec 32
  interestRateRiskUp : Alpha 8
  interestRateRiskDown : Alpha 8
  riskFreeRate2 : Alpha 8
  interestRate2RiskUp : Alpha 8
  interestRate2RiskDown : Alpha 8
  settlPrice : BitVec 64
  tradeModeId : BitVec 32
  groupMaskInt64 : BitVec 64
  sectionIdInt32 : BitVec 32
  baseContractIdInt32 : BitVec 32
  tradePeriodAccess : BitVec 64
  highLimitPxWeekend : BitVec 64
  lowLimitPxWeekend : BitVec 64
  clearingSettlPrice : BitVec 64
  securityDefinitionMessageNoMDFeedTypesGroups : SecurityDefinitionMessageNoMDFeedTypesGroups
  securityDefinitionMessageNoUnderlyingsGroups : SecurityDefinitionMessageNoUnderlyingsGroups
  securityDefinitionMessageNoLegsGroups : SecurityDefinitionMessageNoLegsGroups
  securityDefinitionMessageNoInstrAttribGroups : SecurityDefinitionMessageNoInstrAttribGroups
  securityDefinitionMessageNoEventsGroups : SecurityDefinitionMessageNoEventsGroups
  securityDesc : SecurityDesc
  quotationList : QuotationList
  deriving DecidableEq, Repr

namespace SecurityDefinitionMessage

def encode (message : SecurityDefinitionMessage) : List UInt8 :=
  encodeUIntLE 4 message.totNumReports
    ++ (Alpha.encode message.symbol
    ++ (encodeUIntLE 4 message.securityId
    ++ (Alpha.encode message.securityAltId
    ++ (SecurityAltIdSource.encode message.securityAltIdSource
    ++ (Alpha.encode message.securityType
    ++ (Alpha.encode message.cfiCode
    ++ (encodeUIntLE 8 message.strikePrice
    ++ (encodeUIntLE 8 message.contractMultiplier
    ++ (encodeUInt 1 message.securityTradingStatus
    ++ (Alpha.encode message.currency
    ++ (MarketSegmentId.encode message.marketSegmentId
    ++ (encodeUInt 1 message.tradingSessionId
    ++ (encodeUIntLE 4 message.exchangeTradingSessionIdInt32NullOptional
    ++ (encodeUIntLE 8 message.volatility
    ++ (encodeUIntLE 8 message.highLimitPx
    ++ (encodeUIntLE 8 message.lowLimitPx
    ++ (encodeUIntLE 8 message.minPriceIncrement
    ++ (encodeUIntLE 8 message.minPriceIncrementAmount
    ++ (encodeUIntLE 8 message.initialMarginOnBuy
    ++ (encodeUIntLE 8 message.initialMarginOnSell
    ++ (encodeUIntLE 8 message.initialMarginSyntetic
    ++ (encodeUIntLE 8 message.theorPrice
    ++ (encodeUIntLE 8 message.theorPriceLimit
    ++ (encodeUIntLE 8 message.underlyingQty
    ++ (Alpha.encode message.underlyingCurrency
    ++ (encodeUIntLE 8 message.flags
    ++ (encodeUIntLE 8 message.minPriceIncrementAmountCurr
    ++ (encodeUIntLE 8 message.settlPriceOpen
    ++ (Alpha.encode message.valuationMethod
    ++ (Alpha.encode message.riskFreeRate
    ++ (Alpha.encode message.fixedSpotDiscount
    ++ (Alpha.encode message.projectedSpotDiscount
    ++ (Alpha.encode message.settlCurrency
    ++ (encodeUInt 1 message.negativePrices
    ++ (encodeUIntLE 4 message.derivativeContractMultiplier
    ++ (Alpha.encode message.interestRateRiskUp
    ++ (Alpha.encode message.interestRateRiskDown
    ++ (Alpha.encode message.riskFreeRate2
    ++ (Alpha.encode message.interestRate2RiskUp
    ++ (Alpha.encode message.interestRate2RiskDown
    ++ (encodeUIntLE 8 message.settlPrice
    ++ (encodeUIntLE 4 message.tradeModeId
    ++ (encodeUIntLE 8 message.groupMaskInt64
    ++ (encodeUIntLE 4 message.sectionIdInt32
    ++ (encodeUIntLE 4 message.baseContractIdInt32
    ++ (encodeUIntLE 8 message.tradePeriodAccess
    ++ (encodeUIntLE 8 message.highLimitPxWeekend
    ++ (encodeUIntLE 8 message.lowLimitPxWeekend
    ++ (encodeUIntLE 8 message.clearingSettlPrice
    ++ (SecurityDefinitionMessageNoMDFeedTypesGroups.encode message.securityDefinitionMessageNoMDFeedTypesGroups
    ++ (SecurityDefinitionMessageNoUnderlyingsGroups.encode message.securityDefinitionMessageNoUnderlyingsGroups
    ++ (SecurityDefinitionMessageNoLegsGroups.encode message.securityDefinitionMessageNoLegsGroups
    ++ (SecurityDefinitionMessageNoInstrAttribGroups.encode message.securityDefinitionMessageNoInstrAttribGroups
    ++ (SecurityDefinitionMessageNoEventsGroups.encode message.securityDefinitionMessageNoEventsGroups
    ++ (SecurityDesc.encode message.securityDesc
    ++ (QuotationList.encode message.quotationList))))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SecurityDefinitionMessage × List UInt8) := do
  let (totNumReports, bytes) ← decodeUIntLE 4 bytes
  let (symbol, bytes) ← Alpha.decode 25 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (securityAltId, bytes) ← Alpha.decode 25 bytes
  let (securityAltIdSource, bytes) ← SecurityAltIdSource.decode bytes
  let (securityType, bytes) ← Alpha.decode 4 bytes
  let (cfiCode, bytes) ← Alpha.decode 6 bytes
  let (strikePrice, bytes) ← decodeUIntLE 8 bytes
  let (contractMultiplier, bytes) ← decodeUIntLE 8 bytes
  let (securityTradingStatus, bytes) ← decodeUInt 1 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (marketSegmentId, bytes) ← MarketSegmentId.decode bytes
  let (tradingSessionId, bytes) ← decodeUInt 1 bytes
  let (exchangeTradingSessionIdInt32NullOptional, bytes) ← decodeUIntLE 4 bytes
  let (volatility, bytes) ← decodeUIntLE 8 bytes
  let (highLimitPx, bytes) ← decodeUIntLE 8 bytes
  let (lowLimitPx, bytes) ← decodeUIntLE 8 bytes
  let (minPriceIncrement, bytes) ← decodeUIntLE 8 bytes
  let (minPriceIncrementAmount, bytes) ← decodeUIntLE 8 bytes
  let (initialMarginOnBuy, bytes) ← decodeUIntLE 8 bytes
  let (initialMarginOnSell, bytes) ← decodeUIntLE 8 bytes
  let (initialMarginSyntetic, bytes) ← decodeUIntLE 8 bytes
  let (theorPrice, bytes) ← decodeUIntLE 8 bytes
  let (theorPriceLimit, bytes) ← decodeUIntLE 8 bytes
  let (underlyingQty, bytes) ← decodeUIntLE 8 bytes
  let (underlyingCurrency, bytes) ← Alpha.decode 3 bytes
  let (flags, bytes) ← decodeUIntLE 8 bytes
  let (minPriceIncrementAmountCurr, bytes) ← decodeUIntLE 8 bytes
  let (settlPriceOpen, bytes) ← decodeUIntLE 8 bytes
  let (valuationMethod, bytes) ← Alpha.decode 4 bytes
  let (riskFreeRate, bytes) ← Alpha.decode 8 bytes
  let (fixedSpotDiscount, bytes) ← Alpha.decode 8 bytes
  let (projectedSpotDiscount, bytes) ← Alpha.decode 8 bytes
  let (settlCurrency, bytes) ← Alpha.decode 3 bytes
  let (negativePrices, bytes) ← decodeUInt 1 bytes
  let (derivativeContractMultiplier, bytes) ← decodeUIntLE 4 bytes
  let (interestRateRiskUp, bytes) ← Alpha.decode 8 bytes
  let (interestRateRiskDown, bytes) ← Alpha.decode 8 bytes
  let (riskFreeRate2, bytes) ← Alpha.decode 8 bytes
  let (interestRate2RiskUp, bytes) ← Alpha.decode 8 bytes
  let (interestRate2RiskDown, bytes) ← Alpha.decode 8 bytes
  let (settlPrice, bytes) ← decodeUIntLE 8 bytes
  let (tradeModeId, bytes) ← decodeUIntLE 4 bytes
  let (groupMaskInt64, bytes) ← decodeUIntLE 8 bytes
  let (sectionIdInt32, bytes) ← decodeUIntLE 4 bytes
  let (baseContractIdInt32, bytes) ← decodeUIntLE 4 bytes
  let (tradePeriodAccess, bytes) ← decodeUIntLE 8 bytes
  let (highLimitPxWeekend, bytes) ← decodeUIntLE 8 bytes
  let (lowLimitPxWeekend, bytes) ← decodeUIntLE 8 bytes
  let (clearingSettlPrice, bytes) ← decodeUIntLE 8 bytes
  let (securityDefinitionMessageNoMDFeedTypesGroups, bytes) ← SecurityDefinitionMessageNoMDFeedTypesGroups.decode bytes
  let (securityDefinitionMessageNoUnderlyingsGroups, bytes) ← SecurityDefinitionMessageNoUnderlyingsGroups.decode bytes
  let (securityDefinitionMessageNoLegsGroups, bytes) ← SecurityDefinitionMessageNoLegsGroups.decode bytes
  let (securityDefinitionMessageNoInstrAttribGroups, bytes) ← SecurityDefinitionMessageNoInstrAttribGroups.decode bytes
  let (securityDefinitionMessageNoEventsGroups, bytes) ← SecurityDefinitionMessageNoEventsGroups.decode bytes
  let (securityDesc, bytes) ← SecurityDesc.decode bytes
  let (quotationList, bytes) ← QuotationList.decode bytes
  pure ({ totNumReports, symbol, securityId, securityAltId, securityAltIdSource, securityType, cfiCode, strikePrice, contractMultiplier, securityTradingStatus, currency, marketSegmentId, tradingSessionId, exchangeTradingSessionIdInt32NullOptional, volatility, highLimitPx, lowLimitPx, minPriceIncrement, minPriceIncrementAmount, initialMarginOnBuy, initialMarginOnSell, initialMarginSyntetic, theorPrice, theorPriceLimit, underlyingQty, underlyingCurrency, flags, minPriceIncrementAmountCurr, settlPriceOpen, valuationMethod, riskFreeRate, fixedSpotDiscount, projectedSpotDiscount, settlCurrency, negativePrices, derivativeContractMultiplier, interestRateRiskUp, interestRateRiskDown, riskFreeRate2, interestRate2RiskUp, interestRate2RiskDown, settlPrice, tradeModeId, groupMaskInt64, sectionIdInt32, baseContractIdInt32, tradePeriodAccess, highLimitPxWeekend, lowLimitPxWeekend, clearingSettlPrice, securityDefinitionMessageNoMDFeedTypesGroups, securityDefinitionMessageNoUnderlyingsGroups, securityDefinitionMessageNoLegsGroups, securityDefinitionMessageNoInstrAttribGroups, securityDefinitionMessageNoEventsGroups, securityDesc, quotationList }, bytes)

theorem encode_length_pos (message : SecurityDefinitionMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SecurityDefinitionMessage) : (encode message).length ≤ 170705 := by
  have bound_securityDefinitionMessageNoMDFeedTypesGroups := SecurityDefinitionMessageNoMDFeedTypesGroups.encode_length_le message.securityDefinitionMessageNoMDFeedTypesGroups
  have bound_securityDefinitionMessageNoUnderlyingsGroups := SecurityDefinitionMessageNoUnderlyingsGroups.encode_length_le message.securityDefinitionMessageNoUnderlyingsGroups
  have bound_securityDefinitionMessageNoLegsGroups := SecurityDefinitionMessageNoLegsGroups.encode_length_le message.securityDefinitionMessageNoLegsGroups
  have bound_securityDefinitionMessageNoInstrAttribGroups := SecurityDefinitionMessageNoInstrAttribGroups.encode_length_le message.securityDefinitionMessageNoInstrAttribGroups
  have bound_securityDefinitionMessageNoEventsGroups := SecurityDefinitionMessageNoEventsGroups.encode_length_le message.securityDefinitionMessageNoEventsGroups
  have bound_securityDesc := SecurityDesc.encode_length_le message.securityDesc
  have bound_quotationList := QuotationList.encode_length_le message.quotationList
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Alpha.encode_length, SecurityAltIdSource.encode_length, encodeUInt_length, MarketSegmentId.encode_length]
  omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SecurityDefinitionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityAltIdSource.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketSegmentId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [List.append_assoc, SecurityDefinitionMessageNoMDFeedTypesGroups.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityDefinitionMessageNoUnderlyingsGroups.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityDefinitionMessageNoLegsGroups.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityDefinitionMessageNoInstrAttribGroups.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityDefinitionMessageNoEventsGroups.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityDesc.decode_encode, some_bind]
  dsimp only
  rw [QuotationList.decode_encode, some_bind]
  rfl

end SecurityDefinitionMessage

/-- Trading Session Status Message: 48 bytes -/
structure TradingSessionStatusMessage where
  tradSesOpenTime : BitVec 64
  tradSesCloseTime : BitVec 64
  tradingSessionId : BitVec 8
  exchangeTradingSessionIdInt32NullOptional : BitVec 32
  tradSesStatus : BitVec 8
  marketSegmentId : MarketSegmentId
  tradSesEvent : BitVec 8
  tradePeriodId : BitVec 64
  settlSessBegin : BitVec 64
  clrSessBegin : BitVec 64
  deriving DecidableEq, Repr

namespace TradingSessionStatusMessage

def encode (message : TradingSessionStatusMessage) : List UInt8 :=
  encodeUIntLE 8 message.tradSesOpenTime
    ++ (encodeUIntLE 8 message.tradSesCloseTime
    ++ (encodeUInt 1 message.tradingSessionId
    ++ (encodeUIntLE 4 message.exchangeTradingSessionIdInt32NullOptional
    ++ (encodeUInt 1 message.tradSesStatus
    ++ (MarketSegmentId.encode message.marketSegmentId
    ++ (encodeUInt 1 message.tradSesEvent
    ++ (encodeUIntLE 8 message.tradePeriodId
    ++ (encodeUIntLE 8 message.settlSessBegin
    ++ (encodeUIntLE 8 message.clrSessBegin)))))))))

def decode (bytes : List UInt8) : Option (TradingSessionStatusMessage × List UInt8) := do
  let (tradSesOpenTime, bytes) ← decodeUIntLE 8 bytes
  let (tradSesCloseTime, bytes) ← decodeUIntLE 8 bytes
  let (tradingSessionId, bytes) ← decodeUInt 1 bytes
  let (exchangeTradingSessionIdInt32NullOptional, bytes) ← decodeUIntLE 4 bytes
  let (tradSesStatus, bytes) ← decodeUInt 1 bytes
  let (marketSegmentId, bytes) ← MarketSegmentId.decode bytes
  let (tradSesEvent, bytes) ← decodeUInt 1 bytes
  let (tradePeriodId, bytes) ← decodeUIntLE 8 bytes
  let (settlSessBegin, bytes) ← decodeUIntLE 8 bytes
  let (clrSessBegin, bytes) ← decodeUIntLE 8 bytes
  pure ({ tradSesOpenTime, tradSesCloseTime, tradingSessionId, exchangeTradingSessionIdInt32NullOptional, tradSesStatus, marketSegmentId, tradSesEvent, tradePeriodId, settlSessBegin, clrSessBegin }, bytes)

@[simp] theorem encode_length (message : TradingSessionStatusMessage) : (encode message).length = 48 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, MarketSegmentId.encode_length]

theorem encode_length_pos (message : TradingSessionStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradingSessionStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MarketSegmentId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradingSessionStatusMessage

/-- Underlying Symbol Text -/
structure UnderlyingSymbolText where
  underlyingSymbolTextData : Bounded 2 UInt8
  deriving DecidableEq, Repr

namespace UnderlyingSymbolText

def encode (message : UnderlyingSymbolText) : List UInt8 :=
  encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.underlyingSymbolTextData.val.length)
    ++ (encodeMany Byte.encode message.underlyingSymbolTextData.val)

def decode (bytes : List UInt8) : Option (UnderlyingSymbolText × List UInt8) := do
  let (underlyingSymbolTextLength, bytes) ← decodeUIntLE 2 bytes
  let (underlyingSymbolTextData_, bytes) ← decodeMany Byte.decode underlyingSymbolTextLength.toNat bytes
  if fits_underlyingSymbolTextData : underlyingSymbolTextData_.length < 256 ^ 2 then
    pure ({ underlyingSymbolTextData := ⟨underlyingSymbolTextData_, fits_underlyingSymbolTextData⟩ }, bytes)
  else none

theorem encode_length_pos (message : UnderlyingSymbolText) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : UnderlyingSymbolText) : (encode message).length ≤ 65537 := by
  have bound_underlyingSymbolTextData := message.underlyingSymbolTextData.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

@[simp] theorem decode_encode (message : UnderlyingSymbolText) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Byte.encode Byte.decode Byte.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.underlyingSymbolTextData.length_lt]
  rfl

end UnderlyingSymbolText

/-- Discrete Auction Message No Underlyings Group -/
structure DiscreteAuctionMessageNoUnderlyingsGroup where
  underlyingSymbolText : UnderlyingSymbolText
  deriving DecidableEq, Repr

namespace DiscreteAuctionMessageNoUnderlyingsGroup

def encode (message : DiscreteAuctionMessageNoUnderlyingsGroup) : List UInt8 :=
  UnderlyingSymbolText.encode message.underlyingSymbolText

def decode (bytes : List UInt8) : Option (DiscreteAuctionMessageNoUnderlyingsGroup × List UInt8) := do
  let (underlyingSymbolText, bytes) ← UnderlyingSymbolText.decode bytes
  pure ({ underlyingSymbolText }, bytes)

theorem encode_length_pos (message : DiscreteAuctionMessageNoUnderlyingsGroup) : (encode message).length > 0 := by
  have positive := UnderlyingSymbolText.encode_length_pos message.underlyingSymbolText
  unfold encode
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DiscreteAuctionMessageNoUnderlyingsGroup) : (encode message).length ≤ 65537 := by
  have bound_underlyingSymbolText := UnderlyingSymbolText.encode_length_le message.underlyingSymbolText
  unfold encode
  omega

@[simp] theorem decode_encode (message : DiscreteAuctionMessageNoUnderlyingsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [UnderlyingSymbolText.decode_encode, some_bind]
  rfl

end DiscreteAuctionMessageNoUnderlyingsGroup

/-- Discrete Auction Message No Underlyings Groups -/
structure DiscreteAuctionMessageNoUnderlyingsGroups where
  blockLength : BitVec 16
  discreteAuctionMessageNoUnderlyingsGroup : Bounded 1 DiscreteAuctionMessageNoUnderlyingsGroup
  deriving DecidableEq, Repr

namespace DiscreteAuctionMessageNoUnderlyingsGroups

def encode (message : DiscreteAuctionMessageNoUnderlyingsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.discreteAuctionMessageNoUnderlyingsGroup.val.length)
    ++ (encodeMany DiscreteAuctionMessageNoUnderlyingsGroup.encode message.discreteAuctionMessageNoUnderlyingsGroup.val))

def decode (bytes : List UInt8) : Option (DiscreteAuctionMessageNoUnderlyingsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroupUint8, bytes) ← decodeUInt 1 bytes
  let (discreteAuctionMessageNoUnderlyingsGroup_, bytes) ← decodeMany DiscreteAuctionMessageNoUnderlyingsGroup.decode numInGroupUint8.toNat bytes
  if fits_discreteAuctionMessageNoUnderlyingsGroup : discreteAuctionMessageNoUnderlyingsGroup_.length < 256 ^ 1 then
    pure ({ blockLength, discreteAuctionMessageNoUnderlyingsGroup := ⟨discreteAuctionMessageNoUnderlyingsGroup_, fits_discreteAuctionMessageNoUnderlyingsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : DiscreteAuctionMessageNoUnderlyingsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DiscreteAuctionMessageNoUnderlyingsGroups) : (encode message).length ≤ 16711938 := by
  have bound_discreteAuctionMessageNoUnderlyingsGroup := message.discreteAuctionMessageNoUnderlyingsGroup.length_lt
  have bound_discreteAuctionMessageNoUnderlyingsGroup_items := encodeMany_length_le DiscreteAuctionMessageNoUnderlyingsGroup.encode 65537 DiscreteAuctionMessageNoUnderlyingsGroup.encode_length_le message.discreteAuctionMessageNoUnderlyingsGroup.val
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : DiscreteAuctionMessageNoUnderlyingsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 DiscreteAuctionMessageNoUnderlyingsGroup.encode DiscreteAuctionMessageNoUnderlyingsGroup.decode DiscreteAuctionMessageNoUnderlyingsGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.discreteAuctionMessageNoUnderlyingsGroup.length_lt]
  rfl

end DiscreteAuctionMessageNoUnderlyingsGroups

/-- Discrete Auction Message -/
structure DiscreteAuctionMessage where
  tradSesOpenTime : BitVec 64
  tradSesCloseTimeFrom : BitVec 64
  tradSesCloseTimeTill : BitVec 64
  auctionId : BitVec 64
  exchangeTradingSessionIdInt32 : BitVec 32
  eventIdOpen : BitVec 32
  eventIdClose : BitVec 32
  tradePeriodId : BitVec 64
  discreteAuctionMessageNoUnderlyingsGroups : DiscreteAuctionMessageNoUnderlyingsGroups
  deriving DecidableEq, Repr

namespace DiscreteAuctionMessage

def encode (message : DiscreteAuctionMessage) : List UInt8 :=
  encodeUIntLE 8 message.tradSesOpenTime
    ++ (encodeUIntLE 8 message.tradSesCloseTimeFrom
    ++ (encodeUIntLE 8 message.tradSesCloseTimeTill
    ++ (encodeUIntLE 8 message.auctionId
    ++ (encodeUIntLE 4 message.exchangeTradingSessionIdInt32
    ++ (encodeUIntLE 4 message.eventIdOpen
    ++ (encodeUIntLE 4 message.eventIdClose
    ++ (encodeUIntLE 8 message.tradePeriodId
    ++ (DiscreteAuctionMessageNoUnderlyingsGroups.encode message.discreteAuctionMessageNoUnderlyingsGroups))))))))

def decode (bytes : List UInt8) : Option (DiscreteAuctionMessage × List UInt8) := do
  let (tradSesOpenTime, bytes) ← decodeUIntLE 8 bytes
  let (tradSesCloseTimeFrom, bytes) ← decodeUIntLE 8 bytes
  let (tradSesCloseTimeTill, bytes) ← decodeUIntLE 8 bytes
  let (auctionId, bytes) ← decodeUIntLE 8 bytes
  let (exchangeTradingSessionIdInt32, bytes) ← decodeUIntLE 4 bytes
  let (eventIdOpen, bytes) ← decodeUIntLE 4 bytes
  let (eventIdClose, bytes) ← decodeUIntLE 4 bytes
  let (tradePeriodId, bytes) ← decodeUIntLE 8 bytes
  let (discreteAuctionMessageNoUnderlyingsGroups, bytes) ← DiscreteAuctionMessageNoUnderlyingsGroups.decode bytes
  pure ({ tradSesOpenTime, tradSesCloseTimeFrom, tradSesCloseTimeTill, auctionId, exchangeTradingSessionIdInt32, eventIdOpen, eventIdClose, tradePeriodId, discreteAuctionMessageNoUnderlyingsGroups }, bytes)

theorem encode_length_pos (message : DiscreteAuctionMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DiscreteAuctionMessage) : (encode message).length ≤ 16711990 := by
  have bound_discreteAuctionMessageNoUnderlyingsGroups := DiscreteAuctionMessageNoUnderlyingsGroups.encode_length_le message.discreteAuctionMessageNoUnderlyingsGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
  omega

@[simp] theorem decode_encode (message : DiscreteAuctionMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [DiscreteAuctionMessageNoUnderlyingsGroups.decode_encode, some_bind]
  rfl

end DiscreteAuctionMessage

/-- Security Group Status Message: 38 bytes -/
structure SecurityGroupStatusMessage where
  securityGroupId : BitVec 64
  haltType : BitVec 8
  tradeModeMask : BitVec 32
  groupMaskInt64NullOptional : BitVec 64
  sectionIdInt32NullOptional : BitVec 32
  baseContractIdInt32NullOptional : BitVec 32
  securityTradingStatus : BitVec 8
  statusChangeTime : BitVec 64
  deriving DecidableEq, Repr

namespace SecurityGroupStatusMessage

def encode (message : SecurityGroupStatusMessage) : List UInt8 :=
  encodeUIntLE 8 message.securityGroupId
    ++ (encodeUInt 1 message.haltType
    ++ (encodeUIntLE 4 message.tradeModeMask
    ++ (encodeUIntLE 8 message.groupMaskInt64NullOptional
    ++ (encodeUIntLE 4 message.sectionIdInt32NullOptional
    ++ (encodeUIntLE 4 message.baseContractIdInt32NullOptional
    ++ (encodeUInt 1 message.securityTradingStatus
    ++ (encodeUIntLE 8 message.statusChangeTime)))))))

def decode (bytes : List UInt8) : Option (SecurityGroupStatusMessage × List UInt8) := do
  let (securityGroupId, bytes) ← decodeUIntLE 8 bytes
  let (haltType, bytes) ← decodeUInt 1 bytes
  let (tradeModeMask, bytes) ← decodeUIntLE 4 bytes
  let (groupMaskInt64NullOptional, bytes) ← decodeUIntLE 8 bytes
  let (sectionIdInt32NullOptional, bytes) ← decodeUIntLE 4 bytes
  let (baseContractIdInt32NullOptional, bytes) ← decodeUIntLE 4 bytes
  let (securityTradingStatus, bytes) ← decodeUInt 1 bytes
  let (statusChangeTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ securityGroupId, haltType, tradeModeMask, groupMaskInt64NullOptional, sectionIdInt32NullOptional, baseContractIdInt32NullOptional, securityTradingStatus, statusChangeTime }, bytes)

@[simp] theorem encode_length (message : SecurityGroupStatusMessage) : (encode message).length = 38 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : SecurityGroupStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityGroupStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SecurityGroupStatusMessage

/-- Any Payload, selected by Template Id -/
inductive Payload where
  | heartbeatMessage (message : HeartbeatMessage) -- 1
  | sequenceResetMessage (message : SequenceResetMessage) -- 2
  | securityDefinitionMessage (message : SecurityDefinitionMessage) -- 29
  | tradingSessionStatusMessage (message : TradingSessionStatusMessage) -- 26
  | discreteAuctionMessage (message : DiscreteAuctionMessage) -- 24
  | securityGroupStatusMessage (message : SecurityGroupStatusMessage) -- 22
  deriving DecidableEq, Repr

namespace Payload

/-- The Template Id each message is sent under -/
def tag : Payload → BitVec 16
  | .heartbeatMessage _ => 1
  | .sequenceResetMessage _ => 2
  | .securityDefinitionMessage _ => 29
  | .tradingSessionStatusMessage _ => 26
  | .discreteAuctionMessage _ => 24
  | .securityGroupStatusMessage _ => 22

def encode : Payload → List UInt8
  | .heartbeatMessage message => HeartbeatMessage.encode message
  | .sequenceResetMessage message => SequenceResetMessage.encode message
  | .securityDefinitionMessage message => SecurityDefinitionMessage.encode message
  | .tradingSessionStatusMessage message => TradingSessionStatusMessage.encode message
  | .discreteAuctionMessage message => DiscreteAuctionMessage.encode message
  | .securityGroupStatusMessage message => SecurityGroupStatusMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 16711990 := by
  cases message with
  | heartbeatMessage inner =>
    simp only [encode, HeartbeatMessage.encode_length]
    omega
  | sequenceResetMessage inner =>
    simp only [encode, SequenceResetMessage.encode_length]
    omega
  | securityDefinitionMessage inner =>
    have bound_inner := SecurityDefinitionMessage.encode_length_le inner
    simp only [encode]
    omega
  | tradingSessionStatusMessage inner =>
    simp only [encode, TradingSessionStatusMessage.encode_length]
    omega
  | discreteAuctionMessage inner =>
    have bound_inner := DiscreteAuctionMessage.encode_length_le inner
    simp only [encode]
    omega
  | securityGroupStatusMessage inner =>
    simp only [encode, SecurityGroupStatusMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 1 then (HeartbeatMessage.decode bytes).map fun (message, rest) => (.heartbeatMessage message, rest)
  else if tag = 2 then (SequenceResetMessage.decode bytes).map fun (message, rest) => (.sequenceResetMessage message, rest)
  else if tag = 29 then (SecurityDefinitionMessage.decode bytes).map fun (message, rest) => (.securityDefinitionMessage message, rest)
  else if tag = 26 then (TradingSessionStatusMessage.decode bytes).map fun (message, rest) => (.tradingSessionStatusMessage message, rest)
  else if tag = 24 then (DiscreteAuctionMessage.decode bytes).map fun (message, rest) => (.discreteAuctionMessage message, rest)
  else if tag = 22 then (SecurityGroupStatusMessage.decode bytes).map fun (message, rest) => (.securityGroupStatusMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message -/
structure Message where
  blockLength : BitVec 16
  schemaId : BitVec 16
  version : BitVec 16
  payload : Payload
  deriving DecidableEq, Repr

namespace Message

def encode (message : Message) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUIntLE 2 (Payload.tag message.payload)
    ++ (encodeUIntLE 2 message.schemaId
    ++ (encodeUIntLE 2 message.version
    ++ (Payload.encode message.payload))))

def decode (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (templateId, bytes) ← decodeUIntLE 2 bytes
  let (schemaId, bytes) ← decodeUIntLE 2 bytes
  let (version, bytes) ← decodeUIntLE 2 bytes
  let (payload, bytes) ← Payload.decode templateId bytes
  pure ({ blockLength, schemaId, version, payload }, bytes)

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Message) : (encode message).length ≤ 16711998 := by
  unfold encode
  cases message.payload with
  | heartbeatMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, HeartbeatMessage.encode_length]
    omega
  | sequenceResetMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, SequenceResetMessage.encode_length]
    omega
  | securityDefinitionMessage inner =>
    have bound_inner := SecurityDefinitionMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | tradingSessionStatusMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, TradingSessionStatusMessage.encode_length]
    omega
  | discreteAuctionMessage inner =>
    have bound_inner := DiscreteAuctionMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | securityGroupStatusMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, SecurityGroupStatusMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
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
  rw [Payload.decode_encode, some_bind]
  rfl

end Message

/-- Udp Packet -/
structure UdpPacket where
  marketDataPacketHeader : MarketDataPacketHeader
  message : List Message
  deriving DecidableEq, Repr

namespace UdpPacket

def encode (message : UdpPacket) : List UInt8 :=
  MarketDataPacketHeader.encode message.marketDataPacketHeader
    ++ (encodeMany Message.encode message.message)

def decode (bytes : List UInt8) : Option UdpPacket := do
  let (marketDataPacketHeader, bytes) ← MarketDataPacketHeader.decode bytes
  let message ← decodeAll Message.decode bytes.length bytes
  pure { marketDataPacketHeader, message }

theorem encode_length_pos (message : UdpPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [MarketDataPacketHeader.encode_length, List.length_append]
  omega

theorem decode_encode (message : UdpPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [MarketDataPacketHeader.decode_encode, some_bind]
  dsimp only
  rw [decodeAll_encodeMany Message.encode Message.decode Message.decode_encode Message.encode_length_pos message.message _ (encodeMany_length_ge Message.encode Message.encode_length_pos message.message), some_bind]
  rfl

end UdpPacket

end Omi.MoexSpectraFutinforeplaySimbaV9120
