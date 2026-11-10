import Wire

/-!
# Hong Kong Exchanges and Clearing Orion Market Data Derivatives Standard Retransmission v1.47

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.

Note: Message's Msg Size is written from its body but not checked on decode, since the body has no
bound the prefix must fit; the body is read by its content

Note: Msg Count counts Message from outside Message Buffer: it is handed down to the decoder, and
the list holds exactly as many as it says

Note: Message Buffer is not framed: its size rule does not read a length field

Note: Compression Mode says whether the Message Buffer was Zlib transformed, by Compression Mode =
1: the bytes of a transformed body are carried as they lie rather than read, and Compression Mode is
written from the body the message holds with the proof of which it is

License: MIT No Attribution
-/

namespace Omi.HkexHkexderivativesStandardretransOmdV147

/-- Source: one byte code -/
def Source.codes : List UInt8 :=
  [0x48, 0x4D]

inductive Source where
  | tradingSystem -- Trading System
  | otherMarketAlerts -- Other Market Alerts
  | unlisted (byte : { byte : UInt8 // byte ∉ Source.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Source

def toByte : Source → UInt8
  | .tradingSystem => 0x48
  | .otherMarketAlerts => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Source :=
  if byte = 0x48 then .tradingSystem
  else .otherMarketAlerts

def ofByte (byte : UInt8) : Source :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Source) : ofByte value.toByte = value := by
  cases value with
  | tradingSystem => decide
  | otherMarketAlerts => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Source) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Source × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Source) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Source) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Source) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Source

/-- Last Fragment: one byte code -/
def LastFragment.codes : List UInt8 :=
  [0x59, 0x4E]

inductive LastFragment where
  | complete -- Complete
  | notComplete -- Not Complete
  | unlisted (byte : { byte : UInt8 // byte ∉ LastFragment.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LastFragment

def toByte : LastFragment → UInt8
  | .complete => 0x59
  | .notComplete => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LastFragment :=
  if byte = 0x59 then .complete
  else .notComplete

def ofByte (byte : UInt8) : LastFragment :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LastFragment) : ofByte value.toByte = value := by
  cases value with
  | complete => decide
  | notComplete => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LastFragment) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LastFragment × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LastFragment) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : LastFragment) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : LastFragment) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LastFragment

/-- Is Fractions: one byte code -/
def IsFractions.codes : List UInt8 :=
  [0x31, 0x32]

inductive IsFractions where
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ IsFractions.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace IsFractions

def toByte : IsFractions → UInt8
  | .yes => 0x31
  | .no => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : IsFractions :=
  if byte = 0x31 then .yes
  else .no

def ofByte (byte : UInt8) : IsFractions :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : IsFractions) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : IsFractions) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (IsFractions × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : IsFractions) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : IsFractions) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : IsFractions) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end IsFractions

/-- Leg Side: one byte code -/
def LegSide.codes : List UInt8 :=
  [0x42, 0x43]

inductive LegSide where
  | asDefined -- As Defined
  | opposite -- Opposite
  | unlisted (byte : { byte : UInt8 // byte ∉ LegSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LegSide

def toByte : LegSide → UInt8
  | .asDefined => 0x42
  | .opposite => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LegSide :=
  if byte = 0x42 then .asDefined
  else .opposite

def ofByte (byte : UInt8) : LegSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LegSide) : ofByte value.toByte = value := by
  cases value with
  | asDefined => decide
  | opposite => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LegSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LegSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LegSide) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : LegSide) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : LegSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LegSide

/-- Suspended: one byte code -/
def Suspended.codes : List UInt8 :=
  [0x59, 0x4E]

inductive Suspended where
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ Suspended.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Suspended

def toByte : Suspended → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Suspended :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : Suspended :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Suspended) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Suspended) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Suspended × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Suspended) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Suspended) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Suspended) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Suspended

/-- Book Entry: 24 bytes -/
structure BookEntry where
  aggregateQuantity : BitVec 64
  price : BitVec 32
  numberOfOrders : BitVec 32
  side : BitVec 8
  filler1 : Alpha 1
  priceLevel : BitVec 8
  updateAction : BitVec 8
  filler4 : Alpha 4
  deriving DecidableEq, Repr

namespace BookEntry

def encode (message : BookEntry) : List UInt8 :=
  encodeUIntLE 8 message.aggregateQuantity
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 4 message.numberOfOrders
    ++ (encodeUIntLE 1 message.side
    ++ (Alpha.encode message.filler1
    ++ (encodeUIntLE 1 message.priceLevel
    ++ (encodeUIntLE 1 message.updateAction
    ++ (Alpha.encode message.filler4)))))))

def decode (bytes : List UInt8) : Option (BookEntry × List UInt8) := do
  let (aggregateQuantity, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (numberOfOrders, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← decodeUIntLE 1 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (priceLevel, bytes) ← decodeUIntLE 1 bytes
  let (updateAction, bytes) ← decodeUIntLE 1 bytes
  let (filler4, bytes) ← Alpha.decode 4 bytes
  pure ({ aggregateQuantity, price, numberOfOrders, side, filler1, priceLevel, updateAction, filler4 }, bytes)

@[simp] theorem encode_length (message : BookEntry) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : BookEntry) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BookEntry) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BookEntry

/-- Aggregate Order Book Update Message -/
structure AggregateOrderBookUpdateMessage where
  orderbookId : BitVec 32
  filler3 : Alpha 3
  bookEntry : Bounded 1 BookEntry
  deriving DecidableEq, Repr

namespace AggregateOrderBookUpdateMessage

def encode (message : AggregateOrderBookUpdateMessage) : List UInt8 :=
  encodeUIntLE 4 message.orderbookId
    ++ (Alpha.encode message.filler3
    ++ (encodeUIntLE 1 (BitVec.ofNat (8 * 1) message.bookEntry.val.length)
    ++ (encodeMany BookEntry.encode message.bookEntry.val)))

def decode (bytes : List UInt8) : Option (AggregateOrderBookUpdateMessage × List UInt8) := do
  let (orderbookId, bytes) ← decodeUIntLE 4 bytes
  let (filler3, bytes) ← Alpha.decode 3 bytes
  let (noEntries, bytes) ← decodeUIntLE 1 bytes
  let (bookEntry_, bytes) ← decodeMany BookEntry.decode noEntries.toNat bytes
  if fits_bookEntry : bookEntry_.length < 256 ^ 1 then
    pure ({ orderbookId, filler3, bookEntry := ⟨bookEntry_, fits_bookEntry⟩ }, bytes)
  else none

theorem encode_length_pos (message : AggregateOrderBookUpdateMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : AggregateOrderBookUpdateMessage) : (encode message).length ≤ 6128 := by
  have bound_bookEntry := message.bookEntry.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Alpha.encode_length, encodeMany_length_const BookEntry.encode 24 BookEntry.encode_length]
  omega

@[simp] theorem decode_encode (message : AggregateOrderBookUpdateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 BookEntry.encode BookEntry.decode BookEntry.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.bookEntry.length_lt]
  rfl

end AggregateOrderBookUpdateMessage

/-- Calculated Opening Price Message: 20 bytes -/
structure CalculatedOpeningPriceMessage where
  orderbookId : BitVec 32
  calculatedOpeningPrice : BitVec 32
  filler4 : Alpha 4
  quantity : BitVec 64
  deriving DecidableEq, Repr

namespace CalculatedOpeningPriceMessage

def encode (message : CalculatedOpeningPriceMessage) : List UInt8 :=
  encodeUIntLE 4 message.orderbookId
    ++ (encodeUIntLE 4 message.calculatedOpeningPrice
    ++ (Alpha.encode message.filler4
    ++ (encodeUIntLE 8 message.quantity)))

def decode (bytes : List UInt8) : Option (CalculatedOpeningPriceMessage × List UInt8) := do
  let (orderbookId, bytes) ← decodeUIntLE 4 bytes
  let (calculatedOpeningPrice, bytes) ← decodeUIntLE 4 bytes
  let (filler4, bytes) ← Alpha.decode 4 bytes
  let (quantity, bytes) ← decodeUIntLE 8 bytes
  pure ({ orderbookId, calculatedOpeningPrice, filler4, quantity }, bytes)

@[simp] theorem encode_length (message : CalculatedOpeningPriceMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : CalculatedOpeningPriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CalculatedOpeningPriceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end CalculatedOpeningPriceMessage

/-- Sequence Reset: 4 bytes -/
structure SequenceReset where
  newSeqNo : BitVec 32
  deriving DecidableEq, Repr

namespace SequenceReset

def encode (message : SequenceReset) : List UInt8 :=
  encodeUIntLE 4 message.newSeqNo

def decode (bytes : List UInt8) : Option (SequenceReset × List UInt8) := do
  let (newSeqNo, bytes) ← decodeUIntLE 4 bytes
  pure ({ newSeqNo }, bytes)

@[simp] theorem encode_length (message : SequenceReset) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : SequenceReset) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SequenceReset) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SequenceReset

/-- Disaster Recovery Signal Message: 4 bytes -/
structure DisasterRecoverySignalMessage where
  drStatus : BitVec 32
  deriving DecidableEq, Repr

namespace DisasterRecoverySignalMessage

def encode (message : DisasterRecoverySignalMessage) : List UInt8 :=
  encodeUIntLE 4 message.drStatus

def decode (bytes : List UInt8) : Option (DisasterRecoverySignalMessage × List UInt8) := do
  let (drStatus, bytes) ← decodeUIntLE 4 bytes
  pure ({ drStatus }, bytes)

@[simp] theorem encode_length (message : DisasterRecoverySignalMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : DisasterRecoverySignalMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DisasterRecoverySignalMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end DisasterRecoverySignalMessage

/-- Content: 320 bytes -/
structure ContentEntry where
  content : Alpha 320
  deriving DecidableEq, Repr

namespace ContentEntry

def encode (message : ContentEntry) : List UInt8 :=
  Alpha.encode message.content

def decode (bytes : List UInt8) : Option (ContentEntry × List UInt8) := do
  let (content, bytes) ← Alpha.decode 320 bytes
  pure ({ content }, bytes)

@[simp] theorem encode_length (message : ContentEntry) : (encode message).length = 320 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : ContentEntry) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ContentEntry) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end ContentEntry

/-- Market Alert Message -/
structure MarketAlertMessage where
  alertId : BitVec 16
  source : Source
  filler1 : Alpha 1
  header : Alpha 320
  lastFragment : LastFragment
  infoType : BitVec 8
  priority : BitVec 8
  content : Bounded 1 ContentEntry
  deriving DecidableEq, Repr

namespace MarketAlertMessage

def encode (message : MarketAlertMessage) : List UInt8 :=
  encodeUIntLE 2 message.alertId
    ++ (Source.encode message.source
    ++ (Alpha.encode message.filler1
    ++ (Alpha.encode message.header
    ++ (LastFragment.encode message.lastFragment
    ++ (encodeUIntLE 1 message.infoType
    ++ (encodeUIntLE 1 message.priority
    ++ (encodeUIntLE 1 (BitVec.ofNat (8 * 1) message.content.val.length)
    ++ (encodeMany ContentEntry.encode message.content.val))))))))

def decode (bytes : List UInt8) : Option (MarketAlertMessage × List UInt8) := do
  let (alertId, bytes) ← decodeUIntLE 2 bytes
  let (source, bytes) ← Source.decode bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (header, bytes) ← Alpha.decode 320 bytes
  let (lastFragment, bytes) ← LastFragment.decode bytes
  let (infoType, bytes) ← decodeUIntLE 1 bytes
  let (priority, bytes) ← decodeUIntLE 1 bytes
  let (noLines, bytes) ← decodeUIntLE 1 bytes
  let (content_, bytes) ← decodeMany ContentEntry.decode noLines.toNat bytes
  if fits_content : content_.length < 256 ^ 1 then
    pure ({ alertId, source, filler1, header, lastFragment, infoType, priority, content := ⟨content_, fits_content⟩ }, bytes)
  else none

theorem encode_length_pos (message : MarketAlertMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MarketAlertMessage) : (encode message).length ≤ 81928 := by
  have bound_content := message.content.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Source.encode_length, Alpha.encode_length, LastFragment.encode_length, encodeMany_length_const ContentEntry.encode 320 ContentEntry.encode_length]
  omega

@[simp] theorem decode_encode (message : MarketAlertMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Source.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LastFragment.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 ContentEntry.encode ContentEntry.decode ContentEntry.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.content.length_lt]
  rfl

end MarketAlertMessage

/-- Open Interest Message: 36 bytes -/
structure OpenInterestMessage where
  dayIndicator : BitVec 16
  filler6 : Alpha 6
  orderbookId : BitVec 32
  settlement : BitVec 32
  dealCount : BitVec 32
  grossOi : BitVec 32
  netOi : BitVec 32
  turnover : BitVec 64
  deriving DecidableEq, Repr

namespace OpenInterestMessage

def encode (message : OpenInterestMessage) : List UInt8 :=
  encodeUIntLE 2 message.dayIndicator
    ++ (Alpha.encode message.filler6
    ++ (encodeUIntLE 4 message.orderbookId
    ++ (encodeUIntLE 4 message.settlement
    ++ (encodeUIntLE 4 message.dealCount
    ++ (encodeUIntLE 4 message.grossOi
    ++ (encodeUIntLE 4 message.netOi
    ++ (encodeUIntLE 8 message.turnover)))))))

def decode (bytes : List UInt8) : Option (OpenInterestMessage × List UInt8) := do
  let (dayIndicator, bytes) ← decodeUIntLE 2 bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (orderbookId, bytes) ← decodeUIntLE 4 bytes
  let (settlement, bytes) ← decodeUIntLE 4 bytes
  let (dealCount, bytes) ← decodeUIntLE 4 bytes
  let (grossOi, bytes) ← decodeUIntLE 4 bytes
  let (netOi, bytes) ← decodeUIntLE 4 bytes
  let (turnover, bytes) ← decodeUIntLE 8 bytes
  pure ({ dayIndicator, filler6, orderbookId, settlement, dealCount, grossOi, netOi, turnover }, bytes)

@[simp] theorem encode_length (message : OpenInterestMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : OpenInterestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OpenInterestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OpenInterestMessage

/-- Quote Request: 12 bytes -/
structure QuoteRequest where
  orderbookId : BitVec 32
  numberOfLots : BitVec 32
  bidAskFlag : BitVec 8
  filler3 : Alpha 3
  deriving DecidableEq, Repr

namespace QuoteRequest

def encode (message : QuoteRequest) : List UInt8 :=
  encodeUIntLE 4 message.orderbookId
    ++ (encodeUIntLE 4 message.numberOfLots
    ++ (encodeUIntLE 1 message.bidAskFlag
    ++ (Alpha.encode message.filler3)))

def decode (bytes : List UInt8) : Option (QuoteRequest × List UInt8) := do
  let (orderbookId, bytes) ← decodeUIntLE 4 bytes
  let (numberOfLots, bytes) ← decodeUIntLE 4 bytes
  let (bidAskFlag, bytes) ← decodeUIntLE 1 bytes
  let (filler3, bytes) ← Alpha.decode 3 bytes
  pure ({ orderbookId, numberOfLots, bidAskFlag, filler3 }, bytes)

@[simp] theorem encode_length (message : QuoteRequest) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : QuoteRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end QuoteRequest

/-- Commodity Definition Message: 90 bytes -/
structure CommodityDefinitionMessage where
  commodityCode : BitVec 16
  decimalInUnderlyingPrice : BitVec 16
  isinCode : Alpha 12
  baseCurrency : Alpha 3
  underlyingPriceUnit : BitVec 8
  commodityName : Alpha 32
  nominalValue : BitVec 64
  underlyingCode : Alpha 20
  underlyingType : BitVec 8
  effectiveTomorrow : BitVec 8
  commodityId : Alpha 6
  filler2 : Alpha 2
  deriving DecidableEq, Repr

namespace CommodityDefinitionMessage

def encode (message : CommodityDefinitionMessage) : List UInt8 :=
  encodeUIntLE 2 message.commodityCode
    ++ (encodeUIntLE 2 message.decimalInUnderlyingPrice
    ++ (Alpha.encode message.isinCode
    ++ (Alpha.encode message.baseCurrency
    ++ (encodeUIntLE 1 message.underlyingPriceUnit
    ++ (Alpha.encode message.commodityName
    ++ (encodeUIntLE 8 message.nominalValue
    ++ (Alpha.encode message.underlyingCode
    ++ (encodeUIntLE 1 message.underlyingType
    ++ (encodeUIntLE 1 message.effectiveTomorrow
    ++ (Alpha.encode message.commodityId
    ++ (Alpha.encode message.filler2)))))))))))

def decode (bytes : List UInt8) : Option (CommodityDefinitionMessage × List UInt8) := do
  let (commodityCode, bytes) ← decodeUIntLE 2 bytes
  let (decimalInUnderlyingPrice, bytes) ← decodeUIntLE 2 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (baseCurrency, bytes) ← Alpha.decode 3 bytes
  let (underlyingPriceUnit, bytes) ← decodeUIntLE 1 bytes
  let (commodityName, bytes) ← Alpha.decode 32 bytes
  let (nominalValue, bytes) ← decodeUIntLE 8 bytes
  let (underlyingCode, bytes) ← Alpha.decode 20 bytes
  let (underlyingType, bytes) ← decodeUIntLE 1 bytes
  let (effectiveTomorrow, bytes) ← decodeUIntLE 1 bytes
  let (commodityId, bytes) ← Alpha.decode 6 bytes
  let (filler2, bytes) ← Alpha.decode 2 bytes
  pure ({ commodityCode, decimalInUnderlyingPrice, isinCode, baseCurrency, underlyingPriceUnit, commodityName, nominalValue, underlyingCode, underlyingType, effectiveTomorrow, commodityId, filler2 }, bytes)

@[simp] theorem encode_length (message : CommodityDefinitionMessage) : (encode message).length = 90 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : CommodityDefinitionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CommodityDefinitionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end CommodityDefinitionMessage

/-- Class Definition Message: 114 bytes -/
structure ClassDefinitionMessage where
  country : BitVec 8
  market : BitVec 8
  instrumentGroup : BitVec 8
  modifier : BitVec 8
  commodityCode : BitVec 16
  filler2 : Alpha 2
  priceQuotationFactor : BitVec 32
  contractSize : BitVec 32
  decimalInStrikePrice : BitVec 16
  decimalInContractSize : BitVec 16
  decimalInPremium : BitVec 16
  rankingType : BitVec 16
  tradable : BitVec 8
  premiumUnit4Price : BitVec 8
  baseCurrency : Alpha 3
  instrumentClassId : Alpha 14
  instrumentClassName : Alpha 32
  isFractions : IsFractions
  settlementCurrencyId : Alpha 32
  effectiveTomorrow : BitVec 8
  tickStepSize : BitVec 32
  filler1 : Alpha 1
  deriving DecidableEq, Repr

namespace ClassDefinitionMessage

def encode (message : ClassDefinitionMessage) : List UInt8 :=
  encodeUIntLE 1 message.country
    ++ (encodeUIntLE 1 message.market
    ++ (encodeUIntLE 1 message.instrumentGroup
    ++ (encodeUIntLE 1 message.modifier
    ++ (encodeUIntLE 2 message.commodityCode
    ++ (Alpha.encode message.filler2
    ++ (encodeUIntLE 4 message.priceQuotationFactor
    ++ (encodeUIntLE 4 message.contractSize
    ++ (encodeUIntLE 2 message.decimalInStrikePrice
    ++ (encodeUIntLE 2 message.decimalInContractSize
    ++ (encodeUIntLE 2 message.decimalInPremium
    ++ (encodeUIntLE 2 message.rankingType
    ++ (encodeUIntLE 1 message.tradable
    ++ (encodeUIntLE 1 message.premiumUnit4Price
    ++ (Alpha.encode message.baseCurrency
    ++ (Alpha.encode message.instrumentClassId
    ++ (Alpha.encode message.instrumentClassName
    ++ (IsFractions.encode message.isFractions
    ++ (Alpha.encode message.settlementCurrencyId
    ++ (encodeUIntLE 1 message.effectiveTomorrow
    ++ (encodeUIntLE 4 message.tickStepSize
    ++ (Alpha.encode message.filler1)))))))))))))))))))))

def decode (bytes : List UInt8) : Option (ClassDefinitionMessage × List UInt8) := do
  let (country, bytes) ← decodeUIntLE 1 bytes
  let (market, bytes) ← decodeUIntLE 1 bytes
  let (instrumentGroup, bytes) ← decodeUIntLE 1 bytes
  let (modifier, bytes) ← decodeUIntLE 1 bytes
  let (commodityCode, bytes) ← decodeUIntLE 2 bytes
  let (filler2, bytes) ← Alpha.decode 2 bytes
  let (priceQuotationFactor, bytes) ← decodeUIntLE 4 bytes
  let (contractSize, bytes) ← decodeUIntLE 4 bytes
  let (decimalInStrikePrice, bytes) ← decodeUIntLE 2 bytes
  let (decimalInContractSize, bytes) ← decodeUIntLE 2 bytes
  let (decimalInPremium, bytes) ← decodeUIntLE 2 bytes
  let (rankingType, bytes) ← decodeUIntLE 2 bytes
  let (tradable, bytes) ← decodeUIntLE 1 bytes
  let (premiumUnit4Price, bytes) ← decodeUIntLE 1 bytes
  let (baseCurrency, bytes) ← Alpha.decode 3 bytes
  let (instrumentClassId, bytes) ← Alpha.decode 14 bytes
  let (instrumentClassName, bytes) ← Alpha.decode 32 bytes
  let (isFractions, bytes) ← IsFractions.decode bytes
  let (settlementCurrencyId, bytes) ← Alpha.decode 32 bytes
  let (effectiveTomorrow, bytes) ← decodeUIntLE 1 bytes
  let (tickStepSize, bytes) ← decodeUIntLE 4 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  pure ({ country, market, instrumentGroup, modifier, commodityCode, filler2, priceQuotationFactor, contractSize, decimalInStrikePrice, decimalInContractSize, decimalInPremium, rankingType, tradable, premiumUnit4Price, baseCurrency, instrumentClassId, instrumentClassName, isFractions, settlementCurrencyId, effectiveTomorrow, tickStepSize, filler1 }, bytes)

@[simp] theorem encode_length (message : ClassDefinitionMessage) : (encode message).length = 114 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, IsFractions.encode_length]

theorem encode_length_pos (message : ClassDefinitionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ClassDefinitionMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, IsFractions.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ClassDefinitionMessage

/-- Series Definition Base Message: 56 bytes -/
structure SeriesDefinitionBaseMessage where
  orderbookId : BitVec 32
  symbol : Alpha 32
  financialProduct : BitVec 8
  numberOfDecimalsPrice : BitVec 16
  numberOfLegs : BitVec 8
  strikePrice : BitVec 32
  expirationDate : Alpha 8
  decimalInStrikePrice : BitVec 16
  putOrCall : BitVec 8
  filler1 : Alpha 1
  deriving DecidableEq, Repr

namespace SeriesDefinitionBaseMessage

def encode (message : SeriesDefinitionBaseMessage) : List UInt8 :=
  encodeUIntLE 4 message.orderbookId
    ++ (Alpha.encode message.symbol
    ++ (encodeUIntLE 1 message.financialProduct
    ++ (encodeUIntLE 2 message.numberOfDecimalsPrice
    ++ (encodeUIntLE 1 message.numberOfLegs
    ++ (encodeUIntLE 4 message.strikePrice
    ++ (Alpha.encode message.expirationDate
    ++ (encodeUIntLE 2 message.decimalInStrikePrice
    ++ (encodeUIntLE 1 message.putOrCall
    ++ (Alpha.encode message.filler1)))))))))

def decode (bytes : List UInt8) : Option (SeriesDefinitionBaseMessage × List UInt8) := do
  let (orderbookId, bytes) ← decodeUIntLE 4 bytes
  let (symbol, bytes) ← Alpha.decode 32 bytes
  let (financialProduct, bytes) ← decodeUIntLE 1 bytes
  let (numberOfDecimalsPrice, bytes) ← decodeUIntLE 2 bytes
  let (numberOfLegs, bytes) ← decodeUIntLE 1 bytes
  let (strikePrice, bytes) ← decodeUIntLE 4 bytes
  let (expirationDate, bytes) ← Alpha.decode 8 bytes
  let (decimalInStrikePrice, bytes) ← decodeUIntLE 2 bytes
  let (putOrCall, bytes) ← decodeUIntLE 1 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  pure ({ orderbookId, symbol, financialProduct, numberOfDecimalsPrice, numberOfLegs, strikePrice, expirationDate, decimalInStrikePrice, putOrCall, filler1 }, bytes)

@[simp] theorem encode_length (message : SeriesDefinitionBaseMessage) : (encode message).length = 56 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : SeriesDefinitionBaseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SeriesDefinitionBaseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SeriesDefinitionBaseMessage

/-- Series Definition Extended Message: 100 bytes -/
structure SeriesDefinitionExtendedMessage where
  orderbookId : BitVec 32
  symbol : Alpha 32
  country : BitVec 8
  market : BitVec 8
  instrumentGroup : BitVec 8
  modifier : BitVec 8
  commodityCode : BitVec 16
  expiryDate : BitVec 16
  strikePrice : BitVec 32
  contractSizeExtended : BitVec 64
  isinCode : Alpha 12
  seriesStatus : BitVec 8
  effectiveTomorrow : BitVec 8
  priceQuotationFactor : BitVec 32
  priceMethod : BitVec 8
  filler1 : Alpha 1
  effectiveExpDate : Alpha 8
  dateTimeLastTrading : BitVec 64
  dateTimeFirstTrading : BitVec 64
  deriving DecidableEq, Repr

namespace SeriesDefinitionExtendedMessage

def encode (message : SeriesDefinitionExtendedMessage) : List UInt8 :=
  encodeUIntLE 4 message.orderbookId
    ++ (Alpha.encode message.symbol
    ++ (encodeUIntLE 1 message.country
    ++ (encodeUIntLE 1 message.market
    ++ (encodeUIntLE 1 message.instrumentGroup
    ++ (encodeUIntLE 1 message.modifier
    ++ (encodeUIntLE 2 message.commodityCode
    ++ (encodeUIntLE 2 message.expiryDate
    ++ (encodeUIntLE 4 message.strikePrice
    ++ (encodeUIntLE 8 message.contractSizeExtended
    ++ (Alpha.encode message.isinCode
    ++ (encodeUIntLE 1 message.seriesStatus
    ++ (encodeUIntLE 1 message.effectiveTomorrow
    ++ (encodeUIntLE 4 message.priceQuotationFactor
    ++ (encodeUIntLE 1 message.priceMethod
    ++ (Alpha.encode message.filler1
    ++ (Alpha.encode message.effectiveExpDate
    ++ (encodeUIntLE 8 message.dateTimeLastTrading
    ++ (encodeUIntLE 8 message.dateTimeFirstTrading))))))))))))))))))

def decode (bytes : List UInt8) : Option (SeriesDefinitionExtendedMessage × List UInt8) := do
  let (orderbookId, bytes) ← decodeUIntLE 4 bytes
  let (symbol, bytes) ← Alpha.decode 32 bytes
  let (country, bytes) ← decodeUIntLE 1 bytes
  let (market, bytes) ← decodeUIntLE 1 bytes
  let (instrumentGroup, bytes) ← decodeUIntLE 1 bytes
  let (modifier, bytes) ← decodeUIntLE 1 bytes
  let (commodityCode, bytes) ← decodeUIntLE 2 bytes
  let (expiryDate, bytes) ← decodeUIntLE 2 bytes
  let (strikePrice, bytes) ← decodeUIntLE 4 bytes
  let (contractSizeExtended, bytes) ← decodeUIntLE 8 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (seriesStatus, bytes) ← decodeUIntLE 1 bytes
  let (effectiveTomorrow, bytes) ← decodeUIntLE 1 bytes
  let (priceQuotationFactor, bytes) ← decodeUIntLE 4 bytes
  let (priceMethod, bytes) ← decodeUIntLE 1 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (effectiveExpDate, bytes) ← Alpha.decode 8 bytes
  let (dateTimeLastTrading, bytes) ← decodeUIntLE 8 bytes
  let (dateTimeFirstTrading, bytes) ← decodeUIntLE 8 bytes
  pure ({ orderbookId, symbol, country, market, instrumentGroup, modifier, commodityCode, expiryDate, strikePrice, contractSizeExtended, isinCode, seriesStatus, effectiveTomorrow, priceQuotationFactor, priceMethod, filler1, effectiveExpDate, dateTimeLastTrading, dateTimeFirstTrading }, bytes)

@[simp] theorem encode_length (message : SeriesDefinitionExtendedMessage) : (encode message).length = 100 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : SeriesDefinitionExtendedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SeriesDefinitionExtendedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SeriesDefinitionExtendedMessage

/-- Combination Definition Message: 16 bytes -/
structure CombinationDefinitionMessage where
  comboOrderbookId : BitVec 32
  legOrderbookId : BitVec 32
  filler3 : Alpha 3
  legSide : LegSide
  legRatio : BitVec 32
  deriving DecidableEq, Repr

namespace CombinationDefinitionMessage

def encode (message : CombinationDefinitionMessage) : List UInt8 :=
  encodeUIntLE 4 message.comboOrderbookId
    ++ (encodeUIntLE 4 message.legOrderbookId
    ++ (Alpha.encode message.filler3
    ++ (LegSide.encode message.legSide
    ++ (encodeUIntLE 4 message.legRatio))))

def decode (bytes : List UInt8) : Option (CombinationDefinitionMessage × List UInt8) := do
  let (comboOrderbookId, bytes) ← decodeUIntLE 4 bytes
  let (legOrderbookId, bytes) ← decodeUIntLE 4 bytes
  let (filler3, bytes) ← Alpha.decode 3 bytes
  let (legSide, bytes) ← LegSide.decode bytes
  let (legRatio, bytes) ← decodeUIntLE 4 bytes
  pure ({ comboOrderbookId, legOrderbookId, filler3, legSide, legRatio }, bytes)

@[simp] theorem encode_length (message : CombinationDefinitionMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, LegSide.encode_length]

theorem encode_length_pos (message : CombinationDefinitionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CombinationDefinitionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LegSide.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end CombinationDefinitionMessage

/-- Refresh Complete: 4 bytes -/
structure RefreshComplete where
  lastSeqNum : BitVec 32
  deriving DecidableEq, Repr

namespace RefreshComplete

def encode (message : RefreshComplete) : List UInt8 :=
  encodeUIntLE 4 message.lastSeqNum

def decode (bytes : List UInt8) : Option (RefreshComplete × List UInt8) := do
  let (lastSeqNum, bytes) ← decodeUIntLE 4 bytes
  pure ({ lastSeqNum }, bytes)

@[simp] theorem encode_length (message : RefreshComplete) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : RefreshComplete) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RefreshComplete) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end RefreshComplete

/-- Logon: 12 bytes -/
structure Logon where
  username : Alpha 12
  deriving DecidableEq, Repr

namespace Logon

def encode (message : Logon) : List UInt8 :=
  Alpha.encode message.username

def decode (bytes : List UInt8) : Option (Logon × List UInt8) := do
  let (username, bytes) ← Alpha.decode 12 bytes
  pure ({ username }, bytes)

@[simp] theorem encode_length (message : Logon) : (encode message).length = 12 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : Logon) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Logon) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end Logon

/-- Logon Response: 4 bytes -/
structure LogonResponse where
  sessionStatus : BitVec 8
  filler3 : Alpha 3
  deriving DecidableEq, Repr

namespace LogonResponse

def encode (message : LogonResponse) : List UInt8 :=
  encodeUIntLE 1 message.sessionStatus
    ++ (Alpha.encode message.filler3)

def decode (bytes : List UInt8) : Option (LogonResponse × List UInt8) := do
  let (sessionStatus, bytes) ← decodeUIntLE 1 bytes
  let (filler3, bytes) ← Alpha.decode 3 bytes
  pure ({ sessionStatus, filler3 }, bytes)

@[simp] theorem encode_length (message : LogonResponse) : (encode message).length = 4 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : LogonResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogonResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LogonResponse

/-- Retransmission Request: 12 bytes -/
structure RetransmissionRequest where
  channelId : BitVec 16
  filler2 : Alpha 2
  beginSeqNum : BitVec 32
  endSeqNum : BitVec 32
  deriving DecidableEq, Repr

namespace RetransmissionRequest

def encode (message : RetransmissionRequest) : List UInt8 :=
  encodeUIntLE 2 message.channelId
    ++ (Alpha.encode message.filler2
    ++ (encodeUIntLE 4 message.beginSeqNum
    ++ (encodeUIntLE 4 message.endSeqNum)))

def decode (bytes : List UInt8) : Option (RetransmissionRequest × List UInt8) := do
  let (channelId, bytes) ← decodeUIntLE 2 bytes
  let (filler2, bytes) ← Alpha.decode 2 bytes
  let (beginSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (endSeqNum, bytes) ← decodeUIntLE 4 bytes
  pure ({ channelId, filler2, beginSeqNum, endSeqNum }, bytes)

@[simp] theorem encode_length (message : RetransmissionRequest) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : RetransmissionRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RetransmissionRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end RetransmissionRequest

/-- Retransmission Response: 12 bytes -/
structure RetransmissionResponse where
  channelId : BitVec 16
  retransStatus : BitVec 8
  filler1 : Alpha 1
  beginSeqNum : BitVec 32
  endSeqNum : BitVec 32
  deriving DecidableEq, Repr

namespace RetransmissionResponse

def encode (message : RetransmissionResponse) : List UInt8 :=
  encodeUIntLE 2 message.channelId
    ++ (encodeUIntLE 1 message.retransStatus
    ++ (Alpha.encode message.filler1
    ++ (encodeUIntLE 4 message.beginSeqNum
    ++ (encodeUIntLE 4 message.endSeqNum))))

def decode (bytes : List UInt8) : Option (RetransmissionResponse × List UInt8) := do
  let (channelId, bytes) ← decodeUIntLE 2 bytes
  let (retransStatus, bytes) ← decodeUIntLE 1 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (beginSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (endSeqNum, bytes) ← decodeUIntLE 4 bytes
  pure ({ channelId, retransStatus, filler1, beginSeqNum, endSeqNum }, bytes)

@[simp] theorem encode_length (message : RetransmissionResponse) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : RetransmissionResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RetransmissionResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end RetransmissionResponse

/-- Market Status Message: 48 bytes -/
structure MarketStatusMessage where
  stateLevel : BitVec 16
  market : BitVec 8
  instrument : BitVec 8
  orderbookId : BitVec 32
  commodityCode : BitVec 16
  filler2 : Alpha 2
  actualStartDate : Alpha 8
  actualStartTime : Alpha 6
  plannedStartDate : Alpha 8
  plannedStartTime : Alpha 6
  secondsToStateChange : BitVec 16
  state : BitVec 16
  priority : BitVec 8
  filler3 : Alpha 3
  deriving DecidableEq, Repr

namespace MarketStatusMessage

def encode (message : MarketStatusMessage) : List UInt8 :=
  encodeUIntLE 2 message.stateLevel
    ++ (encodeUIntLE 1 message.market
    ++ (encodeUIntLE 1 message.instrument
    ++ (encodeUIntLE 4 message.orderbookId
    ++ (encodeUIntLE 2 message.commodityCode
    ++ (Alpha.encode message.filler2
    ++ (Alpha.encode message.actualStartDate
    ++ (Alpha.encode message.actualStartTime
    ++ (Alpha.encode message.plannedStartDate
    ++ (Alpha.encode message.plannedStartTime
    ++ (encodeUIntLE 2 message.secondsToStateChange
    ++ (encodeUIntLE 2 message.state
    ++ (encodeUIntLE 1 message.priority
    ++ (Alpha.encode message.filler3)))))))))))))

def decode (bytes : List UInt8) : Option (MarketStatusMessage × List UInt8) := do
  let (stateLevel, bytes) ← decodeUIntLE 2 bytes
  let (market, bytes) ← decodeUIntLE 1 bytes
  let (instrument, bytes) ← decodeUIntLE 1 bytes
  let (orderbookId, bytes) ← decodeUIntLE 4 bytes
  let (commodityCode, bytes) ← decodeUIntLE 2 bytes
  let (filler2, bytes) ← Alpha.decode 2 bytes
  let (actualStartDate, bytes) ← Alpha.decode 8 bytes
  let (actualStartTime, bytes) ← Alpha.decode 6 bytes
  let (plannedStartDate, bytes) ← Alpha.decode 8 bytes
  let (plannedStartTime, bytes) ← Alpha.decode 6 bytes
  let (secondsToStateChange, bytes) ← decodeUIntLE 2 bytes
  let (state, bytes) ← decodeUIntLE 2 bytes
  let (priority, bytes) ← decodeUIntLE 1 bytes
  let (filler3, bytes) ← Alpha.decode 3 bytes
  pure ({ stateLevel, market, instrument, orderbookId, commodityCode, filler2, actualStartDate, actualStartTime, plannedStartDate, plannedStartTime, secondsToStateChange, state, priority, filler3 }, bytes)

@[simp] theorem encode_length (message : MarketStatusMessage) : (encode message).length = 48 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : MarketStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketStatusMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end MarketStatusMessage

/-- Series Status Message: 8 bytes -/
structure SeriesStatusMessage where
  orderbookId : BitVec 32
  suspensionIndicator : BitVec 8
  seriesStatus : BitVec 8
  filler2 : Alpha 2
  deriving DecidableEq, Repr

namespace SeriesStatusMessage

def encode (message : SeriesStatusMessage) : List UInt8 :=
  encodeUIntLE 4 message.orderbookId
    ++ (encodeUIntLE 1 message.suspensionIndicator
    ++ (encodeUIntLE 1 message.seriesStatus
    ++ (Alpha.encode message.filler2)))

def decode (bytes : List UInt8) : Option (SeriesStatusMessage × List UInt8) := do
  let (orderbookId, bytes) ← decodeUIntLE 4 bytes
  let (suspensionIndicator, bytes) ← decodeUIntLE 1 bytes
  let (seriesStatus, bytes) ← decodeUIntLE 1 bytes
  let (filler2, bytes) ← Alpha.decode 2 bytes
  pure ({ orderbookId, suspensionIndicator, seriesStatus, filler2 }, bytes)

@[simp] theorem encode_length (message : SeriesStatusMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : SeriesStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SeriesStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SeriesStatusMessage

/-- Commodity Status Message: 4 bytes -/
structure CommodityStatusMessage where
  commodityCode : BitVec 16
  suspended : Suspended
  locked : BitVec 8
  deriving DecidableEq, Repr

namespace CommodityStatusMessage

def encode (message : CommodityStatusMessage) : List UInt8 :=
  encodeUIntLE 2 message.commodityCode
    ++ (Suspended.encode message.suspended
    ++ (encodeUIntLE 1 message.locked))

def decode (bytes : List UInt8) : Option (CommodityStatusMessage × List UInt8) := do
  let (commodityCode, bytes) ← decodeUIntLE 2 bytes
  let (suspended, bytes) ← Suspended.decode bytes
  let (locked, bytes) ← decodeUIntLE 1 bytes
  pure ({ commodityCode, suspended, locked }, bytes)

@[simp] theorem encode_length (message : CommodityStatusMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Suspended.encode_length]

theorem encode_length_pos (message : CommodityStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CommodityStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Suspended.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end CommodityStatusMessage

/-- Trade Statistics Message: 56 bytes -/
structure TradeStatisticsMessage where
  orderbookId : BitVec 32
  price : BitVec 32
  dealSource : BitVec 8
  session : BitVec 8
  filler2 : Alpha 2
  statisticsAggregateQuantity : BitVec 64
  open_ : BitVec 32
  high : BitVec 32
  low : BitVec 32
  filler4 : Alpha 4
  tradeReportVolume : BitVec 64
  dealCount : BitVec 32
  turnover : BitVec 64
  deriving DecidableEq, Repr

namespace TradeStatisticsMessage

def encode (message : TradeStatisticsMessage) : List UInt8 :=
  encodeUIntLE 4 message.orderbookId
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 1 message.dealSource
    ++ (encodeUIntLE 1 message.session
    ++ (Alpha.encode message.filler2
    ++ (encodeUIntLE 8 message.statisticsAggregateQuantity
    ++ (encodeUIntLE 4 message.open_
    ++ (encodeUIntLE 4 message.high
    ++ (encodeUIntLE 4 message.low
    ++ (Alpha.encode message.filler4
    ++ (encodeUIntLE 8 message.tradeReportVolume
    ++ (encodeUIntLE 4 message.dealCount
    ++ (encodeUIntLE 8 message.turnover))))))))))))

def decode (bytes : List UInt8) : Option (TradeStatisticsMessage × List UInt8) := do
  let (orderbookId, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (dealSource, bytes) ← decodeUIntLE 1 bytes
  let (session, bytes) ← decodeUIntLE 1 bytes
  let (filler2, bytes) ← Alpha.decode 2 bytes
  let (statisticsAggregateQuantity, bytes) ← decodeUIntLE 8 bytes
  let (open_, bytes) ← decodeUIntLE 4 bytes
  let (high, bytes) ← decodeUIntLE 4 bytes
  let (low, bytes) ← decodeUIntLE 4 bytes
  let (filler4, bytes) ← Alpha.decode 4 bytes
  let (tradeReportVolume, bytes) ← decodeUIntLE 8 bytes
  let (dealCount, bytes) ← decodeUIntLE 4 bytes
  let (turnover, bytes) ← decodeUIntLE 8 bytes
  pure ({ orderbookId, price, dealSource, session, filler2, statisticsAggregateQuantity, open_, high, low, filler4, tradeReportVolume, dealCount, turnover }, bytes)

@[simp] theorem encode_length (message : TradeStatisticsMessage) : (encode message).length = 56 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : TradeStatisticsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeStatisticsMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeStatisticsMessage

/-- Any Payload, selected by Msg Type -/
inductive Payload where
  | aggregateOrderBookUpdateMessage (message : AggregateOrderBookUpdateMessage) -- 353
  | calculatedOpeningPriceMessage (message : CalculatedOpeningPriceMessage) -- 364
  | sequenceReset (message : SequenceReset) -- 100
  | disasterRecoverySignalMessage (message : DisasterRecoverySignalMessage) -- 105
  | marketAlertMessage (message : MarketAlertMessage) -- 323
  | openInterestMessage (message : OpenInterestMessage) -- 366
  | quoteRequest (message : QuoteRequest) -- 336
  | commodityDefinitionMessage (message : CommodityDefinitionMessage) -- 301
  | classDefinitionMessage (message : ClassDefinitionMessage) -- 302
  | seriesDefinitionBaseMessage (message : SeriesDefinitionBaseMessage) -- 303
  | seriesDefinitionExtendedMessage (message : SeriesDefinitionExtendedMessage) -- 304
  | combinationDefinitionMessage (message : CombinationDefinitionMessage) -- 305
  | refreshComplete (message : RefreshComplete) -- 203
  | logon (message : Logon) -- 101
  | logonResponse (message : LogonResponse) -- 102
  | retransmissionRequest (message : RetransmissionRequest) -- 201
  | retransmissionResponse (message : RetransmissionResponse) -- 202
  | marketStatusMessage (message : MarketStatusMessage) -- 320
  | seriesStatusMessage (message : SeriesStatusMessage) -- 321
  | commodityStatusMessage (message : CommodityStatusMessage) -- 322
  | tradeStatisticsMessage (message : TradeStatisticsMessage) -- 360
  deriving DecidableEq, Repr

namespace Payload

/-- The Msg Type each message is sent under -/
def tag : Payload → BitVec 16
  | .aggregateOrderBookUpdateMessage _ => 353
  | .calculatedOpeningPriceMessage _ => 364
  | .sequenceReset _ => 100
  | .disasterRecoverySignalMessage _ => 105
  | .marketAlertMessage _ => 323
  | .openInterestMessage _ => 366
  | .quoteRequest _ => 336
  | .commodityDefinitionMessage _ => 301
  | .classDefinitionMessage _ => 302
  | .seriesDefinitionBaseMessage _ => 303
  | .seriesDefinitionExtendedMessage _ => 304
  | .combinationDefinitionMessage _ => 305
  | .refreshComplete _ => 203
  | .logon _ => 101
  | .logonResponse _ => 102
  | .retransmissionRequest _ => 201
  | .retransmissionResponse _ => 202
  | .marketStatusMessage _ => 320
  | .seriesStatusMessage _ => 321
  | .commodityStatusMessage _ => 322
  | .tradeStatisticsMessage _ => 360

def encode : Payload → List UInt8
  | .aggregateOrderBookUpdateMessage message => AggregateOrderBookUpdateMessage.encode message
  | .calculatedOpeningPriceMessage message => CalculatedOpeningPriceMessage.encode message
  | .sequenceReset message => SequenceReset.encode message
  | .disasterRecoverySignalMessage message => DisasterRecoverySignalMessage.encode message
  | .marketAlertMessage message => MarketAlertMessage.encode message
  | .openInterestMessage message => OpenInterestMessage.encode message
  | .quoteRequest message => QuoteRequest.encode message
  | .commodityDefinitionMessage message => CommodityDefinitionMessage.encode message
  | .classDefinitionMessage message => ClassDefinitionMessage.encode message
  | .seriesDefinitionBaseMessage message => SeriesDefinitionBaseMessage.encode message
  | .seriesDefinitionExtendedMessage message => SeriesDefinitionExtendedMessage.encode message
  | .combinationDefinitionMessage message => CombinationDefinitionMessage.encode message
  | .refreshComplete message => RefreshComplete.encode message
  | .logon message => Logon.encode message
  | .logonResponse message => LogonResponse.encode message
  | .retransmissionRequest message => RetransmissionRequest.encode message
  | .retransmissionResponse message => RetransmissionResponse.encode message
  | .marketStatusMessage message => MarketStatusMessage.encode message
  | .seriesStatusMessage message => SeriesStatusMessage.encode message
  | .commodityStatusMessage message => CommodityStatusMessage.encode message
  | .tradeStatisticsMessage message => TradeStatisticsMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 81928 := by
  cases message with
  | aggregateOrderBookUpdateMessage inner =>
    have bound_inner := AggregateOrderBookUpdateMessage.encode_length_le inner
    simp only [encode]
    omega
  | calculatedOpeningPriceMessage inner =>
    simp only [encode, CalculatedOpeningPriceMessage.encode_length]
    omega
  | sequenceReset inner =>
    simp only [encode, SequenceReset.encode_length]
    omega
  | disasterRecoverySignalMessage inner =>
    simp only [encode, DisasterRecoverySignalMessage.encode_length]
    omega
  | marketAlertMessage inner =>
    have bound_inner := MarketAlertMessage.encode_length_le inner
    simp only [encode]
    omega
  | openInterestMessage inner =>
    simp only [encode, OpenInterestMessage.encode_length]
    omega
  | quoteRequest inner =>
    simp only [encode, QuoteRequest.encode_length]
    omega
  | commodityDefinitionMessage inner =>
    simp only [encode, CommodityDefinitionMessage.encode_length]
    omega
  | classDefinitionMessage inner =>
    simp only [encode, ClassDefinitionMessage.encode_length]
    omega
  | seriesDefinitionBaseMessage inner =>
    simp only [encode, SeriesDefinitionBaseMessage.encode_length]
    omega
  | seriesDefinitionExtendedMessage inner =>
    simp only [encode, SeriesDefinitionExtendedMessage.encode_length]
    omega
  | combinationDefinitionMessage inner =>
    simp only [encode, CombinationDefinitionMessage.encode_length]
    omega
  | refreshComplete inner =>
    simp only [encode, RefreshComplete.encode_length]
    omega
  | logon inner =>
    simp only [encode, Logon.encode_length]
    omega
  | logonResponse inner =>
    simp only [encode, LogonResponse.encode_length]
    omega
  | retransmissionRequest inner =>
    simp only [encode, RetransmissionRequest.encode_length]
    omega
  | retransmissionResponse inner =>
    simp only [encode, RetransmissionResponse.encode_length]
    omega
  | marketStatusMessage inner =>
    simp only [encode, MarketStatusMessage.encode_length]
    omega
  | seriesStatusMessage inner =>
    simp only [encode, SeriesStatusMessage.encode_length]
    omega
  | commodityStatusMessage inner =>
    simp only [encode, CommodityStatusMessage.encode_length]
    omega
  | tradeStatisticsMessage inner =>
    simp only [encode, TradeStatisticsMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 353 then (AggregateOrderBookUpdateMessage.decode bytes).map fun (message, rest) => (.aggregateOrderBookUpdateMessage message, rest)
  else if tag = 364 then (CalculatedOpeningPriceMessage.decode bytes).map fun (message, rest) => (.calculatedOpeningPriceMessage message, rest)
  else if tag = 100 then (SequenceReset.decode bytes).map fun (message, rest) => (.sequenceReset message, rest)
  else if tag = 105 then (DisasterRecoverySignalMessage.decode bytes).map fun (message, rest) => (.disasterRecoverySignalMessage message, rest)
  else if tag = 323 then (MarketAlertMessage.decode bytes).map fun (message, rest) => (.marketAlertMessage message, rest)
  else if tag = 366 then (OpenInterestMessage.decode bytes).map fun (message, rest) => (.openInterestMessage message, rest)
  else if tag = 336 then (QuoteRequest.decode bytes).map fun (message, rest) => (.quoteRequest message, rest)
  else if tag = 301 then (CommodityDefinitionMessage.decode bytes).map fun (message, rest) => (.commodityDefinitionMessage message, rest)
  else if tag = 302 then (ClassDefinitionMessage.decode bytes).map fun (message, rest) => (.classDefinitionMessage message, rest)
  else if tag = 303 then (SeriesDefinitionBaseMessage.decode bytes).map fun (message, rest) => (.seriesDefinitionBaseMessage message, rest)
  else if tag = 304 then (SeriesDefinitionExtendedMessage.decode bytes).map fun (message, rest) => (.seriesDefinitionExtendedMessage message, rest)
  else if tag = 305 then (CombinationDefinitionMessage.decode bytes).map fun (message, rest) => (.combinationDefinitionMessage message, rest)
  else if tag = 203 then (RefreshComplete.decode bytes).map fun (message, rest) => (.refreshComplete message, rest)
  else if tag = 101 then (Logon.decode bytes).map fun (message, rest) => (.logon message, rest)
  else if tag = 102 then (LogonResponse.decode bytes).map fun (message, rest) => (.logonResponse message, rest)
  else if tag = 201 then (RetransmissionRequest.decode bytes).map fun (message, rest) => (.retransmissionRequest message, rest)
  else if tag = 202 then (RetransmissionResponse.decode bytes).map fun (message, rest) => (.retransmissionResponse message, rest)
  else if tag = 320 then (MarketStatusMessage.decode bytes).map fun (message, rest) => (.marketStatusMessage message, rest)
  else if tag = 321 then (SeriesStatusMessage.decode bytes).map fun (message, rest) => (.seriesStatusMessage message, rest)
  else if tag = 322 then (CommodityStatusMessage.decode bytes).map fun (message, rest) => (.commodityStatusMessage message, rest)
  else if tag = 360 then (TradeStatisticsMessage.decode bytes).map fun (message, rest) => (.tradeStatisticsMessage message, rest)
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

/-- Size rule: Msg Size counts the bytes after it plus 2, so it is written from the body; the body has no bound the prefix must fit, so it is read by its content and the prefix is not checked -/
def encode (message : Message) : List UInt8 :=
  encodeUIntLE 2 (BitVec.ofNat (8 * 2) ((encodeBody message).length + 2)) ++ encodeBody message

def decode (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (_, bytes) ← decodeUIntLE 2 bytes
  decodeBody bytes

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  exact decodeBody_encodeBody message rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]
  omega

end Message

/-- Message Buffer -/
structure MessageBuffer (msgCount : BitVec 8) where
  message : Exact msgCount.toNat Message
  deriving DecidableEq, Repr

namespace MessageBuffer

def encode {msgCount : BitVec 8} (message : MessageBuffer msgCount) : List UInt8 :=
  encodeMany Message.encode message.message.val

def decode (msgCount : BitVec 8) (bytes : List UInt8) : Option (MessageBuffer msgCount × List UInt8) := do
  let (message_, bytes) ← decodeMany Message.decode msgCount.toNat bytes
  if fits_message : message_.length = msgCount.toNat then
    pure ({ message := ⟨message_, fits_message⟩ }, bytes)
  else none

@[simp] theorem decode_encode (msgCount : BitVec 8) (message : MessageBuffer msgCount) (rest : List UInt8) :
    decode msgCount (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeMany_exact msgCount.toNat Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_eq]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (msgCount : BitVec 8) (message : MessageBuffer msgCount) : decode msgCount (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode msgCount message []

end MessageBuffer

/-- Message Buffer -/
structure MessageBufferZlib where
  payload : List UInt8
  deriving DecidableEq, Repr

namespace MessageBufferZlib

def encode (message : MessageBufferZlib) : List UInt8 :=
  encodeMany Byte.encode message.payload

def decode (bytes : List UInt8) : Option MessageBufferZlib := do
  let payload ← decodeAll Byte.decode bytes.length bytes
  pure { payload }

theorem decode_encode (message : MessageBufferZlib) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany Byte.encode Byte.decode Byte.decode_encode Byte.encode_length_pos message.payload _ (encodeMany_length_ge Byte.encode Byte.encode_length_pos message.payload), some_bind]
  rfl

end MessageBufferZlib

/-- The Message Buffer, as bytes when Compression Mode says it was Zlib transformed and as it lies when it says it was not -/
inductive MessageBufferBody (msgCount : BitVec 8) where
  | zlib (tag : { v : BitVec 8 // v = 1 }) (message : MessageBufferZlib) -- tag = 1
  | plain (tag : { v : BitVec 8 // ¬ (v = 1) }) (message : MessageBuffer msgCount) -- every other value
  deriving DecidableEq, Repr

namespace MessageBufferBody

/-- The Compression Mode each body is read by -/
def tag {msgCount : BitVec 8} : MessageBufferBody msgCount → BitVec 8
  | .zlib tag _ => tag.val
  | .plain tag _ => tag.val

def encode {msgCount : BitVec 8} : MessageBufferBody msgCount → List UInt8
  | .zlib _ message => MessageBufferZlib.encode message
  | .plain _ message => MessageBuffer.encode message

/-- Decoded from the whole of what holds it: a body that reads to its end takes it all, any other must leave nothing -/
def decode (msgCount : BitVec 8) (tag : BitVec 8) (bytes : List UInt8) : Option (MessageBufferBody msgCount) :=
  if h : tag = 1 then (MessageBufferZlib.decode bytes).map fun message => .zlib ⟨tag, h⟩ message
  else (MessageBuffer.decode msgCount bytes).bind fun (message, rest) => if rest.isEmpty then some (.plain ⟨tag, h⟩ message) else none

theorem decode_encode (msgCount : BitVec 8) (message : MessageBufferBody msgCount) :
    decode msgCount (tag message) (encode message) = some message := by
  cases message with
  | zlib t m =>
    obtain ⟨v, h⟩ := t
    simp only [tag, encode, decode, h, reduceDIte, MessageBufferZlib.decode_encode, Option.map_some]
  | plain t m =>
    obtain ⟨v, h⟩ := t
    simp only [tag, encode, decode, h, reduceDIte, MessageBuffer.decode_encode_nil]
    rfl

end MessageBufferBody

/-- Packet -/
structure Packet where
  pktSize : BitVec 16
  msgCount : BitVec 8
  seqNum : BitVec 32
  sendTime : BitVec 64
  messageBuffer : MessageBufferBody msgCount
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUIntLE 2 message.pktSize
    ++ (encodeUInt 1 message.msgCount
    ++ (encodeUInt 1 (MessageBufferBody.tag message.messageBuffer)
    ++ (encodeUIntLE 4 message.seqNum
    ++ (encodeUIntLE 8 message.sendTime
    ++ (MessageBufferBody.encode message.messageBuffer)))))

def decode (bytes : List UInt8) : Option Packet := do
  let (pktSize, bytes) ← decodeUIntLE 2 bytes
  let (msgCount, bytes) ← decodeUInt 1 bytes
  let (compressionMode, bytes) ← decodeUInt 1 bytes
  let (seqNum, bytes) ← decodeUIntLE 4 bytes
  let (sendTime, bytes) ← decodeUIntLE 8 bytes
  let messageBuffer ← MessageBufferBody.decode msgCount compressionMode bytes
  pure { pktSize, msgCount, seqNum, sendTime, messageBuffer }

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [MessageBufferBody.decode_encode, some_bind]
  rfl

end Packet

end Omi.HkexHkexderivativesStandardretransOmdV147
