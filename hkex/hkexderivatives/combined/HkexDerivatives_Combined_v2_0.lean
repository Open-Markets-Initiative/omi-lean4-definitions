import Wire

/-!
# Hong Kong Exchanges and Clearing Orion Market Data Derivatives Combined v2.0

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

namespace Omi.HkexHkexderivativesCombinedOmdV20

/-- Source: one byte code -/
def Source.codes : List UInt8 :=
  [0x48]

inductive Source where
  | tradingSystem -- Trading System
  | unlisted (byte : { byte : UInt8 // byte ∉ Source.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Source

def toByte : Source → UInt8
  | .tradingSystem => 0x48
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : Source :=
  .tradingSystem

def ofByte (byte : UInt8) : Source :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Source) : ofByte value.toByte = value := by
  cases value with
  | tradingSystem => decide
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

/-- Underlying Type: one byte code -/
def UnderlyingType.codes : List UInt8 :=
  [0x53, 0x43, 0x49, 0x45, 0x41, 0x4D]

inductive UnderlyingType where
  | stock -- Stock
  | currency -- Currency
  | fixedIncome -- Fixed Income
  | energyPower -- Energy Power
  | commodity -- Commodity
  | metal -- Metal
  | unlisted (byte : { byte : UInt8 // byte ∉ UnderlyingType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace UnderlyingType

def toByte : UnderlyingType → UInt8
  | .stock => 0x53
  | .currency => 0x43
  | .fixedIncome => 0x49
  | .energyPower => 0x45
  | .commodity => 0x41
  | .metal => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : UnderlyingType :=
  if byte = 0x53 then .stock
  else if byte = 0x43 then .currency
  else if byte = 0x49 then .fixedIncome
  else if byte = 0x45 then .energyPower
  else if byte = 0x41 then .commodity
  else .metal

def ofByte (byte : UInt8) : UnderlyingType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : UnderlyingType) : ofByte value.toByte = value := by
  cases value with
  | stock => decide
  | currency => decide
  | fixedIncome => decide
  | energyPower => decide
  | commodity => decide
  | metal => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : UnderlyingType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (UnderlyingType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : UnderlyingType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : UnderlyingType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : UnderlyingType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end UnderlyingType

/-- Key Type: one byte code -/
def KeyType.codes : List UInt8 :=
  [0x30, 0x31]

inductive KeyType where
  | instrumentClass -- Instrument Class
  | comboClass -- Combo Class
  | unlisted (byte : { byte : UInt8 // byte ∉ KeyType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace KeyType

def toByte : KeyType → UInt8
  | .instrumentClass => 0x30
  | .comboClass => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : KeyType :=
  if byte = 0x30 then .instrumentClass
  else .comboClass

def ofByte (byte : UInt8) : KeyType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : KeyType) : ofByte value.toByte = value := by
  cases value with
  | instrumentClass => decide
  | comboClass => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : KeyType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (KeyType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : KeyType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : KeyType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : KeyType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end KeyType

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

/-- State Level: one byte code -/
def StateLevel.codes : List UInt8 :=
  [0x45, 0x4D, 0x54, 0x74, 0x43, 0x63]

inductive StateLevel where
  | exchange -- Exchange
  | market -- Market
  | instrumentType -- Instrument Type
  | comboType -- Combo Type
  | instrumentClass -- Instrument Class
  | comboClass -- Combo Class
  | unlisted (byte : { byte : UInt8 // byte ∉ StateLevel.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace StateLevel

def toByte : StateLevel → UInt8
  | .exchange => 0x45
  | .market => 0x4D
  | .instrumentType => 0x54
  | .comboType => 0x74
  | .instrumentClass => 0x43
  | .comboClass => 0x63
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : StateLevel :=
  if byte = 0x45 then .exchange
  else if byte = 0x4D then .market
  else if byte = 0x54 then .instrumentType
  else if byte = 0x74 then .comboType
  else if byte = 0x43 then .instrumentClass
  else .comboClass

def ofByte (byte : UInt8) : StateLevel :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : StateLevel) : ofByte value.toByte = value := by
  cases value with
  | exchange => decide
  | market => decide
  | instrumentType => decide
  | comboType => decide
  | instrumentClass => decide
  | comboClass => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : StateLevel) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (StateLevel × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : StateLevel) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : StateLevel) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : StateLevel) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end StateLevel

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

/-- Add Order: 32 bytes -/
structure AddOrder where
  orderbookId : BitVec 32
  orderId : BitVec 64
  price : BitVec 64
  quantity : BitVec 32
  side : BitVec 8
  lotType : BitVec 8
  orderType : BitVec 8
  orderBookPosition : BitVec 32
  filler1 : Alpha 1
  deriving DecidableEq, Repr

namespace AddOrder

def encode (message : AddOrder) : List UInt8 :=
  encodeUIntLE 4 message.orderbookId
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.lotType
    ++ (encodeUInt 1 message.orderType
    ++ (encodeUIntLE 4 message.orderBookPosition
    ++ (Alpha.encode message.filler1))))))))

def decode (bytes : List UInt8) : Option (AddOrder × List UInt8) := do
  let (orderbookId, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (lotType, bytes) ← decodeUInt 1 bytes
  let (orderType, bytes) ← decodeUInt 1 bytes
  let (orderBookPosition, bytes) ← decodeUIntLE 4 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  pure ({ orderbookId, orderId, price, quantity, side, lotType, orderType, orderBookPosition, filler1 }, bytes)

@[simp] theorem encode_length (message : AddOrder) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : AddOrder) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddOrder) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end AddOrder

/-- Aggregate Implied Order: 22 bytes -/
structure AggregateImpliedOrder where
  orderbookId : BitVec 32
  impliedPrice : BitVec 64
  impliedQuantity : BitVec 64
  side : BitVec 8
  filler1 : Alpha 1
  deriving DecidableEq, Repr

namespace AggregateImpliedOrder

def encode (message : AggregateImpliedOrder) : List UInt8 :=
  encodeUIntLE 4 message.orderbookId
    ++ (encodeUIntLE 8 message.impliedPrice
    ++ (encodeUIntLE 8 message.impliedQuantity
    ++ (encodeUInt 1 message.side
    ++ (Alpha.encode message.filler1))))

def decode (bytes : List UInt8) : Option (AggregateImpliedOrder × List UInt8) := do
  let (orderbookId, bytes) ← decodeUIntLE 4 bytes
  let (impliedPrice, bytes) ← decodeUIntLE 8 bytes
  let (impliedQuantity, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  pure ({ orderbookId, impliedPrice, impliedQuantity, side, filler1 }, bytes)

@[simp] theorem encode_length (message : AggregateImpliedOrder) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : AggregateImpliedOrder) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AggregateImpliedOrder) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end AggregateImpliedOrder

/-- Book Entry: 24 bytes -/
structure BookEntry where
  aggregateQuantity : BitVec 64
  price : BitVec 64
  numberOfOrders : BitVec 32
  side : BitVec 8
  filler1 : Alpha 1
  priceLevel : BitVec 8
  updateAction : BitVec 8
  deriving DecidableEq, Repr

namespace BookEntry

def encode (message : BookEntry) : List UInt8 :=
  encodeUIntLE 8 message.aggregateQuantity
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.numberOfOrders
    ++ (encodeUInt 1 message.side
    ++ (Alpha.encode message.filler1
    ++ (encodeUInt 1 message.priceLevel
    ++ (encodeUInt 1 message.updateAction))))))

def decode (bytes : List UInt8) : Option (BookEntry × List UInt8) := do
  let (aggregateQuantity, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (numberOfOrders, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (priceLevel, bytes) ← decodeUInt 1 bytes
  let (updateAction, bytes) ← decodeUInt 1 bytes
  pure ({ aggregateQuantity, price, numberOfOrders, side, filler1, priceLevel, updateAction }, bytes)

@[simp] theorem encode_length (message : BookEntry) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
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
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.bookEntry.val.length)
    ++ (encodeMany BookEntry.encode message.bookEntry.val)))

def decode (bytes : List UInt8) : Option (AggregateOrderBookUpdateMessage × List UInt8) := do
  let (orderbookId, bytes) ← decodeUIntLE 4 bytes
  let (filler3, bytes) ← Alpha.decode 3 bytes
  let (noEntries, bytes) ← decodeUInt 1 bytes
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
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length, encodeMany_length_const BookEntry.encode 24 BookEntry.encode_length]
  omega

@[simp] theorem decode_encode (message : AggregateOrderBookUpdateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 BookEntry.encode BookEntry.decode BookEntry.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.bookEntry.length_lt]
  rfl

end AggregateOrderBookUpdateMessage

/-- Calculated Opening Price Message: 24 bytes -/
structure CalculatedOpeningPriceMessage where
  orderbookId : BitVec 32
  calculatedOpeningPrice : BitVec 64
  filler4 : Alpha 4
  calculatedOpeningQuantity : BitVec 64
  deriving DecidableEq, Repr

namespace CalculatedOpeningPriceMessage

def encode (message : CalculatedOpeningPriceMessage) : List UInt8 :=
  encodeUIntLE 4 message.orderbookId
    ++ (encodeUIntLE 8 message.calculatedOpeningPrice
    ++ (Alpha.encode message.filler4
    ++ (encodeUIntLE 8 message.calculatedOpeningQuantity)))

def decode (bytes : List UInt8) : Option (CalculatedOpeningPriceMessage × List UInt8) := do
  let (orderbookId, bytes) ← decodeUIntLE 4 bytes
  let (calculatedOpeningPrice, bytes) ← decodeUIntLE 8 bytes
  let (filler4, bytes) ← Alpha.decode 4 bytes
  let (calculatedOpeningQuantity, bytes) ← decodeUIntLE 8 bytes
  pure ({ orderbookId, calculatedOpeningPrice, filler4, calculatedOpeningQuantity }, bytes)

@[simp] theorem encode_length (message : CalculatedOpeningPriceMessage) : (encode message).length = 24 := by
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

/-- Delete Order: 14 bytes -/
structure DeleteOrder where
  orderbookId : BitVec 32
  orderId : BitVec 64
  side : BitVec 8
  filler1 : Alpha 1
  deriving DecidableEq, Repr

namespace DeleteOrder

def encode (message : DeleteOrder) : List UInt8 :=
  encodeUIntLE 4 message.orderbookId
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUInt 1 message.side
    ++ (Alpha.encode message.filler1)))

def decode (bytes : List UInt8) : Option (DeleteOrder × List UInt8) := do
  let (orderbookId, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  pure ({ orderbookId, orderId, side, filler1 }, bytes)

@[simp] theorem encode_length (message : DeleteOrder) : (encode message).length = 14 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : DeleteOrder) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DeleteOrder) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end DeleteOrder

/-- Implied Volatility Message: 8 bytes -/
structure ImpliedVolatilityMessage where
  orderbookId : BitVec 32
  impliedVolatility : BitVec 32
  deriving DecidableEq, Repr

namespace ImpliedVolatilityMessage

def encode (message : ImpliedVolatilityMessage) : List UInt8 :=
  encodeUIntLE 4 message.orderbookId
    ++ (encodeUIntLE 4 message.impliedVolatility)

def decode (bytes : List UInt8) : Option (ImpliedVolatilityMessage × List UInt8) := do
  let (orderbookId, bytes) ← decodeUIntLE 4 bytes
  let (impliedVolatility, bytes) ← decodeUIntLE 4 bytes
  pure ({ orderbookId, impliedVolatility }, bytes)

@[simp] theorem encode_length (message : ImpliedVolatilityMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : ImpliedVolatilityMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ImpliedVolatilityMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ImpliedVolatilityMessage

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
  alertId : BitVec 64
  source : Source
  header : Alpha 320
  lastFragment : LastFragment
  priority : BitVec 8
  content : Bounded 1 ContentEntry
  deriving DecidableEq, Repr

namespace MarketAlertMessage

def encode (message : MarketAlertMessage) : List UInt8 :=
  encodeUIntLE 8 message.alertId
    ++ (Source.encode message.source
    ++ (Alpha.encode message.header
    ++ (LastFragment.encode message.lastFragment
    ++ (encodeUInt 1 message.priority
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.content.val.length)
    ++ (encodeMany ContentEntry.encode message.content.val))))))

def decode (bytes : List UInt8) : Option (MarketAlertMessage × List UInt8) := do
  let (alertId, bytes) ← decodeUIntLE 8 bytes
  let (source, bytes) ← Source.decode bytes
  let (header, bytes) ← Alpha.decode 320 bytes
  let (lastFragment, bytes) ← LastFragment.decode bytes
  let (priority, bytes) ← decodeUInt 1 bytes
  let (noofLines, bytes) ← decodeUInt 1 bytes
  let (content_, bytes) ← decodeMany ContentEntry.decode noofLines.toNat bytes
  if fits_content : content_.length < 256 ^ 1 then
    pure ({ alertId, source, header, lastFragment, priority, content := ⟨content_, fits_content⟩ }, bytes)
  else none

theorem encode_length_pos (message : MarketAlertMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MarketAlertMessage) : (encode message).length ≤ 81932 := by
  have bound_content := message.content.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Source.encode_length, Alpha.encode_length, LastFragment.encode_length, encodeUInt_length, encodeMany_length_const ContentEntry.encode 320 ContentEntry.encode_length]
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
  rw [List.append_assoc, LastFragment.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 ContentEntry.encode ContentEntry.decode ContentEntry.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.content.length_lt]
  rfl

end MarketAlertMessage

/-- Modify Order: 32 bytes -/
structure ModifyOrder where
  orderbookId : BitVec 32
  orderId : BitVec 64
  price : BitVec 64
  quantity : BitVec 32
  side : BitVec 8
  filler2 : Alpha 2
  orderType : BitVec 8
  orderBookPosition : BitVec 32
  deriving DecidableEq, Repr

namespace ModifyOrder

def encode (message : ModifyOrder) : List UInt8 :=
  encodeUIntLE 4 message.orderbookId
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUInt 1 message.side
    ++ (Alpha.encode message.filler2
    ++ (encodeUInt 1 message.orderType
    ++ (encodeUIntLE 4 message.orderBookPosition)))))))

def decode (bytes : List UInt8) : Option (ModifyOrder × List UInt8) := do
  let (orderbookId, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (filler2, bytes) ← Alpha.decode 2 bytes
  let (orderType, bytes) ← decodeUInt 1 bytes
  let (orderBookPosition, bytes) ← decodeUIntLE 4 bytes
  pure ({ orderbookId, orderId, price, quantity, side, filler2, orderType, orderBookPosition }, bytes)

@[simp] theorem encode_length (message : ModifyOrder) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : ModifyOrder) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ModifyOrder) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ModifyOrder

/-- Open Interest Message: 24 bytes -/
structure OpenInterestMessage where
  dayIndicator : BitVec 16
  filler6 : Alpha 6
  orderbookId : BitVec 32
  settlementPrice : BitVec 32
  grossOi : BitVec 32
  netOi : BitVec 32
  deriving DecidableEq, Repr

namespace OpenInterestMessage

def encode (message : OpenInterestMessage) : List UInt8 :=
  encodeUIntLE 2 message.dayIndicator
    ++ (Alpha.encode message.filler6
    ++ (encodeUIntLE 4 message.orderbookId
    ++ (encodeUIntLE 4 message.settlementPrice
    ++ (encodeUIntLE 4 message.grossOi
    ++ (encodeUIntLE 4 message.netOi)))))

def decode (bytes : List UInt8) : Option (OpenInterestMessage × List UInt8) := do
  let (dayIndicator, bytes) ← decodeUIntLE 2 bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (orderbookId, bytes) ← decodeUIntLE 4 bytes
  let (settlementPrice, bytes) ← decodeUIntLE 4 bytes
  let (grossOi, bytes) ← decodeUIntLE 4 bytes
  let (netOi, bytes) ← decodeUIntLE 4 bytes
  pure ({ dayIndicator, filler6, orderbookId, settlementPrice, grossOi, netOi }, bytes)

@[simp] theorem encode_length (message : OpenInterestMessage) : (encode message).length = 24 := by
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OpenInterestMessage

/-- Orderbook Clear Message: 4 bytes -/
structure OrderbookClearMessage where
  orderbookId : BitVec 32
  deriving DecidableEq, Repr

namespace OrderbookClearMessage

def encode (message : OrderbookClearMessage) : List UInt8 :=
  encodeUIntLE 4 message.orderbookId

def decode (bytes : List UInt8) : Option (OrderbookClearMessage × List UInt8) := do
  let (orderbookId, bytes) ← decodeUIntLE 4 bytes
  pure ({ orderbookId }, bytes)

@[simp] theorem encode_length (message : OrderbookClearMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : OrderbookClearMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderbookClearMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderbookClearMessage

/-- Quote Request: 12 bytes -/
structure QuoteRequest where
  orderbookId : BitVec 32
  quoteQuantity : BitVec 32
  bidAskFlag : BitVec 8
  filler3 : Alpha 3
  deriving DecidableEq, Repr

namespace QuoteRequest

def encode (message : QuoteRequest) : List UInt8 :=
  encodeUIntLE 4 message.orderbookId
    ++ (encodeUIntLE 4 message.quoteQuantity
    ++ (encodeUInt 1 message.bidAskFlag
    ++ (Alpha.encode message.filler3)))

def decode (bytes : List UInt8) : Option (QuoteRequest × List UInt8) := do
  let (orderbookId, bytes) ← decodeUIntLE 4 bytes
  let (quoteQuantity, bytes) ← decodeUIntLE 4 bytes
  let (bidAskFlag, bytes) ← decodeUInt 1 bytes
  let (filler3, bytes) ← Alpha.decode 3 bytes
  pure ({ orderbookId, quoteQuantity, bidAskFlag, filler3 }, bytes)

@[simp] theorem encode_length (message : QuoteRequest) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end QuoteRequest

/-- Commodity Definition: 82 bytes -/
structure CommodityDefinition where
  commodityCode : BitVec 32
  commodityName : Alpha 40
  commodityId : Alpha 6
  underlyingCode : Alpha 20
  underlyingType : UnderlyingType
  decimalInUnderlyingPrice : BitVec 16
  baseCurrency : Alpha 3
  effectiveTomorrow : BitVec 8
  filler5 : Alpha 5
  deriving DecidableEq, Repr

namespace CommodityDefinition

def encode (message : CommodityDefinition) : List UInt8 :=
  encodeUIntLE 4 message.commodityCode
    ++ (Alpha.encode message.commodityName
    ++ (Alpha.encode message.commodityId
    ++ (Alpha.encode message.underlyingCode
    ++ (UnderlyingType.encode message.underlyingType
    ++ (encodeUIntLE 2 message.decimalInUnderlyingPrice
    ++ (Alpha.encode message.baseCurrency
    ++ (encodeUInt 1 message.effectiveTomorrow
    ++ (Alpha.encode message.filler5))))))))

def decode (bytes : List UInt8) : Option (CommodityDefinition × List UInt8) := do
  let (commodityCode, bytes) ← decodeUIntLE 4 bytes
  let (commodityName, bytes) ← Alpha.decode 40 bytes
  let (commodityId, bytes) ← Alpha.decode 6 bytes
  let (underlyingCode, bytes) ← Alpha.decode 20 bytes
  let (underlyingType, bytes) ← UnderlyingType.decode bytes
  let (decimalInUnderlyingPrice, bytes) ← decodeUIntLE 2 bytes
  let (baseCurrency, bytes) ← Alpha.decode 3 bytes
  let (effectiveTomorrow, bytes) ← decodeUInt 1 bytes
  let (filler5, bytes) ← Alpha.decode 5 bytes
  pure ({ commodityCode, commodityName, commodityId, underlyingCode, underlyingType, decimalInUnderlyingPrice, baseCurrency, effectiveTomorrow, filler5 }, bytes)

@[simp] theorem encode_length (message : CommodityDefinition) : (encode message).length = 82 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, UnderlyingType.encode_length, encodeUInt_length]

theorem encode_length_pos (message : CommodityDefinition) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CommodityDefinition) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, UnderlyingType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end CommodityDefinition

/-- Class Definition: 116 bytes -/
structure ClassDefinition where
  instrumentClassId : Alpha 14
  instrumentClassKey : BitVec 32
  keyType : KeyType
  instrumentClassName : Alpha 40
  exchange : BitVec 16
  market : BitVec 16
  instrumentGroup : BitVec 16
  commodityCode : BitVec 32
  instrumentTypeId : Alpha 8
  instrumentTypeKey : BitVec 32
  filler3 : Alpha 3
  priceQuotationFactor : BitVec 32
  contractSize : BitVec 32
  decimalInContractSize : BitVec 16
  decimalInStrikePrice : BitVec 16
  decimalInPrice : BitVec 16
  tickSize : BitVec 64
  tradable : BitVec 8
  baseCurrency : Alpha 3
  settlementCurrencyId : Alpha 3
  effectiveTomorrow : BitVec 8
  filler2 : Alpha 2
  deriving DecidableEq, Repr

namespace ClassDefinition

def encode (message : ClassDefinition) : List UInt8 :=
  Alpha.encode message.instrumentClassId
    ++ (encodeUIntLE 4 message.instrumentClassKey
    ++ (KeyType.encode message.keyType
    ++ (Alpha.encode message.instrumentClassName
    ++ (encodeUIntLE 2 message.exchange
    ++ (encodeUIntLE 2 message.market
    ++ (encodeUIntLE 2 message.instrumentGroup
    ++ (encodeUIntLE 4 message.commodityCode
    ++ (Alpha.encode message.instrumentTypeId
    ++ (encodeUIntLE 4 message.instrumentTypeKey
    ++ (Alpha.encode message.filler3
    ++ (encodeUIntLE 4 message.priceQuotationFactor
    ++ (encodeUIntLE 4 message.contractSize
    ++ (encodeUIntLE 2 message.decimalInContractSize
    ++ (encodeUIntLE 2 message.decimalInStrikePrice
    ++ (encodeUIntLE 2 message.decimalInPrice
    ++ (encodeUIntLE 8 message.tickSize
    ++ (encodeUInt 1 message.tradable
    ++ (Alpha.encode message.baseCurrency
    ++ (Alpha.encode message.settlementCurrencyId
    ++ (encodeUInt 1 message.effectiveTomorrow
    ++ (Alpha.encode message.filler2)))))))))))))))))))))

def decode (bytes : List UInt8) : Option (ClassDefinition × List UInt8) := do
  let (instrumentClassId, bytes) ← Alpha.decode 14 bytes
  let (instrumentClassKey, bytes) ← decodeUIntLE 4 bytes
  let (keyType, bytes) ← KeyType.decode bytes
  let (instrumentClassName, bytes) ← Alpha.decode 40 bytes
  let (exchange, bytes) ← decodeUIntLE 2 bytes
  let (market, bytes) ← decodeUIntLE 2 bytes
  let (instrumentGroup, bytes) ← decodeUIntLE 2 bytes
  let (commodityCode, bytes) ← decodeUIntLE 4 bytes
  let (instrumentTypeId, bytes) ← Alpha.decode 8 bytes
  let (instrumentTypeKey, bytes) ← decodeUIntLE 4 bytes
  let (filler3, bytes) ← Alpha.decode 3 bytes
  let (priceQuotationFactor, bytes) ← decodeUIntLE 4 bytes
  let (contractSize, bytes) ← decodeUIntLE 4 bytes
  let (decimalInContractSize, bytes) ← decodeUIntLE 2 bytes
  let (decimalInStrikePrice, bytes) ← decodeUIntLE 2 bytes
  let (decimalInPrice, bytes) ← decodeUIntLE 2 bytes
  let (tickSize, bytes) ← decodeUIntLE 8 bytes
  let (tradable, bytes) ← decodeUInt 1 bytes
  let (baseCurrency, bytes) ← Alpha.decode 3 bytes
  let (settlementCurrencyId, bytes) ← Alpha.decode 3 bytes
  let (effectiveTomorrow, bytes) ← decodeUInt 1 bytes
  let (filler2, bytes) ← Alpha.decode 2 bytes
  pure ({ instrumentClassId, instrumentClassKey, keyType, instrumentClassName, exchange, market, instrumentGroup, commodityCode, instrumentTypeId, instrumentTypeKey, filler3, priceQuotationFactor, contractSize, decimalInContractSize, decimalInStrikePrice, decimalInPrice, tickSize, tradable, baseCurrency, settlementCurrencyId, effectiveTomorrow, filler2 }, bytes)

@[simp] theorem encode_length (message : ClassDefinition) : (encode message).length = 116 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length, KeyType.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ClassDefinition) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ClassDefinition) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, KeyType.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ClassDefinition

/-- Instrument Definition: 116 bytes -/
structure InstrumentDefinition where
  orderbookId : BitVec 32
  symbol : Alpha 32
  instrumentClassKey : BitVec 32
  market : BitVec 16
  instrumentGroup : BitVec 16
  modifier : BitVec 16
  commodityCode : BitVec 32
  lastTradingDate : BitVec 32
  lastTradingTime : BitVec 64
  strikePrice : BitVec 64
  effectiveLastTradingDate : BitVec 32
  firstTradingDate : BitVec 32
  firstTradingTime : BitVec 64
  filler3 : Alpha 3
  instrumentStatusCode : BitVec 8
  instrumentContractSize : BitVec 32
  instrumentPriceQuotationFactor : BitVec 32
  numberOfLegs : BitVec 8
  vcmFlag : BitVec 8
  isinCode : Alpha 12
  effectiveTomorrow : BitVec 8
  secondFiller3 : Alpha 3
  deriving DecidableEq, Repr

namespace InstrumentDefinition

def encode (message : InstrumentDefinition) : List UInt8 :=
  encodeUIntLE 4 message.orderbookId
    ++ (Alpha.encode message.symbol
    ++ (encodeUIntLE 4 message.instrumentClassKey
    ++ (encodeUIntLE 2 message.market
    ++ (encodeUIntLE 2 message.instrumentGroup
    ++ (encodeUIntLE 2 message.modifier
    ++ (encodeUIntLE 4 message.commodityCode
    ++ (encodeUIntLE 4 message.lastTradingDate
    ++ (encodeUIntLE 8 message.lastTradingTime
    ++ (encodeUIntLE 8 message.strikePrice
    ++ (encodeUIntLE 4 message.effectiveLastTradingDate
    ++ (encodeUIntLE 4 message.firstTradingDate
    ++ (encodeUIntLE 8 message.firstTradingTime
    ++ (Alpha.encode message.filler3
    ++ (encodeUInt 1 message.instrumentStatusCode
    ++ (encodeUIntLE 4 message.instrumentContractSize
    ++ (encodeUIntLE 4 message.instrumentPriceQuotationFactor
    ++ (encodeUInt 1 message.numberOfLegs
    ++ (encodeUInt 1 message.vcmFlag
    ++ (Alpha.encode message.isinCode
    ++ (encodeUInt 1 message.effectiveTomorrow
    ++ (Alpha.encode message.secondFiller3)))))))))))))))))))))

def decode (bytes : List UInt8) : Option (InstrumentDefinition × List UInt8) := do
  let (orderbookId, bytes) ← decodeUIntLE 4 bytes
  let (symbol, bytes) ← Alpha.decode 32 bytes
  let (instrumentClassKey, bytes) ← decodeUIntLE 4 bytes
  let (market, bytes) ← decodeUIntLE 2 bytes
  let (instrumentGroup, bytes) ← decodeUIntLE 2 bytes
  let (modifier, bytes) ← decodeUIntLE 2 bytes
  let (commodityCode, bytes) ← decodeUIntLE 4 bytes
  let (lastTradingDate, bytes) ← decodeUIntLE 4 bytes
  let (lastTradingTime, bytes) ← decodeUIntLE 8 bytes
  let (strikePrice, bytes) ← decodeUIntLE 8 bytes
  let (effectiveLastTradingDate, bytes) ← decodeUIntLE 4 bytes
  let (firstTradingDate, bytes) ← decodeUIntLE 4 bytes
  let (firstTradingTime, bytes) ← decodeUIntLE 8 bytes
  let (filler3, bytes) ← Alpha.decode 3 bytes
  let (instrumentStatusCode, bytes) ← decodeUInt 1 bytes
  let (instrumentContractSize, bytes) ← decodeUIntLE 4 bytes
  let (instrumentPriceQuotationFactor, bytes) ← decodeUIntLE 4 bytes
  let (numberOfLegs, bytes) ← decodeUInt 1 bytes
  let (vcmFlag, bytes) ← decodeUInt 1 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (effectiveTomorrow, bytes) ← decodeUInt 1 bytes
  let (secondFiller3, bytes) ← Alpha.decode 3 bytes
  pure ({ orderbookId, symbol, instrumentClassKey, market, instrumentGroup, modifier, commodityCode, lastTradingDate, lastTradingTime, strikePrice, effectiveLastTradingDate, firstTradingDate, firstTradingTime, filler3, instrumentStatusCode, instrumentContractSize, instrumentPriceQuotationFactor, numberOfLegs, vcmFlag, isinCode, effectiveTomorrow, secondFiller3 }, bytes)

@[simp] theorem encode_length (message : InstrumentDefinition) : (encode message).length = 116 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : InstrumentDefinition) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentDefinition) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end InstrumentDefinition

/-- Combination Definition: 16 bytes -/
structure CombinationDefinition where
  comboOrderbookId : BitVec 32
  legOrderbookId : BitVec 32
  filler3 : Alpha 3
  legSide : LegSide
  legRatio : BitVec 32
  deriving DecidableEq, Repr

namespace CombinationDefinition

def encode (message : CombinationDefinition) : List UInt8 :=
  encodeUIntLE 4 message.comboOrderbookId
    ++ (encodeUIntLE 4 message.legOrderbookId
    ++ (Alpha.encode message.filler3
    ++ (LegSide.encode message.legSide
    ++ (encodeUIntLE 4 message.legRatio))))

def decode (bytes : List UInt8) : Option (CombinationDefinition × List UInt8) := do
  let (comboOrderbookId, bytes) ← decodeUIntLE 4 bytes
  let (legOrderbookId, bytes) ← decodeUIntLE 4 bytes
  let (filler3, bytes) ← Alpha.decode 3 bytes
  let (legSide, bytes) ← LegSide.decode bytes
  let (legRatio, bytes) ← decodeUIntLE 4 bytes
  pure ({ comboOrderbookId, legOrderbookId, filler3, legSide, legRatio }, bytes)

@[simp] theorem encode_length (message : CombinationDefinition) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, LegSide.encode_length]

theorem encode_length_pos (message : CombinationDefinition) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CombinationDefinition) (rest : List UInt8) :
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

end CombinationDefinition

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

/-- Market Status: 36 bytes -/
structure MarketStatus where
  stateLevel : StateLevel
  statusMarket : BitVec 32
  instrumentTypeKey : BitVec 32
  instrumentClassKey : BitVec 32
  filler4 : Alpha 4
  actualStartTime : BitVec 64
  plannedStartTime : BitVec 64
  state : BitVec 16
  filler1 : Alpha 1
  deriving DecidableEq, Repr

namespace MarketStatus

def encode (message : MarketStatus) : List UInt8 :=
  StateLevel.encode message.stateLevel
    ++ (encodeUIntLE 4 message.statusMarket
    ++ (encodeUIntLE 4 message.instrumentTypeKey
    ++ (encodeUIntLE 4 message.instrumentClassKey
    ++ (Alpha.encode message.filler4
    ++ (encodeUIntLE 8 message.actualStartTime
    ++ (encodeUIntLE 8 message.plannedStartTime
    ++ (encodeUIntLE 2 message.state
    ++ (Alpha.encode message.filler1))))))))

def decode (bytes : List UInt8) : Option (MarketStatus × List UInt8) := do
  let (stateLevel, bytes) ← StateLevel.decode bytes
  let (statusMarket, bytes) ← decodeUIntLE 4 bytes
  let (instrumentTypeKey, bytes) ← decodeUIntLE 4 bytes
  let (instrumentClassKey, bytes) ← decodeUIntLE 4 bytes
  let (filler4, bytes) ← Alpha.decode 4 bytes
  let (actualStartTime, bytes) ← decodeUIntLE 8 bytes
  let (plannedStartTime, bytes) ← decodeUIntLE 8 bytes
  let (state, bytes) ← decodeUIntLE 2 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  pure ({ stateLevel, statusMarket, instrumentTypeKey, instrumentClassKey, filler4, actualStartTime, plannedStartTime, state, filler1 }, bytes)

@[simp] theorem encode_length (message : MarketStatus) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, StateLevel.encode_length, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : MarketStatus) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketStatus) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, StateLevel.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end MarketStatus

/-- Instrument Status: 8 bytes -/
structure InstrumentStatus where
  orderbookId : BitVec 32
  suspensionIndicator : BitVec 8
  instrumentStatusCode : BitVec 8
  filler2 : Alpha 2
  deriving DecidableEq, Repr

namespace InstrumentStatus

def encode (message : InstrumentStatus) : List UInt8 :=
  encodeUIntLE 4 message.orderbookId
    ++ (encodeUInt 1 message.suspensionIndicator
    ++ (encodeUInt 1 message.instrumentStatusCode
    ++ (Alpha.encode message.filler2)))

def decode (bytes : List UInt8) : Option (InstrumentStatus × List UInt8) := do
  let (orderbookId, bytes) ← decodeUIntLE 4 bytes
  let (suspensionIndicator, bytes) ← decodeUInt 1 bytes
  let (instrumentStatusCode, bytes) ← decodeUInt 1 bytes
  let (filler2, bytes) ← Alpha.decode 2 bytes
  pure ({ orderbookId, suspensionIndicator, instrumentStatusCode, filler2 }, bytes)

@[simp] theorem encode_length (message : InstrumentStatus) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : InstrumentStatus) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentStatus) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end InstrumentStatus

/-- Commodity And Class Status: 10 bytes -/
structure CommodityAndClassStatus where
  commodityCode : BitVec 32
  instrumentClassKey : BitVec 32
  suspended : Suspended
  filler1 : Alpha 1
  deriving DecidableEq, Repr

namespace CommodityAndClassStatus

def encode (message : CommodityAndClassStatus) : List UInt8 :=
  encodeUIntLE 4 message.commodityCode
    ++ (encodeUIntLE 4 message.instrumentClassKey
    ++ (Suspended.encode message.suspended
    ++ (Alpha.encode message.filler1)))

def decode (bytes : List UInt8) : Option (CommodityAndClassStatus × List UInt8) := do
  let (commodityCode, bytes) ← decodeUIntLE 4 bytes
  let (instrumentClassKey, bytes) ← decodeUIntLE 4 bytes
  let (suspended, bytes) ← Suspended.decode bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  pure ({ commodityCode, instrumentClassKey, suspended, filler1 }, bytes)

@[simp] theorem encode_length (message : CommodityAndClassStatus) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Suspended.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : CommodityAndClassStatus) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CommodityAndClassStatus) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Suspended.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end CommodityAndClassStatus

/-- Vcm Trigger: 46 bytes -/
structure VcmTrigger where
  orderbookId : BitVec 32
  coolingOffStartTime : BitVec 64
  coolingOffEndTime : BitVec 64
  vcmReferencePrice : BitVec 64
  vcmLowerPrice : BitVec 64
  vcmUpperPrice : BitVec 64
  filler2 : Alpha 2
  deriving DecidableEq, Repr

namespace VcmTrigger

def encode (message : VcmTrigger) : List UInt8 :=
  encodeUIntLE 4 message.orderbookId
    ++ (encodeUIntLE 8 message.coolingOffStartTime
    ++ (encodeUIntLE 8 message.coolingOffEndTime
    ++ (encodeUIntLE 8 message.vcmReferencePrice
    ++ (encodeUIntLE 8 message.vcmLowerPrice
    ++ (encodeUIntLE 8 message.vcmUpperPrice
    ++ (Alpha.encode message.filler2))))))

def decode (bytes : List UInt8) : Option (VcmTrigger × List UInt8) := do
  let (orderbookId, bytes) ← decodeUIntLE 4 bytes
  let (coolingOffStartTime, bytes) ← decodeUIntLE 8 bytes
  let (coolingOffEndTime, bytes) ← decodeUIntLE 8 bytes
  let (vcmReferencePrice, bytes) ← decodeUIntLE 8 bytes
  let (vcmLowerPrice, bytes) ← decodeUIntLE 8 bytes
  let (vcmUpperPrice, bytes) ← decodeUIntLE 8 bytes
  let (filler2, bytes) ← Alpha.decode 2 bytes
  pure ({ orderbookId, coolingOffStartTime, coolingOffEndTime, vcmReferencePrice, vcmLowerPrice, vcmUpperPrice, filler2 }, bytes)

@[simp] theorem encode_length (message : VcmTrigger) : (encode message).length = 46 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : VcmTrigger) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : VcmTrigger) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end VcmTrigger

/-- Vcm End: 20 bytes -/
structure VcmEnd where
  orderbookId : BitVec 32
  coolingOffStartTime : BitVec 64
  coolingOffEndTime : BitVec 64
  deriving DecidableEq, Repr

namespace VcmEnd

def encode (message : VcmEnd) : List UInt8 :=
  encodeUIntLE 4 message.orderbookId
    ++ (encodeUIntLE 8 message.coolingOffStartTime
    ++ (encodeUIntLE 8 message.coolingOffEndTime))

def decode (bytes : List UInt8) : Option (VcmEnd × List UInt8) := do
  let (orderbookId, bytes) ← decodeUIntLE 4 bytes
  let (coolingOffStartTime, bytes) ← decodeUIntLE 8 bytes
  let (coolingOffEndTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ orderbookId, coolingOffStartTime, coolingOffEndTime }, bytes)

@[simp] theorem encode_length (message : VcmEnd) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : VcmEnd) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : VcmEnd) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end VcmEnd

/-- Thm Trigger: 14 bytes -/
structure ThmTrigger where
  instrumentClassKey : BitVec 32
  filler10 : Alpha 10
  deriving DecidableEq, Repr

namespace ThmTrigger

def encode (message : ThmTrigger) : List UInt8 :=
  encodeUIntLE 4 message.instrumentClassKey
    ++ (Alpha.encode message.filler10)

def decode (bytes : List UInt8) : Option (ThmTrigger × List UInt8) := do
  let (instrumentClassKey, bytes) ← decodeUIntLE 4 bytes
  let (filler10, bytes) ← Alpha.decode 10 bytes
  pure ({ instrumentClassKey, filler10 }, bytes)

@[simp] theorem encode_length (message : ThmTrigger) : (encode message).length = 14 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : ThmTrigger) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ThmTrigger) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ThmTrigger

/-- Trade: 54 bytes -/
structure Trade where
  orderbookId : BitVec 32
  orderId : BitVec 64
  price : BitVec 64
  tradeId : BitVec 64
  matchId : BitVec 64
  side : BitVec 8
  tradeSubType : BitVec 8
  tradeCondition : BitVec 8
  filler3 : Alpha 3
  quantity : BitVec 32
  tradeTime : BitVec 64
  deriving DecidableEq, Repr

namespace Trade

def encode (message : Trade) : List UInt8 :=
  encodeUIntLE 4 message.orderbookId
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.tradeId
    ++ (encodeUIntLE 8 message.matchId
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.tradeSubType
    ++ (encodeUInt 1 message.tradeCondition
    ++ (Alpha.encode message.filler3
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 8 message.tradeTime))))))))))

def decode (bytes : List UInt8) : Option (Trade × List UInt8) := do
  let (orderbookId, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (tradeId, bytes) ← decodeUIntLE 8 bytes
  let (matchId, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (tradeSubType, bytes) ← decodeUInt 1 bytes
  let (tradeCondition, bytes) ← decodeUInt 1 bytes
  let (filler3, bytes) ← Alpha.decode 3 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (tradeTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ orderbookId, orderId, price, tradeId, matchId, side, tradeSubType, tradeCondition, filler3, quantity, tradeTime }, bytes)

@[simp] theorem encode_length (message : Trade) : (encode message).length = 54 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : Trade) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Trade) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end Trade

/-- Trade Amendment Message: 36 bytes -/
structure TradeAmendmentMessage where
  orderbookId : BitVec 32
  tradeId : BitVec 64
  price : BitVec 64
  quantity : BitVec 32
  amendmentExecutionTime : BitVec 64
  tradeState : BitVec 8
  filler3 : Alpha 3
  deriving DecidableEq, Repr

namespace TradeAmendmentMessage

def encode (message : TradeAmendmentMessage) : List UInt8 :=
  encodeUIntLE 4 message.orderbookId
    ++ (encodeUIntLE 8 message.tradeId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 8 message.amendmentExecutionTime
    ++ (encodeUInt 1 message.tradeState
    ++ (Alpha.encode message.filler3))))))

def decode (bytes : List UInt8) : Option (TradeAmendmentMessage × List UInt8) := do
  let (orderbookId, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (amendmentExecutionTime, bytes) ← decodeUIntLE 8 bytes
  let (tradeState, bytes) ← decodeUInt 1 bytes
  let (filler3, bytes) ← Alpha.decode 3 bytes
  pure ({ orderbookId, tradeId, price, quantity, amendmentExecutionTime, tradeState, filler3 }, bytes)

@[simp] theorem encode_length (message : TradeAmendmentMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : TradeAmendmentMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeAmendmentMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeAmendmentMessage

/-- Trade Statistics Message: 56 bytes -/
structure TradeStatisticsMessage where
  orderbookId : BitVec 32
  lastPrice : BitVec 64
  session : BitVec 8
  openPrice : BitVec 64
  highPrice : BitVec 64
  lowPrice : BitVec 64
  tradeReportVolume : BitVec 64
  turnover : BitVec 64
  filler3 : Alpha 3
  deriving DecidableEq, Repr

namespace TradeStatisticsMessage

def encode (message : TradeStatisticsMessage) : List UInt8 :=
  encodeUIntLE 4 message.orderbookId
    ++ (encodeUIntLE 8 message.lastPrice
    ++ (encodeUInt 1 message.session
    ++ (encodeUIntLE 8 message.openPrice
    ++ (encodeUIntLE 8 message.highPrice
    ++ (encodeUIntLE 8 message.lowPrice
    ++ (encodeUIntLE 8 message.tradeReportVolume
    ++ (encodeUIntLE 8 message.turnover
    ++ (Alpha.encode message.filler3))))))))

def decode (bytes : List UInt8) : Option (TradeStatisticsMessage × List UInt8) := do
  let (orderbookId, bytes) ← decodeUIntLE 4 bytes
  let (lastPrice, bytes) ← decodeUIntLE 8 bytes
  let (session, bytes) ← decodeUInt 1 bytes
  let (openPrice, bytes) ← decodeUIntLE 8 bytes
  let (highPrice, bytes) ← decodeUIntLE 8 bytes
  let (lowPrice, bytes) ← decodeUIntLE 8 bytes
  let (tradeReportVolume, bytes) ← decodeUIntLE 8 bytes
  let (turnover, bytes) ← decodeUIntLE 8 bytes
  let (filler3, bytes) ← Alpha.decode 3 bytes
  pure ({ orderbookId, lastPrice, session, openPrice, highPrice, lowPrice, tradeReportVolume, turnover, filler3 }, bytes)

@[simp] theorem encode_length (message : TradeStatisticsMessage) : (encode message).length = 56 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

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
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeStatisticsMessage

/-- Any Payload, selected by Msg Type -/
inductive Payload where
  | addOrder (message : AddOrder) -- 330
  | aggregateImpliedOrder (message : AggregateImpliedOrder) -- 337
  | aggregateOrderBookUpdateMessage (message : AggregateOrderBookUpdateMessage) -- 353
  | calculatedOpeningPriceMessage (message : CalculatedOpeningPriceMessage) -- 364
  | sequenceReset (message : SequenceReset) -- 100
  | disasterRecoverySignalMessage (message : DisasterRecoverySignalMessage) -- 105
  | deleteOrder (message : DeleteOrder) -- 332
  | impliedVolatilityMessage (message : ImpliedVolatilityMessage) -- 367
  | marketAlertMessage (message : MarketAlertMessage) -- 323
  | modifyOrder (message : ModifyOrder) -- 331
  | openInterestMessage (message : OpenInterestMessage) -- 366
  | orderbookClearMessage (message : OrderbookClearMessage) -- 335
  | quoteRequest (message : QuoteRequest) -- 336
  | commodityDefinition (message : CommodityDefinition) -- 301
  | classDefinition (message : ClassDefinition) -- 302
  | instrumentDefinition (message : InstrumentDefinition) -- 304
  | combinationDefinition (message : CombinationDefinition) -- 305
  | refreshComplete (message : RefreshComplete) -- 203
  | marketStatus (message : MarketStatus) -- 320
  | instrumentStatus (message : InstrumentStatus) -- 321
  | commodityAndClassStatus (message : CommodityAndClassStatus) -- 322
  | vcmTrigger (message : VcmTrigger) -- 324
  | vcmEnd (message : VcmEnd) -- 325
  | thmTrigger (message : ThmTrigger) -- 326
  | trade (message : Trade) -- 350
  | tradeAmendmentMessage (message : TradeAmendmentMessage) -- 356
  | tradeStatisticsMessage (message : TradeStatisticsMessage) -- 360
  deriving DecidableEq, Repr

namespace Payload

/-- The Msg Type each message is sent under -/
def tag : Payload → BitVec 16
  | .addOrder _ => 330
  | .aggregateImpliedOrder _ => 337
  | .aggregateOrderBookUpdateMessage _ => 353
  | .calculatedOpeningPriceMessage _ => 364
  | .sequenceReset _ => 100
  | .disasterRecoverySignalMessage _ => 105
  | .deleteOrder _ => 332
  | .impliedVolatilityMessage _ => 367
  | .marketAlertMessage _ => 323
  | .modifyOrder _ => 331
  | .openInterestMessage _ => 366
  | .orderbookClearMessage _ => 335
  | .quoteRequest _ => 336
  | .commodityDefinition _ => 301
  | .classDefinition _ => 302
  | .instrumentDefinition _ => 304
  | .combinationDefinition _ => 305
  | .refreshComplete _ => 203
  | .marketStatus _ => 320
  | .instrumentStatus _ => 321
  | .commodityAndClassStatus _ => 322
  | .vcmTrigger _ => 324
  | .vcmEnd _ => 325
  | .thmTrigger _ => 326
  | .trade _ => 350
  | .tradeAmendmentMessage _ => 356
  | .tradeStatisticsMessage _ => 360

def encode : Payload → List UInt8
  | .addOrder message => AddOrder.encode message
  | .aggregateImpliedOrder message => AggregateImpliedOrder.encode message
  | .aggregateOrderBookUpdateMessage message => AggregateOrderBookUpdateMessage.encode message
  | .calculatedOpeningPriceMessage message => CalculatedOpeningPriceMessage.encode message
  | .sequenceReset message => SequenceReset.encode message
  | .disasterRecoverySignalMessage message => DisasterRecoverySignalMessage.encode message
  | .deleteOrder message => DeleteOrder.encode message
  | .impliedVolatilityMessage message => ImpliedVolatilityMessage.encode message
  | .marketAlertMessage message => MarketAlertMessage.encode message
  | .modifyOrder message => ModifyOrder.encode message
  | .openInterestMessage message => OpenInterestMessage.encode message
  | .orderbookClearMessage message => OrderbookClearMessage.encode message
  | .quoteRequest message => QuoteRequest.encode message
  | .commodityDefinition message => CommodityDefinition.encode message
  | .classDefinition message => ClassDefinition.encode message
  | .instrumentDefinition message => InstrumentDefinition.encode message
  | .combinationDefinition message => CombinationDefinition.encode message
  | .refreshComplete message => RefreshComplete.encode message
  | .marketStatus message => MarketStatus.encode message
  | .instrumentStatus message => InstrumentStatus.encode message
  | .commodityAndClassStatus message => CommodityAndClassStatus.encode message
  | .vcmTrigger message => VcmTrigger.encode message
  | .vcmEnd message => VcmEnd.encode message
  | .thmTrigger message => ThmTrigger.encode message
  | .trade message => Trade.encode message
  | .tradeAmendmentMessage message => TradeAmendmentMessage.encode message
  | .tradeStatisticsMessage message => TradeStatisticsMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 81932 := by
  cases message with
  | addOrder inner =>
    simp only [encode, AddOrder.encode_length]
    omega
  | aggregateImpliedOrder inner =>
    simp only [encode, AggregateImpliedOrder.encode_length]
    omega
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
  | deleteOrder inner =>
    simp only [encode, DeleteOrder.encode_length]
    omega
  | impliedVolatilityMessage inner =>
    simp only [encode, ImpliedVolatilityMessage.encode_length]
    omega
  | marketAlertMessage inner =>
    have bound_inner := MarketAlertMessage.encode_length_le inner
    simp only [encode]
    omega
  | modifyOrder inner =>
    simp only [encode, ModifyOrder.encode_length]
    omega
  | openInterestMessage inner =>
    simp only [encode, OpenInterestMessage.encode_length]
    omega
  | orderbookClearMessage inner =>
    simp only [encode, OrderbookClearMessage.encode_length]
    omega
  | quoteRequest inner =>
    simp only [encode, QuoteRequest.encode_length]
    omega
  | commodityDefinition inner =>
    simp only [encode, CommodityDefinition.encode_length]
    omega
  | classDefinition inner =>
    simp only [encode, ClassDefinition.encode_length]
    omega
  | instrumentDefinition inner =>
    simp only [encode, InstrumentDefinition.encode_length]
    omega
  | combinationDefinition inner =>
    simp only [encode, CombinationDefinition.encode_length]
    omega
  | refreshComplete inner =>
    simp only [encode, RefreshComplete.encode_length]
    omega
  | marketStatus inner =>
    simp only [encode, MarketStatus.encode_length]
    omega
  | instrumentStatus inner =>
    simp only [encode, InstrumentStatus.encode_length]
    omega
  | commodityAndClassStatus inner =>
    simp only [encode, CommodityAndClassStatus.encode_length]
    omega
  | vcmTrigger inner =>
    simp only [encode, VcmTrigger.encode_length]
    omega
  | vcmEnd inner =>
    simp only [encode, VcmEnd.encode_length]
    omega
  | thmTrigger inner =>
    simp only [encode, ThmTrigger.encode_length]
    omega
  | trade inner =>
    simp only [encode, Trade.encode_length]
    omega
  | tradeAmendmentMessage inner =>
    simp only [encode, TradeAmendmentMessage.encode_length]
    omega
  | tradeStatisticsMessage inner =>
    simp only [encode, TradeStatisticsMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 330 then (AddOrder.decode bytes).map fun (message, rest) => (.addOrder message, rest)
  else if tag = 337 then (AggregateImpliedOrder.decode bytes).map fun (message, rest) => (.aggregateImpliedOrder message, rest)
  else if tag = 353 then (AggregateOrderBookUpdateMessage.decode bytes).map fun (message, rest) => (.aggregateOrderBookUpdateMessage message, rest)
  else if tag = 364 then (CalculatedOpeningPriceMessage.decode bytes).map fun (message, rest) => (.calculatedOpeningPriceMessage message, rest)
  else if tag = 100 then (SequenceReset.decode bytes).map fun (message, rest) => (.sequenceReset message, rest)
  else if tag = 105 then (DisasterRecoverySignalMessage.decode bytes).map fun (message, rest) => (.disasterRecoverySignalMessage message, rest)
  else if tag = 332 then (DeleteOrder.decode bytes).map fun (message, rest) => (.deleteOrder message, rest)
  else if tag = 367 then (ImpliedVolatilityMessage.decode bytes).map fun (message, rest) => (.impliedVolatilityMessage message, rest)
  else if tag = 323 then (MarketAlertMessage.decode bytes).map fun (message, rest) => (.marketAlertMessage message, rest)
  else if tag = 331 then (ModifyOrder.decode bytes).map fun (message, rest) => (.modifyOrder message, rest)
  else if tag = 366 then (OpenInterestMessage.decode bytes).map fun (message, rest) => (.openInterestMessage message, rest)
  else if tag = 335 then (OrderbookClearMessage.decode bytes).map fun (message, rest) => (.orderbookClearMessage message, rest)
  else if tag = 336 then (QuoteRequest.decode bytes).map fun (message, rest) => (.quoteRequest message, rest)
  else if tag = 301 then (CommodityDefinition.decode bytes).map fun (message, rest) => (.commodityDefinition message, rest)
  else if tag = 302 then (ClassDefinition.decode bytes).map fun (message, rest) => (.classDefinition message, rest)
  else if tag = 304 then (InstrumentDefinition.decode bytes).map fun (message, rest) => (.instrumentDefinition message, rest)
  else if tag = 305 then (CombinationDefinition.decode bytes).map fun (message, rest) => (.combinationDefinition message, rest)
  else if tag = 203 then (RefreshComplete.decode bytes).map fun (message, rest) => (.refreshComplete message, rest)
  else if tag = 320 then (MarketStatus.decode bytes).map fun (message, rest) => (.marketStatus message, rest)
  else if tag = 321 then (InstrumentStatus.decode bytes).map fun (message, rest) => (.instrumentStatus message, rest)
  else if tag = 322 then (CommodityAndClassStatus.decode bytes).map fun (message, rest) => (.commodityAndClassStatus message, rest)
  else if tag = 324 then (VcmTrigger.decode bytes).map fun (message, rest) => (.vcmTrigger message, rest)
  else if tag = 325 then (VcmEnd.decode bytes).map fun (message, rest) => (.vcmEnd message, rest)
  else if tag = 326 then (ThmTrigger.decode bytes).map fun (message, rest) => (.thmTrigger message, rest)
  else if tag = 350 then (Trade.decode bytes).map fun (message, rest) => (.trade message, rest)
  else if tag = 356 then (TradeAmendmentMessage.decode bytes).map fun (message, rest) => (.tradeAmendmentMessage message, rest)
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

end Omi.HkexHkexderivativesCombinedOmdV20
