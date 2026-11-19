import Wire

/-!
# National Stock Exchange of India Ltd Multicast Tick By Tick Data Feed v1.5

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.

License: MIT No Attribution
-/

namespace Omi.NseNseixMtbtndalTbtV15

/-- Daily Contract Indicator: one byte code -/
def DailyContractIndicator.codes : List UInt8 :=
  [0x44, 0x4E]

inductive DailyContractIndicator where
  | dailyContract -- Daily Contract
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ DailyContractIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DailyContractIndicator

def toByte : DailyContractIndicator → UInt8
  | .dailyContract => 0x44
  | .notApplicable => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DailyContractIndicator :=
  if byte = 0x44 then .dailyContract
  else .notApplicable

def ofByte (byte : UInt8) : DailyContractIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DailyContractIndicator) : ofByte value.toByte = value := by
  cases value with
  | dailyContract => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DailyContractIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DailyContractIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DailyContractIndicator) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : DailyContractIndicator) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : DailyContractIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DailyContractIndicator

/-- Order Type: one byte code -/
def OrderType.codes : List UInt8 :=
  [0x42, 0x53]

inductive OrderType where
  | buyOrder -- Buy Order
  | sellOrder -- Sell Order
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderType

def toByte : OrderType → UInt8
  | .buyOrder => 0x42
  | .sellOrder => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderType :=
  if byte = 0x42 then .buyOrder
  else .sellOrder

def ofByte (byte : UInt8) : OrderType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderType) : ofByte value.toByte = value := by
  cases value with
  | buyOrder => decide
  | sellOrder => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OrderType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OrderType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderType

/-- Identifier: one byte code -/
def Identifier.codes : List UInt8 :=
  [0x4F, 0x43]

inductive Identifier where
  | indicativeOpenPrice -- Indicative Open Price
  | indicativeClosePrice -- Indicative Close Price
  | unlisted (byte : { byte : UInt8 // byte ∉ Identifier.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Identifier

def toByte : Identifier → UInt8
  | .indicativeOpenPrice => 0x4F
  | .indicativeClosePrice => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Identifier :=
  if byte = 0x4F then .indicativeOpenPrice
  else .indicativeClosePrice

def ofByte (byte : UInt8) : Identifier :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Identifier) : ofByte value.toByte = value := by
  cases value with
  | indicativeOpenPrice => decide
  | indicativeClosePrice => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Identifier) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Identifier × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Identifier) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Identifier) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Identifier) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Identifier

/-- Contract Information Message: 49 bytes -/
structure ContractInformationMessage where
  timestamp : BitVec 64
  contractStreamId : BitVec 16
  tokenNumber : BitVec 32
  instrument : Alpha 6
  symbol : Alpha 10
  expiryDate : BitVec 32
  strikePrice : BitVec 32
  optionType : Alpha 2
  lowPriceRange : BitVec 32
  highPriceRange : BitVec 32
  dailyContractIndicator : DailyContractIndicator
  deriving DecidableEq, Repr

namespace ContractInformationMessage

def encode (message : ContractInformationMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 2 message.contractStreamId
    ++ (encodeUIntLE 4 message.tokenNumber
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.symbol
    ++ (encodeUIntLE 4 message.expiryDate
    ++ (encodeUIntLE 4 message.strikePrice
    ++ (Alpha.encode message.optionType
    ++ (encodeUIntLE 4 message.lowPriceRange
    ++ (encodeUIntLE 4 message.highPriceRange
    ++ (DailyContractIndicator.encode message.dailyContractIndicator))))))))))

def decode (bytes : List UInt8) : Option (ContractInformationMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (contractStreamId, bytes) ← decodeUIntLE 2 bytes
  let (tokenNumber, bytes) ← decodeUIntLE 4 bytes
  let (instrument, bytes) ← Alpha.decode 6 bytes
  let (symbol, bytes) ← Alpha.decode 10 bytes
  let (expiryDate, bytes) ← decodeUIntLE 4 bytes
  let (strikePrice, bytes) ← decodeUIntLE 4 bytes
  let (optionType, bytes) ← Alpha.decode 2 bytes
  let (lowPriceRange, bytes) ← decodeUIntLE 4 bytes
  let (highPriceRange, bytes) ← decodeUIntLE 4 bytes
  let (dailyContractIndicator, bytes) ← DailyContractIndicator.decode bytes
  pure ({ timestamp, contractStreamId, tokenNumber, instrument, symbol, expiryDate, strikePrice, optionType, lowPriceRange, highPriceRange, dailyContractIndicator }, bytes)

@[simp] theorem encode_length (message : ContractInformationMessage) : (encode message).length = 49 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, DailyContractIndicator.encode_length]

theorem encode_length_pos (message : ContractInformationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ContractInformationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [DailyContractIndicator.decode_encode, some_bind]
  rfl

end ContractInformationMessage

/-- Spread Contract Information Message: 34 bytes -/
structure SpreadContractInformationMessage where
  timestamp : BitVec 64
  contractStreamId : BitVec 16
  token1 : BitVec 32
  token2 : BitVec 32
  dayLowPriceDiffRange : BitVec 32
  dayHighPriceDiffRange : BitVec 32
  operatingRangeLowPriceDiffRange : BitVec 32
  operatingRangeHighPriceDiffRange : BitVec 32
  deriving DecidableEq, Repr

namespace SpreadContractInformationMessage

def encode (message : SpreadContractInformationMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 2 message.contractStreamId
    ++ (encodeUIntLE 4 message.token1
    ++ (encodeUIntLE 4 message.token2
    ++ (encodeUIntLE 4 message.dayLowPriceDiffRange
    ++ (encodeUIntLE 4 message.dayHighPriceDiffRange
    ++ (encodeUIntLE 4 message.operatingRangeLowPriceDiffRange
    ++ (encodeUIntLE 4 message.operatingRangeHighPriceDiffRange)))))))

def decode (bytes : List UInt8) : Option (SpreadContractInformationMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (contractStreamId, bytes) ← decodeUIntLE 2 bytes
  let (token1, bytes) ← decodeUIntLE 4 bytes
  let (token2, bytes) ← decodeUIntLE 4 bytes
  let (dayLowPriceDiffRange, bytes) ← decodeUIntLE 4 bytes
  let (dayHighPriceDiffRange, bytes) ← decodeUIntLE 4 bytes
  let (operatingRangeLowPriceDiffRange, bytes) ← decodeUIntLE 4 bytes
  let (operatingRangeHighPriceDiffRange, bytes) ← decodeUIntLE 4 bytes
  pure ({ timestamp, contractStreamId, token1, token2, dayLowPriceDiffRange, dayHighPriceDiffRange, operatingRangeLowPriceDiffRange, operatingRangeHighPriceDiffRange }, bytes)

@[simp] theorem encode_length (message : SpreadContractInformationMessage) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : SpreadContractInformationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SpreadContractInformationMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SpreadContractInformationMessage

/-- New Order Message: 29 bytes -/
structure NewOrderMessage where
  timestamp : BitVec 64
  orderId : Alpha 8
  token : BitVec 32
  orderType : OrderType
  price : BitVec 32
  quantity : BitVec 32
  deriving DecidableEq, Repr

namespace NewOrderMessage

def encode (message : NewOrderMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (Alpha.encode message.orderId
    ++ (encodeUIntLE 4 message.token
    ++ (OrderType.encode message.orderType
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 4 message.quantity)))))

def decode (bytes : List UInt8) : Option (NewOrderMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← Alpha.decode 8 bytes
  let (token, bytes) ← decodeUIntLE 4 bytes
  let (orderType, bytes) ← OrderType.decode bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  pure ({ timestamp, orderId, token, orderType, price, quantity }, bytes)

@[simp] theorem encode_length (message : NewOrderMessage) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, OrderType.encode_length]

theorem encode_length_pos (message : NewOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrderType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end NewOrderMessage

/-- Order Modification Message: 29 bytes -/
structure OrderModificationMessage where
  timestamp : BitVec 64
  orderId : Alpha 8
  token : BitVec 32
  orderType : OrderType
  price : BitVec 32
  quantity : BitVec 32
  deriving DecidableEq, Repr

namespace OrderModificationMessage

def encode (message : OrderModificationMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (Alpha.encode message.orderId
    ++ (encodeUIntLE 4 message.token
    ++ (OrderType.encode message.orderType
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 4 message.quantity)))))

def decode (bytes : List UInt8) : Option (OrderModificationMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← Alpha.decode 8 bytes
  let (token, bytes) ← decodeUIntLE 4 bytes
  let (orderType, bytes) ← OrderType.decode bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  pure ({ timestamp, orderId, token, orderType, price, quantity }, bytes)

@[simp] theorem encode_length (message : OrderModificationMessage) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, OrderType.encode_length]

theorem encode_length_pos (message : OrderModificationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderModificationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrderType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderModificationMessage

/-- Order Cancellation Message: 29 bytes -/
structure OrderCancellationMessage where
  timestamp : BitVec 64
  orderId : Alpha 8
  token : BitVec 32
  orderType : OrderType
  price : BitVec 32
  quantity : BitVec 32
  deriving DecidableEq, Repr

namespace OrderCancellationMessage

def encode (message : OrderCancellationMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (Alpha.encode message.orderId
    ++ (encodeUIntLE 4 message.token
    ++ (OrderType.encode message.orderType
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 4 message.quantity)))))

def decode (bytes : List UInt8) : Option (OrderCancellationMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← Alpha.decode 8 bytes
  let (token, bytes) ← decodeUIntLE 4 bytes
  let (orderType, bytes) ← OrderType.decode bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  pure ({ timestamp, orderId, token, orderType, price, quantity }, bytes)

@[simp] theorem encode_length (message : OrderCancellationMessage) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, OrderType.encode_length]

theorem encode_length_pos (message : OrderCancellationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancellationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrderType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderCancellationMessage

/-- Trade Message: 36 bytes -/
structure TradeMessage where
  timestamp : BitVec 64
  buyOrderId : Alpha 8
  sellOrderId : Alpha 8
  token : BitVec 32
  tradePrice : BitVec 32
  tradeQuantity : BitVec 32
  deriving DecidableEq, Repr

namespace TradeMessage

def encode (message : TradeMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (Alpha.encode message.buyOrderId
    ++ (Alpha.encode message.sellOrderId
    ++ (encodeUIntLE 4 message.token
    ++ (encodeUIntLE 4 message.tradePrice
    ++ (encodeUIntLE 4 message.tradeQuantity)))))

def decode (bytes : List UInt8) : Option (TradeMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (buyOrderId, bytes) ← Alpha.decode 8 bytes
  let (sellOrderId, bytes) ← Alpha.decode 8 bytes
  let (token, bytes) ← decodeUIntLE 4 bytes
  let (tradePrice, bytes) ← decodeUIntLE 4 bytes
  let (tradeQuantity, bytes) ← decodeUIntLE 4 bytes
  pure ({ timestamp, buyOrderId, sellOrderId, token, tradePrice, tradeQuantity }, bytes)

@[simp] theorem encode_length (message : TradeMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : TradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeMessage

/-- New Spread Order Message: 29 bytes -/
structure NewSpreadOrderMessage where
  timestamp : BitVec 64
  orderId : Alpha 8
  token : BitVec 32
  orderType : OrderType
  price : BitVec 32
  quantity : BitVec 32
  deriving DecidableEq, Repr

namespace NewSpreadOrderMessage

def encode (message : NewSpreadOrderMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (Alpha.encode message.orderId
    ++ (encodeUIntLE 4 message.token
    ++ (OrderType.encode message.orderType
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 4 message.quantity)))))

def decode (bytes : List UInt8) : Option (NewSpreadOrderMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← Alpha.decode 8 bytes
  let (token, bytes) ← decodeUIntLE 4 bytes
  let (orderType, bytes) ← OrderType.decode bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  pure ({ timestamp, orderId, token, orderType, price, quantity }, bytes)

@[simp] theorem encode_length (message : NewSpreadOrderMessage) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, OrderType.encode_length]

theorem encode_length_pos (message : NewSpreadOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewSpreadOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrderType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end NewSpreadOrderMessage

/-- Spread Order Modification Message: 29 bytes -/
structure SpreadOrderModificationMessage where
  timestamp : BitVec 64
  orderId : Alpha 8
  token : BitVec 32
  orderType : OrderType
  price : BitVec 32
  quantity : BitVec 32
  deriving DecidableEq, Repr

namespace SpreadOrderModificationMessage

def encode (message : SpreadOrderModificationMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (Alpha.encode message.orderId
    ++ (encodeUIntLE 4 message.token
    ++ (OrderType.encode message.orderType
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 4 message.quantity)))))

def decode (bytes : List UInt8) : Option (SpreadOrderModificationMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← Alpha.decode 8 bytes
  let (token, bytes) ← decodeUIntLE 4 bytes
  let (orderType, bytes) ← OrderType.decode bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  pure ({ timestamp, orderId, token, orderType, price, quantity }, bytes)

@[simp] theorem encode_length (message : SpreadOrderModificationMessage) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, OrderType.encode_length]

theorem encode_length_pos (message : SpreadOrderModificationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SpreadOrderModificationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrderType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SpreadOrderModificationMessage

/-- Spread Order Cancellation Message: 29 bytes -/
structure SpreadOrderCancellationMessage where
  timestamp : BitVec 64
  orderId : Alpha 8
  token : BitVec 32
  orderType : OrderType
  price : BitVec 32
  quantity : BitVec 32
  deriving DecidableEq, Repr

namespace SpreadOrderCancellationMessage

def encode (message : SpreadOrderCancellationMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (Alpha.encode message.orderId
    ++ (encodeUIntLE 4 message.token
    ++ (OrderType.encode message.orderType
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 4 message.quantity)))))

def decode (bytes : List UInt8) : Option (SpreadOrderCancellationMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← Alpha.decode 8 bytes
  let (token, bytes) ← decodeUIntLE 4 bytes
  let (orderType, bytes) ← OrderType.decode bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  pure ({ timestamp, orderId, token, orderType, price, quantity }, bytes)

@[simp] theorem encode_length (message : SpreadOrderCancellationMessage) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, OrderType.encode_length]

theorem encode_length_pos (message : SpreadOrderCancellationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SpreadOrderCancellationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrderType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SpreadOrderCancellationMessage

/-- Spread Trade Message: 36 bytes -/
structure SpreadTradeMessage where
  timestamp : BitVec 64
  buyOrderId : Alpha 8
  sellOrderId : Alpha 8
  token : BitVec 32
  tradePrice : BitVec 32
  quantity : BitVec 32
  deriving DecidableEq, Repr

namespace SpreadTradeMessage

def encode (message : SpreadTradeMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (Alpha.encode message.buyOrderId
    ++ (Alpha.encode message.sellOrderId
    ++ (encodeUIntLE 4 message.token
    ++ (encodeUIntLE 4 message.tradePrice
    ++ (encodeUIntLE 4 message.quantity)))))

def decode (bytes : List UInt8) : Option (SpreadTradeMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (buyOrderId, bytes) ← Alpha.decode 8 bytes
  let (sellOrderId, bytes) ← Alpha.decode 8 bytes
  let (token, bytes) ← decodeUIntLE 4 bytes
  let (tradePrice, bytes) ← decodeUIntLE 4 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  pure ({ timestamp, buyOrderId, sellOrderId, token, tradePrice, quantity }, bytes)

@[simp] theorem encode_length (message : SpreadTradeMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : SpreadTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SpreadTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SpreadTradeMessage

/-- Market Status Message: 18 bytes -/
structure MarketStatusMessage where
  timestamp : BitVec 64
  instrument : Alpha 6
  status : BitVec 16
  sessionIndicator : BitVec 16
  deriving DecidableEq, Repr

namespace MarketStatusMessage

def encode (message : MarketStatusMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (Alpha.encode message.instrument
    ++ (encodeUIntLE 2 message.status
    ++ (encodeUIntLE 2 message.sessionIndicator)))

def decode (bytes : List UInt8) : Option (MarketStatusMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (instrument, bytes) ← Alpha.decode 6 bytes
  let (status, bytes) ← decodeUIntLE 2 bytes
  let (sessionIndicator, bytes) ← decodeUIntLE 2 bytes
  pure ({ timestamp, instrument, status, sessionIndicator }, bytes)

@[simp] theorem encode_length (message : MarketStatusMessage) : (encode message).length = 18 := by
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end MarketStatusMessage

/-- Indicative Price And Quantity Message: 21 bytes -/
structure IndicativePriceAndQuantityMessage where
  timestamp : BitVec 64
  token : BitVec 32
  identifier : Identifier
  indicativePrice : BitVec 32
  indicativeQuantity : BitVec 32
  deriving DecidableEq, Repr

namespace IndicativePriceAndQuantityMessage

def encode (message : IndicativePriceAndQuantityMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 4 message.token
    ++ (Identifier.encode message.identifier
    ++ (encodeUIntLE 4 message.indicativePrice
    ++ (encodeUIntLE 4 message.indicativeQuantity))))

def decode (bytes : List UInt8) : Option (IndicativePriceAndQuantityMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (token, bytes) ← decodeUIntLE 4 bytes
  let (identifier, bytes) ← Identifier.decode bytes
  let (indicativePrice, bytes) ← decodeUIntLE 4 bytes
  let (indicativeQuantity, bytes) ← decodeUIntLE 4 bytes
  pure ({ timestamp, token, identifier, indicativePrice, indicativeQuantity }, bytes)

@[simp] theorem encode_length (message : IndicativePriceAndQuantityMessage) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Identifier.encode_length]

theorem encode_length_pos (message : IndicativePriceAndQuantityMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IndicativePriceAndQuantityMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Identifier.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end IndicativePriceAndQuantityMessage

/-- Market Statistics Information Message: 90 bytes -/
structure MarketStatisticsInformationMessage where
  timestamp : BitVec 64
  token : BitVec 32
  openingPrice : Alpha 8
  tradeHighPrice : Alpha 8
  tradeLowPrice : Alpha 8
  closingPrice : Alpha 8
  lastTradedPrice : Alpha 8
  previousClosePrice : Alpha 8
  settlementPrice : Alpha 8
  totalTradedQuantity : BitVec 32
  totalTradedValue : Alpha 8
  statisticsOpenInterest : BitVec 32
  changeInOpenInterest : BitVec 32
  sessionIndicator : BitVec 16
  deriving DecidableEq, Repr

namespace MarketStatisticsInformationMessage

def encode (message : MarketStatisticsInformationMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 4 message.token
    ++ (Alpha.encode message.openingPrice
    ++ (Alpha.encode message.tradeHighPrice
    ++ (Alpha.encode message.tradeLowPrice
    ++ (Alpha.encode message.closingPrice
    ++ (Alpha.encode message.lastTradedPrice
    ++ (Alpha.encode message.previousClosePrice
    ++ (Alpha.encode message.settlementPrice
    ++ (encodeUIntLE 4 message.totalTradedQuantity
    ++ (Alpha.encode message.totalTradedValue
    ++ (encodeUIntLE 4 message.statisticsOpenInterest
    ++ (encodeUIntLE 4 message.changeInOpenInterest
    ++ (encodeUIntLE 2 message.sessionIndicator)))))))))))))

def decode (bytes : List UInt8) : Option (MarketStatisticsInformationMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (token, bytes) ← decodeUIntLE 4 bytes
  let (openingPrice, bytes) ← Alpha.decode 8 bytes
  let (tradeHighPrice, bytes) ← Alpha.decode 8 bytes
  let (tradeLowPrice, bytes) ← Alpha.decode 8 bytes
  let (closingPrice, bytes) ← Alpha.decode 8 bytes
  let (lastTradedPrice, bytes) ← Alpha.decode 8 bytes
  let (previousClosePrice, bytes) ← Alpha.decode 8 bytes
  let (settlementPrice, bytes) ← Alpha.decode 8 bytes
  let (totalTradedQuantity, bytes) ← decodeUIntLE 4 bytes
  let (totalTradedValue, bytes) ← Alpha.decode 8 bytes
  let (statisticsOpenInterest, bytes) ← decodeUIntLE 4 bytes
  let (changeInOpenInterest, bytes) ← decodeUIntLE 4 bytes
  let (sessionIndicator, bytes) ← decodeUIntLE 2 bytes
  pure ({ timestamp, token, openingPrice, tradeHighPrice, tradeLowPrice, closingPrice, lastTradedPrice, previousClosePrice, settlementPrice, totalTradedQuantity, totalTradedValue, statisticsOpenInterest, changeInOpenInterest, sessionIndicator }, bytes)

@[simp] theorem encode_length (message : MarketStatisticsInformationMessage) : (encode message).length = 90 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : MarketStatisticsInformationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketStatisticsInformationMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end MarketStatisticsInformationMessage

/-- Open Interest Message: 16 bytes -/
structure OpenInterestMessage where
  timestamp : BitVec 64
  token : BitVec 32
  openInterest : BitVec 32
  deriving DecidableEq, Repr

namespace OpenInterestMessage

def encode (message : OpenInterestMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 4 message.token
    ++ (encodeUIntLE 4 message.openInterest))

def decode (bytes : List UInt8) : Option (OpenInterestMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (token, bytes) ← decodeUIntLE 4 bytes
  let (openInterest, bytes) ← decodeUIntLE 4 bytes
  pure ({ timestamp, token, openInterest }, bytes)

@[simp] theorem encode_length (message : OpenInterestMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OpenInterestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OpenInterestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OpenInterestMessage

/-- Heartbeat Message: 4 bytes -/
structure HeartbeatMessage where
  lastSequenceNo : BitVec 32
  deriving DecidableEq, Repr

namespace HeartbeatMessage

def encode (message : HeartbeatMessage) : List UInt8 :=
  encodeUIntLE 4 message.lastSequenceNo

def decode (bytes : List UInt8) : Option (HeartbeatMessage × List UInt8) := do
  let (lastSequenceNo, bytes) ← decodeUIntLE 4 bytes
  pure ({ lastSequenceNo }, bytes)

@[simp] theorem encode_length (message : HeartbeatMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : HeartbeatMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : HeartbeatMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end HeartbeatMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | contractInformationMessage (message : ContractInformationMessage) -- "c" 0x63
  | spreadContractInformationMessage (message : SpreadContractInformationMessage) -- "d" 0x64
  | newOrderMessage (message : NewOrderMessage) -- "N" 0x4E
  | orderModificationMessage (message : OrderModificationMessage) -- "M" 0x4D
  | orderCancellationMessage (message : OrderCancellationMessage) -- "X" 0x58
  | tradeMessage (message : TradeMessage) -- "T" 0x54
  | newSpreadOrderMessage (message : NewSpreadOrderMessage) -- "G" 0x47
  | spreadOrderModificationMessage (message : SpreadOrderModificationMessage) -- "H" 0x48
  | spreadOrderCancellationMessage (message : SpreadOrderCancellationMessage) -- "J" 0x4A
  | spreadTradeMessage (message : SpreadTradeMessage) -- "K" 0x4B
  | marketStatusMessage (message : MarketStatusMessage) -- "S" 0x53
  | indicativePriceAndQuantityMessage (message : IndicativePriceAndQuantityMessage) -- "P" 0x50
  | marketStatisticsInformationMessage (message : MarketStatisticsInformationMessage) -- "f" 0x66
  | openInterestMessage (message : OpenInterestMessage) -- "o" 0x6F
  | heartbeatMessage (message : HeartbeatMessage) -- "Z" 0x5A
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .contractInformationMessage _ => 99
  | .spreadContractInformationMessage _ => 100
  | .newOrderMessage _ => 78
  | .orderModificationMessage _ => 77
  | .orderCancellationMessage _ => 88
  | .tradeMessage _ => 84
  | .newSpreadOrderMessage _ => 71
  | .spreadOrderModificationMessage _ => 72
  | .spreadOrderCancellationMessage _ => 74
  | .spreadTradeMessage _ => 75
  | .marketStatusMessage _ => 83
  | .indicativePriceAndQuantityMessage _ => 80
  | .marketStatisticsInformationMessage _ => 102
  | .openInterestMessage _ => 111
  | .heartbeatMessage _ => 90

def encode : Payload → List UInt8
  | .contractInformationMessage message => ContractInformationMessage.encode message
  | .spreadContractInformationMessage message => SpreadContractInformationMessage.encode message
  | .newOrderMessage message => NewOrderMessage.encode message
  | .orderModificationMessage message => OrderModificationMessage.encode message
  | .orderCancellationMessage message => OrderCancellationMessage.encode message
  | .tradeMessage message => TradeMessage.encode message
  | .newSpreadOrderMessage message => NewSpreadOrderMessage.encode message
  | .spreadOrderModificationMessage message => SpreadOrderModificationMessage.encode message
  | .spreadOrderCancellationMessage message => SpreadOrderCancellationMessage.encode message
  | .spreadTradeMessage message => SpreadTradeMessage.encode message
  | .marketStatusMessage message => MarketStatusMessage.encode message
  | .indicativePriceAndQuantityMessage message => IndicativePriceAndQuantityMessage.encode message
  | .marketStatisticsInformationMessage message => MarketStatisticsInformationMessage.encode message
  | .openInterestMessage message => OpenInterestMessage.encode message
  | .heartbeatMessage message => HeartbeatMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 90 := by
  cases message with
  | contractInformationMessage inner =>
    simp only [encode, ContractInformationMessage.encode_length]
    omega
  | spreadContractInformationMessage inner =>
    simp only [encode, SpreadContractInformationMessage.encode_length]
    omega
  | newOrderMessage inner =>
    simp only [encode, NewOrderMessage.encode_length]
    omega
  | orderModificationMessage inner =>
    simp only [encode, OrderModificationMessage.encode_length]
    omega
  | orderCancellationMessage inner =>
    simp only [encode, OrderCancellationMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [encode, TradeMessage.encode_length]
    omega
  | newSpreadOrderMessage inner =>
    simp only [encode, NewSpreadOrderMessage.encode_length]
    omega
  | spreadOrderModificationMessage inner =>
    simp only [encode, SpreadOrderModificationMessage.encode_length]
    omega
  | spreadOrderCancellationMessage inner =>
    simp only [encode, SpreadOrderCancellationMessage.encode_length]
    omega
  | spreadTradeMessage inner =>
    simp only [encode, SpreadTradeMessage.encode_length]
    omega
  | marketStatusMessage inner =>
    simp only [encode, MarketStatusMessage.encode_length]
    omega
  | indicativePriceAndQuantityMessage inner =>
    simp only [encode, IndicativePriceAndQuantityMessage.encode_length]
    omega
  | marketStatisticsInformationMessage inner =>
    simp only [encode, MarketStatisticsInformationMessage.encode_length]
    omega
  | openInterestMessage inner =>
    simp only [encode, OpenInterestMessage.encode_length]
    omega
  | heartbeatMessage inner =>
    simp only [encode, HeartbeatMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 99 then (ContractInformationMessage.decode bytes).map fun (message, rest) => (.contractInformationMessage message, rest)
  else if tag = 100 then (SpreadContractInformationMessage.decode bytes).map fun (message, rest) => (.spreadContractInformationMessage message, rest)
  else if tag = 78 then (NewOrderMessage.decode bytes).map fun (message, rest) => (.newOrderMessage message, rest)
  else if tag = 77 then (OrderModificationMessage.decode bytes).map fun (message, rest) => (.orderModificationMessage message, rest)
  else if tag = 88 then (OrderCancellationMessage.decode bytes).map fun (message, rest) => (.orderCancellationMessage message, rest)
  else if tag = 84 then (TradeMessage.decode bytes).map fun (message, rest) => (.tradeMessage message, rest)
  else if tag = 71 then (NewSpreadOrderMessage.decode bytes).map fun (message, rest) => (.newSpreadOrderMessage message, rest)
  else if tag = 72 then (SpreadOrderModificationMessage.decode bytes).map fun (message, rest) => (.spreadOrderModificationMessage message, rest)
  else if tag = 74 then (SpreadOrderCancellationMessage.decode bytes).map fun (message, rest) => (.spreadOrderCancellationMessage message, rest)
  else if tag = 75 then (SpreadTradeMessage.decode bytes).map fun (message, rest) => (.spreadTradeMessage message, rest)
  else if tag = 83 then (MarketStatusMessage.decode bytes).map fun (message, rest) => (.marketStatusMessage message, rest)
  else if tag = 80 then (IndicativePriceAndQuantityMessage.decode bytes).map fun (message, rest) => (.indicativePriceAndQuantityMessage message, rest)
  else if tag = 102 then (MarketStatisticsInformationMessage.decode bytes).map fun (message, rest) => (.marketStatisticsInformationMessage message, rest)
  else if tag = 111 then (OpenInterestMessage.decode bytes).map fun (message, rest) => (.openInterestMessage message, rest)
  else if tag = 90 then (HeartbeatMessage.decode bytes).map fun (message, rest) => (.heartbeatMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Packet -/
structure Packet where
  streamId : BitVec 16
  sequenceNumber : BitVec 32
  payload : Payload
  deriving DecidableEq, Repr

namespace Packet

def encodeBody (message : Packet) : List UInt8 :=
  encodeUIntLE 2 message.streamId
    ++ (encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUInt 1 (Payload.tag message.payload)
    ++ (Payload.encode message.payload)))

def decodeBody (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (streamId, bytes) ← decodeUIntLE 2 bytes
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (payload, bytes) ← Payload.decode messageType bytes
  pure ({ streamId, sequenceNumber, payload }, bytes)

theorem decodeBody_encodeBody (message : Packet) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Packet) : (encodeBody message).length + 2 < 256 ^ 2 := by
  unfold encodeBody
  cases message.payload with
  | contractInformationMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, ContractInformationMessage.encode_length]
    omega
  | spreadContractInformationMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, SpreadContractInformationMessage.encode_length]
    omega
  | newOrderMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, NewOrderMessage.encode_length]
    omega
  | orderModificationMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, OrderModificationMessage.encode_length]
    omega
  | orderCancellationMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, OrderCancellationMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, TradeMessage.encode_length]
    omega
  | newSpreadOrderMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, NewSpreadOrderMessage.encode_length]
    omega
  | spreadOrderModificationMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, SpreadOrderModificationMessage.encode_length]
    omega
  | spreadOrderCancellationMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, SpreadOrderCancellationMessage.encode_length]
    omega
  | spreadTradeMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, SpreadTradeMessage.encode_length]
    omega
  | marketStatusMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, MarketStatusMessage.encode_length]
    omega
  | indicativePriceAndQuantityMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, IndicativePriceAndQuantityMessage.encode_length]
    omega
  | marketStatisticsInformationMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, MarketStatisticsInformationMessage.encode_length]
    omega
  | openInterestMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, OpenInterestMessage.encode_length]
    omega
  | heartbeatMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, HeartbeatMessage.encode_length]
    omega

/-- Size rule: Message Length counts the bytes after it plus 2, so it is written from the body and checked on decode -/
def encode : Packet → List UInt8 :=
  encodeFramedLE 2 2 encodeBody

def decode : List UInt8 → Option (Packet × List UInt8) :=
  decodeFramedLE 2 2 decodeBody

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 2 2 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end Packet

end Omi.NseNseixMtbtndalTbtV15
