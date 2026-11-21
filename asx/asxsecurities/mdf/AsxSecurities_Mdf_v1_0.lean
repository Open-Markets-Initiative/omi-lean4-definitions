import Wire

/-!
# Australian Securities Exchange Trade Market Data Feed v1.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.

Note: a Message Count of 0 marks Heartbeat and carries no messages; the decoder reads it as a count
and the encoder never writes it

Note: a Message Count of 65535 marks End Of Session and carries no messages; the decoder reads it as
a count and the encoder never writes it

License: MIT No Attribution
-/

namespace Omi.AsxAsxsecuritiesMdfItchV10

/-- Status: one byte code -/
def Status.codes : List UInt8 :=
  [0x41, 0x44, 0x53]

inductive Status where
  | active -- Active
  | delisted -- Delisted
  | suspended -- Suspended
  | unlisted (byte : { byte : UInt8 // byte ∉ Status.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Status

def toByte : Status → UInt8
  | .active => 0x41
  | .delisted => 0x44
  | .suspended => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Status :=
  if byte = 0x41 then .active
  else if byte = 0x44 then .delisted
  else .suspended

def ofByte (byte : UInt8) : Status :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Status) : ofByte value.toByte = value := by
  cases value with
  | active => decide
  | delisted => decide
  | suspended => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Status) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Status × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Status) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Status) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Status) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Status

/-- Leg Side: one byte code -/
def LegSide.codes : List UInt8 :=
  [0x42, 0x43]

inductive LegSide where
  | buyLeg -- Buy Leg
  | sellLeg -- Sell Leg
  | unlisted (byte : { byte : UInt8 // byte ∉ LegSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LegSide

def toByte : LegSide → UInt8
  | .buyLeg => 0x42
  | .sellLeg => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LegSide :=
  if byte = 0x42 then .buyLeg
  else .sellLeg

def ofByte (byte : UInt8) : LegSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LegSide) : ofByte value.toByte = value := by
  cases value with
  | buyLeg => decide
  | sellLeg => decide
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

/-- Corporate Action Type: one byte code -/
def CorporateActionType.codes : List UInt8 :=
  [0x42, 0x53]

inductive CorporateActionType where
  | basisOfQuotation -- Basis Of Quotation
  | statusNote -- Status Note
  | unlisted (byte : { byte : UInt8 // byte ∉ CorporateActionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CorporateActionType

def toByte : CorporateActionType → UInt8
  | .basisOfQuotation => 0x42
  | .statusNote => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CorporateActionType :=
  if byte = 0x42 then .basisOfQuotation
  else .statusNote

def ofByte (byte : UInt8) : CorporateActionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CorporateActionType) : ofByte value.toByte = value := by
  cases value with
  | basisOfQuotation => decide
  | statusNote => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CorporateActionType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CorporateActionType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CorporateActionType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CorporateActionType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CorporateActionType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CorporateActionType

/-- Event Code: one byte code -/
def EventCode.codes : List UInt8 :=
  [0x4F, 0x43, 0x45]

inductive EventCode where
  | startOfMessages -- Start Of Messages
  | endOfMessages -- End Of Messages
  | doneForDay -- Done For Day
  | unlisted (byte : { byte : UInt8 // byte ∉ EventCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventCode

def toByte : EventCode → UInt8
  | .startOfMessages => 0x4F
  | .endOfMessages => 0x43
  | .doneForDay => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventCode :=
  if byte = 0x4F then .startOfMessages
  else if byte = 0x43 then .endOfMessages
  else .doneForDay

def ofByte (byte : UInt8) : EventCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventCode) : ofByte value.toByte = value := by
  cases value with
  | startOfMessages => decide
  | endOfMessages => decide
  | doneForDay => decide
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

/-- Level Update Action: one byte code -/
def LevelUpdateAction.codes : List UInt8 :=
  [0x4E, 0x43, 0x44]

inductive LevelUpdateAction where
  | new -- New
  | change -- Change
  | deleteFrom -- Delete From
  | unlisted (byte : { byte : UInt8 // byte ∉ LevelUpdateAction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LevelUpdateAction

def toByte : LevelUpdateAction → UInt8
  | .new => 0x4E
  | .change => 0x43
  | .deleteFrom => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LevelUpdateAction :=
  if byte = 0x4E then .new
  else if byte = 0x43 then .change
  else .deleteFrom

def ofByte (byte : UInt8) : LevelUpdateAction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LevelUpdateAction) : ofByte value.toByte = value := by
  cases value with
  | new => decide
  | change => decide
  | deleteFrom => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LevelUpdateAction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LevelUpdateAction × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LevelUpdateAction) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : LevelUpdateAction) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : LevelUpdateAction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LevelUpdateAction

/-- Side: one byte code -/
def Side.codes : List UInt8 :=
  [0x42, 0x41]

inductive Side where
  | bid -- Bid
  | ask -- Ask
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .bid => 0x42
  | .ask => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x42 then .bid
  else .ask

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | bid => decide
  | ask => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Side) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Side × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Side) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Side) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Side) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Side

/-- Trend Indicator: one byte code -/
def TrendIndicator.codes : List UInt8 :=
  [0x4E, 0x55, 0x44, 0x20]

inductive TrendIndicator where
  | noChange -- No Change
  | up -- Up
  | down -- Down
  | noTrendAvailable -- No Trend Available
  | unlisted (byte : { byte : UInt8 // byte ∉ TrendIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TrendIndicator

def toByte : TrendIndicator → UInt8
  | .noChange => 0x4E
  | .up => 0x55
  | .down => 0x44
  | .noTrendAvailable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TrendIndicator :=
  if byte = 0x4E then .noChange
  else if byte = 0x55 then .up
  else if byte = 0x44 then .down
  else .noTrendAvailable

def ofByte (byte : UInt8) : TrendIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TrendIndicator) : ofByte value.toByte = value := by
  cases value with
  | noChange => decide
  | up => decide
  | down => decide
  | noTrendAvailable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TrendIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TrendIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TrendIndicator) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TrendIndicator) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TrendIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TrendIndicator

/-- Aggressor: one byte code -/
def Aggressor.codes : List UInt8 :=
  [0x42, 0x41]

inductive Aggressor where
  | bid -- Bid
  | ask -- Ask
  | unlisted (byte : { byte : UInt8 // byte ∉ Aggressor.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Aggressor

def toByte : Aggressor → UInt8
  | .bid => 0x42
  | .ask => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Aggressor :=
  if byte = 0x42 then .bid
  else .ask

def ofByte (byte : UInt8) : Aggressor :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Aggressor) : ofByte value.toByte = value := by
  cases value with
  | bid => decide
  | ask => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Aggressor) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Aggressor × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Aggressor) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Aggressor) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Aggressor) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Aggressor

/-- Seconds Message: 4 bytes -/
structure SecondsMessage where
  second : BitVec 32
  deriving DecidableEq, Repr

namespace SecondsMessage

def encode (message : SecondsMessage) : List UInt8 :=
  encodeUInt 4 message.second

def decode (bytes : List UInt8) : Option (SecondsMessage × List UInt8) := do
  let (second, bytes) ← decodeUInt 4 bytes
  pure ({ second }, bytes)

@[simp] theorem encode_length (message : SecondsMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : SecondsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecondsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SecondsMessage

/-- Order Book Directory Message: 366 bytes -/
structure OrderBookDirectoryMessage where
  timestampNanoseconds : BitVec 32
  orderBookId : BitVec 32
  partitionId : BitVec 8
  symbol : Alpha 32
  longName : Alpha 32
  isin : Alpha 12
  assetName : Alpha 32
  financialProduct : BitVec 8
  tradingCurrency : Alpha 3
  numberOfDecimalsInPrice : BitVec 16
  numberOfDecimalsInNominalValue : BitVec 16
  roundLotSize : BitVec 32
  nominalValue : BitVec 64
  numberOfLegs : BitVec 8
  commodityCode : BitVec 32
  strikePrice : BitVec 64
  expirationDate : BitVec 32
  numberOfDecimalsInStrikePrice : BitVec 16
  optionType : BitVec 8
  marketId : BitVec 32
  exchangeId : BitVec 32
  numberOfDecimalsIn : BitVec 16
  sectorCode : Alpha 4
  numberOfTradableEquities : BitVec 64
  numberOfOutstandingEquities : BitVec 64
  lastTradedDate : BitVec 32
  contractMultiplier : BitVec 64
  multiplier : BitVec 64
  decimalsInMultiplier : BitVec 16
  minOrderQuantity : BitVec 64
  maxOrderQuantity : BitVec 64
  numberOfSettlementDays : BitVec 32
  primary : BitVec 8
  testOrderBook : BitVec 8
  aliasName : Alpha 32
  settlementDate : BitVec 32
  tradable : BitVec 8
  externallyPriceSourced : BitVec 8
  deliverable : BitVec 8
  priceUnit : BitVec 8
  issuer : Alpha 32
  foreignOwnershipRestriction : BitVec 8
  lastTradingTime : Alpha 6
  optionStyle : BitVec 8
  minimumValueForInitialTradeReport : BitVec 64
  cfiCode : Alpha 6
  upperLevelSeries : Alpha 32
  upperSeriesLevelOrderBookId : BitVec 32
  instrumentType : Alpha 4
  status : Status
  deriving DecidableEq, Repr

namespace OrderBookDirectoryMessage

def encode (message : OrderBookDirectoryMessage) : List UInt8 :=
  encodeUInt 4 message.timestampNanoseconds
    ++ (encodeUInt 4 message.orderBookId
    ++ (encodeUInt 1 message.partitionId
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.longName
    ++ (Alpha.encode message.isin
    ++ (Alpha.encode message.assetName
    ++ (encodeUInt 1 message.financialProduct
    ++ (Alpha.encode message.tradingCurrency
    ++ (encodeUInt 2 message.numberOfDecimalsInPrice
    ++ (encodeUInt 2 message.numberOfDecimalsInNominalValue
    ++ (encodeUInt 4 message.roundLotSize
    ++ (encodeUInt 8 message.nominalValue
    ++ (encodeUInt 1 message.numberOfLegs
    ++ (encodeUInt 4 message.commodityCode
    ++ (encodeUInt 8 message.strikePrice
    ++ (encodeUInt 4 message.expirationDate
    ++ (encodeUInt 2 message.numberOfDecimalsInStrikePrice
    ++ (encodeUInt 1 message.optionType
    ++ (encodeUInt 4 message.marketId
    ++ (encodeUInt 4 message.exchangeId
    ++ (encodeUInt 2 message.numberOfDecimalsIn
    ++ (Alpha.encode message.sectorCode
    ++ (encodeUInt 8 message.numberOfTradableEquities
    ++ (encodeUInt 8 message.numberOfOutstandingEquities
    ++ (encodeUInt 4 message.lastTradedDate
    ++ (encodeUInt 8 message.contractMultiplier
    ++ (encodeUInt 8 message.multiplier
    ++ (encodeUInt 2 message.decimalsInMultiplier
    ++ (encodeUInt 8 message.minOrderQuantity
    ++ (encodeUInt 8 message.maxOrderQuantity
    ++ (encodeUInt 4 message.numberOfSettlementDays
    ++ (encodeUInt 1 message.primary
    ++ (encodeUInt 1 message.testOrderBook
    ++ (Alpha.encode message.aliasName
    ++ (encodeUInt 4 message.settlementDate
    ++ (encodeUInt 1 message.tradable
    ++ (encodeUInt 1 message.externallyPriceSourced
    ++ (encodeUInt 1 message.deliverable
    ++ (encodeUInt 1 message.priceUnit
    ++ (Alpha.encode message.issuer
    ++ (encodeUInt 1 message.foreignOwnershipRestriction
    ++ (Alpha.encode message.lastTradingTime
    ++ (encodeUInt 1 message.optionStyle
    ++ (encodeUInt 8 message.minimumValueForInitialTradeReport
    ++ (Alpha.encode message.cfiCode
    ++ (Alpha.encode message.upperLevelSeries
    ++ (encodeUInt 4 message.upperSeriesLevelOrderBookId
    ++ (Alpha.encode message.instrumentType
    ++ (Status.encode message.status)))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderBookDirectoryMessage × List UInt8) := do
  let (timestampNanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (partitionId, bytes) ← decodeUInt 1 bytes
  let (symbol, bytes) ← Alpha.decode 32 bytes
  let (longName, bytes) ← Alpha.decode 32 bytes
  let (isin, bytes) ← Alpha.decode 12 bytes
  let (assetName, bytes) ← Alpha.decode 32 bytes
  let (financialProduct, bytes) ← decodeUInt 1 bytes
  let (tradingCurrency, bytes) ← Alpha.decode 3 bytes
  let (numberOfDecimalsInPrice, bytes) ← decodeUInt 2 bytes
  let (numberOfDecimalsInNominalValue, bytes) ← decodeUInt 2 bytes
  let (roundLotSize, bytes) ← decodeUInt 4 bytes
  let (nominalValue, bytes) ← decodeUInt 8 bytes
  let (numberOfLegs, bytes) ← decodeUInt 1 bytes
  let (commodityCode, bytes) ← decodeUInt 4 bytes
  let (strikePrice, bytes) ← decodeUInt 8 bytes
  let (expirationDate, bytes) ← decodeUInt 4 bytes
  let (numberOfDecimalsInStrikePrice, bytes) ← decodeUInt 2 bytes
  let (optionType, bytes) ← decodeUInt 1 bytes
  let (marketId, bytes) ← decodeUInt 4 bytes
  let (exchangeId, bytes) ← decodeUInt 4 bytes
  let (numberOfDecimalsIn, bytes) ← decodeUInt 2 bytes
  let (sectorCode, bytes) ← Alpha.decode 4 bytes
  let (numberOfTradableEquities, bytes) ← decodeUInt 8 bytes
  let (numberOfOutstandingEquities, bytes) ← decodeUInt 8 bytes
  let (lastTradedDate, bytes) ← decodeUInt 4 bytes
  let (contractMultiplier, bytes) ← decodeUInt 8 bytes
  let (multiplier, bytes) ← decodeUInt 8 bytes
  let (decimalsInMultiplier, bytes) ← decodeUInt 2 bytes
  let (minOrderQuantity, bytes) ← decodeUInt 8 bytes
  let (maxOrderQuantity, bytes) ← decodeUInt 8 bytes
  let (numberOfSettlementDays, bytes) ← decodeUInt 4 bytes
  let (primary, bytes) ← decodeUInt 1 bytes
  let (testOrderBook, bytes) ← decodeUInt 1 bytes
  let (aliasName, bytes) ← Alpha.decode 32 bytes
  let (settlementDate, bytes) ← decodeUInt 4 bytes
  let (tradable, bytes) ← decodeUInt 1 bytes
  let (externallyPriceSourced, bytes) ← decodeUInt 1 bytes
  let (deliverable, bytes) ← decodeUInt 1 bytes
  let (priceUnit, bytes) ← decodeUInt 1 bytes
  let (issuer, bytes) ← Alpha.decode 32 bytes
  let (foreignOwnershipRestriction, bytes) ← decodeUInt 1 bytes
  let (lastTradingTime, bytes) ← Alpha.decode 6 bytes
  let (optionStyle, bytes) ← decodeUInt 1 bytes
  let (minimumValueForInitialTradeReport, bytes) ← decodeUInt 8 bytes
  let (cfiCode, bytes) ← Alpha.decode 6 bytes
  let (upperLevelSeries, bytes) ← Alpha.decode 32 bytes
  let (upperSeriesLevelOrderBookId, bytes) ← decodeUInt 4 bytes
  let (instrumentType, bytes) ← Alpha.decode 4 bytes
  let (status, bytes) ← Status.decode bytes
  pure ({ timestampNanoseconds, orderBookId, partitionId, symbol, longName, isin, assetName, financialProduct, tradingCurrency, numberOfDecimalsInPrice, numberOfDecimalsInNominalValue, roundLotSize, nominalValue, numberOfLegs, commodityCode, strikePrice, expirationDate, numberOfDecimalsInStrikePrice, optionType, marketId, exchangeId, numberOfDecimalsIn, sectorCode, numberOfTradableEquities, numberOfOutstandingEquities, lastTradedDate, contractMultiplier, multiplier, decimalsInMultiplier, minOrderQuantity, maxOrderQuantity, numberOfSettlementDays, primary, testOrderBook, aliasName, settlementDate, tradable, externallyPriceSourced, deliverable, priceUnit, issuer, foreignOwnershipRestriction, lastTradingTime, optionStyle, minimumValueForInitialTradeReport, cfiCode, upperLevelSeries, upperSeriesLevelOrderBookId, instrumentType, status }, bytes)

@[simp] theorem encode_length (message : OrderBookDirectoryMessage) : (encode message).length = 366 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, Status.encode_length]

theorem encode_length_pos (message : OrderBookDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OrderBookDirectoryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Status.decode_encode, some_bind]
  rfl

end OrderBookDirectoryMessage

/-- Exchange Directory Message: 40 bytes -/
structure ExchangeDirectoryMessage where
  timestampNanoseconds : BitVec 32
  exchangeId : BitVec 32
  exchangeName : Alpha 32
  deriving DecidableEq, Repr

namespace ExchangeDirectoryMessage

def encode (message : ExchangeDirectoryMessage) : List UInt8 :=
  encodeUInt 4 message.timestampNanoseconds
    ++ (encodeUInt 4 message.exchangeId
    ++ (Alpha.encode message.exchangeName))

def decode (bytes : List UInt8) : Option (ExchangeDirectoryMessage × List UInt8) := do
  let (timestampNanoseconds, bytes) ← decodeUInt 4 bytes
  let (exchangeId, bytes) ← decodeUInt 4 bytes
  let (exchangeName, bytes) ← Alpha.decode 32 bytes
  pure ({ timestampNanoseconds, exchangeId, exchangeName }, bytes)

@[simp] theorem encode_length (message : ExchangeDirectoryMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : ExchangeDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExchangeDirectoryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ExchangeDirectoryMessage

/-- Market Directory Message: 42 bytes -/
structure MarketDirectoryMessage where
  timestampNanoseconds : BitVec 32
  marketId : BitVec 32
  marketName : Alpha 32
  marketType : BitVec 8
  indexMarket : BitVec 8
  deriving DecidableEq, Repr

namespace MarketDirectoryMessage

def encode (message : MarketDirectoryMessage) : List UInt8 :=
  encodeUInt 4 message.timestampNanoseconds
    ++ (encodeUInt 4 message.marketId
    ++ (Alpha.encode message.marketName
    ++ (encodeUInt 1 message.marketType
    ++ (encodeUInt 1 message.indexMarket))))

def decode (bytes : List UInt8) : Option (MarketDirectoryMessage × List UInt8) := do
  let (timestampNanoseconds, bytes) ← decodeUInt 4 bytes
  let (marketId, bytes) ← decodeUInt 4 bytes
  let (marketName, bytes) ← Alpha.decode 32 bytes
  let (marketType, bytes) ← decodeUInt 1 bytes
  let (indexMarket, bytes) ← decodeUInt 1 bytes
  pure ({ timestampNanoseconds, marketId, marketName, marketType, indexMarket }, bytes)

@[simp] theorem encode_length (message : MarketDirectoryMessage) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : MarketDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketDirectoryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MarketDirectoryMessage

/-- Combination Order Book Leg Directory Message: 17 bytes -/
structure CombinationOrderBookLegDirectoryMessage where
  timestampNanoseconds : BitVec 32
  combinationOrderBookId : BitVec 32
  legOrderBookId : BitVec 32
  legSide : LegSide
  legRatio : BitVec 32
  deriving DecidableEq, Repr

namespace CombinationOrderBookLegDirectoryMessage

def encode (message : CombinationOrderBookLegDirectoryMessage) : List UInt8 :=
  encodeUInt 4 message.timestampNanoseconds
    ++ (encodeUInt 4 message.combinationOrderBookId
    ++ (encodeUInt 4 message.legOrderBookId
    ++ (LegSide.encode message.legSide
    ++ (encodeUInt 4 message.legRatio))))

def decode (bytes : List UInt8) : Option (CombinationOrderBookLegDirectoryMessage × List UInt8) := do
  let (timestampNanoseconds, bytes) ← decodeUInt 4 bytes
  let (combinationOrderBookId, bytes) ← decodeUInt 4 bytes
  let (legOrderBookId, bytes) ← decodeUInt 4 bytes
  let (legSide, bytes) ← LegSide.decode bytes
  let (legRatio, bytes) ← decodeUInt 4 bytes
  pure ({ timestampNanoseconds, combinationOrderBookId, legOrderBookId, legSide, legRatio }, bytes)

@[simp] theorem encode_length (message : CombinationOrderBookLegDirectoryMessage) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, LegSide.encode_length]

theorem encode_length_pos (message : CombinationOrderBookLegDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CombinationOrderBookLegDirectoryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, LegSide.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CombinationOrderBookLegDirectoryMessage

/-- Tick Size Table Entry Message: 32 bytes -/
structure TickSizeTableEntryMessage where
  timestampNanoseconds : BitVec 32
  orderBookId : BitVec 32
  tickSize : BitVec 64
  priceFrom : BitVec 64
  priceTo : BitVec 64
  deriving DecidableEq, Repr

namespace TickSizeTableEntryMessage

def encode (message : TickSizeTableEntryMessage) : List UInt8 :=
  encodeUInt 4 message.timestampNanoseconds
    ++ (encodeUInt 4 message.orderBookId
    ++ (encodeUInt 8 message.tickSize
    ++ (encodeUInt 8 message.priceFrom
    ++ (encodeUInt 8 message.priceTo))))

def decode (bytes : List UInt8) : Option (TickSizeTableEntryMessage × List UInt8) := do
  let (timestampNanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (tickSize, bytes) ← decodeUInt 8 bytes
  let (priceFrom, bytes) ← decodeUInt 8 bytes
  let (priceTo, bytes) ← decodeUInt 8 bytes
  pure ({ timestampNanoseconds, orderBookId, tickSize, priceFrom, priceTo }, bytes)

@[simp] theorem encode_length (message : TickSizeTableEntryMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : TickSizeTableEntryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TickSizeTableEntryMessage) (rest : List UInt8) :
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TickSizeTableEntryMessage

/-- Corporate Action Entry Message: 31 bytes -/
structure CorporateActionEntryMessage where
  timestampNanoseconds : BitVec 32
  corporateActionId : BitVec 32
  orderBookId : BitVec 32
  corporateActionCode : Alpha 4
  corporateActionType : CorporateActionType
  startDate : BitVec 32
  endDate : BitVec 32
  recordDate : BitVec 32
  corporateActionStatus : BitVec 8
  action : BitVec 8
  deriving DecidableEq, Repr

namespace CorporateActionEntryMessage

def encode (message : CorporateActionEntryMessage) : List UInt8 :=
  encodeUInt 4 message.timestampNanoseconds
    ++ (encodeUInt 4 message.corporateActionId
    ++ (encodeUInt 4 message.orderBookId
    ++ (Alpha.encode message.corporateActionCode
    ++ (CorporateActionType.encode message.corporateActionType
    ++ (encodeUInt 4 message.startDate
    ++ (encodeUInt 4 message.endDate
    ++ (encodeUInt 4 message.recordDate
    ++ (encodeUInt 1 message.corporateActionStatus
    ++ (encodeUInt 1 message.action)))))))))

def decode (bytes : List UInt8) : Option (CorporateActionEntryMessage × List UInt8) := do
  let (timestampNanoseconds, bytes) ← decodeUInt 4 bytes
  let (corporateActionId, bytes) ← decodeUInt 4 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (corporateActionCode, bytes) ← Alpha.decode 4 bytes
  let (corporateActionType, bytes) ← CorporateActionType.decode bytes
  let (startDate, bytes) ← decodeUInt 4 bytes
  let (endDate, bytes) ← decodeUInt 4 bytes
  let (recordDate, bytes) ← decodeUInt 4 bytes
  let (corporateActionStatus, bytes) ← decodeUInt 1 bytes
  let (action, bytes) ← decodeUInt 1 bytes
  pure ({ timestampNanoseconds, corporateActionId, orderBookId, corporateActionCode, corporateActionType, startDate, endDate, recordDate, corporateActionStatus, action }, bytes)

@[simp] theorem encode_length (message : CorporateActionEntryMessage) : (encode message).length = 31 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, CorporateActionType.encode_length]

theorem encode_length_pos (message : CorporateActionEntryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CorporateActionEntryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CorporateActionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CorporateActionEntryMessage

/-- Order Book Directory Extension Message: 92 bytes -/
structure OrderBookDirectoryExtensionMessage where
  timestampNanoseconds : BitVec 32
  orderBookId : BitVec 32
  accruedInterestRounding : BitVec 32
  accruedInterestUpdown : BitVec 8
  calculationConvention : BitVec 8
  cleanPriceRounding : BitVec 32
  cleanPriceUpdown : BitVec 8
  couponFrequency : BitVec 32
  couponInterest : BitVec 64
  couponFromDate : BitVec 32
  issueDate : BitVec 32
  maturityDate : BitVec 32
  dayCalculationRule : BitVec 8
  dayCountConvention : BitVec 8
  exCouponPeriod : BitVec 32
  dividend : BitVec 64
  fixedIncomeType : BitVec 8
  rateDeterminationDays : BitVec 32
  yieldConvention : BitVec 32
  endOfMonthCountConvention : BitVec 32
  firstSettlementDate : BitVec 32
  couponDivDate : BitVec 32
  dateBooksClose : BitVec 32
  effectiveExpirationDate : BitVec 32
  proceedDate : BitVec 32
  setEndConsideration : BitVec 8
  setStartConsideration : BitVec 8
  deriving DecidableEq, Repr

namespace OrderBookDirectoryExtensionMessage

def encode (message : OrderBookDirectoryExtensionMessage) : List UInt8 :=
  encodeUInt 4 message.timestampNanoseconds
    ++ (encodeUInt 4 message.orderBookId
    ++ (encodeUInt 4 message.accruedInterestRounding
    ++ (encodeUInt 1 message.accruedInterestUpdown
    ++ (encodeUInt 1 message.calculationConvention
    ++ (encodeUInt 4 message.cleanPriceRounding
    ++ (encodeUInt 1 message.cleanPriceUpdown
    ++ (encodeUInt 4 message.couponFrequency
    ++ (encodeUInt 8 message.couponInterest
    ++ (encodeUInt 4 message.couponFromDate
    ++ (encodeUInt 4 message.issueDate
    ++ (encodeUInt 4 message.maturityDate
    ++ (encodeUInt 1 message.dayCalculationRule
    ++ (encodeUInt 1 message.dayCountConvention
    ++ (encodeUInt 4 message.exCouponPeriod
    ++ (encodeUInt 8 message.dividend
    ++ (encodeUInt 1 message.fixedIncomeType
    ++ (encodeUInt 4 message.rateDeterminationDays
    ++ (encodeUInt 4 message.yieldConvention
    ++ (encodeUInt 4 message.endOfMonthCountConvention
    ++ (encodeUInt 4 message.firstSettlementDate
    ++ (encodeUInt 4 message.couponDivDate
    ++ (encodeUInt 4 message.dateBooksClose
    ++ (encodeUInt 4 message.effectiveExpirationDate
    ++ (encodeUInt 4 message.proceedDate
    ++ (encodeUInt 1 message.setEndConsideration
    ++ (encodeUInt 1 message.setStartConsideration))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderBookDirectoryExtensionMessage × List UInt8) := do
  let (timestampNanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (accruedInterestRounding, bytes) ← decodeUInt 4 bytes
  let (accruedInterestUpdown, bytes) ← decodeUInt 1 bytes
  let (calculationConvention, bytes) ← decodeUInt 1 bytes
  let (cleanPriceRounding, bytes) ← decodeUInt 4 bytes
  let (cleanPriceUpdown, bytes) ← decodeUInt 1 bytes
  let (couponFrequency, bytes) ← decodeUInt 4 bytes
  let (couponInterest, bytes) ← decodeUInt 8 bytes
  let (couponFromDate, bytes) ← decodeUInt 4 bytes
  let (issueDate, bytes) ← decodeUInt 4 bytes
  let (maturityDate, bytes) ← decodeUInt 4 bytes
  let (dayCalculationRule, bytes) ← decodeUInt 1 bytes
  let (dayCountConvention, bytes) ← decodeUInt 1 bytes
  let (exCouponPeriod, bytes) ← decodeUInt 4 bytes
  let (dividend, bytes) ← decodeUInt 8 bytes
  let (fixedIncomeType, bytes) ← decodeUInt 1 bytes
  let (rateDeterminationDays, bytes) ← decodeUInt 4 bytes
  let (yieldConvention, bytes) ← decodeUInt 4 bytes
  let (endOfMonthCountConvention, bytes) ← decodeUInt 4 bytes
  let (firstSettlementDate, bytes) ← decodeUInt 4 bytes
  let (couponDivDate, bytes) ← decodeUInt 4 bytes
  let (dateBooksClose, bytes) ← decodeUInt 4 bytes
  let (effectiveExpirationDate, bytes) ← decodeUInt 4 bytes
  let (proceedDate, bytes) ← decodeUInt 4 bytes
  let (setEndConsideration, bytes) ← decodeUInt 1 bytes
  let (setStartConsideration, bytes) ← decodeUInt 1 bytes
  pure ({ timestampNanoseconds, orderBookId, accruedInterestRounding, accruedInterestUpdown, calculationConvention, cleanPriceRounding, cleanPriceUpdown, couponFrequency, couponInterest, couponFromDate, issueDate, maturityDate, dayCalculationRule, dayCountConvention, exCouponPeriod, dividend, fixedIncomeType, rateDeterminationDays, yieldConvention, endOfMonthCountConvention, firstSettlementDate, couponDivDate, dateBooksClose, effectiveExpirationDate, proceedDate, setEndConsideration, setStartConsideration }, bytes)

@[simp] theorem encode_length (message : OrderBookDirectoryExtensionMessage) : (encode message).length = 92 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : OrderBookDirectoryExtensionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OrderBookDirectoryExtensionMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderBookDirectoryExtensionMessage

/-- System Event Message: 5 bytes -/
structure SystemEventMessage where
  timestampNanoseconds : BitVec 32
  eventCode : EventCode
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  encodeUInt 4 message.timestampNanoseconds
    ++ (EventCode.encode message.eventCode)

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (timestampNanoseconds, bytes) ← decodeUInt 4 bytes
  let (eventCode, bytes) ← EventCode.decode bytes
  pure ({ timestampNanoseconds, eventCode }, bytes)

@[simp] theorem encode_length (message : SystemEventMessage) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, EventCode.encode_length]

theorem encode_length_pos (message : SystemEventMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemEventMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [EventCode.decode_encode, some_bind]
  rfl

end SystemEventMessage

/-- Order Book State Message: 48 bytes -/
structure OrderBookStateMessage where
  timestampNanoseconds : BitVec 32
  orderBookId : BitVec 32
  stateName : Alpha 20
  displayName : Alpha 20
  deriving DecidableEq, Repr

namespace OrderBookStateMessage

def encode (message : OrderBookStateMessage) : List UInt8 :=
  encodeUInt 4 message.timestampNanoseconds
    ++ (encodeUInt 4 message.orderBookId
    ++ (Alpha.encode message.stateName
    ++ (Alpha.encode message.displayName)))

def decode (bytes : List UInt8) : Option (OrderBookStateMessage × List UInt8) := do
  let (timestampNanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (stateName, bytes) ← Alpha.decode 20 bytes
  let (displayName, bytes) ← Alpha.decode 20 bytes
  pure ({ timestampNanoseconds, orderBookId, stateName, displayName }, bytes)

@[simp] theorem encode_length (message : OrderBookStateMessage) : (encode message).length = 48 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderBookStateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderBookStateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderBookStateMessage

/-- Business Date Message: 8 bytes -/
structure BusinessDateMessage where
  timestampNanoseconds : BitVec 32
  businessDate : BitVec 32
  deriving DecidableEq, Repr

namespace BusinessDateMessage

def encode (message : BusinessDateMessage) : List UInt8 :=
  encodeUInt 4 message.timestampNanoseconds
    ++ (encodeUInt 4 message.businessDate)

def decode (bytes : List UInt8) : Option (BusinessDateMessage × List UInt8) := do
  let (timestampNanoseconds, bytes) ← decodeUInt 4 bytes
  let (businessDate, bytes) ← decodeUInt 4 bytes
  pure ({ timestampNanoseconds, businessDate }, bytes)

@[simp] theorem encode_length (message : BusinessDateMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : BusinessDateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BusinessDateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end BusinessDateMessage

/-- Instrument Status Message: 65 bytes -/
structure InstrumentStatusMessage where
  timestampNanoseconds : BitVec 32
  tradingStateName : Alpha 20
  instrumentStateLevel : BitVec 8
  nameOfTheInstrumentStateLevel : Alpha 32
  startDate : BitVec 32
  startTime : BitVec 32
  deriving DecidableEq, Repr

namespace InstrumentStatusMessage

def encode (message : InstrumentStatusMessage) : List UInt8 :=
  encodeUInt 4 message.timestampNanoseconds
    ++ (Alpha.encode message.tradingStateName
    ++ (encodeUInt 1 message.instrumentStateLevel
    ++ (Alpha.encode message.nameOfTheInstrumentStateLevel
    ++ (encodeUInt 4 message.startDate
    ++ (encodeUInt 4 message.startTime)))))

def decode (bytes : List UInt8) : Option (InstrumentStatusMessage × List UInt8) := do
  let (timestampNanoseconds, bytes) ← decodeUInt 4 bytes
  let (tradingStateName, bytes) ← Alpha.decode 20 bytes
  let (instrumentStateLevel, bytes) ← decodeUInt 1 bytes
  let (nameOfTheInstrumentStateLevel, bytes) ← Alpha.decode 32 bytes
  let (startDate, bytes) ← decodeUInt 4 bytes
  let (startTime, bytes) ← decodeUInt 4 bytes
  pure ({ timestampNanoseconds, tradingStateName, instrumentStateLevel, nameOfTheInstrumentStateLevel, startDate, startTime }, bytes)

@[simp] theorem encode_length (message : InstrumentStatusMessage) : (encode message).length = 65 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : InstrumentStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end InstrumentStatusMessage

/-- Equilibrium Price Message: 72 bytes -/
structure EquilibriumPriceMessage where
  timestampNanoseconds : BitVec 32
  orderBookId : BitVec 32
  availableBidQuantityAtEquilibriumPrice : BitVec 64
  availableAskQuantityAtEquilibriumPrice : BitVec 64
  equilibriumPrice : BitVec 64
  bestBidPrice : BitVec 64
  bestAskPrice : BitVec 64
  bestBidQuantity : BitVec 64
  bestAskQuantity : BitVec 64
  equilibriumQuantity : BitVec 64
  deriving DecidableEq, Repr

namespace EquilibriumPriceMessage

def encode (message : EquilibriumPriceMessage) : List UInt8 :=
  encodeUInt 4 message.timestampNanoseconds
    ++ (encodeUInt 4 message.orderBookId
    ++ (encodeUInt 8 message.availableBidQuantityAtEquilibriumPrice
    ++ (encodeUInt 8 message.availableAskQuantityAtEquilibriumPrice
    ++ (encodeUInt 8 message.equilibriumPrice
    ++ (encodeUInt 8 message.bestBidPrice
    ++ (encodeUInt 8 message.bestAskPrice
    ++ (encodeUInt 8 message.bestBidQuantity
    ++ (encodeUInt 8 message.bestAskQuantity
    ++ (encodeUInt 8 message.equilibriumQuantity)))))))))

def decode (bytes : List UInt8) : Option (EquilibriumPriceMessage × List UInt8) := do
  let (timestampNanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (availableBidQuantityAtEquilibriumPrice, bytes) ← decodeUInt 8 bytes
  let (availableAskQuantityAtEquilibriumPrice, bytes) ← decodeUInt 8 bytes
  let (equilibriumPrice, bytes) ← decodeUInt 8 bytes
  let (bestBidPrice, bytes) ← decodeUInt 8 bytes
  let (bestAskPrice, bytes) ← decodeUInt 8 bytes
  let (bestBidQuantity, bytes) ← decodeUInt 8 bytes
  let (bestAskQuantity, bytes) ← decodeUInt 8 bytes
  let (equilibriumQuantity, bytes) ← decodeUInt 8 bytes
  pure ({ timestampNanoseconds, orderBookId, availableBidQuantityAtEquilibriumPrice, availableAskQuantityAtEquilibriumPrice, equilibriumPrice, bestBidPrice, bestAskPrice, bestBidQuantity, bestAskQuantity, equilibriumQuantity }, bytes)

@[simp] theorem encode_length (message : EquilibriumPriceMessage) : (encode message).length = 72 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : EquilibriumPriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EquilibriumPriceMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end EquilibriumPriceMessage

/-- Array Of Level Items: 28 bytes -/
structure ArrayOfLevelItems where
  levelUpdateAction : LevelUpdateAction
  side : Side
  level : BitVec 8
  price : BitVec 64
  quantity : BitVec 64
  numberOfDeletes : BitVec 8
  numberOfOrders : BitVec 64
  deriving DecidableEq, Repr

namespace ArrayOfLevelItems

def encode (message : ArrayOfLevelItems) : List UInt8 :=
  LevelUpdateAction.encode message.levelUpdateAction
    ++ (Side.encode message.side
    ++ (encodeUInt 1 message.level
    ++ (encodeUInt 8 message.price
    ++ (encodeUInt 8 message.quantity
    ++ (encodeUInt 1 message.numberOfDeletes
    ++ (encodeUInt 8 message.numberOfOrders))))))

def decode (bytes : List UInt8) : Option (ArrayOfLevelItems × List UInt8) := do
  let (levelUpdateAction, bytes) ← LevelUpdateAction.decode bytes
  let (side, bytes) ← Side.decode bytes
  let (level, bytes) ← decodeUInt 1 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (quantity, bytes) ← decodeUInt 8 bytes
  let (numberOfDeletes, bytes) ← decodeUInt 1 bytes
  let (numberOfOrders, bytes) ← decodeUInt 8 bytes
  pure ({ levelUpdateAction, side, level, price, quantity, numberOfDeletes, numberOfOrders }, bytes)

@[simp] theorem encode_length (message : ArrayOfLevelItems) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, LevelUpdateAction.encode_length, Side.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ArrayOfLevelItems) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ArrayOfLevelItems) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LevelUpdateAction.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ArrayOfLevelItems

/-- Market By Price Message -/
structure MarketByPriceMessage where
  timestampNanoseconds : BitVec 32
  orderBookId : BitVec 32
  maximumLevel : BitVec 8
  arrayOfLevelItems : Bounded 1 ArrayOfLevelItems
  deriving DecidableEq, Repr

namespace MarketByPriceMessage

def encode (message : MarketByPriceMessage) : List UInt8 :=
  encodeUInt 4 message.timestampNanoseconds
    ++ (encodeUInt 4 message.orderBookId
    ++ (encodeUInt 1 message.maximumLevel
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.arrayOfLevelItems.val.length)
    ++ (encodeMany ArrayOfLevelItems.encode message.arrayOfLevelItems.val))))

def decode (bytes : List UInt8) : Option (MarketByPriceMessage × List UInt8) := do
  let (timestampNanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (maximumLevel, bytes) ← decodeUInt 1 bytes
  let (numberOfLevelItems, bytes) ← decodeUInt 1 bytes
  let (arrayOfLevelItems_, bytes) ← decodeMany ArrayOfLevelItems.decode numberOfLevelItems.toNat bytes
  if fits_arrayOfLevelItems : arrayOfLevelItems_.length < 256 ^ 1 then
    pure ({ timestampNanoseconds, orderBookId, maximumLevel, arrayOfLevelItems := ⟨arrayOfLevelItems_, fits_arrayOfLevelItems⟩ }, bytes)
  else none

theorem encode_length_pos (message : MarketByPriceMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MarketByPriceMessage) : (encode message).length ≤ 7150 := by
  have bound_arrayOfLevelItems := message.arrayOfLevelItems.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const ArrayOfLevelItems.encode 28 ArrayOfLevelItems.encode_length]
  omega

@[simp] theorem decode_encode (message : MarketByPriceMessage) (rest : List UInt8) :
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
  rw [decodeMany_bounded 1 ArrayOfLevelItems.encode ArrayOfLevelItems.decode ArrayOfLevelItems.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.arrayOfLevelItems.length_lt]
  rfl

end MarketByPriceMessage

/-- Trade Statistics Message: 89 bytes -/
structure TradeStatisticsMessage where
  timestampNanoseconds : BitVec 32
  orderBookId : BitVec 32
  openPrice : BitVec 64
  highPrice : BitVec 64
  lowPrice : BitVec 64
  lastPrice : BitVec 64
  lastAuctionPrice : BitVec 64
  lastQuantity : BitVec 64
  turnoverQuantity : BitVec 64
  reportedTradesTurnoverQuantity : BitVec 64
  turnoverValue : BitVec 64
  numberOfTrades : BitVec 64
  trendIndicator : TrendIndicator
  deriving DecidableEq, Repr

namespace TradeStatisticsMessage

def encode (message : TradeStatisticsMessage) : List UInt8 :=
  encodeUInt 4 message.timestampNanoseconds
    ++ (encodeUInt 4 message.orderBookId
    ++ (encodeUInt 8 message.openPrice
    ++ (encodeUInt 8 message.highPrice
    ++ (encodeUInt 8 message.lowPrice
    ++ (encodeUInt 8 message.lastPrice
    ++ (encodeUInt 8 message.lastAuctionPrice
    ++ (encodeUInt 8 message.lastQuantity
    ++ (encodeUInt 8 message.turnoverQuantity
    ++ (encodeUInt 8 message.reportedTradesTurnoverQuantity
    ++ (encodeUInt 8 message.turnoverValue
    ++ (encodeUInt 8 message.numberOfTrades
    ++ (TrendIndicator.encode message.trendIndicator))))))))))))

def decode (bytes : List UInt8) : Option (TradeStatisticsMessage × List UInt8) := do
  let (timestampNanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (openPrice, bytes) ← decodeUInt 8 bytes
  let (highPrice, bytes) ← decodeUInt 8 bytes
  let (lowPrice, bytes) ← decodeUInt 8 bytes
  let (lastPrice, bytes) ← decodeUInt 8 bytes
  let (lastAuctionPrice, bytes) ← decodeUInt 8 bytes
  let (lastQuantity, bytes) ← decodeUInt 8 bytes
  let (turnoverQuantity, bytes) ← decodeUInt 8 bytes
  let (reportedTradesTurnoverQuantity, bytes) ← decodeUInt 8 bytes
  let (turnoverValue, bytes) ← decodeUInt 8 bytes
  let (numberOfTrades, bytes) ← decodeUInt 8 bytes
  let (trendIndicator, bytes) ← TrendIndicator.decode bytes
  pure ({ timestampNanoseconds, orderBookId, openPrice, highPrice, lowPrice, lastPrice, lastAuctionPrice, lastQuantity, turnoverQuantity, reportedTradesTurnoverQuantity, turnoverValue, numberOfTrades, trendIndicator }, bytes)

@[simp] theorem encode_length (message : TradeStatisticsMessage) : (encode message).length = 89 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, TrendIndicator.encode_length]

theorem encode_length_pos (message : TradeStatisticsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeStatisticsMessage) (rest : List UInt8) :
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
  rw [TrendIndicator.decode_encode, some_bind]
  rfl

end TradeStatisticsMessage

/-- Reference Price Message: 29 bytes -/
structure ReferencePriceMessage where
  timestampNanoseconds : BitVec 32
  orderBookId : BitVec 32
  priceType : BitVec 8
  price : BitVec 64
  timestamp : BitVec 64
  priceDate : BitVec 32
  deriving DecidableEq, Repr

namespace ReferencePriceMessage

def encode (message : ReferencePriceMessage) : List UInt8 :=
  encodeUInt 4 message.timestampNanoseconds
    ++ (encodeUInt 4 message.orderBookId
    ++ (encodeUInt 1 message.priceType
    ++ (encodeUInt 8 message.price
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.priceDate)))))

def decode (bytes : List UInt8) : Option (ReferencePriceMessage × List UInt8) := do
  let (timestampNanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (priceType, bytes) ← decodeUInt 1 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (priceDate, bytes) ← decodeUInt 4 bytes
  pure ({ timestampNanoseconds, orderBookId, priceType, price, timestamp, priceDate }, bytes)

@[simp] theorem encode_length (message : ReferencePriceMessage) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : ReferencePriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReferencePriceMessage) (rest : List UInt8) :
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ReferencePriceMessage

/-- Index Message: 37 bytes -/
structure IndexMessage where
  timestampNanoseconds : BitVec 32
  orderBookId : BitVec 32
  lastPrice : BitVec 64
  timestamp : BitVec 64
  changePrevious : BitVec 32
  changeYesterday : BitVec 32
  trendIndicator : TrendIndicator
  pointOfMovement : BitVec 32
  deriving DecidableEq, Repr

namespace IndexMessage

def encode (message : IndexMessage) : List UInt8 :=
  encodeUInt 4 message.timestampNanoseconds
    ++ (encodeUInt 4 message.orderBookId
    ++ (encodeUInt 8 message.lastPrice
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.changePrevious
    ++ (encodeUInt 4 message.changeYesterday
    ++ (TrendIndicator.encode message.trendIndicator
    ++ (encodeUInt 4 message.pointOfMovement)))))))

def decode (bytes : List UInt8) : Option (IndexMessage × List UInt8) := do
  let (timestampNanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (lastPrice, bytes) ← decodeUInt 8 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (changePrevious, bytes) ← decodeUInt 4 bytes
  let (changeYesterday, bytes) ← decodeUInt 4 bytes
  let (trendIndicator, bytes) ← TrendIndicator.decode bytes
  let (pointOfMovement, bytes) ← decodeUInt 4 bytes
  pure ({ timestampNanoseconds, orderBookId, lastPrice, timestamp, changePrevious, changeYesterday, trendIndicator, pointOfMovement }, bytes)

@[simp] theorem encode_length (message : IndexMessage) : (encode message).length = 37 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, TrendIndicator.encode_length]

theorem encode_length_pos (message : IndexMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IndexMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, TrendIndicator.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end IndexMessage

/-- Open Interest Message: 24 bytes -/
structure OpenInterestMessage where
  timestampNanoseconds : BitVec 32
  orderBookId : BitVec 32
  openInterest : BitVec 64
  transactTime : BitVec 64
  deriving DecidableEq, Repr

namespace OpenInterestMessage

def encode (message : OpenInterestMessage) : List UInt8 :=
  encodeUInt 4 message.timestampNanoseconds
    ++ (encodeUInt 4 message.orderBookId
    ++ (encodeUInt 8 message.openInterest
    ++ (encodeUInt 8 message.transactTime)))

def decode (bytes : List UInt8) : Option (OpenInterestMessage × List UInt8) := do
  let (timestampNanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (openInterest, bytes) ← decodeUInt 8 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  pure ({ timestampNanoseconds, orderBookId, openInterest, transactTime }, bytes)

@[simp] theorem encode_length (message : OpenInterestMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : OpenInterestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OpenInterestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OpenInterestMessage

/-- Trade Ticker Message: 91 bytes -/
structure TradeTickerMessage where
  timestampNanoseconds : BitVec 32
  orderBookId : BitVec 32
  dealId : BitVec 64
  dealSource : BitVec 8
  price : BitVec 64
  quantity : BitVec 64
  dealTime : BitVec 64
  action : BitVec 8
  aggressor : Aggressor
  tradeReportType : BitVec 16
  printable : BitVec 8
  asOfDate : BitVec 32
  boqList : Alpha 6
  participantIdBuy : Alpha 5
  orderIdBuy : BitVec 64
  participantIdSell : Alpha 5
  orderIdSell : BitVec 64
  tradeSlipNumber : BitVec 32
  exchangeOrderType : BitVec 32
  tradeCondition : BitVec 8
  deriving DecidableEq, Repr

namespace TradeTickerMessage

def encode (message : TradeTickerMessage) : List UInt8 :=
  encodeUInt 4 message.timestampNanoseconds
    ++ (encodeUInt 4 message.orderBookId
    ++ (encodeUInt 8 message.dealId
    ++ (encodeUInt 1 message.dealSource
    ++ (encodeUInt 8 message.price
    ++ (encodeUInt 8 message.quantity
    ++ (encodeUInt 8 message.dealTime
    ++ (encodeUInt 1 message.action
    ++ (Aggressor.encode message.aggressor
    ++ (encodeUInt 2 message.tradeReportType
    ++ (encodeUInt 1 message.printable
    ++ (encodeUInt 4 message.asOfDate
    ++ (Alpha.encode message.boqList
    ++ (Alpha.encode message.participantIdBuy
    ++ (encodeUInt 8 message.orderIdBuy
    ++ (Alpha.encode message.participantIdSell
    ++ (encodeUInt 8 message.orderIdSell
    ++ (encodeUInt 4 message.tradeSlipNumber
    ++ (encodeUInt 4 message.exchangeOrderType
    ++ (encodeUInt 1 message.tradeCondition)))))))))))))))))))

def decode (bytes : List UInt8) : Option (TradeTickerMessage × List UInt8) := do
  let (timestampNanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (dealId, bytes) ← decodeUInt 8 bytes
  let (dealSource, bytes) ← decodeUInt 1 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (quantity, bytes) ← decodeUInt 8 bytes
  let (dealTime, bytes) ← decodeUInt 8 bytes
  let (action, bytes) ← decodeUInt 1 bytes
  let (aggressor, bytes) ← Aggressor.decode bytes
  let (tradeReportType, bytes) ← decodeUInt 2 bytes
  let (printable, bytes) ← decodeUInt 1 bytes
  let (asOfDate, bytes) ← decodeUInt 4 bytes
  let (boqList, bytes) ← Alpha.decode 6 bytes
  let (participantIdBuy, bytes) ← Alpha.decode 5 bytes
  let (orderIdBuy, bytes) ← decodeUInt 8 bytes
  let (participantIdSell, bytes) ← Alpha.decode 5 bytes
  let (orderIdSell, bytes) ← decodeUInt 8 bytes
  let (tradeSlipNumber, bytes) ← decodeUInt 4 bytes
  let (exchangeOrderType, bytes) ← decodeUInt 4 bytes
  let (tradeCondition, bytes) ← decodeUInt 1 bytes
  pure ({ timestampNanoseconds, orderBookId, dealId, dealSource, price, quantity, dealTime, action, aggressor, tradeReportType, printable, asOfDate, boqList, participantIdBuy, orderIdBuy, participantIdSell, orderIdSell, tradeSlipNumber, exchangeOrderType, tradeCondition }, bytes)

@[simp] theorem encode_length (message : TradeTickerMessage) : (encode message).length = 91 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Aggressor.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : TradeTickerMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeTickerMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Aggressor.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TradeTickerMessage

/-- Price Limits Message: 34 bytes -/
structure PriceLimitsMessage where
  timestampNanoseconds : BitVec 32
  orderBookId : BitVec 32
  upperLimit : BitVec 64
  lowerLimit : BitVec 64
  type : BitVec 8
  category : BitVec 8
  referencePrice : BitVec 64
  deriving DecidableEq, Repr

namespace PriceLimitsMessage

def encode (message : PriceLimitsMessage) : List UInt8 :=
  encodeUInt 4 message.timestampNanoseconds
    ++ (encodeUInt 4 message.orderBookId
    ++ (encodeUInt 8 message.upperLimit
    ++ (encodeUInt 8 message.lowerLimit
    ++ (encodeUInt 1 message.type
    ++ (encodeUInt 1 message.category
    ++ (encodeUInt 8 message.referencePrice))))))

def decode (bytes : List UInt8) : Option (PriceLimitsMessage × List UInt8) := do
  let (timestampNanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (upperLimit, bytes) ← decodeUInt 8 bytes
  let (lowerLimit, bytes) ← decodeUInt 8 bytes
  let (type, bytes) ← decodeUInt 1 bytes
  let (category, bytes) ← decodeUInt 1 bytes
  let (referencePrice, bytes) ← decodeUInt 8 bytes
  pure ({ timestampNanoseconds, orderBookId, upperLimit, lowerLimit, type, category, referencePrice }, bytes)

@[simp] theorem encode_length (message : PriceLimitsMessage) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : PriceLimitsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PriceLimitsMessage) (rest : List UInt8) :
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end PriceLimitsMessage

/-- Array Of Message Items: 80 bytes -/
structure ArrayOfMessageItems where
  messageItem : Alpha 80
  deriving DecidableEq, Repr

namespace ArrayOfMessageItems

def encode (message : ArrayOfMessageItems) : List UInt8 :=
  Alpha.encode message.messageItem

def decode (bytes : List UInt8) : Option (ArrayOfMessageItems × List UInt8) := do
  let (messageItem, bytes) ← Alpha.decode 80 bytes
  pure ({ messageItem }, bytes)

@[simp] theorem encode_length (message : ArrayOfMessageItems) : (encode message).length = 80 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : ArrayOfMessageItems) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ArrayOfMessageItems) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end ArrayOfMessageItems

/-- Market Announcement Message -/
structure MarketAnnouncementMessage where
  timestampNanoseconds : BitVec 32
  orderBookId : BitVec 32
  exchangeId : BitVec 32
  marketId : BitVec 32
  messageInformationType : BitVec 8
  messageSource : Alpha 80
  messagePriority : BitVec 8
  header : Alpha 80
  itemsUrl : BitVec 8
  documentUrl : Alpha 255
  numberOfMessagesItems : BitVec 8
  arrayOfMessageItems : Bounded 1 ArrayOfMessageItems
  commodityCode : BitVec 32
  deriving DecidableEq, Repr

namespace MarketAnnouncementMessage

def encode (message : MarketAnnouncementMessage) : List UInt8 :=
  encodeUInt 4 message.timestampNanoseconds
    ++ (encodeUInt 4 message.orderBookId
    ++ (encodeUInt 4 message.exchangeId
    ++ (encodeUInt 4 message.marketId
    ++ (encodeUInt 1 message.messageInformationType
    ++ (Alpha.encode message.messageSource
    ++ (encodeUInt 1 message.messagePriority
    ++ (Alpha.encode message.header
    ++ (encodeUInt 1 message.itemsUrl
    ++ (Alpha.encode message.documentUrl
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.arrayOfMessageItems.val.length)
    ++ (encodeUInt 1 message.numberOfMessagesItems
    ++ (encodeMany ArrayOfMessageItems.encode message.arrayOfMessageItems.val
    ++ (encodeUInt 4 message.commodityCode)))))))))))))

def decode (bytes : List UInt8) : Option (MarketAnnouncementMessage × List UInt8) := do
  let (timestampNanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (exchangeId, bytes) ← decodeUInt 4 bytes
  let (marketId, bytes) ← decodeUInt 4 bytes
  let (messageInformationType, bytes) ← decodeUInt 1 bytes
  let (messageSource, bytes) ← Alpha.decode 80 bytes
  let (messagePriority, bytes) ← decodeUInt 1 bytes
  let (header, bytes) ← Alpha.decode 80 bytes
  let (itemsUrl, bytes) ← decodeUInt 1 bytes
  let (documentUrl, bytes) ← Alpha.decode 255 bytes
  let (numberOfMessageItems, bytes) ← decodeUInt 1 bytes
  let (numberOfMessagesItems, bytes) ← decodeUInt 1 bytes
  let (arrayOfMessageItems_, bytes) ← decodeMany ArrayOfMessageItems.decode numberOfMessageItems.toNat bytes
  let (commodityCode, bytes) ← decodeUInt 4 bytes
  if fits_arrayOfMessageItems : arrayOfMessageItems_.length < 256 ^ 1 then
    pure ({ timestampNanoseconds, orderBookId, exchangeId, marketId, messageInformationType, messageSource, messagePriority, header, itemsUrl, documentUrl, numberOfMessagesItems, arrayOfMessageItems := ⟨arrayOfMessageItems_, fits_arrayOfMessageItems⟩, commodityCode }, bytes)
  else none

theorem encode_length_pos (message : MarketAnnouncementMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MarketAnnouncementMessage) : (encode message).length ≤ 20840 := by
  have bound_arrayOfMessageItems := message.arrayOfMessageItems.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, encodeMany_length_const ArrayOfMessageItems.encode 80 ArrayOfMessageItems.encode_length]
  omega

@[simp] theorem decode_encode (message : MarketAnnouncementMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeMany_bounded 1 ArrayOfMessageItems.encode ArrayOfMessageItems.decode ArrayOfMessageItems.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [dite_eq_left message.arrayOfMessageItems.length_lt]
  rfl

end MarketAnnouncementMessage

/-- End Of Snapshot Message: 20 bytes -/
structure EndOfSnapshotMessage where
  snapshotSequenceNumber : Alpha 20
  deriving DecidableEq, Repr

namespace EndOfSnapshotMessage

def encode (message : EndOfSnapshotMessage) : List UInt8 :=
  Alpha.encode message.snapshotSequenceNumber

def decode (bytes : List UInt8) : Option (EndOfSnapshotMessage × List UInt8) := do
  let (snapshotSequenceNumber, bytes) ← Alpha.decode 20 bytes
  pure ({ snapshotSequenceNumber }, bytes)

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

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | secondsMessage (message : SecondsMessage) -- "T" 0x54
  | orderBookDirectoryMessage (message : OrderBookDirectoryMessage) -- "R" 0x52
  | exchangeDirectoryMessage (message : ExchangeDirectoryMessage) -- "e" 0x65
  | marketDirectoryMessage (message : MarketDirectoryMessage) -- "m" 0x6D
  | combinationOrderBookLegDirectoryMessage (message : CombinationOrderBookLegDirectoryMessage) -- "M" 0x4D
  | tickSizeTableEntryMessage (message : TickSizeTableEntryMessage) -- "L" 0x4C
  | corporateActionEntryMessage (message : CorporateActionEntryMessage) -- "C" 0x43
  | orderBookDirectoryExtensionMessage (message : OrderBookDirectoryExtensionMessage) -- "f" 0x66
  | systemEventMessage (message : SystemEventMessage) -- "S" 0x53
  | orderBookStateMessage (message : OrderBookStateMessage) -- "O" 0x4F
  | businessDateMessage (message : BusinessDateMessage) -- "B" 0x42
  | instrumentStatusMessage (message : InstrumentStatusMessage) -- "t" 0x74
  | equilibriumPriceMessage (message : EquilibriumPriceMessage) -- "Z" 0x5A
  | marketByPriceMessage (message : MarketByPriceMessage) -- "b" 0x62
  | tradeStatisticsMessage (message : TradeStatisticsMessage) -- "I" 0x49
  | referencePriceMessage (message : ReferencePriceMessage) -- "Q" 0x51
  | indexMessage (message : IndexMessage) -- "J" 0x4A
  | openInterestMessage (message : OpenInterestMessage) -- "h" 0x68
  | tradeTickerMessage (message : TradeTickerMessage) -- "i" 0x69
  | priceLimitsMessage (message : PriceLimitsMessage) -- "k" 0x6B
  | marketAnnouncementMessage (message : MarketAnnouncementMessage) -- "N" 0x4E
  | endOfSnapshotMessage (message : EndOfSnapshotMessage) -- "G" 0x47
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .secondsMessage _ => 84
  | .orderBookDirectoryMessage _ => 82
  | .exchangeDirectoryMessage _ => 101
  | .marketDirectoryMessage _ => 109
  | .combinationOrderBookLegDirectoryMessage _ => 77
  | .tickSizeTableEntryMessage _ => 76
  | .corporateActionEntryMessage _ => 67
  | .orderBookDirectoryExtensionMessage _ => 102
  | .systemEventMessage _ => 83
  | .orderBookStateMessage _ => 79
  | .businessDateMessage _ => 66
  | .instrumentStatusMessage _ => 116
  | .equilibriumPriceMessage _ => 90
  | .marketByPriceMessage _ => 98
  | .tradeStatisticsMessage _ => 73
  | .referencePriceMessage _ => 81
  | .indexMessage _ => 74
  | .openInterestMessage _ => 104
  | .tradeTickerMessage _ => 105
  | .priceLimitsMessage _ => 107
  | .marketAnnouncementMessage _ => 78
  | .endOfSnapshotMessage _ => 71

def encode : Payload → List UInt8
  | .secondsMessage message => SecondsMessage.encode message
  | .orderBookDirectoryMessage message => OrderBookDirectoryMessage.encode message
  | .exchangeDirectoryMessage message => ExchangeDirectoryMessage.encode message
  | .marketDirectoryMessage message => MarketDirectoryMessage.encode message
  | .combinationOrderBookLegDirectoryMessage message => CombinationOrderBookLegDirectoryMessage.encode message
  | .tickSizeTableEntryMessage message => TickSizeTableEntryMessage.encode message
  | .corporateActionEntryMessage message => CorporateActionEntryMessage.encode message
  | .orderBookDirectoryExtensionMessage message => OrderBookDirectoryExtensionMessage.encode message
  | .systemEventMessage message => SystemEventMessage.encode message
  | .orderBookStateMessage message => OrderBookStateMessage.encode message
  | .businessDateMessage message => BusinessDateMessage.encode message
  | .instrumentStatusMessage message => InstrumentStatusMessage.encode message
  | .equilibriumPriceMessage message => EquilibriumPriceMessage.encode message
  | .marketByPriceMessage message => MarketByPriceMessage.encode message
  | .tradeStatisticsMessage message => TradeStatisticsMessage.encode message
  | .referencePriceMessage message => ReferencePriceMessage.encode message
  | .indexMessage message => IndexMessage.encode message
  | .openInterestMessage message => OpenInterestMessage.encode message
  | .tradeTickerMessage message => TradeTickerMessage.encode message
  | .priceLimitsMessage message => PriceLimitsMessage.encode message
  | .marketAnnouncementMessage message => MarketAnnouncementMessage.encode message
  | .endOfSnapshotMessage message => EndOfSnapshotMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 20840 := by
  cases message with
  | secondsMessage inner =>
    simp only [encode, SecondsMessage.encode_length]
    omega
  | orderBookDirectoryMessage inner =>
    simp only [encode, OrderBookDirectoryMessage.encode_length]
    omega
  | exchangeDirectoryMessage inner =>
    simp only [encode, ExchangeDirectoryMessage.encode_length]
    omega
  | marketDirectoryMessage inner =>
    simp only [encode, MarketDirectoryMessage.encode_length]
    omega
  | combinationOrderBookLegDirectoryMessage inner =>
    simp only [encode, CombinationOrderBookLegDirectoryMessage.encode_length]
    omega
  | tickSizeTableEntryMessage inner =>
    simp only [encode, TickSizeTableEntryMessage.encode_length]
    omega
  | corporateActionEntryMessage inner =>
    simp only [encode, CorporateActionEntryMessage.encode_length]
    omega
  | orderBookDirectoryExtensionMessage inner =>
    simp only [encode, OrderBookDirectoryExtensionMessage.encode_length]
    omega
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega
  | orderBookStateMessage inner =>
    simp only [encode, OrderBookStateMessage.encode_length]
    omega
  | businessDateMessage inner =>
    simp only [encode, BusinessDateMessage.encode_length]
    omega
  | instrumentStatusMessage inner =>
    simp only [encode, InstrumentStatusMessage.encode_length]
    omega
  | equilibriumPriceMessage inner =>
    simp only [encode, EquilibriumPriceMessage.encode_length]
    omega
  | marketByPriceMessage inner =>
    have bound_inner := MarketByPriceMessage.encode_length_le inner
    simp only [encode]
    omega
  | tradeStatisticsMessage inner =>
    simp only [encode, TradeStatisticsMessage.encode_length]
    omega
  | referencePriceMessage inner =>
    simp only [encode, ReferencePriceMessage.encode_length]
    omega
  | indexMessage inner =>
    simp only [encode, IndexMessage.encode_length]
    omega
  | openInterestMessage inner =>
    simp only [encode, OpenInterestMessage.encode_length]
    omega
  | tradeTickerMessage inner =>
    simp only [encode, TradeTickerMessage.encode_length]
    omega
  | priceLimitsMessage inner =>
    simp only [encode, PriceLimitsMessage.encode_length]
    omega
  | marketAnnouncementMessage inner =>
    have bound_inner := MarketAnnouncementMessage.encode_length_le inner
    simp only [encode]
    omega
  | endOfSnapshotMessage inner =>
    simp only [encode, EndOfSnapshotMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 84 then (SecondsMessage.decode bytes).map fun (message, rest) => (.secondsMessage message, rest)
  else if tag = 82 then (OrderBookDirectoryMessage.decode bytes).map fun (message, rest) => (.orderBookDirectoryMessage message, rest)
  else if tag = 101 then (ExchangeDirectoryMessage.decode bytes).map fun (message, rest) => (.exchangeDirectoryMessage message, rest)
  else if tag = 109 then (MarketDirectoryMessage.decode bytes).map fun (message, rest) => (.marketDirectoryMessage message, rest)
  else if tag = 77 then (CombinationOrderBookLegDirectoryMessage.decode bytes).map fun (message, rest) => (.combinationOrderBookLegDirectoryMessage message, rest)
  else if tag = 76 then (TickSizeTableEntryMessage.decode bytes).map fun (message, rest) => (.tickSizeTableEntryMessage message, rest)
  else if tag = 67 then (CorporateActionEntryMessage.decode bytes).map fun (message, rest) => (.corporateActionEntryMessage message, rest)
  else if tag = 102 then (OrderBookDirectoryExtensionMessage.decode bytes).map fun (message, rest) => (.orderBookDirectoryExtensionMessage message, rest)
  else if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 79 then (OrderBookStateMessage.decode bytes).map fun (message, rest) => (.orderBookStateMessage message, rest)
  else if tag = 66 then (BusinessDateMessage.decode bytes).map fun (message, rest) => (.businessDateMessage message, rest)
  else if tag = 116 then (InstrumentStatusMessage.decode bytes).map fun (message, rest) => (.instrumentStatusMessage message, rest)
  else if tag = 90 then (EquilibriumPriceMessage.decode bytes).map fun (message, rest) => (.equilibriumPriceMessage message, rest)
  else if tag = 98 then (MarketByPriceMessage.decode bytes).map fun (message, rest) => (.marketByPriceMessage message, rest)
  else if tag = 73 then (TradeStatisticsMessage.decode bytes).map fun (message, rest) => (.tradeStatisticsMessage message, rest)
  else if tag = 81 then (ReferencePriceMessage.decode bytes).map fun (message, rest) => (.referencePriceMessage message, rest)
  else if tag = 74 then (IndexMessage.decode bytes).map fun (message, rest) => (.indexMessage message, rest)
  else if tag = 104 then (OpenInterestMessage.decode bytes).map fun (message, rest) => (.openInterestMessage message, rest)
  else if tag = 105 then (TradeTickerMessage.decode bytes).map fun (message, rest) => (.tradeTickerMessage message, rest)
  else if tag = 107 then (PriceLimitsMessage.decode bytes).map fun (message, rest) => (.priceLimitsMessage message, rest)
  else if tag = 78 then (MarketAnnouncementMessage.decode bytes).map fun (message, rest) => (.marketAnnouncementMessage message, rest)
  else if tag = 71 then (EndOfSnapshotMessage.decode bytes).map fun (message, rest) => (.endOfSnapshotMessage message, rest)
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
  encodeUInt 1 (Payload.tag message.payload)
    ++ (Payload.encode message.payload)

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (payload, bytes) ← Payload.decode messageType bytes
  pure ({ payload }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 0 < 256 ^ 2 := by
  unfold encodeBody
  cases message.payload with
  | secondsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SecondsMessage.encode_length]
    omega
  | orderBookDirectoryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderBookDirectoryMessage.encode_length]
    omega
  | exchangeDirectoryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ExchangeDirectoryMessage.encode_length]
    omega
  | marketDirectoryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MarketDirectoryMessage.encode_length]
    omega
  | combinationOrderBookLegDirectoryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, CombinationOrderBookLegDirectoryMessage.encode_length]
    omega
  | tickSizeTableEntryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TickSizeTableEntryMessage.encode_length]
    omega
  | corporateActionEntryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, CorporateActionEntryMessage.encode_length]
    omega
  | orderBookDirectoryExtensionMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderBookDirectoryExtensionMessage.encode_length]
    omega
  | systemEventMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SystemEventMessage.encode_length]
    omega
  | orderBookStateMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderBookStateMessage.encode_length]
    omega
  | businessDateMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, BusinessDateMessage.encode_length]
    omega
  | instrumentStatusMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, InstrumentStatusMessage.encode_length]
    omega
  | equilibriumPriceMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, EquilibriumPriceMessage.encode_length]
    omega
  | marketByPriceMessage inner =>
    have bound_inner := MarketByPriceMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUInt_length]
    omega
  | tradeStatisticsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeStatisticsMessage.encode_length]
    omega
  | referencePriceMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ReferencePriceMessage.encode_length]
    omega
  | indexMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, IndexMessage.encode_length]
    omega
  | openInterestMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OpenInterestMessage.encode_length]
    omega
  | tradeTickerMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeTickerMessage.encode_length]
    omega
  | priceLimitsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, PriceLimitsMessage.encode_length]
    omega
  | marketAnnouncementMessage inner =>
    have bound_inner := MarketAnnouncementMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUInt_length]
    omega
  | endOfSnapshotMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, EndOfSnapshotMessage.encode_length]
    omega

/-- Size rule: Message Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : Message → List UInt8 :=
  encodeFramed 2 0 encodeBody

def decode : List UInt8 → Option (Message × List UInt8) :=
  decodeFramed 2 0 decodeBody

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 2 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end Message

/-- Packet -/
structure Packet where
  session : Alpha 10
  sequenceNumber : BitVec 64
  message : Bounded 2 Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  Alpha.encode message.session
    ++ (encodeUInt 8 message.sequenceNumber
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) message.message.val.length)
    ++ (encodeMany Message.encode message.message.val)))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (session, bytes) ← Alpha.decode 10 bytes
  let (sequenceNumber, bytes) ← decodeUInt 8 bytes
  let (messageCount, bytes) ← decodeUInt 2 bytes
  let (message_, bytes) ← decodeMany Message.decode messageCount.toNat bytes
  if fits_message : message_.length < 256 ^ 2 then
    pure ({ session, sequenceNumber, message := ⟨message_, fits_message⟩ }, bytes)
  else none

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt]
  rfl

end Packet

end Omi.AsxAsxsecuritiesMdfItchV10
