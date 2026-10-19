import Wire

/-!
# Giełda Papierów Wartościowych w Warszawie Warsaw Stock Exchange Full Depth Stream v1.7.6

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.GpwWseStreamfulldepthWatsV17620

/-- Week Plan: 11 bytes -/
structure WeekPlan where
  calendarId : BitVec 32
  weekdays : BitVec 56
  deriving DecidableEq, Repr

namespace WeekPlan

def encode (message : WeekPlan) : List UInt8 :=
  encodeUIntLE 4 message.calendarId
    ++ (encodeUIntLE 7 message.weekdays)

def decode (bytes : List UInt8) : Option (WeekPlan × List UInt8) := do
  let (calendarId, bytes) ← decodeUIntLE 4 bytes
  let (weekdays, bytes) ← decodeUIntLE 7 bytes
  pure ({ calendarId, weekdays }, bytes)

@[simp] theorem encode_length (message : WeekPlan) : (encode message).length = 11 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : WeekPlan) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : WeekPlan) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end WeekPlan

/-- Calendar Exception: 9 bytes -/
structure CalendarException where
  calendarId : BitVec 32
  calendarExceptionDate : BitVec 32
  calendarExceptionType : BitVec 8
  deriving DecidableEq, Repr

namespace CalendarException

def encode (message : CalendarException) : List UInt8 :=
  encodeUIntLE 4 message.calendarId
    ++ (encodeUIntLE 4 message.calendarExceptionDate
    ++ (encodeUIntLE 1 message.calendarExceptionType))

def decode (bytes : List UInt8) : Option (CalendarException × List UInt8) := do
  let (calendarId, bytes) ← decodeUIntLE 4 bytes
  let (calendarExceptionDate, bytes) ← decodeUIntLE 4 bytes
  let (calendarExceptionType, bytes) ← decodeUIntLE 1 bytes
  pure ({ calendarId, calendarExceptionDate, calendarExceptionType }, bytes)

@[simp] theorem encode_length (message : CalendarException) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : CalendarException) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CalendarException) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end CalendarException

/-- Tick Table Entry: 20 bytes -/
structure TickTableEntry where
  tickSize : BitVec 64
  lowerBound : BitVec 64
  tickTableId : BitVec 32
  deriving DecidableEq, Repr

namespace TickTableEntry

def encode (message : TickTableEntry) : List UInt8 :=
  encodeUIntLE 8 message.tickSize
    ++ (encodeUIntLE 8 message.lowerBound
    ++ (encodeUIntLE 4 message.tickTableId))

def decode (bytes : List UInt8) : Option (TickTableEntry × List UInt8) := do
  let (tickSize, bytes) ← decodeUIntLE 8 bytes
  let (lowerBound, bytes) ← decodeUIntLE 8 bytes
  let (tickTableId, bytes) ← decodeUIntLE 4 bytes
  pure ({ tickSize, lowerBound, tickTableId }, bytes)

@[simp] theorem encode_length (message : TickTableEntry) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : TickTableEntry) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TickTableEntry) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TickTableEntry

/-- Collar Table Entry: 54 bytes -/
structure CollarTableEntry where
  collarTableId : BitVec 32
  collarMode : BitVec 8
  collarExpression : BitVec 8
  collarLowerBound : BitVec 64
  collarValue : BitVec 64
  collarLowerBid : BitVec 64
  collarUpperBid : BitVec 64
  collarUpperAsk : BitVec 64
  collarLowerAsk : BitVec 64
  deriving DecidableEq, Repr

namespace CollarTableEntry

def encode (message : CollarTableEntry) : List UInt8 :=
  encodeUIntLE 4 message.collarTableId
    ++ (encodeUIntLE 1 message.collarMode
    ++ (encodeUIntLE 1 message.collarExpression
    ++ (encodeUIntLE 8 message.collarLowerBound
    ++ (encodeUIntLE 8 message.collarValue
    ++ (encodeUIntLE 8 message.collarLowerBid
    ++ (encodeUIntLE 8 message.collarUpperBid
    ++ (encodeUIntLE 8 message.collarUpperAsk
    ++ (encodeUIntLE 8 message.collarLowerAsk))))))))

def decode (bytes : List UInt8) : Option (CollarTableEntry × List UInt8) := do
  let (collarTableId, bytes) ← decodeUIntLE 4 bytes
  let (collarMode, bytes) ← decodeUIntLE 1 bytes
  let (collarExpression, bytes) ← decodeUIntLE 1 bytes
  let (collarLowerBound, bytes) ← decodeUIntLE 8 bytes
  let (collarValue, bytes) ← decodeUIntLE 8 bytes
  let (collarLowerBid, bytes) ← decodeUIntLE 8 bytes
  let (collarUpperBid, bytes) ← decodeUIntLE 8 bytes
  let (collarUpperAsk, bytes) ← decodeUIntLE 8 bytes
  let (collarLowerAsk, bytes) ← decodeUIntLE 8 bytes
  pure ({ collarTableId, collarMode, collarExpression, collarLowerBound, collarValue, collarLowerBid, collarUpperBid, collarUpperAsk, collarLowerAsk }, bytes)

@[simp] theorem encode_length (message : CollarTableEntry) : (encode message).length = 54 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : CollarTableEntry) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CollarTableEntry) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end CollarTableEntry

/-- Trading Phase Schedule Entry: 40 bytes -/
structure TradingPhaseScheduleEntry where
  tradingScheduleId : BitVec 32
  tradingPhaseId : BitVec 32
  tradingPhaseSettlementCycle : BitVec 8
  tradingPhaseMaxBlockSettlementCycle : BitVec 8
  staticCollarVolatilityAuctionId : BitVec 32
  dynamicCollarVolatilityAuctionId : BitVec 32
  tradingPhaseStartTime : BitVec 64
  tradingPhaseType : BitVec 8
  uncrossing : BitVec 8
  extStaticCollarVolatilityAuctionId : BitVec 32
  extDynamicCollarVolatilityAuctionId : BitVec 32
  clatId : BitVec 32
  deriving DecidableEq, Repr

namespace TradingPhaseScheduleEntry

def encode (message : TradingPhaseScheduleEntry) : List UInt8 :=
  encodeUIntLE 4 message.tradingScheduleId
    ++ (encodeUIntLE 4 message.tradingPhaseId
    ++ (encodeUIntLE 1 message.tradingPhaseSettlementCycle
    ++ (encodeUIntLE 1 message.tradingPhaseMaxBlockSettlementCycle
    ++ (encodeUIntLE 4 message.staticCollarVolatilityAuctionId
    ++ (encodeUIntLE 4 message.dynamicCollarVolatilityAuctionId
    ++ (encodeUIntLE 8 message.tradingPhaseStartTime
    ++ (encodeUIntLE 1 message.tradingPhaseType
    ++ (encodeUIntLE 1 message.uncrossing
    ++ (encodeUIntLE 4 message.extStaticCollarVolatilityAuctionId
    ++ (encodeUIntLE 4 message.extDynamicCollarVolatilityAuctionId
    ++ (encodeUIntLE 4 message.clatId)))))))))))

def decode (bytes : List UInt8) : Option (TradingPhaseScheduleEntry × List UInt8) := do
  let (tradingScheduleId, bytes) ← decodeUIntLE 4 bytes
  let (tradingPhaseId, bytes) ← decodeUIntLE 4 bytes
  let (tradingPhaseSettlementCycle, bytes) ← decodeUIntLE 1 bytes
  let (tradingPhaseMaxBlockSettlementCycle, bytes) ← decodeUIntLE 1 bytes
  let (staticCollarVolatilityAuctionId, bytes) ← decodeUIntLE 4 bytes
  let (dynamicCollarVolatilityAuctionId, bytes) ← decodeUIntLE 4 bytes
  let (tradingPhaseStartTime, bytes) ← decodeUIntLE 8 bytes
  let (tradingPhaseType, bytes) ← decodeUIntLE 1 bytes
  let (uncrossing, bytes) ← decodeUIntLE 1 bytes
  let (extStaticCollarVolatilityAuctionId, bytes) ← decodeUIntLE 4 bytes
  let (extDynamicCollarVolatilityAuctionId, bytes) ← decodeUIntLE 4 bytes
  let (clatId, bytes) ← decodeUIntLE 4 bytes
  pure ({ tradingScheduleId, tradingPhaseId, tradingPhaseSettlementCycle, tradingPhaseMaxBlockSettlementCycle, staticCollarVolatilityAuctionId, dynamicCollarVolatilityAuctionId, tradingPhaseStartTime, tradingPhaseType, uncrossing, extStaticCollarVolatilityAuctionId, extDynamicCollarVolatilityAuctionId, clatId }, bytes)

@[simp] theorem encode_length (message : TradingPhaseScheduleEntry) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : TradingPhaseScheduleEntry) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradingPhaseScheduleEntry) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradingPhaseScheduleEntry

/-- Market Structure: 63 bytes -/
structure MarketStructure where
  id : BitVec 32
  parentId : BitVec 32
  mic : Alpha 4
  name : Alpha 50
  marketModelType : BitVec 8
  deriving DecidableEq, Repr

namespace MarketStructure

def encode (message : MarketStructure) : List UInt8 :=
  encodeUIntLE 4 message.id
    ++ (encodeUIntLE 4 message.parentId
    ++ (Alpha.encode message.mic
    ++ (Alpha.encode message.name
    ++ (encodeUIntLE 1 message.marketModelType))))

def decode (bytes : List UInt8) : Option (MarketStructure × List UInt8) := do
  let (id, bytes) ← decodeUIntLE 4 bytes
  let (parentId, bytes) ← decodeUIntLE 4 bytes
  let (mic, bytes) ← Alpha.decode 4 bytes
  let (name, bytes) ← Alpha.decode 50 bytes
  let (marketModelType, bytes) ← decodeUIntLE 1 bytes
  pure ({ id, parentId, mic, name, marketModelType }, bytes)

@[simp] theorem encode_length (message : MarketStructure) : (encode message).length = 63 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : MarketStructure) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketStructure) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end MarketStructure

/-- Collar Group: 20 bytes -/
structure CollarGroup where
  id : BitVec 32
  orderStaticCollarTableId : BitVec 32
  orderDynamicCollarTableId : BitVec 32
  tradeStaticCollarTableId : BitVec 32
  tradeDynamicCollarTableId : BitVec 32
  deriving DecidableEq, Repr

namespace CollarGroup

def encode (message : CollarGroup) : List UInt8 :=
  encodeUIntLE 4 message.id
    ++ (encodeUIntLE 4 message.orderStaticCollarTableId
    ++ (encodeUIntLE 4 message.orderDynamicCollarTableId
    ++ (encodeUIntLE 4 message.tradeStaticCollarTableId
    ++ (encodeUIntLE 4 message.tradeDynamicCollarTableId))))

def decode (bytes : List UInt8) : Option (CollarGroup × List UInt8) := do
  let (id, bytes) ← decodeUIntLE 4 bytes
  let (orderStaticCollarTableId, bytes) ← decodeUIntLE 4 bytes
  let (orderDynamicCollarTableId, bytes) ← decodeUIntLE 4 bytes
  let (tradeStaticCollarTableId, bytes) ← decodeUIntLE 4 bytes
  let (tradeDynamicCollarTableId, bytes) ← decodeUIntLE 4 bytes
  pure ({ id, orderStaticCollarTableId, orderDynamicCollarTableId, tradeStaticCollarTableId, tradeDynamicCollarTableId }, bytes)

@[simp] theorem encode_length (message : CollarGroup) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : CollarGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CollarGroup) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end CollarGroup

/-- External Underlying: 113 bytes -/
structure ExternalUnderlying where
  externalUnderlyingId : BitVec 32
  productIdentificationProductIdentification : Alpha 30
  productIdentificationType : BitVec 8
  productCode : Alpha 20
  productName : Alpha 50
  mic : Alpha 4
  nominalCurrency : BitVec 16
  tradingCurrency : BitVec 16
  deriving DecidableEq, Repr

namespace ExternalUnderlying

def encode (message : ExternalUnderlying) : List UInt8 :=
  encodeUIntLE 4 message.externalUnderlyingId
    ++ (Alpha.encode message.productIdentificationProductIdentification
    ++ (encodeUIntLE 1 message.productIdentificationType
    ++ (Alpha.encode message.productCode
    ++ (Alpha.encode message.productName
    ++ (Alpha.encode message.mic
    ++ (encodeUIntLE 2 message.nominalCurrency
    ++ (encodeUIntLE 2 message.tradingCurrency)))))))

def decode (bytes : List UInt8) : Option (ExternalUnderlying × List UInt8) := do
  let (externalUnderlyingId, bytes) ← decodeUIntLE 4 bytes
  let (productIdentificationProductIdentification, bytes) ← Alpha.decode 30 bytes
  let (productIdentificationType, bytes) ← decodeUIntLE 1 bytes
  let (productCode, bytes) ← Alpha.decode 20 bytes
  let (productName, bytes) ← Alpha.decode 50 bytes
  let (mic, bytes) ← Alpha.decode 4 bytes
  let (nominalCurrency, bytes) ← decodeUIntLE 2 bytes
  let (tradingCurrency, bytes) ← decodeUIntLE 2 bytes
  pure ({ externalUnderlyingId, productIdentificationProductIdentification, productIdentificationType, productCode, productName, mic, nominalCurrency, tradingCurrency }, bytes)

@[simp] theorem encode_length (message : ExternalUnderlying) : (encode message).length = 113 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : ExternalUnderlying) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExternalUnderlying) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ExternalUnderlying

/-- Instrument: 699 bytes -/
structure Instrument where
  instrumentId : BitVec 32
  productType : BitVec 8
  productSubtype : BitVec 8
  firstTradingDate : BitVec 32
  lastTradingDate : BitVec 32
  productId : BitVec 32
  currency : BitVec 16
  icebergMinValue : BitVec 64
  lotSize : BitVec 32
  priceExpressionType : BitVec 8
  calendarId : BitVec 32
  marketStructureId : BitVec 32
  tickTableId : BitVec 32
  referenceInstrumentId : BitVec 32
  collarGroupId : BitVec 32
  tradingScheduleId : BitVec 32
  description : Alpha 64
  mic : Alpha 4
  nominalValuePrice : BitVec 64
  nominalValueType : BitVec 8
  multiplierMultiplier : BitVec 64
  strikePrice : BitVec 64
  strikePriceCurrency : BitVec 16
  productIdentificationProductIdentification : Alpha 30
  productIdentificationType : BitVec 8
  settlementCalendarId : BitVec 32
  bondCouponType : BitVec 8
  preTradeCheckMinPrice : BitVec 64
  preTradeCheckMaxPrice : BitVec 64
  preTradeCheckMinQuantity : BitVec 64
  preTradeCheckMaxQuantity : BitVec 64
  preTradeCheckMaxValue : BitVec 64
  preTradeCheckMinValue : BitVec 64
  liquidity : BitVec 8
  marketModelType : BitVec 8
  issuer : Alpha 150
  issuerRegCountry : BitVec 16
  underlyingInstrumentId : BitVec 32
  productCode : Alpha 20
  cfi : Alpha 6
  fisn : Alpha 35
  issueSize : BitVec 64
  nominalCurrency : BitVec 16
  usIndicator : BitVec 8
  expiryDate : BitVec 32
  versionNumber : BitVec 8
  settlementType : BitVec 8
  optionType : BitVec 8
  exerciseType : BitVec 8
  productName : Alpha 50
  referencePrice : BitVec 64
  status : BitVec 8
  initialPhaseId : BitVec 32
  thresholdMax : BitVec 64
  thresholdMin : BitVec 64
  isLeverage : BitVec 8
  accruedInterestValue : BitVec 64
  kid : Alpha 128
  kidIssueDate : BitVec 32
  valueAtRisk : BitVec 8
  externalUnderlyingId : BitVec 32
  deriving DecidableEq, Repr

namespace Instrument

def encode (message : Instrument) : List UInt8 :=
  encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 1 message.productType
    ++ (encodeUIntLE 1 message.productSubtype
    ++ (encodeUIntLE 4 message.firstTradingDate
    ++ (encodeUIntLE 4 message.lastTradingDate
    ++ (encodeUIntLE 4 message.productId
    ++ (encodeUIntLE 2 message.currency
    ++ (encodeUIntLE 8 message.icebergMinValue
    ++ (encodeUIntLE 4 message.lotSize
    ++ (encodeUIntLE 1 message.priceExpressionType
    ++ (encodeUIntLE 4 message.calendarId
    ++ (encodeUIntLE 4 message.marketStructureId
    ++ (encodeUIntLE 4 message.tickTableId
    ++ (encodeUIntLE 4 message.referenceInstrumentId
    ++ (encodeUIntLE 4 message.collarGroupId
    ++ (encodeUIntLE 4 message.tradingScheduleId
    ++ (Alpha.encode message.description
    ++ (Alpha.encode message.mic
    ++ (encodeUIntLE 8 message.nominalValuePrice
    ++ (encodeUIntLE 1 message.nominalValueType
    ++ (encodeUIntLE 8 message.multiplierMultiplier
    ++ (encodeUIntLE 8 message.strikePrice
    ++ (encodeUIntLE 2 message.strikePriceCurrency
    ++ (Alpha.encode message.productIdentificationProductIdentification
    ++ (encodeUIntLE 1 message.productIdentificationType
    ++ (encodeUIntLE 4 message.settlementCalendarId
    ++ (encodeUIntLE 1 message.bondCouponType
    ++ (encodeUIntLE 8 message.preTradeCheckMinPrice
    ++ (encodeUIntLE 8 message.preTradeCheckMaxPrice
    ++ (encodeUIntLE 8 message.preTradeCheckMinQuantity
    ++ (encodeUIntLE 8 message.preTradeCheckMaxQuantity
    ++ (encodeUIntLE 8 message.preTradeCheckMaxValue
    ++ (encodeUIntLE 8 message.preTradeCheckMinValue
    ++ (encodeUIntLE 1 message.liquidity
    ++ (encodeUIntLE 1 message.marketModelType
    ++ (Alpha.encode message.issuer
    ++ (encodeUIntLE 2 message.issuerRegCountry
    ++ (encodeUIntLE 4 message.underlyingInstrumentId
    ++ (Alpha.encode message.productCode
    ++ (Alpha.encode message.cfi
    ++ (Alpha.encode message.fisn
    ++ (encodeUIntLE 8 message.issueSize
    ++ (encodeUIntLE 2 message.nominalCurrency
    ++ (encodeUIntLE 1 message.usIndicator
    ++ (encodeUIntLE 4 message.expiryDate
    ++ (encodeUIntLE 1 message.versionNumber
    ++ (encodeUIntLE 1 message.settlementType
    ++ (encodeUIntLE 1 message.optionType
    ++ (encodeUIntLE 1 message.exerciseType
    ++ (Alpha.encode message.productName
    ++ (encodeUIntLE 8 message.referencePrice
    ++ (encodeUIntLE 1 message.status
    ++ (encodeUIntLE 4 message.initialPhaseId
    ++ (encodeUIntLE 8 message.thresholdMax
    ++ (encodeUIntLE 8 message.thresholdMin
    ++ (encodeUIntLE 1 message.isLeverage
    ++ (encodeUIntLE 8 message.accruedInterestValue
    ++ (Alpha.encode message.kid
    ++ (encodeUIntLE 4 message.kidIssueDate
    ++ (encodeUIntLE 1 message.valueAtRisk
    ++ (encodeUIntLE 4 message.externalUnderlyingId))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (Instrument × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (productType, bytes) ← decodeUIntLE 1 bytes
  let (productSubtype, bytes) ← decodeUIntLE 1 bytes
  let (firstTradingDate, bytes) ← decodeUIntLE 4 bytes
  let (lastTradingDate, bytes) ← decodeUIntLE 4 bytes
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (currency, bytes) ← decodeUIntLE 2 bytes
  let (icebergMinValue, bytes) ← decodeUIntLE 8 bytes
  let (lotSize, bytes) ← decodeUIntLE 4 bytes
  let (priceExpressionType, bytes) ← decodeUIntLE 1 bytes
  let (calendarId, bytes) ← decodeUIntLE 4 bytes
  let (marketStructureId, bytes) ← decodeUIntLE 4 bytes
  let (tickTableId, bytes) ← decodeUIntLE 4 bytes
  let (referenceInstrumentId, bytes) ← decodeUIntLE 4 bytes
  let (collarGroupId, bytes) ← decodeUIntLE 4 bytes
  let (tradingScheduleId, bytes) ← decodeUIntLE 4 bytes
  let (description, bytes) ← Alpha.decode 64 bytes
  let (mic, bytes) ← Alpha.decode 4 bytes
  let (nominalValuePrice, bytes) ← decodeUIntLE 8 bytes
  let (nominalValueType, bytes) ← decodeUIntLE 1 bytes
  let (multiplierMultiplier, bytes) ← decodeUIntLE 8 bytes
  let (strikePrice, bytes) ← decodeUIntLE 8 bytes
  let (strikePriceCurrency, bytes) ← decodeUIntLE 2 bytes
  let (productIdentificationProductIdentification, bytes) ← Alpha.decode 30 bytes
  let (productIdentificationType, bytes) ← decodeUIntLE 1 bytes
  let (settlementCalendarId, bytes) ← decodeUIntLE 4 bytes
  let (bondCouponType, bytes) ← decodeUIntLE 1 bytes
  let (preTradeCheckMinPrice, bytes) ← decodeUIntLE 8 bytes
  let (preTradeCheckMaxPrice, bytes) ← decodeUIntLE 8 bytes
  let (preTradeCheckMinQuantity, bytes) ← decodeUIntLE 8 bytes
  let (preTradeCheckMaxQuantity, bytes) ← decodeUIntLE 8 bytes
  let (preTradeCheckMaxValue, bytes) ← decodeUIntLE 8 bytes
  let (preTradeCheckMinValue, bytes) ← decodeUIntLE 8 bytes
  let (liquidity, bytes) ← decodeUIntLE 1 bytes
  let (marketModelType, bytes) ← decodeUIntLE 1 bytes
  let (issuer, bytes) ← Alpha.decode 150 bytes
  let (issuerRegCountry, bytes) ← decodeUIntLE 2 bytes
  let (underlyingInstrumentId, bytes) ← decodeUIntLE 4 bytes
  let (productCode, bytes) ← Alpha.decode 20 bytes
  let (cfi, bytes) ← Alpha.decode 6 bytes
  let (fisn, bytes) ← Alpha.decode 35 bytes
  let (issueSize, bytes) ← decodeUIntLE 8 bytes
  let (nominalCurrency, bytes) ← decodeUIntLE 2 bytes
  let (usIndicator, bytes) ← decodeUIntLE 1 bytes
  let (expiryDate, bytes) ← decodeUIntLE 4 bytes
  let (versionNumber, bytes) ← decodeUIntLE 1 bytes
  let (settlementType, bytes) ← decodeUIntLE 1 bytes
  let (optionType, bytes) ← decodeUIntLE 1 bytes
  let (exerciseType, bytes) ← decodeUIntLE 1 bytes
  let (productName, bytes) ← Alpha.decode 50 bytes
  let (referencePrice, bytes) ← decodeUIntLE 8 bytes
  let (status, bytes) ← decodeUIntLE 1 bytes
  let (initialPhaseId, bytes) ← decodeUIntLE 4 bytes
  let (thresholdMax, bytes) ← decodeUIntLE 8 bytes
  let (thresholdMin, bytes) ← decodeUIntLE 8 bytes
  let (isLeverage, bytes) ← decodeUIntLE 1 bytes
  let (accruedInterestValue, bytes) ← decodeUIntLE 8 bytes
  let (kid, bytes) ← Alpha.decode 128 bytes
  let (kidIssueDate, bytes) ← decodeUIntLE 4 bytes
  let (valueAtRisk, bytes) ← decodeUIntLE 1 bytes
  let (externalUnderlyingId, bytes) ← decodeUIntLE 4 bytes
  pure ({ instrumentId, productType, productSubtype, firstTradingDate, lastTradingDate, productId, currency, icebergMinValue, lotSize, priceExpressionType, calendarId, marketStructureId, tickTableId, referenceInstrumentId, collarGroupId, tradingScheduleId, description, mic, nominalValuePrice, nominalValueType, multiplierMultiplier, strikePrice, strikePriceCurrency, productIdentificationProductIdentification, productIdentificationType, settlementCalendarId, bondCouponType, preTradeCheckMinPrice, preTradeCheckMaxPrice, preTradeCheckMinQuantity, preTradeCheckMaxQuantity, preTradeCheckMaxValue, preTradeCheckMinValue, liquidity, marketModelType, issuer, issuerRegCountry, underlyingInstrumentId, productCode, cfi, fisn, issueSize, nominalCurrency, usIndicator, expiryDate, versionNumber, settlementType, optionType, exerciseType, productName, referencePrice, status, initialPhaseId, thresholdMax, thresholdMin, isLeverage, accruedInterestValue, kid, kidIssueDate, valueAtRisk, externalUnderlyingId }, bytes)

@[simp] theorem encode_length (message : Instrument) : (encode message).length = 699 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : Instrument) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : Instrument) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end Instrument

/-- Accrued Interest Table Entry: 16 bytes -/
structure AccruedInterestTableEntry where
  productId : BitVec 32
  accruedInterestTableEntryDate : BitVec 32
  accruedInterestTableEntryValue : BitVec 64
  deriving DecidableEq, Repr

namespace AccruedInterestTableEntry

def encode (message : AccruedInterestTableEntry) : List UInt8 :=
  encodeUIntLE 4 message.productId
    ++ (encodeUIntLE 4 message.accruedInterestTableEntryDate
    ++ (encodeUIntLE 8 message.accruedInterestTableEntryValue))

def decode (bytes : List UInt8) : Option (AccruedInterestTableEntry × List UInt8) := do
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (accruedInterestTableEntryDate, bytes) ← decodeUIntLE 4 bytes
  let (accruedInterestTableEntryValue, bytes) ← decodeUIntLE 8 bytes
  pure ({ productId, accruedInterestTableEntryDate, accruedInterestTableEntryValue }, bytes)

@[simp] theorem encode_length (message : AccruedInterestTableEntry) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : AccruedInterestTableEntry) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AccruedInterestTableEntry) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end AccruedInterestTableEntry

/-- Indexation Table Entry: 16 bytes -/
structure IndexationTableEntry where
  productId : BitVec 32
  indexationTableEntryDate : BitVec 32
  indexationTableEntryValue : BitVec 64
  deriving DecidableEq, Repr

namespace IndexationTableEntry

def encode (message : IndexationTableEntry) : List UInt8 :=
  encodeUIntLE 4 message.productId
    ++ (encodeUIntLE 4 message.indexationTableEntryDate
    ++ (encodeUIntLE 8 message.indexationTableEntryValue))

def decode (bytes : List UInt8) : Option (IndexationTableEntry × List UInt8) := do
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (indexationTableEntryDate, bytes) ← decodeUIntLE 4 bytes
  let (indexationTableEntryValue, bytes) ← decodeUIntLE 8 bytes
  pure ({ productId, indexationTableEntryDate, indexationTableEntryValue }, bytes)

@[simp] theorem encode_length (message : IndexationTableEntry) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : IndexationTableEntry) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IndexationTableEntry) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end IndexationTableEntry

/-- Product Identification Public Product Identification: 31 bytes -/
structure ProductIdentificationPublicProductIdentification where
  productIdentificationProductIdentification : Alpha 30
  productIdentificationType : BitVec 8
  deriving DecidableEq, Repr

namespace ProductIdentificationPublicProductIdentification

def encode (message : ProductIdentificationPublicProductIdentification) : List UInt8 :=
  Alpha.encode message.productIdentificationProductIdentification
    ++ (encodeUIntLE 1 message.productIdentificationType)

def decode (bytes : List UInt8) : Option (ProductIdentificationPublicProductIdentification × List UInt8) := do
  let (productIdentificationProductIdentification, bytes) ← Alpha.decode 30 bytes
  let (productIdentificationType, bytes) ← decodeUIntLE 1 bytes
  pure ({ productIdentificationProductIdentification, productIdentificationType }, bytes)

@[simp] theorem encode_length (message : ProductIdentificationPublicProductIdentification) : (encode message).length = 31 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : ProductIdentificationPublicProductIdentification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ProductIdentificationPublicProductIdentification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ProductIdentificationPublicProductIdentification

/-- Index Underlying: 32 bytes -/
structure IndexUnderlying where
  productIdentificationPublicProductIdentification : ProductIdentificationPublicProductIdentification
  indexUnderlyingType : BitVec 8
  deriving DecidableEq, Repr

namespace IndexUnderlying

def encode (message : IndexUnderlying) : List UInt8 :=
  ProductIdentificationPublicProductIdentification.encode message.productIdentificationPublicProductIdentification
    ++ (encodeUIntLE 1 message.indexUnderlyingType)

def decode (bytes : List UInt8) : Option (IndexUnderlying × List UInt8) := do
  let (productIdentificationPublicProductIdentification, bytes) ← ProductIdentificationPublicProductIdentification.decode bytes
  let (indexUnderlyingType, bytes) ← decodeUIntLE 1 bytes
  pure ({ productIdentificationPublicProductIdentification, indexUnderlyingType }, bytes)

@[simp] theorem encode_length (message : IndexUnderlying) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, ProductIdentificationPublicProductIdentification.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : IndexUnderlying) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IndexUnderlying) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ProductIdentificationPublicProductIdentification.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end IndexUnderlying

/-- Items: 32 bytes -/
structure Items where
  indexUnderlying : IndexUnderlying
  deriving DecidableEq, Repr

namespace Items

def encode (message : Items) : List UInt8 :=
  IndexUnderlying.encode message.indexUnderlying

def decode (bytes : List UInt8) : Option (Items × List UInt8) := do
  let (indexUnderlying, bytes) ← IndexUnderlying.decode bytes
  pure ({ indexUnderlying }, bytes)

@[simp] theorem encode_length (message : Items) : (encode message).length = 32 := by
  unfold encode
  simp only [IndexUnderlying.encode_length]

theorem encode_length_pos (message : Items) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Items) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [IndexUnderlying.decode_encode, some_bind]
  rfl

end Items

/-- Index Underlyings: 97 bytes -/
structure IndexUnderlyings where
  count : BitVec 8
  items : Exact 3 Items
  deriving DecidableEq, Repr

namespace IndexUnderlyings

def encode (message : IndexUnderlyings) : List UInt8 :=
  encodeUIntLE 1 message.count
    ++ (encodeMany Items.encode message.items.val)

def decode (bytes : List UInt8) : Option (IndexUnderlyings × List UInt8) := do
  let (count, bytes) ← decodeUIntLE 1 bytes
  let (items_, bytes) ← decodeMany Items.decode 3 bytes
  if fits_items : items_.length = 3 then
    pure ({ count, items := ⟨items_, fits_items⟩ }, bytes)
  else none

@[simp] theorem encode_length (message : IndexUnderlyings) : (encode message).length = 97 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeMany_length_const Items.encode 32 Items.encode_length, message.items.length_eq]

theorem encode_length_pos (message : IndexUnderlyings) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IndexUnderlyings) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_exact 3 Items.encode Items.decode Items.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.items.length_eq]
  rfl

end IndexUnderlyings

/-- Index Params: 145 bytes -/
structure IndexParams where
  instrumentId : BitVec 32
  indexBaseValue : BitVec 64
  indexBaseCapitalisation : BitVec 64
  indexBaseDate : BitVec 32
  correctionCoefficient : BitVec 64
  numOfComponents : BitVec 16
  indexPublicationSchedule : BitVec 8
  indexType : BitVec 8
  presenceFlagsIndexParamsPresenceFlags : BitVec 8
  daysSinceLastPublication : BitVec 8
  numberOfDividends : BitVec 16
  indexUnderlyings : IndexUnderlyings
  publicationOrder : BitVec 16
  currency : BitVec 16
  dateValidity : BitVec 32
  deriving DecidableEq, Repr

namespace IndexParams

def encode (message : IndexParams) : List UInt8 :=
  encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 8 message.indexBaseValue
    ++ (encodeUIntLE 8 message.indexBaseCapitalisation
    ++ (encodeUIntLE 4 message.indexBaseDate
    ++ (encodeUIntLE 8 message.correctionCoefficient
    ++ (encodeUIntLE 2 message.numOfComponents
    ++ (encodeUIntLE 1 message.indexPublicationSchedule
    ++ (encodeUIntLE 1 message.indexType
    ++ (encodeUIntLE 1 message.presenceFlagsIndexParamsPresenceFlags
    ++ (encodeUIntLE 1 message.daysSinceLastPublication
    ++ (encodeUIntLE 2 message.numberOfDividends
    ++ (IndexUnderlyings.encode message.indexUnderlyings
    ++ (encodeUIntLE 2 message.publicationOrder
    ++ (encodeUIntLE 2 message.currency
    ++ (encodeUIntLE 4 message.dateValidity))))))))))))))

def decode (bytes : List UInt8) : Option (IndexParams × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (indexBaseValue, bytes) ← decodeUIntLE 8 bytes
  let (indexBaseCapitalisation, bytes) ← decodeUIntLE 8 bytes
  let (indexBaseDate, bytes) ← decodeUIntLE 4 bytes
  let (correctionCoefficient, bytes) ← decodeUIntLE 8 bytes
  let (numOfComponents, bytes) ← decodeUIntLE 2 bytes
  let (indexPublicationSchedule, bytes) ← decodeUIntLE 1 bytes
  let (indexType, bytes) ← decodeUIntLE 1 bytes
  let (presenceFlagsIndexParamsPresenceFlags, bytes) ← decodeUIntLE 1 bytes
  let (daysSinceLastPublication, bytes) ← decodeUIntLE 1 bytes
  let (numberOfDividends, bytes) ← decodeUIntLE 2 bytes
  let (indexUnderlyings, bytes) ← IndexUnderlyings.decode bytes
  let (publicationOrder, bytes) ← decodeUIntLE 2 bytes
  let (currency, bytes) ← decodeUIntLE 2 bytes
  let (dateValidity, bytes) ← decodeUIntLE 4 bytes
  pure ({ instrumentId, indexBaseValue, indexBaseCapitalisation, indexBaseDate, correctionCoefficient, numOfComponents, indexPublicationSchedule, indexType, presenceFlagsIndexParamsPresenceFlags, daysSinceLastPublication, numberOfDividends, indexUnderlyings, publicationOrder, currency, dateValidity }, bytes)

@[simp] theorem encode_length (message : IndexParams) : (encode message).length = 145 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, IndexUnderlyings.encode_length]

theorem encode_length_pos (message : IndexParams) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IndexParams) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, IndexUnderlyings.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end IndexParams

/-- Public Product Identification: 31 bytes -/
structure PublicProductIdentification where
  productIdentificationProductIdentification : Alpha 30
  productIdentificationType : BitVec 8
  deriving DecidableEq, Repr

namespace PublicProductIdentification

def encode (message : PublicProductIdentification) : List UInt8 :=
  Alpha.encode message.productIdentificationProductIdentification
    ++ (encodeUIntLE 1 message.productIdentificationType)

def decode (bytes : List UInt8) : Option (PublicProductIdentification × List UInt8) := do
  let (productIdentificationProductIdentification, bytes) ← Alpha.decode 30 bytes
  let (productIdentificationType, bytes) ← decodeUIntLE 1 bytes
  pure ({ productIdentificationProductIdentification, productIdentificationType }, bytes)

@[simp] theorem encode_length (message : PublicProductIdentification) : (encode message).length = 31 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : PublicProductIdentification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PublicProductIdentification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end PublicProductIdentification

/-- Index Portfolio Entry: 59 bytes -/
structure IndexPortfolioEntry where
  id : BitVec 32
  indexId : BitVec 32
  presenceFlagsIndexPortfolioEntryPresenceFlags : BitVec 8
  instrumentId : BitVec 32
  publicProductIdentification : PublicProductIdentification
  mic : Alpha 4
  currency : BitVec 16
  instrumentPacket : BitVec 64
  suspended : BitVec 8
  deriving DecidableEq, Repr

namespace IndexPortfolioEntry

def encode (message : IndexPortfolioEntry) : List UInt8 :=
  encodeUIntLE 4 message.id
    ++ (encodeUIntLE 4 message.indexId
    ++ (encodeUIntLE 1 message.presenceFlagsIndexPortfolioEntryPresenceFlags
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (PublicProductIdentification.encode message.publicProductIdentification
    ++ (Alpha.encode message.mic
    ++ (encodeUIntLE 2 message.currency
    ++ (encodeUIntLE 8 message.instrumentPacket
    ++ (encodeUIntLE 1 message.suspended))))))))

def decode (bytes : List UInt8) : Option (IndexPortfolioEntry × List UInt8) := do
  let (id, bytes) ← decodeUIntLE 4 bytes
  let (indexId, bytes) ← decodeUIntLE 4 bytes
  let (presenceFlagsIndexPortfolioEntryPresenceFlags, bytes) ← decodeUIntLE 1 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (publicProductIdentification, bytes) ← PublicProductIdentification.decode bytes
  let (mic, bytes) ← Alpha.decode 4 bytes
  let (currency, bytes) ← decodeUIntLE 2 bytes
  let (instrumentPacket, bytes) ← decodeUIntLE 8 bytes
  let (suspended, bytes) ← decodeUIntLE 1 bytes
  pure ({ id, indexId, presenceFlagsIndexPortfolioEntryPresenceFlags, instrumentId, publicProductIdentification, mic, currency, instrumentPacket, suspended }, bytes)

@[simp] theorem encode_length (message : IndexPortfolioEntry) : (encode message).length = 59 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, PublicProductIdentification.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : IndexPortfolioEntry) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IndexPortfolioEntry) (rest : List UInt8) :
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
  rw [List.append_assoc, PublicProductIdentification.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end IndexPortfolioEntry

/-- Auction Summary: 21 bytes -/
structure AuctionSummary where
  instrumentId : BitVec 32
  price : BitVec 64
  quantity : BitVec 64
  auctionType : BitVec 8
  deriving DecidableEq, Repr

namespace AuctionSummary

def encode (message : AuctionSummary) : List UInt8 :=
  encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.quantity
    ++ (encodeUIntLE 1 message.auctionType)))

def decode (bytes : List UInt8) : Option (AuctionSummary × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (quantity, bytes) ← decodeUIntLE 8 bytes
  let (auctionType, bytes) ← decodeUIntLE 1 bytes
  pure ({ instrumentId, price, quantity, auctionType }, bytes)

@[simp] theorem encode_length (message : AuctionSummary) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : AuctionSummary) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AuctionSummary) (rest : List UInt8) :
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

end AuctionSummary

/-- Auction Update: 68 bytes -/
structure AuctionUpdate where
  instrumentId : BitVec 32
  indicativeMatchingPrice : BitVec 64
  indicativeMatchingVolume : BitVec 64
  totalSellQuantityAtImp : BitVec 64
  totalBuyQuantityAtImp : BitVec 64
  bestSellLevel : BitVec 64
  bestSellLevelQuantity : BitVec 64
  bestBuyLevel : BitVec 64
  bestBuyLevelQuantity : BitVec 64
  deriving DecidableEq, Repr

namespace AuctionUpdate

def encode (message : AuctionUpdate) : List UInt8 :=
  encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 8 message.indicativeMatchingPrice
    ++ (encodeUIntLE 8 message.indicativeMatchingVolume
    ++ (encodeUIntLE 8 message.totalSellQuantityAtImp
    ++ (encodeUIntLE 8 message.totalBuyQuantityAtImp
    ++ (encodeUIntLE 8 message.bestSellLevel
    ++ (encodeUIntLE 8 message.bestSellLevelQuantity
    ++ (encodeUIntLE 8 message.bestBuyLevel
    ++ (encodeUIntLE 8 message.bestBuyLevelQuantity))))))))

def decode (bytes : List UInt8) : Option (AuctionUpdate × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (indicativeMatchingPrice, bytes) ← decodeUIntLE 8 bytes
  let (indicativeMatchingVolume, bytes) ← decodeUIntLE 8 bytes
  let (totalSellQuantityAtImp, bytes) ← decodeUIntLE 8 bytes
  let (totalBuyQuantityAtImp, bytes) ← decodeUIntLE 8 bytes
  let (bestSellLevel, bytes) ← decodeUIntLE 8 bytes
  let (bestSellLevelQuantity, bytes) ← decodeUIntLE 8 bytes
  let (bestBuyLevel, bytes) ← decodeUIntLE 8 bytes
  let (bestBuyLevelQuantity, bytes) ← decodeUIntLE 8 bytes
  pure ({ instrumentId, indicativeMatchingPrice, indicativeMatchingVolume, totalSellQuantityAtImp, totalBuyQuantityAtImp, bestSellLevel, bestSellLevelQuantity, bestBuyLevel, bestBuyLevelQuantity }, bytes)

@[simp] theorem encode_length (message : AuctionUpdate) : (encode message).length = 68 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : AuctionUpdate) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AuctionUpdate) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end AuctionUpdate

/-- Price Level: 31 bytes -/
structure PriceLevel where
  isEncrypted : BitVec 8
  encryptionOffset : BitVec 64
  encryptionKeyId : BitVec 32
  price : BitVec 64
  quantity : BitVec 64
  orderCount : BitVec 16
  deriving DecidableEq, Repr

namespace PriceLevel

def encode (message : PriceLevel) : List UInt8 :=
  encodeUIntLE 1 message.isEncrypted
    ++ (encodeUIntLE 8 message.encryptionOffset
    ++ (encodeUIntLE 4 message.encryptionKeyId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.quantity
    ++ (encodeUIntLE 2 message.orderCount)))))

def decode (bytes : List UInt8) : Option (PriceLevel × List UInt8) := do
  let (isEncrypted, bytes) ← decodeUIntLE 1 bytes
  let (encryptionOffset, bytes) ← decodeUIntLE 8 bytes
  let (encryptionKeyId, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (quantity, bytes) ← decodeUIntLE 8 bytes
  let (orderCount, bytes) ← decodeUIntLE 2 bytes
  pure ({ isEncrypted, encryptionOffset, encryptionKeyId, price, quantity, orderCount }, bytes)

@[simp] theorem encode_length (message : PriceLevel) : (encode message).length = 31 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : PriceLevel) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PriceLevel) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end PriceLevel

/-- Buy: 31 bytes -/
structure Buy where
  priceLevel : PriceLevel
  deriving DecidableEq, Repr

namespace Buy

def encode (message : Buy) : List UInt8 :=
  PriceLevel.encode message.priceLevel

def decode (bytes : List UInt8) : Option (Buy × List UInt8) := do
  let (priceLevel, bytes) ← PriceLevel.decode bytes
  pure ({ priceLevel }, bytes)

@[simp] theorem encode_length (message : Buy) : (encode message).length = 31 := by
  unfold encode
  simp only [PriceLevel.encode_length]

theorem encode_length_pos (message : Buy) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Buy) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [PriceLevel.decode_encode, some_bind]
  rfl

end Buy

/-- Sell: 31 bytes -/
structure Sell where
  priceLevel : PriceLevel
  deriving DecidableEq, Repr

namespace Sell

def encode (message : Sell) : List UInt8 :=
  PriceLevel.encode message.priceLevel

def decode (bytes : List UInt8) : Option (Sell × List UInt8) := do
  let (priceLevel, bytes) ← PriceLevel.decode bytes
  pure ({ priceLevel }, bytes)

@[simp] theorem encode_length (message : Sell) : (encode message).length = 31 := by
  unfold encode
  simp only [PriceLevel.encode_length]

theorem encode_length_pos (message : Sell) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Sell) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [PriceLevel.decode_encode, some_bind]
  rfl

end Sell

/-- Price Level Snapshot: 317 bytes -/
structure PriceLevelSnapshot where
  instrumentId : BitVec 32
  maxDepth : BitVec 8
  mmBuyQuoteLevel : BitVec 8
  mmSellQuoteLevel : BitVec 8
  buy : Exact 5 Buy
  sell : Exact 5 Sell
  deriving DecidableEq, Repr

namespace PriceLevelSnapshot

def encode (message : PriceLevelSnapshot) : List UInt8 :=
  encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 1 message.maxDepth
    ++ (encodeUIntLE 1 message.mmBuyQuoteLevel
    ++ (encodeUIntLE 1 message.mmSellQuoteLevel
    ++ (encodeMany Buy.encode message.buy.val
    ++ (encodeMany Sell.encode message.sell.val)))))

def decode (bytes : List UInt8) : Option (PriceLevelSnapshot × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (maxDepth, bytes) ← decodeUIntLE 1 bytes
  let (mmBuyQuoteLevel, bytes) ← decodeUIntLE 1 bytes
  let (mmSellQuoteLevel, bytes) ← decodeUIntLE 1 bytes
  let (buy_, bytes) ← decodeMany Buy.decode 5 bytes
  let (sell_, bytes) ← decodeMany Sell.decode 5 bytes
  if fits_buy : buy_.length = 5 then
    if fits_sell : sell_.length = 5 then
      pure ({ instrumentId, maxDepth, mmBuyQuoteLevel, mmSellQuoteLevel, buy := ⟨buy_, fits_buy⟩, sell := ⟨sell_, fits_sell⟩ }, bytes)
    else none
  else none

@[simp] theorem encode_length (message : PriceLevelSnapshot) : (encode message).length = 317 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeMany_length_const Buy.encode 31 Buy.encode_length, message.buy.length_eq, encodeMany_length_const Sell.encode 31 Sell.encode_length, message.sell.length_eq]

theorem encode_length_pos (message : PriceLevelSnapshot) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PriceLevelSnapshot) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeMany_exact 5 Buy.encode Buy.decode Buy.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_exact 5 Sell.encode Sell.decode Sell.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.buy.length_eq, dite_eq_left message.sell.length_eq]
  rfl

end PriceLevelSnapshot

/-- Top Price Level Update: 23 bytes -/
structure TopPriceLevelUpdate where
  instrumentId : BitVec 32
  price : BitVec 64
  quantity : BitVec 64
  side : BitVec 8
  orderCount : BitVec 16
  deriving DecidableEq, Repr

namespace TopPriceLevelUpdate

def encode (message : TopPriceLevelUpdate) : List UInt8 :=
  encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.quantity
    ++ (encodeUIntLE 1 message.side
    ++ (encodeUIntLE 2 message.orderCount))))

def decode (bytes : List UInt8) : Option (TopPriceLevelUpdate × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (quantity, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← decodeUIntLE 1 bytes
  let (orderCount, bytes) ← decodeUIntLE 2 bytes
  pure ({ instrumentId, price, quantity, side, orderCount }, bytes)

@[simp] theorem encode_length (message : TopPriceLevelUpdate) : (encode message).length = 23 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : TopPriceLevelUpdate) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TopPriceLevelUpdate) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TopPriceLevelUpdate

/-- Trade: 178 bytes -/
structure Trade where
  instrumentId : BitVec 32
  settlementValueValue : BitVec 64
  settlementDate : BitVec 32
  tradingTimestamp : BitVec 64
  publicProductIdentification : PublicProductIdentification
  price : BitVec 64
  priceCurrency : BitVec 16
  priceNotation : BitVec 8
  quantity : BitVec 64
  nominalValueValue : BitVec 64
  nominalCurrency : BitVec 16
  mic : Alpha 4
  publicationTimestamp : BitVec 64
  tradeId : BitVec 32
  tradeToBeCleared : BitVec 8
  pctChange : BitVec 64
  vwap : BitVec 64
  noTrades : BitVec 64
  totalVolume : BitVec 64
  totalValue : BitVec 64
  openingPrice : BitVec 64
  maxPrice : BitVec 64
  minPrice : BitVec 64
  mmtMarketMechanism : BitVec 8
  mmtTradingMode : BitVec 8
  mmtTransactionCategory : BitVec 8
  mmtNegotiationIndicator : BitVec 8
  mmtAgencyCrossTradeIndicator : BitVec 8
  mmtModificationIndicator : BitVec 8
  mmtBenchmarkReferencePriceIndicator : BitVec 8
  mmtSpecialDividendIndicator : BitVec 8
  mmtOffBookAutomatedIndicator : BitVec 8
  mmtOrdinaryTradeIndicator : BitVec 8
  mmtAlgorithmicIndicator : BitVec 8
  mmtPostTradeDeferralReason : BitVec 8
  mmtPostTradeDeferralType : BitVec 8
  deriving DecidableEq, Repr

namespace Trade

def encode (message : Trade) : List UInt8 :=
  encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 8 message.settlementValueValue
    ++ (encodeUIntLE 4 message.settlementDate
    ++ (encodeUIntLE 8 message.tradingTimestamp
    ++ (PublicProductIdentification.encode message.publicProductIdentification
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 2 message.priceCurrency
    ++ (encodeUIntLE 1 message.priceNotation
    ++ (encodeUIntLE 8 message.quantity
    ++ (encodeUIntLE 8 message.nominalValueValue
    ++ (encodeUIntLE 2 message.nominalCurrency
    ++ (Alpha.encode message.mic
    ++ (encodeUIntLE 8 message.publicationTimestamp
    ++ (encodeUIntLE 4 message.tradeId
    ++ (encodeUIntLE 1 message.tradeToBeCleared
    ++ (encodeUIntLE 8 message.pctChange
    ++ (encodeUIntLE 8 message.vwap
    ++ (encodeUIntLE 8 message.noTrades
    ++ (encodeUIntLE 8 message.totalVolume
    ++ (encodeUIntLE 8 message.totalValue
    ++ (encodeUIntLE 8 message.openingPrice
    ++ (encodeUIntLE 8 message.maxPrice
    ++ (encodeUIntLE 8 message.minPrice
    ++ (encodeUIntLE 1 message.mmtMarketMechanism
    ++ (encodeUIntLE 1 message.mmtTradingMode
    ++ (encodeUIntLE 1 message.mmtTransactionCategory
    ++ (encodeUIntLE 1 message.mmtNegotiationIndicator
    ++ (encodeUIntLE 1 message.mmtAgencyCrossTradeIndicator
    ++ (encodeUIntLE 1 message.mmtModificationIndicator
    ++ (encodeUIntLE 1 message.mmtBenchmarkReferencePriceIndicator
    ++ (encodeUIntLE 1 message.mmtSpecialDividendIndicator
    ++ (encodeUIntLE 1 message.mmtOffBookAutomatedIndicator
    ++ (encodeUIntLE 1 message.mmtOrdinaryTradeIndicator
    ++ (encodeUIntLE 1 message.mmtAlgorithmicIndicator
    ++ (encodeUIntLE 1 message.mmtPostTradeDeferralReason
    ++ (encodeUIntLE 1 message.mmtPostTradeDeferralType)))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (Trade × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (settlementValueValue, bytes) ← decodeUIntLE 8 bytes
  let (settlementDate, bytes) ← decodeUIntLE 4 bytes
  let (tradingTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (publicProductIdentification, bytes) ← PublicProductIdentification.decode bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (priceCurrency, bytes) ← decodeUIntLE 2 bytes
  let (priceNotation, bytes) ← decodeUIntLE 1 bytes
  let (quantity, bytes) ← decodeUIntLE 8 bytes
  let (nominalValueValue, bytes) ← decodeUIntLE 8 bytes
  let (nominalCurrency, bytes) ← decodeUIntLE 2 bytes
  let (mic, bytes) ← Alpha.decode 4 bytes
  let (publicationTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (tradeToBeCleared, bytes) ← decodeUIntLE 1 bytes
  let (pctChange, bytes) ← decodeUIntLE 8 bytes
  let (vwap, bytes) ← decodeUIntLE 8 bytes
  let (noTrades, bytes) ← decodeUIntLE 8 bytes
  let (totalVolume, bytes) ← decodeUIntLE 8 bytes
  let (totalValue, bytes) ← decodeUIntLE 8 bytes
  let (openingPrice, bytes) ← decodeUIntLE 8 bytes
  let (maxPrice, bytes) ← decodeUIntLE 8 bytes
  let (minPrice, bytes) ← decodeUIntLE 8 bytes
  let (mmtMarketMechanism, bytes) ← decodeUIntLE 1 bytes
  let (mmtTradingMode, bytes) ← decodeUIntLE 1 bytes
  let (mmtTransactionCategory, bytes) ← decodeUIntLE 1 bytes
  let (mmtNegotiationIndicator, bytes) ← decodeUIntLE 1 bytes
  let (mmtAgencyCrossTradeIndicator, bytes) ← decodeUIntLE 1 bytes
  let (mmtModificationIndicator, bytes) ← decodeUIntLE 1 bytes
  let (mmtBenchmarkReferencePriceIndicator, bytes) ← decodeUIntLE 1 bytes
  let (mmtSpecialDividendIndicator, bytes) ← decodeUIntLE 1 bytes
  let (mmtOffBookAutomatedIndicator, bytes) ← decodeUIntLE 1 bytes
  let (mmtOrdinaryTradeIndicator, bytes) ← decodeUIntLE 1 bytes
  let (mmtAlgorithmicIndicator, bytes) ← decodeUIntLE 1 bytes
  let (mmtPostTradeDeferralReason, bytes) ← decodeUIntLE 1 bytes
  let (mmtPostTradeDeferralType, bytes) ← decodeUIntLE 1 bytes
  pure ({ instrumentId, settlementValueValue, settlementDate, tradingTimestamp, publicProductIdentification, price, priceCurrency, priceNotation, quantity, nominalValueValue, nominalCurrency, mic, publicationTimestamp, tradeId, tradeToBeCleared, pctChange, vwap, noTrades, totalVolume, totalValue, openingPrice, maxPrice, minPrice, mmtMarketMechanism, mmtTradingMode, mmtTransactionCategory, mmtNegotiationIndicator, mmtAgencyCrossTradeIndicator, mmtModificationIndicator, mmtBenchmarkReferencePriceIndicator, mmtSpecialDividendIndicator, mmtOffBookAutomatedIndicator, mmtOrdinaryTradeIndicator, mmtAlgorithmicIndicator, mmtPostTradeDeferralReason, mmtPostTradeDeferralType }, bytes)

@[simp] theorem encode_length (message : Trade) : (encode message).length = 178 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, PublicProductIdentification.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : Trade) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
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
  rw [List.append_assoc, PublicProductIdentification.decode_encode, some_bind]
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

end Trade

/-- Position Report: 40 bytes -/
structure PositionReport where
  publicProductIdentification : PublicProductIdentification
  posType : BitVec 8
  openPositions : BitVec 32
  tradeId : BitVec 32
  deriving DecidableEq, Repr

namespace PositionReport

def encode (message : PositionReport) : List UInt8 :=
  PublicProductIdentification.encode message.publicProductIdentification
    ++ (encodeUIntLE 1 message.posType
    ++ (encodeUIntLE 4 message.openPositions
    ++ (encodeUIntLE 4 message.tradeId)))

def decode (bytes : List UInt8) : Option (PositionReport × List UInt8) := do
  let (publicProductIdentification, bytes) ← PublicProductIdentification.decode bytes
  let (posType, bytes) ← decodeUIntLE 1 bytes
  let (openPositions, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  pure ({ publicProductIdentification, posType, openPositions, tradeId }, bytes)

@[simp] theorem encode_length (message : PositionReport) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, PublicProductIdentification.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : PositionReport) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PositionReport) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, PublicProductIdentification.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end PositionReport

/-- Instrument Status Change: 11 bytes -/
structure InstrumentStatusChange where
  instrumentId : BitVec 32
  tradingPhaseId : BitVec 32
  tradingPhaseType : BitVec 8
  status : BitVec 8
  stressedMarket : BitVec 8
  deriving DecidableEq, Repr

namespace InstrumentStatusChange

def encode (message : InstrumentStatusChange) : List UInt8 :=
  encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 4 message.tradingPhaseId
    ++ (encodeUIntLE 1 message.tradingPhaseType
    ++ (encodeUIntLE 1 message.status
    ++ (encodeUIntLE 1 message.stressedMarket))))

def decode (bytes : List UInt8) : Option (InstrumentStatusChange × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (tradingPhaseId, bytes) ← decodeUIntLE 4 bytes
  let (tradingPhaseType, bytes) ← decodeUIntLE 1 bytes
  let (status, bytes) ← decodeUIntLE 1 bytes
  let (stressedMarket, bytes) ← decodeUIntLE 1 bytes
  pure ({ instrumentId, tradingPhaseId, tradingPhaseType, status, stressedMarket }, bytes)

@[simp] theorem encode_length (message : InstrumentStatusChange) : (encode message).length = 11 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : InstrumentStatusChange) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentStatusChange) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end InstrumentStatusChange

/-- Order Collars: 45 bytes -/
structure OrderCollars where
  instrumentId : BitVec 32
  collarType : BitVec 8
  price : BitVec 64
  lowerBid : BitVec 64
  upperBid : BitVec 64
  lowerAsk : BitVec 64
  upperAsk : BitVec 64
  deriving DecidableEq, Repr

namespace OrderCollars

def encode (message : OrderCollars) : List UInt8 :=
  encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 1 message.collarType
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.lowerBid
    ++ (encodeUIntLE 8 message.upperBid
    ++ (encodeUIntLE 8 message.lowerAsk
    ++ (encodeUIntLE 8 message.upperAsk))))))

def decode (bytes : List UInt8) : Option (OrderCollars × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (collarType, bytes) ← decodeUIntLE 1 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (lowerBid, bytes) ← decodeUIntLE 8 bytes
  let (upperBid, bytes) ← decodeUIntLE 8 bytes
  let (lowerAsk, bytes) ← decodeUIntLE 8 bytes
  let (upperAsk, bytes) ← decodeUIntLE 8 bytes
  pure ({ instrumentId, collarType, price, lowerBid, upperBid, lowerAsk, upperAsk }, bytes)

@[simp] theorem encode_length (message : OrderCollars) : (encode message).length = 45 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderCollars) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCollars) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderCollars

/-- Trade Collars: 29 bytes -/
structure TradeCollars where
  instrumentId : BitVec 32
  collarType : BitVec 8
  price : BitVec 64
  lower : BitVec 64
  upper : BitVec 64
  deriving DecidableEq, Repr

namespace TradeCollars

def encode (message : TradeCollars) : List UInt8 :=
  encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 1 message.collarType
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.lower
    ++ (encodeUIntLE 8 message.upper))))

def decode (bytes : List UInt8) : Option (TradeCollars × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (collarType, bytes) ← decodeUIntLE 1 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (lower, bytes) ← decodeUIntLE 8 bytes
  let (upper, bytes) ← decodeUIntLE 8 bytes
  pure ({ instrumentId, collarType, price, lower, upper }, bytes)

@[simp] theorem encode_length (message : TradeCollars) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : TradeCollars) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCollars) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeCollars

/-- Instrument Summary: 95 bytes -/
structure InstrumentSummary where
  instrumentId : BitVec 32
  lastTradedPrice : BitVec 64
  closingPrice : BitVec 64
  closingPriceType : BitVec 8
  adjustedClosingPrice : BitVec 64
  adjustedClosingPriceReason : BitVec 8
  pctChange : BitVec 64
  vwap : BitVec 64
  noTrades : BitVec 64
  totalVolume : BitVec 64
  totalValue : BitVec 64
  openingPrice : BitVec 64
  maxPrice : BitVec 64
  minPrice : BitVec 64
  isCorrection : BitVec 8
  deriving DecidableEq, Repr

namespace InstrumentSummary

def encode (message : InstrumentSummary) : List UInt8 :=
  encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 8 message.lastTradedPrice
    ++ (encodeUIntLE 8 message.closingPrice
    ++ (encodeUIntLE 1 message.closingPriceType
    ++ (encodeUIntLE 8 message.adjustedClosingPrice
    ++ (encodeUIntLE 1 message.adjustedClosingPriceReason
    ++ (encodeUIntLE 8 message.pctChange
    ++ (encodeUIntLE 8 message.vwap
    ++ (encodeUIntLE 8 message.noTrades
    ++ (encodeUIntLE 8 message.totalVolume
    ++ (encodeUIntLE 8 message.totalValue
    ++ (encodeUIntLE 8 message.openingPrice
    ++ (encodeUIntLE 8 message.maxPrice
    ++ (encodeUIntLE 8 message.minPrice
    ++ (encodeUIntLE 1 message.isCorrection))))))))))))))

def decode (bytes : List UInt8) : Option (InstrumentSummary × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (lastTradedPrice, bytes) ← decodeUIntLE 8 bytes
  let (closingPrice, bytes) ← decodeUIntLE 8 bytes
  let (closingPriceType, bytes) ← decodeUIntLE 1 bytes
  let (adjustedClosingPrice, bytes) ← decodeUIntLE 8 bytes
  let (adjustedClosingPriceReason, bytes) ← decodeUIntLE 1 bytes
  let (pctChange, bytes) ← decodeUIntLE 8 bytes
  let (vwap, bytes) ← decodeUIntLE 8 bytes
  let (noTrades, bytes) ← decodeUIntLE 8 bytes
  let (totalVolume, bytes) ← decodeUIntLE 8 bytes
  let (totalValue, bytes) ← decodeUIntLE 8 bytes
  let (openingPrice, bytes) ← decodeUIntLE 8 bytes
  let (maxPrice, bytes) ← decodeUIntLE 8 bytes
  let (minPrice, bytes) ← decodeUIntLE 8 bytes
  let (isCorrection, bytes) ← decodeUIntLE 1 bytes
  pure ({ instrumentId, lastTradedPrice, closingPrice, closingPriceType, adjustedClosingPrice, adjustedClosingPriceReason, pctChange, vwap, noTrades, totalVolume, totalValue, openingPrice, maxPrice, minPrice, isCorrection }, bytes)

@[simp] theorem encode_length (message : InstrumentSummary) : (encode message).length = 95 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : InstrumentSummary) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentSummary) (rest : List UInt8) :
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

end InstrumentSummary

/-- Clob Instrument: 119 bytes -/
structure ClobInstrument where
  instrumentId : BitVec 32
  marketModelType : BitVec 8
  lastTradedPrice : BitVec 64
  closingPrice : BitVec 64
  closingPriceType : BitVec 8
  adjustedClosingPrice : BitVec 64
  adjustedClosingPriceReason : BitVec 8
  pctChange : BitVec 64
  vwap : BitVec 64
  noTrades : BitVec 64
  totalVolume : BitVec 64
  totalValue : BitVec 64
  openingPrice : BitVec 64
  maxPrice : BitVec 64
  minPrice : BitVec 64
  settlementPrice : BitVec 64
  settlementValuePrice : BitVec 64
  endTradingDate : BitVec 32
  lastTradeDate : BitVec 32
  deriving DecidableEq, Repr

namespace ClobInstrument

def encode (message : ClobInstrument) : List UInt8 :=
  encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 1 message.marketModelType
    ++ (encodeUIntLE 8 message.lastTradedPrice
    ++ (encodeUIntLE 8 message.closingPrice
    ++ (encodeUIntLE 1 message.closingPriceType
    ++ (encodeUIntLE 8 message.adjustedClosingPrice
    ++ (encodeUIntLE 1 message.adjustedClosingPriceReason
    ++ (encodeUIntLE 8 message.pctChange
    ++ (encodeUIntLE 8 message.vwap
    ++ (encodeUIntLE 8 message.noTrades
    ++ (encodeUIntLE 8 message.totalVolume
    ++ (encodeUIntLE 8 message.totalValue
    ++ (encodeUIntLE 8 message.openingPrice
    ++ (encodeUIntLE 8 message.maxPrice
    ++ (encodeUIntLE 8 message.minPrice
    ++ (encodeUIntLE 8 message.settlementPrice
    ++ (encodeUIntLE 8 message.settlementValuePrice
    ++ (encodeUIntLE 4 message.endTradingDate
    ++ (encodeUIntLE 4 message.lastTradeDate))))))))))))))))))

def decode (bytes : List UInt8) : Option (ClobInstrument × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (marketModelType, bytes) ← decodeUIntLE 1 bytes
  let (lastTradedPrice, bytes) ← decodeUIntLE 8 bytes
  let (closingPrice, bytes) ← decodeUIntLE 8 bytes
  let (closingPriceType, bytes) ← decodeUIntLE 1 bytes
  let (adjustedClosingPrice, bytes) ← decodeUIntLE 8 bytes
  let (adjustedClosingPriceReason, bytes) ← decodeUIntLE 1 bytes
  let (pctChange, bytes) ← decodeUIntLE 8 bytes
  let (vwap, bytes) ← decodeUIntLE 8 bytes
  let (noTrades, bytes) ← decodeUIntLE 8 bytes
  let (totalVolume, bytes) ← decodeUIntLE 8 bytes
  let (totalValue, bytes) ← decodeUIntLE 8 bytes
  let (openingPrice, bytes) ← decodeUIntLE 8 bytes
  let (maxPrice, bytes) ← decodeUIntLE 8 bytes
  let (minPrice, bytes) ← decodeUIntLE 8 bytes
  let (settlementPrice, bytes) ← decodeUIntLE 8 bytes
  let (settlementValuePrice, bytes) ← decodeUIntLE 8 bytes
  let (endTradingDate, bytes) ← decodeUIntLE 4 bytes
  let (lastTradeDate, bytes) ← decodeUIntLE 4 bytes
  pure ({ instrumentId, marketModelType, lastTradedPrice, closingPrice, closingPriceType, adjustedClosingPrice, adjustedClosingPriceReason, pctChange, vwap, noTrades, totalVolume, totalValue, openingPrice, maxPrice, minPrice, settlementPrice, settlementValuePrice, endTradingDate, lastTradeDate }, bytes)

@[simp] theorem encode_length (message : ClobInstrument) : (encode message).length = 119 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : ClobInstrument) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ClobInstrument) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ClobInstrument

/-- Cross Instrument: 119 bytes -/
structure CrossInstrument where
  instrumentId : BitVec 32
  marketModelType : BitVec 8
  lastTradedPrice : BitVec 64
  closingPrice : BitVec 64
  closingPriceType : BitVec 8
  adjustedClosingPrice : BitVec 64
  adjustedClosingPriceReason : BitVec 8
  pctChange : BitVec 64
  vwap : BitVec 64
  noTrades : BitVec 64
  totalVolume : BitVec 64
  totalValue : BitVec 64
  openingPrice : BitVec 64
  maxPrice : BitVec 64
  minPrice : BitVec 64
  settlementPrice : BitVec 64
  settlementValuePrice : BitVec 64
  endTradingDate : BitVec 32
  lastTradeDate : BitVec 32
  deriving DecidableEq, Repr

namespace CrossInstrument

def encode (message : CrossInstrument) : List UInt8 :=
  encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 1 message.marketModelType
    ++ (encodeUIntLE 8 message.lastTradedPrice
    ++ (encodeUIntLE 8 message.closingPrice
    ++ (encodeUIntLE 1 message.closingPriceType
    ++ (encodeUIntLE 8 message.adjustedClosingPrice
    ++ (encodeUIntLE 1 message.adjustedClosingPriceReason
    ++ (encodeUIntLE 8 message.pctChange
    ++ (encodeUIntLE 8 message.vwap
    ++ (encodeUIntLE 8 message.noTrades
    ++ (encodeUIntLE 8 message.totalVolume
    ++ (encodeUIntLE 8 message.totalValue
    ++ (encodeUIntLE 8 message.openingPrice
    ++ (encodeUIntLE 8 message.maxPrice
    ++ (encodeUIntLE 8 message.minPrice
    ++ (encodeUIntLE 8 message.settlementPrice
    ++ (encodeUIntLE 8 message.settlementValuePrice
    ++ (encodeUIntLE 4 message.endTradingDate
    ++ (encodeUIntLE 4 message.lastTradeDate))))))))))))))))))

def decode (bytes : List UInt8) : Option (CrossInstrument × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (marketModelType, bytes) ← decodeUIntLE 1 bytes
  let (lastTradedPrice, bytes) ← decodeUIntLE 8 bytes
  let (closingPrice, bytes) ← decodeUIntLE 8 bytes
  let (closingPriceType, bytes) ← decodeUIntLE 1 bytes
  let (adjustedClosingPrice, bytes) ← decodeUIntLE 8 bytes
  let (adjustedClosingPriceReason, bytes) ← decodeUIntLE 1 bytes
  let (pctChange, bytes) ← decodeUIntLE 8 bytes
  let (vwap, bytes) ← decodeUIntLE 8 bytes
  let (noTrades, bytes) ← decodeUIntLE 8 bytes
  let (totalVolume, bytes) ← decodeUIntLE 8 bytes
  let (totalValue, bytes) ← decodeUIntLE 8 bytes
  let (openingPrice, bytes) ← decodeUIntLE 8 bytes
  let (maxPrice, bytes) ← decodeUIntLE 8 bytes
  let (minPrice, bytes) ← decodeUIntLE 8 bytes
  let (settlementPrice, bytes) ← decodeUIntLE 8 bytes
  let (settlementValuePrice, bytes) ← decodeUIntLE 8 bytes
  let (endTradingDate, bytes) ← decodeUIntLE 4 bytes
  let (lastTradeDate, bytes) ← decodeUIntLE 4 bytes
  pure ({ instrumentId, marketModelType, lastTradedPrice, closingPrice, closingPriceType, adjustedClosingPrice, adjustedClosingPriceReason, pctChange, vwap, noTrades, totalVolume, totalValue, openingPrice, maxPrice, minPrice, settlementPrice, settlementValuePrice, endTradingDate, lastTradeDate }, bytes)

@[simp] theorem encode_length (message : CrossInstrument) : (encode message).length = 119 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : CrossInstrument) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CrossInstrument) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end CrossInstrument

/-- Block Instrument: 119 bytes -/
structure BlockInstrument where
  instrumentId : BitVec 32
  marketModelType : BitVec 8
  lastTradedPrice : BitVec 64
  closingPrice : BitVec 64
  closingPriceType : BitVec 8
  adjustedClosingPrice : BitVec 64
  adjustedClosingPriceReason : BitVec 8
  pctChange : BitVec 64
  vwap : BitVec 64
  noTrades : BitVec 64
  totalVolume : BitVec 64
  totalValue : BitVec 64
  openingPrice : BitVec 64
  maxPrice : BitVec 64
  minPrice : BitVec 64
  settlementPrice : BitVec 64
  settlementValuePrice : BitVec 64
  endTradingDate : BitVec 32
  lastTradeDate : BitVec 32
  deriving DecidableEq, Repr

namespace BlockInstrument

def encode (message : BlockInstrument) : List UInt8 :=
  encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 1 message.marketModelType
    ++ (encodeUIntLE 8 message.lastTradedPrice
    ++ (encodeUIntLE 8 message.closingPrice
    ++ (encodeUIntLE 1 message.closingPriceType
    ++ (encodeUIntLE 8 message.adjustedClosingPrice
    ++ (encodeUIntLE 1 message.adjustedClosingPriceReason
    ++ (encodeUIntLE 8 message.pctChange
    ++ (encodeUIntLE 8 message.vwap
    ++ (encodeUIntLE 8 message.noTrades
    ++ (encodeUIntLE 8 message.totalVolume
    ++ (encodeUIntLE 8 message.totalValue
    ++ (encodeUIntLE 8 message.openingPrice
    ++ (encodeUIntLE 8 message.maxPrice
    ++ (encodeUIntLE 8 message.minPrice
    ++ (encodeUIntLE 8 message.settlementPrice
    ++ (encodeUIntLE 8 message.settlementValuePrice
    ++ (encodeUIntLE 4 message.endTradingDate
    ++ (encodeUIntLE 4 message.lastTradeDate))))))))))))))))))

def decode (bytes : List UInt8) : Option (BlockInstrument × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (marketModelType, bytes) ← decodeUIntLE 1 bytes
  let (lastTradedPrice, bytes) ← decodeUIntLE 8 bytes
  let (closingPrice, bytes) ← decodeUIntLE 8 bytes
  let (closingPriceType, bytes) ← decodeUIntLE 1 bytes
  let (adjustedClosingPrice, bytes) ← decodeUIntLE 8 bytes
  let (adjustedClosingPriceReason, bytes) ← decodeUIntLE 1 bytes
  let (pctChange, bytes) ← decodeUIntLE 8 bytes
  let (vwap, bytes) ← decodeUIntLE 8 bytes
  let (noTrades, bytes) ← decodeUIntLE 8 bytes
  let (totalVolume, bytes) ← decodeUIntLE 8 bytes
  let (totalValue, bytes) ← decodeUIntLE 8 bytes
  let (openingPrice, bytes) ← decodeUIntLE 8 bytes
  let (maxPrice, bytes) ← decodeUIntLE 8 bytes
  let (minPrice, bytes) ← decodeUIntLE 8 bytes
  let (settlementPrice, bytes) ← decodeUIntLE 8 bytes
  let (settlementValuePrice, bytes) ← decodeUIntLE 8 bytes
  let (endTradingDate, bytes) ← decodeUIntLE 4 bytes
  let (lastTradeDate, bytes) ← decodeUIntLE 4 bytes
  pure ({ instrumentId, marketModelType, lastTradedPrice, closingPrice, closingPriceType, adjustedClosingPrice, adjustedClosingPriceReason, pctChange, vwap, noTrades, totalVolume, totalValue, openingPrice, maxPrice, minPrice, settlementPrice, settlementValuePrice, endTradingDate, lastTradeDate }, bytes)

@[simp] theorem encode_length (message : BlockInstrument) : (encode message).length = 119 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : BlockInstrument) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BlockInstrument) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end BlockInstrument

/-- Hybrid Instrument: 119 bytes -/
structure HybridInstrument where
  instrumentId : BitVec 32
  marketModelType : BitVec 8
  lastTradedPrice : BitVec 64
  closingPrice : BitVec 64
  closingPriceType : BitVec 8
  adjustedClosingPrice : BitVec 64
  adjustedClosingPriceReason : BitVec 8
  pctChange : BitVec 64
  vwap : BitVec 64
  noTrades : BitVec 64
  totalVolume : BitVec 64
  totalValue : BitVec 64
  openingPrice : BitVec 64
  maxPrice : BitVec 64
  minPrice : BitVec 64
  settlementPrice : BitVec 64
  settlementValuePrice : BitVec 64
  endTradingDate : BitVec 32
  lastTradeDate : BitVec 32
  deriving DecidableEq, Repr

namespace HybridInstrument

def encode (message : HybridInstrument) : List UInt8 :=
  encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 1 message.marketModelType
    ++ (encodeUIntLE 8 message.lastTradedPrice
    ++ (encodeUIntLE 8 message.closingPrice
    ++ (encodeUIntLE 1 message.closingPriceType
    ++ (encodeUIntLE 8 message.adjustedClosingPrice
    ++ (encodeUIntLE 1 message.adjustedClosingPriceReason
    ++ (encodeUIntLE 8 message.pctChange
    ++ (encodeUIntLE 8 message.vwap
    ++ (encodeUIntLE 8 message.noTrades
    ++ (encodeUIntLE 8 message.totalVolume
    ++ (encodeUIntLE 8 message.totalValue
    ++ (encodeUIntLE 8 message.openingPrice
    ++ (encodeUIntLE 8 message.maxPrice
    ++ (encodeUIntLE 8 message.minPrice
    ++ (encodeUIntLE 8 message.settlementPrice
    ++ (encodeUIntLE 8 message.settlementValuePrice
    ++ (encodeUIntLE 4 message.endTradingDate
    ++ (encodeUIntLE 4 message.lastTradeDate))))))))))))))))))

def decode (bytes : List UInt8) : Option (HybridInstrument × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (marketModelType, bytes) ← decodeUIntLE 1 bytes
  let (lastTradedPrice, bytes) ← decodeUIntLE 8 bytes
  let (closingPrice, bytes) ← decodeUIntLE 8 bytes
  let (closingPriceType, bytes) ← decodeUIntLE 1 bytes
  let (adjustedClosingPrice, bytes) ← decodeUIntLE 8 bytes
  let (adjustedClosingPriceReason, bytes) ← decodeUIntLE 1 bytes
  let (pctChange, bytes) ← decodeUIntLE 8 bytes
  let (vwap, bytes) ← decodeUIntLE 8 bytes
  let (noTrades, bytes) ← decodeUIntLE 8 bytes
  let (totalVolume, bytes) ← decodeUIntLE 8 bytes
  let (totalValue, bytes) ← decodeUIntLE 8 bytes
  let (openingPrice, bytes) ← decodeUIntLE 8 bytes
  let (maxPrice, bytes) ← decodeUIntLE 8 bytes
  let (minPrice, bytes) ← decodeUIntLE 8 bytes
  let (settlementPrice, bytes) ← decodeUIntLE 8 bytes
  let (settlementValuePrice, bytes) ← decodeUIntLE 8 bytes
  let (endTradingDate, bytes) ← decodeUIntLE 4 bytes
  let (lastTradeDate, bytes) ← decodeUIntLE 4 bytes
  pure ({ instrumentId, marketModelType, lastTradedPrice, closingPrice, closingPriceType, adjustedClosingPrice, adjustedClosingPriceReason, pctChange, vwap, noTrades, totalVolume, totalValue, openingPrice, maxPrice, minPrice, settlementPrice, settlementValuePrice, endTradingDate, lastTradeDate }, bytes)

@[simp] theorem encode_length (message : HybridInstrument) : (encode message).length = 119 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : HybridInstrument) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : HybridInstrument) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end HybridInstrument

/-- Product Summary: 629 bytes -/
structure ProductSummary where
  clobInstrument : ClobInstrument
  crossInstrument : CrossInstrument
  blockInstrument : BlockInstrument
  hybridInstrument : HybridInstrument
  productIdentificationType : BitVec 8
  productIdentificationProductIdentification : Alpha 30
  productId : BitVec 32
  mic : Alpha 4
  accumulatedInterest : BitVec 64
  interestRate : BitVec 64
  currency : BitVec 16
  sessionDate : BitVec 32
  tradingValueCurrency : BitVec 64
  status : BitVec 8
  sector : BitVec 16
  market : BitVec 8
  markerPriceChange : BitVec 8
  lowerLiquidity : BitVec 8
  multiplierNumber : BitVec 64
  dividendRate : BitVec 64
  delta : BitVec 64
  gamma : BitVec 64
  rho : BitVec 64
  theta : BitVec 64
  vega : BitVec 64
  volatility : BitVec 64
  optionsStrikePrice : BitVec 64
  dividend : BitVec 8
  subscriptionRight : BitVec 8
  interimDividendRight : BitVec 8
  split : BitVec 8
  quotationSystem : BitVec 8
  liquiditySupportPge : BitVec 8
  deriving DecidableEq, Repr

namespace ProductSummary

def encode (message : ProductSummary) : List UInt8 :=
  ClobInstrument.encode message.clobInstrument
    ++ (CrossInstrument.encode message.crossInstrument
    ++ (BlockInstrument.encode message.blockInstrument
    ++ (HybridInstrument.encode message.hybridInstrument
    ++ (encodeUIntLE 1 message.productIdentificationType
    ++ (Alpha.encode message.productIdentificationProductIdentification
    ++ (encodeUIntLE 4 message.productId
    ++ (Alpha.encode message.mic
    ++ (encodeUIntLE 8 message.accumulatedInterest
    ++ (encodeUIntLE 8 message.interestRate
    ++ (encodeUIntLE 2 message.currency
    ++ (encodeUIntLE 4 message.sessionDate
    ++ (encodeUIntLE 8 message.tradingValueCurrency
    ++ (encodeUIntLE 1 message.status
    ++ (encodeUIntLE 2 message.sector
    ++ (encodeUIntLE 1 message.market
    ++ (encodeUIntLE 1 message.markerPriceChange
    ++ (encodeUIntLE 1 message.lowerLiquidity
    ++ (encodeUIntLE 8 message.multiplierNumber
    ++ (encodeUIntLE 8 message.dividendRate
    ++ (encodeUIntLE 8 message.delta
    ++ (encodeUIntLE 8 message.gamma
    ++ (encodeUIntLE 8 message.rho
    ++ (encodeUIntLE 8 message.theta
    ++ (encodeUIntLE 8 message.vega
    ++ (encodeUIntLE 8 message.volatility
    ++ (encodeUIntLE 8 message.optionsStrikePrice
    ++ (encodeUIntLE 1 message.dividend
    ++ (encodeUIntLE 1 message.subscriptionRight
    ++ (encodeUIntLE 1 message.interimDividendRight
    ++ (encodeUIntLE 1 message.split
    ++ (encodeUIntLE 1 message.quotationSystem
    ++ (encodeUIntLE 1 message.liquiditySupportPge))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ProductSummary × List UInt8) := do
  let (clobInstrument, bytes) ← ClobInstrument.decode bytes
  let (crossInstrument, bytes) ← CrossInstrument.decode bytes
  let (blockInstrument, bytes) ← BlockInstrument.decode bytes
  let (hybridInstrument, bytes) ← HybridInstrument.decode bytes
  let (productIdentificationType, bytes) ← decodeUIntLE 1 bytes
  let (productIdentificationProductIdentification, bytes) ← Alpha.decode 30 bytes
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (mic, bytes) ← Alpha.decode 4 bytes
  let (accumulatedInterest, bytes) ← decodeUIntLE 8 bytes
  let (interestRate, bytes) ← decodeUIntLE 8 bytes
  let (currency, bytes) ← decodeUIntLE 2 bytes
  let (sessionDate, bytes) ← decodeUIntLE 4 bytes
  let (tradingValueCurrency, bytes) ← decodeUIntLE 8 bytes
  let (status, bytes) ← decodeUIntLE 1 bytes
  let (sector, bytes) ← decodeUIntLE 2 bytes
  let (market, bytes) ← decodeUIntLE 1 bytes
  let (markerPriceChange, bytes) ← decodeUIntLE 1 bytes
  let (lowerLiquidity, bytes) ← decodeUIntLE 1 bytes
  let (multiplierNumber, bytes) ← decodeUIntLE 8 bytes
  let (dividendRate, bytes) ← decodeUIntLE 8 bytes
  let (delta, bytes) ← decodeUIntLE 8 bytes
  let (gamma, bytes) ← decodeUIntLE 8 bytes
  let (rho, bytes) ← decodeUIntLE 8 bytes
  let (theta, bytes) ← decodeUIntLE 8 bytes
  let (vega, bytes) ← decodeUIntLE 8 bytes
  let (volatility, bytes) ← decodeUIntLE 8 bytes
  let (optionsStrikePrice, bytes) ← decodeUIntLE 8 bytes
  let (dividend, bytes) ← decodeUIntLE 1 bytes
  let (subscriptionRight, bytes) ← decodeUIntLE 1 bytes
  let (interimDividendRight, bytes) ← decodeUIntLE 1 bytes
  let (split, bytes) ← decodeUIntLE 1 bytes
  let (quotationSystem, bytes) ← decodeUIntLE 1 bytes
  let (liquiditySupportPge, bytes) ← decodeUIntLE 1 bytes
  pure ({ clobInstrument, crossInstrument, blockInstrument, hybridInstrument, productIdentificationType, productIdentificationProductIdentification, productId, mic, accumulatedInterest, interestRate, currency, sessionDate, tradingValueCurrency, status, sector, market, markerPriceChange, lowerLiquidity, multiplierNumber, dividendRate, delta, gamma, rho, theta, vega, volatility, optionsStrikePrice, dividend, subscriptionRight, interimDividendRight, split, quotationSystem, liquiditySupportPge }, bytes)

@[simp] theorem encode_length (message : ProductSummary) : (encode message).length = 629 := by
  unfold encode
  simp only [List.length_append, ClobInstrument.encode_length, CrossInstrument.encode_length, BlockInstrument.encode_length, HybridInstrument.encode_length, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : ProductSummary) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ProductSummary) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ClobInstrument.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CrossInstrument.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BlockInstrument.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, HybridInstrument.decode_encode, some_bind]
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

end ProductSummary

/-- Price Update: 31 bytes -/
structure PriceUpdate where
  instrumentId : BitVec 32
  priceUpdateType : BitVec 8
  priceYtmPresence : BitVec 16
  value : BitVec 64
  valueBid : BitVec 64
  valueAsk : BitVec 64
  deriving DecidableEq, Repr

namespace PriceUpdate

def encode (message : PriceUpdate) : List UInt8 :=
  encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 1 message.priceUpdateType
    ++ (encodeUIntLE 2 message.priceYtmPresence
    ++ (encodeUIntLE 8 message.value
    ++ (encodeUIntLE 8 message.valueBid
    ++ (encodeUIntLE 8 message.valueAsk)))))

def decode (bytes : List UInt8) : Option (PriceUpdate × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (priceUpdateType, bytes) ← decodeUIntLE 1 bytes
  let (priceYtmPresence, bytes) ← decodeUIntLE 2 bytes
  let (value, bytes) ← decodeUIntLE 8 bytes
  let (valueBid, bytes) ← decodeUIntLE 8 bytes
  let (valueAsk, bytes) ← decodeUIntLE 8 bytes
  pure ({ instrumentId, priceUpdateType, priceYtmPresence, value, valueBid, valueAsk }, bytes)

@[simp] theorem encode_length (message : PriceUpdate) : (encode message).length = 31 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : PriceUpdate) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PriceUpdate) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end PriceUpdate

/-- News: 890 bytes -/
structure News where
  marketStructureId : BitVec 32
  newsId : BitVec 32
  title : Alpha 80
  entryNumber : BitVec 8
  total : BitVec 8
  text : Alpha 800
  deriving DecidableEq, Repr

namespace News

def encode (message : News) : List UInt8 :=
  encodeUIntLE 4 message.marketStructureId
    ++ (encodeUIntLE 4 message.newsId
    ++ (Alpha.encode message.title
    ++ (encodeUIntLE 1 message.entryNumber
    ++ (encodeUIntLE 1 message.total
    ++ (Alpha.encode message.text)))))

def decode (bytes : List UInt8) : Option (News × List UInt8) := do
  let (marketStructureId, bytes) ← decodeUIntLE 4 bytes
  let (newsId, bytes) ← decodeUIntLE 4 bytes
  let (title, bytes) ← Alpha.decode 80 bytes
  let (entryNumber, bytes) ← decodeUIntLE 1 bytes
  let (total, bytes) ← decodeUIntLE 1 bytes
  let (text, bytes) ← Alpha.decode 800 bytes
  pure ({ marketStructureId, newsId, title, entryNumber, total, text }, bytes)

@[simp] theorem encode_length (message : News) : (encode message).length = 890 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : News) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : News) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end News

/-- Real Time Index: 88 bytes -/
structure RealTimeIndex where
  instrumentId : BitVec 32
  indexLevelCode : BitVec 8
  numOfActiveInstruments : BitVec 16
  indIndexOpeningPortfolio : BitVec 64
  indexValue : BitVec 64
  pctChangeIndexValPrevSession : BitVec 64
  sessionLow : BitVec 64
  sessionHigh : BitVec 64
  presenceFlagsRealTimeIndexPresenceFlags : BitVec 8
  tradingValue : BitVec 64
  indexValueBid : BitVec 64
  indexValueAsk : BitVec 64
  midSpreadIndex : BitVec 64
  differenceCentralSpread : BitVec 64
  deriving DecidableEq, Repr

namespace RealTimeIndex

def encode (message : RealTimeIndex) : List UInt8 :=
  encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 1 message.indexLevelCode
    ++ (encodeUIntLE 2 message.numOfActiveInstruments
    ++ (encodeUIntLE 8 message.indIndexOpeningPortfolio
    ++ (encodeUIntLE 8 message.indexValue
    ++ (encodeUIntLE 8 message.pctChangeIndexValPrevSession
    ++ (encodeUIntLE 8 message.sessionLow
    ++ (encodeUIntLE 8 message.sessionHigh
    ++ (encodeUIntLE 1 message.presenceFlagsRealTimeIndexPresenceFlags
    ++ (encodeUIntLE 8 message.tradingValue
    ++ (encodeUIntLE 8 message.indexValueBid
    ++ (encodeUIntLE 8 message.indexValueAsk
    ++ (encodeUIntLE 8 message.midSpreadIndex
    ++ (encodeUIntLE 8 message.differenceCentralSpread)))))))))))))

def decode (bytes : List UInt8) : Option (RealTimeIndex × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (indexLevelCode, bytes) ← decodeUIntLE 1 bytes
  let (numOfActiveInstruments, bytes) ← decodeUIntLE 2 bytes
  let (indIndexOpeningPortfolio, bytes) ← decodeUIntLE 8 bytes
  let (indexValue, bytes) ← decodeUIntLE 8 bytes
  let (pctChangeIndexValPrevSession, bytes) ← decodeUIntLE 8 bytes
  let (sessionLow, bytes) ← decodeUIntLE 8 bytes
  let (sessionHigh, bytes) ← decodeUIntLE 8 bytes
  let (presenceFlagsRealTimeIndexPresenceFlags, bytes) ← decodeUIntLE 1 bytes
  let (tradingValue, bytes) ← decodeUIntLE 8 bytes
  let (indexValueBid, bytes) ← decodeUIntLE 8 bytes
  let (indexValueAsk, bytes) ← decodeUIntLE 8 bytes
  let (midSpreadIndex, bytes) ← decodeUIntLE 8 bytes
  let (differenceCentralSpread, bytes) ← decodeUIntLE 8 bytes
  pure ({ instrumentId, indexLevelCode, numOfActiveInstruments, indIndexOpeningPortfolio, indexValue, pctChangeIndexValPrevSession, sessionLow, sessionHigh, presenceFlagsRealTimeIndexPresenceFlags, tradingValue, indexValueBid, indexValueAsk, midSpreadIndex, differenceCentralSpread }, bytes)

@[simp] theorem encode_length (message : RealTimeIndex) : (encode message).length = 88 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : RealTimeIndex) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RealTimeIndex) (rest : List UInt8) :
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

end RealTimeIndex

/-- Index Summary: 77 bytes -/
structure IndexSummary where
  instrumentId : BitVec 32
  openingIndexValue : BitVec 64
  sessionLow : BitVec 64
  sessionHigh : BitVec 64
  closingIndexValue : BitVec 64
  presenceFlagsIndexSummaryPresenceFlags : BitVec 8
  sessionAvg : BitVec 64
  pctChangeIndexValPrevSession : BitVec 64
  pctChangeIndexValPrevYear : BitVec 64
  closingCapitalisationPortfolio : BitVec 64
  indIndexOpeningPortfolio : BitVec 64
  deriving DecidableEq, Repr

namespace IndexSummary

def encode (message : IndexSummary) : List UInt8 :=
  encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 8 message.openingIndexValue
    ++ (encodeUIntLE 8 message.sessionLow
    ++ (encodeUIntLE 8 message.sessionHigh
    ++ (encodeUIntLE 8 message.closingIndexValue
    ++ (encodeUIntLE 1 message.presenceFlagsIndexSummaryPresenceFlags
    ++ (encodeUIntLE 8 message.sessionAvg
    ++ (encodeUIntLE 8 message.pctChangeIndexValPrevSession
    ++ (encodeUIntLE 8 message.pctChangeIndexValPrevYear
    ++ (encodeUIntLE 8 message.closingCapitalisationPortfolio
    ++ (encodeUIntLE 8 message.indIndexOpeningPortfolio))))))))))

def decode (bytes : List UInt8) : Option (IndexSummary × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (openingIndexValue, bytes) ← decodeUIntLE 8 bytes
  let (sessionLow, bytes) ← decodeUIntLE 8 bytes
  let (sessionHigh, bytes) ← decodeUIntLE 8 bytes
  let (closingIndexValue, bytes) ← decodeUIntLE 8 bytes
  let (presenceFlagsIndexSummaryPresenceFlags, bytes) ← decodeUIntLE 1 bytes
  let (sessionAvg, bytes) ← decodeUIntLE 8 bytes
  let (pctChangeIndexValPrevSession, bytes) ← decodeUIntLE 8 bytes
  let (pctChangeIndexValPrevYear, bytes) ← decodeUIntLE 8 bytes
  let (closingCapitalisationPortfolio, bytes) ← decodeUIntLE 8 bytes
  let (indIndexOpeningPortfolio, bytes) ← decodeUIntLE 8 bytes
  pure ({ instrumentId, openingIndexValue, sessionLow, sessionHigh, closingIndexValue, presenceFlagsIndexSummaryPresenceFlags, sessionAvg, pctChangeIndexValPrevSession, pctChangeIndexValPrevYear, closingCapitalisationPortfolio, indIndexOpeningPortfolio }, bytes)

@[simp] theorem encode_length (message : IndexSummary) : (encode message).length = 77 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : IndexSummary) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IndexSummary) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end IndexSummary

/-- Trading Session Status: 13 bytes -/
structure TradingSessionStatus where
  marketId : Alpha 4
  marketStructureId : BitVec 32
  tradingSessionEvent : BitVec 8
  date : BitVec 32
  deriving DecidableEq, Repr

namespace TradingSessionStatus

def encode (message : TradingSessionStatus) : List UInt8 :=
  Alpha.encode message.marketId
    ++ (encodeUIntLE 4 message.marketStructureId
    ++ (encodeUIntLE 1 message.tradingSessionEvent
    ++ (encodeUIntLE 4 message.date)))

def decode (bytes : List UInt8) : Option (TradingSessionStatus × List UInt8) := do
  let (marketId, bytes) ← Alpha.decode 4 bytes
  let (marketStructureId, bytes) ← decodeUIntLE 4 bytes
  let (tradingSessionEvent, bytes) ← decodeUIntLE 1 bytes
  let (date, bytes) ← decodeUIntLE 4 bytes
  pure ({ marketId, marketStructureId, tradingSessionEvent, date }, bytes)

@[simp] theorem encode_length (message : TradingSessionStatus) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : TradingSessionStatus) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradingSessionStatus) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradingSessionStatus

/-- Test Event: 201 bytes -/
structure TestEvent where
  scenarioName : Alpha 200
  eventTypeEventType : BitVec 8
  deriving DecidableEq, Repr

namespace TestEvent

def encode (message : TestEvent) : List UInt8 :=
  Alpha.encode message.scenarioName
    ++ (encodeUIntLE 1 message.eventTypeEventType)

def decode (bytes : List UInt8) : Option (TestEvent × List UInt8) := do
  let (scenarioName, bytes) ← Alpha.decode 200 bytes
  let (eventTypeEventType, bytes) ← decodeUIntLE 1 bytes
  pure ({ scenarioName, eventTypeEventType }, bytes)

@[simp] theorem encode_length (message : TestEvent) : (encode message).length = 201 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : TestEvent) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TestEvent) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TestEvent

/-- Order Add: 30 bytes -/
structure OrderAdd where
  publicOrderId : BitVec 64
  instrumentId : BitVec 32
  side : BitVec 8
  price : BitVec 64
  quantity : BitVec 64
  mmQuote : BitVec 8
  deriving DecidableEq, Repr

namespace OrderAdd

def encode (message : OrderAdd) : List UInt8 :=
  encodeUIntLE 8 message.publicOrderId
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 1 message.side
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.quantity
    ++ (encodeUIntLE 1 message.mmQuote)))))

def decode (bytes : List UInt8) : Option (OrderAdd × List UInt8) := do
  let (publicOrderId, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← decodeUIntLE 1 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (quantity, bytes) ← decodeUIntLE 8 bytes
  let (mmQuote, bytes) ← decodeUIntLE 1 bytes
  pure ({ publicOrderId, instrumentId, side, price, quantity, mmQuote }, bytes)

@[simp] theorem encode_length (message : OrderAdd) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderAdd) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderAdd) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderAdd

/-- Order Modify: 30 bytes -/
structure OrderModify where
  instrumentId : BitVec 32
  publicOrderId : BitVec 64
  price : BitVec 64
  quantity : BitVec 64
  priorityFlag : BitVec 8
  side : BitVec 8
  deriving DecidableEq, Repr

namespace OrderModify

def encode (message : OrderModify) : List UInt8 :=
  encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 8 message.publicOrderId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.quantity
    ++ (encodeUIntLE 1 message.priorityFlag
    ++ (encodeUIntLE 1 message.side)))))

def decode (bytes : List UInt8) : Option (OrderModify × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (publicOrderId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (quantity, bytes) ← decodeUIntLE 8 bytes
  let (priorityFlag, bytes) ← decodeUIntLE 1 bytes
  let (side, bytes) ← decodeUIntLE 1 bytes
  pure ({ instrumentId, publicOrderId, price, quantity, priorityFlag, side }, bytes)

@[simp] theorem encode_length (message : OrderModify) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderModify) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderModify) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderModify

/-- Order Cancel: 13 bytes -/
structure OrderCancel where
  instrumentId : BitVec 32
  publicOrderId : BitVec 64
  side : BitVec 8
  deriving DecidableEq, Repr

namespace OrderCancel

def encode (message : OrderCancel) : List UInt8 :=
  encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 8 message.publicOrderId
    ++ (encodeUIntLE 1 message.side))

def decode (bytes : List UInt8) : Option (OrderCancel × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (publicOrderId, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← decodeUIntLE 1 bytes
  pure ({ instrumentId, publicOrderId, side }, bytes)

@[simp] theorem encode_length (message : OrderCancel) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderCancel) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancel) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderCancel

/-- Order Execute: 41 bytes -/
structure OrderExecute where
  quantity : BitVec 64
  instrumentId : BitVec 32
  publicOrderId : BitVec 64
  tradeId : BitVec 32
  executionPrice : BitVec 64
  executionQuantity : BitVec 64
  side : BitVec 8
  deriving DecidableEq, Repr

namespace OrderExecute

def encode (message : OrderExecute) : List UInt8 :=
  encodeUIntLE 8 message.quantity
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 8 message.publicOrderId
    ++ (encodeUIntLE 4 message.tradeId
    ++ (encodeUIntLE 8 message.executionPrice
    ++ (encodeUIntLE 8 message.executionQuantity
    ++ (encodeUIntLE 1 message.side))))))

def decode (bytes : List UInt8) : Option (OrderExecute × List UInt8) := do
  let (quantity, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (publicOrderId, bytes) ← decodeUIntLE 8 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (executionPrice, bytes) ← decodeUIntLE 8 bytes
  let (executionQuantity, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← decodeUIntLE 1 bytes
  pure ({ quantity, instrumentId, publicOrderId, tradeId, executionPrice, executionQuantity, side }, bytes)

@[simp] theorem encode_length (message : OrderExecute) : (encode message).length = 41 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderExecute) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderExecute) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderExecute

/-- Order Book Event: 5 bytes -/
structure OrderBookEvent where
  instrumentId : BitVec 32
  eventTypeOrderBookEventType : BitVec 8
  deriving DecidableEq, Repr

namespace OrderBookEvent

def encode (message : OrderBookEvent) : List UInt8 :=
  encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 1 message.eventTypeOrderBookEventType)

def decode (bytes : List UInt8) : Option (OrderBookEvent × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (eventTypeOrderBookEventType, bytes) ← decodeUIntLE 1 bytes
  pure ({ instrumentId, eventTypeOrderBookEventType }, bytes)

@[simp] theorem encode_length (message : OrderBookEvent) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderBookEvent) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderBookEvent) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderBookEvent

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | weekPlan (message : WeekPlan) -- 33
  | calendarException (message : CalendarException) -- 35
  | tickTableEntry (message : TickTableEntry) -- 32
  | collarTableEntry (message : CollarTableEntry) -- 108
  | tradingPhaseScheduleEntry (message : TradingPhaseScheduleEntry) -- 27
  | marketStructure (message : MarketStructure) -- 275
  | collarGroup (message : CollarGroup) -- 299
  | externalUnderlying (message : ExternalUnderlying) -- 806
  | instrument (message : Instrument) -- 279
  | accruedInterestTableEntry (message : AccruedInterestTableEntry) -- 36
  | indexationTableEntry (message : IndexationTableEntry) -- 37
  | indexParams (message : IndexParams) -- 503
  | indexPortfolioEntry (message : IndexPortfolioEntry) -- 502
  | auctionSummary (message : AuctionSummary) -- 270
  | auctionUpdate (message : AuctionUpdate) -- 268
  | priceLevelSnapshot (message : PriceLevelSnapshot) -- 257
  | topPriceLevelUpdate (message : TopPriceLevelUpdate) -- 256
  | trade (message : Trade) -- 38
  | positionReport (message : PositionReport) -- 801
  | instrumentStatusChange (message : InstrumentStatusChange) -- 26
  | orderCollars (message : OrderCollars) -- 272
  | tradeCollars (message : TradeCollars) -- 273
  | instrumentSummary (message : InstrumentSummary) -- 671
  | productSummary (message : ProductSummary) -- 672
  | priceUpdate (message : PriceUpdate) -- 271
  | news (message : News) -- 517
  | realTimeIndex (message : RealTimeIndex) -- 500
  | indexSummary (message : IndexSummary) -- 501
  | tradingSessionStatus (message : TradingSessionStatus) -- 23
  | testEvent (message : TestEvent) -- 8192
  | orderAdd (message : OrderAdd) -- 9
  | orderModify (message : OrderModify) -- 10
  | orderCancel (message : OrderCancel) -- 11
  | orderExecute (message : OrderExecute) -- 12
  | orderBookEvent (message : OrderBookEvent) -- 410
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 16
  | .weekPlan _ => 33
  | .calendarException _ => 35
  | .tickTableEntry _ => 32
  | .collarTableEntry _ => 108
  | .tradingPhaseScheduleEntry _ => 27
  | .marketStructure _ => 275
  | .collarGroup _ => 299
  | .externalUnderlying _ => 806
  | .instrument _ => 279
  | .accruedInterestTableEntry _ => 36
  | .indexationTableEntry _ => 37
  | .indexParams _ => 503
  | .indexPortfolioEntry _ => 502
  | .auctionSummary _ => 270
  | .auctionUpdate _ => 268
  | .priceLevelSnapshot _ => 257
  | .topPriceLevelUpdate _ => 256
  | .trade _ => 38
  | .positionReport _ => 801
  | .instrumentStatusChange _ => 26
  | .orderCollars _ => 272
  | .tradeCollars _ => 273
  | .instrumentSummary _ => 671
  | .productSummary _ => 672
  | .priceUpdate _ => 271
  | .news _ => 517
  | .realTimeIndex _ => 500
  | .indexSummary _ => 501
  | .tradingSessionStatus _ => 23
  | .testEvent _ => 8192
  | .orderAdd _ => 9
  | .orderModify _ => 10
  | .orderCancel _ => 11
  | .orderExecute _ => 12
  | .orderBookEvent _ => 410

def encode : Payload → List UInt8
  | .weekPlan message => WeekPlan.encode message
  | .calendarException message => CalendarException.encode message
  | .tickTableEntry message => TickTableEntry.encode message
  | .collarTableEntry message => CollarTableEntry.encode message
  | .tradingPhaseScheduleEntry message => TradingPhaseScheduleEntry.encode message
  | .marketStructure message => MarketStructure.encode message
  | .collarGroup message => CollarGroup.encode message
  | .externalUnderlying message => ExternalUnderlying.encode message
  | .instrument message => Instrument.encode message
  | .accruedInterestTableEntry message => AccruedInterestTableEntry.encode message
  | .indexationTableEntry message => IndexationTableEntry.encode message
  | .indexParams message => IndexParams.encode message
  | .indexPortfolioEntry message => IndexPortfolioEntry.encode message
  | .auctionSummary message => AuctionSummary.encode message
  | .auctionUpdate message => AuctionUpdate.encode message
  | .priceLevelSnapshot message => PriceLevelSnapshot.encode message
  | .topPriceLevelUpdate message => TopPriceLevelUpdate.encode message
  | .trade message => Trade.encode message
  | .positionReport message => PositionReport.encode message
  | .instrumentStatusChange message => InstrumentStatusChange.encode message
  | .orderCollars message => OrderCollars.encode message
  | .tradeCollars message => TradeCollars.encode message
  | .instrumentSummary message => InstrumentSummary.encode message
  | .productSummary message => ProductSummary.encode message
  | .priceUpdate message => PriceUpdate.encode message
  | .news message => News.encode message
  | .realTimeIndex message => RealTimeIndex.encode message
  | .indexSummary message => IndexSummary.encode message
  | .tradingSessionStatus message => TradingSessionStatus.encode message
  | .testEvent message => TestEvent.encode message
  | .orderAdd message => OrderAdd.encode message
  | .orderModify message => OrderModify.encode message
  | .orderCancel message => OrderCancel.encode message
  | .orderExecute message => OrderExecute.encode message
  | .orderBookEvent message => OrderBookEvent.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 890 := by
  cases message with
  | weekPlan inner =>
    simp only [encode, WeekPlan.encode_length]
    omega
  | calendarException inner =>
    simp only [encode, CalendarException.encode_length]
    omega
  | tickTableEntry inner =>
    simp only [encode, TickTableEntry.encode_length]
    omega
  | collarTableEntry inner =>
    simp only [encode, CollarTableEntry.encode_length]
    omega
  | tradingPhaseScheduleEntry inner =>
    simp only [encode, TradingPhaseScheduleEntry.encode_length]
    omega
  | marketStructure inner =>
    simp only [encode, MarketStructure.encode_length]
    omega
  | collarGroup inner =>
    simp only [encode, CollarGroup.encode_length]
    omega
  | externalUnderlying inner =>
    simp only [encode, ExternalUnderlying.encode_length]
    omega
  | instrument inner =>
    simp only [encode, Instrument.encode_length]
    omega
  | accruedInterestTableEntry inner =>
    simp only [encode, AccruedInterestTableEntry.encode_length]
    omega
  | indexationTableEntry inner =>
    simp only [encode, IndexationTableEntry.encode_length]
    omega
  | indexParams inner =>
    simp only [encode, IndexParams.encode_length]
    omega
  | indexPortfolioEntry inner =>
    simp only [encode, IndexPortfolioEntry.encode_length]
    omega
  | auctionSummary inner =>
    simp only [encode, AuctionSummary.encode_length]
    omega
  | auctionUpdate inner =>
    simp only [encode, AuctionUpdate.encode_length]
    omega
  | priceLevelSnapshot inner =>
    simp only [encode, PriceLevelSnapshot.encode_length]
    omega
  | topPriceLevelUpdate inner =>
    simp only [encode, TopPriceLevelUpdate.encode_length]
    omega
  | trade inner =>
    simp only [encode, Trade.encode_length]
    omega
  | positionReport inner =>
    simp only [encode, PositionReport.encode_length]
    omega
  | instrumentStatusChange inner =>
    simp only [encode, InstrumentStatusChange.encode_length]
    omega
  | orderCollars inner =>
    simp only [encode, OrderCollars.encode_length]
    omega
  | tradeCollars inner =>
    simp only [encode, TradeCollars.encode_length]
    omega
  | instrumentSummary inner =>
    simp only [encode, InstrumentSummary.encode_length]
    omega
  | productSummary inner =>
    simp only [encode, ProductSummary.encode_length]
    omega
  | priceUpdate inner =>
    simp only [encode, PriceUpdate.encode_length]
    omega
  | news inner =>
    simp only [encode, News.encode_length]
    omega
  | realTimeIndex inner =>
    simp only [encode, RealTimeIndex.encode_length]
    omega
  | indexSummary inner =>
    simp only [encode, IndexSummary.encode_length]
    omega
  | tradingSessionStatus inner =>
    simp only [encode, TradingSessionStatus.encode_length]
    omega
  | testEvent inner =>
    simp only [encode, TestEvent.encode_length]
    omega
  | orderAdd inner =>
    simp only [encode, OrderAdd.encode_length]
    omega
  | orderModify inner =>
    simp only [encode, OrderModify.encode_length]
    omega
  | orderCancel inner =>
    simp only [encode, OrderCancel.encode_length]
    omega
  | orderExecute inner =>
    simp only [encode, OrderExecute.encode_length]
    omega
  | orderBookEvent inner =>
    simp only [encode, OrderBookEvent.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 33 then (WeekPlan.decode bytes).map fun (message, rest) => (.weekPlan message, rest)
  else if tag = 35 then (CalendarException.decode bytes).map fun (message, rest) => (.calendarException message, rest)
  else if tag = 32 then (TickTableEntry.decode bytes).map fun (message, rest) => (.tickTableEntry message, rest)
  else if tag = 108 then (CollarTableEntry.decode bytes).map fun (message, rest) => (.collarTableEntry message, rest)
  else if tag = 27 then (TradingPhaseScheduleEntry.decode bytes).map fun (message, rest) => (.tradingPhaseScheduleEntry message, rest)
  else if tag = 275 then (MarketStructure.decode bytes).map fun (message, rest) => (.marketStructure message, rest)
  else if tag = 299 then (CollarGroup.decode bytes).map fun (message, rest) => (.collarGroup message, rest)
  else if tag = 806 then (ExternalUnderlying.decode bytes).map fun (message, rest) => (.externalUnderlying message, rest)
  else if tag = 279 then (Instrument.decode bytes).map fun (message, rest) => (.instrument message, rest)
  else if tag = 36 then (AccruedInterestTableEntry.decode bytes).map fun (message, rest) => (.accruedInterestTableEntry message, rest)
  else if tag = 37 then (IndexationTableEntry.decode bytes).map fun (message, rest) => (.indexationTableEntry message, rest)
  else if tag = 503 then (IndexParams.decode bytes).map fun (message, rest) => (.indexParams message, rest)
  else if tag = 502 then (IndexPortfolioEntry.decode bytes).map fun (message, rest) => (.indexPortfolioEntry message, rest)
  else if tag = 270 then (AuctionSummary.decode bytes).map fun (message, rest) => (.auctionSummary message, rest)
  else if tag = 268 then (AuctionUpdate.decode bytes).map fun (message, rest) => (.auctionUpdate message, rest)
  else if tag = 257 then (PriceLevelSnapshot.decode bytes).map fun (message, rest) => (.priceLevelSnapshot message, rest)
  else if tag = 256 then (TopPriceLevelUpdate.decode bytes).map fun (message, rest) => (.topPriceLevelUpdate message, rest)
  else if tag = 38 then (Trade.decode bytes).map fun (message, rest) => (.trade message, rest)
  else if tag = 801 then (PositionReport.decode bytes).map fun (message, rest) => (.positionReport message, rest)
  else if tag = 26 then (InstrumentStatusChange.decode bytes).map fun (message, rest) => (.instrumentStatusChange message, rest)
  else if tag = 272 then (OrderCollars.decode bytes).map fun (message, rest) => (.orderCollars message, rest)
  else if tag = 273 then (TradeCollars.decode bytes).map fun (message, rest) => (.tradeCollars message, rest)
  else if tag = 671 then (InstrumentSummary.decode bytes).map fun (message, rest) => (.instrumentSummary message, rest)
  else if tag = 672 then (ProductSummary.decode bytes).map fun (message, rest) => (.productSummary message, rest)
  else if tag = 271 then (PriceUpdate.decode bytes).map fun (message, rest) => (.priceUpdate message, rest)
  else if tag = 517 then (News.decode bytes).map fun (message, rest) => (.news message, rest)
  else if tag = 500 then (RealTimeIndex.decode bytes).map fun (message, rest) => (.realTimeIndex message, rest)
  else if tag = 501 then (IndexSummary.decode bytes).map fun (message, rest) => (.indexSummary message, rest)
  else if tag = 23 then (TradingSessionStatus.decode bytes).map fun (message, rest) => (.tradingSessionStatus message, rest)
  else if tag = 8192 then (TestEvent.decode bytes).map fun (message, rest) => (.testEvent message, rest)
  else if tag = 9 then (OrderAdd.decode bytes).map fun (message, rest) => (.orderAdd message, rest)
  else if tag = 10 then (OrderModify.decode bytes).map fun (message, rest) => (.orderModify message, rest)
  else if tag = 11 then (OrderCancel.decode bytes).map fun (message, rest) => (.orderCancel message, rest)
  else if tag = 12 then (OrderExecute.decode bytes).map fun (message, rest) => (.orderExecute message, rest)
  else if tag = 410 then (OrderBookEvent.decode bytes).map fun (message, rest) => (.orderBookEvent message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message -/
structure Message where
  messageLength : BitVec 16
  messageVersion : BitVec 16
  sequenceNumber : BitVec 32
  timestamp : BitVec 64
  sourceTimestamp : BitVec 64
  isEncrypted : BitVec 8
  encryptionOffset : BitVec 64
  encryptionKeyId : BitVec 32
  sessionId : BitVec 16
  streamId : BitVec 8
  payload : Payload
  deriving DecidableEq, Repr

namespace Message

def encode (message : Message) : List UInt8 :=
  encodeUIntLE 2 message.messageLength
    ++ (encodeUIntLE 2 (Payload.tag message.payload)
    ++ (encodeUIntLE 2 message.messageVersion
    ++ (encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.sourceTimestamp
    ++ (encodeUIntLE 1 message.isEncrypted
    ++ (encodeUIntLE 8 message.encryptionOffset
    ++ (encodeUIntLE 4 message.encryptionKeyId
    ++ (encodeUIntLE 2 message.sessionId
    ++ (encodeUIntLE 1 message.streamId
    ++ (Payload.encode message.payload)))))))))))

def decode (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (messageLength, bytes) ← decodeUIntLE 2 bytes
  let (messageType, bytes) ← decodeUIntLE 2 bytes
  let (messageVersion, bytes) ← decodeUIntLE 2 bytes
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (sourceTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (isEncrypted, bytes) ← decodeUIntLE 1 bytes
  let (encryptionOffset, bytes) ← decodeUIntLE 8 bytes
  let (encryptionKeyId, bytes) ← decodeUIntLE 4 bytes
  let (sessionId, bytes) ← decodeUIntLE 2 bytes
  let (streamId, bytes) ← decodeUIntLE 1 bytes
  let (payload, bytes) ← Payload.decode messageType bytes
  pure ({ messageLength, messageVersion, sequenceNumber, timestamp, sourceTimestamp, isEncrypted, encryptionOffset, encryptionKeyId, sessionId, streamId, payload }, bytes)

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Message) : (encode message).length ≤ 932 := by
  unfold encode
  cases message.payload with
  | weekPlan inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, WeekPlan.encode_length]
    omega
  | calendarException inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, CalendarException.encode_length]
    omega
  | tickTableEntry inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, TickTableEntry.encode_length]
    omega
  | collarTableEntry inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, CollarTableEntry.encode_length]
    omega
  | tradingPhaseScheduleEntry inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, TradingPhaseScheduleEntry.encode_length]
    omega
  | marketStructure inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, MarketStructure.encode_length]
    omega
  | collarGroup inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, CollarGroup.encode_length]
    omega
  | externalUnderlying inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, ExternalUnderlying.encode_length]
    omega
  | instrument inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Instrument.encode_length]
    omega
  | accruedInterestTableEntry inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, AccruedInterestTableEntry.encode_length]
    omega
  | indexationTableEntry inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, IndexationTableEntry.encode_length]
    omega
  | indexParams inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, IndexParams.encode_length]
    omega
  | indexPortfolioEntry inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, IndexPortfolioEntry.encode_length]
    omega
  | auctionSummary inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, AuctionSummary.encode_length]
    omega
  | auctionUpdate inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, AuctionUpdate.encode_length]
    omega
  | priceLevelSnapshot inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, PriceLevelSnapshot.encode_length]
    omega
  | topPriceLevelUpdate inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, TopPriceLevelUpdate.encode_length]
    omega
  | trade inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Trade.encode_length]
    omega
  | positionReport inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, PositionReport.encode_length]
    omega
  | instrumentStatusChange inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, InstrumentStatusChange.encode_length]
    omega
  | orderCollars inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OrderCollars.encode_length]
    omega
  | tradeCollars inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, TradeCollars.encode_length]
    omega
  | instrumentSummary inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, InstrumentSummary.encode_length]
    omega
  | productSummary inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, ProductSummary.encode_length]
    omega
  | priceUpdate inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, PriceUpdate.encode_length]
    omega
  | news inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, News.encode_length]
    omega
  | realTimeIndex inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, RealTimeIndex.encode_length]
    omega
  | indexSummary inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, IndexSummary.encode_length]
    omega
  | tradingSessionStatus inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, TradingSessionStatus.encode_length]
    omega
  | testEvent inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, TestEvent.encode_length]
    omega
  | orderAdd inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OrderAdd.encode_length]
    omega
  | orderModify inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OrderModify.encode_length]
    omega
  | orderCancel inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OrderCancel.encode_length]
    omega
  | orderExecute inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OrderExecute.encode_length]
    omega
  | orderBookEvent inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OrderBookEvent.encode_length]
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
  rw [Payload.decode_encode, some_bind]
  rfl

end Message

/-- Packet -/
structure Packet where
  message : List Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeMany Message.encode message.message

def decode (bytes : List UInt8) : Option Packet := do
  let message ← decodeAll Message.decode bytes.length bytes
  pure { message }

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany Message.encode Message.decode Message.decode_encode Message.encode_length_pos message.message _ (encodeMany_length_ge Message.encode Message.encode_length_pos message.message), some_bind]
  rfl

end Packet

end Omi.GpwWseStreamfulldepthWatsV17620
