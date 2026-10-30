import Wire

/-!
# Giełda Papierów Wartościowych w Warszawie BondSpot Prices and Trades v6.8

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.GpwBondspotPricesandtradesXdpV68

/-- Last Trade Indicator: one byte code -/
def LastTradeIndicator.codes : List UInt8 :=
  [0x30, 0x31]

inductive LastTradeIndicator where
  | notLastOfASeriesOfTradeAtTheSamePrice -- Not Last Of A Series Of Trade At The Same Price
  | lastOfASeriesOfTradeAtTheSamePriceAnd -- Last Of A Series Of Trade At The Same Price And
  | unlisted (byte : { byte : UInt8 // byte ∉ LastTradeIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LastTradeIndicator

def toByte : LastTradeIndicator → UInt8
  | .notLastOfASeriesOfTradeAtTheSamePrice => 0x30
  | .lastOfASeriesOfTradeAtTheSamePriceAnd => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LastTradeIndicator :=
  if byte = 0x30 then .notLastOfASeriesOfTradeAtTheSamePrice
  else .lastOfASeriesOfTradeAtTheSamePriceAnd

def ofByte (byte : UInt8) : LastTradeIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LastTradeIndicator) : ofByte value.toByte = value := by
  cases value with
  | notLastOfASeriesOfTradeAtTheSamePrice => decide
  | lastOfASeriesOfTradeAtTheSamePriceAnd => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LastTradeIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LastTradeIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LastTradeIndicator) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : LastTradeIndicator) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : LastTradeIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LastTradeIndicator

/-- Type Of Trade: one byte code -/
def TypeOfTrade.codes : List UInt8 :=
  [0x30, 0x31, 0x34, 0x35, 0x36]

inductive TypeOfTrade where
  | tradeDoesNotStemFromACrossOrder -- Trade Does Not Stem From A Cross Order
  | tradeStemsFromACrossOrder -- Trade Stems From A Cross Order
  | valuationTrade -- Valuation Trade
  | internalizedTrade -- Internalized Trade
  | internalizedCrossTrade -- Internalized Cross Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ TypeOfTrade.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TypeOfTrade

def toByte : TypeOfTrade → UInt8
  | .tradeDoesNotStemFromACrossOrder => 0x30
  | .tradeStemsFromACrossOrder => 0x31
  | .valuationTrade => 0x34
  | .internalizedTrade => 0x35
  | .internalizedCrossTrade => 0x36
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TypeOfTrade :=
  if byte = 0x30 then .tradeDoesNotStemFromACrossOrder
  else if byte = 0x31 then .tradeStemsFromACrossOrder
  else if byte = 0x34 then .valuationTrade
  else if byte = 0x35 then .internalizedTrade
  else .internalizedCrossTrade

def ofByte (byte : UInt8) : TypeOfTrade :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TypeOfTrade) : ofByte value.toByte = value := by
  cases value with
  | tradeDoesNotStemFromACrossOrder => decide
  | tradeStemsFromACrossOrder => decide
  | valuationTrade => decide
  | internalizedTrade => decide
  | internalizedCrossTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TypeOfTrade) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TypeOfTrade × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TypeOfTrade) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TypeOfTrade) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TypeOfTrade) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TypeOfTrade

/-- Trade Origin: one byte code -/
def TradeOrigin.codes : List UInt8 :=
  [0x42, 0x4F, 0x49, 0x54, 0x53, 0x52]

inductive TradeOrigin where
  | ordersFromTheBook -- Orders From The Book
  | blockTrade -- Block Trade
  | ipoTrade -- Ipo Trade
  | tenderOfferTrade -- Tender Offer Trade
  | bisoTrade -- Biso Trade
  | tradeReportingForFutureUse -- Trade Reporting For Future Use
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeOrigin.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeOrigin

def toByte : TradeOrigin → UInt8
  | .ordersFromTheBook => 0x42
  | .blockTrade => 0x4F
  | .ipoTrade => 0x49
  | .tenderOfferTrade => 0x54
  | .bisoTrade => 0x53
  | .tradeReportingForFutureUse => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeOrigin :=
  if byte = 0x42 then .ordersFromTheBook
  else if byte = 0x4F then .blockTrade
  else if byte = 0x49 then .ipoTrade
  else if byte = 0x54 then .tenderOfferTrade
  else if byte = 0x53 then .bisoTrade
  else .tradeReportingForFutureUse

def ofByte (byte : UInt8) : TradeOrigin :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeOrigin) : ofByte value.toByte = value := by
  cases value with
  | ordersFromTheBook => decide
  | blockTrade => decide
  | ipoTrade => decide
  | tenderOfferTrade => decide
  | bisoTrade => decide
  | tradeReportingForFutureUse => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeOrigin) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeOrigin × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeOrigin) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TradeOrigin) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TradeOrigin) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeOrigin

/-- Tick Direction: one byte code -/
def TickDirection.codes : List UInt8 :=
  [0x2B, 0x2D, 0x30]

inductive TickDirection where
  | positiveRising -- Positive Rising
  | negativeFalling -- Negative Falling
  | noVariationUnchangedOrDataFieldNotSignificantUsedForTradeCancellation -- No Variation Unchanged Or Data Field Not Significant Used For Trade Cancellation
  | unlisted (byte : { byte : UInt8 // byte ∉ TickDirection.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TickDirection

def toByte : TickDirection → UInt8
  | .positiveRising => 0x2B
  | .negativeFalling => 0x2D
  | .noVariationUnchangedOrDataFieldNotSignificantUsedForTradeCancellation => 0x30
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TickDirection :=
  if byte = 0x2B then .positiveRising
  else if byte = 0x2D then .negativeFalling
  else .noVariationUnchangedOrDataFieldNotSignificantUsedForTradeCancellation

def ofByte (byte : UInt8) : TickDirection :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TickDirection) : ofByte value.toByte = value := by
  cases value with
  | positiveRising => decide
  | negativeFalling => decide
  | noVariationUnchangedOrDataFieldNotSignificantUsedForTradeCancellation => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TickDirection) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TickDirection × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TickDirection) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TickDirection) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TickDirection) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TickDirection

/-- Opening Trade Indicator: one byte code -/
def OpeningTradeIndicator.codes : List UInt8 :=
  [0x4F, 0x53, 0x20]

inductive OpeningTradeIndicator where
  | opening -- Opening
  | coreContinuous -- Core Continuous
  | bondSpotAlwaysFillsTheFieldWithASpace -- Bond Spot Always Fills The Field With A Space
  | unlisted (byte : { byte : UInt8 // byte ∉ OpeningTradeIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OpeningTradeIndicator

def toByte : OpeningTradeIndicator → UInt8
  | .opening => 0x4F
  | .coreContinuous => 0x53
  | .bondSpotAlwaysFillsTheFieldWithASpace => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OpeningTradeIndicator :=
  if byte = 0x4F then .opening
  else if byte = 0x53 then .coreContinuous
  else .bondSpotAlwaysFillsTheFieldWithASpace

def ofByte (byte : UInt8) : OpeningTradeIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OpeningTradeIndicator) : ofByte value.toByte = value := by
  cases value with
  | opening => decide
  | coreContinuous => decide
  | bondSpotAlwaysFillsTheFieldWithASpace => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OpeningTradeIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OpeningTradeIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OpeningTradeIndicator) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OpeningTradeIndicator) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OpeningTradeIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OpeningTradeIndicator

/-- Trade Full Information Message: 272 bytes -/
structure TradeFullInformationMessage where
  symbolIndex : BitVec 32
  sourceTime : BitVec 32
  tradeIdNumber : BitVec 32
  venueOfExecution : Alpha 4
  sourceSeqNum : BitVec 32
  priceNotation : Alpha 4
  transactionToBeCleared : Alpha 4
  cumulativeQuantity : BitVec 32
  highestPrice : BitVec 32
  lowestPrice : BitVec 32
  variationLastPrice : BitVec 32
  systemId : BitVec 32
  sourceTimeMicroSecs : BitVec 16
  priceCurrency : Alpha 3
  lastTradeIndicator : LastTradeIndicator
  typeOfTrade : TypeOfTrade
  tradeOrigin : TradeOrigin
  tickDirection : TickDirection
  openingTradeIndicator : OpeningTradeIndicator
  variationScaleCode : BitVec 8
  priceScaleCode : BitVec 8
  tradingDateTime : Alpha 27
  publicationDateTime : Alpha 27
  instrumentIdCodeType : Alpha 4
  instrumentIdCode : Alpha 12
  priceAsciiCh20 : Alpha 20
  quantity : Alpha 20
  notionalAmount : Alpha 20
  notionalCurrency : Alpha 3
  reserved1 : Alpha 1
  transactionIdCode : Alpha 52
  mmtMarketMechanism : Alpha 1
  mmtTradingMode : Alpha 1
  mmtAlgorithmicIndicator : Alpha 4
  mmtModificationIndicator : Alpha 4
  mmtNegotiationIndicator : Alpha 4
  mmtSpecialDividendIndicator : Alpha 4
  mmtContributionToPrice : Alpha 4
  mmtBenchmarkIndicator : Alpha 4
  deriving DecidableEq, Repr

namespace TradeFullInformationMessage

def encode (message : TradeFullInformationMessage) : List UInt8 :=
  encodeUInt 4 message.symbolIndex
    ++ (encodeUInt 4 message.sourceTime
    ++ (encodeUInt 4 message.tradeIdNumber
    ++ (Alpha.encode message.venueOfExecution
    ++ (encodeUInt 4 message.sourceSeqNum
    ++ (Alpha.encode message.priceNotation
    ++ (Alpha.encode message.transactionToBeCleared
    ++ (encodeUInt 4 message.cumulativeQuantity
    ++ (encodeUInt 4 message.highestPrice
    ++ (encodeUInt 4 message.lowestPrice
    ++ (encodeUInt 4 message.variationLastPrice
    ++ (encodeUInt 4 message.systemId
    ++ (encodeUInt 2 message.sourceTimeMicroSecs
    ++ (Alpha.encode message.priceCurrency
    ++ (LastTradeIndicator.encode message.lastTradeIndicator
    ++ (TypeOfTrade.encode message.typeOfTrade
    ++ (TradeOrigin.encode message.tradeOrigin
    ++ (TickDirection.encode message.tickDirection
    ++ (OpeningTradeIndicator.encode message.openingTradeIndicator
    ++ (encodeUInt 1 message.variationScaleCode
    ++ (encodeUInt 1 message.priceScaleCode
    ++ (Alpha.encode message.tradingDateTime
    ++ (Alpha.encode message.publicationDateTime
    ++ (Alpha.encode message.instrumentIdCodeType
    ++ (Alpha.encode message.instrumentIdCode
    ++ (Alpha.encode message.priceAsciiCh20
    ++ (Alpha.encode message.quantity
    ++ (Alpha.encode message.notionalAmount
    ++ (Alpha.encode message.notionalCurrency
    ++ (Alpha.encode message.reserved1
    ++ (Alpha.encode message.transactionIdCode
    ++ (Alpha.encode message.mmtMarketMechanism
    ++ (Alpha.encode message.mmtTradingMode
    ++ (Alpha.encode message.mmtAlgorithmicIndicator
    ++ (Alpha.encode message.mmtModificationIndicator
    ++ (Alpha.encode message.mmtNegotiationIndicator
    ++ (Alpha.encode message.mmtSpecialDividendIndicator
    ++ (Alpha.encode message.mmtContributionToPrice
    ++ (Alpha.encode message.mmtBenchmarkIndicator))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TradeFullInformationMessage × List UInt8) := do
  let (symbolIndex, bytes) ← decodeUInt 4 bytes
  let (sourceTime, bytes) ← decodeUInt 4 bytes
  let (tradeIdNumber, bytes) ← decodeUInt 4 bytes
  let (venueOfExecution, bytes) ← Alpha.decode 4 bytes
  let (sourceSeqNum, bytes) ← decodeUInt 4 bytes
  let (priceNotation, bytes) ← Alpha.decode 4 bytes
  let (transactionToBeCleared, bytes) ← Alpha.decode 4 bytes
  let (cumulativeQuantity, bytes) ← decodeUInt 4 bytes
  let (highestPrice, bytes) ← decodeUInt 4 bytes
  let (lowestPrice, bytes) ← decodeUInt 4 bytes
  let (variationLastPrice, bytes) ← decodeUInt 4 bytes
  let (systemId, bytes) ← decodeUInt 4 bytes
  let (sourceTimeMicroSecs, bytes) ← decodeUInt 2 bytes
  let (priceCurrency, bytes) ← Alpha.decode 3 bytes
  let (lastTradeIndicator, bytes) ← LastTradeIndicator.decode bytes
  let (typeOfTrade, bytes) ← TypeOfTrade.decode bytes
  let (tradeOrigin, bytes) ← TradeOrigin.decode bytes
  let (tickDirection, bytes) ← TickDirection.decode bytes
  let (openingTradeIndicator, bytes) ← OpeningTradeIndicator.decode bytes
  let (variationScaleCode, bytes) ← decodeUInt 1 bytes
  let (priceScaleCode, bytes) ← decodeUInt 1 bytes
  let (tradingDateTime, bytes) ← Alpha.decode 27 bytes
  let (publicationDateTime, bytes) ← Alpha.decode 27 bytes
  let (instrumentIdCodeType, bytes) ← Alpha.decode 4 bytes
  let (instrumentIdCode, bytes) ← Alpha.decode 12 bytes
  let (priceAsciiCh20, bytes) ← Alpha.decode 20 bytes
  let (quantity, bytes) ← Alpha.decode 20 bytes
  let (notionalAmount, bytes) ← Alpha.decode 20 bytes
  let (notionalCurrency, bytes) ← Alpha.decode 3 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (transactionIdCode, bytes) ← Alpha.decode 52 bytes
  let (mmtMarketMechanism, bytes) ← Alpha.decode 1 bytes
  let (mmtTradingMode, bytes) ← Alpha.decode 1 bytes
  let (mmtAlgorithmicIndicator, bytes) ← Alpha.decode 4 bytes
  let (mmtModificationIndicator, bytes) ← Alpha.decode 4 bytes
  let (mmtNegotiationIndicator, bytes) ← Alpha.decode 4 bytes
  let (mmtSpecialDividendIndicator, bytes) ← Alpha.decode 4 bytes
  let (mmtContributionToPrice, bytes) ← Alpha.decode 4 bytes
  let (mmtBenchmarkIndicator, bytes) ← Alpha.decode 4 bytes
  pure ({ symbolIndex, sourceTime, tradeIdNumber, venueOfExecution, sourceSeqNum, priceNotation, transactionToBeCleared, cumulativeQuantity, highestPrice, lowestPrice, variationLastPrice, systemId, sourceTimeMicroSecs, priceCurrency, lastTradeIndicator, typeOfTrade, tradeOrigin, tickDirection, openingTradeIndicator, variationScaleCode, priceScaleCode, tradingDateTime, publicationDateTime, instrumentIdCodeType, instrumentIdCode, priceAsciiCh20, quantity, notionalAmount, notionalCurrency, reserved1, transactionIdCode, mmtMarketMechanism, mmtTradingMode, mmtAlgorithmicIndicator, mmtModificationIndicator, mmtNegotiationIndicator, mmtSpecialDividendIndicator, mmtContributionToPrice, mmtBenchmarkIndicator }, bytes)

@[simp] theorem encode_length (message : TradeFullInformationMessage) : (encode message).length = 272 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, LastTradeIndicator.encode_length, TypeOfTrade.encode_length, TradeOrigin.encode_length, TickDirection.encode_length, OpeningTradeIndicator.encode_length]

theorem encode_length_pos (message : TradeFullInformationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : TradeFullInformationMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LastTradeIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TypeOfTrade.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeOrigin.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TickDirection.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpeningTradeIndicator.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeFullInformationMessage

/-- Price Update Message: 40 bytes -/
structure PriceUpdateMessage where
  symbolIndex : BitVec 32
  sourceTime : BitVec 32
  sourceSeqNum : BitVec 32
  priceBinaryInt4 : BitVec 32
  highestPrice : BitVec 32
  lowestPrice : BitVec 32
  variationLastPrice : BitVec 32
  systemId : BitVec 32
  sourceTimeMicroSecs : BitVec 16
  typeOfPrice : BitVec 16
  reserved2 : Alpha 2
  priceScaleCode : BitVec 8
  variationScaleCode : BitVec 8
  deriving DecidableEq, Repr

namespace PriceUpdateMessage

def encode (message : PriceUpdateMessage) : List UInt8 :=
  encodeUInt 4 message.symbolIndex
    ++ (encodeUInt 4 message.sourceTime
    ++ (encodeUInt 4 message.sourceSeqNum
    ++ (encodeUInt 4 message.priceBinaryInt4
    ++ (encodeUInt 4 message.highestPrice
    ++ (encodeUInt 4 message.lowestPrice
    ++ (encodeUInt 4 message.variationLastPrice
    ++ (encodeUInt 4 message.systemId
    ++ (encodeUInt 2 message.sourceTimeMicroSecs
    ++ (encodeUInt 2 message.typeOfPrice
    ++ (Alpha.encode message.reserved2
    ++ (encodeUInt 1 message.priceScaleCode
    ++ (encodeUInt 1 message.variationScaleCode))))))))))))

def decode (bytes : List UInt8) : Option (PriceUpdateMessage × List UInt8) := do
  let (symbolIndex, bytes) ← decodeUInt 4 bytes
  let (sourceTime, bytes) ← decodeUInt 4 bytes
  let (sourceSeqNum, bytes) ← decodeUInt 4 bytes
  let (priceBinaryInt4, bytes) ← decodeUInt 4 bytes
  let (highestPrice, bytes) ← decodeUInt 4 bytes
  let (lowestPrice, bytes) ← decodeUInt 4 bytes
  let (variationLastPrice, bytes) ← decodeUInt 4 bytes
  let (systemId, bytes) ← decodeUInt 4 bytes
  let (sourceTimeMicroSecs, bytes) ← decodeUInt 2 bytes
  let (typeOfPrice, bytes) ← decodeUInt 2 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (priceScaleCode, bytes) ← decodeUInt 1 bytes
  let (variationScaleCode, bytes) ← decodeUInt 1 bytes
  pure ({ symbolIndex, sourceTime, sourceSeqNum, priceBinaryInt4, highestPrice, lowestPrice, variationLastPrice, systemId, sourceTimeMicroSecs, typeOfPrice, reserved2, priceScaleCode, variationScaleCode }, bytes)

@[simp] theorem encode_length (message : PriceUpdateMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : PriceUpdateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PriceUpdateMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end PriceUpdateMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | tradeFullInformationMessage (message : TradeFullInformationMessage) -- 240
  | priceUpdateMessage (message : PriceUpdateMessage) -- 241
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 16
  | .tradeFullInformationMessage _ => 240
  | .priceUpdateMessage _ => 241

def encode : Payload → List UInt8
  | .tradeFullInformationMessage message => TradeFullInformationMessage.encode message
  | .priceUpdateMessage message => PriceUpdateMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 272 := by
  cases message with
  | tradeFullInformationMessage inner =>
    simp only [encode, TradeFullInformationMessage.encode_length]
    omega
  | priceUpdateMessage inner =>
    simp only [encode, PriceUpdateMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 240 then (TradeFullInformationMessage.decode bytes).map fun (message, rest) => (.tradeFullInformationMessage message, rest)
  else if tag = 241 then (PriceUpdateMessage.decode bytes).map fun (message, rest) => (.priceUpdateMessage message, rest)
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
  encodeUInt 2 (Payload.tag message.payload)
    ++ (Payload.encode message.payload)

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (messageType, bytes) ← decodeUInt 2 bytes
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
  | tradeFullInformationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeFullInformationMessage.encode_length]
    omega
  | priceUpdateMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, PriceUpdateMessage.encode_length]
    omega

/-- Size rule: Message Size counts the bytes after it, so it is written from the body and checked on decode -/
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

/-- Message Buffer -/
structure MessageBuffer (numberMsgEntries : BitVec 8) where
  message : Exact numberMsgEntries.toNat Message
  deriving DecidableEq, Repr

namespace MessageBuffer

def encode {numberMsgEntries : BitVec 8} (message : MessageBuffer numberMsgEntries) : List UInt8 :=
  encodeMany Message.encode message.message.val

def decode (numberMsgEntries : BitVec 8) (bytes : List UInt8) : Option (MessageBuffer numberMsgEntries × List UInt8) := do
  let (message_, bytes) ← decodeMany Message.decode numberMsgEntries.toNat bytes
  if fits_message : message_.length = numberMsgEntries.toNat then
    pure ({ message := ⟨message_, fits_message⟩ }, bytes)
  else none

@[simp] theorem decode_encode (numberMsgEntries : BitVec 8) (message : MessageBuffer numberMsgEntries) (rest : List UInt8) :
    decode numberMsgEntries (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeMany_exact numberMsgEntries.toNat Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_eq]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (numberMsgEntries : BitVec 8) (message : MessageBuffer numberMsgEntries) : decode numberMsgEntries (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode numberMsgEntries message []

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

/-- The Message Buffer, as bytes when Delivery Flag says it was Zlib transformed and as it lies when it says it was not -/
inductive MessageBufferBody (numberMsgEntries : BitVec 8) where
  | zlib (tag : { v : BitVec 8 // 15 < v }) (message : MessageBufferZlib) -- 15 < tag
  | plain (tag : { v : BitVec 8 // ¬ (15 < v) }) (message : MessageBuffer numberMsgEntries) -- every other value
  deriving DecidableEq, Repr

namespace MessageBufferBody

/-- The Delivery Flag each body is read by -/
def tag {numberMsgEntries : BitVec 8} : MessageBufferBody numberMsgEntries → BitVec 8
  | .zlib tag _ => tag.val
  | .plain tag _ => tag.val

def encode {numberMsgEntries : BitVec 8} : MessageBufferBody numberMsgEntries → List UInt8
  | .zlib _ message => MessageBufferZlib.encode message
  | .plain _ message => MessageBuffer.encode message

/-- Decoded from the whole of what holds it: a body that reads to its end takes it all, any other must leave nothing -/
def decode (numberMsgEntries : BitVec 8) (tag : BitVec 8) (bytes : List UInt8) : Option (MessageBufferBody numberMsgEntries) :=
  if h : 15 < tag then (MessageBufferZlib.decode bytes).map fun message => .zlib ⟨tag, h⟩ message
  else (MessageBuffer.decode numberMsgEntries bytes).bind fun (message, rest) => if rest.isEmpty then some (.plain ⟨tag, h⟩ message) else none

theorem decode_encode (numberMsgEntries : BitVec 8) (message : MessageBufferBody numberMsgEntries) :
    decode numberMsgEntries (tag message) (encode message) = some message := by
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
  packetLength : BitVec 16
  packetType : BitVec 16
  packetSequenceNumber : BitVec 32
  sendTime : BitVec 32
  serviceId : BitVec 16
  numberMsgEntries : BitVec 8
  messageBuffer : MessageBufferBody numberMsgEntries
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUInt 2 message.packetLength
    ++ (encodeUInt 2 message.packetType
    ++ (encodeUInt 4 message.packetSequenceNumber
    ++ (encodeUInt 4 message.sendTime
    ++ (encodeUInt 2 message.serviceId
    ++ (encodeUInt 1 (MessageBufferBody.tag message.messageBuffer)
    ++ (encodeUInt 1 message.numberMsgEntries
    ++ (MessageBufferBody.encode message.messageBuffer)))))))

def decode (bytes : List UInt8) : Option Packet := do
  let (packetLength, bytes) ← decodeUInt 2 bytes
  let (packetType, bytes) ← decodeUInt 2 bytes
  let (packetSequenceNumber, bytes) ← decodeUInt 4 bytes
  let (sendTime, bytes) ← decodeUInt 4 bytes
  let (serviceId, bytes) ← decodeUInt 2 bytes
  let (deliveryFlag, bytes) ← decodeUInt 1 bytes
  let (numberMsgEntries, bytes) ← decodeUInt 1 bytes
  let messageBuffer ← MessageBufferBody.decode numberMsgEntries deliveryFlag bytes
  pure { packetLength, packetType, packetSequenceNumber, sendTime, serviceId, numberMsgEntries, messageBuffer }

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [MessageBufferBody.decode_encode, some_bind]
  rfl

end Packet

end Omi.GpwBondspotPricesandtradesXdpV68
