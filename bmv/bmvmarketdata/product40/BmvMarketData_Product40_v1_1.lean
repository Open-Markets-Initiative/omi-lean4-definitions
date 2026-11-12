import Wire

/-!
# Bolsa Mexicana de Valores Bmv Market Data Product 40 v1.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.

License: MIT No Attribution
-/

namespace Omi.BmvBmvmarketdataProduct40IntraV11

/-- Market: one byte code -/
def Market.codes : List UInt8 :=
  [0x4C, 0x47, 0x44, 0x46, 0x45, 0x4D, 0x58, 0x56, 0x4A, 0x42, 0x54, 0x49, 0x57, 0x20]

inductive Market where
  | local_ -- Local
  | global -- Global
  | localDebt -- Local Debt
  | globalDebt -- Global Debt
  | money -- Money
  | dollarOptionMarket -- Dollar Option Market
  | stockMarket -- Stock Market
  | forexAndRatesMarket -- Forex And Rates Market
  | fixedIncome -- Fixed Income
  | variableIncome -- Variable Income
  | metals -- Metals
  | mutualFunds -- Mutual Funds
  | warrants -- Warrants
  | allMarkets -- All Markets
  | unlisted (byte : { byte : UInt8 // byte ∉ Market.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Market

def toByte : Market → UInt8
  | .local_ => 0x4C
  | .global => 0x47
  | .localDebt => 0x44
  | .globalDebt => 0x46
  | .money => 0x45
  | .dollarOptionMarket => 0x4D
  | .stockMarket => 0x58
  | .forexAndRatesMarket => 0x56
  | .fixedIncome => 0x4A
  | .variableIncome => 0x42
  | .metals => 0x54
  | .mutualFunds => 0x49
  | .warrants => 0x57
  | .allMarkets => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Market :=
  if byte = 0x4C then .local_
  else if byte = 0x47 then .global
  else if byte = 0x44 then .localDebt
  else if byte = 0x46 then .globalDebt
  else if byte = 0x45 then .money
  else if byte = 0x4D then .dollarOptionMarket
  else if byte = 0x58 then .stockMarket
  else if byte = 0x56 then .forexAndRatesMarket
  else if byte = 0x4A then .fixedIncome
  else if byte = 0x42 then .variableIncome
  else if byte = 0x54 then .metals
  else if byte = 0x49 then .mutualFunds
  else if byte = 0x57 then .warrants
  else .allMarkets

def ofByte (byte : UInt8) : Market :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Market) : ofByte value.toByte = value := by
  cases value with
  | local_ => decide
  | global => decide
  | localDebt => decide
  | globalDebt => decide
  | money => decide
  | dollarOptionMarket => decide
  | stockMarket => decide
  | forexAndRatesMarket => decide
  | fixedIncome => decide
  | variableIncome => decide
  | metals => decide
  | mutualFunds => decide
  | warrants => decide
  | allMarkets => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Market) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Market × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Market) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Market) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Market) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Market

/-- Exchange: one byte code -/
def Exchange.codes : List UInt8 :=
  [0x4D, 0x49]

inductive Exchange where
  | bmv -- Bmv
  | biva -- Biva
  | unlisted (byte : { byte : UInt8 // byte ∉ Exchange.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Exchange

def toByte : Exchange → UInt8
  | .bmv => 0x4D
  | .biva => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Exchange :=
  if byte = 0x4D then .bmv
  else .biva

def ofByte (byte : UInt8) : Exchange :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Exchange) : ofByte value.toByte = value := by
  cases value with
  | bmv => decide
  | biva => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Exchange) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Exchange × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Exchange) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Exchange) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Exchange) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Exchange

/-- Operate Price Rate: one byte code -/
def OperatePriceRate.codes : List UInt8 :=
  [0x54, 0x50, 0x20]

inductive OperatePriceRate where
  | rate -- Rate
  | price -- Price
  | default -- Default
  | unlisted (byte : { byte : UInt8 // byte ∉ OperatePriceRate.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OperatePriceRate

def toByte : OperatePriceRate → UInt8
  | .rate => 0x54
  | .price => 0x50
  | .default => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OperatePriceRate :=
  if byte = 0x54 then .rate
  else if byte = 0x50 then .price
  else .default

def ofByte (byte : UInt8) : OperatePriceRate :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OperatePriceRate) : ofByte value.toByte = value := by
  cases value with
  | rate => decide
  | price => decide
  | default => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OperatePriceRate) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OperatePriceRate × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OperatePriceRate) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OperatePriceRate) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OperatePriceRate) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OperatePriceRate

/-- Warrant Type: one byte code -/
def WarrantType.codes : List UInt8 :=
  [0x43, 0x56]

inductive WarrantType where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ WarrantType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace WarrantType

def toByte : WarrantType → UInt8
  | .buy => 0x43
  | .sell => 0x56
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : WarrantType :=
  if byte = 0x43 then .buy
  else .sell

def ofByte (byte : UInt8) : WarrantType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : WarrantType) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : WarrantType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (WarrantType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : WarrantType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : WarrantType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : WarrantType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end WarrantType

/-- Option Type: one byte code -/
def OptionType.codes : List UInt8 :=
  [0x43, 0x50]

inductive OptionType where
  | call -- Call
  | put -- Put
  | unlisted (byte : { byte : UInt8 // byte ∉ OptionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OptionType

def toByte : OptionType → UInt8
  | .call => 0x43
  | .put => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OptionType :=
  if byte = 0x43 then .call
  else .put

def ofByte (byte : UInt8) : OptionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OptionType) : ofByte value.toByte = value := by
  cases value with
  | call => decide
  | put => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OptionType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OptionType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OptionType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OptionType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OptionType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OptionType

/-- Daily Maturity: one byte code -/
def DailyMaturity.codes : List UInt8 :=
  [0x31, 0x30]

inductive DailyMaturity where
  | forDailyMaturity -- For Daily Maturity
  | notDailyMaturity -- Not Daily Maturity
  | unlisted (byte : { byte : UInt8 // byte ∉ DailyMaturity.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DailyMaturity

def toByte : DailyMaturity → UInt8
  | .forDailyMaturity => 0x31
  | .notDailyMaturity => 0x30
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DailyMaturity :=
  if byte = 0x31 then .forDailyMaturity
  else .notDailyMaturity

def ofByte (byte : UInt8) : DailyMaturity :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DailyMaturity) : ofByte value.toByte = value := by
  cases value with
  | forDailyMaturity => decide
  | notDailyMaturity => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DailyMaturity) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DailyMaturity × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DailyMaturity) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : DailyMaturity) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : DailyMaturity) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DailyMaturity

/-- Type Of Strategy: one byte code -/
def TypeOfStrategy.codes : List UInt8 :=
  [0x52, 0x45, 0x46]

inductive TypeOfStrategy where
  | rollover -- Rollover
  | engrapado -- Engrapado
  | forward -- Forward
  | unlisted (byte : { byte : UInt8 // byte ∉ TypeOfStrategy.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TypeOfStrategy

def toByte : TypeOfStrategy → UInt8
  | .rollover => 0x52
  | .engrapado => 0x45
  | .forward => 0x46
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TypeOfStrategy :=
  if byte = 0x52 then .rollover
  else if byte = 0x45 then .engrapado
  else .forward

def ofByte (byte : UInt8) : TypeOfStrategy :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TypeOfStrategy) : ofByte value.toByte = value := by
  cases value with
  | rollover => decide
  | engrapado => decide
  | forward => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TypeOfStrategy) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TypeOfStrategy × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TypeOfStrategy) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TypeOfStrategy) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TypeOfStrategy) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TypeOfStrategy

/-- Catalog For Instruments Belonging To The Local And Global Stock Market Message: 111 bytes -/
structure CatalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage where
  instrumentNumber : BitVec 32
  valueType : Alpha 2
  issuer : Alpha 7
  series : Alpha 6
  lastPrice : BitVec 64
  wap : BitVec 64
  closingPrice : BitVec 64
  referenceDate : BitVec 64
  reference : Alpha 2
  currentCoupon : BitVec 16
  marketability : Alpha 2
  numericMarketability : BitVec 32
  isin : Alpha 12
  market : Market
  sharesOutstanding : BitVec 64
  blocksAmount : BitVec 64
  exchange : Exchange
  filler : Alpha 20
  deriving DecidableEq, Repr

namespace CatalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage

def encode (message : CatalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (Alpha.encode message.valueType
    ++ (Alpha.encode message.issuer
    ++ (Alpha.encode message.series
    ++ (encodeUInt 8 message.lastPrice
    ++ (encodeUInt 8 message.wap
    ++ (encodeUInt 8 message.closingPrice
    ++ (encodeUInt 8 message.referenceDate
    ++ (Alpha.encode message.reference
    ++ (encodeUInt 2 message.currentCoupon
    ++ (Alpha.encode message.marketability
    ++ (encodeUInt 4 message.numericMarketability
    ++ (Alpha.encode message.isin
    ++ (Market.encode message.market
    ++ (encodeUInt 8 message.sharesOutstanding
    ++ (encodeUInt 8 message.blocksAmount
    ++ (Exchange.encode message.exchange
    ++ (Alpha.encode message.filler)))))))))))))))))

def decode (bytes : List UInt8) : Option (CatalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (valueType, bytes) ← Alpha.decode 2 bytes
  let (issuer, bytes) ← Alpha.decode 7 bytes
  let (series, bytes) ← Alpha.decode 6 bytes
  let (lastPrice, bytes) ← decodeUInt 8 bytes
  let (wap, bytes) ← decodeUInt 8 bytes
  let (closingPrice, bytes) ← decodeUInt 8 bytes
  let (referenceDate, bytes) ← decodeUInt 8 bytes
  let (reference, bytes) ← Alpha.decode 2 bytes
  let (currentCoupon, bytes) ← decodeUInt 2 bytes
  let (marketability, bytes) ← Alpha.decode 2 bytes
  let (numericMarketability, bytes) ← decodeUInt 4 bytes
  let (isin, bytes) ← Alpha.decode 12 bytes
  let (market, bytes) ← Market.decode bytes
  let (sharesOutstanding, bytes) ← decodeUInt 8 bytes
  let (blocksAmount, bytes) ← decodeUInt 8 bytes
  let (exchange, bytes) ← Exchange.decode bytes
  let (filler, bytes) ← Alpha.decode 20 bytes
  pure ({ instrumentNumber, valueType, issuer, series, lastPrice, wap, closingPrice, referenceDate, reference, currentCoupon, marketability, numericMarketability, isin, market, sharesOutstanding, blocksAmount, exchange, filler }, bytes)

@[simp] theorem encode_length (message : CatalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage) : (encode message).length = 111 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, Market.encode_length, Exchange.encode_length]

theorem encode_length_pos (message : CatalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CatalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, Market.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Exchange.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end CatalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage

/-- Catalog Of Instruments That Belong To The Debt Metals And Money Market Message: 124 bytes -/
structure CatalogOfInstrumentsThatBelongToTheDebtMetalsAndMoneyMarketMessage where
  instrumentNumber : BitVec 32
  valueType : Alpha 2
  issuer : Alpha 7
  issue : Alpha 6
  issueDate : BitVec 64
  maturityDate : BitVec 64
  referencePricerate : BitVec 64
  referenceDate : BitVec 64
  reference : Alpha 2
  termDays : BitVec 16
  currentCoupon : BitVec 16
  isin : Alpha 12
  market : Market
  currentNominalValue : BitVec 64
  originalNominalValue : BitVec 64
  outstandingShares : BitVec 64
  amountPlaced : BitVec 64
  operatePriceRate : OperatePriceRate
  exchange : Exchange
  filler : Alpha 20
  deriving DecidableEq, Repr

namespace CatalogOfInstrumentsThatBelongToTheDebtMetalsAndMoneyMarketMessage

def encode (message : CatalogOfInstrumentsThatBelongToTheDebtMetalsAndMoneyMarketMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (Alpha.encode message.valueType
    ++ (Alpha.encode message.issuer
    ++ (Alpha.encode message.issue
    ++ (encodeUInt 8 message.issueDate
    ++ (encodeUInt 8 message.maturityDate
    ++ (encodeUInt 8 message.referencePricerate
    ++ (encodeUInt 8 message.referenceDate
    ++ (Alpha.encode message.reference
    ++ (encodeUInt 2 message.termDays
    ++ (encodeUInt 2 message.currentCoupon
    ++ (Alpha.encode message.isin
    ++ (Market.encode message.market
    ++ (encodeUInt 8 message.currentNominalValue
    ++ (encodeUInt 8 message.originalNominalValue
    ++ (encodeUInt 8 message.outstandingShares
    ++ (encodeUInt 8 message.amountPlaced
    ++ (OperatePriceRate.encode message.operatePriceRate
    ++ (Exchange.encode message.exchange
    ++ (Alpha.encode message.filler)))))))))))))))))))

def decode (bytes : List UInt8) : Option (CatalogOfInstrumentsThatBelongToTheDebtMetalsAndMoneyMarketMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (valueType, bytes) ← Alpha.decode 2 bytes
  let (issuer, bytes) ← Alpha.decode 7 bytes
  let (issue, bytes) ← Alpha.decode 6 bytes
  let (issueDate, bytes) ← decodeUInt 8 bytes
  let (maturityDate, bytes) ← decodeUInt 8 bytes
  let (referencePricerate, bytes) ← decodeUInt 8 bytes
  let (referenceDate, bytes) ← decodeUInt 8 bytes
  let (reference, bytes) ← Alpha.decode 2 bytes
  let (termDays, bytes) ← decodeUInt 2 bytes
  let (currentCoupon, bytes) ← decodeUInt 2 bytes
  let (isin, bytes) ← Alpha.decode 12 bytes
  let (market, bytes) ← Market.decode bytes
  let (currentNominalValue, bytes) ← decodeUInt 8 bytes
  let (originalNominalValue, bytes) ← decodeUInt 8 bytes
  let (outstandingShares, bytes) ← decodeUInt 8 bytes
  let (amountPlaced, bytes) ← decodeUInt 8 bytes
  let (operatePriceRate, bytes) ← OperatePriceRate.decode bytes
  let (exchange, bytes) ← Exchange.decode bytes
  let (filler, bytes) ← Alpha.decode 20 bytes
  pure ({ instrumentNumber, valueType, issuer, issue, issueDate, maturityDate, referencePricerate, referenceDate, reference, termDays, currentCoupon, isin, market, currentNominalValue, originalNominalValue, outstandingShares, amountPlaced, operatePriceRate, exchange, filler }, bytes)

@[simp] theorem encode_length (message : CatalogOfInstrumentsThatBelongToTheDebtMetalsAndMoneyMarketMessage) : (encode message).length = 124 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, Market.encode_length, OperatePriceRate.encode_length, Exchange.encode_length]

theorem encode_length_pos (message : CatalogOfInstrumentsThatBelongToTheDebtMetalsAndMoneyMarketMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CatalogOfInstrumentsThatBelongToTheDebtMetalsAndMoneyMarketMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Market.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OperatePriceRate.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Exchange.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end CatalogOfInstrumentsThatBelongToTheDebtMetalsAndMoneyMarketMessage

/-- Catalog For Instruments Belonging To The Capital Warrants Market Message: 87 bytes -/
structure CatalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage where
  instrumentNumber : BitVec 32
  valueType : Alpha 2
  issuer : Alpha 7
  series : Alpha 6
  warrantType : WarrantType
  maturityDate : BitVec 64
  exercisePrice : BitVec 64
  referencePrice : BitVec 64
  referenceDate : BitVec 64
  reference : Alpha 2
  isin : Alpha 12
  exchange : Exchange
  filler : Alpha 20
  deriving DecidableEq, Repr

namespace CatalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage

def encode (message : CatalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (Alpha.encode message.valueType
    ++ (Alpha.encode message.issuer
    ++ (Alpha.encode message.series
    ++ (WarrantType.encode message.warrantType
    ++ (encodeUInt 8 message.maturityDate
    ++ (encodeUInt 8 message.exercisePrice
    ++ (encodeUInt 8 message.referencePrice
    ++ (encodeUInt 8 message.referenceDate
    ++ (Alpha.encode message.reference
    ++ (Alpha.encode message.isin
    ++ (Exchange.encode message.exchange
    ++ (Alpha.encode message.filler))))))))))))

def decode (bytes : List UInt8) : Option (CatalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (valueType, bytes) ← Alpha.decode 2 bytes
  let (issuer, bytes) ← Alpha.decode 7 bytes
  let (series, bytes) ← Alpha.decode 6 bytes
  let (warrantType, bytes) ← WarrantType.decode bytes
  let (maturityDate, bytes) ← decodeUInt 8 bytes
  let (exercisePrice, bytes) ← decodeUInt 8 bytes
  let (referencePrice, bytes) ← decodeUInt 8 bytes
  let (referenceDate, bytes) ← decodeUInt 8 bytes
  let (reference, bytes) ← Alpha.decode 2 bytes
  let (isin, bytes) ← Alpha.decode 12 bytes
  let (exchange, bytes) ← Exchange.decode bytes
  let (filler, bytes) ← Alpha.decode 20 bytes
  pure ({ instrumentNumber, valueType, issuer, series, warrantType, maturityDate, exercisePrice, referencePrice, referenceDate, reference, isin, exchange, filler }, bytes)

@[simp] theorem encode_length (message : CatalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage) : (encode message).length = 87 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, WarrantType.encode_length, Exchange.encode_length]

theorem encode_length_pos (message : CatalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CatalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, WarrantType.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Exchange.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end CatalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage

/-- Options Futures And Swaps Derivatives Market Instruments Catalog Message: 113 bytes -/
structure OptionsFuturesAndSwapsDerivativesMarketInstrumentsCatalogMessage where
  instrumentNumber : BitVec 32
  valueType : Alpha 2
  class_ : Alpha 7
  maturity : Alpha 6
  optionType : OptionType
  exercisePrice : BitVec 64
  bid : BitVec 64
  priorDaySettlementPrice : BitVec 64
  lastDayOfOperation : BitVec 64
  maturityDate : BitVec 64
  openContracts : BitVec 32
  contractSize : BitVec 32
  productCode : Alpha 12
  dailyMaturity : DailyMaturity
  keyExercisePrice : Alpha 6
  cfiCode : Alpha 6
  filler : Alpha 20
  deriving DecidableEq, Repr

namespace OptionsFuturesAndSwapsDerivativesMarketInstrumentsCatalogMessage

def encode (message : OptionsFuturesAndSwapsDerivativesMarketInstrumentsCatalogMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (Alpha.encode message.valueType
    ++ (Alpha.encode message.class_
    ++ (Alpha.encode message.maturity
    ++ (OptionType.encode message.optionType
    ++ (encodeUInt 8 message.exercisePrice
    ++ (encodeUInt 8 message.bid
    ++ (encodeUInt 8 message.priorDaySettlementPrice
    ++ (encodeUInt 8 message.lastDayOfOperation
    ++ (encodeUInt 8 message.maturityDate
    ++ (encodeUInt 4 message.openContracts
    ++ (encodeUInt 4 message.contractSize
    ++ (Alpha.encode message.productCode
    ++ (DailyMaturity.encode message.dailyMaturity
    ++ (Alpha.encode message.keyExercisePrice
    ++ (Alpha.encode message.cfiCode
    ++ (Alpha.encode message.filler))))))))))))))))

def decode (bytes : List UInt8) : Option (OptionsFuturesAndSwapsDerivativesMarketInstrumentsCatalogMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (valueType, bytes) ← Alpha.decode 2 bytes
  let (class_, bytes) ← Alpha.decode 7 bytes
  let (maturity, bytes) ← Alpha.decode 6 bytes
  let (optionType, bytes) ← OptionType.decode bytes
  let (exercisePrice, bytes) ← decodeUInt 8 bytes
  let (bid, bytes) ← decodeUInt 8 bytes
  let (priorDaySettlementPrice, bytes) ← decodeUInt 8 bytes
  let (lastDayOfOperation, bytes) ← decodeUInt 8 bytes
  let (maturityDate, bytes) ← decodeUInt 8 bytes
  let (openContracts, bytes) ← decodeUInt 4 bytes
  let (contractSize, bytes) ← decodeUInt 4 bytes
  let (productCode, bytes) ← Alpha.decode 12 bytes
  let (dailyMaturity, bytes) ← DailyMaturity.decode bytes
  let (keyExercisePrice, bytes) ← Alpha.decode 6 bytes
  let (cfiCode, bytes) ← Alpha.decode 6 bytes
  let (filler, bytes) ← Alpha.decode 20 bytes
  pure ({ instrumentNumber, valueType, class_, maturity, optionType, exercisePrice, bid, priorDaySettlementPrice, lastDayOfOperation, maturityDate, openContracts, contractSize, productCode, dailyMaturity, keyExercisePrice, cfiCode, filler }, bytes)

@[simp] theorem encode_length (message : OptionsFuturesAndSwapsDerivativesMarketInstrumentsCatalogMessage) : (encode message).length = 113 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, OptionType.encode_length, DailyMaturity.encode_length]

theorem encode_length_pos (message : OptionsFuturesAndSwapsDerivativesMarketInstrumentsCatalogMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionsFuturesAndSwapsDerivativesMarketInstrumentsCatalogMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OptionType.decode_encode, some_bind]
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
  rw [List.append_assoc, DailyMaturity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OptionsFuturesAndSwapsDerivativesMarketInstrumentsCatalogMessage

/-- Catalog Sent For Instruments Belonging To Capital Tracs Message: 101 bytes -/
structure CatalogSentForInstrumentsBelongingToCapitalTracsMessage where
  tracNumber : BitVec 32
  tracName : Alpha 8
  underlyingIssuer : Alpha 7
  underlyingSeries : Alpha 6
  securities : BitVec 64
  excludedSecurities : BitVec 64
  price : BitVec 64
  cashComponent : BitVec 64
  excludedValue : BitVec 64
  numberOfCertificates : BitVec 64
  theoreticalPrice : BitVec 64
  filler : Alpha 20
  deriving DecidableEq, Repr

namespace CatalogSentForInstrumentsBelongingToCapitalTracsMessage

def encode (message : CatalogSentForInstrumentsBelongingToCapitalTracsMessage) : List UInt8 :=
  encodeUInt 4 message.tracNumber
    ++ (Alpha.encode message.tracName
    ++ (Alpha.encode message.underlyingIssuer
    ++ (Alpha.encode message.underlyingSeries
    ++ (encodeUInt 8 message.securities
    ++ (encodeUInt 8 message.excludedSecurities
    ++ (encodeUInt 8 message.price
    ++ (encodeUInt 8 message.cashComponent
    ++ (encodeUInt 8 message.excludedValue
    ++ (encodeUInt 8 message.numberOfCertificates
    ++ (encodeUInt 8 message.theoreticalPrice
    ++ (Alpha.encode message.filler)))))))))))

def decode (bytes : List UInt8) : Option (CatalogSentForInstrumentsBelongingToCapitalTracsMessage × List UInt8) := do
  let (tracNumber, bytes) ← decodeUInt 4 bytes
  let (tracName, bytes) ← Alpha.decode 8 bytes
  let (underlyingIssuer, bytes) ← Alpha.decode 7 bytes
  let (underlyingSeries, bytes) ← Alpha.decode 6 bytes
  let (securities, bytes) ← decodeUInt 8 bytes
  let (excludedSecurities, bytes) ← decodeUInt 8 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (cashComponent, bytes) ← decodeUInt 8 bytes
  let (excludedValue, bytes) ← decodeUInt 8 bytes
  let (numberOfCertificates, bytes) ← decodeUInt 8 bytes
  let (theoreticalPrice, bytes) ← decodeUInt 8 bytes
  let (filler, bytes) ← Alpha.decode 20 bytes
  pure ({ tracNumber, tracName, underlyingIssuer, underlyingSeries, securities, excludedSecurities, price, cashComponent, excludedValue, numberOfCertificates, theoreticalPrice, filler }, bytes)

@[simp] theorem encode_length (message : CatalogSentForInstrumentsBelongingToCapitalTracsMessage) : (encode message).length = 101 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : CatalogSentForInstrumentsBelongingToCapitalTracsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CatalogSentForInstrumentsBelongingToCapitalTracsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end CatalogSentForInstrumentsBelongingToCapitalTracsMessage

/-- Catalog Sent For Instruments Belonging To Mutual Funds Message: 98 bytes -/
structure CatalogSentForInstrumentsBelongingToMutualFundsMessage where
  instrumentNumber : BitVec 32
  valueType : Alpha 2
  issuer : Alpha 7
  series : Alpha 6
  sector : BitVec 8
  subsector : BitVec 8
  businessLine : BitVec 8
  subLine : BitVec 8
  operatingCompany : Alpha 10
  referencePrice : BitVec 64
  referenceDate : BitVec 64
  reference : Alpha 2
  isin : Alpha 12
  rating : Alpha 15
  filler : Alpha 20
  deriving DecidableEq, Repr

namespace CatalogSentForInstrumentsBelongingToMutualFundsMessage

def encode (message : CatalogSentForInstrumentsBelongingToMutualFundsMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (Alpha.encode message.valueType
    ++ (Alpha.encode message.issuer
    ++ (Alpha.encode message.series
    ++ (encodeUInt 1 message.sector
    ++ (encodeUInt 1 message.subsector
    ++ (encodeUInt 1 message.businessLine
    ++ (encodeUInt 1 message.subLine
    ++ (Alpha.encode message.operatingCompany
    ++ (encodeUInt 8 message.referencePrice
    ++ (encodeUInt 8 message.referenceDate
    ++ (Alpha.encode message.reference
    ++ (Alpha.encode message.isin
    ++ (Alpha.encode message.rating
    ++ (Alpha.encode message.filler))))))))))))))

def decode (bytes : List UInt8) : Option (CatalogSentForInstrumentsBelongingToMutualFundsMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (valueType, bytes) ← Alpha.decode 2 bytes
  let (issuer, bytes) ← Alpha.decode 7 bytes
  let (series, bytes) ← Alpha.decode 6 bytes
  let (sector, bytes) ← decodeUInt 1 bytes
  let (subsector, bytes) ← decodeUInt 1 bytes
  let (businessLine, bytes) ← decodeUInt 1 bytes
  let (subLine, bytes) ← decodeUInt 1 bytes
  let (operatingCompany, bytes) ← Alpha.decode 10 bytes
  let (referencePrice, bytes) ← decodeUInt 8 bytes
  let (referenceDate, bytes) ← decodeUInt 8 bytes
  let (reference, bytes) ← Alpha.decode 2 bytes
  let (isin, bytes) ← Alpha.decode 12 bytes
  let (rating, bytes) ← Alpha.decode 15 bytes
  let (filler, bytes) ← Alpha.decode 20 bytes
  pure ({ instrumentNumber, valueType, issuer, series, sector, subsector, businessLine, subLine, operatingCompany, referencePrice, referenceDate, reference, isin, rating, filler }, bytes)

@[simp] theorem encode_length (message : CatalogSentForInstrumentsBelongingToMutualFundsMessage) : (encode message).length = 98 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : CatalogSentForInstrumentsBelongingToMutualFundsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CatalogSentForInstrumentsBelongingToMutualFundsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end CatalogSentForInstrumentsBelongingToMutualFundsMessage

/-- Catalog Sent For Instruments Belonging To The Strategy Derivative Market Message: 74 bytes -/
structure CatalogSentForInstrumentsBelongingToTheStrategyDerivativeMarketMessage where
  instrumentNumber : BitVec 32
  valueType : Alpha 2
  class_ : Alpha 7
  maturity : Alpha 6
  typeOfStrategy : TypeOfStrategy
  bid : BitVec 64
  lastDateOperation : BitVec 64
  maturityDate : BitVec 64
  shortLegInstrumentIdentifier : BitVec 32
  longLegInstrumentsId : BitVec 32
  frequency : BitVec 8
  numberOfMaturities : BitVec 8
  filler : Alpha 20
  deriving DecidableEq, Repr

namespace CatalogSentForInstrumentsBelongingToTheStrategyDerivativeMarketMessage

def encode (message : CatalogSentForInstrumentsBelongingToTheStrategyDerivativeMarketMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (Alpha.encode message.valueType
    ++ (Alpha.encode message.class_
    ++ (Alpha.encode message.maturity
    ++ (TypeOfStrategy.encode message.typeOfStrategy
    ++ (encodeUInt 8 message.bid
    ++ (encodeUInt 8 message.lastDateOperation
    ++ (encodeUInt 8 message.maturityDate
    ++ (encodeUInt 4 message.shortLegInstrumentIdentifier
    ++ (encodeUInt 4 message.longLegInstrumentsId
    ++ (encodeUInt 1 message.frequency
    ++ (encodeUInt 1 message.numberOfMaturities
    ++ (Alpha.encode message.filler))))))))))))

def decode (bytes : List UInt8) : Option (CatalogSentForInstrumentsBelongingToTheStrategyDerivativeMarketMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (valueType, bytes) ← Alpha.decode 2 bytes
  let (class_, bytes) ← Alpha.decode 7 bytes
  let (maturity, bytes) ← Alpha.decode 6 bytes
  let (typeOfStrategy, bytes) ← TypeOfStrategy.decode bytes
  let (bid, bytes) ← decodeUInt 8 bytes
  let (lastDateOperation, bytes) ← decodeUInt 8 bytes
  let (maturityDate, bytes) ← decodeUInt 8 bytes
  let (shortLegInstrumentIdentifier, bytes) ← decodeUInt 4 bytes
  let (longLegInstrumentsId, bytes) ← decodeUInt 4 bytes
  let (frequency, bytes) ← decodeUInt 1 bytes
  let (numberOfMaturities, bytes) ← decodeUInt 1 bytes
  let (filler, bytes) ← Alpha.decode 20 bytes
  pure ({ instrumentNumber, valueType, class_, maturity, typeOfStrategy, bid, lastDateOperation, maturityDate, shortLegInstrumentIdentifier, longLegInstrumentsId, frequency, numberOfMaturities, filler }, bytes)

@[simp] theorem encode_length (message : CatalogSentForInstrumentsBelongingToTheStrategyDerivativeMarketMessage) : (encode message).length = 74 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, TypeOfStrategy.encode_length]

theorem encode_length_pos (message : CatalogSentForInstrumentsBelongingToTheStrategyDerivativeMarketMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CatalogSentForInstrumentsBelongingToTheStrategyDerivativeMarketMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TypeOfStrategy.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end CatalogSentForInstrumentsBelongingToTheStrategyDerivativeMarketMessage

/-- Underlying Value On Warrants Catalog Message: 63 bytes -/
structure UnderlyingValueOnWarrantsCatalogMessage where
  instrumentNumber : BitVec 32
  issuer : Alpha 7
  series : Alpha 6
  valueType : Alpha 2
  underlyingIssuer : Alpha 7
  underlyingSeries : Alpha 6
  underlyingValueType : Alpha 2
  numberOfRegisteredValues : BitVec 64
  exchange : Exchange
  filler : Alpha 20
  deriving DecidableEq, Repr

namespace UnderlyingValueOnWarrantsCatalogMessage

def encode (message : UnderlyingValueOnWarrantsCatalogMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (Alpha.encode message.issuer
    ++ (Alpha.encode message.series
    ++ (Alpha.encode message.valueType
    ++ (Alpha.encode message.underlyingIssuer
    ++ (Alpha.encode message.underlyingSeries
    ++ (Alpha.encode message.underlyingValueType
    ++ (encodeUInt 8 message.numberOfRegisteredValues
    ++ (Exchange.encode message.exchange
    ++ (Alpha.encode message.filler)))))))))

def decode (bytes : List UInt8) : Option (UnderlyingValueOnWarrantsCatalogMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (issuer, bytes) ← Alpha.decode 7 bytes
  let (series, bytes) ← Alpha.decode 6 bytes
  let (valueType, bytes) ← Alpha.decode 2 bytes
  let (underlyingIssuer, bytes) ← Alpha.decode 7 bytes
  let (underlyingSeries, bytes) ← Alpha.decode 6 bytes
  let (underlyingValueType, bytes) ← Alpha.decode 2 bytes
  let (numberOfRegisteredValues, bytes) ← decodeUInt 8 bytes
  let (exchange, bytes) ← Exchange.decode bytes
  let (filler, bytes) ← Alpha.decode 20 bytes
  pure ({ instrumentNumber, issuer, series, valueType, underlyingIssuer, underlyingSeries, underlyingValueType, numberOfRegisteredValues, exchange, filler }, bytes)

@[simp] theorem encode_length (message : UnderlyingValueOnWarrantsCatalogMessage) : (encode message).length = 63 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, Exchange.encode_length]

theorem encode_length_pos (message : UnderlyingValueOnWarrantsCatalogMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UnderlyingValueOnWarrantsCatalogMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Exchange.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end UnderlyingValueOnWarrantsCatalogMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | catalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage (message : CatalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage) -- 25441
  | catalogOfInstrumentsThatBelongToTheDebtMetalsAndMoneyMarketMessage (message : CatalogOfInstrumentsThatBelongToTheDebtMetalsAndMoneyMarketMessage) -- 25442
  | catalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage (message : CatalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage) -- 25443
  | optionsFuturesAndSwapsDerivativesMarketInstrumentsCatalogMessage (message : OptionsFuturesAndSwapsDerivativesMarketInstrumentsCatalogMessage) -- 25444
  | catalogSentForInstrumentsBelongingToCapitalTracsMessage (message : CatalogSentForInstrumentsBelongingToCapitalTracsMessage) -- 25445
  | catalogSentForInstrumentsBelongingToMutualFundsMessage (message : CatalogSentForInstrumentsBelongingToMutualFundsMessage) -- 25446
  | catalogSentForInstrumentsBelongingToTheStrategyDerivativeMarketMessage (message : CatalogSentForInstrumentsBelongingToTheStrategyDerivativeMarketMessage) -- 25447
  | underlyingValueOnWarrantsCatalogMessage (message : UnderlyingValueOnWarrantsCatalogMessage) -- 25465
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 16
  | .catalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage _ => 25441
  | .catalogOfInstrumentsThatBelongToTheDebtMetalsAndMoneyMarketMessage _ => 25442
  | .catalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage _ => 25443
  | .optionsFuturesAndSwapsDerivativesMarketInstrumentsCatalogMessage _ => 25444
  | .catalogSentForInstrumentsBelongingToCapitalTracsMessage _ => 25445
  | .catalogSentForInstrumentsBelongingToMutualFundsMessage _ => 25446
  | .catalogSentForInstrumentsBelongingToTheStrategyDerivativeMarketMessage _ => 25447
  | .underlyingValueOnWarrantsCatalogMessage _ => 25465

def encode : Payload → List UInt8
  | .catalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage message => CatalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage.encode message
  | .catalogOfInstrumentsThatBelongToTheDebtMetalsAndMoneyMarketMessage message => CatalogOfInstrumentsThatBelongToTheDebtMetalsAndMoneyMarketMessage.encode message
  | .catalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage message => CatalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage.encode message
  | .optionsFuturesAndSwapsDerivativesMarketInstrumentsCatalogMessage message => OptionsFuturesAndSwapsDerivativesMarketInstrumentsCatalogMessage.encode message
  | .catalogSentForInstrumentsBelongingToCapitalTracsMessage message => CatalogSentForInstrumentsBelongingToCapitalTracsMessage.encode message
  | .catalogSentForInstrumentsBelongingToMutualFundsMessage message => CatalogSentForInstrumentsBelongingToMutualFundsMessage.encode message
  | .catalogSentForInstrumentsBelongingToTheStrategyDerivativeMarketMessage message => CatalogSentForInstrumentsBelongingToTheStrategyDerivativeMarketMessage.encode message
  | .underlyingValueOnWarrantsCatalogMessage message => UnderlyingValueOnWarrantsCatalogMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 124 := by
  cases message with
  | catalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage inner =>
    simp only [encode, CatalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage.encode_length]
    omega
  | catalogOfInstrumentsThatBelongToTheDebtMetalsAndMoneyMarketMessage inner =>
    simp only [encode, CatalogOfInstrumentsThatBelongToTheDebtMetalsAndMoneyMarketMessage.encode_length]
    omega
  | catalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage inner =>
    simp only [encode, CatalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage.encode_length]
    omega
  | optionsFuturesAndSwapsDerivativesMarketInstrumentsCatalogMessage inner =>
    simp only [encode, OptionsFuturesAndSwapsDerivativesMarketInstrumentsCatalogMessage.encode_length]
    omega
  | catalogSentForInstrumentsBelongingToCapitalTracsMessage inner =>
    simp only [encode, CatalogSentForInstrumentsBelongingToCapitalTracsMessage.encode_length]
    omega
  | catalogSentForInstrumentsBelongingToMutualFundsMessage inner =>
    simp only [encode, CatalogSentForInstrumentsBelongingToMutualFundsMessage.encode_length]
    omega
  | catalogSentForInstrumentsBelongingToTheStrategyDerivativeMarketMessage inner =>
    simp only [encode, CatalogSentForInstrumentsBelongingToTheStrategyDerivativeMarketMessage.encode_length]
    omega
  | underlyingValueOnWarrantsCatalogMessage inner =>
    simp only [encode, UnderlyingValueOnWarrantsCatalogMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 25441 then (CatalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage.decode bytes).map fun (message, rest) => (.catalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage message, rest)
  else if tag = 25442 then (CatalogOfInstrumentsThatBelongToTheDebtMetalsAndMoneyMarketMessage.decode bytes).map fun (message, rest) => (.catalogOfInstrumentsThatBelongToTheDebtMetalsAndMoneyMarketMessage message, rest)
  else if tag = 25443 then (CatalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage.decode bytes).map fun (message, rest) => (.catalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage message, rest)
  else if tag = 25444 then (OptionsFuturesAndSwapsDerivativesMarketInstrumentsCatalogMessage.decode bytes).map fun (message, rest) => (.optionsFuturesAndSwapsDerivativesMarketInstrumentsCatalogMessage message, rest)
  else if tag = 25445 then (CatalogSentForInstrumentsBelongingToCapitalTracsMessage.decode bytes).map fun (message, rest) => (.catalogSentForInstrumentsBelongingToCapitalTracsMessage message, rest)
  else if tag = 25446 then (CatalogSentForInstrumentsBelongingToMutualFundsMessage.decode bytes).map fun (message, rest) => (.catalogSentForInstrumentsBelongingToMutualFundsMessage message, rest)
  else if tag = 25447 then (CatalogSentForInstrumentsBelongingToTheStrategyDerivativeMarketMessage.decode bytes).map fun (message, rest) => (.catalogSentForInstrumentsBelongingToTheStrategyDerivativeMarketMessage message, rest)
  else if tag = 25465 then (UnderlyingValueOnWarrantsCatalogMessage.decode bytes).map fun (message, rest) => (.underlyingValueOnWarrantsCatalogMessage message, rest)
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
  | catalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, CatalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage.encode_length]
    omega
  | catalogOfInstrumentsThatBelongToTheDebtMetalsAndMoneyMarketMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, CatalogOfInstrumentsThatBelongToTheDebtMetalsAndMoneyMarketMessage.encode_length]
    omega
  | catalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, CatalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage.encode_length]
    omega
  | optionsFuturesAndSwapsDerivativesMarketInstrumentsCatalogMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OptionsFuturesAndSwapsDerivativesMarketInstrumentsCatalogMessage.encode_length]
    omega
  | catalogSentForInstrumentsBelongingToCapitalTracsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, CatalogSentForInstrumentsBelongingToCapitalTracsMessage.encode_length]
    omega
  | catalogSentForInstrumentsBelongingToMutualFundsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, CatalogSentForInstrumentsBelongingToMutualFundsMessage.encode_length]
    omega
  | catalogSentForInstrumentsBelongingToTheStrategyDerivativeMarketMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, CatalogSentForInstrumentsBelongingToTheStrategyDerivativeMarketMessage.encode_length]
    omega
  | underlyingValueOnWarrantsCatalogMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, UnderlyingValueOnWarrantsCatalogMessage.encode_length]
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

end Omi.BmvBmvmarketdataProduct40IntraV11
