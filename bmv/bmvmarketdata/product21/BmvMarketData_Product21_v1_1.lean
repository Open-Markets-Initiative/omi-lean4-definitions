import Wire

/-!
# Bolsa Mexicana de Valores Bmv Market Data Product 21 v1.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.

License: MIT No Attribution
-/

namespace Omi.BmvBmvmarketdataProduct21IntraV11

/-- Event Code: one byte code -/
def EventCode.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x4A, 0x4B, 0x4D, 0x4E, 0x4F, 0x50, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57]

inductive EventCode where
  | startOfSystemHours -- Start Of System Hours
  | cancelationOfOffers -- Cancelation Of Offers
  | startOfOpeningAuction -- Start Of Opening Auction
  | startOfContinuousMarket -- Start Of Continuous Market
  | startOfWapPeriod -- Start Of Wap Period
  | continuousMarketEnds -- Continuous Market Ends
  | startOfAfterClosingPhase -- Start Of After Closing Phase
  | itEndsAfterClosing -- It Ends After Closing
  | transmissionOfFinalPricesEnds -- Transmission Of Final Prices Ends
  | endOfSystemHours -- End Of System Hours
  | startOfAdministrativeRecess -- Start Of Administrative Recess
  | endOfAdministrativeRecess -- End Of Administrative Recess
  | startDvmamxMarkets -- Start Dvmamx Markets
  | endOfDvmaMarkets -- End Of Dvma Markets
  | endOfMxMarkets -- End Of Mx Markets
  | startOfOpcModality -- Start Of Opc Modality
  | endOfOpcModality -- End Of Opc Modality
  | startOfSettlementAuction -- Start Of Settlement Auction
  | endOfSettlementAuction -- End Of Settlement Auction
  | finalRegisterOfSettlementPrices -- Final Register Of Settlement Prices
  | openInterest -- Open Interest
  | unlisted (byte : { byte : UInt8 // byte ∉ EventCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventCode

def toByte : EventCode → UInt8
  | .startOfSystemHours => 0x41
  | .cancelationOfOffers => 0x42
  | .startOfOpeningAuction => 0x43
  | .startOfContinuousMarket => 0x44
  | .startOfWapPeriod => 0x45
  | .continuousMarketEnds => 0x46
  | .startOfAfterClosingPhase => 0x47
  | .itEndsAfterClosing => 0x48
  | .transmissionOfFinalPricesEnds => 0x4A
  | .endOfSystemHours => 0x4B
  | .startOfAdministrativeRecess => 0x4D
  | .endOfAdministrativeRecess => 0x4E
  | .startDvmamxMarkets => 0x4F
  | .endOfDvmaMarkets => 0x50
  | .endOfMxMarkets => 0x51
  | .startOfOpcModality => 0x52
  | .endOfOpcModality => 0x53
  | .startOfSettlementAuction => 0x54
  | .endOfSettlementAuction => 0x55
  | .finalRegisterOfSettlementPrices => 0x56
  | .openInterest => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventCode :=
  if byte = 0x41 then .startOfSystemHours
  else if byte = 0x42 then .cancelationOfOffers
  else if byte = 0x43 then .startOfOpeningAuction
  else if byte = 0x44 then .startOfContinuousMarket
  else if byte = 0x45 then .startOfWapPeriod
  else if byte = 0x46 then .continuousMarketEnds
  else if byte = 0x47 then .startOfAfterClosingPhase
  else if byte = 0x48 then .itEndsAfterClosing
  else if byte = 0x4A then .transmissionOfFinalPricesEnds
  else if byte = 0x4B then .endOfSystemHours
  else if byte = 0x4D then .startOfAdministrativeRecess
  else if byte = 0x4E then .endOfAdministrativeRecess
  else if byte = 0x4F then .startDvmamxMarkets
  else if byte = 0x50 then .endOfDvmaMarkets
  else if byte = 0x51 then .endOfMxMarkets
  else if byte = 0x52 then .startOfOpcModality
  else if byte = 0x53 then .endOfOpcModality
  else if byte = 0x54 then .startOfSettlementAuction
  else if byte = 0x55 then .endOfSettlementAuction
  else if byte = 0x56 then .finalRegisterOfSettlementPrices
  else .openInterest

def ofByte (byte : UInt8) : EventCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventCode) : ofByte value.toByte = value := by
  cases value with
  | startOfSystemHours => decide
  | cancelationOfOffers => decide
  | startOfOpeningAuction => decide
  | startOfContinuousMarket => decide
  | startOfWapPeriod => decide
  | continuousMarketEnds => decide
  | startOfAfterClosingPhase => decide
  | itEndsAfterClosing => decide
  | transmissionOfFinalPricesEnds => decide
  | endOfSystemHours => decide
  | startOfAdministrativeRecess => decide
  | endOfAdministrativeRecess => decide
  | startDvmamxMarkets => decide
  | endOfDvmaMarkets => decide
  | endOfMxMarkets => decide
  | startOfOpcModality => decide
  | endOfOpcModality => decide
  | startOfSettlementAuction => decide
  | endOfSettlementAuction => decide
  | finalRegisterOfSettlementPrices => decide
  | openInterest => decide
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

/-- Multiple Type: one byte code -/
def MultipleType.codes : List UInt8 :=
  [0x45, 0x53]

inductive MultipleType where
  | multipleOfMarketByTransmitter -- Multiple Of Market By Transmitter
  | multipleOfMarketBySector -- Multiple Of Market By Sector
  | unlisted (byte : { byte : UInt8 // byte ∉ MultipleType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MultipleType

def toByte : MultipleType → UInt8
  | .multipleOfMarketByTransmitter => 0x45
  | .multipleOfMarketBySector => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MultipleType :=
  if byte = 0x45 then .multipleOfMarketByTransmitter
  else .multipleOfMarketBySector

def ofByte (byte : UInt8) : MultipleType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MultipleType) : ofByte value.toByte = value := by
  cases value with
  | multipleOfMarketByTransmitter => decide
  | multipleOfMarketBySector => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MultipleType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MultipleType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MultipleType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : MultipleType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : MultipleType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MultipleType

/-- Rebalance: one byte code -/
def Rebalance.codes : List UInt8 :=
  [0x52, 0x4E]

inductive Rebalance where
  | rebalanced -- Rebalanced
  | notRebalanced -- Not Rebalanced
  | unlisted (byte : { byte : UInt8 // byte ∉ Rebalance.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Rebalance

def toByte : Rebalance → UInt8
  | .rebalanced => 0x52
  | .notRebalanced => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Rebalance :=
  if byte = 0x52 then .rebalanced
  else .notRebalanced

def ofByte (byte : UInt8) : Rebalance :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Rebalance) : ofByte value.toByte = value := by
  cases value with
  | rebalanced => decide
  | notRebalanced => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Rebalance) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Rebalance × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Rebalance) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Rebalance) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Rebalance) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Rebalance

/-- Events System Message: 22 bytes -/
structure EventsSystemMessage where
  instrumentNumber : BitVec 32
  eventCode : EventCode
  market : Market
  sendingTime : BitVec 64
  endingTime : BitVec 64
  deriving DecidableEq, Repr

namespace EventsSystemMessage

def encode (message : EventsSystemMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (EventCode.encode message.eventCode
    ++ (Market.encode message.market
    ++ (encodeUInt 8 message.sendingTime
    ++ (encodeUInt 8 message.endingTime))))

def decode (bytes : List UInt8) : Option (EventsSystemMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (eventCode, bytes) ← EventCode.decode bytes
  let (market, bytes) ← Market.decode bytes
  let (sendingTime, bytes) ← decodeUInt 8 bytes
  let (endingTime, bytes) ← decodeUInt 8 bytes
  pure ({ instrumentNumber, eventCode, market, sendingTime, endingTime }, bytes)

@[simp] theorem encode_length (message : EventsSystemMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, EventCode.encode_length, Market.encode_length]

theorem encode_length_pos (message : EventsSystemMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EventsSystemMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, EventCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Market.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end EventsSystemMessage

/-- Dollar Buy Sell Message: 38 bytes -/
structure DollarBuySellMessage where
  postureDate : BitVec 64
  currency : Alpha 5
  dollarSide : Alpha 1
  buy : BitVec 64
  sell : BitVec 64
  lastDeal : BitVec 64
  deriving DecidableEq, Repr

namespace DollarBuySellMessage

def encode (message : DollarBuySellMessage) : List UInt8 :=
  encodeUInt 8 message.postureDate
    ++ (Alpha.encode message.currency
    ++ (Alpha.encode message.dollarSide
    ++ (encodeUInt 8 message.buy
    ++ (encodeUInt 8 message.sell
    ++ (encodeUInt 8 message.lastDeal)))))

def decode (bytes : List UInt8) : Option (DollarBuySellMessage × List UInt8) := do
  let (postureDate, bytes) ← decodeUInt 8 bytes
  let (currency, bytes) ← Alpha.decode 5 bytes
  let (dollarSide, bytes) ← Alpha.decode 1 bytes
  let (buy, bytes) ← decodeUInt 8 bytes
  let (sell, bytes) ← decodeUInt 8 bytes
  let (lastDeal, bytes) ← decodeUInt 8 bytes
  pure ({ postureDate, currency, dollarSide, buy, sell, lastDeal }, bytes)

@[simp] theorem encode_length (message : DollarBuySellMessage) : (encode message).length = 38 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : DollarBuySellMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DollarBuySellMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end DollarBuySellMessage

/-- Short Sales Balances Per Instrument Message: 44 bytes -/
structure ShortSalesBalancesPerInstrumentMessage where
  instrumentNumber : BitVec 32
  date : BitVec 64
  previousBalance : BitVec 64
  amountTraded : BitVec 64
  buybacks : BitVec 64
  currentBalance : BitVec 64
  deriving DecidableEq, Repr

namespace ShortSalesBalancesPerInstrumentMessage

def encode (message : ShortSalesBalancesPerInstrumentMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (encodeUInt 8 message.date
    ++ (encodeUInt 8 message.previousBalance
    ++ (encodeUInt 8 message.amountTraded
    ++ (encodeUInt 8 message.buybacks
    ++ (encodeUInt 8 message.currentBalance)))))

def decode (bytes : List UInt8) : Option (ShortSalesBalancesPerInstrumentMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (date, bytes) ← decodeUInt 8 bytes
  let (previousBalance, bytes) ← decodeUInt 8 bytes
  let (amountTraded, bytes) ← decodeUInt 8 bytes
  let (buybacks, bytes) ← decodeUInt 8 bytes
  let (currentBalance, bytes) ← decodeUInt 8 bytes
  pure ({ instrumentNumber, date, previousBalance, amountTraded, buybacks, currentBalance }, bytes)

@[simp] theorem encode_length (message : ShortSalesBalancesPerInstrumentMessage) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : ShortSalesBalancesPerInstrumentMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ShortSalesBalancesPerInstrumentMessage) (rest : List UInt8) :
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

end ShortSalesBalancesPerInstrumentMessage

/-- Capital Market Multiples Message: 130 bytes -/
structure CapitalMarketMultiplesMessage where
  instrumentId : BitVec 32
  multipleType : MultipleType
  registryNumber : Alpha 1
  sector : BitVec 8
  subsector : BitVec 8
  businessLine : BitVec 8
  subLine : BitVec 8
  pflepaMultiple : BitVec 64
  pfepaMultiple : BitVec 64
  veUaiidaMultiple : BitVec 64
  pU : BitVec 64
  pVl : BitVec 64
  f1PUnoc : BitVec 64
  f2PUnoc : BitVec 64
  f1PUe : BitVec 64
  f2PUe : BitVec 64
  f1VeUaiida : BitVec 64
  f2VeUaiida : BitVec 64
  f1PU : BitVec 64
  f2PU : BitVec 64
  f1PVl : BitVec 64
  f2PVl : BitVec 64
  deriving DecidableEq, Repr

namespace CapitalMarketMultiplesMessage

def encode (message : CapitalMarketMultiplesMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentId
    ++ (MultipleType.encode message.multipleType
    ++ (Alpha.encode message.registryNumber
    ++ (encodeUInt 1 message.sector
    ++ (encodeUInt 1 message.subsector
    ++ (encodeUInt 1 message.businessLine
    ++ (encodeUInt 1 message.subLine
    ++ (encodeUInt 8 message.pflepaMultiple
    ++ (encodeUInt 8 message.pfepaMultiple
    ++ (encodeUInt 8 message.veUaiidaMultiple
    ++ (encodeUInt 8 message.pU
    ++ (encodeUInt 8 message.pVl
    ++ (encodeUInt 8 message.f1PUnoc
    ++ (encodeUInt 8 message.f2PUnoc
    ++ (encodeUInt 8 message.f1PUe
    ++ (encodeUInt 8 message.f2PUe
    ++ (encodeUInt 8 message.f1VeUaiida
    ++ (encodeUInt 8 message.f2VeUaiida
    ++ (encodeUInt 8 message.f1PU
    ++ (encodeUInt 8 message.f2PU
    ++ (encodeUInt 8 message.f1PVl
    ++ (encodeUInt 8 message.f2PVl)))))))))))))))))))))

def decode (bytes : List UInt8) : Option (CapitalMarketMultiplesMessage × List UInt8) := do
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (multipleType, bytes) ← MultipleType.decode bytes
  let (registryNumber, bytes) ← Alpha.decode 1 bytes
  let (sector, bytes) ← decodeUInt 1 bytes
  let (subsector, bytes) ← decodeUInt 1 bytes
  let (businessLine, bytes) ← decodeUInt 1 bytes
  let (subLine, bytes) ← decodeUInt 1 bytes
  let (pflepaMultiple, bytes) ← decodeUInt 8 bytes
  let (pfepaMultiple, bytes) ← decodeUInt 8 bytes
  let (veUaiidaMultiple, bytes) ← decodeUInt 8 bytes
  let (pU, bytes) ← decodeUInt 8 bytes
  let (pVl, bytes) ← decodeUInt 8 bytes
  let (f1PUnoc, bytes) ← decodeUInt 8 bytes
  let (f2PUnoc, bytes) ← decodeUInt 8 bytes
  let (f1PUe, bytes) ← decodeUInt 8 bytes
  let (f2PUe, bytes) ← decodeUInt 8 bytes
  let (f1VeUaiida, bytes) ← decodeUInt 8 bytes
  let (f2VeUaiida, bytes) ← decodeUInt 8 bytes
  let (f1PU, bytes) ← decodeUInt 8 bytes
  let (f2PU, bytes) ← decodeUInt 8 bytes
  let (f1PVl, bytes) ← decodeUInt 8 bytes
  let (f2PVl, bytes) ← decodeUInt 8 bytes
  pure ({ instrumentId, multipleType, registryNumber, sector, subsector, businessLine, subLine, pflepaMultiple, pfepaMultiple, veUaiidaMultiple, pU, pVl, f1PUnoc, f2PUnoc, f1PUe, f2PUe, f1VeUaiida, f2VeUaiida, f1PU, f2PU, f1PVl, f2PVl }, bytes)

@[simp] theorem encode_length (message : CapitalMarketMultiplesMessage) : (encode message).length = 130 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, MultipleType.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : CapitalMarketMultiplesMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CapitalMarketMultiplesMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MultipleType.decode_encode, some_bind]
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

end CapitalMarketMultiplesMessage

/-- Benchmark Message: 149 bytes -/
structure BenchmarkMessage where
  benchmarkName : Alpha 40
  benchmarkDate : BitVec 64
  outstanding : BitVec 64
  integerAmount : BitVec 64
  decimalAmount : BitVec 32
  indices : BitVec 64
  indices24 : BitVec 64
  rebalance : Rebalance
  dailyPerformance : BitVec 64
  annualPerformance : BitVec 64
  monthlyPerformance : BitVec 64
  last12MonthsPerformance : BitVec 64
  t24HoursDailyPerformance : BitVec 64
  t24HoursAnnualPerformance : BitVec 64
  t24HoursMonthlyPerformance : BitVec 64
  last12Months24HoursPerformance : BitVec 64
  deriving DecidableEq, Repr

namespace BenchmarkMessage

def encode (message : BenchmarkMessage) : List UInt8 :=
  Alpha.encode message.benchmarkName
    ++ (encodeUInt 8 message.benchmarkDate
    ++ (encodeUInt 8 message.outstanding
    ++ (encodeUInt 8 message.integerAmount
    ++ (encodeUInt 4 message.decimalAmount
    ++ (encodeUInt 8 message.indices
    ++ (encodeUInt 8 message.indices24
    ++ (Rebalance.encode message.rebalance
    ++ (encodeUInt 8 message.dailyPerformance
    ++ (encodeUInt 8 message.annualPerformance
    ++ (encodeUInt 8 message.monthlyPerformance
    ++ (encodeUInt 8 message.last12MonthsPerformance
    ++ (encodeUInt 8 message.t24HoursDailyPerformance
    ++ (encodeUInt 8 message.t24HoursAnnualPerformance
    ++ (encodeUInt 8 message.t24HoursMonthlyPerformance
    ++ (encodeUInt 8 message.last12Months24HoursPerformance)))))))))))))))

def decode (bytes : List UInt8) : Option (BenchmarkMessage × List UInt8) := do
  let (benchmarkName, bytes) ← Alpha.decode 40 bytes
  let (benchmarkDate, bytes) ← decodeUInt 8 bytes
  let (outstanding, bytes) ← decodeUInt 8 bytes
  let (integerAmount, bytes) ← decodeUInt 8 bytes
  let (decimalAmount, bytes) ← decodeUInt 4 bytes
  let (indices, bytes) ← decodeUInt 8 bytes
  let (indices24, bytes) ← decodeUInt 8 bytes
  let (rebalance, bytes) ← Rebalance.decode bytes
  let (dailyPerformance, bytes) ← decodeUInt 8 bytes
  let (annualPerformance, bytes) ← decodeUInt 8 bytes
  let (monthlyPerformance, bytes) ← decodeUInt 8 bytes
  let (last12MonthsPerformance, bytes) ← decodeUInt 8 bytes
  let (t24HoursDailyPerformance, bytes) ← decodeUInt 8 bytes
  let (t24HoursAnnualPerformance, bytes) ← decodeUInt 8 bytes
  let (t24HoursMonthlyPerformance, bytes) ← decodeUInt 8 bytes
  let (last12Months24HoursPerformance, bytes) ← decodeUInt 8 bytes
  pure ({ benchmarkName, benchmarkDate, outstanding, integerAmount, decimalAmount, indices, indices24, rebalance, dailyPerformance, annualPerformance, monthlyPerformance, last12MonthsPerformance, t24HoursDailyPerformance, t24HoursAnnualPerformance, t24HoursMonthlyPerformance, last12Months24HoursPerformance }, bytes)

@[simp] theorem encode_length (message : BenchmarkMessage) : (encode message).length = 149 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, Rebalance.encode_length]

theorem encode_length_pos (message : BenchmarkMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BenchmarkMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Rebalance.decode_encode, some_bind]
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

end BenchmarkMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | eventsSystemMessage (message : EventsSystemMessage) -- 83
  | dollarBuySellMessage (message : DollarBuySellMessage) -- 114
  | shortSalesBalancesPerInstrumentMessage (message : ShortSalesBalancesPerInstrumentMessage) -- 115
  | capitalMarketMultiplesMessage (message : CapitalMarketMultiplesMessage) -- 116
  | benchmarkMessage (message : BenchmarkMessage) -- 120
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .eventsSystemMessage _ => 83
  | .dollarBuySellMessage _ => 114
  | .shortSalesBalancesPerInstrumentMessage _ => 115
  | .capitalMarketMultiplesMessage _ => 116
  | .benchmarkMessage _ => 120

def encode : Payload → List UInt8
  | .eventsSystemMessage message => EventsSystemMessage.encode message
  | .dollarBuySellMessage message => DollarBuySellMessage.encode message
  | .shortSalesBalancesPerInstrumentMessage message => ShortSalesBalancesPerInstrumentMessage.encode message
  | .capitalMarketMultiplesMessage message => CapitalMarketMultiplesMessage.encode message
  | .benchmarkMessage message => BenchmarkMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 149 := by
  cases message with
  | eventsSystemMessage inner =>
    simp only [encode, EventsSystemMessage.encode_length]
    omega
  | dollarBuySellMessage inner =>
    simp only [encode, DollarBuySellMessage.encode_length]
    omega
  | shortSalesBalancesPerInstrumentMessage inner =>
    simp only [encode, ShortSalesBalancesPerInstrumentMessage.encode_length]
    omega
  | capitalMarketMultiplesMessage inner =>
    simp only [encode, CapitalMarketMultiplesMessage.encode_length]
    omega
  | benchmarkMessage inner =>
    simp only [encode, BenchmarkMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 83 then (EventsSystemMessage.decode bytes).map fun (message, rest) => (.eventsSystemMessage message, rest)
  else if tag = 114 then (DollarBuySellMessage.decode bytes).map fun (message, rest) => (.dollarBuySellMessage message, rest)
  else if tag = 115 then (ShortSalesBalancesPerInstrumentMessage.decode bytes).map fun (message, rest) => (.shortSalesBalancesPerInstrumentMessage message, rest)
  else if tag = 116 then (CapitalMarketMultiplesMessage.decode bytes).map fun (message, rest) => (.capitalMarketMultiplesMessage message, rest)
  else if tag = 120 then (BenchmarkMessage.decode bytes).map fun (message, rest) => (.benchmarkMessage message, rest)
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
  encodeUInt 1 (Payload.tag message.payload)
    ++ (Payload.encode message.payload)

def decodeBody (bytes : List UInt8) : Option (MessageBlock × List UInt8) := do
  let (messageType, bytes) ← decodeUInt 1 bytes
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
  | eventsSystemMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, EventsSystemMessage.encode_length]
    omega
  | dollarBuySellMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, DollarBuySellMessage.encode_length]
    omega
  | shortSalesBalancesPerInstrumentMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ShortSalesBalancesPerInstrumentMessage.encode_length]
    omega
  | capitalMarketMultiplesMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, CapitalMarketMultiplesMessage.encode_length]
    omega
  | benchmarkMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, BenchmarkMessage.encode_length]
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

end Omi.BmvBmvmarketdataProduct21IntraV11
