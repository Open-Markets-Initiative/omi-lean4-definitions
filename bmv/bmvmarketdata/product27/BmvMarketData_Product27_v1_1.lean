import Wire

/-!
# Bolsa Mexicana de Valores Bmv Market Data Product 27 v1.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.

License: MIT No Attribution
-/

namespace Omi.BmvBmvmarketdataProduct27IntraV11

/-- Origin: one byte code -/
def Origin.codes : List UInt8 :=
  [0x4D, 0x49, 0x41]

inductive Origin where
  | bmv -- Bmv
  | biva -- Biva
  | both -- Both
  | unlisted (byte : { byte : UInt8 // byte ∉ Origin.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Origin

def toByte : Origin → UInt8
  | .bmv => 0x4D
  | .biva => 0x49
  | .both => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Origin :=
  if byte = 0x4D then .bmv
  else if byte = 0x49 then .biva
  else .both

def ofByte (byte : UInt8) : Origin :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Origin) : ofByte value.toByte = value := by
  cases value with
  | bmv => decide
  | biva => decide
  | both => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Origin) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Origin × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Origin) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Origin) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Origin) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Origin

/-- Reference: one byte code -/
def Reference.codes : List UInt8 :=
  [0x4E, 0x4A, 0x56, 0x20]

inductive Reference where
  | previous -- Previous
  | adjusted -- Adjusted
  | adjustedNominalValue -- Adjusted Nominal Value
  | withoutPrice -- Without Price
  | unlisted (byte : { byte : UInt8 // byte ∉ Reference.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Reference

def toByte : Reference → UInt8
  | .previous => 0x4E
  | .adjusted => 0x4A
  | .adjustedNominalValue => 0x56
  | .withoutPrice => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Reference :=
  if byte = 0x4E then .previous
  else if byte = 0x4A then .adjusted
  else if byte = 0x56 then .adjustedNominalValue
  else .withoutPrice

def ofByte (byte : UInt8) : Reference :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Reference) : ofByte value.toByte = value := by
  cases value with
  | previous => decide
  | adjusted => decide
  | adjustedNominalValue => decide
  | withoutPrice => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Reference) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Reference × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Reference) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Reference) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Reference) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Reference

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

/-- Trades Rate Price: one byte code -/
def TradesRatePrice.codes : List UInt8 :=
  [0x54, 0x50, 0x20]

inductive TradesRatePrice where
  | rate -- Rate
  | price -- Price
  | byDefault -- By Default
  | unlisted (byte : { byte : UInt8 // byte ∉ TradesRatePrice.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradesRatePrice

def toByte : TradesRatePrice → UInt8
  | .rate => 0x54
  | .price => 0x50
  | .byDefault => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradesRatePrice :=
  if byte = 0x54 then .rate
  else if byte = 0x50 then .price
  else .byDefault

def ofByte (byte : UInt8) : TradesRatePrice :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradesRatePrice) : ofByte value.toByte = value := by
  cases value with
  | rate => decide
  | price => decide
  | byDefault => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradesRatePrice) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradesRatePrice × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradesRatePrice) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TradesRatePrice) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TradesRatePrice) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradesRatePrice

/-- Code Of Event: one byte code -/
def CodeOfEvent.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x4A, 0x4B, 0x4D, 0x4E, 0x4F, 0x50, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57]

inductive CodeOfEvent where
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
  | unlisted (byte : { byte : UInt8 // byte ∉ CodeOfEvent.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CodeOfEvent

def toByte : CodeOfEvent → UInt8
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
def listed (byte : UInt8) : CodeOfEvent :=
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

def ofByte (byte : UInt8) : CodeOfEvent :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CodeOfEvent) : ofByte value.toByte = value := by
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

def encode (value : CodeOfEvent) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CodeOfEvent × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CodeOfEvent) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CodeOfEvent) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CodeOfEvent) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CodeOfEvent

/-- Price Type: one byte code -/
def PriceType.codes : List UInt8 :=
  [0x52, 0x43, 0x49, 0x56]

inductive PriceType where
  | reference -- Reference
  | closingPrice -- Closing Price
  | inav -- Inav
  | volumeWeightedAveragePrice -- Volume Weighted Average Price
  | unlisted (byte : { byte : UInt8 // byte ∉ PriceType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PriceType

def toByte : PriceType → UInt8
  | .reference => 0x52
  | .closingPrice => 0x43
  | .inav => 0x49
  | .volumeWeightedAveragePrice => 0x56
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PriceType :=
  if byte = 0x52 then .reference
  else if byte = 0x43 then .closingPrice
  else if byte = 0x49 then .inav
  else .volumeWeightedAveragePrice

def ofByte (byte : UInt8) : PriceType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PriceType) : ofByte value.toByte = value := by
  cases value with
  | reference => decide
  | closingPrice => decide
  | inav => decide
  | volumeWeightedAveragePrice => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PriceType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PriceType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PriceType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : PriceType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : PriceType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PriceType

/-- Status: one byte code -/
def Status.codes : List UInt8 :=
  [0x43, 0x41, 0x50, 0x45, 0x47, 0x54, 0x4E, 0x4B, 0x4D, 0x55, 0x4F, 0x56, 0x4C, 0x49, 0x42, 0x57, 0x58, 0x59, 0x52]

inductive Status where
  | bidsCancellation -- Bids Cancellation
  | openingBiddingSession -- Opening Bidding Session
  | preOpening -- Pre Opening
  | inAllotment -- In Allotment
  | assignedBiddingSession -- Assigned Bidding Session
  | endedBiddingSession -- Ended Bidding Session
  | ongoingTrading -- Ongoing Trading
  | biddingSessionDueToParametersBreaking -- Bidding Session Due To Parameters Breaking
  | ongoingBiddingSessionDueToOperationsCeasingForMoreThan20BusinessDays -- Ongoing Bidding Session Due To Operations Ceasing For More Than 20 Business Days
  | demergerBiddingSession -- Demerger Bidding Session
  | suspendedSeries -- Suspended Series
  | suspendedListing -- Suspended Listing
  | biddingSessionDueToBreach -- Bidding Session Due To Breach
  | withdrawalOfOrdersInAnOngoingBiddingSession -- Withdrawal Of Orders In An Ongoing Bidding Session
  | withdrawalOfOrdersInIntradayBiddingSession -- Withdrawal Of Orders In Intraday Bidding Session
  | awaitingNews -- Awaiting News
  | settlementBiddingSession -- Settlement Bidding Session
  | extraordinarySettlementBiddingSession -- Extraordinary Settlement Bidding Session
  | ckdesTotalBiddingSession -- Ckdes Total Bidding Session
  | unlisted (byte : { byte : UInt8 // byte ∉ Status.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Status

def toByte : Status → UInt8
  | .bidsCancellation => 0x43
  | .openingBiddingSession => 0x41
  | .preOpening => 0x50
  | .inAllotment => 0x45
  | .assignedBiddingSession => 0x47
  | .endedBiddingSession => 0x54
  | .ongoingTrading => 0x4E
  | .biddingSessionDueToParametersBreaking => 0x4B
  | .ongoingBiddingSessionDueToOperationsCeasingForMoreThan20BusinessDays => 0x4D
  | .demergerBiddingSession => 0x55
  | .suspendedSeries => 0x4F
  | .suspendedListing => 0x56
  | .biddingSessionDueToBreach => 0x4C
  | .withdrawalOfOrdersInAnOngoingBiddingSession => 0x49
  | .withdrawalOfOrdersInIntradayBiddingSession => 0x42
  | .awaitingNews => 0x57
  | .settlementBiddingSession => 0x58
  | .extraordinarySettlementBiddingSession => 0x59
  | .ckdesTotalBiddingSession => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Status :=
  if byte = 0x43 then .bidsCancellation
  else if byte = 0x41 then .openingBiddingSession
  else if byte = 0x50 then .preOpening
  else if byte = 0x45 then .inAllotment
  else if byte = 0x47 then .assignedBiddingSession
  else if byte = 0x54 then .endedBiddingSession
  else if byte = 0x4E then .ongoingTrading
  else if byte = 0x4B then .biddingSessionDueToParametersBreaking
  else if byte = 0x4D then .ongoingBiddingSessionDueToOperationsCeasingForMoreThan20BusinessDays
  else if byte = 0x55 then .demergerBiddingSession
  else if byte = 0x4F then .suspendedSeries
  else if byte = 0x56 then .suspendedListing
  else if byte = 0x4C then .biddingSessionDueToBreach
  else if byte = 0x49 then .withdrawalOfOrdersInAnOngoingBiddingSession
  else if byte = 0x42 then .withdrawalOfOrdersInIntradayBiddingSession
  else if byte = 0x57 then .awaitingNews
  else if byte = 0x58 then .settlementBiddingSession
  else if byte = 0x59 then .extraordinarySettlementBiddingSession
  else .ckdesTotalBiddingSession

def ofByte (byte : UInt8) : Status :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Status) : ofByte value.toByte = value := by
  cases value with
  | bidsCancellation => decide
  | openingBiddingSession => decide
  | preOpening => decide
  | inAllotment => decide
  | assignedBiddingSession => decide
  | endedBiddingSession => decide
  | ongoingTrading => decide
  | biddingSessionDueToParametersBreaking => decide
  | ongoingBiddingSessionDueToOperationsCeasingForMoreThan20BusinessDays => decide
  | demergerBiddingSession => decide
  | suspendedSeries => decide
  | suspendedListing => decide
  | biddingSessionDueToBreach => decide
  | withdrawalOfOrdersInAnOngoingBiddingSession => decide
  | withdrawalOfOrdersInIntradayBiddingSession => decide
  | awaitingNews => decide
  | settlementBiddingSession => decide
  | extraordinarySettlementBiddingSession => decide
  | ckdesTotalBiddingSession => decide
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

/-- Reason: one byte code -/
def Reason.codes : List UInt8 :=
  [0x4E, 0x48, 0x41, 0x42, 0x51, 0x53, 0x4D, 0x4F, 0x43, 0x49]

inductive Reason where
  | normalOperation -- Normal Operation
  | volatilityBiddingSession -- Volatility Bidding Session
  | startupOfTheVolatilityBiddingSession -- Startup Of The Volatility Bidding Session
  | endOfTheVolatilityBiddingSession -- End Of The Volatility Bidding Session
  | awaitingNews -- Awaiting News
  | staticPriceBandBreach -- Static Price Band Breach
  | suspensionDueToMarketsSurveillance -- Suspension Due To Markets Surveillance
  | suspensionFromTheMarketOfOrigin -- Suspension From The Market Of Origin
  | withoutCompliance -- Without Compliance
  | startupOfTheInterestNotice -- Startup Of The Interest Notice
  | unlisted (byte : { byte : UInt8 // byte ∉ Reason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Reason

def toByte : Reason → UInt8
  | .normalOperation => 0x4E
  | .volatilityBiddingSession => 0x48
  | .startupOfTheVolatilityBiddingSession => 0x41
  | .endOfTheVolatilityBiddingSession => 0x42
  | .awaitingNews => 0x51
  | .staticPriceBandBreach => 0x53
  | .suspensionDueToMarketsSurveillance => 0x4D
  | .suspensionFromTheMarketOfOrigin => 0x4F
  | .withoutCompliance => 0x43
  | .startupOfTheInterestNotice => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Reason :=
  if byte = 0x4E then .normalOperation
  else if byte = 0x48 then .volatilityBiddingSession
  else if byte = 0x41 then .startupOfTheVolatilityBiddingSession
  else if byte = 0x42 then .endOfTheVolatilityBiddingSession
  else if byte = 0x51 then .awaitingNews
  else if byte = 0x53 then .staticPriceBandBreach
  else if byte = 0x4D then .suspensionDueToMarketsSurveillance
  else if byte = 0x4F then .suspensionFromTheMarketOfOrigin
  else if byte = 0x43 then .withoutCompliance
  else .startupOfTheInterestNotice

def ofByte (byte : UInt8) : Reason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Reason) : ofByte value.toByte = value := by
  cases value with
  | normalOperation => decide
  | volatilityBiddingSession => decide
  | startupOfTheVolatilityBiddingSession => decide
  | endOfTheVolatilityBiddingSession => decide
  | awaitingNews => decide
  | staticPriceBandBreach => decide
  | suspensionDueToMarketsSurveillance => decide
  | suspensionFromTheMarketOfOrigin => decide
  | withoutCompliance => decide
  | startupOfTheInterestNotice => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Reason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Reason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Reason) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Reason) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Reason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Reason

/-- Type Of Warrant: one byte code -/
def TypeOfWarrant.codes : List UInt8 :=
  [0x43, 0x56]

inductive TypeOfWarrant where
  | purchase -- Purchase
  | sale -- Sale
  | unlisted (byte : { byte : UInt8 // byte ∉ TypeOfWarrant.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TypeOfWarrant

def toByte : TypeOfWarrant → UInt8
  | .purchase => 0x43
  | .sale => 0x56
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TypeOfWarrant :=
  if byte = 0x43 then .purchase
  else .sale

def ofByte (byte : UInt8) : TypeOfWarrant :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TypeOfWarrant) : ofByte value.toByte = value := by
  cases value with
  | purchase => decide
  | sale => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TypeOfWarrant) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TypeOfWarrant × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TypeOfWarrant) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TypeOfWarrant) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TypeOfWarrant) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TypeOfWarrant

/-- Marketability: one byte code -/
def Marketability.codes : List UInt8 :=
  [0x41, 0x4D, 0x42, 0x4E, 0x52, 0x20]

inductive Marketability where
  | high -- High
  | medium -- Medium
  | low -- Low
  | minimum -- Minimum
  | recentQuotation -- Recent Quotation
  | nullOrInapplicable -- Null Or Inapplicable
  | unlisted (byte : { byte : UInt8 // byte ∉ Marketability.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Marketability

def toByte : Marketability → UInt8
  | .high => 0x41
  | .medium => 0x4D
  | .low => 0x42
  | .minimum => 0x4E
  | .recentQuotation => 0x52
  | .nullOrInapplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Marketability :=
  if byte = 0x41 then .high
  else if byte = 0x4D then .medium
  else if byte = 0x42 then .low
  else if byte = 0x4E then .minimum
  else if byte = 0x52 then .recentQuotation
  else .nullOrInapplicable

def ofByte (byte : UInt8) : Marketability :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Marketability) : ofByte value.toByte = value := by
  cases value with
  | high => decide
  | medium => decide
  | low => decide
  | minimum => decide
  | recentQuotation => decide
  | nullOrInapplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Marketability) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Marketability × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Marketability) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Marketability) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Marketability) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Marketability

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

/-- Type Of Trading: one byte code -/
def TypeOfTrading.codes : List UInt8 :=
  [0x45, 0x43, 0x42, 0x44, 0x57]

inductive TypeOfTrading where
  | continuousElectronicTrading -- Continuous Electronic Trading
  | marketOnClose -- Market On Close
  | blockTrading -- Block Trading
  | debtTrading -- Debt Trading
  | warrantsTrading -- Warrants Trading
  | unlisted (byte : { byte : UInt8 // byte ∉ TypeOfTrading.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TypeOfTrading

def toByte : TypeOfTrading → UInt8
  | .continuousElectronicTrading => 0x45
  | .marketOnClose => 0x43
  | .blockTrading => 0x42
  | .debtTrading => 0x44
  | .warrantsTrading => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TypeOfTrading :=
  if byte = 0x45 then .continuousElectronicTrading
  else if byte = 0x43 then .marketOnClose
  else if byte = 0x42 then .blockTrading
  else if byte = 0x44 then .debtTrading
  else .warrantsTrading

def ofByte (byte : UInt8) : TypeOfTrading :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TypeOfTrading) : ofByte value.toByte = value := by
  cases value with
  | continuousElectronicTrading => decide
  | marketOnClose => decide
  | blockTrading => decide
  | debtTrading => decide
  | warrantsTrading => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TypeOfTrading) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TypeOfTrading × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TypeOfTrading) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TypeOfTrading) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TypeOfTrading) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TypeOfTrading

/-- Type Of Agreement: one byte code -/
def TypeOfAgreement.codes : List UInt8 :=
  [0x43, 0x4F, 0x48, 0x44, 0x4D, 0x50, 0x58, 0x76, 0x77, 0x25, 0x78, 0x79, 0x41, 0x42, 0x45, 0x46, 0x47, 0x4A, 0x4B, 0x4C, 0x4E, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57, 0x59, 0x5A, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x6A, 0x6B, 0x6C, 0x6D, 0x6E, 0x6F, 0x70, 0x71, 0x72, 0x73, 0x74, 0x75, 0x7A, 0x23, 0x49, 0x2B, 0x26, 0x28, 0x29]

inductive TypeOfAgreement where
  | crossingOperation -- Crossing Operation
  | orderClosing -- Order Closing
  | operationAtClosingPrice -- Operation At Closing Price
  | operationAfterClosing -- Operation After Closing
  | operationAtMediumPrice -- Operation At Medium Price
  | operationAtAveragePriceForTheDay -- Operation At Average Price For The Day
  | blockOperationsByException -- Block Operations By Exception
  | vwapOperationsByException -- Vwap Operations By Exception
  | twapOperationsByException -- Twap Operations By Exception
  | basketTrading -- Basket Trading
  | otcRecentOperations -- Otc Recent Operations
  | otcAgreedOperations -- Otc Agreed Operations
  | buyAutoEntry -- Buy Auto Entry
  | sellAutoEntry -- Sell Auto Entry
  | blockTrade -- Block Trade
  | legOfBlocktradeForChainOfForwards -- Leg Of Blocktrade For Chain Of Forwards
  | legOfChainOfForwards -- Leg Of Chain Of Forwards
  | legOfCrossingOfForeignCurrencyStrategy -- Leg Of Crossing Of Foreign Currency Strategy
  | sellLegAutoEntryOfForeignCurrencyStrategy -- Sell Leg Auto Entry Of Foreign Currency Strategy
  | buyLegAutoEntryOfForeignCurrencyStrategy -- Buy Leg Auto Entry Of Foreign Currency Strategy
  | legOfForeignCurrencyStrategy -- Leg Of Foreign Currency Strategy
  | legOfForeignCurrencyStrategy_51 -- Leg Of Foreign Currency Strategy
  | legOfCrossingOfChainOfForwards -- Leg Of Crossing Of Chain Of Forwards
  | sellLegAutoEntryOfChainOfForwards -- Sell Leg Auto Entry Of Chain Of Forwards
  | buyLegAutoEntryOfChainOfForwards -- Buy Leg Auto Entry Of Chain Of Forwards
  | legOfAuctionOfChainOfForwards -- Leg Of Auction Of Chain Of Forwards
  | legOfRoundOfChainOfForwards -- Leg Of Round Of Chain Of Forwards
  | chainsOfForwards -- Chains Of Forwards
  | legOfRolloverCrossing -- Leg Of Rollover Crossing
  | sellLegAutoEntryOfRollover -- Sell Leg Auto Entry Of Rollover
  | buyLegAutoEntryOfRollover -- Buy Leg Auto Entry Of Rollover
  | legOfRoundOfRollover -- Leg Of Round Of Rollover
  | depthOfRoundOfChainOfForwards -- Depth Of Round Of Chain Of Forwards
  | tradingOfChainOfForwards -- Trading Of Chain Of Forwards
  | depthOfRound -- Depth Of Round
  | roundOfChainOfForwards -- Round Of Chain Of Forwards
  | rolloverSentra -- Rollover Sentra
  | typeRound -- Type Round
  | auctions -- Auctions
  | legOfBlockTradeOfRollover -- Leg Of Block Trade Of Rollover
  | legOfBlockTradeOfForeignCurrencyStrategy -- Leg Of Block Trade Of Foreign Currency Strategy
  | blockTradeOfForeignCurrencyStrategy -- Block Trade Of Foreign Currency Strategy
  | blockTradeOfChainOfForwards -- Block Trade Of Chain Of Forwards
  | blocktradeOfRollover -- Blocktrade Of Rollover
  | crossingOfChainOfForwards -- Crossing Of Chain Of Forwards
  | sellAutoEntryOfChainOfForwards -- Sell Auto Entry Of Chain Of Forwards
  | buyAutoEntryOfChainOfForwards -- Buy Auto Entry Of Chain Of Forwards
  | swapBlockTrade -- Swap Block Trade
  | swapBlockTradeWithContinuousCoupon -- Swap Block Trade With Continuous Coupon
  | blockTradeOfUnwind -- Block Trade Of Unwind
  | blockTradeOfSubstitution -- Block Trade Of Substitution
  | voiceOver -- Voice Over
  | firmOrder -- Firm Order
  | ipoCross -- Ipo Cross
  | unintentionalSelfCross -- Unintentional Self Cross
  | withoutConcertation -- Without Concertation
  | inavToClosingPriceTrading -- Inav To Closing Price Trading
  | inavAfterClosing -- Inav After Closing
  | unlisted (byte : { byte : UInt8 // byte ∉ TypeOfAgreement.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TypeOfAgreement

def toByte : TypeOfAgreement → UInt8
  | .crossingOperation => 0x43
  | .orderClosing => 0x4F
  | .operationAtClosingPrice => 0x48
  | .operationAfterClosing => 0x44
  | .operationAtMediumPrice => 0x4D
  | .operationAtAveragePriceForTheDay => 0x50
  | .blockOperationsByException => 0x58
  | .vwapOperationsByException => 0x76
  | .twapOperationsByException => 0x77
  | .basketTrading => 0x25
  | .otcRecentOperations => 0x78
  | .otcAgreedOperations => 0x79
  | .buyAutoEntry => 0x41
  | .sellAutoEntry => 0x42
  | .blockTrade => 0x45
  | .legOfBlocktradeForChainOfForwards => 0x46
  | .legOfChainOfForwards => 0x47
  | .legOfCrossingOfForeignCurrencyStrategy => 0x4A
  | .sellLegAutoEntryOfForeignCurrencyStrategy => 0x4B
  | .buyLegAutoEntryOfForeignCurrencyStrategy => 0x4C
  | .legOfForeignCurrencyStrategy => 0x4E
  | .legOfForeignCurrencyStrategy_51 => 0x51
  | .legOfCrossingOfChainOfForwards => 0x52
  | .sellLegAutoEntryOfChainOfForwards => 0x53
  | .buyLegAutoEntryOfChainOfForwards => 0x54
  | .legOfAuctionOfChainOfForwards => 0x55
  | .legOfRoundOfChainOfForwards => 0x56
  | .chainsOfForwards => 0x57
  | .legOfRolloverCrossing => 0x59
  | .sellLegAutoEntryOfRollover => 0x5A
  | .buyLegAutoEntryOfRollover => 0x61
  | .legOfRoundOfRollover => 0x62
  | .depthOfRoundOfChainOfForwards => 0x63
  | .tradingOfChainOfForwards => 0x64
  | .depthOfRound => 0x65
  | .roundOfChainOfForwards => 0x66
  | .rolloverSentra => 0x67
  | .typeRound => 0x68
  | .auctions => 0x69
  | .legOfBlockTradeOfRollover => 0x6A
  | .legOfBlockTradeOfForeignCurrencyStrategy => 0x6B
  | .blockTradeOfForeignCurrencyStrategy => 0x6C
  | .blockTradeOfChainOfForwards => 0x6D
  | .blocktradeOfRollover => 0x6E
  | .crossingOfChainOfForwards => 0x6F
  | .sellAutoEntryOfChainOfForwards => 0x70
  | .buyAutoEntryOfChainOfForwards => 0x71
  | .swapBlockTrade => 0x72
  | .swapBlockTradeWithContinuousCoupon => 0x73
  | .blockTradeOfUnwind => 0x74
  | .blockTradeOfSubstitution => 0x75
  | .voiceOver => 0x7A
  | .firmOrder => 0x23
  | .ipoCross => 0x49
  | .unintentionalSelfCross => 0x2B
  | .withoutConcertation => 0x26
  | .inavToClosingPriceTrading => 0x28
  | .inavAfterClosing => 0x29
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TypeOfAgreement :=
  if byte = 0x43 then .crossingOperation
  else if byte = 0x4F then .orderClosing
  else if byte = 0x48 then .operationAtClosingPrice
  else if byte = 0x44 then .operationAfterClosing
  else if byte = 0x4D then .operationAtMediumPrice
  else if byte = 0x50 then .operationAtAveragePriceForTheDay
  else if byte = 0x58 then .blockOperationsByException
  else if byte = 0x76 then .vwapOperationsByException
  else if byte = 0x77 then .twapOperationsByException
  else if byte = 0x25 then .basketTrading
  else if byte = 0x78 then .otcRecentOperations
  else if byte = 0x79 then .otcAgreedOperations
  else if byte = 0x41 then .buyAutoEntry
  else if byte = 0x42 then .sellAutoEntry
  else if byte = 0x45 then .blockTrade
  else if byte = 0x46 then .legOfBlocktradeForChainOfForwards
  else if byte = 0x47 then .legOfChainOfForwards
  else if byte = 0x4A then .legOfCrossingOfForeignCurrencyStrategy
  else if byte = 0x4B then .sellLegAutoEntryOfForeignCurrencyStrategy
  else if byte = 0x4C then .buyLegAutoEntryOfForeignCurrencyStrategy
  else if byte = 0x4E then .legOfForeignCurrencyStrategy
  else if byte = 0x51 then .legOfForeignCurrencyStrategy_51
  else if byte = 0x52 then .legOfCrossingOfChainOfForwards
  else if byte = 0x53 then .sellLegAutoEntryOfChainOfForwards
  else if byte = 0x54 then .buyLegAutoEntryOfChainOfForwards
  else if byte = 0x55 then .legOfAuctionOfChainOfForwards
  else if byte = 0x56 then .legOfRoundOfChainOfForwards
  else if byte = 0x57 then .chainsOfForwards
  else if byte = 0x59 then .legOfRolloverCrossing
  else if byte = 0x5A then .sellLegAutoEntryOfRollover
  else if byte = 0x61 then .buyLegAutoEntryOfRollover
  else if byte = 0x62 then .legOfRoundOfRollover
  else if byte = 0x63 then .depthOfRoundOfChainOfForwards
  else if byte = 0x64 then .tradingOfChainOfForwards
  else if byte = 0x65 then .depthOfRound
  else if byte = 0x66 then .roundOfChainOfForwards
  else if byte = 0x67 then .rolloverSentra
  else if byte = 0x68 then .typeRound
  else if byte = 0x69 then .auctions
  else if byte = 0x6A then .legOfBlockTradeOfRollover
  else if byte = 0x6B then .legOfBlockTradeOfForeignCurrencyStrategy
  else if byte = 0x6C then .blockTradeOfForeignCurrencyStrategy
  else if byte = 0x6D then .blockTradeOfChainOfForwards
  else if byte = 0x6E then .blocktradeOfRollover
  else if byte = 0x6F then .crossingOfChainOfForwards
  else if byte = 0x70 then .sellAutoEntryOfChainOfForwards
  else if byte = 0x71 then .buyAutoEntryOfChainOfForwards
  else if byte = 0x72 then .swapBlockTrade
  else if byte = 0x73 then .swapBlockTradeWithContinuousCoupon
  else if byte = 0x74 then .blockTradeOfUnwind
  else if byte = 0x75 then .blockTradeOfSubstitution
  else if byte = 0x7A then .voiceOver
  else if byte = 0x23 then .firmOrder
  else if byte = 0x49 then .ipoCross
  else if byte = 0x2B then .unintentionalSelfCross
  else if byte = 0x26 then .withoutConcertation
  else if byte = 0x28 then .inavToClosingPriceTrading
  else .inavAfterClosing

def ofByte (byte : UInt8) : TypeOfAgreement :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TypeOfAgreement) : ofByte value.toByte = value := by
  cases value with
  | crossingOperation => decide
  | orderClosing => decide
  | operationAtClosingPrice => decide
  | operationAfterClosing => decide
  | operationAtMediumPrice => decide
  | operationAtAveragePriceForTheDay => decide
  | blockOperationsByException => decide
  | vwapOperationsByException => decide
  | twapOperationsByException => decide
  | basketTrading => decide
  | otcRecentOperations => decide
  | otcAgreedOperations => decide
  | buyAutoEntry => decide
  | sellAutoEntry => decide
  | blockTrade => decide
  | legOfBlocktradeForChainOfForwards => decide
  | legOfChainOfForwards => decide
  | legOfCrossingOfForeignCurrencyStrategy => decide
  | sellLegAutoEntryOfForeignCurrencyStrategy => decide
  | buyLegAutoEntryOfForeignCurrencyStrategy => decide
  | legOfForeignCurrencyStrategy => decide
  | legOfForeignCurrencyStrategy_51 => decide
  | legOfCrossingOfChainOfForwards => decide
  | sellLegAutoEntryOfChainOfForwards => decide
  | buyLegAutoEntryOfChainOfForwards => decide
  | legOfAuctionOfChainOfForwards => decide
  | legOfRoundOfChainOfForwards => decide
  | chainsOfForwards => decide
  | legOfRolloverCrossing => decide
  | sellLegAutoEntryOfRollover => decide
  | buyLegAutoEntryOfRollover => decide
  | legOfRoundOfRollover => decide
  | depthOfRoundOfChainOfForwards => decide
  | tradingOfChainOfForwards => decide
  | depthOfRound => decide
  | roundOfChainOfForwards => decide
  | rolloverSentra => decide
  | typeRound => decide
  | auctions => decide
  | legOfBlockTradeOfRollover => decide
  | legOfBlockTradeOfForeignCurrencyStrategy => decide
  | blockTradeOfForeignCurrencyStrategy => decide
  | blockTradeOfChainOfForwards => decide
  | blocktradeOfRollover => decide
  | crossingOfChainOfForwards => decide
  | sellAutoEntryOfChainOfForwards => decide
  | buyAutoEntryOfChainOfForwards => decide
  | swapBlockTrade => decide
  | swapBlockTradeWithContinuousCoupon => decide
  | blockTradeOfUnwind => decide
  | blockTradeOfSubstitution => decide
  | voiceOver => decide
  | firmOrder => decide
  | ipoCross => decide
  | unintentionalSelfCross => decide
  | withoutConcertation => decide
  | inavToClosingPriceTrading => decide
  | inavAfterClosing => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TypeOfAgreement) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TypeOfAgreement × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TypeOfAgreement) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TypeOfAgreement) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TypeOfAgreement) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TypeOfAgreement

/-- Settlement: one byte code -/
def Settlement.codes : List UInt8 :=
  [0x4D, 0x32, 0x34, 0x37, 0x39, 0x31]

inductive Settlement where
  | sameDay -- Same Day
  | twentyFourHours -- Twenty Four Hours
  | fortyEightHours -- Forty Eight Hours
  | seventyTwoHours -- Seventy Two Hours
  | ninetySixHours -- Ninety Six Hours
  | oneHundredTwentyHours -- One Hundred Twenty Hours
  | unlisted (byte : { byte : UInt8 // byte ∉ Settlement.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Settlement

def toByte : Settlement → UInt8
  | .sameDay => 0x4D
  | .twentyFourHours => 0x32
  | .fortyEightHours => 0x34
  | .seventyTwoHours => 0x37
  | .ninetySixHours => 0x39
  | .oneHundredTwentyHours => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Settlement :=
  if byte = 0x4D then .sameDay
  else if byte = 0x32 then .twentyFourHours
  else if byte = 0x34 then .fortyEightHours
  else if byte = 0x37 then .seventyTwoHours
  else if byte = 0x39 then .ninetySixHours
  else .oneHundredTwentyHours

def ofByte (byte : UInt8) : Settlement :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Settlement) : ofByte value.toByte = value := by
  cases value with
  | sameDay => decide
  | twentyFourHours => decide
  | fortyEightHours => decide
  | seventyTwoHours => decide
  | ninetySixHours => decide
  | oneHundredTwentyHours => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Settlement) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Settlement × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Settlement) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Settlement) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Settlement) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Settlement

/-- Auction Indicator: one byte code -/
def AuctionIndicator.codes : List UInt8 :=
  [0x50, 0x53, 0x20, 0x4E]

inductive AuctionIndicator where
  | openingAuction -- Opening Auction
  | otherAuctions -- Other Auctions
  | continuousMarket -- Continuous Market
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ AuctionIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AuctionIndicator

def toByte : AuctionIndicator → UInt8
  | .openingAuction => 0x50
  | .otherAuctions => 0x53
  | .continuousMarket => 0x20
  | .notApplicable => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AuctionIndicator :=
  if byte = 0x50 then .openingAuction
  else if byte = 0x53 then .otherAuctions
  else if byte = 0x20 then .continuousMarket
  else .notApplicable

def ofByte (byte : UInt8) : AuctionIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AuctionIndicator) : ofByte value.toByte = value := by
  cases value with
  | openingAuction => decide
  | otherAuctions => decide
  | continuousMarket => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AuctionIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AuctionIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AuctionIndicator) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : AuctionIndicator) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : AuctionIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AuctionIndicator

/-- Indicator: one byte code -/
def Indicator.codes : List UInt8 :=
  [0x4E, 0x59]

inductive Indicator where
  | no -- No
  | yes -- Yes
  | unlisted (byte : { byte : UInt8 // byte ∉ Indicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Indicator

def toByte : Indicator → UInt8
  | .no => 0x4E
  | .yes => 0x59
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Indicator :=
  if byte = 0x4E then .no
  else .yes

def ofByte (byte : UInt8) : Indicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Indicator) : ofByte value.toByte = value := by
  cases value with
  | no => decide
  | yes => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Indicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Indicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Indicator) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Indicator) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Indicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Indicator

/-- Type Of Cross Trading: one byte code -/
def TypeOfCrossTrading.codes : List UInt8 :=
  [0x4F, 0x49]

inductive TypeOfCrossTrading where
  | preOpening -- Pre Opening
  | intradayAuction -- Intraday Auction
  | unlisted (byte : { byte : UInt8 // byte ∉ TypeOfCrossTrading.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TypeOfCrossTrading

def toByte : TypeOfCrossTrading → UInt8
  | .preOpening => 0x4F
  | .intradayAuction => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TypeOfCrossTrading :=
  if byte = 0x4F then .preOpening
  else .intradayAuction

def ofByte (byte : UInt8) : TypeOfCrossTrading :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TypeOfCrossTrading) : ofByte value.toByte = value := by
  cases value with
  | preOpening => decide
  | intradayAuction => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TypeOfCrossTrading) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TypeOfCrossTrading × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TypeOfCrossTrading) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TypeOfCrossTrading) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TypeOfCrossTrading) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TypeOfCrossTrading

/-- Direction: one byte code -/
def Direction.codes : List UInt8 :=
  [0x43, 0x56]

inductive Direction where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ Direction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Direction

def toByte : Direction → UInt8
  | .buy => 0x43
  | .sell => 0x56
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Direction :=
  if byte = 0x43 then .buy
  else .sell

def ofByte (byte : UInt8) : Direction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Direction) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Direction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Direction × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Direction) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Direction) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Direction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Direction

/-- Mutual Funds Trades Message: 53 bytes -/
structure MutualFundsTradesMessage where
  instrumentNumber : BitVec 32
  origin : Origin
  dateOfTheTrade : BitVec 64
  price : BitVec 64
  bookValue : BitVec 64
  numberOfSalesTrades : BitVec 32
  salesVolume : BitVec 64
  numberOfPurchaseTrades : BitVec 32
  purchaseVolume : BitVec 64
  deriving DecidableEq, Repr

namespace MutualFundsTradesMessage

def encode (message : MutualFundsTradesMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (Origin.encode message.origin
    ++ (encodeUInt 8 message.dateOfTheTrade
    ++ (encodeUInt 8 message.price
    ++ (encodeUInt 8 message.bookValue
    ++ (encodeUInt 4 message.numberOfSalesTrades
    ++ (encodeUInt 8 message.salesVolume
    ++ (encodeUInt 4 message.numberOfPurchaseTrades
    ++ (encodeUInt 8 message.purchaseVolume))))))))

def decode (bytes : List UInt8) : Option (MutualFundsTradesMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (origin, bytes) ← Origin.decode bytes
  let (dateOfTheTrade, bytes) ← decodeUInt 8 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (bookValue, bytes) ← decodeUInt 8 bytes
  let (numberOfSalesTrades, bytes) ← decodeUInt 4 bytes
  let (salesVolume, bytes) ← decodeUInt 8 bytes
  let (numberOfPurchaseTrades, bytes) ← decodeUInt 4 bytes
  let (purchaseVolume, bytes) ← decodeUInt 8 bytes
  pure ({ instrumentNumber, origin, dateOfTheTrade, price, bookValue, numberOfSalesTrades, salesVolume, numberOfPurchaseTrades, purchaseVolume }, bytes)

@[simp] theorem encode_length (message : MutualFundsTradesMessage) : (encode message).length = 53 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Origin.encode_length]

theorem encode_length_pos (message : MutualFundsTradesMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MutualFundsTradesMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Origin.decode_encode, some_bind]
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

end MutualFundsTradesMessage

/-- Opening Of Continuous Auctions Message: 21 bytes -/
structure OpeningOfContinuousAuctionsMessage where
  instrumentNumber : BitVec 32
  origin : Origin
  auctionSessionStartupTime : BitVec 64
  auctionSessionEndTime : BitVec 64
  deriving DecidableEq, Repr

namespace OpeningOfContinuousAuctionsMessage

def encode (message : OpeningOfContinuousAuctionsMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (Origin.encode message.origin
    ++ (encodeUInt 8 message.auctionSessionStartupTime
    ++ (encodeUInt 8 message.auctionSessionEndTime)))

def decode (bytes : List UInt8) : Option (OpeningOfContinuousAuctionsMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (origin, bytes) ← Origin.decode bytes
  let (auctionSessionStartupTime, bytes) ← decodeUInt 8 bytes
  let (auctionSessionEndTime, bytes) ← decodeUInt 8 bytes
  pure ({ instrumentNumber, origin, auctionSessionStartupTime, auctionSessionEndTime }, bytes)

@[simp] theorem encode_length (message : OpeningOfContinuousAuctionsMessage) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Origin.encode_length]

theorem encode_length_pos (message : OpeningOfContinuousAuctionsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OpeningOfContinuousAuctionsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Origin.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OpeningOfContinuousAuctionsMessage

/-- Existence Of Bids At Mid Price Message: 6 bytes -/
structure ExistenceOfBidsAtMidPriceMessage where
  instrumentNumber : BitVec 32
  origin : Origin
  bidsExisting : Alpha 1
  deriving DecidableEq, Repr

namespace ExistenceOfBidsAtMidPriceMessage

def encode (message : ExistenceOfBidsAtMidPriceMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (Origin.encode message.origin
    ++ (Alpha.encode message.bidsExisting))

def decode (bytes : List UInt8) : Option (ExistenceOfBidsAtMidPriceMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (origin, bytes) ← Origin.decode bytes
  let (bidsExisting, bytes) ← Alpha.decode 1 bytes
  pure ({ instrumentNumber, origin, bidsExisting }, bytes)

@[simp] theorem encode_length (message : ExistenceOfBidsAtMidPriceMessage) : (encode message).length = 6 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Origin.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : ExistenceOfBidsAtMidPriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExistenceOfBidsAtMidPriceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Origin.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ExistenceOfBidsAtMidPriceMessage

/-- Catalogue Of Debt And Metals Instruments Message: 103 bytes -/
structure CatalogueOfDebtAndMetalsInstrumentsMessage where
  numberOfTheInstrument : BitVec 32
  origin : Origin
  typeOfValue : Alpha 2
  issuingCompany : Alpha 7
  issuance : Alpha 6
  dateOfIssuance : BitVec 64
  dateOfMaturity : BitVec 64
  priceRateOfReference : BitVec 64
  dateOfReference : BitVec 64
  reference : Reference
  termDays : BitVec 16
  couponPeriod : BitVec 16
  isin : Alpha 12
  market : Market
  currentNominalValue : BitVec 64
  originalNominalValue : BitVec 64
  outstandingShares : BitVec 64
  amountPlaced : BitVec 64
  tradesRatePrice : TradesRatePrice
  deriving DecidableEq, Repr

namespace CatalogueOfDebtAndMetalsInstrumentsMessage

def encode (message : CatalogueOfDebtAndMetalsInstrumentsMessage) : List UInt8 :=
  encodeUInt 4 message.numberOfTheInstrument
    ++ (Origin.encode message.origin
    ++ (Alpha.encode message.typeOfValue
    ++ (Alpha.encode message.issuingCompany
    ++ (Alpha.encode message.issuance
    ++ (encodeUInt 8 message.dateOfIssuance
    ++ (encodeUInt 8 message.dateOfMaturity
    ++ (encodeUInt 8 message.priceRateOfReference
    ++ (encodeUInt 8 message.dateOfReference
    ++ (Reference.encode message.reference
    ++ (encodeUInt 2 message.termDays
    ++ (encodeUInt 2 message.couponPeriod
    ++ (Alpha.encode message.isin
    ++ (Market.encode message.market
    ++ (encodeUInt 8 message.currentNominalValue
    ++ (encodeUInt 8 message.originalNominalValue
    ++ (encodeUInt 8 message.outstandingShares
    ++ (encodeUInt 8 message.amountPlaced
    ++ (TradesRatePrice.encode message.tradesRatePrice))))))))))))))))))

def decode (bytes : List UInt8) : Option (CatalogueOfDebtAndMetalsInstrumentsMessage × List UInt8) := do
  let (numberOfTheInstrument, bytes) ← decodeUInt 4 bytes
  let (origin, bytes) ← Origin.decode bytes
  let (typeOfValue, bytes) ← Alpha.decode 2 bytes
  let (issuingCompany, bytes) ← Alpha.decode 7 bytes
  let (issuance, bytes) ← Alpha.decode 6 bytes
  let (dateOfIssuance, bytes) ← decodeUInt 8 bytes
  let (dateOfMaturity, bytes) ← decodeUInt 8 bytes
  let (priceRateOfReference, bytes) ← decodeUInt 8 bytes
  let (dateOfReference, bytes) ← decodeUInt 8 bytes
  let (reference, bytes) ← Reference.decode bytes
  let (termDays, bytes) ← decodeUInt 2 bytes
  let (couponPeriod, bytes) ← decodeUInt 2 bytes
  let (isin, bytes) ← Alpha.decode 12 bytes
  let (market, bytes) ← Market.decode bytes
  let (currentNominalValue, bytes) ← decodeUInt 8 bytes
  let (originalNominalValue, bytes) ← decodeUInt 8 bytes
  let (outstandingShares, bytes) ← decodeUInt 8 bytes
  let (amountPlaced, bytes) ← decodeUInt 8 bytes
  let (tradesRatePrice, bytes) ← TradesRatePrice.decode bytes
  pure ({ numberOfTheInstrument, origin, typeOfValue, issuingCompany, issuance, dateOfIssuance, dateOfMaturity, priceRateOfReference, dateOfReference, reference, termDays, couponPeriod, isin, market, currentNominalValue, originalNominalValue, outstandingShares, amountPlaced, tradesRatePrice }, bytes)

@[simp] theorem encode_length (message : CatalogueOfDebtAndMetalsInstrumentsMessage) : (encode message).length = 103 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Origin.encode_length, Alpha.encode_length, Reference.encode_length, Market.encode_length, TradesRatePrice.encode_length]

theorem encode_length_pos (message : CatalogueOfDebtAndMetalsInstrumentsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CatalogueOfDebtAndMetalsInstrumentsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Origin.decode_encode, some_bind]
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
  rw [List.append_assoc, Reference.decode_encode, some_bind]
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
  rw [TradesRatePrice.decode_encode, some_bind]
  rfl

end CatalogueOfDebtAndMetalsInstrumentsMessage

/-- Catalog Sent For Instruments Belonging To Mutual Funds Message: 78 bytes -/
structure CatalogSentForInstrumentsBelongingToMutualFundsMessage where
  numberOfTheInstrument : BitVec 32
  origin : Origin
  typeOfValue : Alpha 2
  issuingCompany : Alpha 7
  series : Alpha 6
  sector : BitVec 8
  subSector : BitVec 8
  industry : BitVec 8
  subIndustry : BitVec 8
  tradingCompany : Alpha 10
  referencePrice : BitVec 64
  referenceDate : BitVec 64
  reference : Reference
  isin : Alpha 12
  rating : Alpha 15
  deriving DecidableEq, Repr

namespace CatalogSentForInstrumentsBelongingToMutualFundsMessage

def encode (message : CatalogSentForInstrumentsBelongingToMutualFundsMessage) : List UInt8 :=
  encodeUInt 4 message.numberOfTheInstrument
    ++ (Origin.encode message.origin
    ++ (Alpha.encode message.typeOfValue
    ++ (Alpha.encode message.issuingCompany
    ++ (Alpha.encode message.series
    ++ (encodeUInt 1 message.sector
    ++ (encodeUInt 1 message.subSector
    ++ (encodeUInt 1 message.industry
    ++ (encodeUInt 1 message.subIndustry
    ++ (Alpha.encode message.tradingCompany
    ++ (encodeUInt 8 message.referencePrice
    ++ (encodeUInt 8 message.referenceDate
    ++ (Reference.encode message.reference
    ++ (Alpha.encode message.isin
    ++ (Alpha.encode message.rating))))))))))))))

def decode (bytes : List UInt8) : Option (CatalogSentForInstrumentsBelongingToMutualFundsMessage × List UInt8) := do
  let (numberOfTheInstrument, bytes) ← decodeUInt 4 bytes
  let (origin, bytes) ← Origin.decode bytes
  let (typeOfValue, bytes) ← Alpha.decode 2 bytes
  let (issuingCompany, bytes) ← Alpha.decode 7 bytes
  let (series, bytes) ← Alpha.decode 6 bytes
  let (sector, bytes) ← decodeUInt 1 bytes
  let (subSector, bytes) ← decodeUInt 1 bytes
  let (industry, bytes) ← decodeUInt 1 bytes
  let (subIndustry, bytes) ← decodeUInt 1 bytes
  let (tradingCompany, bytes) ← Alpha.decode 10 bytes
  let (referencePrice, bytes) ← decodeUInt 8 bytes
  let (referenceDate, bytes) ← decodeUInt 8 bytes
  let (reference, bytes) ← Reference.decode bytes
  let (isin, bytes) ← Alpha.decode 12 bytes
  let (rating, bytes) ← Alpha.decode 15 bytes
  pure ({ numberOfTheInstrument, origin, typeOfValue, issuingCompany, series, sector, subSector, industry, subIndustry, tradingCompany, referencePrice, referenceDate, reference, isin, rating }, bytes)

@[simp] theorem encode_length (message : CatalogSentForInstrumentsBelongingToMutualFundsMessage) : (encode message).length = 78 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Origin.encode_length, Alpha.encode_length, Reference.encode_length]

theorem encode_length_pos (message : CatalogSentForInstrumentsBelongingToMutualFundsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CatalogSentForInstrumentsBelongingToMutualFundsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Origin.decode_encode, some_bind]
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
  rw [List.append_assoc, Reference.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end CatalogSentForInstrumentsBelongingToMutualFundsMessage

/-- Weighted Average Price Message: 21 bytes -/
structure WeightedAveragePriceMessage where
  instrumentNumber : BitVec 32
  origin : Origin
  weightedAveragePrice : BitVec 64
  volatility : BitVec 64
  deriving DecidableEq, Repr

namespace WeightedAveragePriceMessage

def encode (message : WeightedAveragePriceMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (Origin.encode message.origin
    ++ (encodeUInt 8 message.weightedAveragePrice
    ++ (encodeUInt 8 message.volatility)))

def decode (bytes : List UInt8) : Option (WeightedAveragePriceMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (origin, bytes) ← Origin.decode bytes
  let (weightedAveragePrice, bytes) ← decodeUInt 8 bytes
  let (volatility, bytes) ← decodeUInt 8 bytes
  pure ({ instrumentNumber, origin, weightedAveragePrice, volatility }, bytes)

@[simp] theorem encode_length (message : WeightedAveragePriceMessage) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Origin.encode_length]

theorem encode_length_pos (message : WeightedAveragePriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : WeightedAveragePriceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Origin.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end WeightedAveragePriceMessage

/-- System Events Message: 31 bytes -/
structure SystemEventsMessage where
  instrumentNumber : BitVec 32
  origin : Origin
  codeOfEvent : CodeOfEvent
  market : Market
  sendTime : BitVec 64
  endTime : BitVec 64
  group : Alpha 8
  deriving DecidableEq, Repr

namespace SystemEventsMessage

def encode (message : SystemEventsMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (Origin.encode message.origin
    ++ (CodeOfEvent.encode message.codeOfEvent
    ++ (Market.encode message.market
    ++ (encodeUInt 8 message.sendTime
    ++ (encodeUInt 8 message.endTime
    ++ (Alpha.encode message.group))))))

def decode (bytes : List UInt8) : Option (SystemEventsMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (origin, bytes) ← Origin.decode bytes
  let (codeOfEvent, bytes) ← CodeOfEvent.decode bytes
  let (market, bytes) ← Market.decode bytes
  let (sendTime, bytes) ← decodeUInt 8 bytes
  let (endTime, bytes) ← decodeUInt 8 bytes
  let (group, bytes) ← Alpha.decode 8 bytes
  pure ({ instrumentNumber, origin, codeOfEvent, market, sendTime, endTime, group }, bytes)

@[simp] theorem encode_length (message : SystemEventsMessage) : (encode message).length = 31 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Origin.encode_length, CodeOfEvent.encode_length, Market.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : SystemEventsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemEventsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Origin.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CodeOfEvent.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Market.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SystemEventsMessage

/-- Reference Price Message: 14 bytes -/
structure ReferencePriceMessage where
  instrumentNumber : BitVec 32
  origin : Origin
  price : BitVec 64
  priceType : PriceType
  deriving DecidableEq, Repr

namespace ReferencePriceMessage

def encode (message : ReferencePriceMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (Origin.encode message.origin
    ++ (encodeUInt 8 message.price
    ++ (PriceType.encode message.priceType)))

def decode (bytes : List UInt8) : Option (ReferencePriceMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (origin, bytes) ← Origin.decode bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (priceType, bytes) ← PriceType.decode bytes
  pure ({ instrumentNumber, origin, price, priceType }, bytes)

@[simp] theorem encode_length (message : ReferencePriceMessage) : (encode message).length = 14 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Origin.encode_length, PriceType.encode_length]

theorem encode_length_pos (message : ReferencePriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReferencePriceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Origin.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [PriceType.decode_encode, some_bind]
  rfl

end ReferencePriceMessage

/-- Changes In Status Message: 7 bytes -/
structure ChangesInStatusMessage where
  instrumentNumber : BitVec 32
  origin : Origin
  status : Status
  reason : Reason
  deriving DecidableEq, Repr

namespace ChangesInStatusMessage

def encode (message : ChangesInStatusMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (Origin.encode message.origin
    ++ (Status.encode message.status
    ++ (Reason.encode message.reason)))

def decode (bytes : List UInt8) : Option (ChangesInStatusMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (origin, bytes) ← Origin.decode bytes
  let (status, bytes) ← Status.decode bytes
  let (reason, bytes) ← Reason.decode bytes
  pure ({ instrumentNumber, origin, status, reason }, bytes)

@[simp] theorem encode_length (message : ChangesInStatusMessage) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Origin.encode_length, Status.encode_length, Reason.encode_length]

theorem encode_length_pos (message : ChangesInStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ChangesInStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Origin.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Status.decode_encode, some_bind]
  dsimp only
  rw [Reason.decode_encode, some_bind]
  rfl

end ChangesInStatusMessage

/-- Catalog For Instruments Belonging To The Capital Warrants Market Message: 66 bytes -/
structure CatalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage where
  numberOfTheInstrument : BitVec 32
  origin : Origin
  typeOfValue : Alpha 2
  issuingCompany : Alpha 7
  series : Alpha 6
  typeOfWarrant : TypeOfWarrant
  dateOfMaturity : BitVec 64
  priceOfExercise : BitVec 64
  referencePrice : BitVec 64
  referenceDate : BitVec 64
  reference : Reference
  isin : Alpha 12
  deriving DecidableEq, Repr

namespace CatalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage

def encode (message : CatalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage) : List UInt8 :=
  encodeUInt 4 message.numberOfTheInstrument
    ++ (Origin.encode message.origin
    ++ (Alpha.encode message.typeOfValue
    ++ (Alpha.encode message.issuingCompany
    ++ (Alpha.encode message.series
    ++ (TypeOfWarrant.encode message.typeOfWarrant
    ++ (encodeUInt 8 message.dateOfMaturity
    ++ (encodeUInt 8 message.priceOfExercise
    ++ (encodeUInt 8 message.referencePrice
    ++ (encodeUInt 8 message.referenceDate
    ++ (Reference.encode message.reference
    ++ (Alpha.encode message.isin)))))))))))

def decode (bytes : List UInt8) : Option (CatalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage × List UInt8) := do
  let (numberOfTheInstrument, bytes) ← decodeUInt 4 bytes
  let (origin, bytes) ← Origin.decode bytes
  let (typeOfValue, bytes) ← Alpha.decode 2 bytes
  let (issuingCompany, bytes) ← Alpha.decode 7 bytes
  let (series, bytes) ← Alpha.decode 6 bytes
  let (typeOfWarrant, bytes) ← TypeOfWarrant.decode bytes
  let (dateOfMaturity, bytes) ← decodeUInt 8 bytes
  let (priceOfExercise, bytes) ← decodeUInt 8 bytes
  let (referencePrice, bytes) ← decodeUInt 8 bytes
  let (referenceDate, bytes) ← decodeUInt 8 bytes
  let (reference, bytes) ← Reference.decode bytes
  let (isin, bytes) ← Alpha.decode 12 bytes
  pure ({ numberOfTheInstrument, origin, typeOfValue, issuingCompany, series, typeOfWarrant, dateOfMaturity, priceOfExercise, referencePrice, referenceDate, reference, isin }, bytes)

@[simp] theorem encode_length (message : CatalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage) : (encode message).length = 66 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Origin.encode_length, Alpha.encode_length, TypeOfWarrant.encode_length, Reference.encode_length]

theorem encode_length_pos (message : CatalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CatalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Origin.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TypeOfWarrant.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Reference.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end CatalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage

/-- Catalog Sent For Instruments Belonging To Capital Tracs Message: 82 bytes -/
structure CatalogSentForInstrumentsBelongingToCapitalTracsMessage where
  numberOfTheTrac : BitVec 32
  origin : Origin
  nameOfTheTrac : Alpha 8
  underlyingIssuingCompany : Alpha 7
  underlyingSeries : Alpha 6
  securities : BitVec 64
  excludedSecurities : BitVec 64
  price : BitVec 64
  componentInCash : BitVec 64
  excludedValue : BitVec 64
  numberOfCertificates : BitVec 64
  theoreticalPrice : BitVec 64
  deriving DecidableEq, Repr

namespace CatalogSentForInstrumentsBelongingToCapitalTracsMessage

def encode (message : CatalogSentForInstrumentsBelongingToCapitalTracsMessage) : List UInt8 :=
  encodeUInt 4 message.numberOfTheTrac
    ++ (Origin.encode message.origin
    ++ (Alpha.encode message.nameOfTheTrac
    ++ (Alpha.encode message.underlyingIssuingCompany
    ++ (Alpha.encode message.underlyingSeries
    ++ (encodeUInt 8 message.securities
    ++ (encodeUInt 8 message.excludedSecurities
    ++ (encodeUInt 8 message.price
    ++ (encodeUInt 8 message.componentInCash
    ++ (encodeUInt 8 message.excludedValue
    ++ (encodeUInt 8 message.numberOfCertificates
    ++ (encodeUInt 8 message.theoreticalPrice)))))))))))

def decode (bytes : List UInt8) : Option (CatalogSentForInstrumentsBelongingToCapitalTracsMessage × List UInt8) := do
  let (numberOfTheTrac, bytes) ← decodeUInt 4 bytes
  let (origin, bytes) ← Origin.decode bytes
  let (nameOfTheTrac, bytes) ← Alpha.decode 8 bytes
  let (underlyingIssuingCompany, bytes) ← Alpha.decode 7 bytes
  let (underlyingSeries, bytes) ← Alpha.decode 6 bytes
  let (securities, bytes) ← decodeUInt 8 bytes
  let (excludedSecurities, bytes) ← decodeUInt 8 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (componentInCash, bytes) ← decodeUInt 8 bytes
  let (excludedValue, bytes) ← decodeUInt 8 bytes
  let (numberOfCertificates, bytes) ← decodeUInt 8 bytes
  let (theoreticalPrice, bytes) ← decodeUInt 8 bytes
  pure ({ numberOfTheTrac, origin, nameOfTheTrac, underlyingIssuingCompany, underlyingSeries, securities, excludedSecurities, price, componentInCash, excludedValue, numberOfCertificates, theoreticalPrice }, bytes)

@[simp] theorem encode_length (message : CatalogSentForInstrumentsBelongingToCapitalTracsMessage) : (encode message).length = 82 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Origin.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : CatalogSentForInstrumentsBelongingToCapitalTracsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CatalogSentForInstrumentsBelongingToCapitalTracsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Origin.decode_encode, some_bind]
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CatalogSentForInstrumentsBelongingToCapitalTracsMessage

/-- Consolidated Inav Message: 13 bytes -/
structure ConsolidatedInavMessage where
  numberOfTheTrac : BitVec 32
  origin : Origin
  currentTheoreticalPrice : BitVec 64
  deriving DecidableEq, Repr

namespace ConsolidatedInavMessage

def encode (message : ConsolidatedInavMessage) : List UInt8 :=
  encodeUInt 4 message.numberOfTheTrac
    ++ (Origin.encode message.origin
    ++ (encodeUInt 8 message.currentTheoreticalPrice))

def decode (bytes : List UInt8) : Option (ConsolidatedInavMessage × List UInt8) := do
  let (numberOfTheTrac, bytes) ← decodeUInt 4 bytes
  let (origin, bytes) ← Origin.decode bytes
  let (currentTheoreticalPrice, bytes) ← decodeUInt 8 bytes
  pure ({ numberOfTheTrac, origin, currentTheoreticalPrice }, bytes)

@[simp] theorem encode_length (message : ConsolidatedInavMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Origin.encode_length]

theorem encode_length_pos (message : ConsolidatedInavMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ConsolidatedInavMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Origin.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ConsolidatedInavMessage

/-- Catalog For Instruments Belonging To The Local And Global Stock Market Message: 73 bytes -/
structure CatalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage where
  mseInstrumentNumber : BitVec 32
  valueOfType : Alpha 2
  issuingCompany : Alpha 7
  series : Alpha 6
  lastPrice : BitVec 64
  pppWeightedAveragePrice : BitVec 64
  referenceDate : BitVec 64
  reference : Reference
  couponInEffect : BitVec 16
  marketability : Marketability
  numericalMarketability : BitVec 32
  isin : Alpha 12
  market : Market
  registeredValues : BitVec 64
  exchange : Exchange
  deriving DecidableEq, Repr

namespace CatalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage

def encode (message : CatalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage) : List UInt8 :=
  encodeUInt 4 message.mseInstrumentNumber
    ++ (Alpha.encode message.valueOfType
    ++ (Alpha.encode message.issuingCompany
    ++ (Alpha.encode message.series
    ++ (encodeUInt 8 message.lastPrice
    ++ (encodeUInt 8 message.pppWeightedAveragePrice
    ++ (encodeUInt 8 message.referenceDate
    ++ (Reference.encode message.reference
    ++ (encodeUInt 2 message.couponInEffect
    ++ (Marketability.encode message.marketability
    ++ (encodeUInt 4 message.numericalMarketability
    ++ (Alpha.encode message.isin
    ++ (Market.encode message.market
    ++ (encodeUInt 8 message.registeredValues
    ++ (Exchange.encode message.exchange))))))))))))))

def decode (bytes : List UInt8) : Option (CatalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage × List UInt8) := do
  let (mseInstrumentNumber, bytes) ← decodeUInt 4 bytes
  let (valueOfType, bytes) ← Alpha.decode 2 bytes
  let (issuingCompany, bytes) ← Alpha.decode 7 bytes
  let (series, bytes) ← Alpha.decode 6 bytes
  let (lastPrice, bytes) ← decodeUInt 8 bytes
  let (pppWeightedAveragePrice, bytes) ← decodeUInt 8 bytes
  let (referenceDate, bytes) ← decodeUInt 8 bytes
  let (reference, bytes) ← Reference.decode bytes
  let (couponInEffect, bytes) ← decodeUInt 2 bytes
  let (marketability, bytes) ← Marketability.decode bytes
  let (numericalMarketability, bytes) ← decodeUInt 4 bytes
  let (isin, bytes) ← Alpha.decode 12 bytes
  let (market, bytes) ← Market.decode bytes
  let (registeredValues, bytes) ← decodeUInt 8 bytes
  let (exchange, bytes) ← Exchange.decode bytes
  pure ({ mseInstrumentNumber, valueOfType, issuingCompany, series, lastPrice, pppWeightedAveragePrice, referenceDate, reference, couponInEffect, marketability, numericalMarketability, isin, market, registeredValues, exchange }, bytes)

@[simp] theorem encode_length (message : CatalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage) : (encode message).length = 73 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, Reference.encode_length, Marketability.encode_length, Market.encode_length, Exchange.encode_length]

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
  rw [List.append_assoc, Reference.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Marketability.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Market.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Exchange.decode_encode, some_bind]
  rfl

end CatalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage

/-- Probable Price Of Allocation Message: 21 bytes -/
structure ProbablePriceOfAllocationMessage where
  instrumentNumber : BitVec 32
  origin : Origin
  probablePriceOfAllocation : BitVec 64
  volume : BitVec 64
  deriving DecidableEq, Repr

namespace ProbablePriceOfAllocationMessage

def encode (message : ProbablePriceOfAllocationMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (Origin.encode message.origin
    ++ (encodeUInt 8 message.probablePriceOfAllocation
    ++ (encodeUInt 8 message.volume)))

def decode (bytes : List UInt8) : Option (ProbablePriceOfAllocationMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (origin, bytes) ← Origin.decode bytes
  let (probablePriceOfAllocation, bytes) ← decodeUInt 8 bytes
  let (volume, bytes) ← decodeUInt 8 bytes
  pure ({ instrumentNumber, origin, probablePriceOfAllocation, volume }, bytes)

@[simp] theorem encode_length (message : ProbablePriceOfAllocationMessage) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Origin.encode_length]

theorem encode_length_pos (message : ProbablePriceOfAllocationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ProbablePriceOfAllocationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Origin.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ProbablePriceOfAllocationMessage

/-- Relation Between Bmvbiva Instruments Message: 9 bytes -/
structure RelationBetweenBmvbivaInstrumentsMessage where
  numberOfTheBmvInstrument : BitVec 32
  bivaInstrument : BitVec 32
  typeOfTrading : TypeOfTrading
  deriving DecidableEq, Repr

namespace RelationBetweenBmvbivaInstrumentsMessage

def encode (message : RelationBetweenBmvbivaInstrumentsMessage) : List UInt8 :=
  encodeUInt 4 message.numberOfTheBmvInstrument
    ++ (encodeUInt 4 message.bivaInstrument
    ++ (TypeOfTrading.encode message.typeOfTrading))

def decode (bytes : List UInt8) : Option (RelationBetweenBmvbivaInstrumentsMessage × List UInt8) := do
  let (numberOfTheBmvInstrument, bytes) ← decodeUInt 4 bytes
  let (bivaInstrument, bytes) ← decodeUInt 4 bytes
  let (typeOfTrading, bytes) ← TypeOfTrading.decode bytes
  pure ({ numberOfTheBmvInstrument, bivaInstrument, typeOfTrading }, bytes)

@[simp] theorem encode_length (message : RelationBetweenBmvbivaInstrumentsMessage) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, TypeOfTrading.encode_length]

theorem encode_length_pos (message : RelationBetweenBmvbivaInstrumentsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RelationBetweenBmvbivaInstrumentsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [TypeOfTrading.decode_encode, some_bind]
  rfl

end RelationBetweenBmvbivaInstrumentsMessage

/-- Equities Market Trades Message: 61 bytes -/
structure EquitiesMarketTradesMessage where
  instrumentNumber : BitVec 32
  origin : Origin
  timeOfTheTrade : BitVec 64
  volume : BitVec 64
  price : BitVec 64
  typeOfAgreement : TypeOfAgreement
  consecutiveNumberOfTheTrade : BitVec 64
  setsPrice : Alpha 1
  typeOfTrading : TypeOfTrading
  amount : BitVec 64
  purchases : Alpha 5
  sells : Alpha 5
  settlement : Settlement
  auctionIndicator : AuctionIndicator
  indicator : Indicator
  deriving DecidableEq, Repr

namespace EquitiesMarketTradesMessage

def encode (message : EquitiesMarketTradesMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (Origin.encode message.origin
    ++ (encodeUInt 8 message.timeOfTheTrade
    ++ (encodeUInt 8 message.volume
    ++ (encodeUInt 8 message.price
    ++ (TypeOfAgreement.encode message.typeOfAgreement
    ++ (encodeUInt 8 message.consecutiveNumberOfTheTrade
    ++ (Alpha.encode message.setsPrice
    ++ (TypeOfTrading.encode message.typeOfTrading
    ++ (encodeUInt 8 message.amount
    ++ (Alpha.encode message.purchases
    ++ (Alpha.encode message.sells
    ++ (Settlement.encode message.settlement
    ++ (AuctionIndicator.encode message.auctionIndicator
    ++ (Indicator.encode message.indicator))))))))))))))

def decode (bytes : List UInt8) : Option (EquitiesMarketTradesMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (origin, bytes) ← Origin.decode bytes
  let (timeOfTheTrade, bytes) ← decodeUInt 8 bytes
  let (volume, bytes) ← decodeUInt 8 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (typeOfAgreement, bytes) ← TypeOfAgreement.decode bytes
  let (consecutiveNumberOfTheTrade, bytes) ← decodeUInt 8 bytes
  let (setsPrice, bytes) ← Alpha.decode 1 bytes
  let (typeOfTrading, bytes) ← TypeOfTrading.decode bytes
  let (amount, bytes) ← decodeUInt 8 bytes
  let (purchases, bytes) ← Alpha.decode 5 bytes
  let (sells, bytes) ← Alpha.decode 5 bytes
  let (settlement, bytes) ← Settlement.decode bytes
  let (auctionIndicator, bytes) ← AuctionIndicator.decode bytes
  let (indicator, bytes) ← Indicator.decode bytes
  pure ({ instrumentNumber, origin, timeOfTheTrade, volume, price, typeOfAgreement, consecutiveNumberOfTheTrade, setsPrice, typeOfTrading, amount, purchases, sells, settlement, auctionIndicator, indicator }, bytes)

@[simp] theorem encode_length (message : EquitiesMarketTradesMessage) : (encode message).length = 61 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Origin.encode_length, TypeOfAgreement.encode_length, Alpha.encode_length, TypeOfTrading.encode_length, Settlement.encode_length, AuctionIndicator.encode_length, Indicator.encode_length]

theorem encode_length_pos (message : EquitiesMarketTradesMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EquitiesMarketTradesMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Origin.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TypeOfAgreement.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TypeOfTrading.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Settlement.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AuctionIndicator.decode_encode, some_bind]
  dsimp only
  rw [Indicator.decode_encode, some_bind]
  rfl

end EquitiesMarketTradesMessage

/-- Consolidated Trade Cancellation Message: 13 bytes -/
structure ConsolidatedTradeCancellationMessage where
  instrumentNumber : BitVec 32
  origin : Origin
  consecutiveNumberOfTheTrade : BitVec 64
  deriving DecidableEq, Repr

namespace ConsolidatedTradeCancellationMessage

def encode (message : ConsolidatedTradeCancellationMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (Origin.encode message.origin
    ++ (encodeUInt 8 message.consecutiveNumberOfTheTrade))

def decode (bytes : List UInt8) : Option (ConsolidatedTradeCancellationMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (origin, bytes) ← Origin.decode bytes
  let (consecutiveNumberOfTheTrade, bytes) ← decodeUInt 8 bytes
  pure ({ instrumentNumber, origin, consecutiveNumberOfTheTrade }, bytes)

@[simp] theorem encode_length (message : ConsolidatedTradeCancellationMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Origin.encode_length]

theorem encode_length_pos (message : ConsolidatedTradeCancellationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ConsolidatedTradeCancellationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Origin.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ConsolidatedTradeCancellationMessage

/-- Pricevolume Indicator Message: 38 bytes -/
structure PricevolumeIndicatorMessage where
  instrumentNumber : BitVec 32
  origin : Origin
  probablePriceOfAllotment : BitVec 64
  volume : BitVec 64
  bestSellingPrice : BitVec 64
  bestPurchasingPrice : BitVec 64
  typeOfCrossTrading : TypeOfCrossTrading
  deriving DecidableEq, Repr

namespace PricevolumeIndicatorMessage

def encode (message : PricevolumeIndicatorMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (Origin.encode message.origin
    ++ (encodeUInt 8 message.probablePriceOfAllotment
    ++ (encodeUInt 8 message.volume
    ++ (encodeUInt 8 message.bestSellingPrice
    ++ (encodeUInt 8 message.bestPurchasingPrice
    ++ (TypeOfCrossTrading.encode message.typeOfCrossTrading))))))

def decode (bytes : List UInt8) : Option (PricevolumeIndicatorMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (origin, bytes) ← Origin.decode bytes
  let (probablePriceOfAllotment, bytes) ← decodeUInt 8 bytes
  let (volume, bytes) ← decodeUInt 8 bytes
  let (bestSellingPrice, bytes) ← decodeUInt 8 bytes
  let (bestPurchasingPrice, bytes) ← decodeUInt 8 bytes
  let (typeOfCrossTrading, bytes) ← TypeOfCrossTrading.decode bytes
  pure ({ instrumentNumber, origin, probablePriceOfAllotment, volume, bestSellingPrice, bestPurchasingPrice, typeOfCrossTrading }, bytes)

@[simp] theorem encode_length (message : PricevolumeIndicatorMessage) : (encode message).length = 38 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Origin.encode_length, TypeOfCrossTrading.encode_length]

theorem encode_length_pos (message : PricevolumeIndicatorMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PricevolumeIndicatorMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Origin.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [TypeOfCrossTrading.decode_encode, some_bind]
  rfl

end PricevolumeIndicatorMessage

/-- Consolidated Execution Of Orders Message: 52 bytes -/
structure ConsolidatedExecutionOfOrdersMessage where
  instrumentNumber : BitVec 32
  origin : Origin
  date : BitVec 64
  consecutiveNumber : BitVec 64
  volume : BitVec 64
  consecutiveNumberOfTheTrade : BitVec 64
  executionPrice : BitVec 64
  indicator : Indicator
  setsPrice : Alpha 1
  participant : Alpha 5
  deriving DecidableEq, Repr

namespace ConsolidatedExecutionOfOrdersMessage

def encode (message : ConsolidatedExecutionOfOrdersMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (Origin.encode message.origin
    ++ (encodeUInt 8 message.date
    ++ (encodeUInt 8 message.consecutiveNumber
    ++ (encodeUInt 8 message.volume
    ++ (encodeUInt 8 message.consecutiveNumberOfTheTrade
    ++ (encodeUInt 8 message.executionPrice
    ++ (Indicator.encode message.indicator
    ++ (Alpha.encode message.setsPrice
    ++ (Alpha.encode message.participant)))))))))

def decode (bytes : List UInt8) : Option (ConsolidatedExecutionOfOrdersMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (origin, bytes) ← Origin.decode bytes
  let (date, bytes) ← decodeUInt 8 bytes
  let (consecutiveNumber, bytes) ← decodeUInt 8 bytes
  let (volume, bytes) ← decodeUInt 8 bytes
  let (consecutiveNumberOfTheTrade, bytes) ← decodeUInt 8 bytes
  let (executionPrice, bytes) ← decodeUInt 8 bytes
  let (indicator, bytes) ← Indicator.decode bytes
  let (setsPrice, bytes) ← Alpha.decode 1 bytes
  let (participant, bytes) ← Alpha.decode 5 bytes
  pure ({ instrumentNumber, origin, date, consecutiveNumber, volume, consecutiveNumberOfTheTrade, executionPrice, indicator, setsPrice, participant }, bytes)

@[simp] theorem encode_length (message : ConsolidatedExecutionOfOrdersMessage) : (encode message).length = 52 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Origin.encode_length, Indicator.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : ConsolidatedExecutionOfOrdersMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ConsolidatedExecutionOfOrdersMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Origin.decode_encode, some_bind]
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
  rw [List.append_assoc, Indicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ConsolidatedExecutionOfOrdersMessage

/-- Registration Of Order Message: 43 bytes -/
structure RegistrationOfOrderMessage where
  instrumentNumber : BitVec 32
  origin : Origin
  dateAndTime : BitVec 64
  consecutiveNumber : BitVec 64
  direction : Direction
  volume : BitVec 64
  price : BitVec 64
  participant : Alpha 5
  deriving DecidableEq, Repr

namespace RegistrationOfOrderMessage

def encode (message : RegistrationOfOrderMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (Origin.encode message.origin
    ++ (encodeUInt 8 message.dateAndTime
    ++ (encodeUInt 8 message.consecutiveNumber
    ++ (Direction.encode message.direction
    ++ (encodeUInt 8 message.volume
    ++ (encodeUInt 8 message.price
    ++ (Alpha.encode message.participant)))))))

def decode (bytes : List UInt8) : Option (RegistrationOfOrderMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (origin, bytes) ← Origin.decode bytes
  let (dateAndTime, bytes) ← decodeUInt 8 bytes
  let (consecutiveNumber, bytes) ← decodeUInt 8 bytes
  let (direction, bytes) ← Direction.decode bytes
  let (volume, bytes) ← decodeUInt 8 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (participant, bytes) ← Alpha.decode 5 bytes
  pure ({ instrumentNumber, origin, dateAndTime, consecutiveNumber, direction, volume, price, participant }, bytes)

@[simp] theorem encode_length (message : RegistrationOfOrderMessage) : (encode message).length = 43 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Origin.encode_length, Direction.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : RegistrationOfOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RegistrationOfOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Origin.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Direction.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end RegistrationOfOrderMessage

/-- Cancellations Of Orders Message: 21 bytes -/
structure CancellationsOfOrdersMessage where
  instrumentNumber : BitVec 32
  origin : Origin
  date : BitVec 64
  consecutiveNumber : BitVec 64
  deriving DecidableEq, Repr

namespace CancellationsOfOrdersMessage

def encode (message : CancellationsOfOrdersMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (Origin.encode message.origin
    ++ (encodeUInt 8 message.date
    ++ (encodeUInt 8 message.consecutiveNumber)))

def decode (bytes : List UInt8) : Option (CancellationsOfOrdersMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (origin, bytes) ← Origin.decode bytes
  let (date, bytes) ← decodeUInt 8 bytes
  let (consecutiveNumber, bytes) ← decodeUInt 8 bytes
  pure ({ instrumentNumber, origin, date, consecutiveNumber }, bytes)

@[simp] theorem encode_length (message : CancellationsOfOrdersMessage) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Origin.encode_length]

theorem encode_length_pos (message : CancellationsOfOrdersMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CancellationsOfOrdersMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Origin.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CancellationsOfOrdersMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | mutualFundsTradesMessage (message : MutualFundsTradesMessage) -- 40
  | openingOfContinuousAuctionsMessage (message : OpeningOfContinuousAuctionsMessage) -- 41
  | existenceOfBidsAtMidPriceMessage (message : ExistenceOfBidsAtMidPriceMessage) -- 44
  | catalogueOfDebtAndMetalsInstrumentsMessage (message : CatalogueOfDebtAndMetalsInstrumentsMessage) -- 46
  | catalogSentForInstrumentsBelongingToMutualFundsMessage (message : CatalogSentForInstrumentsBelongingToMutualFundsMessage) -- 48
  | weightedAveragePriceMessage (message : WeightedAveragePriceMessage) -- 54
  | systemEventsMessage (message : SystemEventsMessage) -- 55
  | referencePriceMessage (message : ReferencePriceMessage) -- 56
  | changesInStatusMessage (message : ChangesInStatusMessage) -- 57
  | catalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage (message : CatalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage) -- 84
  | catalogSentForInstrumentsBelongingToCapitalTracsMessage (message : CatalogSentForInstrumentsBelongingToCapitalTracsMessage) -- 91
  | consolidatedInavMessage (message : ConsolidatedInavMessage) -- 93
  | catalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage (message : CatalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage) -- 104
  | probablePriceOfAllocationMessage (message : ProbablePriceOfAllocationMessage) -- 105
  | relationBetweenBmvbivaInstrumentsMessage (message : RelationBetweenBmvbivaInstrumentsMessage) -- 106
  | equitiesMarketTradesMessage (message : EquitiesMarketTradesMessage) -- 112
  | consolidatedTradeCancellationMessage (message : ConsolidatedTradeCancellationMessage) -- 113
  | pricevolumeIndicatorMessage (message : PricevolumeIndicatorMessage) -- 92
  | consolidatedExecutionOfOrdersMessage (message : ConsolidatedExecutionOfOrdersMessage) -- 107
  | registrationOfOrderMessage (message : RegistrationOfOrderMessage) -- 110
  | cancellationsOfOrdersMessage (message : CancellationsOfOrdersMessage) -- 117
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .mutualFundsTradesMessage _ => 40
  | .openingOfContinuousAuctionsMessage _ => 41
  | .existenceOfBidsAtMidPriceMessage _ => 44
  | .catalogueOfDebtAndMetalsInstrumentsMessage _ => 46
  | .catalogSentForInstrumentsBelongingToMutualFundsMessage _ => 48
  | .weightedAveragePriceMessage _ => 54
  | .systemEventsMessage _ => 55
  | .referencePriceMessage _ => 56
  | .changesInStatusMessage _ => 57
  | .catalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage _ => 84
  | .catalogSentForInstrumentsBelongingToCapitalTracsMessage _ => 91
  | .consolidatedInavMessage _ => 93
  | .catalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage _ => 104
  | .probablePriceOfAllocationMessage _ => 105
  | .relationBetweenBmvbivaInstrumentsMessage _ => 106
  | .equitiesMarketTradesMessage _ => 112
  | .consolidatedTradeCancellationMessage _ => 113
  | .pricevolumeIndicatorMessage _ => 92
  | .consolidatedExecutionOfOrdersMessage _ => 107
  | .registrationOfOrderMessage _ => 110
  | .cancellationsOfOrdersMessage _ => 117

def encode : Payload → List UInt8
  | .mutualFundsTradesMessage message => MutualFundsTradesMessage.encode message
  | .openingOfContinuousAuctionsMessage message => OpeningOfContinuousAuctionsMessage.encode message
  | .existenceOfBidsAtMidPriceMessage message => ExistenceOfBidsAtMidPriceMessage.encode message
  | .catalogueOfDebtAndMetalsInstrumentsMessage message => CatalogueOfDebtAndMetalsInstrumentsMessage.encode message
  | .catalogSentForInstrumentsBelongingToMutualFundsMessage message => CatalogSentForInstrumentsBelongingToMutualFundsMessage.encode message
  | .weightedAveragePriceMessage message => WeightedAveragePriceMessage.encode message
  | .systemEventsMessage message => SystemEventsMessage.encode message
  | .referencePriceMessage message => ReferencePriceMessage.encode message
  | .changesInStatusMessage message => ChangesInStatusMessage.encode message
  | .catalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage message => CatalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage.encode message
  | .catalogSentForInstrumentsBelongingToCapitalTracsMessage message => CatalogSentForInstrumentsBelongingToCapitalTracsMessage.encode message
  | .consolidatedInavMessage message => ConsolidatedInavMessage.encode message
  | .catalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage message => CatalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage.encode message
  | .probablePriceOfAllocationMessage message => ProbablePriceOfAllocationMessage.encode message
  | .relationBetweenBmvbivaInstrumentsMessage message => RelationBetweenBmvbivaInstrumentsMessage.encode message
  | .equitiesMarketTradesMessage message => EquitiesMarketTradesMessage.encode message
  | .consolidatedTradeCancellationMessage message => ConsolidatedTradeCancellationMessage.encode message
  | .pricevolumeIndicatorMessage message => PricevolumeIndicatorMessage.encode message
  | .consolidatedExecutionOfOrdersMessage message => ConsolidatedExecutionOfOrdersMessage.encode message
  | .registrationOfOrderMessage message => RegistrationOfOrderMessage.encode message
  | .cancellationsOfOrdersMessage message => CancellationsOfOrdersMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 103 := by
  cases message with
  | mutualFundsTradesMessage inner =>
    simp only [encode, MutualFundsTradesMessage.encode_length]
    omega
  | openingOfContinuousAuctionsMessage inner =>
    simp only [encode, OpeningOfContinuousAuctionsMessage.encode_length]
    omega
  | existenceOfBidsAtMidPriceMessage inner =>
    simp only [encode, ExistenceOfBidsAtMidPriceMessage.encode_length]
    omega
  | catalogueOfDebtAndMetalsInstrumentsMessage inner =>
    simp only [encode, CatalogueOfDebtAndMetalsInstrumentsMessage.encode_length]
    omega
  | catalogSentForInstrumentsBelongingToMutualFundsMessage inner =>
    simp only [encode, CatalogSentForInstrumentsBelongingToMutualFundsMessage.encode_length]
    omega
  | weightedAveragePriceMessage inner =>
    simp only [encode, WeightedAveragePriceMessage.encode_length]
    omega
  | systemEventsMessage inner =>
    simp only [encode, SystemEventsMessage.encode_length]
    omega
  | referencePriceMessage inner =>
    simp only [encode, ReferencePriceMessage.encode_length]
    omega
  | changesInStatusMessage inner =>
    simp only [encode, ChangesInStatusMessage.encode_length]
    omega
  | catalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage inner =>
    simp only [encode, CatalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage.encode_length]
    omega
  | catalogSentForInstrumentsBelongingToCapitalTracsMessage inner =>
    simp only [encode, CatalogSentForInstrumentsBelongingToCapitalTracsMessage.encode_length]
    omega
  | consolidatedInavMessage inner =>
    simp only [encode, ConsolidatedInavMessage.encode_length]
    omega
  | catalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage inner =>
    simp only [encode, CatalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage.encode_length]
    omega
  | probablePriceOfAllocationMessage inner =>
    simp only [encode, ProbablePriceOfAllocationMessage.encode_length]
    omega
  | relationBetweenBmvbivaInstrumentsMessage inner =>
    simp only [encode, RelationBetweenBmvbivaInstrumentsMessage.encode_length]
    omega
  | equitiesMarketTradesMessage inner =>
    simp only [encode, EquitiesMarketTradesMessage.encode_length]
    omega
  | consolidatedTradeCancellationMessage inner =>
    simp only [encode, ConsolidatedTradeCancellationMessage.encode_length]
    omega
  | pricevolumeIndicatorMessage inner =>
    simp only [encode, PricevolumeIndicatorMessage.encode_length]
    omega
  | consolidatedExecutionOfOrdersMessage inner =>
    simp only [encode, ConsolidatedExecutionOfOrdersMessage.encode_length]
    omega
  | registrationOfOrderMessage inner =>
    simp only [encode, RegistrationOfOrderMessage.encode_length]
    omega
  | cancellationsOfOrdersMessage inner =>
    simp only [encode, CancellationsOfOrdersMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 40 then (MutualFundsTradesMessage.decode bytes).map fun (message, rest) => (.mutualFundsTradesMessage message, rest)
  else if tag = 41 then (OpeningOfContinuousAuctionsMessage.decode bytes).map fun (message, rest) => (.openingOfContinuousAuctionsMessage message, rest)
  else if tag = 44 then (ExistenceOfBidsAtMidPriceMessage.decode bytes).map fun (message, rest) => (.existenceOfBidsAtMidPriceMessage message, rest)
  else if tag = 46 then (CatalogueOfDebtAndMetalsInstrumentsMessage.decode bytes).map fun (message, rest) => (.catalogueOfDebtAndMetalsInstrumentsMessage message, rest)
  else if tag = 48 then (CatalogSentForInstrumentsBelongingToMutualFundsMessage.decode bytes).map fun (message, rest) => (.catalogSentForInstrumentsBelongingToMutualFundsMessage message, rest)
  else if tag = 54 then (WeightedAveragePriceMessage.decode bytes).map fun (message, rest) => (.weightedAveragePriceMessage message, rest)
  else if tag = 55 then (SystemEventsMessage.decode bytes).map fun (message, rest) => (.systemEventsMessage message, rest)
  else if tag = 56 then (ReferencePriceMessage.decode bytes).map fun (message, rest) => (.referencePriceMessage message, rest)
  else if tag = 57 then (ChangesInStatusMessage.decode bytes).map fun (message, rest) => (.changesInStatusMessage message, rest)
  else if tag = 84 then (CatalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage.decode bytes).map fun (message, rest) => (.catalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage message, rest)
  else if tag = 91 then (CatalogSentForInstrumentsBelongingToCapitalTracsMessage.decode bytes).map fun (message, rest) => (.catalogSentForInstrumentsBelongingToCapitalTracsMessage message, rest)
  else if tag = 93 then (ConsolidatedInavMessage.decode bytes).map fun (message, rest) => (.consolidatedInavMessage message, rest)
  else if tag = 104 then (CatalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage.decode bytes).map fun (message, rest) => (.catalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage message, rest)
  else if tag = 105 then (ProbablePriceOfAllocationMessage.decode bytes).map fun (message, rest) => (.probablePriceOfAllocationMessage message, rest)
  else if tag = 106 then (RelationBetweenBmvbivaInstrumentsMessage.decode bytes).map fun (message, rest) => (.relationBetweenBmvbivaInstrumentsMessage message, rest)
  else if tag = 112 then (EquitiesMarketTradesMessage.decode bytes).map fun (message, rest) => (.equitiesMarketTradesMessage message, rest)
  else if tag = 113 then (ConsolidatedTradeCancellationMessage.decode bytes).map fun (message, rest) => (.consolidatedTradeCancellationMessage message, rest)
  else if tag = 92 then (PricevolumeIndicatorMessage.decode bytes).map fun (message, rest) => (.pricevolumeIndicatorMessage message, rest)
  else if tag = 107 then (ConsolidatedExecutionOfOrdersMessage.decode bytes).map fun (message, rest) => (.consolidatedExecutionOfOrdersMessage message, rest)
  else if tag = 110 then (RegistrationOfOrderMessage.decode bytes).map fun (message, rest) => (.registrationOfOrderMessage message, rest)
  else if tag = 117 then (CancellationsOfOrdersMessage.decode bytes).map fun (message, rest) => (.cancellationsOfOrdersMessage message, rest)
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
  | mutualFundsTradesMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MutualFundsTradesMessage.encode_length]
    omega
  | openingOfContinuousAuctionsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OpeningOfContinuousAuctionsMessage.encode_length]
    omega
  | existenceOfBidsAtMidPriceMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ExistenceOfBidsAtMidPriceMessage.encode_length]
    omega
  | catalogueOfDebtAndMetalsInstrumentsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, CatalogueOfDebtAndMetalsInstrumentsMessage.encode_length]
    omega
  | catalogSentForInstrumentsBelongingToMutualFundsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, CatalogSentForInstrumentsBelongingToMutualFundsMessage.encode_length]
    omega
  | weightedAveragePriceMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, WeightedAveragePriceMessage.encode_length]
    omega
  | systemEventsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SystemEventsMessage.encode_length]
    omega
  | referencePriceMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ReferencePriceMessage.encode_length]
    omega
  | changesInStatusMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ChangesInStatusMessage.encode_length]
    omega
  | catalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, CatalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage.encode_length]
    omega
  | catalogSentForInstrumentsBelongingToCapitalTracsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, CatalogSentForInstrumentsBelongingToCapitalTracsMessage.encode_length]
    omega
  | consolidatedInavMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ConsolidatedInavMessage.encode_length]
    omega
  | catalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, CatalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage.encode_length]
    omega
  | probablePriceOfAllocationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ProbablePriceOfAllocationMessage.encode_length]
    omega
  | relationBetweenBmvbivaInstrumentsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, RelationBetweenBmvbivaInstrumentsMessage.encode_length]
    omega
  | equitiesMarketTradesMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, EquitiesMarketTradesMessage.encode_length]
    omega
  | consolidatedTradeCancellationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ConsolidatedTradeCancellationMessage.encode_length]
    omega
  | pricevolumeIndicatorMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, PricevolumeIndicatorMessage.encode_length]
    omega
  | consolidatedExecutionOfOrdersMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ConsolidatedExecutionOfOrdersMessage.encode_length]
    omega
  | registrationOfOrderMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, RegistrationOfOrderMessage.encode_length]
    omega
  | cancellationsOfOrdersMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, CancellationsOfOrdersMessage.encode_length]
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

end Omi.BmvBmvmarketdataProduct27IntraV11
