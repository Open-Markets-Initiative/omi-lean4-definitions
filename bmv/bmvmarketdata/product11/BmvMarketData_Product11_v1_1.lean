import Wire

/-!
# Bolsa Mexicana de Valores Bmv Market Data Product 11 v1.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.

License: MIT No Attribution
-/

namespace Omi.BmvBmvmarketdataProduct11IntraV11

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

/-- Concertation Type: one byte code -/
def ConcertationType.codes : List UInt8 :=
  [0x43, 0x4F, 0x48, 0x44, 0x4D, 0x50, 0x58, 0x76, 0x77, 0x25, 0x78, 0x79, 0x41, 0x42, 0x45, 0x46, 0x47, 0x4A, 0x4B, 0x4C, 0x4E, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57, 0x59, 0x5A, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x6A, 0x6B, 0x6C, 0x6D, 0x6E, 0x6F, 0x70, 0x71, 0x72, 0x73, 0x74, 0x75, 0x7A, 0x23, 0x49, 0x2B, 0x26, 0x28, 0x29]

inductive ConcertationType where
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
  | unlisted (byte : { byte : UInt8 // byte ∉ ConcertationType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ConcertationType

def toByte : ConcertationType → UInt8
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
def listed (byte : UInt8) : ConcertationType :=
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

def ofByte (byte : UInt8) : ConcertationType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ConcertationType) : ofByte value.toByte = value := by
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

def encode (value : ConcertationType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ConcertationType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ConcertationType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ConcertationType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ConcertationType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ConcertationType

/-- Operation Type: one byte code -/
def OperationType.codes : List UInt8 :=
  [0x43, 0x4F, 0x52, 0x41, 0x53, 0x46, 0x48, 0x4D, 0x58, 0x50, 0x44, 0x4E]

inductive OperationType where
  | cash -- Cash
  | publicOffering -- Public Offering
  | registrationOperation -- Registration Operation
  | overallocation -- Overallocation
  | reciprocalSubscription -- Reciprocal Subscription
  | publicBuyOffering -- Public Buy Offering
  | tradesAtClosing -- Trades At Closing
  | mediumPrice -- Medium Price
  | operationByException -- Operation By Exception
  | averageForTheDay -- Average For The Day
  | afterClosing -- After Closing
  | inavTrading -- Inav Trading
  | unlisted (byte : { byte : UInt8 // byte ∉ OperationType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OperationType

def toByte : OperationType → UInt8
  | .cash => 0x43
  | .publicOffering => 0x4F
  | .registrationOperation => 0x52
  | .overallocation => 0x41
  | .reciprocalSubscription => 0x53
  | .publicBuyOffering => 0x46
  | .tradesAtClosing => 0x48
  | .mediumPrice => 0x4D
  | .operationByException => 0x58
  | .averageForTheDay => 0x50
  | .afterClosing => 0x44
  | .inavTrading => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OperationType :=
  if byte = 0x43 then .cash
  else if byte = 0x4F then .publicOffering
  else if byte = 0x52 then .registrationOperation
  else if byte = 0x41 then .overallocation
  else if byte = 0x53 then .reciprocalSubscription
  else if byte = 0x46 then .publicBuyOffering
  else if byte = 0x48 then .tradesAtClosing
  else if byte = 0x4D then .mediumPrice
  else if byte = 0x58 then .operationByException
  else if byte = 0x50 then .averageForTheDay
  else if byte = 0x44 then .afterClosing
  else .inavTrading

def ofByte (byte : UInt8) : OperationType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OperationType) : ofByte value.toByte = value := by
  cases value with
  | cash => decide
  | publicOffering => decide
  | registrationOperation => decide
  | overallocation => decide
  | reciprocalSubscription => decide
  | publicBuyOffering => decide
  | tradesAtClosing => decide
  | mediumPrice => decide
  | operationByException => decide
  | averageForTheDay => decide
  | afterClosing => decide
  | inavTrading => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OperationType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OperationType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OperationType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OperationType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OperationType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OperationType

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

/-- Offer Type: one byte code -/
def OfferType.codes : List UInt8 :=
  [0x50, 0x52, 0x43, 0x41, 0x53]

inductive OfferType where
  | publicOffering -- Public Offering
  | registrationOperation -- Registration Operation
  | buyPublicOffering -- Buy Public Offering
  | overallocation -- Overallocation
  | reciprocalSubscription -- Reciprocal Subscription
  | unlisted (byte : { byte : UInt8 // byte ∉ OfferType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OfferType

def toByte : OfferType → UInt8
  | .publicOffering => 0x50
  | .registrationOperation => 0x52
  | .buyPublicOffering => 0x43
  | .overallocation => 0x41
  | .reciprocalSubscription => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OfferType :=
  if byte = 0x50 then .publicOffering
  else if byte = 0x52 then .registrationOperation
  else if byte = 0x43 then .buyPublicOffering
  else if byte = 0x41 then .overallocation
  else .reciprocalSubscription

def ofByte (byte : UInt8) : OfferType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OfferType) : ofByte value.toByte = value := by
  cases value with
  | publicOffering => decide
  | registrationOperation => decide
  | buyPublicOffering => decide
  | overallocation => decide
  | reciprocalSubscription => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OfferType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OfferType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OfferType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OfferType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OfferType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OfferType

/-- Income: one byte code -/
def Income.codes : List UInt8 :=
  [0x56, 0x46, 0x57]

inductive Income where
  | variableIncome -- Variable Income
  | fixedIncome -- Fixed Income
  | warrants -- Warrants
  | unlisted (byte : { byte : UInt8 // byte ∉ Income.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Income

def toByte : Income → UInt8
  | .variableIncome => 0x56
  | .fixedIncome => 0x46
  | .warrants => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Income :=
  if byte = 0x56 then .variableIncome
  else if byte = 0x46 then .fixedIncome
  else .warrants

def ofByte (byte : UInt8) : Income :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Income) : ofByte value.toByte = value := by
  cases value with
  | variableIncome => decide
  | fixedIncome => decide
  | warrants => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Income) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Income × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Income) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Income) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Income) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Income

/-- Movement: one byte code -/
def Movement.codes : List UInt8 :=
  [0x41, 0x55, 0x43, 0x42]

inductive Movement where
  | registryOperation -- Registry Operation
  | operationAuthorization -- Operation Authorization
  | placementOperation -- Placement Operation
  | deleteOperation -- Delete Operation
  | unlisted (byte : { byte : UInt8 // byte ∉ Movement.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Movement

def toByte : Movement → UInt8
  | .registryOperation => 0x41
  | .operationAuthorization => 0x55
  | .placementOperation => 0x43
  | .deleteOperation => 0x42
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Movement :=
  if byte = 0x41 then .registryOperation
  else if byte = 0x55 then .operationAuthorization
  else if byte = 0x43 then .placementOperation
  else .deleteOperation

def ofByte (byte : UInt8) : Movement :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Movement) : ofByte value.toByte = value := by
  cases value with
  | registryOperation => decide
  | operationAuthorization => decide
  | placementOperation => decide
  | deleteOperation => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Movement) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Movement × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Movement) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Movement) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Movement) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Movement

/-- Currency Type: one byte code -/
def CurrencyType.codes : List UInt8 :=
  [0x4E, 0x44]

inductive CurrencyType where
  | mexicanCurrency -- Mexican Currency
  | dollar -- Dollar
  | unlisted (byte : { byte : UInt8 // byte ∉ CurrencyType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CurrencyType

def toByte : CurrencyType → UInt8
  | .mexicanCurrency => 0x4E
  | .dollar => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CurrencyType :=
  if byte = 0x4E then .mexicanCurrency
  else .dollar

def ofByte (byte : UInt8) : CurrencyType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CurrencyType) : ofByte value.toByte = value := by
  cases value with
  | mexicanCurrency => decide
  | dollar => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CurrencyType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CurrencyType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CurrencyType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CurrencyType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CurrencyType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CurrencyType

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

/-- Trade Cancellation Message: 8 bytes -/
structure TradeCancellationMessage where
  instrumentNumber : BitVec 32
  tradeNumber : BitVec 32
  deriving DecidableEq, Repr

namespace TradeCancellationMessage

def encode (message : TradeCancellationMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (encodeUInt 4 message.tradeNumber)

def decode (bytes : List UInt8) : Option (TradeCancellationMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (tradeNumber, bytes) ← decodeUInt 4 bytes
  pure ({ instrumentNumber, tradeNumber }, bytes)

@[simp] theorem encode_length (message : TradeCancellationMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : TradeCancellationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCancellationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TradeCancellationMessage

/-- Capital Trades Message: 51 bytes -/
structure CapitalTradesMessage where
  instrumentNumber : BitVec 32
  tradeTime : BitVec 64
  volumeInt324 : BitVec 32
  price : BitVec 64
  concertationType : ConcertationType
  tradeNumber : BitVec 32
  priceSetter : Alpha 1
  operationType : OperationType
  amount : BitVec 64
  buy : Alpha 5
  sell : Alpha 5
  settlement : Settlement
  auctionIndicator : AuctionIndicator
  deriving DecidableEq, Repr

namespace CapitalTradesMessage

def encode (message : CapitalTradesMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (encodeUInt 8 message.tradeTime
    ++ (encodeUInt 4 message.volumeInt324
    ++ (encodeUInt 8 message.price
    ++ (ConcertationType.encode message.concertationType
    ++ (encodeUInt 4 message.tradeNumber
    ++ (Alpha.encode message.priceSetter
    ++ (OperationType.encode message.operationType
    ++ (encodeUInt 8 message.amount
    ++ (Alpha.encode message.buy
    ++ (Alpha.encode message.sell
    ++ (Settlement.encode message.settlement
    ++ (AuctionIndicator.encode message.auctionIndicator))))))))))))

def decode (bytes : List UInt8) : Option (CapitalTradesMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (tradeTime, bytes) ← decodeUInt 8 bytes
  let (volumeInt324, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (concertationType, bytes) ← ConcertationType.decode bytes
  let (tradeNumber, bytes) ← decodeUInt 4 bytes
  let (priceSetter, bytes) ← Alpha.decode 1 bytes
  let (operationType, bytes) ← OperationType.decode bytes
  let (amount, bytes) ← decodeUInt 8 bytes
  let (buy, bytes) ← Alpha.decode 5 bytes
  let (sell, bytes) ← Alpha.decode 5 bytes
  let (settlement, bytes) ← Settlement.decode bytes
  let (auctionIndicator, bytes) ← AuctionIndicator.decode bytes
  pure ({ instrumentNumber, tradeTime, volumeInt324, price, concertationType, tradeNumber, priceSetter, operationType, amount, buy, sell, settlement, auctionIndicator }, bytes)

@[simp] theorem encode_length (message : CapitalTradesMessage) : (encode message).length = 51 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, ConcertationType.encode_length, Alpha.encode_length, OperationType.encode_length, Settlement.encode_length, AuctionIndicator.encode_length]

theorem encode_length_pos (message : CapitalTradesMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CapitalTradesMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, ConcertationType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OperationType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Settlement.decode_encode, some_bind]
  dsimp only
  rw [AuctionIndicator.decode_encode, some_bind]
  rfl

end CapitalTradesMessage

/-- Registry Operations Message: 61 bytes -/
structure RegistryOperationsMessage where
  instrumentNumber : BitVec 32
  offerType : OfferType
  income : Income
  valueType : Alpha 4
  issuer : Alpha 7
  series : Alpha 6
  maximumVolume : BitVec 64
  registeredVolume : BitVec 64
  priceRate : BitVec 64
  settlementDate : BitVec 64
  firm : Alpha 5
  movement : Movement
  deriving DecidableEq, Repr

namespace RegistryOperationsMessage

def encode (message : RegistryOperationsMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (OfferType.encode message.offerType
    ++ (Income.encode message.income
    ++ (Alpha.encode message.valueType
    ++ (Alpha.encode message.issuer
    ++ (Alpha.encode message.series
    ++ (encodeUInt 8 message.maximumVolume
    ++ (encodeUInt 8 message.registeredVolume
    ++ (encodeUInt 8 message.priceRate
    ++ (encodeUInt 8 message.settlementDate
    ++ (Alpha.encode message.firm
    ++ (Movement.encode message.movement)))))))))))

def decode (bytes : List UInt8) : Option (RegistryOperationsMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (offerType, bytes) ← OfferType.decode bytes
  let (income, bytes) ← Income.decode bytes
  let (valueType, bytes) ← Alpha.decode 4 bytes
  let (issuer, bytes) ← Alpha.decode 7 bytes
  let (series, bytes) ← Alpha.decode 6 bytes
  let (maximumVolume, bytes) ← decodeUInt 8 bytes
  let (registeredVolume, bytes) ← decodeUInt 8 bytes
  let (priceRate, bytes) ← decodeUInt 8 bytes
  let (settlementDate, bytes) ← decodeUInt 8 bytes
  let (firm, bytes) ← Alpha.decode 5 bytes
  let (movement, bytes) ← Movement.decode bytes
  pure ({ instrumentNumber, offerType, income, valueType, issuer, series, maximumVolume, registeredVolume, priceRate, settlementDate, firm, movement }, bytes)

@[simp] theorem encode_length (message : RegistryOperationsMessage) : (encode message).length = 61 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, OfferType.encode_length, Income.encode_length, Alpha.encode_length, Movement.encode_length]

theorem encode_length_pos (message : RegistryOperationsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RegistryOperationsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OfferType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Income.decode_encode, some_bind]
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
  rw [Movement.decode_encode, some_bind]
  rfl

end RegistryOperationsMessage

/-- Public Offerings Message: 66 bytes -/
structure PublicOfferingsMessage where
  instrumentNumber : BitVec 32
  number : BitVec 32
  volumeInt648 : BitVec 64
  discountRateOrPrice : BitVec 64
  rateOfReturn : BitVec 32
  termDays : BitVec 16
  currencyType : CurrencyType
  settlement : Settlement
  buy : Alpha 5
  sell : Alpha 5
  placementDate : BitVec 64
  issueDate : BitVec 64
  maturityDate : BitVec 64
  deriving DecidableEq, Repr

namespace PublicOfferingsMessage

def encode (message : PublicOfferingsMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (encodeUInt 4 message.number
    ++ (encodeUInt 8 message.volumeInt648
    ++ (encodeUInt 8 message.discountRateOrPrice
    ++ (encodeUInt 4 message.rateOfReturn
    ++ (encodeUInt 2 message.termDays
    ++ (CurrencyType.encode message.currencyType
    ++ (Settlement.encode message.settlement
    ++ (Alpha.encode message.buy
    ++ (Alpha.encode message.sell
    ++ (encodeUInt 8 message.placementDate
    ++ (encodeUInt 8 message.issueDate
    ++ (encodeUInt 8 message.maturityDate))))))))))))

def decode (bytes : List UInt8) : Option (PublicOfferingsMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (number, bytes) ← decodeUInt 4 bytes
  let (volumeInt648, bytes) ← decodeUInt 8 bytes
  let (discountRateOrPrice, bytes) ← decodeUInt 8 bytes
  let (rateOfReturn, bytes) ← decodeUInt 4 bytes
  let (termDays, bytes) ← decodeUInt 2 bytes
  let (currencyType, bytes) ← CurrencyType.decode bytes
  let (settlement, bytes) ← Settlement.decode bytes
  let (buy, bytes) ← Alpha.decode 5 bytes
  let (sell, bytes) ← Alpha.decode 5 bytes
  let (placementDate, bytes) ← decodeUInt 8 bytes
  let (issueDate, bytes) ← decodeUInt 8 bytes
  let (maturityDate, bytes) ← decodeUInt 8 bytes
  pure ({ instrumentNumber, number, volumeInt648, discountRateOrPrice, rateOfReturn, termDays, currencyType, settlement, buy, sell, placementDate, issueDate, maturityDate }, bytes)

@[simp] theorem encode_length (message : PublicOfferingsMessage) : (encode message).length = 66 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, CurrencyType.encode_length, Settlement.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : PublicOfferingsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PublicOfferingsMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, CurrencyType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Settlement.decode_encode, some_bind]
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

end PublicOfferingsMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | eventsSystemMessage (message : EventsSystemMessage) -- 83
  | tradeCancellationMessage (message : TradeCancellationMessage) -- 72
  | capitalTradesMessage (message : CapitalTradesMessage) -- 80
  | registryOperationsMessage (message : RegistryOperationsMessage) -- 90
  | publicOfferingsMessage (message : PublicOfferingsMessage) -- 66
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .eventsSystemMessage _ => 83
  | .tradeCancellationMessage _ => 72
  | .capitalTradesMessage _ => 80
  | .registryOperationsMessage _ => 90
  | .publicOfferingsMessage _ => 66

def encode : Payload → List UInt8
  | .eventsSystemMessage message => EventsSystemMessage.encode message
  | .tradeCancellationMessage message => TradeCancellationMessage.encode message
  | .capitalTradesMessage message => CapitalTradesMessage.encode message
  | .registryOperationsMessage message => RegistryOperationsMessage.encode message
  | .publicOfferingsMessage message => PublicOfferingsMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 66 := by
  cases message with
  | eventsSystemMessage inner =>
    simp only [encode, EventsSystemMessage.encode_length]
    omega
  | tradeCancellationMessage inner =>
    simp only [encode, TradeCancellationMessage.encode_length]
    omega
  | capitalTradesMessage inner =>
    simp only [encode, CapitalTradesMessage.encode_length]
    omega
  | registryOperationsMessage inner =>
    simp only [encode, RegistryOperationsMessage.encode_length]
    omega
  | publicOfferingsMessage inner =>
    simp only [encode, PublicOfferingsMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 83 then (EventsSystemMessage.decode bytes).map fun (message, rest) => (.eventsSystemMessage message, rest)
  else if tag = 72 then (TradeCancellationMessage.decode bytes).map fun (message, rest) => (.tradeCancellationMessage message, rest)
  else if tag = 80 then (CapitalTradesMessage.decode bytes).map fun (message, rest) => (.capitalTradesMessage message, rest)
  else if tag = 90 then (RegistryOperationsMessage.decode bytes).map fun (message, rest) => (.registryOperationsMessage message, rest)
  else if tag = 66 then (PublicOfferingsMessage.decode bytes).map fun (message, rest) => (.publicOfferingsMessage message, rest)
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
  | tradeCancellationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeCancellationMessage.encode_length]
    omega
  | capitalTradesMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, CapitalTradesMessage.encode_length]
    omega
  | registryOperationsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, RegistryOperationsMessage.encode_length]
    omega
  | publicOfferingsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, PublicOfferingsMessage.encode_length]
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

end Omi.BmvBmvmarketdataProduct11IntraV11
