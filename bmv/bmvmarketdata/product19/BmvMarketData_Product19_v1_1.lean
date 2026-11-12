import Wire

/-!
# Bolsa Mexicana de Valores Bmv Market Data Product 19 v1.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.

License: MIT No Attribution
-/

namespace Omi.BmvBmvmarketdataProduct19IntraV11

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

/-- Instrument Status: one byte code -/
def InstrumentStatus.codes : List UInt8 :=
  [0x43, 0x41, 0x50, 0x45, 0x47, 0x54, 0x4E, 0x4B, 0x4D, 0x55, 0x4F, 0x56, 0x4C, 0x49, 0x42, 0x57, 0x58, 0x59, 0x52]

inductive InstrumentStatus where
  | cancellationOfOffers -- Cancellation Of Offers
  | openingAuction -- Opening Auction
  | preOpening -- Pre Opening
  | beingAllocated -- Being Allocated
  | auctionAllocated -- Auction Allocated
  | auctionEnded -- Auction Ended
  | continuousTrading -- Continuous Trading
  | breakingAuctionParameters -- Breaking Auction Parameters
  | continuousAuctionDueToStopOperatingMoreThan20WorkingDays -- Continuous Auction Due To Stop Operating More Than 20 Working Days
  | cleavingAuction -- Cleaving Auction
  | suspendedSeries -- Suspended Series
  | suspendedQuotation -- Suspended Quotation
  | auctionForBreach -- Auction For Breach
  | withdrawalOfOrdersOnContinuousAuction -- Withdrawal Of Orders On Continuous Auction
  | withdrawalOfOrderOnIntradayAuction -- Withdrawal Of Order On Intraday Auction
  | newsPending -- News Pending
  | settlementAuction -- Settlement Auction
  | extraordinarySettlementAuction -- Extraordinary Settlement Auction
  | auctionTotalOfCkDes -- Auction Total Of Ck Des
  | unlisted (byte : { byte : UInt8 // byte ∉ InstrumentStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InstrumentStatus

def toByte : InstrumentStatus → UInt8
  | .cancellationOfOffers => 0x43
  | .openingAuction => 0x41
  | .preOpening => 0x50
  | .beingAllocated => 0x45
  | .auctionAllocated => 0x47
  | .auctionEnded => 0x54
  | .continuousTrading => 0x4E
  | .breakingAuctionParameters => 0x4B
  | .continuousAuctionDueToStopOperatingMoreThan20WorkingDays => 0x4D
  | .cleavingAuction => 0x55
  | .suspendedSeries => 0x4F
  | .suspendedQuotation => 0x56
  | .auctionForBreach => 0x4C
  | .withdrawalOfOrdersOnContinuousAuction => 0x49
  | .withdrawalOfOrderOnIntradayAuction => 0x42
  | .newsPending => 0x57
  | .settlementAuction => 0x58
  | .extraordinarySettlementAuction => 0x59
  | .auctionTotalOfCkDes => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : InstrumentStatus :=
  if byte = 0x43 then .cancellationOfOffers
  else if byte = 0x41 then .openingAuction
  else if byte = 0x50 then .preOpening
  else if byte = 0x45 then .beingAllocated
  else if byte = 0x47 then .auctionAllocated
  else if byte = 0x54 then .auctionEnded
  else if byte = 0x4E then .continuousTrading
  else if byte = 0x4B then .breakingAuctionParameters
  else if byte = 0x4D then .continuousAuctionDueToStopOperatingMoreThan20WorkingDays
  else if byte = 0x55 then .cleavingAuction
  else if byte = 0x4F then .suspendedSeries
  else if byte = 0x56 then .suspendedQuotation
  else if byte = 0x4C then .auctionForBreach
  else if byte = 0x49 then .withdrawalOfOrdersOnContinuousAuction
  else if byte = 0x42 then .withdrawalOfOrderOnIntradayAuction
  else if byte = 0x57 then .newsPending
  else if byte = 0x58 then .settlementAuction
  else if byte = 0x59 then .extraordinarySettlementAuction
  else .auctionTotalOfCkDes

def ofByte (byte : UInt8) : InstrumentStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InstrumentStatus) : ofByte value.toByte = value := by
  cases value with
  | cancellationOfOffers => decide
  | openingAuction => decide
  | preOpening => decide
  | beingAllocated => decide
  | auctionAllocated => decide
  | auctionEnded => decide
  | continuousTrading => decide
  | breakingAuctionParameters => decide
  | continuousAuctionDueToStopOperatingMoreThan20WorkingDays => decide
  | cleavingAuction => decide
  | suspendedSeries => decide
  | suspendedQuotation => decide
  | auctionForBreach => decide
  | withdrawalOfOrdersOnContinuousAuction => decide
  | withdrawalOfOrderOnIntradayAuction => decide
  | newsPending => decide
  | settlementAuction => decide
  | extraordinarySettlementAuction => decide
  | auctionTotalOfCkDes => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : InstrumentStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (InstrumentStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : InstrumentStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : InstrumentStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : InstrumentStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end InstrumentStatus

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

/-- Leg Type: one byte code -/
def LegType.codes : List UInt8 :=
  [0x4C, 0x43, 0x58, 0x50, 0x20]

inductive LegType where
  | longLeg -- Long Leg
  | shortLeg -- Short Leg
  | forwardsChainLeg -- Forwards Chain Leg
  | parentStrategy -- Parent Strategy
  | notGeneratedFromAStrategy -- Not Generated From A Strategy
  | unlisted (byte : { byte : UInt8 // byte ∉ LegType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LegType

def toByte : LegType → UInt8
  | .longLeg => 0x4C
  | .shortLeg => 0x43
  | .forwardsChainLeg => 0x58
  | .parentStrategy => 0x50
  | .notGeneratedFromAStrategy => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LegType :=
  if byte = 0x4C then .longLeg
  else if byte = 0x43 then .shortLeg
  else if byte = 0x58 then .forwardsChainLeg
  else if byte = 0x50 then .parentStrategy
  else .notGeneratedFromAStrategy

def ofByte (byte : UInt8) : LegType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LegType) : ofByte value.toByte = value := by
  cases value with
  | longLeg => decide
  | shortLeg => decide
  | forwardsChainLeg => decide
  | parentStrategy => decide
  | notGeneratedFromAStrategy => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LegType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LegType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LegType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : LegType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : LegType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LegType

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

/-- Status Changes Message: 5 bytes -/
structure StatusChangesMessage where
  instrumentNumber : BitVec 32
  instrumentStatus : InstrumentStatus
  deriving DecidableEq, Repr

namespace StatusChangesMessage

def encode (message : StatusChangesMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (InstrumentStatus.encode message.instrumentStatus)

def decode (bytes : List UInt8) : Option (StatusChangesMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (instrumentStatus, bytes) ← InstrumentStatus.decode bytes
  pure ({ instrumentNumber, instrumentStatus }, bytes)

@[simp] theorem encode_length (message : StatusChangesMessage) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, InstrumentStatus.encode_length]

theorem encode_length_pos (message : StatusChangesMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StatusChangesMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [InstrumentStatus.decode_encode, some_bind]
  rfl

end StatusChangesMessage

/-- Weighted Average Price Settlement Prices Message: 20 bytes -/
structure WeightedAveragePriceSettlementPricesMessage where
  instrumentNumber : BitVec 32
  weightedAveragePrice : BitVec 64
  volatility : BitVec 64
  deriving DecidableEq, Repr

namespace WeightedAveragePriceSettlementPricesMessage

def encode (message : WeightedAveragePriceSettlementPricesMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (encodeUInt 8 message.weightedAveragePrice
    ++ (encodeUInt 8 message.volatility))

def decode (bytes : List UInt8) : Option (WeightedAveragePriceSettlementPricesMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (weightedAveragePrice, bytes) ← decodeUInt 8 bytes
  let (volatility, bytes) ← decodeUInt 8 bytes
  pure ({ instrumentNumber, weightedAveragePrice, volatility }, bytes)

@[simp] theorem encode_length (message : WeightedAveragePriceSettlementPricesMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : WeightedAveragePriceSettlementPricesMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : WeightedAveragePriceSettlementPricesMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end WeightedAveragePriceSettlementPricesMessage

/-- Price Level: 14 bytes -/
structure PriceLevel where
  price : BitVec 64
  numberOfOrders : BitVec 16
  volume : BitVec 32
  deriving DecidableEq, Repr

namespace PriceLevel

def encode (message : PriceLevel) : List UInt8 :=
  encodeUInt 8 message.price
    ++ (encodeUInt 2 message.numberOfOrders
    ++ (encodeUInt 4 message.volume))

def decode (bytes : List UInt8) : Option (PriceLevel × List UInt8) := do
  let (price, bytes) ← decodeUInt 8 bytes
  let (numberOfOrders, bytes) ← decodeUInt 2 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  pure ({ price, numberOfOrders, volume }, bytes)

@[simp] theorem encode_length (message : PriceLevel) : (encode message).length = 14 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : PriceLevel) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PriceLevel) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end PriceLevel

/-- Depth Message -/
structure DepthMessage where
  instrumentNumber : BitVec 32
  side : BitVec 8
  priceLevel : Bounded 1 PriceLevel
  deriving DecidableEq, Repr

namespace DepthMessage

def encode (message : DepthMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.priceLevel.val.length)
    ++ (encodeMany PriceLevel.encode message.priceLevel.val)))

def decode (bytes : List UInt8) : Option (DepthMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (purchaseOrSaleLevels, bytes) ← decodeUInt 1 bytes
  let (priceLevel_, bytes) ← decodeMany PriceLevel.decode purchaseOrSaleLevels.toNat bytes
  if fits_priceLevel : priceLevel_.length < 256 ^ 1 then
    pure ({ instrumentNumber, side, priceLevel := ⟨priceLevel_, fits_priceLevel⟩ }, bytes)
  else none

theorem encode_length_pos (message : DepthMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DepthMessage) : (encode message).length ≤ 3576 := by
  have bound_priceLevel := message.priceLevel.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const PriceLevel.encode 14 PriceLevel.encode_length]
  omega

@[simp] theorem decode_encode (message : DepthMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 PriceLevel.encode PriceLevel.decode PriceLevel.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.priceLevel.length_lt]
  rfl

end DepthMessage

/-- Open Interest Message: 8 bytes -/
structure OpenInterestMessage where
  instrumentNumber : BitVec 32
  openInterest : BitVec 32
  deriving DecidableEq, Repr

namespace OpenInterestMessage

def encode (message : OpenInterestMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (encodeUInt 4 message.openInterest)

def decode (bytes : List UInt8) : Option (OpenInterestMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (openInterest, bytes) ← decodeUInt 4 bytes
  pure ({ instrumentNumber, openInterest }, bytes)

@[simp] theorem encode_length (message : OpenInterestMessage) : (encode message).length = 8 := by
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OpenInterestMessage

/-- Derivatives Market Trades Message: 43 bytes -/
structure DerivativesMarketTradesMessage where
  instrumentNumber : BitVec 32
  tradeTime : BitVec 64
  volume : BitVec 32
  priceRate : BitVec 64
  concertationType : ConcertationType
  tradeNumber : BitVec 32
  operationType : OperationType
  amount : BitVec 64
  parentTradeNumber : BitVec 32
  legType : LegType
  deriving DecidableEq, Repr

namespace DerivativesMarketTradesMessage

def encode (message : DerivativesMarketTradesMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (encodeUInt 8 message.tradeTime
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 8 message.priceRate
    ++ (ConcertationType.encode message.concertationType
    ++ (encodeUInt 4 message.tradeNumber
    ++ (OperationType.encode message.operationType
    ++ (encodeUInt 8 message.amount
    ++ (encodeUInt 4 message.parentTradeNumber
    ++ (LegType.encode message.legType)))))))))

def decode (bytes : List UInt8) : Option (DerivativesMarketTradesMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (tradeTime, bytes) ← decodeUInt 8 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (priceRate, bytes) ← decodeUInt 8 bytes
  let (concertationType, bytes) ← ConcertationType.decode bytes
  let (tradeNumber, bytes) ← decodeUInt 4 bytes
  let (operationType, bytes) ← OperationType.decode bytes
  let (amount, bytes) ← decodeUInt 8 bytes
  let (parentTradeNumber, bytes) ← decodeUInt 4 bytes
  let (legType, bytes) ← LegType.decode bytes
  pure ({ instrumentNumber, tradeTime, volume, priceRate, concertationType, tradeNumber, operationType, amount, parentTradeNumber, legType }, bytes)

@[simp] theorem encode_length (message : DerivativesMarketTradesMessage) : (encode message).length = 43 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, ConcertationType.encode_length, OperationType.encode_length, LegType.encode_length]

theorem encode_length_pos (message : DerivativesMarketTradesMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DerivativesMarketTradesMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, OperationType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [LegType.decode_encode, some_bind]
  rfl

end DerivativesMarketTradesMessage

/-- Statistics Of Instruments Message: 44 bytes -/
structure StatisticsOfInstrumentsMessage where
  instrumentNumber : BitVec 32
  previousSettlementPrice : BitVec 64
  openingPrice : BitVec 64
  maxPriceOfTheDay : BitVec 64
  lowerPriceOfTheDay : BitVec 64
  lastPriceOfTheDay : BitVec 64
  deriving DecidableEq, Repr

namespace StatisticsOfInstrumentsMessage

def encode (message : StatisticsOfInstrumentsMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (encodeUInt 8 message.previousSettlementPrice
    ++ (encodeUInt 8 message.openingPrice
    ++ (encodeUInt 8 message.maxPriceOfTheDay
    ++ (encodeUInt 8 message.lowerPriceOfTheDay
    ++ (encodeUInt 8 message.lastPriceOfTheDay)))))

def decode (bytes : List UInt8) : Option (StatisticsOfInstrumentsMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (previousSettlementPrice, bytes) ← decodeUInt 8 bytes
  let (openingPrice, bytes) ← decodeUInt 8 bytes
  let (maxPriceOfTheDay, bytes) ← decodeUInt 8 bytes
  let (lowerPriceOfTheDay, bytes) ← decodeUInt 8 bytes
  let (lastPriceOfTheDay, bytes) ← decodeUInt 8 bytes
  pure ({ instrumentNumber, previousSettlementPrice, openingPrice, maxPriceOfTheDay, lowerPriceOfTheDay, lastPriceOfTheDay }, bytes)

@[simp] theorem encode_length (message : StatisticsOfInstrumentsMessage) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : StatisticsOfInstrumentsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StatisticsOfInstrumentsMessage) (rest : List UInt8) :
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

end StatisticsOfInstrumentsMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | eventsSystemMessage (message : EventsSystemMessage) -- 83
  | tradeCancellationMessage (message : TradeCancellationMessage) -- 72
  | statusChangesMessage (message : StatusChangesMessage) -- 52
  | weightedAveragePriceSettlementPricesMessage (message : WeightedAveragePriceSettlementPricesMessage) -- 77
  | depthMessage (message : DepthMessage) -- 49
  | openInterestMessage (message : OpenInterestMessage) -- 73
  | derivativesMarketTradesMessage (message : DerivativesMarketTradesMessage) -- 81
  | statisticsOfInstrumentsMessage (message : StatisticsOfInstrumentsMessage) -- 82
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .eventsSystemMessage _ => 83
  | .tradeCancellationMessage _ => 72
  | .statusChangesMessage _ => 52
  | .weightedAveragePriceSettlementPricesMessage _ => 77
  | .depthMessage _ => 49
  | .openInterestMessage _ => 73
  | .derivativesMarketTradesMessage _ => 81
  | .statisticsOfInstrumentsMessage _ => 82

def encode : Payload → List UInt8
  | .eventsSystemMessage message => EventsSystemMessage.encode message
  | .tradeCancellationMessage message => TradeCancellationMessage.encode message
  | .statusChangesMessage message => StatusChangesMessage.encode message
  | .weightedAveragePriceSettlementPricesMessage message => WeightedAveragePriceSettlementPricesMessage.encode message
  | .depthMessage message => DepthMessage.encode message
  | .openInterestMessage message => OpenInterestMessage.encode message
  | .derivativesMarketTradesMessage message => DerivativesMarketTradesMessage.encode message
  | .statisticsOfInstrumentsMessage message => StatisticsOfInstrumentsMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 3576 := by
  cases message with
  | eventsSystemMessage inner =>
    simp only [encode, EventsSystemMessage.encode_length]
    omega
  | tradeCancellationMessage inner =>
    simp only [encode, TradeCancellationMessage.encode_length]
    omega
  | statusChangesMessage inner =>
    simp only [encode, StatusChangesMessage.encode_length]
    omega
  | weightedAveragePriceSettlementPricesMessage inner =>
    simp only [encode, WeightedAveragePriceSettlementPricesMessage.encode_length]
    omega
  | depthMessage inner =>
    have bound_inner := DepthMessage.encode_length_le inner
    simp only [encode]
    omega
  | openInterestMessage inner =>
    simp only [encode, OpenInterestMessage.encode_length]
    omega
  | derivativesMarketTradesMessage inner =>
    simp only [encode, DerivativesMarketTradesMessage.encode_length]
    omega
  | statisticsOfInstrumentsMessage inner =>
    simp only [encode, StatisticsOfInstrumentsMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 83 then (EventsSystemMessage.decode bytes).map fun (message, rest) => (.eventsSystemMessage message, rest)
  else if tag = 72 then (TradeCancellationMessage.decode bytes).map fun (message, rest) => (.tradeCancellationMessage message, rest)
  else if tag = 52 then (StatusChangesMessage.decode bytes).map fun (message, rest) => (.statusChangesMessage message, rest)
  else if tag = 77 then (WeightedAveragePriceSettlementPricesMessage.decode bytes).map fun (message, rest) => (.weightedAveragePriceSettlementPricesMessage message, rest)
  else if tag = 49 then (DepthMessage.decode bytes).map fun (message, rest) => (.depthMessage message, rest)
  else if tag = 73 then (OpenInterestMessage.decode bytes).map fun (message, rest) => (.openInterestMessage message, rest)
  else if tag = 81 then (DerivativesMarketTradesMessage.decode bytes).map fun (message, rest) => (.derivativesMarketTradesMessage message, rest)
  else if tag = 82 then (StatisticsOfInstrumentsMessage.decode bytes).map fun (message, rest) => (.statisticsOfInstrumentsMessage message, rest)
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
  | statusChangesMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, StatusChangesMessage.encode_length]
    omega
  | weightedAveragePriceSettlementPricesMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, WeightedAveragePriceSettlementPricesMessage.encode_length]
    omega
  | depthMessage inner =>
    have bound_inner := DepthMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUInt_length]
    omega
  | openInterestMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OpenInterestMessage.encode_length]
    omega
  | derivativesMarketTradesMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, DerivativesMarketTradesMessage.encode_length]
    omega
  | statisticsOfInstrumentsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, StatisticsOfInstrumentsMessage.encode_length]
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

end Omi.BmvBmvmarketdataProduct19IntraV11
