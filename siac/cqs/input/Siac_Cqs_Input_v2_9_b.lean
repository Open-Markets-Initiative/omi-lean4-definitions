import Wire

/-!
# The Securities Industry Automation Corporation  v2.9.b

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.SiacCqsInputCtaV29B

/-- Instrument Type: one byte code -/
def InstrumentType.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33]

inductive InstrumentType where
  | ctaEligibleEquity -- Cta Eligible Equity
  | localIssue -- Local Issue
  | corporateBond -- Corporate Bond
  | governmentBond -- Government Bond
  | unlisted (byte : { byte : UInt8 // byte ∉ InstrumentType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InstrumentType

def toByte : InstrumentType → UInt8
  | .ctaEligibleEquity => 0x30
  | .localIssue => 0x31
  | .corporateBond => 0x32
  | .governmentBond => 0x33
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : InstrumentType :=
  if byte = 0x30 then .ctaEligibleEquity
  else if byte = 0x31 then .localIssue
  else if byte = 0x32 then .corporateBond
  else .governmentBond

def ofByte (byte : UInt8) : InstrumentType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InstrumentType) : ofByte value.toByte = value := by
  cases value with
  | ctaEligibleEquity => decide
  | localIssue => decide
  | corporateBond => decide
  | governmentBond => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : InstrumentType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (InstrumentType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : InstrumentType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : InstrumentType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : InstrumentType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end InstrumentType

/-- Quote Condition: one byte code -/
def QuoteCondition.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x45, 0x46, 0x48, 0x4C, 0x4E, 0x4F, 0x52, 0x55, 0x57, 0x34]

inductive QuoteCondition where
  | slowQuoteOnOfferSide -- Slow Quote On Offer Side
  | slowQuoteOnBidSide -- Slow Quote On Bid Side
  | closing -- Closing
  | slowQuoteDueToLrpOrGapQuoteOnTheBidSide -- Slow Quote Due To Lrp Or Gap Quote On The Bid Side
  | slowQuoteDueToLrpOrGapQuoteOnTheOfferSide -- Slow Quote Due To Lrp Or Gap Quote On The Offer Side
  | slowQuoteOnTheBidAndOfferSides -- Slow Quote On The Bid And Offer Sides
  | closedMarketMakerFinra -- Closed Market Maker Finra
  | nonFirmQuote -- Non Firm Quote
  | openingQuote -- Opening Quote
  | regular -- Regular
  | slowQuoteDueToLrpOrGapQuoteOnBothSides -- Slow Quote Due To Lrp Or Gap Quote On Both Sides
  | slowQuoteDueToSetSlowListOnBothSides -- Slow Quote Due To Set Slow List On Both Sides
  | onDemandIntraDayAuction -- On Demand Intra Day Auction
  | unlisted (byte : { byte : UInt8 // byte ∉ QuoteCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace QuoteCondition

def toByte : QuoteCondition → UInt8
  | .slowQuoteOnOfferSide => 0x41
  | .slowQuoteOnBidSide => 0x42
  | .closing => 0x43
  | .slowQuoteDueToLrpOrGapQuoteOnTheBidSide => 0x45
  | .slowQuoteDueToLrpOrGapQuoteOnTheOfferSide => 0x46
  | .slowQuoteOnTheBidAndOfferSides => 0x48
  | .closedMarketMakerFinra => 0x4C
  | .nonFirmQuote => 0x4E
  | .openingQuote => 0x4F
  | .regular => 0x52
  | .slowQuoteDueToLrpOrGapQuoteOnBothSides => 0x55
  | .slowQuoteDueToSetSlowListOnBothSides => 0x57
  | .onDemandIntraDayAuction => 0x34
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : QuoteCondition :=
  if byte = 0x41 then .slowQuoteOnOfferSide
  else if byte = 0x42 then .slowQuoteOnBidSide
  else if byte = 0x43 then .closing
  else if byte = 0x45 then .slowQuoteDueToLrpOrGapQuoteOnTheBidSide
  else if byte = 0x46 then .slowQuoteDueToLrpOrGapQuoteOnTheOfferSide
  else if byte = 0x48 then .slowQuoteOnTheBidAndOfferSides
  else if byte = 0x4C then .closedMarketMakerFinra
  else if byte = 0x4E then .nonFirmQuote
  else if byte = 0x4F then .openingQuote
  else if byte = 0x52 then .regular
  else if byte = 0x55 then .slowQuoteDueToLrpOrGapQuoteOnBothSides
  else if byte = 0x57 then .slowQuoteDueToSetSlowListOnBothSides
  else .onDemandIntraDayAuction

def ofByte (byte : UInt8) : QuoteCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : QuoteCondition) : ofByte value.toByte = value := by
  cases value with
  | slowQuoteOnOfferSide => decide
  | slowQuoteOnBidSide => decide
  | closing => decide
  | slowQuoteDueToLrpOrGapQuoteOnTheBidSide => decide
  | slowQuoteDueToLrpOrGapQuoteOnTheOfferSide => decide
  | slowQuoteOnTheBidAndOfferSides => decide
  | closedMarketMakerFinra => decide
  | nonFirmQuote => decide
  | openingQuote => decide
  | regular => decide
  | slowQuoteDueToLrpOrGapQuoteOnBothSides => decide
  | slowQuoteDueToSetSlowListOnBothSides => decide
  | onDemandIntraDayAuction => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : QuoteCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (QuoteCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : QuoteCondition) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : QuoteCondition) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : QuoteCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end QuoteCondition

/-- Retail Interest Indicator: one byte code -/
def RetailInterestIndicator.codes : List UInt8 :=
  [0x20, 0x41, 0x42, 0x43]

inductive RetailInterestIndicator where
  | retailInterestNotApplicable -- Retail Interest Not Applicable
  | retailInterestOnBidQuote -- Retail Interest On Bid Quote
  | retailInterestOnOfferQuote -- Retail Interest On Offer Quote
  | retailInterestOnBothTheBidAndOfferQuotes -- Retail Interest On Both The Bid And Offer Quotes
  | unlisted (byte : { byte : UInt8 // byte ∉ RetailInterestIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RetailInterestIndicator

def toByte : RetailInterestIndicator → UInt8
  | .retailInterestNotApplicable => 0x20
  | .retailInterestOnBidQuote => 0x41
  | .retailInterestOnOfferQuote => 0x42
  | .retailInterestOnBothTheBidAndOfferQuotes => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RetailInterestIndicator :=
  if byte = 0x20 then .retailInterestNotApplicable
  else if byte = 0x41 then .retailInterestOnBidQuote
  else if byte = 0x42 then .retailInterestOnOfferQuote
  else .retailInterestOnBothTheBidAndOfferQuotes

def ofByte (byte : UInt8) : RetailInterestIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RetailInterestIndicator) : ofByte value.toByte = value := by
  cases value with
  | retailInterestNotApplicable => decide
  | retailInterestOnBidQuote => decide
  | retailInterestOnOfferQuote => decide
  | retailInterestOnBothTheBidAndOfferQuotes => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RetailInterestIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RetailInterestIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RetailInterestIndicator) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : RetailInterestIndicator) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : RetailInterestIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RetailInterestIndicator

/-- Settlement Condition: one byte code -/
def SettlementCondition.codes : List UInt8 :=
  [0x20, 0x41, 0x42]

inductive SettlementCondition where
  | regularWaySettlement -- Regular Way Settlement
  | cashOnlySettlement -- Cash Only Settlement
  | nextDayOnlySettlement -- Next Day Only Settlement
  | unlisted (byte : { byte : UInt8 // byte ∉ SettlementCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SettlementCondition

def toByte : SettlementCondition → UInt8
  | .regularWaySettlement => 0x20
  | .cashOnlySettlement => 0x41
  | .nextDayOnlySettlement => 0x42
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SettlementCondition :=
  if byte = 0x20 then .regularWaySettlement
  else if byte = 0x41 then .cashOnlySettlement
  else .nextDayOnlySettlement

def ofByte (byte : UInt8) : SettlementCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SettlementCondition) : ofByte value.toByte = value := by
  cases value with
  | regularWaySettlement => decide
  | cashOnlySettlement => decide
  | nextDayOnlySettlement => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SettlementCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SettlementCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SettlementCondition) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SettlementCondition) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SettlementCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SettlementCondition

/-- Market Condition: one byte code -/
def MarketCondition.codes : List UInt8 :=
  [0x20, 0x41, 0x42]

inductive MarketCondition where
  | normalAuctionMarket -- Normal Auction Market
  | crossedMarket -- Crossed Market
  | lockedMarket -- Locked Market
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketCondition

def toByte : MarketCondition → UInt8
  | .normalAuctionMarket => 0x20
  | .crossedMarket => 0x41
  | .lockedMarket => 0x42
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketCondition :=
  if byte = 0x20 then .normalAuctionMarket
  else if byte = 0x41 then .crossedMarket
  else .lockedMarket

def ofByte (byte : UInt8) : MarketCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketCondition) : ofByte value.toByte = value := by
  cases value with
  | normalAuctionMarket => decide
  | crossedMarket => decide
  | lockedMarket => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarketCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketCondition) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : MarketCondition) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : MarketCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarketCondition

/-- Finra Bbo Indicator: one byte code -/
def FinraBboIndicator.codes : List UInt8 :=
  [0x20, 0x41, 0x42]

inductive FinraBboIndicator where
  | finraBboIndicatorNotApplicable -- Finra Bbo Indicator Not Applicable
  | noFinraBboChange -- No Finra Bbo Change
  | noFinraBboExists -- No Finra Bbo Exists
  | unlisted (byte : { byte : UInt8 // byte ∉ FinraBboIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace FinraBboIndicator

def toByte : FinraBboIndicator → UInt8
  | .finraBboIndicatorNotApplicable => 0x20
  | .noFinraBboChange => 0x41
  | .noFinraBboExists => 0x42
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : FinraBboIndicator :=
  if byte = 0x20 then .finraBboIndicatorNotApplicable
  else if byte = 0x41 then .noFinraBboChange
  else .noFinraBboExists

def ofByte (byte : UInt8) : FinraBboIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : FinraBboIndicator) : ofByte value.toByte = value := by
  cases value with
  | finraBboIndicatorNotApplicable => decide
  | noFinraBboChange => decide
  | noFinraBboExists => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : FinraBboIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (FinraBboIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : FinraBboIndicator) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : FinraBboIndicator) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : FinraBboIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end FinraBboIndicator

/-- Short Sale Restriction Indicator: one byte code -/
def ShortSaleRestrictionIndicator.codes : List UInt8 :=
  [0x20, 0x41, 0x43, 0x44]

inductive ShortSaleRestrictionIndicator where
  | shortSaleRestrictionNotApplicable -- Short Sale Restriction Not Applicable
  | shortSaleRestrictionActivated -- Short Sale Restriction Activated
  | shortSaleRestrictionContinued -- Short Sale Restriction Continued
  | shortSaleRestrictionDeactivated -- Short Sale Restriction Deactivated
  | unlisted (byte : { byte : UInt8 // byte ∉ ShortSaleRestrictionIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ShortSaleRestrictionIndicator

def toByte : ShortSaleRestrictionIndicator → UInt8
  | .shortSaleRestrictionNotApplicable => 0x20
  | .shortSaleRestrictionActivated => 0x41
  | .shortSaleRestrictionContinued => 0x43
  | .shortSaleRestrictionDeactivated => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ShortSaleRestrictionIndicator :=
  if byte = 0x20 then .shortSaleRestrictionNotApplicable
  else if byte = 0x41 then .shortSaleRestrictionActivated
  else if byte = 0x43 then .shortSaleRestrictionContinued
  else .shortSaleRestrictionDeactivated

def ofByte (byte : UInt8) : ShortSaleRestrictionIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ShortSaleRestrictionIndicator) : ofByte value.toByte = value := by
  cases value with
  | shortSaleRestrictionNotApplicable => decide
  | shortSaleRestrictionActivated => decide
  | shortSaleRestrictionContinued => decide
  | shortSaleRestrictionDeactivated => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ShortSaleRestrictionIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ShortSaleRestrictionIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ShortSaleRestrictionIndicator) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ShortSaleRestrictionIndicator) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ShortSaleRestrictionIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ShortSaleRestrictionIndicator

/-- Clear Prior Odd Lot Quotes: one byte code -/
def ClearPriorOddLotQuotes.codes : List UInt8 :=
  [0x20, 0x42, 0x53, 0x58]

inductive ClearPriorOddLotQuotes where
  | notApplicable -- Not Applicable
  | clearAllPreviousOddLotBids -- Clear All Previous Odd Lot Bids
  | clearAllPreviousOddLotOffers -- Clear All Previous Odd Lot Offers
  | clearAllPreviousOddLotBidsAndOffers -- Clear All Previous Odd Lot Bids And Offers
  | unlisted (byte : { byte : UInt8 // byte ∉ ClearPriorOddLotQuotes.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ClearPriorOddLotQuotes

def toByte : ClearPriorOddLotQuotes → UInt8
  | .notApplicable => 0x20
  | .clearAllPreviousOddLotBids => 0x42
  | .clearAllPreviousOddLotOffers => 0x53
  | .clearAllPreviousOddLotBidsAndOffers => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ClearPriorOddLotQuotes :=
  if byte = 0x20 then .notApplicable
  else if byte = 0x42 then .clearAllPreviousOddLotBids
  else if byte = 0x53 then .clearAllPreviousOddLotOffers
  else .clearAllPreviousOddLotBidsAndOffers

def ofByte (byte : UInt8) : ClearPriorOddLotQuotes :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ClearPriorOddLotQuotes) : ofByte value.toByte = value := by
  cases value with
  | notApplicable => decide
  | clearAllPreviousOddLotBids => decide
  | clearAllPreviousOddLotOffers => decide
  | clearAllPreviousOddLotBidsAndOffers => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ClearPriorOddLotQuotes) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ClearPriorOddLotQuotes × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ClearPriorOddLotQuotes) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ClearPriorOddLotQuotes) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ClearPriorOddLotQuotes) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ClearPriorOddLotQuotes

/-- Security Status: one byte code -/
def SecurityStatus.codes : List UInt8 :=
  [0x20, 0x32, 0x33, 0x35, 0x36, 0x37, 0x38, 0x39, 0x41, 0x43, 0x44, 0x45, 0x46]

inductive SecurityStatus where
  | securityStatusNotApplicable -- Security Status Not Applicable
  | tradingHalt -- Trading Halt
  | resume -- Resume
  | priceIndication -- Price Indication
  | tradingRangeIndication -- Trading Range Indication
  | marketImbalanceBuy -- Market Imbalance Buy
  | marketImbalanceSell -- Market Imbalance Sell
  | closingImbalanceBuy -- Closing Imbalance Buy
  | closingImbalanceSell -- Closing Imbalance Sell
  | noMarketImbalance -- No Market Imbalance
  | noClosingImbalance -- No Closing Imbalance
  | shortSaleRestriction -- Short Sale Restriction
  | limitUpLimitDownLuldReferencePrice -- Limit Up Limit Down Luld Reference Price
  | unlisted (byte : { byte : UInt8 // byte ∉ SecurityStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SecurityStatus

def toByte : SecurityStatus → UInt8
  | .securityStatusNotApplicable => 0x20
  | .tradingHalt => 0x32
  | .resume => 0x33
  | .priceIndication => 0x35
  | .tradingRangeIndication => 0x36
  | .marketImbalanceBuy => 0x37
  | .marketImbalanceSell => 0x38
  | .closingImbalanceBuy => 0x39
  | .closingImbalanceSell => 0x41
  | .noMarketImbalance => 0x43
  | .noClosingImbalance => 0x44
  | .shortSaleRestriction => 0x45
  | .limitUpLimitDownLuldReferencePrice => 0x46
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SecurityStatus :=
  if byte = 0x20 then .securityStatusNotApplicable
  else if byte = 0x32 then .tradingHalt
  else if byte = 0x33 then .resume
  else if byte = 0x35 then .priceIndication
  else if byte = 0x36 then .tradingRangeIndication
  else if byte = 0x37 then .marketImbalanceBuy
  else if byte = 0x38 then .marketImbalanceSell
  else if byte = 0x39 then .closingImbalanceBuy
  else if byte = 0x41 then .closingImbalanceSell
  else if byte = 0x43 then .noMarketImbalance
  else if byte = 0x44 then .noClosingImbalance
  else if byte = 0x45 then .shortSaleRestriction
  else .limitUpLimitDownLuldReferencePrice

def ofByte (byte : UInt8) : SecurityStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SecurityStatus) : ofByte value.toByte = value := by
  cases value with
  | securityStatusNotApplicable => decide
  | tradingHalt => decide
  | resume => decide
  | priceIndication => decide
  | tradingRangeIndication => decide
  | marketImbalanceBuy => decide
  | marketImbalanceSell => decide
  | closingImbalanceBuy => decide
  | closingImbalanceSell => decide
  | noMarketImbalance => decide
  | noClosingImbalance => decide
  | shortSaleRestriction => decide
  | limitUpLimitDownLuldReferencePrice => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SecurityStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SecurityStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SecurityStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SecurityStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SecurityStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SecurityStatus

/-- Halt Reason: one byte code -/
def HaltReason.codes : List UInt8 :=
  [0x20, 0x41, 0x43, 0x44, 0x45, 0x46, 0x49, 0x4D, 0x4E, 0x4F, 0x50, 0x56, 0x58, 0x59, 0x31, 0x32, 0x33]

inductive HaltReason where
  | haltReasonNotApplicable -- Halt Reason Not Applicable
  | additionalInformationRequested -- Additional Information Requested
  | regulatoryConcern -- Regulatory Concern
  | newsReleased -- News Released
  | mergerEffective -- Merger Effective
  | etfComponentPricesNotAvailable -- Etf Component Prices Not Available
  | orderImbalance -- Order Imbalance
  | limitUpLimitDownLuldTradingPause -- Limit Up Limit Down Luld Trading Pause
  | corporateAction -- Corporate Action
  | newSecurityOffering -- New Security Offering
  | newsPending -- News Pending
  | intradayIndicativeValueNotAvailable -- Intraday Indicative Value Not Available
  | operational -- Operational
  | subPennyTrading -- Sub Penny Trading
  | marketWideCircuitBreakerLevel1Breached -- Market Wide Circuit Breaker Level 1 Breached
  | marketWideCircuitBreakerLevel2Breached -- Market Wide Circuit Breaker Level 2 Breached
  | marketWideCircuitBreakerLevel3Breached -- Market Wide Circuit Breaker Level 3 Breached
  | unlisted (byte : { byte : UInt8 // byte ∉ HaltReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace HaltReason

def toByte : HaltReason → UInt8
  | .haltReasonNotApplicable => 0x20
  | .additionalInformationRequested => 0x41
  | .regulatoryConcern => 0x43
  | .newsReleased => 0x44
  | .mergerEffective => 0x45
  | .etfComponentPricesNotAvailable => 0x46
  | .orderImbalance => 0x49
  | .limitUpLimitDownLuldTradingPause => 0x4D
  | .corporateAction => 0x4E
  | .newSecurityOffering => 0x4F
  | .newsPending => 0x50
  | .intradayIndicativeValueNotAvailable => 0x56
  | .operational => 0x58
  | .subPennyTrading => 0x59
  | .marketWideCircuitBreakerLevel1Breached => 0x31
  | .marketWideCircuitBreakerLevel2Breached => 0x32
  | .marketWideCircuitBreakerLevel3Breached => 0x33
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : HaltReason :=
  if byte = 0x20 then .haltReasonNotApplicable
  else if byte = 0x41 then .additionalInformationRequested
  else if byte = 0x43 then .regulatoryConcern
  else if byte = 0x44 then .newsReleased
  else if byte = 0x45 then .mergerEffective
  else if byte = 0x46 then .etfComponentPricesNotAvailable
  else if byte = 0x49 then .orderImbalance
  else if byte = 0x4D then .limitUpLimitDownLuldTradingPause
  else if byte = 0x4E then .corporateAction
  else if byte = 0x4F then .newSecurityOffering
  else if byte = 0x50 then .newsPending
  else if byte = 0x56 then .intradayIndicativeValueNotAvailable
  else if byte = 0x58 then .operational
  else if byte = 0x59 then .subPennyTrading
  else if byte = 0x31 then .marketWideCircuitBreakerLevel1Breached
  else if byte = 0x32 then .marketWideCircuitBreakerLevel2Breached
  else .marketWideCircuitBreakerLevel3Breached

def ofByte (byte : UInt8) : HaltReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : HaltReason) : ofByte value.toByte = value := by
  cases value with
  | haltReasonNotApplicable => decide
  | additionalInformationRequested => decide
  | regulatoryConcern => decide
  | newsReleased => decide
  | mergerEffective => decide
  | etfComponentPricesNotAvailable => decide
  | orderImbalance => decide
  | limitUpLimitDownLuldTradingPause => decide
  | corporateAction => decide
  | newSecurityOffering => decide
  | newsPending => decide
  | intradayIndicativeValueNotAvailable => decide
  | operational => decide
  | subPennyTrading => decide
  | marketWideCircuitBreakerLevel1Breached => decide
  | marketWideCircuitBreakerLevel2Breached => decide
  | marketWideCircuitBreakerLevel3Breached => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : HaltReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (HaltReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : HaltReason) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : HaltReason) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : HaltReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end HaltReason

/-- Timestamp 1: 8 bytes -/
structure Timestamp1 where
  seconds : BitVec 32
  nanoseconds : BitVec 32
  deriving DecidableEq, Repr

namespace Timestamp1

def encode (message : Timestamp1) : List UInt8 :=
  encodeUInt 4 message.seconds
    ++ (encodeUInt 4 message.nanoseconds)

def decode (bytes : List UInt8) : Option (Timestamp1 × List UInt8) := do
  let (seconds, bytes) ← decodeUInt 4 bytes
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  pure ({ seconds, nanoseconds }, bytes)

@[simp] theorem encode_length (message : Timestamp1) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : Timestamp1) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Timestamp1) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end Timestamp1

/-- Rejection Message: 14 bytes -/
structure RejectionMessage where
  errorCode : BitVec 8
  blockSequenceNumber : BitVec 32
  participantReferenceNumber : BitVec 64
  messageId : BitVec 8
  deriving DecidableEq, Repr

namespace RejectionMessage

def encode (message : RejectionMessage) : List UInt8 :=
  encodeUInt 1 message.errorCode
    ++ (encodeUInt 4 message.blockSequenceNumber
    ++ (encodeUInt 8 message.participantReferenceNumber
    ++ (encodeUInt 1 message.messageId)))

def decode (bytes : List UInt8) : Option (RejectionMessage × List UInt8) := do
  let (errorCode, bytes) ← decodeUInt 1 bytes
  let (blockSequenceNumber, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  pure ({ errorCode, blockSequenceNumber, participantReferenceNumber, messageId }, bytes)

@[simp] theorem encode_length (message : RejectionMessage) : (encode message).length = 14 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : RejectionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RejectionMessage) (rest : List UInt8) :
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

end RejectionMessage

/-- Partial Reject Odd Lot Bid Short Quote Appendage: 3 bytes -/
structure PartialRejectOddLotBidShortQuoteAppendage where
  oddLotQuotePrice2 : BitVec 16
  oddLotQuoteSize : BitVec 8
  deriving DecidableEq, Repr

namespace PartialRejectOddLotBidShortQuoteAppendage

def encode (message : PartialRejectOddLotBidShortQuoteAppendage) : List UInt8 :=
  encodeUInt 2 message.oddLotQuotePrice2
    ++ (encodeUInt 1 message.oddLotQuoteSize)

def decode (bytes : List UInt8) : Option (PartialRejectOddLotBidShortQuoteAppendage × List UInt8) := do
  let (oddLotQuotePrice2, bytes) ← decodeUInt 2 bytes
  let (oddLotQuoteSize, bytes) ← decodeUInt 1 bytes
  pure ({ oddLotQuotePrice2, oddLotQuoteSize }, bytes)

@[simp] theorem encode_length (message : PartialRejectOddLotBidShortQuoteAppendage) : (encode message).length = 3 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : PartialRejectOddLotBidShortQuoteAppendage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PartialRejectOddLotBidShortQuoteAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end PartialRejectOddLotBidShortQuoteAppendage

/-- Partial Reject Odd Lot Offer Short Quote Appendage: 3 bytes -/
structure PartialRejectOddLotOfferShortQuoteAppendage where
  oddLotQuotePrice2 : BitVec 16
  oddLotQuoteSize : BitVec 8
  deriving DecidableEq, Repr

namespace PartialRejectOddLotOfferShortQuoteAppendage

def encode (message : PartialRejectOddLotOfferShortQuoteAppendage) : List UInt8 :=
  encodeUInt 2 message.oddLotQuotePrice2
    ++ (encodeUInt 1 message.oddLotQuoteSize)

def decode (bytes : List UInt8) : Option (PartialRejectOddLotOfferShortQuoteAppendage × List UInt8) := do
  let (oddLotQuotePrice2, bytes) ← decodeUInt 2 bytes
  let (oddLotQuoteSize, bytes) ← decodeUInt 1 bytes
  pure ({ oddLotQuotePrice2, oddLotQuoteSize }, bytes)

@[simp] theorem encode_length (message : PartialRejectOddLotOfferShortQuoteAppendage) : (encode message).length = 3 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : PartialRejectOddLotOfferShortQuoteAppendage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PartialRejectOddLotOfferShortQuoteAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end PartialRejectOddLotOfferShortQuoteAppendage

/-- Partial Reject Odd Lot Bid Short Quote Appendage: 6 bytes -/
structure PartialRejectOddLotBidShortQuoteAppendagePartialRejectOddLotOfferShortQuoteAppendage where
  partialRejectOddLotBidShortQuoteAppendage : PartialRejectOddLotBidShortQuoteAppendage
  partialRejectOddLotOfferShortQuoteAppendage : PartialRejectOddLotOfferShortQuoteAppendage
  deriving DecidableEq, Repr

namespace PartialRejectOddLotBidShortQuoteAppendagePartialRejectOddLotOfferShortQuoteAppendage

def encode (message : PartialRejectOddLotBidShortQuoteAppendagePartialRejectOddLotOfferShortQuoteAppendage) : List UInt8 :=
  PartialRejectOddLotBidShortQuoteAppendage.encode message.partialRejectOddLotBidShortQuoteAppendage
    ++ (PartialRejectOddLotOfferShortQuoteAppendage.encode message.partialRejectOddLotOfferShortQuoteAppendage)

def decode (bytes : List UInt8) : Option (PartialRejectOddLotBidShortQuoteAppendagePartialRejectOddLotOfferShortQuoteAppendage × List UInt8) := do
  let (partialRejectOddLotBidShortQuoteAppendage, bytes) ← PartialRejectOddLotBidShortQuoteAppendage.decode bytes
  let (partialRejectOddLotOfferShortQuoteAppendage, bytes) ← PartialRejectOddLotOfferShortQuoteAppendage.decode bytes
  pure ({ partialRejectOddLotBidShortQuoteAppendage, partialRejectOddLotOfferShortQuoteAppendage }, bytes)

@[simp] theorem encode_length (message : PartialRejectOddLotBidShortQuoteAppendagePartialRejectOddLotOfferShortQuoteAppendage) : (encode message).length = 6 := by
  unfold encode
  simp only [List.length_append, PartialRejectOddLotBidShortQuoteAppendage.encode_length, PartialRejectOddLotOfferShortQuoteAppendage.encode_length]

theorem encode_length_pos (message : PartialRejectOddLotBidShortQuoteAppendagePartialRejectOddLotOfferShortQuoteAppendage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PartialRejectOddLotBidShortQuoteAppendagePartialRejectOddLotOfferShortQuoteAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, PartialRejectOddLotBidShortQuoteAppendage.decode_encode, some_bind]
  dsimp only
  rw [PartialRejectOddLotOfferShortQuoteAppendage.decode_encode, some_bind]
  rfl

end PartialRejectOddLotBidShortQuoteAppendagePartialRejectOddLotOfferShortQuoteAppendage

/-- Partial Reject Odd Lot Bid Long Quote Appendage: 9 bytes -/
structure PartialRejectOddLotBidLongQuoteAppendage where
  oddLotQuotePrice : BitVec 64
  oddLotQuoteSize : BitVec 8
  deriving DecidableEq, Repr

namespace PartialRejectOddLotBidLongQuoteAppendage

def encode (message : PartialRejectOddLotBidLongQuoteAppendage) : List UInt8 :=
  encodeUInt 8 message.oddLotQuotePrice
    ++ (encodeUInt 1 message.oddLotQuoteSize)

def decode (bytes : List UInt8) : Option (PartialRejectOddLotBidLongQuoteAppendage × List UInt8) := do
  let (oddLotQuotePrice, bytes) ← decodeUInt 8 bytes
  let (oddLotQuoteSize, bytes) ← decodeUInt 1 bytes
  pure ({ oddLotQuotePrice, oddLotQuoteSize }, bytes)

@[simp] theorem encode_length (message : PartialRejectOddLotBidLongQuoteAppendage) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : PartialRejectOddLotBidLongQuoteAppendage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PartialRejectOddLotBidLongQuoteAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end PartialRejectOddLotBidLongQuoteAppendage

/-- Partial Reject Odd Lot Offer Long Quote Appendage: 9 bytes -/
structure PartialRejectOddLotOfferLongQuoteAppendage where
  oddLotQuotePrice : BitVec 64
  oddLotQuoteSize : BitVec 8
  deriving DecidableEq, Repr

namespace PartialRejectOddLotOfferLongQuoteAppendage

def encode (message : PartialRejectOddLotOfferLongQuoteAppendage) : List UInt8 :=
  encodeUInt 8 message.oddLotQuotePrice
    ++ (encodeUInt 1 message.oddLotQuoteSize)

def decode (bytes : List UInt8) : Option (PartialRejectOddLotOfferLongQuoteAppendage × List UInt8) := do
  let (oddLotQuotePrice, bytes) ← decodeUInt 8 bytes
  let (oddLotQuoteSize, bytes) ← decodeUInt 1 bytes
  pure ({ oddLotQuotePrice, oddLotQuoteSize }, bytes)

@[simp] theorem encode_length (message : PartialRejectOddLotOfferLongQuoteAppendage) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : PartialRejectOddLotOfferLongQuoteAppendage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PartialRejectOddLotOfferLongQuoteAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end PartialRejectOddLotOfferLongQuoteAppendage

/-- Partial Reject Odd Lot Bid Long Quote Appendage: 18 bytes -/
structure PartialRejectOddLotBidLongQuoteAppendagePartialRejectOddLotOfferLongQuoteAppendage where
  partialRejectOddLotBidLongQuoteAppendage : PartialRejectOddLotBidLongQuoteAppendage
  partialRejectOddLotOfferLongQuoteAppendage : PartialRejectOddLotOfferLongQuoteAppendage
  deriving DecidableEq, Repr

namespace PartialRejectOddLotBidLongQuoteAppendagePartialRejectOddLotOfferLongQuoteAppendage

def encode (message : PartialRejectOddLotBidLongQuoteAppendagePartialRejectOddLotOfferLongQuoteAppendage) : List UInt8 :=
  PartialRejectOddLotBidLongQuoteAppendage.encode message.partialRejectOddLotBidLongQuoteAppendage
    ++ (PartialRejectOddLotOfferLongQuoteAppendage.encode message.partialRejectOddLotOfferLongQuoteAppendage)

def decode (bytes : List UInt8) : Option (PartialRejectOddLotBidLongQuoteAppendagePartialRejectOddLotOfferLongQuoteAppendage × List UInt8) := do
  let (partialRejectOddLotBidLongQuoteAppendage, bytes) ← PartialRejectOddLotBidLongQuoteAppendage.decode bytes
  let (partialRejectOddLotOfferLongQuoteAppendage, bytes) ← PartialRejectOddLotOfferLongQuoteAppendage.decode bytes
  pure ({ partialRejectOddLotBidLongQuoteAppendage, partialRejectOddLotOfferLongQuoteAppendage }, bytes)

@[simp] theorem encode_length (message : PartialRejectOddLotBidLongQuoteAppendagePartialRejectOddLotOfferLongQuoteAppendage) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, PartialRejectOddLotBidLongQuoteAppendage.encode_length, PartialRejectOddLotOfferLongQuoteAppendage.encode_length]

theorem encode_length_pos (message : PartialRejectOddLotBidLongQuoteAppendagePartialRejectOddLotOfferLongQuoteAppendage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PartialRejectOddLotBidLongQuoteAppendagePartialRejectOddLotOfferLongQuoteAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, PartialRejectOddLotBidLongQuoteAppendage.decode_encode, some_bind]
  dsimp only
  rw [PartialRejectOddLotOfferLongQuoteAppendage.decode_encode, some_bind]
  rfl

end PartialRejectOddLotBidLongQuoteAppendagePartialRejectOddLotOfferLongQuoteAppendage

/-- Partial Reject Odd Lot Bid Extended Quote Appendage: 13 bytes -/
structure PartialRejectOddLotBidExtendedQuoteAppendage where
  oddLotQuotePrice : BitVec 64
  oddLotQuoteSize : BitVec 8
  oddLotFinraMarketMakerId : Alpha 4
  deriving DecidableEq, Repr

namespace PartialRejectOddLotBidExtendedQuoteAppendage

def encode (message : PartialRejectOddLotBidExtendedQuoteAppendage) : List UInt8 :=
  encodeUInt 8 message.oddLotQuotePrice
    ++ (encodeUInt 1 message.oddLotQuoteSize
    ++ (Alpha.encode message.oddLotFinraMarketMakerId))

def decode (bytes : List UInt8) : Option (PartialRejectOddLotBidExtendedQuoteAppendage × List UInt8) := do
  let (oddLotQuotePrice, bytes) ← decodeUInt 8 bytes
  let (oddLotQuoteSize, bytes) ← decodeUInt 1 bytes
  let (oddLotFinraMarketMakerId, bytes) ← Alpha.decode 4 bytes
  pure ({ oddLotQuotePrice, oddLotQuoteSize, oddLotFinraMarketMakerId }, bytes)

@[simp] theorem encode_length (message : PartialRejectOddLotBidExtendedQuoteAppendage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : PartialRejectOddLotBidExtendedQuoteAppendage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PartialRejectOddLotBidExtendedQuoteAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end PartialRejectOddLotBidExtendedQuoteAppendage

/-- Partial Reject Odd Lot Offer Extended Quote Appendage: 13 bytes -/
structure PartialRejectOddLotOfferExtendedQuoteAppendage where
  oddLotQuotePrice : BitVec 64
  oddLotQuoteSize : BitVec 8
  oddLotFinraMarketMakerId : Alpha 4
  deriving DecidableEq, Repr

namespace PartialRejectOddLotOfferExtendedQuoteAppendage

def encode (message : PartialRejectOddLotOfferExtendedQuoteAppendage) : List UInt8 :=
  encodeUInt 8 message.oddLotQuotePrice
    ++ (encodeUInt 1 message.oddLotQuoteSize
    ++ (Alpha.encode message.oddLotFinraMarketMakerId))

def decode (bytes : List UInt8) : Option (PartialRejectOddLotOfferExtendedQuoteAppendage × List UInt8) := do
  let (oddLotQuotePrice, bytes) ← decodeUInt 8 bytes
  let (oddLotQuoteSize, bytes) ← decodeUInt 1 bytes
  let (oddLotFinraMarketMakerId, bytes) ← Alpha.decode 4 bytes
  pure ({ oddLotQuotePrice, oddLotQuoteSize, oddLotFinraMarketMakerId }, bytes)

@[simp] theorem encode_length (message : PartialRejectOddLotOfferExtendedQuoteAppendage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : PartialRejectOddLotOfferExtendedQuoteAppendage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PartialRejectOddLotOfferExtendedQuoteAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end PartialRejectOddLotOfferExtendedQuoteAppendage

/-- Partial Reject Odd Lot Bid Extended Quote Appendage: 26 bytes -/
structure PartialRejectOddLotBidExtendedQuoteAppendagePartialRejectOddLotOfferExtendedQuoteAppendage where
  partialRejectOddLotBidExtendedQuoteAppendage : PartialRejectOddLotBidExtendedQuoteAppendage
  partialRejectOddLotOfferExtendedQuoteAppendage : PartialRejectOddLotOfferExtendedQuoteAppendage
  deriving DecidableEq, Repr

namespace PartialRejectOddLotBidExtendedQuoteAppendagePartialRejectOddLotOfferExtendedQuoteAppendage

def encode (message : PartialRejectOddLotBidExtendedQuoteAppendagePartialRejectOddLotOfferExtendedQuoteAppendage) : List UInt8 :=
  PartialRejectOddLotBidExtendedQuoteAppendage.encode message.partialRejectOddLotBidExtendedQuoteAppendage
    ++ (PartialRejectOddLotOfferExtendedQuoteAppendage.encode message.partialRejectOddLotOfferExtendedQuoteAppendage)

def decode (bytes : List UInt8) : Option (PartialRejectOddLotBidExtendedQuoteAppendagePartialRejectOddLotOfferExtendedQuoteAppendage × List UInt8) := do
  let (partialRejectOddLotBidExtendedQuoteAppendage, bytes) ← PartialRejectOddLotBidExtendedQuoteAppendage.decode bytes
  let (partialRejectOddLotOfferExtendedQuoteAppendage, bytes) ← PartialRejectOddLotOfferExtendedQuoteAppendage.decode bytes
  pure ({ partialRejectOddLotBidExtendedQuoteAppendage, partialRejectOddLotOfferExtendedQuoteAppendage }, bytes)

@[simp] theorem encode_length (message : PartialRejectOddLotBidExtendedQuoteAppendagePartialRejectOddLotOfferExtendedQuoteAppendage) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, PartialRejectOddLotBidExtendedQuoteAppendage.encode_length, PartialRejectOddLotOfferExtendedQuoteAppendage.encode_length]

theorem encode_length_pos (message : PartialRejectOddLotBidExtendedQuoteAppendagePartialRejectOddLotOfferExtendedQuoteAppendage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PartialRejectOddLotBidExtendedQuoteAppendagePartialRejectOddLotOfferExtendedQuoteAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, PartialRejectOddLotBidExtendedQuoteAppendage.decode_encode, some_bind]
  dsimp only
  rw [PartialRejectOddLotOfferExtendedQuoteAppendage.decode_encode, some_bind]
  rfl

end PartialRejectOddLotBidExtendedQuoteAppendagePartialRejectOddLotOfferExtendedQuoteAppendage

/-- The Partial Reject Odd Lot Bid Short Quote Appendage or Partial Reject Odd Lot Offer Short Quote Appendage or Partial Reject Odd Lot Bid Long Quote Appendage or Partial Reject Odd Lot Offer Long Quote Appendage or Partial Reject Odd Lot Bid Extended Quote Appendage or Partial Reject Odd Lot Offer Extended Quote Appendage the Odd Lot Quote Appendage Type says is attached, or none -/
inductive OddLotQuoteAppendageTypeChoice where
  | partialRejectOddLotBidShortQuoteAppendagePartialRejectOddLotOfferShortQuoteAppendage (message : PartialRejectOddLotBidShortQuoteAppendagePartialRejectOddLotOfferShortQuoteAppendage) -- "S" 0x53
  | partialRejectOddLotBidLongQuoteAppendagePartialRejectOddLotOfferLongQuoteAppendage (message : PartialRejectOddLotBidLongQuoteAppendagePartialRejectOddLotOfferLongQuoteAppendage) -- "L" 0x4C
  | partialRejectOddLotBidExtendedQuoteAppendagePartialRejectOddLotOfferExtendedQuoteAppendage (message : PartialRejectOddLotBidExtendedQuoteAppendagePartialRejectOddLotOfferExtendedQuoteAppendage) -- "E" 0x45
  | absent (tag : { v : BitVec 8 // v ≠ 83 ∧ v ≠ 76 ∧ v ≠ 69 }) -- any other value, read as nothing
  deriving DecidableEq, Repr

namespace OddLotQuoteAppendageTypeChoice

/-- The Odd Lot Quote Appendage Type each message is sent under -/
def tag : OddLotQuoteAppendageTypeChoice → BitVec 8
  | .partialRejectOddLotBidShortQuoteAppendagePartialRejectOddLotOfferShortQuoteAppendage _ => 83
  | .partialRejectOddLotBidLongQuoteAppendagePartialRejectOddLotOfferLongQuoteAppendage _ => 76
  | .partialRejectOddLotBidExtendedQuoteAppendagePartialRejectOddLotOfferExtendedQuoteAppendage _ => 69
  | .absent tag => tag.val

def encode : OddLotQuoteAppendageTypeChoice → List UInt8
  | .partialRejectOddLotBidShortQuoteAppendagePartialRejectOddLotOfferShortQuoteAppendage message => PartialRejectOddLotBidShortQuoteAppendagePartialRejectOddLotOfferShortQuoteAppendage.encode message
  | .partialRejectOddLotBidLongQuoteAppendagePartialRejectOddLotOfferLongQuoteAppendage message => PartialRejectOddLotBidLongQuoteAppendagePartialRejectOddLotOfferLongQuoteAppendage.encode message
  | .partialRejectOddLotBidExtendedQuoteAppendagePartialRejectOddLotOfferExtendedQuoteAppendage message => PartialRejectOddLotBidExtendedQuoteAppendagePartialRejectOddLotOfferExtendedQuoteAppendage.encode message
  | .absent _ => []

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : OddLotQuoteAppendageTypeChoice) : (encode message).length ≤ 26 := by
  cases message with
  | partialRejectOddLotBidShortQuoteAppendagePartialRejectOddLotOfferShortQuoteAppendage inner =>
    simp only [encode, PartialRejectOddLotBidShortQuoteAppendagePartialRejectOddLotOfferShortQuoteAppendage.encode_length]
    omega
  | partialRejectOddLotBidLongQuoteAppendagePartialRejectOddLotOfferLongQuoteAppendage inner =>
    simp only [encode, PartialRejectOddLotBidLongQuoteAppendagePartialRejectOddLotOfferLongQuoteAppendage.encode_length]
    omega
  | partialRejectOddLotBidExtendedQuoteAppendagePartialRejectOddLotOfferExtendedQuoteAppendage inner =>
    simp only [encode, PartialRejectOddLotBidExtendedQuoteAppendagePartialRejectOddLotOfferExtendedQuoteAppendage.encode_length]
    omega
  | absent _ =>
    simp only [encode, List.length_nil]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (OddLotQuoteAppendageTypeChoice × List UInt8) :=
  if h0 : tag = 83 then (PartialRejectOddLotBidShortQuoteAppendagePartialRejectOddLotOfferShortQuoteAppendage.decode bytes).map fun (message, rest) => (.partialRejectOddLotBidShortQuoteAppendagePartialRejectOddLotOfferShortQuoteAppendage message, rest)
  else if h1 : tag = 76 then (PartialRejectOddLotBidLongQuoteAppendagePartialRejectOddLotOfferLongQuoteAppendage.decode bytes).map fun (message, rest) => (.partialRejectOddLotBidLongQuoteAppendagePartialRejectOddLotOfferLongQuoteAppendage message, rest)
  else if h2 : tag = 69 then (PartialRejectOddLotBidExtendedQuoteAppendagePartialRejectOddLotOfferExtendedQuoteAppendage.decode bytes).map fun (message, rest) => (.partialRejectOddLotBidExtendedQuoteAppendagePartialRejectOddLotOfferExtendedQuoteAppendage message, rest)
  else some (.absent ⟨tag, h0, h1, h2⟩, bytes)

@[simp] theorem decode_encode (message : OddLotQuoteAppendageTypeChoice) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message with
  | partialRejectOddLotBidShortQuoteAppendagePartialRejectOddLotOfferShortQuoteAppendage m => simp [decode, encode, tag]
  | partialRejectOddLotBidLongQuoteAppendagePartialRejectOddLotOfferLongQuoteAppendage m => simp [decode, encode, tag]
  | partialRejectOddLotBidExtendedQuoteAppendagePartialRejectOddLotOfferExtendedQuoteAppendage m => simp [decode, encode, tag]
  | absent t =>
    obtain ⟨v, h0, h1, h2⟩ := t
    simp only [tag, encode, decode, h0, h1, h2, List.nil_append, reduceDIte]

end OddLotQuoteAppendageTypeChoice

/-- Partial Rejection Message -/
structure PartialRejectionMessage where
  errorCode : BitVec 8
  blockSequenceNumber : BitVec 32
  participantReferenceNumber : BitVec 64
  messageId : BitVec 8
  countOfOddLotBidAppendages : BitVec 8
  countOfOddLotOfferAppendages : BitVec 8
  oddLotQuoteAppendageTypeChoice : OddLotQuoteAppendageTypeChoice
  deriving DecidableEq, Repr

namespace PartialRejectionMessage

def encode (message : PartialRejectionMessage) : List UInt8 :=
  encodeUInt 1 message.errorCode
    ++ (encodeUInt 4 message.blockSequenceNumber
    ++ (encodeUInt 8 message.participantReferenceNumber
    ++ (encodeUInt 1 message.messageId
    ++ (encodeUInt 1 (OddLotQuoteAppendageTypeChoice.tag message.oddLotQuoteAppendageTypeChoice)
    ++ (encodeUInt 1 message.countOfOddLotBidAppendages
    ++ (encodeUInt 1 message.countOfOddLotOfferAppendages
    ++ (OddLotQuoteAppendageTypeChoice.encode message.oddLotQuoteAppendageTypeChoice)))))))

def decode (bytes : List UInt8) : Option (PartialRejectionMessage × List UInt8) := do
  let (errorCode, bytes) ← decodeUInt 1 bytes
  let (blockSequenceNumber, bytes) ← decodeUInt 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (oddLotQuoteAppendageType, bytes) ← decodeUInt 1 bytes
  let (countOfOddLotBidAppendages, bytes) ← decodeUInt 1 bytes
  let (countOfOddLotOfferAppendages, bytes) ← decodeUInt 1 bytes
  let (oddLotQuoteAppendageTypeChoice, bytes) ← OddLotQuoteAppendageTypeChoice.decode oddLotQuoteAppendageType bytes
  pure ({ errorCode, blockSequenceNumber, participantReferenceNumber, messageId, countOfOddLotBidAppendages, countOfOddLotOfferAppendages, oddLotQuoteAppendageTypeChoice }, bytes)

theorem encode_length_pos (message : PartialRejectionMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : PartialRejectionMessage) : (encode message).length ≤ 43 := by
  unfold encode
  cases message.oddLotQuoteAppendageTypeChoice with
  | partialRejectOddLotBidShortQuoteAppendagePartialRejectOddLotOfferShortQuoteAppendage inner =>
    simp only [OddLotQuoteAppendageTypeChoice.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, PartialRejectOddLotBidShortQuoteAppendagePartialRejectOddLotOfferShortQuoteAppendage.encode_length]
    omega
  | partialRejectOddLotBidLongQuoteAppendagePartialRejectOddLotOfferLongQuoteAppendage inner =>
    simp only [OddLotQuoteAppendageTypeChoice.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, PartialRejectOddLotBidLongQuoteAppendagePartialRejectOddLotOfferLongQuoteAppendage.encode_length]
    omega
  | partialRejectOddLotBidExtendedQuoteAppendagePartialRejectOddLotOfferExtendedQuoteAppendage inner =>
    simp only [OddLotQuoteAppendageTypeChoice.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, PartialRejectOddLotBidExtendedQuoteAppendagePartialRejectOddLotOfferExtendedQuoteAppendage.encode_length]
    omega
  | absent _ =>
    simp only [OddLotQuoteAppendageTypeChoice.encode, List.length_nil, List.length_append, ← Nat.add_assoc, encodeUInt_length]
    omega

@[simp] theorem decode_encode (message : PartialRejectionMessage) (rest : List UInt8) :
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
  rw [OddLotQuoteAppendageTypeChoice.decode_encode, some_bind]
  rfl

end PartialRejectionMessage

/-- Warning Message: 12 bytes -/
structure WarningMessage where
  previousBlockSequenceNumber : BitVec 32
  previousParticipantReferenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace WarningMessage

def encode (message : WarningMessage) : List UInt8 :=
  encodeUInt 4 message.previousBlockSequenceNumber
    ++ (encodeUInt 8 message.previousParticipantReferenceNumber)

def decode (bytes : List UInt8) : Option (WarningMessage × List UInt8) := do
  let (previousBlockSequenceNumber, bytes) ← decodeUInt 4 bytes
  let (previousParticipantReferenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ previousBlockSequenceNumber, previousParticipantReferenceNumber }, bytes)

@[simp] theorem encode_length (message : WarningMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : WarningMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : WarningMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end WarningMessage

/-- Any Administrative Message Payload, selected by Administrative Message Type -/
inductive AdministrativeMessagePayload where
  | rejectionMessage (message : RejectionMessage) -- "R" 0x52
  | partialRejectionMessage (message : PartialRejectionMessage) -- "P" 0x50
  | warningMessage (message : WarningMessage) -- "W" 0x57
  deriving DecidableEq, Repr

namespace AdministrativeMessagePayload

/-- The Administrative Message Type each message is sent under -/
def tag : AdministrativeMessagePayload → BitVec 8
  | .rejectionMessage _ => 82
  | .partialRejectionMessage _ => 80
  | .warningMessage _ => 87

def encode : AdministrativeMessagePayload → List UInt8
  | .rejectionMessage message => RejectionMessage.encode message
  | .partialRejectionMessage message => PartialRejectionMessage.encode message
  | .warningMessage message => WarningMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : AdministrativeMessagePayload) : (encode message).length ≤ 43 := by
  cases message with
  | rejectionMessage inner =>
    simp only [encode, RejectionMessage.encode_length]
    omega
  | partialRejectionMessage inner =>
    have bound_inner := PartialRejectionMessage.encode_length_le inner
    simp only [encode]
    omega
  | warningMessage inner =>
    simp only [encode, WarningMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (AdministrativeMessagePayload × List UInt8) :=
  if tag = 82 then (RejectionMessage.decode bytes).map fun (message, rest) => (.rejectionMessage message, rest)
  else if tag = 80 then (PartialRejectionMessage.decode bytes).map fun (message, rest) => (.partialRejectionMessage message, rest)
  else if tag = 87 then (WarningMessage.decode bytes).map fun (message, rest) => (.warningMessage message, rest)
  else none

@[simp] theorem decode_encode (message : AdministrativeMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end AdministrativeMessagePayload

/-- Administrative Message -/
structure AdministrativeMessage where
  administrativeMessagePayload : AdministrativeMessagePayload
  deriving DecidableEq, Repr

namespace AdministrativeMessage

def encode (message : AdministrativeMessage) : List UInt8 :=
  encodeUInt 1 (AdministrativeMessagePayload.tag message.administrativeMessagePayload)
    ++ (AdministrativeMessagePayload.encode message.administrativeMessagePayload)

def decode (bytes : List UInt8) : Option (AdministrativeMessage × List UInt8) := do
  let (administrativeMessageType, bytes) ← decodeUInt 1 bytes
  let (administrativeMessagePayload, bytes) ← AdministrativeMessagePayload.decode administrativeMessageType bytes
  pure ({ administrativeMessagePayload }, bytes)

theorem encode_length_pos (message : AdministrativeMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : AdministrativeMessage) : (encode message).length ≤ 44 := by
  unfold encode
  cases message.administrativeMessagePayload with
  | rejectionMessage inner =>
    simp only [AdministrativeMessagePayload.encode, List.length_append, encodeUInt_length, RejectionMessage.encode_length]
    omega
  | partialRejectionMessage inner =>
    have bound_inner := PartialRejectionMessage.encode_length_le inner
    simp only [AdministrativeMessagePayload.encode, List.length_append, encodeUInt_length]
    omega
  | warningMessage inner =>
    simp only [AdministrativeMessagePayload.encode, List.length_append, encodeUInt_length, WarningMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : AdministrativeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [AdministrativeMessagePayload.decode_encode, some_bind]
  rfl

end AdministrativeMessage

/-- Start Of Day Message: 0 bytes -/
structure StartOfDayMessage where
  deriving DecidableEq, Repr

namespace StartOfDayMessage

def encode (_ : StartOfDayMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (StartOfDayMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : StartOfDayMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : StartOfDayMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end StartOfDayMessage

/-- Finra Close Message: 0 bytes -/
structure FinraCloseMessage where
  deriving DecidableEq, Repr

namespace FinraCloseMessage

def encode (_ : FinraCloseMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (FinraCloseMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : FinraCloseMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : FinraCloseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end FinraCloseMessage

/-- Sequence Information And Message Count Inquiry Message: 0 bytes -/
structure SequenceInformationAndMessageCountInquiryMessage where
  deriving DecidableEq, Repr

namespace SequenceInformationAndMessageCountInquiryMessage

def encode (_ : SequenceInformationAndMessageCountInquiryMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (SequenceInformationAndMessageCountInquiryMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : SequenceInformationAndMessageCountInquiryMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : SequenceInformationAndMessageCountInquiryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end SequenceInformationAndMessageCountInquiryMessage

/-- Sequence Information And Message Count Response Message: 20 bytes -/
structure SequenceInformationAndMessageCountResponseMessage where
  currentBlockSequenceNumber : BitVec 32
  lastParticipantReferenceNumber : BitVec 64
  messageCount : BitVec 64
  deriving DecidableEq, Repr

namespace SequenceInformationAndMessageCountResponseMessage

def encode (message : SequenceInformationAndMessageCountResponseMessage) : List UInt8 :=
  encodeUInt 4 message.currentBlockSequenceNumber
    ++ (encodeUInt 8 message.lastParticipantReferenceNumber
    ++ (encodeUInt 8 message.messageCount))

def decode (bytes : List UInt8) : Option (SequenceInformationAndMessageCountResponseMessage × List UInt8) := do
  let (currentBlockSequenceNumber, bytes) ← decodeUInt 4 bytes
  let (lastParticipantReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (messageCount, bytes) ← decodeUInt 8 bytes
  pure ({ currentBlockSequenceNumber, lastParticipantReferenceNumber, messageCount }, bytes)

@[simp] theorem encode_length (message : SequenceInformationAndMessageCountResponseMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : SequenceInformationAndMessageCountResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SequenceInformationAndMessageCountResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SequenceInformationAndMessageCountResponseMessage

/-- Finra Open Message: 0 bytes -/
structure FinraOpenMessage where
  deriving DecidableEq, Repr

namespace FinraOpenMessage

def encode (_ : FinraOpenMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (FinraOpenMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : FinraOpenMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : FinraOpenMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end FinraOpenMessage

/-- Odd Lot Refresh Request Message: 30 bytes -/
structure OddLotRefreshRequestMessage where
  securitySymbolBeginRange : Alpha 11
  securitySymbolEndRange : Alpha 11
  reserved8 : Alpha 8
  deriving DecidableEq, Repr

namespace OddLotRefreshRequestMessage

def encode (message : OddLotRefreshRequestMessage) : List UInt8 :=
  Alpha.encode message.securitySymbolBeginRange
    ++ (Alpha.encode message.securitySymbolEndRange
    ++ (Alpha.encode message.reserved8))

def decode (bytes : List UInt8) : Option (OddLotRefreshRequestMessage × List UInt8) := do
  let (securitySymbolBeginRange, bytes) ← Alpha.decode 11 bytes
  let (securitySymbolEndRange, bytes) ← Alpha.decode 11 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  pure ({ securitySymbolBeginRange, securitySymbolEndRange, reserved8 }, bytes)

@[simp] theorem encode_length (message : OddLotRefreshRequestMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : OddLotRefreshRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OddLotRefreshRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OddLotRefreshRequestMessage

/-- Line Integrity Message: 0 bytes -/
structure LineIntegrityMessage where
  deriving DecidableEq, Repr

namespace LineIntegrityMessage

def encode (_ : LineIntegrityMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (LineIntegrityMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : LineIntegrityMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : LineIntegrityMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end LineIntegrityMessage

/-- End Of Day Message: 0 bytes -/
structure EndOfDayMessage where
  deriving DecidableEq, Repr

namespace EndOfDayMessage

def encode (_ : EndOfDayMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (EndOfDayMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : EndOfDayMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : EndOfDayMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end EndOfDayMessage

/-- Test Message: 256 bytes -/
structure TestMessage where
  data : Alpha 256
  deriving DecidableEq, Repr

namespace TestMessage

def encode (message : TestMessage) : List UInt8 :=
  Alpha.encode message.data

def decode (bytes : List UInt8) : Option (TestMessage × List UInt8) := do
  let (data, bytes) ← Alpha.decode 256 bytes
  pure ({ data }, bytes)

@[simp] theorem encode_length (message : TestMessage) : (encode message).length = 256 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : TestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end TestMessage

/-- Any Control Message Payload, selected by Control Message Type -/
inductive ControlMessagePayload where
  | startOfDayMessage (message : StartOfDayMessage) -- "A" 0x41
  | finraCloseMessage (message : FinraCloseMessage) -- "C" 0x43
  | sequenceInformationAndMessageCountInquiryMessage (message : SequenceInformationAndMessageCountInquiryMessage) -- "I" 0x49
  | sequenceInformationAndMessageCountResponseMessage (message : SequenceInformationAndMessageCountResponseMessage) -- "N" 0x4E
  | finraOpenMessage (message : FinraOpenMessage) -- "O" 0x4F
  | oddLotRefreshRequestMessage (message : OddLotRefreshRequestMessage) -- "R" 0x52
  | lineIntegrityMessage (message : LineIntegrityMessage) -- "T" 0x54
  | endOfDayMessage (message : EndOfDayMessage) -- "Z" 0x5A
  | testMessage (message : TestMessage) -- "5" 0x35
  deriving DecidableEq, Repr

namespace ControlMessagePayload

/-- The Control Message Type each message is sent under -/
def tag : ControlMessagePayload → BitVec 8
  | .startOfDayMessage _ => 65
  | .finraCloseMessage _ => 67
  | .sequenceInformationAndMessageCountInquiryMessage _ => 73
  | .sequenceInformationAndMessageCountResponseMessage _ => 78
  | .finraOpenMessage _ => 79
  | .oddLotRefreshRequestMessage _ => 82
  | .lineIntegrityMessage _ => 84
  | .endOfDayMessage _ => 90
  | .testMessage _ => 53

def encode : ControlMessagePayload → List UInt8
  | .startOfDayMessage message => StartOfDayMessage.encode message
  | .finraCloseMessage message => FinraCloseMessage.encode message
  | .sequenceInformationAndMessageCountInquiryMessage message => SequenceInformationAndMessageCountInquiryMessage.encode message
  | .sequenceInformationAndMessageCountResponseMessage message => SequenceInformationAndMessageCountResponseMessage.encode message
  | .finraOpenMessage message => FinraOpenMessage.encode message
  | .oddLotRefreshRequestMessage message => OddLotRefreshRequestMessage.encode message
  | .lineIntegrityMessage message => LineIntegrityMessage.encode message
  | .endOfDayMessage message => EndOfDayMessage.encode message
  | .testMessage message => TestMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ControlMessagePayload) : (encode message).length ≤ 256 := by
  cases message with
  | startOfDayMessage inner =>
    simp only [encode, StartOfDayMessage.encode_length]
    omega
  | finraCloseMessage inner =>
    simp only [encode, FinraCloseMessage.encode_length]
    omega
  | sequenceInformationAndMessageCountInquiryMessage inner =>
    simp only [encode, SequenceInformationAndMessageCountInquiryMessage.encode_length]
    omega
  | sequenceInformationAndMessageCountResponseMessage inner =>
    simp only [encode, SequenceInformationAndMessageCountResponseMessage.encode_length]
    omega
  | finraOpenMessage inner =>
    simp only [encode, FinraOpenMessage.encode_length]
    omega
  | oddLotRefreshRequestMessage inner =>
    simp only [encode, OddLotRefreshRequestMessage.encode_length]
    omega
  | lineIntegrityMessage inner =>
    simp only [encode, LineIntegrityMessage.encode_length]
    omega
  | endOfDayMessage inner =>
    simp only [encode, EndOfDayMessage.encode_length]
    omega
  | testMessage inner =>
    simp only [encode, TestMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (ControlMessagePayload × List UInt8) :=
  if tag = 65 then (StartOfDayMessage.decode bytes).map fun (message, rest) => (.startOfDayMessage message, rest)
  else if tag = 67 then (FinraCloseMessage.decode bytes).map fun (message, rest) => (.finraCloseMessage message, rest)
  else if tag = 73 then (SequenceInformationAndMessageCountInquiryMessage.decode bytes).map fun (message, rest) => (.sequenceInformationAndMessageCountInquiryMessage message, rest)
  else if tag = 78 then (SequenceInformationAndMessageCountResponseMessage.decode bytes).map fun (message, rest) => (.sequenceInformationAndMessageCountResponseMessage message, rest)
  else if tag = 79 then (FinraOpenMessage.decode bytes).map fun (message, rest) => (.finraOpenMessage message, rest)
  else if tag = 82 then (OddLotRefreshRequestMessage.decode bytes).map fun (message, rest) => (.oddLotRefreshRequestMessage message, rest)
  else if tag = 84 then (LineIntegrityMessage.decode bytes).map fun (message, rest) => (.lineIntegrityMessage message, rest)
  else if tag = 90 then (EndOfDayMessage.decode bytes).map fun (message, rest) => (.endOfDayMessage message, rest)
  else if tag = 53 then (TestMessage.decode bytes).map fun (message, rest) => (.testMessage message, rest)
  else none

@[simp] theorem decode_encode (message : ControlMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ControlMessagePayload

/-- Control Message -/
structure ControlMessage where
  controlMessagePayload : ControlMessagePayload
  deriving DecidableEq, Repr

namespace ControlMessage

def encode (message : ControlMessage) : List UInt8 :=
  encodeUInt 1 (ControlMessagePayload.tag message.controlMessagePayload)
    ++ (ControlMessagePayload.encode message.controlMessagePayload)

def decode (bytes : List UInt8) : Option (ControlMessage × List UInt8) := do
  let (controlMessageType, bytes) ← decodeUInt 1 bytes
  let (controlMessagePayload, bytes) ← ControlMessagePayload.decode controlMessageType bytes
  pure ({ controlMessagePayload }, bytes)

theorem encode_length_pos (message : ControlMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ControlMessage) : (encode message).length ≤ 257 := by
  unfold encode
  cases message.controlMessagePayload with
  | startOfDayMessage inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, StartOfDayMessage.encode_length]
    omega
  | finraCloseMessage inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, FinraCloseMessage.encode_length]
    omega
  | sequenceInformationAndMessageCountInquiryMessage inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, SequenceInformationAndMessageCountInquiryMessage.encode_length]
    omega
  | sequenceInformationAndMessageCountResponseMessage inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, SequenceInformationAndMessageCountResponseMessage.encode_length]
    omega
  | finraOpenMessage inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, FinraOpenMessage.encode_length]
    omega
  | oddLotRefreshRequestMessage inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, OddLotRefreshRequestMessage.encode_length]
    omega
  | lineIntegrityMessage inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, LineIntegrityMessage.encode_length]
    omega
  | endOfDayMessage inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, EndOfDayMessage.encode_length]
    omega
  | testMessage inner =>
    simp only [ControlMessagePayload.encode, List.length_append, encodeUInt_length, TestMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : ControlMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ControlMessagePayload.decode_encode, some_bind]
  rfl

end ControlMessage

/-- Auction Status Message: 99 bytes -/
structure AuctionStatusMessage where
  securitySymbol : Alpha 11
  instrumentType : InstrumentType
  auctionCollarReferencePrice : BitVec 64
  auctionCollarUpperThresholdPrice : BitVec 64
  auctionCollarLowerThresholdPrice : BitVec 64
  numberOfExtensions : BitVec 8
  reserved62 : Alpha 62
  deriving DecidableEq, Repr

namespace AuctionStatusMessage

def encode (message : AuctionStatusMessage) : List UInt8 :=
  Alpha.encode message.securitySymbol
    ++ (InstrumentType.encode message.instrumentType
    ++ (encodeUInt 8 message.auctionCollarReferencePrice
    ++ (encodeUInt 8 message.auctionCollarUpperThresholdPrice
    ++ (encodeUInt 8 message.auctionCollarLowerThresholdPrice
    ++ (encodeUInt 1 message.numberOfExtensions
    ++ (Alpha.encode message.reserved62))))))

def decode (bytes : List UInt8) : Option (AuctionStatusMessage × List UInt8) := do
  let (securitySymbol, bytes) ← Alpha.decode 11 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  let (auctionCollarReferencePrice, bytes) ← decodeUInt 8 bytes
  let (auctionCollarUpperThresholdPrice, bytes) ← decodeUInt 8 bytes
  let (auctionCollarLowerThresholdPrice, bytes) ← decodeUInt 8 bytes
  let (numberOfExtensions, bytes) ← decodeUInt 1 bytes
  let (reserved62, bytes) ← Alpha.decode 62 bytes
  pure ({ securitySymbol, instrumentType, auctionCollarReferencePrice, auctionCollarUpperThresholdPrice, auctionCollarLowerThresholdPrice, numberOfExtensions, reserved62 }, bytes)

@[simp] theorem encode_length (message : AuctionStatusMessage) : (encode message).length = 99 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, InstrumentType.encode_length, encodeUInt_length]

theorem encode_length_pos (message : AuctionStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AuctionStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentType.decode_encode, some_bind]
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

end AuctionStatusMessage

/-- Short Quote Message: 15 bytes -/
structure ShortQuoteMessage where
  securitySymbolShort : Alpha 5
  bidPriceShort : BitVec 16
  bidSizeShort : BitVec 16
  offerPriceShort : BitVec 16
  offerSizeShort : BitVec 16
  reserved2 : Alpha 2
  deriving DecidableEq, Repr

namespace ShortQuoteMessage

def encode (message : ShortQuoteMessage) : List UInt8 :=
  Alpha.encode message.securitySymbolShort
    ++ (encodeUInt 2 message.bidPriceShort
    ++ (encodeUInt 2 message.bidSizeShort
    ++ (encodeUInt 2 message.offerPriceShort
    ++ (encodeUInt 2 message.offerSizeShort
    ++ (Alpha.encode message.reserved2)))))

def decode (bytes : List UInt8) : Option (ShortQuoteMessage × List UInt8) := do
  let (securitySymbolShort, bytes) ← Alpha.decode 5 bytes
  let (bidPriceShort, bytes) ← decodeUInt 2 bytes
  let (bidSizeShort, bytes) ← decodeUInt 2 bytes
  let (offerPriceShort, bytes) ← decodeUInt 2 bytes
  let (offerSizeShort, bytes) ← decodeUInt 2 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  pure ({ securitySymbolShort, bidPriceShort, bidSizeShort, offerPriceShort, offerSizeShort, reserved2 }, bytes)

@[simp] theorem encode_length (message : ShortQuoteMessage) : (encode message).length = 15 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ShortQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ShortQuoteMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end ShortQuoteMessage

/-- Timestamp 2: 8 bytes -/
structure Timestamp2 where
  seconds : BitVec 32
  nanoseconds : BitVec 32
  deriving DecidableEq, Repr

namespace Timestamp2

def encode (message : Timestamp2) : List UInt8 :=
  encodeUInt 4 message.seconds
    ++ (encodeUInt 4 message.nanoseconds)

def decode (bytes : List UInt8) : Option (Timestamp2 × List UInt8) := do
  let (seconds, bytes) ← decodeUInt 4 bytes
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  pure ({ seconds, nanoseconds }, bytes)

@[simp] theorem encode_length (message : Timestamp2) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : Timestamp2) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Timestamp2) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end Timestamp2

/-- Long Quote Message: 55 bytes -/
structure LongQuoteMessage where
  securitySymbol : Alpha 11
  instrumentType : InstrumentType
  quoteCondition : QuoteCondition
  securityStatusIndicator : Alpha 1
  bidPrice : BitVec 64
  bidSize : BitVec 32
  offerPrice : BitVec 64
  offerSize : BitVec 32
  retailInterestIndicator : RetailInterestIndicator
  settlementCondition : SettlementCondition
  marketCondition : MarketCondition
  finraMarketMakerId : Alpha 4
  finraBboIndicator : FinraBboIndicator
  timestamp2 : Timestamp2
  shortSaleRestrictionIndicator : ShortSaleRestrictionIndicator
  deriving DecidableEq, Repr

namespace LongQuoteMessage

def encode (message : LongQuoteMessage) : List UInt8 :=
  Alpha.encode message.securitySymbol
    ++ (InstrumentType.encode message.instrumentType
    ++ (QuoteCondition.encode message.quoteCondition
    ++ (Alpha.encode message.securityStatusIndicator
    ++ (encodeUInt 8 message.bidPrice
    ++ (encodeUInt 4 message.bidSize
    ++ (encodeUInt 8 message.offerPrice
    ++ (encodeUInt 4 message.offerSize
    ++ (RetailInterestIndicator.encode message.retailInterestIndicator
    ++ (SettlementCondition.encode message.settlementCondition
    ++ (MarketCondition.encode message.marketCondition
    ++ (Alpha.encode message.finraMarketMakerId
    ++ (FinraBboIndicator.encode message.finraBboIndicator
    ++ (Timestamp2.encode message.timestamp2
    ++ (ShortSaleRestrictionIndicator.encode message.shortSaleRestrictionIndicator))))))))))))))

def decode (bytes : List UInt8) : Option (LongQuoteMessage × List UInt8) := do
  let (securitySymbol, bytes) ← Alpha.decode 11 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  let (quoteCondition, bytes) ← QuoteCondition.decode bytes
  let (securityStatusIndicator, bytes) ← Alpha.decode 1 bytes
  let (bidPrice, bytes) ← decodeUInt 8 bytes
  let (bidSize, bytes) ← decodeUInt 4 bytes
  let (offerPrice, bytes) ← decodeUInt 8 bytes
  let (offerSize, bytes) ← decodeUInt 4 bytes
  let (retailInterestIndicator, bytes) ← RetailInterestIndicator.decode bytes
  let (settlementCondition, bytes) ← SettlementCondition.decode bytes
  let (marketCondition, bytes) ← MarketCondition.decode bytes
  let (finraMarketMakerId, bytes) ← Alpha.decode 4 bytes
  let (finraBboIndicator, bytes) ← FinraBboIndicator.decode bytes
  let (timestamp2, bytes) ← Timestamp2.decode bytes
  let (shortSaleRestrictionIndicator, bytes) ← ShortSaleRestrictionIndicator.decode bytes
  pure ({ securitySymbol, instrumentType, quoteCondition, securityStatusIndicator, bidPrice, bidSize, offerPrice, offerSize, retailInterestIndicator, settlementCondition, marketCondition, finraMarketMakerId, finraBboIndicator, timestamp2, shortSaleRestrictionIndicator }, bytes)

@[simp] theorem encode_length (message : LongQuoteMessage) : (encode message).length = 55 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, encodeUInt_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, FinraBboIndicator.encode_length, Timestamp2.encode_length, ShortSaleRestrictionIndicator.encode_length]

theorem encode_length_pos (message : LongQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LongQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, QuoteCondition.decode_encode, some_bind]
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
  rw [List.append_assoc, RetailInterestIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SettlementCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FinraBboIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp2.decode_encode, some_bind]
  dsimp only
  rw [ShortSaleRestrictionIndicator.decode_encode, some_bind]
  rfl

end LongQuoteMessage

/-- Special Long Quote Message: 88 bytes -/
structure SpecialLongQuoteMessage where
  securitySymbol : Alpha 11
  instrumentType : InstrumentType
  quoteCondition : QuoteCondition
  securityStatusIndicator : Alpha 1
  bidPrice : BitVec 64
  bidSize : BitVec 32
  offerPrice : BitVec 64
  offerSize : BitVec 32
  retailInterestIndicator : RetailInterestIndicator
  settlementCondition : SettlementCondition
  marketCondition : MarketCondition
  finraMarketMakerId : Alpha 4
  finraBestBidQuoteCondition : Alpha 1
  finraBestBidPrice : BitVec 64
  finraBestBidSize : BitVec 32
  finraBestBidMarketMakerId : Alpha 4
  finraBestOfferQuoteCondition : Alpha 1
  finraBestOfferPrice : BitVec 64
  finraBestOfferSize : BitVec 32
  finraBestOfferMarketMakerId : Alpha 4
  timestamp2 : Timestamp2
  shortSaleRestrictionIndicator : ShortSaleRestrictionIndicator
  deriving DecidableEq, Repr

namespace SpecialLongQuoteMessage

def encode (message : SpecialLongQuoteMessage) : List UInt8 :=
  Alpha.encode message.securitySymbol
    ++ (InstrumentType.encode message.instrumentType
    ++ (QuoteCondition.encode message.quoteCondition
    ++ (Alpha.encode message.securityStatusIndicator
    ++ (encodeUInt 8 message.bidPrice
    ++ (encodeUInt 4 message.bidSize
    ++ (encodeUInt 8 message.offerPrice
    ++ (encodeUInt 4 message.offerSize
    ++ (RetailInterestIndicator.encode message.retailInterestIndicator
    ++ (SettlementCondition.encode message.settlementCondition
    ++ (MarketCondition.encode message.marketCondition
    ++ (Alpha.encode message.finraMarketMakerId
    ++ (Alpha.encode message.finraBestBidQuoteCondition
    ++ (encodeUInt 8 message.finraBestBidPrice
    ++ (encodeUInt 4 message.finraBestBidSize
    ++ (Alpha.encode message.finraBestBidMarketMakerId
    ++ (Alpha.encode message.finraBestOfferQuoteCondition
    ++ (encodeUInt 8 message.finraBestOfferPrice
    ++ (encodeUInt 4 message.finraBestOfferSize
    ++ (Alpha.encode message.finraBestOfferMarketMakerId
    ++ (Timestamp2.encode message.timestamp2
    ++ (ShortSaleRestrictionIndicator.encode message.shortSaleRestrictionIndicator)))))))))))))))))))))

def decode (bytes : List UInt8) : Option (SpecialLongQuoteMessage × List UInt8) := do
  let (securitySymbol, bytes) ← Alpha.decode 11 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  let (quoteCondition, bytes) ← QuoteCondition.decode bytes
  let (securityStatusIndicator, bytes) ← Alpha.decode 1 bytes
  let (bidPrice, bytes) ← decodeUInt 8 bytes
  let (bidSize, bytes) ← decodeUInt 4 bytes
  let (offerPrice, bytes) ← decodeUInt 8 bytes
  let (offerSize, bytes) ← decodeUInt 4 bytes
  let (retailInterestIndicator, bytes) ← RetailInterestIndicator.decode bytes
  let (settlementCondition, bytes) ← SettlementCondition.decode bytes
  let (marketCondition, bytes) ← MarketCondition.decode bytes
  let (finraMarketMakerId, bytes) ← Alpha.decode 4 bytes
  let (finraBestBidQuoteCondition, bytes) ← Alpha.decode 1 bytes
  let (finraBestBidPrice, bytes) ← decodeUInt 8 bytes
  let (finraBestBidSize, bytes) ← decodeUInt 4 bytes
  let (finraBestBidMarketMakerId, bytes) ← Alpha.decode 4 bytes
  let (finraBestOfferQuoteCondition, bytes) ← Alpha.decode 1 bytes
  let (finraBestOfferPrice, bytes) ← decodeUInt 8 bytes
  let (finraBestOfferSize, bytes) ← decodeUInt 4 bytes
  let (finraBestOfferMarketMakerId, bytes) ← Alpha.decode 4 bytes
  let (timestamp2, bytes) ← Timestamp2.decode bytes
  let (shortSaleRestrictionIndicator, bytes) ← ShortSaleRestrictionIndicator.decode bytes
  pure ({ securitySymbol, instrumentType, quoteCondition, securityStatusIndicator, bidPrice, bidSize, offerPrice, offerSize, retailInterestIndicator, settlementCondition, marketCondition, finraMarketMakerId, finraBestBidQuoteCondition, finraBestBidPrice, finraBestBidSize, finraBestBidMarketMakerId, finraBestOfferQuoteCondition, finraBestOfferPrice, finraBestOfferSize, finraBestOfferMarketMakerId, timestamp2, shortSaleRestrictionIndicator }, bytes)

@[simp] theorem encode_length (message : SpecialLongQuoteMessage) : (encode message).length = 88 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, InstrumentType.encode_length, QuoteCondition.encode_length, encodeUInt_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, Timestamp2.encode_length, ShortSaleRestrictionIndicator.encode_length]

theorem encode_length_pos (message : SpecialLongQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SpecialLongQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, QuoteCondition.decode_encode, some_bind]
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
  rw [List.append_assoc, RetailInterestIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SettlementCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp2.decode_encode, some_bind]
  dsimp only
  rw [ShortSaleRestrictionIndicator.decode_encode, some_bind]
  rfl

end SpecialLongQuoteMessage

/-- Odd Lot Bid Short Quote Appendage: 3 bytes -/
structure OddLotBidShortQuoteAppendage where
  oddLotQuotePrice2 : BitVec 16
  oddLotQuoteSize : BitVec 8
  deriving DecidableEq, Repr

namespace OddLotBidShortQuoteAppendage

def encode (message : OddLotBidShortQuoteAppendage) : List UInt8 :=
  encodeUInt 2 message.oddLotQuotePrice2
    ++ (encodeUInt 1 message.oddLotQuoteSize)

def decode (bytes : List UInt8) : Option (OddLotBidShortQuoteAppendage × List UInt8) := do
  let (oddLotQuotePrice2, bytes) ← decodeUInt 2 bytes
  let (oddLotQuoteSize, bytes) ← decodeUInt 1 bytes
  pure ({ oddLotQuotePrice2, oddLotQuoteSize }, bytes)

@[simp] theorem encode_length (message : OddLotBidShortQuoteAppendage) : (encode message).length = 3 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : OddLotBidShortQuoteAppendage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OddLotBidShortQuoteAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OddLotBidShortQuoteAppendage

/-- Odd Lot Offer Short Quote Appendage: 3 bytes -/
structure OddLotOfferShortQuoteAppendage where
  oddLotQuotePrice2 : BitVec 16
  oddLotQuoteSize : BitVec 8
  deriving DecidableEq, Repr

namespace OddLotOfferShortQuoteAppendage

def encode (message : OddLotOfferShortQuoteAppendage) : List UInt8 :=
  encodeUInt 2 message.oddLotQuotePrice2
    ++ (encodeUInt 1 message.oddLotQuoteSize)

def decode (bytes : List UInt8) : Option (OddLotOfferShortQuoteAppendage × List UInt8) := do
  let (oddLotQuotePrice2, bytes) ← decodeUInt 2 bytes
  let (oddLotQuoteSize, bytes) ← decodeUInt 1 bytes
  pure ({ oddLotQuotePrice2, oddLotQuoteSize }, bytes)

@[simp] theorem encode_length (message : OddLotOfferShortQuoteAppendage) : (encode message).length = 3 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : OddLotOfferShortQuoteAppendage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OddLotOfferShortQuoteAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OddLotOfferShortQuoteAppendage

/-- Round Lot Short Quote Message -/
structure RoundLotShortQuoteMessage where
  securitySymbolShort : Alpha 5
  roundLotBidPriceShort : BitVec 16
  roundLotBidSizeShort : BitVec 16
  roundLotOfferPriceShort : BitVec 16
  roundLotOfferSizeShort : BitVec 16
  clearPriorOddLotQuotes : ClearPriorOddLotQuotes
  oddLotBidShortQuoteAppendage : Bounded 1 OddLotBidShortQuoteAppendage
  oddLotOfferShortQuoteAppendage : Bounded 1 OddLotOfferShortQuoteAppendage
  deriving DecidableEq, Repr

namespace RoundLotShortQuoteMessage

def encode (message : RoundLotShortQuoteMessage) : List UInt8 :=
  Alpha.encode message.securitySymbolShort
    ++ (encodeUInt 2 message.roundLotBidPriceShort
    ++ (encodeUInt 2 message.roundLotBidSizeShort
    ++ (encodeUInt 2 message.roundLotOfferPriceShort
    ++ (encodeUInt 2 message.roundLotOfferSizeShort
    ++ (ClearPriorOddLotQuotes.encode message.clearPriorOddLotQuotes
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.oddLotBidShortQuoteAppendage.val.length)
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.oddLotOfferShortQuoteAppendage.val.length)
    ++ (encodeMany OddLotBidShortQuoteAppendage.encode message.oddLotBidShortQuoteAppendage.val
    ++ (encodeMany OddLotOfferShortQuoteAppendage.encode message.oddLotOfferShortQuoteAppendage.val)))))))))

def decode (bytes : List UInt8) : Option (RoundLotShortQuoteMessage × List UInt8) := do
  let (securitySymbolShort, bytes) ← Alpha.decode 5 bytes
  let (roundLotBidPriceShort, bytes) ← decodeUInt 2 bytes
  let (roundLotBidSizeShort, bytes) ← decodeUInt 2 bytes
  let (roundLotOfferPriceShort, bytes) ← decodeUInt 2 bytes
  let (roundLotOfferSizeShort, bytes) ← decodeUInt 2 bytes
  let (clearPriorOddLotQuotes, bytes) ← ClearPriorOddLotQuotes.decode bytes
  let (countOfOddLotBidAppendages, bytes) ← decodeUInt 1 bytes
  let (countOfOddLotOfferAppendages, bytes) ← decodeUInt 1 bytes
  let (oddLotBidShortQuoteAppendage_, bytes) ← decodeMany OddLotBidShortQuoteAppendage.decode countOfOddLotBidAppendages.toNat bytes
  let (oddLotOfferShortQuoteAppendage_, bytes) ← decodeMany OddLotOfferShortQuoteAppendage.decode countOfOddLotOfferAppendages.toNat bytes
  if fits_oddLotBidShortQuoteAppendage : oddLotBidShortQuoteAppendage_.length < 256 ^ 1 then
    if fits_oddLotOfferShortQuoteAppendage : oddLotOfferShortQuoteAppendage_.length < 256 ^ 1 then
      pure ({ securitySymbolShort, roundLotBidPriceShort, roundLotBidSizeShort, roundLotOfferPriceShort, roundLotOfferSizeShort, clearPriorOddLotQuotes, oddLotBidShortQuoteAppendage := ⟨oddLotBidShortQuoteAppendage_, fits_oddLotBidShortQuoteAppendage⟩, oddLotOfferShortQuoteAppendage := ⟨oddLotOfferShortQuoteAppendage_, fits_oddLotOfferShortQuoteAppendage⟩ }, bytes)
    else none
  else none

theorem encode_length_pos (message : RoundLotShortQuoteMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : RoundLotShortQuoteMessage) : (encode message).length ≤ 1546 := by
  have bound_oddLotBidShortQuoteAppendage := message.oddLotBidShortQuoteAppendage.length_lt
  have bound_oddLotOfferShortQuoteAppendage := message.oddLotOfferShortQuoteAppendage.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, ClearPriorOddLotQuotes.encode_length, encodeMany_length_const OddLotBidShortQuoteAppendage.encode 3 OddLotBidShortQuoteAppendage.encode_length, encodeMany_length_const OddLotOfferShortQuoteAppendage.encode 3 OddLotOfferShortQuoteAppendage.encode_length]
  omega

@[simp] theorem decode_encode (message : RoundLotShortQuoteMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, ClearPriorOddLotQuotes.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeMany_bounded 1 OddLotBidShortQuoteAppendage.encode OddLotBidShortQuoteAppendage.decode OddLotBidShortQuoteAppendage.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 OddLotOfferShortQuoteAppendage.encode OddLotOfferShortQuoteAppendage.decode OddLotOfferShortQuoteAppendage.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.oddLotBidShortQuoteAppendage.length_lt, dite_eq_left message.oddLotOfferShortQuoteAppendage.length_lt]
  rfl

end RoundLotShortQuoteMessage

/-- Odd Lot Bid Long Quote Appendage: 9 bytes -/
structure OddLotBidLongQuoteAppendage where
  oddLotQuotePrice : BitVec 64
  oddLotQuoteSize : BitVec 8
  deriving DecidableEq, Repr

namespace OddLotBidLongQuoteAppendage

def encode (message : OddLotBidLongQuoteAppendage) : List UInt8 :=
  encodeUInt 8 message.oddLotQuotePrice
    ++ (encodeUInt 1 message.oddLotQuoteSize)

def decode (bytes : List UInt8) : Option (OddLotBidLongQuoteAppendage × List UInt8) := do
  let (oddLotQuotePrice, bytes) ← decodeUInt 8 bytes
  let (oddLotQuoteSize, bytes) ← decodeUInt 1 bytes
  pure ({ oddLotQuotePrice, oddLotQuoteSize }, bytes)

@[simp] theorem encode_length (message : OddLotBidLongQuoteAppendage) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : OddLotBidLongQuoteAppendage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OddLotBidLongQuoteAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OddLotBidLongQuoteAppendage

/-- Odd Lot Offer Long Quote Appendage: 9 bytes -/
structure OddLotOfferLongQuoteAppendage where
  oddLotQuotePrice : BitVec 64
  oddLotQuoteSize : BitVec 8
  deriving DecidableEq, Repr

namespace OddLotOfferLongQuoteAppendage

def encode (message : OddLotOfferLongQuoteAppendage) : List UInt8 :=
  encodeUInt 8 message.oddLotQuotePrice
    ++ (encodeUInt 1 message.oddLotQuoteSize)

def decode (bytes : List UInt8) : Option (OddLotOfferLongQuoteAppendage × List UInt8) := do
  let (oddLotQuotePrice, bytes) ← decodeUInt 8 bytes
  let (oddLotQuoteSize, bytes) ← decodeUInt 1 bytes
  pure ({ oddLotQuotePrice, oddLotQuoteSize }, bytes)

@[simp] theorem encode_length (message : OddLotOfferLongQuoteAppendage) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : OddLotOfferLongQuoteAppendage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OddLotOfferLongQuoteAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OddLotOfferLongQuoteAppendage

/-- Round Lot Long Quote Message -/
structure RoundLotLongQuoteMessage where
  securitySymbol : Alpha 11
  quoteCondition : QuoteCondition
  roundLotBidPrice : BitVec 64
  roundLotBidSize : BitVec 32
  roundLotOfferPrice : BitVec 64
  roundLotOfferSize : BitVec 32
  retailInterestIndicator : RetailInterestIndicator
  settlementCondition : SettlementCondition
  marketCondition : MarketCondition
  finraMarketMakerId : Alpha 4
  finraBboIndicator : FinraBboIndicator
  timestamp2 : Timestamp2
  clearPriorOddLotQuotes : ClearPriorOddLotQuotes
  oddLotBidLongQuoteAppendage : Bounded 1 OddLotBidLongQuoteAppendage
  oddLotOfferLongQuoteAppendage : Bounded 1 OddLotOfferLongQuoteAppendage
  deriving DecidableEq, Repr

namespace RoundLotLongQuoteMessage

def encode (message : RoundLotLongQuoteMessage) : List UInt8 :=
  Alpha.encode message.securitySymbol
    ++ (QuoteCondition.encode message.quoteCondition
    ++ (encodeUInt 8 message.roundLotBidPrice
    ++ (encodeUInt 4 message.roundLotBidSize
    ++ (encodeUInt 8 message.roundLotOfferPrice
    ++ (encodeUInt 4 message.roundLotOfferSize
    ++ (RetailInterestIndicator.encode message.retailInterestIndicator
    ++ (SettlementCondition.encode message.settlementCondition
    ++ (MarketCondition.encode message.marketCondition
    ++ (Alpha.encode message.finraMarketMakerId
    ++ (FinraBboIndicator.encode message.finraBboIndicator
    ++ (Timestamp2.encode message.timestamp2
    ++ (ClearPriorOddLotQuotes.encode message.clearPriorOddLotQuotes
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.oddLotBidLongQuoteAppendage.val.length)
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.oddLotOfferLongQuoteAppendage.val.length)
    ++ (encodeMany OddLotBidLongQuoteAppendage.encode message.oddLotBidLongQuoteAppendage.val
    ++ (encodeMany OddLotOfferLongQuoteAppendage.encode message.oddLotOfferLongQuoteAppendage.val))))))))))))))))

def decode (bytes : List UInt8) : Option (RoundLotLongQuoteMessage × List UInt8) := do
  let (securitySymbol, bytes) ← Alpha.decode 11 bytes
  let (quoteCondition, bytes) ← QuoteCondition.decode bytes
  let (roundLotBidPrice, bytes) ← decodeUInt 8 bytes
  let (roundLotBidSize, bytes) ← decodeUInt 4 bytes
  let (roundLotOfferPrice, bytes) ← decodeUInt 8 bytes
  let (roundLotOfferSize, bytes) ← decodeUInt 4 bytes
  let (retailInterestIndicator, bytes) ← RetailInterestIndicator.decode bytes
  let (settlementCondition, bytes) ← SettlementCondition.decode bytes
  let (marketCondition, bytes) ← MarketCondition.decode bytes
  let (finraMarketMakerId, bytes) ← Alpha.decode 4 bytes
  let (finraBboIndicator, bytes) ← FinraBboIndicator.decode bytes
  let (timestamp2, bytes) ← Timestamp2.decode bytes
  let (clearPriorOddLotQuotes, bytes) ← ClearPriorOddLotQuotes.decode bytes
  let (countOfOddLotBidAppendages, bytes) ← decodeUInt 1 bytes
  let (countOfOddLotOfferAppendages, bytes) ← decodeUInt 1 bytes
  let (oddLotBidLongQuoteAppendage_, bytes) ← decodeMany OddLotBidLongQuoteAppendage.decode countOfOddLotBidAppendages.toNat bytes
  let (oddLotOfferLongQuoteAppendage_, bytes) ← decodeMany OddLotOfferLongQuoteAppendage.decode countOfOddLotOfferAppendages.toNat bytes
  if fits_oddLotBidLongQuoteAppendage : oddLotBidLongQuoteAppendage_.length < 256 ^ 1 then
    if fits_oddLotOfferLongQuoteAppendage : oddLotOfferLongQuoteAppendage_.length < 256 ^ 1 then
      pure ({ securitySymbol, quoteCondition, roundLotBidPrice, roundLotBidSize, roundLotOfferPrice, roundLotOfferSize, retailInterestIndicator, settlementCondition, marketCondition, finraMarketMakerId, finraBboIndicator, timestamp2, clearPriorOddLotQuotes, oddLotBidLongQuoteAppendage := ⟨oddLotBidLongQuoteAppendage_, fits_oddLotBidLongQuoteAppendage⟩, oddLotOfferLongQuoteAppendage := ⟨oddLotOfferLongQuoteAppendage_, fits_oddLotOfferLongQuoteAppendage⟩ }, bytes)
    else none
  else none

theorem encode_length_pos (message : RoundLotLongQuoteMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : RoundLotLongQuoteMessage) : (encode message).length ≤ 4645 := by
  have bound_oddLotBidLongQuoteAppendage := message.oddLotBidLongQuoteAppendage.length_lt
  have bound_oddLotOfferLongQuoteAppendage := message.oddLotOfferLongQuoteAppendage.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, QuoteCondition.encode_length, encodeUInt_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, FinraBboIndicator.encode_length, Timestamp2.encode_length, ClearPriorOddLotQuotes.encode_length, encodeMany_length_const OddLotBidLongQuoteAppendage.encode 9 OddLotBidLongQuoteAppendage.encode_length, encodeMany_length_const OddLotOfferLongQuoteAppendage.encode 9 OddLotOfferLongQuoteAppendage.encode_length]
  omega

@[simp] theorem decode_encode (message : RoundLotLongQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, QuoteCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, RetailInterestIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SettlementCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FinraBboIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ClearPriorOddLotQuotes.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeMany_bounded 1 OddLotBidLongQuoteAppendage.encode OddLotBidLongQuoteAppendage.decode OddLotBidLongQuoteAppendage.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 OddLotOfferLongQuoteAppendage.encode OddLotOfferLongQuoteAppendage.decode OddLotOfferLongQuoteAppendage.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.oddLotBidLongQuoteAppendage.length_lt, dite_eq_left message.oddLotOfferLongQuoteAppendage.length_lt]
  rfl

end RoundLotLongQuoteMessage

/-- Odd Lot Bid Extended Quote Appendage: 13 bytes -/
structure OddLotBidExtendedQuoteAppendage where
  oddLotQuotePrice : BitVec 64
  oddLotQuoteSize : BitVec 8
  oddLotFinraMarketMakerId : Alpha 4
  deriving DecidableEq, Repr

namespace OddLotBidExtendedQuoteAppendage

def encode (message : OddLotBidExtendedQuoteAppendage) : List UInt8 :=
  encodeUInt 8 message.oddLotQuotePrice
    ++ (encodeUInt 1 message.oddLotQuoteSize
    ++ (Alpha.encode message.oddLotFinraMarketMakerId))

def decode (bytes : List UInt8) : Option (OddLotBidExtendedQuoteAppendage × List UInt8) := do
  let (oddLotQuotePrice, bytes) ← decodeUInt 8 bytes
  let (oddLotQuoteSize, bytes) ← decodeUInt 1 bytes
  let (oddLotFinraMarketMakerId, bytes) ← Alpha.decode 4 bytes
  pure ({ oddLotQuotePrice, oddLotQuoteSize, oddLotFinraMarketMakerId }, bytes)

@[simp] theorem encode_length (message : OddLotBidExtendedQuoteAppendage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : OddLotBidExtendedQuoteAppendage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OddLotBidExtendedQuoteAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OddLotBidExtendedQuoteAppendage

/-- Odd Lot Offer Extended Quote Appendage: 13 bytes -/
structure OddLotOfferExtendedQuoteAppendage where
  oddLotQuotePrice : BitVec 64
  oddLotQuoteSize : BitVec 8
  oddLotFinraMarketMakerId : Alpha 4
  deriving DecidableEq, Repr

namespace OddLotOfferExtendedQuoteAppendage

def encode (message : OddLotOfferExtendedQuoteAppendage) : List UInt8 :=
  encodeUInt 8 message.oddLotQuotePrice
    ++ (encodeUInt 1 message.oddLotQuoteSize
    ++ (Alpha.encode message.oddLotFinraMarketMakerId))

def decode (bytes : List UInt8) : Option (OddLotOfferExtendedQuoteAppendage × List UInt8) := do
  let (oddLotQuotePrice, bytes) ← decodeUInt 8 bytes
  let (oddLotQuoteSize, bytes) ← decodeUInt 1 bytes
  let (oddLotFinraMarketMakerId, bytes) ← Alpha.decode 4 bytes
  pure ({ oddLotQuotePrice, oddLotQuoteSize, oddLotFinraMarketMakerId }, bytes)

@[simp] theorem encode_length (message : OddLotOfferExtendedQuoteAppendage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : OddLotOfferExtendedQuoteAppendage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OddLotOfferExtendedQuoteAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OddLotOfferExtendedQuoteAppendage

/-- Round Lot Finra Adf Quote Message -/
structure RoundLotFinraAdfQuoteMessage where
  securitySymbol : Alpha 11
  quoteCondition : QuoteCondition
  roundLotBidPrice : BitVec 64
  roundLotBidSize : BitVec 32
  roundLotOfferPrice : BitVec 64
  roundLotOfferSize : BitVec 32
  retailInterestIndicator : RetailInterestIndicator
  settlementCondition : SettlementCondition
  marketCondition : MarketCondition
  finraMarketMakerId : Alpha 4
  finraBestBidQuoteCondition : Alpha 1
  finraBestBidPrice : BitVec 64
  finraBestBidSize : BitVec 32
  finraBestBidMarketMakerId : Alpha 4
  finraBestOfferQuoteCondition : Alpha 1
  finraBestOfferPrice : BitVec 64
  finraBestOfferSize : BitVec 32
  finraBestOfferMarketMakerId : Alpha 4
  timestamp2 : Timestamp2
  clearPriorOddLotQuotes : ClearPriorOddLotQuotes
  oddLotBidExtendedQuoteAppendage : Bounded 1 OddLotBidExtendedQuoteAppendage
  oddLotOfferExtendedQuoteAppendage : Bounded 1 OddLotOfferExtendedQuoteAppendage
  deriving DecidableEq, Repr

namespace RoundLotFinraAdfQuoteMessage

def encode (message : RoundLotFinraAdfQuoteMessage) : List UInt8 :=
  Alpha.encode message.securitySymbol
    ++ (QuoteCondition.encode message.quoteCondition
    ++ (encodeUInt 8 message.roundLotBidPrice
    ++ (encodeUInt 4 message.roundLotBidSize
    ++ (encodeUInt 8 message.roundLotOfferPrice
    ++ (encodeUInt 4 message.roundLotOfferSize
    ++ (RetailInterestIndicator.encode message.retailInterestIndicator
    ++ (SettlementCondition.encode message.settlementCondition
    ++ (MarketCondition.encode message.marketCondition
    ++ (Alpha.encode message.finraMarketMakerId
    ++ (Alpha.encode message.finraBestBidQuoteCondition
    ++ (encodeUInt 8 message.finraBestBidPrice
    ++ (encodeUInt 4 message.finraBestBidSize
    ++ (Alpha.encode message.finraBestBidMarketMakerId
    ++ (Alpha.encode message.finraBestOfferQuoteCondition
    ++ (encodeUInt 8 message.finraBestOfferPrice
    ++ (encodeUInt 4 message.finraBestOfferSize
    ++ (Alpha.encode message.finraBestOfferMarketMakerId
    ++ (Timestamp2.encode message.timestamp2
    ++ (ClearPriorOddLotQuotes.encode message.clearPriorOddLotQuotes
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.oddLotBidExtendedQuoteAppendage.val.length)
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.oddLotOfferExtendedQuoteAppendage.val.length)
    ++ (encodeMany OddLotBidExtendedQuoteAppendage.encode message.oddLotBidExtendedQuoteAppendage.val
    ++ (encodeMany OddLotOfferExtendedQuoteAppendage.encode message.oddLotOfferExtendedQuoteAppendage.val)))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (RoundLotFinraAdfQuoteMessage × List UInt8) := do
  let (securitySymbol, bytes) ← Alpha.decode 11 bytes
  let (quoteCondition, bytes) ← QuoteCondition.decode bytes
  let (roundLotBidPrice, bytes) ← decodeUInt 8 bytes
  let (roundLotBidSize, bytes) ← decodeUInt 4 bytes
  let (roundLotOfferPrice, bytes) ← decodeUInt 8 bytes
  let (roundLotOfferSize, bytes) ← decodeUInt 4 bytes
  let (retailInterestIndicator, bytes) ← RetailInterestIndicator.decode bytes
  let (settlementCondition, bytes) ← SettlementCondition.decode bytes
  let (marketCondition, bytes) ← MarketCondition.decode bytes
  let (finraMarketMakerId, bytes) ← Alpha.decode 4 bytes
  let (finraBestBidQuoteCondition, bytes) ← Alpha.decode 1 bytes
  let (finraBestBidPrice, bytes) ← decodeUInt 8 bytes
  let (finraBestBidSize, bytes) ← decodeUInt 4 bytes
  let (finraBestBidMarketMakerId, bytes) ← Alpha.decode 4 bytes
  let (finraBestOfferQuoteCondition, bytes) ← Alpha.decode 1 bytes
  let (finraBestOfferPrice, bytes) ← decodeUInt 8 bytes
  let (finraBestOfferSize, bytes) ← decodeUInt 4 bytes
  let (finraBestOfferMarketMakerId, bytes) ← Alpha.decode 4 bytes
  let (timestamp2, bytes) ← Timestamp2.decode bytes
  let (clearPriorOddLotQuotes, bytes) ← ClearPriorOddLotQuotes.decode bytes
  let (countOfOddLotBidAppendages, bytes) ← decodeUInt 1 bytes
  let (countOfOddLotOfferAppendages, bytes) ← decodeUInt 1 bytes
  let (oddLotBidExtendedQuoteAppendage_, bytes) ← decodeMany OddLotBidExtendedQuoteAppendage.decode countOfOddLotBidAppendages.toNat bytes
  let (oddLotOfferExtendedQuoteAppendage_, bytes) ← decodeMany OddLotOfferExtendedQuoteAppendage.decode countOfOddLotOfferAppendages.toNat bytes
  if fits_oddLotBidExtendedQuoteAppendage : oddLotBidExtendedQuoteAppendage_.length < 256 ^ 1 then
    if fits_oddLotOfferExtendedQuoteAppendage : oddLotOfferExtendedQuoteAppendage_.length < 256 ^ 1 then
      pure ({ securitySymbol, quoteCondition, roundLotBidPrice, roundLotBidSize, roundLotOfferPrice, roundLotOfferSize, retailInterestIndicator, settlementCondition, marketCondition, finraMarketMakerId, finraBestBidQuoteCondition, finraBestBidPrice, finraBestBidSize, finraBestBidMarketMakerId, finraBestOfferQuoteCondition, finraBestOfferPrice, finraBestOfferSize, finraBestOfferMarketMakerId, timestamp2, clearPriorOddLotQuotes, oddLotBidExtendedQuoteAppendage := ⟨oddLotBidExtendedQuoteAppendage_, fits_oddLotBidExtendedQuoteAppendage⟩, oddLotOfferExtendedQuoteAppendage := ⟨oddLotOfferExtendedQuoteAppendage_, fits_oddLotOfferExtendedQuoteAppendage⟩ }, bytes)
    else none
  else none

theorem encode_length_pos (message : RoundLotFinraAdfQuoteMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : RoundLotFinraAdfQuoteMessage) : (encode message).length ≤ 6718 := by
  have bound_oddLotBidExtendedQuoteAppendage := message.oddLotBidExtendedQuoteAppendage.length_lt
  have bound_oddLotOfferExtendedQuoteAppendage := message.oddLotOfferExtendedQuoteAppendage.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, QuoteCondition.encode_length, encodeUInt_length, RetailInterestIndicator.encode_length, SettlementCondition.encode_length, MarketCondition.encode_length, Timestamp2.encode_length, ClearPriorOddLotQuotes.encode_length, encodeMany_length_const OddLotBidExtendedQuoteAppendage.encode 13 OddLotBidExtendedQuoteAppendage.encode_length, encodeMany_length_const OddLotOfferExtendedQuoteAppendage.encode 13 OddLotOfferExtendedQuoteAppendage.encode_length]
  omega

@[simp] theorem decode_encode (message : RoundLotFinraAdfQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, QuoteCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, RetailInterestIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SettlementCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ClearPriorOddLotQuotes.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeMany_bounded 1 OddLotBidExtendedQuoteAppendage.encode OddLotBidExtendedQuoteAppendage.decode OddLotBidExtendedQuoteAppendage.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 OddLotOfferExtendedQuoteAppendage.encode OddLotOfferExtendedQuoteAppendage.decode OddLotOfferExtendedQuoteAppendage.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.oddLotBidExtendedQuoteAppendage.length_lt, dite_eq_left message.oddLotOfferExtendedQuoteAppendage.length_lt]
  rfl

end RoundLotFinraAdfQuoteMessage

/-- Odd Lot Short Quote Message -/
structure OddLotShortQuoteMessage where
  securitySymbolShort : Alpha 5
  clearPriorOddLotQuotes : ClearPriorOddLotQuotes
  oddLotBidShortQuoteAppendage : Bounded 1 OddLotBidShortQuoteAppendage
  oddLotOfferShortQuoteAppendage : Bounded 1 OddLotOfferShortQuoteAppendage
  deriving DecidableEq, Repr

namespace OddLotShortQuoteMessage

def encode (message : OddLotShortQuoteMessage) : List UInt8 :=
  Alpha.encode message.securitySymbolShort
    ++ (ClearPriorOddLotQuotes.encode message.clearPriorOddLotQuotes
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.oddLotBidShortQuoteAppendage.val.length)
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.oddLotOfferShortQuoteAppendage.val.length)
    ++ (encodeMany OddLotBidShortQuoteAppendage.encode message.oddLotBidShortQuoteAppendage.val
    ++ (encodeMany OddLotOfferShortQuoteAppendage.encode message.oddLotOfferShortQuoteAppendage.val)))))

def decode (bytes : List UInt8) : Option (OddLotShortQuoteMessage × List UInt8) := do
  let (securitySymbolShort, bytes) ← Alpha.decode 5 bytes
  let (clearPriorOddLotQuotes, bytes) ← ClearPriorOddLotQuotes.decode bytes
  let (countOfOddLotBidAppendages, bytes) ← decodeUInt 1 bytes
  let (countOfOddLotOfferAppendages, bytes) ← decodeUInt 1 bytes
  let (oddLotBidShortQuoteAppendage_, bytes) ← decodeMany OddLotBidShortQuoteAppendage.decode countOfOddLotBidAppendages.toNat bytes
  let (oddLotOfferShortQuoteAppendage_, bytes) ← decodeMany OddLotOfferShortQuoteAppendage.decode countOfOddLotOfferAppendages.toNat bytes
  if fits_oddLotBidShortQuoteAppendage : oddLotBidShortQuoteAppendage_.length < 256 ^ 1 then
    if fits_oddLotOfferShortQuoteAppendage : oddLotOfferShortQuoteAppendage_.length < 256 ^ 1 then
      pure ({ securitySymbolShort, clearPriorOddLotQuotes, oddLotBidShortQuoteAppendage := ⟨oddLotBidShortQuoteAppendage_, fits_oddLotBidShortQuoteAppendage⟩, oddLotOfferShortQuoteAppendage := ⟨oddLotOfferShortQuoteAppendage_, fits_oddLotOfferShortQuoteAppendage⟩ }, bytes)
    else none
  else none

theorem encode_length_pos (message : OddLotShortQuoteMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OddLotShortQuoteMessage) : (encode message).length ≤ 1538 := by
  have bound_oddLotBidShortQuoteAppendage := message.oddLotBidShortQuoteAppendage.length_lt
  have bound_oddLotOfferShortQuoteAppendage := message.oddLotOfferShortQuoteAppendage.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, ClearPriorOddLotQuotes.encode_length, encodeUInt_length, encodeMany_length_const OddLotBidShortQuoteAppendage.encode 3 OddLotBidShortQuoteAppendage.encode_length, encodeMany_length_const OddLotOfferShortQuoteAppendage.encode 3 OddLotOfferShortQuoteAppendage.encode_length]
  omega

@[simp] theorem decode_encode (message : OddLotShortQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ClearPriorOddLotQuotes.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeMany_bounded 1 OddLotBidShortQuoteAppendage.encode OddLotBidShortQuoteAppendage.decode OddLotBidShortQuoteAppendage.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 OddLotOfferShortQuoteAppendage.encode OddLotOfferShortQuoteAppendage.decode OddLotOfferShortQuoteAppendage.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.oddLotBidShortQuoteAppendage.length_lt, dite_eq_left message.oddLotOfferShortQuoteAppendage.length_lt]
  rfl

end OddLotShortQuoteMessage

/-- Odd Lot Long Quote Message -/
structure OddLotLongQuoteMessage where
  securitySymbol : Alpha 11
  clearPriorOddLotQuotes : ClearPriorOddLotQuotes
  oddLotBidLongQuoteAppendage : Bounded 1 OddLotBidLongQuoteAppendage
  oddLotOfferLongQuoteAppendage : Bounded 1 OddLotOfferLongQuoteAppendage
  deriving DecidableEq, Repr

namespace OddLotLongQuoteMessage

def encode (message : OddLotLongQuoteMessage) : List UInt8 :=
  Alpha.encode message.securitySymbol
    ++ (ClearPriorOddLotQuotes.encode message.clearPriorOddLotQuotes
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.oddLotBidLongQuoteAppendage.val.length)
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.oddLotOfferLongQuoteAppendage.val.length)
    ++ (encodeMany OddLotBidLongQuoteAppendage.encode message.oddLotBidLongQuoteAppendage.val
    ++ (encodeMany OddLotOfferLongQuoteAppendage.encode message.oddLotOfferLongQuoteAppendage.val)))))

def decode (bytes : List UInt8) : Option (OddLotLongQuoteMessage × List UInt8) := do
  let (securitySymbol, bytes) ← Alpha.decode 11 bytes
  let (clearPriorOddLotQuotes, bytes) ← ClearPriorOddLotQuotes.decode bytes
  let (countOfOddLotBidAppendages, bytes) ← decodeUInt 1 bytes
  let (countOfOddLotOfferAppendages, bytes) ← decodeUInt 1 bytes
  let (oddLotBidLongQuoteAppendage_, bytes) ← decodeMany OddLotBidLongQuoteAppendage.decode countOfOddLotBidAppendages.toNat bytes
  let (oddLotOfferLongQuoteAppendage_, bytes) ← decodeMany OddLotOfferLongQuoteAppendage.decode countOfOddLotOfferAppendages.toNat bytes
  if fits_oddLotBidLongQuoteAppendage : oddLotBidLongQuoteAppendage_.length < 256 ^ 1 then
    if fits_oddLotOfferLongQuoteAppendage : oddLotOfferLongQuoteAppendage_.length < 256 ^ 1 then
      pure ({ securitySymbol, clearPriorOddLotQuotes, oddLotBidLongQuoteAppendage := ⟨oddLotBidLongQuoteAppendage_, fits_oddLotBidLongQuoteAppendage⟩, oddLotOfferLongQuoteAppendage := ⟨oddLotOfferLongQuoteAppendage_, fits_oddLotOfferLongQuoteAppendage⟩ }, bytes)
    else none
  else none

theorem encode_length_pos (message : OddLotLongQuoteMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OddLotLongQuoteMessage) : (encode message).length ≤ 4604 := by
  have bound_oddLotBidLongQuoteAppendage := message.oddLotBidLongQuoteAppendage.length_lt
  have bound_oddLotOfferLongQuoteAppendage := message.oddLotOfferLongQuoteAppendage.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, ClearPriorOddLotQuotes.encode_length, encodeUInt_length, encodeMany_length_const OddLotBidLongQuoteAppendage.encode 9 OddLotBidLongQuoteAppendage.encode_length, encodeMany_length_const OddLotOfferLongQuoteAppendage.encode 9 OddLotOfferLongQuoteAppendage.encode_length]
  omega

@[simp] theorem decode_encode (message : OddLotLongQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ClearPriorOddLotQuotes.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeMany_bounded 1 OddLotBidLongQuoteAppendage.encode OddLotBidLongQuoteAppendage.decode OddLotBidLongQuoteAppendage.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 OddLotOfferLongQuoteAppendage.encode OddLotOfferLongQuoteAppendage.decode OddLotOfferLongQuoteAppendage.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.oddLotBidLongQuoteAppendage.length_lt, dite_eq_left message.oddLotOfferLongQuoteAppendage.length_lt]
  rfl

end OddLotLongQuoteMessage

/-- Odd Lot Finra Adf Quote Message -/
structure OddLotFinraAdfQuoteMessage where
  securitySymbol : Alpha 11
  clearPriorOddLotQuotes : ClearPriorOddLotQuotes
  oddLotBidExtendedQuoteAppendage : Bounded 1 OddLotBidExtendedQuoteAppendage
  oddLotOfferExtendedQuoteAppendage : Bounded 1 OddLotOfferExtendedQuoteAppendage
  deriving DecidableEq, Repr

namespace OddLotFinraAdfQuoteMessage

def encode (message : OddLotFinraAdfQuoteMessage) : List UInt8 :=
  Alpha.encode message.securitySymbol
    ++ (ClearPriorOddLotQuotes.encode message.clearPriorOddLotQuotes
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.oddLotBidExtendedQuoteAppendage.val.length)
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.oddLotOfferExtendedQuoteAppendage.val.length)
    ++ (encodeMany OddLotBidExtendedQuoteAppendage.encode message.oddLotBidExtendedQuoteAppendage.val
    ++ (encodeMany OddLotOfferExtendedQuoteAppendage.encode message.oddLotOfferExtendedQuoteAppendage.val)))))

def decode (bytes : List UInt8) : Option (OddLotFinraAdfQuoteMessage × List UInt8) := do
  let (securitySymbol, bytes) ← Alpha.decode 11 bytes
  let (clearPriorOddLotQuotes, bytes) ← ClearPriorOddLotQuotes.decode bytes
  let (countOfOddLotBidAppendages, bytes) ← decodeUInt 1 bytes
  let (countOfOddLotOfferAppendages, bytes) ← decodeUInt 1 bytes
  let (oddLotBidExtendedQuoteAppendage_, bytes) ← decodeMany OddLotBidExtendedQuoteAppendage.decode countOfOddLotBidAppendages.toNat bytes
  let (oddLotOfferExtendedQuoteAppendage_, bytes) ← decodeMany OddLotOfferExtendedQuoteAppendage.decode countOfOddLotOfferAppendages.toNat bytes
  if fits_oddLotBidExtendedQuoteAppendage : oddLotBidExtendedQuoteAppendage_.length < 256 ^ 1 then
    if fits_oddLotOfferExtendedQuoteAppendage : oddLotOfferExtendedQuoteAppendage_.length < 256 ^ 1 then
      pure ({ securitySymbol, clearPriorOddLotQuotes, oddLotBidExtendedQuoteAppendage := ⟨oddLotBidExtendedQuoteAppendage_, fits_oddLotBidExtendedQuoteAppendage⟩, oddLotOfferExtendedQuoteAppendage := ⟨oddLotOfferExtendedQuoteAppendage_, fits_oddLotOfferExtendedQuoteAppendage⟩ }, bytes)
    else none
  else none

theorem encode_length_pos (message : OddLotFinraAdfQuoteMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OddLotFinraAdfQuoteMessage) : (encode message).length ≤ 6644 := by
  have bound_oddLotBidExtendedQuoteAppendage := message.oddLotBidExtendedQuoteAppendage.length_lt
  have bound_oddLotOfferExtendedQuoteAppendage := message.oddLotOfferExtendedQuoteAppendage.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, ClearPriorOddLotQuotes.encode_length, encodeUInt_length, encodeMany_length_const OddLotBidExtendedQuoteAppendage.encode 13 OddLotBidExtendedQuoteAppendage.encode_length, encodeMany_length_const OddLotOfferExtendedQuoteAppendage.encode 13 OddLotOfferExtendedQuoteAppendage.encode_length]
  omega

@[simp] theorem decode_encode (message : OddLotFinraAdfQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ClearPriorOddLotQuotes.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeMany_bounded 1 OddLotBidExtendedQuoteAppendage.encode OddLotBidExtendedQuoteAppendage.decode OddLotBidExtendedQuoteAppendage.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 OddLotOfferExtendedQuoteAppendage.encode OddLotOfferExtendedQuoteAppendage.decode OddLotOfferExtendedQuoteAppendage.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.oddLotBidExtendedQuoteAppendage.length_lt, dite_eq_left message.oddLotOfferExtendedQuoteAppendage.length_lt]
  rfl

end OddLotFinraAdfQuoteMessage

/-- Any Quote Message Payload, selected by Quote Message Type -/
inductive QuoteMessagePayload where
  | auctionStatusMessage (message : AuctionStatusMessage) -- "A" 0x41
  | shortQuoteMessage (message : ShortQuoteMessage) -- "Q" 0x51
  | longQuoteMessage (message : LongQuoteMessage) -- "L" 0x4C
  | specialLongQuoteMessage (message : SpecialLongQuoteMessage) -- "S" 0x53
  | roundLotShortQuoteMessage (message : RoundLotShortQuoteMessage) -- "P" 0x50
  | roundLotLongQuoteMessage (message : RoundLotLongQuoteMessage) -- "K" 0x4B
  | roundLotFinraAdfQuoteMessage (message : RoundLotFinraAdfQuoteMessage) -- "U" 0x55
  | oddLotShortQuoteMessage (message : OddLotShortQuoteMessage) -- "R" 0x52
  | oddLotLongQuoteMessage (message : OddLotLongQuoteMessage) -- "M" 0x4D
  | oddLotFinraAdfQuoteMessage (message : OddLotFinraAdfQuoteMessage) -- "T" 0x54
  deriving DecidableEq, Repr

namespace QuoteMessagePayload

/-- The Quote Message Type each message is sent under -/
def tag : QuoteMessagePayload → BitVec 8
  | .auctionStatusMessage _ => 65
  | .shortQuoteMessage _ => 81
  | .longQuoteMessage _ => 76
  | .specialLongQuoteMessage _ => 83
  | .roundLotShortQuoteMessage _ => 80
  | .roundLotLongQuoteMessage _ => 75
  | .roundLotFinraAdfQuoteMessage _ => 85
  | .oddLotShortQuoteMessage _ => 82
  | .oddLotLongQuoteMessage _ => 77
  | .oddLotFinraAdfQuoteMessage _ => 84

def encode : QuoteMessagePayload → List UInt8
  | .auctionStatusMessage message => AuctionStatusMessage.encode message
  | .shortQuoteMessage message => ShortQuoteMessage.encode message
  | .longQuoteMessage message => LongQuoteMessage.encode message
  | .specialLongQuoteMessage message => SpecialLongQuoteMessage.encode message
  | .roundLotShortQuoteMessage message => RoundLotShortQuoteMessage.encode message
  | .roundLotLongQuoteMessage message => RoundLotLongQuoteMessage.encode message
  | .roundLotFinraAdfQuoteMessage message => RoundLotFinraAdfQuoteMessage.encode message
  | .oddLotShortQuoteMessage message => OddLotShortQuoteMessage.encode message
  | .oddLotLongQuoteMessage message => OddLotLongQuoteMessage.encode message
  | .oddLotFinraAdfQuoteMessage message => OddLotFinraAdfQuoteMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : QuoteMessagePayload) : (encode message).length ≤ 6718 := by
  cases message with
  | auctionStatusMessage inner =>
    simp only [encode, AuctionStatusMessage.encode_length]
    omega
  | shortQuoteMessage inner =>
    simp only [encode, ShortQuoteMessage.encode_length]
    omega
  | longQuoteMessage inner =>
    simp only [encode, LongQuoteMessage.encode_length]
    omega
  | specialLongQuoteMessage inner =>
    simp only [encode, SpecialLongQuoteMessage.encode_length]
    omega
  | roundLotShortQuoteMessage inner =>
    have bound_inner := RoundLotShortQuoteMessage.encode_length_le inner
    simp only [encode]
    omega
  | roundLotLongQuoteMessage inner =>
    have bound_inner := RoundLotLongQuoteMessage.encode_length_le inner
    simp only [encode]
    omega
  | roundLotFinraAdfQuoteMessage inner =>
    have bound_inner := RoundLotFinraAdfQuoteMessage.encode_length_le inner
    simp only [encode]
    omega
  | oddLotShortQuoteMessage inner =>
    have bound_inner := OddLotShortQuoteMessage.encode_length_le inner
    simp only [encode]
    omega
  | oddLotLongQuoteMessage inner =>
    have bound_inner := OddLotLongQuoteMessage.encode_length_le inner
    simp only [encode]
    omega
  | oddLotFinraAdfQuoteMessage inner =>
    have bound_inner := OddLotFinraAdfQuoteMessage.encode_length_le inner
    simp only [encode]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (QuoteMessagePayload × List UInt8) :=
  if tag = 65 then (AuctionStatusMessage.decode bytes).map fun (message, rest) => (.auctionStatusMessage message, rest)
  else if tag = 81 then (ShortQuoteMessage.decode bytes).map fun (message, rest) => (.shortQuoteMessage message, rest)
  else if tag = 76 then (LongQuoteMessage.decode bytes).map fun (message, rest) => (.longQuoteMessage message, rest)
  else if tag = 83 then (SpecialLongQuoteMessage.decode bytes).map fun (message, rest) => (.specialLongQuoteMessage message, rest)
  else if tag = 80 then (RoundLotShortQuoteMessage.decode bytes).map fun (message, rest) => (.roundLotShortQuoteMessage message, rest)
  else if tag = 75 then (RoundLotLongQuoteMessage.decode bytes).map fun (message, rest) => (.roundLotLongQuoteMessage message, rest)
  else if tag = 85 then (RoundLotFinraAdfQuoteMessage.decode bytes).map fun (message, rest) => (.roundLotFinraAdfQuoteMessage message, rest)
  else if tag = 82 then (OddLotShortQuoteMessage.decode bytes).map fun (message, rest) => (.oddLotShortQuoteMessage message, rest)
  else if tag = 77 then (OddLotLongQuoteMessage.decode bytes).map fun (message, rest) => (.oddLotLongQuoteMessage message, rest)
  else if tag = 84 then (OddLotFinraAdfQuoteMessage.decode bytes).map fun (message, rest) => (.oddLotFinraAdfQuoteMessage message, rest)
  else none

@[simp] theorem decode_encode (message : QuoteMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end QuoteMessagePayload

/-- Quote Message -/
structure QuoteMessage where
  quoteMessagePayload : QuoteMessagePayload
  deriving DecidableEq, Repr

namespace QuoteMessage

def encode (message : QuoteMessage) : List UInt8 :=
  encodeUInt 1 (QuoteMessagePayload.tag message.quoteMessagePayload)
    ++ (QuoteMessagePayload.encode message.quoteMessagePayload)

def decode (bytes : List UInt8) : Option (QuoteMessage × List UInt8) := do
  let (quoteMessageType, bytes) ← decodeUInt 1 bytes
  let (quoteMessagePayload, bytes) ← QuoteMessagePayload.decode quoteMessageType bytes
  pure ({ quoteMessagePayload }, bytes)

theorem encode_length_pos (message : QuoteMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : QuoteMessage) : (encode message).length ≤ 6719 := by
  unfold encode
  cases message.quoteMessagePayload with
  | auctionStatusMessage inner =>
    simp only [QuoteMessagePayload.encode, List.length_append, encodeUInt_length, AuctionStatusMessage.encode_length]
    omega
  | shortQuoteMessage inner =>
    simp only [QuoteMessagePayload.encode, List.length_append, encodeUInt_length, ShortQuoteMessage.encode_length]
    omega
  | longQuoteMessage inner =>
    simp only [QuoteMessagePayload.encode, List.length_append, encodeUInt_length, LongQuoteMessage.encode_length]
    omega
  | specialLongQuoteMessage inner =>
    simp only [QuoteMessagePayload.encode, List.length_append, encodeUInt_length, SpecialLongQuoteMessage.encode_length]
    omega
  | roundLotShortQuoteMessage inner =>
    have bound_inner := RoundLotShortQuoteMessage.encode_length_le inner
    simp only [QuoteMessagePayload.encode, List.length_append, encodeUInt_length]
    omega
  | roundLotLongQuoteMessage inner =>
    have bound_inner := RoundLotLongQuoteMessage.encode_length_le inner
    simp only [QuoteMessagePayload.encode, List.length_append, encodeUInt_length]
    omega
  | roundLotFinraAdfQuoteMessage inner =>
    have bound_inner := RoundLotFinraAdfQuoteMessage.encode_length_le inner
    simp only [QuoteMessagePayload.encode, List.length_append, encodeUInt_length]
    omega
  | oddLotShortQuoteMessage inner =>
    have bound_inner := OddLotShortQuoteMessage.encode_length_le inner
    simp only [QuoteMessagePayload.encode, List.length_append, encodeUInt_length]
    omega
  | oddLotLongQuoteMessage inner =>
    have bound_inner := OddLotLongQuoteMessage.encode_length_le inner
    simp only [QuoteMessagePayload.encode, List.length_append, encodeUInt_length]
    omega
  | oddLotFinraAdfQuoteMessage inner =>
    have bound_inner := OddLotFinraAdfQuoteMessage.encode_length_le inner
    simp only [QuoteMessagePayload.encode, List.length_append, encodeUInt_length]
    omega

@[simp] theorem decode_encode (message : QuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [QuoteMessagePayload.decode_encode, some_bind]
  rfl

end QuoteMessage

/-- Trading Status Message: 51 bytes -/
structure TradingStatusMessage where
  securitySymbol : Alpha 11
  instrumentType : InstrumentType
  lastPriceOpeningReopeningLuldReferencePrice : BitVec 64
  highIndicationPriceUpperLimitPriceBand : BitVec 64
  lowIndicationPriceLowerLimitPriceBand : BitVec 64
  buyVolume : BitVec 32
  sellVolume : BitVec 32
  securityStatus : SecurityStatus
  haltReason : HaltReason
  shortSaleRestrictionIndicator : ShortSaleRestrictionIndicator
  tradingStatusId : BitVec 32
  deriving DecidableEq, Repr

namespace TradingStatusMessage

def encode (message : TradingStatusMessage) : List UInt8 :=
  Alpha.encode message.securitySymbol
    ++ (InstrumentType.encode message.instrumentType
    ++ (encodeUInt 8 message.lastPriceOpeningReopeningLuldReferencePrice
    ++ (encodeUInt 8 message.highIndicationPriceUpperLimitPriceBand
    ++ (encodeUInt 8 message.lowIndicationPriceLowerLimitPriceBand
    ++ (encodeUInt 4 message.buyVolume
    ++ (encodeUInt 4 message.sellVolume
    ++ (SecurityStatus.encode message.securityStatus
    ++ (HaltReason.encode message.haltReason
    ++ (ShortSaleRestrictionIndicator.encode message.shortSaleRestrictionIndicator
    ++ (encodeUInt 4 message.tradingStatusId))))))))))

def decode (bytes : List UInt8) : Option (TradingStatusMessage × List UInt8) := do
  let (securitySymbol, bytes) ← Alpha.decode 11 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  let (lastPriceOpeningReopeningLuldReferencePrice, bytes) ← decodeUInt 8 bytes
  let (highIndicationPriceUpperLimitPriceBand, bytes) ← decodeUInt 8 bytes
  let (lowIndicationPriceLowerLimitPriceBand, bytes) ← decodeUInt 8 bytes
  let (buyVolume, bytes) ← decodeUInt 4 bytes
  let (sellVolume, bytes) ← decodeUInt 4 bytes
  let (securityStatus, bytes) ← SecurityStatus.decode bytes
  let (haltReason, bytes) ← HaltReason.decode bytes
  let (shortSaleRestrictionIndicator, bytes) ← ShortSaleRestrictionIndicator.decode bytes
  let (tradingStatusId, bytes) ← decodeUInt 4 bytes
  pure ({ securitySymbol, instrumentType, lastPriceOpeningReopeningLuldReferencePrice, highIndicationPriceUpperLimitPriceBand, lowIndicationPriceLowerLimitPriceBand, buyVolume, sellVolume, securityStatus, haltReason, shortSaleRestrictionIndicator, tradingStatusId }, bytes)

@[simp] theorem encode_length (message : TradingStatusMessage) : (encode message).length = 51 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, InstrumentType.encode_length, encodeUInt_length, SecurityStatus.encode_length, HaltReason.encode_length, ShortSaleRestrictionIndicator.encode_length]

theorem encode_length_pos (message : TradingStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradingStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentType.decode_encode, some_bind]
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
  rw [List.append_assoc, SecurityStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, HaltReason.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ShortSaleRestrictionIndicator.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TradingStatusMessage

/-- Any Trade Message Payload, selected by Trade Message Type -/
inductive TradeMessagePayload where
  | tradingStatusMessage (message : TradingStatusMessage) -- "S" 0x53
  deriving DecidableEq, Repr

namespace TradeMessagePayload

/-- The Trade Message Type each message is sent under -/
def tag : TradeMessagePayload → BitVec 8
  | .tradingStatusMessage _ => 83

def encode : TradeMessagePayload → List UInt8
  | .tradingStatusMessage message => TradingStatusMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : TradeMessagePayload) : (encode message).length ≤ 51 := by
  cases message with
  | tradingStatusMessage inner =>
    simp only [encode, TradingStatusMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (TradeMessagePayload × List UInt8) :=
  if tag = 83 then (TradingStatusMessage.decode bytes).map fun (message, rest) => (.tradingStatusMessage message, rest)
  else none

@[simp] theorem decode_encode (message : TradeMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end TradeMessagePayload

/-- Trade Message -/
structure TradeMessage where
  tradeMessagePayload : TradeMessagePayload
  deriving DecidableEq, Repr

namespace TradeMessage

def encode (message : TradeMessage) : List UInt8 :=
  encodeUInt 1 (TradeMessagePayload.tag message.tradeMessagePayload)
    ++ (TradeMessagePayload.encode message.tradeMessagePayload)

def decode (bytes : List UInt8) : Option (TradeMessage × List UInt8) := do
  let (tradeMessageType, bytes) ← decodeUInt 1 bytes
  let (tradeMessagePayload, bytes) ← TradeMessagePayload.decode tradeMessageType bytes
  pure ({ tradeMessagePayload }, bytes)

theorem encode_length_pos (message : TradeMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TradeMessage) : (encode message).length ≤ 52 := by
  unfold encode
  cases message.tradeMessagePayload with
  | tradingStatusMessage inner =>
    simp only [TradeMessagePayload.encode, List.length_append, encodeUInt_length, TradingStatusMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : TradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [TradeMessagePayload.decode_encode, some_bind]
  rfl

end TradeMessage

/-- Any Category Payload, selected by Message Category -/
inductive CategoryPayload where
  | administrativeMessage (message : AdministrativeMessage) -- "A" 0x41
  | controlMessage (message : ControlMessage) -- "C" 0x43
  | quoteMessage (message : QuoteMessage) -- "Q" 0x51
  | tradeMessage (message : TradeMessage) -- "T" 0x54
  deriving DecidableEq, Repr

namespace CategoryPayload

/-- The Message Category each message is sent under -/
def tag : CategoryPayload → BitVec 8
  | .administrativeMessage _ => 65
  | .controlMessage _ => 67
  | .quoteMessage _ => 81
  | .tradeMessage _ => 84

def encode : CategoryPayload → List UInt8
  | .administrativeMessage message => AdministrativeMessage.encode message
  | .controlMessage message => ControlMessage.encode message
  | .quoteMessage message => QuoteMessage.encode message
  | .tradeMessage message => TradeMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : CategoryPayload) : (encode message).length ≤ 6719 := by
  cases message with
  | administrativeMessage inner =>
    have bound_inner := AdministrativeMessage.encode_length_le inner
    simp only [encode]
    omega
  | controlMessage inner =>
    have bound_inner := ControlMessage.encode_length_le inner
    simp only [encode]
    omega
  | quoteMessage inner =>
    have bound_inner := QuoteMessage.encode_length_le inner
    simp only [encode]
    omega
  | tradeMessage inner =>
    have bound_inner := TradeMessage.encode_length_le inner
    simp only [encode]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (CategoryPayload × List UInt8) :=
  if tag = 65 then (AdministrativeMessage.decode bytes).map fun (message, rest) => (.administrativeMessage message, rest)
  else if tag = 67 then (ControlMessage.decode bytes).map fun (message, rest) => (.controlMessage message, rest)
  else if tag = 81 then (QuoteMessage.decode bytes).map fun (message, rest) => (.quoteMessage message, rest)
  else if tag = 84 then (TradeMessage.decode bytes).map fun (message, rest) => (.tradeMessage message, rest)
  else none

@[simp] theorem decode_encode (message : CategoryPayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end CategoryPayload

/-- Message -/
structure Message where
  messageLength : BitVec 16
  messageType : Alpha 1
  participantId : Alpha 1
  timestamp1 : Timestamp1
  messageId : BitVec 8
  reserved : Alpha 4
  participantReferenceNumber : BitVec 64
  categoryPayload : CategoryPayload
  deriving DecidableEq, Repr

namespace Message

def encode (message : Message) : List UInt8 :=
  encodeUInt 2 message.messageLength
    ++ (encodeUInt 1 (CategoryPayload.tag message.categoryPayload)
    ++ (Alpha.encode message.messageType
    ++ (Alpha.encode message.participantId
    ++ (Timestamp1.encode message.timestamp1
    ++ (encodeUInt 1 message.messageId
    ++ (Alpha.encode message.reserved
    ++ (encodeUInt 8 message.participantReferenceNumber
    ++ (CategoryPayload.encode message.categoryPayload))))))))

def decode (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (messageLength, bytes) ← decodeUInt 2 bytes
  let (messageCategory, bytes) ← decodeUInt 1 bytes
  let (messageType, bytes) ← Alpha.decode 1 bytes
  let (participantId, bytes) ← Alpha.decode 1 bytes
  let (timestamp1, bytes) ← Timestamp1.decode bytes
  let (messageId, bytes) ← decodeUInt 1 bytes
  let (reserved, bytes) ← Alpha.decode 4 bytes
  let (participantReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (categoryPayload, bytes) ← CategoryPayload.decode messageCategory bytes
  pure ({ messageLength, messageType, participantId, timestamp1, messageId, reserved, participantReferenceNumber, categoryPayload }, bytes)

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Message) : (encode message).length ≤ 6745 := by
  unfold encode
  cases message.categoryPayload with
  | administrativeMessage inner =>
    have bound_inner := AdministrativeMessage.encode_length_le inner
    simp only [CategoryPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, Timestamp1.encode_length]
    omega
  | controlMessage inner =>
    have bound_inner := ControlMessage.encode_length_le inner
    simp only [CategoryPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, Timestamp1.encode_length]
    omega
  | quoteMessage inner =>
    have bound_inner := QuoteMessage.encode_length_le inner
    simp only [CategoryPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, Timestamp1.encode_length]
    omega
  | tradeMessage inner =>
    have bound_inner := TradeMessage.encode_length_le inner
    simp only [CategoryPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, Timestamp1.encode_length]
    omega

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Timestamp1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [CategoryPayload.decode_encode, some_bind]
  rfl

end Message

/-- Packet -/
structure Packet where
  blockSeparator : BitVec 16
  version : BitVec 8
  blockSize : BitVec 16
  blockSequenceNumber : BitVec 32
  blockChecksum : BitVec 16
  message : Bounded 1 Message
  blockPadByte : Capped 1
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUInt 2 message.blockSeparator
    ++ (encodeUInt 1 message.version
    ++ (encodeUInt 2 message.blockSize
    ++ (encodeUInt 4 message.blockSequenceNumber
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.message.val.length)
    ++ (encodeUInt 2 message.blockChecksum
    ++ (encodeMany Message.encode message.message.val
    ++ (message.blockPadByte.val)))))))

def decode (bytes : List UInt8) : Option Packet := do
  let (blockSeparator, bytes) ← decodeUInt 2 bytes
  let (version, bytes) ← decodeUInt 1 bytes
  let (blockSize, bytes) ← decodeUInt 2 bytes
  let (blockSequenceNumber, bytes) ← decodeUInt 4 bytes
  let (messagesInBlock, bytes) ← decodeUInt 1 bytes
  let (blockChecksum, bytes) ← decodeUInt 2 bytes
  let (message_, bytes) ← decodeMany Message.decode messagesInBlock.toNat bytes
  let blockPadByte_ := bytes
  if fits_message : message_.length < 256 ^ 1 then
    if fits_blockPadByte : blockPadByte_.length ≤ 1 then
      pure { blockSeparator, version, blockSize, blockSequenceNumber, blockChecksum, message := ⟨message_, fits_message⟩, blockPadByte := ⟨blockPadByte_, fits_blockPadByte⟩ }
    else none
  else none

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Packet) : (encode message).length ≤ 1719988 := by
  have bound_message := message.message.length_lt
  have bound_message_items := encodeMany_length_le Message.encode 6745 Message.encode_length_le message.message.val
  have bound_blockPadByte := message.blockPadByte.length_le
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length]
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
  rw [decodeMany_bounded 1 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt, dite_eq_left message.blockPadByte.length_le]
  rfl

end Packet

end Omi.SiacCqsInputCtaV29B
