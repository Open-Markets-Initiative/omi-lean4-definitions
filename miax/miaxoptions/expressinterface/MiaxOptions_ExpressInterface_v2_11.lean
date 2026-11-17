import Wire

/-!
# Miami International Holdings Express Interface v2.11

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.

Note: Sequenced Data Packet is not framed: its length Sesm Packet Length is not an integer it reads

Note: Unsequenced Data Packet is not framed: its length Sesm Packet Length is not an integer it
reads

Note: a Sesm Tcp Packet that ends the session is the last of sesmTcpPacket: the decoder turns away
one that is followed, and the record carries the proof it is not

License: MIT No Attribution
-/

namespace Omi.MiaxMiaxoptionsExpressinterfaceMeiV211

/-- Call Or Put: one byte code -/
def CallOrPut.codes : List UInt8 :=
  [0x43, 0x50]

inductive CallOrPut where
  | call -- Call
  | put -- Put
  | unlisted (byte : { byte : UInt8 // byte ∉ CallOrPut.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CallOrPut

def toByte : CallOrPut → UInt8
  | .call => 0x43
  | .put => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CallOrPut :=
  if byte = 0x43 then .call
  else .put

def ofByte (byte : UInt8) : CallOrPut :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CallOrPut) : ofByte value.toByte = value := by
  cases value with
  | call => decide
  | put => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CallOrPut) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CallOrPut × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CallOrPut) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CallOrPut) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CallOrPut) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CallOrPut

/-- Restricted Option: one byte code -/
def RestrictedOption.codes : List UInt8 :=
  [0x59, 0x4E]

inductive RestrictedOption where
  | miaxWillAcceptPositionClosingOrdersOnly -- Miax Will Accept Position Closing Orders Only
  | miaxWillAcceptOpenAndClosePositions -- Miax Will Accept Open And Close Positions
  | unlisted (byte : { byte : UInt8 // byte ∉ RestrictedOption.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RestrictedOption

def toByte : RestrictedOption → UInt8
  | .miaxWillAcceptPositionClosingOrdersOnly => 0x59
  | .miaxWillAcceptOpenAndClosePositions => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RestrictedOption :=
  if byte = 0x59 then .miaxWillAcceptPositionClosingOrdersOnly
  else .miaxWillAcceptOpenAndClosePositions

def ofByte (byte : UInt8) : RestrictedOption :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RestrictedOption) : ofByte value.toByte = value := by
  cases value with
  | miaxWillAcceptPositionClosingOrdersOnly => decide
  | miaxWillAcceptOpenAndClosePositions => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RestrictedOption) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RestrictedOption × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RestrictedOption) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : RestrictedOption) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : RestrictedOption) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RestrictedOption

/-- Long Term Option: one byte code -/
def LongTermOption.codes : List UInt8 :=
  [0x59, 0x4E]

inductive LongTermOption where
  | farMonthExpirationAsDefinedByMiaxRules -- Far Month Expiration As Defined By Miax Rules
  | nearMonthExpirationAsDefinedByMiaxRules -- Near Month Expiration As Defined By Miax Rules
  | unlisted (byte : { byte : UInt8 // byte ∉ LongTermOption.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LongTermOption

def toByte : LongTermOption → UInt8
  | .farMonthExpirationAsDefinedByMiaxRules => 0x59
  | .nearMonthExpirationAsDefinedByMiaxRules => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LongTermOption :=
  if byte = 0x59 then .farMonthExpirationAsDefinedByMiaxRules
  else .nearMonthExpirationAsDefinedByMiaxRules

def ofByte (byte : UInt8) : LongTermOption :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LongTermOption) : ofByte value.toByte = value := by
  cases value with
  | farMonthExpirationAsDefinedByMiaxRules => decide
  | nearMonthExpirationAsDefinedByMiaxRules => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LongTermOption) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LongTermOption × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LongTermOption) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : LongTermOption) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : LongTermOption) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LongTermOption

/-- Active On Miax: one byte code -/
def ActiveOnMiax.codes : List UInt8 :=
  [0x41, 0x49]

inductive ActiveOnMiax where
  | activeTradableOnMiax -- Active Tradable On Miax
  | inactiveNotTradableOnMiax -- Inactive Not Tradable On Miax
  | unlisted (byte : { byte : UInt8 // byte ∉ ActiveOnMiax.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ActiveOnMiax

def toByte : ActiveOnMiax → UInt8
  | .activeTradableOnMiax => 0x41
  | .inactiveNotTradableOnMiax => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ActiveOnMiax :=
  if byte = 0x41 then .activeTradableOnMiax
  else .inactiveNotTradableOnMiax

def ofByte (byte : UInt8) : ActiveOnMiax :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ActiveOnMiax) : ofByte value.toByte = value := by
  cases value with
  | activeTradableOnMiax => decide
  | inactiveNotTradableOnMiax => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ActiveOnMiax) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ActiveOnMiax × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ActiveOnMiax) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ActiveOnMiax) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ActiveOnMiax) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ActiveOnMiax

/-- Miax Bbo Posting Increment Indicator: one byte code -/
def MiaxBboPostingIncrementIndicator.codes : List UInt8 :=
  [0x50, 0x4E, 0x44]

inductive MiaxBboPostingIncrementIndicator where
  | penny -- Penny
  | pennyNickel -- Penny Nickel
  | nickelDime -- Nickel Dime
  | unlisted (byte : { byte : UInt8 // byte ∉ MiaxBboPostingIncrementIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MiaxBboPostingIncrementIndicator

def toByte : MiaxBboPostingIncrementIndicator → UInt8
  | .penny => 0x50
  | .pennyNickel => 0x4E
  | .nickelDime => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MiaxBboPostingIncrementIndicator :=
  if byte = 0x50 then .penny
  else if byte = 0x4E then .pennyNickel
  else .nickelDime

def ofByte (byte : UInt8) : MiaxBboPostingIncrementIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MiaxBboPostingIncrementIndicator) : ofByte value.toByte = value := by
  cases value with
  | penny => decide
  | pennyNickel => decide
  | nickelDime => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MiaxBboPostingIncrementIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MiaxBboPostingIncrementIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MiaxBboPostingIncrementIndicator) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : MiaxBboPostingIncrementIndicator) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : MiaxBboPostingIncrementIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MiaxBboPostingIncrementIndicator

/-- Quote Acceptance Increment Indicator: one byte code -/
def QuoteAcceptanceIncrementIndicator.codes : List UInt8 :=
  [0x50, 0x4E, 0x44]

inductive QuoteAcceptanceIncrementIndicator where
  | penny -- Penny
  | pennyNickel -- Penny Nickel
  | nickelDime -- Nickel Dime
  | unlisted (byte : { byte : UInt8 // byte ∉ QuoteAcceptanceIncrementIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace QuoteAcceptanceIncrementIndicator

def toByte : QuoteAcceptanceIncrementIndicator → UInt8
  | .penny => 0x50
  | .pennyNickel => 0x4E
  | .nickelDime => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : QuoteAcceptanceIncrementIndicator :=
  if byte = 0x50 then .penny
  else if byte = 0x4E then .pennyNickel
  else .nickelDime

def ofByte (byte : UInt8) : QuoteAcceptanceIncrementIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : QuoteAcceptanceIncrementIndicator) : ofByte value.toByte = value := by
  cases value with
  | penny => decide
  | pennyNickel => decide
  | nickelDime => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : QuoteAcceptanceIncrementIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (QuoteAcceptanceIncrementIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : QuoteAcceptanceIncrementIndicator) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : QuoteAcceptanceIncrementIndicator) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : QuoteAcceptanceIncrementIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end QuoteAcceptanceIncrementIndicator

/-- Opening Underlying Market Code: one byte code -/
def OpeningUnderlyingMarketCode.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x45, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x50, 0x51, 0x54, 0x55, 0x56, 0x57, 0x58, 0x59, 0x5A]

inductive OpeningUnderlyingMarketCode where
  | nyseAmex -- Nyse Amex
  | nasdaqOmxBx -- Nasdaq Omx Bx
  | nationalStockExchange -- National Stock Exchange
  | finraAdf -- Finra Adf
  | marketIndependentAnyMarketThatOpensFirst -- Market Independent Any Market That Opens First
  | miaxPearlEquities -- Miax Pearl Equities
  | internationalSecuritiesExchange -- International Securities Exchange
  | edgaExchangeInc -- Edga Exchange Inc
  | edgxExchangeInc -- Edgx Exchange Inc
  | ltse -- Ltse
  | chicagoStockExchange -- Chicago Stock Exchange
  | nyseEuronext -- Nyse Euronext
  | nyseArcaExchange -- Nyse Arca Exchange
  | nasdaqOmxViaUtpFeed -- Nasdaq Omx Via Utp Feed
  | nasdaqOmxViaCtaFeed -- Nasdaq Omx Via Cta Feed
  | memx -- Memx
  | iex -- Iex
  | cboeStockExchangeCbsx -- Cboe Stock Exchange Cbsx
  | nasdaqOmxPhlx -- Nasdaq Omx Phlx
  | batsYExchangeInc -- Bats Y Exchange Inc
  | batsExchangeInc -- Bats Exchange Inc
  | unlisted (byte : { byte : UInt8 // byte ∉ OpeningUnderlyingMarketCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OpeningUnderlyingMarketCode

def toByte : OpeningUnderlyingMarketCode → UInt8
  | .nyseAmex => 0x41
  | .nasdaqOmxBx => 0x42
  | .nationalStockExchange => 0x43
  | .finraAdf => 0x44
  | .marketIndependentAnyMarketThatOpensFirst => 0x45
  | .miaxPearlEquities => 0x48
  | .internationalSecuritiesExchange => 0x49
  | .edgaExchangeInc => 0x4A
  | .edgxExchangeInc => 0x4B
  | .ltse => 0x4C
  | .chicagoStockExchange => 0x4D
  | .nyseEuronext => 0x4E
  | .nyseArcaExchange => 0x50
  | .nasdaqOmxViaUtpFeed => 0x51
  | .nasdaqOmxViaCtaFeed => 0x54
  | .memx => 0x55
  | .iex => 0x56
  | .cboeStockExchangeCbsx => 0x57
  | .nasdaqOmxPhlx => 0x58
  | .batsYExchangeInc => 0x59
  | .batsExchangeInc => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OpeningUnderlyingMarketCode :=
  if byte = 0x41 then .nyseAmex
  else if byte = 0x42 then .nasdaqOmxBx
  else if byte = 0x43 then .nationalStockExchange
  else if byte = 0x44 then .finraAdf
  else if byte = 0x45 then .marketIndependentAnyMarketThatOpensFirst
  else if byte = 0x48 then .miaxPearlEquities
  else if byte = 0x49 then .internationalSecuritiesExchange
  else if byte = 0x4A then .edgaExchangeInc
  else if byte = 0x4B then .edgxExchangeInc
  else if byte = 0x4C then .ltse
  else if byte = 0x4D then .chicagoStockExchange
  else if byte = 0x4E then .nyseEuronext
  else if byte = 0x50 then .nyseArcaExchange
  else if byte = 0x51 then .nasdaqOmxViaUtpFeed
  else if byte = 0x54 then .nasdaqOmxViaCtaFeed
  else if byte = 0x55 then .memx
  else if byte = 0x56 then .iex
  else if byte = 0x57 then .cboeStockExchangeCbsx
  else if byte = 0x58 then .nasdaqOmxPhlx
  else if byte = 0x59 then .batsYExchangeInc
  else .batsExchangeInc

def ofByte (byte : UInt8) : OpeningUnderlyingMarketCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OpeningUnderlyingMarketCode) : ofByte value.toByte = value := by
  cases value with
  | nyseAmex => decide
  | nasdaqOmxBx => decide
  | nationalStockExchange => decide
  | finraAdf => decide
  | marketIndependentAnyMarketThatOpensFirst => decide
  | miaxPearlEquities => decide
  | internationalSecuritiesExchange => decide
  | edgaExchangeInc => decide
  | edgxExchangeInc => decide
  | ltse => decide
  | chicagoStockExchange => decide
  | nyseEuronext => decide
  | nyseArcaExchange => decide
  | nasdaqOmxViaUtpFeed => decide
  | nasdaqOmxViaCtaFeed => decide
  | memx => decide
  | iex => decide
  | cboeStockExchangeCbsx => decide
  | nasdaqOmxPhlx => decide
  | batsYExchangeInc => decide
  | batsExchangeInc => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OpeningUnderlyingMarketCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OpeningUnderlyingMarketCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OpeningUnderlyingMarketCode) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OpeningUnderlyingMarketCode) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OpeningUnderlyingMarketCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OpeningUnderlyingMarketCode

/-- Mpv Class: one byte code -/
def MpvClass.codes : List UInt8 :=
  [0x50, 0x4E, 0x44]

inductive MpvClass where
  | penny -- Penny
  | pennyNickel -- Penny Nickel
  | nickelDime -- Nickel Dime
  | unlisted (byte : { byte : UInt8 // byte ∉ MpvClass.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MpvClass

def toByte : MpvClass → UInt8
  | .penny => 0x50
  | .pennyNickel => 0x4E
  | .nickelDime => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MpvClass :=
  if byte = 0x50 then .penny
  else if byte = 0x4E then .pennyNickel
  else .nickelDime

def ofByte (byte : UInt8) : MpvClass :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MpvClass) : ofByte value.toByte = value := by
  cases value with
  | penny => decide
  | pennyNickel => decide
  | nickelDime => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MpvClass) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MpvClass × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MpvClass) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : MpvClass) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : MpvClass) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MpvClass

/-- E Quote Request Status: one byte code -/
def EQuoteRequestStatus.codes : List UInt8 :=
  [0x20, 0x49, 0x41, 0x42, 0x56, 0x4D, 0x50, 0x54, 0x53, 0x31, 0x32, 0x33, 0x34, 0x55, 0x35, 0x58, 0x4B, 0x43, 0x44, 0x59, 0x5A, 0x2A, 0x4A, 0x47, 0x37, 0x38]

inductive EQuoteRequestStatus where
  | requestAcceptedSuccessfully -- Request Accepted Successfully
  | invalidProductId -- Invalid Product Id
  | noEventWithSuchEventId -- No Event With Such Event Id
  | invalidEQuoteAction -- Invalid E Quote Action
  | invalidSize -- Invalid Size
  | eQuoteSizeMinimumRequiredSize -- E Quote Size Minimum Required Size
  | invalidPrice -- Invalid Price
  | invalidEQuoteType -- Invalid E Quote Type
  | invalidSide -- Invalid Side
  | eQuoteNotPermittedForThisPrice -- E Quote Not Permitted For This Price
  | eQuoteNotPermittedForThisSide -- E Quote Not Permitted For This Side
  | eQuoteRepresentedByTargetMessageIdWasNotFound -- E Quote Represented By Target Message Id Was Not Found
  | clientMessageIdNotUnique -- Client Message Id Not Unique
  | unknownMpid -- Unknown Mpid
  | rejectedDueToQuoteProtection -- Rejected Due To Quote Protection
  | notPermitted -- Not Permitted
  | testEQuoteSuccessfullyAcceptedPriorToLqwOrSetLqwAsApplicableButNotPlacedOnMiaxBook -- Test E Quote Successfully Accepted Prior To Lqw Or Set Lqw As Applicable But Not Placed On Miax Book
  | miaxClosedForTradingOfThisProductRequestCannotBeCompleted -- Miax Closed For Trading Of This Product Request Cannot Be Completed
  | rejectedDueToSelfCrossingPrimeAgencyOrder -- Rejected Due To Self Crossing Prime Agency Order
  | rejectedDueToSingleSideLiquidityProtectionInEffect -- Rejected Due To Single Side Liquidity Protection In Effect
  | undefinedError -- Undefined Error
  | downgradedFromOlderVersion -- Downgraded From Older Version
  | outsidePriceRangeForStrategy -- Outside Price Range For Strategy
  | complexFeatureIsDisabled -- Complex Feature Is Disabled
  | rejectedDueToStockClearingAccountUnderlyingMpidOrDtcAccountNumberNotConfigured -- Rejected Due To Stock Clearing Account Underlying Mpid Or Dtc Account Number Not Configured
  | invalidSellShortIndicator -- Invalid Sell Short Indicator
  | unlisted (byte : { byte : UInt8 // byte ∉ EQuoteRequestStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EQuoteRequestStatus

def toByte : EQuoteRequestStatus → UInt8
  | .requestAcceptedSuccessfully => 0x20
  | .invalidProductId => 0x49
  | .noEventWithSuchEventId => 0x41
  | .invalidEQuoteAction => 0x42
  | .invalidSize => 0x56
  | .eQuoteSizeMinimumRequiredSize => 0x4D
  | .invalidPrice => 0x50
  | .invalidEQuoteType => 0x54
  | .invalidSide => 0x53
  | .eQuoteNotPermittedForThisPrice => 0x31
  | .eQuoteNotPermittedForThisSide => 0x32
  | .eQuoteRepresentedByTargetMessageIdWasNotFound => 0x33
  | .clientMessageIdNotUnique => 0x34
  | .unknownMpid => 0x55
  | .rejectedDueToQuoteProtection => 0x35
  | .notPermitted => 0x58
  | .testEQuoteSuccessfullyAcceptedPriorToLqwOrSetLqwAsApplicableButNotPlacedOnMiaxBook => 0x4B
  | .miaxClosedForTradingOfThisProductRequestCannotBeCompleted => 0x43
  | .rejectedDueToSelfCrossingPrimeAgencyOrder => 0x44
  | .rejectedDueToSingleSideLiquidityProtectionInEffect => 0x59
  | .undefinedError => 0x5A
  | .downgradedFromOlderVersion => 0x2A
  | .outsidePriceRangeForStrategy => 0x4A
  | .complexFeatureIsDisabled => 0x47
  | .rejectedDueToStockClearingAccountUnderlyingMpidOrDtcAccountNumberNotConfigured => 0x37
  | .invalidSellShortIndicator => 0x38
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EQuoteRequestStatus :=
  if byte = 0x20 then .requestAcceptedSuccessfully
  else if byte = 0x49 then .invalidProductId
  else if byte = 0x41 then .noEventWithSuchEventId
  else if byte = 0x42 then .invalidEQuoteAction
  else if byte = 0x56 then .invalidSize
  else if byte = 0x4D then .eQuoteSizeMinimumRequiredSize
  else if byte = 0x50 then .invalidPrice
  else if byte = 0x54 then .invalidEQuoteType
  else if byte = 0x53 then .invalidSide
  else if byte = 0x31 then .eQuoteNotPermittedForThisPrice
  else if byte = 0x32 then .eQuoteNotPermittedForThisSide
  else if byte = 0x33 then .eQuoteRepresentedByTargetMessageIdWasNotFound
  else if byte = 0x34 then .clientMessageIdNotUnique
  else if byte = 0x55 then .unknownMpid
  else if byte = 0x35 then .rejectedDueToQuoteProtection
  else if byte = 0x58 then .notPermitted
  else if byte = 0x4B then .testEQuoteSuccessfullyAcceptedPriorToLqwOrSetLqwAsApplicableButNotPlacedOnMiaxBook
  else if byte = 0x43 then .miaxClosedForTradingOfThisProductRequestCannotBeCompleted
  else if byte = 0x44 then .rejectedDueToSelfCrossingPrimeAgencyOrder
  else if byte = 0x59 then .rejectedDueToSingleSideLiquidityProtectionInEffect
  else if byte = 0x5A then .undefinedError
  else if byte = 0x2A then .downgradedFromOlderVersion
  else if byte = 0x4A then .outsidePriceRangeForStrategy
  else if byte = 0x47 then .complexFeatureIsDisabled
  else if byte = 0x37 then .rejectedDueToStockClearingAccountUnderlyingMpidOrDtcAccountNumberNotConfigured
  else .invalidSellShortIndicator

def ofByte (byte : UInt8) : EQuoteRequestStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EQuoteRequestStatus) : ofByte value.toByte = value := by
  cases value with
  | requestAcceptedSuccessfully => decide
  | invalidProductId => decide
  | noEventWithSuchEventId => decide
  | invalidEQuoteAction => decide
  | invalidSize => decide
  | eQuoteSizeMinimumRequiredSize => decide
  | invalidPrice => decide
  | invalidEQuoteType => decide
  | invalidSide => decide
  | eQuoteNotPermittedForThisPrice => decide
  | eQuoteNotPermittedForThisSide => decide
  | eQuoteRepresentedByTargetMessageIdWasNotFound => decide
  | clientMessageIdNotUnique => decide
  | unknownMpid => decide
  | rejectedDueToQuoteProtection => decide
  | notPermitted => decide
  | testEQuoteSuccessfullyAcceptedPriorToLqwOrSetLqwAsApplicableButNotPlacedOnMiaxBook => decide
  | miaxClosedForTradingOfThisProductRequestCannotBeCompleted => decide
  | rejectedDueToSelfCrossingPrimeAgencyOrder => decide
  | rejectedDueToSingleSideLiquidityProtectionInEffect => decide
  | undefinedError => decide
  | downgradedFromOlderVersion => decide
  | outsidePriceRangeForStrategy => decide
  | complexFeatureIsDisabled => decide
  | rejectedDueToStockClearingAccountUnderlyingMpidOrDtcAccountNumberNotConfigured => decide
  | invalidSellShortIndicator => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : EQuoteRequestStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (EQuoteRequestStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : EQuoteRequestStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : EQuoteRequestStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : EQuoteRequestStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end EQuoteRequestStatus

/-- System Status: one byte code -/
def SystemStatus.codes : List UInt8 :=
  [0x53, 0x50, 0x43, 0x4C, 0x58, 0x31, 0x32]

inductive SystemStatus where
  | firmInterfaceStartUpTimeReadyToAcceptApplicationMessages -- Firm Interface Start Up Time Ready To Accept Application Messages
  | lqwReadyToAcceptOfficialQuotes -- Lqw Ready To Accept Official Quotes
  | endOfSystemHours -- End Of System Hours
  | preLqwNotReadyToAcceptOfficialQuotes -- Pre Lqw Not Ready To Accept Official Quotes
  | systemCurrentlyNotAcceptingMessages -- System Currently Not Accepting Messages
  | startOfTestSessionSentBeforeTests -- Start Of Test Session Sent Before Tests
  | endOfTestSession -- End Of Test Session
  | unlisted (byte : { byte : UInt8 // byte ∉ SystemStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SystemStatus

def toByte : SystemStatus → UInt8
  | .firmInterfaceStartUpTimeReadyToAcceptApplicationMessages => 0x53
  | .lqwReadyToAcceptOfficialQuotes => 0x50
  | .endOfSystemHours => 0x43
  | .preLqwNotReadyToAcceptOfficialQuotes => 0x4C
  | .systemCurrentlyNotAcceptingMessages => 0x58
  | .startOfTestSessionSentBeforeTests => 0x31
  | .endOfTestSession => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SystemStatus :=
  if byte = 0x53 then .firmInterfaceStartUpTimeReadyToAcceptApplicationMessages
  else if byte = 0x50 then .lqwReadyToAcceptOfficialQuotes
  else if byte = 0x43 then .endOfSystemHours
  else if byte = 0x4C then .preLqwNotReadyToAcceptOfficialQuotes
  else if byte = 0x58 then .systemCurrentlyNotAcceptingMessages
  else if byte = 0x31 then .startOfTestSessionSentBeforeTests
  else .endOfTestSession

def ofByte (byte : UInt8) : SystemStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SystemStatus) : ofByte value.toByte = value := by
  cases value with
  | firmInterfaceStartUpTimeReadyToAcceptApplicationMessages => decide
  | lqwReadyToAcceptOfficialQuotes => decide
  | endOfSystemHours => decide
  | preLqwNotReadyToAcceptOfficialQuotes => decide
  | systemCurrentlyNotAcceptingMessages => decide
  | startOfTestSessionSentBeforeTests => decide
  | endOfTestSession => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SystemStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SystemStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SystemStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SystemStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SystemStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SystemStatus

/-- Trading Status: one byte code -/
def TradingStatus.codes : List UInt8 :=
  [0x48, 0x43, 0x52, 0x4F]

inductive TradingStatus where
  | halted -- Halted
  | closing -- Closing
  | resume -- Resume
  | open_ -- Open
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingStatus

def toByte : TradingStatus → UInt8
  | .halted => 0x48
  | .closing => 0x43
  | .resume => 0x52
  | .open_ => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingStatus :=
  if byte = 0x48 then .halted
  else if byte = 0x43 then .closing
  else if byte = 0x52 then .resume
  else .open_

def ofByte (byte : UInt8) : TradingStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingStatus) : ofByte value.toByte = value := by
  cases value with
  | halted => decide
  | closing => decide
  | resume => decide
  | open_ => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradingStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradingStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradingStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TradingStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TradingStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradingStatus

/-- Event Reason: one byte code -/
def EventReason.codes : List UInt8 :=
  [0x41, 0x4D]

inductive EventReason where
  | thisEventResultedFromAutomaticmarketDrivenEvent -- This Event Resulted From Automaticmarket Driven Event
  | miaxManuallyInitiatedThisEvent -- Miax Manually Initiated This Event
  | unlisted (byte : { byte : UInt8 // byte ∉ EventReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventReason

def toByte : EventReason → UInt8
  | .thisEventResultedFromAutomaticmarketDrivenEvent => 0x41
  | .miaxManuallyInitiatedThisEvent => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventReason :=
  if byte = 0x41 then .thisEventResultedFromAutomaticmarketDrivenEvent
  else .miaxManuallyInitiatedThisEvent

def ofByte (byte : UInt8) : EventReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventReason) : ofByte value.toByte = value := by
  cases value with
  | thisEventResultedFromAutomaticmarketDrivenEvent => decide
  | miaxManuallyInitiatedThisEvent => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : EventReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (EventReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : EventReason) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : EventReason) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : EventReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end EventReason

/-- Action: one byte code -/
def Action.codes : List UInt8 :=
  [0x53, 0x44]

inductive Action where
  | setAddOrUpdateArmSettings -- Set Add Or Update Arm Settings
  | deleteArmSettings -- Delete Arm Settings
  | unlisted (byte : { byte : UInt8 // byte ∉ Action.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Action

def toByte : Action → UInt8
  | .setAddOrUpdateArmSettings => 0x53
  | .deleteArmSettings => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Action :=
  if byte = 0x53 then .setAddOrUpdateArmSettings
  else .deleteArmSettings

def ofByte (byte : UInt8) : Action :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Action) : ofByte value.toByte = value := by
  cases value with
  | setAddOrUpdateArmSettings => decide
  | deleteArmSettings => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Action) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Action × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Action) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Action) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Action) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Action

/-- Source: one byte code -/
def Source.codes : List UInt8 :=
  [0x54, 0x45]

inductive Source where
  | changesCarriedOutByTheFirmViaMei -- Changes Carried Out By The Firm Via Mei
  | changesCarriedOutByTheExchangeGlobalDefaultChangesOrFirmRequestedSettingsAppliedManually -- Changes Carried Out By The Exchange Global Default Changes Or Firm Requested Settings Applied Manually
  | unlisted (byte : { byte : UInt8 // byte ∉ Source.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Source

def toByte : Source → UInt8
  | .changesCarriedOutByTheFirmViaMei => 0x54
  | .changesCarriedOutByTheExchangeGlobalDefaultChangesOrFirmRequestedSettingsAppliedManually => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Source :=
  if byte = 0x54 then .changesCarriedOutByTheFirmViaMei
  else .changesCarriedOutByTheExchangeGlobalDefaultChangesOrFirmRequestedSettingsAppliedManually

def ofByte (byte : UInt8) : Source :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Source) : ofByte value.toByte = value := by
  cases value with
  | changesCarriedOutByTheFirmViaMei => decide
  | changesCarriedOutByTheExchangeGlobalDefaultChangesOrFirmRequestedSettingsAppliedManually => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Source) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Source × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Source) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Source) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Source) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Source

/-- Security Id Scope: one byte code -/
def SecurityIdScope.codes : List UInt8 :=
  [0x50, 0x53]

inductive SecurityIdScope where
  | securityIdSpecifiesOptionProductId -- Security Id Specifies Option Product Id
  | securityIdSpecifiesComplexStrategyId -- Security Id Specifies Complex Strategy Id
  | unlisted (byte : { byte : UInt8 // byte ∉ SecurityIdScope.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SecurityIdScope

def toByte : SecurityIdScope → UInt8
  | .securityIdSpecifiesOptionProductId => 0x50
  | .securityIdSpecifiesComplexStrategyId => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SecurityIdScope :=
  if byte = 0x50 then .securityIdSpecifiesOptionProductId
  else .securityIdSpecifiesComplexStrategyId

def ofByte (byte : UInt8) : SecurityIdScope :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SecurityIdScope) : ofByte value.toByte = value := by
  cases value with
  | securityIdSpecifiesOptionProductId => decide
  | securityIdSpecifiesComplexStrategyId => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SecurityIdScope) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SecurityIdScope × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SecurityIdScope) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SecurityIdScope) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SecurityIdScope) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SecurityIdScope

/-- Side: one byte code -/
def Side.codes : List UInt8 :=
  [0x42, 0x41, 0x4E, 0x53]

inductive Side where
  | bid -- Bid
  | ask -- Ask
  | notApplicable -- Not Applicable
  | sold -- Sold
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .bid => 0x42
  | .ask => 0x41
  | .notApplicable => 0x4E
  | .sold => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x42 then .bid
  else if byte = 0x41 then .ask
  else if byte = 0x4E then .notApplicable
  else .sold

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | bid => decide
  | ask => decide
  | notApplicable => decide
  | sold => decide
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

/-- Notification Type: one byte code -/
def NotificationType.codes : List UInt8 :=
  [0x54, 0x52, 0x2A]

inductive NotificationType where
  | arm2UnderlyingLevelProtectionTriggered -- Arm 2 Underlying Level Protection Triggered
  | arm2UnderlyingLevelProtectionReset -- Arm 2 Underlying Level Protection Reset
  | downgradedFromOlderVersion -- Downgraded From Older Version
  | unlisted (byte : { byte : UInt8 // byte ∉ NotificationType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace NotificationType

def toByte : NotificationType → UInt8
  | .arm2UnderlyingLevelProtectionTriggered => 0x54
  | .arm2UnderlyingLevelProtectionReset => 0x52
  | .downgradedFromOlderVersion => 0x2A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : NotificationType :=
  if byte = 0x54 then .arm2UnderlyingLevelProtectionTriggered
  else if byte = 0x52 then .arm2UnderlyingLevelProtectionReset
  else .downgradedFromOlderVersion

def ofByte (byte : UInt8) : NotificationType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : NotificationType) : ofByte value.toByte = value := by
  cases value with
  | arm2UnderlyingLevelProtectionTriggered => decide
  | arm2UnderlyingLevelProtectionReset => decide
  | downgradedFromOlderVersion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : NotificationType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (NotificationType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : NotificationType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : NotificationType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : NotificationType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end NotificationType

/-- Update Reason: one byte code -/
def UpdateReason.codes : List UInt8 :=
  [0x4E, 0x55, 0x2A]

inductive UpdateReason where
  | newStrategyCreated -- New Strategy Created
  | strategyDefinitionUpdated -- Strategy Definition Updated
  | downgradedForOlderVersion -- Downgraded For Older Version
  | unlisted (byte : { byte : UInt8 // byte ∉ UpdateReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace UpdateReason

def toByte : UpdateReason → UInt8
  | .newStrategyCreated => 0x4E
  | .strategyDefinitionUpdated => 0x55
  | .downgradedForOlderVersion => 0x2A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : UpdateReason :=
  if byte = 0x4E then .newStrategyCreated
  else if byte = 0x55 then .strategyDefinitionUpdated
  else .downgradedForOlderVersion

def ofByte (byte : UInt8) : UpdateReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : UpdateReason) : ofByte value.toByte = value := by
  cases value with
  | newStrategyCreated => decide
  | strategyDefinitionUpdated => decide
  | downgradedForOlderVersion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : UpdateReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (UpdateReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : UpdateReason) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : UpdateReason) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : UpdateReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end UpdateReason

/-- Leg Side: one byte code -/
def LegSide.codes : List UInt8 :=
  [0x42, 0x41]

inductive LegSide where
  | bid -- Bid
  | ask -- Ask
  | unlisted (byte : { byte : UInt8 // byte ∉ LegSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LegSide

def toByte : LegSide → UInt8
  | .bid => 0x42
  | .ask => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LegSide :=
  if byte = 0x42 then .bid
  else .ask

def ofByte (byte : UInt8) : LegSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LegSide) : ofByte value.toByte = value := by
  cases value with
  | bid => decide
  | ask => decide
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

/-- Liquidity Type: one byte code -/
def LiquidityType.codes : List UInt8 :=
  [0x51, 0x45, 0x43, 0x58]

inductive LiquidityType where
  | simpleQuote -- Simple Quote
  | simpleEQuote -- Simple E Quote
  | complexEQuote -- Complex E Quote
  | reservedForFutureUse -- Reserved For Future Use
  | unlisted (byte : { byte : UInt8 // byte ∉ LiquidityType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LiquidityType

def toByte : LiquidityType → UInt8
  | .simpleQuote => 0x51
  | .simpleEQuote => 0x45
  | .complexEQuote => 0x43
  | .reservedForFutureUse => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LiquidityType :=
  if byte = 0x51 then .simpleQuote
  else if byte = 0x45 then .simpleEQuote
  else if byte = 0x43 then .complexEQuote
  else .reservedForFutureUse

def ofByte (byte : UInt8) : LiquidityType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LiquidityType) : ofByte value.toByte = value := by
  cases value with
  | simpleQuote => decide
  | simpleEQuote => decide
  | complexEQuote => decide
  | reservedForFutureUse => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LiquidityType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LiquidityType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LiquidityType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : LiquidityType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : LiquidityType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LiquidityType

/-- Quotee Quote Side: one byte code -/
def QuoteeQuoteSide.codes : List UInt8 :=
  [0x42, 0x41]

inductive QuoteeQuoteSide where
  | bid -- Bid
  | ask -- Ask
  | unlisted (byte : { byte : UInt8 // byte ∉ QuoteeQuoteSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace QuoteeQuoteSide

def toByte : QuoteeQuoteSide → UInt8
  | .bid => 0x42
  | .ask => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : QuoteeQuoteSide :=
  if byte = 0x42 then .bid
  else .ask

def ofByte (byte : UInt8) : QuoteeQuoteSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : QuoteeQuoteSide) : ofByte value.toByte = value := by
  cases value with
  | bid => decide
  | ask => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : QuoteeQuoteSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (QuoteeQuoteSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : QuoteeQuoteSide) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : QuoteeQuoteSide) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : QuoteeQuoteSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end QuoteeQuoteSide

/-- Cancel Reason: one byte code -/
def CancelReason.codes : List UInt8 :=
  [0x53, 0x57, 0x43, 0x4B, 0x4C, 0x4D, 0x4E, 0x4A, 0x52, 0x51, 0x42, 0x50, 0x41, 0x2A]

inductive CancelReason where
  | cancelForUnexecutedPartOfSimplecomplexEQuote -- Cancel For Unexecuted Part Of Simplecomplex E Quote
  | cancelForQuoteUnusedInOpeningReopeningOrClosingForBackwardCompatibilityWithMeiAppProtocolVersionsLessThan210AWCancelReasonCodeWillAlsoBeUsedToIndicateAnExistingQuoteCancelationDueToAReplacementQuoteReject -- Cancel For Quote Unused In Opening Reopening Or Closing For Backward Compatibility With Mei App Protocol Versions Less Than 2.10 A W Cancel Reason Code Will Also Be Used To Indicate An Existing Quote Cancelation Due To A Replacement Quote Reject
  | cancelOfRestingSimpleQuoteCrossedByOppositeSideQuoteOfSameMpid -- Cancel Of Resting Simple Quote Crossed By Opposite Side Quote Of Same Mpid
  | complexStrategyLegHasWideMbboOnlyApplicableToComplexEQuotes -- Complex Strategy Leg Has Wide Mbbo Only Applicable To Complex E Quotes
  | complexStrategyLegHasPrimeAuction -- Complex Strategy Leg Has Prime Auction
  | complexStrategyLegHasRouteTimer -- Complex Strategy Leg Has Route Timer
  | complexStrategyLegHasLiquidityRefreshTimer -- Complex Strategy Leg Has Liquidity Refresh Timer
  | complexStrategyAuctionInProgress -- Complex Strategy Auction In Progress
  | complexStrategyLegHasLiquidityExposureTimer -- Complex Strategy Leg Has Liquidity Exposure Timer
  | strategyIsNotOpenForTrading -- Strategy Is Not Open For Trading
  | canceledDueToSingleSideLiquidityProtectionTrigger -- Canceled Due To Single Side Liquidity Protection Trigger
  | reserved -- Reserved
  | restingQuoteCanceledDueToReplacementQuoteReject -- Resting Quote Canceled Due To Replacement Quote Reject
  | downgradedForOlderVersion -- Downgraded For Older Version
  | unlisted (byte : { byte : UInt8 // byte ∉ CancelReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CancelReason

def toByte : CancelReason → UInt8
  | .cancelForUnexecutedPartOfSimplecomplexEQuote => 0x53
  | .cancelForQuoteUnusedInOpeningReopeningOrClosingForBackwardCompatibilityWithMeiAppProtocolVersionsLessThan210AWCancelReasonCodeWillAlsoBeUsedToIndicateAnExistingQuoteCancelationDueToAReplacementQuoteReject => 0x57
  | .cancelOfRestingSimpleQuoteCrossedByOppositeSideQuoteOfSameMpid => 0x43
  | .complexStrategyLegHasWideMbboOnlyApplicableToComplexEQuotes => 0x4B
  | .complexStrategyLegHasPrimeAuction => 0x4C
  | .complexStrategyLegHasRouteTimer => 0x4D
  | .complexStrategyLegHasLiquidityRefreshTimer => 0x4E
  | .complexStrategyAuctionInProgress => 0x4A
  | .complexStrategyLegHasLiquidityExposureTimer => 0x52
  | .strategyIsNotOpenForTrading => 0x51
  | .canceledDueToSingleSideLiquidityProtectionTrigger => 0x42
  | .reserved => 0x50
  | .restingQuoteCanceledDueToReplacementQuoteReject => 0x41
  | .downgradedForOlderVersion => 0x2A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CancelReason :=
  if byte = 0x53 then .cancelForUnexecutedPartOfSimplecomplexEQuote
  else if byte = 0x57 then .cancelForQuoteUnusedInOpeningReopeningOrClosingForBackwardCompatibilityWithMeiAppProtocolVersionsLessThan210AWCancelReasonCodeWillAlsoBeUsedToIndicateAnExistingQuoteCancelationDueToAReplacementQuoteReject
  else if byte = 0x43 then .cancelOfRestingSimpleQuoteCrossedByOppositeSideQuoteOfSameMpid
  else if byte = 0x4B then .complexStrategyLegHasWideMbboOnlyApplicableToComplexEQuotes
  else if byte = 0x4C then .complexStrategyLegHasPrimeAuction
  else if byte = 0x4D then .complexStrategyLegHasRouteTimer
  else if byte = 0x4E then .complexStrategyLegHasLiquidityRefreshTimer
  else if byte = 0x4A then .complexStrategyAuctionInProgress
  else if byte = 0x52 then .complexStrategyLegHasLiquidityExposureTimer
  else if byte = 0x51 then .strategyIsNotOpenForTrading
  else if byte = 0x42 then .canceledDueToSingleSideLiquidityProtectionTrigger
  else if byte = 0x50 then .reserved
  else if byte = 0x41 then .restingQuoteCanceledDueToReplacementQuoteReject
  else .downgradedForOlderVersion

def ofByte (byte : UInt8) : CancelReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CancelReason) : ofByte value.toByte = value := by
  cases value with
  | cancelForUnexecutedPartOfSimplecomplexEQuote => decide
  | cancelForQuoteUnusedInOpeningReopeningOrClosingForBackwardCompatibilityWithMeiAppProtocolVersionsLessThan210AWCancelReasonCodeWillAlsoBeUsedToIndicateAnExistingQuoteCancelationDueToAReplacementQuoteReject => decide
  | cancelOfRestingSimpleQuoteCrossedByOppositeSideQuoteOfSameMpid => decide
  | complexStrategyLegHasWideMbboOnlyApplicableToComplexEQuotes => decide
  | complexStrategyLegHasPrimeAuction => decide
  | complexStrategyLegHasRouteTimer => decide
  | complexStrategyLegHasLiquidityRefreshTimer => decide
  | complexStrategyAuctionInProgress => decide
  | complexStrategyLegHasLiquidityExposureTimer => decide
  | strategyIsNotOpenForTrading => decide
  | canceledDueToSingleSideLiquidityProtectionTrigger => decide
  | reserved => decide
  | restingQuoteCanceledDueToReplacementQuoteReject => decide
  | downgradedForOlderVersion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CancelReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CancelReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CancelReason) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CancelReason) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CancelReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CancelReason

/-- Trade Status: one byte code -/
def TradeStatus.codes : List UInt8 :=
  [0x45]

inductive TradeStatus where
  | newExecution -- New Execution
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeStatus

def toByte : TradeStatus → UInt8
  | .newExecution => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : TradeStatus :=
  .newExecution

def ofByte (byte : UInt8) : TradeStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeStatus) : ofByte value.toByte = value := by
  cases value with
  | newExecution => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TradeStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TradeStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeStatus

/-- Stock Sell Short Indicator: one byte code -/
def StockSellShortIndicator.codes : List UInt8 :=
  [0x4E, 0x59, 0x45, 0x20]

inductive StockSellShortIndicator where
  | notShort -- Not Short
  | short -- Short
  | shortExempt -- Short Exempt
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ StockSellShortIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace StockSellShortIndicator

def toByte : StockSellShortIndicator → UInt8
  | .notShort => 0x4E
  | .short => 0x59
  | .shortExempt => 0x45
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : StockSellShortIndicator :=
  if byte = 0x4E then .notShort
  else if byte = 0x59 then .short
  else if byte = 0x45 then .shortExempt
  else .notApplicable

def ofByte (byte : UInt8) : StockSellShortIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : StockSellShortIndicator) : ofByte value.toByte = value := by
  cases value with
  | notShort => decide
  | short => decide
  | shortExempt => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : StockSellShortIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (StockSellShortIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : StockSellShortIndicator) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : StockSellShortIndicator) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : StockSellShortIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end StockSellShortIndicator

/-- Arm Settings Update Status: one byte code -/
def ArmSettingsUpdateStatus.codes : List UInt8 :=
  [0x20, 0x41, 0x42, 0x43, 0x50, 0x44, 0x4D, 0x55, 0x58, 0x4E, 0x5A, 0x45]

inductive ArmSettingsUpdateStatus where
  | settingsAppliedSuccessfully -- Settings Applied Successfully
  | invalidAction -- Invalid Action
  | invalidOriginMultiplierValue -- Invalid Origin Multiplier Value
  | enhancedArmFeatureIsDisabled -- Enhanced Arm Feature Is Disabled
  | invalidAllowableEngagementPercentage -- Invalid Allowable Engagement Percentage
  | invalidCountingPeriod -- Invalid Counting Period
  | unknownMpid -- Unknown Mpid
  | invalidUnderlying -- Invalid Underlying
  | notPermitted -- Not Permitted
  | noSuchArmSettings -- No Such Arm Settings
  | undefinedError -- Undefined Error
  | featureNotSupported -- Feature Not Supported
  | unlisted (byte : { byte : UInt8 // byte ∉ ArmSettingsUpdateStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ArmSettingsUpdateStatus

def toByte : ArmSettingsUpdateStatus → UInt8
  | .settingsAppliedSuccessfully => 0x20
  | .invalidAction => 0x41
  | .invalidOriginMultiplierValue => 0x42
  | .enhancedArmFeatureIsDisabled => 0x43
  | .invalidAllowableEngagementPercentage => 0x50
  | .invalidCountingPeriod => 0x44
  | .unknownMpid => 0x4D
  | .invalidUnderlying => 0x55
  | .notPermitted => 0x58
  | .noSuchArmSettings => 0x4E
  | .undefinedError => 0x5A
  | .featureNotSupported => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ArmSettingsUpdateStatus :=
  if byte = 0x20 then .settingsAppliedSuccessfully
  else if byte = 0x41 then .invalidAction
  else if byte = 0x42 then .invalidOriginMultiplierValue
  else if byte = 0x43 then .enhancedArmFeatureIsDisabled
  else if byte = 0x50 then .invalidAllowableEngagementPercentage
  else if byte = 0x44 then .invalidCountingPeriod
  else if byte = 0x4D then .unknownMpid
  else if byte = 0x55 then .invalidUnderlying
  else if byte = 0x58 then .notPermitted
  else if byte = 0x4E then .noSuchArmSettings
  else if byte = 0x5A then .undefinedError
  else .featureNotSupported

def ofByte (byte : UInt8) : ArmSettingsUpdateStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ArmSettingsUpdateStatus) : ofByte value.toByte = value := by
  cases value with
  | settingsAppliedSuccessfully => decide
  | invalidAction => decide
  | invalidOriginMultiplierValue => decide
  | enhancedArmFeatureIsDisabled => decide
  | invalidAllowableEngagementPercentage => decide
  | invalidCountingPeriod => decide
  | unknownMpid => decide
  | invalidUnderlying => decide
  | notPermitted => decide
  | noSuchArmSettings => decide
  | undefinedError => decide
  | featureNotSupported => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ArmSettingsUpdateStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ArmSettingsUpdateStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ArmSettingsUpdateStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ArmSettingsUpdateStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ArmSettingsUpdateStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ArmSettingsUpdateStatus

/-- Bulk Quote Status: one byte code -/
def BulkQuoteStatus.codes : List UInt8 :=
  [0x20, 0x52, 0x5A]

inductive BulkQuoteStatus where
  | bulkQuoteBlockIsValid -- Bulk Quote Block Is Valid
  | invalidBulkQuoteBlock -- Invalid Bulk Quote Block
  | undefinedError -- Undefined Error
  | unlisted (byte : { byte : UInt8 // byte ∉ BulkQuoteStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BulkQuoteStatus

def toByte : BulkQuoteStatus → UInt8
  | .bulkQuoteBlockIsValid => 0x20
  | .invalidBulkQuoteBlock => 0x52
  | .undefinedError => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BulkQuoteStatus :=
  if byte = 0x20 then .bulkQuoteBlockIsValid
  else if byte = 0x52 then .invalidBulkQuoteBlock
  else .undefinedError

def ofByte (byte : UInt8) : BulkQuoteStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BulkQuoteStatus) : ofByte value.toByte = value := by
  cases value with
  | bulkQuoteBlockIsValid => decide
  | invalidBulkQuoteBlock => decide
  | undefinedError => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BulkQuoteStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BulkQuoteStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BulkQuoteStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : BulkQuoteStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : BulkQuoteStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BulkQuoteStatus

/-- Quote Status: one byte code -/
def QuoteStatus.codes : List UInt8 :=
  [0x20, 0x54, 0x43, 0x4F, 0x50, 0x51, 0x53, 0x55, 0x58, 0x4D, 0x52, 0x44, 0x59, 0x75, 0x5A]

inductive QuoteStatus where
  | quoteSuccessfullyAccepted -- Quote Successfully Accepted
  | testQuoteSuccessfullyAcceptedPriorToLqwOrSetLqwAsApplicableButNotPlacedOnMiaxBook -- Test Quote Successfully Accepted Prior To Lqw Or Set Lqw As Applicable But Not Placed On Miax Book
  | miaxClosedForTradingOfThisProductRequestCannotBeCompleted -- Miax Closed For Trading Of This Product Request Cannot Be Completed
  | invalidProductId -- Invalid Product Id
  | invalidPrice -- Invalid Price
  | invalidSize -- Invalid Size
  | invalidSide -- Invalid Side
  | unknownMpid -- Unknown Mpid
  | notPermitted -- Not Permitted
  | quoteSizeMinimumRequiredSize -- Quote Size Minimum Required Size
  | rejectedDueToQuoteProtection -- Rejected Due To Quote Protection
  | rejectedDueToSelfCrossingPrimeAgencyOrder -- Rejected Due To Self Crossing Prime Agency Order
  | rejectedDueToSingleSideLiquidityProtectionInEffect -- Rejected Due To Single Side Liquidity Protection In Effect
  | rejectedDueToSlapProtectionInEffect -- Rejected Due To Slap Protection In Effect
  | undefinedError -- Undefined Error
  | unlisted (byte : { byte : UInt8 // byte ∉ QuoteStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace QuoteStatus

def toByte : QuoteStatus → UInt8
  | .quoteSuccessfullyAccepted => 0x20
  | .testQuoteSuccessfullyAcceptedPriorToLqwOrSetLqwAsApplicableButNotPlacedOnMiaxBook => 0x54
  | .miaxClosedForTradingOfThisProductRequestCannotBeCompleted => 0x43
  | .invalidProductId => 0x4F
  | .invalidPrice => 0x50
  | .invalidSize => 0x51
  | .invalidSide => 0x53
  | .unknownMpid => 0x55
  | .notPermitted => 0x58
  | .quoteSizeMinimumRequiredSize => 0x4D
  | .rejectedDueToQuoteProtection => 0x52
  | .rejectedDueToSelfCrossingPrimeAgencyOrder => 0x44
  | .rejectedDueToSingleSideLiquidityProtectionInEffect => 0x59
  | .rejectedDueToSlapProtectionInEffect => 0x75
  | .undefinedError => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : QuoteStatus :=
  if byte = 0x20 then .quoteSuccessfullyAccepted
  else if byte = 0x54 then .testQuoteSuccessfullyAcceptedPriorToLqwOrSetLqwAsApplicableButNotPlacedOnMiaxBook
  else if byte = 0x43 then .miaxClosedForTradingOfThisProductRequestCannotBeCompleted
  else if byte = 0x4F then .invalidProductId
  else if byte = 0x50 then .invalidPrice
  else if byte = 0x51 then .invalidSize
  else if byte = 0x53 then .invalidSide
  else if byte = 0x55 then .unknownMpid
  else if byte = 0x58 then .notPermitted
  else if byte = 0x4D then .quoteSizeMinimumRequiredSize
  else if byte = 0x52 then .rejectedDueToQuoteProtection
  else if byte = 0x44 then .rejectedDueToSelfCrossingPrimeAgencyOrder
  else if byte = 0x59 then .rejectedDueToSingleSideLiquidityProtectionInEffect
  else if byte = 0x75 then .rejectedDueToSlapProtectionInEffect
  else .undefinedError

def ofByte (byte : UInt8) : QuoteStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : QuoteStatus) : ofByte value.toByte = value := by
  cases value with
  | quoteSuccessfullyAccepted => decide
  | testQuoteSuccessfullyAcceptedPriorToLqwOrSetLqwAsApplicableButNotPlacedOnMiaxBook => decide
  | miaxClosedForTradingOfThisProductRequestCannotBeCompleted => decide
  | invalidProductId => decide
  | invalidPrice => decide
  | invalidSize => decide
  | invalidSide => decide
  | unknownMpid => decide
  | notPermitted => decide
  | quoteSizeMinimumRequiredSize => decide
  | rejectedDueToQuoteProtection => decide
  | rejectedDueToSelfCrossingPrimeAgencyOrder => decide
  | rejectedDueToSingleSideLiquidityProtectionInEffect => decide
  | rejectedDueToSlapProtectionInEffect => decide
  | undefinedError => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : QuoteStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (QuoteStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : QuoteStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : QuoteStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : QuoteStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end QuoteStatus

/-- E Quote Action: one byte code -/
def EQuoteAction.codes : List UInt8 :=
  [0x4E, 0x43, 0x52]

inductive EQuoteAction where
  | newEQuote -- New E Quote
  | cancelEQuote -- Cancel E Quote
  | replaceEQuote -- Replace E Quote
  | unlisted (byte : { byte : UInt8 // byte ∉ EQuoteAction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EQuoteAction

def toByte : EQuoteAction → UInt8
  | .newEQuote => 0x4E
  | .cancelEQuote => 0x43
  | .replaceEQuote => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EQuoteAction :=
  if byte = 0x4E then .newEQuote
  else if byte = 0x43 then .cancelEQuote
  else .replaceEQuote

def ofByte (byte : UInt8) : EQuoteAction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EQuoteAction) : ofByte value.toByte = value := by
  cases value with
  | newEQuote => decide
  | cancelEQuote => decide
  | replaceEQuote => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : EQuoteAction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (EQuoteAction × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : EQuoteAction) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : EQuoteAction) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : EQuoteAction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end EQuoteAction

/-- E Quote Type: one byte code -/
def EQuoteType.codes : List UInt8 :=
  [0x4F, 0x41, 0x49, 0x53, 0x50]

inductive EQuoteType where
  | opg -- Opg
  | aoc -- Aoc
  | ioc -- Ioc
  | iso -- Iso
  | futureUse -- Future Use
  | unlisted (byte : { byte : UInt8 // byte ∉ EQuoteType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EQuoteType

def toByte : EQuoteType → UInt8
  | .opg => 0x4F
  | .aoc => 0x41
  | .ioc => 0x49
  | .iso => 0x53
  | .futureUse => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EQuoteType :=
  if byte = 0x4F then .opg
  else if byte = 0x41 then .aoc
  else if byte = 0x49 then .ioc
  else if byte = 0x53 then .iso
  else .futureUse

def ofByte (byte : UInt8) : EQuoteType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EQuoteType) : ofByte value.toByte = value := by
  cases value with
  | opg => decide
  | aoc => decide
  | ioc => decide
  | iso => decide
  | futureUse => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : EQuoteType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (EQuoteType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : EQuoteType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : EQuoteType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : EQuoteType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end EQuoteType

/-- Simple Mass Quote Cancel Status: one byte code -/
def SimpleMassQuoteCancelStatus.codes : List UInt8 :=
  [0x20, 0x55, 0x49, 0x48, 0x4E, 0x58, 0x4D, 0x43, 0x5A]

inductive SimpleMassQuoteCancelStatus where
  | cancelSuccessful -- Cancel Successful
  | invalidUnderlying -- Invalid Underlying
  | massQuoteCancelStillInProgress -- Mass Quote Cancel Still In Progress
  | haltTriggeredCleanupOfQuotesStillInProgress -- Halt Triggered Cleanup Of Quotes Still In Progress
  | allQuoteHaveAlreadyBeenCanceled -- All Quote Have Already Been Canceled
  | notPermitted -- Not Permitted
  | unknownMpid -- Unknown Mpid
  | miaxClosedRequestCannotBeCompleted -- Miax Closed Request Cannot Be Completed
  | undefinedError -- Undefined Error
  | unlisted (byte : { byte : UInt8 // byte ∉ SimpleMassQuoteCancelStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SimpleMassQuoteCancelStatus

def toByte : SimpleMassQuoteCancelStatus → UInt8
  | .cancelSuccessful => 0x20
  | .invalidUnderlying => 0x55
  | .massQuoteCancelStillInProgress => 0x49
  | .haltTriggeredCleanupOfQuotesStillInProgress => 0x48
  | .allQuoteHaveAlreadyBeenCanceled => 0x4E
  | .notPermitted => 0x58
  | .unknownMpid => 0x4D
  | .miaxClosedRequestCannotBeCompleted => 0x43
  | .undefinedError => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SimpleMassQuoteCancelStatus :=
  if byte = 0x20 then .cancelSuccessful
  else if byte = 0x55 then .invalidUnderlying
  else if byte = 0x49 then .massQuoteCancelStillInProgress
  else if byte = 0x48 then .haltTriggeredCleanupOfQuotesStillInProgress
  else if byte = 0x4E then .allQuoteHaveAlreadyBeenCanceled
  else if byte = 0x58 then .notPermitted
  else if byte = 0x4D then .unknownMpid
  else if byte = 0x43 then .miaxClosedRequestCannotBeCompleted
  else .undefinedError

def ofByte (byte : UInt8) : SimpleMassQuoteCancelStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SimpleMassQuoteCancelStatus) : ofByte value.toByte = value := by
  cases value with
  | cancelSuccessful => decide
  | invalidUnderlying => decide
  | massQuoteCancelStillInProgress => decide
  | haltTriggeredCleanupOfQuotesStillInProgress => decide
  | allQuoteHaveAlreadyBeenCanceled => decide
  | notPermitted => decide
  | unknownMpid => decide
  | miaxClosedRequestCannotBeCompleted => decide
  | undefinedError => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SimpleMassQuoteCancelStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SimpleMassQuoteCancelStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SimpleMassQuoteCancelStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SimpleMassQuoteCancelStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SimpleMassQuoteCancelStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SimpleMassQuoteCancelStatus

/-- Simple Mass Cancel: one byte code -/
def SimpleMassCancel.codes : List UInt8 :=
  [0x59, 0x4E, 0x51, 0x53]

inductive SimpleMassCancel where
  | standardMassCancelMassCancelSimpleQuotesAndEQuotes -- Standard Mass Cancel Mass Cancel Simple Quotes And E Quotes
  | doNotMassCancelSimpleQuotesAndEQuotes -- Do Not Mass Cancel Simple Quotes And E Quotes
  | hybridMassCancelMassCancelSimpleQuotesOnlyUnderlyingSymbolMustBeFilledWithValidUnderlyingForThisOption -- Hybrid Mass Cancel Mass Cancel Simple Quotes Only Underlying Symbol Must Be Filled With Valid Underlying For This Option
  | selectiveLiquidityAutoPurgeSlapWhenUsedComplexMassCancelMustBeN -- Selective Liquidity Auto Purge Slap When Used Complex Mass Cancel Must Be N
  | unlisted (byte : { byte : UInt8 // byte ∉ SimpleMassCancel.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SimpleMassCancel

def toByte : SimpleMassCancel → UInt8
  | .standardMassCancelMassCancelSimpleQuotesAndEQuotes => 0x59
  | .doNotMassCancelSimpleQuotesAndEQuotes => 0x4E
  | .hybridMassCancelMassCancelSimpleQuotesOnlyUnderlyingSymbolMustBeFilledWithValidUnderlyingForThisOption => 0x51
  | .selectiveLiquidityAutoPurgeSlapWhenUsedComplexMassCancelMustBeN => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SimpleMassCancel :=
  if byte = 0x59 then .standardMassCancelMassCancelSimpleQuotesAndEQuotes
  else if byte = 0x4E then .doNotMassCancelSimpleQuotesAndEQuotes
  else if byte = 0x51 then .hybridMassCancelMassCancelSimpleQuotesOnlyUnderlyingSymbolMustBeFilledWithValidUnderlyingForThisOption
  else .selectiveLiquidityAutoPurgeSlapWhenUsedComplexMassCancelMustBeN

def ofByte (byte : UInt8) : SimpleMassCancel :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SimpleMassCancel) : ofByte value.toByte = value := by
  cases value with
  | standardMassCancelMassCancelSimpleQuotesAndEQuotes => decide
  | doNotMassCancelSimpleQuotesAndEQuotes => decide
  | hybridMassCancelMassCancelSimpleQuotesOnlyUnderlyingSymbolMustBeFilledWithValidUnderlyingForThisOption => decide
  | selectiveLiquidityAutoPurgeSlapWhenUsedComplexMassCancelMustBeN => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SimpleMassCancel) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SimpleMassCancel × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SimpleMassCancel) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SimpleMassCancel) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SimpleMassCancel) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SimpleMassCancel

/-- Complex Mass Cancel: one byte code -/
def ComplexMassCancel.codes : List UInt8 :=
  [0x59, 0x4E]

inductive ComplexMassCancel where
  | massCancelComplexEQuotesOnly -- Mass Cancel Complex E Quotes Only
  | doNotMassCancelComplexLiquidities -- Do Not Mass Cancel Complex Liquidities
  | unlisted (byte : { byte : UInt8 // byte ∉ ComplexMassCancel.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ComplexMassCancel

def toByte : ComplexMassCancel → UInt8
  | .massCancelComplexEQuotesOnly => 0x59
  | .doNotMassCancelComplexLiquidities => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ComplexMassCancel :=
  if byte = 0x59 then .massCancelComplexEQuotesOnly
  else .doNotMassCancelComplexLiquidities

def ofByte (byte : UInt8) : ComplexMassCancel :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ComplexMassCancel) : ofByte value.toByte = value := by
  cases value with
  | massCancelComplexEQuotesOnly => decide
  | doNotMassCancelComplexLiquidities => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ComplexMassCancel) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ComplexMassCancel × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ComplexMassCancel) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ComplexMassCancel) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ComplexMassCancel) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ComplexMassCancel

/-- Simple Mass Liquidity Cancel Status: one byte code -/
def SimpleMassLiquidityCancelStatus.codes : List UInt8 :=
  [0x20, 0x55, 0x49, 0x48, 0x4E, 0x58, 0x4D, 0x43, 0x4A, 0x45, 0x5A, 0x51, 0x41, 0x42, 0x44, 0x53, 0x52, 0x2A]

inductive SimpleMassLiquidityCancelStatus where
  | simpleMassLiquidityCancelSuccessful -- Simple Mass Liquidity Cancel Successful
  | invalidUnderlying -- Invalid Underlying
  | simpleMassLiquidityCancelStillInProgress -- Simple Mass Liquidity Cancel Still In Progress
  | haltTriggeredCleanupOfLiquiditiesStillInProgress -- Halt Triggered Cleanup Of Liquidities Still In Progress
  | allLiquiditiesHaveAlreadyBeenCanceled -- All Liquidities Have Already Been Canceled
  | notPermitted -- Not Permitted
  | unknownMpid -- Unknown Mpid
  | miaxClosedRequestCannotBeCompleted -- Miax Closed Request Cannot Be Completed
  | invalidRequest -- Invalid Request
  | featureNotSupported -- Feature Not Supported
  | undefinedError -- Undefined Error
  | notRequested -- Not Requested
  | allSpecifiedSlapCodesAreAlreadyPurged -- All Specified Slap Codes Are Already Purged
  | slapCodesAreNotProvidedInTheRequest -- Slap Codes Are Not Provided In The Request
  | slapPurgeWhileStandardhybridMassCancelIsActive -- Slap Purge While Standardhybrid Mass Cancel Is Active
  | attemptToUseSlapForSimpleMassCancelWhenComplexMassCancelNotN -- Attempt To Use Slap For Simple Mass Cancel When Complex Mass Cancel Not N
  | slapFeatureDisabled -- Slap Feature Disabled
  | downgradedFromOlderVersion -- Downgraded From Older Version
  | unlisted (byte : { byte : UInt8 // byte ∉ SimpleMassLiquidityCancelStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SimpleMassLiquidityCancelStatus

def toByte : SimpleMassLiquidityCancelStatus → UInt8
  | .simpleMassLiquidityCancelSuccessful => 0x20
  | .invalidUnderlying => 0x55
  | .simpleMassLiquidityCancelStillInProgress => 0x49
  | .haltTriggeredCleanupOfLiquiditiesStillInProgress => 0x48
  | .allLiquiditiesHaveAlreadyBeenCanceled => 0x4E
  | .notPermitted => 0x58
  | .unknownMpid => 0x4D
  | .miaxClosedRequestCannotBeCompleted => 0x43
  | .invalidRequest => 0x4A
  | .featureNotSupported => 0x45
  | .undefinedError => 0x5A
  | .notRequested => 0x51
  | .allSpecifiedSlapCodesAreAlreadyPurged => 0x41
  | .slapCodesAreNotProvidedInTheRequest => 0x42
  | .slapPurgeWhileStandardhybridMassCancelIsActive => 0x44
  | .attemptToUseSlapForSimpleMassCancelWhenComplexMassCancelNotN => 0x53
  | .slapFeatureDisabled => 0x52
  | .downgradedFromOlderVersion => 0x2A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SimpleMassLiquidityCancelStatus :=
  if byte = 0x20 then .simpleMassLiquidityCancelSuccessful
  else if byte = 0x55 then .invalidUnderlying
  else if byte = 0x49 then .simpleMassLiquidityCancelStillInProgress
  else if byte = 0x48 then .haltTriggeredCleanupOfLiquiditiesStillInProgress
  else if byte = 0x4E then .allLiquiditiesHaveAlreadyBeenCanceled
  else if byte = 0x58 then .notPermitted
  else if byte = 0x4D then .unknownMpid
  else if byte = 0x43 then .miaxClosedRequestCannotBeCompleted
  else if byte = 0x4A then .invalidRequest
  else if byte = 0x45 then .featureNotSupported
  else if byte = 0x5A then .undefinedError
  else if byte = 0x51 then .notRequested
  else if byte = 0x41 then .allSpecifiedSlapCodesAreAlreadyPurged
  else if byte = 0x42 then .slapCodesAreNotProvidedInTheRequest
  else if byte = 0x44 then .slapPurgeWhileStandardhybridMassCancelIsActive
  else if byte = 0x53 then .attemptToUseSlapForSimpleMassCancelWhenComplexMassCancelNotN
  else if byte = 0x52 then .slapFeatureDisabled
  else .downgradedFromOlderVersion

def ofByte (byte : UInt8) : SimpleMassLiquidityCancelStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SimpleMassLiquidityCancelStatus) : ofByte value.toByte = value := by
  cases value with
  | simpleMassLiquidityCancelSuccessful => decide
  | invalidUnderlying => decide
  | simpleMassLiquidityCancelStillInProgress => decide
  | haltTriggeredCleanupOfLiquiditiesStillInProgress => decide
  | allLiquiditiesHaveAlreadyBeenCanceled => decide
  | notPermitted => decide
  | unknownMpid => decide
  | miaxClosedRequestCannotBeCompleted => decide
  | invalidRequest => decide
  | featureNotSupported => decide
  | undefinedError => decide
  | notRequested => decide
  | allSpecifiedSlapCodesAreAlreadyPurged => decide
  | slapCodesAreNotProvidedInTheRequest => decide
  | slapPurgeWhileStandardhybridMassCancelIsActive => decide
  | attemptToUseSlapForSimpleMassCancelWhenComplexMassCancelNotN => decide
  | slapFeatureDisabled => decide
  | downgradedFromOlderVersion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SimpleMassLiquidityCancelStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SimpleMassLiquidityCancelStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SimpleMassLiquidityCancelStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SimpleMassLiquidityCancelStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SimpleMassLiquidityCancelStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SimpleMassLiquidityCancelStatus

/-- Complex Mass Liquidity Cancel Status: one byte code -/
def ComplexMassLiquidityCancelStatus.codes : List UInt8 :=
  [0x20, 0x55, 0x49, 0x48, 0x4E, 0x58, 0x4D, 0x43, 0x4A, 0x45, 0x5A, 0x51, 0x53, 0x2A]

inductive ComplexMassLiquidityCancelStatus where
  | complexMassLiquidityCancelSuccessful -- Complex Mass Liquidity Cancel Successful
  | invalidUnderlying -- Invalid Underlying
  | complexMassLiquidityCancelStillInProgress -- Complex Mass Liquidity Cancel Still In Progress
  | haltTriggeredCleanupOfLiquiditiesStillInProgress -- Halt Triggered Cleanup Of Liquidities Still In Progress
  | allLiquiditiesHaveAlreadyBeenCanceled -- All Liquidities Have Already Been Canceled
  | notPermitted -- Not Permitted
  | unknownMpid -- Unknown Mpid
  | miaxClosedRequestCannotBeCompleted -- Miax Closed Request Cannot Be Completed
  | invalidRequest -- Invalid Request
  | featureNotSupported -- Feature Not Supported
  | undefinedError -- Undefined Error
  | notRequested -- Not Requested
  | attemptToUseSlapForSimpleMassCancelWhenComplexMassCancelNotN -- Attempt To Use Slap For Simple Mass Cancel When Complex Mass Cancel Not N
  | downgradedFromOlderVersion -- Downgraded From Older Version
  | unlisted (byte : { byte : UInt8 // byte ∉ ComplexMassLiquidityCancelStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ComplexMassLiquidityCancelStatus

def toByte : ComplexMassLiquidityCancelStatus → UInt8
  | .complexMassLiquidityCancelSuccessful => 0x20
  | .invalidUnderlying => 0x55
  | .complexMassLiquidityCancelStillInProgress => 0x49
  | .haltTriggeredCleanupOfLiquiditiesStillInProgress => 0x48
  | .allLiquiditiesHaveAlreadyBeenCanceled => 0x4E
  | .notPermitted => 0x58
  | .unknownMpid => 0x4D
  | .miaxClosedRequestCannotBeCompleted => 0x43
  | .invalidRequest => 0x4A
  | .featureNotSupported => 0x45
  | .undefinedError => 0x5A
  | .notRequested => 0x51
  | .attemptToUseSlapForSimpleMassCancelWhenComplexMassCancelNotN => 0x53
  | .downgradedFromOlderVersion => 0x2A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ComplexMassLiquidityCancelStatus :=
  if byte = 0x20 then .complexMassLiquidityCancelSuccessful
  else if byte = 0x55 then .invalidUnderlying
  else if byte = 0x49 then .complexMassLiquidityCancelStillInProgress
  else if byte = 0x48 then .haltTriggeredCleanupOfLiquiditiesStillInProgress
  else if byte = 0x4E then .allLiquiditiesHaveAlreadyBeenCanceled
  else if byte = 0x58 then .notPermitted
  else if byte = 0x4D then .unknownMpid
  else if byte = 0x43 then .miaxClosedRequestCannotBeCompleted
  else if byte = 0x4A then .invalidRequest
  else if byte = 0x45 then .featureNotSupported
  else if byte = 0x5A then .undefinedError
  else if byte = 0x51 then .notRequested
  else if byte = 0x53 then .attemptToUseSlapForSimpleMassCancelWhenComplexMassCancelNotN
  else .downgradedFromOlderVersion

def ofByte (byte : UInt8) : ComplexMassLiquidityCancelStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ComplexMassLiquidityCancelStatus) : ofByte value.toByte = value := by
  cases value with
  | complexMassLiquidityCancelSuccessful => decide
  | invalidUnderlying => decide
  | complexMassLiquidityCancelStillInProgress => decide
  | haltTriggeredCleanupOfLiquiditiesStillInProgress => decide
  | allLiquiditiesHaveAlreadyBeenCanceled => decide
  | notPermitted => decide
  | unknownMpid => decide
  | miaxClosedRequestCannotBeCompleted => decide
  | invalidRequest => decide
  | featureNotSupported => decide
  | undefinedError => decide
  | notRequested => decide
  | attemptToUseSlapForSimpleMassCancelWhenComplexMassCancelNotN => decide
  | downgradedFromOlderVersion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ComplexMassLiquidityCancelStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ComplexMassLiquidityCancelStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ComplexMassLiquidityCancelStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ComplexMassLiquidityCancelStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ComplexMassLiquidityCancelStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ComplexMassLiquidityCancelStatus

/-- Quote Protection Reset Status: one byte code -/
def QuoteProtectionResetStatus.codes : List UInt8 :=
  [0x20, 0x55, 0x49, 0x48, 0x4D, 0x58, 0x43, 0x41, 0x46, 0x4B, 0x5A, 0x2A]

inductive QuoteProtectionResetStatus where
  | quoteProtectionResetSuccessful -- Quote Protection Reset Successful
  | invalidUnderlying -- Invalid Underlying
  | massQuoteCancelStillInProgress -- Mass Quote Cancel Still In Progress
  | haltTriggeredCleanupOfQuotesStillInProgress -- Halt Triggered Cleanup Of Quotes Still In Progress
  | unknownMpid -- Unknown Mpid
  | notPermitted -- Not Permitted
  | miaxClosedRequestCannotBeCompleted -- Miax Closed Request Cannot Be Completed
  | arm2UnderlyingLevelProtectionIsInEffect -- Arm 2 Underlying Level Protection Is In Effect
  | arm2FirmLevelProtectionIsInEffect -- Arm 2 Firm Level Protection Is In Effect
  | killSwitchProtectionIsInEffect -- Kill Switch Protection Is In Effect
  | undefinedError -- Undefined Error
  | downgradedFromOlderVersion -- Downgraded From Older Version
  | unlisted (byte : { byte : UInt8 // byte ∉ QuoteProtectionResetStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace QuoteProtectionResetStatus

def toByte : QuoteProtectionResetStatus → UInt8
  | .quoteProtectionResetSuccessful => 0x20
  | .invalidUnderlying => 0x55
  | .massQuoteCancelStillInProgress => 0x49
  | .haltTriggeredCleanupOfQuotesStillInProgress => 0x48
  | .unknownMpid => 0x4D
  | .notPermitted => 0x58
  | .miaxClosedRequestCannotBeCompleted => 0x43
  | .arm2UnderlyingLevelProtectionIsInEffect => 0x41
  | .arm2FirmLevelProtectionIsInEffect => 0x46
  | .killSwitchProtectionIsInEffect => 0x4B
  | .undefinedError => 0x5A
  | .downgradedFromOlderVersion => 0x2A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : QuoteProtectionResetStatus :=
  if byte = 0x20 then .quoteProtectionResetSuccessful
  else if byte = 0x55 then .invalidUnderlying
  else if byte = 0x49 then .massQuoteCancelStillInProgress
  else if byte = 0x48 then .haltTriggeredCleanupOfQuotesStillInProgress
  else if byte = 0x4D then .unknownMpid
  else if byte = 0x58 then .notPermitted
  else if byte = 0x43 then .miaxClosedRequestCannotBeCompleted
  else if byte = 0x41 then .arm2UnderlyingLevelProtectionIsInEffect
  else if byte = 0x46 then .arm2FirmLevelProtectionIsInEffect
  else if byte = 0x4B then .killSwitchProtectionIsInEffect
  else if byte = 0x5A then .undefinedError
  else .downgradedFromOlderVersion

def ofByte (byte : UInt8) : QuoteProtectionResetStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : QuoteProtectionResetStatus) : ofByte value.toByte = value := by
  cases value with
  | quoteProtectionResetSuccessful => decide
  | invalidUnderlying => decide
  | massQuoteCancelStillInProgress => decide
  | haltTriggeredCleanupOfQuotesStillInProgress => decide
  | unknownMpid => decide
  | notPermitted => decide
  | miaxClosedRequestCannotBeCompleted => decide
  | arm2UnderlyingLevelProtectionIsInEffect => decide
  | arm2FirmLevelProtectionIsInEffect => decide
  | killSwitchProtectionIsInEffect => decide
  | undefinedError => decide
  | downgradedFromOlderVersion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : QuoteProtectionResetStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (QuoteProtectionResetStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : QuoteProtectionResetStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : QuoteProtectionResetStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : QuoteProtectionResetStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end QuoteProtectionResetStatus

/-- Simple Liquidity Reset: one byte code -/
def SimpleLiquidityReset.codes : List UInt8 :=
  [0x59, 0x4E, 0x53]

inductive SimpleLiquidityReset where
  | standardHybridMassCancelReset -- Standard Hybrid Mass Cancel Reset
  | no -- No
  | slapReset -- Slap Reset
  | unlisted (byte : { byte : UInt8 // byte ∉ SimpleLiquidityReset.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SimpleLiquidityReset

def toByte : SimpleLiquidityReset → UInt8
  | .standardHybridMassCancelReset => 0x59
  | .no => 0x4E
  | .slapReset => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SimpleLiquidityReset :=
  if byte = 0x59 then .standardHybridMassCancelReset
  else if byte = 0x4E then .no
  else .slapReset

def ofByte (byte : UInt8) : SimpleLiquidityReset :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SimpleLiquidityReset) : ofByte value.toByte = value := by
  cases value with
  | standardHybridMassCancelReset => decide
  | no => decide
  | slapReset => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SimpleLiquidityReset) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SimpleLiquidityReset × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SimpleLiquidityReset) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SimpleLiquidityReset) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SimpleLiquidityReset) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SimpleLiquidityReset

/-- Complex Liquidity Reset: one byte code -/
def ComplexLiquidityReset.codes : List UInt8 :=
  [0x59, 0x4E]

inductive ComplexLiquidityReset where
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ ComplexLiquidityReset.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ComplexLiquidityReset

def toByte : ComplexLiquidityReset → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ComplexLiquidityReset :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : ComplexLiquidityReset :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ComplexLiquidityReset) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ComplexLiquidityReset) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ComplexLiquidityReset × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ComplexLiquidityReset) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ComplexLiquidityReset) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ComplexLiquidityReset) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ComplexLiquidityReset

/-- Simple Liquidity Protection Reset Status: one byte code -/
def SimpleLiquidityProtectionResetStatus.codes : List UInt8 :=
  [0x20, 0x55, 0x49, 0x48, 0x4D, 0x58, 0x43, 0x41, 0x46, 0x4B, 0x45, 0x5A, 0x4A, 0x51, 0x42, 0x44, 0x53, 0x52, 0x2A]

inductive SimpleLiquidityProtectionResetStatus where
  | simpleLiquidityProtectionResetSuccessful -- Simple Liquidity Protection Reset Successful
  | invalidUnderlying -- Invalid Underlying
  | simpleMassLiquidityCancelStillInProgress -- Simple Mass Liquidity Cancel Still In Progress
  | haltTriggeredCleanupOfLiquidatesStillInProgress -- Halt Triggered Cleanup Of Liquidates Still In Progress
  | unknownMpid -- Unknown Mpid
  | notPermitted -- Not Permitted
  | miaxClosedRequestCannotBeCompleted -- Miax Closed Request Cannot Be Completed
  | arm2UnderlyingLevelProtectionIsInEffect -- Arm 2 Underlying Level Protection Is In Effect
  | arm2FirmLevelProtectionIsInEffect -- Arm 2 Firm Level Protection Is In Effect
  | killSwitchProtectionIsInEffect -- Kill Switch Protection Is In Effect
  | featureNotSupported -- Feature Not Supported
  | undefinedError -- Undefined Error
  | invalidRequest -- Invalid Request
  | notRequested -- Not Requested
  | slapCodesWereNotProvidedInTheRequest -- Slap Codes Were Not Provided In The Request
  | slapResetWhileStandardhybridMassCancelIsActive -- Slap Reset While Standardhybrid Mass Cancel Is Active
  | attemptToResetSlapForSimpleLiquidityResetWhenComplexLiquidityResetNotN -- Attempt To Reset Slap For Simple Liquidity Reset When Complex Liquidity Reset Not N
  | slapFeatureDisabled -- Slap Feature Disabled
  | downgradedFromOlderVersion -- Downgraded From Older Version
  | unlisted (byte : { byte : UInt8 // byte ∉ SimpleLiquidityProtectionResetStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SimpleLiquidityProtectionResetStatus

def toByte : SimpleLiquidityProtectionResetStatus → UInt8
  | .simpleLiquidityProtectionResetSuccessful => 0x20
  | .invalidUnderlying => 0x55
  | .simpleMassLiquidityCancelStillInProgress => 0x49
  | .haltTriggeredCleanupOfLiquidatesStillInProgress => 0x48
  | .unknownMpid => 0x4D
  | .notPermitted => 0x58
  | .miaxClosedRequestCannotBeCompleted => 0x43
  | .arm2UnderlyingLevelProtectionIsInEffect => 0x41
  | .arm2FirmLevelProtectionIsInEffect => 0x46
  | .killSwitchProtectionIsInEffect => 0x4B
  | .featureNotSupported => 0x45
  | .undefinedError => 0x5A
  | .invalidRequest => 0x4A
  | .notRequested => 0x51
  | .slapCodesWereNotProvidedInTheRequest => 0x42
  | .slapResetWhileStandardhybridMassCancelIsActive => 0x44
  | .attemptToResetSlapForSimpleLiquidityResetWhenComplexLiquidityResetNotN => 0x53
  | .slapFeatureDisabled => 0x52
  | .downgradedFromOlderVersion => 0x2A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SimpleLiquidityProtectionResetStatus :=
  if byte = 0x20 then .simpleLiquidityProtectionResetSuccessful
  else if byte = 0x55 then .invalidUnderlying
  else if byte = 0x49 then .simpleMassLiquidityCancelStillInProgress
  else if byte = 0x48 then .haltTriggeredCleanupOfLiquidatesStillInProgress
  else if byte = 0x4D then .unknownMpid
  else if byte = 0x58 then .notPermitted
  else if byte = 0x43 then .miaxClosedRequestCannotBeCompleted
  else if byte = 0x41 then .arm2UnderlyingLevelProtectionIsInEffect
  else if byte = 0x46 then .arm2FirmLevelProtectionIsInEffect
  else if byte = 0x4B then .killSwitchProtectionIsInEffect
  else if byte = 0x45 then .featureNotSupported
  else if byte = 0x5A then .undefinedError
  else if byte = 0x4A then .invalidRequest
  else if byte = 0x51 then .notRequested
  else if byte = 0x42 then .slapCodesWereNotProvidedInTheRequest
  else if byte = 0x44 then .slapResetWhileStandardhybridMassCancelIsActive
  else if byte = 0x53 then .attemptToResetSlapForSimpleLiquidityResetWhenComplexLiquidityResetNotN
  else if byte = 0x52 then .slapFeatureDisabled
  else .downgradedFromOlderVersion

def ofByte (byte : UInt8) : SimpleLiquidityProtectionResetStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SimpleLiquidityProtectionResetStatus) : ofByte value.toByte = value := by
  cases value with
  | simpleLiquidityProtectionResetSuccessful => decide
  | invalidUnderlying => decide
  | simpleMassLiquidityCancelStillInProgress => decide
  | haltTriggeredCleanupOfLiquidatesStillInProgress => decide
  | unknownMpid => decide
  | notPermitted => decide
  | miaxClosedRequestCannotBeCompleted => decide
  | arm2UnderlyingLevelProtectionIsInEffect => decide
  | arm2FirmLevelProtectionIsInEffect => decide
  | killSwitchProtectionIsInEffect => decide
  | featureNotSupported => decide
  | undefinedError => decide
  | invalidRequest => decide
  | notRequested => decide
  | slapCodesWereNotProvidedInTheRequest => decide
  | slapResetWhileStandardhybridMassCancelIsActive => decide
  | attemptToResetSlapForSimpleLiquidityResetWhenComplexLiquidityResetNotN => decide
  | slapFeatureDisabled => decide
  | downgradedFromOlderVersion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SimpleLiquidityProtectionResetStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SimpleLiquidityProtectionResetStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SimpleLiquidityProtectionResetStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SimpleLiquidityProtectionResetStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SimpleLiquidityProtectionResetStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SimpleLiquidityProtectionResetStatus

/-- Complex Liquidity Protection Reset Status: one byte code -/
def ComplexLiquidityProtectionResetStatus.codes : List UInt8 :=
  [0x20, 0x55, 0x49, 0x48, 0x4D, 0x58, 0x43, 0x41, 0x46, 0x4B, 0x45, 0x5A, 0x4A, 0x51, 0x2A]

inductive ComplexLiquidityProtectionResetStatus where
  | complexLiquidityProtectionResetSuccessful -- Complex Liquidity Protection Reset Successful
  | invalidUnderlying -- Invalid Underlying
  | complexMassLiquidityCancelStillInProgress -- Complex Mass Liquidity Cancel Still In Progress
  | haltTriggeredCleanupOfLiquiditiesStillInProgress -- Halt Triggered Cleanup Of Liquidities Still In Progress
  | unknownMpid -- Unknown Mpid
  | notPermitted -- Not Permitted
  | miaxClosedRequestCannotBeCompleted -- Miax Closed Request Cannot Be Completed
  | arm2UnderlyingLevelProtectionIsInEffect -- Arm 2 Underlying Level Protection Is In Effect
  | arm2FirmLevelProtectionIsInEffect -- Arm 2 Firm Level Protection Is In Effect
  | killSwitchProtectionIsInEffect -- Kill Switch Protection Is In Effect
  | featureNotSupported -- Feature Not Supported
  | undefinedError -- Undefined Error
  | invalidRequest -- Invalid Request
  | notRequested -- Not Requested
  | downgradedFromOlderVersion -- Downgraded From Older Version
  | unlisted (byte : { byte : UInt8 // byte ∉ ComplexLiquidityProtectionResetStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ComplexLiquidityProtectionResetStatus

def toByte : ComplexLiquidityProtectionResetStatus → UInt8
  | .complexLiquidityProtectionResetSuccessful => 0x20
  | .invalidUnderlying => 0x55
  | .complexMassLiquidityCancelStillInProgress => 0x49
  | .haltTriggeredCleanupOfLiquiditiesStillInProgress => 0x48
  | .unknownMpid => 0x4D
  | .notPermitted => 0x58
  | .miaxClosedRequestCannotBeCompleted => 0x43
  | .arm2UnderlyingLevelProtectionIsInEffect => 0x41
  | .arm2FirmLevelProtectionIsInEffect => 0x46
  | .killSwitchProtectionIsInEffect => 0x4B
  | .featureNotSupported => 0x45
  | .undefinedError => 0x5A
  | .invalidRequest => 0x4A
  | .notRequested => 0x51
  | .downgradedFromOlderVersion => 0x2A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ComplexLiquidityProtectionResetStatus :=
  if byte = 0x20 then .complexLiquidityProtectionResetSuccessful
  else if byte = 0x55 then .invalidUnderlying
  else if byte = 0x49 then .complexMassLiquidityCancelStillInProgress
  else if byte = 0x48 then .haltTriggeredCleanupOfLiquiditiesStillInProgress
  else if byte = 0x4D then .unknownMpid
  else if byte = 0x58 then .notPermitted
  else if byte = 0x43 then .miaxClosedRequestCannotBeCompleted
  else if byte = 0x41 then .arm2UnderlyingLevelProtectionIsInEffect
  else if byte = 0x46 then .arm2FirmLevelProtectionIsInEffect
  else if byte = 0x4B then .killSwitchProtectionIsInEffect
  else if byte = 0x45 then .featureNotSupported
  else if byte = 0x5A then .undefinedError
  else if byte = 0x4A then .invalidRequest
  else if byte = 0x51 then .notRequested
  else .downgradedFromOlderVersion

def ofByte (byte : UInt8) : ComplexLiquidityProtectionResetStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ComplexLiquidityProtectionResetStatus) : ofByte value.toByte = value := by
  cases value with
  | complexLiquidityProtectionResetSuccessful => decide
  | invalidUnderlying => decide
  | complexMassLiquidityCancelStillInProgress => decide
  | haltTriggeredCleanupOfLiquiditiesStillInProgress => decide
  | unknownMpid => decide
  | notPermitted => decide
  | miaxClosedRequestCannotBeCompleted => decide
  | arm2UnderlyingLevelProtectionIsInEffect => decide
  | arm2FirmLevelProtectionIsInEffect => decide
  | killSwitchProtectionIsInEffect => decide
  | featureNotSupported => decide
  | undefinedError => decide
  | invalidRequest => decide
  | notRequested => decide
  | downgradedFromOlderVersion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ComplexLiquidityProtectionResetStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ComplexLiquidityProtectionResetStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ComplexLiquidityProtectionResetStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ComplexLiquidityProtectionResetStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ComplexLiquidityProtectionResetStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ComplexLiquidityProtectionResetStatus

/-- Status: one byte code -/
def Status.codes : List UInt8 :=
  [0x20, 0x4D, 0x43, 0x49, 0x53, 0x45, 0x5A, 0x2A]

inductive Status where
  | singleSideProtectionResetRequestSuccessful -- Single Side Protection Reset Request Successful
  | invalidMpid -- Invalid Mpid
  | invalidSecurityIdScope -- Invalid Security Id Scope
  | invalidSecurityId -- Invalid Security Id
  | invalidSide -- Invalid Side
  | featureNotEnabled -- Feature Not Enabled
  | undefinedError -- Undefined Error
  | downgradedFromOlderVersion -- Downgraded From Older Version
  | unlisted (byte : { byte : UInt8 // byte ∉ Status.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Status

def toByte : Status → UInt8
  | .singleSideProtectionResetRequestSuccessful => 0x20
  | .invalidMpid => 0x4D
  | .invalidSecurityIdScope => 0x43
  | .invalidSecurityId => 0x49
  | .invalidSide => 0x53
  | .featureNotEnabled => 0x45
  | .undefinedError => 0x5A
  | .downgradedFromOlderVersion => 0x2A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Status :=
  if byte = 0x20 then .singleSideProtectionResetRequestSuccessful
  else if byte = 0x4D then .invalidMpid
  else if byte = 0x43 then .invalidSecurityIdScope
  else if byte = 0x49 then .invalidSecurityId
  else if byte = 0x53 then .invalidSide
  else if byte = 0x45 then .featureNotEnabled
  else if byte = 0x5A then .undefinedError
  else .downgradedFromOlderVersion

def ofByte (byte : UInt8) : Status :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Status) : ofByte value.toByte = value := by
  cases value with
  | singleSideProtectionResetRequestSuccessful => decide
  | invalidMpid => decide
  | invalidSecurityIdScope => decide
  | invalidSecurityId => decide
  | invalidSide => decide
  | featureNotEnabled => decide
  | undefinedError => decide
  | downgradedFromOlderVersion => decide
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

/-- Trigger Reason: one byte code -/
def TriggerReason.codes : List UInt8 :=
  [0x45, 0x44, 0x55, 0x52, 0x54, 0x4B, 0x46, 0x4A, 0x2A]

inductive TriggerReason where
  | exchangeInitiatedMassQuoteCancel -- Exchange Initiated Mass Quote Cancel
  | lineDisconnectInitiatedMassQuoteCancel -- Line Disconnect Initiated Mass Quote Cancel
  | firmInitiatedMassQuoteCancel -- Firm Initiated Mass Quote Cancel
  | armTriggeredProtection -- Arm Triggered Protection
  | tradingHalt -- Trading Halt
  | killSwitchProtectionIsInEffectFutureUse -- Kill Switch Protection Is In Effect Future Use
  | arm2FirmLevelProtectionInitiatedMassQuoteCancel -- Arm 2 Firm Level Protection Initiated Mass Quote Cancel
  | reservedForFutureUse -- Reserved For Future Use
  | downgradedFromOlderVersion -- Downgraded From Older Version
  | unlisted (byte : { byte : UInt8 // byte ∉ TriggerReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TriggerReason

def toByte : TriggerReason → UInt8
  | .exchangeInitiatedMassQuoteCancel => 0x45
  | .lineDisconnectInitiatedMassQuoteCancel => 0x44
  | .firmInitiatedMassQuoteCancel => 0x55
  | .armTriggeredProtection => 0x52
  | .tradingHalt => 0x54
  | .killSwitchProtectionIsInEffectFutureUse => 0x4B
  | .arm2FirmLevelProtectionInitiatedMassQuoteCancel => 0x46
  | .reservedForFutureUse => 0x4A
  | .downgradedFromOlderVersion => 0x2A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TriggerReason :=
  if byte = 0x45 then .exchangeInitiatedMassQuoteCancel
  else if byte = 0x44 then .lineDisconnectInitiatedMassQuoteCancel
  else if byte = 0x55 then .firmInitiatedMassQuoteCancel
  else if byte = 0x52 then .armTriggeredProtection
  else if byte = 0x54 then .tradingHalt
  else if byte = 0x4B then .killSwitchProtectionIsInEffectFutureUse
  else if byte = 0x46 then .arm2FirmLevelProtectionInitiatedMassQuoteCancel
  else if byte = 0x4A then .reservedForFutureUse
  else .downgradedFromOlderVersion

def ofByte (byte : UInt8) : TriggerReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TriggerReason) : ofByte value.toByte = value := by
  cases value with
  | exchangeInitiatedMassQuoteCancel => decide
  | lineDisconnectInitiatedMassQuoteCancel => decide
  | firmInitiatedMassQuoteCancel => decide
  | armTriggeredProtection => decide
  | tradingHalt => decide
  | killSwitchProtectionIsInEffectFutureUse => decide
  | arm2FirmLevelProtectionInitiatedMassQuoteCancel => decide
  | reservedForFutureUse => decide
  | downgradedFromOlderVersion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TriggerReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TriggerReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TriggerReason) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TriggerReason) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TriggerReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TriggerReason

/-- Login Status: one byte code -/
def LoginStatus.codes : List UInt8 :=
  [0x20, 0x58, 0x53, 0x4E, 0x49, 0x41, 0x4C]

inductive LoginStatus where
  | loginSuccessful -- Login Successful
  | rejected -- Rejected
  | requestedSessionIsNotAvailable -- Requested Session Is Not Available
  | invalidStartSequenceNumberRequested -- Invalid Start Sequence Number Requested
  | incompatibleSessionProtocolVersion -- Incompatible Session Protocol Version
  | incompatibleApplicationProtocolVersion -- Incompatible Application Protocol Version
  | requestRejectedBecauseClientAlreadyLoggedIn -- Request Rejected Because Client Already Logged In
  | unlisted (byte : { byte : UInt8 // byte ∉ LoginStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LoginStatus

def toByte : LoginStatus → UInt8
  | .loginSuccessful => 0x20
  | .rejected => 0x58
  | .requestedSessionIsNotAvailable => 0x53
  | .invalidStartSequenceNumberRequested => 0x4E
  | .incompatibleSessionProtocolVersion => 0x49
  | .incompatibleApplicationProtocolVersion => 0x41
  | .requestRejectedBecauseClientAlreadyLoggedIn => 0x4C
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LoginStatus :=
  if byte = 0x20 then .loginSuccessful
  else if byte = 0x58 then .rejected
  else if byte = 0x53 then .requestedSessionIsNotAvailable
  else if byte = 0x4E then .invalidStartSequenceNumberRequested
  else if byte = 0x49 then .incompatibleSessionProtocolVersion
  else if byte = 0x41 then .incompatibleApplicationProtocolVersion
  else .requestRejectedBecauseClientAlreadyLoggedIn

def ofByte (byte : UInt8) : LoginStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LoginStatus) : ofByte value.toByte = value := by
  cases value with
  | loginSuccessful => decide
  | rejected => decide
  | requestedSessionIsNotAvailable => decide
  | invalidStartSequenceNumberRequested => decide
  | incompatibleSessionProtocolVersion => decide
  | incompatibleApplicationProtocolVersion => decide
  | requestRejectedBecauseClientAlreadyLoggedIn => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LoginStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LoginStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LoginStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : LoginStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : LoginStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LoginStatus

/-- Logout Reason: one byte code -/
def LogoutReason.codes : List UInt8 :=
  [0x20, 0x42, 0x4C, 0x41]

inductive LogoutReason where
  | gracefulLogout -- Graceful Logout
  | badSesmPacket -- Bad Sesm Packet
  | timedOutWaitingForLoginPacket -- Timed Out Waiting For Login Packet
  | applicationTerminatingConnection -- Application Terminating Connection
  | unlisted (byte : { byte : UInt8 // byte ∉ LogoutReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LogoutReason

def toByte : LogoutReason → UInt8
  | .gracefulLogout => 0x20
  | .badSesmPacket => 0x42
  | .timedOutWaitingForLoginPacket => 0x4C
  | .applicationTerminatingConnection => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LogoutReason :=
  if byte = 0x20 then .gracefulLogout
  else if byte = 0x42 then .badSesmPacket
  else if byte = 0x4C then .timedOutWaitingForLoginPacket
  else .applicationTerminatingConnection

def ofByte (byte : UInt8) : LogoutReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LogoutReason) : ofByte value.toByte = value := by
  cases value with
  | gracefulLogout => decide
  | badSesmPacket => decide
  | timedOutWaitingForLoginPacket => decide
  | applicationTerminatingConnection => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LogoutReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LogoutReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LogoutReason) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : LogoutReason) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : LogoutReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LogoutReason

/-- Goodbye Reason: one byte code -/
def GoodbyeReason.codes : List UInt8 :=
  [0x42, 0x4C, 0x41]

inductive GoodbyeReason where
  | badSesmPacket -- Bad Sesm Packet
  | timedOutWaitingForLoginPacket -- Timed Out Waiting For Login Packet
  | applicationTerminatingConnection -- Application Terminating Connection
  | unlisted (byte : { byte : UInt8 // byte ∉ GoodbyeReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace GoodbyeReason

def toByte : GoodbyeReason → UInt8
  | .badSesmPacket => 0x42
  | .timedOutWaitingForLoginPacket => 0x4C
  | .applicationTerminatingConnection => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : GoodbyeReason :=
  if byte = 0x42 then .badSesmPacket
  else if byte = 0x4C then .timedOutWaitingForLoginPacket
  else .applicationTerminatingConnection

def ofByte (byte : UInt8) : GoodbyeReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : GoodbyeReason) : ofByte value.toByte = value := by
  cases value with
  | badSesmPacket => decide
  | timedOutWaitingForLoginPacket => decide
  | applicationTerminatingConnection => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : GoodbyeReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (GoodbyeReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : GoodbyeReason) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : GoodbyeReason) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : GoodbyeReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end GoodbyeReason

/-- Simple Series Update: 76 bytes -/
structure SimpleSeriesUpdate where
  productAddUpdateTime : BitVec 64
  productId : BitVec 32
  underlyingSymbol : Alpha 11
  securitySymbol : Alpha 6
  expirationDate : Alpha 8
  strikePrice : BitVec 32
  callOrPut : CallOrPut
  openingTime : Alpha 8
  closingTime : Alpha 8
  restrictedOption : RestrictedOption
  longTermOption : LongTermOption
  activeOnMiax : ActiveOnMiax
  miaxBboPostingIncrementIndicator : MiaxBboPostingIncrementIndicator
  quoteAcceptanceIncrementIndicator : QuoteAcceptanceIncrementIndicator
  openingUnderlyingMarketCode : OpeningUnderlyingMarketCode
  priorityQuoteWidth : BitVec 32
  reserved8 : Alpha 8
  deriving DecidableEq, Repr

namespace SimpleSeriesUpdate

def encode (message : SimpleSeriesUpdate) : List UInt8 :=
  encodeUIntLE 8 message.productAddUpdateTime
    ++ (encodeUIntLE 4 message.productId
    ++ (Alpha.encode message.underlyingSymbol
    ++ (Alpha.encode message.securitySymbol
    ++ (Alpha.encode message.expirationDate
    ++ (encodeUIntLE 4 message.strikePrice
    ++ (CallOrPut.encode message.callOrPut
    ++ (Alpha.encode message.openingTime
    ++ (Alpha.encode message.closingTime
    ++ (RestrictedOption.encode message.restrictedOption
    ++ (LongTermOption.encode message.longTermOption
    ++ (ActiveOnMiax.encode message.activeOnMiax
    ++ (MiaxBboPostingIncrementIndicator.encode message.miaxBboPostingIncrementIndicator
    ++ (QuoteAcceptanceIncrementIndicator.encode message.quoteAcceptanceIncrementIndicator
    ++ (OpeningUnderlyingMarketCode.encode message.openingUnderlyingMarketCode
    ++ (encodeUIntLE 4 message.priorityQuoteWidth
    ++ (Alpha.encode message.reserved8))))))))))))))))

def decode (bytes : List UInt8) : Option (SimpleSeriesUpdate × List UInt8) := do
  let (productAddUpdateTime, bytes) ← decodeUIntLE 8 bytes
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 11 bytes
  let (securitySymbol, bytes) ← Alpha.decode 6 bytes
  let (expirationDate, bytes) ← Alpha.decode 8 bytes
  let (strikePrice, bytes) ← decodeUIntLE 4 bytes
  let (callOrPut, bytes) ← CallOrPut.decode bytes
  let (openingTime, bytes) ← Alpha.decode 8 bytes
  let (closingTime, bytes) ← Alpha.decode 8 bytes
  let (restrictedOption, bytes) ← RestrictedOption.decode bytes
  let (longTermOption, bytes) ← LongTermOption.decode bytes
  let (activeOnMiax, bytes) ← ActiveOnMiax.decode bytes
  let (miaxBboPostingIncrementIndicator, bytes) ← MiaxBboPostingIncrementIndicator.decode bytes
  let (quoteAcceptanceIncrementIndicator, bytes) ← QuoteAcceptanceIncrementIndicator.decode bytes
  let (openingUnderlyingMarketCode, bytes) ← OpeningUnderlyingMarketCode.decode bytes
  let (priorityQuoteWidth, bytes) ← decodeUIntLE 4 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  pure ({ productAddUpdateTime, productId, underlyingSymbol, securitySymbol, expirationDate, strikePrice, callOrPut, openingTime, closingTime, restrictedOption, longTermOption, activeOnMiax, miaxBboPostingIncrementIndicator, quoteAcceptanceIncrementIndicator, openingUnderlyingMarketCode, priorityQuoteWidth, reserved8 }, bytes)

@[simp] theorem encode_length (message : SimpleSeriesUpdate) : (encode message).length = 76 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, CallOrPut.encode_length, RestrictedOption.encode_length, LongTermOption.encode_length, ActiveOnMiax.encode_length, MiaxBboPostingIncrementIndicator.encode_length, QuoteAcceptanceIncrementIndicator.encode_length, OpeningUnderlyingMarketCode.encode_length]

theorem encode_length_pos (message : SimpleSeriesUpdate) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SimpleSeriesUpdate) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, CallOrPut.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RestrictedOption.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LongTermOption.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ActiveOnMiax.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MiaxBboPostingIncrementIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, QuoteAcceptanceIncrementIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpeningUnderlyingMarketCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SimpleSeriesUpdate

/-- Valid Quote Width For Opening: 21 bytes -/
structure ValidQuoteWidthForOpening where
  notificationTime : BitVec 64
  mpvClass : MpvClass
  lowEndOfApplicableRange : BitVec 32
  maximumQuoteWidth : BitVec 32
  longTermOptionMultiplier : BitVec 32
  deriving DecidableEq, Repr

namespace ValidQuoteWidthForOpening

def encode (message : ValidQuoteWidthForOpening) : List UInt8 :=
  encodeUIntLE 8 message.notificationTime
    ++ (MpvClass.encode message.mpvClass
    ++ (encodeUIntLE 4 message.lowEndOfApplicableRange
    ++ (encodeUIntLE 4 message.maximumQuoteWidth
    ++ (encodeUIntLE 4 message.longTermOptionMultiplier))))

def decode (bytes : List UInt8) : Option (ValidQuoteWidthForOpening × List UInt8) := do
  let (notificationTime, bytes) ← decodeUIntLE 8 bytes
  let (mpvClass, bytes) ← MpvClass.decode bytes
  let (lowEndOfApplicableRange, bytes) ← decodeUIntLE 4 bytes
  let (maximumQuoteWidth, bytes) ← decodeUIntLE 4 bytes
  let (longTermOptionMultiplier, bytes) ← decodeUIntLE 4 bytes
  pure ({ notificationTime, mpvClass, lowEndOfApplicableRange, maximumQuoteWidth, longTermOptionMultiplier }, bytes)

@[simp] theorem encode_length (message : ValidQuoteWidthForOpening) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, MpvClass.encode_length]

theorem encode_length_pos (message : ValidQuoteWidthForOpening) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ValidQuoteWidthForOpening) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, MpvClass.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ValidQuoteWidthForOpening

/-- Valid Quote Width For Free Trading: 37 bytes -/
structure ValidQuoteWidthForFreeTrading where
  notificationTime : BitVec 64
  mpvClass : MpvClass
  lowEndOfApplicableRange : BitVec 32
  maximumQuoteWidth : BitVec 32
  longTermOptionMultiplier : BitVec 32
  reserved16 : Alpha 16
  deriving DecidableEq, Repr

namespace ValidQuoteWidthForFreeTrading

def encode (message : ValidQuoteWidthForFreeTrading) : List UInt8 :=
  encodeUIntLE 8 message.notificationTime
    ++ (MpvClass.encode message.mpvClass
    ++ (encodeUIntLE 4 message.lowEndOfApplicableRange
    ++ (encodeUIntLE 4 message.maximumQuoteWidth
    ++ (encodeUIntLE 4 message.longTermOptionMultiplier
    ++ (Alpha.encode message.reserved16)))))

def decode (bytes : List UInt8) : Option (ValidQuoteWidthForFreeTrading × List UInt8) := do
  let (notificationTime, bytes) ← decodeUIntLE 8 bytes
  let (mpvClass, bytes) ← MpvClass.decode bytes
  let (lowEndOfApplicableRange, bytes) ← decodeUIntLE 4 bytes
  let (maximumQuoteWidth, bytes) ← decodeUIntLE 4 bytes
  let (longTermOptionMultiplier, bytes) ← decodeUIntLE 4 bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  pure ({ notificationTime, mpvClass, lowEndOfApplicableRange, maximumQuoteWidth, longTermOptionMultiplier, reserved16 }, bytes)

@[simp] theorem encode_length (message : ValidQuoteWidthForFreeTrading) : (encode message).length = 37 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, MpvClass.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : ValidQuoteWidthForFreeTrading) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ValidQuoteWidthForFreeTrading) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, MpvClass.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ValidQuoteWidthForFreeTrading

/-- Simple Enhanced Quote E Quote Response: 17 bytes -/
structure SimpleEnhancedQuoteEQuoteResponse where
  clientMessageId : BitVec 32
  mpid : Alpha 4
  eQuoteId : BitVec 64
  eQuoteRequestStatus : EQuoteRequestStatus
  deriving DecidableEq, Repr

namespace SimpleEnhancedQuoteEQuoteResponse

def encode (message : SimpleEnhancedQuoteEQuoteResponse) : List UInt8 :=
  encodeUIntLE 4 message.clientMessageId
    ++ (Alpha.encode message.mpid
    ++ (encodeUIntLE 8 message.eQuoteId
    ++ (EQuoteRequestStatus.encode message.eQuoteRequestStatus)))

def decode (bytes : List UInt8) : Option (SimpleEnhancedQuoteEQuoteResponse × List UInt8) := do
  let (clientMessageId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (eQuoteId, bytes) ← decodeUIntLE 8 bytes
  let (eQuoteRequestStatus, bytes) ← EQuoteRequestStatus.decode bytes
  pure ({ clientMessageId, mpid, eQuoteId, eQuoteRequestStatus }, bytes)

@[simp] theorem encode_length (message : SimpleEnhancedQuoteEQuoteResponse) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, EQuoteRequestStatus.encode_length]

theorem encode_length_pos (message : SimpleEnhancedQuoteEQuoteResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SimpleEnhancedQuoteEQuoteResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [EQuoteRequestStatus.decode_encode, some_bind]
  rfl

end SimpleEnhancedQuoteEQuoteResponse

/-- Complex Enhanced Quote E Quote Response: 17 bytes -/
structure ComplexEnhancedQuoteEQuoteResponse where
  clientMessageId : BitVec 32
  mpid : Alpha 4
  eQuoteId : BitVec 64
  eQuoteRequestStatus : EQuoteRequestStatus
  deriving DecidableEq, Repr

namespace ComplexEnhancedQuoteEQuoteResponse

def encode (message : ComplexEnhancedQuoteEQuoteResponse) : List UInt8 :=
  encodeUIntLE 4 message.clientMessageId
    ++ (Alpha.encode message.mpid
    ++ (encodeUIntLE 8 message.eQuoteId
    ++ (EQuoteRequestStatus.encode message.eQuoteRequestStatus)))

def decode (bytes : List UInt8) : Option (ComplexEnhancedQuoteEQuoteResponse × List UInt8) := do
  let (clientMessageId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (eQuoteId, bytes) ← decodeUIntLE 8 bytes
  let (eQuoteRequestStatus, bytes) ← EQuoteRequestStatus.decode bytes
  pure ({ clientMessageId, mpid, eQuoteId, eQuoteRequestStatus }, bytes)

@[simp] theorem encode_length (message : ComplexEnhancedQuoteEQuoteResponse) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, EQuoteRequestStatus.encode_length]

theorem encode_length_pos (message : ComplexEnhancedQuoteEQuoteResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ComplexEnhancedQuoteEQuoteResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [EQuoteRequestStatus.decode_encode, some_bind]
  rfl

end ComplexEnhancedQuoteEQuoteResponse

/-- System State Notification: 18 bytes -/
structure SystemStateNotification where
  notificationTime : BitVec 64
  meiVersion : Alpha 8
  sessionId : BitVec 8
  systemStatus : SystemStatus
  deriving DecidableEq, Repr

namespace SystemStateNotification

def encode (message : SystemStateNotification) : List UInt8 :=
  encodeUIntLE 8 message.notificationTime
    ++ (Alpha.encode message.meiVersion
    ++ (encodeUInt 1 message.sessionId
    ++ (SystemStatus.encode message.systemStatus)))

def decode (bytes : List UInt8) : Option (SystemStateNotification × List UInt8) := do
  let (notificationTime, bytes) ← decodeUIntLE 8 bytes
  let (meiVersion, bytes) ← Alpha.decode 8 bytes
  let (sessionId, bytes) ← decodeUInt 1 bytes
  let (systemStatus, bytes) ← SystemStatus.decode bytes
  pure ({ notificationTime, meiVersion, sessionId, systemStatus }, bytes)

@[simp] theorem encode_length (message : SystemStateNotification) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length, SystemStatus.encode_length]

theorem encode_length_pos (message : SystemStateNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemStateNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [SystemStatus.decode_encode, some_bind]
  rfl

end SystemStateNotification

/-- Product Trading Status Notification: 21 bytes -/
structure ProductTradingStatusNotification where
  notificationTime : BitVec 64
  productId : BitVec 32
  tradingStatus : TradingStatus
  expectedEventTime : BitVec 64
  deriving DecidableEq, Repr

namespace ProductTradingStatusNotification

def encode (message : ProductTradingStatusNotification) : List UInt8 :=
  encodeUIntLE 8 message.notificationTime
    ++ (encodeUIntLE 4 message.productId
    ++ (TradingStatus.encode message.tradingStatus
    ++ (encodeUIntLE 8 message.expectedEventTime)))

def decode (bytes : List UInt8) : Option (ProductTradingStatusNotification × List UInt8) := do
  let (notificationTime, bytes) ← decodeUIntLE 8 bytes
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (tradingStatus, bytes) ← TradingStatus.decode bytes
  let (expectedEventTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ notificationTime, productId, tradingStatus, expectedEventTime }, bytes)

@[simp] theorem encode_length (message : ProductTradingStatusNotification) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, TradingStatus.encode_length]

theorem encode_length_pos (message : ProductTradingStatusNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ProductTradingStatusNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TradingStatus.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ProductTradingStatusNotification

/-- Underlying Trading Status Notification: 29 bytes -/
structure UnderlyingTradingStatusNotification where
  notificationTime : BitVec 64
  underlyingSymbol : Alpha 11
  tradingStatus : TradingStatus
  eventReason : EventReason
  expectedEventTime : BitVec 64
  deriving DecidableEq, Repr

namespace UnderlyingTradingStatusNotification

def encode (message : UnderlyingTradingStatusNotification) : List UInt8 :=
  encodeUIntLE 8 message.notificationTime
    ++ (Alpha.encode message.underlyingSymbol
    ++ (TradingStatus.encode message.tradingStatus
    ++ (EventReason.encode message.eventReason
    ++ (encodeUIntLE 8 message.expectedEventTime))))

def decode (bytes : List UInt8) : Option (UnderlyingTradingStatusNotification × List UInt8) := do
  let (notificationTime, bytes) ← decodeUIntLE 8 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 11 bytes
  let (tradingStatus, bytes) ← TradingStatus.decode bytes
  let (eventReason, bytes) ← EventReason.decode bytes
  let (expectedEventTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ notificationTime, underlyingSymbol, tradingStatus, eventReason, expectedEventTime }, bytes)

@[simp] theorem encode_length (message : UnderlyingTradingStatusNotification) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TradingStatus.encode_length, EventReason.encode_length]

theorem encode_length_pos (message : UnderlyingTradingStatusNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UnderlyingTradingStatusNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradingStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, EventReason.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end UnderlyingTradingStatusNotification

/-- Opening Quote Width Relief Notification: 23 bytes -/
structure OpeningQuoteWidthReliefNotification where
  notificationTime : BitVec 64
  underlyingSymbol : Alpha 11
  reliefMultiplier : BitVec 32
  deriving DecidableEq, Repr

namespace OpeningQuoteWidthReliefNotification

def encode (message : OpeningQuoteWidthReliefNotification) : List UInt8 :=
  encodeUIntLE 8 message.notificationTime
    ++ (Alpha.encode message.underlyingSymbol
    ++ (encodeUIntLE 4 message.reliefMultiplier))

def decode (bytes : List UInt8) : Option (OpeningQuoteWidthReliefNotification × List UInt8) := do
  let (notificationTime, bytes) ← decodeUIntLE 8 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 11 bytes
  let (reliefMultiplier, bytes) ← decodeUIntLE 4 bytes
  pure ({ notificationTime, underlyingSymbol, reliefMultiplier }, bytes)

@[simp] theorem encode_length (message : OpeningQuoteWidthReliefNotification) : (encode message).length = 23 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : OpeningQuoteWidthReliefNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OpeningQuoteWidthReliefNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OpeningQuoteWidthReliefNotification

/-- Free Trading Quote Width Relief Notification: 39 bytes -/
structure FreeTradingQuoteWidthReliefNotification where
  notificationTime : BitVec 64
  underlyingSymbol : Alpha 11
  reliefMultiplier : BitVec 32
  reserved16 : Alpha 16
  deriving DecidableEq, Repr

namespace FreeTradingQuoteWidthReliefNotification

def encode (message : FreeTradingQuoteWidthReliefNotification) : List UInt8 :=
  encodeUIntLE 8 message.notificationTime
    ++ (Alpha.encode message.underlyingSymbol
    ++ (encodeUIntLE 4 message.reliefMultiplier
    ++ (Alpha.encode message.reserved16)))

def decode (bytes : List UInt8) : Option (FreeTradingQuoteWidthReliefNotification × List UInt8) := do
  let (notificationTime, bytes) ← decodeUIntLE 8 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 11 bytes
  let (reliefMultiplier, bytes) ← decodeUIntLE 4 bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  pure ({ notificationTime, underlyingSymbol, reliefMultiplier, reserved16 }, bytes)

@[simp] theorem encode_length (message : FreeTradingQuoteWidthReliefNotification) : (encode message).length = 39 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : FreeTradingQuoteWidthReliefNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FreeTradingQuoteWidthReliefNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FreeTradingQuoteWidthReliefNotification

/-- Simple Arm Protection Settings Notification: 59 bytes -/
structure SimpleArmProtectionSettingsNotification where
  notificationTime : BitVec 64
  mpid : Alpha 4
  underlyingSymbol : Alpha 11
  allowableEngagementPercentage : BitVec 32
  countingPeriod : BitVec 16
  action : Action
  source : Source
  marketMakerOriginMultiplier : BitVec 16
  awayMarketMakerOriginMultiplier : BitVec 16
  brokerDealerOriginMultiplier : BitVec 16
  firmOriginMultiplier : BitVec 16
  priorityCustomerOriginMultiplier : BitVec 16
  nonPriorityCustomerOriginMultiplier : BitVec 16
  reserved16 : Alpha 16
  deriving DecidableEq, Repr

namespace SimpleArmProtectionSettingsNotification

def encode (message : SimpleArmProtectionSettingsNotification) : List UInt8 :=
  encodeUIntLE 8 message.notificationTime
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.underlyingSymbol
    ++ (encodeUIntLE 4 message.allowableEngagementPercentage
    ++ (encodeUIntLE 2 message.countingPeriod
    ++ (Action.encode message.action
    ++ (Source.encode message.source
    ++ (encodeUIntLE 2 message.marketMakerOriginMultiplier
    ++ (encodeUIntLE 2 message.awayMarketMakerOriginMultiplier
    ++ (encodeUIntLE 2 message.brokerDealerOriginMultiplier
    ++ (encodeUIntLE 2 message.firmOriginMultiplier
    ++ (encodeUIntLE 2 message.priorityCustomerOriginMultiplier
    ++ (encodeUIntLE 2 message.nonPriorityCustomerOriginMultiplier
    ++ (Alpha.encode message.reserved16)))))))))))))

def decode (bytes : List UInt8) : Option (SimpleArmProtectionSettingsNotification × List UInt8) := do
  let (notificationTime, bytes) ← decodeUIntLE 8 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 11 bytes
  let (allowableEngagementPercentage, bytes) ← decodeUIntLE 4 bytes
  let (countingPeriod, bytes) ← decodeUIntLE 2 bytes
  let (action, bytes) ← Action.decode bytes
  let (source, bytes) ← Source.decode bytes
  let (marketMakerOriginMultiplier, bytes) ← decodeUIntLE 2 bytes
  let (awayMarketMakerOriginMultiplier, bytes) ← decodeUIntLE 2 bytes
  let (brokerDealerOriginMultiplier, bytes) ← decodeUIntLE 2 bytes
  let (firmOriginMultiplier, bytes) ← decodeUIntLE 2 bytes
  let (priorityCustomerOriginMultiplier, bytes) ← decodeUIntLE 2 bytes
  let (nonPriorityCustomerOriginMultiplier, bytes) ← decodeUIntLE 2 bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  pure ({ notificationTime, mpid, underlyingSymbol, allowableEngagementPercentage, countingPeriod, action, source, marketMakerOriginMultiplier, awayMarketMakerOriginMultiplier, brokerDealerOriginMultiplier, firmOriginMultiplier, priorityCustomerOriginMultiplier, nonPriorityCustomerOriginMultiplier, reserved16 }, bytes)

@[simp] theorem encode_length (message : SimpleArmProtectionSettingsNotification) : (encode message).length = 59 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, Action.encode_length, Source.encode_length]

theorem encode_length_pos (message : SimpleArmProtectionSettingsNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SimpleArmProtectionSettingsNotification) (rest : List UInt8) :
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
  rw [List.append_assoc, Action.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Source.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end SimpleArmProtectionSettingsNotification

/-- Arm 2 Underlying Level Protection Settings Notification: 48 bytes -/
structure Arm2UnderlyingLevelProtectionSettingsNotification where
  notificationTime : BitVec 64
  mpid : Alpha 4
  action : Action
  underlyingSymbol : Alpha 11
  armThresholdCount : BitVec 32
  arm2CountingPeriod : BitVec 32
  reserved16 : Alpha 16
  deriving DecidableEq, Repr

namespace Arm2UnderlyingLevelProtectionSettingsNotification

def encode (message : Arm2UnderlyingLevelProtectionSettingsNotification) : List UInt8 :=
  encodeUIntLE 8 message.notificationTime
    ++ (Alpha.encode message.mpid
    ++ (Action.encode message.action
    ++ (Alpha.encode message.underlyingSymbol
    ++ (encodeUIntLE 4 message.armThresholdCount
    ++ (encodeUIntLE 4 message.arm2CountingPeriod
    ++ (Alpha.encode message.reserved16))))))

def decode (bytes : List UInt8) : Option (Arm2UnderlyingLevelProtectionSettingsNotification × List UInt8) := do
  let (notificationTime, bytes) ← decodeUIntLE 8 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (action, bytes) ← Action.decode bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 11 bytes
  let (armThresholdCount, bytes) ← decodeUIntLE 4 bytes
  let (arm2CountingPeriod, bytes) ← decodeUIntLE 4 bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  pure ({ notificationTime, mpid, action, underlyingSymbol, armThresholdCount, arm2CountingPeriod, reserved16 }, bytes)

@[simp] theorem encode_length (message : Arm2UnderlyingLevelProtectionSettingsNotification) : (encode message).length = 48 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, Action.encode_length]

theorem encode_length_pos (message : Arm2UnderlyingLevelProtectionSettingsNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Arm2UnderlyingLevelProtectionSettingsNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Action.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end Arm2UnderlyingLevelProtectionSettingsNotification

/-- Single Side Liquidity Protection Trigger Notification: 27 bytes -/
structure SingleSideLiquidityProtectionTriggerNotification where
  notificationTime : BitVec 64
  mpid : Alpha 4
  securityIdScope : SecurityIdScope
  securityId : BitVec 32
  side : Side
  triggeringClientMessageId : BitVec 32
  triggeringBulkQuoteIndex : BitVec 8
  reserved4 : Alpha 4
  deriving DecidableEq, Repr

namespace SingleSideLiquidityProtectionTriggerNotification

def encode (message : SingleSideLiquidityProtectionTriggerNotification) : List UInt8 :=
  encodeUIntLE 8 message.notificationTime
    ++ (Alpha.encode message.mpid
    ++ (SecurityIdScope.encode message.securityIdScope
    ++ (encodeUIntLE 4 message.securityId
    ++ (Side.encode message.side
    ++ (encodeUIntLE 4 message.triggeringClientMessageId
    ++ (encodeUInt 1 message.triggeringBulkQuoteIndex
    ++ (Alpha.encode message.reserved4)))))))

def decode (bytes : List UInt8) : Option (SingleSideLiquidityProtectionTriggerNotification × List UInt8) := do
  let (notificationTime, bytes) ← decodeUIntLE 8 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (securityIdScope, bytes) ← SecurityIdScope.decode bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (triggeringClientMessageId, bytes) ← decodeUIntLE 4 bytes
  let (triggeringBulkQuoteIndex, bytes) ← decodeUInt 1 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  pure ({ notificationTime, mpid, securityIdScope, securityId, side, triggeringClientMessageId, triggeringBulkQuoteIndex, reserved4 }, bytes)

@[simp] theorem encode_length (message : SingleSideLiquidityProtectionTriggerNotification) : (encode message).length = 27 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, SecurityIdScope.encode_length, Side.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SingleSideLiquidityProtectionTriggerNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SingleSideLiquidityProtectionTriggerNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityIdScope.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SingleSideLiquidityProtectionTriggerNotification

/-- Arm 2 Underlying Level Protection Notification: 48 bytes -/
structure Arm2UnderlyingLevelProtectionNotification where
  notificationTime : BitVec 64
  mpid : Alpha 4
  underlyingSymbol : Alpha 11
  notificationType : NotificationType
  armThresholdCount : BitVec 32
  arm2CountingPeriod : BitVec 32
  reserved16 : Alpha 16
  deriving DecidableEq, Repr

namespace Arm2UnderlyingLevelProtectionNotification

def encode (message : Arm2UnderlyingLevelProtectionNotification) : List UInt8 :=
  encodeUIntLE 8 message.notificationTime
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.underlyingSymbol
    ++ (NotificationType.encode message.notificationType
    ++ (encodeUIntLE 4 message.armThresholdCount
    ++ (encodeUIntLE 4 message.arm2CountingPeriod
    ++ (Alpha.encode message.reserved16))))))

def decode (bytes : List UInt8) : Option (Arm2UnderlyingLevelProtectionNotification × List UInt8) := do
  let (notificationTime, bytes) ← decodeUIntLE 8 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 11 bytes
  let (notificationType, bytes) ← NotificationType.decode bytes
  let (armThresholdCount, bytes) ← decodeUIntLE 4 bytes
  let (arm2CountingPeriod, bytes) ← decodeUIntLE 4 bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  pure ({ notificationTime, mpid, underlyingSymbol, notificationType, armThresholdCount, arm2CountingPeriod, reserved16 }, bytes)

@[simp] theorem encode_length (message : Arm2UnderlyingLevelProtectionNotification) : (encode message).length = 48 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, NotificationType.encode_length]

theorem encode_length_pos (message : Arm2UnderlyingLevelProtectionNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Arm2UnderlyingLevelProtectionNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NotificationType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end Arm2UnderlyingLevelProtectionNotification

/-- Arm 2 Firm Level Protection Notification: 33 bytes -/
structure Arm2FirmLevelProtectionNotification where
  notificationTime : BitVec 64
  armThresholdCount : BitVec 32
  arm2CountingPeriod : BitVec 32
  notificationType : NotificationType
  reserved16 : Alpha 16
  deriving DecidableEq, Repr

namespace Arm2FirmLevelProtectionNotification

def encode (message : Arm2FirmLevelProtectionNotification) : List UInt8 :=
  encodeUIntLE 8 message.notificationTime
    ++ (encodeUIntLE 4 message.armThresholdCount
    ++ (encodeUIntLE 4 message.arm2CountingPeriod
    ++ (NotificationType.encode message.notificationType
    ++ (Alpha.encode message.reserved16))))

def decode (bytes : List UInt8) : Option (Arm2FirmLevelProtectionNotification × List UInt8) := do
  let (notificationTime, bytes) ← decodeUIntLE 8 bytes
  let (armThresholdCount, bytes) ← decodeUIntLE 4 bytes
  let (arm2CountingPeriod, bytes) ← decodeUIntLE 4 bytes
  let (notificationType, bytes) ← NotificationType.decode bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  pure ({ notificationTime, armThresholdCount, arm2CountingPeriod, notificationType, reserved16 }, bytes)

@[simp] theorem encode_length (message : Arm2FirmLevelProtectionNotification) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, NotificationType.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : Arm2FirmLevelProtectionNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Arm2FirmLevelProtectionNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, NotificationType.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end Arm2FirmLevelProtectionNotification

/-- Leg: 15 bytes -/
structure Leg where
  productId : BitVec 32
  legRatioQty : BitVec 16
  legSide : LegSide
  reserved8 : Alpha 8
  deriving DecidableEq, Repr

namespace Leg

def encode (message : Leg) : List UInt8 :=
  encodeUIntLE 4 message.productId
    ++ (encodeUIntLE 2 message.legRatioQty
    ++ (LegSide.encode message.legSide
    ++ (Alpha.encode message.reserved8)))

def decode (bytes : List UInt8) : Option (Leg × List UInt8) := do
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (legRatioQty, bytes) ← decodeUIntLE 2 bytes
  let (legSide, bytes) ← LegSide.decode bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  pure ({ productId, legRatioQty, legSide, reserved8 }, bytes)

@[simp] theorem encode_length (message : Leg) : (encode message).length = 15 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, LegSide.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : Leg) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Leg) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, LegSide.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end Leg

/-- Complex Strategy Definition Notification -/
structure ComplexStrategyDefinitionNotification where
  notificationTime : BitVec 64
  strategyId : BitVec 32
  underlyingSymbol : Alpha 11
  activeOnMiax : ActiveOnMiax
  reserved1 : Alpha 1
  updateReason : UpdateReason
  reserved10 : Alpha 10
  leg : Bounded 1 Leg
  deriving DecidableEq, Repr

namespace ComplexStrategyDefinitionNotification

def encode (message : ComplexStrategyDefinitionNotification) : List UInt8 :=
  encodeUIntLE 8 message.notificationTime
    ++ (encodeUIntLE 4 message.strategyId
    ++ (Alpha.encode message.underlyingSymbol
    ++ (ActiveOnMiax.encode message.activeOnMiax
    ++ (Alpha.encode message.reserved1
    ++ (UpdateReason.encode message.updateReason
    ++ (Alpha.encode message.reserved10
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.leg.val.length)
    ++ (encodeMany Leg.encode message.leg.val))))))))

def decode (bytes : List UInt8) : Option (ComplexStrategyDefinitionNotification × List UInt8) := do
  let (notificationTime, bytes) ← decodeUIntLE 8 bytes
  let (strategyId, bytes) ← decodeUIntLE 4 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 11 bytes
  let (activeOnMiax, bytes) ← ActiveOnMiax.decode bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (updateReason, bytes) ← UpdateReason.decode bytes
  let (reserved10, bytes) ← Alpha.decode 10 bytes
  let (numberOfLegs, bytes) ← decodeUInt 1 bytes
  let (leg_, bytes) ← decodeMany Leg.decode numberOfLegs.toNat bytes
  if fits_leg : leg_.length < 256 ^ 1 then
    pure ({ notificationTime, strategyId, underlyingSymbol, activeOnMiax, reserved1, updateReason, reserved10, leg := ⟨leg_, fits_leg⟩ }, bytes)
  else none

theorem encode_length_pos (message : ComplexStrategyDefinitionNotification) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ComplexStrategyDefinitionNotification) : (encode message).length ≤ 3862 := by
  have bound_leg := message.leg.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Alpha.encode_length, ActiveOnMiax.encode_length, UpdateReason.encode_length, encodeUInt_length, encodeMany_length_const Leg.encode 15 Leg.encode_length]
  omega

@[simp] theorem decode_encode (message : ComplexStrategyDefinitionNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ActiveOnMiax.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, UpdateReason.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 Leg.encode Leg.decode Leg.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.leg.length_lt]
  rfl

end ComplexStrategyDefinitionNotification

/-- Cancel Notification: 36 bytes -/
structure CancelNotification where
  notificationTime : BitVec 64
  mpid : Alpha 4
  productIdOrStrategyId : BitVec 32
  liquidityType : LiquidityType
  clientMessageId : BitVec 32
  bulkQuoteIndex : BitVec 8
  quoteeQuoteSide : QuoteeQuoteSide
  size : BitVec 32
  engineSequenceNumber : BitVec 64
  cancelReason : CancelReason
  deriving DecidableEq, Repr

namespace CancelNotification

def encode (message : CancelNotification) : List UInt8 :=
  encodeUIntLE 8 message.notificationTime
    ++ (Alpha.encode message.mpid
    ++ (encodeUIntLE 4 message.productIdOrStrategyId
    ++ (LiquidityType.encode message.liquidityType
    ++ (encodeUIntLE 4 message.clientMessageId
    ++ (encodeUInt 1 message.bulkQuoteIndex
    ++ (QuoteeQuoteSide.encode message.quoteeQuoteSide
    ++ (encodeUIntLE 4 message.size
    ++ (encodeUIntLE 8 message.engineSequenceNumber
    ++ (CancelReason.encode message.cancelReason)))))))))

def decode (bytes : List UInt8) : Option (CancelNotification × List UInt8) := do
  let (notificationTime, bytes) ← decodeUIntLE 8 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (productIdOrStrategyId, bytes) ← decodeUIntLE 4 bytes
  let (liquidityType, bytes) ← LiquidityType.decode bytes
  let (clientMessageId, bytes) ← decodeUIntLE 4 bytes
  let (bulkQuoteIndex, bytes) ← decodeUInt 1 bytes
  let (quoteeQuoteSide, bytes) ← QuoteeQuoteSide.decode bytes
  let (size, bytes) ← decodeUIntLE 4 bytes
  let (engineSequenceNumber, bytes) ← decodeUIntLE 8 bytes
  let (cancelReason, bytes) ← CancelReason.decode bytes
  pure ({ notificationTime, mpid, productIdOrStrategyId, liquidityType, clientMessageId, bulkQuoteIndex, quoteeQuoteSide, size, engineSequenceNumber, cancelReason }, bytes)

@[simp] theorem encode_length (message : CancelNotification) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, LiquidityType.encode_length, encodeUInt_length, QuoteeQuoteSide.encode_length, CancelReason.encode_length]

theorem encode_length_pos (message : CancelNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CancelNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, LiquidityType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, QuoteeQuoteSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [CancelReason.decode_encode, some_bind]
  rfl

end CancelNotification

/-- Option Execution Notification: 49 bytes -/
structure OptionExecutionNotification where
  notificationTime : BitVec 64
  mpid : Alpha 4
  productId : BitVec 32
  liquidityType : LiquidityType
  clientMessageId : BitVec 32
  bulkQuoteIndex : BitVec 8
  eventId : BitVec 32
  tradeId : BitVec 32
  executionId : BitVec 64
  reserved1 : Alpha 1
  tradeStatus : TradeStatus
  lastPrice : BitVec 32
  side : Side
  lastSize : BitVec 32
  deriving DecidableEq, Repr

namespace OptionExecutionNotification

def encode (message : OptionExecutionNotification) : List UInt8 :=
  encodeUIntLE 8 message.notificationTime
    ++ (Alpha.encode message.mpid
    ++ (encodeUIntLE 4 message.productId
    ++ (LiquidityType.encode message.liquidityType
    ++ (encodeUIntLE 4 message.clientMessageId
    ++ (encodeUInt 1 message.bulkQuoteIndex
    ++ (encodeUIntLE 4 message.eventId
    ++ (encodeUIntLE 4 message.tradeId
    ++ (encodeUIntLE 8 message.executionId
    ++ (Alpha.encode message.reserved1
    ++ (TradeStatus.encode message.tradeStatus
    ++ (encodeUIntLE 4 message.lastPrice
    ++ (Side.encode message.side
    ++ (encodeUIntLE 4 message.lastSize)))))))))))))

def decode (bytes : List UInt8) : Option (OptionExecutionNotification × List UInt8) := do
  let (notificationTime, bytes) ← decodeUIntLE 8 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (liquidityType, bytes) ← LiquidityType.decode bytes
  let (clientMessageId, bytes) ← decodeUIntLE 4 bytes
  let (bulkQuoteIndex, bytes) ← decodeUInt 1 bytes
  let (eventId, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (executionId, bytes) ← decodeUIntLE 8 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (tradeStatus, bytes) ← TradeStatus.decode bytes
  let (lastPrice, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (lastSize, bytes) ← decodeUIntLE 4 bytes
  pure ({ notificationTime, mpid, productId, liquidityType, clientMessageId, bulkQuoteIndex, eventId, tradeId, executionId, reserved1, tradeStatus, lastPrice, side, lastSize }, bytes)

@[simp] theorem encode_length (message : OptionExecutionNotification) : (encode message).length = 49 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, LiquidityType.encode_length, encodeUInt_length, TradeStatus.encode_length, Side.encode_length]

theorem encode_length_pos (message : OptionExecutionNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionExecutionNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, LiquidityType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OptionExecutionNotification

/-- Stock Leg Execution Notification: 71 bytes -/
structure StockLegExecutionNotification where
  notificationTime : BitVec 64
  mpid : Alpha 4
  underlyingSymbol : Alpha 11
  liquidityType : LiquidityType
  clientMessageId : BitVec 32
  eventId : BitVec 32
  tradeId : BitVec 32
  executionId : BitVec 64
  tradeStatus : TradeStatus
  lastPrice : BitVec 32
  side : Side
  stockSellShortIndicator : StockSellShortIndicator
  lastSize : BitVec 32
  reserved16 : Alpha 16
  deriving DecidableEq, Repr

namespace StockLegExecutionNotification

def encode (message : StockLegExecutionNotification) : List UInt8 :=
  encodeUIntLE 8 message.notificationTime
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.underlyingSymbol
    ++ (LiquidityType.encode message.liquidityType
    ++ (encodeUIntLE 4 message.clientMessageId
    ++ (encodeUIntLE 4 message.eventId
    ++ (encodeUIntLE 4 message.tradeId
    ++ (encodeUIntLE 8 message.executionId
    ++ (TradeStatus.encode message.tradeStatus
    ++ (encodeUIntLE 4 message.lastPrice
    ++ (Side.encode message.side
    ++ (StockSellShortIndicator.encode message.stockSellShortIndicator
    ++ (encodeUIntLE 4 message.lastSize
    ++ (Alpha.encode message.reserved16)))))))))))))

def decode (bytes : List UInt8) : Option (StockLegExecutionNotification × List UInt8) := do
  let (notificationTime, bytes) ← decodeUIntLE 8 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 11 bytes
  let (liquidityType, bytes) ← LiquidityType.decode bytes
  let (clientMessageId, bytes) ← decodeUIntLE 4 bytes
  let (eventId, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (executionId, bytes) ← decodeUIntLE 8 bytes
  let (tradeStatus, bytes) ← TradeStatus.decode bytes
  let (lastPrice, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (stockSellShortIndicator, bytes) ← StockSellShortIndicator.decode bytes
  let (lastSize, bytes) ← decodeUIntLE 4 bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  pure ({ notificationTime, mpid, underlyingSymbol, liquidityType, clientMessageId, eventId, tradeId, executionId, tradeStatus, lastPrice, side, stockSellShortIndicator, lastSize, reserved16 }, bytes)

@[simp] theorem encode_length (message : StockLegExecutionNotification) : (encode message).length = 71 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, LiquidityType.encode_length, TradeStatus.encode_length, Side.encode_length, StockSellShortIndicator.encode_length]

theorem encode_length_pos (message : StockLegExecutionNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StockLegExecutionNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LiquidityType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TradeStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StockSellShortIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StockLegExecutionNotification

/-- Any Sequenced Message, selected by Sequenced Message Type -/
inductive SequencedMessage where
  | simpleSeriesUpdate (message : SimpleSeriesUpdate) -- "SU" 0x5355
  | validQuoteWidthForOpening (message : ValidQuoteWidthForOpening) -- "QW" 0x5157
  | validQuoteWidthForFreeTrading (message : ValidQuoteWidthForFreeTrading) -- "FW" 0x4657
  | simpleEnhancedQuoteEQuoteResponse (message : SimpleEnhancedQuoteEQuoteResponse) -- "ER" 0x4552
  | complexEnhancedQuoteEQuoteResponse (message : ComplexEnhancedQuoteEQuoteResponse) -- "CR" 0x4352
  | systemStateNotification (message : SystemStateNotification) -- "SN" 0x534E
  | productTradingStatusNotification (message : ProductTradingStatusNotification) -- "TN" 0x544E
  | underlyingTradingStatusNotification (message : UnderlyingTradingStatusNotification) -- "UN" 0x554E
  | openingQuoteWidthReliefNotification (message : OpeningQuoteWidthReliefNotification) -- "QN" 0x514E
  | freeTradingQuoteWidthReliefNotification (message : FreeTradingQuoteWidthReliefNotification) -- "FN" 0x464E
  | simpleArmProtectionSettingsNotification (message : SimpleArmProtectionSettingsNotification) -- "RN" 0x524E
  | arm2UnderlyingLevelProtectionSettingsNotification (message : Arm2UnderlyingLevelProtectionSettingsNotification) -- "A2" 0x4132
  | singleSideLiquidityProtectionTriggerNotification (message : SingleSideLiquidityProtectionTriggerNotification) -- "QX" 0x5158
  | arm2UnderlyingLevelProtectionNotification (message : Arm2UnderlyingLevelProtectionNotification) -- "UP" 0x5550
  | arm2FirmLevelProtectionNotification (message : Arm2FirmLevelProtectionNotification) -- "FP" 0x4650
  | complexStrategyDefinitionNotification (message : ComplexStrategyDefinitionNotification) -- "SC" 0x5343
  | cancelNotification (message : CancelNotification) -- "XN" 0x584E
  | optionExecutionNotification (message : OptionExecutionNotification) -- "EN" 0x454E
  | stockLegExecutionNotification (message : StockLegExecutionNotification) -- "ST" 0x5354
  deriving DecidableEq, Repr

namespace SequencedMessage

/-- The Sequenced Message Type each message is sent under -/
def tag : SequencedMessage → BitVec 16
  | .simpleSeriesUpdate _ => 21333
  | .validQuoteWidthForOpening _ => 20823
  | .validQuoteWidthForFreeTrading _ => 18007
  | .simpleEnhancedQuoteEQuoteResponse _ => 17746
  | .complexEnhancedQuoteEQuoteResponse _ => 17234
  | .systemStateNotification _ => 21326
  | .productTradingStatusNotification _ => 21582
  | .underlyingTradingStatusNotification _ => 21838
  | .openingQuoteWidthReliefNotification _ => 20814
  | .freeTradingQuoteWidthReliefNotification _ => 17998
  | .simpleArmProtectionSettingsNotification _ => 21070
  | .arm2UnderlyingLevelProtectionSettingsNotification _ => 16690
  | .singleSideLiquidityProtectionTriggerNotification _ => 20824
  | .arm2UnderlyingLevelProtectionNotification _ => 21840
  | .arm2FirmLevelProtectionNotification _ => 18000
  | .complexStrategyDefinitionNotification _ => 21315
  | .cancelNotification _ => 22606
  | .optionExecutionNotification _ => 17742
  | .stockLegExecutionNotification _ => 21332

def encode : SequencedMessage → List UInt8
  | .simpleSeriesUpdate message => SimpleSeriesUpdate.encode message
  | .validQuoteWidthForOpening message => ValidQuoteWidthForOpening.encode message
  | .validQuoteWidthForFreeTrading message => ValidQuoteWidthForFreeTrading.encode message
  | .simpleEnhancedQuoteEQuoteResponse message => SimpleEnhancedQuoteEQuoteResponse.encode message
  | .complexEnhancedQuoteEQuoteResponse message => ComplexEnhancedQuoteEQuoteResponse.encode message
  | .systemStateNotification message => SystemStateNotification.encode message
  | .productTradingStatusNotification message => ProductTradingStatusNotification.encode message
  | .underlyingTradingStatusNotification message => UnderlyingTradingStatusNotification.encode message
  | .openingQuoteWidthReliefNotification message => OpeningQuoteWidthReliefNotification.encode message
  | .freeTradingQuoteWidthReliefNotification message => FreeTradingQuoteWidthReliefNotification.encode message
  | .simpleArmProtectionSettingsNotification message => SimpleArmProtectionSettingsNotification.encode message
  | .arm2UnderlyingLevelProtectionSettingsNotification message => Arm2UnderlyingLevelProtectionSettingsNotification.encode message
  | .singleSideLiquidityProtectionTriggerNotification message => SingleSideLiquidityProtectionTriggerNotification.encode message
  | .arm2UnderlyingLevelProtectionNotification message => Arm2UnderlyingLevelProtectionNotification.encode message
  | .arm2FirmLevelProtectionNotification message => Arm2FirmLevelProtectionNotification.encode message
  | .complexStrategyDefinitionNotification message => ComplexStrategyDefinitionNotification.encode message
  | .cancelNotification message => CancelNotification.encode message
  | .optionExecutionNotification message => OptionExecutionNotification.encode message
  | .stockLegExecutionNotification message => StockLegExecutionNotification.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : SequencedMessage) : (encode message).length ≤ 3862 := by
  cases message with
  | simpleSeriesUpdate inner =>
    simp only [encode, SimpleSeriesUpdate.encode_length]
    omega
  | validQuoteWidthForOpening inner =>
    simp only [encode, ValidQuoteWidthForOpening.encode_length]
    omega
  | validQuoteWidthForFreeTrading inner =>
    simp only [encode, ValidQuoteWidthForFreeTrading.encode_length]
    omega
  | simpleEnhancedQuoteEQuoteResponse inner =>
    simp only [encode, SimpleEnhancedQuoteEQuoteResponse.encode_length]
    omega
  | complexEnhancedQuoteEQuoteResponse inner =>
    simp only [encode, ComplexEnhancedQuoteEQuoteResponse.encode_length]
    omega
  | systemStateNotification inner =>
    simp only [encode, SystemStateNotification.encode_length]
    omega
  | productTradingStatusNotification inner =>
    simp only [encode, ProductTradingStatusNotification.encode_length]
    omega
  | underlyingTradingStatusNotification inner =>
    simp only [encode, UnderlyingTradingStatusNotification.encode_length]
    omega
  | openingQuoteWidthReliefNotification inner =>
    simp only [encode, OpeningQuoteWidthReliefNotification.encode_length]
    omega
  | freeTradingQuoteWidthReliefNotification inner =>
    simp only [encode, FreeTradingQuoteWidthReliefNotification.encode_length]
    omega
  | simpleArmProtectionSettingsNotification inner =>
    simp only [encode, SimpleArmProtectionSettingsNotification.encode_length]
    omega
  | arm2UnderlyingLevelProtectionSettingsNotification inner =>
    simp only [encode, Arm2UnderlyingLevelProtectionSettingsNotification.encode_length]
    omega
  | singleSideLiquidityProtectionTriggerNotification inner =>
    simp only [encode, SingleSideLiquidityProtectionTriggerNotification.encode_length]
    omega
  | arm2UnderlyingLevelProtectionNotification inner =>
    simp only [encode, Arm2UnderlyingLevelProtectionNotification.encode_length]
    omega
  | arm2FirmLevelProtectionNotification inner =>
    simp only [encode, Arm2FirmLevelProtectionNotification.encode_length]
    omega
  | complexStrategyDefinitionNotification inner =>
    have bound_inner := ComplexStrategyDefinitionNotification.encode_length_le inner
    simp only [encode]
    omega
  | cancelNotification inner =>
    simp only [encode, CancelNotification.encode_length]
    omega
  | optionExecutionNotification inner =>
    simp only [encode, OptionExecutionNotification.encode_length]
    omega
  | stockLegExecutionNotification inner =>
    simp only [encode, StockLegExecutionNotification.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (SequencedMessage × List UInt8) :=
  if tag = 21333 then (SimpleSeriesUpdate.decode bytes).map fun (message, rest) => (.simpleSeriesUpdate message, rest)
  else if tag = 20823 then (ValidQuoteWidthForOpening.decode bytes).map fun (message, rest) => (.validQuoteWidthForOpening message, rest)
  else if tag = 18007 then (ValidQuoteWidthForFreeTrading.decode bytes).map fun (message, rest) => (.validQuoteWidthForFreeTrading message, rest)
  else if tag = 17746 then (SimpleEnhancedQuoteEQuoteResponse.decode bytes).map fun (message, rest) => (.simpleEnhancedQuoteEQuoteResponse message, rest)
  else if tag = 17234 then (ComplexEnhancedQuoteEQuoteResponse.decode bytes).map fun (message, rest) => (.complexEnhancedQuoteEQuoteResponse message, rest)
  else if tag = 21326 then (SystemStateNotification.decode bytes).map fun (message, rest) => (.systemStateNotification message, rest)
  else if tag = 21582 then (ProductTradingStatusNotification.decode bytes).map fun (message, rest) => (.productTradingStatusNotification message, rest)
  else if tag = 21838 then (UnderlyingTradingStatusNotification.decode bytes).map fun (message, rest) => (.underlyingTradingStatusNotification message, rest)
  else if tag = 20814 then (OpeningQuoteWidthReliefNotification.decode bytes).map fun (message, rest) => (.openingQuoteWidthReliefNotification message, rest)
  else if tag = 17998 then (FreeTradingQuoteWidthReliefNotification.decode bytes).map fun (message, rest) => (.freeTradingQuoteWidthReliefNotification message, rest)
  else if tag = 21070 then (SimpleArmProtectionSettingsNotification.decode bytes).map fun (message, rest) => (.simpleArmProtectionSettingsNotification message, rest)
  else if tag = 16690 then (Arm2UnderlyingLevelProtectionSettingsNotification.decode bytes).map fun (message, rest) => (.arm2UnderlyingLevelProtectionSettingsNotification message, rest)
  else if tag = 20824 then (SingleSideLiquidityProtectionTriggerNotification.decode bytes).map fun (message, rest) => (.singleSideLiquidityProtectionTriggerNotification message, rest)
  else if tag = 21840 then (Arm2UnderlyingLevelProtectionNotification.decode bytes).map fun (message, rest) => (.arm2UnderlyingLevelProtectionNotification message, rest)
  else if tag = 18000 then (Arm2FirmLevelProtectionNotification.decode bytes).map fun (message, rest) => (.arm2FirmLevelProtectionNotification message, rest)
  else if tag = 21315 then (ComplexStrategyDefinitionNotification.decode bytes).map fun (message, rest) => (.complexStrategyDefinitionNotification message, rest)
  else if tag = 22606 then (CancelNotification.decode bytes).map fun (message, rest) => (.cancelNotification message, rest)
  else if tag = 17742 then (OptionExecutionNotification.decode bytes).map fun (message, rest) => (.optionExecutionNotification message, rest)
  else if tag = 21332 then (StockLegExecutionNotification.decode bytes).map fun (message, rest) => (.stockLegExecutionNotification message, rest)
  else none

@[simp] theorem decode_encode (message : SequencedMessage) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end SequencedMessage

/-- Sequenced Data Packet -/
structure SequencedDataPacket where
  sequenceNumber : BitVec 64
  sequencedMessage : SequencedMessage
  deriving DecidableEq, Repr

namespace SequencedDataPacket

def encode (message : SequencedDataPacket) : List UInt8 :=
  encodeUIntLE 8 message.sequenceNumber
    ++ (encodeUInt 2 (SequencedMessage.tag message.sequencedMessage)
    ++ (SequencedMessage.encode message.sequencedMessage))

def decode (bytes : List UInt8) : Option (SequencedDataPacket × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 8 bytes
  let (sequencedMessageType, bytes) ← decodeUInt 2 bytes
  let (sequencedMessage, bytes) ← SequencedMessage.decode sequencedMessageType bytes
  pure ({ sequenceNumber, sequencedMessage }, bytes)

theorem encode_length_pos (message : SequencedDataPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SequencedDataPacket) : (encode message).length ≤ 3872 := by
  unfold encode
  cases message.sequencedMessage with
  | simpleSeriesUpdate inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, SimpleSeriesUpdate.encode_length]
    omega
  | validQuoteWidthForOpening inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, ValidQuoteWidthForOpening.encode_length]
    omega
  | validQuoteWidthForFreeTrading inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, ValidQuoteWidthForFreeTrading.encode_length]
    omega
  | simpleEnhancedQuoteEQuoteResponse inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, SimpleEnhancedQuoteEQuoteResponse.encode_length]
    omega
  | complexEnhancedQuoteEQuoteResponse inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, ComplexEnhancedQuoteEQuoteResponse.encode_length]
    omega
  | systemStateNotification inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, SystemStateNotification.encode_length]
    omega
  | productTradingStatusNotification inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, ProductTradingStatusNotification.encode_length]
    omega
  | underlyingTradingStatusNotification inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, UnderlyingTradingStatusNotification.encode_length]
    omega
  | openingQuoteWidthReliefNotification inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, OpeningQuoteWidthReliefNotification.encode_length]
    omega
  | freeTradingQuoteWidthReliefNotification inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, FreeTradingQuoteWidthReliefNotification.encode_length]
    omega
  | simpleArmProtectionSettingsNotification inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, SimpleArmProtectionSettingsNotification.encode_length]
    omega
  | arm2UnderlyingLevelProtectionSettingsNotification inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Arm2UnderlyingLevelProtectionSettingsNotification.encode_length]
    omega
  | singleSideLiquidityProtectionTriggerNotification inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, SingleSideLiquidityProtectionTriggerNotification.encode_length]
    omega
  | arm2UnderlyingLevelProtectionNotification inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Arm2UnderlyingLevelProtectionNotification.encode_length]
    omega
  | arm2FirmLevelProtectionNotification inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Arm2FirmLevelProtectionNotification.encode_length]
    omega
  | complexStrategyDefinitionNotification inner =>
    have bound_inner := ComplexStrategyDefinitionNotification.encode_length_le inner
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
    omega
  | cancelNotification inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, CancelNotification.encode_length]
    omega
  | optionExecutionNotification inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, OptionExecutionNotification.encode_length]
    omega
  | stockLegExecutionNotification inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, StockLegExecutionNotification.encode_length]
    omega

@[simp] theorem decode_encode (message : SequencedDataPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [SequencedMessage.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SequencedDataPacket) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SequencedDataPacket

/-- Simple Arm Settings Update Request: 54 bytes -/
structure SimpleArmSettingsUpdateRequest where
  clientMessageId : BitVec 32
  mpid : Alpha 4
  action : Action
  underlyingSymbol : Alpha 11
  allowableEngagementPercentage : BitVec 32
  countingPeriod : BitVec 16
  marketMakerOriginMultiplier : BitVec 16
  awayMarketMakerOriginMultiplier : BitVec 16
  brokerDealerOriginMultiplier : BitVec 16
  firmOriginMultiplier : BitVec 16
  priorityCustomerOriginMultiplier : BitVec 16
  nonPriorityCustomerOriginMultiplier : BitVec 16
  reserved16 : Alpha 16
  deriving DecidableEq, Repr

namespace SimpleArmSettingsUpdateRequest

def encode (message : SimpleArmSettingsUpdateRequest) : List UInt8 :=
  encodeUIntLE 4 message.clientMessageId
    ++ (Alpha.encode message.mpid
    ++ (Action.encode message.action
    ++ (Alpha.encode message.underlyingSymbol
    ++ (encodeUIntLE 4 message.allowableEngagementPercentage
    ++ (encodeUIntLE 2 message.countingPeriod
    ++ (encodeUIntLE 2 message.marketMakerOriginMultiplier
    ++ (encodeUIntLE 2 message.awayMarketMakerOriginMultiplier
    ++ (encodeUIntLE 2 message.brokerDealerOriginMultiplier
    ++ (encodeUIntLE 2 message.firmOriginMultiplier
    ++ (encodeUIntLE 2 message.priorityCustomerOriginMultiplier
    ++ (encodeUIntLE 2 message.nonPriorityCustomerOriginMultiplier
    ++ (Alpha.encode message.reserved16))))))))))))

def decode (bytes : List UInt8) : Option (SimpleArmSettingsUpdateRequest × List UInt8) := do
  let (clientMessageId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (action, bytes) ← Action.decode bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 11 bytes
  let (allowableEngagementPercentage, bytes) ← decodeUIntLE 4 bytes
  let (countingPeriod, bytes) ← decodeUIntLE 2 bytes
  let (marketMakerOriginMultiplier, bytes) ← decodeUIntLE 2 bytes
  let (awayMarketMakerOriginMultiplier, bytes) ← decodeUIntLE 2 bytes
  let (brokerDealerOriginMultiplier, bytes) ← decodeUIntLE 2 bytes
  let (firmOriginMultiplier, bytes) ← decodeUIntLE 2 bytes
  let (priorityCustomerOriginMultiplier, bytes) ← decodeUIntLE 2 bytes
  let (nonPriorityCustomerOriginMultiplier, bytes) ← decodeUIntLE 2 bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  pure ({ clientMessageId, mpid, action, underlyingSymbol, allowableEngagementPercentage, countingPeriod, marketMakerOriginMultiplier, awayMarketMakerOriginMultiplier, brokerDealerOriginMultiplier, firmOriginMultiplier, priorityCustomerOriginMultiplier, nonPriorityCustomerOriginMultiplier, reserved16 }, bytes)

@[simp] theorem encode_length (message : SimpleArmSettingsUpdateRequest) : (encode message).length = 54 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, Action.encode_length]

theorem encode_length_pos (message : SimpleArmSettingsUpdateRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SimpleArmSettingsUpdateRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Action.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end SimpleArmSettingsUpdateRequest

/-- Simple Arm Settings Update Response: 20 bytes -/
structure SimpleArmSettingsUpdateResponse where
  clientMessageId : BitVec 32
  mpid : Alpha 4
  underlyingSymbol : Alpha 11
  armSettingsUpdateStatus : ArmSettingsUpdateStatus
  deriving DecidableEq, Repr

namespace SimpleArmSettingsUpdateResponse

def encode (message : SimpleArmSettingsUpdateResponse) : List UInt8 :=
  encodeUIntLE 4 message.clientMessageId
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.underlyingSymbol
    ++ (ArmSettingsUpdateStatus.encode message.armSettingsUpdateStatus)))

def decode (bytes : List UInt8) : Option (SimpleArmSettingsUpdateResponse × List UInt8) := do
  let (clientMessageId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 11 bytes
  let (armSettingsUpdateStatus, bytes) ← ArmSettingsUpdateStatus.decode bytes
  pure ({ clientMessageId, mpid, underlyingSymbol, armSettingsUpdateStatus }, bytes)

@[simp] theorem encode_length (message : SimpleArmSettingsUpdateResponse) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, ArmSettingsUpdateStatus.encode_length]

theorem encode_length_pos (message : SimpleArmSettingsUpdateResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SimpleArmSettingsUpdateResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [ArmSettingsUpdateStatus.decode_encode, some_bind]
  rfl

end SimpleArmSettingsUpdateResponse

/-- Arm 2 Underlying Level Protection Settings Update Request: 28 bytes -/
structure Arm2UnderlyingLevelProtectionSettingsUpdateRequest where
  clientMessageId : BitVec 32
  mpid : Alpha 4
  action : Action
  underlyingSymbol : Alpha 11
  armThresholdCount : BitVec 32
  arm2CountingPeriod : BitVec 32
  deriving DecidableEq, Repr

namespace Arm2UnderlyingLevelProtectionSettingsUpdateRequest

def encode (message : Arm2UnderlyingLevelProtectionSettingsUpdateRequest) : List UInt8 :=
  encodeUIntLE 4 message.clientMessageId
    ++ (Alpha.encode message.mpid
    ++ (Action.encode message.action
    ++ (Alpha.encode message.underlyingSymbol
    ++ (encodeUIntLE 4 message.armThresholdCount
    ++ (encodeUIntLE 4 message.arm2CountingPeriod)))))

def decode (bytes : List UInt8) : Option (Arm2UnderlyingLevelProtectionSettingsUpdateRequest × List UInt8) := do
  let (clientMessageId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (action, bytes) ← Action.decode bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 11 bytes
  let (armThresholdCount, bytes) ← decodeUIntLE 4 bytes
  let (arm2CountingPeriod, bytes) ← decodeUIntLE 4 bytes
  pure ({ clientMessageId, mpid, action, underlyingSymbol, armThresholdCount, arm2CountingPeriod }, bytes)

@[simp] theorem encode_length (message : Arm2UnderlyingLevelProtectionSettingsUpdateRequest) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, Action.encode_length]

theorem encode_length_pos (message : Arm2UnderlyingLevelProtectionSettingsUpdateRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Arm2UnderlyingLevelProtectionSettingsUpdateRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Action.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end Arm2UnderlyingLevelProtectionSettingsUpdateRequest

/-- Arm 2 Underlying Level Protection Settings Update Response: 20 bytes -/
structure Arm2UnderlyingLevelProtectionSettingsUpdateResponse where
  clientMessageId : BitVec 32
  mpid : Alpha 4
  underlyingSymbol : Alpha 11
  armSettingsUpdateStatus : ArmSettingsUpdateStatus
  deriving DecidableEq, Repr

namespace Arm2UnderlyingLevelProtectionSettingsUpdateResponse

def encode (message : Arm2UnderlyingLevelProtectionSettingsUpdateResponse) : List UInt8 :=
  encodeUIntLE 4 message.clientMessageId
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.underlyingSymbol
    ++ (ArmSettingsUpdateStatus.encode message.armSettingsUpdateStatus)))

def decode (bytes : List UInt8) : Option (Arm2UnderlyingLevelProtectionSettingsUpdateResponse × List UInt8) := do
  let (clientMessageId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 11 bytes
  let (armSettingsUpdateStatus, bytes) ← ArmSettingsUpdateStatus.decode bytes
  pure ({ clientMessageId, mpid, underlyingSymbol, armSettingsUpdateStatus }, bytes)

@[simp] theorem encode_length (message : Arm2UnderlyingLevelProtectionSettingsUpdateResponse) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, ArmSettingsUpdateStatus.encode_length]

theorem encode_length_pos (message : Arm2UnderlyingLevelProtectionSettingsUpdateResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Arm2UnderlyingLevelProtectionSettingsUpdateResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [ArmSettingsUpdateStatus.decode_encode, some_bind]
  rfl

end Arm2UnderlyingLevelProtectionSettingsUpdateResponse

/-- Single Side Quote: 15 bytes -/
structure SingleSideQuote where
  productId : BitVec 32
  price : BitVec 32
  size : BitVec 32
  side : Side
  slapCodes : BitVec 8
  reserved1 : Alpha 1
  deriving DecidableEq, Repr

namespace SingleSideQuote

def encode (message : SingleSideQuote) : List UInt8 :=
  encodeUIntLE 4 message.productId
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 4 message.size
    ++ (Side.encode message.side
    ++ (encodeUInt 1 message.slapCodes
    ++ (Alpha.encode message.reserved1)))))

def decode (bytes : List UInt8) : Option (SingleSideQuote × List UInt8) := do
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (size, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (slapCodes, bytes) ← decodeUInt 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  pure ({ productId, price, size, side, slapCodes, reserved1 }, bytes)

@[simp] theorem encode_length (message : SingleSideQuote) : (encode message).length = 15 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Side.encode_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : SingleSideQuote) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SingleSideQuote) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SingleSideQuote

/-- Simple Bulk Quote Message -/
structure SimpleBulkQuoteMessage where
  clientMessageId : BitVec 32
  mpid : Alpha 4
  clientSendTime : BitVec 64
  reserved32 : Alpha 32
  singleSideQuote : Bounded 1 SingleSideQuote
  deriving DecidableEq, Repr

namespace SimpleBulkQuoteMessage

def encode (message : SimpleBulkQuoteMessage) : List UInt8 :=
  encodeUIntLE 4 message.clientMessageId
    ++ (Alpha.encode message.mpid
    ++ (encodeUIntLE 8 message.clientSendTime
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.singleSideQuote.val.length)
    ++ (Alpha.encode message.reserved32
    ++ (encodeMany SingleSideQuote.encode message.singleSideQuote.val)))))

def decode (bytes : List UInt8) : Option (SimpleBulkQuoteMessage × List UInt8) := do
  let (clientMessageId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (clientSendTime, bytes) ← decodeUIntLE 8 bytes
  let (quoteCount, bytes) ← decodeUInt 1 bytes
  let (reserved32, bytes) ← Alpha.decode 32 bytes
  let (singleSideQuote_, bytes) ← decodeMany SingleSideQuote.decode quoteCount.toNat bytes
  if fits_singleSideQuote : singleSideQuote_.length < 256 ^ 1 then
    pure ({ clientMessageId, mpid, clientSendTime, reserved32, singleSideQuote := ⟨singleSideQuote_, fits_singleSideQuote⟩ }, bytes)
  else none

theorem encode_length_pos (message : SimpleBulkQuoteMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SimpleBulkQuoteMessage) : (encode message).length ≤ 3874 := by
  have bound_singleSideQuote := message.singleSideQuote.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length, encodeMany_length_const SingleSideQuote.encode 15 SingleSideQuote.encode_length]
  omega

@[simp] theorem decode_encode (message : SimpleBulkQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 SingleSideQuote.encode SingleSideQuote.decode SingleSideQuote.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.singleSideQuote.length_lt]
  rfl

end SimpleBulkQuoteMessage

/-- Single Side Quote Response: 9 bytes -/
structure SingleSideQuoteResponse where
  quoteStatus : QuoteStatus
  engineSequenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace SingleSideQuoteResponse

def encode (message : SingleSideQuoteResponse) : List UInt8 :=
  QuoteStatus.encode message.quoteStatus
    ++ (encodeUIntLE 8 message.engineSequenceNumber)

def decode (bytes : List UInt8) : Option (SingleSideQuoteResponse × List UInt8) := do
  let (quoteStatus, bytes) ← QuoteStatus.decode bytes
  let (engineSequenceNumber, bytes) ← decodeUIntLE 8 bytes
  pure ({ quoteStatus, engineSequenceNumber }, bytes)

@[simp] theorem encode_length (message : SingleSideQuoteResponse) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, QuoteStatus.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : SingleSideQuoteResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SingleSideQuoteResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, QuoteStatus.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SingleSideQuoteResponse

/-- Simple Bulk Quote Response -/
structure SimpleBulkQuoteResponse where
  clientMessageId : BitVec 32
  mpid : Alpha 4
  bulkQuoteStatus : BulkQuoteStatus
  quoteCount : BitVec 8
  quoteAckTime : BitVec 64
  singleSideQuoteResponse : Bounded 1 SingleSideQuoteResponse
  deriving DecidableEq, Repr

namespace SimpleBulkQuoteResponse

def encode (message : SimpleBulkQuoteResponse) : List UInt8 :=
  encodeUIntLE 4 message.clientMessageId
    ++ (Alpha.encode message.mpid
    ++ (BulkQuoteStatus.encode message.bulkQuoteStatus
    ++ (encodeUInt 1 message.quoteCount
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.singleSideQuoteResponse.val.length)
    ++ (encodeUIntLE 8 message.quoteAckTime
    ++ (encodeMany SingleSideQuoteResponse.encode message.singleSideQuoteResponse.val))))))

def decode (bytes : List UInt8) : Option (SimpleBulkQuoteResponse × List UInt8) := do
  let (clientMessageId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (bulkQuoteStatus, bytes) ← BulkQuoteStatus.decode bytes
  let (quoteCount, bytes) ← decodeUInt 1 bytes
  let (invalidQuoteCount, bytes) ← decodeUInt 1 bytes
  let (quoteAckTime, bytes) ← decodeUIntLE 8 bytes
  let (singleSideQuoteResponse_, bytes) ← decodeMany SingleSideQuoteResponse.decode invalidQuoteCount.toNat bytes
  if fits_singleSideQuoteResponse : singleSideQuoteResponse_.length < 256 ^ 1 then
    pure ({ clientMessageId, mpid, bulkQuoteStatus, quoteCount, quoteAckTime, singleSideQuoteResponse := ⟨singleSideQuoteResponse_, fits_singleSideQuoteResponse⟩ }, bytes)
  else none

theorem encode_length_pos (message : SimpleBulkQuoteResponse) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SimpleBulkQuoteResponse) : (encode message).length ≤ 2314 := by
  have bound_singleSideQuoteResponse := message.singleSideQuoteResponse.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Alpha.encode_length, BulkQuoteStatus.encode_length, encodeUInt_length, encodeMany_length_const SingleSideQuoteResponse.encode 9 SingleSideQuoteResponse.encode_length]
  omega

@[simp] theorem decode_encode (message : SimpleBulkQuoteResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BulkQuoteStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 SingleSideQuoteResponse.encode SingleSideQuoteResponse.decode SingleSideQuoteResponse.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.singleSideQuoteResponse.length_lt]
  rfl

end SimpleBulkQuoteResponse

/-- Simple Enhanced Quote E Quote Message: 43 bytes -/
structure SimpleEnhancedQuoteEQuoteMessage where
  clientMessageId : BitVec 32
  mpid : Alpha 4
  clientSendTime : BitVec 64
  productId : BitVec 32
  eQuoteAction : EQuoteAction
  eQuoteType : EQuoteType
  eventId : BitVec 32
  targetMessageId : BitVec 32
  price : BitVec 32
  size : BitVec 32
  side : Side
  reserved4 : Alpha 4
  deriving DecidableEq, Repr

namespace SimpleEnhancedQuoteEQuoteMessage

def encode (message : SimpleEnhancedQuoteEQuoteMessage) : List UInt8 :=
  encodeUIntLE 4 message.clientMessageId
    ++ (Alpha.encode message.mpid
    ++ (encodeUIntLE 8 message.clientSendTime
    ++ (encodeUIntLE 4 message.productId
    ++ (EQuoteAction.encode message.eQuoteAction
    ++ (EQuoteType.encode message.eQuoteType
    ++ (encodeUIntLE 4 message.eventId
    ++ (encodeUIntLE 4 message.targetMessageId
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 4 message.size
    ++ (Side.encode message.side
    ++ (Alpha.encode message.reserved4)))))))))))

def decode (bytes : List UInt8) : Option (SimpleEnhancedQuoteEQuoteMessage × List UInt8) := do
  let (clientMessageId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (clientSendTime, bytes) ← decodeUIntLE 8 bytes
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (eQuoteAction, bytes) ← EQuoteAction.decode bytes
  let (eQuoteType, bytes) ← EQuoteType.decode bytes
  let (eventId, bytes) ← decodeUIntLE 4 bytes
  let (targetMessageId, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (size, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  pure ({ clientMessageId, mpid, clientSendTime, productId, eQuoteAction, eQuoteType, eventId, targetMessageId, price, size, side, reserved4 }, bytes)

@[simp] theorem encode_length (message : SimpleEnhancedQuoteEQuoteMessage) : (encode message).length = 43 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, EQuoteAction.encode_length, EQuoteType.encode_length, Side.encode_length]

theorem encode_length_pos (message : SimpleEnhancedQuoteEQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SimpleEnhancedQuoteEQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, EQuoteAction.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, EQuoteType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SimpleEnhancedQuoteEQuoteMessage

/-- Complex Enhanced Quote E Quote Message: 59 bytes -/
structure ComplexEnhancedQuoteEQuoteMessage where
  clientMessageId : BitVec 32
  mpid : Alpha 4
  clientSendTime : BitVec 64
  strategyId : BitVec 32
  eQuoteAction : EQuoteAction
  eQuoteType : EQuoteType
  complexEventId : BitVec 32
  targetMessageId : BitVec 32
  netPrice : BitVec 64
  size : BitVec 32
  side : Side
  stockSellShortIndicator : StockSellShortIndicator
  reserved15 : Alpha 15
  deriving DecidableEq, Repr

namespace ComplexEnhancedQuoteEQuoteMessage

def encode (message : ComplexEnhancedQuoteEQuoteMessage) : List UInt8 :=
  encodeUIntLE 4 message.clientMessageId
    ++ (Alpha.encode message.mpid
    ++ (encodeUIntLE 8 message.clientSendTime
    ++ (encodeUIntLE 4 message.strategyId
    ++ (EQuoteAction.encode message.eQuoteAction
    ++ (EQuoteType.encode message.eQuoteType
    ++ (encodeUIntLE 4 message.complexEventId
    ++ (encodeUIntLE 4 message.targetMessageId
    ++ (encodeUIntLE 8 message.netPrice
    ++ (encodeUIntLE 4 message.size
    ++ (Side.encode message.side
    ++ (StockSellShortIndicator.encode message.stockSellShortIndicator
    ++ (Alpha.encode message.reserved15))))))))))))

def decode (bytes : List UInt8) : Option (ComplexEnhancedQuoteEQuoteMessage × List UInt8) := do
  let (clientMessageId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (clientSendTime, bytes) ← decodeUIntLE 8 bytes
  let (strategyId, bytes) ← decodeUIntLE 4 bytes
  let (eQuoteAction, bytes) ← EQuoteAction.decode bytes
  let (eQuoteType, bytes) ← EQuoteType.decode bytes
  let (complexEventId, bytes) ← decodeUIntLE 4 bytes
  let (targetMessageId, bytes) ← decodeUIntLE 4 bytes
  let (netPrice, bytes) ← decodeUIntLE 8 bytes
  let (size, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (stockSellShortIndicator, bytes) ← StockSellShortIndicator.decode bytes
  let (reserved15, bytes) ← Alpha.decode 15 bytes
  pure ({ clientMessageId, mpid, clientSendTime, strategyId, eQuoteAction, eQuoteType, complexEventId, targetMessageId, netPrice, size, side, stockSellShortIndicator, reserved15 }, bytes)

@[simp] theorem encode_length (message : ComplexEnhancedQuoteEQuoteMessage) : (encode message).length = 59 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, EQuoteAction.encode_length, EQuoteType.encode_length, Side.encode_length, StockSellShortIndicator.encode_length]

theorem encode_length_pos (message : ComplexEnhancedQuoteEQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ComplexEnhancedQuoteEQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, EQuoteAction.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, EQuoteType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StockSellShortIndicator.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ComplexEnhancedQuoteEQuoteMessage

/-- Simple Mass Quote Cancel Request: 31 bytes -/
structure SimpleMassQuoteCancelRequest where
  clientMessageId : BitVec 32
  mpid : Alpha 4
  clientSendTime : BitVec 64
  underlyingSymbol : Alpha 11
  reserved4 : Alpha 4
  deriving DecidableEq, Repr

namespace SimpleMassQuoteCancelRequest

def encode (message : SimpleMassQuoteCancelRequest) : List UInt8 :=
  encodeUIntLE 4 message.clientMessageId
    ++ (Alpha.encode message.mpid
    ++ (encodeUIntLE 8 message.clientSendTime
    ++ (Alpha.encode message.underlyingSymbol
    ++ (Alpha.encode message.reserved4))))

def decode (bytes : List UInt8) : Option (SimpleMassQuoteCancelRequest × List UInt8) := do
  let (clientMessageId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (clientSendTime, bytes) ← decodeUIntLE 8 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 11 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  pure ({ clientMessageId, mpid, clientSendTime, underlyingSymbol, reserved4 }, bytes)

@[simp] theorem encode_length (message : SimpleMassQuoteCancelRequest) : (encode message).length = 31 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : SimpleMassQuoteCancelRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SimpleMassQuoteCancelRequest) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end SimpleMassQuoteCancelRequest

/-- Simple Mass Quote Cancel Response: 9 bytes -/
structure SimpleMassQuoteCancelResponse where
  clientMessageId : BitVec 32
  mpid : Alpha 4
  simpleMassQuoteCancelStatus : SimpleMassQuoteCancelStatus
  deriving DecidableEq, Repr

namespace SimpleMassQuoteCancelResponse

def encode (message : SimpleMassQuoteCancelResponse) : List UInt8 :=
  encodeUIntLE 4 message.clientMessageId
    ++ (Alpha.encode message.mpid
    ++ (SimpleMassQuoteCancelStatus.encode message.simpleMassQuoteCancelStatus))

def decode (bytes : List UInt8) : Option (SimpleMassQuoteCancelResponse × List UInt8) := do
  let (clientMessageId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (simpleMassQuoteCancelStatus, bytes) ← SimpleMassQuoteCancelStatus.decode bytes
  pure ({ clientMessageId, mpid, simpleMassQuoteCancelStatus }, bytes)

@[simp] theorem encode_length (message : SimpleMassQuoteCancelResponse) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, SimpleMassQuoteCancelStatus.encode_length]

theorem encode_length_pos (message : SimpleMassQuoteCancelResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SimpleMassQuoteCancelResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [SimpleMassQuoteCancelStatus.decode_encode, some_bind]
  rfl

end SimpleMassQuoteCancelResponse

/-- Mass Liquidity Cancel Request Simple And Complex: 37 bytes -/
structure MassLiquidityCancelRequestSimpleAndComplex where
  clientMessageId : BitVec 32
  mpid : Alpha 4
  clientSendTime : BitVec 64
  underlyingSymbol : Alpha 11
  simpleMassCancel : SimpleMassCancel
  complexMassCancel : ComplexMassCancel
  slapCodes : BitVec 8
  reserved7 : Alpha 7
  deriving DecidableEq, Repr

namespace MassLiquidityCancelRequestSimpleAndComplex

def encode (message : MassLiquidityCancelRequestSimpleAndComplex) : List UInt8 :=
  encodeUIntLE 4 message.clientMessageId
    ++ (Alpha.encode message.mpid
    ++ (encodeUIntLE 8 message.clientSendTime
    ++ (Alpha.encode message.underlyingSymbol
    ++ (SimpleMassCancel.encode message.simpleMassCancel
    ++ (ComplexMassCancel.encode message.complexMassCancel
    ++ (encodeUInt 1 message.slapCodes
    ++ (Alpha.encode message.reserved7)))))))

def decode (bytes : List UInt8) : Option (MassLiquidityCancelRequestSimpleAndComplex × List UInt8) := do
  let (clientMessageId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (clientSendTime, bytes) ← decodeUIntLE 8 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 11 bytes
  let (simpleMassCancel, bytes) ← SimpleMassCancel.decode bytes
  let (complexMassCancel, bytes) ← ComplexMassCancel.decode bytes
  let (slapCodes, bytes) ← decodeUInt 1 bytes
  let (reserved7, bytes) ← Alpha.decode 7 bytes
  pure ({ clientMessageId, mpid, clientSendTime, underlyingSymbol, simpleMassCancel, complexMassCancel, slapCodes, reserved7 }, bytes)

@[simp] theorem encode_length (message : MassLiquidityCancelRequestSimpleAndComplex) : (encode message).length = 37 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, SimpleMassCancel.encode_length, ComplexMassCancel.encode_length, encodeUInt_length]

theorem encode_length_pos (message : MassLiquidityCancelRequestSimpleAndComplex) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MassLiquidityCancelRequestSimpleAndComplex) (rest : List UInt8) :
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
  rw [List.append_assoc, SimpleMassCancel.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ComplexMassCancel.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MassLiquidityCancelRequestSimpleAndComplex

/-- Mass Liquidity Cancel Response: 10 bytes -/
structure MassLiquidityCancelResponse where
  clientMessageId : BitVec 32
  mpid : Alpha 4
  simpleMassLiquidityCancelStatus : SimpleMassLiquidityCancelStatus
  complexMassLiquidityCancelStatus : ComplexMassLiquidityCancelStatus
  deriving DecidableEq, Repr

namespace MassLiquidityCancelResponse

def encode (message : MassLiquidityCancelResponse) : List UInt8 :=
  encodeUIntLE 4 message.clientMessageId
    ++ (Alpha.encode message.mpid
    ++ (SimpleMassLiquidityCancelStatus.encode message.simpleMassLiquidityCancelStatus
    ++ (ComplexMassLiquidityCancelStatus.encode message.complexMassLiquidityCancelStatus)))

def decode (bytes : List UInt8) : Option (MassLiquidityCancelResponse × List UInt8) := do
  let (clientMessageId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (simpleMassLiquidityCancelStatus, bytes) ← SimpleMassLiquidityCancelStatus.decode bytes
  let (complexMassLiquidityCancelStatus, bytes) ← ComplexMassLiquidityCancelStatus.decode bytes
  pure ({ clientMessageId, mpid, simpleMassLiquidityCancelStatus, complexMassLiquidityCancelStatus }, bytes)

@[simp] theorem encode_length (message : MassLiquidityCancelResponse) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, SimpleMassLiquidityCancelStatus.encode_length, ComplexMassLiquidityCancelStatus.encode_length]

theorem encode_length_pos (message : MassLiquidityCancelResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MassLiquidityCancelResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SimpleMassLiquidityCancelStatus.decode_encode, some_bind]
  dsimp only
  rw [ComplexMassLiquidityCancelStatus.decode_encode, some_bind]
  rfl

end MassLiquidityCancelResponse

/-- Simple Quote Protection Reset Request: 19 bytes -/
structure SimpleQuoteProtectionResetRequest where
  clientMessageId : BitVec 32
  mpid : Alpha 4
  underlyingSymbol : Alpha 11
  deriving DecidableEq, Repr

namespace SimpleQuoteProtectionResetRequest

def encode (message : SimpleQuoteProtectionResetRequest) : List UInt8 :=
  encodeUIntLE 4 message.clientMessageId
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.underlyingSymbol))

def decode (bytes : List UInt8) : Option (SimpleQuoteProtectionResetRequest × List UInt8) := do
  let (clientMessageId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 11 bytes
  pure ({ clientMessageId, mpid, underlyingSymbol }, bytes)

@[simp] theorem encode_length (message : SimpleQuoteProtectionResetRequest) : (encode message).length = 19 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : SimpleQuoteProtectionResetRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SimpleQuoteProtectionResetRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SimpleQuoteProtectionResetRequest

/-- Simple Quote Protection Reset Response: 9 bytes -/
structure SimpleQuoteProtectionResetResponse where
  clientMessageId : BitVec 32
  mpid : Alpha 4
  quoteProtectionResetStatus : QuoteProtectionResetStatus
  deriving DecidableEq, Repr

namespace SimpleQuoteProtectionResetResponse

def encode (message : SimpleQuoteProtectionResetResponse) : List UInt8 :=
  encodeUIntLE 4 message.clientMessageId
    ++ (Alpha.encode message.mpid
    ++ (QuoteProtectionResetStatus.encode message.quoteProtectionResetStatus))

def decode (bytes : List UInt8) : Option (SimpleQuoteProtectionResetResponse × List UInt8) := do
  let (clientMessageId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (quoteProtectionResetStatus, bytes) ← QuoteProtectionResetStatus.decode bytes
  pure ({ clientMessageId, mpid, quoteProtectionResetStatus }, bytes)

@[simp] theorem encode_length (message : SimpleQuoteProtectionResetResponse) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, QuoteProtectionResetStatus.encode_length]

theorem encode_length_pos (message : SimpleQuoteProtectionResetResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SimpleQuoteProtectionResetResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [QuoteProtectionResetStatus.decode_encode, some_bind]
  rfl

end SimpleQuoteProtectionResetResponse

/-- Liquidity Protection Reset Request: 29 bytes -/
structure LiquidityProtectionResetRequest where
  clientMessageId : BitVec 32
  mpid : Alpha 4
  underlyingSymbol : Alpha 11
  simpleLiquidityReset : SimpleLiquidityReset
  complexLiquidityReset : ComplexLiquidityReset
  slapCodes : BitVec 8
  reserved7 : Alpha 7
  deriving DecidableEq, Repr

namespace LiquidityProtectionResetRequest

def encode (message : LiquidityProtectionResetRequest) : List UInt8 :=
  encodeUIntLE 4 message.clientMessageId
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.underlyingSymbol
    ++ (SimpleLiquidityReset.encode message.simpleLiquidityReset
    ++ (ComplexLiquidityReset.encode message.complexLiquidityReset
    ++ (encodeUInt 1 message.slapCodes
    ++ (Alpha.encode message.reserved7))))))

def decode (bytes : List UInt8) : Option (LiquidityProtectionResetRequest × List UInt8) := do
  let (clientMessageId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 11 bytes
  let (simpleLiquidityReset, bytes) ← SimpleLiquidityReset.decode bytes
  let (complexLiquidityReset, bytes) ← ComplexLiquidityReset.decode bytes
  let (slapCodes, bytes) ← decodeUInt 1 bytes
  let (reserved7, bytes) ← Alpha.decode 7 bytes
  pure ({ clientMessageId, mpid, underlyingSymbol, simpleLiquidityReset, complexLiquidityReset, slapCodes, reserved7 }, bytes)

@[simp] theorem encode_length (message : LiquidityProtectionResetRequest) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, SimpleLiquidityReset.encode_length, ComplexLiquidityReset.encode_length, encodeUInt_length]

theorem encode_length_pos (message : LiquidityProtectionResetRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LiquidityProtectionResetRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SimpleLiquidityReset.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ComplexLiquidityReset.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LiquidityProtectionResetRequest

/-- Liquidity Protection Reset Response: 10 bytes -/
structure LiquidityProtectionResetResponse where
  clientMessageId : BitVec 32
  mpid : Alpha 4
  simpleLiquidityProtectionResetStatus : SimpleLiquidityProtectionResetStatus
  complexLiquidityProtectionResetStatus : ComplexLiquidityProtectionResetStatus
  deriving DecidableEq, Repr

namespace LiquidityProtectionResetResponse

def encode (message : LiquidityProtectionResetResponse) : List UInt8 :=
  encodeUIntLE 4 message.clientMessageId
    ++ (Alpha.encode message.mpid
    ++ (SimpleLiquidityProtectionResetStatus.encode message.simpleLiquidityProtectionResetStatus
    ++ (ComplexLiquidityProtectionResetStatus.encode message.complexLiquidityProtectionResetStatus)))

def decode (bytes : List UInt8) : Option (LiquidityProtectionResetResponse × List UInt8) := do
  let (clientMessageId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (simpleLiquidityProtectionResetStatus, bytes) ← SimpleLiquidityProtectionResetStatus.decode bytes
  let (complexLiquidityProtectionResetStatus, bytes) ← ComplexLiquidityProtectionResetStatus.decode bytes
  pure ({ clientMessageId, mpid, simpleLiquidityProtectionResetStatus, complexLiquidityProtectionResetStatus }, bytes)

@[simp] theorem encode_length (message : LiquidityProtectionResetResponse) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, SimpleLiquidityProtectionResetStatus.encode_length, ComplexLiquidityProtectionResetStatus.encode_length]

theorem encode_length_pos (message : LiquidityProtectionResetResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LiquidityProtectionResetResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SimpleLiquidityProtectionResetStatus.decode_encode, some_bind]
  dsimp only
  rw [ComplexLiquidityProtectionResetStatus.decode_encode, some_bind]
  rfl

end LiquidityProtectionResetResponse

/-- Single Side Liquidity Protection Reset Request: 18 bytes -/
structure SingleSideLiquidityProtectionResetRequest where
  clientMessageId : BitVec 32
  mpid : Alpha 4
  securityIdScope : SecurityIdScope
  securityId : BitVec 32
  side : Side
  reserved4 : Alpha 4
  deriving DecidableEq, Repr

namespace SingleSideLiquidityProtectionResetRequest

def encode (message : SingleSideLiquidityProtectionResetRequest) : List UInt8 :=
  encodeUIntLE 4 message.clientMessageId
    ++ (Alpha.encode message.mpid
    ++ (SecurityIdScope.encode message.securityIdScope
    ++ (encodeUIntLE 4 message.securityId
    ++ (Side.encode message.side
    ++ (Alpha.encode message.reserved4)))))

def decode (bytes : List UInt8) : Option (SingleSideLiquidityProtectionResetRequest × List UInt8) := do
  let (clientMessageId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (securityIdScope, bytes) ← SecurityIdScope.decode bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  pure ({ clientMessageId, mpid, securityIdScope, securityId, side, reserved4 }, bytes)

@[simp] theorem encode_length (message : SingleSideLiquidityProtectionResetRequest) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, SecurityIdScope.encode_length, Side.encode_length]

theorem encode_length_pos (message : SingleSideLiquidityProtectionResetRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SingleSideLiquidityProtectionResetRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityIdScope.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SingleSideLiquidityProtectionResetRequest

/-- Single Side Liquidity Protection Reset Response: 13 bytes -/
structure SingleSideLiquidityProtectionResetResponse where
  clientMessageId : BitVec 32
  mpid : Alpha 4
  reserved4 : Alpha 4
  status : Status
  deriving DecidableEq, Repr

namespace SingleSideLiquidityProtectionResetResponse

def encode (message : SingleSideLiquidityProtectionResetResponse) : List UInt8 :=
  encodeUIntLE 4 message.clientMessageId
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.reserved4
    ++ (Status.encode message.status)))

def decode (bytes : List UInt8) : Option (SingleSideLiquidityProtectionResetResponse × List UInt8) := do
  let (clientMessageId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (status, bytes) ← Status.decode bytes
  pure ({ clientMessageId, mpid, reserved4, status }, bytes)

@[simp] theorem encode_length (message : SingleSideLiquidityProtectionResetResponse) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, Status.encode_length]

theorem encode_length_pos (message : SingleSideLiquidityProtectionResetResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SingleSideLiquidityProtectionResetResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Status.decode_encode, some_bind]
  rfl

end SingleSideLiquidityProtectionResetResponse

/-- Simple Quote Protection Trigger Notification: 24 bytes -/
structure SimpleQuoteProtectionTriggerNotification where
  notificationTime : BitVec 64
  mpid : Alpha 4
  underlyingSymbol : Alpha 11
  triggerReason : TriggerReason
  deriving DecidableEq, Repr

namespace SimpleQuoteProtectionTriggerNotification

def encode (message : SimpleQuoteProtectionTriggerNotification) : List UInt8 :=
  encodeUIntLE 8 message.notificationTime
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.underlyingSymbol
    ++ (TriggerReason.encode message.triggerReason)))

def decode (bytes : List UInt8) : Option (SimpleQuoteProtectionTriggerNotification × List UInt8) := do
  let (notificationTime, bytes) ← decodeUIntLE 8 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 11 bytes
  let (triggerReason, bytes) ← TriggerReason.decode bytes
  pure ({ notificationTime, mpid, underlyingSymbol, triggerReason }, bytes)

@[simp] theorem encode_length (message : SimpleQuoteProtectionTriggerNotification) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TriggerReason.encode_length]

theorem encode_length_pos (message : SimpleQuoteProtectionTriggerNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SimpleQuoteProtectionTriggerNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [TriggerReason.decode_encode, some_bind]
  rfl

end SimpleQuoteProtectionTriggerNotification

/-- Complex Liquidity Protection Trigger Notification: 24 bytes -/
structure ComplexLiquidityProtectionTriggerNotification where
  notificationTime : BitVec 64
  mpid : Alpha 4
  underlyingSymbol : Alpha 11
  triggerReason : TriggerReason
  deriving DecidableEq, Repr

namespace ComplexLiquidityProtectionTriggerNotification

def encode (message : ComplexLiquidityProtectionTriggerNotification) : List UInt8 :=
  encodeUIntLE 8 message.notificationTime
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.underlyingSymbol
    ++ (TriggerReason.encode message.triggerReason)))

def decode (bytes : List UInt8) : Option (ComplexLiquidityProtectionTriggerNotification × List UInt8) := do
  let (notificationTime, bytes) ← decodeUIntLE 8 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 11 bytes
  let (triggerReason, bytes) ← TriggerReason.decode bytes
  pure ({ notificationTime, mpid, underlyingSymbol, triggerReason }, bytes)

@[simp] theorem encode_length (message : ComplexLiquidityProtectionTriggerNotification) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TriggerReason.encode_length]

theorem encode_length_pos (message : ComplexLiquidityProtectionTriggerNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ComplexLiquidityProtectionTriggerNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [TriggerReason.decode_encode, some_bind]
  rfl

end ComplexLiquidityProtectionTriggerNotification

/-- Slap Protection Trigger Notification: 35 bytes -/
structure SlapProtectionTriggerNotification where
  notificationTime : BitVec 64
  mpid : Alpha 4
  underlyingSymbol : Alpha 11
  requestedSlapCodes : BitVec 8
  triggeredSlapCodes : BitVec 8
  reserved10 : Alpha 10
  deriving DecidableEq, Repr

namespace SlapProtectionTriggerNotification

def encode (message : SlapProtectionTriggerNotification) : List UInt8 :=
  encodeUIntLE 8 message.notificationTime
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.underlyingSymbol
    ++ (encodeUInt 1 message.requestedSlapCodes
    ++ (encodeUInt 1 message.triggeredSlapCodes
    ++ (Alpha.encode message.reserved10)))))

def decode (bytes : List UInt8) : Option (SlapProtectionTriggerNotification × List UInt8) := do
  let (notificationTime, bytes) ← decodeUIntLE 8 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 11 bytes
  let (requestedSlapCodes, bytes) ← decodeUInt 1 bytes
  let (triggeredSlapCodes, bytes) ← decodeUInt 1 bytes
  let (reserved10, bytes) ← Alpha.decode 10 bytes
  pure ({ notificationTime, mpid, underlyingSymbol, requestedSlapCodes, triggeredSlapCodes, reserved10 }, bytes)

@[simp] theorem encode_length (message : SlapProtectionTriggerNotification) : (encode message).length = 35 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SlapProtectionTriggerNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SlapProtectionTriggerNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SlapProtectionTriggerNotification

/-- Any Unsequenced Message, selected by Unsequenced Message Type -/
inductive UnsequencedMessage where
  | simpleArmSettingsUpdateRequest (message : SimpleArmSettingsUpdateRequest) -- "RS" 0x5253
  | simpleArmSettingsUpdateResponse (message : SimpleArmSettingsUpdateResponse) -- "AA" 0x4141
  | arm2UnderlyingLevelProtectionSettingsUpdateRequest (message : Arm2UnderlyingLevelProtectionSettingsUpdateRequest) -- "2S" 0x3253
  | arm2UnderlyingLevelProtectionSettingsUpdateResponse (message : Arm2UnderlyingLevelProtectionSettingsUpdateResponse) -- "2R" 0x3252
  | simpleBulkQuoteMessage (message : SimpleBulkQuoteMessage) -- "qq" 0x7171
  | simpleBulkQuoteResponse (message : SimpleBulkQuoteResponse) -- "QR" 0x5152
  | simpleEnhancedQuoteEQuoteMessage (message : SimpleEnhancedQuoteEQuoteMessage) -- "eq" 0x6571
  | complexEnhancedQuoteEQuoteMessage (message : ComplexEnhancedQuoteEQuoteMessage) -- "ce" 0x6365
  | simpleMassQuoteCancelRequest (message : SimpleMassQuoteCancelRequest) -- "xq" 0x7871
  | simpleMassQuoteCancelResponse (message : SimpleMassQuoteCancelResponse) -- "XR" 0x5852
  | massLiquidityCancelRequestSimpleAndComplex (message : MassLiquidityCancelRequestSimpleAndComplex) -- "xk" 0x786B
  | massLiquidityCancelResponse (message : MassLiquidityCancelResponse) -- "XP" 0x5850
  | simpleQuoteProtectionResetRequest (message : SimpleQuoteProtectionResetRequest) -- "PX" 0x5058
  | simpleQuoteProtectionResetResponse (message : SimpleQuoteProtectionResetResponse) -- "PR" 0x5052
  | liquidityProtectionResetRequest (message : LiquidityProtectionResetRequest) -- "PC" 0x5043
  | liquidityProtectionResetResponse (message : LiquidityProtectionResetResponse) -- "PK" 0x504B
  | singleSideLiquidityProtectionResetRequest (message : SingleSideLiquidityProtectionResetRequest) -- "SS" 0x5353
  | singleSideLiquidityProtectionResetResponse (message : SingleSideLiquidityProtectionResetResponse) -- "SR" 0x5352
  | simpleQuoteProtectionTriggerNotification (message : SimpleQuoteProtectionTriggerNotification) -- "QP" 0x5150
  | complexLiquidityProtectionTriggerNotification (message : ComplexLiquidityProtectionTriggerNotification) -- "QC" 0x5143
  | cancelNotification (message : CancelNotification) -- "XN" 0x584E
  | slapProtectionTriggerNotification (message : SlapProtectionTriggerNotification) -- "SL" 0x534C
  deriving DecidableEq, Repr

namespace UnsequencedMessage

/-- The Unsequenced Message Type each message is sent under -/
def tag : UnsequencedMessage → BitVec 16
  | .simpleArmSettingsUpdateRequest _ => 21075
  | .simpleArmSettingsUpdateResponse _ => 16705
  | .arm2UnderlyingLevelProtectionSettingsUpdateRequest _ => 12883
  | .arm2UnderlyingLevelProtectionSettingsUpdateResponse _ => 12882
  | .simpleBulkQuoteMessage _ => 29041
  | .simpleBulkQuoteResponse _ => 20818
  | .simpleEnhancedQuoteEQuoteMessage _ => 25969
  | .complexEnhancedQuoteEQuoteMessage _ => 25445
  | .simpleMassQuoteCancelRequest _ => 30833
  | .simpleMassQuoteCancelResponse _ => 22610
  | .massLiquidityCancelRequestSimpleAndComplex _ => 30827
  | .massLiquidityCancelResponse _ => 22608
  | .simpleQuoteProtectionResetRequest _ => 20568
  | .simpleQuoteProtectionResetResponse _ => 20562
  | .liquidityProtectionResetRequest _ => 20547
  | .liquidityProtectionResetResponse _ => 20555
  | .singleSideLiquidityProtectionResetRequest _ => 21331
  | .singleSideLiquidityProtectionResetResponse _ => 21330
  | .simpleQuoteProtectionTriggerNotification _ => 20816
  | .complexLiquidityProtectionTriggerNotification _ => 20803
  | .cancelNotification _ => 22606
  | .slapProtectionTriggerNotification _ => 21324

def encode : UnsequencedMessage → List UInt8
  | .simpleArmSettingsUpdateRequest message => SimpleArmSettingsUpdateRequest.encode message
  | .simpleArmSettingsUpdateResponse message => SimpleArmSettingsUpdateResponse.encode message
  | .arm2UnderlyingLevelProtectionSettingsUpdateRequest message => Arm2UnderlyingLevelProtectionSettingsUpdateRequest.encode message
  | .arm2UnderlyingLevelProtectionSettingsUpdateResponse message => Arm2UnderlyingLevelProtectionSettingsUpdateResponse.encode message
  | .simpleBulkQuoteMessage message => SimpleBulkQuoteMessage.encode message
  | .simpleBulkQuoteResponse message => SimpleBulkQuoteResponse.encode message
  | .simpleEnhancedQuoteEQuoteMessage message => SimpleEnhancedQuoteEQuoteMessage.encode message
  | .complexEnhancedQuoteEQuoteMessage message => ComplexEnhancedQuoteEQuoteMessage.encode message
  | .simpleMassQuoteCancelRequest message => SimpleMassQuoteCancelRequest.encode message
  | .simpleMassQuoteCancelResponse message => SimpleMassQuoteCancelResponse.encode message
  | .massLiquidityCancelRequestSimpleAndComplex message => MassLiquidityCancelRequestSimpleAndComplex.encode message
  | .massLiquidityCancelResponse message => MassLiquidityCancelResponse.encode message
  | .simpleQuoteProtectionResetRequest message => SimpleQuoteProtectionResetRequest.encode message
  | .simpleQuoteProtectionResetResponse message => SimpleQuoteProtectionResetResponse.encode message
  | .liquidityProtectionResetRequest message => LiquidityProtectionResetRequest.encode message
  | .liquidityProtectionResetResponse message => LiquidityProtectionResetResponse.encode message
  | .singleSideLiquidityProtectionResetRequest message => SingleSideLiquidityProtectionResetRequest.encode message
  | .singleSideLiquidityProtectionResetResponse message => SingleSideLiquidityProtectionResetResponse.encode message
  | .simpleQuoteProtectionTriggerNotification message => SimpleQuoteProtectionTriggerNotification.encode message
  | .complexLiquidityProtectionTriggerNotification message => ComplexLiquidityProtectionTriggerNotification.encode message
  | .cancelNotification message => CancelNotification.encode message
  | .slapProtectionTriggerNotification message => SlapProtectionTriggerNotification.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : UnsequencedMessage) : (encode message).length ≤ 3874 := by
  cases message with
  | simpleArmSettingsUpdateRequest inner =>
    simp only [encode, SimpleArmSettingsUpdateRequest.encode_length]
    omega
  | simpleArmSettingsUpdateResponse inner =>
    simp only [encode, SimpleArmSettingsUpdateResponse.encode_length]
    omega
  | arm2UnderlyingLevelProtectionSettingsUpdateRequest inner =>
    simp only [encode, Arm2UnderlyingLevelProtectionSettingsUpdateRequest.encode_length]
    omega
  | arm2UnderlyingLevelProtectionSettingsUpdateResponse inner =>
    simp only [encode, Arm2UnderlyingLevelProtectionSettingsUpdateResponse.encode_length]
    omega
  | simpleBulkQuoteMessage inner =>
    have bound_inner := SimpleBulkQuoteMessage.encode_length_le inner
    simp only [encode]
    omega
  | simpleBulkQuoteResponse inner =>
    have bound_inner := SimpleBulkQuoteResponse.encode_length_le inner
    simp only [encode]
    omega
  | simpleEnhancedQuoteEQuoteMessage inner =>
    simp only [encode, SimpleEnhancedQuoteEQuoteMessage.encode_length]
    omega
  | complexEnhancedQuoteEQuoteMessage inner =>
    simp only [encode, ComplexEnhancedQuoteEQuoteMessage.encode_length]
    omega
  | simpleMassQuoteCancelRequest inner =>
    simp only [encode, SimpleMassQuoteCancelRequest.encode_length]
    omega
  | simpleMassQuoteCancelResponse inner =>
    simp only [encode, SimpleMassQuoteCancelResponse.encode_length]
    omega
  | massLiquidityCancelRequestSimpleAndComplex inner =>
    simp only [encode, MassLiquidityCancelRequestSimpleAndComplex.encode_length]
    omega
  | massLiquidityCancelResponse inner =>
    simp only [encode, MassLiquidityCancelResponse.encode_length]
    omega
  | simpleQuoteProtectionResetRequest inner =>
    simp only [encode, SimpleQuoteProtectionResetRequest.encode_length]
    omega
  | simpleQuoteProtectionResetResponse inner =>
    simp only [encode, SimpleQuoteProtectionResetResponse.encode_length]
    omega
  | liquidityProtectionResetRequest inner =>
    simp only [encode, LiquidityProtectionResetRequest.encode_length]
    omega
  | liquidityProtectionResetResponse inner =>
    simp only [encode, LiquidityProtectionResetResponse.encode_length]
    omega
  | singleSideLiquidityProtectionResetRequest inner =>
    simp only [encode, SingleSideLiquidityProtectionResetRequest.encode_length]
    omega
  | singleSideLiquidityProtectionResetResponse inner =>
    simp only [encode, SingleSideLiquidityProtectionResetResponse.encode_length]
    omega
  | simpleQuoteProtectionTriggerNotification inner =>
    simp only [encode, SimpleQuoteProtectionTriggerNotification.encode_length]
    omega
  | complexLiquidityProtectionTriggerNotification inner =>
    simp only [encode, ComplexLiquidityProtectionTriggerNotification.encode_length]
    omega
  | cancelNotification inner =>
    simp only [encode, CancelNotification.encode_length]
    omega
  | slapProtectionTriggerNotification inner =>
    simp only [encode, SlapProtectionTriggerNotification.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (UnsequencedMessage × List UInt8) :=
  if tag = 21075 then (SimpleArmSettingsUpdateRequest.decode bytes).map fun (message, rest) => (.simpleArmSettingsUpdateRequest message, rest)
  else if tag = 16705 then (SimpleArmSettingsUpdateResponse.decode bytes).map fun (message, rest) => (.simpleArmSettingsUpdateResponse message, rest)
  else if tag = 12883 then (Arm2UnderlyingLevelProtectionSettingsUpdateRequest.decode bytes).map fun (message, rest) => (.arm2UnderlyingLevelProtectionSettingsUpdateRequest message, rest)
  else if tag = 12882 then (Arm2UnderlyingLevelProtectionSettingsUpdateResponse.decode bytes).map fun (message, rest) => (.arm2UnderlyingLevelProtectionSettingsUpdateResponse message, rest)
  else if tag = 29041 then (SimpleBulkQuoteMessage.decode bytes).map fun (message, rest) => (.simpleBulkQuoteMessage message, rest)
  else if tag = 20818 then (SimpleBulkQuoteResponse.decode bytes).map fun (message, rest) => (.simpleBulkQuoteResponse message, rest)
  else if tag = 25969 then (SimpleEnhancedQuoteEQuoteMessage.decode bytes).map fun (message, rest) => (.simpleEnhancedQuoteEQuoteMessage message, rest)
  else if tag = 25445 then (ComplexEnhancedQuoteEQuoteMessage.decode bytes).map fun (message, rest) => (.complexEnhancedQuoteEQuoteMessage message, rest)
  else if tag = 30833 then (SimpleMassQuoteCancelRequest.decode bytes).map fun (message, rest) => (.simpleMassQuoteCancelRequest message, rest)
  else if tag = 22610 then (SimpleMassQuoteCancelResponse.decode bytes).map fun (message, rest) => (.simpleMassQuoteCancelResponse message, rest)
  else if tag = 30827 then (MassLiquidityCancelRequestSimpleAndComplex.decode bytes).map fun (message, rest) => (.massLiquidityCancelRequestSimpleAndComplex message, rest)
  else if tag = 22608 then (MassLiquidityCancelResponse.decode bytes).map fun (message, rest) => (.massLiquidityCancelResponse message, rest)
  else if tag = 20568 then (SimpleQuoteProtectionResetRequest.decode bytes).map fun (message, rest) => (.simpleQuoteProtectionResetRequest message, rest)
  else if tag = 20562 then (SimpleQuoteProtectionResetResponse.decode bytes).map fun (message, rest) => (.simpleQuoteProtectionResetResponse message, rest)
  else if tag = 20547 then (LiquidityProtectionResetRequest.decode bytes).map fun (message, rest) => (.liquidityProtectionResetRequest message, rest)
  else if tag = 20555 then (LiquidityProtectionResetResponse.decode bytes).map fun (message, rest) => (.liquidityProtectionResetResponse message, rest)
  else if tag = 21331 then (SingleSideLiquidityProtectionResetRequest.decode bytes).map fun (message, rest) => (.singleSideLiquidityProtectionResetRequest message, rest)
  else if tag = 21330 then (SingleSideLiquidityProtectionResetResponse.decode bytes).map fun (message, rest) => (.singleSideLiquidityProtectionResetResponse message, rest)
  else if tag = 20816 then (SimpleQuoteProtectionTriggerNotification.decode bytes).map fun (message, rest) => (.simpleQuoteProtectionTriggerNotification message, rest)
  else if tag = 20803 then (ComplexLiquidityProtectionTriggerNotification.decode bytes).map fun (message, rest) => (.complexLiquidityProtectionTriggerNotification message, rest)
  else if tag = 22606 then (CancelNotification.decode bytes).map fun (message, rest) => (.cancelNotification message, rest)
  else if tag = 21324 then (SlapProtectionTriggerNotification.decode bytes).map fun (message, rest) => (.slapProtectionTriggerNotification message, rest)
  else none

@[simp] theorem decode_encode (message : UnsequencedMessage) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end UnsequencedMessage

/-- Unsequenced Data Packet -/
structure UnsequencedDataPacket where
  unsequencedMessage : UnsequencedMessage
  deriving DecidableEq, Repr

namespace UnsequencedDataPacket

def encode (message : UnsequencedDataPacket) : List UInt8 :=
  encodeUInt 2 (UnsequencedMessage.tag message.unsequencedMessage)
    ++ (UnsequencedMessage.encode message.unsequencedMessage)

def decode (bytes : List UInt8) : Option (UnsequencedDataPacket × List UInt8) := do
  let (unsequencedMessageType, bytes) ← decodeUInt 2 bytes
  let (unsequencedMessage, bytes) ← UnsequencedMessage.decode unsequencedMessageType bytes
  pure ({ unsequencedMessage }, bytes)

theorem encode_length_pos (message : UnsequencedDataPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : UnsequencedDataPacket) : (encode message).length ≤ 3876 := by
  unfold encode
  cases message.unsequencedMessage with
  | simpleArmSettingsUpdateRequest inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, SimpleArmSettingsUpdateRequest.encode_length]
    omega
  | simpleArmSettingsUpdateResponse inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, SimpleArmSettingsUpdateResponse.encode_length]
    omega
  | arm2UnderlyingLevelProtectionSettingsUpdateRequest inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, Arm2UnderlyingLevelProtectionSettingsUpdateRequest.encode_length]
    omega
  | arm2UnderlyingLevelProtectionSettingsUpdateResponse inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, Arm2UnderlyingLevelProtectionSettingsUpdateResponse.encode_length]
    omega
  | simpleBulkQuoteMessage inner =>
    have bound_inner := SimpleBulkQuoteMessage.encode_length_le inner
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length]
    omega
  | simpleBulkQuoteResponse inner =>
    have bound_inner := SimpleBulkQuoteResponse.encode_length_le inner
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length]
    omega
  | simpleEnhancedQuoteEQuoteMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, SimpleEnhancedQuoteEQuoteMessage.encode_length]
    omega
  | complexEnhancedQuoteEQuoteMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, ComplexEnhancedQuoteEQuoteMessage.encode_length]
    omega
  | simpleMassQuoteCancelRequest inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, SimpleMassQuoteCancelRequest.encode_length]
    omega
  | simpleMassQuoteCancelResponse inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, SimpleMassQuoteCancelResponse.encode_length]
    omega
  | massLiquidityCancelRequestSimpleAndComplex inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, MassLiquidityCancelRequestSimpleAndComplex.encode_length]
    omega
  | massLiquidityCancelResponse inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, MassLiquidityCancelResponse.encode_length]
    omega
  | simpleQuoteProtectionResetRequest inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, SimpleQuoteProtectionResetRequest.encode_length]
    omega
  | simpleQuoteProtectionResetResponse inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, SimpleQuoteProtectionResetResponse.encode_length]
    omega
  | liquidityProtectionResetRequest inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, LiquidityProtectionResetRequest.encode_length]
    omega
  | liquidityProtectionResetResponse inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, LiquidityProtectionResetResponse.encode_length]
    omega
  | singleSideLiquidityProtectionResetRequest inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, SingleSideLiquidityProtectionResetRequest.encode_length]
    omega
  | singleSideLiquidityProtectionResetResponse inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, SingleSideLiquidityProtectionResetResponse.encode_length]
    omega
  | simpleQuoteProtectionTriggerNotification inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, SimpleQuoteProtectionTriggerNotification.encode_length]
    omega
  | complexLiquidityProtectionTriggerNotification inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, ComplexLiquidityProtectionTriggerNotification.encode_length]
    omega
  | cancelNotification inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, CancelNotification.encode_length]
    omega
  | slapProtectionTriggerNotification inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, SlapProtectionTriggerNotification.encode_length]
    omega

@[simp] theorem decode_encode (message : UnsequencedDataPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [UnsequencedMessage.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : UnsequencedDataPacket) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end UnsequencedDataPacket

/-- Login Request: 35 bytes -/
structure LoginRequest where
  sesmVersion : Alpha 5
  username : Alpha 5
  computerId : Alpha 8
  applicationProtocol : Alpha 8
  requestedSession : BitVec 8
  requestedSequenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace LoginRequest

def encode (message : LoginRequest) : List UInt8 :=
  Alpha.encode message.sesmVersion
    ++ (Alpha.encode message.username
    ++ (Alpha.encode message.computerId
    ++ (Alpha.encode message.applicationProtocol
    ++ (encodeUInt 1 message.requestedSession
    ++ (encodeUIntLE 8 message.requestedSequenceNumber)))))

def decode (bytes : List UInt8) : Option (LoginRequest × List UInt8) := do
  let (sesmVersion, bytes) ← Alpha.decode 5 bytes
  let (username, bytes) ← Alpha.decode 5 bytes
  let (computerId, bytes) ← Alpha.decode 8 bytes
  let (applicationProtocol, bytes) ← Alpha.decode 8 bytes
  let (requestedSession, bytes) ← decodeUInt 1 bytes
  let (requestedSequenceNumber, bytes) ← decodeUIntLE 8 bytes
  pure ({ sesmVersion, username, computerId, applicationProtocol, requestedSession, requestedSequenceNumber }, bytes)

@[simp] theorem encode_length (message : LoginRequest) : (encode message).length = 35 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, encodeUIntLE_length]

theorem encode_length_pos (message : LoginRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LoginRequest) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end LoginRequest

/-- Login Response: 10 bytes -/
structure LoginResponse where
  loginStatus : LoginStatus
  sessionId : BitVec 8
  highestSequenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace LoginResponse

def encode (message : LoginResponse) : List UInt8 :=
  LoginStatus.encode message.loginStatus
    ++ (encodeUInt 1 message.sessionId
    ++ (encodeUIntLE 8 message.highestSequenceNumber))

def decode (bytes : List UInt8) : Option (LoginResponse × List UInt8) := do
  let (loginStatus, bytes) ← LoginStatus.decode bytes
  let (sessionId, bytes) ← decodeUInt 1 bytes
  let (highestSequenceNumber, bytes) ← decodeUIntLE 8 bytes
  pure ({ loginStatus, sessionId, highestSequenceNumber }, bytes)

@[simp] theorem encode_length (message : LoginResponse) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, LoginStatus.encode_length, encodeUInt_length, encodeUIntLE_length]

theorem encode_length_pos (message : LoginResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LoginStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LoginResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end LoginResponse

/-- Synchronization Complete: 0 bytes -/
structure SynchronizationComplete where
  deriving DecidableEq, Repr

namespace SynchronizationComplete

def encode (_ : SynchronizationComplete) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (SynchronizationComplete × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : SynchronizationComplete) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : SynchronizationComplete) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SynchronizationComplete) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SynchronizationComplete

/-- Retransmission Request: 16 bytes -/
structure RetransmissionRequest where
  startSequenceNumber : BitVec 64
  endSequenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace RetransmissionRequest

def encode (message : RetransmissionRequest) : List UInt8 :=
  encodeUIntLE 8 message.startSequenceNumber
    ++ (encodeUIntLE 8 message.endSequenceNumber)

def decode (bytes : List UInt8) : Option (RetransmissionRequest × List UInt8) := do
  let (startSequenceNumber, bytes) ← decodeUIntLE 8 bytes
  let (endSequenceNumber, bytes) ← decodeUIntLE 8 bytes
  pure ({ startSequenceNumber, endSequenceNumber }, bytes)

@[simp] theorem encode_length (message : RetransmissionRequest) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : RetransmissionRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RetransmissionRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : RetransmissionRequest) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end RetransmissionRequest

/-- Logout Request -/
structure LogoutRequest where
  logoutReason : LogoutReason
  logoutText : Capped 61658
  deriving DecidableEq, Repr

namespace LogoutRequest

def encode (message : LogoutRequest) : List UInt8 :=
  LogoutReason.encode message.logoutReason
    ++ (message.logoutText.val)

def decode (bytes : List UInt8) : Option LogoutRequest := do
  let (logoutReason, bytes) ← LogoutReason.decode bytes
  let logoutText_ := bytes
  if fits_logoutText : logoutText_.length ≤ 61658 then
    pure { logoutReason, logoutText := ⟨logoutText_, fits_logoutText⟩ }
  else none

theorem encode_length_pos (message : LogoutRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [LogoutReason.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : LogoutRequest) : (encode message).length ≤ 61659 := by
  have bound_logoutText := message.logoutText.length_le
  unfold encode
  simp only [List.length_append, LogoutReason.encode_length]
  omega

theorem decode_encode (message : LogoutRequest) : decode (encode message) = some message := by
  unfold decode encode
  rw [LogoutReason.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.logoutText.length_le]
  rfl

end LogoutRequest

/-- Goodbye Packet -/
structure GoodbyePacket where
  goodbyeReason : GoodbyeReason
  logoutText : Capped 61658
  deriving DecidableEq, Repr

namespace GoodbyePacket

def encode (message : GoodbyePacket) : List UInt8 :=
  GoodbyeReason.encode message.goodbyeReason
    ++ (message.logoutText.val)

def decode (bytes : List UInt8) : Option GoodbyePacket := do
  let (goodbyeReason, bytes) ← GoodbyeReason.decode bytes
  let logoutText_ := bytes
  if fits_logoutText : logoutText_.length ≤ 61658 then
    pure { goodbyeReason, logoutText := ⟨logoutText_, fits_logoutText⟩ }
  else none

theorem encode_length_pos (message : GoodbyePacket) : (encode message).length > 0 := by
  unfold encode
  simp only [GoodbyeReason.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : GoodbyePacket) : (encode message).length ≤ 61659 := by
  have bound_logoutText := message.logoutText.length_le
  unfold encode
  simp only [List.length_append, GoodbyeReason.encode_length]
  omega

theorem decode_encode (message : GoodbyePacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [GoodbyeReason.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.logoutText.length_le]
  rfl

end GoodbyePacket

/-- End Of Session: 0 bytes -/
structure EndOfSession where
  deriving DecidableEq, Repr

namespace EndOfSession

def encode (_ : EndOfSession) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (EndOfSession × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : EndOfSession) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : EndOfSession) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : EndOfSession) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end EndOfSession

/-- Server Heartbeat: 0 bytes -/
structure ServerHeartbeat where
  deriving DecidableEq, Repr

namespace ServerHeartbeat

def encode (_ : ServerHeartbeat) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (ServerHeartbeat × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : ServerHeartbeat) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : ServerHeartbeat) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ServerHeartbeat) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ServerHeartbeat

/-- Client Heartbeat: 0 bytes -/
structure ClientHeartbeat where
  deriving DecidableEq, Repr

namespace ClientHeartbeat

def encode (_ : ClientHeartbeat) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (ClientHeartbeat × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : ClientHeartbeat) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : ClientHeartbeat) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ClientHeartbeat) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ClientHeartbeat

/-- Test Packet -/
structure TestPacket where
  testText : Capped 61658
  deriving DecidableEq, Repr

namespace TestPacket

def encode (message : TestPacket) : List UInt8 :=
  message.testText.val

def decode (bytes : List UInt8) : Option TestPacket := do
  let testText_ := bytes
  if fits_testText : testText_.length ≤ 61658 then
    pure { testText := ⟨testText_, fits_testText⟩ }
  else none

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TestPacket) : (encode message).length ≤ 61658 := by
  have bound_testText := message.testText.length_le
  unfold encode
  omega

theorem decode_encode (message : TestPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [dite_eq_left message.testText.length_le]
  rfl

end TestPacket

/-- Any Sesm Payload, selected by Sesm Packet Type -/
inductive SesmPayload where
  | sequencedDataPacket (message : SequencedDataPacket) -- "S" 0x53
  | unsequencedDataPacket (message : UnsequencedDataPacket) -- "U" 0x55
  | loginRequest (message : LoginRequest) -- "L" 0x4C
  | loginResponse (message : LoginResponse) -- "R" 0x52
  | synchronizationComplete (message : SynchronizationComplete) -- "C" 0x43
  | retransmissionRequest (message : RetransmissionRequest) -- "A" 0x41
  | logoutRequest (message : LogoutRequest) -- "X" 0x58
  | goodbyePacket (message : GoodbyePacket) -- "G" 0x47
  | endOfSession (message : EndOfSession) -- "E" 0x45
  | serverHeartbeat (message : ServerHeartbeat) -- "0" 0x30
  | clientHeartbeat (message : ClientHeartbeat) -- "1" 0x31
  | testPacket (message : TestPacket) -- "T" 0x54
  deriving DecidableEq, Repr

namespace SesmPayload

/-- The Sesm Packet Type each message is sent under -/
def tag : SesmPayload → BitVec 8
  | .sequencedDataPacket _ => 83
  | .unsequencedDataPacket _ => 85
  | .loginRequest _ => 76
  | .loginResponse _ => 82
  | .synchronizationComplete _ => 67
  | .retransmissionRequest _ => 65
  | .logoutRequest _ => 88
  | .goodbyePacket _ => 71
  | .endOfSession _ => 69
  | .serverHeartbeat _ => 48
  | .clientHeartbeat _ => 49
  | .testPacket _ => 84

def encode : SesmPayload → List UInt8
  | .sequencedDataPacket message => SequencedDataPacket.encode message
  | .unsequencedDataPacket message => UnsequencedDataPacket.encode message
  | .loginRequest message => LoginRequest.encode message
  | .loginResponse message => LoginResponse.encode message
  | .synchronizationComplete message => SynchronizationComplete.encode message
  | .retransmissionRequest message => RetransmissionRequest.encode message
  | .logoutRequest message => LogoutRequest.encode message
  | .goodbyePacket message => GoodbyePacket.encode message
  | .endOfSession message => EndOfSession.encode message
  | .serverHeartbeat message => ServerHeartbeat.encode message
  | .clientHeartbeat message => ClientHeartbeat.encode message
  | .testPacket message => TestPacket.encode message

/-- Does the message end the session? Nothing in its packet may follow it -/
def endsSession : SesmPayload → Bool
  | .endOfSession _ => true
  | _ => false

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : SesmPayload) : (encode message).length ≤ 61659 := by
  cases message with
  | sequencedDataPacket inner =>
    have bound_inner := SequencedDataPacket.encode_length_le inner
    simp only [encode]
    omega
  | unsequencedDataPacket inner =>
    have bound_inner := UnsequencedDataPacket.encode_length_le inner
    simp only [encode]
    omega
  | loginRequest inner =>
    simp only [encode, LoginRequest.encode_length]
    omega
  | loginResponse inner =>
    simp only [encode, LoginResponse.encode_length]
    omega
  | synchronizationComplete inner =>
    simp only [encode, SynchronizationComplete.encode_length]
    omega
  | retransmissionRequest inner =>
    simp only [encode, RetransmissionRequest.encode_length]
    omega
  | logoutRequest inner =>
    have bound_inner := LogoutRequest.encode_length_le inner
    simp only [encode]
    omega
  | goodbyePacket inner =>
    have bound_inner := GoodbyePacket.encode_length_le inner
    simp only [encode]
    omega
  | endOfSession inner =>
    simp only [encode, EndOfSession.encode_length]
    omega
  | serverHeartbeat inner =>
    simp only [encode, ServerHeartbeat.encode_length]
    omega
  | clientHeartbeat inner =>
    simp only [encode, ClientHeartbeat.encode_length]
    omega
  | testPacket inner =>
    have bound_inner := TestPacket.encode_length_le inner
    simp only [encode]
    omega

/-- Decoded from the whole of the frame: a message that reads to its end takes it all, any other must leave nothing -/
def decode (tag : BitVec 8) (bytes : List UInt8) : Option SesmPayload :=
  if tag = 83 then (SequencedDataPacket.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.sequencedDataPacket message) else none
  else if tag = 85 then (UnsequencedDataPacket.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.unsequencedDataPacket message) else none
  else if tag = 76 then (LoginRequest.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.loginRequest message) else none
  else if tag = 82 then (LoginResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.loginResponse message) else none
  else if tag = 67 then (SynchronizationComplete.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.synchronizationComplete message) else none
  else if tag = 65 then (RetransmissionRequest.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.retransmissionRequest message) else none
  else if tag = 88 then (LogoutRequest.decode bytes).map fun message => .logoutRequest message
  else if tag = 71 then (GoodbyePacket.decode bytes).map fun message => .goodbyePacket message
  else if tag = 69 then (EndOfSession.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.endOfSession message) else none
  else if tag = 48 then (ServerHeartbeat.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.serverHeartbeat message) else none
  else if tag = 49 then (ClientHeartbeat.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.clientHeartbeat message) else none
  else if tag = 84 then (TestPacket.decode bytes).map fun message => .testPacket message
  else none

theorem decode_encode (message : SesmPayload) :
    decode (tag message) (encode message) = some message := by
  cases message with
  | sequencedDataPacket message => simp [decode, encode, tag, SequencedDataPacket.decode_encode_nil]
  | unsequencedDataPacket message => simp [decode, encode, tag, UnsequencedDataPacket.decode_encode_nil]
  | loginRequest message => simp [decode, encode, tag, LoginRequest.decode_encode_nil]
  | loginResponse message => simp [decode, encode, tag, LoginResponse.decode_encode_nil]
  | synchronizationComplete message => simp [decode, encode, tag, SynchronizationComplete.decode_encode_nil]
  | retransmissionRequest message => simp [decode, encode, tag, RetransmissionRequest.decode_encode_nil]
  | logoutRequest message => simp [decode, encode, tag, LogoutRequest.decode_encode]
  | goodbyePacket message => simp [decode, encode, tag, GoodbyePacket.decode_encode]
  | endOfSession message => simp [decode, encode, tag, EndOfSession.decode_encode_nil]
  | serverHeartbeat message => simp [decode, encode, tag, ServerHeartbeat.decode_encode_nil]
  | clientHeartbeat message => simp [decode, encode, tag, ClientHeartbeat.decode_encode_nil]
  | testPacket message => simp [decode, encode, tag, TestPacket.decode_encode]

end SesmPayload

/-- Sesm Tcp Packet -/
structure SesmTcpPacket where
  sesmPayload : SesmPayload
  deriving DecidableEq, Repr

namespace SesmTcpPacket

def encodeBody (message : SesmTcpPacket) : List UInt8 :=
  encodeUInt 1 (SesmPayload.tag message.sesmPayload)
    ++ (SesmPayload.encode message.sesmPayload)

def decodeBody (bytes : List UInt8) : Option SesmTcpPacket := do
  let (sesmPacketType, bytes) ← decodeUInt 1 bytes
  let sesmPayload ← SesmPayload.decode sesmPacketType bytes
  pure { sesmPayload }

theorem decodeBody_encodeBody (message : SesmTcpPacket) : decodeBody (encodeBody message) = some message := by
  unfold decodeBody encodeBody
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [SesmPayload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : SesmTcpPacket) : (encodeBody message).length + 0 < 256 ^ 2 := by
  unfold encodeBody
  cases message.sesmPayload with
  | sequencedDataPacket inner =>
    have bound_inner := SequencedDataPacket.encode_length_le inner
    simp only [SesmPayload.encode, List.length_append, encodeUInt_length]
    omega
  | unsequencedDataPacket inner =>
    have bound_inner := UnsequencedDataPacket.encode_length_le inner
    simp only [SesmPayload.encode, List.length_append, encodeUInt_length]
    omega
  | loginRequest inner =>
    simp only [SesmPayload.encode, List.length_append, encodeUInt_length, LoginRequest.encode_length]
    omega
  | loginResponse inner =>
    simp only [SesmPayload.encode, List.length_append, encodeUInt_length, LoginResponse.encode_length]
    omega
  | synchronizationComplete inner =>
    simp only [SesmPayload.encode, List.length_append, encodeUInt_length, SynchronizationComplete.encode_length]
    omega
  | retransmissionRequest inner =>
    simp only [SesmPayload.encode, List.length_append, encodeUInt_length, RetransmissionRequest.encode_length]
    omega
  | logoutRequest inner =>
    have bound_inner := LogoutRequest.encode_length_le inner
    simp only [SesmPayload.encode, List.length_append, encodeUInt_length]
    omega
  | goodbyePacket inner =>
    have bound_inner := GoodbyePacket.encode_length_le inner
    simp only [SesmPayload.encode, List.length_append, encodeUInt_length]
    omega
  | endOfSession inner =>
    simp only [SesmPayload.encode, List.length_append, encodeUInt_length, EndOfSession.encode_length]
    omega
  | serverHeartbeat inner =>
    simp only [SesmPayload.encode, List.length_append, encodeUInt_length, ServerHeartbeat.encode_length]
    omega
  | clientHeartbeat inner =>
    simp only [SesmPayload.encode, List.length_append, encodeUInt_length, ClientHeartbeat.encode_length]
    omega
  | testPacket inner =>
    have bound_inner := TestPacket.encode_length_le inner
    simp only [SesmPayload.encode, List.length_append, encodeUInt_length]
    omega

/-- Size rule: Sesm Packet Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : SesmTcpPacket → List UInt8 :=
  encodeFramedLE 2 0 encodeBody

def decode : List UInt8 → Option (SesmTcpPacket × List UInt8) :=
  decodeFramedAllLE 2 0 decodeBody

@[simp] theorem decode_encode (message : SesmTcpPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedAllLE_encodeFramedLE 2 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : SesmTcpPacket) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

/-- Does the message end the session? Nothing in its packet may follow it -/
def endsSession (message : SesmTcpPacket) : Bool :=
  SesmPayload.endsSession message.sesmPayload

end SesmTcpPacket

/-- Packet -/
structure Packet where
  sesmTcpPacket : List SesmTcpPacket
  sesmTcpPacket_last : endsLast SesmTcpPacket.endsSession sesmTcpPacket = true
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeMany SesmTcpPacket.encode message.sesmTcpPacket

def decode (bytes : List UInt8) : Option Packet := do
  let sesmTcpPacket ← decodeAll SesmTcpPacket.decode bytes.length bytes
  if last_sesmTcpPacket : endsLast SesmTcpPacket.endsSession sesmTcpPacket = true then
    pure { sesmTcpPacket, sesmTcpPacket_last := last_sesmTcpPacket }
  else none

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany SesmTcpPacket.encode SesmTcpPacket.decode SesmTcpPacket.decode_encode SesmTcpPacket.encode_length_pos message.sesmTcpPacket _ (encodeMany_length_ge SesmTcpPacket.encode SesmTcpPacket.encode_length_pos message.sesmTcpPacket), some_bind]
  rw [dite_eq_left message.sesmTcpPacket_last]
  rfl

end Packet

end Omi.MiaxMiaxoptionsExpressinterfaceMeiV211
