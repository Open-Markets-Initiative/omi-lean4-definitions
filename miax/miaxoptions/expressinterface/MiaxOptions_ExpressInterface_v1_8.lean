import Wire

/-!
# Miami International Holdings Express Interface v1.8

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

namespace Omi.MiaxMiaxoptionsExpressinterfaceMeiV18

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
  [0x41, 0x42, 0x43, 0x44, 0x45, 0x49, 0x4A, 0x4B, 0x4D, 0x4E, 0x50, 0x51, 0x54, 0x57, 0x58, 0x59, 0x5A]

inductive OpeningUnderlyingMarketCode where
  | nyseAmex -- Nyse Amex
  | nasdaqOmxBx -- Nasdaq Omx Bx
  | nationalStockExchange -- National Stock Exchange
  | finraAdf -- Finra Adf
  | marketIndependentAnyMarketThatOpensFirst -- Market Independent Any Market That Opens First
  | internationalSecuritiesExchange -- International Securities Exchange
  | edgaExchangeInc -- Edga Exchange Inc
  | edgxExchangeInc -- Edgx Exchange Inc
  | chicagoStockExchange -- Chicago Stock Exchange
  | nyseEuronext -- Nyse Euronext
  | nyseArcaExchange -- Nyse Arca Exchange
  | nasdaqOmxViaUtpFeed -- Nasdaq Omx Via Utp Feed
  | nasdaqOmxViaCtaFeed -- Nasdaq Omx Via Cta Feed
  | chicagoBoardOptionsExchange -- Chicago Board Options Exchange
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
  | .internationalSecuritiesExchange => 0x49
  | .edgaExchangeInc => 0x4A
  | .edgxExchangeInc => 0x4B
  | .chicagoStockExchange => 0x4D
  | .nyseEuronext => 0x4E
  | .nyseArcaExchange => 0x50
  | .nasdaqOmxViaUtpFeed => 0x51
  | .nasdaqOmxViaCtaFeed => 0x54
  | .chicagoBoardOptionsExchange => 0x57
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
  else if byte = 0x49 then .internationalSecuritiesExchange
  else if byte = 0x4A then .edgaExchangeInc
  else if byte = 0x4B then .edgxExchangeInc
  else if byte = 0x4D then .chicagoStockExchange
  else if byte = 0x4E then .nyseEuronext
  else if byte = 0x50 then .nyseArcaExchange
  else if byte = 0x51 then .nasdaqOmxViaUtpFeed
  else if byte = 0x54 then .nasdaqOmxViaCtaFeed
  else if byte = 0x57 then .chicagoBoardOptionsExchange
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
  | internationalSecuritiesExchange => decide
  | edgaExchangeInc => decide
  | edgxExchangeInc => decide
  | chicagoStockExchange => decide
  | nyseEuronext => decide
  | nyseArcaExchange => decide
  | nasdaqOmxViaUtpFeed => decide
  | nasdaqOmxViaCtaFeed => decide
  | chicagoBoardOptionsExchange => decide
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
  [0x20, 0x49, 0x41, 0x42, 0x56, 0x4D, 0x50, 0x54, 0x53, 0x31, 0x32, 0x33, 0x34, 0x55, 0x35, 0x58, 0x4B, 0x43, 0x44, 0x5A, 0x2A]

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
  | testEQuoteSuccessfullyAcceptedPriorToLqwButNotPlacedOnMiaxBook -- Test E Quote Successfully Accepted Prior To Lqw But Not Placed On Miax Book
  | miaxClosedForTradingOfThisProductRequestCannotBeCompleted -- Miax Closed For Trading Of This Product Request Cannot Be Completed
  | rejectedDueToSelfCrossingPrimeAgencyOrder -- Rejected Due To Self Crossing Prime Agency Order
  | undefinedError -- Undefined Error
  | downgradedFromOlderVersion -- Downgraded From Older Version
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
  | .testEQuoteSuccessfullyAcceptedPriorToLqwButNotPlacedOnMiaxBook => 0x4B
  | .miaxClosedForTradingOfThisProductRequestCannotBeCompleted => 0x43
  | .rejectedDueToSelfCrossingPrimeAgencyOrder => 0x44
  | .undefinedError => 0x5A
  | .downgradedFromOlderVersion => 0x2A
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
  else if byte = 0x4B then .testEQuoteSuccessfullyAcceptedPriorToLqwButNotPlacedOnMiaxBook
  else if byte = 0x43 then .miaxClosedForTradingOfThisProductRequestCannotBeCompleted
  else if byte = 0x44 then .rejectedDueToSelfCrossingPrimeAgencyOrder
  else if byte = 0x5A then .undefinedError
  else .downgradedFromOlderVersion

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
  | testEQuoteSuccessfullyAcceptedPriorToLqwButNotPlacedOnMiaxBook => decide
  | miaxClosedForTradingOfThisProductRequestCannotBeCompleted => decide
  | rejectedDueToSelfCrossingPrimeAgencyOrder => decide
  | undefinedError => decide
  | downgradedFromOlderVersion => decide
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

/-- Liquidity Type: one byte code -/
def LiquidityType.codes : List UInt8 :=
  [0x51, 0x45]

inductive LiquidityType where
  | quote -- Quote
  | eQuote -- E Quote
  | unlisted (byte : { byte : UInt8 // byte ∉ LiquidityType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LiquidityType

def toByte : LiquidityType → UInt8
  | .quote => 0x51
  | .eQuote => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LiquidityType :=
  if byte = 0x51 then .quote
  else .eQuote

def ofByte (byte : UInt8) : LiquidityType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LiquidityType) : ofByte value.toByte = value := by
  cases value with
  | quote => decide
  | eQuote => decide
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
  [0x53, 0x57, 0x43]

inductive CancelReason where
  | cancelForUnexecutedPartOfEQuote -- Cancel For Unexecuted Part Of E Quote
  | cancelForQuoteUnusedInOpeningReopeningOrClosing -- Cancel For Quote Unused In Opening Reopening Or Closing
  | cancelOfRestingQuoteCrossedByOppositeSideQuoteOfSameMpid -- Cancel Of Resting Quote Crossed By Opposite Side Quote Of Same Mpid
  | unlisted (byte : { byte : UInt8 // byte ∉ CancelReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CancelReason

def toByte : CancelReason → UInt8
  | .cancelForUnexecutedPartOfEQuote => 0x53
  | .cancelForQuoteUnusedInOpeningReopeningOrClosing => 0x57
  | .cancelOfRestingQuoteCrossedByOppositeSideQuoteOfSameMpid => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CancelReason :=
  if byte = 0x53 then .cancelForUnexecutedPartOfEQuote
  else if byte = 0x57 then .cancelForQuoteUnusedInOpeningReopeningOrClosing
  else .cancelOfRestingQuoteCrossedByOppositeSideQuoteOfSameMpid

def ofByte (byte : UInt8) : CancelReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CancelReason) : ofByte value.toByte = value := by
  cases value with
  | cancelForUnexecutedPartOfEQuote => decide
  | cancelForQuoteUnusedInOpeningReopeningOrClosing => decide
  | cancelOfRestingQuoteCrossedByOppositeSideQuoteOfSameMpid => decide
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

/-- Side: one byte code -/
def Side.codes : List UInt8 :=
  [0x42, 0x41, 0x53]

inductive Side where
  | bid -- Bid
  | ask -- Ask
  | sold -- Sold
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .bid => 0x42
  | .ask => 0x41
  | .sold => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x42 then .bid
  else if byte = 0x41 then .ask
  else .sold

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | bid => decide
  | ask => decide
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

/-- Arm Settings Update Status: one byte code -/
def ArmSettingsUpdateStatus.codes : List UInt8 :=
  [0x20, 0x41, 0x50, 0x44, 0x4D, 0x55, 0x58, 0x4E, 0x5A, 0x45]

inductive ArmSettingsUpdateStatus where
  | settingsAppliedSuccessfully -- Settings Applied Successfully
  | invalidAction -- Invalid Action
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
  [0x20, 0x54, 0x43, 0x4F, 0x50, 0x51, 0x53, 0x55, 0x58, 0x4D, 0x52, 0x44, 0x5A]

inductive QuoteStatus where
  | quoteSuccessfullyAccepted -- Quote Successfully Accepted
  | testQuoteSuccessfullyAcceptedPriorToLqwButNotPlacedOnMiaxBook -- Test Quote Successfully Accepted Prior To Lqw But Not Placed On Miax Book
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
  | undefinedError -- Undefined Error
  | unlisted (byte : { byte : UInt8 // byte ∉ QuoteStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace QuoteStatus

def toByte : QuoteStatus → UInt8
  | .quoteSuccessfullyAccepted => 0x20
  | .testQuoteSuccessfullyAcceptedPriorToLqwButNotPlacedOnMiaxBook => 0x54
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
  | .undefinedError => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : QuoteStatus :=
  if byte = 0x20 then .quoteSuccessfullyAccepted
  else if byte = 0x54 then .testQuoteSuccessfullyAcceptedPriorToLqwButNotPlacedOnMiaxBook
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
  else .undefinedError

def ofByte (byte : UInt8) : QuoteStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : QuoteStatus) : ofByte value.toByte = value := by
  cases value with
  | quoteSuccessfullyAccepted => decide
  | testQuoteSuccessfullyAcceptedPriorToLqwButNotPlacedOnMiaxBook => decide
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
  [0x4F, 0x41, 0x49, 0x46, 0x53]

inductive EQuoteType where
  | opg -- Opg
  | aoc -- Aoc
  | ioc -- Ioc
  | fok -- Fok
  | iso -- Iso
  | unlisted (byte : { byte : UInt8 // byte ∉ EQuoteType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EQuoteType

def toByte : EQuoteType → UInt8
  | .opg => 0x4F
  | .aoc => 0x41
  | .ioc => 0x49
  | .fok => 0x46
  | .iso => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EQuoteType :=
  if byte = 0x4F then .opg
  else if byte = 0x41 then .aoc
  else if byte = 0x49 then .ioc
  else if byte = 0x46 then .fok
  else .iso

def ofByte (byte : UInt8) : EQuoteType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EQuoteType) : ofByte value.toByte = value := by
  cases value with
  | opg => decide
  | aoc => decide
  | ioc => decide
  | fok => decide
  | iso => decide
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

/-- Mass Quote Cancel Status: one byte code -/
def MassQuoteCancelStatus.codes : List UInt8 :=
  [0x20, 0x55, 0x49, 0x48, 0x4E, 0x58, 0x4D, 0x43, 0x5A, 0x2A]

inductive MassQuoteCancelStatus where
  | cancelSuccessful -- Cancel Successful
  | invalidUnderlying -- Invalid Underlying
  | massQuoteCancelStillInProgress -- Mass Quote Cancel Still In Progress
  | haltTriggeredCleanupOfQuotesStillInProgress -- Halt Triggered Cleanup Of Quotes Still In Progress
  | allQuoteHaveAlreadyBeenCanceled -- All Quote Have Already Been Canceled
  | notPermitted -- Not Permitted
  | unknownMpid -- Unknown Mpid
  | miaxClosedRequestCannotBeCompleted -- Miax Closed Request Cannot Be Completed
  | undefinedError -- Undefined Error
  | downgradedFromOlderVersion -- Downgraded From Older Version
  | unlisted (byte : { byte : UInt8 // byte ∉ MassQuoteCancelStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MassQuoteCancelStatus

def toByte : MassQuoteCancelStatus → UInt8
  | .cancelSuccessful => 0x20
  | .invalidUnderlying => 0x55
  | .massQuoteCancelStillInProgress => 0x49
  | .haltTriggeredCleanupOfQuotesStillInProgress => 0x48
  | .allQuoteHaveAlreadyBeenCanceled => 0x4E
  | .notPermitted => 0x58
  | .unknownMpid => 0x4D
  | .miaxClosedRequestCannotBeCompleted => 0x43
  | .undefinedError => 0x5A
  | .downgradedFromOlderVersion => 0x2A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MassQuoteCancelStatus :=
  if byte = 0x20 then .cancelSuccessful
  else if byte = 0x55 then .invalidUnderlying
  else if byte = 0x49 then .massQuoteCancelStillInProgress
  else if byte = 0x48 then .haltTriggeredCleanupOfQuotesStillInProgress
  else if byte = 0x4E then .allQuoteHaveAlreadyBeenCanceled
  else if byte = 0x58 then .notPermitted
  else if byte = 0x4D then .unknownMpid
  else if byte = 0x43 then .miaxClosedRequestCannotBeCompleted
  else if byte = 0x5A then .undefinedError
  else .downgradedFromOlderVersion

def ofByte (byte : UInt8) : MassQuoteCancelStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MassQuoteCancelStatus) : ofByte value.toByte = value := by
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
  | downgradedFromOlderVersion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MassQuoteCancelStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MassQuoteCancelStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MassQuoteCancelStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : MassQuoteCancelStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : MassQuoteCancelStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MassQuoteCancelStatus

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
  | killSwitchProtectionIsInEffectFutureUse -- Kill Switch Protection Is In Effect Future Use
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
  | .killSwitchProtectionIsInEffectFutureUse => 0x4B
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
  else if byte = 0x4B then .killSwitchProtectionIsInEffectFutureUse
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
  | killSwitchProtectionIsInEffectFutureUse => decide
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

/-- Trigger Reason: one byte code -/
def TriggerReason.codes : List UInt8 :=
  [0x45, 0x55, 0x52, 0x54, 0x4B, 0x46, 0x2A]

inductive TriggerReason where
  | exchangeInitiatedMassQuoteCancel -- Exchange Initiated Mass Quote Cancel
  | firmInitiatedMassQuoteCancel -- Firm Initiated Mass Quote Cancel
  | armTriggeredProtection -- Arm Triggered Protection
  | tradingHalt -- Trading Halt
  | killSwitchProtectionIsInEffectFutureUse -- Kill Switch Protection Is In Effect Future Use
  | arm2FirmLevelProtectionInitiatedMassQuoteCancel -- Arm 2 Firm Level Protection Initiated Mass Quote Cancel
  | downgradedFromOlderVersion -- Downgraded From Older Version
  | unlisted (byte : { byte : UInt8 // byte ∉ TriggerReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TriggerReason

def toByte : TriggerReason → UInt8
  | .exchangeInitiatedMassQuoteCancel => 0x45
  | .firmInitiatedMassQuoteCancel => 0x55
  | .armTriggeredProtection => 0x52
  | .tradingHalt => 0x54
  | .killSwitchProtectionIsInEffectFutureUse => 0x4B
  | .arm2FirmLevelProtectionInitiatedMassQuoteCancel => 0x46
  | .downgradedFromOlderVersion => 0x2A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TriggerReason :=
  if byte = 0x45 then .exchangeInitiatedMassQuoteCancel
  else if byte = 0x55 then .firmInitiatedMassQuoteCancel
  else if byte = 0x52 then .armTriggeredProtection
  else if byte = 0x54 then .tradingHalt
  else if byte = 0x4B then .killSwitchProtectionIsInEffectFutureUse
  else if byte = 0x46 then .arm2FirmLevelProtectionInitiatedMassQuoteCancel
  else .downgradedFromOlderVersion

def ofByte (byte : UInt8) : TriggerReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TriggerReason) : ofByte value.toByte = value := by
  cases value with
  | exchangeInitiatedMassQuoteCancel => decide
  | firmInitiatedMassQuoteCancel => decide
  | armTriggeredProtection => decide
  | tradingHalt => decide
  | killSwitchProtectionIsInEffectFutureUse => decide
  | arm2FirmLevelProtectionInitiatedMassQuoteCancel => decide
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

/-- Series Update: 76 bytes -/
structure SeriesUpdate where
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

namespace SeriesUpdate

def encode (message : SeriesUpdate) : List UInt8 :=
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

def decode (bytes : List UInt8) : Option (SeriesUpdate × List UInt8) := do
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

@[simp] theorem encode_length (message : SeriesUpdate) : (encode message).length = 76 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, CallOrPut.encode_length, RestrictedOption.encode_length, LongTermOption.encode_length, ActiveOnMiax.encode_length, MiaxBboPostingIncrementIndicator.encode_length, QuoteAcceptanceIncrementIndicator.encode_length, OpeningUnderlyingMarketCode.encode_length]

theorem encode_length_pos (message : SeriesUpdate) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SeriesUpdate) (rest : List UInt8) :
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

end SeriesUpdate

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

/-- Enhanced Quote E Quote Response: 17 bytes -/
structure EnhancedQuoteEQuoteResponse where
  clientMessageId : BitVec 32
  mpid : Alpha 4
  eQuoteId : BitVec 64
  eQuoteRequestStatus : EQuoteRequestStatus
  deriving DecidableEq, Repr

namespace EnhancedQuoteEQuoteResponse

def encode (message : EnhancedQuoteEQuoteResponse) : List UInt8 :=
  encodeUIntLE 4 message.clientMessageId
    ++ (Alpha.encode message.mpid
    ++ (encodeUIntLE 8 message.eQuoteId
    ++ (EQuoteRequestStatus.encode message.eQuoteRequestStatus)))

def decode (bytes : List UInt8) : Option (EnhancedQuoteEQuoteResponse × List UInt8) := do
  let (clientMessageId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (eQuoteId, bytes) ← decodeUIntLE 8 bytes
  let (eQuoteRequestStatus, bytes) ← EQuoteRequestStatus.decode bytes
  pure ({ clientMessageId, mpid, eQuoteId, eQuoteRequestStatus }, bytes)

@[simp] theorem encode_length (message : EnhancedQuoteEQuoteResponse) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, EQuoteRequestStatus.encode_length]

theorem encode_length_pos (message : EnhancedQuoteEQuoteResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EnhancedQuoteEQuoteResponse) (rest : List UInt8) :
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

end EnhancedQuoteEQuoteResponse

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

/-- Quote Width Relief Notification: 23 bytes -/
structure QuoteWidthReliefNotification where
  notificationTime : BitVec 64
  underlyingSymbol : Alpha 11
  reliefMultiplier : BitVec 32
  deriving DecidableEq, Repr

namespace QuoteWidthReliefNotification

def encode (message : QuoteWidthReliefNotification) : List UInt8 :=
  encodeUIntLE 8 message.notificationTime
    ++ (Alpha.encode message.underlyingSymbol
    ++ (encodeUIntLE 4 message.reliefMultiplier))

def decode (bytes : List UInt8) : Option (QuoteWidthReliefNotification × List UInt8) := do
  let (notificationTime, bytes) ← decodeUIntLE 8 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 11 bytes
  let (reliefMultiplier, bytes) ← decodeUIntLE 4 bytes
  pure ({ notificationTime, underlyingSymbol, reliefMultiplier }, bytes)

@[simp] theorem encode_length (message : QuoteWidthReliefNotification) : (encode message).length = 23 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : QuoteWidthReliefNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteWidthReliefNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end QuoteWidthReliefNotification

/-- Arm Protection Settings Notification: 31 bytes -/
structure ArmProtectionSettingsNotification where
  notificationTime : BitVec 64
  mpid : Alpha 4
  underlyingSymbol : Alpha 11
  allowableEngagementPercentage : BitVec 32
  countingPeriod : BitVec 16
  action : Action
  source : Source
  deriving DecidableEq, Repr

namespace ArmProtectionSettingsNotification

def encode (message : ArmProtectionSettingsNotification) : List UInt8 :=
  encodeUIntLE 8 message.notificationTime
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.underlyingSymbol
    ++ (encodeUIntLE 4 message.allowableEngagementPercentage
    ++ (encodeUIntLE 2 message.countingPeriod
    ++ (Action.encode message.action
    ++ (Source.encode message.source))))))

def decode (bytes : List UInt8) : Option (ArmProtectionSettingsNotification × List UInt8) := do
  let (notificationTime, bytes) ← decodeUIntLE 8 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 11 bytes
  let (allowableEngagementPercentage, bytes) ← decodeUIntLE 4 bytes
  let (countingPeriod, bytes) ← decodeUIntLE 2 bytes
  let (action, bytes) ← Action.decode bytes
  let (source, bytes) ← Source.decode bytes
  pure ({ notificationTime, mpid, underlyingSymbol, allowableEngagementPercentage, countingPeriod, action, source }, bytes)

@[simp] theorem encode_length (message : ArmProtectionSettingsNotification) : (encode message).length = 31 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, Action.encode_length, Source.encode_length]

theorem encode_length_pos (message : ArmProtectionSettingsNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ArmProtectionSettingsNotification) (rest : List UInt8) :
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
  rw [Source.decode_encode, some_bind]
  rfl

end ArmProtectionSettingsNotification

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

/-- Cancel Notification: 36 bytes -/
structure CancelNotification where
  notificationTime : BitVec 64
  mpid : Alpha 4
  productId : BitVec 32
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
    ++ (encodeUIntLE 4 message.productId
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
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (liquidityType, bytes) ← LiquidityType.decode bytes
  let (clientMessageId, bytes) ← decodeUIntLE 4 bytes
  let (bulkQuoteIndex, bytes) ← decodeUInt 1 bytes
  let (quoteeQuoteSide, bytes) ← QuoteeQuoteSide.decode bytes
  let (size, bytes) ← decodeUIntLE 4 bytes
  let (engineSequenceNumber, bytes) ← decodeUIntLE 8 bytes
  let (cancelReason, bytes) ← CancelReason.decode bytes
  pure ({ notificationTime, mpid, productId, liquidityType, clientMessageId, bulkQuoteIndex, quoteeQuoteSide, size, engineSequenceNumber, cancelReason }, bytes)

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

/-- Execution Notification: 49 bytes -/
structure ExecutionNotification where
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

namespace ExecutionNotification

def encode (message : ExecutionNotification) : List UInt8 :=
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

def decode (bytes : List UInt8) : Option (ExecutionNotification × List UInt8) := do
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

@[simp] theorem encode_length (message : ExecutionNotification) : (encode message).length = 49 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, LiquidityType.encode_length, encodeUInt_length, TradeStatus.encode_length, Side.encode_length]

theorem encode_length_pos (message : ExecutionNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExecutionNotification) (rest : List UInt8) :
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

end ExecutionNotification

/-- Any Sequenced Message, selected by Sequenced Message Type -/
inductive SequencedMessage where
  | seriesUpdate (message : SeriesUpdate) -- "SU" 0x5355
  | validQuoteWidthForOpening (message : ValidQuoteWidthForOpening) -- "QW" 0x5157
  | enhancedQuoteEQuoteResponse (message : EnhancedQuoteEQuoteResponse) -- "ER" 0x4552
  | systemStateNotification (message : SystemStateNotification) -- "SN" 0x534E
  | productTradingStatusNotification (message : ProductTradingStatusNotification) -- "TN" 0x544E
  | underlyingTradingStatusNotification (message : UnderlyingTradingStatusNotification) -- "UN" 0x554E
  | quoteWidthReliefNotification (message : QuoteWidthReliefNotification) -- "QN" 0x514E
  | armProtectionSettingsNotification (message : ArmProtectionSettingsNotification) -- "AN" 0x414E
  | arm2UnderlyingLevelProtectionSettingsNotification (message : Arm2UnderlyingLevelProtectionSettingsNotification) -- "A2" 0x4132
  | arm2UnderlyingLevelProtectionNotification (message : Arm2UnderlyingLevelProtectionNotification) -- "UP" 0x5550
  | arm2FirmLevelProtectionNotification (message : Arm2FirmLevelProtectionNotification) -- "FP" 0x4650
  | cancelNotification (message : CancelNotification) -- "XN" 0x584E
  | executionNotification (message : ExecutionNotification) -- "EN" 0x454E
  deriving DecidableEq, Repr

namespace SequencedMessage

/-- The Sequenced Message Type each message is sent under -/
def tag : SequencedMessage → BitVec 16
  | .seriesUpdate _ => 21333
  | .validQuoteWidthForOpening _ => 20823
  | .enhancedQuoteEQuoteResponse _ => 17746
  | .systemStateNotification _ => 21326
  | .productTradingStatusNotification _ => 21582
  | .underlyingTradingStatusNotification _ => 21838
  | .quoteWidthReliefNotification _ => 20814
  | .armProtectionSettingsNotification _ => 16718
  | .arm2UnderlyingLevelProtectionSettingsNotification _ => 16690
  | .arm2UnderlyingLevelProtectionNotification _ => 21840
  | .arm2FirmLevelProtectionNotification _ => 18000
  | .cancelNotification _ => 22606
  | .executionNotification _ => 17742

def encode : SequencedMessage → List UInt8
  | .seriesUpdate message => SeriesUpdate.encode message
  | .validQuoteWidthForOpening message => ValidQuoteWidthForOpening.encode message
  | .enhancedQuoteEQuoteResponse message => EnhancedQuoteEQuoteResponse.encode message
  | .systemStateNotification message => SystemStateNotification.encode message
  | .productTradingStatusNotification message => ProductTradingStatusNotification.encode message
  | .underlyingTradingStatusNotification message => UnderlyingTradingStatusNotification.encode message
  | .quoteWidthReliefNotification message => QuoteWidthReliefNotification.encode message
  | .armProtectionSettingsNotification message => ArmProtectionSettingsNotification.encode message
  | .arm2UnderlyingLevelProtectionSettingsNotification message => Arm2UnderlyingLevelProtectionSettingsNotification.encode message
  | .arm2UnderlyingLevelProtectionNotification message => Arm2UnderlyingLevelProtectionNotification.encode message
  | .arm2FirmLevelProtectionNotification message => Arm2FirmLevelProtectionNotification.encode message
  | .cancelNotification message => CancelNotification.encode message
  | .executionNotification message => ExecutionNotification.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : SequencedMessage) : (encode message).length ≤ 76 := by
  cases message with
  | seriesUpdate inner =>
    simp only [encode, SeriesUpdate.encode_length]
    omega
  | validQuoteWidthForOpening inner =>
    simp only [encode, ValidQuoteWidthForOpening.encode_length]
    omega
  | enhancedQuoteEQuoteResponse inner =>
    simp only [encode, EnhancedQuoteEQuoteResponse.encode_length]
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
  | quoteWidthReliefNotification inner =>
    simp only [encode, QuoteWidthReliefNotification.encode_length]
    omega
  | armProtectionSettingsNotification inner =>
    simp only [encode, ArmProtectionSettingsNotification.encode_length]
    omega
  | arm2UnderlyingLevelProtectionSettingsNotification inner =>
    simp only [encode, Arm2UnderlyingLevelProtectionSettingsNotification.encode_length]
    omega
  | arm2UnderlyingLevelProtectionNotification inner =>
    simp only [encode, Arm2UnderlyingLevelProtectionNotification.encode_length]
    omega
  | arm2FirmLevelProtectionNotification inner =>
    simp only [encode, Arm2FirmLevelProtectionNotification.encode_length]
    omega
  | cancelNotification inner =>
    simp only [encode, CancelNotification.encode_length]
    omega
  | executionNotification inner =>
    simp only [encode, ExecutionNotification.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (SequencedMessage × List UInt8) :=
  if tag = 21333 then (SeriesUpdate.decode bytes).map fun (message, rest) => (.seriesUpdate message, rest)
  else if tag = 20823 then (ValidQuoteWidthForOpening.decode bytes).map fun (message, rest) => (.validQuoteWidthForOpening message, rest)
  else if tag = 17746 then (EnhancedQuoteEQuoteResponse.decode bytes).map fun (message, rest) => (.enhancedQuoteEQuoteResponse message, rest)
  else if tag = 21326 then (SystemStateNotification.decode bytes).map fun (message, rest) => (.systemStateNotification message, rest)
  else if tag = 21582 then (ProductTradingStatusNotification.decode bytes).map fun (message, rest) => (.productTradingStatusNotification message, rest)
  else if tag = 21838 then (UnderlyingTradingStatusNotification.decode bytes).map fun (message, rest) => (.underlyingTradingStatusNotification message, rest)
  else if tag = 20814 then (QuoteWidthReliefNotification.decode bytes).map fun (message, rest) => (.quoteWidthReliefNotification message, rest)
  else if tag = 16718 then (ArmProtectionSettingsNotification.decode bytes).map fun (message, rest) => (.armProtectionSettingsNotification message, rest)
  else if tag = 16690 then (Arm2UnderlyingLevelProtectionSettingsNotification.decode bytes).map fun (message, rest) => (.arm2UnderlyingLevelProtectionSettingsNotification message, rest)
  else if tag = 21840 then (Arm2UnderlyingLevelProtectionNotification.decode bytes).map fun (message, rest) => (.arm2UnderlyingLevelProtectionNotification message, rest)
  else if tag = 18000 then (Arm2FirmLevelProtectionNotification.decode bytes).map fun (message, rest) => (.arm2FirmLevelProtectionNotification message, rest)
  else if tag = 22606 then (CancelNotification.decode bytes).map fun (message, rest) => (.cancelNotification message, rest)
  else if tag = 17742 then (ExecutionNotification.decode bytes).map fun (message, rest) => (.executionNotification message, rest)
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
theorem encode_length_le (message : SequencedDataPacket) : (encode message).length ≤ 86 := by
  unfold encode
  cases message.sequencedMessage with
  | seriesUpdate inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, SeriesUpdate.encode_length]
    omega
  | validQuoteWidthForOpening inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, ValidQuoteWidthForOpening.encode_length]
    omega
  | enhancedQuoteEQuoteResponse inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, EnhancedQuoteEQuoteResponse.encode_length]
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
  | quoteWidthReliefNotification inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, QuoteWidthReliefNotification.encode_length]
    omega
  | armProtectionSettingsNotification inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, ArmProtectionSettingsNotification.encode_length]
    omega
  | arm2UnderlyingLevelProtectionSettingsNotification inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Arm2UnderlyingLevelProtectionSettingsNotification.encode_length]
    omega
  | arm2UnderlyingLevelProtectionNotification inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Arm2UnderlyingLevelProtectionNotification.encode_length]
    omega
  | arm2FirmLevelProtectionNotification inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Arm2FirmLevelProtectionNotification.encode_length]
    omega
  | cancelNotification inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, CancelNotification.encode_length]
    omega
  | executionNotification inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, ExecutionNotification.encode_length]
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

/-- Arm Settings Update Request: 26 bytes -/
structure ArmSettingsUpdateRequest where
  clientMessageId : BitVec 32
  mpid : Alpha 4
  action : Action
  underlyingSymbol : Alpha 11
  allowableEngagementPercentage : BitVec 32
  countingPeriod : BitVec 16
  deriving DecidableEq, Repr

namespace ArmSettingsUpdateRequest

def encode (message : ArmSettingsUpdateRequest) : List UInt8 :=
  encodeUIntLE 4 message.clientMessageId
    ++ (Alpha.encode message.mpid
    ++ (Action.encode message.action
    ++ (Alpha.encode message.underlyingSymbol
    ++ (encodeUIntLE 4 message.allowableEngagementPercentage
    ++ (encodeUIntLE 2 message.countingPeriod)))))

def decode (bytes : List UInt8) : Option (ArmSettingsUpdateRequest × List UInt8) := do
  let (clientMessageId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (action, bytes) ← Action.decode bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 11 bytes
  let (allowableEngagementPercentage, bytes) ← decodeUIntLE 4 bytes
  let (countingPeriod, bytes) ← decodeUIntLE 2 bytes
  pure ({ clientMessageId, mpid, action, underlyingSymbol, allowableEngagementPercentage, countingPeriod }, bytes)

@[simp] theorem encode_length (message : ArmSettingsUpdateRequest) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, Action.encode_length]

theorem encode_length_pos (message : ArmSettingsUpdateRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ArmSettingsUpdateRequest) (rest : List UInt8) :
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

end ArmSettingsUpdateRequest

/-- Arm Settings Update Response: 20 bytes -/
structure ArmSettingsUpdateResponse where
  clientMessageId : BitVec 32
  mpid : Alpha 4
  underlyingSymbol : Alpha 11
  armSettingsUpdateStatus : ArmSettingsUpdateStatus
  deriving DecidableEq, Repr

namespace ArmSettingsUpdateResponse

def encode (message : ArmSettingsUpdateResponse) : List UInt8 :=
  encodeUIntLE 4 message.clientMessageId
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.underlyingSymbol
    ++ (ArmSettingsUpdateStatus.encode message.armSettingsUpdateStatus)))

def decode (bytes : List UInt8) : Option (ArmSettingsUpdateResponse × List UInt8) := do
  let (clientMessageId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 11 bytes
  let (armSettingsUpdateStatus, bytes) ← ArmSettingsUpdateStatus.decode bytes
  pure ({ clientMessageId, mpid, underlyingSymbol, armSettingsUpdateStatus }, bytes)

@[simp] theorem encode_length (message : ArmSettingsUpdateResponse) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, ArmSettingsUpdateStatus.encode_length]

theorem encode_length_pos (message : ArmSettingsUpdateResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ArmSettingsUpdateResponse) (rest : List UInt8) :
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

end ArmSettingsUpdateResponse

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

/-- Single Side Quote: 13 bytes -/
structure SingleSideQuote where
  productId : BitVec 32
  price : BitVec 32
  size : BitVec 32
  side : Side
  deriving DecidableEq, Repr

namespace SingleSideQuote

def encode (message : SingleSideQuote) : List UInt8 :=
  encodeUIntLE 4 message.productId
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 4 message.size
    ++ (Side.encode message.side)))

def decode (bytes : List UInt8) : Option (SingleSideQuote × List UInt8) := do
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (size, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← Side.decode bytes
  pure ({ productId, price, size, side }, bytes)

@[simp] theorem encode_length (message : SingleSideQuote) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Side.encode_length]

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
  rw [Side.decode_encode, some_bind]
  rfl

end SingleSideQuote

/-- Bulk Quote Message -/
structure BulkQuoteMessage where
  clientMessageId : BitVec 32
  mpid : Alpha 4
  singleSideQuote : Bounded 1 SingleSideQuote
  deriving DecidableEq, Repr

namespace BulkQuoteMessage

def encode (message : BulkQuoteMessage) : List UInt8 :=
  encodeUIntLE 4 message.clientMessageId
    ++ (Alpha.encode message.mpid
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.singleSideQuote.val.length)
    ++ (encodeMany SingleSideQuote.encode message.singleSideQuote.val)))

def decode (bytes : List UInt8) : Option (BulkQuoteMessage × List UInt8) := do
  let (clientMessageId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (quoteCount, bytes) ← decodeUInt 1 bytes
  let (singleSideQuote_, bytes) ← decodeMany SingleSideQuote.decode quoteCount.toNat bytes
  if fits_singleSideQuote : singleSideQuote_.length < 256 ^ 1 then
    pure ({ clientMessageId, mpid, singleSideQuote := ⟨singleSideQuote_, fits_singleSideQuote⟩ }, bytes)
  else none

theorem encode_length_pos (message : BulkQuoteMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : BulkQuoteMessage) : (encode message).length ≤ 3324 := by
  have bound_singleSideQuote := message.singleSideQuote.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length, encodeMany_length_const SingleSideQuote.encode 13 SingleSideQuote.encode_length]
  omega

@[simp] theorem decode_encode (message : BulkQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 SingleSideQuote.encode SingleSideQuote.decode SingleSideQuote.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.singleSideQuote.length_lt]
  rfl

end BulkQuoteMessage

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

/-- Bulk Quote Response -/
structure BulkQuoteResponse where
  clientMessageId : BitVec 32
  mpid : Alpha 4
  bulkQuoteStatus : BulkQuoteStatus
  quoteCount : BitVec 8
  quoteAckTime : BitVec 64
  singleSideQuoteResponse : Bounded 1 SingleSideQuoteResponse
  deriving DecidableEq, Repr

namespace BulkQuoteResponse

def encode (message : BulkQuoteResponse) : List UInt8 :=
  encodeUIntLE 4 message.clientMessageId
    ++ (Alpha.encode message.mpid
    ++ (BulkQuoteStatus.encode message.bulkQuoteStatus
    ++ (encodeUInt 1 message.quoteCount
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.singleSideQuoteResponse.val.length)
    ++ (encodeUIntLE 8 message.quoteAckTime
    ++ (encodeMany SingleSideQuoteResponse.encode message.singleSideQuoteResponse.val))))))

def decode (bytes : List UInt8) : Option (BulkQuoteResponse × List UInt8) := do
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

theorem encode_length_pos (message : BulkQuoteResponse) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : BulkQuoteResponse) : (encode message).length ≤ 2314 := by
  have bound_singleSideQuoteResponse := message.singleSideQuoteResponse.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Alpha.encode_length, BulkQuoteStatus.encode_length, encodeUInt_length, encodeMany_length_const SingleSideQuoteResponse.encode 9 SingleSideQuoteResponse.encode_length]
  omega

@[simp] theorem decode_encode (message : BulkQuoteResponse) (rest : List UInt8) :
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

end BulkQuoteResponse

/-- Enhanced Quote E Quote Message: 31 bytes -/
structure EnhancedQuoteEQuoteMessage where
  clientMessageId : BitVec 32
  mpid : Alpha 4
  productId : BitVec 32
  eQuoteAction : EQuoteAction
  eQuoteType : EQuoteType
  eventId : BitVec 32
  targetMessageId : BitVec 32
  price : BitVec 32
  size : BitVec 32
  side : Side
  deriving DecidableEq, Repr

namespace EnhancedQuoteEQuoteMessage

def encode (message : EnhancedQuoteEQuoteMessage) : List UInt8 :=
  encodeUIntLE 4 message.clientMessageId
    ++ (Alpha.encode message.mpid
    ++ (encodeUIntLE 4 message.productId
    ++ (EQuoteAction.encode message.eQuoteAction
    ++ (EQuoteType.encode message.eQuoteType
    ++ (encodeUIntLE 4 message.eventId
    ++ (encodeUIntLE 4 message.targetMessageId
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 4 message.size
    ++ (Side.encode message.side)))))))))

def decode (bytes : List UInt8) : Option (EnhancedQuoteEQuoteMessage × List UInt8) := do
  let (clientMessageId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (eQuoteAction, bytes) ← EQuoteAction.decode bytes
  let (eQuoteType, bytes) ← EQuoteType.decode bytes
  let (eventId, bytes) ← decodeUIntLE 4 bytes
  let (targetMessageId, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (size, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← Side.decode bytes
  pure ({ clientMessageId, mpid, productId, eQuoteAction, eQuoteType, eventId, targetMessageId, price, size, side }, bytes)

@[simp] theorem encode_length (message : EnhancedQuoteEQuoteMessage) : (encode message).length = 31 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, EQuoteAction.encode_length, EQuoteType.encode_length, Side.encode_length]

theorem encode_length_pos (message : EnhancedQuoteEQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EnhancedQuoteEQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [Side.decode_encode, some_bind]
  rfl

end EnhancedQuoteEQuoteMessage

/-- Mass Quote Cancel Request: 19 bytes -/
structure MassQuoteCancelRequest where
  clientMessageId : BitVec 32
  mpid : Alpha 4
  underlyingSymbol : Alpha 11
  deriving DecidableEq, Repr

namespace MassQuoteCancelRequest

def encode (message : MassQuoteCancelRequest) : List UInt8 :=
  encodeUIntLE 4 message.clientMessageId
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.underlyingSymbol))

def decode (bytes : List UInt8) : Option (MassQuoteCancelRequest × List UInt8) := do
  let (clientMessageId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 11 bytes
  pure ({ clientMessageId, mpid, underlyingSymbol }, bytes)

@[simp] theorem encode_length (message : MassQuoteCancelRequest) : (encode message).length = 19 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : MassQuoteCancelRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MassQuoteCancelRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MassQuoteCancelRequest

/-- Mass Quote Cancel Response: 9 bytes -/
structure MassQuoteCancelResponse where
  clientMessageId : BitVec 32
  mpid : Alpha 4
  massQuoteCancelStatus : MassQuoteCancelStatus
  deriving DecidableEq, Repr

namespace MassQuoteCancelResponse

def encode (message : MassQuoteCancelResponse) : List UInt8 :=
  encodeUIntLE 4 message.clientMessageId
    ++ (Alpha.encode message.mpid
    ++ (MassQuoteCancelStatus.encode message.massQuoteCancelStatus))

def decode (bytes : List UInt8) : Option (MassQuoteCancelResponse × List UInt8) := do
  let (clientMessageId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (massQuoteCancelStatus, bytes) ← MassQuoteCancelStatus.decode bytes
  pure ({ clientMessageId, mpid, massQuoteCancelStatus }, bytes)

@[simp] theorem encode_length (message : MassQuoteCancelResponse) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, MassQuoteCancelStatus.encode_length]

theorem encode_length_pos (message : MassQuoteCancelResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MassQuoteCancelResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [MassQuoteCancelStatus.decode_encode, some_bind]
  rfl

end MassQuoteCancelResponse

/-- Quote Protection Reset Request: 19 bytes -/
structure QuoteProtectionResetRequest where
  clientMessageId : BitVec 32
  mpid : Alpha 4
  underlyingSymbol : Alpha 11
  deriving DecidableEq, Repr

namespace QuoteProtectionResetRequest

def encode (message : QuoteProtectionResetRequest) : List UInt8 :=
  encodeUIntLE 4 message.clientMessageId
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.underlyingSymbol))

def decode (bytes : List UInt8) : Option (QuoteProtectionResetRequest × List UInt8) := do
  let (clientMessageId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 11 bytes
  pure ({ clientMessageId, mpid, underlyingSymbol }, bytes)

@[simp] theorem encode_length (message : QuoteProtectionResetRequest) : (encode message).length = 19 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : QuoteProtectionResetRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteProtectionResetRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end QuoteProtectionResetRequest

/-- Quote Protection Reset Response: 9 bytes -/
structure QuoteProtectionResetResponse where
  clientMessageId : BitVec 32
  mpid : Alpha 4
  quoteProtectionResetStatus : QuoteProtectionResetStatus
  deriving DecidableEq, Repr

namespace QuoteProtectionResetResponse

def encode (message : QuoteProtectionResetResponse) : List UInt8 :=
  encodeUIntLE 4 message.clientMessageId
    ++ (Alpha.encode message.mpid
    ++ (QuoteProtectionResetStatus.encode message.quoteProtectionResetStatus))

def decode (bytes : List UInt8) : Option (QuoteProtectionResetResponse × List UInt8) := do
  let (clientMessageId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (quoteProtectionResetStatus, bytes) ← QuoteProtectionResetStatus.decode bytes
  pure ({ clientMessageId, mpid, quoteProtectionResetStatus }, bytes)

@[simp] theorem encode_length (message : QuoteProtectionResetResponse) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, QuoteProtectionResetStatus.encode_length]

theorem encode_length_pos (message : QuoteProtectionResetResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteProtectionResetResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [QuoteProtectionResetStatus.decode_encode, some_bind]
  rfl

end QuoteProtectionResetResponse

/-- Quote Protection Trigger Notification: 24 bytes -/
structure QuoteProtectionTriggerNotification where
  notificationTime : BitVec 64
  mpid : Alpha 4
  underlyingSymbol : Alpha 11
  triggerReason : TriggerReason
  deriving DecidableEq, Repr

namespace QuoteProtectionTriggerNotification

def encode (message : QuoteProtectionTriggerNotification) : List UInt8 :=
  encodeUIntLE 8 message.notificationTime
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.underlyingSymbol
    ++ (TriggerReason.encode message.triggerReason)))

def decode (bytes : List UInt8) : Option (QuoteProtectionTriggerNotification × List UInt8) := do
  let (notificationTime, bytes) ← decodeUIntLE 8 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 11 bytes
  let (triggerReason, bytes) ← TriggerReason.decode bytes
  pure ({ notificationTime, mpid, underlyingSymbol, triggerReason }, bytes)

@[simp] theorem encode_length (message : QuoteProtectionTriggerNotification) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TriggerReason.encode_length]

theorem encode_length_pos (message : QuoteProtectionTriggerNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteProtectionTriggerNotification) (rest : List UInt8) :
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

end QuoteProtectionTriggerNotification

/-- Any Unsequenced Message, selected by Unsequenced Message Type -/
inductive UnsequencedMessage where
  | armSettingsUpdateRequest (message : ArmSettingsUpdateRequest) -- "AS" 0x4153
  | armSettingsUpdateResponse (message : ArmSettingsUpdateResponse) -- "AA" 0x4141
  | arm2UnderlyingLevelProtectionSettingsUpdateRequest (message : Arm2UnderlyingLevelProtectionSettingsUpdateRequest) -- "2S" 0x3253
  | arm2UnderlyingLevelProtectionSettingsUpdateResponse (message : Arm2UnderlyingLevelProtectionSettingsUpdateResponse) -- "2R" 0x3252
  | bulkQuoteMessage (message : BulkQuoteMessage) -- "QM" 0x514D
  | bulkQuoteResponse (message : BulkQuoteResponse) -- "QR" 0x5152
  | enhancedQuoteEQuoteMessage (message : EnhancedQuoteEQuoteMessage) -- "EQ" 0x4551
  | massQuoteCancelRequest (message : MassQuoteCancelRequest) -- "XQ" 0x5851
  | massQuoteCancelResponse (message : MassQuoteCancelResponse) -- "XR" 0x5852
  | quoteProtectionResetRequest (message : QuoteProtectionResetRequest) -- "PX" 0x5058
  | quoteProtectionResetResponse (message : QuoteProtectionResetResponse) -- "PR" 0x5052
  | quoteProtectionTriggerNotification (message : QuoteProtectionTriggerNotification) -- "QP" 0x5150
  | cancelNotification (message : CancelNotification) -- "XN" 0x584E
  deriving DecidableEq, Repr

namespace UnsequencedMessage

/-- The Unsequenced Message Type each message is sent under -/
def tag : UnsequencedMessage → BitVec 16
  | .armSettingsUpdateRequest _ => 16723
  | .armSettingsUpdateResponse _ => 16705
  | .arm2UnderlyingLevelProtectionSettingsUpdateRequest _ => 12883
  | .arm2UnderlyingLevelProtectionSettingsUpdateResponse _ => 12882
  | .bulkQuoteMessage _ => 20813
  | .bulkQuoteResponse _ => 20818
  | .enhancedQuoteEQuoteMessage _ => 17745
  | .massQuoteCancelRequest _ => 22609
  | .massQuoteCancelResponse _ => 22610
  | .quoteProtectionResetRequest _ => 20568
  | .quoteProtectionResetResponse _ => 20562
  | .quoteProtectionTriggerNotification _ => 20816
  | .cancelNotification _ => 22606

def encode : UnsequencedMessage → List UInt8
  | .armSettingsUpdateRequest message => ArmSettingsUpdateRequest.encode message
  | .armSettingsUpdateResponse message => ArmSettingsUpdateResponse.encode message
  | .arm2UnderlyingLevelProtectionSettingsUpdateRequest message => Arm2UnderlyingLevelProtectionSettingsUpdateRequest.encode message
  | .arm2UnderlyingLevelProtectionSettingsUpdateResponse message => Arm2UnderlyingLevelProtectionSettingsUpdateResponse.encode message
  | .bulkQuoteMessage message => BulkQuoteMessage.encode message
  | .bulkQuoteResponse message => BulkQuoteResponse.encode message
  | .enhancedQuoteEQuoteMessage message => EnhancedQuoteEQuoteMessage.encode message
  | .massQuoteCancelRequest message => MassQuoteCancelRequest.encode message
  | .massQuoteCancelResponse message => MassQuoteCancelResponse.encode message
  | .quoteProtectionResetRequest message => QuoteProtectionResetRequest.encode message
  | .quoteProtectionResetResponse message => QuoteProtectionResetResponse.encode message
  | .quoteProtectionTriggerNotification message => QuoteProtectionTriggerNotification.encode message
  | .cancelNotification message => CancelNotification.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : UnsequencedMessage) : (encode message).length ≤ 3324 := by
  cases message with
  | armSettingsUpdateRequest inner =>
    simp only [encode, ArmSettingsUpdateRequest.encode_length]
    omega
  | armSettingsUpdateResponse inner =>
    simp only [encode, ArmSettingsUpdateResponse.encode_length]
    omega
  | arm2UnderlyingLevelProtectionSettingsUpdateRequest inner =>
    simp only [encode, Arm2UnderlyingLevelProtectionSettingsUpdateRequest.encode_length]
    omega
  | arm2UnderlyingLevelProtectionSettingsUpdateResponse inner =>
    simp only [encode, Arm2UnderlyingLevelProtectionSettingsUpdateResponse.encode_length]
    omega
  | bulkQuoteMessage inner =>
    have bound_inner := BulkQuoteMessage.encode_length_le inner
    simp only [encode]
    omega
  | bulkQuoteResponse inner =>
    have bound_inner := BulkQuoteResponse.encode_length_le inner
    simp only [encode]
    omega
  | enhancedQuoteEQuoteMessage inner =>
    simp only [encode, EnhancedQuoteEQuoteMessage.encode_length]
    omega
  | massQuoteCancelRequest inner =>
    simp only [encode, MassQuoteCancelRequest.encode_length]
    omega
  | massQuoteCancelResponse inner =>
    simp only [encode, MassQuoteCancelResponse.encode_length]
    omega
  | quoteProtectionResetRequest inner =>
    simp only [encode, QuoteProtectionResetRequest.encode_length]
    omega
  | quoteProtectionResetResponse inner =>
    simp only [encode, QuoteProtectionResetResponse.encode_length]
    omega
  | quoteProtectionTriggerNotification inner =>
    simp only [encode, QuoteProtectionTriggerNotification.encode_length]
    omega
  | cancelNotification inner =>
    simp only [encode, CancelNotification.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (UnsequencedMessage × List UInt8) :=
  if tag = 16723 then (ArmSettingsUpdateRequest.decode bytes).map fun (message, rest) => (.armSettingsUpdateRequest message, rest)
  else if tag = 16705 then (ArmSettingsUpdateResponse.decode bytes).map fun (message, rest) => (.armSettingsUpdateResponse message, rest)
  else if tag = 12883 then (Arm2UnderlyingLevelProtectionSettingsUpdateRequest.decode bytes).map fun (message, rest) => (.arm2UnderlyingLevelProtectionSettingsUpdateRequest message, rest)
  else if tag = 12882 then (Arm2UnderlyingLevelProtectionSettingsUpdateResponse.decode bytes).map fun (message, rest) => (.arm2UnderlyingLevelProtectionSettingsUpdateResponse message, rest)
  else if tag = 20813 then (BulkQuoteMessage.decode bytes).map fun (message, rest) => (.bulkQuoteMessage message, rest)
  else if tag = 20818 then (BulkQuoteResponse.decode bytes).map fun (message, rest) => (.bulkQuoteResponse message, rest)
  else if tag = 17745 then (EnhancedQuoteEQuoteMessage.decode bytes).map fun (message, rest) => (.enhancedQuoteEQuoteMessage message, rest)
  else if tag = 22609 then (MassQuoteCancelRequest.decode bytes).map fun (message, rest) => (.massQuoteCancelRequest message, rest)
  else if tag = 22610 then (MassQuoteCancelResponse.decode bytes).map fun (message, rest) => (.massQuoteCancelResponse message, rest)
  else if tag = 20568 then (QuoteProtectionResetRequest.decode bytes).map fun (message, rest) => (.quoteProtectionResetRequest message, rest)
  else if tag = 20562 then (QuoteProtectionResetResponse.decode bytes).map fun (message, rest) => (.quoteProtectionResetResponse message, rest)
  else if tag = 20816 then (QuoteProtectionTriggerNotification.decode bytes).map fun (message, rest) => (.quoteProtectionTriggerNotification message, rest)
  else if tag = 22606 then (CancelNotification.decode bytes).map fun (message, rest) => (.cancelNotification message, rest)
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
theorem encode_length_le (message : UnsequencedDataPacket) : (encode message).length ≤ 3326 := by
  unfold encode
  cases message.unsequencedMessage with
  | armSettingsUpdateRequest inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, ArmSettingsUpdateRequest.encode_length]
    omega
  | armSettingsUpdateResponse inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, ArmSettingsUpdateResponse.encode_length]
    omega
  | arm2UnderlyingLevelProtectionSettingsUpdateRequest inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, Arm2UnderlyingLevelProtectionSettingsUpdateRequest.encode_length]
    omega
  | arm2UnderlyingLevelProtectionSettingsUpdateResponse inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, Arm2UnderlyingLevelProtectionSettingsUpdateResponse.encode_length]
    omega
  | bulkQuoteMessage inner =>
    have bound_inner := BulkQuoteMessage.encode_length_le inner
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length]
    omega
  | bulkQuoteResponse inner =>
    have bound_inner := BulkQuoteResponse.encode_length_le inner
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length]
    omega
  | enhancedQuoteEQuoteMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, EnhancedQuoteEQuoteMessage.encode_length]
    omega
  | massQuoteCancelRequest inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, MassQuoteCancelRequest.encode_length]
    omega
  | massQuoteCancelResponse inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, MassQuoteCancelResponse.encode_length]
    omega
  | quoteProtectionResetRequest inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, QuoteProtectionResetRequest.encode_length]
    omega
  | quoteProtectionResetResponse inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, QuoteProtectionResetResponse.encode_length]
    omega
  | quoteProtectionTriggerNotification inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, QuoteProtectionTriggerNotification.encode_length]
    omega
  | cancelNotification inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, CancelNotification.encode_length]
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
  logoutText : Capped 62208
  deriving DecidableEq, Repr

namespace LogoutRequest

def encode (message : LogoutRequest) : List UInt8 :=
  LogoutReason.encode message.logoutReason
    ++ (message.logoutText.val)

def decode (bytes : List UInt8) : Option LogoutRequest := do
  let (logoutReason, bytes) ← LogoutReason.decode bytes
  let logoutText_ := bytes
  if fits_logoutText : logoutText_.length ≤ 62208 then
    pure { logoutReason, logoutText := ⟨logoutText_, fits_logoutText⟩ }
  else none

theorem encode_length_pos (message : LogoutRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [LogoutReason.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : LogoutRequest) : (encode message).length ≤ 62209 := by
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
  logoutText : Capped 62208
  deriving DecidableEq, Repr

namespace GoodbyePacket

def encode (message : GoodbyePacket) : List UInt8 :=
  GoodbyeReason.encode message.goodbyeReason
    ++ (message.logoutText.val)

def decode (bytes : List UInt8) : Option GoodbyePacket := do
  let (goodbyeReason, bytes) ← GoodbyeReason.decode bytes
  let logoutText_ := bytes
  if fits_logoutText : logoutText_.length ≤ 62208 then
    pure { goodbyeReason, logoutText := ⟨logoutText_, fits_logoutText⟩ }
  else none

theorem encode_length_pos (message : GoodbyePacket) : (encode message).length > 0 := by
  unfold encode
  simp only [GoodbyeReason.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : GoodbyePacket) : (encode message).length ≤ 62209 := by
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
  testText : Capped 62208
  deriving DecidableEq, Repr

namespace TestPacket

def encode (message : TestPacket) : List UInt8 :=
  message.testText.val

def decode (bytes : List UInt8) : Option TestPacket := do
  let testText_ := bytes
  if fits_testText : testText_.length ≤ 62208 then
    pure { testText := ⟨testText_, fits_testText⟩ }
  else none

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TestPacket) : (encode message).length ≤ 62208 := by
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
theorem encode_length_le (message : SesmPayload) : (encode message).length ≤ 62209 := by
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

end Omi.MiaxMiaxoptionsExpressinterfaceMeiV18
