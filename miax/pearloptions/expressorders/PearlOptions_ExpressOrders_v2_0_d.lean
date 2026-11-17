import Wire

/-!
# Miami International Holdings Express Orders v2.0.d

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

namespace Omi.MiaxPearloptionsExpressordersMeoV20D

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
  | pearlWillAcceptPositionClosingOrdersOnly -- Pearl Will Accept Position Closing Orders Only
  | pearlWillAcceptOpenAndClosePositions -- Pearl Will Accept Open And Close Positions
  | unlisted (byte : { byte : UInt8 // byte ∉ RestrictedOption.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RestrictedOption

def toByte : RestrictedOption → UInt8
  | .pearlWillAcceptPositionClosingOrdersOnly => 0x59
  | .pearlWillAcceptOpenAndClosePositions => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RestrictedOption :=
  if byte = 0x59 then .pearlWillAcceptPositionClosingOrdersOnly
  else .pearlWillAcceptOpenAndClosePositions

def ofByte (byte : UInt8) : RestrictedOption :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RestrictedOption) : ofByte value.toByte = value := by
  cases value with
  | pearlWillAcceptPositionClosingOrdersOnly => decide
  | pearlWillAcceptOpenAndClosePositions => decide
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
  | farMonthExpirationAsDefinedByPearlRules -- Far Month Expiration As Defined By Pearl Rules
  | nearMonthExpirationAsDefinedByPearlRules -- Near Month Expiration As Defined By Pearl Rules
  | unlisted (byte : { byte : UInt8 // byte ∉ LongTermOption.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LongTermOption

def toByte : LongTermOption → UInt8
  | .farMonthExpirationAsDefinedByPearlRules => 0x59
  | .nearMonthExpirationAsDefinedByPearlRules => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LongTermOption :=
  if byte = 0x59 then .farMonthExpirationAsDefinedByPearlRules
  else .nearMonthExpirationAsDefinedByPearlRules

def ofByte (byte : UInt8) : LongTermOption :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LongTermOption) : ofByte value.toByte = value := by
  cases value with
  | farMonthExpirationAsDefinedByPearlRules => decide
  | nearMonthExpirationAsDefinedByPearlRules => decide
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

/-- Active On Pearl: one byte code -/
def ActiveOnPearl.codes : List UInt8 :=
  [0x41, 0x49]

inductive ActiveOnPearl where
  | activeTradableOnPearl -- Active Tradable On Pearl
  | inactiveNotTradableOnPearl -- Inactive Not Tradable On Pearl
  | unlisted (byte : { byte : UInt8 // byte ∉ ActiveOnPearl.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ActiveOnPearl

def toByte : ActiveOnPearl → UInt8
  | .activeTradableOnPearl => 0x41
  | .inactiveNotTradableOnPearl => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ActiveOnPearl :=
  if byte = 0x41 then .activeTradableOnPearl
  else .inactiveNotTradableOnPearl

def ofByte (byte : UInt8) : ActiveOnPearl :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ActiveOnPearl) : ofByte value.toByte = value := by
  cases value with
  | activeTradableOnPearl => decide
  | inactiveNotTradableOnPearl => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ActiveOnPearl) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ActiveOnPearl × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ActiveOnPearl) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ActiveOnPearl) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ActiveOnPearl) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ActiveOnPearl

/-- Pearl Bbo Posting Increment Indicator: one byte code -/
def PearlBboPostingIncrementIndicator.codes : List UInt8 :=
  [0x50, 0x4E, 0x44]

inductive PearlBboPostingIncrementIndicator where
  | pennyPenny -- Penny Penny
  | pennyNickel -- Penny Nickel
  | nickelDime -- Nickel Dime
  | unlisted (byte : { byte : UInt8 // byte ∉ PearlBboPostingIncrementIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PearlBboPostingIncrementIndicator

def toByte : PearlBboPostingIncrementIndicator → UInt8
  | .pennyPenny => 0x50
  | .pennyNickel => 0x4E
  | .nickelDime => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PearlBboPostingIncrementIndicator :=
  if byte = 0x50 then .pennyPenny
  else if byte = 0x4E then .pennyNickel
  else .nickelDime

def ofByte (byte : UInt8) : PearlBboPostingIncrementIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PearlBboPostingIncrementIndicator) : ofByte value.toByte = value := by
  cases value with
  | pennyPenny => decide
  | pennyNickel => decide
  | nickelDime => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PearlBboPostingIncrementIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PearlBboPostingIncrementIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PearlBboPostingIncrementIndicator) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : PearlBboPostingIncrementIndicator) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : PearlBboPostingIncrementIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PearlBboPostingIncrementIndicator

/-- Order Acceptance Increment Indicator: one byte code -/
def OrderAcceptanceIncrementIndicator.codes : List UInt8 :=
  [0x50, 0x4E, 0x44]

inductive OrderAcceptanceIncrementIndicator where
  | pennyPenny -- Penny Penny
  | pennyNickel -- Penny Nickel
  | nickelDime -- Nickel Dime
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderAcceptanceIncrementIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderAcceptanceIncrementIndicator

def toByte : OrderAcceptanceIncrementIndicator → UInt8
  | .pennyPenny => 0x50
  | .pennyNickel => 0x4E
  | .nickelDime => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderAcceptanceIncrementIndicator :=
  if byte = 0x50 then .pennyPenny
  else if byte = 0x4E then .pennyNickel
  else .nickelDime

def ofByte (byte : UInt8) : OrderAcceptanceIncrementIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderAcceptanceIncrementIndicator) : ofByte value.toByte = value := by
  cases value with
  | pennyPenny => decide
  | pennyNickel => decide
  | nickelDime => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderAcceptanceIncrementIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderAcceptanceIncrementIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderAcceptanceIncrementIndicator) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OrderAcceptanceIncrementIndicator) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OrderAcceptanceIncrementIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderAcceptanceIncrementIndicator

/-- Opening Underlying Market Code: one byte code -/
def OpeningUnderlyingMarketCode.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x45, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x50, 0x51, 0x54, 0x55, 0x56, 0x57, 0x58, 0x59, 0x5A]

inductive OpeningUnderlyingMarketCode where
  | nyseAmex -- Nyse Amex
  | nasdaqOmxBx -- Nasdaq Omx Bx
  | nationalStockExchange -- National Stock Exchange
  | finraAdf -- Finra Adf
  | marketIndependent -- Market Independent
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
  | .marketIndependent => 0x45
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
  else if byte = 0x45 then .marketIndependent
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
  | marketIndependent => decide
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

/-- System Status: one byte code -/
def SystemStatus.codes : List UInt8 :=
  [0x53, 0x43, 0x50, 0x4C, 0x4D, 0x45, 0x31, 0x32]

inductive SystemStatus where
  | startOfSystemHours -- Start Of System Hours
  | endOfSystemHours -- End Of System Hours
  | low -- Low
  | notInLow -- Not In Low
  | mpidProductAssignmentWindowOpen -- Mpid Product Assignment Window Open
  | mpidProductAssignmentWindowClosed -- Mpid Product Assignment Window Closed
  | startOfTestSession -- Start Of Test Session
  | endOfTestSession -- End Of Test Session
  | unlisted (byte : { byte : UInt8 // byte ∉ SystemStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SystemStatus

def toByte : SystemStatus → UInt8
  | .startOfSystemHours => 0x53
  | .endOfSystemHours => 0x43
  | .low => 0x50
  | .notInLow => 0x4C
  | .mpidProductAssignmentWindowOpen => 0x4D
  | .mpidProductAssignmentWindowClosed => 0x45
  | .startOfTestSession => 0x31
  | .endOfTestSession => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SystemStatus :=
  if byte = 0x53 then .startOfSystemHours
  else if byte = 0x43 then .endOfSystemHours
  else if byte = 0x50 then .low
  else if byte = 0x4C then .notInLow
  else if byte = 0x4D then .mpidProductAssignmentWindowOpen
  else if byte = 0x45 then .mpidProductAssignmentWindowClosed
  else if byte = 0x31 then .startOfTestSession
  else .endOfTestSession

def ofByte (byte : UInt8) : SystemStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SystemStatus) : ofByte value.toByte = value := by
  cases value with
  | startOfSystemHours => decide
  | endOfSystemHours => decide
  | low => decide
  | notInLow => decide
  | mpidProductAssignmentWindowOpen => decide
  | mpidProductAssignmentWindowClosed => decide
  | startOfTestSession => decide
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
  [0x48, 0x52, 0x4F]

inductive TradingStatus where
  | pearlHasHaltedTradingForThisUnderlyingSymbol -- Pearl Has Halted Trading For This Underlying Symbol
  | pearlWillResumeTradingReopenForThisUnderlyingSymbol -- Pearl Will Resume Trading Reopen For This Underlying Symbol
  | pearlWillOpenTradingForThisUnderlyingSymbol -- Pearl Will Open Trading For This Underlying Symbol
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingStatus

def toByte : TradingStatus → UInt8
  | .pearlHasHaltedTradingForThisUnderlyingSymbol => 0x48
  | .pearlWillResumeTradingReopenForThisUnderlyingSymbol => 0x52
  | .pearlWillOpenTradingForThisUnderlyingSymbol => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingStatus :=
  if byte = 0x48 then .pearlHasHaltedTradingForThisUnderlyingSymbol
  else if byte = 0x52 then .pearlWillResumeTradingReopenForThisUnderlyingSymbol
  else .pearlWillOpenTradingForThisUnderlyingSymbol

def ofByte (byte : UInt8) : TradingStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingStatus) : ofByte value.toByte = value := by
  cases value with
  | pearlHasHaltedTradingForThisUnderlyingSymbol => decide
  | pearlWillResumeTradingReopenForThisUnderlyingSymbol => decide
  | pearlWillOpenTradingForThisUnderlyingSymbol => decide
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
  | pearlManuallyInitiatedThisEvent -- Pearl Manually Initiated This Event
  | unlisted (byte : { byte : UInt8 // byte ∉ EventReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventReason

def toByte : EventReason → UInt8
  | .thisEventResultedFromAutomaticmarketDrivenEvent => 0x41
  | .pearlManuallyInitiatedThisEvent => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventReason :=
  if byte = 0x41 then .thisEventResultedFromAutomaticmarketDrivenEvent
  else .pearlManuallyInitiatedThisEvent

def ofByte (byte : UInt8) : EventReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventReason) : ofByte value.toByte = value := by
  cases value with
  | thisEventResultedFromAutomaticmarketDrivenEvent => decide
  | pearlManuallyInitiatedThisEvent => decide
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
  [0x53, 0x44, 0x41, 0x55]

inductive Action where
  | set -- Set
  | delete -- Delete
  | assign -- Assign
  | unassign -- Unassign
  | unlisted (byte : { byte : UInt8 // byte ∉ Action.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Action

def toByte : Action → UInt8
  | .set => 0x53
  | .delete => 0x44
  | .assign => 0x41
  | .unassign => 0x55
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Action :=
  if byte = 0x53 then .set
  else if byte = 0x44 then .delete
  else if byte = 0x41 then .assign
  else .unassign

def ofByte (byte : UInt8) : Action :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Action) : ofByte value.toByte = value := by
  cases value with
  | set => decide
  | delete => decide
  | assign => decide
  | unassign => decide
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
  | changesCarriedOutByTheFirmViaMeo -- Changes Carried Out By The Firm Via Meo
  | changesCarriedOutByTheExchange -- Changes Carried Out By The Exchange
  | unlisted (byte : { byte : UInt8 // byte ∉ Source.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Source

def toByte : Source → UInt8
  | .changesCarriedOutByTheFirmViaMeo => 0x54
  | .changesCarriedOutByTheExchange => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Source :=
  if byte = 0x54 then .changesCarriedOutByTheFirmViaMeo
  else .changesCarriedOutByTheExchange

def ofByte (byte : UInt8) : Source :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Source) : ofByte value.toByte = value := by
  cases value with
  | changesCarriedOutByTheFirmViaMeo => decide
  | changesCarriedOutByTheExchange => decide
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

/-- Side: one byte code -/
def Side.codes : List UInt8 :=
  [0x42, 0x53, 0x4E]

inductive Side where
  | buy -- Buy
  | sell -- Sell
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .notApplicable => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x42 then .buy
  else if byte = 0x53 then .sell
  else .notApplicable

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | notApplicable => decide
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
  | triggered -- Triggered
  | reset -- Reset
  | downgradedFromOlderVersion -- Downgraded From Older Version
  | unlisted (byte : { byte : UInt8 // byte ∉ NotificationType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace NotificationType

def toByte : NotificationType → UInt8
  | .triggered => 0x54
  | .reset => 0x52
  | .downgradedFromOlderVersion => 0x2A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : NotificationType :=
  if byte = 0x54 then .triggered
  else if byte = 0x52 then .reset
  else .downgradedFromOlderVersion

def ofByte (byte : UInt8) : NotificationType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : NotificationType) : ofByte value.toByte = value := by
  cases value with
  | triggered => decide
  | reset => decide
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
  [0x4F, 0x58]

inductive LiquidityType where
  | binaryOrder -- Binary Order
  | reservedForFutureUse -- Reserved For Future Use
  | unlisted (byte : { byte : UInt8 // byte ∉ LiquidityType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LiquidityType

def toByte : LiquidityType → UInt8
  | .binaryOrder => 0x4F
  | .reservedForFutureUse => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LiquidityType :=
  if byte = 0x4F then .binaryOrder
  else .reservedForFutureUse

def ofByte (byte : UInt8) : LiquidityType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LiquidityType) : ofByte value.toByte = value := by
  cases value with
  | binaryOrder => decide
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

/-- Cancel Reason: one byte code -/
def CancelReason.codes : List UInt8 :=
  [0x4C, 0x42, 0x55, 0x52, 0x4F, 0x54, 0x46, 0x41, 0x43, 0x44, 0x4A, 0x4D, 0x50, 0x53, 0x51, 0x5A, 0x2A]

inductive CancelReason where
  | lineDisconnectTriggeredProtectionMassCancel -- Line Disconnect Triggered Protection Mass Cancel
  | pearlHelpDeskInitiatedCancel -- Pearl Help Desk Initiated Cancel
  | firmInitiatedMassCancel -- Firm Initiated Mass Cancel
  | pearlInitiatedMassCancelDueToArmProtection -- Pearl Initiated Mass Cancel Due To Arm Protection
  | rpmBinaryOrderRateProtectionTriggerMassCancel -- Rpm Binary Order Rate Protection Trigger Mass Cancel
  | rpmBinaryOrderExecutedContractsRateProtectionTriggerMassCancel -- Rpm Binary Order Executed Contracts Rate Protection Trigger Mass Cancel
  | arm2FirmLevelProtectionInitiatedMassCancel -- Arm 2 Firm Level Protection Initiated Mass Cancel
  | priceProtectionCanceled -- Price Protection Canceled
  | cancelOfRestingOrderCrossedByOppositeSideOrderOfSameMpidOrFirm -- Cancel Of Resting Order Crossed By Opposite Side Order Of Same Mpid Or Firm
  | luldCanceled -- Luld Canceled
  | canceledByUserWithCancelOrReplaceRequest -- Canceled By User With Cancel Or Replace Request
  | canceledDueToReplaceRequestWhileBlockedByRpmProtection -- Canceled Due To Replace Request While Blocked By Rpm Protection
  | postOnlyCanceledDueToLockingOrCrossingManagedInterestOnTheOppositeSide -- Post Only Canceled Due To Locking Or Crossing Managed Interest On The Opposite Side
  | cancelForUnexecutedPartOfOrder -- Cancel For Unexecuted Part Of Order
  | canceledDueToSingleSideLiquidityProtectionTrigger -- Canceled Due To Single Side Liquidity Protection Trigger
  | undefinedReason -- Undefined Reason
  | downgradedFromOlderVersion -- Downgraded From Older Version
  | unlisted (byte : { byte : UInt8 // byte ∉ CancelReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CancelReason

def toByte : CancelReason → UInt8
  | .lineDisconnectTriggeredProtectionMassCancel => 0x4C
  | .pearlHelpDeskInitiatedCancel => 0x42
  | .firmInitiatedMassCancel => 0x55
  | .pearlInitiatedMassCancelDueToArmProtection => 0x52
  | .rpmBinaryOrderRateProtectionTriggerMassCancel => 0x4F
  | .rpmBinaryOrderExecutedContractsRateProtectionTriggerMassCancel => 0x54
  | .arm2FirmLevelProtectionInitiatedMassCancel => 0x46
  | .priceProtectionCanceled => 0x41
  | .cancelOfRestingOrderCrossedByOppositeSideOrderOfSameMpidOrFirm => 0x43
  | .luldCanceled => 0x44
  | .canceledByUserWithCancelOrReplaceRequest => 0x4A
  | .canceledDueToReplaceRequestWhileBlockedByRpmProtection => 0x4D
  | .postOnlyCanceledDueToLockingOrCrossingManagedInterestOnTheOppositeSide => 0x50
  | .cancelForUnexecutedPartOfOrder => 0x53
  | .canceledDueToSingleSideLiquidityProtectionTrigger => 0x51
  | .undefinedReason => 0x5A
  | .downgradedFromOlderVersion => 0x2A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CancelReason :=
  if byte = 0x4C then .lineDisconnectTriggeredProtectionMassCancel
  else if byte = 0x42 then .pearlHelpDeskInitiatedCancel
  else if byte = 0x55 then .firmInitiatedMassCancel
  else if byte = 0x52 then .pearlInitiatedMassCancelDueToArmProtection
  else if byte = 0x4F then .rpmBinaryOrderRateProtectionTriggerMassCancel
  else if byte = 0x54 then .rpmBinaryOrderExecutedContractsRateProtectionTriggerMassCancel
  else if byte = 0x46 then .arm2FirmLevelProtectionInitiatedMassCancel
  else if byte = 0x41 then .priceProtectionCanceled
  else if byte = 0x43 then .cancelOfRestingOrderCrossedByOppositeSideOrderOfSameMpidOrFirm
  else if byte = 0x44 then .luldCanceled
  else if byte = 0x4A then .canceledByUserWithCancelOrReplaceRequest
  else if byte = 0x4D then .canceledDueToReplaceRequestWhileBlockedByRpmProtection
  else if byte = 0x50 then .postOnlyCanceledDueToLockingOrCrossingManagedInterestOnTheOppositeSide
  else if byte = 0x53 then .cancelForUnexecutedPartOfOrder
  else if byte = 0x51 then .canceledDueToSingleSideLiquidityProtectionTrigger
  else if byte = 0x5A then .undefinedReason
  else .downgradedFromOlderVersion

def ofByte (byte : UInt8) : CancelReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CancelReason) : ofByte value.toByte = value := by
  cases value with
  | lineDisconnectTriggeredProtectionMassCancel => decide
  | pearlHelpDeskInitiatedCancel => decide
  | firmInitiatedMassCancel => decide
  | pearlInitiatedMassCancelDueToArmProtection => decide
  | rpmBinaryOrderRateProtectionTriggerMassCancel => decide
  | rpmBinaryOrderExecutedContractsRateProtectionTriggerMassCancel => decide
  | arm2FirmLevelProtectionInitiatedMassCancel => decide
  | priceProtectionCanceled => decide
  | cancelOfRestingOrderCrossedByOppositeSideOrderOfSameMpidOrFirm => decide
  | luldCanceled => decide
  | canceledByUserWithCancelOrReplaceRequest => decide
  | canceledDueToReplaceRequestWhileBlockedByRpmProtection => decide
  | postOnlyCanceledDueToLockingOrCrossingManagedInterestOnTheOppositeSide => decide
  | cancelForUnexecutedPartOfOrder => decide
  | canceledDueToSingleSideLiquidityProtectionTrigger => decide
  | undefinedReason => decide
  | downgradedFromOlderVersion => decide
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

/-- Liquidity Indicator: one byte code -/
def LiquidityIndicator.codes : List UInt8 :=
  [0x4D, 0x54, 0x20, 0x2A]

inductive LiquidityIndicator where
  | maker -- Maker
  | taker -- Taker
  | na -- Na
  | downgradedForOlderVersion -- Downgraded For Older Version
  | unlisted (byte : { byte : UInt8 // byte ∉ LiquidityIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LiquidityIndicator

def toByte : LiquidityIndicator → UInt8
  | .maker => 0x4D
  | .taker => 0x54
  | .na => 0x20
  | .downgradedForOlderVersion => 0x2A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LiquidityIndicator :=
  if byte = 0x4D then .maker
  else if byte = 0x54 then .taker
  else if byte = 0x20 then .na
  else .downgradedForOlderVersion

def ofByte (byte : UInt8) : LiquidityIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LiquidityIndicator) : ofByte value.toByte = value := by
  cases value with
  | maker => decide
  | taker => decide
  | na => decide
  | downgradedForOlderVersion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LiquidityIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LiquidityIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LiquidityIndicator) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : LiquidityIndicator) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : LiquidityIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LiquidityIndicator

/-- Arm Settings Update Status: one byte code -/
def ArmSettingsUpdateStatus.codes : List UInt8 :=
  [0x20, 0x41, 0x50, 0x44, 0x4D, 0x55, 0x4E, 0x5A, 0x2A]

inductive ArmSettingsUpdateStatus where
  | settingsAppliedSuccessfully -- Settings Applied Successfully
  | invalidAction -- Invalid Action
  | invalidAllowableEngagementPercentage -- Invalid Allowable Engagement Percentage
  | invalidCountingPeriod -- Invalid Counting Period
  | unknownMpid -- Unknown Mpid
  | invalidUnderlying -- Invalid Underlying
  | noSuchArmSettings -- No Such Arm Settings
  | undefinedError -- Undefined Error
  | downgradedFromOlderVersion -- Downgraded From Older Version
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
  | .noSuchArmSettings => 0x4E
  | .undefinedError => 0x5A
  | .downgradedFromOlderVersion => 0x2A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ArmSettingsUpdateStatus :=
  if byte = 0x20 then .settingsAppliedSuccessfully
  else if byte = 0x41 then .invalidAction
  else if byte = 0x50 then .invalidAllowableEngagementPercentage
  else if byte = 0x44 then .invalidCountingPeriod
  else if byte = 0x4D then .unknownMpid
  else if byte = 0x55 then .invalidUnderlying
  else if byte = 0x4E then .noSuchArmSettings
  else if byte = 0x5A then .undefinedError
  else .downgradedFromOlderVersion

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
  | noSuchArmSettings => decide
  | undefinedError => decide
  | downgradedFromOlderVersion => decide
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

/-- Arm 2 Settings Update Status: one byte code -/
def Arm2SettingsUpdateStatus.codes : List UInt8 :=
  [0x20, 0x41, 0x50, 0x44, 0x49, 0x4D, 0x55, 0x4E, 0x5A, 0x2A]

inductive Arm2SettingsUpdateStatus where
  | settingsAppliedSuccessfully -- Settings Applied Successfully
  | invalidAction -- Invalid Action
  | invalidArmThreshold -- Invalid Arm Threshold
  | invalidCountingPeriod -- Invalid Counting Period
  | invalidForEemMpid -- Invalid For Eem Mpid
  | unknownMpid -- Unknown Mpid
  | invalidUnderlying -- Invalid Underlying
  | noSuchArm2Setting -- No Such Arm 2 Setting
  | undefinedError -- Undefined Error
  | downgradedFromOlderVersion -- Downgraded From Older Version
  | unlisted (byte : { byte : UInt8 // byte ∉ Arm2SettingsUpdateStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Arm2SettingsUpdateStatus

def toByte : Arm2SettingsUpdateStatus → UInt8
  | .settingsAppliedSuccessfully => 0x20
  | .invalidAction => 0x41
  | .invalidArmThreshold => 0x50
  | .invalidCountingPeriod => 0x44
  | .invalidForEemMpid => 0x49
  | .unknownMpid => 0x4D
  | .invalidUnderlying => 0x55
  | .noSuchArm2Setting => 0x4E
  | .undefinedError => 0x5A
  | .downgradedFromOlderVersion => 0x2A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Arm2SettingsUpdateStatus :=
  if byte = 0x20 then .settingsAppliedSuccessfully
  else if byte = 0x41 then .invalidAction
  else if byte = 0x50 then .invalidArmThreshold
  else if byte = 0x44 then .invalidCountingPeriod
  else if byte = 0x49 then .invalidForEemMpid
  else if byte = 0x4D then .unknownMpid
  else if byte = 0x55 then .invalidUnderlying
  else if byte = 0x4E then .noSuchArm2Setting
  else if byte = 0x5A then .undefinedError
  else .downgradedFromOlderVersion

def ofByte (byte : UInt8) : Arm2SettingsUpdateStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Arm2SettingsUpdateStatus) : ofByte value.toByte = value := by
  cases value with
  | settingsAppliedSuccessfully => decide
  | invalidAction => decide
  | invalidArmThreshold => decide
  | invalidCountingPeriod => decide
  | invalidForEemMpid => decide
  | unknownMpid => decide
  | invalidUnderlying => decide
  | noSuchArm2Setting => decide
  | undefinedError => decide
  | downgradedFromOlderVersion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Arm2SettingsUpdateStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Arm2SettingsUpdateStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Arm2SettingsUpdateStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Arm2SettingsUpdateStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Arm2SettingsUpdateStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Arm2SettingsUpdateStatus

/-- Assignment Settings Status: one byte code -/
def AssignmentSettingsStatus.codes : List UInt8 :=
  [0x20, 0x41, 0x4D, 0x45, 0x54, 0x49, 0x50, 0x5A, 0x2A]

inductive AssignmentSettingsStatus where
  | settingsAppliedSuccessfully -- Settings Applied Successfully
  | invalidAction -- Invalid Action
  | unknownMpid -- Unknown Mpid
  | invalidRequestForEemMpid -- Invalid Request For Eem Mpid
  | settingsNotPermitted -- Settings Not Permitted
  | invalidProductCode -- Invalid Product Code
  | assignmentCannotBeForPutOptions -- Assignment Cannot Be For Put Options
  | undefinedError -- Undefined Error
  | downgradedFromOlderVersion -- Downgraded From Older Version
  | unlisted (byte : { byte : UInt8 // byte ∉ AssignmentSettingsStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AssignmentSettingsStatus

def toByte : AssignmentSettingsStatus → UInt8
  | .settingsAppliedSuccessfully => 0x20
  | .invalidAction => 0x41
  | .unknownMpid => 0x4D
  | .invalidRequestForEemMpid => 0x45
  | .settingsNotPermitted => 0x54
  | .invalidProductCode => 0x49
  | .assignmentCannotBeForPutOptions => 0x50
  | .undefinedError => 0x5A
  | .downgradedFromOlderVersion => 0x2A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AssignmentSettingsStatus :=
  if byte = 0x20 then .settingsAppliedSuccessfully
  else if byte = 0x41 then .invalidAction
  else if byte = 0x4D then .unknownMpid
  else if byte = 0x45 then .invalidRequestForEemMpid
  else if byte = 0x54 then .settingsNotPermitted
  else if byte = 0x49 then .invalidProductCode
  else if byte = 0x50 then .assignmentCannotBeForPutOptions
  else if byte = 0x5A then .undefinedError
  else .downgradedFromOlderVersion

def ofByte (byte : UInt8) : AssignmentSettingsStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AssignmentSettingsStatus) : ofByte value.toByte = value := by
  cases value with
  | settingsAppliedSuccessfully => decide
  | invalidAction => decide
  | unknownMpid => decide
  | invalidRequestForEemMpid => decide
  | settingsNotPermitted => decide
  | invalidProductCode => decide
  | assignmentCannotBeForPutOptions => decide
  | undefinedError => decide
  | downgradedFromOlderVersion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AssignmentSettingsStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AssignmentSettingsStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AssignmentSettingsStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : AssignmentSettingsStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : AssignmentSettingsStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AssignmentSettingsStatus

/-- Self Trade Protection Status: one byte code -/
def SelfTradeProtectionStatus.codes : List UInt8 :=
  [0x20, 0x4D, 0x45, 0x41, 0x5A, 0x2A]

inductive SelfTradeProtectionStatus where
  | settingsAppliedSuccessfully -- Settings Applied Successfully
  | unknownMpid -- Unknown Mpid
  | invalidForMmMpid -- Invalid For Mm Mpid
  | invalidAction -- Invalid Action
  | undefinedError -- Undefined Error
  | downgradedFromOlderVersion -- Downgraded From Older Version
  | unlisted (byte : { byte : UInt8 // byte ∉ SelfTradeProtectionStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SelfTradeProtectionStatus

def toByte : SelfTradeProtectionStatus → UInt8
  | .settingsAppliedSuccessfully => 0x20
  | .unknownMpid => 0x4D
  | .invalidForMmMpid => 0x45
  | .invalidAction => 0x41
  | .undefinedError => 0x5A
  | .downgradedFromOlderVersion => 0x2A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SelfTradeProtectionStatus :=
  if byte = 0x20 then .settingsAppliedSuccessfully
  else if byte = 0x4D then .unknownMpid
  else if byte = 0x45 then .invalidForMmMpid
  else if byte = 0x41 then .invalidAction
  else if byte = 0x5A then .undefinedError
  else .downgradedFromOlderVersion

def ofByte (byte : UInt8) : SelfTradeProtectionStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SelfTradeProtectionStatus) : ofByte value.toByte = value := by
  cases value with
  | settingsAppliedSuccessfully => decide
  | unknownMpid => decide
  | invalidForMmMpid => decide
  | invalidAction => decide
  | undefinedError => decide
  | downgradedFromOlderVersion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SelfTradeProtectionStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SelfTradeProtectionStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SelfTradeProtectionStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SelfTradeProtectionStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SelfTradeProtectionStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SelfTradeProtectionStatus

/-- Bulk Order Status: one byte code -/
def BulkOrderStatus.codes : List UInt8 :=
  [0x20, 0x52, 0x5A]

inductive BulkOrderStatus where
  | bulkLiquidityBlockIsValid -- Bulk Liquidity Block Is Valid
  | invalidBulkLiquidityBlock -- Invalid Bulk Liquidity Block
  | undefinedError -- Undefined Error
  | unlisted (byte : { byte : UInt8 // byte ∉ BulkOrderStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BulkOrderStatus

def toByte : BulkOrderStatus → UInt8
  | .bulkLiquidityBlockIsValid => 0x20
  | .invalidBulkLiquidityBlock => 0x52
  | .undefinedError => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BulkOrderStatus :=
  if byte = 0x20 then .bulkLiquidityBlockIsValid
  else if byte = 0x52 then .invalidBulkLiquidityBlock
  else .undefinedError

def ofByte (byte : UInt8) : BulkOrderStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BulkOrderStatus) : ofByte value.toByte = value := by
  cases value with
  | bulkLiquidityBlockIsValid => decide
  | invalidBulkLiquidityBlock => decide
  | undefinedError => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BulkOrderStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BulkOrderStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BulkOrderStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : BulkOrderStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : BulkOrderStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BulkOrderStatus

/-- Order Status: one byte code -/
def OrderStatus.codes : List UInt8 :=
  [0x20, 0x41, 0x42, 0x43, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4E, 0x4F, 0x50, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58, 0x59, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x30, 0x61, 0x62, 0x63, 0x65, 0x66, 0x67, 0x68, 0x73, 0x74, 0x5A, 0x2A]

inductive OrderStatus where
  | successfullyAccepted -- Successfully Accepted
  | marketOrderNotAcceptedDuringLuld -- Market Order Not Accepted During Luld
  | tooWideForSellMarketZeroBid -- Too Wide For Sell Market Zero Bid
  | pearlClosedForTradingOfThisProduct -- Pearl Closed For Trading Of This Product
  | marketTooWideToAcceptMarketOrder -- Market Too Wide To Accept Market Order
  | buySellLimitTooAggressive -- Buy Sell Limit Too Aggressive
  | maxOpenOrdersExceeded -- Max Open Orders Exceeded
  | maxOpenContractsExceeded -- Max Open Contracts Exceeded
  | invalidTifWhenOptionNotTrading -- Invalid Tif When Option Not Trading
  | invalidOrderInstructionWhenOptionNotTrading -- Invalid Order Instruction When Option Not Trading
  | noAROrderToCancel -- No A R Order To Cancel
  | orderReceivedWhileNotInLow -- Order Received While Not In Low
  | invalidClientOrderId -- Invalid Client Order Id
  | invalidProductId -- Invalid Product Id
  | invalidOrProtectedPrice -- Invalid Or Protected Price
  | invalidSize -- Invalid Size
  | rejectedDueToOrderProtection -- Rejected Due To Order Protection
  | invalidSide -- Invalid Side
  | invalidTargetClientOrderId -- Invalid Target Client Order Id
  | unknownMpid -- Unknown Mpid
  | invalidToChange -- Invalid To Change
  | invalidCancelRequest -- Invalid Cancel Request
  | notPermitted -- Not Permitted
  | invalidForMpid -- Invalid For Mpid
  | invalidOrigin -- Invalid Origin
  | invalidTif -- Invalid Tif
  | restrictedOption -- Restricted Option
  | nonTradableOption -- Non Tradable Option
  | incompatibleOrderType -- Incompatible Order Type
  | incompatibleTif -- Incompatible Tif
  | invalidOrderInstruction -- Invalid Order Instruction
  | invalidOpenClose -- Invalid Open Close
  | invalidCoveredUnCovered -- Invalid Covered Un Covered
  | invalidMvpTicks -- Invalid Mvp Ticks
  | invalidClearingAccount -- Invalid Clearing Account
  | blockedByOccKillSwitch -- Blocked By Occ Kill Switch
  | blockedByRpm -- Blocked By Rpm
  | duplicateClientOrderId -- Duplicate Client Order Id
  | invalidAccount -- Invalid Account
  | invalidLiquidityUnitType -- Invalid Liquidity Unit Type
  | invalidCmtaSpecified -- Invalid Cmta Specified
  | rejectedDueToSingleSideLiquidityProtectionInEffect -- Rejected Due To Single Side Liquidity Protection In Effect
  | invalidAdditionalText -- Invalid Additional Text
  | undefinedError -- Undefined Error
  | downgradedFromOlderVersion -- Downgraded From Older Version
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderStatus

def toByte : OrderStatus → UInt8
  | .successfullyAccepted => 0x20
  | .marketOrderNotAcceptedDuringLuld => 0x41
  | .tooWideForSellMarketZeroBid => 0x42
  | .pearlClosedForTradingOfThisProduct => 0x43
  | .marketTooWideToAcceptMarketOrder => 0x45
  | .buySellLimitTooAggressive => 0x46
  | .maxOpenOrdersExceeded => 0x47
  | .maxOpenContractsExceeded => 0x48
  | .invalidTifWhenOptionNotTrading => 0x49
  | .invalidOrderInstructionWhenOptionNotTrading => 0x4A
  | .noAROrderToCancel => 0x4B
  | .orderReceivedWhileNotInLow => 0x4C
  | .invalidClientOrderId => 0x4E
  | .invalidProductId => 0x4F
  | .invalidOrProtectedPrice => 0x50
  | .invalidSize => 0x51
  | .rejectedDueToOrderProtection => 0x52
  | .invalidSide => 0x53
  | .invalidTargetClientOrderId => 0x54
  | .unknownMpid => 0x55
  | .invalidToChange => 0x56
  | .invalidCancelRequest => 0x57
  | .notPermitted => 0x58
  | .invalidForMpid => 0x59
  | .invalidOrigin => 0x31
  | .invalidTif => 0x32
  | .restrictedOption => 0x33
  | .nonTradableOption => 0x34
  | .incompatibleOrderType => 0x35
  | .incompatibleTif => 0x36
  | .invalidOrderInstruction => 0x37
  | .invalidOpenClose => 0x38
  | .invalidCoveredUnCovered => 0x39
  | .invalidMvpTicks => 0x30
  | .invalidClearingAccount => 0x61
  | .blockedByOccKillSwitch => 0x62
  | .blockedByRpm => 0x63
  | .duplicateClientOrderId => 0x65
  | .invalidAccount => 0x66
  | .invalidLiquidityUnitType => 0x67
  | .invalidCmtaSpecified => 0x68
  | .rejectedDueToSingleSideLiquidityProtectionInEffect => 0x73
  | .invalidAdditionalText => 0x74
  | .undefinedError => 0x5A
  | .downgradedFromOlderVersion => 0x2A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderStatus :=
  if byte = 0x20 then .successfullyAccepted
  else if byte = 0x41 then .marketOrderNotAcceptedDuringLuld
  else if byte = 0x42 then .tooWideForSellMarketZeroBid
  else if byte = 0x43 then .pearlClosedForTradingOfThisProduct
  else if byte = 0x45 then .marketTooWideToAcceptMarketOrder
  else if byte = 0x46 then .buySellLimitTooAggressive
  else if byte = 0x47 then .maxOpenOrdersExceeded
  else if byte = 0x48 then .maxOpenContractsExceeded
  else if byte = 0x49 then .invalidTifWhenOptionNotTrading
  else if byte = 0x4A then .invalidOrderInstructionWhenOptionNotTrading
  else if byte = 0x4B then .noAROrderToCancel
  else if byte = 0x4C then .orderReceivedWhileNotInLow
  else if byte = 0x4E then .invalidClientOrderId
  else if byte = 0x4F then .invalidProductId
  else if byte = 0x50 then .invalidOrProtectedPrice
  else if byte = 0x51 then .invalidSize
  else if byte = 0x52 then .rejectedDueToOrderProtection
  else if byte = 0x53 then .invalidSide
  else if byte = 0x54 then .invalidTargetClientOrderId
  else if byte = 0x55 then .unknownMpid
  else if byte = 0x56 then .invalidToChange
  else if byte = 0x57 then .invalidCancelRequest
  else if byte = 0x58 then .notPermitted
  else if byte = 0x59 then .invalidForMpid
  else if byte = 0x31 then .invalidOrigin
  else if byte = 0x32 then .invalidTif
  else if byte = 0x33 then .restrictedOption
  else if byte = 0x34 then .nonTradableOption
  else if byte = 0x35 then .incompatibleOrderType
  else if byte = 0x36 then .incompatibleTif
  else if byte = 0x37 then .invalidOrderInstruction
  else if byte = 0x38 then .invalidOpenClose
  else if byte = 0x39 then .invalidCoveredUnCovered
  else if byte = 0x30 then .invalidMvpTicks
  else if byte = 0x61 then .invalidClearingAccount
  else if byte = 0x62 then .blockedByOccKillSwitch
  else if byte = 0x63 then .blockedByRpm
  else if byte = 0x65 then .duplicateClientOrderId
  else if byte = 0x66 then .invalidAccount
  else if byte = 0x67 then .invalidLiquidityUnitType
  else if byte = 0x68 then .invalidCmtaSpecified
  else if byte = 0x73 then .rejectedDueToSingleSideLiquidityProtectionInEffect
  else if byte = 0x74 then .invalidAdditionalText
  else if byte = 0x5A then .undefinedError
  else .downgradedFromOlderVersion

def ofByte (byte : UInt8) : OrderStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderStatus) : ofByte value.toByte = value := by
  cases value with
  | successfullyAccepted => decide
  | marketOrderNotAcceptedDuringLuld => decide
  | tooWideForSellMarketZeroBid => decide
  | pearlClosedForTradingOfThisProduct => decide
  | marketTooWideToAcceptMarketOrder => decide
  | buySellLimitTooAggressive => decide
  | maxOpenOrdersExceeded => decide
  | maxOpenContractsExceeded => decide
  | invalidTifWhenOptionNotTrading => decide
  | invalidOrderInstructionWhenOptionNotTrading => decide
  | noAROrderToCancel => decide
  | orderReceivedWhileNotInLow => decide
  | invalidClientOrderId => decide
  | invalidProductId => decide
  | invalidOrProtectedPrice => decide
  | invalidSize => decide
  | rejectedDueToOrderProtection => decide
  | invalidSide => decide
  | invalidTargetClientOrderId => decide
  | unknownMpid => decide
  | invalidToChange => decide
  | invalidCancelRequest => decide
  | notPermitted => decide
  | invalidForMpid => decide
  | invalidOrigin => decide
  | invalidTif => decide
  | restrictedOption => decide
  | nonTradableOption => decide
  | incompatibleOrderType => decide
  | incompatibleTif => decide
  | invalidOrderInstruction => decide
  | invalidOpenClose => decide
  | invalidCoveredUnCovered => decide
  | invalidMvpTicks => decide
  | invalidClearingAccount => decide
  | blockedByOccKillSwitch => decide
  | blockedByRpm => decide
  | duplicateClientOrderId => decide
  | invalidAccount => decide
  | invalidLiquidityUnitType => decide
  | invalidCmtaSpecified => decide
  | rejectedDueToSingleSideLiquidityProtectionInEffect => decide
  | invalidAdditionalText => decide
  | undefinedError => decide
  | downgradedFromOlderVersion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OrderStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OrderStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderStatus

/-- Mass Cancel Scope: one byte code -/
def MassCancelScope.codes : List UInt8 :=
  [0x41, 0x44]

inductive MassCancelScope where
  | massCancelAllOpenBinaryOrdersAndBlockAllSubsequentBinaryOrders -- Mass Cancel All Open Binary Orders And Block All Subsequent Binary Orders
  | massCancelAllOpenBinaryOrders -- Mass Cancel All Open Binary Orders
  | unlisted (byte : { byte : UInt8 // byte ∉ MassCancelScope.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MassCancelScope

def toByte : MassCancelScope → UInt8
  | .massCancelAllOpenBinaryOrdersAndBlockAllSubsequentBinaryOrders => 0x41
  | .massCancelAllOpenBinaryOrders => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MassCancelScope :=
  if byte = 0x41 then .massCancelAllOpenBinaryOrdersAndBlockAllSubsequentBinaryOrders
  else .massCancelAllOpenBinaryOrders

def ofByte (byte : UInt8) : MassCancelScope :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MassCancelScope) : ofByte value.toByte = value := by
  cases value with
  | massCancelAllOpenBinaryOrdersAndBlockAllSubsequentBinaryOrders => decide
  | massCancelAllOpenBinaryOrders => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MassCancelScope) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MassCancelScope × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MassCancelScope) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : MassCancelScope) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : MassCancelScope) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MassCancelScope

/-- Status: one byte code -/
def Status.codes : List UInt8 :=
  [0x20, 0x41, 0x43, 0x45, 0x46, 0x4A, 0x4D, 0x4E, 0x53, 0x55, 0x5A, 0x2A]

inductive Status where
  | successful -- Successful
  | arm2UnderlyingLevelProtectionIsInEffect -- Arm 2 Underlying Level Protection Is In Effect
  | cannotCancelWhileNotInLow -- Cannot Cancel While Not In Low
  | featureNotEnabled -- Feature Not Enabled
  | arm2FirmLevelProtectionIsInEffect -- Arm 2 Firm Level Protection Is In Effect
  | massCancelScopeContainsInvalidValue -- Mass Cancel Scope Contains Invalid Value
  | unknownMpid -- Unknown Mpid
  | allOrdersHaveAlreadyBeenCanceled -- All Orders Have Already Been Canceled
  | invalidSide -- Invalid Side
  | invalidUnderlying -- Invalid Underlying
  | undefinedError -- Undefined Error
  | downgradedFromOlderVersion -- Downgraded From Older Version
  | unlisted (byte : { byte : UInt8 // byte ∉ Status.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Status

def toByte : Status → UInt8
  | .successful => 0x20
  | .arm2UnderlyingLevelProtectionIsInEffect => 0x41
  | .cannotCancelWhileNotInLow => 0x43
  | .featureNotEnabled => 0x45
  | .arm2FirmLevelProtectionIsInEffect => 0x46
  | .massCancelScopeContainsInvalidValue => 0x4A
  | .unknownMpid => 0x4D
  | .allOrdersHaveAlreadyBeenCanceled => 0x4E
  | .invalidSide => 0x53
  | .invalidUnderlying => 0x55
  | .undefinedError => 0x5A
  | .downgradedFromOlderVersion => 0x2A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Status :=
  if byte = 0x20 then .successful
  else if byte = 0x41 then .arm2UnderlyingLevelProtectionIsInEffect
  else if byte = 0x43 then .cannotCancelWhileNotInLow
  else if byte = 0x45 then .featureNotEnabled
  else if byte = 0x46 then .arm2FirmLevelProtectionIsInEffect
  else if byte = 0x4A then .massCancelScopeContainsInvalidValue
  else if byte = 0x4D then .unknownMpid
  else if byte = 0x4E then .allOrdersHaveAlreadyBeenCanceled
  else if byte = 0x53 then .invalidSide
  else if byte = 0x55 then .invalidUnderlying
  else if byte = 0x5A then .undefinedError
  else .downgradedFromOlderVersion

def ofByte (byte : UInt8) : Status :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Status) : ofByte value.toByte = value := by
  cases value with
  | successful => decide
  | arm2UnderlyingLevelProtectionIsInEffect => decide
  | cannotCancelWhileNotInLow => decide
  | featureNotEnabled => decide
  | arm2FirmLevelProtectionIsInEffect => decide
  | massCancelScopeContainsInvalidValue => decide
  | unknownMpid => decide
  | allOrdersHaveAlreadyBeenCanceled => decide
  | invalidSide => decide
  | invalidUnderlying => decide
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
  [0x4C, 0x42, 0x55, 0x52, 0x4F, 0x54, 0x46, 0x4A, 0x2A]

inductive TriggerReason where
  | lineDisconnectTriggeredProtection -- Line Disconnect Triggered Protection
  | pearlHelpDeskTriggeredProtection -- Pearl Help Desk Triggered Protection
  | firmInitiatedMassCancel -- Firm Initiated Mass Cancel
  | armTriggeredProtection -- Arm Triggered Protection
  | rpmBinaryOrderRateProtectionTrigger -- Rpm Binary Order Rate Protection Trigger
  | rpmBinaryOrderExecutedContractsRateProtectionTrigger -- Rpm Binary Order Executed Contracts Rate Protection Trigger
  | arm2FirmLevelProtectionInitiatedMassCancel -- Arm 2 Firm Level Protection Initiated Mass Cancel
  | reservedForFutureUse -- Reserved For Future Use
  | downgradedFromOlderVersion -- Downgraded From Older Version
  | unlisted (byte : { byte : UInt8 // byte ∉ TriggerReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TriggerReason

def toByte : TriggerReason → UInt8
  | .lineDisconnectTriggeredProtection => 0x4C
  | .pearlHelpDeskTriggeredProtection => 0x42
  | .firmInitiatedMassCancel => 0x55
  | .armTriggeredProtection => 0x52
  | .rpmBinaryOrderRateProtectionTrigger => 0x4F
  | .rpmBinaryOrderExecutedContractsRateProtectionTrigger => 0x54
  | .arm2FirmLevelProtectionInitiatedMassCancel => 0x46
  | .reservedForFutureUse => 0x4A
  | .downgradedFromOlderVersion => 0x2A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TriggerReason :=
  if byte = 0x4C then .lineDisconnectTriggeredProtection
  else if byte = 0x42 then .pearlHelpDeskTriggeredProtection
  else if byte = 0x55 then .firmInitiatedMassCancel
  else if byte = 0x52 then .armTriggeredProtection
  else if byte = 0x4F then .rpmBinaryOrderRateProtectionTrigger
  else if byte = 0x54 then .rpmBinaryOrderExecutedContractsRateProtectionTrigger
  else if byte = 0x46 then .arm2FirmLevelProtectionInitiatedMassCancel
  else if byte = 0x4A then .reservedForFutureUse
  else .downgradedFromOlderVersion

def ofByte (byte : UInt8) : TriggerReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TriggerReason) : ofByte value.toByte = value := by
  cases value with
  | lineDisconnectTriggeredProtection => decide
  | pearlHelpDeskTriggeredProtection => decide
  | firmInitiatedMassCancel => decide
  | armTriggeredProtection => decide
  | rpmBinaryOrderRateProtectionTrigger => decide
  | rpmBinaryOrderExecutedContractsRateProtectionTrigger => decide
  | arm2FirmLevelProtectionInitiatedMassCancel => decide
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

/-- Time In Force Tif: one byte code -/
def TimeInForceTif.codes : List UInt8 :=
  [0x44, 0x49]

inductive TimeInForceTif where
  | day -- Day
  | ioc -- Ioc
  | unlisted (byte : { byte : UInt8 // byte ∉ TimeInForceTif.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TimeInForceTif

def toByte : TimeInForceTif → UInt8
  | .day => 0x44
  | .ioc => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TimeInForceTif :=
  if byte = 0x44 then .day
  else .ioc

def ofByte (byte : UInt8) : TimeInForceTif :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TimeInForceTif) : ofByte value.toByte = value := by
  cases value with
  | day => decide
  | ioc => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TimeInForceTif) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TimeInForceTif × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TimeInForceTif) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TimeInForceTif) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TimeInForceTif) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TimeInForceTif

/-- Order Instruction: one byte code -/
def OrderInstruction.codes : List UInt8 :=
  [0x52, 0x53, 0x50]

inductive OrderInstruction where
  | regular -- Regular
  | iso -- Iso
  | postOnly -- Post Only
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderInstruction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderInstruction

def toByte : OrderInstruction → UInt8
  | .regular => 0x52
  | .iso => 0x53
  | .postOnly => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderInstruction :=
  if byte = 0x52 then .regular
  else if byte = 0x53 then .iso
  else .postOnly

def ofByte (byte : UInt8) : OrderInstruction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderInstruction) : ofByte value.toByte = value := by
  cases value with
  | regular => decide
  | iso => decide
  | postOnly => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderInstruction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderInstruction × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderInstruction) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OrderInstruction) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OrderInstruction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderInstruction

/-- Origin: one byte code -/
def Origin.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x34, 0x35, 0x38]

inductive Origin where
  | priorityCustomer -- Priority Customer
  | firm -- Firm
  | brokerDealer -- Broker Dealer
  | marketMaker -- Market Maker
  | nonMemberMarketMaker -- Non Member Market Maker
  | nonPriorityCustomer -- Non Priority Customer
  | unlisted (byte : { byte : UInt8 // byte ∉ Origin.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Origin

def toByte : Origin → UInt8
  | .priorityCustomer => 0x30
  | .firm => 0x31
  | .brokerDealer => 0x32
  | .marketMaker => 0x34
  | .nonMemberMarketMaker => 0x35
  | .nonPriorityCustomer => 0x38
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Origin :=
  if byte = 0x30 then .priorityCustomer
  else if byte = 0x31 then .firm
  else if byte = 0x32 then .brokerDealer
  else if byte = 0x34 then .marketMaker
  else if byte = 0x35 then .nonMemberMarketMaker
  else .nonPriorityCustomer

def ofByte (byte : UInt8) : Origin :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Origin) : ofByte value.toByte = value := by
  cases value with
  | priorityCustomer => decide
  | firm => decide
  | brokerDealer => decide
  | marketMaker => decide
  | nonMemberMarketMaker => decide
  | nonPriorityCustomer => decide
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

/-- Open Close: one byte code -/
def OpenClose.codes : List UInt8 :=
  [0x4F, 0x43, 0x4E]

inductive OpenClose where
  | open_ -- Open
  | close -- Close
  | na -- Na
  | unlisted (byte : { byte : UInt8 // byte ∉ OpenClose.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OpenClose

def toByte : OpenClose → UInt8
  | .open_ => 0x4F
  | .close => 0x43
  | .na => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OpenClose :=
  if byte = 0x4F then .open_
  else if byte = 0x43 then .close
  else .na

def ofByte (byte : UInt8) : OpenClose :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OpenClose) : ofByte value.toByte = value := by
  cases value with
  | open_ => decide
  | close => decide
  | na => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OpenClose) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OpenClose × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OpenClose) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OpenClose) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OpenClose) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OpenClose

/-- Covered Uncovered: one byte code -/
def CoveredUncovered.codes : List UInt8 :=
  [0x43, 0x55, 0x4E]

inductive CoveredUncovered where
  | covered -- Covered
  | uncovered -- Uncovered
  | na -- Na
  | unlisted (byte : { byte : UInt8 // byte ∉ CoveredUncovered.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CoveredUncovered

def toByte : CoveredUncovered → UInt8
  | .covered => 0x43
  | .uncovered => 0x55
  | .na => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CoveredUncovered :=
  if byte = 0x43 then .covered
  else if byte = 0x55 then .uncovered
  else .na

def ofByte (byte : UInt8) : CoveredUncovered :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CoveredUncovered) : ofByte value.toByte = value := by
  cases value with
  | covered => decide
  | uncovered => decide
  | na => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CoveredUncovered) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CoveredUncovered × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CoveredUncovered) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CoveredUncovered) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CoveredUncovered) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CoveredUncovered

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
  activeOnPearl : ActiveOnPearl
  pearlBboPostingIncrementIndicator : PearlBboPostingIncrementIndicator
  orderAcceptanceIncrementIndicator : OrderAcceptanceIncrementIndicator
  openingUnderlyingMarketCode : OpeningUnderlyingMarketCode
  reserved12 : Alpha 12
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
    ++ (ActiveOnPearl.encode message.activeOnPearl
    ++ (PearlBboPostingIncrementIndicator.encode message.pearlBboPostingIncrementIndicator
    ++ (OrderAcceptanceIncrementIndicator.encode message.orderAcceptanceIncrementIndicator
    ++ (OpeningUnderlyingMarketCode.encode message.openingUnderlyingMarketCode
    ++ (Alpha.encode message.reserved12)))))))))))))))

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
  let (activeOnPearl, bytes) ← ActiveOnPearl.decode bytes
  let (pearlBboPostingIncrementIndicator, bytes) ← PearlBboPostingIncrementIndicator.decode bytes
  let (orderAcceptanceIncrementIndicator, bytes) ← OrderAcceptanceIncrementIndicator.decode bytes
  let (openingUnderlyingMarketCode, bytes) ← OpeningUnderlyingMarketCode.decode bytes
  let (reserved12, bytes) ← Alpha.decode 12 bytes
  pure ({ productAddUpdateTime, productId, underlyingSymbol, securitySymbol, expirationDate, strikePrice, callOrPut, openingTime, closingTime, restrictedOption, longTermOption, activeOnPearl, pearlBboPostingIncrementIndicator, orderAcceptanceIncrementIndicator, openingUnderlyingMarketCode, reserved12 }, bytes)

@[simp] theorem encode_length (message : SeriesUpdate) : (encode message).length = 76 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, CallOrPut.encode_length, RestrictedOption.encode_length, LongTermOption.encode_length, ActiveOnPearl.encode_length, PearlBboPostingIncrementIndicator.encode_length, OrderAcceptanceIncrementIndicator.encode_length, OpeningUnderlyingMarketCode.encode_length]

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
  rw [List.append_assoc, ActiveOnPearl.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PearlBboPostingIncrementIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderAcceptanceIncrementIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpeningUnderlyingMarketCode.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SeriesUpdate

/-- System State Notification: 18 bytes -/
structure SystemStateNotification where
  notificationTime : BitVec 64
  meoVersion : Alpha 8
  sessionId : BitVec 8
  systemStatus : SystemStatus
  deriving DecidableEq, Repr

namespace SystemStateNotification

def encode (message : SystemStateNotification) : List UInt8 :=
  encodeUIntLE 8 message.notificationTime
    ++ (Alpha.encode message.meoVersion
    ++ (encodeUInt 1 message.sessionId
    ++ (SystemStatus.encode message.systemStatus)))

def decode (bytes : List UInt8) : Option (SystemStateNotification × List UInt8) := do
  let (notificationTime, bytes) ← decodeUIntLE 8 bytes
  let (meoVersion, bytes) ← Alpha.decode 8 bytes
  let (sessionId, bytes) ← decodeUInt 1 bytes
  let (systemStatus, bytes) ← SystemStatus.decode bytes
  pure ({ notificationTime, meoVersion, sessionId, systemStatus }, bytes)

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

/-- Opening Width Relief Notification: 23 bytes -/
structure OpeningWidthReliefNotification where
  notificationTime : BitVec 64
  underlyingSymbol : Alpha 11
  reliefMultiplier : BitVec 32
  deriving DecidableEq, Repr

namespace OpeningWidthReliefNotification

def encode (message : OpeningWidthReliefNotification) : List UInt8 :=
  encodeUIntLE 8 message.notificationTime
    ++ (Alpha.encode message.underlyingSymbol
    ++ (encodeUIntLE 4 message.reliefMultiplier))

def decode (bytes : List UInt8) : Option (OpeningWidthReliefNotification × List UInt8) := do
  let (notificationTime, bytes) ← decodeUIntLE 8 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 11 bytes
  let (reliefMultiplier, bytes) ← decodeUIntLE 4 bytes
  pure ({ notificationTime, underlyingSymbol, reliefMultiplier }, bytes)

@[simp] theorem encode_length (message : OpeningWidthReliefNotification) : (encode message).length = 23 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : OpeningWidthReliefNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OpeningWidthReliefNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OpeningWidthReliefNotification

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

/-- Single Side Liquidity Protection Trigger Notification: 26 bytes -/
structure SingleSideLiquidityProtectionTriggerNotification where
  notificationTime : BitVec 64
  mpid : Alpha 4
  productId : BitVec 32
  side : Side
  triggeringClientMessageId : BitVec 32
  triggeringBulkOrderIndex : BitVec 8
  reserved4 : Alpha 4
  deriving DecidableEq, Repr

namespace SingleSideLiquidityProtectionTriggerNotification

def encode (message : SingleSideLiquidityProtectionTriggerNotification) : List UInt8 :=
  encodeUIntLE 8 message.notificationTime
    ++ (Alpha.encode message.mpid
    ++ (encodeUIntLE 4 message.productId
    ++ (Side.encode message.side
    ++ (encodeUIntLE 4 message.triggeringClientMessageId
    ++ (encodeUInt 1 message.triggeringBulkOrderIndex
    ++ (Alpha.encode message.reserved4))))))

def decode (bytes : List UInt8) : Option (SingleSideLiquidityProtectionTriggerNotification × List UInt8) := do
  let (notificationTime, bytes) ← decodeUIntLE 8 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (triggeringClientMessageId, bytes) ← decodeUIntLE 4 bytes
  let (triggeringBulkOrderIndex, bytes) ← decodeUInt 1 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  pure ({ notificationTime, mpid, productId, side, triggeringClientMessageId, triggeringBulkOrderIndex, reserved4 }, bytes)

@[simp] theorem encode_length (message : SingleSideLiquidityProtectionTriggerNotification) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, Side.encode_length, encodeUInt_length]

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

/-- Cancel Notification: 40 bytes -/
structure CancelNotification where
  notificationTime : BitVec 64
  mpid : Alpha 4
  productId : BitVec 32
  liquidityType : LiquidityType
  clientMessageId : BitVec 32
  clientOrderId : BitVec 32
  bulkOrderIndex : BitVec 8
  side : Side
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
    ++ (encodeUIntLE 4 message.clientOrderId
    ++ (encodeUInt 1 message.bulkOrderIndex
    ++ (Side.encode message.side
    ++ (encodeUIntLE 4 message.size
    ++ (encodeUIntLE 8 message.engineSequenceNumber
    ++ (CancelReason.encode message.cancelReason))))))))))

def decode (bytes : List UInt8) : Option (CancelNotification × List UInt8) := do
  let (notificationTime, bytes) ← decodeUIntLE 8 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (liquidityType, bytes) ← LiquidityType.decode bytes
  let (clientMessageId, bytes) ← decodeUIntLE 4 bytes
  let (clientOrderId, bytes) ← decodeUIntLE 4 bytes
  let (bulkOrderIndex, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← Side.decode bytes
  let (size, bytes) ← decodeUIntLE 4 bytes
  let (engineSequenceNumber, bytes) ← decodeUIntLE 8 bytes
  let (cancelReason, bytes) ← CancelReason.decode bytes
  pure ({ notificationTime, mpid, productId, liquidityType, clientMessageId, clientOrderId, bulkOrderIndex, side, size, engineSequenceNumber, cancelReason }, bytes)

@[simp] theorem encode_length (message : CancelNotification) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, LiquidityType.encode_length, encodeUInt_length, Side.encode_length, CancelReason.encode_length]

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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [CancelReason.decode_encode, some_bind]
  rfl

end CancelNotification

/-- Execution Notification: 64 bytes -/
structure ExecutionNotification where
  notificationTime : BitVec 64
  mpid : Alpha 4
  productId : BitVec 32
  liquidityType : LiquidityType
  clientMessageId : BitVec 32
  clientOrderId : BitVec 32
  bulkOrderIndex : BitVec 8
  tradeId : BitVec 32
  executionId : BitVec 64
  tradeStatus : TradeStatus
  lastPrice : BitVec 32
  side : Side
  lastSize : BitVec 32
  liquidityIndicator : LiquidityIndicator
  reserved15 : Alpha 15
  deriving DecidableEq, Repr

namespace ExecutionNotification

def encode (message : ExecutionNotification) : List UInt8 :=
  encodeUIntLE 8 message.notificationTime
    ++ (Alpha.encode message.mpid
    ++ (encodeUIntLE 4 message.productId
    ++ (LiquidityType.encode message.liquidityType
    ++ (encodeUIntLE 4 message.clientMessageId
    ++ (encodeUIntLE 4 message.clientOrderId
    ++ (encodeUInt 1 message.bulkOrderIndex
    ++ (encodeUIntLE 4 message.tradeId
    ++ (encodeUIntLE 8 message.executionId
    ++ (TradeStatus.encode message.tradeStatus
    ++ (encodeUIntLE 4 message.lastPrice
    ++ (Side.encode message.side
    ++ (encodeUIntLE 4 message.lastSize
    ++ (LiquidityIndicator.encode message.liquidityIndicator
    ++ (Alpha.encode message.reserved15))))))))))))))

def decode (bytes : List UInt8) : Option (ExecutionNotification × List UInt8) := do
  let (notificationTime, bytes) ← decodeUIntLE 8 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (liquidityType, bytes) ← LiquidityType.decode bytes
  let (clientMessageId, bytes) ← decodeUIntLE 4 bytes
  let (clientOrderId, bytes) ← decodeUIntLE 4 bytes
  let (bulkOrderIndex, bytes) ← decodeUInt 1 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (executionId, bytes) ← decodeUIntLE 8 bytes
  let (tradeStatus, bytes) ← TradeStatus.decode bytes
  let (lastPrice, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (lastSize, bytes) ← decodeUIntLE 4 bytes
  let (liquidityIndicator, bytes) ← LiquidityIndicator.decode bytes
  let (reserved15, bytes) ← Alpha.decode 15 bytes
  pure ({ notificationTime, mpid, productId, liquidityType, clientMessageId, clientOrderId, bulkOrderIndex, tradeId, executionId, tradeStatus, lastPrice, side, lastSize, liquidityIndicator, reserved15 }, bytes)

@[simp] theorem encode_length (message : ExecutionNotification) : (encode message).length = 64 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, LiquidityType.encode_length, encodeUInt_length, TradeStatus.encode_length, Side.encode_length, LiquidityIndicator.encode_length]

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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, LiquidityIndicator.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ExecutionNotification

/-- Any Sequenced Message, selected by Sequenced Message Type -/
inductive SequencedMessage where
  | seriesUpdate (message : SeriesUpdate) -- "SU" 0x5355
  | systemStateNotification (message : SystemStateNotification) -- "SN" 0x534E
  | underlyingTradingStatusNotification (message : UnderlyingTradingStatusNotification) -- "UN" 0x554E
  | openingWidthReliefNotification (message : OpeningWidthReliefNotification) -- "QN" 0x514E
  | armProtectionSettingsNotification (message : ArmProtectionSettingsNotification) -- "AN" 0x414E
  | arm2UnderlyingLevelProtectionSettingsNotification (message : Arm2UnderlyingLevelProtectionSettingsNotification) -- "A2" 0x4132
  | singleSideLiquidityProtectionTriggerNotification (message : SingleSideLiquidityProtectionTriggerNotification) -- "QX" 0x5158
  | arm2UnderlyingLevelProtectionNotification (message : Arm2UnderlyingLevelProtectionNotification) -- "UP" 0x5550
  | arm2FirmLevelProtectionNotification (message : Arm2FirmLevelProtectionNotification) -- "FP" 0x4650
  | cancelNotification (message : CancelNotification) -- "XN" 0x584E
  | executionNotification (message : ExecutionNotification) -- "EN" 0x454E
  deriving DecidableEq, Repr

namespace SequencedMessage

/-- The Sequenced Message Type each message is sent under -/
def tag : SequencedMessage → BitVec 16
  | .seriesUpdate _ => 21333
  | .systemStateNotification _ => 21326
  | .underlyingTradingStatusNotification _ => 21838
  | .openingWidthReliefNotification _ => 20814
  | .armProtectionSettingsNotification _ => 16718
  | .arm2UnderlyingLevelProtectionSettingsNotification _ => 16690
  | .singleSideLiquidityProtectionTriggerNotification _ => 20824
  | .arm2UnderlyingLevelProtectionNotification _ => 21840
  | .arm2FirmLevelProtectionNotification _ => 18000
  | .cancelNotification _ => 22606
  | .executionNotification _ => 17742

def encode : SequencedMessage → List UInt8
  | .seriesUpdate message => SeriesUpdate.encode message
  | .systemStateNotification message => SystemStateNotification.encode message
  | .underlyingTradingStatusNotification message => UnderlyingTradingStatusNotification.encode message
  | .openingWidthReliefNotification message => OpeningWidthReliefNotification.encode message
  | .armProtectionSettingsNotification message => ArmProtectionSettingsNotification.encode message
  | .arm2UnderlyingLevelProtectionSettingsNotification message => Arm2UnderlyingLevelProtectionSettingsNotification.encode message
  | .singleSideLiquidityProtectionTriggerNotification message => SingleSideLiquidityProtectionTriggerNotification.encode message
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
  | systemStateNotification inner =>
    simp only [encode, SystemStateNotification.encode_length]
    omega
  | underlyingTradingStatusNotification inner =>
    simp only [encode, UnderlyingTradingStatusNotification.encode_length]
    omega
  | openingWidthReliefNotification inner =>
    simp only [encode, OpeningWidthReliefNotification.encode_length]
    omega
  | armProtectionSettingsNotification inner =>
    simp only [encode, ArmProtectionSettingsNotification.encode_length]
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
  | cancelNotification inner =>
    simp only [encode, CancelNotification.encode_length]
    omega
  | executionNotification inner =>
    simp only [encode, ExecutionNotification.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (SequencedMessage × List UInt8) :=
  if tag = 21333 then (SeriesUpdate.decode bytes).map fun (message, rest) => (.seriesUpdate message, rest)
  else if tag = 21326 then (SystemStateNotification.decode bytes).map fun (message, rest) => (.systemStateNotification message, rest)
  else if tag = 21838 then (UnderlyingTradingStatusNotification.decode bytes).map fun (message, rest) => (.underlyingTradingStatusNotification message, rest)
  else if tag = 20814 then (OpeningWidthReliefNotification.decode bytes).map fun (message, rest) => (.openingWidthReliefNotification message, rest)
  else if tag = 16718 then (ArmProtectionSettingsNotification.decode bytes).map fun (message, rest) => (.armProtectionSettingsNotification message, rest)
  else if tag = 16690 then (Arm2UnderlyingLevelProtectionSettingsNotification.decode bytes).map fun (message, rest) => (.arm2UnderlyingLevelProtectionSettingsNotification message, rest)
  else if tag = 20824 then (SingleSideLiquidityProtectionTriggerNotification.decode bytes).map fun (message, rest) => (.singleSideLiquidityProtectionTriggerNotification message, rest)
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
  | systemStateNotification inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, SystemStateNotification.encode_length]
    omega
  | underlyingTradingStatusNotification inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, UnderlyingTradingStatusNotification.encode_length]
    omega
  | openingWidthReliefNotification inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, OpeningWidthReliefNotification.encode_length]
    omega
  | armProtectionSettingsNotification inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, ArmProtectionSettingsNotification.encode_length]
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
  arm2SettingsUpdateStatus : Arm2SettingsUpdateStatus
  deriving DecidableEq, Repr

namespace Arm2UnderlyingLevelProtectionSettingsUpdateResponse

def encode (message : Arm2UnderlyingLevelProtectionSettingsUpdateResponse) : List UInt8 :=
  encodeUIntLE 4 message.clientMessageId
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.underlyingSymbol
    ++ (Arm2SettingsUpdateStatus.encode message.arm2SettingsUpdateStatus)))

def decode (bytes : List UInt8) : Option (Arm2UnderlyingLevelProtectionSettingsUpdateResponse × List UInt8) := do
  let (clientMessageId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 11 bytes
  let (arm2SettingsUpdateStatus, bytes) ← Arm2SettingsUpdateStatus.decode bytes
  pure ({ clientMessageId, mpid, underlyingSymbol, arm2SettingsUpdateStatus }, bytes)

@[simp] theorem encode_length (message : Arm2UnderlyingLevelProtectionSettingsUpdateResponse) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, Arm2SettingsUpdateStatus.encode_length]

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
  rw [Arm2SettingsUpdateStatus.decode_encode, some_bind]
  rfl

end Arm2UnderlyingLevelProtectionSettingsUpdateResponse

/-- Series Assignment Request: 13 bytes -/
structure SeriesAssignmentRequest where
  clientMessageId : BitVec 32
  mpid : Alpha 4
  productId : BitVec 32
  action : Action
  deriving DecidableEq, Repr

namespace SeriesAssignmentRequest

def encode (message : SeriesAssignmentRequest) : List UInt8 :=
  encodeUIntLE 4 message.clientMessageId
    ++ (Alpha.encode message.mpid
    ++ (encodeUIntLE 4 message.productId
    ++ (Action.encode message.action)))

def decode (bytes : List UInt8) : Option (SeriesAssignmentRequest × List UInt8) := do
  let (clientMessageId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (action, bytes) ← Action.decode bytes
  pure ({ clientMessageId, mpid, productId, action }, bytes)

@[simp] theorem encode_length (message : SeriesAssignmentRequest) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, Action.encode_length]

theorem encode_length_pos (message : SeriesAssignmentRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SeriesAssignmentRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Action.decode_encode, some_bind]
  rfl

end SeriesAssignmentRequest

/-- Series Assignment Response: 9 bytes -/
structure SeriesAssignmentResponse where
  clientMessageId : BitVec 32
  mpid : Alpha 4
  assignmentSettingsStatus : AssignmentSettingsStatus
  deriving DecidableEq, Repr

namespace SeriesAssignmentResponse

def encode (message : SeriesAssignmentResponse) : List UInt8 :=
  encodeUIntLE 4 message.clientMessageId
    ++ (Alpha.encode message.mpid
    ++ (AssignmentSettingsStatus.encode message.assignmentSettingsStatus))

def decode (bytes : List UInt8) : Option (SeriesAssignmentResponse × List UInt8) := do
  let (clientMessageId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (assignmentSettingsStatus, bytes) ← AssignmentSettingsStatus.decode bytes
  pure ({ clientMessageId, mpid, assignmentSettingsStatus }, bytes)

@[simp] theorem encode_length (message : SeriesAssignmentResponse) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, AssignmentSettingsStatus.encode_length]

theorem encode_length_pos (message : SeriesAssignmentResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SeriesAssignmentResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [AssignmentSettingsStatus.decode_encode, some_bind]
  rfl

end SeriesAssignmentResponse

/-- Self Trade Protection Designation Request: 9 bytes -/
structure SelfTradeProtectionDesignationRequest where
  clientMessageId : BitVec 32
  mpid : Alpha 4
  action : Action
  deriving DecidableEq, Repr

namespace SelfTradeProtectionDesignationRequest

def encode (message : SelfTradeProtectionDesignationRequest) : List UInt8 :=
  encodeUIntLE 4 message.clientMessageId
    ++ (Alpha.encode message.mpid
    ++ (Action.encode message.action))

def decode (bytes : List UInt8) : Option (SelfTradeProtectionDesignationRequest × List UInt8) := do
  let (clientMessageId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (action, bytes) ← Action.decode bytes
  pure ({ clientMessageId, mpid, action }, bytes)

@[simp] theorem encode_length (message : SelfTradeProtectionDesignationRequest) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, Action.encode_length]

theorem encode_length_pos (message : SelfTradeProtectionDesignationRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SelfTradeProtectionDesignationRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Action.decode_encode, some_bind]
  rfl

end SelfTradeProtectionDesignationRequest

/-- Self Trade Protection Designation Response: 9 bytes -/
structure SelfTradeProtectionDesignationResponse where
  clientMessageId : BitVec 32
  mpid : Alpha 4
  selfTradeProtectionStatus : SelfTradeProtectionStatus
  deriving DecidableEq, Repr

namespace SelfTradeProtectionDesignationResponse

def encode (message : SelfTradeProtectionDesignationResponse) : List UInt8 :=
  encodeUIntLE 4 message.clientMessageId
    ++ (Alpha.encode message.mpid
    ++ (SelfTradeProtectionStatus.encode message.selfTradeProtectionStatus))

def decode (bytes : List UInt8) : Option (SelfTradeProtectionDesignationResponse × List UInt8) := do
  let (clientMessageId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (selfTradeProtectionStatus, bytes) ← SelfTradeProtectionStatus.decode bytes
  pure ({ clientMessageId, mpid, selfTradeProtectionStatus }, bytes)

@[simp] theorem encode_length (message : SelfTradeProtectionDesignationResponse) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, SelfTradeProtectionStatus.encode_length]

theorem encode_length_pos (message : SelfTradeProtectionDesignationResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SelfTradeProtectionDesignationResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [SelfTradeProtectionStatus.decode_encode, some_bind]
  rfl

end SelfTradeProtectionDesignationResponse

/-- Liquidity Units: 57 bytes -/
structure LiquidityUnits where
  liquidityUnit : BitVec 456
  deriving DecidableEq, Repr

namespace LiquidityUnits

def encode (message : LiquidityUnits) : List UInt8 :=
  encodeUIntLE 57 message.liquidityUnit

def decode (bytes : List UInt8) : Option (LiquidityUnits × List UInt8) := do
  let (liquidityUnit, bytes) ← decodeUIntLE 57 bytes
  pure ({ liquidityUnit }, bytes)

@[simp] theorem encode_length (message : LiquidityUnits) : (encode message).length = 57 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : LiquidityUnits) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LiquidityUnits) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end LiquidityUnits

/-- Bulk Liquidity Message -/
structure BulkLiquidityMessage where
  clientMessageId : BitVec 32
  clientSendTime : BitVec 64
  reserved4 : Alpha 4
  liquidityUnits : Bounded 1 LiquidityUnits
  deriving DecidableEq, Repr

namespace BulkLiquidityMessage

def encode (message : BulkLiquidityMessage) : List UInt8 :=
  encodeUIntLE 4 message.clientMessageId
    ++ (encodeUIntLE 8 message.clientSendTime
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.liquidityUnits.val.length)
    ++ (Alpha.encode message.reserved4
    ++ (encodeMany LiquidityUnits.encode message.liquidityUnits.val))))

def decode (bytes : List UInt8) : Option (BulkLiquidityMessage × List UInt8) := do
  let (clientMessageId, bytes) ← decodeUIntLE 4 bytes
  let (clientSendTime, bytes) ← decodeUIntLE 8 bytes
  let (liquidityUnitCount, bytes) ← decodeUInt 1 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (liquidityUnits_, bytes) ← decodeMany LiquidityUnits.decode liquidityUnitCount.toNat bytes
  if fits_liquidityUnits : liquidityUnits_.length < 256 ^ 1 then
    pure ({ clientMessageId, clientSendTime, reserved4, liquidityUnits := ⟨liquidityUnits_, fits_liquidityUnits⟩ }, bytes)
  else none

theorem encode_length_pos (message : BulkLiquidityMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : BulkLiquidityMessage) : (encode message).length ≤ 14552 := by
  have bound_liquidityUnits := message.liquidityUnits.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, encodeMany_length_const LiquidityUnits.encode 57 LiquidityUnits.encode_length]
  omega

@[simp] theorem decode_encode (message : BulkLiquidityMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 LiquidityUnits.encode LiquidityUnits.decode LiquidityUnits.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.liquidityUnits.length_lt]
  rfl

end BulkLiquidityMessage

/-- Order Response: 13 bytes -/
structure OrderResponse where
  orderStatus : OrderStatus
  engineSequenceNumber : BitVec 64
  openSize : BitVec 32
  deriving DecidableEq, Repr

namespace OrderResponse

def encode (message : OrderResponse) : List UInt8 :=
  OrderStatus.encode message.orderStatus
    ++ (encodeUIntLE 8 message.engineSequenceNumber
    ++ (encodeUIntLE 4 message.openSize))

def decode (bytes : List UInt8) : Option (OrderResponse × List UInt8) := do
  let (orderStatus, bytes) ← OrderStatus.decode bytes
  let (engineSequenceNumber, bytes) ← decodeUIntLE 8 bytes
  let (openSize, bytes) ← decodeUIntLE 4 bytes
  pure ({ orderStatus, engineSequenceNumber, openSize }, bytes)

@[simp] theorem encode_length (message : OrderResponse) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, OrderStatus.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : OrderResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OrderStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderResponse

/-- Bulk Liquidity Message Response -/
structure BulkLiquidityMessageResponse where
  clientMessageId : BitVec 32
  bulkOrderStatus : BulkOrderStatus
  orderCount : BitVec 8
  orderAckTime : BitVec 64
  orderResponse : Bounded 1 OrderResponse
  deriving DecidableEq, Repr

namespace BulkLiquidityMessageResponse

def encode (message : BulkLiquidityMessageResponse) : List UInt8 :=
  encodeUIntLE 4 message.clientMessageId
    ++ (BulkOrderStatus.encode message.bulkOrderStatus
    ++ (encodeUInt 1 message.orderCount
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.orderResponse.val.length)
    ++ (encodeUIntLE 8 message.orderAckTime
    ++ (encodeMany OrderResponse.encode message.orderResponse.val)))))

def decode (bytes : List UInt8) : Option (BulkLiquidityMessageResponse × List UInt8) := do
  let (clientMessageId, bytes) ← decodeUIntLE 4 bytes
  let (bulkOrderStatus, bytes) ← BulkOrderStatus.decode bytes
  let (orderCount, bytes) ← decodeUInt 1 bytes
  let (invalidOrderCount, bytes) ← decodeUInt 1 bytes
  let (orderAckTime, bytes) ← decodeUIntLE 8 bytes
  let (orderResponse_, bytes) ← decodeMany OrderResponse.decode invalidOrderCount.toNat bytes
  if fits_orderResponse : orderResponse_.length < 256 ^ 1 then
    pure ({ clientMessageId, bulkOrderStatus, orderCount, orderAckTime, orderResponse := ⟨orderResponse_, fits_orderResponse⟩ }, bytes)
  else none

theorem encode_length_pos (message : BulkLiquidityMessageResponse) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : BulkLiquidityMessageResponse) : (encode message).length ≤ 3330 := by
  have bound_orderResponse := message.orderResponse.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, BulkOrderStatus.encode_length, encodeUInt_length, encodeMany_length_const OrderResponse.encode 13 OrderResponse.encode_length]
  omega

@[simp] theorem decode_encode (message : BulkLiquidityMessageResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, BulkOrderStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 OrderResponse.encode OrderResponse.decode OrderResponse.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.orderResponse.length_lt]
  rfl

end BulkLiquidityMessageResponse

/-- Liquidity Mass Cancel Request: 35 bytes -/
structure LiquidityMassCancelRequest where
  clientMessageId : BitVec 32
  mpid : Alpha 4
  clientSendTime : BitVec 64
  underlyingSymbol : Alpha 11
  massCancelScope : MassCancelScope
  reserved7 : Alpha 7
  deriving DecidableEq, Repr

namespace LiquidityMassCancelRequest

def encode (message : LiquidityMassCancelRequest) : List UInt8 :=
  encodeUIntLE 4 message.clientMessageId
    ++ (Alpha.encode message.mpid
    ++ (encodeUIntLE 8 message.clientSendTime
    ++ (Alpha.encode message.underlyingSymbol
    ++ (MassCancelScope.encode message.massCancelScope
    ++ (Alpha.encode message.reserved7)))))

def decode (bytes : List UInt8) : Option (LiquidityMassCancelRequest × List UInt8) := do
  let (clientMessageId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (clientSendTime, bytes) ← decodeUIntLE 8 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 11 bytes
  let (massCancelScope, bytes) ← MassCancelScope.decode bytes
  let (reserved7, bytes) ← Alpha.decode 7 bytes
  pure ({ clientMessageId, mpid, clientSendTime, underlyingSymbol, massCancelScope, reserved7 }, bytes)

@[simp] theorem encode_length (message : LiquidityMassCancelRequest) : (encode message).length = 35 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, MassCancelScope.encode_length]

theorem encode_length_pos (message : LiquidityMassCancelRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LiquidityMassCancelRequest) (rest : List UInt8) :
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
  rw [List.append_assoc, MassCancelScope.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LiquidityMassCancelRequest

/-- Liquidity Mass Cancel Response: 9 bytes -/
structure LiquidityMassCancelResponse where
  clientMessageId : BitVec 32
  mpid : Alpha 4
  status : Status
  deriving DecidableEq, Repr

namespace LiquidityMassCancelResponse

def encode (message : LiquidityMassCancelResponse) : List UInt8 :=
  encodeUIntLE 4 message.clientMessageId
    ++ (Alpha.encode message.mpid
    ++ (Status.encode message.status))

def decode (bytes : List UInt8) : Option (LiquidityMassCancelResponse × List UInt8) := do
  let (clientMessageId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (status, bytes) ← Status.decode bytes
  pure ({ clientMessageId, mpid, status }, bytes)

@[simp] theorem encode_length (message : LiquidityMassCancelResponse) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, Status.encode_length]

theorem encode_length_pos (message : LiquidityMassCancelResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LiquidityMassCancelResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Status.decode_encode, some_bind]
  rfl

end LiquidityMassCancelResponse

/-- Liquidity Protection Reset Request: 19 bytes -/
structure LiquidityProtectionResetRequest where
  clientMessageId : BitVec 32
  mpid : Alpha 4
  underlyingSymbol : Alpha 11
  deriving DecidableEq, Repr

namespace LiquidityProtectionResetRequest

def encode (message : LiquidityProtectionResetRequest) : List UInt8 :=
  encodeUIntLE 4 message.clientMessageId
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.underlyingSymbol))

def decode (bytes : List UInt8) : Option (LiquidityProtectionResetRequest × List UInt8) := do
  let (clientMessageId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 11 bytes
  pure ({ clientMessageId, mpid, underlyingSymbol }, bytes)

@[simp] theorem encode_length (message : LiquidityProtectionResetRequest) : (encode message).length = 19 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

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
  rw [Alpha.decode_encode, some_bind]
  rfl

end LiquidityProtectionResetRequest

/-- Liquidity Protection Reset Response: 9 bytes -/
structure LiquidityProtectionResetResponse where
  clientMessageId : BitVec 32
  mpid : Alpha 4
  status : Status
  deriving DecidableEq, Repr

namespace LiquidityProtectionResetResponse

def encode (message : LiquidityProtectionResetResponse) : List UInt8 :=
  encodeUIntLE 4 message.clientMessageId
    ++ (Alpha.encode message.mpid
    ++ (Status.encode message.status))

def decode (bytes : List UInt8) : Option (LiquidityProtectionResetResponse × List UInt8) := do
  let (clientMessageId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (status, bytes) ← Status.decode bytes
  pure ({ clientMessageId, mpid, status }, bytes)

@[simp] theorem encode_length (message : LiquidityProtectionResetResponse) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, Status.encode_length]

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
  rw [Status.decode_encode, some_bind]
  rfl

end LiquidityProtectionResetResponse

/-- Single Side Liquidity Protection Reset Request: 17 bytes -/
structure SingleSideLiquidityProtectionResetRequest where
  clientMessageId : BitVec 32
  mpid : Alpha 4
  productId : BitVec 32
  side : Side
  reserved4 : Alpha 4
  deriving DecidableEq, Repr

namespace SingleSideLiquidityProtectionResetRequest

def encode (message : SingleSideLiquidityProtectionResetRequest) : List UInt8 :=
  encodeUIntLE 4 message.clientMessageId
    ++ (Alpha.encode message.mpid
    ++ (encodeUIntLE 4 message.productId
    ++ (Side.encode message.side
    ++ (Alpha.encode message.reserved4))))

def decode (bytes : List UInt8) : Option (SingleSideLiquidityProtectionResetRequest × List UInt8) := do
  let (clientMessageId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  pure ({ clientMessageId, mpid, productId, side, reserved4 }, bytes)

@[simp] theorem encode_length (message : SingleSideLiquidityProtectionResetRequest) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, Side.encode_length]

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

/-- Liquidity Protection Trigger Notification: 24 bytes -/
structure LiquidityProtectionTriggerNotification where
  notificationTime : BitVec 64
  mpid : Alpha 4
  underlyingSymbol : Alpha 11
  triggerReason : TriggerReason
  deriving DecidableEq, Repr

namespace LiquidityProtectionTriggerNotification

def encode (message : LiquidityProtectionTriggerNotification) : List UInt8 :=
  encodeUIntLE 8 message.notificationTime
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.underlyingSymbol
    ++ (TriggerReason.encode message.triggerReason)))

def decode (bytes : List UInt8) : Option (LiquidityProtectionTriggerNotification × List UInt8) := do
  let (notificationTime, bytes) ← decodeUIntLE 8 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 11 bytes
  let (triggerReason, bytes) ← TriggerReason.decode bytes
  pure ({ notificationTime, mpid, underlyingSymbol, triggerReason }, bytes)

@[simp] theorem encode_length (message : LiquidityProtectionTriggerNotification) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TriggerReason.encode_length]

theorem encode_length_pos (message : LiquidityProtectionTriggerNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LiquidityProtectionTriggerNotification) (rest : List UInt8) :
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

end LiquidityProtectionTriggerNotification

/-- Order Notification: 63 bytes -/
structure OrderNotification where
  notificationTime : BitVec 64
  clientOrderId : BitVec 32
  clientMessageId : BitVec 32
  bulkOrderIndex : BitVec 8
  targetClientOrderId : BitVec 32
  mpid : Alpha 4
  productId : BitVec 32
  timeInForceTif : TimeInForceTif
  orderInstruction : OrderInstruction
  origin : Origin
  mvp : BitVec 8
  price : BitVec 32
  size : BitVec 32
  side : Side
  openClose : OpenClose
  coveredUncovered : CoveredUncovered
  clearingAccount : Alpha 5
  cmta : BitVec 32
  account : Alpha 10
  deriving DecidableEq, Repr

namespace OrderNotification

def encode (message : OrderNotification) : List UInt8 :=
  encodeUIntLE 8 message.notificationTime
    ++ (encodeUIntLE 4 message.clientOrderId
    ++ (encodeUIntLE 4 message.clientMessageId
    ++ (encodeUInt 1 message.bulkOrderIndex
    ++ (encodeUIntLE 4 message.targetClientOrderId
    ++ (Alpha.encode message.mpid
    ++ (encodeUIntLE 4 message.productId
    ++ (TimeInForceTif.encode message.timeInForceTif
    ++ (OrderInstruction.encode message.orderInstruction
    ++ (Origin.encode message.origin
    ++ (encodeUInt 1 message.mvp
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 4 message.size
    ++ (Side.encode message.side
    ++ (OpenClose.encode message.openClose
    ++ (CoveredUncovered.encode message.coveredUncovered
    ++ (Alpha.encode message.clearingAccount
    ++ (encodeUIntLE 4 message.cmta
    ++ (Alpha.encode message.account))))))))))))))))))

def decode (bytes : List UInt8) : Option (OrderNotification × List UInt8) := do
  let (notificationTime, bytes) ← decodeUIntLE 8 bytes
  let (clientOrderId, bytes) ← decodeUIntLE 4 bytes
  let (clientMessageId, bytes) ← decodeUIntLE 4 bytes
  let (bulkOrderIndex, bytes) ← decodeUInt 1 bytes
  let (targetClientOrderId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (timeInForceTif, bytes) ← TimeInForceTif.decode bytes
  let (orderInstruction, bytes) ← OrderInstruction.decode bytes
  let (origin, bytes) ← Origin.decode bytes
  let (mvp, bytes) ← decodeUInt 1 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (size, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (openClose, bytes) ← OpenClose.decode bytes
  let (coveredUncovered, bytes) ← CoveredUncovered.decode bytes
  let (clearingAccount, bytes) ← Alpha.decode 5 bytes
  let (cmta, bytes) ← decodeUIntLE 4 bytes
  let (account, bytes) ← Alpha.decode 10 bytes
  pure ({ notificationTime, clientOrderId, clientMessageId, bulkOrderIndex, targetClientOrderId, mpid, productId, timeInForceTif, orderInstruction, origin, mvp, price, size, side, openClose, coveredUncovered, clearingAccount, cmta, account }, bytes)

@[simp] theorem encode_length (message : OrderNotification) : (encode message).length = 63 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, TimeInForceTif.encode_length, OrderInstruction.encode_length, Origin.encode_length, Side.encode_length, OpenClose.encode_length, CoveredUncovered.encode_length]

theorem encode_length_pos (message : OrderNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TimeInForceTif.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderInstruction.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Origin.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpenClose.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CoveredUncovered.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderNotification

/-- Done For The Day Notification: 63 bytes -/
structure DoneForTheDayNotification where
  notificationTime : BitVec 64
  clientOrderId : BitVec 32
  clientMessageId : BitVec 32
  bulkOrderIndex : BitVec 8
  targetClientOrderId : BitVec 32
  mpid : Alpha 4
  productId : BitVec 32
  timeInForceTif : TimeInForceTif
  orderInstruction : OrderInstruction
  origin : Origin
  mvp : BitVec 8
  price : BitVec 32
  size : BitVec 32
  side : Side
  openClose : OpenClose
  coveredUncovered : CoveredUncovered
  clearingAccount : Alpha 5
  cmta : BitVec 32
  account : Alpha 10
  deriving DecidableEq, Repr

namespace DoneForTheDayNotification

def encode (message : DoneForTheDayNotification) : List UInt8 :=
  encodeUIntLE 8 message.notificationTime
    ++ (encodeUIntLE 4 message.clientOrderId
    ++ (encodeUIntLE 4 message.clientMessageId
    ++ (encodeUInt 1 message.bulkOrderIndex
    ++ (encodeUIntLE 4 message.targetClientOrderId
    ++ (Alpha.encode message.mpid
    ++ (encodeUIntLE 4 message.productId
    ++ (TimeInForceTif.encode message.timeInForceTif
    ++ (OrderInstruction.encode message.orderInstruction
    ++ (Origin.encode message.origin
    ++ (encodeUInt 1 message.mvp
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 4 message.size
    ++ (Side.encode message.side
    ++ (OpenClose.encode message.openClose
    ++ (CoveredUncovered.encode message.coveredUncovered
    ++ (Alpha.encode message.clearingAccount
    ++ (encodeUIntLE 4 message.cmta
    ++ (Alpha.encode message.account))))))))))))))))))

def decode (bytes : List UInt8) : Option (DoneForTheDayNotification × List UInt8) := do
  let (notificationTime, bytes) ← decodeUIntLE 8 bytes
  let (clientOrderId, bytes) ← decodeUIntLE 4 bytes
  let (clientMessageId, bytes) ← decodeUIntLE 4 bytes
  let (bulkOrderIndex, bytes) ← decodeUInt 1 bytes
  let (targetClientOrderId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (timeInForceTif, bytes) ← TimeInForceTif.decode bytes
  let (orderInstruction, bytes) ← OrderInstruction.decode bytes
  let (origin, bytes) ← Origin.decode bytes
  let (mvp, bytes) ← decodeUInt 1 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (size, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (openClose, bytes) ← OpenClose.decode bytes
  let (coveredUncovered, bytes) ← CoveredUncovered.decode bytes
  let (clearingAccount, bytes) ← Alpha.decode 5 bytes
  let (cmta, bytes) ← decodeUIntLE 4 bytes
  let (account, bytes) ← Alpha.decode 10 bytes
  pure ({ notificationTime, clientOrderId, clientMessageId, bulkOrderIndex, targetClientOrderId, mpid, productId, timeInForceTif, orderInstruction, origin, mvp, price, size, side, openClose, coveredUncovered, clearingAccount, cmta, account }, bytes)

@[simp] theorem encode_length (message : DoneForTheDayNotification) : (encode message).length = 63 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, TimeInForceTif.encode_length, OrderInstruction.encode_length, Origin.encode_length, Side.encode_length, OpenClose.encode_length, CoveredUncovered.encode_length]

theorem encode_length_pos (message : DoneForTheDayNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DoneForTheDayNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TimeInForceTif.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderInstruction.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Origin.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpenClose.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CoveredUncovered.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end DoneForTheDayNotification

/-- Any Unsequenced Message, selected by Unsequenced Message Type -/
inductive UnsequencedMessage where
  | armSettingsUpdateRequest (message : ArmSettingsUpdateRequest) -- "AS" 0x4153
  | armSettingsUpdateResponse (message : ArmSettingsUpdateResponse) -- "AA" 0x4141
  | arm2UnderlyingLevelProtectionSettingsUpdateRequest (message : Arm2UnderlyingLevelProtectionSettingsUpdateRequest) -- "2S" 0x3253
  | arm2UnderlyingLevelProtectionSettingsUpdateResponse (message : Arm2UnderlyingLevelProtectionSettingsUpdateResponse) -- "2R" 0x3252
  | seriesAssignmentRequest (message : SeriesAssignmentRequest) -- "SA" 0x5341
  | seriesAssignmentResponse (message : SeriesAssignmentResponse) -- "AR" 0x4152
  | selfTradeProtectionDesignationRequest (message : SelfTradeProtectionDesignationRequest) -- "SP" 0x5350
  | selfTradeProtectionDesignationResponse (message : SelfTradeProtectionDesignationResponse) -- "SR" 0x5352
  | bulkLiquidityMessage (message : BulkLiquidityMessage) -- "lm" 0x6C6D
  | bulkLiquidityMessageResponse (message : BulkLiquidityMessageResponse) -- "LR" 0x4C52
  | liquidityMassCancelRequest (message : LiquidityMassCancelRequest) -- "xq" 0x7871
  | liquidityMassCancelResponse (message : LiquidityMassCancelResponse) -- "XR" 0x5852
  | liquidityProtectionResetRequest (message : LiquidityProtectionResetRequest) -- "PX" 0x5058
  | liquidityProtectionResetResponse (message : LiquidityProtectionResetResponse) -- "PR" 0x5052
  | singleSideLiquidityProtectionResetRequest (message : SingleSideLiquidityProtectionResetRequest) -- "SS" 0x5353
  | singleSideLiquidityProtectionResetResponse (message : SingleSideLiquidityProtectionResetResponse) -- "ST" 0x5354
  | liquidityProtectionTriggerNotification (message : LiquidityProtectionTriggerNotification) -- "QP" 0x5150
  | orderNotification (message : OrderNotification) -- "ON" 0x4F4E
  | doneForTheDayNotification (message : DoneForTheDayNotification) -- "DD" 0x4444
  | cancelNotification (message : CancelNotification) -- "XN" 0x584E
  deriving DecidableEq, Repr

namespace UnsequencedMessage

/-- The Unsequenced Message Type each message is sent under -/
def tag : UnsequencedMessage → BitVec 16
  | .armSettingsUpdateRequest _ => 16723
  | .armSettingsUpdateResponse _ => 16705
  | .arm2UnderlyingLevelProtectionSettingsUpdateRequest _ => 12883
  | .arm2UnderlyingLevelProtectionSettingsUpdateResponse _ => 12882
  | .seriesAssignmentRequest _ => 21313
  | .seriesAssignmentResponse _ => 16722
  | .selfTradeProtectionDesignationRequest _ => 21328
  | .selfTradeProtectionDesignationResponse _ => 21330
  | .bulkLiquidityMessage _ => 27757
  | .bulkLiquidityMessageResponse _ => 19538
  | .liquidityMassCancelRequest _ => 30833
  | .liquidityMassCancelResponse _ => 22610
  | .liquidityProtectionResetRequest _ => 20568
  | .liquidityProtectionResetResponse _ => 20562
  | .singleSideLiquidityProtectionResetRequest _ => 21331
  | .singleSideLiquidityProtectionResetResponse _ => 21332
  | .liquidityProtectionTriggerNotification _ => 20816
  | .orderNotification _ => 20302
  | .doneForTheDayNotification _ => 17476
  | .cancelNotification _ => 22606

def encode : UnsequencedMessage → List UInt8
  | .armSettingsUpdateRequest message => ArmSettingsUpdateRequest.encode message
  | .armSettingsUpdateResponse message => ArmSettingsUpdateResponse.encode message
  | .arm2UnderlyingLevelProtectionSettingsUpdateRequest message => Arm2UnderlyingLevelProtectionSettingsUpdateRequest.encode message
  | .arm2UnderlyingLevelProtectionSettingsUpdateResponse message => Arm2UnderlyingLevelProtectionSettingsUpdateResponse.encode message
  | .seriesAssignmentRequest message => SeriesAssignmentRequest.encode message
  | .seriesAssignmentResponse message => SeriesAssignmentResponse.encode message
  | .selfTradeProtectionDesignationRequest message => SelfTradeProtectionDesignationRequest.encode message
  | .selfTradeProtectionDesignationResponse message => SelfTradeProtectionDesignationResponse.encode message
  | .bulkLiquidityMessage message => BulkLiquidityMessage.encode message
  | .bulkLiquidityMessageResponse message => BulkLiquidityMessageResponse.encode message
  | .liquidityMassCancelRequest message => LiquidityMassCancelRequest.encode message
  | .liquidityMassCancelResponse message => LiquidityMassCancelResponse.encode message
  | .liquidityProtectionResetRequest message => LiquidityProtectionResetRequest.encode message
  | .liquidityProtectionResetResponse message => LiquidityProtectionResetResponse.encode message
  | .singleSideLiquidityProtectionResetRequest message => SingleSideLiquidityProtectionResetRequest.encode message
  | .singleSideLiquidityProtectionResetResponse message => SingleSideLiquidityProtectionResetResponse.encode message
  | .liquidityProtectionTriggerNotification message => LiquidityProtectionTriggerNotification.encode message
  | .orderNotification message => OrderNotification.encode message
  | .doneForTheDayNotification message => DoneForTheDayNotification.encode message
  | .cancelNotification message => CancelNotification.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : UnsequencedMessage) : (encode message).length ≤ 14552 := by
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
  | seriesAssignmentRequest inner =>
    simp only [encode, SeriesAssignmentRequest.encode_length]
    omega
  | seriesAssignmentResponse inner =>
    simp only [encode, SeriesAssignmentResponse.encode_length]
    omega
  | selfTradeProtectionDesignationRequest inner =>
    simp only [encode, SelfTradeProtectionDesignationRequest.encode_length]
    omega
  | selfTradeProtectionDesignationResponse inner =>
    simp only [encode, SelfTradeProtectionDesignationResponse.encode_length]
    omega
  | bulkLiquidityMessage inner =>
    have bound_inner := BulkLiquidityMessage.encode_length_le inner
    simp only [encode]
    omega
  | bulkLiquidityMessageResponse inner =>
    have bound_inner := BulkLiquidityMessageResponse.encode_length_le inner
    simp only [encode]
    omega
  | liquidityMassCancelRequest inner =>
    simp only [encode, LiquidityMassCancelRequest.encode_length]
    omega
  | liquidityMassCancelResponse inner =>
    simp only [encode, LiquidityMassCancelResponse.encode_length]
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
  | liquidityProtectionTriggerNotification inner =>
    simp only [encode, LiquidityProtectionTriggerNotification.encode_length]
    omega
  | orderNotification inner =>
    simp only [encode, OrderNotification.encode_length]
    omega
  | doneForTheDayNotification inner =>
    simp only [encode, DoneForTheDayNotification.encode_length]
    omega
  | cancelNotification inner =>
    simp only [encode, CancelNotification.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (UnsequencedMessage × List UInt8) :=
  if tag = 16723 then (ArmSettingsUpdateRequest.decode bytes).map fun (message, rest) => (.armSettingsUpdateRequest message, rest)
  else if tag = 16705 then (ArmSettingsUpdateResponse.decode bytes).map fun (message, rest) => (.armSettingsUpdateResponse message, rest)
  else if tag = 12883 then (Arm2UnderlyingLevelProtectionSettingsUpdateRequest.decode bytes).map fun (message, rest) => (.arm2UnderlyingLevelProtectionSettingsUpdateRequest message, rest)
  else if tag = 12882 then (Arm2UnderlyingLevelProtectionSettingsUpdateResponse.decode bytes).map fun (message, rest) => (.arm2UnderlyingLevelProtectionSettingsUpdateResponse message, rest)
  else if tag = 21313 then (SeriesAssignmentRequest.decode bytes).map fun (message, rest) => (.seriesAssignmentRequest message, rest)
  else if tag = 16722 then (SeriesAssignmentResponse.decode bytes).map fun (message, rest) => (.seriesAssignmentResponse message, rest)
  else if tag = 21328 then (SelfTradeProtectionDesignationRequest.decode bytes).map fun (message, rest) => (.selfTradeProtectionDesignationRequest message, rest)
  else if tag = 21330 then (SelfTradeProtectionDesignationResponse.decode bytes).map fun (message, rest) => (.selfTradeProtectionDesignationResponse message, rest)
  else if tag = 27757 then (BulkLiquidityMessage.decode bytes).map fun (message, rest) => (.bulkLiquidityMessage message, rest)
  else if tag = 19538 then (BulkLiquidityMessageResponse.decode bytes).map fun (message, rest) => (.bulkLiquidityMessageResponse message, rest)
  else if tag = 30833 then (LiquidityMassCancelRequest.decode bytes).map fun (message, rest) => (.liquidityMassCancelRequest message, rest)
  else if tag = 22610 then (LiquidityMassCancelResponse.decode bytes).map fun (message, rest) => (.liquidityMassCancelResponse message, rest)
  else if tag = 20568 then (LiquidityProtectionResetRequest.decode bytes).map fun (message, rest) => (.liquidityProtectionResetRequest message, rest)
  else if tag = 20562 then (LiquidityProtectionResetResponse.decode bytes).map fun (message, rest) => (.liquidityProtectionResetResponse message, rest)
  else if tag = 21331 then (SingleSideLiquidityProtectionResetRequest.decode bytes).map fun (message, rest) => (.singleSideLiquidityProtectionResetRequest message, rest)
  else if tag = 21332 then (SingleSideLiquidityProtectionResetResponse.decode bytes).map fun (message, rest) => (.singleSideLiquidityProtectionResetResponse message, rest)
  else if tag = 20816 then (LiquidityProtectionTriggerNotification.decode bytes).map fun (message, rest) => (.liquidityProtectionTriggerNotification message, rest)
  else if tag = 20302 then (OrderNotification.decode bytes).map fun (message, rest) => (.orderNotification message, rest)
  else if tag = 17476 then (DoneForTheDayNotification.decode bytes).map fun (message, rest) => (.doneForTheDayNotification message, rest)
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
theorem encode_length_le (message : UnsequencedDataPacket) : (encode message).length ≤ 14554 := by
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
  | seriesAssignmentRequest inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, SeriesAssignmentRequest.encode_length]
    omega
  | seriesAssignmentResponse inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, SeriesAssignmentResponse.encode_length]
    omega
  | selfTradeProtectionDesignationRequest inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, SelfTradeProtectionDesignationRequest.encode_length]
    omega
  | selfTradeProtectionDesignationResponse inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, SelfTradeProtectionDesignationResponse.encode_length]
    omega
  | bulkLiquidityMessage inner =>
    have bound_inner := BulkLiquidityMessage.encode_length_le inner
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length]
    omega
  | bulkLiquidityMessageResponse inner =>
    have bound_inner := BulkLiquidityMessageResponse.encode_length_le inner
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length]
    omega
  | liquidityMassCancelRequest inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, LiquidityMassCancelRequest.encode_length]
    omega
  | liquidityMassCancelResponse inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, LiquidityMassCancelResponse.encode_length]
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
  | liquidityProtectionTriggerNotification inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, LiquidityProtectionTriggerNotification.encode_length]
    omega
  | orderNotification inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, OrderNotification.encode_length]
    omega
  | doneForTheDayNotification inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, DoneForTheDayNotification.encode_length]
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
  logoutText : Capped 50980
  deriving DecidableEq, Repr

namespace LogoutRequest

def encode (message : LogoutRequest) : List UInt8 :=
  LogoutReason.encode message.logoutReason
    ++ (message.logoutText.val)

def decode (bytes : List UInt8) : Option LogoutRequest := do
  let (logoutReason, bytes) ← LogoutReason.decode bytes
  let logoutText_ := bytes
  if fits_logoutText : logoutText_.length ≤ 50980 then
    pure { logoutReason, logoutText := ⟨logoutText_, fits_logoutText⟩ }
  else none

theorem encode_length_pos (message : LogoutRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [LogoutReason.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : LogoutRequest) : (encode message).length ≤ 50981 := by
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
  logoutText : Capped 50980
  deriving DecidableEq, Repr

namespace GoodbyePacket

def encode (message : GoodbyePacket) : List UInt8 :=
  GoodbyeReason.encode message.goodbyeReason
    ++ (message.logoutText.val)

def decode (bytes : List UInt8) : Option GoodbyePacket := do
  let (goodbyeReason, bytes) ← GoodbyeReason.decode bytes
  let logoutText_ := bytes
  if fits_logoutText : logoutText_.length ≤ 50980 then
    pure { goodbyeReason, logoutText := ⟨logoutText_, fits_logoutText⟩ }
  else none

theorem encode_length_pos (message : GoodbyePacket) : (encode message).length > 0 := by
  unfold encode
  simp only [GoodbyeReason.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : GoodbyePacket) : (encode message).length ≤ 50981 := by
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
  testText : Capped 50980
  deriving DecidableEq, Repr

namespace TestPacket

def encode (message : TestPacket) : List UInt8 :=
  message.testText.val

def decode (bytes : List UInt8) : Option TestPacket := do
  let testText_ := bytes
  if fits_testText : testText_.length ≤ 50980 then
    pure { testText := ⟨testText_, fits_testText⟩ }
  else none

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TestPacket) : (encode message).length ≤ 50980 := by
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
theorem encode_length_le (message : SesmPayload) : (encode message).length ≤ 50981 := by
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

end Omi.MiaxPearloptionsExpressordersMeoV20D
