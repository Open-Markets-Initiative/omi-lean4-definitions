import Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Nasdaq Basic Canada v1.6

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.

Note: a Message Count of 0 marks Heartbeat and carries no messages; the decoder reads it as a count
and the encoder never writes it

Note: a Message Count of 65535 marks End Of Session and carries no messages; the decoder reads it as
a count and the encoder never writes it

License: MIT No Attribution
-/

namespace Omi.NasdaqNasdaqcanadaBasicItchV16

/-- Originating Market Center Identifier: one byte code -/
def OriginatingMarketCenterIdentifier.codes : List UInt8 :=
  [0x43, 0x58, 0x44, 0x41]

inductive OriginatingMarketCenterIdentifier where
  | theNasdaqCxcTradingBook -- The Nasdaq Cxc Trading Book
  | theNasdaqCx2TradingBook -- The Nasdaq Cx 2 Trading Book
  | theNasdaqCxdTradingBook -- The Nasdaq Cxd Trading Book
  | allMarkets -- All Markets
  | unlisted (byte : { byte : UInt8 // byte ∉ OriginatingMarketCenterIdentifier.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OriginatingMarketCenterIdentifier

def toByte : OriginatingMarketCenterIdentifier → UInt8
  | .theNasdaqCxcTradingBook => 0x43
  | .theNasdaqCx2TradingBook => 0x58
  | .theNasdaqCxdTradingBook => 0x44
  | .allMarkets => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OriginatingMarketCenterIdentifier :=
  if byte = 0x43 then .theNasdaqCxcTradingBook
  else if byte = 0x58 then .theNasdaqCx2TradingBook
  else if byte = 0x44 then .theNasdaqCxdTradingBook
  else .allMarkets

def ofByte (byte : UInt8) : OriginatingMarketCenterIdentifier :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OriginatingMarketCenterIdentifier) : ofByte value.toByte = value := by
  cases value with
  | theNasdaqCxcTradingBook => decide
  | theNasdaqCx2TradingBook => decide
  | theNasdaqCxdTradingBook => decide
  | allMarkets => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OriginatingMarketCenterIdentifier) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OriginatingMarketCenterIdentifier × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OriginatingMarketCenterIdentifier) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OriginatingMarketCenterIdentifier) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OriginatingMarketCenterIdentifier) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OriginatingMarketCenterIdentifier

/-- Sale Condition Modifier Level 1: one byte code -/
def SaleConditionModifierLevel1.codes : List UInt8 :=
  [0x20, 0x42, 0x4C, 0x50]

inductive SaleConditionModifierLevel1 where
  | regularTrade -- Regular Trade
  | bypass -- Bypass
  | mElo -- M Elo
  | cxdPureStream -- Cxd Pure Stream
  | unlisted (byte : { byte : UInt8 // byte ∉ SaleConditionModifierLevel1.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SaleConditionModifierLevel1

def toByte : SaleConditionModifierLevel1 → UInt8
  | .regularTrade => 0x20
  | .bypass => 0x42
  | .mElo => 0x4C
  | .cxdPureStream => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SaleConditionModifierLevel1 :=
  if byte = 0x20 then .regularTrade
  else if byte = 0x42 then .bypass
  else if byte = 0x4C then .mElo
  else .cxdPureStream

def ofByte (byte : UInt8) : SaleConditionModifierLevel1 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SaleConditionModifierLevel1) : ofByte value.toByte = value := by
  cases value with
  | regularTrade => decide
  | bypass => decide
  | mElo => decide
  | cxdPureStream => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SaleConditionModifierLevel1) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SaleConditionModifierLevel1 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SaleConditionModifierLevel1) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SaleConditionModifierLevel1) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SaleConditionModifierLevel1) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SaleConditionModifierLevel1

/-- Sales Condition Modifier Level 2: one byte code -/
def SalesConditionModifierLevel2.codes : List UInt8 :=
  [0x20, 0x49, 0x42, 0x43, 0x56, 0x58, 0x44]

inductive SalesConditionModifierLevel2 where
  | regular -- Regular
  | internal -- Internal
  | basis -- Basis
  | contingent -- Contingent
  | vwap -- Vwap
  | intentional -- Intentional
  | derivativeRelated -- Derivative Related
  | unlisted (byte : { byte : UInt8 // byte ∉ SalesConditionModifierLevel2.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SalesConditionModifierLevel2

def toByte : SalesConditionModifierLevel2 → UInt8
  | .regular => 0x20
  | .internal => 0x49
  | .basis => 0x42
  | .contingent => 0x43
  | .vwap => 0x56
  | .intentional => 0x58
  | .derivativeRelated => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SalesConditionModifierLevel2 :=
  if byte = 0x20 then .regular
  else if byte = 0x49 then .internal
  else if byte = 0x42 then .basis
  else if byte = 0x43 then .contingent
  else if byte = 0x56 then .vwap
  else if byte = 0x58 then .intentional
  else .derivativeRelated

def ofByte (byte : UInt8) : SalesConditionModifierLevel2 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SalesConditionModifierLevel2) : ofByte value.toByte = value := by
  cases value with
  | regular => decide
  | internal => decide
  | basis => decide
  | contingent => decide
  | vwap => decide
  | intentional => decide
  | derivativeRelated => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SalesConditionModifierLevel2) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SalesConditionModifierLevel2 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SalesConditionModifierLevel2) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SalesConditionModifierLevel2) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SalesConditionModifierLevel2) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SalesConditionModifierLevel2

/-- Sales Condition Modifier Level 3: one byte code -/
def SalesConditionModifierLevel3.codes : List UInt8 :=
  [0x20, 0x54, 0x43, 0x44]

inductive SalesConditionModifierLevel3 where
  | regular -- Regular
  | cashToday -- Cash Today
  | cashTomorrow -- Cash Tomorrow
  | delayedDelivery -- Delayed Delivery
  | unlisted (byte : { byte : UInt8 // byte ∉ SalesConditionModifierLevel3.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SalesConditionModifierLevel3

def toByte : SalesConditionModifierLevel3 → UInt8
  | .regular => 0x20
  | .cashToday => 0x54
  | .cashTomorrow => 0x43
  | .delayedDelivery => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SalesConditionModifierLevel3 :=
  if byte = 0x20 then .regular
  else if byte = 0x54 then .cashToday
  else if byte = 0x43 then .cashTomorrow
  else .delayedDelivery

def ofByte (byte : UInt8) : SalesConditionModifierLevel3 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SalesConditionModifierLevel3) : ofByte value.toByte = value := by
  cases value with
  | regular => decide
  | cashToday => decide
  | cashTomorrow => decide
  | delayedDelivery => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SalesConditionModifierLevel3) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SalesConditionModifierLevel3 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SalesConditionModifierLevel3) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SalesConditionModifierLevel3) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SalesConditionModifierLevel3) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SalesConditionModifierLevel3

/-- Sales Condition Modifier Level 4: one byte code -/
def SalesConditionModifierLevel4.codes : List UInt8 :=
  [0x41, 0x42]

inductive SalesConditionModifierLevel4 where
  | oddLot -- Odd Lot
  | boardLotOrLarger -- Board Lot Or Larger
  | unlisted (byte : { byte : UInt8 // byte ∉ SalesConditionModifierLevel4.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SalesConditionModifierLevel4

def toByte : SalesConditionModifierLevel4 → UInt8
  | .oddLot => 0x41
  | .boardLotOrLarger => 0x42
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SalesConditionModifierLevel4 :=
  if byte = 0x41 then .oddLot
  else .boardLotOrLarger

def ofByte (byte : UInt8) : SalesConditionModifierLevel4 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SalesConditionModifierLevel4) : ofByte value.toByte = value := by
  cases value with
  | oddLot => decide
  | boardLotOrLarger => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SalesConditionModifierLevel4) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SalesConditionModifierLevel4 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SalesConditionModifierLevel4) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SalesConditionModifierLevel4) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SalesConditionModifierLevel4) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SalesConditionModifierLevel4

/-- Event Code: one byte code -/
def EventCode.codes : List UInt8 :=
  [0x4F, 0x53, 0x51, 0x4D, 0x45, 0x43]

inductive EventCode where
  | firstMessageOfTheDay -- First Message Of The Day
  | startOfNasdaqCanadaTradingSession -- Start Of Nasdaq Canada Trading Session
  | startOfPrimaryMarketTradingActivitySession -- Start Of Primary Market Trading Activity Session
  | endOfPrimaryMarketTradingSession -- End Of Primary Market Trading Session
  | endOfNasdaqCanadaTradingSession -- End Of Nasdaq Canada Trading Session
  | endOfMessages -- End Of Messages
  | unlisted (byte : { byte : UInt8 // byte ∉ EventCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventCode

def toByte : EventCode → UInt8
  | .firstMessageOfTheDay => 0x4F
  | .startOfNasdaqCanadaTradingSession => 0x53
  | .startOfPrimaryMarketTradingActivitySession => 0x51
  | .endOfPrimaryMarketTradingSession => 0x4D
  | .endOfNasdaqCanadaTradingSession => 0x45
  | .endOfMessages => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventCode :=
  if byte = 0x4F then .firstMessageOfTheDay
  else if byte = 0x53 then .startOfNasdaqCanadaTradingSession
  else if byte = 0x51 then .startOfPrimaryMarketTradingActivitySession
  else if byte = 0x4D then .endOfPrimaryMarketTradingSession
  else if byte = 0x45 then .endOfNasdaqCanadaTradingSession
  else .endOfMessages

def ofByte (byte : UInt8) : EventCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventCode) : ofByte value.toByte = value := by
  cases value with
  | firstMessageOfTheDay => decide
  | startOfNasdaqCanadaTradingSession => decide
  | startOfPrimaryMarketTradingActivitySession => decide
  | endOfPrimaryMarketTradingSession => decide
  | endOfNasdaqCanadaTradingSession => decide
  | endOfMessages => decide
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

/-- Listing Market: one byte code -/
def ListingMarket.codes : List UInt8 :=
  [0x54, 0x43, 0x56, 0x4E]

inductive ListingMarket where
  | theTmxSeniorMarket -- The Tmx Senior Market
  | theCanadianSecuritiesExchange -- The Canadian Securities Exchange
  | theTmxVentureMarket -- The Tmx Venture Market
  | theNeoExchange -- The Neo Exchange
  | unlisted (byte : { byte : UInt8 // byte ∉ ListingMarket.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ListingMarket

def toByte : ListingMarket → UInt8
  | .theTmxSeniorMarket => 0x54
  | .theCanadianSecuritiesExchange => 0x43
  | .theTmxVentureMarket => 0x56
  | .theNeoExchange => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ListingMarket :=
  if byte = 0x54 then .theTmxSeniorMarket
  else if byte = 0x43 then .theCanadianSecuritiesExchange
  else if byte = 0x56 then .theTmxVentureMarket
  else .theNeoExchange

def ofByte (byte : UInt8) : ListingMarket :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ListingMarket) : ofByte value.toByte = value := by
  cases value with
  | theTmxSeniorMarket => decide
  | theCanadianSecuritiesExchange => decide
  | theTmxVentureMarket => decide
  | theNeoExchange => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ListingMarket) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ListingMarket × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ListingMarket) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ListingMarket) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ListingMarket) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ListingMarket

/-- Currency: one byte code -/
def Currency.codes : List UInt8 :=
  [0x55, 0x43]

inductive Currency where
  | usd -- Usd
  | cad -- Cad
  | unlisted (byte : { byte : UInt8 // byte ∉ Currency.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Currency

def toByte : Currency → UInt8
  | .usd => 0x55
  | .cad => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Currency :=
  if byte = 0x55 then .usd
  else .cad

def ofByte (byte : UInt8) : Currency :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Currency) : ofByte value.toByte = value := by
  cases value with
  | usd => decide
  | cad => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Currency) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Currency × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Currency) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Currency) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Currency) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Currency

/-- Market: one byte code -/
def Market.codes : List UInt8 :=
  [0x43, 0x58, 0x44, 0x41]

inductive Market where
  | theNasdaqCxcTradingBook -- The Nasdaq Cxc Trading Book
  | theNasdaqCx2TradingBook -- The Nasdaq Cx 2 Trading Book
  | theNasdaqCxdTradingBook -- The Nasdaq Cxd Trading Book
  | allMarkets -- All Markets
  | unlisted (byte : { byte : UInt8 // byte ∉ Market.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Market

def toByte : Market → UInt8
  | .theNasdaqCxcTradingBook => 0x43
  | .theNasdaqCx2TradingBook => 0x58
  | .theNasdaqCxdTradingBook => 0x44
  | .allMarkets => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Market :=
  if byte = 0x43 then .theNasdaqCxcTradingBook
  else if byte = 0x58 then .theNasdaqCx2TradingBook
  else if byte = 0x44 then .theNasdaqCxdTradingBook
  else .allMarkets

def ofByte (byte : UInt8) : Market :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Market) : ofByte value.toByte = value := by
  cases value with
  | theNasdaqCxcTradingBook => decide
  | theNasdaqCx2TradingBook => decide
  | theNasdaqCxdTradingBook => decide
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

/-- System Status: one byte code -/
def SystemStatus.codes : List UInt8 :=
  [0x48, 0x54]

inductive SystemStatus where
  | halted -- Halted
  | trading -- Trading
  | unlisted (byte : { byte : UInt8 // byte ∉ SystemStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SystemStatus

def toByte : SystemStatus → UInt8
  | .halted => 0x48
  | .trading => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SystemStatus :=
  if byte = 0x48 then .halted
  else .trading

def ofByte (byte : UInt8) : SystemStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SystemStatus) : ofByte value.toByte = value := by
  cases value with
  | halted => decide
  | trading => decide
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

/-- Security Class: one byte code -/
def SecurityClass.codes : List UInt8 :=
  [0x54, 0x43, 0x56, 0x4E]

inductive SecurityClass where
  | theTmxSeniorMarket -- The Tmx Senior Market
  | theCanadianSecuritiesExchange -- The Canadian Securities Exchange
  | theTmxVentureMarket -- The Tmx Venture Market
  | theNeoExchange -- The Neo Exchange
  | unlisted (byte : { byte : UInt8 // byte ∉ SecurityClass.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SecurityClass

def toByte : SecurityClass → UInt8
  | .theTmxSeniorMarket => 0x54
  | .theCanadianSecuritiesExchange => 0x43
  | .theTmxVentureMarket => 0x56
  | .theNeoExchange => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SecurityClass :=
  if byte = 0x54 then .theTmxSeniorMarket
  else if byte = 0x43 then .theCanadianSecuritiesExchange
  else if byte = 0x56 then .theTmxVentureMarket
  else .theNeoExchange

def ofByte (byte : UInt8) : SecurityClass :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SecurityClass) : ofByte value.toByte = value := by
  cases value with
  | theTmxSeniorMarket => decide
  | theCanadianSecuritiesExchange => decide
  | theTmxVentureMarket => decide
  | theNeoExchange => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SecurityClass) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SecurityClass × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SecurityClass) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SecurityClass) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SecurityClass) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SecurityClass

/-- Quotation Message: 58 bytes -/
structure QuotationMessage where
  timeStamp : BitVec 64
  stockSymbol : Alpha 10
  nasdaqCanadaBestBidPrice : BitVec 64
  nasdaqCanadaBestBidSize : BitVec 32
  nasdaqCxcBestBidSize : BitVec 32
  nasdaqCx2BestBidSize : BitVec 32
  nasdaqCanadaBestAskPrice : BitVec 64
  nasdaqCanadaBestAskSize : BitVec 32
  nasdaqCxcBestAskSize : BitVec 32
  nasdaqCx2BestAskSize : BitVec 32
  deriving DecidableEq, Repr

namespace QuotationMessage

def encode (message : QuotationMessage) : List UInt8 :=
  encodeUInt 8 message.timeStamp
    ++ (Alpha.encode message.stockSymbol
    ++ (encodeUInt 8 message.nasdaqCanadaBestBidPrice
    ++ (encodeUInt 4 message.nasdaqCanadaBestBidSize
    ++ (encodeUInt 4 message.nasdaqCxcBestBidSize
    ++ (encodeUInt 4 message.nasdaqCx2BestBidSize
    ++ (encodeUInt 8 message.nasdaqCanadaBestAskPrice
    ++ (encodeUInt 4 message.nasdaqCanadaBestAskSize
    ++ (encodeUInt 4 message.nasdaqCxcBestAskSize
    ++ (encodeUInt 4 message.nasdaqCx2BestAskSize)))))))))

def decode (bytes : List UInt8) : Option (QuotationMessage × List UInt8) := do
  let (timeStamp, bytes) ← decodeUInt 8 bytes
  let (stockSymbol, bytes) ← Alpha.decode 10 bytes
  let (nasdaqCanadaBestBidPrice, bytes) ← decodeUInt 8 bytes
  let (nasdaqCanadaBestBidSize, bytes) ← decodeUInt 4 bytes
  let (nasdaqCxcBestBidSize, bytes) ← decodeUInt 4 bytes
  let (nasdaqCx2BestBidSize, bytes) ← decodeUInt 4 bytes
  let (nasdaqCanadaBestAskPrice, bytes) ← decodeUInt 8 bytes
  let (nasdaqCanadaBestAskSize, bytes) ← decodeUInt 4 bytes
  let (nasdaqCxcBestAskSize, bytes) ← decodeUInt 4 bytes
  let (nasdaqCx2BestAskSize, bytes) ← decodeUInt 4 bytes
  pure ({ timeStamp, stockSymbol, nasdaqCanadaBestBidPrice, nasdaqCanadaBestBidSize, nasdaqCxcBestBidSize, nasdaqCx2BestBidSize, nasdaqCanadaBestAskPrice, nasdaqCanadaBestAskSize, nasdaqCxcBestAskSize, nasdaqCx2BestAskSize }, bytes)

@[simp] theorem encode_length (message : QuotationMessage) : (encode message).length = 58 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : QuotationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuotationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end QuotationMessage

/-- Sale Condition Modifier: 4 bytes -/
structure SaleConditionModifier where
  saleConditionModifierLevel1 : SaleConditionModifierLevel1
  salesConditionModifierLevel2 : SalesConditionModifierLevel2
  salesConditionModifierLevel3 : SalesConditionModifierLevel3
  salesConditionModifierLevel4 : SalesConditionModifierLevel4
  deriving DecidableEq, Repr

namespace SaleConditionModifier

def encode (message : SaleConditionModifier) : List UInt8 :=
  SaleConditionModifierLevel1.encode message.saleConditionModifierLevel1
    ++ (SalesConditionModifierLevel2.encode message.salesConditionModifierLevel2
    ++ (SalesConditionModifierLevel3.encode message.salesConditionModifierLevel3
    ++ (SalesConditionModifierLevel4.encode message.salesConditionModifierLevel4)))

def decode (bytes : List UInt8) : Option (SaleConditionModifier × List UInt8) := do
  let (saleConditionModifierLevel1, bytes) ← SaleConditionModifierLevel1.decode bytes
  let (salesConditionModifierLevel2, bytes) ← SalesConditionModifierLevel2.decode bytes
  let (salesConditionModifierLevel3, bytes) ← SalesConditionModifierLevel3.decode bytes
  let (salesConditionModifierLevel4, bytes) ← SalesConditionModifierLevel4.decode bytes
  pure ({ saleConditionModifierLevel1, salesConditionModifierLevel2, salesConditionModifierLevel3, salesConditionModifierLevel4 }, bytes)

@[simp] theorem encode_length (message : SaleConditionModifier) : (encode message).length = 4 := by
  unfold encode
  simp only [List.length_append, SaleConditionModifierLevel1.encode_length, SalesConditionModifierLevel2.encode_length, SalesConditionModifierLevel3.encode_length, SalesConditionModifierLevel4.encode_length]

theorem encode_length_pos (message : SaleConditionModifier) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SaleConditionModifier) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, SaleConditionModifierLevel1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SalesConditionModifierLevel2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SalesConditionModifierLevel3.decode_encode, some_bind]
  dsimp only
  rw [SalesConditionModifierLevel4.decode_encode, some_bind]
  rfl

end SaleConditionModifier

/-- Trade Report Message: 53 bytes -/
structure TradeReportMessage where
  timeStamp : BitVec 64
  originatingMarketCenterIdentifier : OriginatingMarketCenterIdentifier
  stockSymbol : Alpha 10
  tradeNumber : BitVec 32
  tradePrice : BitVec 64
  tradeSize : BitVec 32
  broker : Alpha 3
  contraBroker : Alpha 3
  saleConditionModifier : SaleConditionModifier
  consolidatedTradeVolume : BitVec 64
  deriving DecidableEq, Repr

namespace TradeReportMessage

def encode (message : TradeReportMessage) : List UInt8 :=
  encodeUInt 8 message.timeStamp
    ++ (OriginatingMarketCenterIdentifier.encode message.originatingMarketCenterIdentifier
    ++ (Alpha.encode message.stockSymbol
    ++ (encodeUInt 4 message.tradeNumber
    ++ (encodeUInt 8 message.tradePrice
    ++ (encodeUInt 4 message.tradeSize
    ++ (Alpha.encode message.broker
    ++ (Alpha.encode message.contraBroker
    ++ (SaleConditionModifier.encode message.saleConditionModifier
    ++ (encodeUInt 8 message.consolidatedTradeVolume)))))))))

def decode (bytes : List UInt8) : Option (TradeReportMessage × List UInt8) := do
  let (timeStamp, bytes) ← decodeUInt 8 bytes
  let (originatingMarketCenterIdentifier, bytes) ← OriginatingMarketCenterIdentifier.decode bytes
  let (stockSymbol, bytes) ← Alpha.decode 10 bytes
  let (tradeNumber, bytes) ← decodeUInt 4 bytes
  let (tradePrice, bytes) ← decodeUInt 8 bytes
  let (tradeSize, bytes) ← decodeUInt 4 bytes
  let (broker, bytes) ← Alpha.decode 3 bytes
  let (contraBroker, bytes) ← Alpha.decode 3 bytes
  let (saleConditionModifier, bytes) ← SaleConditionModifier.decode bytes
  let (consolidatedTradeVolume, bytes) ← decodeUInt 8 bytes
  pure ({ timeStamp, originatingMarketCenterIdentifier, stockSymbol, tradeNumber, tradePrice, tradeSize, broker, contraBroker, saleConditionModifier, consolidatedTradeVolume }, bytes)

@[simp] theorem encode_length (message : TradeReportMessage) : (encode message).length = 53 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, OriginatingMarketCenterIdentifier.encode_length, Alpha.encode_length, SaleConditionModifier.encode_length]

theorem encode_length_pos (message : TradeReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OriginatingMarketCenterIdentifier.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, SaleConditionModifier.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TradeReportMessage

/-- Trade Break Message: 13 bytes -/
structure TradeBreakMessage where
  timeStamp : BitVec 64
  tradeControlNumber : BitVec 32
  originatingMarketCenterIdentifier : OriginatingMarketCenterIdentifier
  deriving DecidableEq, Repr

namespace TradeBreakMessage

def encode (message : TradeBreakMessage) : List UInt8 :=
  encodeUInt 8 message.timeStamp
    ++ (encodeUInt 4 message.tradeControlNumber
    ++ (OriginatingMarketCenterIdentifier.encode message.originatingMarketCenterIdentifier))

def decode (bytes : List UInt8) : Option (TradeBreakMessage × List UInt8) := do
  let (timeStamp, bytes) ← decodeUInt 8 bytes
  let (tradeControlNumber, bytes) ← decodeUInt 4 bytes
  let (originatingMarketCenterIdentifier, bytes) ← OriginatingMarketCenterIdentifier.decode bytes
  pure ({ timeStamp, tradeControlNumber, originatingMarketCenterIdentifier }, bytes)

@[simp] theorem encode_length (message : TradeBreakMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, OriginatingMarketCenterIdentifier.encode_length]

theorem encode_length_pos (message : TradeBreakMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeBreakMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [OriginatingMarketCenterIdentifier.decode_encode, some_bind]
  rfl

end TradeBreakMessage

/-- Trade Correction Message: 47 bytes -/
structure TradeCorrectionMessage where
  timeStamp : BitVec 64
  originatingMarketCenterIdentifier : OriginatingMarketCenterIdentifier
  stockSymbol : Alpha 10
  originalTradeNumber : BitVec 32
  originalTradePrice : BitVec 64
  originalTradeSize : BitVec 32
  correctedTradePrice : BitVec 64
  correctedTradeSize : BitVec 32
  deriving DecidableEq, Repr

namespace TradeCorrectionMessage

def encode (message : TradeCorrectionMessage) : List UInt8 :=
  encodeUInt 8 message.timeStamp
    ++ (OriginatingMarketCenterIdentifier.encode message.originatingMarketCenterIdentifier
    ++ (Alpha.encode message.stockSymbol
    ++ (encodeUInt 4 message.originalTradeNumber
    ++ (encodeUInt 8 message.originalTradePrice
    ++ (encodeUInt 4 message.originalTradeSize
    ++ (encodeUInt 8 message.correctedTradePrice
    ++ (encodeUInt 4 message.correctedTradeSize)))))))

def decode (bytes : List UInt8) : Option (TradeCorrectionMessage × List UInt8) := do
  let (timeStamp, bytes) ← decodeUInt 8 bytes
  let (originatingMarketCenterIdentifier, bytes) ← OriginatingMarketCenterIdentifier.decode bytes
  let (stockSymbol, bytes) ← Alpha.decode 10 bytes
  let (originalTradeNumber, bytes) ← decodeUInt 4 bytes
  let (originalTradePrice, bytes) ← decodeUInt 8 bytes
  let (originalTradeSize, bytes) ← decodeUInt 4 bytes
  let (correctedTradePrice, bytes) ← decodeUInt 8 bytes
  let (correctedTradeSize, bytes) ← decodeUInt 4 bytes
  pure ({ timeStamp, originatingMarketCenterIdentifier, stockSymbol, originalTradeNumber, originalTradePrice, originalTradeSize, correctedTradePrice, correctedTradeSize }, bytes)

@[simp] theorem encode_length (message : TradeCorrectionMessage) : (encode message).length = 47 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, OriginatingMarketCenterIdentifier.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : TradeCorrectionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCorrectionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OriginatingMarketCenterIdentifier.decode_encode, some_bind]
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TradeCorrectionMessage

/-- System Event Message: 10 bytes -/
structure SystemEventMessage where
  timeStamp : BitVec 64
  originatingMarketCenterIdentifier : OriginatingMarketCenterIdentifier
  eventCode : EventCode
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  encodeUInt 8 message.timeStamp
    ++ (OriginatingMarketCenterIdentifier.encode message.originatingMarketCenterIdentifier
    ++ (EventCode.encode message.eventCode))

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (timeStamp, bytes) ← decodeUInt 8 bytes
  let (originatingMarketCenterIdentifier, bytes) ← OriginatingMarketCenterIdentifier.decode bytes
  let (eventCode, bytes) ← EventCode.decode bytes
  pure ({ timeStamp, originatingMarketCenterIdentifier, eventCode }, bytes)

@[simp] theorem encode_length (message : SystemEventMessage) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, OriginatingMarketCenterIdentifier.encode_length, EventCode.encode_length]

theorem encode_length_pos (message : SystemEventMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemEventMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OriginatingMarketCenterIdentifier.decode_encode, some_bind]
  dsimp only
  rw [EventCode.decode_encode, some_bind]
  rfl

end SystemEventMessage

/-- Stock Directory Message: 64 bytes -/
structure StockDirectoryMessage where
  timeStamp : BitVec 64
  stockSymbol : Alpha 10
  stockDisplayName : Alpha 40
  listingMarket : ListingMarket
  boardLotSize : Alpha 4
  currency : Currency
  deriving DecidableEq, Repr

namespace StockDirectoryMessage

def encode (message : StockDirectoryMessage) : List UInt8 :=
  encodeUInt 8 message.timeStamp
    ++ (Alpha.encode message.stockSymbol
    ++ (Alpha.encode message.stockDisplayName
    ++ (ListingMarket.encode message.listingMarket
    ++ (Alpha.encode message.boardLotSize
    ++ (Currency.encode message.currency)))))

def decode (bytes : List UInt8) : Option (StockDirectoryMessage × List UInt8) := do
  let (timeStamp, bytes) ← decodeUInt 8 bytes
  let (stockSymbol, bytes) ← Alpha.decode 10 bytes
  let (stockDisplayName, bytes) ← Alpha.decode 40 bytes
  let (listingMarket, bytes) ← ListingMarket.decode bytes
  let (boardLotSize, bytes) ← Alpha.decode 4 bytes
  let (currency, bytes) ← Currency.decode bytes
  pure ({ timeStamp, stockSymbol, stockDisplayName, listingMarket, boardLotSize, currency }, bytes)

@[simp] theorem encode_length (message : StockDirectoryMessage) : (encode message).length = 64 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, ListingMarket.encode_length, Currency.encode_length]

theorem encode_length_pos (message : StockDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StockDirectoryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ListingMarket.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Currency.decode_encode, some_bind]
  rfl

end StockDirectoryMessage

/-- Stock Status Message: 20 bytes -/
structure StockStatusMessage where
  timeStamp : BitVec 64
  stockSymbol : Alpha 10
  market : Market
  systemStatus : SystemStatus
  deriving DecidableEq, Repr

namespace StockStatusMessage

def encode (message : StockStatusMessage) : List UInt8 :=
  encodeUInt 8 message.timeStamp
    ++ (Alpha.encode message.stockSymbol
    ++ (Market.encode message.market
    ++ (SystemStatus.encode message.systemStatus)))

def decode (bytes : List UInt8) : Option (StockStatusMessage × List UInt8) := do
  let (timeStamp, bytes) ← decodeUInt 8 bytes
  let (stockSymbol, bytes) ← Alpha.decode 10 bytes
  let (market, bytes) ← Market.decode bytes
  let (systemStatus, bytes) ← SystemStatus.decode bytes
  pure ({ timeStamp, stockSymbol, market, systemStatus }, bytes)

@[simp] theorem encode_length (message : StockStatusMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, Market.encode_length, SystemStatus.encode_length]

theorem encode_length_pos (message : StockStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StockStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Market.decode_encode, some_bind]
  dsimp only
  rw [SystemStatus.decode_encode, some_bind]
  rfl

end StockStatusMessage

/-- End Of Day Trade Summary Message: 74 bytes -/
structure EndOfDayTradeSummaryMessage where
  timeStamp : BitVec 64
  stockSymbol : Alpha 10
  consolidatedHighPrice : BitVec 64
  consolidatedLowPrice : BitVec 64
  consolidatedOpenPrice : BitVec 64
  listingCenterOpenPrice : BitVec 64
  consolidatedClosePrice : BitVec 64
  listingCenterClosePrice : BitVec 64
  consolidatedVolume : BitVec 64
  deriving DecidableEq, Repr

namespace EndOfDayTradeSummaryMessage

def encode (message : EndOfDayTradeSummaryMessage) : List UInt8 :=
  encodeUInt 8 message.timeStamp
    ++ (Alpha.encode message.stockSymbol
    ++ (encodeUInt 8 message.consolidatedHighPrice
    ++ (encodeUInt 8 message.consolidatedLowPrice
    ++ (encodeUInt 8 message.consolidatedOpenPrice
    ++ (encodeUInt 8 message.listingCenterOpenPrice
    ++ (encodeUInt 8 message.consolidatedClosePrice
    ++ (encodeUInt 8 message.listingCenterClosePrice
    ++ (encodeUInt 8 message.consolidatedVolume))))))))

def decode (bytes : List UInt8) : Option (EndOfDayTradeSummaryMessage × List UInt8) := do
  let (timeStamp, bytes) ← decodeUInt 8 bytes
  let (stockSymbol, bytes) ← Alpha.decode 10 bytes
  let (consolidatedHighPrice, bytes) ← decodeUInt 8 bytes
  let (consolidatedLowPrice, bytes) ← decodeUInt 8 bytes
  let (consolidatedOpenPrice, bytes) ← decodeUInt 8 bytes
  let (listingCenterOpenPrice, bytes) ← decodeUInt 8 bytes
  let (consolidatedClosePrice, bytes) ← decodeUInt 8 bytes
  let (listingCenterClosePrice, bytes) ← decodeUInt 8 bytes
  let (consolidatedVolume, bytes) ← decodeUInt 8 bytes
  pure ({ timeStamp, stockSymbol, consolidatedHighPrice, consolidatedLowPrice, consolidatedOpenPrice, listingCenterOpenPrice, consolidatedClosePrice, listingCenterClosePrice, consolidatedVolume }, bytes)

@[simp] theorem encode_length (message : EndOfDayTradeSummaryMessage) : (encode message).length = 74 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : EndOfDayTradeSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EndOfDayTradeSummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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

end EndOfDayTradeSummaryMessage

/-- Adjusted Closing Price Message: 27 bytes -/
structure AdjustedClosingPriceMessage where
  timeStamp : BitVec 64
  issueSymbol : Alpha 10
  securityClass : SecurityClass
  adjustedClosingPrice : BitVec 64
  deriving DecidableEq, Repr

namespace AdjustedClosingPriceMessage

def encode (message : AdjustedClosingPriceMessage) : List UInt8 :=
  encodeUInt 8 message.timeStamp
    ++ (Alpha.encode message.issueSymbol
    ++ (SecurityClass.encode message.securityClass
    ++ (encodeUInt 8 message.adjustedClosingPrice)))

def decode (bytes : List UInt8) : Option (AdjustedClosingPriceMessage × List UInt8) := do
  let (timeStamp, bytes) ← decodeUInt 8 bytes
  let (issueSymbol, bytes) ← Alpha.decode 10 bytes
  let (securityClass, bytes) ← SecurityClass.decode bytes
  let (adjustedClosingPrice, bytes) ← decodeUInt 8 bytes
  pure ({ timeStamp, issueSymbol, securityClass, adjustedClosingPrice }, bytes)

@[simp] theorem encode_length (message : AdjustedClosingPriceMessage) : (encode message).length = 27 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, SecurityClass.encode_length]

theorem encode_length_pos (message : AdjustedClosingPriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AdjustedClosingPriceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityClass.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AdjustedClosingPriceMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | quotationMessage (message : QuotationMessage) -- "C" 0x43
  | tradeReportMessage (message : TradeReportMessage) -- "T" 0x54
  | tradeBreakMessage (message : TradeBreakMessage) -- "X" 0x58
  | tradeCorrectionMessage (message : TradeCorrectionMessage) -- "Z" 0x5A
  | systemEventMessage (message : SystemEventMessage) -- "S" 0x53
  | stockDirectoryMessage (message : StockDirectoryMessage) -- "R" 0x52
  | stockStatusMessage (message : StockStatusMessage) -- "H" 0x48
  | endOfDayTradeSummaryMessage (message : EndOfDayTradeSummaryMessage) -- "D" 0x44
  | adjustedClosingPriceMessage (message : AdjustedClosingPriceMessage) -- "G" 0x47
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .quotationMessage _ => 67
  | .tradeReportMessage _ => 84
  | .tradeBreakMessage _ => 88
  | .tradeCorrectionMessage _ => 90
  | .systemEventMessage _ => 83
  | .stockDirectoryMessage _ => 82
  | .stockStatusMessage _ => 72
  | .endOfDayTradeSummaryMessage _ => 68
  | .adjustedClosingPriceMessage _ => 71

def encode : Payload → List UInt8
  | .quotationMessage message => QuotationMessage.encode message
  | .tradeReportMessage message => TradeReportMessage.encode message
  | .tradeBreakMessage message => TradeBreakMessage.encode message
  | .tradeCorrectionMessage message => TradeCorrectionMessage.encode message
  | .systemEventMessage message => SystemEventMessage.encode message
  | .stockDirectoryMessage message => StockDirectoryMessage.encode message
  | .stockStatusMessage message => StockStatusMessage.encode message
  | .endOfDayTradeSummaryMessage message => EndOfDayTradeSummaryMessage.encode message
  | .adjustedClosingPriceMessage message => AdjustedClosingPriceMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 74 := by
  cases message with
  | quotationMessage inner =>
    simp only [encode, QuotationMessage.encode_length]
    omega
  | tradeReportMessage inner =>
    simp only [encode, TradeReportMessage.encode_length]
    omega
  | tradeBreakMessage inner =>
    simp only [encode, TradeBreakMessage.encode_length]
    omega
  | tradeCorrectionMessage inner =>
    simp only [encode, TradeCorrectionMessage.encode_length]
    omega
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega
  | stockDirectoryMessage inner =>
    simp only [encode, StockDirectoryMessage.encode_length]
    omega
  | stockStatusMessage inner =>
    simp only [encode, StockStatusMessage.encode_length]
    omega
  | endOfDayTradeSummaryMessage inner =>
    simp only [encode, EndOfDayTradeSummaryMessage.encode_length]
    omega
  | adjustedClosingPriceMessage inner =>
    simp only [encode, AdjustedClosingPriceMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 67 then (QuotationMessage.decode bytes).map fun (message, rest) => (.quotationMessage message, rest)
  else if tag = 84 then (TradeReportMessage.decode bytes).map fun (message, rest) => (.tradeReportMessage message, rest)
  else if tag = 88 then (TradeBreakMessage.decode bytes).map fun (message, rest) => (.tradeBreakMessage message, rest)
  else if tag = 90 then (TradeCorrectionMessage.decode bytes).map fun (message, rest) => (.tradeCorrectionMessage message, rest)
  else if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 82 then (StockDirectoryMessage.decode bytes).map fun (message, rest) => (.stockDirectoryMessage message, rest)
  else if tag = 72 then (StockStatusMessage.decode bytes).map fun (message, rest) => (.stockStatusMessage message, rest)
  else if tag = 68 then (EndOfDayTradeSummaryMessage.decode bytes).map fun (message, rest) => (.endOfDayTradeSummaryMessage message, rest)
  else if tag = 71 then (AdjustedClosingPriceMessage.decode bytes).map fun (message, rest) => (.adjustedClosingPriceMessage message, rest)
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
  encodeUInt 1 (Payload.tag message.payload)
    ++ (Payload.encode message.payload)

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (messageType, bytes) ← decodeUInt 1 bytes
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
  | quotationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, QuotationMessage.encode_length]
    omega
  | tradeReportMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeReportMessage.encode_length]
    omega
  | tradeBreakMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeBreakMessage.encode_length]
    omega
  | tradeCorrectionMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeCorrectionMessage.encode_length]
    omega
  | systemEventMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SystemEventMessage.encode_length]
    omega
  | stockDirectoryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, StockDirectoryMessage.encode_length]
    omega
  | stockStatusMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, StockStatusMessage.encode_length]
    omega
  | endOfDayTradeSummaryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, EndOfDayTradeSummaryMessage.encode_length]
    omega
  | adjustedClosingPriceMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, AdjustedClosingPriceMessage.encode_length]
    omega

/-- Size rule: Message Length counts the bytes after it, so it is written from the body and checked on decode -/
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

/-- Packet -/
structure Packet where
  session : Alpha 10
  sequenceNumber : BitVec 64
  message : Bounded 2 Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  Alpha.encode message.session
    ++ (encodeUInt 8 message.sequenceNumber
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) message.message.val.length)
    ++ (encodeMany Message.encode message.message.val)))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (session, bytes) ← Alpha.decode 10 bytes
  let (sequenceNumber, bytes) ← decodeUInt 8 bytes
  let (messageCount, bytes) ← decodeUInt 2 bytes
  let (message_, bytes) ← decodeMany Message.decode messageCount.toNat bytes
  if fits_message : message_.length < 256 ^ 2 then
    pure ({ session, sequenceNumber, message := ⟨message_, fits_message⟩ }, bytes)
  else none

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt]
  rfl

end Packet

end Omi.NasdaqNasdaqcanadaBasicItchV16
