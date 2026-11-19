import Wire

/-!
# SIX Swiss Exchange SIX Swiss Exchange ITCH Market Data Interface Total View v1.24.0

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

namespace Omi.SixSixswissexchangeTotalviewItchV1240

/-- Event Code: one byte code -/
def EventCode.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x45, 0x49, 0x4D, 0x4F, 0x51, 0x53, 0x55, 0x56, 0x54, 0x4C, 0x20]

inductive EventCode where
  | break_ -- Break
  | resumptionAfterBreak -- Resumption After Break
  | endOfMessages -- End Of Messages
  | endOfSystemHours -- End Of System Hours
  | startOfAccepting -- Start Of Accepting
  | endOfMarketHours -- End Of Market Hours
  | startOfMessages -- Start Of Messages
  | startOfMarketHours -- Start Of Market Hours
  | startOfSystemHours -- Start Of System Hours
  | auctionCloses -- Auction Closes
  | auctionStarts -- Auction Starts
  | startOfTradingAtLast -- Start Of Trading At Last
  | endOfTradingAtLast -- End Of Trading At Last
  | synchronizedWithGroup -- Synchronized With Group
  | unlisted (byte : { byte : UInt8 // byte ∉ EventCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventCode

def toByte : EventCode → UInt8
  | .break_ => 0x41
  | .resumptionAfterBreak => 0x42
  | .endOfMessages => 0x43
  | .endOfSystemHours => 0x45
  | .startOfAccepting => 0x49
  | .endOfMarketHours => 0x4D
  | .startOfMessages => 0x4F
  | .startOfMarketHours => 0x51
  | .startOfSystemHours => 0x53
  | .auctionCloses => 0x55
  | .auctionStarts => 0x56
  | .startOfTradingAtLast => 0x54
  | .endOfTradingAtLast => 0x4C
  | .synchronizedWithGroup => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventCode :=
  if byte = 0x41 then .break_
  else if byte = 0x42 then .resumptionAfterBreak
  else if byte = 0x43 then .endOfMessages
  else if byte = 0x45 then .endOfSystemHours
  else if byte = 0x49 then .startOfAccepting
  else if byte = 0x4D then .endOfMarketHours
  else if byte = 0x4F then .startOfMessages
  else if byte = 0x51 then .startOfMarketHours
  else if byte = 0x53 then .startOfSystemHours
  else if byte = 0x55 then .auctionCloses
  else if byte = 0x56 then .auctionStarts
  else if byte = 0x54 then .startOfTradingAtLast
  else if byte = 0x4C then .endOfTradingAtLast
  else .synchronizedWithGroup

def ofByte (byte : UInt8) : EventCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventCode) : ofByte value.toByte = value := by
  cases value with
  | break_ => decide
  | resumptionAfterBreak => decide
  | endOfMessages => decide
  | endOfSystemHours => decide
  | startOfAccepting => decide
  | endOfMarketHours => decide
  | startOfMessages => decide
  | startOfMarketHours => decide
  | startOfSystemHours => decide
  | auctionCloses => decide
  | auctionStarts => decide
  | startOfTradingAtLast => decide
  | endOfTradingAtLast => decide
  | synchronizedWithGroup => decide
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

/-- Price Type: one byte code -/
def PriceType.codes : List UInt8 :=
  [0x55, 0x50]

inductive PriceType where
  | perUnit -- Per Unit
  | percentage -- Percentage
  | unlisted (byte : { byte : UInt8 // byte ∉ PriceType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PriceType

def toByte : PriceType → UInt8
  | .perUnit => 0x55
  | .percentage => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PriceType :=
  if byte = 0x55 then .perUnit
  else .percentage

def ofByte (byte : UInt8) : PriceType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PriceType) : ofByte value.toByte = value := by
  cases value with
  | perUnit => decide
  | percentage => decide
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

/-- Trading State: one byte code -/
def TradingState.codes : List UInt8 :=
  [0x54, 0x56, 0x4D, 0x45, 0x4F, 0x55, 0x51, 0x43, 0x4C, 0x50]

inductive TradingState where
  | trading -- Trading
  | suspended -- Suspended
  | swissAtMidOrderBookSuspended -- Swiss At Mid Order Book Suspended
  | swissEbboOrderBookSuspended -- Swiss Ebbo Order Book Suspended
  | swissEbboAndSwissAtMidOrderBooksSuspended -- Swiss Ebbo And Swiss At Mid Order Books Suspended
  | underlyingCondition -- Underlying Condition
  | quoteOnDemandOrderBookSuspended -- Quote On Demand Order Book Suspended
  | clobSuspendedAndQodOrderBookInTrading -- Clob Suspended And Qod Order Book In Trading
  | lpBidOnlyActive -- Lp Bid Only Active
  | lpBidOnlyActiveAndQodOrderBookSuspended -- Lp Bid Only Active And Qod Order Book Suspended
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingState

def toByte : TradingState → UInt8
  | .trading => 0x54
  | .suspended => 0x56
  | .swissAtMidOrderBookSuspended => 0x4D
  | .swissEbboOrderBookSuspended => 0x45
  | .swissEbboAndSwissAtMidOrderBooksSuspended => 0x4F
  | .underlyingCondition => 0x55
  | .quoteOnDemandOrderBookSuspended => 0x51
  | .clobSuspendedAndQodOrderBookInTrading => 0x43
  | .lpBidOnlyActive => 0x4C
  | .lpBidOnlyActiveAndQodOrderBookSuspended => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingState :=
  if byte = 0x54 then .trading
  else if byte = 0x56 then .suspended
  else if byte = 0x4D then .swissAtMidOrderBookSuspended
  else if byte = 0x45 then .swissEbboOrderBookSuspended
  else if byte = 0x4F then .swissEbboAndSwissAtMidOrderBooksSuspended
  else if byte = 0x55 then .underlyingCondition
  else if byte = 0x51 then .quoteOnDemandOrderBookSuspended
  else if byte = 0x43 then .clobSuspendedAndQodOrderBookInTrading
  else if byte = 0x4C then .lpBidOnlyActive
  else .lpBidOnlyActiveAndQodOrderBookSuspended

def ofByte (byte : UInt8) : TradingState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingState) : ofByte value.toByte = value := by
  cases value with
  | trading => decide
  | suspended => decide
  | swissAtMidOrderBookSuspended => decide
  | swissEbboOrderBookSuspended => decide
  | swissEbboAndSwissAtMidOrderBooksSuspended => decide
  | underlyingCondition => decide
  | quoteOnDemandOrderBookSuspended => decide
  | clobSuspendedAndQodOrderBookInTrading => decide
  | lpBidOnlyActive => decide
  | lpBidOnlyActiveAndQodOrderBookSuspended => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradingState) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradingState × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradingState) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TradingState) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TradingState) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradingState

/-- Book Condition: one byte code -/
def BookCondition.codes : List UInt8 :=
  [0x44, 0x48, 0x4A, 0x4C, 0x4E, 0x50, 0x31, 0x32, 0x33, 0x34, 0x35]

inductive BookCondition where
  | delayAuction -- Delay Auction
  | stopTrading -- Stop Trading
  | stopTradingWithNonOpening -- Stop Trading With Non Opening
  | delayAuctionWithNonOpening -- Delay Auction With Non Opening
  | normalTrading -- Normal Trading
  | nonOpening -- Non Opening
  | lpBidOnlyReasonUsWithholdingTax -- Lp Bid Only Reason Us Withholding Tax
  | lpBidOnlyReasonIssuerSoldOut -- Lp Bid Only Reason Issuer Sold Out
  | lpBidOnlyReasonIssuerBusinessPolicy -- Lp Bid Only Reason Issuer Business Policy
  | lpBidOnlyReasonSuccessorProduct -- Lp Bid Only Reason Successor Product
  | lpBidOnlyReasonProductWorthless -- Lp Bid Only Reason Product Worthless
  | unlisted (byte : { byte : UInt8 // byte ∉ BookCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BookCondition

def toByte : BookCondition → UInt8
  | .delayAuction => 0x44
  | .stopTrading => 0x48
  | .stopTradingWithNonOpening => 0x4A
  | .delayAuctionWithNonOpening => 0x4C
  | .normalTrading => 0x4E
  | .nonOpening => 0x50
  | .lpBidOnlyReasonUsWithholdingTax => 0x31
  | .lpBidOnlyReasonIssuerSoldOut => 0x32
  | .lpBidOnlyReasonIssuerBusinessPolicy => 0x33
  | .lpBidOnlyReasonSuccessorProduct => 0x34
  | .lpBidOnlyReasonProductWorthless => 0x35
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BookCondition :=
  if byte = 0x44 then .delayAuction
  else if byte = 0x48 then .stopTrading
  else if byte = 0x4A then .stopTradingWithNonOpening
  else if byte = 0x4C then .delayAuctionWithNonOpening
  else if byte = 0x4E then .normalTrading
  else if byte = 0x50 then .nonOpening
  else if byte = 0x31 then .lpBidOnlyReasonUsWithholdingTax
  else if byte = 0x32 then .lpBidOnlyReasonIssuerSoldOut
  else if byte = 0x33 then .lpBidOnlyReasonIssuerBusinessPolicy
  else if byte = 0x34 then .lpBidOnlyReasonSuccessorProduct
  else .lpBidOnlyReasonProductWorthless

def ofByte (byte : UInt8) : BookCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BookCondition) : ofByte value.toByte = value := by
  cases value with
  | delayAuction => decide
  | stopTrading => decide
  | stopTradingWithNonOpening => decide
  | delayAuctionWithNonOpening => decide
  | normalTrading => decide
  | nonOpening => decide
  | lpBidOnlyReasonUsWithholdingTax => decide
  | lpBidOnlyReasonIssuerSoldOut => decide
  | lpBidOnlyReasonIssuerBusinessPolicy => decide
  | lpBidOnlyReasonSuccessorProduct => decide
  | lpBidOnlyReasonProductWorthless => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BookCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BookCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BookCondition) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : BookCondition) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : BookCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BookCondition

/-- Order Verb: one byte code -/
def OrderVerb.codes : List UInt8 :=
  [0x42, 0x53, 0x20]

inductive OrderVerb where
  | buy -- Buy
  | sell -- Sell
  | referencePriceUpdate -- Reference Price Update
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderVerb.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderVerb

def toByte : OrderVerb → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .referencePriceUpdate => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderVerb :=
  if byte = 0x42 then .buy
  else if byte = 0x53 then .sell
  else .referencePriceUpdate

def ofByte (byte : UInt8) : OrderVerb :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderVerb) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | referencePriceUpdate => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderVerb) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderVerb × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderVerb) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OrderVerb) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OrderVerb) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderVerb

/-- Printable: one byte code -/
def Printable.codes : List UInt8 :=
  [0x4E, 0x59]

inductive Printable where
  | nonPrintable -- Non Printable
  | printable -- Printable
  | unlisted (byte : { byte : UInt8 // byte ∉ Printable.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Printable

def toByte : Printable → UInt8
  | .nonPrintable => 0x4E
  | .printable => 0x59
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Printable :=
  if byte = 0x4E then .nonPrintable
  else .printable

def ofByte (byte : UInt8) : Printable :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Printable) : ofByte value.toByte = value := by
  cases value with
  | nonPrintable => decide
  | printable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Printable) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Printable × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Printable) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Printable) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Printable) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Printable

/-- Aggressor Side: one byte code -/
def AggressorSide.codes : List UInt8 :=
  [0x42, 0x53]

inductive AggressorSide where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ AggressorSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AggressorSide

def toByte : AggressorSide → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AggressorSide :=
  if byte = 0x42 then .buy
  else .sell

def ofByte (byte : UInt8) : AggressorSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AggressorSide) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AggressorSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AggressorSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AggressorSide) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : AggressorSide) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : AggressorSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AggressorSide

/-- Far Side: one byte code -/
def FarSide.codes : List UInt8 :=
  [0x42, 0x53, 0x20]

inductive FarSide where
  | buy -- Buy
  | sell -- Sell
  | noFarQuantityRemaining -- No Far Quantity Remaining
  | unlisted (byte : { byte : UInt8 // byte ∉ FarSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace FarSide

def toByte : FarSide → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .noFarQuantityRemaining => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : FarSide :=
  if byte = 0x42 then .buy
  else if byte = 0x53 then .sell
  else .noFarQuantityRemaining

def ofByte (byte : UInt8) : FarSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : FarSide) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | noFarQuantityRemaining => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : FarSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (FarSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : FarSide) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : FarSide) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : FarSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end FarSide

/-- Book Type: one byte code -/
def BookType.codes : List UInt8 :=
  [0x45, 0x4C, 0x4D, 0x4E, 0x51]

inductive BookType where
  | swissEbbo -- Swiss Ebbo
  | quoteDrivenMarket -- Quote Driven Market
  | swissAtMid -- Swiss At Mid
  | centralLimitOrderBookNonDisplayed -- Central Limit Order Book Non Displayed
  | quoteOnDemand -- Quote On Demand
  | unlisted (byte : { byte : UInt8 // byte ∉ BookType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BookType

def toByte : BookType → UInt8
  | .swissEbbo => 0x45
  | .quoteDrivenMarket => 0x4C
  | .swissAtMid => 0x4D
  | .centralLimitOrderBookNonDisplayed => 0x4E
  | .quoteOnDemand => 0x51
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BookType :=
  if byte = 0x45 then .swissEbbo
  else if byte = 0x4C then .quoteDrivenMarket
  else if byte = 0x4D then .swissAtMid
  else if byte = 0x4E then .centralLimitOrderBookNonDisplayed
  else .quoteOnDemand

def ofByte (byte : UInt8) : BookType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BookType) : ofByte value.toByte = value := by
  cases value with
  | swissEbbo => decide
  | quoteDrivenMarket => decide
  | swissAtMid => decide
  | centralLimitOrderBookNonDisplayed => decide
  | quoteOnDemand => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BookType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BookType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BookType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : BookType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : BookType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BookType

/-- Trading Session Id: one byte code -/
def TradingSessionId.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33, 0x34]

inductive TradingSessionId where
  | openingAuction -- Opening Auction
  | intradayAuction -- Intraday Auction
  | continuousTrading -- Continuous Trading
  | closingAuction -- Closing Auction
  | atMarketClose -- At Market Close
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingSessionId.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingSessionId

def toByte : TradingSessionId → UInt8
  | .openingAuction => 0x30
  | .intradayAuction => 0x31
  | .continuousTrading => 0x32
  | .closingAuction => 0x33
  | .atMarketClose => 0x34
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingSessionId :=
  if byte = 0x30 then .openingAuction
  else if byte = 0x31 then .intradayAuction
  else if byte = 0x32 then .continuousTrading
  else if byte = 0x33 then .closingAuction
  else .atMarketClose

def ofByte (byte : UInt8) : TradingSessionId :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingSessionId) : ofByte value.toByte = value := by
  cases value with
  | openingAuction => decide
  | intradayAuction => decide
  | continuousTrading => decide
  | closingAuction => decide
  | atMarketClose => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradingSessionId) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradingSessionId × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradingSessionId) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TradingSessionId) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TradingSessionId) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradingSessionId

/-- Reason: one byte code -/
def Reason.codes : List UInt8 :=
  [0x43, 0x53]

inductive Reason where
  | consent -- Consent
  | supervisory -- Supervisory
  | unlisted (byte : { byte : UInt8 // byte ∉ Reason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Reason

def toByte : Reason → UInt8
  | .consent => 0x43
  | .supervisory => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Reason :=
  if byte = 0x43 then .consent
  else .supervisory

def ofByte (byte : UInt8) : Reason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Reason) : ofByte value.toByte = value := by
  cases value with
  | consent => decide
  | supervisory => decide
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

/-- Cross Type: one byte code -/
def CrossType.codes : List UInt8 :=
  [0x43, 0x49, 0x4F]

inductive CrossType where
  | closingAuction -- Closing Auction
  | intradayAuction -- Intraday Auction
  | preOpeningAuction -- Pre Opening Auction
  | unlisted (byte : { byte : UInt8 // byte ∉ CrossType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CrossType

def toByte : CrossType → UInt8
  | .closingAuction => 0x43
  | .intradayAuction => 0x49
  | .preOpeningAuction => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CrossType :=
  if byte = 0x43 then .closingAuction
  else if byte = 0x49 then .intradayAuction
  else .preOpeningAuction

def ofByte (byte : UInt8) : CrossType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CrossType) : ofByte value.toByte = value := by
  cases value with
  | closingAuction => decide
  | intradayAuction => decide
  | preOpeningAuction => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CrossType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CrossType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CrossType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CrossType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CrossType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CrossType

/-- Time Stamp Seconds Message: 4 bytes -/
structure TimeStampSecondsMessage where
  second : BitVec 32
  deriving DecidableEq, Repr

namespace TimeStampSecondsMessage

def encode (message : TimeStampSecondsMessage) : List UInt8 :=
  encodeUInt 4 message.second

def decode (bytes : List UInt8) : Option (TimeStampSecondsMessage × List UInt8) := do
  let (second, bytes) ← decodeUInt 4 bytes
  pure ({ second }, bytes)

@[simp] theorem encode_length (message : TimeStampSecondsMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : TimeStampSecondsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TimeStampSecondsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TimeStampSecondsMessage

/-- System Event Message: 17 bytes -/
structure SystemEventMessage where
  timestamp : BitVec 32
  group : Alpha 8
  eventCode : EventCode
  orderbook : BitVec 32
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  encodeUInt 4 message.timestamp
    ++ (Alpha.encode message.group
    ++ (EventCode.encode message.eventCode
    ++ (encodeUInt 4 message.orderbook)))

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 4 bytes
  let (group, bytes) ← Alpha.decode 8 bytes
  let (eventCode, bytes) ← EventCode.decode bytes
  let (orderbook, bytes) ← decodeUInt 4 bytes
  pure ({ timestamp, group, eventCode, orderbook }, bytes)

@[simp] theorem encode_length (message : SystemEventMessage) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, EventCode.encode_length]

theorem encode_length_pos (message : SystemEventMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemEventMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, EventCode.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SystemEventMessage

/-- Quantity Tick Size Message: 16 bytes -/
structure QuantityTickSizeMessage where
  timestamp : BitVec 32
  quantityTickTableId : BitVec 32
  quantityTickSize : BitVec 32
  quantityStart : BitVec 32
  deriving DecidableEq, Repr

namespace QuantityTickSizeMessage

def encode (message : QuantityTickSizeMessage) : List UInt8 :=
  encodeUInt 4 message.timestamp
    ++ (encodeUInt 4 message.quantityTickTableId
    ++ (encodeUInt 4 message.quantityTickSize
    ++ (encodeUInt 4 message.quantityStart)))

def decode (bytes : List UInt8) : Option (QuantityTickSizeMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 4 bytes
  let (quantityTickTableId, bytes) ← decodeUInt 4 bytes
  let (quantityTickSize, bytes) ← decodeUInt 4 bytes
  let (quantityStart, bytes) ← decodeUInt 4 bytes
  pure ({ timestamp, quantityTickTableId, quantityTickSize, quantityStart }, bytes)

@[simp] theorem encode_length (message : QuantityTickSizeMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : QuantityTickSizeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuantityTickSizeMessage) (rest : List UInt8) :
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

end QuantityTickSizeMessage

/-- Price Tick Size Message: 16 bytes -/
structure PriceTickSizeMessage where
  timestamp : BitVec 32
  priceTickTableId : BitVec 32
  priceTickSize : BitVec 32
  priceStart : BitVec 32
  deriving DecidableEq, Repr

namespace PriceTickSizeMessage

def encode (message : PriceTickSizeMessage) : List UInt8 :=
  encodeUInt 4 message.timestamp
    ++ (encodeUInt 4 message.priceTickTableId
    ++ (encodeUInt 4 message.priceTickSize
    ++ (encodeUInt 4 message.priceStart)))

def decode (bytes : List UInt8) : Option (PriceTickSizeMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 4 bytes
  let (priceTickTableId, bytes) ← decodeUInt 4 bytes
  let (priceTickSize, bytes) ← decodeUInt 4 bytes
  let (priceStart, bytes) ← decodeUInt 4 bytes
  pure ({ timestamp, priceTickTableId, priceTickSize, priceStart }, bytes)

@[simp] theorem encode_length (message : PriceTickSizeMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : PriceTickSizeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PriceTickSizeMessage) (rest : List UInt8) :
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

end PriceTickSizeMessage

/-- Orderbook Directory Message: 68 bytes -/
structure OrderbookDirectoryMessage where
  timestamp : BitVec 32
  orderbook : BitVec 32
  priceType : PriceType
  isin : Alpha 12
  currency : Alpha 3
  group : Alpha 8
  minimumQuantity : BitVec 32
  quantityTickTableId : BitVec 32
  priceTickTableId : BitVec 32
  priceDecimals : BitVec 32
  delistingDate : BitVec 32
  delistingTime : BitVec 32
  qodPriceDecimals : BitVec 32
  securityExchange : Alpha 4
  referenceExchange : Alpha 4
  deriving DecidableEq, Repr

namespace OrderbookDirectoryMessage

def encode (message : OrderbookDirectoryMessage) : List UInt8 :=
  encodeUInt 4 message.timestamp
    ++ (encodeUInt 4 message.orderbook
    ++ (PriceType.encode message.priceType
    ++ (Alpha.encode message.isin
    ++ (Alpha.encode message.currency
    ++ (Alpha.encode message.group
    ++ (encodeUInt 4 message.minimumQuantity
    ++ (encodeUInt 4 message.quantityTickTableId
    ++ (encodeUInt 4 message.priceTickTableId
    ++ (encodeUInt 4 message.priceDecimals
    ++ (encodeUInt 4 message.delistingDate
    ++ (encodeUInt 4 message.delistingTime
    ++ (encodeUInt 4 message.qodPriceDecimals
    ++ (Alpha.encode message.securityExchange
    ++ (Alpha.encode message.referenceExchange))))))))))))))

def decode (bytes : List UInt8) : Option (OrderbookDirectoryMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 4 bytes
  let (orderbook, bytes) ← decodeUInt 4 bytes
  let (priceType, bytes) ← PriceType.decode bytes
  let (isin, bytes) ← Alpha.decode 12 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (group, bytes) ← Alpha.decode 8 bytes
  let (minimumQuantity, bytes) ← decodeUInt 4 bytes
  let (quantityTickTableId, bytes) ← decodeUInt 4 bytes
  let (priceTickTableId, bytes) ← decodeUInt 4 bytes
  let (priceDecimals, bytes) ← decodeUInt 4 bytes
  let (delistingDate, bytes) ← decodeUInt 4 bytes
  let (delistingTime, bytes) ← decodeUInt 4 bytes
  let (qodPriceDecimals, bytes) ← decodeUInt 4 bytes
  let (securityExchange, bytes) ← Alpha.decode 4 bytes
  let (referenceExchange, bytes) ← Alpha.decode 4 bytes
  pure ({ timestamp, orderbook, priceType, isin, currency, group, minimumQuantity, quantityTickTableId, priceTickTableId, priceDecimals, delistingDate, delistingTime, qodPriceDecimals, securityExchange, referenceExchange }, bytes)

@[simp] theorem encode_length (message : OrderbookDirectoryMessage) : (encode message).length = 68 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, PriceType.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderbookDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderbookDirectoryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, PriceType.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderbookDirectoryMessage

/-- Orderbook Trading Action Message: 10 bytes -/
structure OrderbookTradingActionMessage where
  timestamp : BitVec 32
  orderbook : BitVec 32
  tradingState : TradingState
  bookCondition : BookCondition
  deriving DecidableEq, Repr

namespace OrderbookTradingActionMessage

def encode (message : OrderbookTradingActionMessage) : List UInt8 :=
  encodeUInt 4 message.timestamp
    ++ (encodeUInt 4 message.orderbook
    ++ (TradingState.encode message.tradingState
    ++ (BookCondition.encode message.bookCondition)))

def decode (bytes : List UInt8) : Option (OrderbookTradingActionMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 4 bytes
  let (orderbook, bytes) ← decodeUInt 4 bytes
  let (tradingState, bytes) ← TradingState.decode bytes
  let (bookCondition, bytes) ← BookCondition.decode bytes
  pure ({ timestamp, orderbook, tradingState, bookCondition }, bytes)

@[simp] theorem encode_length (message : OrderbookTradingActionMessage) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, TradingState.encode_length, BookCondition.encode_length]

theorem encode_length_pos (message : OrderbookTradingActionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderbookTradingActionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TradingState.decode_encode, some_bind]
  dsimp only
  rw [BookCondition.decode_encode, some_bind]
  rfl

end OrderbookTradingActionMessage

/-- Add Order Message: 25 bytes -/
structure AddOrderMessage where
  timestamp : BitVec 32
  orderNumber : BitVec 64
  orderVerb : OrderVerb
  orderQuantity : BitVec 32
  orderbook : BitVec 32
  orderPrice : BitVec 32
  deriving DecidableEq, Repr

namespace AddOrderMessage

def encode (message : AddOrderMessage) : List UInt8 :=
  encodeUInt 4 message.timestamp
    ++ (encodeUInt 8 message.orderNumber
    ++ (OrderVerb.encode message.orderVerb
    ++ (encodeUInt 4 message.orderQuantity
    ++ (encodeUInt 4 message.orderbook
    ++ (encodeUInt 4 message.orderPrice)))))

def decode (bytes : List UInt8) : Option (AddOrderMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 4 bytes
  let (orderNumber, bytes) ← decodeUInt 8 bytes
  let (orderVerb, bytes) ← OrderVerb.decode bytes
  let (orderQuantity, bytes) ← decodeUInt 4 bytes
  let (orderbook, bytes) ← decodeUInt 4 bytes
  let (orderPrice, bytes) ← decodeUInt 4 bytes
  pure ({ timestamp, orderNumber, orderVerb, orderQuantity, orderbook, orderPrice }, bytes)

@[simp] theorem encode_length (message : AddOrderMessage) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, OrderVerb.encode_length]

theorem encode_length_pos (message : AddOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OrderVerb.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AddOrderMessage

/-- Order Executed Message: 24 bytes -/
structure OrderExecutedMessage where
  timestamp : BitVec 32
  orderNumber : BitVec 64
  executedQuantity : BitVec 32
  matchNumber : BitVec 64
  deriving DecidableEq, Repr

namespace OrderExecutedMessage

def encode (message : OrderExecutedMessage) : List UInt8 :=
  encodeUInt 4 message.timestamp
    ++ (encodeUInt 8 message.orderNumber
    ++ (encodeUInt 4 message.executedQuantity
    ++ (encodeUInt 8 message.matchNumber)))

def decode (bytes : List UInt8) : Option (OrderExecutedMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 4 bytes
  let (orderNumber, bytes) ← decodeUInt 8 bytes
  let (executedQuantity, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← decodeUInt 8 bytes
  pure ({ timestamp, orderNumber, executedQuantity, matchNumber }, bytes)

@[simp] theorem encode_length (message : OrderExecutedMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : OrderExecutedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderExecutedMessage) (rest : List UInt8) :
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

end OrderExecutedMessage

/-- Order Executed With Price Message: 29 bytes -/
structure OrderExecutedWithPriceMessage where
  timestamp : BitVec 32
  orderNumber : BitVec 64
  executedQuantity : BitVec 32
  matchNumber : BitVec 64
  printable : Printable
  executionPrice : BitVec 32
  deriving DecidableEq, Repr

namespace OrderExecutedWithPriceMessage

def encode (message : OrderExecutedWithPriceMessage) : List UInt8 :=
  encodeUInt 4 message.timestamp
    ++ (encodeUInt 8 message.orderNumber
    ++ (encodeUInt 4 message.executedQuantity
    ++ (encodeUInt 8 message.matchNumber
    ++ (Printable.encode message.printable
    ++ (encodeUInt 4 message.executionPrice)))))

def decode (bytes : List UInt8) : Option (OrderExecutedWithPriceMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 4 bytes
  let (orderNumber, bytes) ← decodeUInt 8 bytes
  let (executedQuantity, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← decodeUInt 8 bytes
  let (printable_, bytes) ← Printable.decode bytes
  let (executionPrice, bytes) ← decodeUInt 4 bytes
  pure ({ timestamp, orderNumber, executedQuantity, matchNumber, printable := printable_, executionPrice }, bytes)

@[simp] theorem encode_length (message : OrderExecutedWithPriceMessage) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Printable.encode_length]

theorem encode_length_pos (message : OrderExecutedWithPriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderExecutedWithPriceMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Printable.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderExecutedWithPriceMessage

/-- Execution Summary Message: 40 bytes -/
structure ExecutionSummaryMessage where
  timestamp : BitVec 32
  orderbook : BitVec 32
  aggressorSide : AggressorSide
  totalMpobQuantity : BitVec 32
  totalEbboBookQuantity : BitVec 32
  totalClobqdmQuantity : BitVec 32
  restingHiddenQuantity : BitVec 32
  restingCancelledQuantity : BitVec 32
  farSide : FarSide
  farPrice : BitVec 32
  farQuantityRemaining : BitVec 32
  numberOfExecutions : BitVec 16
  deriving DecidableEq, Repr

namespace ExecutionSummaryMessage

def encode (message : ExecutionSummaryMessage) : List UInt8 :=
  encodeUInt 4 message.timestamp
    ++ (encodeUInt 4 message.orderbook
    ++ (AggressorSide.encode message.aggressorSide
    ++ (encodeUInt 4 message.totalMpobQuantity
    ++ (encodeUInt 4 message.totalEbboBookQuantity
    ++ (encodeUInt 4 message.totalClobqdmQuantity
    ++ (encodeUInt 4 message.restingHiddenQuantity
    ++ (encodeUInt 4 message.restingCancelledQuantity
    ++ (FarSide.encode message.farSide
    ++ (encodeUInt 4 message.farPrice
    ++ (encodeUInt 4 message.farQuantityRemaining
    ++ (encodeUInt 2 message.numberOfExecutions)))))))))))

def decode (bytes : List UInt8) : Option (ExecutionSummaryMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 4 bytes
  let (orderbook, bytes) ← decodeUInt 4 bytes
  let (aggressorSide, bytes) ← AggressorSide.decode bytes
  let (totalMpobQuantity, bytes) ← decodeUInt 4 bytes
  let (totalEbboBookQuantity, bytes) ← decodeUInt 4 bytes
  let (totalClobqdmQuantity, bytes) ← decodeUInt 4 bytes
  let (restingHiddenQuantity, bytes) ← decodeUInt 4 bytes
  let (restingCancelledQuantity, bytes) ← decodeUInt 4 bytes
  let (farSide, bytes) ← FarSide.decode bytes
  let (farPrice, bytes) ← decodeUInt 4 bytes
  let (farQuantityRemaining, bytes) ← decodeUInt 4 bytes
  let (numberOfExecutions, bytes) ← decodeUInt 2 bytes
  pure ({ timestamp, orderbook, aggressorSide, totalMpobQuantity, totalEbboBookQuantity, totalClobqdmQuantity, restingHiddenQuantity, restingCancelledQuantity, farSide, farPrice, farQuantityRemaining, numberOfExecutions }, bytes)

@[simp] theorem encode_length (message : ExecutionSummaryMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, AggressorSide.encode_length, FarSide.encode_length]

theorem encode_length_pos (message : ExecutionSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExecutionSummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, AggressorSide.decode_encode, some_bind]
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
  rw [List.append_assoc, FarSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ExecutionSummaryMessage

/-- Trade Message: 34 bytes -/
structure TradeMessage where
  timestamp : BitVec 32
  executionTime : BitVec 64
  orderbook : BitVec 32
  executedQuantity : BitVec 32
  executionPrice : BitVec 32
  matchNumber : BitVec 64
  bookType : BookType
  tradingSessionId : TradingSessionId
  deriving DecidableEq, Repr

namespace TradeMessage

def encode (message : TradeMessage) : List UInt8 :=
  encodeUInt 4 message.timestamp
    ++ (encodeUInt 8 message.executionTime
    ++ (encodeUInt 4 message.orderbook
    ++ (encodeUInt 4 message.executedQuantity
    ++ (encodeUInt 4 message.executionPrice
    ++ (encodeUInt 8 message.matchNumber
    ++ (BookType.encode message.bookType
    ++ (TradingSessionId.encode message.tradingSessionId)))))))

def decode (bytes : List UInt8) : Option (TradeMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 4 bytes
  let (executionTime, bytes) ← decodeUInt 8 bytes
  let (orderbook, bytes) ← decodeUInt 4 bytes
  let (executedQuantity, bytes) ← decodeUInt 4 bytes
  let (executionPrice, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← decodeUInt 8 bytes
  let (bookType, bytes) ← BookType.decode bytes
  let (tradingSessionId, bytes) ← TradingSessionId.decode bytes
  pure ({ timestamp, executionTime, orderbook, executedQuantity, executionPrice, matchNumber, bookType, tradingSessionId }, bytes)

@[simp] theorem encode_length (message : TradeMessage) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, BookType.encode_length, TradingSessionId.encode_length]

theorem encode_length_pos (message : TradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, BookType.decode_encode, some_bind]
  dsimp only
  rw [TradingSessionId.decode_encode, some_bind]
  rfl

end TradeMessage

/-- Broken Trade Message: 13 bytes -/
structure BrokenTradeMessage where
  timestamp : BitVec 32
  matchNumber : BitVec 64
  reason : Reason
  deriving DecidableEq, Repr

namespace BrokenTradeMessage

def encode (message : BrokenTradeMessage) : List UInt8 :=
  encodeUInt 4 message.timestamp
    ++ (encodeUInt 8 message.matchNumber
    ++ (Reason.encode message.reason))

def decode (bytes : List UInt8) : Option (BrokenTradeMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← decodeUInt 8 bytes
  let (reason, bytes) ← Reason.decode bytes
  pure ({ timestamp, matchNumber, reason }, bytes)

@[simp] theorem encode_length (message : BrokenTradeMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Reason.encode_length]

theorem encode_length_pos (message : BrokenTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BrokenTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Reason.decode_encode, some_bind]
  rfl

end BrokenTradeMessage

/-- Order Delete Message: 12 bytes -/
structure OrderDeleteMessage where
  timestamp : BitVec 32
  orderNumber : BitVec 64
  deriving DecidableEq, Repr

namespace OrderDeleteMessage

def encode (message : OrderDeleteMessage) : List UInt8 :=
  encodeUInt 4 message.timestamp
    ++ (encodeUInt 8 message.orderNumber)

def decode (bytes : List UInt8) : Option (OrderDeleteMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 4 bytes
  let (orderNumber, bytes) ← decodeUInt 8 bytes
  pure ({ timestamp, orderNumber }, bytes)

@[simp] theorem encode_length (message : OrderDeleteMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : OrderDeleteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderDeleteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderDeleteMessage

/-- Order Replace Message: 28 bytes -/
structure OrderReplaceMessage where
  timestamp : BitVec 32
  originalOrderNumber : BitVec 64
  newOrderNumber : BitVec 64
  orderQuantity : BitVec 32
  orderPrice : BitVec 32
  deriving DecidableEq, Repr

namespace OrderReplaceMessage

def encode (message : OrderReplaceMessage) : List UInt8 :=
  encodeUInt 4 message.timestamp
    ++ (encodeUInt 8 message.originalOrderNumber
    ++ (encodeUInt 8 message.newOrderNumber
    ++ (encodeUInt 4 message.orderQuantity
    ++ (encodeUInt 4 message.orderPrice))))

def decode (bytes : List UInt8) : Option (OrderReplaceMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 4 bytes
  let (originalOrderNumber, bytes) ← decodeUInt 8 bytes
  let (newOrderNumber, bytes) ← decodeUInt 8 bytes
  let (orderQuantity, bytes) ← decodeUInt 4 bytes
  let (orderPrice, bytes) ← decodeUInt 4 bytes
  pure ({ timestamp, originalOrderNumber, newOrderNumber, orderQuantity, orderPrice }, bytes)

@[simp] theorem encode_length (message : OrderReplaceMessage) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : OrderReplaceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderReplaceMessage) (rest : List UInt8) :
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderReplaceMessage

/-- Indicative Price Quantity Message: 29 bytes -/
structure IndicativePriceQuantityMessage where
  timestamp : BitVec 32
  theoreticalOpeningQuantity : BitVec 64
  orderbook : BitVec 32
  bestBid : BitVec 32
  bestOffer : BitVec 32
  theoreticalOpeningPrice : BitVec 32
  crossType : CrossType
  deriving DecidableEq, Repr

namespace IndicativePriceQuantityMessage

def encode (message : IndicativePriceQuantityMessage) : List UInt8 :=
  encodeUInt 4 message.timestamp
    ++ (encodeUInt 8 message.theoreticalOpeningQuantity
    ++ (encodeUInt 4 message.orderbook
    ++ (encodeUInt 4 message.bestBid
    ++ (encodeUInt 4 message.bestOffer
    ++ (encodeUInt 4 message.theoreticalOpeningPrice
    ++ (CrossType.encode message.crossType))))))

def decode (bytes : List UInt8) : Option (IndicativePriceQuantityMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 4 bytes
  let (theoreticalOpeningQuantity, bytes) ← decodeUInt 8 bytes
  let (orderbook, bytes) ← decodeUInt 4 bytes
  let (bestBid, bytes) ← decodeUInt 4 bytes
  let (bestOffer, bytes) ← decodeUInt 4 bytes
  let (theoreticalOpeningPrice, bytes) ← decodeUInt 4 bytes
  let (crossType, bytes) ← CrossType.decode bytes
  pure ({ timestamp, theoreticalOpeningQuantity, orderbook, bestBid, bestOffer, theoreticalOpeningPrice, crossType }, bytes)

@[simp] theorem encode_length (message : IndicativePriceQuantityMessage) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, CrossType.encode_length]

theorem encode_length_pos (message : IndicativePriceQuantityMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IndicativePriceQuantityMessage) (rest : List UInt8) :
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
  rw [CrossType.decode_encode, some_bind]
  rfl

end IndicativePriceQuantityMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | timeStampSecondsMessage (message : TimeStampSecondsMessage) -- "T" 0x54
  | systemEventMessage (message : SystemEventMessage) -- "S" 0x53
  | quantityTickSizeMessage (message : QuantityTickSizeMessage) -- "M" 0x4D
  | priceTickSizeMessage (message : PriceTickSizeMessage) -- "L" 0x4C
  | orderbookDirectoryMessage (message : OrderbookDirectoryMessage) -- "R" 0x52
  | orderbookTradingActionMessage (message : OrderbookTradingActionMessage) -- "H" 0x48
  | addOrderMessage (message : AddOrderMessage) -- "A" 0x41
  | orderExecutedMessage (message : OrderExecutedMessage) -- "E" 0x45
  | orderExecutedWithPriceMessage (message : OrderExecutedWithPriceMessage) -- "C" 0x43
  | executionSummaryMessage (message : ExecutionSummaryMessage) -- "Y" 0x59
  | tradeMessage (message : TradeMessage) -- "P" 0x50
  | brokenTradeMessage (message : BrokenTradeMessage) -- "B" 0x42
  | orderDeleteMessage (message : OrderDeleteMessage) -- "D" 0x44
  | orderReplaceMessage (message : OrderReplaceMessage) -- "U" 0x55
  | indicativePriceQuantityMessage (message : IndicativePriceQuantityMessage) -- "I" 0x49
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .timeStampSecondsMessage _ => 84
  | .systemEventMessage _ => 83
  | .quantityTickSizeMessage _ => 77
  | .priceTickSizeMessage _ => 76
  | .orderbookDirectoryMessage _ => 82
  | .orderbookTradingActionMessage _ => 72
  | .addOrderMessage _ => 65
  | .orderExecutedMessage _ => 69
  | .orderExecutedWithPriceMessage _ => 67
  | .executionSummaryMessage _ => 89
  | .tradeMessage _ => 80
  | .brokenTradeMessage _ => 66
  | .orderDeleteMessage _ => 68
  | .orderReplaceMessage _ => 85
  | .indicativePriceQuantityMessage _ => 73

def encode : Payload → List UInt8
  | .timeStampSecondsMessage message => TimeStampSecondsMessage.encode message
  | .systemEventMessage message => SystemEventMessage.encode message
  | .quantityTickSizeMessage message => QuantityTickSizeMessage.encode message
  | .priceTickSizeMessage message => PriceTickSizeMessage.encode message
  | .orderbookDirectoryMessage message => OrderbookDirectoryMessage.encode message
  | .orderbookTradingActionMessage message => OrderbookTradingActionMessage.encode message
  | .addOrderMessage message => AddOrderMessage.encode message
  | .orderExecutedMessage message => OrderExecutedMessage.encode message
  | .orderExecutedWithPriceMessage message => OrderExecutedWithPriceMessage.encode message
  | .executionSummaryMessage message => ExecutionSummaryMessage.encode message
  | .tradeMessage message => TradeMessage.encode message
  | .brokenTradeMessage message => BrokenTradeMessage.encode message
  | .orderDeleteMessage message => OrderDeleteMessage.encode message
  | .orderReplaceMessage message => OrderReplaceMessage.encode message
  | .indicativePriceQuantityMessage message => IndicativePriceQuantityMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 68 := by
  cases message with
  | timeStampSecondsMessage inner =>
    simp only [encode, TimeStampSecondsMessage.encode_length]
    omega
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega
  | quantityTickSizeMessage inner =>
    simp only [encode, QuantityTickSizeMessage.encode_length]
    omega
  | priceTickSizeMessage inner =>
    simp only [encode, PriceTickSizeMessage.encode_length]
    omega
  | orderbookDirectoryMessage inner =>
    simp only [encode, OrderbookDirectoryMessage.encode_length]
    omega
  | orderbookTradingActionMessage inner =>
    simp only [encode, OrderbookTradingActionMessage.encode_length]
    omega
  | addOrderMessage inner =>
    simp only [encode, AddOrderMessage.encode_length]
    omega
  | orderExecutedMessage inner =>
    simp only [encode, OrderExecutedMessage.encode_length]
    omega
  | orderExecutedWithPriceMessage inner =>
    simp only [encode, OrderExecutedWithPriceMessage.encode_length]
    omega
  | executionSummaryMessage inner =>
    simp only [encode, ExecutionSummaryMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [encode, TradeMessage.encode_length]
    omega
  | brokenTradeMessage inner =>
    simp only [encode, BrokenTradeMessage.encode_length]
    omega
  | orderDeleteMessage inner =>
    simp only [encode, OrderDeleteMessage.encode_length]
    omega
  | orderReplaceMessage inner =>
    simp only [encode, OrderReplaceMessage.encode_length]
    omega
  | indicativePriceQuantityMessage inner =>
    simp only [encode, IndicativePriceQuantityMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 84 then (TimeStampSecondsMessage.decode bytes).map fun (message, rest) => (.timeStampSecondsMessage message, rest)
  else if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 77 then (QuantityTickSizeMessage.decode bytes).map fun (message, rest) => (.quantityTickSizeMessage message, rest)
  else if tag = 76 then (PriceTickSizeMessage.decode bytes).map fun (message, rest) => (.priceTickSizeMessage message, rest)
  else if tag = 82 then (OrderbookDirectoryMessage.decode bytes).map fun (message, rest) => (.orderbookDirectoryMessage message, rest)
  else if tag = 72 then (OrderbookTradingActionMessage.decode bytes).map fun (message, rest) => (.orderbookTradingActionMessage message, rest)
  else if tag = 65 then (AddOrderMessage.decode bytes).map fun (message, rest) => (.addOrderMessage message, rest)
  else if tag = 69 then (OrderExecutedMessage.decode bytes).map fun (message, rest) => (.orderExecutedMessage message, rest)
  else if tag = 67 then (OrderExecutedWithPriceMessage.decode bytes).map fun (message, rest) => (.orderExecutedWithPriceMessage message, rest)
  else if tag = 89 then (ExecutionSummaryMessage.decode bytes).map fun (message, rest) => (.executionSummaryMessage message, rest)
  else if tag = 80 then (TradeMessage.decode bytes).map fun (message, rest) => (.tradeMessage message, rest)
  else if tag = 66 then (BrokenTradeMessage.decode bytes).map fun (message, rest) => (.brokenTradeMessage message, rest)
  else if tag = 68 then (OrderDeleteMessage.decode bytes).map fun (message, rest) => (.orderDeleteMessage message, rest)
  else if tag = 85 then (OrderReplaceMessage.decode bytes).map fun (message, rest) => (.orderReplaceMessage message, rest)
  else if tag = 73 then (IndicativePriceQuantityMessage.decode bytes).map fun (message, rest) => (.indicativePriceQuantityMessage message, rest)
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
  | timeStampSecondsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TimeStampSecondsMessage.encode_length]
    omega
  | systemEventMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SystemEventMessage.encode_length]
    omega
  | quantityTickSizeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, QuantityTickSizeMessage.encode_length]
    omega
  | priceTickSizeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, PriceTickSizeMessage.encode_length]
    omega
  | orderbookDirectoryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderbookDirectoryMessage.encode_length]
    omega
  | orderbookTradingActionMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderbookTradingActionMessage.encode_length]
    omega
  | addOrderMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, AddOrderMessage.encode_length]
    omega
  | orderExecutedMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderExecutedMessage.encode_length]
    omega
  | orderExecutedWithPriceMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderExecutedWithPriceMessage.encode_length]
    omega
  | executionSummaryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ExecutionSummaryMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeMessage.encode_length]
    omega
  | brokenTradeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, BrokenTradeMessage.encode_length]
    omega
  | orderDeleteMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderDeleteMessage.encode_length]
    omega
  | orderReplaceMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderReplaceMessage.encode_length]
    omega
  | indicativePriceQuantityMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, IndicativePriceQuantityMessage.encode_length]
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

end Omi.SixSixswissexchangeTotalviewItchV1240
