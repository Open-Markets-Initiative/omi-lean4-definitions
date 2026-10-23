import Wire

/-!
# Canadian Securities Exchange CSE2 Multicast Market Data Retransmission v1.6

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.CnsxCse2RetransmissionMmdV16

/-- Event Code: one byte code -/
def EventCode.codes : List UInt8 :=
  [0x4F, 0x53, 0x48, 0x51, 0x4D, 0x45, 0x43, 0x5A]

inductive EventCode where
  | startOfMessagesTheFirstMessageIsSent -- Start Of Messages The First Message Is Sent
  | startOfSystemHours -- Start Of System Hours
  | tradingHaltedOrdersCanBeCancelledButNoNewOrdersCanBeEntered -- Trading Halted Orders Can Be Cancelled But No New Orders Can Be Entered
  | startOfMarketHoursThePreopenAuctionIsConcludedAndContinuousTradingBegins -- Start Of Market Hours The Preopen Auction Is Concluded And Continuous Trading Begins
  | endOfMarketHoursIndicatesTheEndOfContinuousTrading -- End Of Market Hours Indicates The End Of Continuous Trading
  | endOfSystemHoursIndicatesTheExchangeIsClosed -- End Of System Hours Indicates The Exchange Is Closed
  | endOfMessagesTheLastMessageSent -- End Of Messages The Last Message Sent
  | failoverEvent -- Failover Event
  | unlisted (byte : { byte : UInt8 // byte ∉ EventCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventCode

def toByte : EventCode → UInt8
  | .startOfMessagesTheFirstMessageIsSent => 0x4F
  | .startOfSystemHours => 0x53
  | .tradingHaltedOrdersCanBeCancelledButNoNewOrdersCanBeEntered => 0x48
  | .startOfMarketHoursThePreopenAuctionIsConcludedAndContinuousTradingBegins => 0x51
  | .endOfMarketHoursIndicatesTheEndOfContinuousTrading => 0x4D
  | .endOfSystemHoursIndicatesTheExchangeIsClosed => 0x45
  | .endOfMessagesTheLastMessageSent => 0x43
  | .failoverEvent => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventCode :=
  if byte = 0x4F then .startOfMessagesTheFirstMessageIsSent
  else if byte = 0x53 then .startOfSystemHours
  else if byte = 0x48 then .tradingHaltedOrdersCanBeCancelledButNoNewOrdersCanBeEntered
  else if byte = 0x51 then .startOfMarketHoursThePreopenAuctionIsConcludedAndContinuousTradingBegins
  else if byte = 0x4D then .endOfMarketHoursIndicatesTheEndOfContinuousTrading
  else if byte = 0x45 then .endOfSystemHoursIndicatesTheExchangeIsClosed
  else if byte = 0x43 then .endOfMessagesTheLastMessageSent
  else .failoverEvent

def ofByte (byte : UInt8) : EventCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventCode) : ofByte value.toByte = value := by
  cases value with
  | startOfMessagesTheFirstMessageIsSent => decide
  | startOfSystemHours => decide
  | tradingHaltedOrdersCanBeCancelledButNoNewOrdersCanBeEntered => decide
  | startOfMarketHoursThePreopenAuctionIsConcludedAndContinuousTradingBegins => decide
  | endOfMarketHoursIndicatesTheEndOfContinuousTrading => decide
  | endOfSystemHoursIndicatesTheExchangeIsClosed => decide
  | endOfMessagesTheLastMessageSent => decide
  | failoverEvent => decide
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
  [0x43, 0x54, 0x56, 0x41, 0x4E]

inductive ListingMarket where
  | cse -- Cse
  | tse -- Tse
  | tsxv -- Tsxv
  | alpha -- Alpha
  | cboeCanada -- Cboe Canada
  | unlisted (byte : { byte : UInt8 // byte ∉ ListingMarket.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ListingMarket

def toByte : ListingMarket → UInt8
  | .cse => 0x43
  | .tse => 0x54
  | .tsxv => 0x56
  | .alpha => 0x41
  | .cboeCanada => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ListingMarket :=
  if byte = 0x43 then .cse
  else if byte = 0x54 then .tse
  else if byte = 0x56 then .tsxv
  else if byte = 0x41 then .alpha
  else .cboeCanada

def ofByte (byte : UInt8) : ListingMarket :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ListingMarket) : ofByte value.toByte = value := by
  cases value with
  | cse => decide
  | tse => decide
  | tsxv => decide
  | alpha => decide
  | cboeCanada => decide
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

/-- Gmf Setting: one byte code -/
def GmfSetting.codes : List UInt8 :=
  [0x59, 0x4E]

inductive GmfSetting where
  | gmfEnabled -- Gmf Enabled
  | gmfDisabled -- Gmf Disabled
  | unlisted (byte : { byte : UInt8 // byte ∉ GmfSetting.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace GmfSetting

def toByte : GmfSetting → UInt8
  | .gmfEnabled => 0x59
  | .gmfDisabled => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : GmfSetting :=
  if byte = 0x59 then .gmfEnabled
  else .gmfDisabled

def ofByte (byte : UInt8) : GmfSetting :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : GmfSetting) : ofByte value.toByte = value := by
  cases value with
  | gmfEnabled => decide
  | gmfDisabled => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : GmfSetting) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (GmfSetting × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : GmfSetting) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : GmfSetting) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : GmfSetting) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end GmfSetting

/-- Anonymous Setting: one byte code -/
def AnonymousSetting.codes : List UInt8 :=
  [0x59, 0x4E]

inductive AnonymousSetting where
  | anonymousEnabled -- Anonymous Enabled
  | anonymousDisabled -- Anonymous Disabled
  | unlisted (byte : { byte : UInt8 // byte ∉ AnonymousSetting.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AnonymousSetting

def toByte : AnonymousSetting → UInt8
  | .anonymousEnabled => 0x59
  | .anonymousDisabled => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AnonymousSetting :=
  if byte = 0x59 then .anonymousEnabled
  else .anonymousDisabled

def ofByte (byte : UInt8) : AnonymousSetting :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AnonymousSetting) : ofByte value.toByte = value := by
  cases value with
  | anonymousEnabled => decide
  | anonymousDisabled => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AnonymousSetting) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AnonymousSetting × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AnonymousSetting) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : AnonymousSetting) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : AnonymousSetting) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AnonymousSetting

/-- Moc Eligible: one byte code -/
def MocEligible.codes : List UInt8 :=
  [0x4E]

inductive MocEligible where
  | notMocEligible -- Not Moc Eligible
  | unlisted (byte : { byte : UInt8 // byte ∉ MocEligible.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MocEligible

def toByte : MocEligible → UInt8
  | .notMocEligible => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : MocEligible :=
  .notMocEligible

def ofByte (byte : UInt8) : MocEligible :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MocEligible) : ofByte value.toByte = value := by
  cases value with
  | notMocEligible => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MocEligible) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MocEligible × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MocEligible) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : MocEligible) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : MocEligible) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MocEligible

/-- Trading State: one byte code -/
def TradingState.codes : List UInt8 :=
  [0x4E, 0x56, 0x48]

inductive TradingState where
  | normalTrading -- Normal Trading
  | suspendTrading -- Suspend Trading
  | halt -- Halt
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingState

def toByte : TradingState → UInt8
  | .normalTrading => 0x4E
  | .suspendTrading => 0x56
  | .halt => 0x48
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingState :=
  if byte = 0x4E then .normalTrading
  else if byte = 0x56 then .suspendTrading
  else .halt

def ofByte (byte : UInt8) : TradingState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingState) : ofByte value.toByte = value := by
  cases value with
  | normalTrading => decide
  | suspendTrading => decide
  | halt => decide
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

/-- Order Verb: one byte code -/
def OrderVerb.codes : List UInt8 :=
  [0x42, 0x53]

inductive OrderVerb where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderVerb.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderVerb

def toByte : OrderVerb → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderVerb :=
  if byte = 0x42 then .buy
  else .sell

def ofByte (byte : UInt8) : OrderVerb :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderVerb) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
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

/-- Odd Lot Flag: one byte code -/
def OddLotFlag.codes : List UInt8 :=
  [0x59, 0x4E]

inductive OddLotFlag where
  | oddLotOrder -- Odd Lot Order
  | notAnOddLot -- Not An Odd Lot
  | unlisted (byte : { byte : UInt8 // byte ∉ OddLotFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OddLotFlag

def toByte : OddLotFlag → UInt8
  | .oddLotOrder => 0x59
  | .notAnOddLot => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OddLotFlag :=
  if byte = 0x59 then .oddLotOrder
  else .notAnOddLot

def ofByte (byte : UInt8) : OddLotFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OddLotFlag) : ofByte value.toByte = value := by
  cases value with
  | oddLotOrder => decide
  | notAnOddLot => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OddLotFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OddLotFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OddLotFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OddLotFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OddLotFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OddLotFlag

/-- Trade Attribute: one byte code -/
def TradeAttribute.codes : List UInt8 :=
  [0x42, 0x20]

inductive TradeAttribute where
  | byPassOrder -- By Pass Order
  | default -- Default
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeAttribute.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeAttribute

def toByte : TradeAttribute → UInt8
  | .byPassOrder => 0x42
  | .default => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeAttribute :=
  if byte = 0x42 then .byPassOrder
  else .default

def ofByte (byte : UInt8) : TradeAttribute :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeAttribute) : ofByte value.toByte = value := by
  cases value with
  | byPassOrder => decide
  | default => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeAttribute) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeAttribute × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeAttribute) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TradeAttribute) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TradeAttribute) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeAttribute

/-- Cross Type: one byte code -/
def CrossType.codes : List UInt8 :=
  [0x52, 0x49, 0x43, 0x42, 0x56, 0x44, 0x20, 0x53, 0x4E]

inductive CrossType where
  | regular -- Regular
  | internal -- Internal
  | contingent -- Contingent
  | basis -- Basis
  | vwap -- Vwap
  | derivativerelated -- Derivativerelated
  | otherwiseEmptyStringNotSpecified -- Otherwise Empty String Not Specified
  | ccpClosingPrice -- Ccp Closing Price
  | netAssetValueNav -- Net Asset Value Nav
  | unlisted (byte : { byte : UInt8 // byte ∉ CrossType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CrossType

def toByte : CrossType → UInt8
  | .regular => 0x52
  | .internal => 0x49
  | .contingent => 0x43
  | .basis => 0x42
  | .vwap => 0x56
  | .derivativerelated => 0x44
  | .otherwiseEmptyStringNotSpecified => 0x20
  | .ccpClosingPrice => 0x53
  | .netAssetValueNav => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CrossType :=
  if byte = 0x52 then .regular
  else if byte = 0x49 then .internal
  else if byte = 0x43 then .contingent
  else if byte = 0x42 then .basis
  else if byte = 0x56 then .vwap
  else if byte = 0x44 then .derivativerelated
  else if byte = 0x20 then .otherwiseEmptyStringNotSpecified
  else if byte = 0x53 then .ccpClosingPrice
  else .netAssetValueNav

def ofByte (byte : UInt8) : CrossType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CrossType) : ofByte value.toByte = value := by
  cases value with
  | regular => decide
  | internal => decide
  | contingent => decide
  | basis => decide
  | vwap => decide
  | derivativerelated => decide
  | otherwiseEmptyStringNotSpecified => decide
  | ccpClosingPrice => decide
  | netAssetValueNav => decide
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

/-- Sets The Last Price: one byte code -/
def SetsTheLastPrice.codes : List UInt8 :=
  [0x59, 0x4E]

inductive SetsTheLastPrice where
  | lastSale -- Last Sale
  | notLastSale -- Not Last Sale
  | unlisted (byte : { byte : UInt8 // byte ∉ SetsTheLastPrice.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SetsTheLastPrice

def toByte : SetsTheLastPrice → UInt8
  | .lastSale => 0x59
  | .notLastSale => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SetsTheLastPrice :=
  if byte = 0x59 then .lastSale
  else .notLastSale

def ofByte (byte : UInt8) : SetsTheLastPrice :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SetsTheLastPrice) : ofByte value.toByte = value := by
  cases value with
  | lastSale => decide
  | notLastSale => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SetsTheLastPrice) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SetsTheLastPrice × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SetsTheLastPrice) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SetsTheLastPrice) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SetsTheLastPrice) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SetsTheLastPrice

/-- Opening Trade: one byte code -/
def OpeningTrade.codes : List UInt8 :=
  [0x59, 0x4E]

inductive OpeningTrade where
  | openingTrade -- Opening Trade
  | notOpeningTrade -- Not Opening Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ OpeningTrade.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OpeningTrade

def toByte : OpeningTrade → UInt8
  | .openingTrade => 0x59
  | .notOpeningTrade => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OpeningTrade :=
  if byte = 0x59 then .openingTrade
  else .notOpeningTrade

def ofByte (byte : UInt8) : OpeningTrade :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OpeningTrade) : ofByte value.toByte = value := by
  cases value with
  | openingTrade => decide
  | notOpeningTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OpeningTrade) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OpeningTrade × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OpeningTrade) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OpeningTrade) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OpeningTrade) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OpeningTrade

/-- Ccp Session Trade: one byte code -/
def CcpSessionTrade.codes : List UInt8 :=
  [0x59, 0x4E]

inductive CcpSessionTrade where
  | ccpSessionTrade -- Ccp Session Trade
  | notCcpSessionTrade -- Not Ccp Session Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ CcpSessionTrade.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CcpSessionTrade

def toByte : CcpSessionTrade → UInt8
  | .ccpSessionTrade => 0x59
  | .notCcpSessionTrade => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CcpSessionTrade :=
  if byte = 0x59 then .ccpSessionTrade
  else .notCcpSessionTrade

def ofByte (byte : UInt8) : CcpSessionTrade :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CcpSessionTrade) : ofByte value.toByte = value := by
  cases value with
  | ccpSessionTrade => decide
  | notCcpSessionTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CcpSessionTrade) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CcpSessionTrade × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CcpSessionTrade) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CcpSessionTrade) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CcpSessionTrade) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CcpSessionTrade

/-- Moc Trade Marker: one byte code -/
def MocTradeMarker.codes : List UInt8 :=
  [0x59, 0x4E]

inductive MocTradeMarker where
  | mocOrLocTrade -- Moc Or Loc Trade
  | notMocOrLocTrade -- Not Moc Or Loc Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ MocTradeMarker.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MocTradeMarker

def toByte : MocTradeMarker → UInt8
  | .mocOrLocTrade => 0x59
  | .notMocOrLocTrade => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MocTradeMarker :=
  if byte = 0x59 then .mocOrLocTrade
  else .notMocOrLocTrade

def ofByte (byte : UInt8) : MocTradeMarker :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MocTradeMarker) : ofByte value.toByte = value := by
  cases value with
  | mocOrLocTrade => decide
  | notMocOrLocTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MocTradeMarker) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MocTradeMarker × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MocTradeMarker) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : MocTradeMarker) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : MocTradeMarker) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MocTradeMarker

/-- Reason: one byte code -/
def Reason.codes : List UInt8 :=
  [0x53, 0x41]

inductive Reason where
  | supervisoryTheTradeWasManuallyBrokenByTheExchange -- Supervisory The Trade Was Manually Broken By The Exchange
  | amended -- Amended
  | unlisted (byte : { byte : UInt8 // byte ∉ Reason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Reason

def toByte : Reason → UInt8
  | .supervisoryTheTradeWasManuallyBrokenByTheExchange => 0x53
  | .amended => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Reason :=
  if byte = 0x53 then .supervisoryTheTradeWasManuallyBrokenByTheExchange
  else .amended

def ofByte (byte : UInt8) : Reason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Reason) : ofByte value.toByte = value := by
  cases value with
  | supervisoryTheTradeWasManuallyBrokenByTheExchange => decide
  | amended => decide
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

/-- Login Status: one byte code -/
def LoginStatus.codes : List UInt8 :=
  [0x59]

inductive LoginStatus where
  | loginAccepted -- Login Accepted
  | unlisted (byte : { byte : UInt8 // byte ∉ LoginStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LoginStatus

def toByte : LoginStatus → UInt8
  | .loginAccepted => 0x59
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : LoginStatus :=
  .loginAccepted

def ofByte (byte : UInt8) : LoginStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LoginStatus) : ofByte value.toByte = value := by
  cases value with
  | loginAccepted => decide
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

/-- Retransmission Status: one byte code -/
def RetransmissionStatus.codes : List UInt8 :=
  [0x59, 0x4E]

inductive RetransmissionStatus where
  | retransmissionWillFollow -- Retransmission Will Follow
  | requestIgnored -- Request Ignored
  | unlisted (byte : { byte : UInt8 // byte ∉ RetransmissionStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RetransmissionStatus

def toByte : RetransmissionStatus → UInt8
  | .retransmissionWillFollow => 0x59
  | .requestIgnored => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RetransmissionStatus :=
  if byte = 0x59 then .retransmissionWillFollow
  else .requestIgnored

def ofByte (byte : UInt8) : RetransmissionStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RetransmissionStatus) : ofByte value.toByte = value := by
  cases value with
  | retransmissionWillFollow => decide
  | requestIgnored => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RetransmissionStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RetransmissionStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RetransmissionStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : RetransmissionStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : RetransmissionStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RetransmissionStatus

/-- Spin Status: one byte code -/
def SpinStatus.codes : List UInt8 :=
  [0x53, 0x45]

inductive SpinStatus where
  | spinAcknowledged -- Spin Acknowledged
  | endOfSpin -- End Of Spin
  | unlisted (byte : { byte : UInt8 // byte ∉ SpinStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SpinStatus

def toByte : SpinStatus → UInt8
  | .spinAcknowledged => 0x53
  | .endOfSpin => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SpinStatus :=
  if byte = 0x53 then .spinAcknowledged
  else .endOfSpin

def ofByte (byte : UInt8) : SpinStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SpinStatus) : ofByte value.toByte = value := by
  cases value with
  | spinAcknowledged => decide
  | endOfSpin => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SpinStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SpinStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SpinStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SpinStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SpinStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SpinStatus

/-- Time Message: 6 bytes -/
structure TimeMessage where
  second : BitVec 32
  millisecond : BitVec 16
  deriving DecidableEq, Repr

namespace TimeMessage

def encode (message : TimeMessage) : List UInt8 :=
  encodeUInt 4 message.second
    ++ (encodeUInt 2 message.millisecond)

def decode (bytes : List UInt8) : Option (TimeMessage × List UInt8) := do
  let (second, bytes) ← decodeUInt 4 bytes
  let (millisecond, bytes) ← decodeUInt 2 bytes
  pure ({ second, millisecond }, bytes)

@[simp] theorem encode_length (message : TimeMessage) : (encode message).length = 6 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : TimeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TimeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TimeMessage

/-- System Event Message: 21 bytes -/
structure SystemEventMessage where
  timeOffset : BitVec 32
  group : BitVec 64
  eventCode : EventCode
  exchangeTimestamp : BitVec 64
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  encodeUInt 4 message.timeOffset
    ++ (encodeUInt 8 message.group
    ++ (EventCode.encode message.eventCode
    ++ (encodeUInt 8 message.exchangeTimestamp)))

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (timeOffset, bytes) ← decodeUInt 4 bytes
  let (group, bytes) ← decodeUInt 8 bytes
  let (eventCode, bytes) ← EventCode.decode bytes
  let (exchangeTimestamp, bytes) ← decodeUInt 8 bytes
  pure ({ timeOffset, group, eventCode, exchangeTimestamp }, bytes)

@[simp] theorem encode_length (message : SystemEventMessage) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, EventCode.encode_length]

theorem encode_length_pos (message : SystemEventMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemEventMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, EventCode.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SystemEventMessage

/-- Symbol Directory Message: 195 bytes -/
structure SymbolDirectoryMessage where
  timeOffset : BitVec 32
  symbol : Alpha 12
  cusip : Alpha 12
  secName : Alpha 15
  currency : Alpha 3
  stockGroup : BitVec 64
  listing : BitVec 64
  expiry : BitVec 64
  lotSize : BitVec 32
  settlementTerm : Alpha 8
  listingMarket : ListingMarket
  previousClosingPrice : BitVec 32
  listingTier : BitVec 8
  marketMakerName : Alpha 20
  marketMakerPhoneNumber : Alpha 12
  fullSecName : Alpha 75
  deriving DecidableEq, Repr

namespace SymbolDirectoryMessage

def encode (message : SymbolDirectoryMessage) : List UInt8 :=
  encodeUInt 4 message.timeOffset
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.cusip
    ++ (Alpha.encode message.secName
    ++ (Alpha.encode message.currency
    ++ (encodeUInt 8 message.stockGroup
    ++ (encodeUInt 8 message.listing
    ++ (encodeUInt 8 message.expiry
    ++ (encodeUInt 4 message.lotSize
    ++ (Alpha.encode message.settlementTerm
    ++ (ListingMarket.encode message.listingMarket
    ++ (encodeUInt 4 message.previousClosingPrice
    ++ (encodeUInt 1 message.listingTier
    ++ (Alpha.encode message.marketMakerName
    ++ (Alpha.encode message.marketMakerPhoneNumber
    ++ (Alpha.encode message.fullSecName)))))))))))))))

def decode (bytes : List UInt8) : Option (SymbolDirectoryMessage × List UInt8) := do
  let (timeOffset, bytes) ← decodeUInt 4 bytes
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (cusip, bytes) ← Alpha.decode 12 bytes
  let (secName, bytes) ← Alpha.decode 15 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (stockGroup, bytes) ← decodeUInt 8 bytes
  let (listing, bytes) ← decodeUInt 8 bytes
  let (expiry, bytes) ← decodeUInt 8 bytes
  let (lotSize, bytes) ← decodeUInt 4 bytes
  let (settlementTerm, bytes) ← Alpha.decode 8 bytes
  let (listingMarket, bytes) ← ListingMarket.decode bytes
  let (previousClosingPrice, bytes) ← decodeUInt 4 bytes
  let (listingTier, bytes) ← decodeUInt 1 bytes
  let (marketMakerName, bytes) ← Alpha.decode 20 bytes
  let (marketMakerPhoneNumber, bytes) ← Alpha.decode 12 bytes
  let (fullSecName, bytes) ← Alpha.decode 75 bytes
  pure ({ timeOffset, symbol, cusip, secName, currency, stockGroup, listing, expiry, lotSize, settlementTerm, listingMarket, previousClosingPrice, listingTier, marketMakerName, marketMakerPhoneNumber, fullSecName }, bytes)

@[simp] theorem encode_length (message : SymbolDirectoryMessage) : (encode message).length = 195 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, ListingMarket.encode_length]

theorem encode_length_pos (message : SymbolDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SymbolDirectoryMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, ListingMarket.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SymbolDirectoryMessage

/-- Symbol Dynamics Message: 35 bytes -/
structure SymbolDynamicsMessage where
  timeOffset : BitVec 32
  symbol : Alpha 12
  settlementTerm : Alpha 8
  gmfSetting : GmfSetting
  gmfVolume : BitVec 64
  anonymousSetting : AnonymousSetting
  mocEligible : MocEligible
  deriving DecidableEq, Repr

namespace SymbolDynamicsMessage

def encode (message : SymbolDynamicsMessage) : List UInt8 :=
  encodeUInt 4 message.timeOffset
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.settlementTerm
    ++ (GmfSetting.encode message.gmfSetting
    ++ (encodeUInt 8 message.gmfVolume
    ++ (AnonymousSetting.encode message.anonymousSetting
    ++ (MocEligible.encode message.mocEligible))))))

def decode (bytes : List UInt8) : Option (SymbolDynamicsMessage × List UInt8) := do
  let (timeOffset, bytes) ← decodeUInt 4 bytes
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (settlementTerm, bytes) ← Alpha.decode 8 bytes
  let (gmfSetting, bytes) ← GmfSetting.decode bytes
  let (gmfVolume, bytes) ← decodeUInt 8 bytes
  let (anonymousSetting, bytes) ← AnonymousSetting.decode bytes
  let (mocEligible, bytes) ← MocEligible.decode bytes
  pure ({ timeOffset, symbol, settlementTerm, gmfSetting, gmfVolume, anonymousSetting, mocEligible }, bytes)

@[simp] theorem encode_length (message : SymbolDynamicsMessage) : (encode message).length = 35 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, GmfSetting.encode_length, AnonymousSetting.encode_length, MocEligible.encode_length]

theorem encode_length_pos (message : SymbolDynamicsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SymbolDynamicsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, GmfSetting.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, AnonymousSetting.decode_encode, some_bind]
  dsimp only
  rw [MocEligible.decode_encode, some_bind]
  rfl

end SymbolDynamicsMessage

/-- Trading Action Message: 25 bytes -/
structure TradingActionMessage where
  timeOffset : BitVec 32
  symbol : Alpha 12
  tradingState : TradingState
  exchangeTimestamp : BitVec 64
  deriving DecidableEq, Repr

namespace TradingActionMessage

def encode (message : TradingActionMessage) : List UInt8 :=
  encodeUInt 4 message.timeOffset
    ++ (Alpha.encode message.symbol
    ++ (TradingState.encode message.tradingState
    ++ (encodeUInt 8 message.exchangeTimestamp)))

def decode (bytes : List UInt8) : Option (TradingActionMessage × List UInt8) := do
  let (timeOffset, bytes) ← decodeUInt 4 bytes
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (tradingState, bytes) ← TradingState.decode bytes
  let (exchangeTimestamp, bytes) ← decodeUInt 8 bytes
  pure ({ timeOffset, symbol, tradingState, exchangeTimestamp }, bytes)

@[simp] theorem encode_length (message : TradingActionMessage) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, TradingState.encode_length]

theorem encode_length_pos (message : TradingActionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradingActionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradingState.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TradingActionMessage

/-- Add Order Message: 71 bytes -/
structure AddOrderMessage where
  timeOffset : BitVec 32
  orderNumber : Alpha 18
  orderVerb : OrderVerb
  quantity : BitVec 32
  symbol : Alpha 12
  price : BitVec 32
  firmId : Alpha 3
  settlementTerm : Alpha 8
  oddLotFlag : OddLotFlag
  exchangeTimestamp : BitVec 64
  priorityTimestamp : BitVec 64
  deriving DecidableEq, Repr

namespace AddOrderMessage

def encode (message : AddOrderMessage) : List UInt8 :=
  encodeUInt 4 message.timeOffset
    ++ (Alpha.encode message.orderNumber
    ++ (OrderVerb.encode message.orderVerb
    ++ (encodeUInt 4 message.quantity
    ++ (Alpha.encode message.symbol
    ++ (encodeUInt 4 message.price
    ++ (Alpha.encode message.firmId
    ++ (Alpha.encode message.settlementTerm
    ++ (OddLotFlag.encode message.oddLotFlag
    ++ (encodeUInt 8 message.exchangeTimestamp
    ++ (encodeUInt 8 message.priorityTimestamp))))))))))

def decode (bytes : List UInt8) : Option (AddOrderMessage × List UInt8) := do
  let (timeOffset, bytes) ← decodeUInt 4 bytes
  let (orderNumber, bytes) ← Alpha.decode 18 bytes
  let (orderVerb, bytes) ← OrderVerb.decode bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (firmId, bytes) ← Alpha.decode 3 bytes
  let (settlementTerm, bytes) ← Alpha.decode 8 bytes
  let (oddLotFlag, bytes) ← OddLotFlag.decode bytes
  let (exchangeTimestamp, bytes) ← decodeUInt 8 bytes
  let (priorityTimestamp, bytes) ← decodeUInt 8 bytes
  pure ({ timeOffset, orderNumber, orderVerb, quantity, symbol, price, firmId, settlementTerm, oddLotFlag, exchangeTimestamp, priorityTimestamp }, bytes)

@[simp] theorem encode_length (message : AddOrderMessage) : (encode message).length = 71 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, OrderVerb.encode_length, OddLotFlag.encode_length]

theorem encode_length_pos (message : AddOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderVerb.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OddLotFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AddOrderMessage

/-- Order Executed Message: 52 bytes -/
structure OrderExecutedMessage where
  timeOffset : BitVec 32
  orderNumber : Alpha 18
  executedQuantity : BitVec 32
  matchNumber : Alpha 18
  exchangeTimestamp : BitVec 64
  deriving DecidableEq, Repr

namespace OrderExecutedMessage

def encode (message : OrderExecutedMessage) : List UInt8 :=
  encodeUInt 4 message.timeOffset
    ++ (Alpha.encode message.orderNumber
    ++ (encodeUInt 4 message.executedQuantity
    ++ (Alpha.encode message.matchNumber
    ++ (encodeUInt 8 message.exchangeTimestamp))))

def decode (bytes : List UInt8) : Option (OrderExecutedMessage × List UInt8) := do
  let (timeOffset, bytes) ← decodeUInt 4 bytes
  let (orderNumber, bytes) ← Alpha.decode 18 bytes
  let (executedQuantity, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← Alpha.decode 18 bytes
  let (exchangeTimestamp, bytes) ← decodeUInt 8 bytes
  pure ({ timeOffset, orderNumber, executedQuantity, matchNumber, exchangeTimestamp }, bytes)

@[simp] theorem encode_length (message : OrderExecutedMessage) : (encode message).length = 52 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderExecutedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderExecutedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderExecutedMessage

/-- Order Executed With Price Message: 56 bytes -/
structure OrderExecutedWithPriceMessage where
  timeOffset : BitVec 32
  orderNumber : Alpha 18
  executedQuantity : BitVec 32
  matchNumber : Alpha 18
  executionPrice : BitVec 32
  exchangeTimestamp : BitVec 64
  deriving DecidableEq, Repr

namespace OrderExecutedWithPriceMessage

def encode (message : OrderExecutedWithPriceMessage) : List UInt8 :=
  encodeUInt 4 message.timeOffset
    ++ (Alpha.encode message.orderNumber
    ++ (encodeUInt 4 message.executedQuantity
    ++ (Alpha.encode message.matchNumber
    ++ (encodeUInt 4 message.executionPrice
    ++ (encodeUInt 8 message.exchangeTimestamp)))))

def decode (bytes : List UInt8) : Option (OrderExecutedWithPriceMessage × List UInt8) := do
  let (timeOffset, bytes) ← decodeUInt 4 bytes
  let (orderNumber, bytes) ← Alpha.decode 18 bytes
  let (executedQuantity, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← Alpha.decode 18 bytes
  let (executionPrice, bytes) ← decodeUInt 4 bytes
  let (exchangeTimestamp, bytes) ← decodeUInt 8 bytes
  pure ({ timeOffset, orderNumber, executedQuantity, matchNumber, executionPrice, exchangeTimestamp }, bytes)

@[simp] theorem encode_length (message : OrderExecutedWithPriceMessage) : (encode message).length = 56 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderExecutedWithPriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderExecutedWithPriceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderExecutedWithPriceMessage

/-- Trade Message: 71 bytes -/
structure TradeMessage where
  timeOffset : BitVec 32
  executedQuantity : BitVec 32
  symbol : Alpha 12
  executionPrice : BitVec 32
  matchNumber : Alpha 18
  firmId : Alpha 3
  contraFirmId : Alpha 3
  settlementTerm : Alpha 8
  tradeAttribute : TradeAttribute
  crossType : CrossType
  oddLotFlag : OddLotFlag
  setsTheLastPrice : SetsTheLastPrice
  exchangeTimestamp : BitVec 64
  openingTrade : OpeningTrade
  ccpSessionTrade : CcpSessionTrade
  mocTradeMarker : MocTradeMarker
  deriving DecidableEq, Repr

namespace TradeMessage

def encode (message : TradeMessage) : List UInt8 :=
  encodeUInt 4 message.timeOffset
    ++ (encodeUInt 4 message.executedQuantity
    ++ (Alpha.encode message.symbol
    ++ (encodeUInt 4 message.executionPrice
    ++ (Alpha.encode message.matchNumber
    ++ (Alpha.encode message.firmId
    ++ (Alpha.encode message.contraFirmId
    ++ (Alpha.encode message.settlementTerm
    ++ (TradeAttribute.encode message.tradeAttribute
    ++ (CrossType.encode message.crossType
    ++ (OddLotFlag.encode message.oddLotFlag
    ++ (SetsTheLastPrice.encode message.setsTheLastPrice
    ++ (encodeUInt 8 message.exchangeTimestamp
    ++ (OpeningTrade.encode message.openingTrade
    ++ (CcpSessionTrade.encode message.ccpSessionTrade
    ++ (MocTradeMarker.encode message.mocTradeMarker)))))))))))))))

def decode (bytes : List UInt8) : Option (TradeMessage × List UInt8) := do
  let (timeOffset, bytes) ← decodeUInt 4 bytes
  let (executedQuantity, bytes) ← decodeUInt 4 bytes
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (executionPrice, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← Alpha.decode 18 bytes
  let (firmId, bytes) ← Alpha.decode 3 bytes
  let (contraFirmId, bytes) ← Alpha.decode 3 bytes
  let (settlementTerm, bytes) ← Alpha.decode 8 bytes
  let (tradeAttribute, bytes) ← TradeAttribute.decode bytes
  let (crossType, bytes) ← CrossType.decode bytes
  let (oddLotFlag, bytes) ← OddLotFlag.decode bytes
  let (setsTheLastPrice, bytes) ← SetsTheLastPrice.decode bytes
  let (exchangeTimestamp, bytes) ← decodeUInt 8 bytes
  let (openingTrade_, bytes) ← OpeningTrade.decode bytes
  let (ccpSessionTrade_, bytes) ← CcpSessionTrade.decode bytes
  let (mocTradeMarker, bytes) ← MocTradeMarker.decode bytes
  pure ({ timeOffset, executedQuantity, symbol, executionPrice, matchNumber, firmId, contraFirmId, settlementTerm, tradeAttribute, crossType, oddLotFlag, setsTheLastPrice, exchangeTimestamp, openingTrade := openingTrade_, ccpSessionTrade := ccpSessionTrade_, mocTradeMarker }, bytes)

@[simp] theorem encode_length (message : TradeMessage) : (encode message).length = 71 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, TradeAttribute.encode_length, CrossType.encode_length, OddLotFlag.encode_length, SetsTheLastPrice.encode_length, OpeningTrade.encode_length, CcpSessionTrade.encode_length, MocTradeMarker.encode_length]

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeAttribute.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CrossType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OddLotFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SetsTheLastPrice.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OpeningTrade.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CcpSessionTrade.decode_encode, some_bind]
  dsimp only
  rw [MocTradeMarker.decode_encode, some_bind]
  rfl

end TradeMessage

/-- Broken Trade Message: 31 bytes -/
structure BrokenTradeMessage where
  timeOffset : BitVec 32
  matchNumber : Alpha 18
  reason : Reason
  exchangeTimestamp : BitVec 64
  deriving DecidableEq, Repr

namespace BrokenTradeMessage

def encode (message : BrokenTradeMessage) : List UInt8 :=
  encodeUInt 4 message.timeOffset
    ++ (Alpha.encode message.matchNumber
    ++ (Reason.encode message.reason
    ++ (encodeUInt 8 message.exchangeTimestamp)))

def decode (bytes : List UInt8) : Option (BrokenTradeMessage × List UInt8) := do
  let (timeOffset, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← Alpha.decode 18 bytes
  let (reason, bytes) ← Reason.decode bytes
  let (exchangeTimestamp, bytes) ← decodeUInt 8 bytes
  pure ({ timeOffset, matchNumber, reason, exchangeTimestamp }, bytes)

@[simp] theorem encode_length (message : BrokenTradeMessage) : (encode message).length = 31 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, Reason.encode_length]

theorem encode_length_pos (message : BrokenTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BrokenTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Reason.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end BrokenTradeMessage

/-- Order Delete Message: 30 bytes -/
structure OrderDeleteMessage where
  timeOffset : BitVec 32
  orderNumber : Alpha 18
  exchangeTimestamp : BitVec 64
  deriving DecidableEq, Repr

namespace OrderDeleteMessage

def encode (message : OrderDeleteMessage) : List UInt8 :=
  encodeUInt 4 message.timeOffset
    ++ (Alpha.encode message.orderNumber
    ++ (encodeUInt 8 message.exchangeTimestamp))

def decode (bytes : List UInt8) : Option (OrderDeleteMessage × List UInt8) := do
  let (timeOffset, bytes) ← decodeUInt 4 bytes
  let (orderNumber, bytes) ← Alpha.decode 18 bytes
  let (exchangeTimestamp, bytes) ← decodeUInt 8 bytes
  pure ({ timeOffset, orderNumber, exchangeTimestamp }, bytes)

@[simp] theorem encode_length (message : OrderDeleteMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderDeleteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderDeleteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderDeleteMessage

/-- Order Replace Message: 38 bytes -/
structure OrderReplaceMessage where
  timeOffset : BitVec 32
  orderNumber : Alpha 18
  quantity : BitVec 32
  price : BitVec 32
  exchangeTimestamp : BitVec 64
  deriving DecidableEq, Repr

namespace OrderReplaceMessage

def encode (message : OrderReplaceMessage) : List UInt8 :=
  encodeUInt 4 message.timeOffset
    ++ (Alpha.encode message.orderNumber
    ++ (encodeUInt 4 message.quantity
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 8 message.exchangeTimestamp))))

def decode (bytes : List UInt8) : Option (OrderReplaceMessage × List UInt8) := do
  let (timeOffset, bytes) ← decodeUInt 4 bytes
  let (orderNumber, bytes) ← Alpha.decode 18 bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (exchangeTimestamp, bytes) ← decodeUInt 8 bytes
  pure ({ timeOffset, orderNumber, quantity, price, exchangeTimestamp }, bytes)

@[simp] theorem encode_length (message : OrderReplaceMessage) : (encode message).length = 38 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderReplaceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderReplaceMessage) (rest : List UInt8) :
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderReplaceMessage

/-- Best Bid Offer Message: 40 bytes -/
structure BestBidOfferMessage where
  timeOffset : BitVec 32
  symbol : Alpha 12
  bestBid : BitVec 32
  bestBidSize : BitVec 32
  bestOffer : BitVec 32
  bestOfferSize : BitVec 32
  exchangeTimestamp : BitVec 64
  deriving DecidableEq, Repr

namespace BestBidOfferMessage

def encode (message : BestBidOfferMessage) : List UInt8 :=
  encodeUInt 4 message.timeOffset
    ++ (Alpha.encode message.symbol
    ++ (encodeUInt 4 message.bestBid
    ++ (encodeUInt 4 message.bestBidSize
    ++ (encodeUInt 4 message.bestOffer
    ++ (encodeUInt 4 message.bestOfferSize
    ++ (encodeUInt 8 message.exchangeTimestamp))))))

def decode (bytes : List UInt8) : Option (BestBidOfferMessage × List UInt8) := do
  let (timeOffset, bytes) ← decodeUInt 4 bytes
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (bestBid, bytes) ← decodeUInt 4 bytes
  let (bestBidSize, bytes) ← decodeUInt 4 bytes
  let (bestOffer, bytes) ← decodeUInt 4 bytes
  let (bestOfferSize, bytes) ← decodeUInt 4 bytes
  let (exchangeTimestamp, bytes) ← decodeUInt 8 bytes
  pure ({ timeOffset, symbol, bestBid, bestBidSize, bestOffer, bestOfferSize, exchangeTimestamp }, bytes)

@[simp] theorem encode_length (message : BestBidOfferMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : BestBidOfferMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BestBidOfferMessage) (rest : List UInt8) :
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end BestBidOfferMessage

/-- Closing Price Message: 20 bytes -/
structure ClosingPriceMessage where
  timeOffset : BitVec 32
  symbol : Alpha 12
  price : BitVec 32
  deriving DecidableEq, Repr

namespace ClosingPriceMessage

def encode (message : ClosingPriceMessage) : List UInt8 :=
  encodeUInt 4 message.timeOffset
    ++ (Alpha.encode message.symbol
    ++ (encodeUInt 4 message.price))

def decode (bytes : List UInt8) : Option (ClosingPriceMessage × List UInt8) := do
  let (timeOffset, bytes) ← decodeUInt 4 bytes
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  pure ({ timeOffset, symbol, price }, bytes)

@[simp] theorem encode_length (message : ClosingPriceMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : ClosingPriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ClosingPriceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ClosingPriceMessage

/-- General Message: 132 bytes -/
structure GeneralMessage where
  timeOffset : BitVec 32
  messageText : Alpha 128
  deriving DecidableEq, Repr

namespace GeneralMessage

def encode (message : GeneralMessage) : List UInt8 :=
  encodeUInt 4 message.timeOffset
    ++ (Alpha.encode message.messageText)

def decode (bytes : List UInt8) : Option (GeneralMessage × List UInt8) := do
  let (timeOffset, bytes) ← decodeUInt 4 bytes
  let (messageText, bytes) ← Alpha.decode 128 bytes
  pure ({ timeOffset, messageText }, bytes)

@[simp] theorem encode_length (message : GeneralMessage) : (encode message).length = 132 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : GeneralMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : GeneralMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end GeneralMessage

/-- Login Request Message: 32 bytes -/
structure LoginRequestMessage where
  userId : Alpha 16
  password : Alpha 16
  deriving DecidableEq, Repr

namespace LoginRequestMessage

def encode (message : LoginRequestMessage) : List UInt8 :=
  Alpha.encode message.userId
    ++ (Alpha.encode message.password)

def decode (bytes : List UInt8) : Option (LoginRequestMessage × List UInt8) := do
  let (userId, bytes) ← Alpha.decode 16 bytes
  let (password, bytes) ← Alpha.decode 16 bytes
  pure ({ userId, password }, bytes)

@[simp] theorem encode_length (message : LoginRequestMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : LoginRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LoginRequestMessage

/-- Login Response Message: 17 bytes -/
structure LoginResponseMessage where
  userId : Alpha 16
  loginStatus : LoginStatus
  deriving DecidableEq, Repr

namespace LoginResponseMessage

def encode (message : LoginResponseMessage) : List UInt8 :=
  Alpha.encode message.userId
    ++ (LoginStatus.encode message.loginStatus)

def decode (bytes : List UInt8) : Option (LoginResponseMessage × List UInt8) := do
  let (userId, bytes) ← Alpha.decode 16 bytes
  let (loginStatus, bytes) ← LoginStatus.decode bytes
  pure ({ userId, loginStatus }, bytes)

@[simp] theorem encode_length (message : LoginResponseMessage) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, LoginStatus.encode_length]

theorem encode_length_pos (message : LoginResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [LoginStatus.decode_encode, some_bind]
  rfl

end LoginResponseMessage

/-- Retransmission Request Message: 8 bytes -/
structure RetransmissionRequestMessage where
  startSequence : BitVec 32
  numberOfMessages : BitVec 32
  deriving DecidableEq, Repr

namespace RetransmissionRequestMessage

def encode (message : RetransmissionRequestMessage) : List UInt8 :=
  encodeUInt 4 message.startSequence
    ++ (encodeUInt 4 message.numberOfMessages)

def decode (bytes : List UInt8) : Option (RetransmissionRequestMessage × List UInt8) := do
  let (startSequence, bytes) ← decodeUInt 4 bytes
  let (numberOfMessages, bytes) ← decodeUInt 4 bytes
  pure ({ startSequence, numberOfMessages }, bytes)

@[simp] theorem encode_length (message : RetransmissionRequestMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : RetransmissionRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RetransmissionRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end RetransmissionRequestMessage

/-- Retransmission Response Message: 9 bytes -/
structure RetransmissionResponseMessage where
  startSequence : BitVec 32
  numberOfMessages : BitVec 32
  retransmissionStatus : RetransmissionStatus
  deriving DecidableEq, Repr

namespace RetransmissionResponseMessage

def encode (message : RetransmissionResponseMessage) : List UInt8 :=
  encodeUInt 4 message.startSequence
    ++ (encodeUInt 4 message.numberOfMessages
    ++ (RetransmissionStatus.encode message.retransmissionStatus))

def decode (bytes : List UInt8) : Option (RetransmissionResponseMessage × List UInt8) := do
  let (startSequence, bytes) ← decodeUInt 4 bytes
  let (numberOfMessages, bytes) ← decodeUInt 4 bytes
  let (retransmissionStatus, bytes) ← RetransmissionStatus.decode bytes
  pure ({ startSequence, numberOfMessages, retransmissionStatus }, bytes)

@[simp] theorem encode_length (message : RetransmissionResponseMessage) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, RetransmissionStatus.encode_length]

theorem encode_length_pos (message : RetransmissionResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RetransmissionResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [RetransmissionStatus.decode_encode, some_bind]
  rfl

end RetransmissionResponseMessage

/-- Spin Request Message: 4 bytes -/
structure SpinRequestMessage where
  clientIdentifier : BitVec 32
  deriving DecidableEq, Repr

namespace SpinRequestMessage

def encode (message : SpinRequestMessage) : List UInt8 :=
  encodeUInt 4 message.clientIdentifier

def decode (bytes : List UInt8) : Option (SpinRequestMessage × List UInt8) := do
  let (clientIdentifier, bytes) ← decodeUInt 4 bytes
  pure ({ clientIdentifier }, bytes)

@[simp] theorem encode_length (message : SpinRequestMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : SpinRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SpinRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SpinRequestMessage

/-- Spin Response Message: 5 bytes -/
structure SpinResponseMessage where
  clientIdentifier : BitVec 32
  spinStatus : SpinStatus
  deriving DecidableEq, Repr

namespace SpinResponseMessage

def encode (message : SpinResponseMessage) : List UInt8 :=
  encodeUInt 4 message.clientIdentifier
    ++ (SpinStatus.encode message.spinStatus)

def decode (bytes : List UInt8) : Option (SpinResponseMessage × List UInt8) := do
  let (clientIdentifier, bytes) ← decodeUInt 4 bytes
  let (spinStatus, bytes) ← SpinStatus.decode bytes
  pure ({ clientIdentifier, spinStatus }, bytes)

@[simp] theorem encode_length (message : SpinResponseMessage) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, SpinStatus.encode_length]

theorem encode_length_pos (message : SpinResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SpinResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [SpinStatus.decode_encode, some_bind]
  rfl

end SpinResponseMessage

/-- Heartbeat Message: 4 bytes -/
structure HeartbeatMessage where
  clientIdentifier : BitVec 32
  deriving DecidableEq, Repr

namespace HeartbeatMessage

def encode (message : HeartbeatMessage) : List UInt8 :=
  encodeUInt 4 message.clientIdentifier

def decode (bytes : List UInt8) : Option (HeartbeatMessage × List UInt8) := do
  let (clientIdentifier, bytes) ← decodeUInt 4 bytes
  pure ({ clientIdentifier }, bytes)

@[simp] theorem encode_length (message : HeartbeatMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : HeartbeatMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : HeartbeatMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end HeartbeatMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | timeMessage (message : TimeMessage) -- "T" 0x54
  | systemEventMessage (message : SystemEventMessage) -- "S" 0x53
  | symbolDirectoryMessage (message : SymbolDirectoryMessage) -- "R" 0x52
  | symbolDynamicsMessage (message : SymbolDynamicsMessage) -- "O" 0x4F
  | tradingActionMessage (message : TradingActionMessage) -- "H" 0x48
  | addOrderMessage (message : AddOrderMessage) -- "A" 0x41
  | orderExecutedMessage (message : OrderExecutedMessage) -- "E" 0x45
  | orderExecutedWithPriceMessage (message : OrderExecutedWithPriceMessage) -- "C" 0x43
  | tradeMessage (message : TradeMessage) -- "P" 0x50
  | brokenTradeMessage (message : BrokenTradeMessage) -- "B" 0x42
  | orderDeleteMessage (message : OrderDeleteMessage) -- "D" 0x44
  | orderReplaceMessage (message : OrderReplaceMessage) -- "U" 0x55
  | bestBidOfferMessage (message : BestBidOfferMessage) -- "Q" 0x51
  | closingPriceMessage (message : ClosingPriceMessage) -- "F" 0x46
  | generalMessage (message : GeneralMessage) -- "G" 0x47
  | loginRequestMessage (message : LoginRequestMessage) -- "l" 0x6C
  | loginResponseMessage (message : LoginResponseMessage) -- "a" 0x61
  | retransmissionRequestMessage (message : RetransmissionRequestMessage) -- "r" 0x72
  | retransmissionResponseMessage (message : RetransmissionResponseMessage) -- "b" 0x62
  | spinRequestMessage (message : SpinRequestMessage) -- "s" 0x73
  | spinResponseMessage (message : SpinResponseMessage) -- "c" 0x63
  | heartbeatMessage (message : HeartbeatMessage) -- "h" 0x68
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .timeMessage _ => 84
  | .systemEventMessage _ => 83
  | .symbolDirectoryMessage _ => 82
  | .symbolDynamicsMessage _ => 79
  | .tradingActionMessage _ => 72
  | .addOrderMessage _ => 65
  | .orderExecutedMessage _ => 69
  | .orderExecutedWithPriceMessage _ => 67
  | .tradeMessage _ => 80
  | .brokenTradeMessage _ => 66
  | .orderDeleteMessage _ => 68
  | .orderReplaceMessage _ => 85
  | .bestBidOfferMessage _ => 81
  | .closingPriceMessage _ => 70
  | .generalMessage _ => 71
  | .loginRequestMessage _ => 108
  | .loginResponseMessage _ => 97
  | .retransmissionRequestMessage _ => 114
  | .retransmissionResponseMessage _ => 98
  | .spinRequestMessage _ => 115
  | .spinResponseMessage _ => 99
  | .heartbeatMessage _ => 104

def encode : Payload → List UInt8
  | .timeMessage message => TimeMessage.encode message
  | .systemEventMessage message => SystemEventMessage.encode message
  | .symbolDirectoryMessage message => SymbolDirectoryMessage.encode message
  | .symbolDynamicsMessage message => SymbolDynamicsMessage.encode message
  | .tradingActionMessage message => TradingActionMessage.encode message
  | .addOrderMessage message => AddOrderMessage.encode message
  | .orderExecutedMessage message => OrderExecutedMessage.encode message
  | .orderExecutedWithPriceMessage message => OrderExecutedWithPriceMessage.encode message
  | .tradeMessage message => TradeMessage.encode message
  | .brokenTradeMessage message => BrokenTradeMessage.encode message
  | .orderDeleteMessage message => OrderDeleteMessage.encode message
  | .orderReplaceMessage message => OrderReplaceMessage.encode message
  | .bestBidOfferMessage message => BestBidOfferMessage.encode message
  | .closingPriceMessage message => ClosingPriceMessage.encode message
  | .generalMessage message => GeneralMessage.encode message
  | .loginRequestMessage message => LoginRequestMessage.encode message
  | .loginResponseMessage message => LoginResponseMessage.encode message
  | .retransmissionRequestMessage message => RetransmissionRequestMessage.encode message
  | .retransmissionResponseMessage message => RetransmissionResponseMessage.encode message
  | .spinRequestMessage message => SpinRequestMessage.encode message
  | .spinResponseMessage message => SpinResponseMessage.encode message
  | .heartbeatMessage message => HeartbeatMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 195 := by
  cases message with
  | timeMessage inner =>
    simp only [encode, TimeMessage.encode_length]
    omega
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega
  | symbolDirectoryMessage inner =>
    simp only [encode, SymbolDirectoryMessage.encode_length]
    omega
  | symbolDynamicsMessage inner =>
    simp only [encode, SymbolDynamicsMessage.encode_length]
    omega
  | tradingActionMessage inner =>
    simp only [encode, TradingActionMessage.encode_length]
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
  | bestBidOfferMessage inner =>
    simp only [encode, BestBidOfferMessage.encode_length]
    omega
  | closingPriceMessage inner =>
    simp only [encode, ClosingPriceMessage.encode_length]
    omega
  | generalMessage inner =>
    simp only [encode, GeneralMessage.encode_length]
    omega
  | loginRequestMessage inner =>
    simp only [encode, LoginRequestMessage.encode_length]
    omega
  | loginResponseMessage inner =>
    simp only [encode, LoginResponseMessage.encode_length]
    omega
  | retransmissionRequestMessage inner =>
    simp only [encode, RetransmissionRequestMessage.encode_length]
    omega
  | retransmissionResponseMessage inner =>
    simp only [encode, RetransmissionResponseMessage.encode_length]
    omega
  | spinRequestMessage inner =>
    simp only [encode, SpinRequestMessage.encode_length]
    omega
  | spinResponseMessage inner =>
    simp only [encode, SpinResponseMessage.encode_length]
    omega
  | heartbeatMessage inner =>
    simp only [encode, HeartbeatMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 84 then (TimeMessage.decode bytes).map fun (message, rest) => (.timeMessage message, rest)
  else if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 82 then (SymbolDirectoryMessage.decode bytes).map fun (message, rest) => (.symbolDirectoryMessage message, rest)
  else if tag = 79 then (SymbolDynamicsMessage.decode bytes).map fun (message, rest) => (.symbolDynamicsMessage message, rest)
  else if tag = 72 then (TradingActionMessage.decode bytes).map fun (message, rest) => (.tradingActionMessage message, rest)
  else if tag = 65 then (AddOrderMessage.decode bytes).map fun (message, rest) => (.addOrderMessage message, rest)
  else if tag = 69 then (OrderExecutedMessage.decode bytes).map fun (message, rest) => (.orderExecutedMessage message, rest)
  else if tag = 67 then (OrderExecutedWithPriceMessage.decode bytes).map fun (message, rest) => (.orderExecutedWithPriceMessage message, rest)
  else if tag = 80 then (TradeMessage.decode bytes).map fun (message, rest) => (.tradeMessage message, rest)
  else if tag = 66 then (BrokenTradeMessage.decode bytes).map fun (message, rest) => (.brokenTradeMessage message, rest)
  else if tag = 68 then (OrderDeleteMessage.decode bytes).map fun (message, rest) => (.orderDeleteMessage message, rest)
  else if tag = 85 then (OrderReplaceMessage.decode bytes).map fun (message, rest) => (.orderReplaceMessage message, rest)
  else if tag = 81 then (BestBidOfferMessage.decode bytes).map fun (message, rest) => (.bestBidOfferMessage message, rest)
  else if tag = 70 then (ClosingPriceMessage.decode bytes).map fun (message, rest) => (.closingPriceMessage message, rest)
  else if tag = 71 then (GeneralMessage.decode bytes).map fun (message, rest) => (.generalMessage message, rest)
  else if tag = 108 then (LoginRequestMessage.decode bytes).map fun (message, rest) => (.loginRequestMessage message, rest)
  else if tag = 97 then (LoginResponseMessage.decode bytes).map fun (message, rest) => (.loginResponseMessage message, rest)
  else if tag = 114 then (RetransmissionRequestMessage.decode bytes).map fun (message, rest) => (.retransmissionRequestMessage message, rest)
  else if tag = 98 then (RetransmissionResponseMessage.decode bytes).map fun (message, rest) => (.retransmissionResponseMessage message, rest)
  else if tag = 115 then (SpinRequestMessage.decode bytes).map fun (message, rest) => (.spinRequestMessage message, rest)
  else if tag = 99 then (SpinResponseMessage.decode bytes).map fun (message, rest) => (.spinResponseMessage message, rest)
  else if tag = 104 then (HeartbeatMessage.decode bytes).map fun (message, rest) => (.heartbeatMessage message, rest)
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
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 1 < 256 ^ 1 := by
  unfold encodeBody
  cases message.payload with
  | timeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TimeMessage.encode_length]
    omega
  | systemEventMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SystemEventMessage.encode_length]
    omega
  | symbolDirectoryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SymbolDirectoryMessage.encode_length]
    omega
  | symbolDynamicsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SymbolDynamicsMessage.encode_length]
    omega
  | tradingActionMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradingActionMessage.encode_length]
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
  | bestBidOfferMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, BestBidOfferMessage.encode_length]
    omega
  | closingPriceMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ClosingPriceMessage.encode_length]
    omega
  | generalMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, GeneralMessage.encode_length]
    omega
  | loginRequestMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, LoginRequestMessage.encode_length]
    omega
  | loginResponseMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, LoginResponseMessage.encode_length]
    omega
  | retransmissionRequestMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, RetransmissionRequestMessage.encode_length]
    omega
  | retransmissionResponseMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, RetransmissionResponseMessage.encode_length]
    omega
  | spinRequestMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SpinRequestMessage.encode_length]
    omega
  | spinResponseMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SpinResponseMessage.encode_length]
    omega
  | heartbeatMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, HeartbeatMessage.encode_length]
    omega

/-- Size rule: Sub Length counts the bytes after it plus 1, so it is written from the body and checked on decode -/
def encode : Message → List UInt8 :=
  encodeFramed 1 1 encodeBody

def decode : List UInt8 → Option (Message × List UInt8) :=
  decodeFramed 1 1 decodeBody

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 1 1 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end Message

/-- Block -/
structure Block where
  blockStartSequence : BitVec 32
  message : Bounded 1 Message
  deriving DecidableEq, Repr

namespace Block

def encodeBody (message : Block) : List UInt8 :=
  encodeUInt 1 (BitVec.ofNat (8 * 1) message.message.val.length)
    ++ (encodeUInt 4 message.blockStartSequence
    ++ (encodeMany Message.encode message.message.val))

def decodeBody (bytes : List UInt8) : Option (Block × List UInt8) := do
  let (blockNumberOfMessages, bytes) ← decodeUInt 1 bytes
  let (blockStartSequence, bytes) ← decodeUInt 4 bytes
  let (message_, bytes) ← decodeMany Message.decode blockNumberOfMessages.toNat bytes
  if fits_message : message_.length < 256 ^ 1 then
    pure ({ blockStartSequence, message := ⟨message_, fits_message⟩ }, bytes)
  else none

theorem decodeBody_encodeBody (message : Block) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt]
  rfl

/-- Size rule: Block Length counts the bytes after it plus 2, so it is written from the body; the body has no bound the prefix must fit, so it is read by its content and the prefix is not checked -/
def encode (message : Block) : List UInt8 :=
  encodeUInt 2 (BitVec.ofNat (8 * 2) ((encodeBody message).length + 2)) ++ encodeBody message

def decode (bytes : List UInt8) : Option (Block × List UInt8) := do
  let (_, bytes) ← decodeUInt 2 bytes
  decodeBody bytes

@[simp] theorem decode_encode (message : Block) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  exact decodeBody_encodeBody message rest

theorem encode_length_pos (message : Block) : (encode message).length > 0 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]
  omega

end Block

/-- Packet -/
structure Packet where
  block : List Block
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeMany Block.encode message.block

def decode (bytes : List UInt8) : Option Packet := do
  let block ← decodeAll Block.decode bytes.length bytes
  pure { block }

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany Block.encode Block.decode Block.decode_encode Block.encode_length_pos message.block _ (encodeMany_length_ge Block.encode Block.encode_length_pos message.block), some_bind]
  rfl

end Packet

end Omi.CnsxCse2RetransmissionMmdV16
