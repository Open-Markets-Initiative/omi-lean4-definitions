import Wire

/-!
# Athens Exchange Group Athens Exchange Derivatives Market Real Time Channel v5.2

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.AthexAthexderivativesRealtimeIdsV52

/-- Message Subcategory: one byte code -/
def MessageSubcategory.codes : List UInt8 :=
  [0x20, 0x42, 0x45, 0x49, 0x4E, 0x53, 0x57, 0x4F, 0x46, 0x52, 0x56]

inductive MessageSubcategory where
  | generic -- Generic
  | bond -- Bond
  | etf -- Etf
  | stockIndex -- Stock Index
  | etfIndicativeNetAssetValue -- Etf Indicative Net Asset Value
  | stockRights -- Stock Rights
  | warrant -- Warrant
  | option -- Option
  | future -- Future
  | repos -- Repos
  | standardCombinations -- Standard Combinations
  | unlisted (byte : { byte : UInt8 // byte ∉ MessageSubcategory.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MessageSubcategory

def toByte : MessageSubcategory → UInt8
  | .generic => 0x20
  | .bond => 0x42
  | .etf => 0x45
  | .stockIndex => 0x49
  | .etfIndicativeNetAssetValue => 0x4E
  | .stockRights => 0x53
  | .warrant => 0x57
  | .option => 0x4F
  | .future => 0x46
  | .repos => 0x52
  | .standardCombinations => 0x56
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MessageSubcategory :=
  if byte = 0x20 then .generic
  else if byte = 0x42 then .bond
  else if byte = 0x45 then .etf
  else if byte = 0x49 then .stockIndex
  else if byte = 0x4E then .etfIndicativeNetAssetValue
  else if byte = 0x53 then .stockRights
  else if byte = 0x57 then .warrant
  else if byte = 0x4F then .option
  else if byte = 0x46 then .future
  else if byte = 0x52 then .repos
  else .standardCombinations

def ofByte (byte : UInt8) : MessageSubcategory :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MessageSubcategory) : ofByte value.toByte = value := by
  cases value with
  | generic => decide
  | bond => decide
  | etf => decide
  | stockIndex => decide
  | etfIndicativeNetAssetValue => decide
  | stockRights => decide
  | warrant => decide
  | option => decide
  | future => decide
  | repos => decide
  | standardCombinations => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MessageSubcategory) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MessageSubcategory × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MessageSubcategory) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : MessageSubcategory) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : MessageSubcategory) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MessageSubcategory

/-- Board Id: one byte code -/
def BoardId.codes : List UInt8 :=
  [0x4D, 0x4F, 0x42, 0x53, 0x46]

inductive BoardId where
  | mainBoard -- Main Board
  | oddLotBoard -- Odd Lot Board
  | preAgreedBoard -- Pre Agreed Board
  | specialTermsBoard -- Special Terms Board
  | forcedSalesBoard -- Forced Sales Board
  | unlisted (byte : { byte : UInt8 // byte ∉ BoardId.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BoardId

def toByte : BoardId → UInt8
  | .mainBoard => 0x4D
  | .oddLotBoard => 0x4F
  | .preAgreedBoard => 0x42
  | .specialTermsBoard => 0x53
  | .forcedSalesBoard => 0x46
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BoardId :=
  if byte = 0x4D then .mainBoard
  else if byte = 0x4F then .oddLotBoard
  else if byte = 0x42 then .preAgreedBoard
  else if byte = 0x53 then .specialTermsBoard
  else .forcedSalesBoard

def ofByte (byte : UInt8) : BoardId :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BoardId) : ofByte value.toByte = value := by
  cases value with
  | mainBoard => decide
  | oddLotBoard => decide
  | preAgreedBoard => decide
  | specialTermsBoard => decide
  | forcedSalesBoard => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BoardId) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BoardId × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BoardId) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : BoardId) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : BoardId) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BoardId

/-- Trade Type: one byte code -/
def TradeType.codes : List UInt8 :=
  [0x4E, 0x45, 0x43]

inductive TradeType where
  | new -- New
  | edit -- Edit
  | cancel -- Cancel
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeType

def toByte : TradeType → UInt8
  | .new => 0x4E
  | .edit => 0x45
  | .cancel => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeType :=
  if byte = 0x4E then .new
  else if byte = 0x45 then .edit
  else .cancel

def ofByte (byte : UInt8) : TradeType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeType) : ofByte value.toByte = value := by
  cases value with
  | new => decide
  | edit => decide
  | cancel => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TradeType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TradeType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeType

/-- Trade Source: one byte code -/
def TradeSource.codes : List UInt8 :=
  [0x54, 0x43]

inductive TradeSource where
  | tradingPlatform -- Trading Platform
  | clearingSystem -- Clearing System
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeSource.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeSource

def toByte : TradeSource → UInt8
  | .tradingPlatform => 0x54
  | .clearingSystem => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeSource :=
  if byte = 0x54 then .tradingPlatform
  else .clearingSystem

def ofByte (byte : UInt8) : TradeSource :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeSource) : ofByte value.toByte = value := by
  cases value with
  | tradingPlatform => decide
  | clearingSystem => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeSource) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeSource × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeSource) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TradeSource) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TradeSource) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeSource

/-- Buy Order Type: one byte code -/
def BuyOrderType.codes : List UInt8 :=
  [0x42, 0x51, 0x4E]

inductive BuyOrderType where
  | strategy -- Strategy
  | quote -- Quote
  | normal -- Normal
  | unlisted (byte : { byte : UInt8 // byte ∉ BuyOrderType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BuyOrderType

def toByte : BuyOrderType → UInt8
  | .strategy => 0x42
  | .quote => 0x51
  | .normal => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BuyOrderType :=
  if byte = 0x42 then .strategy
  else if byte = 0x51 then .quote
  else .normal

def ofByte (byte : UInt8) : BuyOrderType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BuyOrderType) : ofByte value.toByte = value := by
  cases value with
  | strategy => decide
  | quote => decide
  | normal => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BuyOrderType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BuyOrderType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BuyOrderType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : BuyOrderType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : BuyOrderType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BuyOrderType

/-- Sell Order Type: one byte code -/
def SellOrderType.codes : List UInt8 :=
  [0x42, 0x51, 0x4E]

inductive SellOrderType where
  | strategy -- Strategy
  | quote -- Quote
  | normal -- Normal
  | unlisted (byte : { byte : UInt8 // byte ∉ SellOrderType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SellOrderType

def toByte : SellOrderType → UInt8
  | .strategy => 0x42
  | .quote => 0x51
  | .normal => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SellOrderType :=
  if byte = 0x42 then .strategy
  else if byte = 0x51 then .quote
  else .normal

def ofByte (byte : UInt8) : SellOrderType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SellOrderType) : ofByte value.toByte = value := by
  cases value with
  | strategy => decide
  | quote => decide
  | normal => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SellOrderType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SellOrderType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SellOrderType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SellOrderType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SellOrderType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SellOrderType

/-- Buy Algo Flag: one byte code -/
def BuyAlgoFlag.codes : List UInt8 :=
  [0x59]

inductive BuyAlgoFlag where
  | flagOn -- Flag On
  | unlisted (byte : { byte : UInt8 // byte ∉ BuyAlgoFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BuyAlgoFlag

def toByte : BuyAlgoFlag → UInt8
  | .flagOn => 0x59
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : BuyAlgoFlag :=
  .flagOn

def ofByte (byte : UInt8) : BuyAlgoFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BuyAlgoFlag) : ofByte value.toByte = value := by
  cases value with
  | flagOn => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BuyAlgoFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BuyAlgoFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BuyAlgoFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : BuyAlgoFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : BuyAlgoFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BuyAlgoFlag

/-- Sell Algo Flag: one byte code -/
def SellAlgoFlag.codes : List UInt8 :=
  [0x59]

inductive SellAlgoFlag where
  | flagOn -- Flag On
  | unlisted (byte : { byte : UInt8 // byte ∉ SellAlgoFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SellAlgoFlag

def toByte : SellAlgoFlag → UInt8
  | .flagOn => 0x59
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : SellAlgoFlag :=
  .flagOn

def ofByte (byte : UInt8) : SellAlgoFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SellAlgoFlag) : ofByte value.toByte = value := by
  cases value with
  | flagOn => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SellAlgoFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SellAlgoFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SellAlgoFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SellAlgoFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SellAlgoFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SellAlgoFlag

/-- Sdiv Flag: one byte code -/
def SdivFlag.codes : List UInt8 :=
  [0x59]

inductive SdivFlag where
  | flagOn -- Flag On
  | unlisted (byte : { byte : UInt8 // byte ∉ SdivFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SdivFlag

def toByte : SdivFlag → UInt8
  | .flagOn => 0x59
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : SdivFlag :=
  .flagOn

def ofByte (byte : UInt8) : SdivFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SdivFlag) : ofByte value.toByte = value := by
  cases value with
  | flagOn => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SdivFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SdivFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SdivFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SdivFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SdivFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SdivFlag

/-- Dupl Flag: one byte code -/
def DuplFlag.codes : List UInt8 :=
  [0x59]

inductive DuplFlag where
  | flagOn -- Flag On
  | unlisted (byte : { byte : UInt8 // byte ∉ DuplFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DuplFlag

def toByte : DuplFlag → UInt8
  | .flagOn => 0x59
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : DuplFlag :=
  .flagOn

def ofByte (byte : UInt8) : DuplFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DuplFlag) : ofByte value.toByte = value := by
  cases value with
  | flagOn => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DuplFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DuplFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DuplFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : DuplFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : DuplFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DuplFlag

/-- Price Flag: one byte code -/
def PriceFlag.codes : List UInt8 :=
  [0x30, 0x31, 0x32]

inductive PriceFlag where
  | projectedAuctionPrice -- Projected Auction Price
  | auctionOpenPrice -- Auction Open Price
  | projectedClose -- Projected Close
  | unlisted (byte : { byte : UInt8 // byte ∉ PriceFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PriceFlag

def toByte : PriceFlag → UInt8
  | .projectedAuctionPrice => 0x30
  | .auctionOpenPrice => 0x31
  | .projectedClose => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PriceFlag :=
  if byte = 0x30 then .projectedAuctionPrice
  else if byte = 0x31 then .auctionOpenPrice
  else .projectedClose

def ofByte (byte : UInt8) : PriceFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PriceFlag) : ofByte value.toByte = value := by
  cases value with
  | projectedAuctionPrice => decide
  | auctionOpenPrice => decide
  | projectedClose => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PriceFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PriceFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PriceFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : PriceFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : PriceFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PriceFlag

/-- Phase Id: one byte code -/
def PhaseId.codes : List UInt8 :=
  [0x20, 0x50, 0x54, 0x41, 0x43, 0x53]

inductive PhaseId where
  | startPhase -- Start Phase
  | preCall -- Pre Call
  | continuous -- Continuous
  | atcOrdersReleased -- Atc Orders Released
  | closingPriceTrading -- Closing Price Trading
  | stop -- Stop
  | unlisted (byte : { byte : UInt8 // byte ∉ PhaseId.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PhaseId

def toByte : PhaseId → UInt8
  | .startPhase => 0x20
  | .preCall => 0x50
  | .continuous => 0x54
  | .atcOrdersReleased => 0x41
  | .closingPriceTrading => 0x43
  | .stop => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PhaseId :=
  if byte = 0x20 then .startPhase
  else if byte = 0x50 then .preCall
  else if byte = 0x54 then .continuous
  else if byte = 0x41 then .atcOrdersReleased
  else if byte = 0x43 then .closingPriceTrading
  else .stop

def ofByte (byte : UInt8) : PhaseId :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PhaseId) : ofByte value.toByte = value := by
  cases value with
  | startPhase => decide
  | preCall => decide
  | continuous => decide
  | atcOrdersReleased => decide
  | closingPriceTrading => decide
  | stop => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PhaseId) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PhaseId × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PhaseId) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : PhaseId) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : PhaseId) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PhaseId

/-- Instrument Status: one byte code -/
def InstrumentStatus.codes : List UInt8 :=
  [0x41, 0x48, 0x53, 0x52]

inductive InstrumentStatus where
  | active -- Active
  | halt -- Halt
  | suspended -- Suspended
  | resumed -- Resumed
  | unlisted (byte : { byte : UInt8 // byte ∉ InstrumentStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InstrumentStatus

def toByte : InstrumentStatus → UInt8
  | .active => 0x41
  | .halt => 0x48
  | .suspended => 0x53
  | .resumed => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : InstrumentStatus :=
  if byte = 0x41 then .active
  else if byte = 0x48 then .halt
  else if byte = 0x53 then .suspended
  else .resumed

def ofByte (byte : UInt8) : InstrumentStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InstrumentStatus) : ofByte value.toByte = value := by
  cases value with
  | active => decide
  | halt => decide
  | suspended => decide
  | resumed => decide
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

/-- Halt Suspend Reason: one byte code -/
def HaltSuspendReason.codes : List UInt8 :=
  [0x20, 0x45, 0x56]

inductive HaltSuspendReason where
  | noReason -- No Reason
  | exchange -- Exchange
  | volatilityInterrupter -- Volatility Interrupter
  | unlisted (byte : { byte : UInt8 // byte ∉ HaltSuspendReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace HaltSuspendReason

def toByte : HaltSuspendReason → UInt8
  | .noReason => 0x20
  | .exchange => 0x45
  | .volatilityInterrupter => 0x56
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : HaltSuspendReason :=
  if byte = 0x20 then .noReason
  else if byte = 0x45 then .exchange
  else .volatilityInterrupter

def ofByte (byte : UInt8) : HaltSuspendReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : HaltSuspendReason) : ofByte value.toByte = value := by
  cases value with
  | noReason => decide
  | exchange => decide
  | volatilityInterrupter => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : HaltSuspendReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (HaltSuspendReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : HaltSuspendReason) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : HaltSuspendReason) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : HaltSuspendReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end HaltSuspendReason

/-- Market Status: one byte code -/
def MarketStatus.codes : List UInt8 :=
  [0x50, 0x4A, 0x54, 0x43, 0x52, 0x45, 0x48]

inductive MarketStatus where
  | preCall -- Pre Call
  | projectedAuction -- Projected Auction
  | continuous -- Continuous
  | closingPriceTrading -- Closing Price Trading
  | runOff -- Run Off
  | endOfDay -- End Of Day
  | halt -- Halt
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketStatus

def toByte : MarketStatus → UInt8
  | .preCall => 0x50
  | .projectedAuction => 0x4A
  | .continuous => 0x54
  | .closingPriceTrading => 0x43
  | .runOff => 0x52
  | .endOfDay => 0x45
  | .halt => 0x48
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketStatus :=
  if byte = 0x50 then .preCall
  else if byte = 0x4A then .projectedAuction
  else if byte = 0x54 then .continuous
  else if byte = 0x43 then .closingPriceTrading
  else if byte = 0x52 then .runOff
  else if byte = 0x45 then .endOfDay
  else .halt

def ofByte (byte : UInt8) : MarketStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketStatus) : ofByte value.toByte = value := by
  cases value with
  | preCall => decide
  | projectedAuction => decide
  | continuous => decide
  | closingPriceTrading => decide
  | runOff => decide
  | endOfDay => decide
  | halt => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarketStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : MarketStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : MarketStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarketStatus

/-- Side: one byte code -/
def Side.codes : List UInt8 :=
  [0x42, 0x53]

inductive Side where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x42 then .buy
  else .sell

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
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

/-- Original Price Type: one byte code -/
def OriginalPriceType.codes : List UInt8 :=
  [0x4C, 0x4D, 0x4F, 0x43]

inductive OriginalPriceType where
  | limitPrice -- Limit Price
  | market -- Market
  | atTheOpen -- At The Open
  | atTheClose -- At The Close
  | unlisted (byte : { byte : UInt8 // byte ∉ OriginalPriceType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OriginalPriceType

def toByte : OriginalPriceType → UInt8
  | .limitPrice => 0x4C
  | .market => 0x4D
  | .atTheOpen => 0x4F
  | .atTheClose => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OriginalPriceType :=
  if byte = 0x4C then .limitPrice
  else if byte = 0x4D then .market
  else if byte = 0x4F then .atTheOpen
  else .atTheClose

def ofByte (byte : UInt8) : OriginalPriceType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OriginalPriceType) : ofByte value.toByte = value := by
  cases value with
  | limitPrice => decide
  | market => decide
  | atTheOpen => decide
  | atTheClose => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OriginalPriceType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OriginalPriceType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OriginalPriceType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OriginalPriceType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OriginalPriceType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OriginalPriceType

/-- Order Lifetime: one byte code -/
def OrderLifetime.codes : List UInt8 :=
  [0x44, 0x43, 0x45]

inductive OrderLifetime where
  | day -- Day
  | goodTillCancel -- Good Till Cancel
  | goodTillDate -- Good Till Date
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderLifetime.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderLifetime

def toByte : OrderLifetime → UInt8
  | .day => 0x44
  | .goodTillCancel => 0x43
  | .goodTillDate => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderLifetime :=
  if byte = 0x44 then .day
  else if byte = 0x43 then .goodTillCancel
  else .goodTillDate

def ofByte (byte : UInt8) : OrderLifetime :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderLifetime) : ofByte value.toByte = value := by
  cases value with
  | day => decide
  | goodTillCancel => decide
  | goodTillDate => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderLifetime) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderLifetime × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderLifetime) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OrderLifetime) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OrderLifetime) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderLifetime

/-- Special Conditions: one byte code -/
def SpecialConditions.codes : List UInt8 :=
  [0x4E, 0x46, 0x49, 0x53, 0x44, 0x41, 0x4D, 0x4F]

inductive SpecialConditions where
  | none_ -- None
  | fillOrKill -- Fill Or Kill
  | immediateOrCancel -- Immediate Or Cancel
  | stopInstrument -- Stop Instrument
  | stopIndex -- Stop Index
  | allOrNone -- All Or None
  | minimumFill -- Minimum Fill
  | multipleOf -- Multiple Of
  | unlisted (byte : { byte : UInt8 // byte ∉ SpecialConditions.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SpecialConditions

def toByte : SpecialConditions → UInt8
  | .none_ => 0x4E
  | .fillOrKill => 0x46
  | .immediateOrCancel => 0x49
  | .stopInstrument => 0x53
  | .stopIndex => 0x44
  | .allOrNone => 0x41
  | .minimumFill => 0x4D
  | .multipleOf => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SpecialConditions :=
  if byte = 0x4E then .none_
  else if byte = 0x46 then .fillOrKill
  else if byte = 0x49 then .immediateOrCancel
  else if byte = 0x53 then .stopInstrument
  else if byte = 0x44 then .stopIndex
  else if byte = 0x41 then .allOrNone
  else if byte = 0x4D then .minimumFill
  else .multipleOf

def ofByte (byte : UInt8) : SpecialConditions :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SpecialConditions) : ofByte value.toByte = value := by
  cases value with
  | none_ => decide
  | fillOrKill => decide
  | immediateOrCancel => decide
  | stopInstrument => decide
  | stopIndex => decide
  | allOrNone => decide
  | minimumFill => decide
  | multipleOf => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SpecialConditions) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SpecialConditions × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SpecialConditions) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SpecialConditions) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SpecialConditions) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SpecialConditions

/-- Order Type: one byte code -/
def OrderType.codes : List UInt8 :=
  [0x42, 0x51, 0x4E]

inductive OrderType where
  | strategy -- Strategy
  | quote -- Quote
  | normal -- Normal
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderType

def toByte : OrderType → UInt8
  | .strategy => 0x42
  | .quote => 0x51
  | .normal => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderType :=
  if byte = 0x42 then .strategy
  else if byte = 0x51 then .quote
  else .normal

def ofByte (byte : UInt8) : OrderType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderType) : ofByte value.toByte = value := by
  cases value with
  | strategy => decide
  | quote => decide
  | normal => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OrderType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OrderType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderType

/-- Start Of Day Control Message: 0 bytes -/
structure StartOfDayControlMessage where
  deriving DecidableEq, Repr

namespace StartOfDayControlMessage

def encode (_ : StartOfDayControlMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (StartOfDayControlMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : StartOfDayControlMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : StartOfDayControlMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : StartOfDayControlMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end StartOfDayControlMessage

/-- Administrative Message -/
structure AdministrativeMessage where
  freeText : List UInt8
  deriving DecidableEq, Repr

namespace AdministrativeMessage

def encode (message : AdministrativeMessage) : List UInt8 :=
  encodeMany Byte.encode message.freeText

def decode (bytes : List UInt8) : Option AdministrativeMessage := do
  let freeText ← decodeAll Byte.decode bytes.length bytes
  pure { freeText }

theorem decode_encode (message : AdministrativeMessage) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany Byte.encode Byte.decode Byte.decode_encode Byte.encode_length_pos message.freeText _ (encodeMany_length_ge Byte.encode Byte.encode_length_pos message.freeText), some_bind]
  rfl

end AdministrativeMessage

/-- End Of Day Control Message: 0 bytes -/
structure EndOfDayControlMessage where
  deriving DecidableEq, Repr

namespace EndOfDayControlMessage

def encode (_ : EndOfDayControlMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (EndOfDayControlMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : EndOfDayControlMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : EndOfDayControlMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : EndOfDayControlMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end EndOfDayControlMessage

/-- Line Verification Control Message: 0 bytes -/
structure LineVerificationControlMessage where
  deriving DecidableEq, Repr

namespace LineVerificationControlMessage

def encode (_ : LineVerificationControlMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (LineVerificationControlMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : LineVerificationControlMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : LineVerificationControlMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LineVerificationControlMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end LineVerificationControlMessage

/-- Any Control Message Text, selected by Message Type -/
inductive ControlMessageText where
  | startOfDayControlMessage (message : StartOfDayControlMessage) -- "A" 0x41
  | administrativeMessage (message : AdministrativeMessage) -- "F" 0x46
  | endOfDayControlMessage (message : EndOfDayControlMessage) -- "H" 0x48
  | lineVerificationControlMessage (message : LineVerificationControlMessage) -- "T" 0x54
  deriving DecidableEq, Repr

namespace ControlMessageText

/-- The Message Type each message is sent under -/
def tag : ControlMessageText → BitVec 8
  | .startOfDayControlMessage _ => 65
  | .administrativeMessage _ => 70
  | .endOfDayControlMessage _ => 72
  | .lineVerificationControlMessage _ => 84

def encode : ControlMessageText → List UInt8
  | .startOfDayControlMessage message => StartOfDayControlMessage.encode message
  | .administrativeMessage message => AdministrativeMessage.encode message
  | .endOfDayControlMessage message => EndOfDayControlMessage.encode message
  | .lineVerificationControlMessage message => LineVerificationControlMessage.encode message

/-- Decoded from the whole of the frame: a message that reads to its end takes it all, any other must leave nothing -/
def decode (tag : BitVec 8) (bytes : List UInt8) : Option ControlMessageText :=
  if tag = 65 then (StartOfDayControlMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.startOfDayControlMessage message) else none
  else if tag = 70 then (AdministrativeMessage.decode bytes).map fun message => .administrativeMessage message
  else if tag = 72 then (EndOfDayControlMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.endOfDayControlMessage message) else none
  else if tag = 84 then (LineVerificationControlMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.lineVerificationControlMessage message) else none
  else none

theorem decode_encode (message : ControlMessageText) :
    decode (tag message) (encode message) = some message := by
  cases message with
  | startOfDayControlMessage message => simp [decode, encode, tag, StartOfDayControlMessage.decode_encode_nil]
  | administrativeMessage message => simp [decode, encode, tag, AdministrativeMessage.decode_encode]
  | endOfDayControlMessage message => simp [decode, encode, tag, EndOfDayControlMessage.decode_encode_nil]
  | lineVerificationControlMessage message => simp [decode, encode, tag, LineVerificationControlMessage.decode_encode_nil]

end ControlMessageText

/-- Control Message -/
structure ControlMessage where
  controlMessageText : ControlMessageText
  deriving DecidableEq, Repr

namespace ControlMessage

def encode (message : ControlMessage) : List UInt8 :=
  encodeUInt 1 (ControlMessageText.tag message.controlMessageText)
    ++ (ControlMessageText.encode message.controlMessageText)

def decode (bytes : List UInt8) : Option ControlMessage := do
  let (messageType, bytes) ← decodeUInt 1 bytes
  let controlMessageText ← ControlMessageText.decode messageType bytes
  pure { controlMessageText }

theorem encode_length_pos (message : ControlMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

theorem decode_encode (message : ControlMessage) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ControlMessageText.decode_encode, some_bind]
  rfl

end ControlMessage

/-- Trade Message: 147 bytes -/
structure TradeMessage where
  symbol : Alpha 15
  boardId : BoardId
  tradeNumber : Alpha 6
  buyOrderNumber : Alpha 8
  buyOrderDate : Alpha 8
  sellOrderNumber : Alpha 8
  sellOrderDate : Alpha 8
  price : Alpha 9
  volume : Alpha 17
  totalVolume : Alpha 17
  tradeType : TradeType
  tradeSource : TradeSource
  buyOrderType : BuyOrderType
  sellOrderType : SellOrderType
  buyWaiverIndicator : Alpha 4
  sellWaiverIndicator : Alpha 4
  notionalAmount : Alpha 14
  buyAlgoFlag : BuyAlgoFlag
  sellAlgoFlag : SellAlgoFlag
  sdivFlag : SdivFlag
  duplFlag : DuplFlag
  timeStamp : Alpha 20
  deriving DecidableEq, Repr

namespace TradeMessage

def encode (message : TradeMessage) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (BoardId.encode message.boardId
    ++ (Alpha.encode message.tradeNumber
    ++ (Alpha.encode message.buyOrderNumber
    ++ (Alpha.encode message.buyOrderDate
    ++ (Alpha.encode message.sellOrderNumber
    ++ (Alpha.encode message.sellOrderDate
    ++ (Alpha.encode message.price
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.totalVolume
    ++ (TradeType.encode message.tradeType
    ++ (TradeSource.encode message.tradeSource
    ++ (BuyOrderType.encode message.buyOrderType
    ++ (SellOrderType.encode message.sellOrderType
    ++ (Alpha.encode message.buyWaiverIndicator
    ++ (Alpha.encode message.sellWaiverIndicator
    ++ (Alpha.encode message.notionalAmount
    ++ (BuyAlgoFlag.encode message.buyAlgoFlag
    ++ (SellAlgoFlag.encode message.sellAlgoFlag
    ++ (SdivFlag.encode message.sdivFlag
    ++ (DuplFlag.encode message.duplFlag
    ++ (Alpha.encode message.timeStamp)))))))))))))))))))))

def decode (bytes : List UInt8) : Option (TradeMessage × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 15 bytes
  let (boardId, bytes) ← BoardId.decode bytes
  let (tradeNumber, bytes) ← Alpha.decode 6 bytes
  let (buyOrderNumber, bytes) ← Alpha.decode 8 bytes
  let (buyOrderDate, bytes) ← Alpha.decode 8 bytes
  let (sellOrderNumber, bytes) ← Alpha.decode 8 bytes
  let (sellOrderDate, bytes) ← Alpha.decode 8 bytes
  let (price, bytes) ← Alpha.decode 9 bytes
  let (volume, bytes) ← Alpha.decode 17 bytes
  let (totalVolume, bytes) ← Alpha.decode 17 bytes
  let (tradeType, bytes) ← TradeType.decode bytes
  let (tradeSource, bytes) ← TradeSource.decode bytes
  let (buyOrderType, bytes) ← BuyOrderType.decode bytes
  let (sellOrderType, bytes) ← SellOrderType.decode bytes
  let (buyWaiverIndicator, bytes) ← Alpha.decode 4 bytes
  let (sellWaiverIndicator, bytes) ← Alpha.decode 4 bytes
  let (notionalAmount, bytes) ← Alpha.decode 14 bytes
  let (buyAlgoFlag, bytes) ← BuyAlgoFlag.decode bytes
  let (sellAlgoFlag, bytes) ← SellAlgoFlag.decode bytes
  let (sdivFlag, bytes) ← SdivFlag.decode bytes
  let (duplFlag, bytes) ← DuplFlag.decode bytes
  let (timeStamp, bytes) ← Alpha.decode 20 bytes
  pure ({ symbol, boardId, tradeNumber, buyOrderNumber, buyOrderDate, sellOrderNumber, sellOrderDate, price, volume, totalVolume, tradeType, tradeSource, buyOrderType, sellOrderType, buyWaiverIndicator, sellWaiverIndicator, notionalAmount, buyAlgoFlag, sellAlgoFlag, sdivFlag, duplFlag, timeStamp }, bytes)

@[simp] theorem encode_length (message : TradeMessage) : (encode message).length = 147 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, BoardId.encode_length, TradeType.encode_length, TradeSource.encode_length, BuyOrderType.encode_length, SellOrderType.encode_length, BuyAlgoFlag.encode_length, SellAlgoFlag.encode_length, SdivFlag.encode_length, DuplFlag.encode_length]

theorem encode_length_pos (message : TradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BoardId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeSource.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BuyOrderType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SellOrderType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BuyAlgoFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SellAlgoFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SdivFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DuplFlag.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : TradeMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end TradeMessage

/-- Quote Level: 66 bytes -/
structure QuoteLevel where
  bidPrice : Alpha 9
  bidSize : Alpha 17
  bidOrders : Alpha 7
  askPrice : Alpha 9
  askSize : Alpha 17
  askOrders : Alpha 7
  deriving DecidableEq, Repr

namespace QuoteLevel

def encode (message : QuoteLevel) : List UInt8 :=
  Alpha.encode message.bidPrice
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.bidOrders
    ++ (Alpha.encode message.askPrice
    ++ (Alpha.encode message.askSize
    ++ (Alpha.encode message.askOrders)))))

def decode (bytes : List UInt8) : Option (QuoteLevel × List UInt8) := do
  let (bidPrice, bytes) ← Alpha.decode 9 bytes
  let (bidSize, bytes) ← Alpha.decode 17 bytes
  let (bidOrders, bytes) ← Alpha.decode 7 bytes
  let (askPrice, bytes) ← Alpha.decode 9 bytes
  let (askSize, bytes) ← Alpha.decode 17 bytes
  let (askOrders, bytes) ← Alpha.decode 7 bytes
  pure ({ bidPrice, bidSize, bidOrders, askPrice, askSize, askOrders }, bytes)

@[simp] theorem encode_length (message : QuoteLevel) : (encode message).length = 66 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : QuoteLevel) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteLevel) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end QuoteLevel

/-- Quote Message -/
structure QuoteMessage where
  symbol : Alpha 15
  quoteLevel : Digited 3 QuoteLevel
  deriving DecidableEq, Repr

namespace QuoteMessage

def encode (message : QuoteMessage) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (encodeDigits 3 message.quoteLevel.val.length
    ++ (encodeMany QuoteLevel.encode message.quoteLevel.val))

def decode (bytes : List UInt8) : Option (QuoteMessage × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 15 bytes
  let (quoteLevels, bytes) ← decodeDigits 3 bytes
  let (quoteLevel_, bytes) ← decodeMany QuoteLevel.decode quoteLevels bytes
  if fits_quoteLevel : quoteLevel_.length < 10 ^ 3 then
    pure ({ symbol, quoteLevel := ⟨quoteLevel_, fits_quoteLevel⟩ }, bytes)
  else none

theorem encode_length_pos (message : QuoteMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : QuoteMessage) : (encode message).length ≤ 65952 := by
  have bound_quoteLevel := message.quoteLevel.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeDigits_length, encodeMany_length_const QuoteLevel.encode 66 QuoteLevel.encode_length]
  omega

@[simp] theorem decode_encode (message : QuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.quoteLevel.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany QuoteLevel.encode QuoteLevel.decode QuoteLevel.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.quoteLevel.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : QuoteMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end QuoteMessage

/-- Index Message: 24 bytes -/
structure IndexMessage where
  symbol : Alpha 15
  indexPrice : Alpha 9
  deriving DecidableEq, Repr

namespace IndexMessage

def encode (message : IndexMessage) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (Alpha.encode message.indexPrice)

def decode (bytes : List UInt8) : Option (IndexMessage × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 15 bytes
  let (indexPrice, bytes) ← Alpha.decode 9 bytes
  pure ({ symbol, indexPrice }, bytes)

@[simp] theorem encode_length (message : IndexMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : IndexMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IndexMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : IndexMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end IndexMessage

/-- Instrument Summary Message: 103 bytes -/
structure InstrumentSummaryMessage where
  symbol : Alpha 15
  openingPrice : Alpha 9
  high : Alpha 9
  low : Alpha 9
  last : Alpha 9
  closingPrice : Alpha 9
  startOfDayPrice : Alpha 9
  totalVolume : Alpha 17
  totalValue : Alpha 17
  deriving DecidableEq, Repr

namespace InstrumentSummaryMessage

def encode (message : InstrumentSummaryMessage) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (Alpha.encode message.openingPrice
    ++ (Alpha.encode message.high
    ++ (Alpha.encode message.low
    ++ (Alpha.encode message.last
    ++ (Alpha.encode message.closingPrice
    ++ (Alpha.encode message.startOfDayPrice
    ++ (Alpha.encode message.totalVolume
    ++ (Alpha.encode message.totalValue))))))))

def decode (bytes : List UInt8) : Option (InstrumentSummaryMessage × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 15 bytes
  let (openingPrice, bytes) ← Alpha.decode 9 bytes
  let (high, bytes) ← Alpha.decode 9 bytes
  let (low, bytes) ← Alpha.decode 9 bytes
  let (last, bytes) ← Alpha.decode 9 bytes
  let (closingPrice, bytes) ← Alpha.decode 9 bytes
  let (startOfDayPrice, bytes) ← Alpha.decode 9 bytes
  let (totalVolume, bytes) ← Alpha.decode 17 bytes
  let (totalValue, bytes) ← Alpha.decode 17 bytes
  pure ({ symbol, openingPrice, high, low, last, closingPrice, startOfDayPrice, totalVolume, totalValue }, bytes)

@[simp] theorem encode_length (message : InstrumentSummaryMessage) : (encode message).length = 103 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : InstrumentSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentSummaryMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : InstrumentSummaryMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end InstrumentSummaryMessage

/-- Cancelled Trade Message: 147 bytes -/
structure CancelledTradeMessage where
  symbol : Alpha 15
  boardId : BoardId
  tradeNumber : Alpha 6
  buyOrderNumber : Alpha 8
  buyOrderDate : Alpha 8
  sellOrderNumber : Alpha 8
  sellOrderDate : Alpha 8
  cancelledTradePrice : Alpha 9
  cancelledVolume : Alpha 17
  totalVolume : Alpha 17
  tradeType : TradeType
  tradeSource : TradeSource
  buyOrderType : BuyOrderType
  sellOrderType : SellOrderType
  buyWaiverIndicator : Alpha 4
  sellWaiverIndicator : Alpha 4
  notionalAmount : Alpha 14
  buyAlgoFlag : BuyAlgoFlag
  sellAlgoFlag : SellAlgoFlag
  sdivFlag : SdivFlag
  duplFlag : DuplFlag
  timeStamp : Alpha 20
  deriving DecidableEq, Repr

namespace CancelledTradeMessage

def encode (message : CancelledTradeMessage) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (BoardId.encode message.boardId
    ++ (Alpha.encode message.tradeNumber
    ++ (Alpha.encode message.buyOrderNumber
    ++ (Alpha.encode message.buyOrderDate
    ++ (Alpha.encode message.sellOrderNumber
    ++ (Alpha.encode message.sellOrderDate
    ++ (Alpha.encode message.cancelledTradePrice
    ++ (Alpha.encode message.cancelledVolume
    ++ (Alpha.encode message.totalVolume
    ++ (TradeType.encode message.tradeType
    ++ (TradeSource.encode message.tradeSource
    ++ (BuyOrderType.encode message.buyOrderType
    ++ (SellOrderType.encode message.sellOrderType
    ++ (Alpha.encode message.buyWaiverIndicator
    ++ (Alpha.encode message.sellWaiverIndicator
    ++ (Alpha.encode message.notionalAmount
    ++ (BuyAlgoFlag.encode message.buyAlgoFlag
    ++ (SellAlgoFlag.encode message.sellAlgoFlag
    ++ (SdivFlag.encode message.sdivFlag
    ++ (DuplFlag.encode message.duplFlag
    ++ (Alpha.encode message.timeStamp)))))))))))))))))))))

def decode (bytes : List UInt8) : Option (CancelledTradeMessage × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 15 bytes
  let (boardId, bytes) ← BoardId.decode bytes
  let (tradeNumber, bytes) ← Alpha.decode 6 bytes
  let (buyOrderNumber, bytes) ← Alpha.decode 8 bytes
  let (buyOrderDate, bytes) ← Alpha.decode 8 bytes
  let (sellOrderNumber, bytes) ← Alpha.decode 8 bytes
  let (sellOrderDate, bytes) ← Alpha.decode 8 bytes
  let (cancelledTradePrice, bytes) ← Alpha.decode 9 bytes
  let (cancelledVolume, bytes) ← Alpha.decode 17 bytes
  let (totalVolume, bytes) ← Alpha.decode 17 bytes
  let (tradeType, bytes) ← TradeType.decode bytes
  let (tradeSource, bytes) ← TradeSource.decode bytes
  let (buyOrderType, bytes) ← BuyOrderType.decode bytes
  let (sellOrderType, bytes) ← SellOrderType.decode bytes
  let (buyWaiverIndicator, bytes) ← Alpha.decode 4 bytes
  let (sellWaiverIndicator, bytes) ← Alpha.decode 4 bytes
  let (notionalAmount, bytes) ← Alpha.decode 14 bytes
  let (buyAlgoFlag, bytes) ← BuyAlgoFlag.decode bytes
  let (sellAlgoFlag, bytes) ← SellAlgoFlag.decode bytes
  let (sdivFlag, bytes) ← SdivFlag.decode bytes
  let (duplFlag, bytes) ← DuplFlag.decode bytes
  let (timeStamp, bytes) ← Alpha.decode 20 bytes
  pure ({ symbol, boardId, tradeNumber, buyOrderNumber, buyOrderDate, sellOrderNumber, sellOrderDate, cancelledTradePrice, cancelledVolume, totalVolume, tradeType, tradeSource, buyOrderType, sellOrderType, buyWaiverIndicator, sellWaiverIndicator, notionalAmount, buyAlgoFlag, sellAlgoFlag, sdivFlag, duplFlag, timeStamp }, bytes)

@[simp] theorem encode_length (message : CancelledTradeMessage) : (encode message).length = 147 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, BoardId.encode_length, TradeType.encode_length, TradeSource.encode_length, BuyOrderType.encode_length, SellOrderType.encode_length, BuyAlgoFlag.encode_length, SellAlgoFlag.encode_length, SdivFlag.encode_length, DuplFlag.encode_length]

theorem encode_length_pos (message : CancelledTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CancelledTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BoardId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeSource.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BuyOrderType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SellOrderType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BuyAlgoFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SellAlgoFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SdivFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DuplFlag.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : CancelledTradeMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end CancelledTradeMessage

/-- Closing Price Message: 32 bytes -/
structure ClosingPriceMessage where
  symbol : Alpha 15
  closing : Alpha 9
  openInterest : Alpha 8
  deriving DecidableEq, Repr

namespace ClosingPriceMessage

def encode (message : ClosingPriceMessage) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (Alpha.encode message.closing
    ++ (Alpha.encode message.openInterest))

def decode (bytes : List UInt8) : Option (ClosingPriceMessage × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 15 bytes
  let (closing, bytes) ← Alpha.decode 9 bytes
  let (openInterest, bytes) ← Alpha.decode 8 bytes
  pure ({ symbol, closing, openInterest }, bytes)

@[simp] theorem encode_length (message : ClosingPriceMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : ClosingPriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ClosingPriceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ClosingPriceMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ClosingPriceMessage

/-- Projected Auction Auction Open Projected Close Price Message: 62 bytes -/
structure ProjectedAuctionAuctionOpenProjectedClosePriceMessage where
  symbol : Alpha 15
  priceFlag : PriceFlag
  price : Alpha 9
  volume : Alpha 17
  timeStamp : Alpha 20
  deriving DecidableEq, Repr

namespace ProjectedAuctionAuctionOpenProjectedClosePriceMessage

def encode (message : ProjectedAuctionAuctionOpenProjectedClosePriceMessage) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (PriceFlag.encode message.priceFlag
    ++ (Alpha.encode message.price
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.timeStamp))))

def decode (bytes : List UInt8) : Option (ProjectedAuctionAuctionOpenProjectedClosePriceMessage × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 15 bytes
  let (priceFlag, bytes) ← PriceFlag.decode bytes
  let (price, bytes) ← Alpha.decode 9 bytes
  let (volume, bytes) ← Alpha.decode 17 bytes
  let (timeStamp, bytes) ← Alpha.decode 20 bytes
  pure ({ symbol, priceFlag, price, volume, timeStamp }, bytes)

@[simp] theorem encode_length (message : ProjectedAuctionAuctionOpenProjectedClosePriceMessage) : (encode message).length = 62 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, PriceFlag.encode_length]

theorem encode_length_pos (message : ProjectedAuctionAuctionOpenProjectedClosePriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ProjectedAuctionAuctionOpenProjectedClosePriceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PriceFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ProjectedAuctionAuctionOpenProjectedClosePriceMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ProjectedAuctionAuctionOpenProjectedClosePriceMessage

/-- High Low Limit Modification Message: 56 bytes -/
structure HighLowLimitModificationMessage where
  symbol : Alpha 15
  ceilingPrice : Alpha 9
  floorPrice : Alpha 9
  startOfDayPrice : Alpha 9
  accruedInterest : Alpha 14
  deriving DecidableEq, Repr

namespace HighLowLimitModificationMessage

def encode (message : HighLowLimitModificationMessage) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (Alpha.encode message.ceilingPrice
    ++ (Alpha.encode message.floorPrice
    ++ (Alpha.encode message.startOfDayPrice
    ++ (Alpha.encode message.accruedInterest))))

def decode (bytes : List UInt8) : Option (HighLowLimitModificationMessage × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 15 bytes
  let (ceilingPrice, bytes) ← Alpha.decode 9 bytes
  let (floorPrice, bytes) ← Alpha.decode 9 bytes
  let (startOfDayPrice, bytes) ← Alpha.decode 9 bytes
  let (accruedInterest, bytes) ← Alpha.decode 14 bytes
  pure ({ symbol, ceilingPrice, floorPrice, startOfDayPrice, accruedInterest }, bytes)

@[simp] theorem encode_length (message : HighLowLimitModificationMessage) : (encode message).length = 56 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : HighLowLimitModificationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : HighLowLimitModificationMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : HighLowLimitModificationMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end HighLowLimitModificationMessage

/-- Instrument State Message: 38 bytes -/
structure InstrumentStateMessage where
  symbol : Alpha 15
  phaseId : PhaseId
  instrumentStatus : InstrumentStatus
  haltSuspendReason : HaltSuspendReason
  timeStamp : Alpha 20
  deriving DecidableEq, Repr

namespace InstrumentStateMessage

def encode (message : InstrumentStateMessage) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (PhaseId.encode message.phaseId
    ++ (InstrumentStatus.encode message.instrumentStatus
    ++ (HaltSuspendReason.encode message.haltSuspendReason
    ++ (Alpha.encode message.timeStamp))))

def decode (bytes : List UInt8) : Option (InstrumentStateMessage × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 15 bytes
  let (phaseId, bytes) ← PhaseId.decode bytes
  let (instrumentStatus, bytes) ← InstrumentStatus.decode bytes
  let (haltSuspendReason, bytes) ← HaltSuspendReason.decode bytes
  let (timeStamp, bytes) ← Alpha.decode 20 bytes
  pure ({ symbol, phaseId, instrumentStatus, haltSuspendReason, timeStamp }, bytes)

@[simp] theorem encode_length (message : InstrumentStateMessage) : (encode message).length = 38 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, PhaseId.encode_length, InstrumentStatus.encode_length, HaltSuspendReason.encode_length]

theorem encode_length_pos (message : InstrumentStateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentStateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PhaseId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, HaltSuspendReason.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : InstrumentStateMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end InstrumentStateMessage

/-- Market Status Message: 2 bytes -/
structure MarketStatusMessage where
  marketId : Alpha 1
  marketStatus : MarketStatus
  deriving DecidableEq, Repr

namespace MarketStatusMessage

def encode (message : MarketStatusMessage) : List UInt8 :=
  Alpha.encode message.marketId
    ++ (MarketStatus.encode message.marketStatus)

def decode (bytes : List UInt8) : Option (MarketStatusMessage × List UInt8) := do
  let (marketId, bytes) ← Alpha.decode 1 bytes
  let (marketStatus, bytes) ← MarketStatus.decode bytes
  pure ({ marketId, marketStatus }, bytes)

@[simp] theorem encode_length (message : MarketStatusMessage) : (encode message).length = 2 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, MarketStatus.encode_length]

theorem encode_length_pos (message : MarketStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [MarketStatus.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : MarketStatusMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end MarketStatusMessage

/-- Order Message: 147 bytes -/
structure OrderMessage where
  symbol : Alpha 15
  boardId : BoardId
  orderNumber : Alpha 8
  orderEntryDate : Alpha 8
  orderStatus : Alpha 2
  side : Side
  volume : Alpha 17
  matchedVolume : Alpha 17
  price : Alpha 9
  originalPriceType : OriginalPriceType
  orderLifetime : OrderLifetime
  specialConditions : SpecialConditions
  conditionVolume : Alpha 17
  orderReleaseDate : Alpha 8
  orderReleaseTime : Alpha 12
  lastOrderUpdateDate : Alpha 8
  orderType : OrderType
  timeStamp : Alpha 20
  deriving DecidableEq, Repr

namespace OrderMessage

def encode (message : OrderMessage) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (BoardId.encode message.boardId
    ++ (Alpha.encode message.orderNumber
    ++ (Alpha.encode message.orderEntryDate
    ++ (Alpha.encode message.orderStatus
    ++ (Side.encode message.side
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.matchedVolume
    ++ (Alpha.encode message.price
    ++ (OriginalPriceType.encode message.originalPriceType
    ++ (OrderLifetime.encode message.orderLifetime
    ++ (SpecialConditions.encode message.specialConditions
    ++ (Alpha.encode message.conditionVolume
    ++ (Alpha.encode message.orderReleaseDate
    ++ (Alpha.encode message.orderReleaseTime
    ++ (Alpha.encode message.lastOrderUpdateDate
    ++ (OrderType.encode message.orderType
    ++ (Alpha.encode message.timeStamp)))))))))))))))))

def decode (bytes : List UInt8) : Option (OrderMessage × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 15 bytes
  let (boardId, bytes) ← BoardId.decode bytes
  let (orderNumber, bytes) ← Alpha.decode 8 bytes
  let (orderEntryDate, bytes) ← Alpha.decode 8 bytes
  let (orderStatus, bytes) ← Alpha.decode 2 bytes
  let (side, bytes) ← Side.decode bytes
  let (volume, bytes) ← Alpha.decode 17 bytes
  let (matchedVolume, bytes) ← Alpha.decode 17 bytes
  let (price, bytes) ← Alpha.decode 9 bytes
  let (originalPriceType, bytes) ← OriginalPriceType.decode bytes
  let (orderLifetime, bytes) ← OrderLifetime.decode bytes
  let (specialConditions, bytes) ← SpecialConditions.decode bytes
  let (conditionVolume, bytes) ← Alpha.decode 17 bytes
  let (orderReleaseDate, bytes) ← Alpha.decode 8 bytes
  let (orderReleaseTime, bytes) ← Alpha.decode 12 bytes
  let (lastOrderUpdateDate, bytes) ← Alpha.decode 8 bytes
  let (orderType, bytes) ← OrderType.decode bytes
  let (timeStamp, bytes) ← Alpha.decode 20 bytes
  pure ({ symbol, boardId, orderNumber, orderEntryDate, orderStatus, side, volume, matchedVolume, price, originalPriceType, orderLifetime, specialConditions, conditionVolume, orderReleaseDate, orderReleaseTime, lastOrderUpdateDate, orderType, timeStamp }, bytes)

@[simp] theorem encode_length (message : OrderMessage) : (encode message).length = 147 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, BoardId.encode_length, Side.encode_length, OriginalPriceType.encode_length, OrderLifetime.encode_length, SpecialConditions.encode_length, OrderType.encode_length]

theorem encode_length_pos (message : OrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BoardId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OriginalPriceType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderLifetime.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SpecialConditions.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderType.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : OrderMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end OrderMessage

/-- Cancelled Order Message: 117 bytes -/
structure CancelledOrderMessage where
  symbol : Alpha 15
  boardId : BoardId
  orderNumber : Alpha 8
  orderEntryDate : Alpha 8
  side : Side
  volume : Alpha 17
  matchedVolume : Alpha 17
  price : Alpha 9
  originalPriceType : OriginalPriceType
  orderLifetime : OrderLifetime
  specialConditions : SpecialConditions
  conditionVolume : Alpha 17
  orderType : OrderType
  timeStamp : Alpha 20
  deriving DecidableEq, Repr

namespace CancelledOrderMessage

def encode (message : CancelledOrderMessage) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (BoardId.encode message.boardId
    ++ (Alpha.encode message.orderNumber
    ++ (Alpha.encode message.orderEntryDate
    ++ (Side.encode message.side
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.matchedVolume
    ++ (Alpha.encode message.price
    ++ (OriginalPriceType.encode message.originalPriceType
    ++ (OrderLifetime.encode message.orderLifetime
    ++ (SpecialConditions.encode message.specialConditions
    ++ (Alpha.encode message.conditionVolume
    ++ (OrderType.encode message.orderType
    ++ (Alpha.encode message.timeStamp)))))))))))))

def decode (bytes : List UInt8) : Option (CancelledOrderMessage × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 15 bytes
  let (boardId, bytes) ← BoardId.decode bytes
  let (orderNumber, bytes) ← Alpha.decode 8 bytes
  let (orderEntryDate, bytes) ← Alpha.decode 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (volume, bytes) ← Alpha.decode 17 bytes
  let (matchedVolume, bytes) ← Alpha.decode 17 bytes
  let (price, bytes) ← Alpha.decode 9 bytes
  let (originalPriceType, bytes) ← OriginalPriceType.decode bytes
  let (orderLifetime, bytes) ← OrderLifetime.decode bytes
  let (specialConditions, bytes) ← SpecialConditions.decode bytes
  let (conditionVolume, bytes) ← Alpha.decode 17 bytes
  let (orderType, bytes) ← OrderType.decode bytes
  let (timeStamp, bytes) ← Alpha.decode 20 bytes
  pure ({ symbol, boardId, orderNumber, orderEntryDate, side, volume, matchedVolume, price, originalPriceType, orderLifetime, specialConditions, conditionVolume, orderType, timeStamp }, bytes)

@[simp] theorem encode_length (message : CancelledOrderMessage) : (encode message).length = 117 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, BoardId.encode_length, Side.encode_length, OriginalPriceType.encode_length, OrderLifetime.encode_length, SpecialConditions.encode_length, OrderType.encode_length]

theorem encode_length_pos (message : CancelledOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CancelledOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BoardId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OriginalPriceType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderLifetime.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SpecialConditions.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderType.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : CancelledOrderMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end CancelledOrderMessage

/-- Exchange Notifications Message -/
structure ExchangeNotificationsMessage where
  notificationHeadlineInEnglish : Alpha 72
  notificationHeadlineInLocal : Alpha 72
  englishNotificationText : Digited 5 UInt8
  localNotificationText : Digited 5 UInt8
  deriving DecidableEq, Repr

namespace ExchangeNotificationsMessage

def encode (message : ExchangeNotificationsMessage) : List UInt8 :=
  Alpha.encode message.notificationHeadlineInEnglish
    ++ (Alpha.encode message.notificationHeadlineInLocal
    ++ (encodeDigits 5 message.englishNotificationText.val.length
    ++ (encodeDigits 5 message.localNotificationText.val.length
    ++ (encodeMany Byte.encode message.englishNotificationText.val
    ++ (encodeMany Byte.encode message.localNotificationText.val)))))

def decode (bytes : List UInt8) : Option (ExchangeNotificationsMessage × List UInt8) := do
  let (notificationHeadlineInEnglish, bytes) ← Alpha.decode 72 bytes
  let (notificationHeadlineInLocal, bytes) ← Alpha.decode 72 bytes
  let (textSizeInEnglish, bytes) ← decodeDigits 5 bytes
  let (textSizeInLocal, bytes) ← decodeDigits 5 bytes
  let (englishNotificationText_, bytes) ← decodeMany Byte.decode textSizeInEnglish bytes
  let (localNotificationText_, bytes) ← decodeMany Byte.decode textSizeInLocal bytes
  if fits_englishNotificationText : englishNotificationText_.length < 10 ^ 5 then
    if fits_localNotificationText : localNotificationText_.length < 10 ^ 5 then
      pure ({ notificationHeadlineInEnglish, notificationHeadlineInLocal, englishNotificationText := ⟨englishNotificationText_, fits_englishNotificationText⟩, localNotificationText := ⟨localNotificationText_, fits_localNotificationText⟩ }, bytes)
    else none
  else none

theorem encode_length_pos (message : ExchangeNotificationsMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ExchangeNotificationsMessage) : (encode message).length ≤ 200152 := by
  have bound_englishNotificationText := message.englishNotificationText.length_lt
  have bound_localNotificationText := message.localNotificationText.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeDigits_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

@[simp] theorem decode_encode (message : ExchangeNotificationsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.englishNotificationText.length_lt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.localNotificationText.length_lt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeMany_encodeMany Byte.encode Byte.decode Byte.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_encodeMany Byte.encode Byte.decode Byte.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.englishNotificationText.length_lt, dite_eq_left message.localNotificationText.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ExchangeNotificationsMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ExchangeNotificationsMessage

/-- Any Message Text, selected by Message Category -/
inductive MessageText where
  | controlMessage (message : ControlMessage) -- "K" 0x4B
  | tradeMessage (message : TradeMessage) -- "A" 0x41
  | quoteMessage (message : QuoteMessage) -- "B" 0x42
  | indexMessage (message : IndexMessage) -- "C" 0x43
  | instrumentSummaryMessage (message : InstrumentSummaryMessage) -- "G" 0x47
  | cancelledTradeMessage (message : CancelledTradeMessage) -- "I" 0x49
  | closingPriceMessage (message : ClosingPriceMessage) -- "L" 0x4C
  | projectedAuctionAuctionOpenProjectedClosePriceMessage (message : ProjectedAuctionAuctionOpenProjectedClosePriceMessage) -- "M" 0x4D
  | highLowLimitModificationMessage (message : HighLowLimitModificationMessage) -- "N" 0x4E
  | instrumentStateMessage (message : InstrumentStateMessage) -- "O" 0x4F
  | marketStatusMessage (message : MarketStatusMessage) -- "P" 0x50
  | orderMessage (message : OrderMessage) -- "Q" 0x51
  | cancelledOrderMessage (message : CancelledOrderMessage) -- "R" 0x52
  | exchangeNotificationsMessage (message : ExchangeNotificationsMessage) -- "S" 0x53
  deriving DecidableEq, Repr

namespace MessageText

/-- The Message Category each message is sent under -/
def tag : MessageText → BitVec 8
  | .controlMessage _ => 75
  | .tradeMessage _ => 65
  | .quoteMessage _ => 66
  | .indexMessage _ => 67
  | .instrumentSummaryMessage _ => 71
  | .cancelledTradeMessage _ => 73
  | .closingPriceMessage _ => 76
  | .projectedAuctionAuctionOpenProjectedClosePriceMessage _ => 77
  | .highLowLimitModificationMessage _ => 78
  | .instrumentStateMessage _ => 79
  | .marketStatusMessage _ => 80
  | .orderMessage _ => 81
  | .cancelledOrderMessage _ => 82
  | .exchangeNotificationsMessage _ => 83

def encode : MessageText → List UInt8
  | .controlMessage message => ControlMessage.encode message
  | .tradeMessage message => TradeMessage.encode message
  | .quoteMessage message => QuoteMessage.encode message
  | .indexMessage message => IndexMessage.encode message
  | .instrumentSummaryMessage message => InstrumentSummaryMessage.encode message
  | .cancelledTradeMessage message => CancelledTradeMessage.encode message
  | .closingPriceMessage message => ClosingPriceMessage.encode message
  | .projectedAuctionAuctionOpenProjectedClosePriceMessage message => ProjectedAuctionAuctionOpenProjectedClosePriceMessage.encode message
  | .highLowLimitModificationMessage message => HighLowLimitModificationMessage.encode message
  | .instrumentStateMessage message => InstrumentStateMessage.encode message
  | .marketStatusMessage message => MarketStatusMessage.encode message
  | .orderMessage message => OrderMessage.encode message
  | .cancelledOrderMessage message => CancelledOrderMessage.encode message
  | .exchangeNotificationsMessage message => ExchangeNotificationsMessage.encode message

/-- Decoded from the whole of the frame: a message that reads to its end takes it all, any other must leave nothing -/
def decode (tag : BitVec 8) (bytes : List UInt8) : Option MessageText :=
  if tag = 75 then (ControlMessage.decode bytes).map fun message => .controlMessage message
  else if tag = 65 then (TradeMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tradeMessage message) else none
  else if tag = 66 then (QuoteMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.quoteMessage message) else none
  else if tag = 67 then (IndexMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.indexMessage message) else none
  else if tag = 71 then (InstrumentSummaryMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.instrumentSummaryMessage message) else none
  else if tag = 73 then (CancelledTradeMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.cancelledTradeMessage message) else none
  else if tag = 76 then (ClosingPriceMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.closingPriceMessage message) else none
  else if tag = 77 then (ProjectedAuctionAuctionOpenProjectedClosePriceMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.projectedAuctionAuctionOpenProjectedClosePriceMessage message) else none
  else if tag = 78 then (HighLowLimitModificationMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.highLowLimitModificationMessage message) else none
  else if tag = 79 then (InstrumentStateMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.instrumentStateMessage message) else none
  else if tag = 80 then (MarketStatusMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.marketStatusMessage message) else none
  else if tag = 81 then (OrderMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderMessage message) else none
  else if tag = 82 then (CancelledOrderMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.cancelledOrderMessage message) else none
  else if tag = 83 then (ExchangeNotificationsMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.exchangeNotificationsMessage message) else none
  else none

theorem decode_encode (message : MessageText) :
    decode (tag message) (encode message) = some message := by
  cases message with
  | controlMessage message => simp [decode, encode, tag, ControlMessage.decode_encode]
  | tradeMessage message => simp [decode, encode, tag, TradeMessage.decode_encode_nil]
  | quoteMessage message => simp [decode, encode, tag, QuoteMessage.decode_encode_nil]
  | indexMessage message => simp [decode, encode, tag, IndexMessage.decode_encode_nil]
  | instrumentSummaryMessage message => simp [decode, encode, tag, InstrumentSummaryMessage.decode_encode_nil]
  | cancelledTradeMessage message => simp [decode, encode, tag, CancelledTradeMessage.decode_encode_nil]
  | closingPriceMessage message => simp [decode, encode, tag, ClosingPriceMessage.decode_encode_nil]
  | projectedAuctionAuctionOpenProjectedClosePriceMessage message => simp [decode, encode, tag, ProjectedAuctionAuctionOpenProjectedClosePriceMessage.decode_encode_nil]
  | highLowLimitModificationMessage message => simp [decode, encode, tag, HighLowLimitModificationMessage.decode_encode_nil]
  | instrumentStateMessage message => simp [decode, encode, tag, InstrumentStateMessage.decode_encode_nil]
  | marketStatusMessage message => simp [decode, encode, tag, MarketStatusMessage.decode_encode_nil]
  | orderMessage message => simp [decode, encode, tag, OrderMessage.decode_encode_nil]
  | cancelledOrderMessage message => simp [decode, encode, tag, CancelledOrderMessage.decode_encode_nil]
  | exchangeNotificationsMessage message => simp [decode, encode, tag, ExchangeNotificationsMessage.decode_encode_nil]

end MessageText

/-- Packet -/
structure Packet where
  soh : BitVec 8
  vendorIdentifier : Alpha 2
  messageSubcategory : MessageSubcategory
  venueId : Alpha 4
  messageSequenceNumber : Alpha 7
  publicationTimestamp : Alpha 20
  messageText : MessageText
  etx : BitVec 8
  lrc : BitVec 8
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUInt 1 message.soh
    ++ (Alpha.encode message.vendorIdentifier
    ++ (encodeUInt 1 (MessageText.tag message.messageText)
    ++ (MessageSubcategory.encode message.messageSubcategory
    ++ (Alpha.encode message.venueId
    ++ (Alpha.encode message.messageSequenceNumber
    ++ (Alpha.encode message.publicationTimestamp
    ++ (MessageText.encode message.messageText
    ++ (encodeUInt 1 message.etx
    ++ (encodeUInt 1 message.lrc)))))))))

def decode (bytes : List UInt8) : Option Packet := do
  let (soh, bytes) ← decodeUInt 1 bytes
  let (vendorIdentifier, bytes) ← Alpha.decode 2 bytes
  let (messageCategory, bytes) ← decodeUInt 1 bytes
  let (messageSubcategory, bytes) ← MessageSubcategory.decode bytes
  let (venueId, bytes) ← Alpha.decode 4 bytes
  let (messageSequenceNumber, bytes) ← Alpha.decode 7 bytes
  let (publicationTimestamp, bytes) ← Alpha.decode 20 bytes
  let (bytes, trailing) ← splitTrailer 2 bytes
  let messageText ← MessageText.decode messageCategory bytes
  let bytes := trailing
  let (etx, bytes) ← decodeUInt 1 bytes
  let (lrc, _) ← decodeUInt 1 bytes
  pure { soh, vendorIdentifier, messageSubcategory, venueId, messageSequenceNumber, publicationTimestamp, messageText, etx, lrc }

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [MessageSubcategory.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  have trailing_length : (encodeUInt 1 message.etx ++ encodeUInt 1 message.lrc).length = 2 := by
    simp [List.length_append, encodeUInt_length]
  rw [splitTrailer_append 2 _ _ trailing_length, some_bind]
  dsimp only
  rw [MessageText.decode_encode, some_bind]
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end Packet

end Omi.AthexAthexderivativesRealtimeIdsV52
