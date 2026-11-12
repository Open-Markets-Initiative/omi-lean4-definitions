import Wire

/-!
# Nairobi Securities Exchange Nairobi Equities Real Time v1.22

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.

Note: Symbol Directory Flags is a bit field set, proven as its 1 byte integer rather than bit by bit

Note: Sub Book Flags is a bit field set, proven as its 1 byte integer rather than bit by bit

Note: Symbol Status Flags is a bit field set, proven as its 1 byte integer rather than bit by bit

Note: Add Order Flags is a bit field set, proven as its 1 byte integer rather than bit by bit

Note: Add Attributed Order Flags is a bit field set, proven as its 1 byte integer rather than bit by
bit

Note: Order Modified Flags is a bit field set, proven as its 1 byte integer rather than bit by bit

Note: Price Point Sub Book Flags is a bit field set, proven as its 1 byte integer rather than bit by
bit

Note: Update Price Point Flags is a bit field set, proven as its 1 byte integer rather than bit by
bit

License: MIT No Attribution
-/

namespace Omi.NairobiNairobiequitiesRealtimeMitchV122

/-- Event Code: one byte code -/
def EventCode.codes : List UInt8 :=
  [0x43, 0x4F]

inductive EventCode where
  | endOfDay -- End Of Day
  | startOfDay -- Start Of Day
  | unlisted (byte : { byte : UInt8 // byte ∉ EventCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventCode

def toByte : EventCode → UInt8
  | .endOfDay => 0x43
  | .startOfDay => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventCode :=
  if byte = 0x43 then .endOfDay
  else .startOfDay

def ofByte (byte : UInt8) : EventCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventCode) : ofByte value.toByte = value := by
  cases value with
  | endOfDay => decide
  | startOfDay => decide
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

/-- Symbol Status: one byte code -/
def SymbolStatus.codes : List UInt8 :=
  [0x48, 0x53, 0x61, 0x20]

inductive SymbolStatus where
  | halted -- Halted
  | suspended -- Suspended
  | inactive -- Inactive
  | active -- Active
  | unlisted (byte : { byte : UInt8 // byte ∉ SymbolStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SymbolStatus

def toByte : SymbolStatus → UInt8
  | .halted => 0x48
  | .suspended => 0x53
  | .inactive => 0x61
  | .active => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SymbolStatus :=
  if byte = 0x48 then .halted
  else if byte = 0x53 then .suspended
  else if byte = 0x61 then .inactive
  else .active

def ofByte (byte : UInt8) : SymbolStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SymbolStatus) : ofByte value.toByte = value := by
  cases value with
  | halted => decide
  | suspended => decide
  | inactive => decide
  | active => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SymbolStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SymbolStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SymbolStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SymbolStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SymbolStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SymbolStatus

/-- Option Type: one byte code -/
def OptionType.codes : List UInt8 :=
  [0x43, 0x50, 0x20]

inductive OptionType where
  | callOption -- Call Option
  | putOption -- Put Option
  | notAnOption -- Not An Option
  | unlisted (byte : { byte : UInt8 // byte ∉ OptionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OptionType

def toByte : OptionType → UInt8
  | .callOption => 0x43
  | .putOption => 0x50
  | .notAnOption => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OptionType :=
  if byte = 0x43 then .callOption
  else if byte = 0x50 then .putOption
  else .notAnOption

def ofByte (byte : UInt8) : OptionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OptionType) : ofByte value.toByte = value := by
  cases value with
  | callOption => decide
  | putOption => decide
  | notAnOption => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OptionType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OptionType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OptionType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OptionType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OptionType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OptionType

/-- Trading Status: one byte code -/
def TradingStatus.codes : List UInt8 :=
  [0x48, 0x54, 0x61, 0x62, 0x63, 0x64, 0x65, 0x6C, 0x6E, 0x70, 0x71, 0x72, 0x73, 0x74, 0x75, 0x76, 0x77, 0x78, 0x79, 0x7A, 0x6F, 0x30]

inductive TradingStatus where
  | halt -- Halt
  | regularTrading -- Regular Trading
  | openingAuctionCall -- Opening Auction Call
  | postClose -- Post Close
  | marketClose -- Market Close
  | closingAuctionCall -- Closing Auction Call
  | reOpeningAuctionCall -- Re Opening Auction Call
  | pause -- Pause
  | orderEntry -- Order Entry
  | auctionInitiation -- Auction Initiation
  | startOfAuctionCall -- Start Of Auction Call
  | endOfAuctionCall -- End Of Auction Call
  | startOfAonOrderEntry -- Start Of Aon Order Entry
  | endOfAonOrderEntry -- End Of Aon Order Entry
  | closingPriceCross -- Closing Price Cross
  | reservedForBackwardCompatibility -- Reserved For Backward Compatibility
  | noActiveSession -- No Active Session
  | endOfPostClose -- End Of Post Close
  | preTrading -- Pre Trading
  | closingPricePublication -- Closing Price Publication
  | intradayAuctionCall -- Intraday Auction Call
  | auctionExecution -- Auction Execution
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingStatus

def toByte : TradingStatus → UInt8
  | .halt => 0x48
  | .regularTrading => 0x54
  | .openingAuctionCall => 0x61
  | .postClose => 0x62
  | .marketClose => 0x63
  | .closingAuctionCall => 0x64
  | .reOpeningAuctionCall => 0x65
  | .pause => 0x6C
  | .orderEntry => 0x6E
  | .auctionInitiation => 0x70
  | .startOfAuctionCall => 0x71
  | .endOfAuctionCall => 0x72
  | .startOfAonOrderEntry => 0x73
  | .endOfAonOrderEntry => 0x74
  | .closingPriceCross => 0x75
  | .reservedForBackwardCompatibility => 0x76
  | .noActiveSession => 0x77
  | .endOfPostClose => 0x78
  | .preTrading => 0x79
  | .closingPricePublication => 0x7A
  | .intradayAuctionCall => 0x6F
  | .auctionExecution => 0x30
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingStatus :=
  if byte = 0x48 then .halt
  else if byte = 0x54 then .regularTrading
  else if byte = 0x61 then .openingAuctionCall
  else if byte = 0x62 then .postClose
  else if byte = 0x63 then .marketClose
  else if byte = 0x64 then .closingAuctionCall
  else if byte = 0x65 then .reOpeningAuctionCall
  else if byte = 0x6C then .pause
  else if byte = 0x6E then .orderEntry
  else if byte = 0x70 then .auctionInitiation
  else if byte = 0x71 then .startOfAuctionCall
  else if byte = 0x72 then .endOfAuctionCall
  else if byte = 0x73 then .startOfAonOrderEntry
  else if byte = 0x74 then .endOfAonOrderEntry
  else if byte = 0x75 then .closingPriceCross
  else if byte = 0x76 then .reservedForBackwardCompatibility
  else if byte = 0x77 then .noActiveSession
  else if byte = 0x78 then .endOfPostClose
  else if byte = 0x79 then .preTrading
  else if byte = 0x7A then .closingPricePublication
  else if byte = 0x6F then .intradayAuctionCall
  else .auctionExecution

def ofByte (byte : UInt8) : TradingStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingStatus) : ofByte value.toByte = value := by
  cases value with
  | halt => decide
  | regularTrading => decide
  | openingAuctionCall => decide
  | postClose => decide
  | marketClose => decide
  | closingAuctionCall => decide
  | reOpeningAuctionCall => decide
  | pause => decide
  | orderEntry => decide
  | auctionInitiation => decide
  | startOfAuctionCall => decide
  | endOfAuctionCall => decide
  | startOfAonOrderEntry => decide
  | endOfAonOrderEntry => decide
  | closingPriceCross => decide
  | reservedForBackwardCompatibility => decide
  | noActiveSession => decide
  | endOfPostClose => decide
  | preTrading => decide
  | closingPricePublication => decide
  | intradayAuctionCall => decide
  | auctionExecution => decide
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

/-- Side: one byte code -/
def Side.codes : List UInt8 :=
  [0x42, 0x53]

inductive Side where
  | buyOrder -- Buy Order
  | sellOrder -- Sell Order
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .buyOrder => 0x42
  | .sellOrder => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x42 then .buyOrder
  else .sellOrder

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | buyOrder => decide
  | sellOrder => decide
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

/-- Settlement Type: one byte code -/
def SettlementType.codes : List UInt8 :=
  [0x31, 0x32, 0x33, 0x34]

inductive SettlementType where
  | cashTPlus0 -- Cash T Plus 0
  | earlySettleTPlus1 -- Early Settle T Plus 1
  | tPlus2 -- T Plus 2
  | regularTPlus3 -- Regular T Plus 3
  | unlisted (byte : { byte : UInt8 // byte ∉ SettlementType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SettlementType

def toByte : SettlementType → UInt8
  | .cashTPlus0 => 0x31
  | .earlySettleTPlus1 => 0x32
  | .tPlus2 => 0x33
  | .regularTPlus3 => 0x34
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SettlementType :=
  if byte = 0x31 then .cashTPlus0
  else if byte = 0x32 then .earlySettleTPlus1
  else if byte = 0x33 then .tPlus2
  else .regularTPlus3

def ofByte (byte : UInt8) : SettlementType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SettlementType) : ofByte value.toByte = value := by
  cases value with
  | cashTPlus0 => decide
  | earlySettleTPlus1 => decide
  | tPlus2 => decide
  | regularTPlus3 => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SettlementType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SettlementType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SettlementType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SettlementType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SettlementType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SettlementType

/-- Book Type: one byte code -/
def BookType.codes : List UInt8 :=
  [0x30, 0x31]

inductive BookType where
  | mbpMboStatistics -- Mbp Mbo Statistics
  | topOfBook -- Top Of Book
  | unlisted (byte : { byte : UInt8 // byte ∉ BookType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BookType

def toByte : BookType → UInt8
  | .mbpMboStatistics => 0x30
  | .topOfBook => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BookType :=
  if byte = 0x30 then .mbpMboStatistics
  else .topOfBook

def ofByte (byte : UInt8) : BookType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BookType) : ofByte value.toByte = value := by
  cases value with
  | mbpMboStatistics => decide
  | topOfBook => decide
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

/-- Auction Type: one byte code -/
def AuctionType.codes : List UInt8 :=
  [0x41, 0x43, 0x4F, 0x4B, 0x20]

inductive AuctionType where
  | reOpeningAuction -- Re Opening Auction
  | closingAuction -- Closing Auction
  | openingAuction -- Opening Auction
  | intraDayAuction -- Intra Day Auction
  | notAnAuctionTrade -- Not An Auction Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ AuctionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AuctionType

def toByte : AuctionType → UInt8
  | .reOpeningAuction => 0x41
  | .closingAuction => 0x43
  | .openingAuction => 0x4F
  | .intraDayAuction => 0x4B
  | .notAnAuctionTrade => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AuctionType :=
  if byte = 0x41 then .reOpeningAuction
  else if byte = 0x43 then .closingAuction
  else if byte = 0x4F then .openingAuction
  else if byte = 0x4B then .intraDayAuction
  else .notAnAuctionTrade

def ofByte (byte : UInt8) : AuctionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AuctionType) : ofByte value.toByte = value := by
  cases value with
  | reOpeningAuction => decide
  | closingAuction => decide
  | openingAuction => decide
  | intraDayAuction => decide
  | notAnAuctionTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AuctionType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AuctionType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AuctionType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : AuctionType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : AuctionType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AuctionType

/-- Trade Type: one byte code -/
def TradeType.codes : List UInt8 :=
  [0x54, 0x4E]

inductive TradeType where
  | onBookTrade -- On Book Trade
  | offBookTrade -- Off Book Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeType

def toByte : TradeType → UInt8
  | .onBookTrade => 0x54
  | .offBookTrade => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeType :=
  if byte = 0x54 then .onBookTrade
  else .offBookTrade

def ofByte (byte : UInt8) : TradeType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeType) : ofByte value.toByte = value := by
  cases value with
  | onBookTrade => decide
  | offBookTrade => decide
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

/-- Action Type: one byte code -/
def ActionType.codes : List UInt8 :=
  [0x43, 0x4E, 0x41]

inductive ActionType where
  | cancelledTrade -- Cancelled Trade
  | trade -- Trade
  | amendTrade -- Amend Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ ActionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ActionType

def toByte : ActionType → UInt8
  | .cancelledTrade => 0x43
  | .trade => 0x4E
  | .amendTrade => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ActionType :=
  if byte = 0x43 then .cancelledTrade
  else if byte = 0x4E then .trade
  else .amendTrade

def ofByte (byte : UInt8) : ActionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ActionType) : ofByte value.toByte = value := by
  cases value with
  | cancelledTrade => decide
  | trade => decide
  | amendTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ActionType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ActionType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ActionType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ActionType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ActionType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ActionType

/-- Auction Trade Type: one byte code -/
def AuctionTradeType.codes : List UInt8 :=
  [0x42, 0x53]

inductive AuctionTradeType where
  | bulkTrade -- Bulk Trade
  | supplementaryTrade -- Supplementary Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ AuctionTradeType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AuctionTradeType

def toByte : AuctionTradeType → UInt8
  | .bulkTrade => 0x42
  | .supplementaryTrade => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AuctionTradeType :=
  if byte = 0x42 then .bulkTrade
  else .supplementaryTrade

def ofByte (byte : UInt8) : AuctionTradeType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AuctionTradeType) : ofByte value.toByte = value := by
  cases value with
  | bulkTrade => decide
  | supplementaryTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AuctionTradeType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AuctionTradeType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AuctionTradeType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : AuctionTradeType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : AuctionTradeType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AuctionTradeType

/-- Imbalance Direction: one byte code -/
def ImbalanceDirection.codes : List UInt8 :=
  [0x42, 0x4E, 0x4F, 0x53]

inductive ImbalanceDirection where
  | buyImbalance -- Buy Imbalance
  | noImbalance -- No Imbalance
  | insufficientOrdersForAuction -- Insufficient Orders For Auction
  | sellImbalance -- Sell Imbalance
  | unlisted (byte : { byte : UInt8 // byte ∉ ImbalanceDirection.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ImbalanceDirection

def toByte : ImbalanceDirection → UInt8
  | .buyImbalance => 0x42
  | .noImbalance => 0x4E
  | .insufficientOrdersForAuction => 0x4F
  | .sellImbalance => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ImbalanceDirection :=
  if byte = 0x42 then .buyImbalance
  else if byte = 0x4E then .noImbalance
  else if byte = 0x4F then .insufficientOrdersForAuction
  else .sellImbalance

def ofByte (byte : UInt8) : ImbalanceDirection :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ImbalanceDirection) : ofByte value.toByte = value := by
  cases value with
  | buyImbalance => decide
  | noImbalance => decide
  | insufficientOrdersForAuction => decide
  | sellImbalance => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ImbalanceDirection) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ImbalanceDirection × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ImbalanceDirection) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ImbalanceDirection) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ImbalanceDirection) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ImbalanceDirection

/-- Statistic Type: one byte code -/
def StatisticType.codes : List UInt8 :=
  [0x43, 0x4F, 0x50]

inductive StatisticType where
  | closingPrice -- Closing Price
  | openingPrice -- Opening Price
  | previousClose -- Previous Close
  | unlisted (byte : { byte : UInt8 // byte ∉ StatisticType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace StatisticType

def toByte : StatisticType → UInt8
  | .closingPrice => 0x43
  | .openingPrice => 0x4F
  | .previousClose => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : StatisticType :=
  if byte = 0x43 then .closingPrice
  else if byte = 0x4F then .openingPrice
  else .previousClose

def ofByte (byte : UInt8) : StatisticType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : StatisticType) : ofByte value.toByte = value := by
  cases value with
  | closingPrice => decide
  | openingPrice => decide
  | previousClose => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : StatisticType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (StatisticType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : StatisticType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : StatisticType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : StatisticType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end StatisticType

/-- Open Close Indicator: one byte code -/
def OpenCloseIndicator.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x48, 0x49, 0x54, 0x55, 0x56, 0x57, 0x58, 0x59, 0x5A]

inductive OpenCloseIndicator where
  | auctionTrade -- Auction Trade
  | regularTrade -- Regular Trade
  | midPoint -- Mid Point
  | lastRegularTrade -- Last Regular Trade
  | lastAuction -- Last Auction
  | manual -- Manual
  | vwap -- Vwap
  | previousClose -- Previous Close
  | theoreticalPrice -- Theoretical Price
  | bestBid -- Best Bid
  | bestOffer -- Best Offer
  | none_ -- None
  | vwapOfLastNTrades -- Vwap Of Last N Trades
  | referencePrice -- Reference Price
  | priceUnavailable -- Price Unavailable
  | unlisted (byte : { byte : UInt8 // byte ∉ OpenCloseIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OpenCloseIndicator

def toByte : OpenCloseIndicator → UInt8
  | .auctionTrade => 0x41
  | .regularTrade => 0x42
  | .midPoint => 0x43
  | .lastRegularTrade => 0x44
  | .lastAuction => 0x45
  | .manual => 0x46
  | .vwap => 0x48
  | .previousClose => 0x49
  | .theoreticalPrice => 0x54
  | .bestBid => 0x55
  | .bestOffer => 0x56
  | .none_ => 0x57
  | .vwapOfLastNTrades => 0x58
  | .referencePrice => 0x59
  | .priceUnavailable => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OpenCloseIndicator :=
  if byte = 0x41 then .auctionTrade
  else if byte = 0x42 then .regularTrade
  else if byte = 0x43 then .midPoint
  else if byte = 0x44 then .lastRegularTrade
  else if byte = 0x45 then .lastAuction
  else if byte = 0x46 then .manual
  else if byte = 0x48 then .vwap
  else if byte = 0x49 then .previousClose
  else if byte = 0x54 then .theoreticalPrice
  else if byte = 0x55 then .bestBid
  else if byte = 0x56 then .bestOffer
  else if byte = 0x57 then .none_
  else if byte = 0x58 then .vwapOfLastNTrades
  else if byte = 0x59 then .referencePrice
  else .priceUnavailable

def ofByte (byte : UInt8) : OpenCloseIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OpenCloseIndicator) : ofByte value.toByte = value := by
  cases value with
  | auctionTrade => decide
  | regularTrade => decide
  | midPoint => decide
  | lastRegularTrade => decide
  | lastAuction => decide
  | manual => decide
  | vwap => decide
  | previousClose => decide
  | theoreticalPrice => decide
  | bestBid => decide
  | bestOffer => decide
  | none_ => decide
  | vwapOfLastNTrades => decide
  | referencePrice => decide
  | priceUnavailable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OpenCloseIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OpenCloseIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OpenCloseIndicator) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OpenCloseIndicator) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OpenCloseIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OpenCloseIndicator

/-- Aon Status: one byte code -/
def AonStatus.codes : List UInt8 :=
  [0x41, 0x43, 0x48, 0x49, 0x58]

inductive AonStatus where
  | active -- Active
  | completed -- Completed
  | halted -- Halted
  | inactive -- Inactive
  | cancelled -- Cancelled
  | unlisted (byte : { byte : UInt8 // byte ∉ AonStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AonStatus

def toByte : AonStatus → UInt8
  | .active => 0x41
  | .completed => 0x43
  | .halted => 0x48
  | .inactive => 0x49
  | .cancelled => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AonStatus :=
  if byte = 0x41 then .active
  else if byte = 0x43 then .completed
  else if byte = 0x48 then .halted
  else if byte = 0x49 then .inactive
  else .cancelled

def ofByte (byte : UInt8) : AonStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AonStatus) : ofByte value.toByte = value := by
  cases value with
  | active => decide
  | completed => decide
  | halted => decide
  | inactive => decide
  | cancelled => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AonStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AonStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AonStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : AonStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : AonStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AonStatus

/-- Urgency: one byte code -/
def Urgency.codes : List UInt8 :=
  [0x30, 0x31, 0x32]

inductive Urgency where
  | regular -- Regular
  | highPriority -- High Priority
  | lowPriority -- Low Priority
  | unlisted (byte : { byte : UInt8 // byte ∉ Urgency.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Urgency

def toByte : Urgency → UInt8
  | .regular => 0x30
  | .highPriority => 0x31
  | .lowPriority => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Urgency :=
  if byte = 0x30 then .regular
  else if byte = 0x31 then .highPriority
  else .lowPriority

def ofByte (byte : UInt8) : Urgency :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Urgency) : ofByte value.toByte = value := by
  cases value with
  | regular => decide
  | highPriority => decide
  | lowPriority => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Urgency) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Urgency × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Urgency) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Urgency) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Urgency) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Urgency

/-- Price Point Action: one byte code -/
def PricePointAction.codes : List UInt8 :=
  [0x30, 0x31]

inductive PricePointAction where
  | add -- Add
  | change -- Change
  | unlisted (byte : { byte : UInt8 // byte ∉ PricePointAction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PricePointAction

def toByte : PricePointAction → UInt8
  | .add => 0x30
  | .change => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PricePointAction :=
  if byte = 0x30 then .add
  else .change

def ofByte (byte : UInt8) : PricePointAction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PricePointAction) : ofByte value.toByte = value := by
  cases value with
  | add => decide
  | change => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PricePointAction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PricePointAction × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PricePointAction) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : PricePointAction) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : PricePointAction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PricePointAction

/-- Top Of Book Action: one byte code -/
def TopOfBookAction.codes : List UInt8 :=
  [0x31, 0x32]

inductive TopOfBookAction where
  | update -- Update
  | delete -- Delete
  | unlisted (byte : { byte : UInt8 // byte ∉ TopOfBookAction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TopOfBookAction

def toByte : TopOfBookAction → UInt8
  | .update => 0x31
  | .delete => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TopOfBookAction :=
  if byte = 0x31 then .update
  else .delete

def ofByte (byte : UInt8) : TopOfBookAction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TopOfBookAction) : ofByte value.toByte = value := by
  cases value with
  | update => decide
  | delete => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TopOfBookAction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TopOfBookAction × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TopOfBookAction) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TopOfBookAction) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TopOfBookAction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TopOfBookAction

/-- Time Message: 4 bytes -/
structure TimeMessage where
  seconds : BitVec 32
  deriving DecidableEq, Repr

namespace TimeMessage

def encode (message : TimeMessage) : List UInt8 :=
  encodeUIntLE 4 message.seconds

def decode (bytes : List UInt8) : Option (TimeMessage × List UInt8) := do
  let (seconds, bytes) ← decodeUIntLE 4 bytes
  pure ({ seconds }, bytes)

@[simp] theorem encode_length (message : TimeMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : TimeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TimeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TimeMessage

/-- System Event Message: 5 bytes -/
structure SystemEventMessage where
  nanosecond : BitVec 32
  eventCode : EventCode
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanosecond
    ++ (EventCode.encode message.eventCode)

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (nanosecond, bytes) ← decodeUIntLE 4 bytes
  let (eventCode, bytes) ← EventCode.decode bytes
  pure ({ nanosecond, eventCode }, bytes)

@[simp] theorem encode_length (message : SystemEventMessage) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, EventCode.encode_length]

theorem encode_length_pos (message : SystemEventMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemEventMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [EventCode.decode_encode, some_bind]
  rfl

end SystemEventMessage

/-- Symbol Directory Message: 87 bytes -/
structure SymbolDirectoryMessage where
  nanosecond : BitVec 32
  symbol : Alpha 12
  symbolStatus : SymbolStatus
  identificationNumber : Alpha 12
  segment : Alpha 6
  expirationDate : Alpha 8
  underlying : Alpha 6
  strikePrice : BitVec 32
  optionType : OptionType
  issuer : Alpha 6
  issueDate : Alpha 8
  coupon : BitVec 32
  symbolDirectoryFlags : BitVec 8
  subBookFlags : BitVec 8
  corporateAction : Alpha 5
  issuedQuantity : BitVec 64
  deriving DecidableEq, Repr

namespace SymbolDirectoryMessage

def encode (message : SymbolDirectoryMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanosecond
    ++ (Alpha.encode message.symbol
    ++ (SymbolStatus.encode message.symbolStatus
    ++ (Alpha.encode message.identificationNumber
    ++ (Alpha.encode message.segment
    ++ (Alpha.encode message.expirationDate
    ++ (Alpha.encode message.underlying
    ++ (encodeUIntLE 4 message.strikePrice
    ++ (OptionType.encode message.optionType
    ++ (Alpha.encode message.issuer
    ++ (Alpha.encode message.issueDate
    ++ (encodeUIntLE 4 message.coupon
    ++ (encodeUIntLE 1 message.symbolDirectoryFlags
    ++ (encodeUIntLE 1 message.subBookFlags
    ++ (Alpha.encode message.corporateAction
    ++ (encodeUIntLE 8 message.issuedQuantity)))))))))))))))

def decode (bytes : List UInt8) : Option (SymbolDirectoryMessage × List UInt8) := do
  let (nanosecond, bytes) ← decodeUIntLE 4 bytes
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (symbolStatus, bytes) ← SymbolStatus.decode bytes
  let (identificationNumber, bytes) ← Alpha.decode 12 bytes
  let (segment, bytes) ← Alpha.decode 6 bytes
  let (expirationDate, bytes) ← Alpha.decode 8 bytes
  let (underlying, bytes) ← Alpha.decode 6 bytes
  let (strikePrice, bytes) ← decodeUIntLE 4 bytes
  let (optionType, bytes) ← OptionType.decode bytes
  let (issuer, bytes) ← Alpha.decode 6 bytes
  let (issueDate, bytes) ← Alpha.decode 8 bytes
  let (coupon, bytes) ← decodeUIntLE 4 bytes
  let (symbolDirectoryFlags, bytes) ← decodeUIntLE 1 bytes
  let (subBookFlags, bytes) ← decodeUIntLE 1 bytes
  let (corporateAction, bytes) ← Alpha.decode 5 bytes
  let (issuedQuantity, bytes) ← decodeUIntLE 8 bytes
  pure ({ nanosecond, symbol, symbolStatus, identificationNumber, segment, expirationDate, underlying, strikePrice, optionType, issuer, issueDate, coupon, symbolDirectoryFlags, subBookFlags, corporateAction, issuedQuantity }, bytes)

@[simp] theorem encode_length (message : SymbolDirectoryMessage) : (encode message).length = 87 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, SymbolStatus.encode_length, OptionType.encode_length]

theorem encode_length_pos (message : SymbolDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SymbolDirectoryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SymbolStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OptionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SymbolDirectoryMessage

/-- Symbol Status Message: 32 bytes -/
structure SymbolStatusMessage where
  nanosecond : BitVec 32
  symbol : Alpha 12
  tradingStatus : TradingStatus
  symbolStatusFlags : BitVec 8
  haltReason : Alpha 4
  sessionChangeReason : BitVec 8
  newEndTime : Alpha 8
  subBook : BitVec 8
  deriving DecidableEq, Repr

namespace SymbolStatusMessage

def encode (message : SymbolStatusMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanosecond
    ++ (Alpha.encode message.symbol
    ++ (TradingStatus.encode message.tradingStatus
    ++ (encodeUIntLE 1 message.symbolStatusFlags
    ++ (Alpha.encode message.haltReason
    ++ (encodeUIntLE 1 message.sessionChangeReason
    ++ (Alpha.encode message.newEndTime
    ++ (encodeUIntLE 1 message.subBook)))))))

def decode (bytes : List UInt8) : Option (SymbolStatusMessage × List UInt8) := do
  let (nanosecond, bytes) ← decodeUIntLE 4 bytes
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (tradingStatus, bytes) ← TradingStatus.decode bytes
  let (symbolStatusFlags, bytes) ← decodeUIntLE 1 bytes
  let (haltReason, bytes) ← Alpha.decode 4 bytes
  let (sessionChangeReason, bytes) ← decodeUIntLE 1 bytes
  let (newEndTime, bytes) ← Alpha.decode 8 bytes
  let (subBook, bytes) ← decodeUIntLE 1 bytes
  pure ({ nanosecond, symbol, tradingStatus, symbolStatusFlags, haltReason, sessionChangeReason, newEndTime, subBook }, bytes)

@[simp] theorem encode_length (message : SymbolStatusMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TradingStatus.encode_length]

theorem encode_length_pos (message : SymbolStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SymbolStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradingStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SymbolStatusMessage

/-- Add Order Message: 41 bytes -/
structure AddOrderMessage where
  nanosecond : BitVec 32
  orderId : BitVec 64
  side : Side
  quantity : BitVec 32
  symbol : Alpha 12
  price : BitVec 32
  addOrderFlags : BitVec 8
  subBook : BitVec 8
  settlementType : SettlementType
  interestRate : BitVec 32
  term : BitVec 8
  deriving DecidableEq, Repr

namespace AddOrderMessage

def encode (message : AddOrderMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanosecond
    ++ (encodeUIntLE 8 message.orderId
    ++ (Side.encode message.side
    ++ (encodeUIntLE 4 message.quantity
    ++ (Alpha.encode message.symbol
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 1 message.addOrderFlags
    ++ (encodeUIntLE 1 message.subBook
    ++ (SettlementType.encode message.settlementType
    ++ (encodeUIntLE 4 message.interestRate
    ++ (encodeUIntLE 1 message.term))))))))))

def decode (bytes : List UInt8) : Option (AddOrderMessage × List UInt8) := do
  let (nanosecond, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (addOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (subBook, bytes) ← decodeUIntLE 1 bytes
  let (settlementType, bytes) ← SettlementType.decode bytes
  let (interestRate, bytes) ← decodeUIntLE 4 bytes
  let (term, bytes) ← decodeUIntLE 1 bytes
  pure ({ nanosecond, orderId, side, quantity, symbol, price, addOrderFlags, subBook, settlementType, interestRate, term }, bytes)

@[simp] theorem encode_length (message : AddOrderMessage) : (encode message).length = 41 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Side.encode_length, Alpha.encode_length, SettlementType.encode_length]

theorem encode_length_pos (message : AddOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, SettlementType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end AddOrderMessage

/-- Add Attributed Order Message: 41 bytes -/
structure AddAttributedOrderMessage where
  nanosecond : BitVec 32
  orderId : BitVec 64
  side : Side
  quantity : BitVec 32
  symbol : Alpha 12
  price : BitVec 32
  attribution : Alpha 6
  addAttributedOrderFlags : BitVec 8
  subBook : BitVec 8
  deriving DecidableEq, Repr

namespace AddAttributedOrderMessage

def encode (message : AddAttributedOrderMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanosecond
    ++ (encodeUIntLE 8 message.orderId
    ++ (Side.encode message.side
    ++ (encodeUIntLE 4 message.quantity
    ++ (Alpha.encode message.symbol
    ++ (encodeUIntLE 4 message.price
    ++ (Alpha.encode message.attribution
    ++ (encodeUIntLE 1 message.addAttributedOrderFlags
    ++ (encodeUIntLE 1 message.subBook))))))))

def decode (bytes : List UInt8) : Option (AddAttributedOrderMessage × List UInt8) := do
  let (nanosecond, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (attribution, bytes) ← Alpha.decode 6 bytes
  let (addAttributedOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (subBook, bytes) ← decodeUIntLE 1 bytes
  pure ({ nanosecond, orderId, side, quantity, symbol, price, attribution, addAttributedOrderFlags, subBook }, bytes)

@[simp] theorem encode_length (message : AddAttributedOrderMessage) : (encode message).length = 41 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Side.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : AddAttributedOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddAttributedOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end AddAttributedOrderMessage

/-- Order Deleted Message: 12 bytes -/
structure OrderDeletedMessage where
  nanosecond : BitVec 32
  orderId : BitVec 64
  deriving DecidableEq, Repr

namespace OrderDeletedMessage

def encode (message : OrderDeletedMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanosecond
    ++ (encodeUIntLE 8 message.orderId)

def decode (bytes : List UInt8) : Option (OrderDeletedMessage × List UInt8) := do
  let (nanosecond, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  pure ({ nanosecond, orderId }, bytes)

@[simp] theorem encode_length (message : OrderDeletedMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderDeletedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderDeletedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderDeletedMessage

/-- Order Modified Message: 27 bytes -/
structure OrderModifiedMessage where
  nanosecond : BitVec 32
  orderId : BitVec 64
  newQuantity : BitVec 32
  newPrice : BitVec 32
  orderModifiedFlags : BitVec 8
  settlementType : SettlementType
  interestRate : BitVec 32
  term : BitVec 8
  deriving DecidableEq, Repr

namespace OrderModifiedMessage

def encode (message : OrderModifiedMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanosecond
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 4 message.newQuantity
    ++ (encodeUIntLE 4 message.newPrice
    ++ (encodeUIntLE 1 message.orderModifiedFlags
    ++ (SettlementType.encode message.settlementType
    ++ (encodeUIntLE 4 message.interestRate
    ++ (encodeUIntLE 1 message.term)))))))

def decode (bytes : List UInt8) : Option (OrderModifiedMessage × List UInt8) := do
  let (nanosecond, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (newQuantity, bytes) ← decodeUIntLE 4 bytes
  let (newPrice, bytes) ← decodeUIntLE 4 bytes
  let (orderModifiedFlags, bytes) ← decodeUIntLE 1 bytes
  let (settlementType, bytes) ← SettlementType.decode bytes
  let (interestRate, bytes) ← decodeUIntLE 4 bytes
  let (term, bytes) ← decodeUIntLE 1 bytes
  pure ({ nanosecond, orderId, newQuantity, newPrice, orderModifiedFlags, settlementType, interestRate, term }, bytes)

@[simp] theorem encode_length (message : OrderModifiedMessage) : (encode message).length = 27 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, SettlementType.encode_length]

theorem encode_length_pos (message : OrderModifiedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderModifiedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, SettlementType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderModifiedMessage

/-- Order Book Clear Message: 18 bytes -/
structure OrderBookClearMessage where
  nanosecond : BitVec 32
  symbol : Alpha 12
  subBook : BitVec 8
  bookType : BookType
  deriving DecidableEq, Repr

namespace OrderBookClearMessage

def encode (message : OrderBookClearMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanosecond
    ++ (Alpha.encode message.symbol
    ++ (encodeUIntLE 1 message.subBook
    ++ (BookType.encode message.bookType)))

def decode (bytes : List UInt8) : Option (OrderBookClearMessage × List UInt8) := do
  let (nanosecond, bytes) ← decodeUIntLE 4 bytes
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (subBook, bytes) ← decodeUIntLE 1 bytes
  let (bookType, bytes) ← BookType.decode bytes
  pure ({ nanosecond, symbol, subBook, bookType }, bytes)

@[simp] theorem encode_length (message : OrderBookClearMessage) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, BookType.encode_length]

theorem encode_length_pos (message : OrderBookClearMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderBookClearMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [BookType.decode_encode, some_bind]
  rfl

end OrderBookClearMessage

/-- Order Executed Message: 60 bytes -/
structure OrderExecutedMessage where
  nanosecond : BitVec 32
  orderId : BitVec 64
  executedQuantity : BitVec 32
  tradeId : BitVec 64
  buyFirm : Alpha 6
  sellFirm : Alpha 6
  lastOptPx : BitVec 64
  volatility : BitVec 64
  underlyingReferencePrice : BitVec 64
  deriving DecidableEq, Repr

namespace OrderExecutedMessage

def encode (message : OrderExecutedMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanosecond
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 4 message.executedQuantity
    ++ (encodeUIntLE 8 message.tradeId
    ++ (Alpha.encode message.buyFirm
    ++ (Alpha.encode message.sellFirm
    ++ (encodeUIntLE 8 message.lastOptPx
    ++ (encodeUIntLE 8 message.volatility
    ++ (encodeUIntLE 8 message.underlyingReferencePrice))))))))

def decode (bytes : List UInt8) : Option (OrderExecutedMessage × List UInt8) := do
  let (nanosecond, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (executedQuantity, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 8 bytes
  let (buyFirm, bytes) ← Alpha.decode 6 bytes
  let (sellFirm, bytes) ← Alpha.decode 6 bytes
  let (lastOptPx, bytes) ← decodeUIntLE 8 bytes
  let (volatility, bytes) ← decodeUIntLE 8 bytes
  let (underlyingReferencePrice, bytes) ← decodeUIntLE 8 bytes
  pure ({ nanosecond, orderId, executedQuantity, tradeId, buyFirm, sellFirm, lastOptPx, volatility, underlyingReferencePrice }, bytes)

@[simp] theorem encode_length (message : OrderExecutedMessage) : (encode message).length = 60 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderExecutedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderExecutedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderExecutedMessage

/-- Order Executed With Price Size Message: 69 bytes -/
structure OrderExecutedWithPriceSizeMessage where
  nanosecond : BitVec 32
  orderId : BitVec 64
  executedQuantity : BitVec 32
  displayQuantity : BitVec 32
  tradeId : BitVec 64
  printable : Printable
  price : BitVec 32
  buyFirm : Alpha 6
  sellFirm : Alpha 6
  lastOptPx : BitVec 64
  volatility : BitVec 64
  underlyingReferencePrice : BitVec 64
  deriving DecidableEq, Repr

namespace OrderExecutedWithPriceSizeMessage

def encode (message : OrderExecutedWithPriceSizeMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanosecond
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 4 message.executedQuantity
    ++ (encodeUIntLE 4 message.displayQuantity
    ++ (encodeUIntLE 8 message.tradeId
    ++ (Printable.encode message.printable
    ++ (encodeUIntLE 4 message.price
    ++ (Alpha.encode message.buyFirm
    ++ (Alpha.encode message.sellFirm
    ++ (encodeUIntLE 8 message.lastOptPx
    ++ (encodeUIntLE 8 message.volatility
    ++ (encodeUIntLE 8 message.underlyingReferencePrice)))))))))))

def decode (bytes : List UInt8) : Option (OrderExecutedWithPriceSizeMessage × List UInt8) := do
  let (nanosecond, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (executedQuantity, bytes) ← decodeUIntLE 4 bytes
  let (displayQuantity, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 8 bytes
  let (printable_, bytes) ← Printable.decode bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (buyFirm, bytes) ← Alpha.decode 6 bytes
  let (sellFirm, bytes) ← Alpha.decode 6 bytes
  let (lastOptPx, bytes) ← decodeUIntLE 8 bytes
  let (volatility, bytes) ← decodeUIntLE 8 bytes
  let (underlyingReferencePrice, bytes) ← decodeUIntLE 8 bytes
  pure ({ nanosecond, orderId, executedQuantity, displayQuantity, tradeId, printable := printable_, price, buyFirm, sellFirm, lastOptPx, volatility, underlyingReferencePrice }, bytes)

@[simp] theorem encode_length (message : OrderExecutedWithPriceSizeMessage) : (encode message).length = 69 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Printable.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderExecutedWithPriceSizeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderExecutedWithPriceSizeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Printable.decode_encode, some_bind]
  dsimp only
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderExecutedWithPriceSizeMessage

/-- Trade Message: 69 bytes -/
structure TradeMessage where
  nanosecond : BitVec 32
  executedQuantity : BitVec 32
  symbol : Alpha 12
  price : BitVec 32
  tradeId : BitVec 64
  subBook : BitVec 8
  buyFirm : Alpha 6
  sellFirm : Alpha 6
  lastOptPx : BitVec 64
  volatility : BitVec 64
  underlyingReferencePrice : BitVec 64
  deriving DecidableEq, Repr

namespace TradeMessage

def encode (message : TradeMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanosecond
    ++ (encodeUIntLE 4 message.executedQuantity
    ++ (Alpha.encode message.symbol
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 8 message.tradeId
    ++ (encodeUIntLE 1 message.subBook
    ++ (Alpha.encode message.buyFirm
    ++ (Alpha.encode message.sellFirm
    ++ (encodeUIntLE 8 message.lastOptPx
    ++ (encodeUIntLE 8 message.volatility
    ++ (encodeUIntLE 8 message.underlyingReferencePrice))))))))))

def decode (bytes : List UInt8) : Option (TradeMessage × List UInt8) := do
  let (nanosecond, bytes) ← decodeUIntLE 4 bytes
  let (executedQuantity, bytes) ← decodeUIntLE 4 bytes
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 8 bytes
  let (subBook, bytes) ← decodeUIntLE 1 bytes
  let (buyFirm, bytes) ← Alpha.decode 6 bytes
  let (sellFirm, bytes) ← Alpha.decode 6 bytes
  let (lastOptPx, bytes) ← decodeUIntLE 8 bytes
  let (volatility, bytes) ← decodeUIntLE 8 bytes
  let (underlyingReferencePrice, bytes) ← decodeUIntLE 8 bytes
  pure ({ nanosecond, executedQuantity, symbol, price, tradeId, subBook, buyFirm, sellFirm, lastOptPx, volatility, underlyingReferencePrice }, bytes)

@[simp] theorem encode_length (message : TradeMessage) : (encode message).length = 69 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : TradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeMessage

/-- Auction Trade Message: 57 bytes -/
structure AuctionTradeMessage where
  nanosecond : BitVec 32
  executedQuantity : BitVec 32
  symbol : Alpha 12
  price : BitVec 32
  tradeId : BitVec 64
  auctionType : AuctionType
  lastOptPx : BitVec 64
  volatility : BitVec 64
  underlyingReferencePrice : BitVec 64
  deriving DecidableEq, Repr

namespace AuctionTradeMessage

def encode (message : AuctionTradeMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanosecond
    ++ (encodeUIntLE 4 message.executedQuantity
    ++ (Alpha.encode message.symbol
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 8 message.tradeId
    ++ (AuctionType.encode message.auctionType
    ++ (encodeUIntLE 8 message.lastOptPx
    ++ (encodeUIntLE 8 message.volatility
    ++ (encodeUIntLE 8 message.underlyingReferencePrice))))))))

def decode (bytes : List UInt8) : Option (AuctionTradeMessage × List UInt8) := do
  let (nanosecond, bytes) ← decodeUIntLE 4 bytes
  let (executedQuantity, bytes) ← decodeUIntLE 4 bytes
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 8 bytes
  let (auctionType, bytes) ← AuctionType.decode bytes
  let (lastOptPx, bytes) ← decodeUIntLE 8 bytes
  let (volatility, bytes) ← decodeUIntLE 8 bytes
  let (underlyingReferencePrice, bytes) ← decodeUIntLE 8 bytes
  pure ({ nanosecond, executedQuantity, symbol, price, tradeId, auctionType, lastOptPx, volatility, underlyingReferencePrice }, bytes)

@[simp] theorem encode_length (message : AuctionTradeMessage) : (encode message).length = 57 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, AuctionType.encode_length]

theorem encode_length_pos (message : AuctionTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AuctionTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, AuctionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end AuctionTradeMessage

/-- Off Book Trade Message: 76 bytes -/
structure OffBookTradeMessage where
  nanosecond : BitVec 32
  executedQuantity : BitVec 32
  symbol : Alpha 12
  price : BitVec 32
  tradeId : BitVec 64
  offBookTradeType : Alpha 4
  tradeTime : Alpha 8
  tradeDate : Alpha 8
  lastOptPx : BitVec 64
  volatility : BitVec 64
  underlyingReferencePrice : BitVec 64
  deriving DecidableEq, Repr

namespace OffBookTradeMessage

def encode (message : OffBookTradeMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanosecond
    ++ (encodeUIntLE 4 message.executedQuantity
    ++ (Alpha.encode message.symbol
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 8 message.tradeId
    ++ (Alpha.encode message.offBookTradeType
    ++ (Alpha.encode message.tradeTime
    ++ (Alpha.encode message.tradeDate
    ++ (encodeUIntLE 8 message.lastOptPx
    ++ (encodeUIntLE 8 message.volatility
    ++ (encodeUIntLE 8 message.underlyingReferencePrice))))))))))

def decode (bytes : List UInt8) : Option (OffBookTradeMessage × List UInt8) := do
  let (nanosecond, bytes) ← decodeUIntLE 4 bytes
  let (executedQuantity, bytes) ← decodeUIntLE 4 bytes
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 8 bytes
  let (offBookTradeType, bytes) ← Alpha.decode 4 bytes
  let (tradeTime, bytes) ← Alpha.decode 8 bytes
  let (tradeDate, bytes) ← Alpha.decode 8 bytes
  let (lastOptPx, bytes) ← decodeUIntLE 8 bytes
  let (volatility, bytes) ← decodeUIntLE 8 bytes
  let (underlyingReferencePrice, bytes) ← decodeUIntLE 8 bytes
  pure ({ nanosecond, executedQuantity, symbol, price, tradeId, offBookTradeType, tradeTime, tradeDate, lastOptPx, volatility, underlyingReferencePrice }, bytes)

@[simp] theorem encode_length (message : OffBookTradeMessage) : (encode message).length = 76 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : OffBookTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OffBookTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OffBookTradeMessage

/-- Trade Break Message: 13 bytes -/
structure TradeBreakMessage where
  nanosecond : BitVec 32
  tradeId : BitVec 64
  tradeType : TradeType
  deriving DecidableEq, Repr

namespace TradeBreakMessage

def encode (message : TradeBreakMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanosecond
    ++ (encodeUIntLE 8 message.tradeId
    ++ (TradeType.encode message.tradeType))

def decode (bytes : List UInt8) : Option (TradeBreakMessage × List UInt8) := do
  let (nanosecond, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 8 bytes
  let (tradeType, bytes) ← TradeType.decode bytes
  pure ({ nanosecond, tradeId, tradeType }, bytes)

@[simp] theorem encode_length (message : TradeBreakMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, TradeType.encode_length]

theorem encode_length_pos (message : TradeBreakMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeBreakMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [TradeType.decode_encode, some_bind]
  rfl

end TradeBreakMessage

/-- Trade Correction Message: 45 bytes -/
structure TradeCorrectionMessage where
  nanosecond : BitVec 32
  tradeId : BitVec 64
  symbol : Alpha 12
  price : BitVec 32
  quantity : BitVec 32
  subBook : BitVec 8
  buyFirm : Alpha 6
  sellFirm : Alpha 6
  deriving DecidableEq, Repr

namespace TradeCorrectionMessage

def encode (message : TradeCorrectionMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanosecond
    ++ (encodeUIntLE 8 message.tradeId
    ++ (Alpha.encode message.symbol
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 1 message.subBook
    ++ (Alpha.encode message.buyFirm
    ++ (Alpha.encode message.sellFirm)))))))

def decode (bytes : List UInt8) : Option (TradeCorrectionMessage × List UInt8) := do
  let (nanosecond, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 8 bytes
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (subBook, bytes) ← decodeUIntLE 1 bytes
  let (buyFirm, bytes) ← Alpha.decode 6 bytes
  let (sellFirm, bytes) ← Alpha.decode 6 bytes
  pure ({ nanosecond, tradeId, symbol, price, quantity, subBook, buyFirm, sellFirm }, bytes)

@[simp] theorem encode_length (message : TradeCorrectionMessage) : (encode message).length = 45 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : TradeCorrectionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCorrectionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeCorrectionMessage

/-- Recovery Trade Message: 92 bytes -/
structure RecoveryTradeMessage where
  nanosecond : BitVec 32
  executedQuantity : BitVec 32
  symbol : Alpha 12
  price : BitVec 32
  tradeId : BitVec 64
  auctionType : AuctionType
  offBookTradeType : Alpha 4
  tradeTime : Alpha 8
  tradeDate : Alpha 8
  actionType : ActionType
  subBook : BitVec 8
  buyFirm : Alpha 6
  sellFirm : Alpha 6
  lastOptPx : BitVec 64
  volatility : BitVec 64
  underlyingReferencePrice : BitVec 64
  auctionTradeType : AuctionTradeType
  deriving DecidableEq, Repr

namespace RecoveryTradeMessage

def encode (message : RecoveryTradeMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanosecond
    ++ (encodeUIntLE 4 message.executedQuantity
    ++ (Alpha.encode message.symbol
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 8 message.tradeId
    ++ (AuctionType.encode message.auctionType
    ++ (Alpha.encode message.offBookTradeType
    ++ (Alpha.encode message.tradeTime
    ++ (Alpha.encode message.tradeDate
    ++ (ActionType.encode message.actionType
    ++ (encodeUIntLE 1 message.subBook
    ++ (Alpha.encode message.buyFirm
    ++ (Alpha.encode message.sellFirm
    ++ (encodeUIntLE 8 message.lastOptPx
    ++ (encodeUIntLE 8 message.volatility
    ++ (encodeUIntLE 8 message.underlyingReferencePrice
    ++ (AuctionTradeType.encode message.auctionTradeType))))))))))))))))

def decode (bytes : List UInt8) : Option (RecoveryTradeMessage × List UInt8) := do
  let (nanosecond, bytes) ← decodeUIntLE 4 bytes
  let (executedQuantity, bytes) ← decodeUIntLE 4 bytes
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 8 bytes
  let (auctionType, bytes) ← AuctionType.decode bytes
  let (offBookTradeType, bytes) ← Alpha.decode 4 bytes
  let (tradeTime, bytes) ← Alpha.decode 8 bytes
  let (tradeDate, bytes) ← Alpha.decode 8 bytes
  let (actionType, bytes) ← ActionType.decode bytes
  let (subBook, bytes) ← decodeUIntLE 1 bytes
  let (buyFirm, bytes) ← Alpha.decode 6 bytes
  let (sellFirm, bytes) ← Alpha.decode 6 bytes
  let (lastOptPx, bytes) ← decodeUIntLE 8 bytes
  let (volatility, bytes) ← decodeUIntLE 8 bytes
  let (underlyingReferencePrice, bytes) ← decodeUIntLE 8 bytes
  let (auctionTradeType, bytes) ← AuctionTradeType.decode bytes
  pure ({ nanosecond, executedQuantity, symbol, price, tradeId, auctionType, offBookTradeType, tradeTime, tradeDate, actionType, subBook, buyFirm, sellFirm, lastOptPx, volatility, underlyingReferencePrice, auctionTradeType }, bytes)

@[simp] theorem encode_length (message : RecoveryTradeMessage) : (encode message).length = 92 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, AuctionType.encode_length, ActionType.encode_length, AuctionTradeType.encode_length]

theorem encode_length_pos (message : RecoveryTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RecoveryTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, AuctionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ActionType.decode_encode, some_bind]
  dsimp only
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [AuctionTradeType.decode_encode, some_bind]
  rfl

end RecoveryTradeMessage

/-- Auction Info Message: 30 bytes -/
structure AuctionInfoMessage where
  nanosecond : BitVec 32
  pairedQuantity : BitVec 32
  imbalanceQuantity : BitVec 32
  imbalanceDirection : ImbalanceDirection
  symbol : Alpha 12
  price : BitVec 32
  auctionType : AuctionType
  deriving DecidableEq, Repr

namespace AuctionInfoMessage

def encode (message : AuctionInfoMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanosecond
    ++ (encodeUIntLE 4 message.pairedQuantity
    ++ (encodeUIntLE 4 message.imbalanceQuantity
    ++ (ImbalanceDirection.encode message.imbalanceDirection
    ++ (Alpha.encode message.symbol
    ++ (encodeUIntLE 4 message.price
    ++ (AuctionType.encode message.auctionType))))))

def decode (bytes : List UInt8) : Option (AuctionInfoMessage × List UInt8) := do
  let (nanosecond, bytes) ← decodeUIntLE 4 bytes
  let (pairedQuantity, bytes) ← decodeUIntLE 4 bytes
  let (imbalanceQuantity, bytes) ← decodeUIntLE 4 bytes
  let (imbalanceDirection, bytes) ← ImbalanceDirection.decode bytes
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (auctionType, bytes) ← AuctionType.decode bytes
  pure ({ nanosecond, pairedQuantity, imbalanceQuantity, imbalanceDirection, symbol, price, auctionType }, bytes)

@[simp] theorem encode_length (message : AuctionInfoMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, ImbalanceDirection.encode_length, Alpha.encode_length, AuctionType.encode_length]

theorem encode_length_pos (message : AuctionInfoMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AuctionInfoMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, ImbalanceDirection.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [AuctionType.decode_encode, some_bind]
  rfl

end AuctionInfoMessage

/-- Statistics Message: 23 bytes -/
structure StatisticsMessage where
  nanosecond : BitVec 32
  symbol : Alpha 12
  statisticType : StatisticType
  price : BitVec 32
  openCloseIndicator : OpenCloseIndicator
  subBook : BitVec 8
  deriving DecidableEq, Repr

namespace StatisticsMessage

def encode (message : StatisticsMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanosecond
    ++ (Alpha.encode message.symbol
    ++ (StatisticType.encode message.statisticType
    ++ (encodeUIntLE 4 message.price
    ++ (OpenCloseIndicator.encode message.openCloseIndicator
    ++ (encodeUIntLE 1 message.subBook)))))

def decode (bytes : List UInt8) : Option (StatisticsMessage × List UInt8) := do
  let (nanosecond, bytes) ← decodeUIntLE 4 bytes
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (statisticType, bytes) ← StatisticType.decode bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (openCloseIndicator, bytes) ← OpenCloseIndicator.decode bytes
  let (subBook, bytes) ← decodeUIntLE 1 bytes
  pure ({ nanosecond, symbol, statisticType, price, openCloseIndicator, subBook }, bytes)

@[simp] theorem encode_length (message : StatisticsMessage) : (encode message).length = 23 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, StatisticType.encode_length, OpenCloseIndicator.encode_length]

theorem encode_length_pos (message : StatisticsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StatisticsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StatisticType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OpenCloseIndicator.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end StatisticsMessage

/-- Extended Statistics Message: 93 bytes -/
structure ExtendedStatisticsMessage where
  nanosecond : BitVec 32
  symbol : Alpha 12
  highPrice : BitVec 32
  lowPrice : BitVec 32
  vwap : BitVec 32
  volume : BitVec 32
  turnover : BitVec 64
  trades : BitVec 32
  reserved8 : Alpha 8
  subBook : BitVec 8
  notionalExposure : BitVec 64
  notionalDeltaExposure : BitVec 64
  dailyForeignBuyValue : BitVec 64
  dailyForeignSellValue : BitVec 64
  marketCapitalization : BitVec 64
  deriving DecidableEq, Repr

namespace ExtendedStatisticsMessage

def encode (message : ExtendedStatisticsMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanosecond
    ++ (Alpha.encode message.symbol
    ++ (encodeUIntLE 4 message.highPrice
    ++ (encodeUIntLE 4 message.lowPrice
    ++ (encodeUIntLE 4 message.vwap
    ++ (encodeUIntLE 4 message.volume
    ++ (encodeUIntLE 8 message.turnover
    ++ (encodeUIntLE 4 message.trades
    ++ (Alpha.encode message.reserved8
    ++ (encodeUIntLE 1 message.subBook
    ++ (encodeUIntLE 8 message.notionalExposure
    ++ (encodeUIntLE 8 message.notionalDeltaExposure
    ++ (encodeUIntLE 8 message.dailyForeignBuyValue
    ++ (encodeUIntLE 8 message.dailyForeignSellValue
    ++ (encodeUIntLE 8 message.marketCapitalization))))))))))))))

def decode (bytes : List UInt8) : Option (ExtendedStatisticsMessage × List UInt8) := do
  let (nanosecond, bytes) ← decodeUIntLE 4 bytes
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (highPrice, bytes) ← decodeUIntLE 4 bytes
  let (lowPrice, bytes) ← decodeUIntLE 4 bytes
  let (vwap, bytes) ← decodeUIntLE 4 bytes
  let (volume, bytes) ← decodeUIntLE 4 bytes
  let (turnover, bytes) ← decodeUIntLE 8 bytes
  let (trades, bytes) ← decodeUIntLE 4 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  let (subBook, bytes) ← decodeUIntLE 1 bytes
  let (notionalExposure, bytes) ← decodeUIntLE 8 bytes
  let (notionalDeltaExposure, bytes) ← decodeUIntLE 8 bytes
  let (dailyForeignBuyValue, bytes) ← decodeUIntLE 8 bytes
  let (dailyForeignSellValue, bytes) ← decodeUIntLE 8 bytes
  let (marketCapitalization, bytes) ← decodeUIntLE 8 bytes
  pure ({ nanosecond, symbol, highPrice, lowPrice, vwap, volume, turnover, trades, reserved8, subBook, notionalExposure, notionalDeltaExposure, dailyForeignBuyValue, dailyForeignSellValue, marketCapitalization }, bytes)

@[simp] theorem encode_length (message : ExtendedStatisticsMessage) : (encode message).length = 93 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : ExtendedStatisticsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExtendedStatisticsMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ExtendedStatisticsMessage

/-- Consolidated Statistics Message: 57 bytes -/
structure ConsolidatedStatisticsMessage where
  nanosecond : BitVec 32
  statisticsType : BitVec 8
  symbol : Alpha 12
  volume : BitVec 32
  turnover : BitVec 64
  trades : BitVec 32
  dailyForeignBuyValue : BitVec 64
  dailyForeignSellValue : BitVec 64
  marketCapitalization : BitVec 64
  deriving DecidableEq, Repr

namespace ConsolidatedStatisticsMessage

def encode (message : ConsolidatedStatisticsMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanosecond
    ++ (encodeUIntLE 1 message.statisticsType
    ++ (Alpha.encode message.symbol
    ++ (encodeUIntLE 4 message.volume
    ++ (encodeUIntLE 8 message.turnover
    ++ (encodeUIntLE 4 message.trades
    ++ (encodeUIntLE 8 message.dailyForeignBuyValue
    ++ (encodeUIntLE 8 message.dailyForeignSellValue
    ++ (encodeUIntLE 8 message.marketCapitalization))))))))

def decode (bytes : List UInt8) : Option (ConsolidatedStatisticsMessage × List UInt8) := do
  let (nanosecond, bytes) ← decodeUIntLE 4 bytes
  let (statisticsType, bytes) ← decodeUIntLE 1 bytes
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (volume, bytes) ← decodeUIntLE 4 bytes
  let (turnover, bytes) ← decodeUIntLE 8 bytes
  let (trades, bytes) ← decodeUIntLE 4 bytes
  let (dailyForeignBuyValue, bytes) ← decodeUIntLE 8 bytes
  let (dailyForeignSellValue, bytes) ← decodeUIntLE 8 bytes
  let (marketCapitalization, bytes) ← decodeUIntLE 8 bytes
  pure ({ nanosecond, statisticsType, symbol, volume, turnover, trades, dailyForeignBuyValue, dailyForeignSellValue, marketCapitalization }, bytes)

@[simp] theorem encode_length (message : ConsolidatedStatisticsMessage) : (encode message).length = 57 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : ConsolidatedStatisticsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ConsolidatedStatisticsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ConsolidatedStatisticsMessage

/-- Index Message: 25 bytes -/
structure IndexMessage where
  nanosecond : BitVec 32
  symbol : Alpha 12
  indexValue : BitVec 32
  updateType : BitVec 8
  perctgDiffFromClosing : BitVec 32
  deriving DecidableEq, Repr

namespace IndexMessage

def encode (message : IndexMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanosecond
    ++ (Alpha.encode message.symbol
    ++ (encodeUIntLE 4 message.indexValue
    ++ (encodeUIntLE 1 message.updateType
    ++ (encodeUIntLE 4 message.perctgDiffFromClosing))))

def decode (bytes : List UInt8) : Option (IndexMessage × List UInt8) := do
  let (nanosecond, bytes) ← decodeUIntLE 4 bytes
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (indexValue, bytes) ← decodeUIntLE 4 bytes
  let (updateType, bytes) ← decodeUIntLE 1 bytes
  let (perctgDiffFromClosing, bytes) ← decodeUIntLE 4 bytes
  pure ({ nanosecond, symbol, indexValue, updateType, perctgDiffFromClosing }, bytes)

@[simp] theorem encode_length (message : IndexMessage) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : IndexMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IndexMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end IndexMessage

/-- Aon Info Message: 34 bytes -/
structure AonInfoMessage where
  nanosecond : BitVec 32
  symbol : Alpha 12
  price : BitVec 32
  side : Side
  quantity : BitVec 32
  aonStatus : AonStatus
  date : Alpha 8
  deriving DecidableEq, Repr

namespace AonInfoMessage

def encode (message : AonInfoMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanosecond
    ++ (Alpha.encode message.symbol
    ++ (encodeUIntLE 4 message.price
    ++ (Side.encode message.side
    ++ (encodeUIntLE 4 message.quantity
    ++ (AonStatus.encode message.aonStatus
    ++ (Alpha.encode message.date))))))

def decode (bytes : List UInt8) : Option (AonInfoMessage × List UInt8) := do
  let (nanosecond, bytes) ← decodeUIntLE 4 bytes
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (aonStatus, bytes) ← AonStatus.decode bytes
  let (date, bytes) ← Alpha.decode 8 bytes
  pure ({ nanosecond, symbol, price, side, quantity, aonStatus, date }, bytes)

@[simp] theorem encode_length (message : AonInfoMessage) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, Side.encode_length, AonStatus.encode_length]

theorem encode_length_pos (message : AonInfoMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AonInfoMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, AonStatus.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end AonInfoMessage

/-- News Message: 1063 bytes -/
structure NewsMessage where
  nanosecond : BitVec 32
  time : Alpha 8
  urgency : Urgency
  headline : Alpha 100
  text : Alpha 750
  instruments : Alpha 100
  underlyings : Alpha 100
  deriving DecidableEq, Repr

namespace NewsMessage

def encode (message : NewsMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanosecond
    ++ (Alpha.encode message.time
    ++ (Urgency.encode message.urgency
    ++ (Alpha.encode message.headline
    ++ (Alpha.encode message.text
    ++ (Alpha.encode message.instruments
    ++ (Alpha.encode message.underlyings))))))

def decode (bytes : List UInt8) : Option (NewsMessage × List UInt8) := do
  let (nanosecond, bytes) ← decodeUIntLE 4 bytes
  let (time, bytes) ← Alpha.decode 8 bytes
  let (urgency, bytes) ← Urgency.decode bytes
  let (headline, bytes) ← Alpha.decode 100 bytes
  let (text, bytes) ← Alpha.decode 750 bytes
  let (instruments, bytes) ← Alpha.decode 100 bytes
  let (underlyings, bytes) ← Alpha.decode 100 bytes
  pure ({ nanosecond, time, urgency, headline, text, instruments, underlyings }, bytes)

@[simp] theorem encode_length (message : NewsMessage) : (encode message).length = 1063 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, Urgency.encode_length]

theorem encode_length_pos (message : NewsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Urgency.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end NewsMessage

/-- Update Price Point Message: 34 bytes -/
structure UpdatePricePointMessage where
  nanosecond : BitVec 32
  symbol : Alpha 12
  pricePointSubBookFlags : BitVec 8
  pricePointAction : PricePointAction
  side : Side
  priceLevel : BitVec 8
  price : BitVec 32
  quantity : BitVec 32
  splits : BitVec 32
  updatePricePointFlags : BitVec 8
  reserved1 : Alpha 1
  deriving DecidableEq, Repr

namespace UpdatePricePointMessage

def encode (message : UpdatePricePointMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanosecond
    ++ (Alpha.encode message.symbol
    ++ (encodeUIntLE 1 message.pricePointSubBookFlags
    ++ (PricePointAction.encode message.pricePointAction
    ++ (Side.encode message.side
    ++ (encodeUIntLE 1 message.priceLevel
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 4 message.splits
    ++ (encodeUIntLE 1 message.updatePricePointFlags
    ++ (Alpha.encode message.reserved1))))))))))

def decode (bytes : List UInt8) : Option (UpdatePricePointMessage × List UInt8) := do
  let (nanosecond, bytes) ← decodeUIntLE 4 bytes
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (pricePointSubBookFlags, bytes) ← decodeUIntLE 1 bytes
  let (pricePointAction, bytes) ← PricePointAction.decode bytes
  let (side, bytes) ← Side.decode bytes
  let (priceLevel, bytes) ← decodeUIntLE 1 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (splits, bytes) ← decodeUIntLE 4 bytes
  let (updatePricePointFlags, bytes) ← decodeUIntLE 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  pure ({ nanosecond, symbol, pricePointSubBookFlags, pricePointAction, side, priceLevel, price, quantity, splits, updatePricePointFlags, reserved1 }, bytes)

@[simp] theorem encode_length (message : UpdatePricePointMessage) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, PricePointAction.encode_length, Side.encode_length]

theorem encode_length_pos (message : UpdatePricePointMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UpdatePricePointMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, PricePointAction.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
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

end UpdatePricePointMessage

/-- Delete Price Point Message: 20 bytes -/
structure DeletePricePointMessage where
  nanosecond : BitVec 32
  symbol : Alpha 12
  pricePointSubBookFlags : BitVec 8
  side : Side
  priceLevel : BitVec 8
  reserved1 : Alpha 1
  deriving DecidableEq, Repr

namespace DeletePricePointMessage

def encode (message : DeletePricePointMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanosecond
    ++ (Alpha.encode message.symbol
    ++ (encodeUIntLE 1 message.pricePointSubBookFlags
    ++ (Side.encode message.side
    ++ (encodeUIntLE 1 message.priceLevel
    ++ (Alpha.encode message.reserved1)))))

def decode (bytes : List UInt8) : Option (DeletePricePointMessage × List UInt8) := do
  let (nanosecond, bytes) ← decodeUIntLE 4 bytes
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (pricePointSubBookFlags, bytes) ← decodeUIntLE 1 bytes
  let (side, bytes) ← Side.decode bytes
  let (priceLevel, bytes) ← decodeUIntLE 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  pure ({ nanosecond, symbol, pricePointSubBookFlags, side, priceLevel, reserved1 }, bytes)

@[simp] theorem encode_length (message : DeletePricePointMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, Side.encode_length]

theorem encode_length_pos (message : DeletePricePointMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DeletePricePointMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end DeletePricePointMessage

/-- Top Of Book Message: 33 bytes -/
structure TopOfBookMessage where
  nanosecond : BitVec 32
  symbol : Alpha 12
  pricePointSubBookFlags : BitVec 8
  topOfBookAction : TopOfBookAction
  side : Side
  price : BitVec 32
  quantity : BitVec 32
  marketOrderQuantity : BitVec 32
  reserved2 : Alpha 2
  deriving DecidableEq, Repr

namespace TopOfBookMessage

def encode (message : TopOfBookMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanosecond
    ++ (Alpha.encode message.symbol
    ++ (encodeUIntLE 1 message.pricePointSubBookFlags
    ++ (TopOfBookAction.encode message.topOfBookAction
    ++ (Side.encode message.side
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 4 message.marketOrderQuantity
    ++ (Alpha.encode message.reserved2))))))))

def decode (bytes : List UInt8) : Option (TopOfBookMessage × List UInt8) := do
  let (nanosecond, bytes) ← decodeUIntLE 4 bytes
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (pricePointSubBookFlags, bytes) ← decodeUIntLE 1 bytes
  let (topOfBookAction, bytes) ← TopOfBookAction.decode bytes
  let (side, bytes) ← Side.decode bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (marketOrderQuantity, bytes) ← decodeUIntLE 4 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  pure ({ nanosecond, symbol, pricePointSubBookFlags, topOfBookAction, side, price, quantity, marketOrderQuantity, reserved2 }, bytes)

@[simp] theorem encode_length (message : TopOfBookMessage) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TopOfBookAction.encode_length, Side.encode_length]

theorem encode_length_pos (message : TopOfBookMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TopOfBookMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TopOfBookAction.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TopOfBookMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | timeMessage (message : TimeMessage) -- 84
  | systemEventMessage (message : SystemEventMessage) -- 83
  | symbolDirectoryMessage (message : SymbolDirectoryMessage) -- 82
  | symbolStatusMessage (message : SymbolStatusMessage) -- 72
  | addOrderMessage (message : AddOrderMessage) -- 65
  | addAttributedOrderMessage (message : AddAttributedOrderMessage) -- 70
  | orderDeletedMessage (message : OrderDeletedMessage) -- 68
  | orderModifiedMessage (message : OrderModifiedMessage) -- 85
  | orderBookClearMessage (message : OrderBookClearMessage) -- 121
  | orderExecutedMessage (message : OrderExecutedMessage) -- 69
  | orderExecutedWithPriceSizeMessage (message : OrderExecutedWithPriceSizeMessage) -- 67
  | tradeMessage (message : TradeMessage) -- 80
  | auctionTradeMessage (message : AuctionTradeMessage) -- 81
  | offBookTradeMessage (message : OffBookTradeMessage) -- 120
  | tradeBreakMessage (message : TradeBreakMessage) -- 66
  | tradeCorrectionMessage (message : TradeCorrectionMessage) -- 96
  | recoveryTradeMessage (message : RecoveryTradeMessage) -- 118
  | auctionInfoMessage (message : AuctionInfoMessage) -- 73
  | statisticsMessage (message : StatisticsMessage) -- 119
  | extendedStatisticsMessage (message : ExtendedStatisticsMessage) -- 128
  | consolidatedStatisticsMessage (message : ConsolidatedStatisticsMessage) -- 100
  | indexMessage (message : IndexMessage) -- 98
  | aonInfoMessage (message : AonInfoMessage) -- 101
  | newsMessage (message : NewsMessage) -- 117
  | updatePricePointMessage (message : UpdatePricePointMessage) -- 115
  | deletePricePointMessage (message : DeletePricePointMessage) -- 114
  | topOfBookMessage (message : TopOfBookMessage) -- 113
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .timeMessage _ => 84
  | .systemEventMessage _ => 83
  | .symbolDirectoryMessage _ => 82
  | .symbolStatusMessage _ => 72
  | .addOrderMessage _ => 65
  | .addAttributedOrderMessage _ => 70
  | .orderDeletedMessage _ => 68
  | .orderModifiedMessage _ => 85
  | .orderBookClearMessage _ => 121
  | .orderExecutedMessage _ => 69
  | .orderExecutedWithPriceSizeMessage _ => 67
  | .tradeMessage _ => 80
  | .auctionTradeMessage _ => 81
  | .offBookTradeMessage _ => 120
  | .tradeBreakMessage _ => 66
  | .tradeCorrectionMessage _ => 96
  | .recoveryTradeMessage _ => 118
  | .auctionInfoMessage _ => 73
  | .statisticsMessage _ => 119
  | .extendedStatisticsMessage _ => 128
  | .consolidatedStatisticsMessage _ => 100
  | .indexMessage _ => 98
  | .aonInfoMessage _ => 101
  | .newsMessage _ => 117
  | .updatePricePointMessage _ => 115
  | .deletePricePointMessage _ => 114
  | .topOfBookMessage _ => 113

def encode : Payload → List UInt8
  | .timeMessage message => TimeMessage.encode message
  | .systemEventMessage message => SystemEventMessage.encode message
  | .symbolDirectoryMessage message => SymbolDirectoryMessage.encode message
  | .symbolStatusMessage message => SymbolStatusMessage.encode message
  | .addOrderMessage message => AddOrderMessage.encode message
  | .addAttributedOrderMessage message => AddAttributedOrderMessage.encode message
  | .orderDeletedMessage message => OrderDeletedMessage.encode message
  | .orderModifiedMessage message => OrderModifiedMessage.encode message
  | .orderBookClearMessage message => OrderBookClearMessage.encode message
  | .orderExecutedMessage message => OrderExecutedMessage.encode message
  | .orderExecutedWithPriceSizeMessage message => OrderExecutedWithPriceSizeMessage.encode message
  | .tradeMessage message => TradeMessage.encode message
  | .auctionTradeMessage message => AuctionTradeMessage.encode message
  | .offBookTradeMessage message => OffBookTradeMessage.encode message
  | .tradeBreakMessage message => TradeBreakMessage.encode message
  | .tradeCorrectionMessage message => TradeCorrectionMessage.encode message
  | .recoveryTradeMessage message => RecoveryTradeMessage.encode message
  | .auctionInfoMessage message => AuctionInfoMessage.encode message
  | .statisticsMessage message => StatisticsMessage.encode message
  | .extendedStatisticsMessage message => ExtendedStatisticsMessage.encode message
  | .consolidatedStatisticsMessage message => ConsolidatedStatisticsMessage.encode message
  | .indexMessage message => IndexMessage.encode message
  | .aonInfoMessage message => AonInfoMessage.encode message
  | .newsMessage message => NewsMessage.encode message
  | .updatePricePointMessage message => UpdatePricePointMessage.encode message
  | .deletePricePointMessage message => DeletePricePointMessage.encode message
  | .topOfBookMessage message => TopOfBookMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 1063 := by
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
  | symbolStatusMessage inner =>
    simp only [encode, SymbolStatusMessage.encode_length]
    omega
  | addOrderMessage inner =>
    simp only [encode, AddOrderMessage.encode_length]
    omega
  | addAttributedOrderMessage inner =>
    simp only [encode, AddAttributedOrderMessage.encode_length]
    omega
  | orderDeletedMessage inner =>
    simp only [encode, OrderDeletedMessage.encode_length]
    omega
  | orderModifiedMessage inner =>
    simp only [encode, OrderModifiedMessage.encode_length]
    omega
  | orderBookClearMessage inner =>
    simp only [encode, OrderBookClearMessage.encode_length]
    omega
  | orderExecutedMessage inner =>
    simp only [encode, OrderExecutedMessage.encode_length]
    omega
  | orderExecutedWithPriceSizeMessage inner =>
    simp only [encode, OrderExecutedWithPriceSizeMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [encode, TradeMessage.encode_length]
    omega
  | auctionTradeMessage inner =>
    simp only [encode, AuctionTradeMessage.encode_length]
    omega
  | offBookTradeMessage inner =>
    simp only [encode, OffBookTradeMessage.encode_length]
    omega
  | tradeBreakMessage inner =>
    simp only [encode, TradeBreakMessage.encode_length]
    omega
  | tradeCorrectionMessage inner =>
    simp only [encode, TradeCorrectionMessage.encode_length]
    omega
  | recoveryTradeMessage inner =>
    simp only [encode, RecoveryTradeMessage.encode_length]
    omega
  | auctionInfoMessage inner =>
    simp only [encode, AuctionInfoMessage.encode_length]
    omega
  | statisticsMessage inner =>
    simp only [encode, StatisticsMessage.encode_length]
    omega
  | extendedStatisticsMessage inner =>
    simp only [encode, ExtendedStatisticsMessage.encode_length]
    omega
  | consolidatedStatisticsMessage inner =>
    simp only [encode, ConsolidatedStatisticsMessage.encode_length]
    omega
  | indexMessage inner =>
    simp only [encode, IndexMessage.encode_length]
    omega
  | aonInfoMessage inner =>
    simp only [encode, AonInfoMessage.encode_length]
    omega
  | newsMessage inner =>
    simp only [encode, NewsMessage.encode_length]
    omega
  | updatePricePointMessage inner =>
    simp only [encode, UpdatePricePointMessage.encode_length]
    omega
  | deletePricePointMessage inner =>
    simp only [encode, DeletePricePointMessage.encode_length]
    omega
  | topOfBookMessage inner =>
    simp only [encode, TopOfBookMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 84 then (TimeMessage.decode bytes).map fun (message, rest) => (.timeMessage message, rest)
  else if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 82 then (SymbolDirectoryMessage.decode bytes).map fun (message, rest) => (.symbolDirectoryMessage message, rest)
  else if tag = 72 then (SymbolStatusMessage.decode bytes).map fun (message, rest) => (.symbolStatusMessage message, rest)
  else if tag = 65 then (AddOrderMessage.decode bytes).map fun (message, rest) => (.addOrderMessage message, rest)
  else if tag = 70 then (AddAttributedOrderMessage.decode bytes).map fun (message, rest) => (.addAttributedOrderMessage message, rest)
  else if tag = 68 then (OrderDeletedMessage.decode bytes).map fun (message, rest) => (.orderDeletedMessage message, rest)
  else if tag = 85 then (OrderModifiedMessage.decode bytes).map fun (message, rest) => (.orderModifiedMessage message, rest)
  else if tag = 121 then (OrderBookClearMessage.decode bytes).map fun (message, rest) => (.orderBookClearMessage message, rest)
  else if tag = 69 then (OrderExecutedMessage.decode bytes).map fun (message, rest) => (.orderExecutedMessage message, rest)
  else if tag = 67 then (OrderExecutedWithPriceSizeMessage.decode bytes).map fun (message, rest) => (.orderExecutedWithPriceSizeMessage message, rest)
  else if tag = 80 then (TradeMessage.decode bytes).map fun (message, rest) => (.tradeMessage message, rest)
  else if tag = 81 then (AuctionTradeMessage.decode bytes).map fun (message, rest) => (.auctionTradeMessage message, rest)
  else if tag = 120 then (OffBookTradeMessage.decode bytes).map fun (message, rest) => (.offBookTradeMessage message, rest)
  else if tag = 66 then (TradeBreakMessage.decode bytes).map fun (message, rest) => (.tradeBreakMessage message, rest)
  else if tag = 96 then (TradeCorrectionMessage.decode bytes).map fun (message, rest) => (.tradeCorrectionMessage message, rest)
  else if tag = 118 then (RecoveryTradeMessage.decode bytes).map fun (message, rest) => (.recoveryTradeMessage message, rest)
  else if tag = 73 then (AuctionInfoMessage.decode bytes).map fun (message, rest) => (.auctionInfoMessage message, rest)
  else if tag = 119 then (StatisticsMessage.decode bytes).map fun (message, rest) => (.statisticsMessage message, rest)
  else if tag = 128 then (ExtendedStatisticsMessage.decode bytes).map fun (message, rest) => (.extendedStatisticsMessage message, rest)
  else if tag = 100 then (ConsolidatedStatisticsMessage.decode bytes).map fun (message, rest) => (.consolidatedStatisticsMessage message, rest)
  else if tag = 98 then (IndexMessage.decode bytes).map fun (message, rest) => (.indexMessage message, rest)
  else if tag = 101 then (AonInfoMessage.decode bytes).map fun (message, rest) => (.aonInfoMessage message, rest)
  else if tag = 117 then (NewsMessage.decode bytes).map fun (message, rest) => (.newsMessage message, rest)
  else if tag = 115 then (UpdatePricePointMessage.decode bytes).map fun (message, rest) => (.updatePricePointMessage message, rest)
  else if tag = 114 then (DeletePricePointMessage.decode bytes).map fun (message, rest) => (.deletePricePointMessage message, rest)
  else if tag = 113 then (TopOfBookMessage.decode bytes).map fun (message, rest) => (.topOfBookMessage message, rest)
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
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 2 < 256 ^ 2 := by
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
  | symbolStatusMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SymbolStatusMessage.encode_length]
    omega
  | addOrderMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, AddOrderMessage.encode_length]
    omega
  | addAttributedOrderMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, AddAttributedOrderMessage.encode_length]
    omega
  | orderDeletedMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderDeletedMessage.encode_length]
    omega
  | orderModifiedMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderModifiedMessage.encode_length]
    omega
  | orderBookClearMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderBookClearMessage.encode_length]
    omega
  | orderExecutedMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderExecutedMessage.encode_length]
    omega
  | orderExecutedWithPriceSizeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderExecutedWithPriceSizeMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeMessage.encode_length]
    omega
  | auctionTradeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, AuctionTradeMessage.encode_length]
    omega
  | offBookTradeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OffBookTradeMessage.encode_length]
    omega
  | tradeBreakMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeBreakMessage.encode_length]
    omega
  | tradeCorrectionMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeCorrectionMessage.encode_length]
    omega
  | recoveryTradeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, RecoveryTradeMessage.encode_length]
    omega
  | auctionInfoMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, AuctionInfoMessage.encode_length]
    omega
  | statisticsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, StatisticsMessage.encode_length]
    omega
  | extendedStatisticsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ExtendedStatisticsMessage.encode_length]
    omega
  | consolidatedStatisticsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ConsolidatedStatisticsMessage.encode_length]
    omega
  | indexMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, IndexMessage.encode_length]
    omega
  | aonInfoMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, AonInfoMessage.encode_length]
    omega
  | newsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, NewsMessage.encode_length]
    omega
  | updatePricePointMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, UpdatePricePointMessage.encode_length]
    omega
  | deletePricePointMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, DeletePricePointMessage.encode_length]
    omega
  | topOfBookMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TopOfBookMessage.encode_length]
    omega

/-- Size rule: Message Length counts the bytes after it plus 2, so it is written from the body and checked on decode -/
def encode : Message → List UInt8 :=
  encodeFramedLE 2 2 encodeBody

def decode : List UInt8 → Option (Message × List UInt8) :=
  decodeFramedLE 2 2 decodeBody

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 2 2 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end Message

/-- Packet -/
structure Packet where
  length : BitVec 16
  marketDataGroup : Alpha 1
  sequenceNumber : BitVec 32
  message : Bounded 1 Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUIntLE 2 message.length
    ++ (encodeUIntLE 1 (BitVec.ofNat (8 * 1) message.message.val.length)
    ++ (Alpha.encode message.marketDataGroup
    ++ (encodeUIntLE 4 message.sequenceNumber
    ++ (encodeMany Message.encode message.message.val))))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (length, bytes) ← decodeUIntLE 2 bytes
  let (messageCount, bytes) ← decodeUIntLE 1 bytes
  let (marketDataGroup, bytes) ← Alpha.decode 1 bytes
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (message_, bytes) ← decodeMany Message.decode messageCount.toNat bytes
  if fits_message : message_.length < 256 ^ 1 then
    pure ({ length, marketDataGroup, sequenceNumber, message := ⟨message_, fits_message⟩ }, bytes)
  else none

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt]
  rfl

end Packet

end Omi.NairobiNairobiequitiesRealtimeMitchV122
