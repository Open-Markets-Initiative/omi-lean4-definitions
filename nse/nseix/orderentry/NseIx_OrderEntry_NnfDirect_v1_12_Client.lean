import Wire

/-!
# National Stock Exchange of India Ltd Order Entry v1.12

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.

Note: St Broker Eligibility Per Mkt is a bit field set, proven as its 2 byte integer rather than bit
by bit

Note: Sign On Request In Message is selected by more than one code: each is a constructor of its own
over the one record, so the code read is the code written back

Note: St Order Flags is a bit field set, proven as its 2 byte integer rather than bit by bit

Note: Additional Order Flags is a bit field set, proven as its 1 byte integer rather than bit by bit

Note: Order Entry Request Message is selected by more than one code: each is a constructor of its
own over the one record, so the code read is the code written back

Note: Order Modification Request Message is selected by more than one code: each is a constructor of
its own over the one record, so the code read is the code written back

Note: Order Cancellation Request Message is selected by more than one code: each is a constructor of
its own over the one record, so the code read is the code written back

Note: Trade Inquiry Message is selected by more than one code: each is a constructor of its own over
the one record, so the code read is the code written back

Note: Spread Order Entry Request Message is selected by more than one code: each is a constructor of
its own over the one record, so the code read is the code written back

Note: Mba Inquiry Request Message is selected by more than one code: each is a constructor of its
own over the one record, so the code read is the code written back

Note: Normal Order Limit Update Message is selected by more than one code: each is a constructor of
its own over the one record, so the code read is the code written back

Note: Client Packet Body is keyed on Transaction Code, which Client Registration Packet holds 16
bytes in, behind what frames it: those 2 bytes are read where they lie without taking them, 23008
reading Client Registration Packet and any other Client Session Packet, each carrying the proof of
what its encoding holds there

Note: Client Direct Packet's Packet Length is written from its body but not checked on decode, since
the body has no bound the prefix must fit; the body is read by its content

License: MIT No Attribution
-/

namespace Omi.NseNseixOrderentryNnfdirectV112Client

/-- Broker Status: one byte code -/
def BrokerStatus.codes : List UInt8 :=
  [0x53, 0x41, 0x44, 0x43, 0x56]

inductive BrokerStatus where
  | suspended -- Suspended
  | active -- Active
  | deactivated -- Deactivated
  | closeout -- Closeout
  | voluntaryCloseOut -- Voluntary Close Out
  | unlisted (byte : { byte : UInt8 // byte ∉ BrokerStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BrokerStatus

def toByte : BrokerStatus → UInt8
  | .suspended => 0x53
  | .active => 0x41
  | .deactivated => 0x44
  | .closeout => 0x43
  | .voluntaryCloseOut => 0x56
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BrokerStatus :=
  if byte = 0x53 then .suspended
  else if byte = 0x41 then .active
  else if byte = 0x44 then .deactivated
  else if byte = 0x43 then .closeout
  else .voluntaryCloseOut

def ofByte (byte : UInt8) : BrokerStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BrokerStatus) : ofByte value.toByte = value := by
  cases value with
  | suspended => decide
  | active => decide
  | deactivated => decide
  | closeout => decide
  | voluntaryCloseOut => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BrokerStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BrokerStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BrokerStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : BrokerStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : BrokerStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BrokerStatus

/-- Show Index: one byte code -/
def ShowIndex.codes : List UInt8 :=
  [0x54]

inductive ShowIndex where
  | trimNnfProtocol -- Trim Nnf Protocol
  | unlisted (byte : { byte : UInt8 // byte ∉ ShowIndex.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ShowIndex

def toByte : ShowIndex → UInt8
  | .trimNnfProtocol => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : ShowIndex :=
  .trimNnfProtocol

def ofByte (byte : UInt8) : ShowIndex :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ShowIndex) : ofByte value.toByte = value := by
  cases value with
  | trimNnfProtocol => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ShowIndex) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ShowIndex × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ShowIndex) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ShowIndex) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ShowIndex) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ShowIndex

/-- Clearing Status: one byte code -/
def ClearingStatus.codes : List UInt8 :=
  [0x41, 0x53, 0x44, 0x56]

inductive ClearingStatus where
  | active -- Active
  | suspended -- Suspended
  | deactivated -- Deactivated
  | voluntaryCloseOut -- Voluntary Close Out
  | unlisted (byte : { byte : UInt8 // byte ∉ ClearingStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ClearingStatus

def toByte : ClearingStatus → UInt8
  | .active => 0x41
  | .suspended => 0x53
  | .deactivated => 0x44
  | .voluntaryCloseOut => 0x56
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ClearingStatus :=
  if byte = 0x41 then .active
  else if byte = 0x53 then .suspended
  else if byte = 0x44 then .deactivated
  else .voluntaryCloseOut

def ofByte (byte : UInt8) : ClearingStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ClearingStatus) : ofByte value.toByte = value := by
  cases value with
  | active => decide
  | suspended => decide
  | deactivated => decide
  | voluntaryCloseOut => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ClearingStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ClearingStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ClearingStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ClearingStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ClearingStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ClearingStatus

/-- Request For Open Orders: one byte code -/
def RequestForOpenOrders.codes : List UInt8 :=
  [0x47, 0x4E]

inductive RequestForOpenOrders where
  | downloadGtcAndGtdOrders -- Download Gtc And Gtd Orders
  | noOpenOrders -- No Open Orders
  | unlisted (byte : { byte : UInt8 // byte ∉ RequestForOpenOrders.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RequestForOpenOrders

def toByte : RequestForOpenOrders → UInt8
  | .downloadGtcAndGtdOrders => 0x47
  | .noOpenOrders => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RequestForOpenOrders :=
  if byte = 0x47 then .downloadGtcAndGtdOrders
  else .noOpenOrders

def ofByte (byte : UInt8) : RequestForOpenOrders :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RequestForOpenOrders) : ofByte value.toByte = value := by
  cases value with
  | downloadGtcAndGtdOrders => decide
  | noOpenOrders => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RequestForOpenOrders) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RequestForOpenOrders × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RequestForOpenOrders) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : RequestForOpenOrders) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : RequestForOpenOrders) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RequestForOpenOrders

/-- Modified Cancelled By: one byte code -/
def ModifiedCancelledBy.codes : List UInt8 :=
  [0x54, 0x42, 0x4D, 0x43]

inductive ModifiedCancelledBy where
  | trader -- Trader
  | branchManager -- Branch Manager
  | corporateManager -- Corporate Manager
  | exchange -- Exchange
  | unlisted (byte : { byte : UInt8 // byte ∉ ModifiedCancelledBy.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ModifiedCancelledBy

def toByte : ModifiedCancelledBy → UInt8
  | .trader => 0x54
  | .branchManager => 0x42
  | .corporateManager => 0x4D
  | .exchange => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ModifiedCancelledBy :=
  if byte = 0x54 then .trader
  else if byte = 0x42 then .branchManager
  else if byte = 0x4D then .corporateManager
  else .exchange

def ofByte (byte : UInt8) : ModifiedCancelledBy :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ModifiedCancelledBy) : ofByte value.toByte = value := by
  cases value with
  | trader => decide
  | branchManager => decide
  | corporateManager => decide
  | exchange => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ModifiedCancelledBy) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ModifiedCancelledBy × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ModifiedCancelledBy) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ModifiedCancelledBy) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ModifiedCancelledBy) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ModifiedCancelledBy

/-- Open Close: one byte code -/
def OpenClose.codes : List UInt8 :=
  [0x4F, 0x43]

inductive OpenClose where
  | open_ -- Open
  | close -- Close
  | unlisted (byte : { byte : UInt8 // byte ∉ OpenClose.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OpenClose

def toByte : OpenClose → UInt8
  | .open_ => 0x4F
  | .close => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OpenClose :=
  if byte = 0x4F then .open_
  else .close

def ofByte (byte : UInt8) : OpenClose :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OpenClose) : ofByte value.toByte = value := by
  cases value with
  | open_ => decide
  | close => decide
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

/-- Mkt Type: one byte code -/
def MktType.codes : List UInt8 :=
  [0x31, 0x32, 0x33, 0x34]

inductive MktType where
  | normalMarket -- Normal Market
  | oddLotMarket -- Odd Lot Market
  | spotMarket -- Spot Market
  | auctionMarket -- Auction Market
  | unlisted (byte : { byte : UInt8 // byte ∉ MktType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MktType

def toByte : MktType → UInt8
  | .normalMarket => 0x31
  | .oddLotMarket => 0x32
  | .spotMarket => 0x33
  | .auctionMarket => 0x34
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MktType :=
  if byte = 0x31 then .normalMarket
  else if byte = 0x32 then .oddLotMarket
  else if byte = 0x33 then .spotMarket
  else .auctionMarket

def ofByte (byte : UInt8) : MktType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MktType) : ofByte value.toByte = value := by
  cases value with
  | normalMarket => decide
  | oddLotMarket => decide
  | spotMarket => decide
  | auctionMarket => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MktType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MktType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MktType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : MktType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : MktType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MktType

/-- Buy Open Close: one byte code -/
def BuyOpenClose.codes : List UInt8 :=
  [0x4F, 0x43]

inductive BuyOpenClose where
  | open_ -- Open
  | close -- Close
  | unlisted (byte : { byte : UInt8 // byte ∉ BuyOpenClose.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BuyOpenClose

def toByte : BuyOpenClose → UInt8
  | .open_ => 0x4F
  | .close => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BuyOpenClose :=
  if byte = 0x4F then .open_
  else .close

def ofByte (byte : UInt8) : BuyOpenClose :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BuyOpenClose) : ofByte value.toByte = value := by
  cases value with
  | open_ => decide
  | close => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BuyOpenClose) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BuyOpenClose × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BuyOpenClose) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : BuyOpenClose) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : BuyOpenClose) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BuyOpenClose

/-- Requested By: one byte code -/
def RequestedBy.codes : List UInt8 :=
  [0x31, 0x32, 0x33]

inductive RequestedBy where
  | buy -- Buy
  | sell -- Sell
  | both -- Both
  | unlisted (byte : { byte : UInt8 // byte ∉ RequestedBy.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RequestedBy

def toByte : RequestedBy → UInt8
  | .buy => 0x31
  | .sell => 0x32
  | .both => 0x33
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RequestedBy :=
  if byte = 0x31 then .buy
  else if byte = 0x32 then .sell
  else .both

def ofByte (byte : UInt8) : RequestedBy :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RequestedBy) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | both => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RequestedBy) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RequestedBy × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RequestedBy) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : RequestedBy) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : RequestedBy) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RequestedBy

/-- Sell Open Close: one byte code -/
def SellOpenClose.codes : List UInt8 :=
  [0x4F, 0x43]

inductive SellOpenClose where
  | open_ -- Open
  | close -- Close
  | unlisted (byte : { byte : UInt8 // byte ∉ SellOpenClose.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SellOpenClose

def toByte : SellOpenClose → UInt8
  | .open_ => 0x4F
  | .close => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SellOpenClose :=
  if byte = 0x4F then .open_
  else .close

def ofByte (byte : UInt8) : SellOpenClose :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SellOpenClose) : ofByte value.toByte = value := by
  cases value with
  | open_ => decide
  | close => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SellOpenClose) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SellOpenClose × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SellOpenClose) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SellOpenClose) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SellOpenClose) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SellOpenClose

/-- Col User Bit: one byte code -/
def ColUserBit.codes : List UInt8 :=
  [0x30, 0x31]

inductive ColUserBit where
  | disableColStatus -- Disable Col Status
  | enableColStatus -- Enable Col Status
  | unlisted (byte : { byte : UInt8 // byte ∉ ColUserBit.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ColUserBit

def toByte : ColUserBit → UInt8
  | .disableColStatus => 0x30
  | .enableColStatus => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ColUserBit :=
  if byte = 0x30 then .disableColStatus
  else .enableColStatus

def ofByte (byte : UInt8) : ColUserBit :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ColUserBit) : ofByte value.toByte = value := by
  cases value with
  | disableColStatus => decide
  | enableColStatus => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ColUserBit) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ColUserBit × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ColUserBit) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ColUserBit) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ColUserBit) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ColUserBit

/-- Trd Mod Cxl Bit: one byte code -/
def TrdModCxlBit.codes : List UInt8 :=
  [0x59, 0x4E]

inductive TrdModCxlBit where
  | enable -- Enable
  | disable -- Disable
  | unlisted (byte : { byte : UInt8 // byte ∉ TrdModCxlBit.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TrdModCxlBit

def toByte : TrdModCxlBit → UInt8
  | .enable => 0x59
  | .disable => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TrdModCxlBit :=
  if byte = 0x59 then .enable
  else .disable

def ofByte (byte : UInt8) : TrdModCxlBit :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TrdModCxlBit) : ofByte value.toByte = value := by
  cases value with
  | enable => decide
  | disable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TrdModCxlBit) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TrdModCxlBit × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TrdModCxlBit) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TrdModCxlBit) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TrdModCxlBit) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TrdModCxlBit

/-- Sign On Request In Message: 174 bytes -/
structure SignOnRequestInMessage where
  userId : BitVec 32
  password : Alpha 8
  newPassword : Alpha 8
  traderName : Alpha 26
  lastPasswordChangeDate : BitVec 32
  brokerId : Alpha 5
  reserved1 : Alpha 1
  branchId : BitVec 16
  versionNumber : BitVec 32
  batch2StartTime : BitVec 32
  hostSwitchContext : Alpha 1
  colour : Alpha 50
  secondReserved1 : Alpha 1
  userType : BitVec 16
  sequenceNumber : Alpha 8
  wsClassName : Alpha 14
  brokerStatus : BrokerStatus
  showIndex : ShowIndex
  stBrokerEligibilityPerMkt : BitVec 16
  memberType : BitVec 16
  clearingStatus : ClearingStatus
  brokerName : Alpha 25
  deriving DecidableEq, Repr

namespace SignOnRequestInMessage

def encode (message : SignOnRequestInMessage) : List UInt8 :=
  encodeUInt 4 message.userId
    ++ (Alpha.encode message.password
    ++ (Alpha.encode message.newPassword
    ++ (Alpha.encode message.traderName
    ++ (encodeUInt 4 message.lastPasswordChangeDate
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.branchId
    ++ (encodeUInt 4 message.versionNumber
    ++ (encodeUInt 4 message.batch2StartTime
    ++ (Alpha.encode message.hostSwitchContext
    ++ (Alpha.encode message.colour
    ++ (Alpha.encode message.secondReserved1
    ++ (encodeUInt 2 message.userType
    ++ (Alpha.encode message.sequenceNumber
    ++ (Alpha.encode message.wsClassName
    ++ (BrokerStatus.encode message.brokerStatus
    ++ (ShowIndex.encode message.showIndex
    ++ (encodeUInt 2 message.stBrokerEligibilityPerMkt
    ++ (encodeUInt 2 message.memberType
    ++ (ClearingStatus.encode message.clearingStatus
    ++ (Alpha.encode message.brokerName)))))))))))))))))))))

def decode (bytes : List UInt8) : Option (SignOnRequestInMessage × List UInt8) := do
  let (userId, bytes) ← decodeUInt 4 bytes
  let (password, bytes) ← Alpha.decode 8 bytes
  let (newPassword, bytes) ← Alpha.decode 8 bytes
  let (traderName, bytes) ← Alpha.decode 26 bytes
  let (lastPasswordChangeDate, bytes) ← decodeUInt 4 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (branchId, bytes) ← decodeUInt 2 bytes
  let (versionNumber, bytes) ← decodeUInt 4 bytes
  let (batch2StartTime, bytes) ← decodeUInt 4 bytes
  let (hostSwitchContext, bytes) ← Alpha.decode 1 bytes
  let (colour, bytes) ← Alpha.decode 50 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  let (userType, bytes) ← decodeUInt 2 bytes
  let (sequenceNumber, bytes) ← Alpha.decode 8 bytes
  let (wsClassName, bytes) ← Alpha.decode 14 bytes
  let (brokerStatus, bytes) ← BrokerStatus.decode bytes
  let (showIndex, bytes) ← ShowIndex.decode bytes
  let (stBrokerEligibilityPerMkt, bytes) ← decodeUInt 2 bytes
  let (memberType, bytes) ← decodeUInt 2 bytes
  let (clearingStatus, bytes) ← ClearingStatus.decode bytes
  let (brokerName, bytes) ← Alpha.decode 25 bytes
  pure ({ userId, password, newPassword, traderName, lastPasswordChangeDate, brokerId, reserved1, branchId, versionNumber, batch2StartTime, hostSwitchContext, colour, secondReserved1, userType, sequenceNumber, wsClassName, brokerStatus, showIndex, stBrokerEligibilityPerMkt, memberType, clearingStatus, brokerName }, bytes)

@[simp] theorem encode_length (message : SignOnRequestInMessage) : (encode message).length = 174 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, BrokerStatus.encode_length, ShowIndex.encode_length, ClearingStatus.encode_length]

theorem encode_length_pos (message : SignOnRequestInMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SignOnRequestInMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BrokerStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ShowIndex.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ClearingStatus.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SignOnRequestInMessage

/-- Sign Off Request In Message: 0 bytes -/
structure SignOffRequestInMessage where
  deriving DecidableEq, Repr

namespace SignOffRequestInMessage

def encode (_ : SignOffRequestInMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (SignOffRequestInMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : SignOffRequestInMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : SignOffRequestInMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end SignOffRequestInMessage

/-- System Information In Message: 4 bytes -/
structure SystemInformationInMessage where
  lastUpdatePortfolioTime : BitVec 32
  deriving DecidableEq, Repr

namespace SystemInformationInMessage

def encode (message : SystemInformationInMessage) : List UInt8 :=
  encodeUInt 4 message.lastUpdatePortfolioTime

def decode (bytes : List UInt8) : Option (SystemInformationInMessage × List UInt8) := do
  let (lastUpdatePortfolioTime, bytes) ← decodeUInt 4 bytes
  pure ({ lastUpdatePortfolioTime }, bytes)

@[simp] theorem encode_length (message : SystemInformationInMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : SystemInformationInMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemInformationInMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SystemInformationInMessage

/-- St Market Status: 8 bytes -/
structure StMarketStatus where
  normal : BitVec 16
  oddlot : BitVec 16
  spot : BitVec 16
  auction : BitVec 16
  deriving DecidableEq, Repr

namespace StMarketStatus

def encode (message : StMarketStatus) : List UInt8 :=
  encodeUInt 2 message.normal
    ++ (encodeUInt 2 message.oddlot
    ++ (encodeUInt 2 message.spot
    ++ (encodeUInt 2 message.auction)))

def decode (bytes : List UInt8) : Option (StMarketStatus × List UInt8) := do
  let (normal, bytes) ← decodeUInt 2 bytes
  let (oddlot, bytes) ← decodeUInt 2 bytes
  let (spot, bytes) ← decodeUInt 2 bytes
  let (auction, bytes) ← decodeUInt 2 bytes
  pure ({ normal, oddlot, spot, auction }, bytes)

@[simp] theorem encode_length (message : StMarketStatus) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : StMarketStatus) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StMarketStatus) (rest : List UInt8) :
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

end StMarketStatus

/-- St Ex Market Status: 8 bytes -/
structure StExMarketStatus where
  normal : BitVec 16
  oddlot : BitVec 16
  spot : BitVec 16
  auction : BitVec 16
  deriving DecidableEq, Repr

namespace StExMarketStatus

def encode (message : StExMarketStatus) : List UInt8 :=
  encodeUInt 2 message.normal
    ++ (encodeUInt 2 message.oddlot
    ++ (encodeUInt 2 message.spot
    ++ (encodeUInt 2 message.auction)))

def decode (bytes : List UInt8) : Option (StExMarketStatus × List UInt8) := do
  let (normal, bytes) ← decodeUInt 2 bytes
  let (oddlot, bytes) ← decodeUInt 2 bytes
  let (spot, bytes) ← decodeUInt 2 bytes
  let (auction, bytes) ← decodeUInt 2 bytes
  pure ({ normal, oddlot, spot, auction }, bytes)

@[simp] theorem encode_length (message : StExMarketStatus) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : StExMarketStatus) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StExMarketStatus) (rest : List UInt8) :
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

end StExMarketStatus

/-- St Pl Market Status: 8 bytes -/
structure StPlMarketStatus where
  normal : BitVec 16
  oddlot : BitVec 16
  spot : BitVec 16
  auction : BitVec 16
  deriving DecidableEq, Repr

namespace StPlMarketStatus

def encode (message : StPlMarketStatus) : List UInt8 :=
  encodeUInt 2 message.normal
    ++ (encodeUInt 2 message.oddlot
    ++ (encodeUInt 2 message.spot
    ++ (encodeUInt 2 message.auction)))

def decode (bytes : List UInt8) : Option (StPlMarketStatus × List UInt8) := do
  let (normal, bytes) ← decodeUInt 2 bytes
  let (oddlot, bytes) ← decodeUInt 2 bytes
  let (spot, bytes) ← decodeUInt 2 bytes
  let (auction, bytes) ← decodeUInt 2 bytes
  pure ({ normal, oddlot, spot, auction }, bytes)

@[simp] theorem encode_length (message : StPlMarketStatus) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : StPlMarketStatus) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StPlMarketStatus) (rest : List UInt8) :
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

end StPlMarketStatus

/-- Update Local Database In Message: 42 bytes -/
structure UpdateLocalDatabaseInMessage where
  lastUpdateSecurityTime : BitVec 32
  lastUpdateParticipantTime : BitVec 32
  lastUpdateInstrumentTime : BitVec 32
  lastUpdateIndexTime : BitVec 32
  requestForOpenOrders : RequestForOpenOrders
  cFiller : Alpha 1
  stMarketStatus : StMarketStatus
  stExMarketStatus : StExMarketStatus
  stPlMarketStatus : StPlMarketStatus
  deriving DecidableEq, Repr

namespace UpdateLocalDatabaseInMessage

def encode (message : UpdateLocalDatabaseInMessage) : List UInt8 :=
  encodeUInt 4 message.lastUpdateSecurityTime
    ++ (encodeUInt 4 message.lastUpdateParticipantTime
    ++ (encodeUInt 4 message.lastUpdateInstrumentTime
    ++ (encodeUInt 4 message.lastUpdateIndexTime
    ++ (RequestForOpenOrders.encode message.requestForOpenOrders
    ++ (Alpha.encode message.cFiller
    ++ (StMarketStatus.encode message.stMarketStatus
    ++ (StExMarketStatus.encode message.stExMarketStatus
    ++ (StPlMarketStatus.encode message.stPlMarketStatus))))))))

def decode (bytes : List UInt8) : Option (UpdateLocalDatabaseInMessage × List UInt8) := do
  let (lastUpdateSecurityTime, bytes) ← decodeUInt 4 bytes
  let (lastUpdateParticipantTime, bytes) ← decodeUInt 4 bytes
  let (lastUpdateInstrumentTime, bytes) ← decodeUInt 4 bytes
  let (lastUpdateIndexTime, bytes) ← decodeUInt 4 bytes
  let (requestForOpenOrders, bytes) ← RequestForOpenOrders.decode bytes
  let (cFiller, bytes) ← Alpha.decode 1 bytes
  let (stMarketStatus, bytes) ← StMarketStatus.decode bytes
  let (stExMarketStatus, bytes) ← StExMarketStatus.decode bytes
  let (stPlMarketStatus, bytes) ← StPlMarketStatus.decode bytes
  pure ({ lastUpdateSecurityTime, lastUpdateParticipantTime, lastUpdateInstrumentTime, lastUpdateIndexTime, requestForOpenOrders, cFiller, stMarketStatus, stExMarketStatus, stPlMarketStatus }, bytes)

@[simp] theorem encode_length (message : UpdateLocalDatabaseInMessage) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, RequestForOpenOrders.encode_length, Alpha.encode_length, StMarketStatus.encode_length, StExMarketStatus.encode_length, StPlMarketStatus.encode_length]

theorem encode_length_pos (message : UpdateLocalDatabaseInMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UpdateLocalDatabaseInMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, RequestForOpenOrders.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StMarketStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StExMarketStatus.decode_encode, some_bind]
  dsimp only
  rw [StPlMarketStatus.decode_encode, some_bind]
  rfl

end UpdateLocalDatabaseInMessage

/-- Download Request Message: 8 bytes -/
structure DownloadRequestMessage where
  sequenceNumber : Alpha 8
  deriving DecidableEq, Repr

namespace DownloadRequestMessage

def encode (message : DownloadRequestMessage) : List UInt8 :=
  Alpha.encode message.sequenceNumber

def decode (bytes : List UInt8) : Option (DownloadRequestMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ sequenceNumber }, bytes)

@[simp] theorem encode_length (message : DownloadRequestMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : DownloadRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DownloadRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end DownloadRequestMessage

/-- Contract Desc: 28 bytes -/
structure ContractDesc where
  instrumentName : Alpha 6
  symbol : Alpha 10
  expiryDate : BitVec 32
  strikePrice : BitVec 32
  optionType : Alpha 2
  caLevel : BitVec 16
  deriving DecidableEq, Repr

namespace ContractDesc

def encode (message : ContractDesc) : List UInt8 :=
  Alpha.encode message.instrumentName
    ++ (Alpha.encode message.symbol
    ++ (encodeUInt 4 message.expiryDate
    ++ (encodeUInt 4 message.strikePrice
    ++ (Alpha.encode message.optionType
    ++ (encodeUInt 2 message.caLevel)))))

def decode (bytes : List UInt8) : Option (ContractDesc × List UInt8) := do
  let (instrumentName, bytes) ← Alpha.decode 6 bytes
  let (symbol, bytes) ← Alpha.decode 10 bytes
  let (expiryDate, bytes) ← decodeUInt 4 bytes
  let (strikePrice, bytes) ← decodeUInt 4 bytes
  let (optionType, bytes) ← Alpha.decode 2 bytes
  let (caLevel, bytes) ← decodeUInt 2 bytes
  pure ({ instrumentName, symbol, expiryDate, strikePrice, optionType, caLevel }, bytes)

@[simp] theorem encode_length (message : ContractDesc) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ContractDesc) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ContractDesc) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ContractDesc

/-- Order Entry Body: 276 bytes -/
structure OrderEntryBody where
  participantType : Alpha 1
  reserved1 : Alpha 1
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  modifiedCancelledBy : ModifiedCancelledBy
  secondReserved1 : Alpha 1
  reasonCode : BitVec 16
  reserved4 : Alpha 4
  tokenNo : BitVec 32
  contractDesc : ContractDesc
  counterPartyBrokerId : Alpha 5
  thirdReserved1 : Alpha 1
  reserved2 : Alpha 2
  closeoutFlag : Alpha 1
  fourthReserved1 : Alpha 1
  orderType : BitVec 16
  orderNumber : Alpha 8
  accountNumber : Alpha 10
  bookType : BitVec 16
  buySellIndicator : BitVec 16
  disclosedVolume : BitVec 32
  disclosedVolumeRemaining : BitVec 32
  totalVolumeRemaining : BitVec 32
  volume : BitVec 32
  volumeFilledToday : BitVec 32
  price : BitVec 32
  triggerPrice : BitVec 32
  goodTillDate : BitVec 32
  entryDateTime : BitVec 32
  minimumFillAonVolume : BitVec 32
  lastModified : BitVec 32
  stOrderFlags : BitVec 16
  branchId : BitVec 16
  traderId : BitVec 32
  brokerId : Alpha 5
  cOrdFiller : Alpha 24
  openClose : OpenClose
  settlor : Alpha 12
  proClientIndicator : BitVec 16
  settlementPeriod : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag : Alpha 1
  reference : Alpha 4
  nnfField : Alpha 8
  mktReplay : Alpha 8
  echoBack : Alpha 16
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  deriving DecidableEq, Repr

namespace OrderEntryBody

def encode (message : OrderEntryBody) : List UInt8 :=
  Alpha.encode message.participantType
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (ModifiedCancelledBy.encode message.modifiedCancelledBy
    ++ (Alpha.encode message.secondReserved1
    ++ (encodeUInt 2 message.reasonCode
    ++ (Alpha.encode message.reserved4
    ++ (encodeUInt 4 message.tokenNo
    ++ (ContractDesc.encode message.contractDesc
    ++ (Alpha.encode message.counterPartyBrokerId
    ++ (Alpha.encode message.thirdReserved1
    ++ (Alpha.encode message.reserved2
    ++ (Alpha.encode message.closeoutFlag
    ++ (Alpha.encode message.fourthReserved1
    ++ (encodeUInt 2 message.orderType
    ++ (Alpha.encode message.orderNumber
    ++ (Alpha.encode message.accountNumber
    ++ (encodeUInt 2 message.bookType
    ++ (encodeUInt 2 message.buySellIndicator
    ++ (encodeUInt 4 message.disclosedVolume
    ++ (encodeUInt 4 message.disclosedVolumeRemaining
    ++ (encodeUInt 4 message.totalVolumeRemaining
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 4 message.volumeFilledToday
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.triggerPrice
    ++ (encodeUInt 4 message.goodTillDate
    ++ (encodeUInt 4 message.entryDateTime
    ++ (encodeUInt 4 message.minimumFillAonVolume
    ++ (encodeUInt 4 message.lastModified
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId
    ++ (encodeUInt 4 message.traderId
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.cOrdFiller
    ++ (OpenClose.encode message.openClose
    ++ (Alpha.encode message.settlor
    ++ (encodeUInt 2 message.proClientIndicator
    ++ (encodeUInt 2 message.settlementPeriod
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag
    ++ (Alpha.encode message.reference
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.mktReplay
    ++ (Alpha.encode message.echoBack
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52)))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderEntryBody × List UInt8) := do
  let (participantType, bytes) ← Alpha.decode 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (modifiedCancelledBy, bytes) ← ModifiedCancelledBy.decode bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  let (reasonCode, bytes) ← decodeUInt 2 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (tokenNo, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (counterPartyBrokerId, bytes) ← Alpha.decode 5 bytes
  let (thirdReserved1, bytes) ← Alpha.decode 1 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (closeoutFlag, bytes) ← Alpha.decode 1 bytes
  let (fourthReserved1, bytes) ← Alpha.decode 1 bytes
  let (orderType, bytes) ← decodeUInt 2 bytes
  let (orderNumber, bytes) ← Alpha.decode 8 bytes
  let (accountNumber, bytes) ← Alpha.decode 10 bytes
  let (bookType, bytes) ← decodeUInt 2 bytes
  let (buySellIndicator, bytes) ← decodeUInt 2 bytes
  let (disclosedVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolumeRemaining, bytes) ← decodeUInt 4 bytes
  let (totalVolumeRemaining, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (triggerPrice, bytes) ← decodeUInt 4 bytes
  let (goodTillDate, bytes) ← decodeUInt 4 bytes
  let (entryDateTime, bytes) ← decodeUInt 4 bytes
  let (minimumFillAonVolume, bytes) ← decodeUInt 4 bytes
  let (lastModified, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId, bytes) ← decodeUInt 2 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (cOrdFiller, bytes) ← Alpha.decode 24 bytes
  let (openClose, bytes) ← OpenClose.decode bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  let (proClientIndicator, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 4 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← Alpha.decode 8 bytes
  let (echoBack, bytes) ← Alpha.decode 16 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  pure ({ participantType, reserved1, competitorPeriod, solicitorPeriod, modifiedCancelledBy, secondReserved1, reasonCode, reserved4, tokenNo, contractDesc, counterPartyBrokerId, thirdReserved1, reserved2, closeoutFlag, fourthReserved1, orderType, orderNumber, accountNumber, bookType, buySellIndicator, disclosedVolume, disclosedVolumeRemaining, totalVolumeRemaining, volume, volumeFilledToday, price, triggerPrice, goodTillDate, entryDateTime, minimumFillAonVolume, lastModified, stOrderFlags, branchId, traderId, brokerId, cOrdFiller, openClose, settlor, proClientIndicator, settlementPeriod, additionalOrderFlags, giveupFlag, reference, nnfField, mktReplay, echoBack, lastActivityReference, reserved52 }, bytes)

@[simp] theorem encode_length (message : OrderEntryBody) : (encode message).length = 276 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ModifiedCancelledBy.encode_length, ContractDesc.encode_length, OpenClose.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : OrderEntryBody) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OrderEntryBody) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ModifiedCancelledBy.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpenClose.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderEntryBody

/-- Order Entry Request Message: 276 bytes -/
structure OrderEntryRequestMessage where
  orderEntryBody : OrderEntryBody
  deriving DecidableEq, Repr

namespace OrderEntryRequestMessage

def encode (message : OrderEntryRequestMessage) : List UInt8 :=
  OrderEntryBody.encode message.orderEntryBody

def decode (bytes : List UInt8) : Option (OrderEntryRequestMessage × List UInt8) := do
  let (orderEntryBody, bytes) ← OrderEntryBody.decode bytes
  pure ({ orderEntryBody }, bytes)

@[simp] theorem encode_length (message : OrderEntryRequestMessage) : (encode message).length = 276 := by
  unfold encode
  simp only [OrderEntryBody.encode_length]

theorem encode_length_pos (message : OrderEntryRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderEntryRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [OrderEntryBody.decode_encode, some_bind]
  rfl

end OrderEntryRequestMessage

/-- Order Modification Request Message: 276 bytes -/
structure OrderModificationRequestMessage where
  orderEntryBody : OrderEntryBody
  deriving DecidableEq, Repr

namespace OrderModificationRequestMessage

def encode (message : OrderModificationRequestMessage) : List UInt8 :=
  OrderEntryBody.encode message.orderEntryBody

def decode (bytes : List UInt8) : Option (OrderModificationRequestMessage × List UInt8) := do
  let (orderEntryBody, bytes) ← OrderEntryBody.decode bytes
  pure ({ orderEntryBody }, bytes)

@[simp] theorem encode_length (message : OrderModificationRequestMessage) : (encode message).length = 276 := by
  unfold encode
  simp only [OrderEntryBody.encode_length]

theorem encode_length_pos (message : OrderModificationRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderModificationRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [OrderEntryBody.decode_encode, some_bind]
  rfl

end OrderModificationRequestMessage

/-- Order Cancellation Request Message: 276 bytes -/
structure OrderCancellationRequestMessage where
  orderEntryBody : OrderEntryBody
  deriving DecidableEq, Repr

namespace OrderCancellationRequestMessage

def encode (message : OrderCancellationRequestMessage) : List UInt8 :=
  OrderEntryBody.encode message.orderEntryBody

def decode (bytes : List UInt8) : Option (OrderCancellationRequestMessage × List UInt8) := do
  let (orderEntryBody, bytes) ← OrderEntryBody.decode bytes
  pure ({ orderEntryBody }, bytes)

@[simp] theorem encode_length (message : OrderCancellationRequestMessage) : (encode message).length = 276 := by
  unfold encode
  simp only [OrderEntryBody.encode_length]

theorem encode_length_pos (message : OrderCancellationRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancellationRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [OrderEntryBody.decode_encode, some_bind]
  rfl

end OrderCancellationRequestMessage

/-- Kill Switch Request Message: 276 bytes -/
structure KillSwitchRequestMessage where
  orderEntryBody : OrderEntryBody
  deriving DecidableEq, Repr

namespace KillSwitchRequestMessage

def encode (message : KillSwitchRequestMessage) : List UInt8 :=
  OrderEntryBody.encode message.orderEntryBody

def decode (bytes : List UInt8) : Option (KillSwitchRequestMessage × List UInt8) := do
  let (orderEntryBody, bytes) ← OrderEntryBody.decode bytes
  pure ({ orderEntryBody }, bytes)

@[simp] theorem encode_length (message : KillSwitchRequestMessage) : (encode message).length = 276 := by
  unfold encode
  simp only [OrderEntryBody.encode_length]

theorem encode_length_pos (message : KillSwitchRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : KillSwitchRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [OrderEntryBody.decode_encode, some_bind]
  rfl

end KillSwitchRequestMessage

/-- Price Modification Message: 66 bytes -/
structure PriceModificationMessage where
  tokenNo : BitVec 32
  traderId : BitVec 32
  orderNumber : Alpha 8
  buySell : BitVec 16
  price : BitVec 32
  volume : BitVec 32
  lastModified : BitVec 32
  reference : Alpha 4
  lastActivityReference : BitVec 64
  reserved24 : Alpha 24
  deriving DecidableEq, Repr

namespace PriceModificationMessage

def encode (message : PriceModificationMessage) : List UInt8 :=
  encodeUInt 4 message.tokenNo
    ++ (encodeUInt 4 message.traderId
    ++ (Alpha.encode message.orderNumber
    ++ (encodeUInt 2 message.buySell
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 4 message.lastModified
    ++ (Alpha.encode message.reference
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved24)))))))))

def decode (bytes : List UInt8) : Option (PriceModificationMessage × List UInt8) := do
  let (tokenNo, bytes) ← decodeUInt 4 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (orderNumber, bytes) ← Alpha.decode 8 bytes
  let (buySell, bytes) ← decodeUInt 2 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (lastModified, bytes) ← decodeUInt 4 bytes
  let (reference, bytes) ← Alpha.decode 4 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved24, bytes) ← Alpha.decode 24 bytes
  pure ({ tokenNo, traderId, orderNumber, buySell, price, volume, lastModified, reference, lastActivityReference, reserved24 }, bytes)

@[simp] theorem encode_length (message : PriceModificationMessage) : (encode message).length = 66 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : PriceModificationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PriceModificationMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end PriceModificationMessage

/-- Trade Inquiry Body: 194 bytes -/
structure TradeInquiryBody where
  tokenNo : BitVec 32
  contractDesc : ContractDesc
  fillNumber : BitVec 32
  fillQuantity : BitVec 32
  fillPrice : BitVec 32
  mktType : MktType
  buyOpenClose : BuyOpenClose
  newVolume : BitVec 32
  buyBrokerId : Alpha 5
  sellBrokerId : Alpha 5
  traderId : BitVec 32
  requestedBy : RequestedBy
  sellOpenClose : SellOpenClose
  buyAccountNumber : Alpha 10
  sellAccountNumber : Alpha 10
  buyParticipant : Alpha 12
  sellParticipant : Alpha 12
  reserved2 : Alpha 2
  buyGiveupFlag : Alpha 1
  sellGiveupFlag : Alpha 1
  reserved80 : Alpha 80
  deriving DecidableEq, Repr

namespace TradeInquiryBody

def encode (message : TradeInquiryBody) : List UInt8 :=
  encodeUInt 4 message.tokenNo
    ++ (ContractDesc.encode message.contractDesc
    ++ (encodeUInt 4 message.fillNumber
    ++ (encodeUInt 4 message.fillQuantity
    ++ (encodeUInt 4 message.fillPrice
    ++ (MktType.encode message.mktType
    ++ (BuyOpenClose.encode message.buyOpenClose
    ++ (encodeUInt 4 message.newVolume
    ++ (Alpha.encode message.buyBrokerId
    ++ (Alpha.encode message.sellBrokerId
    ++ (encodeUInt 4 message.traderId
    ++ (RequestedBy.encode message.requestedBy
    ++ (SellOpenClose.encode message.sellOpenClose
    ++ (Alpha.encode message.buyAccountNumber
    ++ (Alpha.encode message.sellAccountNumber
    ++ (Alpha.encode message.buyParticipant
    ++ (Alpha.encode message.sellParticipant
    ++ (Alpha.encode message.reserved2
    ++ (Alpha.encode message.buyGiveupFlag
    ++ (Alpha.encode message.sellGiveupFlag
    ++ (Alpha.encode message.reserved80))))))))))))))))))))

def decode (bytes : List UInt8) : Option (TradeInquiryBody × List UInt8) := do
  let (tokenNo, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (fillNumber, bytes) ← decodeUInt 4 bytes
  let (fillQuantity, bytes) ← decodeUInt 4 bytes
  let (fillPrice, bytes) ← decodeUInt 4 bytes
  let (mktType, bytes) ← MktType.decode bytes
  let (buyOpenClose, bytes) ← BuyOpenClose.decode bytes
  let (newVolume, bytes) ← decodeUInt 4 bytes
  let (buyBrokerId, bytes) ← Alpha.decode 5 bytes
  let (sellBrokerId, bytes) ← Alpha.decode 5 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (requestedBy, bytes) ← RequestedBy.decode bytes
  let (sellOpenClose, bytes) ← SellOpenClose.decode bytes
  let (buyAccountNumber, bytes) ← Alpha.decode 10 bytes
  let (sellAccountNumber, bytes) ← Alpha.decode 10 bytes
  let (buyParticipant, bytes) ← Alpha.decode 12 bytes
  let (sellParticipant, bytes) ← Alpha.decode 12 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (buyGiveupFlag, bytes) ← Alpha.decode 1 bytes
  let (sellGiveupFlag, bytes) ← Alpha.decode 1 bytes
  let (reserved80, bytes) ← Alpha.decode 80 bytes
  pure ({ tokenNo, contractDesc, fillNumber, fillQuantity, fillPrice, mktType, buyOpenClose, newVolume, buyBrokerId, sellBrokerId, traderId, requestedBy, sellOpenClose, buyAccountNumber, sellAccountNumber, buyParticipant, sellParticipant, reserved2, buyGiveupFlag, sellGiveupFlag, reserved80 }, bytes)

@[simp] theorem encode_length (message : TradeInquiryBody) : (encode message).length = 194 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, ContractDesc.encode_length, MktType.encode_length, BuyOpenClose.encode_length, Alpha.encode_length, RequestedBy.encode_length, SellOpenClose.encode_length]

theorem encode_length_pos (message : TradeInquiryBody) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeInquiryBody) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MktType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BuyOpenClose.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, RequestedBy.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SellOpenClose.decode_encode, some_bind]
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

end TradeInquiryBody

/-- Trade Inquiry Message: 194 bytes -/
structure TradeInquiryMessage where
  tradeInquiryBody : TradeInquiryBody
  deriving DecidableEq, Repr

namespace TradeInquiryMessage

def encode (message : TradeInquiryMessage) : List UInt8 :=
  TradeInquiryBody.encode message.tradeInquiryBody

def decode (bytes : List UInt8) : Option (TradeInquiryMessage × List UInt8) := do
  let (tradeInquiryBody, bytes) ← TradeInquiryBody.decode bytes
  pure ({ tradeInquiryBody }, bytes)

@[simp] theorem encode_length (message : TradeInquiryMessage) : (encode message).length = 194 := by
  unfold encode
  simp only [TradeInquiryBody.encode_length]

theorem encode_length_pos (message : TradeInquiryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeInquiryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [TradeInquiryBody.decode_encode, some_bind]
  rfl

end TradeInquiryMessage

/-- Ms Spd Leg Info: 80 bytes -/
structure MsSpdLegInfo where
  token2 : BitVec 32
  contractDesc : ContractDesc
  opBrokerId2 : Alpha 5
  fillerx2 : Alpha 1
  orderType2 : BitVec 16
  buySell2 : BitVec 16
  disclosedVol2 : BitVec 32
  disclosedVolRemaining2 : BitVec 32
  totalVolRemaining2 : BitVec 32
  volume2 : BitVec 32
  volumeFilledToday2 : BitVec 32
  price2 : BitVec 32
  triggerPrice2 : BitVec 32
  minFillAon2 : BitVec 32
  stOrderFlags : BitVec 16
  openClose2 : Alpha 1
  additionalOrderFlags : BitVec 8
  giveupFlag2 : Alpha 1
  fillerY : Alpha 1
  deriving DecidableEq, Repr

namespace MsSpdLegInfo

def encode (message : MsSpdLegInfo) : List UInt8 :=
  encodeUInt 4 message.token2
    ++ (ContractDesc.encode message.contractDesc
    ++ (Alpha.encode message.opBrokerId2
    ++ (Alpha.encode message.fillerx2
    ++ (encodeUInt 2 message.orderType2
    ++ (encodeUInt 2 message.buySell2
    ++ (encodeUInt 4 message.disclosedVol2
    ++ (encodeUInt 4 message.disclosedVolRemaining2
    ++ (encodeUInt 4 message.totalVolRemaining2
    ++ (encodeUInt 4 message.volume2
    ++ (encodeUInt 4 message.volumeFilledToday2
    ++ (encodeUInt 4 message.price2
    ++ (encodeUInt 4 message.triggerPrice2
    ++ (encodeUInt 4 message.minFillAon2
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (Alpha.encode message.openClose2
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag2
    ++ (Alpha.encode message.fillerY))))))))))))))))))

def decode (bytes : List UInt8) : Option (MsSpdLegInfo × List UInt8) := do
  let (token2, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (opBrokerId2, bytes) ← Alpha.decode 5 bytes
  let (fillerx2, bytes) ← Alpha.decode 1 bytes
  let (orderType2, bytes) ← decodeUInt 2 bytes
  let (buySell2, bytes) ← decodeUInt 2 bytes
  let (disclosedVol2, bytes) ← decodeUInt 4 bytes
  let (disclosedVolRemaining2, bytes) ← decodeUInt 4 bytes
  let (totalVolRemaining2, bytes) ← decodeUInt 4 bytes
  let (volume2, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday2, bytes) ← decodeUInt 4 bytes
  let (price2, bytes) ← decodeUInt 4 bytes
  let (triggerPrice2, bytes) ← decodeUInt 4 bytes
  let (minFillAon2, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (openClose2, bytes) ← Alpha.decode 1 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag2, bytes) ← Alpha.decode 1 bytes
  let (fillerY, bytes) ← Alpha.decode 1 bytes
  pure ({ token2, contractDesc, opBrokerId2, fillerx2, orderType2, buySell2, disclosedVol2, disclosedVolRemaining2, totalVolRemaining2, volume2, volumeFilledToday2, price2, triggerPrice2, minFillAon2, stOrderFlags, openClose2, additionalOrderFlags, giveupFlag2, fillerY }, bytes)

@[simp] theorem encode_length (message : MsSpdLegInfo) : (encode message).length = 80 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, ContractDesc.encode_length, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : MsSpdLegInfo) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MsSpdLegInfo) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MsSpdLegInfo

/-- Spread Order Body: 440 bytes -/
structure SpreadOrderBody where
  participantType1 : Alpha 1
  filler1 : Alpha 1
  competitorPeriod1 : BitVec 16
  solicitorPeriod1 : BitVec 16
  modCxlBy1 : Alpha 1
  filler9 : Alpha 1
  reasonCode1 : BitVec 16
  startAlpha1 : Alpha 2
  endAlpha1 : Alpha 2
  token1 : BitVec 32
  contractDesc : ContractDesc
  opBrokerId1 : Alpha 5
  fillerx1 : Alpha 1
  fillerOptions1 : Alpha 3
  fillery1 : Alpha 1
  orderType1 : BitVec 16
  orderNumber1 : Alpha 8
  accountNumber1 : Alpha 10
  bookType1 : BitVec 16
  buySell1 : BitVec 16
  disclosedVol1 : BitVec 32
  disclosedVolRemaining1 : BitVec 32
  totalVolRemaining1 : BitVec 32
  volume1 : BitVec 32
  volumeFilledToday1 : BitVec 32
  price1 : BitVec 32
  triggerPrice1 : BitVec 32
  goodTillDate1 : BitVec 32
  entryDateTime1 : BitVec 32
  minFillAon1 : BitVec 32
  lastModified1 : BitVec 32
  stOrderFlags : BitVec 16
  branchId1 : BitVec 16
  traderId1 : BitVec 32
  brokerId1 : Alpha 5
  cOrdFiller : Alpha 24
  openClose1 : Alpha 1
  settlor1 : Alpha 12
  proClient1 : BitVec 16
  settlementPeriod1 : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag1 : Alpha 1
  filler116 : Alpha 2
  filler17 : Alpha 1
  filler18 : Alpha 1
  nnfField : Alpha 8
  mktReplay : Alpha 8
  echoBack : Alpha 16
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  priceDiff : BitVec 32
  msSpdLegInfo : Exact 2 MsSpdLegInfo
  deriving DecidableEq, Repr

namespace SpreadOrderBody

def encode (message : SpreadOrderBody) : List UInt8 :=
  Alpha.encode message.participantType1
    ++ (Alpha.encode message.filler1
    ++ (encodeUInt 2 message.competitorPeriod1
    ++ (encodeUInt 2 message.solicitorPeriod1
    ++ (Alpha.encode message.modCxlBy1
    ++ (Alpha.encode message.filler9
    ++ (encodeUInt 2 message.reasonCode1
    ++ (Alpha.encode message.startAlpha1
    ++ (Alpha.encode message.endAlpha1
    ++ (encodeUInt 4 message.token1
    ++ (ContractDesc.encode message.contractDesc
    ++ (Alpha.encode message.opBrokerId1
    ++ (Alpha.encode message.fillerx1
    ++ (Alpha.encode message.fillerOptions1
    ++ (Alpha.encode message.fillery1
    ++ (encodeUInt 2 message.orderType1
    ++ (Alpha.encode message.orderNumber1
    ++ (Alpha.encode message.accountNumber1
    ++ (encodeUInt 2 message.bookType1
    ++ (encodeUInt 2 message.buySell1
    ++ (encodeUInt 4 message.disclosedVol1
    ++ (encodeUInt 4 message.disclosedVolRemaining1
    ++ (encodeUInt 4 message.totalVolRemaining1
    ++ (encodeUInt 4 message.volume1
    ++ (encodeUInt 4 message.volumeFilledToday1
    ++ (encodeUInt 4 message.price1
    ++ (encodeUInt 4 message.triggerPrice1
    ++ (encodeUInt 4 message.goodTillDate1
    ++ (encodeUInt 4 message.entryDateTime1
    ++ (encodeUInt 4 message.minFillAon1
    ++ (encodeUInt 4 message.lastModified1
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId1
    ++ (encodeUInt 4 message.traderId1
    ++ (Alpha.encode message.brokerId1
    ++ (Alpha.encode message.cOrdFiller
    ++ (Alpha.encode message.openClose1
    ++ (Alpha.encode message.settlor1
    ++ (encodeUInt 2 message.proClient1
    ++ (encodeUInt 2 message.settlementPeriod1
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag1
    ++ (Alpha.encode message.filler116
    ++ (Alpha.encode message.filler17
    ++ (Alpha.encode message.filler18
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.mktReplay
    ++ (Alpha.encode message.echoBack
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52
    ++ (encodeUInt 4 message.priceDiff
    ++ (encodeMany MsSpdLegInfo.encode message.msSpdLegInfo.val)))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SpreadOrderBody × List UInt8) := do
  let (participantType1, bytes) ← Alpha.decode 1 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod1, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod1, bytes) ← decodeUInt 2 bytes
  let (modCxlBy1, bytes) ← Alpha.decode 1 bytes
  let (filler9, bytes) ← Alpha.decode 1 bytes
  let (reasonCode1, bytes) ← decodeUInt 2 bytes
  let (startAlpha1, bytes) ← Alpha.decode 2 bytes
  let (endAlpha1, bytes) ← Alpha.decode 2 bytes
  let (token1, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (opBrokerId1, bytes) ← Alpha.decode 5 bytes
  let (fillerx1, bytes) ← Alpha.decode 1 bytes
  let (fillerOptions1, bytes) ← Alpha.decode 3 bytes
  let (fillery1, bytes) ← Alpha.decode 1 bytes
  let (orderType1, bytes) ← decodeUInt 2 bytes
  let (orderNumber1, bytes) ← Alpha.decode 8 bytes
  let (accountNumber1, bytes) ← Alpha.decode 10 bytes
  let (bookType1, bytes) ← decodeUInt 2 bytes
  let (buySell1, bytes) ← decodeUInt 2 bytes
  let (disclosedVol1, bytes) ← decodeUInt 4 bytes
  let (disclosedVolRemaining1, bytes) ← decodeUInt 4 bytes
  let (totalVolRemaining1, bytes) ← decodeUInt 4 bytes
  let (volume1, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday1, bytes) ← decodeUInt 4 bytes
  let (price1, bytes) ← decodeUInt 4 bytes
  let (triggerPrice1, bytes) ← decodeUInt 4 bytes
  let (goodTillDate1, bytes) ← decodeUInt 4 bytes
  let (entryDateTime1, bytes) ← decodeUInt 4 bytes
  let (minFillAon1, bytes) ← decodeUInt 4 bytes
  let (lastModified1, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId1, bytes) ← decodeUInt 2 bytes
  let (traderId1, bytes) ← decodeUInt 4 bytes
  let (brokerId1, bytes) ← Alpha.decode 5 bytes
  let (cOrdFiller, bytes) ← Alpha.decode 24 bytes
  let (openClose1, bytes) ← Alpha.decode 1 bytes
  let (settlor1, bytes) ← Alpha.decode 12 bytes
  let (proClient1, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod1, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag1, bytes) ← Alpha.decode 1 bytes
  let (filler116, bytes) ← Alpha.decode 2 bytes
  let (filler17, bytes) ← Alpha.decode 1 bytes
  let (filler18, bytes) ← Alpha.decode 1 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← Alpha.decode 8 bytes
  let (echoBack, bytes) ← Alpha.decode 16 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  let (priceDiff, bytes) ← decodeUInt 4 bytes
  let (msSpdLegInfo_, bytes) ← decodeMany MsSpdLegInfo.decode 2 bytes
  if fits_msSpdLegInfo : msSpdLegInfo_.length = 2 then
    pure ({ participantType1, filler1, competitorPeriod1, solicitorPeriod1, modCxlBy1, filler9, reasonCode1, startAlpha1, endAlpha1, token1, contractDesc, opBrokerId1, fillerx1, fillerOptions1, fillery1, orderType1, orderNumber1, accountNumber1, bookType1, buySell1, disclosedVol1, disclosedVolRemaining1, totalVolRemaining1, volume1, volumeFilledToday1, price1, triggerPrice1, goodTillDate1, entryDateTime1, minFillAon1, lastModified1, stOrderFlags, branchId1, traderId1, brokerId1, cOrdFiller, openClose1, settlor1, proClient1, settlementPeriod1, additionalOrderFlags, giveupFlag1, filler116, filler17, filler18, nnfField, mktReplay, echoBack, lastActivityReference, reserved52, priceDiff, msSpdLegInfo := ⟨msSpdLegInfo_, fits_msSpdLegInfo⟩ }, bytes)
  else none

@[simp] theorem encode_length (message : SpreadOrderBody) : (encode message).length = 440 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, encodeUIntLE_length, encodeMany_length_const MsSpdLegInfo.encode 80 MsSpdLegInfo.encode_length, message.msSpdLegInfo.length_eq]

theorem encode_length_pos (message : SpreadOrderBody) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SpreadOrderBody) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_exact 2 MsSpdLegInfo.encode MsSpdLegInfo.decode MsSpdLegInfo.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.msSpdLegInfo.length_eq]
  rfl

end SpreadOrderBody

/-- Spread Order Entry Request Message: 440 bytes -/
structure SpreadOrderEntryRequestMessage where
  spreadOrderBody : SpreadOrderBody
  deriving DecidableEq, Repr

namespace SpreadOrderEntryRequestMessage

def encode (message : SpreadOrderEntryRequestMessage) : List UInt8 :=
  SpreadOrderBody.encode message.spreadOrderBody

def decode (bytes : List UInt8) : Option (SpreadOrderEntryRequestMessage × List UInt8) := do
  let (spreadOrderBody, bytes) ← SpreadOrderBody.decode bytes
  pure ({ spreadOrderBody }, bytes)

@[simp] theorem encode_length (message : SpreadOrderEntryRequestMessage) : (encode message).length = 440 := by
  unfold encode
  simp only [SpreadOrderBody.encode_length]

theorem encode_length_pos (message : SpreadOrderEntryRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SpreadOrderEntryRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [SpreadOrderBody.decode_encode, some_bind]
  rfl

end SpreadOrderEntryRequestMessage

/-- Mba Inquiry Definition: 16 bytes -/
structure MbaInquiryDefinition where
  cumulativeQuantity : BitVec 32
  totalValue : Alpha 8
  wap : BitVec 32
  deriving DecidableEq, Repr

namespace MbaInquiryDefinition

def encode (message : MbaInquiryDefinition) : List UInt8 :=
  encodeUInt 4 message.cumulativeQuantity
    ++ (Alpha.encode message.totalValue
    ++ (encodeUInt 4 message.wap))

def decode (bytes : List UInt8) : Option (MbaInquiryDefinition × List UInt8) := do
  let (cumulativeQuantity, bytes) ← decodeUInt 4 bytes
  let (totalValue, bytes) ← Alpha.decode 8 bytes
  let (wap, bytes) ← decodeUInt 4 bytes
  pure ({ cumulativeQuantity, totalValue, wap }, bytes)

@[simp] theorem encode_length (message : MbaInquiryDefinition) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : MbaInquiryDefinition) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MbaInquiryDefinition) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MbaInquiryDefinition

/-- Mba Inquiry Request Message: 24 bytes -/
structure MbaInquiryRequestMessage where
  token : BitVec 32
  book : BitVec 16
  buySell : BitVec 16
  mbaInquiryDefinition : MbaInquiryDefinition
  deriving DecidableEq, Repr

namespace MbaInquiryRequestMessage

def encode (message : MbaInquiryRequestMessage) : List UInt8 :=
  encodeUInt 4 message.token
    ++ (encodeUInt 2 message.book
    ++ (encodeUInt 2 message.buySell
    ++ (MbaInquiryDefinition.encode message.mbaInquiryDefinition)))

def decode (bytes : List UInt8) : Option (MbaInquiryRequestMessage × List UInt8) := do
  let (token, bytes) ← decodeUInt 4 bytes
  let (book, bytes) ← decodeUInt 2 bytes
  let (buySell, bytes) ← decodeUInt 2 bytes
  let (mbaInquiryDefinition, bytes) ← MbaInquiryDefinition.decode bytes
  pure ({ token, book, buySell, mbaInquiryDefinition }, bytes)

@[simp] theorem encode_length (message : MbaInquiryRequestMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, MbaInquiryDefinition.encode_length]

theorem encode_length_pos (message : MbaInquiryRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MbaInquiryRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [MbaInquiryDefinition.decode_encode, some_bind]
  rfl

end MbaInquiryRequestMessage

/-- Gateway Router Request Message: 8 bytes -/
structure GatewayRouterRequestMessage where
  boxId : BitVec 16
  brokerId : Alpha 5
  filler : Alpha 1
  deriving DecidableEq, Repr

namespace GatewayRouterRequestMessage

def encode (message : GatewayRouterRequestMessage) : List UInt8 :=
  encodeUInt 2 message.boxId
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.filler))

def decode (bytes : List UInt8) : Option (GatewayRouterRequestMessage × List UInt8) := do
  let (boxId, bytes) ← decodeUInt 2 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (filler, bytes) ← Alpha.decode 1 bytes
  pure ({ boxId, brokerId, filler }, bytes)

@[simp] theorem encode_length (message : GatewayRouterRequestMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : GatewayRouterRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : GatewayRouterRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end GatewayRouterRequestMessage

/-- Secure Box Registration Request In Message: 2 bytes -/
structure SecureBoxRegistrationRequestInMessage where
  boxId : BitVec 16
  deriving DecidableEq, Repr

namespace SecureBoxRegistrationRequestInMessage

def encode (message : SecureBoxRegistrationRequestInMessage) : List UInt8 :=
  encodeUInt 2 message.boxId

def decode (bytes : List UInt8) : Option (SecureBoxRegistrationRequestInMessage × List UInt8) := do
  let (boxId, bytes) ← decodeUInt 2 bytes
  pure ({ boxId }, bytes)

@[simp] theorem encode_length (message : SecureBoxRegistrationRequestInMessage) : (encode message).length = 2 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : SecureBoxRegistrationRequestInMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecureBoxRegistrationRequestInMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SecureBoxRegistrationRequestInMessage

/-- Box Sign On Request In Message: 20 bytes -/
structure BoxSignOnRequestInMessage where
  boxId : BitVec 16
  brokerId : Alpha 5
  reserved5 : Alpha 5
  sessionKey : Alpha 8
  deriving DecidableEq, Repr

namespace BoxSignOnRequestInMessage

def encode (message : BoxSignOnRequestInMessage) : List UInt8 :=
  encodeUInt 2 message.boxId
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.reserved5
    ++ (Alpha.encode message.sessionKey)))

def decode (bytes : List UInt8) : Option (BoxSignOnRequestInMessage × List UInt8) := do
  let (boxId, bytes) ← decodeUInt 2 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (reserved5, bytes) ← Alpha.decode 5 bytes
  let (sessionKey, bytes) ← Alpha.decode 8 bytes
  pure ({ boxId, brokerId, reserved5, sessionKey }, bytes)

@[simp] theorem encode_length (message : BoxSignOnRequestInMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : BoxSignOnRequestInMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BoxSignOnRequestInMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BoxSignOnRequestInMessage

/-- Heartbeat Message: 0 bytes -/
structure HeartbeatMessage where
  deriving DecidableEq, Repr

namespace HeartbeatMessage

def encode (_ : HeartbeatMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (HeartbeatMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : HeartbeatMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : HeartbeatMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end HeartbeatMessage

/-- Branch Limits: 32 bytes -/
structure BranchLimits where
  branchBuyValueLimit : Alpha 8
  branchSellValueLimit : Alpha 8
  reserved16 : Alpha 16
  deriving DecidableEq, Repr

namespace BranchLimits

def encode (message : BranchLimits) : List UInt8 :=
  Alpha.encode message.branchBuyValueLimit
    ++ (Alpha.encode message.branchSellValueLimit
    ++ (Alpha.encode message.reserved16))

def decode (bytes : List UInt8) : Option (BranchLimits × List UInt8) := do
  let (branchBuyValueLimit, bytes) ← Alpha.decode 8 bytes
  let (branchSellValueLimit, bytes) ← Alpha.decode 8 bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  pure ({ branchBuyValueLimit, branchSellValueLimit, reserved16 }, bytes)

@[simp] theorem encode_length (message : BranchLimits) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : BranchLimits) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BranchLimits) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BranchLimits

/-- Branch Order Value Limit Body: 96 bytes -/
structure BranchOrderValueLimitBody where
  brokerId : Alpha 5
  reserved25 : Alpha 25
  branchId : BitVec 16
  branchLimits : Exact 2 BranchLimits
  deriving DecidableEq, Repr

namespace BranchOrderValueLimitBody

def encode (message : BranchOrderValueLimitBody) : List UInt8 :=
  Alpha.encode message.brokerId
    ++ (Alpha.encode message.reserved25
    ++ (encodeUInt 2 message.branchId
    ++ (encodeMany BranchLimits.encode message.branchLimits.val)))

def decode (bytes : List UInt8) : Option (BranchOrderValueLimitBody × List UInt8) := do
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (reserved25, bytes) ← Alpha.decode 25 bytes
  let (branchId, bytes) ← decodeUInt 2 bytes
  let (branchLimits_, bytes) ← decodeMany BranchLimits.decode 2 bytes
  if fits_branchLimits : branchLimits_.length = 2 then
    pure ({ brokerId, reserved25, branchId, branchLimits := ⟨branchLimits_, fits_branchLimits⟩ }, bytes)
  else none

@[simp] theorem encode_length (message : BranchOrderValueLimitBody) : (encode message).length = 96 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, encodeMany_length_const BranchLimits.encode 32 BranchLimits.encode_length, message.branchLimits.length_eq]

theorem encode_length_pos (message : BranchOrderValueLimitBody) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BranchOrderValueLimitBody) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_exact 2 BranchLimits.encode BranchLimits.decode BranchLimits.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.branchLimits.length_eq]
  rfl

end BranchOrderValueLimitBody

/-- Branch Order Value Limit Update Request Message: 96 bytes -/
structure BranchOrderValueLimitUpdateRequestMessage where
  branchOrderValueLimitBody : BranchOrderValueLimitBody
  deriving DecidableEq, Repr

namespace BranchOrderValueLimitUpdateRequestMessage

def encode (message : BranchOrderValueLimitUpdateRequestMessage) : List UInt8 :=
  BranchOrderValueLimitBody.encode message.branchOrderValueLimitBody

def decode (bytes : List UInt8) : Option (BranchOrderValueLimitUpdateRequestMessage × List UInt8) := do
  let (branchOrderValueLimitBody, bytes) ← BranchOrderValueLimitBody.decode bytes
  pure ({ branchOrderValueLimitBody }, bytes)

@[simp] theorem encode_length (message : BranchOrderValueLimitUpdateRequestMessage) : (encode message).length = 96 := by
  unfold encode
  simp only [BranchOrderValueLimitBody.encode_length]

theorem encode_length_pos (message : BranchOrderValueLimitUpdateRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BranchOrderValueLimitUpdateRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [BranchOrderValueLimitBody.decode_encode, some_bind]
  rfl

end BranchOrderValueLimitUpdateRequestMessage

/-- User Limits: 64 bytes -/
structure UserLimits where
  reserved32 : Alpha 32
  userOrderBuyValueLimit : Alpha 8
  userOrderSellValueLimit : Alpha 8
  reserved16 : Alpha 16
  deriving DecidableEq, Repr

namespace UserLimits

def encode (message : UserLimits) : List UInt8 :=
  Alpha.encode message.reserved32
    ++ (Alpha.encode message.userOrderBuyValueLimit
    ++ (Alpha.encode message.userOrderSellValueLimit
    ++ (Alpha.encode message.reserved16)))

def decode (bytes : List UInt8) : Option (UserLimits × List UInt8) := do
  let (reserved32, bytes) ← Alpha.decode 32 bytes
  let (userOrderBuyValueLimit, bytes) ← Alpha.decode 8 bytes
  let (userOrderSellValueLimit, bytes) ← Alpha.decode 8 bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  pure ({ reserved32, userOrderBuyValueLimit, userOrderSellValueLimit, reserved16 }, bytes)

@[simp] theorem encode_length (message : UserLimits) : (encode message).length = 64 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : UserLimits) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UserLimits) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end UserLimits

/-- User Order Value Limit Body: 168 bytes -/
structure UserOrderValueLimitBody where
  brokerId : Alpha 5
  reserved1 : Alpha 1
  branchId : BitVec 16
  reserved26 : Alpha 26
  userId : BitVec 32
  reserved2 : Alpha 2
  userLimits : Exact 2 UserLimits
  deriving DecidableEq, Repr

namespace UserOrderValueLimitBody

def encode (message : UserOrderValueLimitBody) : List UInt8 :=
  Alpha.encode message.brokerId
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.branchId
    ++ (Alpha.encode message.reserved26
    ++ (encodeUInt 4 message.userId
    ++ (Alpha.encode message.reserved2
    ++ (encodeMany UserLimits.encode message.userLimits.val))))))

def decode (bytes : List UInt8) : Option (UserOrderValueLimitBody × List UInt8) := do
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (branchId, bytes) ← decodeUInt 2 bytes
  let (reserved26, bytes) ← Alpha.decode 26 bytes
  let (userId, bytes) ← decodeUInt 4 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (userLimits_, bytes) ← decodeMany UserLimits.decode 2 bytes
  if fits_userLimits : userLimits_.length = 2 then
    pure ({ brokerId, reserved1, branchId, reserved26, userId, reserved2, userLimits := ⟨userLimits_, fits_userLimits⟩ }, bytes)
  else none

@[simp] theorem encode_length (message : UserOrderValueLimitBody) : (encode message).length = 168 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, encodeMany_length_const UserLimits.encode 64 UserLimits.encode_length, message.userLimits.length_eq]

theorem encode_length_pos (message : UserOrderValueLimitBody) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UserOrderValueLimitBody) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_exact 2 UserLimits.encode UserLimits.decode UserLimits.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.userLimits.length_eq]
  rfl

end UserOrderValueLimitBody

/-- User Order Value Limit Update Message: 168 bytes -/
structure UserOrderValueLimitUpdateMessage where
  userOrderValueLimitBody : UserOrderValueLimitBody
  deriving DecidableEq, Repr

namespace UserOrderValueLimitUpdateMessage

def encode (message : UserOrderValueLimitUpdateMessage) : List UInt8 :=
  UserOrderValueLimitBody.encode message.userOrderValueLimitBody

def decode (bytes : List UInt8) : Option (UserOrderValueLimitUpdateMessage × List UInt8) := do
  let (userOrderValueLimitBody, bytes) ← UserOrderValueLimitBody.decode bytes
  pure ({ userOrderValueLimitBody }, bytes)

@[simp] theorem encode_length (message : UserOrderValueLimitUpdateMessage) : (encode message).length = 168 := by
  unfold encode
  simp only [UserOrderValueLimitBody.encode_length]

theorem encode_length_pos (message : UserOrderValueLimitUpdateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UserOrderValueLimitUpdateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [UserOrderValueLimitBody.decode_encode, some_bind]
  rfl

end UserOrderValueLimitUpdateMessage

/-- Normal Order Limit Update Message: 26 bytes -/
structure NormalOrderLimitUpdateMessage where
  brokerId : Alpha 5
  reserved1 : Alpha 1
  userId : BitVec 32
  orderQtyLimit : Alpha 8
  orderValLimit : Alpha 8
  deriving DecidableEq, Repr

namespace NormalOrderLimitUpdateMessage

def encode (message : NormalOrderLimitUpdateMessage) : List UInt8 :=
  Alpha.encode message.brokerId
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 4 message.userId
    ++ (Alpha.encode message.orderQtyLimit
    ++ (Alpha.encode message.orderValLimit))))

def decode (bytes : List UInt8) : Option (NormalOrderLimitUpdateMessage × List UInt8) := do
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (userId, bytes) ← decodeUInt 4 bytes
  let (orderQtyLimit, bytes) ← Alpha.decode 8 bytes
  let (orderValLimit, bytes) ← Alpha.decode 8 bytes
  pure ({ brokerId, reserved1, userId, orderQtyLimit, orderValLimit }, bytes)

@[simp] theorem encode_length (message : NormalOrderLimitUpdateMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : NormalOrderLimitUpdateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NormalOrderLimitUpdateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end NormalOrderLimitUpdateMessage

/-- Reset User Password Message: 18 bytes -/
structure ResetUserPasswordMessage where
  userId : BitVec 32
  reserved14 : Alpha 14
  deriving DecidableEq, Repr

namespace ResetUserPasswordMessage

def encode (message : ResetUserPasswordMessage) : List UInt8 :=
  encodeUInt 4 message.userId
    ++ (Alpha.encode message.reserved14)

def decode (bytes : List UInt8) : Option (ResetUserPasswordMessage × List UInt8) := do
  let (userId, bytes) ← decodeUInt 4 bytes
  let (reserved14, bytes) ← Alpha.decode 14 bytes
  pure ({ userId, reserved14 }, bytes)

@[simp] theorem encode_length (message : ResetUserPasswordMessage) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : ResetUserPasswordMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ResetUserPasswordMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ResetUserPasswordMessage

/-- Collateral User Status Change Request Message: 12 bytes -/
structure CollateralUserStatusChangeRequestMessage where
  userId : BitVec 32
  colUserBit : ColUserBit
  reserved7 : Alpha 7
  deriving DecidableEq, Repr

namespace CollateralUserStatusChangeRequestMessage

def encode (message : CollateralUserStatusChangeRequestMessage) : List UInt8 :=
  encodeUInt 4 message.userId
    ++ (ColUserBit.encode message.colUserBit
    ++ (Alpha.encode message.reserved7))

def decode (bytes : List UInt8) : Option (CollateralUserStatusChangeRequestMessage × List UInt8) := do
  let (userId, bytes) ← decodeUInt 4 bytes
  let (colUserBit, bytes) ← ColUserBit.decode bytes
  let (reserved7, bytes) ← Alpha.decode 7 bytes
  pure ({ userId, colUserBit, reserved7 }, bytes)

@[simp] theorem encode_length (message : CollateralUserStatusChangeRequestMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, ColUserBit.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : CollateralUserStatusChangeRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CollateralUserStatusChangeRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ColUserBit.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end CollateralUserStatusChangeRequestMessage

/-- User Trade Modify Cancel Status Change Request Message: 12 bytes -/
structure UserTradeModifyCancelStatusChangeRequestMessage where
  userId : BitVec 32
  trdModCxlBit : TrdModCxlBit
  reserved7 : Alpha 7
  deriving DecidableEq, Repr

namespace UserTradeModifyCancelStatusChangeRequestMessage

def encode (message : UserTradeModifyCancelStatusChangeRequestMessage) : List UInt8 :=
  encodeUInt 4 message.userId
    ++ (TrdModCxlBit.encode message.trdModCxlBit
    ++ (Alpha.encode message.reserved7))

def decode (bytes : List UInt8) : Option (UserTradeModifyCancelStatusChangeRequestMessage × List UInt8) := do
  let (userId, bytes) ← decodeUInt 4 bytes
  let (trdModCxlBit, bytes) ← TrdModCxlBit.decode bytes
  let (reserved7, bytes) ← Alpha.decode 7 bytes
  pure ({ userId, trdModCxlBit, reserved7 }, bytes)

@[simp] theorem encode_length (message : UserTradeModifyCancelStatusChangeRequestMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, TrdModCxlBit.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : UserTradeModifyCancelStatusChangeRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UserTradeModifyCancelStatusChangeRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TrdModCxlBit.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end UserTradeModifyCancelStatusChangeRequestMessage

/-- User Address Unlock Request Message: 74 bytes -/
structure UserAddressUnlockRequestMessage where
  userId : BitVec 32
  reserved70 : Alpha 70
  deriving DecidableEq, Repr

namespace UserAddressUnlockRequestMessage

def encode (message : UserAddressUnlockRequestMessage) : List UInt8 :=
  encodeUInt 4 message.userId
    ++ (Alpha.encode message.reserved70)

def decode (bytes : List UInt8) : Option (UserAddressUnlockRequestMessage × List UInt8) := do
  let (userId, bytes) ← decodeUInt 4 bytes
  let (reserved70, bytes) ← Alpha.decode 70 bytes
  pure ({ userId, reserved70 }, bytes)

@[simp] theorem encode_length (message : UserAddressUnlockRequestMessage) : (encode message).length = 74 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : UserAddressUnlockRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UserAddressUnlockRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end UserAddressUnlockRequestMessage

/-- Nlt Order Inquiry Request Message: 6 bytes -/
structure NltOrderInquiryRequestMessage where
  brokerId : Alpha 5
  reserved1 : Alpha 1
  deriving DecidableEq, Repr

namespace NltOrderInquiryRequestMessage

def encode (message : NltOrderInquiryRequestMessage) : List UInt8 :=
  Alpha.encode message.brokerId
    ++ (Alpha.encode message.reserved1)

def decode (bytes : List UInt8) : Option (NltOrderInquiryRequestMessage × List UInt8) := do
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  pure ({ brokerId, reserved1 }, bytes)

@[simp] theorem encode_length (message : NltOrderInquiryRequestMessage) : (encode message).length = 6 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : NltOrderInquiryRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NltOrderInquiryRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end NltOrderInquiryRequestMessage

/-- Any Client Message Payload, selected by Transaction Code -/
inductive ClientMessagePayload where
  | signOnRequestInMessage (message : SignOnRequestInMessage) -- 2300
  | signOnRequestInMessage5584 (message : SignOnRequestInMessage) -- 5584
  | signOffRequestInMessage (message : SignOffRequestInMessage) -- 2320
  | systemInformationInMessage (message : SystemInformationInMessage) -- 1600
  | updateLocalDatabaseInMessage (message : UpdateLocalDatabaseInMessage) -- 7300
  | downloadRequestMessage (message : DownloadRequestMessage) -- 7000
  | orderEntryRequestMessage (message : OrderEntryRequestMessage) -- 2000
  | orderEntryRequestMessage2082 (message : OrderEntryRequestMessage) -- 2082
  | orderModificationRequestMessage (message : OrderModificationRequestMessage) -- 2040
  | orderModificationRequestMessage2084 (message : OrderModificationRequestMessage) -- 2084
  | orderCancellationRequestMessage (message : OrderCancellationRequestMessage) -- 2070
  | orderCancellationRequestMessage2086 (message : OrderCancellationRequestMessage) -- 2086
  | killSwitchRequestMessage (message : KillSwitchRequestMessage) -- 2062
  | priceModificationMessage (message : PriceModificationMessage) -- 2013
  | tradeInquiryMessage (message : TradeInquiryMessage) -- 5440
  | tradeInquiryMessage5445 (message : TradeInquiryMessage) -- 5445
  | tradeInquiryMessage5448 (message : TradeInquiryMessage) -- 5448
  | tradeInquiryMessage5451 (message : TradeInquiryMessage) -- 5451
  | spreadOrderEntryRequestMessage (message : SpreadOrderEntryRequestMessage) -- 2100
  | spreadOrderEntryRequestMessage2102 (message : SpreadOrderEntryRequestMessage) -- 2102
  | spreadOrderEntryRequestMessage2104 (message : SpreadOrderEntryRequestMessage) -- 2104
  | spreadOrderEntryRequestMessage2106 (message : SpreadOrderEntryRequestMessage) -- 2106
  | spreadOrderEntryRequestMessage2118 (message : SpreadOrderEntryRequestMessage) -- 2118
  | mbaInquiryRequestMessage (message : MbaInquiryRequestMessage) -- 1684
  | mbaInquiryRequestMessage1686 (message : MbaInquiryRequestMessage) -- 1686
  | mbaInquiryRequestMessage1688 (message : MbaInquiryRequestMessage) -- 1688
  | gatewayRouterRequestMessage (message : GatewayRouterRequestMessage) -- 2400
  | secureBoxRegistrationRequestInMessage (message : SecureBoxRegistrationRequestInMessage) -- 23008
  | boxSignOnRequestInMessage (message : BoxSignOnRequestInMessage) -- 23000
  | heartbeatMessage (message : HeartbeatMessage) -- 23506
  | branchOrderValueLimitUpdateRequestMessage (message : BranchOrderValueLimitUpdateRequestMessage) -- 5716
  | userOrderValueLimitUpdateMessage (message : UserOrderValueLimitUpdateMessage) -- 5730
  | normalOrderLimitUpdateMessage (message : NormalOrderLimitUpdateMessage) -- 5732
  | normalOrderLimitUpdateMessage5771 (message : NormalOrderLimitUpdateMessage) -- 5771
  | resetUserPasswordMessage (message : ResetUserPasswordMessage) -- 5740
  | collateralUserStatusChangeRequestMessage (message : CollateralUserStatusChangeRequestMessage) -- 5744
  | userTradeModifyCancelStatusChangeRequestMessage (message : UserTradeModifyCancelStatusChangeRequestMessage) -- 5738
  | userAddressUnlockRequestMessage (message : UserAddressUnlockRequestMessage) -- 5427
  | nltOrderInquiryRequestMessage (message : NltOrderInquiryRequestMessage) -- 1242
  deriving DecidableEq, Repr

namespace ClientMessagePayload

/-- The Transaction Code each message is sent under -/
def tag : ClientMessagePayload → BitVec 16
  | .signOnRequestInMessage _ => 2300
  | .signOnRequestInMessage5584 _ => 5584
  | .signOffRequestInMessage _ => 2320
  | .systemInformationInMessage _ => 1600
  | .updateLocalDatabaseInMessage _ => 7300
  | .downloadRequestMessage _ => 7000
  | .orderEntryRequestMessage _ => 2000
  | .orderEntryRequestMessage2082 _ => 2082
  | .orderModificationRequestMessage _ => 2040
  | .orderModificationRequestMessage2084 _ => 2084
  | .orderCancellationRequestMessage _ => 2070
  | .orderCancellationRequestMessage2086 _ => 2086
  | .killSwitchRequestMessage _ => 2062
  | .priceModificationMessage _ => 2013
  | .tradeInquiryMessage _ => 5440
  | .tradeInquiryMessage5445 _ => 5445
  | .tradeInquiryMessage5448 _ => 5448
  | .tradeInquiryMessage5451 _ => 5451
  | .spreadOrderEntryRequestMessage _ => 2100
  | .spreadOrderEntryRequestMessage2102 _ => 2102
  | .spreadOrderEntryRequestMessage2104 _ => 2104
  | .spreadOrderEntryRequestMessage2106 _ => 2106
  | .spreadOrderEntryRequestMessage2118 _ => 2118
  | .mbaInquiryRequestMessage _ => 1684
  | .mbaInquiryRequestMessage1686 _ => 1686
  | .mbaInquiryRequestMessage1688 _ => 1688
  | .gatewayRouterRequestMessage _ => 2400
  | .secureBoxRegistrationRequestInMessage _ => 23008
  | .boxSignOnRequestInMessage _ => 23000
  | .heartbeatMessage _ => 23506
  | .branchOrderValueLimitUpdateRequestMessage _ => 5716
  | .userOrderValueLimitUpdateMessage _ => 5730
  | .normalOrderLimitUpdateMessage _ => 5732
  | .normalOrderLimitUpdateMessage5771 _ => 5771
  | .resetUserPasswordMessage _ => 5740
  | .collateralUserStatusChangeRequestMessage _ => 5744
  | .userTradeModifyCancelStatusChangeRequestMessage _ => 5738
  | .userAddressUnlockRequestMessage _ => 5427
  | .nltOrderInquiryRequestMessage _ => 1242

def encode : ClientMessagePayload → List UInt8
  | .signOnRequestInMessage message => SignOnRequestInMessage.encode message
  | .signOnRequestInMessage5584 message => SignOnRequestInMessage.encode message
  | .signOffRequestInMessage message => SignOffRequestInMessage.encode message
  | .systemInformationInMessage message => SystemInformationInMessage.encode message
  | .updateLocalDatabaseInMessage message => UpdateLocalDatabaseInMessage.encode message
  | .downloadRequestMessage message => DownloadRequestMessage.encode message
  | .orderEntryRequestMessage message => OrderEntryRequestMessage.encode message
  | .orderEntryRequestMessage2082 message => OrderEntryRequestMessage.encode message
  | .orderModificationRequestMessage message => OrderModificationRequestMessage.encode message
  | .orderModificationRequestMessage2084 message => OrderModificationRequestMessage.encode message
  | .orderCancellationRequestMessage message => OrderCancellationRequestMessage.encode message
  | .orderCancellationRequestMessage2086 message => OrderCancellationRequestMessage.encode message
  | .killSwitchRequestMessage message => KillSwitchRequestMessage.encode message
  | .priceModificationMessage message => PriceModificationMessage.encode message
  | .tradeInquiryMessage message => TradeInquiryMessage.encode message
  | .tradeInquiryMessage5445 message => TradeInquiryMessage.encode message
  | .tradeInquiryMessage5448 message => TradeInquiryMessage.encode message
  | .tradeInquiryMessage5451 message => TradeInquiryMessage.encode message
  | .spreadOrderEntryRequestMessage message => SpreadOrderEntryRequestMessage.encode message
  | .spreadOrderEntryRequestMessage2102 message => SpreadOrderEntryRequestMessage.encode message
  | .spreadOrderEntryRequestMessage2104 message => SpreadOrderEntryRequestMessage.encode message
  | .spreadOrderEntryRequestMessage2106 message => SpreadOrderEntryRequestMessage.encode message
  | .spreadOrderEntryRequestMessage2118 message => SpreadOrderEntryRequestMessage.encode message
  | .mbaInquiryRequestMessage message => MbaInquiryRequestMessage.encode message
  | .mbaInquiryRequestMessage1686 message => MbaInquiryRequestMessage.encode message
  | .mbaInquiryRequestMessage1688 message => MbaInquiryRequestMessage.encode message
  | .gatewayRouterRequestMessage message => GatewayRouterRequestMessage.encode message
  | .secureBoxRegistrationRequestInMessage message => SecureBoxRegistrationRequestInMessage.encode message
  | .boxSignOnRequestInMessage message => BoxSignOnRequestInMessage.encode message
  | .heartbeatMessage message => HeartbeatMessage.encode message
  | .branchOrderValueLimitUpdateRequestMessage message => BranchOrderValueLimitUpdateRequestMessage.encode message
  | .userOrderValueLimitUpdateMessage message => UserOrderValueLimitUpdateMessage.encode message
  | .normalOrderLimitUpdateMessage message => NormalOrderLimitUpdateMessage.encode message
  | .normalOrderLimitUpdateMessage5771 message => NormalOrderLimitUpdateMessage.encode message
  | .resetUserPasswordMessage message => ResetUserPasswordMessage.encode message
  | .collateralUserStatusChangeRequestMessage message => CollateralUserStatusChangeRequestMessage.encode message
  | .userTradeModifyCancelStatusChangeRequestMessage message => UserTradeModifyCancelStatusChangeRequestMessage.encode message
  | .userAddressUnlockRequestMessage message => UserAddressUnlockRequestMessage.encode message
  | .nltOrderInquiryRequestMessage message => NltOrderInquiryRequestMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ClientMessagePayload) : (encode message).length ≤ 440 := by
  cases message with
  | signOnRequestInMessage inner =>
    simp only [encode, SignOnRequestInMessage.encode_length]
    omega
  | signOnRequestInMessage5584 inner =>
    simp only [encode, SignOnRequestInMessage.encode_length]
    omega
  | signOffRequestInMessage inner =>
    simp only [encode, SignOffRequestInMessage.encode_length]
    omega
  | systemInformationInMessage inner =>
    simp only [encode, SystemInformationInMessage.encode_length]
    omega
  | updateLocalDatabaseInMessage inner =>
    simp only [encode, UpdateLocalDatabaseInMessage.encode_length]
    omega
  | downloadRequestMessage inner =>
    simp only [encode, DownloadRequestMessage.encode_length]
    omega
  | orderEntryRequestMessage inner =>
    simp only [encode, OrderEntryRequestMessage.encode_length]
    omega
  | orderEntryRequestMessage2082 inner =>
    simp only [encode, OrderEntryRequestMessage.encode_length]
    omega
  | orderModificationRequestMessage inner =>
    simp only [encode, OrderModificationRequestMessage.encode_length]
    omega
  | orderModificationRequestMessage2084 inner =>
    simp only [encode, OrderModificationRequestMessage.encode_length]
    omega
  | orderCancellationRequestMessage inner =>
    simp only [encode, OrderCancellationRequestMessage.encode_length]
    omega
  | orderCancellationRequestMessage2086 inner =>
    simp only [encode, OrderCancellationRequestMessage.encode_length]
    omega
  | killSwitchRequestMessage inner =>
    simp only [encode, KillSwitchRequestMessage.encode_length]
    omega
  | priceModificationMessage inner =>
    simp only [encode, PriceModificationMessage.encode_length]
    omega
  | tradeInquiryMessage inner =>
    simp only [encode, TradeInquiryMessage.encode_length]
    omega
  | tradeInquiryMessage5445 inner =>
    simp only [encode, TradeInquiryMessage.encode_length]
    omega
  | tradeInquiryMessage5448 inner =>
    simp only [encode, TradeInquiryMessage.encode_length]
    omega
  | tradeInquiryMessage5451 inner =>
    simp only [encode, TradeInquiryMessage.encode_length]
    omega
  | spreadOrderEntryRequestMessage inner =>
    simp only [encode, SpreadOrderEntryRequestMessage.encode_length]
    omega
  | spreadOrderEntryRequestMessage2102 inner =>
    simp only [encode, SpreadOrderEntryRequestMessage.encode_length]
    omega
  | spreadOrderEntryRequestMessage2104 inner =>
    simp only [encode, SpreadOrderEntryRequestMessage.encode_length]
    omega
  | spreadOrderEntryRequestMessage2106 inner =>
    simp only [encode, SpreadOrderEntryRequestMessage.encode_length]
    omega
  | spreadOrderEntryRequestMessage2118 inner =>
    simp only [encode, SpreadOrderEntryRequestMessage.encode_length]
    omega
  | mbaInquiryRequestMessage inner =>
    simp only [encode, MbaInquiryRequestMessage.encode_length]
    omega
  | mbaInquiryRequestMessage1686 inner =>
    simp only [encode, MbaInquiryRequestMessage.encode_length]
    omega
  | mbaInquiryRequestMessage1688 inner =>
    simp only [encode, MbaInquiryRequestMessage.encode_length]
    omega
  | gatewayRouterRequestMessage inner =>
    simp only [encode, GatewayRouterRequestMessage.encode_length]
    omega
  | secureBoxRegistrationRequestInMessage inner =>
    simp only [encode, SecureBoxRegistrationRequestInMessage.encode_length]
    omega
  | boxSignOnRequestInMessage inner =>
    simp only [encode, BoxSignOnRequestInMessage.encode_length]
    omega
  | heartbeatMessage inner =>
    simp only [encode, HeartbeatMessage.encode_length]
    omega
  | branchOrderValueLimitUpdateRequestMessage inner =>
    simp only [encode, BranchOrderValueLimitUpdateRequestMessage.encode_length]
    omega
  | userOrderValueLimitUpdateMessage inner =>
    simp only [encode, UserOrderValueLimitUpdateMessage.encode_length]
    omega
  | normalOrderLimitUpdateMessage inner =>
    simp only [encode, NormalOrderLimitUpdateMessage.encode_length]
    omega
  | normalOrderLimitUpdateMessage5771 inner =>
    simp only [encode, NormalOrderLimitUpdateMessage.encode_length]
    omega
  | resetUserPasswordMessage inner =>
    simp only [encode, ResetUserPasswordMessage.encode_length]
    omega
  | collateralUserStatusChangeRequestMessage inner =>
    simp only [encode, CollateralUserStatusChangeRequestMessage.encode_length]
    omega
  | userTradeModifyCancelStatusChangeRequestMessage inner =>
    simp only [encode, UserTradeModifyCancelStatusChangeRequestMessage.encode_length]
    omega
  | userAddressUnlockRequestMessage inner =>
    simp only [encode, UserAddressUnlockRequestMessage.encode_length]
    omega
  | nltOrderInquiryRequestMessage inner =>
    simp only [encode, NltOrderInquiryRequestMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (ClientMessagePayload × List UInt8) :=
  if tag = 2300 then (SignOnRequestInMessage.decode bytes).map fun (message, rest) => (.signOnRequestInMessage message, rest)
  else if tag = 5584 then (SignOnRequestInMessage.decode bytes).map fun (message, rest) => (.signOnRequestInMessage5584 message, rest)
  else if tag = 2320 then (SignOffRequestInMessage.decode bytes).map fun (message, rest) => (.signOffRequestInMessage message, rest)
  else if tag = 1600 then (SystemInformationInMessage.decode bytes).map fun (message, rest) => (.systemInformationInMessage message, rest)
  else if tag = 7300 then (UpdateLocalDatabaseInMessage.decode bytes).map fun (message, rest) => (.updateLocalDatabaseInMessage message, rest)
  else if tag = 7000 then (DownloadRequestMessage.decode bytes).map fun (message, rest) => (.downloadRequestMessage message, rest)
  else if tag = 2000 then (OrderEntryRequestMessage.decode bytes).map fun (message, rest) => (.orderEntryRequestMessage message, rest)
  else if tag = 2082 then (OrderEntryRequestMessage.decode bytes).map fun (message, rest) => (.orderEntryRequestMessage2082 message, rest)
  else if tag = 2040 then (OrderModificationRequestMessage.decode bytes).map fun (message, rest) => (.orderModificationRequestMessage message, rest)
  else if tag = 2084 then (OrderModificationRequestMessage.decode bytes).map fun (message, rest) => (.orderModificationRequestMessage2084 message, rest)
  else if tag = 2070 then (OrderCancellationRequestMessage.decode bytes).map fun (message, rest) => (.orderCancellationRequestMessage message, rest)
  else if tag = 2086 then (OrderCancellationRequestMessage.decode bytes).map fun (message, rest) => (.orderCancellationRequestMessage2086 message, rest)
  else if tag = 2062 then (KillSwitchRequestMessage.decode bytes).map fun (message, rest) => (.killSwitchRequestMessage message, rest)
  else if tag = 2013 then (PriceModificationMessage.decode bytes).map fun (message, rest) => (.priceModificationMessage message, rest)
  else if tag = 5440 then (TradeInquiryMessage.decode bytes).map fun (message, rest) => (.tradeInquiryMessage message, rest)
  else if tag = 5445 then (TradeInquiryMessage.decode bytes).map fun (message, rest) => (.tradeInquiryMessage5445 message, rest)
  else if tag = 5448 then (TradeInquiryMessage.decode bytes).map fun (message, rest) => (.tradeInquiryMessage5448 message, rest)
  else if tag = 5451 then (TradeInquiryMessage.decode bytes).map fun (message, rest) => (.tradeInquiryMessage5451 message, rest)
  else if tag = 2100 then (SpreadOrderEntryRequestMessage.decode bytes).map fun (message, rest) => (.spreadOrderEntryRequestMessage message, rest)
  else if tag = 2102 then (SpreadOrderEntryRequestMessage.decode bytes).map fun (message, rest) => (.spreadOrderEntryRequestMessage2102 message, rest)
  else if tag = 2104 then (SpreadOrderEntryRequestMessage.decode bytes).map fun (message, rest) => (.spreadOrderEntryRequestMessage2104 message, rest)
  else if tag = 2106 then (SpreadOrderEntryRequestMessage.decode bytes).map fun (message, rest) => (.spreadOrderEntryRequestMessage2106 message, rest)
  else if tag = 2118 then (SpreadOrderEntryRequestMessage.decode bytes).map fun (message, rest) => (.spreadOrderEntryRequestMessage2118 message, rest)
  else if tag = 1684 then (MbaInquiryRequestMessage.decode bytes).map fun (message, rest) => (.mbaInquiryRequestMessage message, rest)
  else if tag = 1686 then (MbaInquiryRequestMessage.decode bytes).map fun (message, rest) => (.mbaInquiryRequestMessage1686 message, rest)
  else if tag = 1688 then (MbaInquiryRequestMessage.decode bytes).map fun (message, rest) => (.mbaInquiryRequestMessage1688 message, rest)
  else if tag = 2400 then (GatewayRouterRequestMessage.decode bytes).map fun (message, rest) => (.gatewayRouterRequestMessage message, rest)
  else if tag = 23008 then (SecureBoxRegistrationRequestInMessage.decode bytes).map fun (message, rest) => (.secureBoxRegistrationRequestInMessage message, rest)
  else if tag = 23000 then (BoxSignOnRequestInMessage.decode bytes).map fun (message, rest) => (.boxSignOnRequestInMessage message, rest)
  else if tag = 23506 then (HeartbeatMessage.decode bytes).map fun (message, rest) => (.heartbeatMessage message, rest)
  else if tag = 5716 then (BranchOrderValueLimitUpdateRequestMessage.decode bytes).map fun (message, rest) => (.branchOrderValueLimitUpdateRequestMessage message, rest)
  else if tag = 5730 then (UserOrderValueLimitUpdateMessage.decode bytes).map fun (message, rest) => (.userOrderValueLimitUpdateMessage message, rest)
  else if tag = 5732 then (NormalOrderLimitUpdateMessage.decode bytes).map fun (message, rest) => (.normalOrderLimitUpdateMessage message, rest)
  else if tag = 5771 then (NormalOrderLimitUpdateMessage.decode bytes).map fun (message, rest) => (.normalOrderLimitUpdateMessage5771 message, rest)
  else if tag = 5740 then (ResetUserPasswordMessage.decode bytes).map fun (message, rest) => (.resetUserPasswordMessage message, rest)
  else if tag = 5744 then (CollateralUserStatusChangeRequestMessage.decode bytes).map fun (message, rest) => (.collateralUserStatusChangeRequestMessage message, rest)
  else if tag = 5738 then (UserTradeModifyCancelStatusChangeRequestMessage.decode bytes).map fun (message, rest) => (.userTradeModifyCancelStatusChangeRequestMessage message, rest)
  else if tag = 5427 then (UserAddressUnlockRequestMessage.decode bytes).map fun (message, rest) => (.userAddressUnlockRequestMessage message, rest)
  else if tag = 1242 then (NltOrderInquiryRequestMessage.decode bytes).map fun (message, rest) => (.nltOrderInquiryRequestMessage message, rest)
  else none

@[simp] theorem decode_encode (message : ClientMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ClientMessagePayload

/-- Client Registration Packet -/
structure ClientRegistrationPacket where
  registrationChecksum : Alpha 16
  logTime : BitVec 32
  alphaChar : Alpha 2
  traderId : BitVec 32
  errorCode : BitVec 16
  headerTimestamp : Alpha 8
  timeStamp1 : Alpha 8
  timeStamp2 : Alpha 8
  messageLength : BitVec 16
  clientMessagePayload : ClientMessagePayload
  deriving DecidableEq, Repr

namespace ClientRegistrationPacket

def encode (message : ClientRegistrationPacket) : List UInt8 :=
  Alpha.encode message.registrationChecksum
    ++ (encodeUInt 2 (ClientMessagePayload.tag message.clientMessagePayload)
    ++ (encodeUInt 4 message.logTime
    ++ (Alpha.encode message.alphaChar
    ++ (encodeUInt 4 message.traderId
    ++ (encodeUInt 2 message.errorCode
    ++ (Alpha.encode message.headerTimestamp
    ++ (Alpha.encode message.timeStamp1
    ++ (Alpha.encode message.timeStamp2
    ++ (encodeUInt 2 message.messageLength
    ++ (ClientMessagePayload.encode message.clientMessagePayload))))))))))

def decode (bytes : List UInt8) : Option (ClientRegistrationPacket × List UInt8) := do
  let (registrationChecksum, bytes) ← Alpha.decode 16 bytes
  let (transactionCode, bytes) ← decodeUInt 2 bytes
  let (logTime, bytes) ← decodeUInt 4 bytes
  let (alphaChar, bytes) ← Alpha.decode 2 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (errorCode, bytes) ← decodeUInt 2 bytes
  let (headerTimestamp, bytes) ← Alpha.decode 8 bytes
  let (timeStamp1, bytes) ← Alpha.decode 8 bytes
  let (timeStamp2, bytes) ← Alpha.decode 8 bytes
  let (messageLength, bytes) ← decodeUInt 2 bytes
  let (clientMessagePayload, bytes) ← ClientMessagePayload.decode transactionCode bytes
  pure ({ registrationChecksum, logTime, alphaChar, traderId, errorCode, headerTimestamp, timeStamp1, timeStamp2, messageLength, clientMessagePayload }, bytes)

theorem encode_length_pos (message : ClientRegistrationPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ClientRegistrationPacket) : (encode message).length ≤ 496 := by
  unfold encode
  cases message.clientMessagePayload with
  | signOnRequestInMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, SignOnRequestInMessage.encode_length]
    omega
  | signOnRequestInMessage5584 inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, SignOnRequestInMessage.encode_length]
    omega
  | signOffRequestInMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, SignOffRequestInMessage.encode_length]
    omega
  | systemInformationInMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, SystemInformationInMessage.encode_length]
    omega
  | updateLocalDatabaseInMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, UpdateLocalDatabaseInMessage.encode_length]
    omega
  | downloadRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, DownloadRequestMessage.encode_length]
    omega
  | orderEntryRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, OrderEntryRequestMessage.encode_length]
    omega
  | orderEntryRequestMessage2082 inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, OrderEntryRequestMessage.encode_length]
    omega
  | orderModificationRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, OrderModificationRequestMessage.encode_length]
    omega
  | orderModificationRequestMessage2084 inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, OrderModificationRequestMessage.encode_length]
    omega
  | orderCancellationRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, OrderCancellationRequestMessage.encode_length]
    omega
  | orderCancellationRequestMessage2086 inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, OrderCancellationRequestMessage.encode_length]
    omega
  | killSwitchRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, KillSwitchRequestMessage.encode_length]
    omega
  | priceModificationMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, PriceModificationMessage.encode_length]
    omega
  | tradeInquiryMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, TradeInquiryMessage.encode_length]
    omega
  | tradeInquiryMessage5445 inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, TradeInquiryMessage.encode_length]
    omega
  | tradeInquiryMessage5448 inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, TradeInquiryMessage.encode_length]
    omega
  | tradeInquiryMessage5451 inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, TradeInquiryMessage.encode_length]
    omega
  | spreadOrderEntryRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, SpreadOrderEntryRequestMessage.encode_length]
    omega
  | spreadOrderEntryRequestMessage2102 inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, SpreadOrderEntryRequestMessage.encode_length]
    omega
  | spreadOrderEntryRequestMessage2104 inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, SpreadOrderEntryRequestMessage.encode_length]
    omega
  | spreadOrderEntryRequestMessage2106 inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, SpreadOrderEntryRequestMessage.encode_length]
    omega
  | spreadOrderEntryRequestMessage2118 inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, SpreadOrderEntryRequestMessage.encode_length]
    omega
  | mbaInquiryRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, MbaInquiryRequestMessage.encode_length]
    omega
  | mbaInquiryRequestMessage1686 inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, MbaInquiryRequestMessage.encode_length]
    omega
  | mbaInquiryRequestMessage1688 inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, MbaInquiryRequestMessage.encode_length]
    omega
  | gatewayRouterRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, GatewayRouterRequestMessage.encode_length]
    omega
  | secureBoxRegistrationRequestInMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, SecureBoxRegistrationRequestInMessage.encode_length]
    omega
  | boxSignOnRequestInMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, BoxSignOnRequestInMessage.encode_length]
    omega
  | heartbeatMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, HeartbeatMessage.encode_length]
    omega
  | branchOrderValueLimitUpdateRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, BranchOrderValueLimitUpdateRequestMessage.encode_length]
    omega
  | userOrderValueLimitUpdateMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, UserOrderValueLimitUpdateMessage.encode_length]
    omega
  | normalOrderLimitUpdateMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, NormalOrderLimitUpdateMessage.encode_length]
    omega
  | normalOrderLimitUpdateMessage5771 inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, NormalOrderLimitUpdateMessage.encode_length]
    omega
  | resetUserPasswordMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, ResetUserPasswordMessage.encode_length]
    omega
  | collateralUserStatusChangeRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, CollateralUserStatusChangeRequestMessage.encode_length]
    omega
  | userTradeModifyCancelStatusChangeRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, UserTradeModifyCancelStatusChangeRequestMessage.encode_length]
    omega
  | userAddressUnlockRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, UserAddressUnlockRequestMessage.encode_length]
    omega
  | nltOrderInquiryRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, NltOrderInquiryRequestMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : ClientRegistrationPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ClientMessagePayload.decode_encode, some_bind]
  rfl

end ClientRegistrationPacket

/-- Client Message Data -/
structure ClientMessageData where
  logTime : BitVec 32
  alphaChar : Alpha 2
  traderId : BitVec 32
  errorCode : BitVec 16
  headerTimestamp : Alpha 8
  timeStamp1 : Alpha 8
  timeStamp2 : Alpha 8
  messageLength : BitVec 16
  clientMessagePayload : ClientMessagePayload
  deriving DecidableEq, Repr

namespace ClientMessageData

def encode (message : ClientMessageData) : List UInt8 :=
  encodeUInt 2 (ClientMessagePayload.tag message.clientMessagePayload)
    ++ (encodeUInt 4 message.logTime
    ++ (Alpha.encode message.alphaChar
    ++ (encodeUInt 4 message.traderId
    ++ (encodeUInt 2 message.errorCode
    ++ (Alpha.encode message.headerTimestamp
    ++ (Alpha.encode message.timeStamp1
    ++ (Alpha.encode message.timeStamp2
    ++ (encodeUInt 2 message.messageLength
    ++ (ClientMessagePayload.encode message.clientMessagePayload)))))))))

def decode (bytes : List UInt8) : Option (ClientMessageData × List UInt8) := do
  let (transactionCode, bytes) ← decodeUInt 2 bytes
  let (logTime, bytes) ← decodeUInt 4 bytes
  let (alphaChar, bytes) ← Alpha.decode 2 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (errorCode, bytes) ← decodeUInt 2 bytes
  let (headerTimestamp, bytes) ← Alpha.decode 8 bytes
  let (timeStamp1, bytes) ← Alpha.decode 8 bytes
  let (timeStamp2, bytes) ← Alpha.decode 8 bytes
  let (messageLength, bytes) ← decodeUInt 2 bytes
  let (clientMessagePayload, bytes) ← ClientMessagePayload.decode transactionCode bytes
  pure ({ logTime, alphaChar, traderId, errorCode, headerTimestamp, timeStamp1, timeStamp2, messageLength, clientMessagePayload }, bytes)

theorem encode_length_pos (message : ClientMessageData) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ClientMessageData) : (encode message).length ≤ 480 := by
  unfold encode
  cases message.clientMessagePayload with
  | signOnRequestInMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, SignOnRequestInMessage.encode_length]
    omega
  | signOnRequestInMessage5584 inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, SignOnRequestInMessage.encode_length]
    omega
  | signOffRequestInMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, SignOffRequestInMessage.encode_length]
    omega
  | systemInformationInMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, SystemInformationInMessage.encode_length]
    omega
  | updateLocalDatabaseInMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, UpdateLocalDatabaseInMessage.encode_length]
    omega
  | downloadRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, DownloadRequestMessage.encode_length]
    omega
  | orderEntryRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OrderEntryRequestMessage.encode_length]
    omega
  | orderEntryRequestMessage2082 inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OrderEntryRequestMessage.encode_length]
    omega
  | orderModificationRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OrderModificationRequestMessage.encode_length]
    omega
  | orderModificationRequestMessage2084 inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OrderModificationRequestMessage.encode_length]
    omega
  | orderCancellationRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OrderCancellationRequestMessage.encode_length]
    omega
  | orderCancellationRequestMessage2086 inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OrderCancellationRequestMessage.encode_length]
    omega
  | killSwitchRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, KillSwitchRequestMessage.encode_length]
    omega
  | priceModificationMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, PriceModificationMessage.encode_length]
    omega
  | tradeInquiryMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, TradeInquiryMessage.encode_length]
    omega
  | tradeInquiryMessage5445 inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, TradeInquiryMessage.encode_length]
    omega
  | tradeInquiryMessage5448 inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, TradeInquiryMessage.encode_length]
    omega
  | tradeInquiryMessage5451 inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, TradeInquiryMessage.encode_length]
    omega
  | spreadOrderEntryRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, SpreadOrderEntryRequestMessage.encode_length]
    omega
  | spreadOrderEntryRequestMessage2102 inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, SpreadOrderEntryRequestMessage.encode_length]
    omega
  | spreadOrderEntryRequestMessage2104 inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, SpreadOrderEntryRequestMessage.encode_length]
    omega
  | spreadOrderEntryRequestMessage2106 inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, SpreadOrderEntryRequestMessage.encode_length]
    omega
  | spreadOrderEntryRequestMessage2118 inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, SpreadOrderEntryRequestMessage.encode_length]
    omega
  | mbaInquiryRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, MbaInquiryRequestMessage.encode_length]
    omega
  | mbaInquiryRequestMessage1686 inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, MbaInquiryRequestMessage.encode_length]
    omega
  | mbaInquiryRequestMessage1688 inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, MbaInquiryRequestMessage.encode_length]
    omega
  | gatewayRouterRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, GatewayRouterRequestMessage.encode_length]
    omega
  | secureBoxRegistrationRequestInMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, SecureBoxRegistrationRequestInMessage.encode_length]
    omega
  | boxSignOnRequestInMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, BoxSignOnRequestInMessage.encode_length]
    omega
  | heartbeatMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, HeartbeatMessage.encode_length]
    omega
  | branchOrderValueLimitUpdateRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, BranchOrderValueLimitUpdateRequestMessage.encode_length]
    omega
  | userOrderValueLimitUpdateMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, UserOrderValueLimitUpdateMessage.encode_length]
    omega
  | normalOrderLimitUpdateMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, NormalOrderLimitUpdateMessage.encode_length]
    omega
  | normalOrderLimitUpdateMessage5771 inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, NormalOrderLimitUpdateMessage.encode_length]
    omega
  | resetUserPasswordMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, ResetUserPasswordMessage.encode_length]
    omega
  | collateralUserStatusChangeRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, CollateralUserStatusChangeRequestMessage.encode_length]
    omega
  | userTradeModifyCancelStatusChangeRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, UserTradeModifyCancelStatusChangeRequestMessage.encode_length]
    omega
  | userAddressUnlockRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, UserAddressUnlockRequestMessage.encode_length]
    omega
  | nltOrderInquiryRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, NltOrderInquiryRequestMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : ClientMessageData) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ClientMessagePayload.decode_encode, some_bind]
  rfl

end ClientMessageData

/-- Client Session Packet -/
structure ClientSessionPacket where
  checksum : Alpha 16
  clientMessageData : ClientMessageData
  deriving DecidableEq, Repr

namespace ClientSessionPacket

def encode (message : ClientSessionPacket) : List UInt8 :=
  Alpha.encode message.checksum
    ++ (ClientMessageData.encode message.clientMessageData)

def decode (bytes : List UInt8) : Option (ClientSessionPacket × List UInt8) := do
  let (checksum, bytes) ← Alpha.decode 16 bytes
  let (clientMessageData, bytes) ← ClientMessageData.decode bytes
  pure ({ checksum, clientMessageData }, bytes)

theorem encode_length_pos (message : ClientSessionPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

@[simp] theorem decode_encode (message : ClientSessionPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [ClientMessageData.decode_encode, some_bind]
  rfl

end ClientSessionPacket

/-- Client Direct Packet -/
structure ClientDirectPacket where
  packetSequenceNumber : BitVec 32
  clientPacketBody : Peeked (ClientRegistrationPacket) (ClientSessionPacket) ClientRegistrationPacket.encode ClientSessionPacket.encode 16 [89, 224]
  deriving DecidableEq, Repr

namespace ClientDirectPacket

def encodeBody (message : ClientDirectPacket) : List UInt8 :=
  encodeUInt 4 message.packetSequenceNumber
    ++ (encodePeek ClientRegistrationPacket.encode ClientSessionPacket.encode message.clientPacketBody)

def decodeBody (bytes : List UInt8) : Option (ClientDirectPacket × List UInt8) := do
  let (packetSequenceNumber, bytes) ← decodeUInt 4 bytes
  let (clientPacketBody, bytes) ← decodePeek 16 [89, 224] (decodeKeyed ClientRegistrationPacket.encode ClientRegistrationPacket.decode 16 [89, 224]) (decodeUnkeyed ClientSessionPacket.encode ClientSessionPacket.decode 16 [89, 224]) bytes
  pure ({ packetSequenceNumber, clientPacketBody }, bytes)

theorem decodeBody_encodeBody (message : ClientDirectPacket) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodePeek_encodePeek ClientRegistrationPacket.encode ClientRegistrationPacket.decode ClientSessionPacket.encode ClientSessionPacket.decode 16 [89, 224] ClientRegistrationPacket.decode_encode ClientSessionPacket.decode_encode, some_bind]
  rfl

/-- Size rule: Packet Length counts the bytes after it plus 2, so it is written from the body; the body has no bound the prefix must fit, so it is read by its content and the prefix is not checked -/
def encode (message : ClientDirectPacket) : List UInt8 :=
  encodeUInt 2 (BitVec.ofNat (8 * 2) ((encodeBody message).length + 2)) ++ encodeBody message

def decode (bytes : List UInt8) : Option (ClientDirectPacket × List UInt8) := do
  let (_, bytes) ← decodeUInt 2 bytes
  decodeBody bytes

@[simp] theorem decode_encode (message : ClientDirectPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  exact decodeBody_encodeBody message rest

theorem encode_length_pos (message : ClientDirectPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]
  omega

end ClientDirectPacket

/-- Client Packet -/
structure ClientPacket where
  clientDirectPacket : List ClientDirectPacket
  deriving DecidableEq, Repr

namespace ClientPacket

def encode (message : ClientPacket) : List UInt8 :=
  encodeMany ClientDirectPacket.encode message.clientDirectPacket

def decode (bytes : List UInt8) : Option ClientPacket := do
  let clientDirectPacket ← decodeAll ClientDirectPacket.decode bytes.length bytes
  pure { clientDirectPacket }

theorem decode_encode (message : ClientPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany ClientDirectPacket.encode ClientDirectPacket.decode ClientDirectPacket.decode_encode ClientDirectPacket.encode_length_pos message.clientDirectPacket _ (encodeMany_length_ge ClientDirectPacket.encode ClientDirectPacket.encode_length_pos message.clientDirectPacket), some_bind]
  rfl

end ClientPacket

end Omi.NseNseixOrderentryNnfdirectV112Client
