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

Note: Sign On Response Body is keyed on Message Length, the length framing it, and closes that frame
behind 40 fixed bytes: it is read as the arm as wide as what the frame leaves (214 being Sign On Out
Body, 174 bytes, 182 being Error Response Body, 142 bytes)

Note: Sign On Request Out Message is selected by more than one code: each is a constructor of its
own over the one record, so the code read is the code written back

Note: St Stock Eligible Indicators is a bit field set, proven as its 2 byte integer rather than bit
by bit

Note: System Information Out Message is selected by more than one code: each is a constructor of its
own over the one record, so the code read is the code written back

Note: St Order Flags is a bit field set, proven as its 2 byte integer rather than bit by bit

Note: Additional Order Flags is a bit field set, proven as its 1 byte integer rather than bit by bit

Note: Order Confirmation Message is selected by more than one code: each is a constructor of its own
over the one record, so the code read is the code written back

Note: Order Modification Confirmation Message is selected by more than one code: each is a
constructor of its own over the one record, so the code read is the code written back

Note: Order Response Message is selected by more than one code: each is a constructor of its own
over the one record, so the code read is the code written back

Note: Cancellation Confirmation Body is keyed on Message Length, the length framing it, and closes
that frame behind 40 fixed bytes: it is read as the arm as wide as what the frame leaves (316 being
Order Entry Body, 276 bytes, 480 being Spread Order Body, 440 bytes)

Note: Trade Inquiry Response Message is selected by more than one code: each is a constructor of its
own over the one record, so the code read is the code written back

Note: Trade Confirmation Message is selected by more than one code: each is a constructor of its own
over the one record, so the code read is the code written back

Note: Spread Order Response Message is selected by more than one code: each is a constructor of its
own over the one record, so the code read is the code written back

Note: User Limit Response Body is keyed on Message Length, the length framing it, and closes that
frame behind 40 fixed bytes: it is read as the arm as wide as what the frame leaves (206 being User
Order Limit Body, 166 bytes, 208 being User Order Value Limit Body, 168 bytes, 182 being Error
Response Body, 142 bytes)

Note: Mba Inquiry Response Message is selected by more than one code: each is a constructor of its
own over the one record, so the code read is the code written back

Note: Giveup Confirmation Message is selected by more than one code: each is a constructor of its
own over the one record, so the code read is the code written back

Note: Branch Limit Response Body is keyed on Message Length, the length framing it, and closes that
frame behind 40 fixed bytes: it is read as the arm as wide as what the frame leaves (136 being
Branch Order Value Limit Body, 96 bytes, 182 being Error Response Body, 142 bytes)

Note: User Address Unlock Approve Message is selected by more than one code: each is a constructor
of its own over the one record, so the code read is the code written back

Note: Server Message's body has no bound its 2 byte Message Length must fit, so every message
carries the proof its own encoding fits: the record is its body with that proof, checked as the
frame is read

License: MIT No Attribution
-/

namespace Omi.NseNseixOrderentryNnfV112Server

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

/-- Old Open Close: one byte code -/
def OldOpenClose.codes : List UInt8 :=
  [0x4F, 0x43]

inductive OldOpenClose where
  | open_ -- Open
  | close -- Close
  | unlisted (byte : { byte : UInt8 // byte ∉ OldOpenClose.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OldOpenClose

def toByte : OldOpenClose → UInt8
  | .open_ => 0x4F
  | .close => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OldOpenClose :=
  if byte = 0x4F then .open_
  else .close

def ofByte (byte : UInt8) : OldOpenClose :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OldOpenClose) : ofByte value.toByte = value := by
  cases value with
  | open_ => decide
  | close => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OldOpenClose) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OldOpenClose × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OldOpenClose) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OldOpenClose) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OldOpenClose) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OldOpenClose

/-- Give Up Trade: one byte code -/
def GiveUpTrade.codes : List UInt8 :=
  [0x50, 0x41, 0x52]

inductive GiveUpTrade where
  | p -- P
  | a -- A
  | r -- R
  | unlisted (byte : { byte : UInt8 // byte ∉ GiveUpTrade.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace GiveUpTrade

def toByte : GiveUpTrade → UInt8
  | .p => 0x50
  | .a => 0x41
  | .r => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : GiveUpTrade :=
  if byte = 0x50 then .p
  else if byte = 0x41 then .a
  else .r

def ofByte (byte : UInt8) : GiveUpTrade :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : GiveUpTrade) : ofByte value.toByte = value := by
  cases value with
  | p => decide
  | a => decide
  | r => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : GiveUpTrade) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (GiveUpTrade × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : GiveUpTrade) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : GiveUpTrade) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : GiveUpTrade) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end GiveUpTrade

/-- Initiated By Control: one byte code -/
def InitiatedByControl.codes : List UInt8 :=
  [0x59, 0x4E]

inductive InitiatedByControl where
  | initiatedByControl -- Initiated By Control
  | notInitiatedByControl -- Not Initiated By Control
  | unlisted (byte : { byte : UInt8 // byte ∉ InitiatedByControl.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InitiatedByControl

def toByte : InitiatedByControl → UInt8
  | .initiatedByControl => 0x59
  | .notInitiatedByControl => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : InitiatedByControl :=
  if byte = 0x59 then .initiatedByControl
  else .notInitiatedByControl

def ofByte (byte : UInt8) : InitiatedByControl :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InitiatedByControl) : ofByte value.toByte = value := by
  cases value with
  | initiatedByControl => decide
  | notInitiatedByControl => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : InitiatedByControl) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (InitiatedByControl × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : InitiatedByControl) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : InitiatedByControl) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : InitiatedByControl) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end InitiatedByControl

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

/-- Sign On Out Body: 174 bytes -/
structure SignOnOutBody where
  userId : BitVec 32
  password : Alpha 8
  newPassword : Alpha 8
  traderName : Alpha 26
  lastPasswordChangeDate : BitVec 32
  brokerId : Alpha 5
  reserved1 : Alpha 1
  branchId : BitVec 16
  versionNumber : BitVec 32
  endTime : BitVec 32
  secondReserved1 : Alpha 1
  colour : Alpha 50
  thirdReserved1 : Alpha 1
  userType : BitVec 16
  sequenceNumber : Alpha 8
  wsClassName : Alpha 14
  brokerStatus : BrokerStatus
  fourthReserved1 : Alpha 1
  stBrokerEligibilityPerMkt : BitVec 16
  memberType : BitVec 16
  clearingStatus : ClearingStatus
  brokerName : Alpha 25
  deriving DecidableEq, Repr

namespace SignOnOutBody

def encode (message : SignOnOutBody) : List UInt8 :=
  encodeUInt 4 message.userId
    ++ (Alpha.encode message.password
    ++ (Alpha.encode message.newPassword
    ++ (Alpha.encode message.traderName
    ++ (encodeUInt 4 message.lastPasswordChangeDate
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.branchId
    ++ (encodeUInt 4 message.versionNumber
    ++ (encodeUInt 4 message.endTime
    ++ (Alpha.encode message.secondReserved1
    ++ (Alpha.encode message.colour
    ++ (Alpha.encode message.thirdReserved1
    ++ (encodeUInt 2 message.userType
    ++ (Alpha.encode message.sequenceNumber
    ++ (Alpha.encode message.wsClassName
    ++ (BrokerStatus.encode message.brokerStatus
    ++ (Alpha.encode message.fourthReserved1
    ++ (encodeUInt 2 message.stBrokerEligibilityPerMkt
    ++ (encodeUInt 2 message.memberType
    ++ (ClearingStatus.encode message.clearingStatus
    ++ (Alpha.encode message.brokerName)))))))))))))))))))))

def decode (bytes : List UInt8) : Option (SignOnOutBody × List UInt8) := do
  let (userId, bytes) ← decodeUInt 4 bytes
  let (password, bytes) ← Alpha.decode 8 bytes
  let (newPassword, bytes) ← Alpha.decode 8 bytes
  let (traderName, bytes) ← Alpha.decode 26 bytes
  let (lastPasswordChangeDate, bytes) ← decodeUInt 4 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (branchId, bytes) ← decodeUInt 2 bytes
  let (versionNumber, bytes) ← decodeUInt 4 bytes
  let (endTime, bytes) ← decodeUInt 4 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  let (colour, bytes) ← Alpha.decode 50 bytes
  let (thirdReserved1, bytes) ← Alpha.decode 1 bytes
  let (userType, bytes) ← decodeUInt 2 bytes
  let (sequenceNumber, bytes) ← Alpha.decode 8 bytes
  let (wsClassName, bytes) ← Alpha.decode 14 bytes
  let (brokerStatus, bytes) ← BrokerStatus.decode bytes
  let (fourthReserved1, bytes) ← Alpha.decode 1 bytes
  let (stBrokerEligibilityPerMkt, bytes) ← decodeUInt 2 bytes
  let (memberType, bytes) ← decodeUInt 2 bytes
  let (clearingStatus, bytes) ← ClearingStatus.decode bytes
  let (brokerName, bytes) ← Alpha.decode 25 bytes
  pure ({ userId, password, newPassword, traderName, lastPasswordChangeDate, brokerId, reserved1, branchId, versionNumber, endTime, secondReserved1, colour, thirdReserved1, userType, sequenceNumber, wsClassName, brokerStatus, fourthReserved1, stBrokerEligibilityPerMkt, memberType, clearingStatus, brokerName }, bytes)

@[simp] theorem encode_length (message : SignOnOutBody) : (encode message).length = 174 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, BrokerStatus.encode_length, ClearingStatus.encode_length]

theorem encode_length_pos (message : SignOnOutBody) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SignOnOutBody) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ClearingStatus.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SignOnOutBody

/-- Error Response Body: 142 bytes -/
structure ErrorResponseBody where
  key : Alpha 14
  errorMessage : Alpha 128
  deriving DecidableEq, Repr

namespace ErrorResponseBody

def encode (message : ErrorResponseBody) : List UInt8 :=
  Alpha.encode message.key
    ++ (Alpha.encode message.errorMessage)

def decode (bytes : List UInt8) : Option (ErrorResponseBody × List UInt8) := do
  let (key, bytes) ← Alpha.decode 14 bytes
  let (errorMessage, bytes) ← Alpha.decode 128 bytes
  pure ({ key, errorMessage }, bytes)

@[simp] theorem encode_length (message : ErrorResponseBody) : (encode message).length = 142 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : ErrorResponseBody) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ErrorResponseBody) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ErrorResponseBody

/-- Sign On Request Out Message -/
structure SignOnRequestOutMessage where
  signOnResponseBody : SignOnOutBody ⊕ (ErrorResponseBody)
  deriving DecidableEq, Repr

namespace SignOnRequestOutMessage

def encode (message : SignOnRequestOutMessage) : List UInt8 :=
  encodeEither SignOnOutBody.encode (ErrorResponseBody.encode) message.signOnResponseBody

def decode (bytes : List UInt8) : Option SignOnRequestOutMessage := do
  let signOnResponseBody ← decodeByWidth 174 (decodeWhole SignOnOutBody.decode) ((decodeWhole ErrorResponseBody.decode)) bytes
  pure { signOnResponseBody }

theorem decode_encode (message : SignOnRequestOutMessage) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeByWidth_encodeEither SignOnOutBody.encode (decodeWhole SignOnOutBody.decode) (ErrorResponseBody.encode) ((decodeWhole ErrorResponseBody.decode)) 174 SignOnOutBody.encode_length (by intro item; simp [ErrorResponseBody.encode_length]) (decodeWhole_encode SignOnOutBody.encode SignOnOutBody.decode SignOnOutBody.decode_encode) ((decodeWhole_encode ErrorResponseBody.encode ErrorResponseBody.decode ErrorResponseBody.decode_encode)), some_bind]
  rfl

end SignOnRequestOutMessage

/-- Sign Off Request Out Message: 150 bytes -/
structure SignOffRequestOutMessage where
  userId : BitVec 32
  reserved145 : Alpha 145
  reserved1 : Alpha 1
  deriving DecidableEq, Repr

namespace SignOffRequestOutMessage

def encode (message : SignOffRequestOutMessage) : List UInt8 :=
  encodeUInt 4 message.userId
    ++ (Alpha.encode message.reserved145
    ++ (Alpha.encode message.reserved1))

def decode (bytes : List UInt8) : Option (SignOffRequestOutMessage × List UInt8) := do
  let (userId, bytes) ← decodeUInt 4 bytes
  let (reserved145, bytes) ← Alpha.decode 145 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  pure ({ userId, reserved145, reserved1 }, bytes)

@[simp] theorem encode_length (message : SignOffRequestOutMessage) : (encode message).length = 150 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : SignOffRequestOutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SignOffRequestOutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SignOffRequestOutMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SignOffRequestOutMessage

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

/-- System Information Out Message: 66 bytes -/
structure SystemInformationOutMessage where
  stMarketStatus : StMarketStatus
  stExMarketStatus : StExMarketStatus
  stPlMarketStatus : StPlMarketStatus
  updatePortfolio : Alpha 1
  cFiller : Alpha 1
  marketIndex : BitVec 32
  defaultSettlementPeriodNormal : BitVec 16
  defaultSettlementPeriodSpot : BitVec 16
  defaultSettlementPeriodAuction : BitVec 16
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  warningPercent : BitVec 16
  volumeFreezePercent : BitVec 16
  snapQuoteTime : BitVec 16
  reserved2 : Alpha 2
  boardLotQuantity : BitVec 32
  tickSize : BitVec 32
  maximumGtcDays : BitVec 16
  stStockEligibleIndicators : BitVec 16
  disclosedQuantityPercentAllowed : BitVec 16
  riskFreeInterestRate : BitVec 32
  deriving DecidableEq, Repr

namespace SystemInformationOutMessage

def encode (message : SystemInformationOutMessage) : List UInt8 :=
  StMarketStatus.encode message.stMarketStatus
    ++ (StExMarketStatus.encode message.stExMarketStatus
    ++ (StPlMarketStatus.encode message.stPlMarketStatus
    ++ (Alpha.encode message.updatePortfolio
    ++ (Alpha.encode message.cFiller
    ++ (encodeUInt 4 message.marketIndex
    ++ (encodeUInt 2 message.defaultSettlementPeriodNormal
    ++ (encodeUInt 2 message.defaultSettlementPeriodSpot
    ++ (encodeUInt 2 message.defaultSettlementPeriodAuction
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (encodeUInt 2 message.warningPercent
    ++ (encodeUInt 2 message.volumeFreezePercent
    ++ (encodeUInt 2 message.snapQuoteTime
    ++ (Alpha.encode message.reserved2
    ++ (encodeUInt 4 message.boardLotQuantity
    ++ (encodeUInt 4 message.tickSize
    ++ (encodeUInt 2 message.maximumGtcDays
    ++ (encodeUInt 2 message.stStockEligibleIndicators
    ++ (encodeUInt 2 message.disclosedQuantityPercentAllowed
    ++ (encodeUInt 4 message.riskFreeInterestRate))))))))))))))))))))

def decode (bytes : List UInt8) : Option (SystemInformationOutMessage × List UInt8) := do
  let (stMarketStatus, bytes) ← StMarketStatus.decode bytes
  let (stExMarketStatus, bytes) ← StExMarketStatus.decode bytes
  let (stPlMarketStatus, bytes) ← StPlMarketStatus.decode bytes
  let (updatePortfolio, bytes) ← Alpha.decode 1 bytes
  let (cFiller, bytes) ← Alpha.decode 1 bytes
  let (marketIndex, bytes) ← decodeUInt 4 bytes
  let (defaultSettlementPeriodNormal, bytes) ← decodeUInt 2 bytes
  let (defaultSettlementPeriodSpot, bytes) ← decodeUInt 2 bytes
  let (defaultSettlementPeriodAuction, bytes) ← decodeUInt 2 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (warningPercent, bytes) ← decodeUInt 2 bytes
  let (volumeFreezePercent, bytes) ← decodeUInt 2 bytes
  let (snapQuoteTime, bytes) ← decodeUInt 2 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (boardLotQuantity, bytes) ← decodeUInt 4 bytes
  let (tickSize, bytes) ← decodeUInt 4 bytes
  let (maximumGtcDays, bytes) ← decodeUInt 2 bytes
  let (stStockEligibleIndicators, bytes) ← decodeUInt 2 bytes
  let (disclosedQuantityPercentAllowed, bytes) ← decodeUInt 2 bytes
  let (riskFreeInterestRate, bytes) ← decodeUInt 4 bytes
  pure ({ stMarketStatus, stExMarketStatus, stPlMarketStatus, updatePortfolio, cFiller, marketIndex, defaultSettlementPeriodNormal, defaultSettlementPeriodSpot, defaultSettlementPeriodAuction, competitorPeriod, solicitorPeriod, warningPercent, volumeFreezePercent, snapQuoteTime, reserved2, boardLotQuantity, tickSize, maximumGtcDays, stStockEligibleIndicators, disclosedQuantityPercentAllowed, riskFreeInterestRate }, bytes)

@[simp] theorem encode_length (message : SystemInformationOutMessage) : (encode message).length = 66 := by
  unfold encode
  simp only [List.length_append, StMarketStatus.encode_length, StExMarketStatus.encode_length, StPlMarketStatus.encode_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SystemInformationOutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemInformationOutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, StMarketStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StExMarketStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StPlMarketStatus.decode_encode, some_bind]
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SystemInformationOutMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SystemInformationOutMessage

/-- Update Local Database Header Message: 2 bytes -/
structure UpdateLocalDatabaseHeaderMessage where
  reserved2 : Alpha 2
  deriving DecidableEq, Repr

namespace UpdateLocalDatabaseHeaderMessage

def encode (message : UpdateLocalDatabaseHeaderMessage) : List UInt8 :=
  Alpha.encode message.reserved2

def decode (bytes : List UInt8) : Option (UpdateLocalDatabaseHeaderMessage × List UInt8) := do
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  pure ({ reserved2 }, bytes)

@[simp] theorem encode_length (message : UpdateLocalDatabaseHeaderMessage) : (encode message).length = 2 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : UpdateLocalDatabaseHeaderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UpdateLocalDatabaseHeaderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : UpdateLocalDatabaseHeaderMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end UpdateLocalDatabaseHeaderMessage

/-- Update Local Database Trailer Message: 2 bytes -/
structure UpdateLocalDatabaseTrailerMessage where
  reserved2 : Alpha 2
  deriving DecidableEq, Repr

namespace UpdateLocalDatabaseTrailerMessage

def encode (message : UpdateLocalDatabaseTrailerMessage) : List UInt8 :=
  Alpha.encode message.reserved2

def decode (bytes : List UInt8) : Option (UpdateLocalDatabaseTrailerMessage × List UInt8) := do
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  pure ({ reserved2 }, bytes)

@[simp] theorem encode_length (message : UpdateLocalDatabaseTrailerMessage) : (encode message).length = 2 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : UpdateLocalDatabaseTrailerMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UpdateLocalDatabaseTrailerMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : UpdateLocalDatabaseTrailerMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end UpdateLocalDatabaseTrailerMessage

/-- Inner Header: 40 bytes -/
structure InnerHeader where
  innerTraderId : BitVec 32
  innerLogTime : BitVec 32
  innerAlphaChar : Alpha 2
  innerTransactionCode : BitVec 16
  innerErrorCode : BitVec 16
  innerTimestamp : Alpha 8
  innerTimeStamp1 : Alpha 8
  innerTimeStamp2 : Alpha 8
  innerMessageLength : BitVec 16
  deriving DecidableEq, Repr

namespace InnerHeader

def encode (message : InnerHeader) : List UInt8 :=
  encodeUInt 4 message.innerTraderId
    ++ (encodeUInt 4 message.innerLogTime
    ++ (Alpha.encode message.innerAlphaChar
    ++ (encodeUInt 2 message.innerTransactionCode
    ++ (encodeUInt 2 message.innerErrorCode
    ++ (Alpha.encode message.innerTimestamp
    ++ (Alpha.encode message.innerTimeStamp1
    ++ (Alpha.encode message.innerTimeStamp2
    ++ (encodeUInt 2 message.innerMessageLength))))))))

def decode (bytes : List UInt8) : Option (InnerHeader × List UInt8) := do
  let (innerTraderId, bytes) ← decodeUInt 4 bytes
  let (innerLogTime, bytes) ← decodeUInt 4 bytes
  let (innerAlphaChar, bytes) ← Alpha.decode 2 bytes
  let (innerTransactionCode, bytes) ← decodeUInt 2 bytes
  let (innerErrorCode, bytes) ← decodeUInt 2 bytes
  let (innerTimestamp, bytes) ← Alpha.decode 8 bytes
  let (innerTimeStamp1, bytes) ← Alpha.decode 8 bytes
  let (innerTimeStamp2, bytes) ← Alpha.decode 8 bytes
  let (innerMessageLength, bytes) ← decodeUInt 2 bytes
  pure ({ innerTraderId, innerLogTime, innerAlphaChar, innerTransactionCode, innerErrorCode, innerTimestamp, innerTimeStamp1, innerTimeStamp2, innerMessageLength }, bytes)

@[simp] theorem encode_length (message : InnerHeader) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : InnerHeader) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InnerHeader) (rest : List UInt8) :
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end InnerHeader

/-- Update Local Database Data Message -/
structure UpdateLocalDatabaseDataMessage where
  innerHeader : InnerHeader
  dataPayload : Capped 65047
  deriving DecidableEq, Repr

namespace UpdateLocalDatabaseDataMessage

def encode (message : UpdateLocalDatabaseDataMessage) : List UInt8 :=
  InnerHeader.encode message.innerHeader
    ++ (message.dataPayload.val)

def decode (bytes : List UInt8) : Option UpdateLocalDatabaseDataMessage := do
  let (innerHeader, bytes) ← InnerHeader.decode bytes
  let dataPayload_ := bytes
  if fits_dataPayload : dataPayload_.length ≤ 65047 then
    pure { innerHeader, dataPayload := ⟨dataPayload_, fits_dataPayload⟩ }
  else none

theorem encode_length_pos (message : UpdateLocalDatabaseDataMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [InnerHeader.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : UpdateLocalDatabaseDataMessage) : (encode message).length ≤ 65087 := by
  have bound_dataPayload := message.dataPayload.length_le
  unfold encode
  simp only [List.length_append, InnerHeader.encode_length]
  omega

theorem decode_encode (message : UpdateLocalDatabaseDataMessage) : decode (encode message) = some message := by
  unfold decode encode
  rw [InnerHeader.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.dataPayload.length_le]
  rfl

end UpdateLocalDatabaseDataMessage

/-- Header Record Message: 0 bytes -/
structure HeaderRecordMessage where
  deriving DecidableEq, Repr

namespace HeaderRecordMessage

def encode (_ : HeaderRecordMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (HeaderRecordMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : HeaderRecordMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : HeaderRecordMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : HeaderRecordMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end HeaderRecordMessage

/-- Message Record Message -/
structure MessageRecordMessage where
  innerHeader : InnerHeader
  downloadPayload : Capped 65047
  deriving DecidableEq, Repr

namespace MessageRecordMessage

def encode (message : MessageRecordMessage) : List UInt8 :=
  InnerHeader.encode message.innerHeader
    ++ (message.downloadPayload.val)

def decode (bytes : List UInt8) : Option MessageRecordMessage := do
  let (innerHeader, bytes) ← InnerHeader.decode bytes
  let downloadPayload_ := bytes
  if fits_downloadPayload : downloadPayload_.length ≤ 65047 then
    pure { innerHeader, downloadPayload := ⟨downloadPayload_, fits_downloadPayload⟩ }
  else none

theorem encode_length_pos (message : MessageRecordMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [InnerHeader.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MessageRecordMessage) : (encode message).length ≤ 65087 := by
  have bound_downloadPayload := message.downloadPayload.length_le
  unfold encode
  simp only [List.length_append, InnerHeader.encode_length]
  omega

theorem decode_encode (message : MessageRecordMessage) : decode (encode message) = some message := by
  unfold decode encode
  rw [InnerHeader.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.downloadPayload.length_le]
  rfl

end MessageRecordMessage

/-- Trailer Record Message: 0 bytes -/
structure TrailerRecordMessage where
  deriving DecidableEq, Repr

namespace TrailerRecordMessage

def encode (_ : TrailerRecordMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (TrailerRecordMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : TrailerRecordMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : TrailerRecordMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : TrailerRecordMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end TrailerRecordMessage

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

/-- Order Confirmation Message: 276 bytes -/
structure OrderConfirmationMessage where
  orderEntryBody : OrderEntryBody
  deriving DecidableEq, Repr

namespace OrderConfirmationMessage

def encode (message : OrderConfirmationMessage) : List UInt8 :=
  OrderEntryBody.encode message.orderEntryBody

def decode (bytes : List UInt8) : Option (OrderConfirmationMessage × List UInt8) := do
  let (orderEntryBody, bytes) ← OrderEntryBody.decode bytes
  pure ({ orderEntryBody }, bytes)

@[simp] theorem encode_length (message : OrderConfirmationMessage) : (encode message).length = 276 := by
  unfold encode
  simp only [OrderEntryBody.encode_length]

theorem encode_length_pos (message : OrderConfirmationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderConfirmationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [OrderEntryBody.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : OrderConfirmationMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end OrderConfirmationMessage

/-- Order Modification Confirmation Message: 276 bytes -/
structure OrderModificationConfirmationMessage where
  orderEntryBody : OrderEntryBody
  deriving DecidableEq, Repr

namespace OrderModificationConfirmationMessage

def encode (message : OrderModificationConfirmationMessage) : List UInt8 :=
  OrderEntryBody.encode message.orderEntryBody

def decode (bytes : List UInt8) : Option (OrderModificationConfirmationMessage × List UInt8) := do
  let (orderEntryBody, bytes) ← OrderEntryBody.decode bytes
  pure ({ orderEntryBody }, bytes)

@[simp] theorem encode_length (message : OrderModificationConfirmationMessage) : (encode message).length = 276 := by
  unfold encode
  simp only [OrderEntryBody.encode_length]

theorem encode_length_pos (message : OrderModificationConfirmationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderModificationConfirmationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [OrderEntryBody.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : OrderModificationConfirmationMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end OrderModificationConfirmationMessage

/-- Order Response Message: 276 bytes -/
structure OrderResponseMessage where
  orderEntryBody : OrderEntryBody
  deriving DecidableEq, Repr

namespace OrderResponseMessage

def encode (message : OrderResponseMessage) : List UInt8 :=
  OrderEntryBody.encode message.orderEntryBody

def decode (bytes : List UInt8) : Option (OrderResponseMessage × List UInt8) := do
  let (orderEntryBody, bytes) ← OrderEntryBody.decode bytes
  pure ({ orderEntryBody }, bytes)

@[simp] theorem encode_length (message : OrderResponseMessage) : (encode message).length = 276 := by
  unfold encode
  simp only [OrderEntryBody.encode_length]

theorem encode_length_pos (message : OrderResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [OrderEntryBody.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : OrderResponseMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end OrderResponseMessage

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

/-- Order Cancellation Confirmation Message -/
structure OrderCancellationConfirmationMessage where
  cancellationConfirmationBody : OrderEntryBody ⊕ (SpreadOrderBody)
  deriving DecidableEq, Repr

namespace OrderCancellationConfirmationMessage

def encode (message : OrderCancellationConfirmationMessage) : List UInt8 :=
  encodeEither OrderEntryBody.encode (SpreadOrderBody.encode) message.cancellationConfirmationBody

def decode (bytes : List UInt8) : Option OrderCancellationConfirmationMessage := do
  let cancellationConfirmationBody ← decodeByWidth 276 (decodeWhole OrderEntryBody.decode) ((decodeWhole SpreadOrderBody.decode)) bytes
  pure { cancellationConfirmationBody }

theorem decode_encode (message : OrderCancellationConfirmationMessage) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeByWidth_encodeEither OrderEntryBody.encode (decodeWhole OrderEntryBody.decode) (SpreadOrderBody.encode) ((decodeWhole SpreadOrderBody.decode)) 276 OrderEntryBody.encode_length (by intro item; simp [SpreadOrderBody.encode_length]) (decodeWhole_encode OrderEntryBody.encode OrderEntryBody.decode OrderEntryBody.decode_encode) ((decodeWhole_encode SpreadOrderBody.encode SpreadOrderBody.decode SpreadOrderBody.decode_encode)), some_bind]
  rfl

end OrderCancellationConfirmationMessage

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

/-- Trade Inquiry Response Message: 194 bytes -/
structure TradeInquiryResponseMessage where
  tradeInquiryBody : TradeInquiryBody
  deriving DecidableEq, Repr

namespace TradeInquiryResponseMessage

def encode (message : TradeInquiryResponseMessage) : List UInt8 :=
  TradeInquiryBody.encode message.tradeInquiryBody

def decode (bytes : List UInt8) : Option (TradeInquiryResponseMessage × List UInt8) := do
  let (tradeInquiryBody, bytes) ← TradeInquiryBody.decode bytes
  pure ({ tradeInquiryBody }, bytes)

@[simp] theorem encode_length (message : TradeInquiryResponseMessage) : (encode message).length = 194 := by
  unfold encode
  simp only [TradeInquiryBody.encode_length]

theorem encode_length_pos (message : TradeInquiryResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeInquiryResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [TradeInquiryBody.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : TradeInquiryResponseMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end TradeInquiryResponseMessage

/-- Trade Confirmation Message: 256 bytes -/
structure TradeConfirmationMessage where
  responseOrderNumber : Alpha 8
  brokerId : Alpha 5
  reserved1 : Alpha 1
  traderNumber : BitVec 32
  accountNumber : Alpha 10
  buySellIndicator : BitVec 16
  originalVolume : BitVec 32
  disclosedVolume : BitVec 32
  remainingVolume : BitVec 32
  disclosedVolumeRemaining : BitVec 32
  price : BitVec 32
  stOrderFlags : BitVec 16
  goodTillDate : BitVec 32
  fillNumber : BitVec 32
  fillQuantity : BitVec 32
  fillPrice : BitVec 32
  volumeFilledToday : BitVec 32
  activityType : Alpha 2
  activityTime : BitVec 32
  counterTraderOrderNumber : Alpha 8
  counterBrokerId : Alpha 5
  secondReserved1 : Alpha 1
  token : BitVec 32
  contractDesc : ContractDesc
  openClose : OpenClose
  oldOpenClose : OldOpenClose
  tradeBookType : Alpha 1
  thirdReserved1 : Alpha 1
  newVolume : BitVec 32
  oldAccountNumber : Alpha 10
  participant : Alpha 12
  oldParticipant : Alpha 12
  additionalOrderFlags : BitVec 8
  fourthReserved1 : Alpha 1
  giveUpTrade : GiveUpTrade
  fifthReserved1 : Alpha 1
  reserved10 : Alpha 10
  echoBack : Alpha 16
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  deriving DecidableEq, Repr

namespace TradeConfirmationMessage

def encode (message : TradeConfirmationMessage) : List UInt8 :=
  Alpha.encode message.responseOrderNumber
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 4 message.traderNumber
    ++ (Alpha.encode message.accountNumber
    ++ (encodeUInt 2 message.buySellIndicator
    ++ (encodeUInt 4 message.originalVolume
    ++ (encodeUInt 4 message.disclosedVolume
    ++ (encodeUInt 4 message.remainingVolume
    ++ (encodeUInt 4 message.disclosedVolumeRemaining
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 4 message.goodTillDate
    ++ (encodeUInt 4 message.fillNumber
    ++ (encodeUInt 4 message.fillQuantity
    ++ (encodeUInt 4 message.fillPrice
    ++ (encodeUInt 4 message.volumeFilledToday
    ++ (Alpha.encode message.activityType
    ++ (encodeUInt 4 message.activityTime
    ++ (Alpha.encode message.counterTraderOrderNumber
    ++ (Alpha.encode message.counterBrokerId
    ++ (Alpha.encode message.secondReserved1
    ++ (encodeUInt 4 message.token
    ++ (ContractDesc.encode message.contractDesc
    ++ (OpenClose.encode message.openClose
    ++ (OldOpenClose.encode message.oldOpenClose
    ++ (Alpha.encode message.tradeBookType
    ++ (Alpha.encode message.thirdReserved1
    ++ (encodeUInt 4 message.newVolume
    ++ (Alpha.encode message.oldAccountNumber
    ++ (Alpha.encode message.participant
    ++ (Alpha.encode message.oldParticipant
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.fourthReserved1
    ++ (GiveUpTrade.encode message.giveUpTrade
    ++ (Alpha.encode message.fifthReserved1
    ++ (Alpha.encode message.reserved10
    ++ (Alpha.encode message.echoBack
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52)))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TradeConfirmationMessage × List UInt8) := do
  let (responseOrderNumber, bytes) ← Alpha.decode 8 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (traderNumber, bytes) ← decodeUInt 4 bytes
  let (accountNumber, bytes) ← Alpha.decode 10 bytes
  let (buySellIndicator, bytes) ← decodeUInt 2 bytes
  let (originalVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolume, bytes) ← decodeUInt 4 bytes
  let (remainingVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolumeRemaining, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (goodTillDate, bytes) ← decodeUInt 4 bytes
  let (fillNumber, bytes) ← decodeUInt 4 bytes
  let (fillQuantity, bytes) ← decodeUInt 4 bytes
  let (fillPrice, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday, bytes) ← decodeUInt 4 bytes
  let (activityType, bytes) ← Alpha.decode 2 bytes
  let (activityTime, bytes) ← decodeUInt 4 bytes
  let (counterTraderOrderNumber, bytes) ← Alpha.decode 8 bytes
  let (counterBrokerId, bytes) ← Alpha.decode 5 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  let (token, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (openClose, bytes) ← OpenClose.decode bytes
  let (oldOpenClose, bytes) ← OldOpenClose.decode bytes
  let (tradeBookType, bytes) ← Alpha.decode 1 bytes
  let (thirdReserved1, bytes) ← Alpha.decode 1 bytes
  let (newVolume, bytes) ← decodeUInt 4 bytes
  let (oldAccountNumber, bytes) ← Alpha.decode 10 bytes
  let (participant, bytes) ← Alpha.decode 12 bytes
  let (oldParticipant, bytes) ← Alpha.decode 12 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (fourthReserved1, bytes) ← Alpha.decode 1 bytes
  let (giveUpTrade, bytes) ← GiveUpTrade.decode bytes
  let (fifthReserved1, bytes) ← Alpha.decode 1 bytes
  let (reserved10, bytes) ← Alpha.decode 10 bytes
  let (echoBack, bytes) ← Alpha.decode 16 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  pure ({ responseOrderNumber, brokerId, reserved1, traderNumber, accountNumber, buySellIndicator, originalVolume, disclosedVolume, remainingVolume, disclosedVolumeRemaining, price, stOrderFlags, goodTillDate, fillNumber, fillQuantity, fillPrice, volumeFilledToday, activityType, activityTime, counterTraderOrderNumber, counterBrokerId, secondReserved1, token, contractDesc, openClose, oldOpenClose, tradeBookType, thirdReserved1, newVolume, oldAccountNumber, participant, oldParticipant, additionalOrderFlags, fourthReserved1, giveUpTrade, fifthReserved1, reserved10, echoBack, lastActivityReference, reserved52 }, bytes)

@[simp] theorem encode_length (message : TradeConfirmationMessage) : (encode message).length = 256 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, OpenClose.encode_length, OldOpenClose.encode_length, encodeUIntLE_length, GiveUpTrade.encode_length]

theorem encode_length_pos (message : TradeConfirmationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : TradeConfirmationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpenClose.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OldOpenClose.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, GiveUpTrade.decode_encode, some_bind]
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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : TradeConfirmationMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end TradeConfirmationMessage

/-- Spread Order Response Message: 440 bytes -/
structure SpreadOrderResponseMessage where
  spreadOrderBody : SpreadOrderBody
  deriving DecidableEq, Repr

namespace SpreadOrderResponseMessage

def encode (message : SpreadOrderResponseMessage) : List UInt8 :=
  SpreadOrderBody.encode message.spreadOrderBody

def decode (bytes : List UInt8) : Option (SpreadOrderResponseMessage × List UInt8) := do
  let (spreadOrderBody, bytes) ← SpreadOrderBody.decode bytes
  pure ({ spreadOrderBody }, bytes)

@[simp] theorem encode_length (message : SpreadOrderResponseMessage) : (encode message).length = 440 := by
  unfold encode
  simp only [SpreadOrderBody.encode_length]

theorem encode_length_pos (message : SpreadOrderResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SpreadOrderResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [SpreadOrderBody.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SpreadOrderResponseMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SpreadOrderResponseMessage

/-- Instrument User: 64 bytes -/
structure InstrumentUser where
  branchBuyValueLimit : Alpha 8
  branchSellValueLimit : Alpha 8
  branchUsedBuyValueLimit : Alpha 8
  branchUsedSellValueLimit : Alpha 8
  userOrderBuyValueLimit : Alpha 8
  userOrderSellValueLimit : Alpha 8
  userOrderUsedBuyValueLimit : Alpha 8
  userOrderUsedSellValueLimit : Alpha 8
  deriving DecidableEq, Repr

namespace InstrumentUser

def encode (message : InstrumentUser) : List UInt8 :=
  Alpha.encode message.branchBuyValueLimit
    ++ (Alpha.encode message.branchSellValueLimit
    ++ (Alpha.encode message.branchUsedBuyValueLimit
    ++ (Alpha.encode message.branchUsedSellValueLimit
    ++ (Alpha.encode message.userOrderBuyValueLimit
    ++ (Alpha.encode message.userOrderSellValueLimit
    ++ (Alpha.encode message.userOrderUsedBuyValueLimit
    ++ (Alpha.encode message.userOrderUsedSellValueLimit)))))))

def decode (bytes : List UInt8) : Option (InstrumentUser × List UInt8) := do
  let (branchBuyValueLimit, bytes) ← Alpha.decode 8 bytes
  let (branchSellValueLimit, bytes) ← Alpha.decode 8 bytes
  let (branchUsedBuyValueLimit, bytes) ← Alpha.decode 8 bytes
  let (branchUsedSellValueLimit, bytes) ← Alpha.decode 8 bytes
  let (userOrderBuyValueLimit, bytes) ← Alpha.decode 8 bytes
  let (userOrderSellValueLimit, bytes) ← Alpha.decode 8 bytes
  let (userOrderUsedBuyValueLimit, bytes) ← Alpha.decode 8 bytes
  let (userOrderUsedSellValueLimit, bytes) ← Alpha.decode 8 bytes
  pure ({ branchBuyValueLimit, branchSellValueLimit, branchUsedBuyValueLimit, branchUsedSellValueLimit, userOrderBuyValueLimit, userOrderSellValueLimit, userOrderUsedBuyValueLimit, userOrderUsedSellValueLimit }, bytes)

@[simp] theorem encode_length (message : InstrumentUser) : (encode message).length = 64 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : InstrumentUser) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentUser) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end InstrumentUser

/-- User Order Limit Body: 166 bytes -/
structure UserOrderLimitBody where
  brokerId : Alpha 5
  branchId : BitVec 16
  userName : Alpha 25
  userId : BitVec 32
  userType : BitVec 16
  instrumentUser : Exact 2 InstrumentUser
  deriving DecidableEq, Repr

namespace UserOrderLimitBody

def encode (message : UserOrderLimitBody) : List UInt8 :=
  Alpha.encode message.brokerId
    ++ (encodeUInt 2 message.branchId
    ++ (Alpha.encode message.userName
    ++ (encodeUInt 4 message.userId
    ++ (encodeUInt 2 message.userType
    ++ (encodeMany InstrumentUser.encode message.instrumentUser.val)))))

def decode (bytes : List UInt8) : Option (UserOrderLimitBody × List UInt8) := do
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (branchId, bytes) ← decodeUInt 2 bytes
  let (userName, bytes) ← Alpha.decode 25 bytes
  let (userId, bytes) ← decodeUInt 4 bytes
  let (userType, bytes) ← decodeUInt 2 bytes
  let (instrumentUser_, bytes) ← decodeMany InstrumentUser.decode 2 bytes
  if fits_instrumentUser : instrumentUser_.length = 2 then
    pure ({ brokerId, branchId, userName, userId, userType, instrumentUser := ⟨instrumentUser_, fits_instrumentUser⟩ }, bytes)
  else none

@[simp] theorem encode_length (message : UserOrderLimitBody) : (encode message).length = 166 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, encodeMany_length_const InstrumentUser.encode 64 InstrumentUser.encode_length, message.instrumentUser.length_eq]

theorem encode_length_pos (message : UserOrderLimitBody) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UserOrderLimitBody) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_exact 2 InstrumentUser.encode InstrumentUser.decode InstrumentUser.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.instrumentUser.length_eq]
  rfl

end UserOrderLimitBody

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

/-- User Order Limit Update Message -/
structure UserOrderLimitUpdateMessage where
  userLimitResponseBody : UserOrderLimitBody ⊕ (UserOrderValueLimitBody ⊕ (ErrorResponseBody))
  deriving DecidableEq, Repr

namespace UserOrderLimitUpdateMessage

def encode (message : UserOrderLimitUpdateMessage) : List UInt8 :=
  encodeEither UserOrderLimitBody.encode (encodeEither UserOrderValueLimitBody.encode (ErrorResponseBody.encode)) message.userLimitResponseBody

def decode (bytes : List UInt8) : Option UserOrderLimitUpdateMessage := do
  let userLimitResponseBody ← decodeByWidth 166 (decodeWhole UserOrderLimitBody.decode) (decodeByWidth 168 (decodeWhole UserOrderValueLimitBody.decode) ((decodeWhole ErrorResponseBody.decode))) bytes
  pure { userLimitResponseBody }

theorem decode_encode (message : UserOrderLimitUpdateMessage) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeByWidth_encodeEither UserOrderLimitBody.encode (decodeWhole UserOrderLimitBody.decode) (encodeEither UserOrderValueLimitBody.encode (ErrorResponseBody.encode)) (decodeByWidth 168 (decodeWhole UserOrderValueLimitBody.decode) ((decodeWhole ErrorResponseBody.decode))) 166 UserOrderLimitBody.encode_length (by intro item; rcases item with item | item <;> simp [encodeEither, UserOrderValueLimitBody.encode_length, ErrorResponseBody.encode_length]) (decodeWhole_encode UserOrderLimitBody.encode UserOrderLimitBody.decode UserOrderLimitBody.decode_encode) (decodeByWidth_encodeEither UserOrderValueLimitBody.encode (decodeWhole UserOrderValueLimitBody.decode) (ErrorResponseBody.encode) ((decodeWhole ErrorResponseBody.decode)) 168 UserOrderValueLimitBody.encode_length (by intro item; simp [ErrorResponseBody.encode_length]) (decodeWhole_encode UserOrderValueLimitBody.encode UserOrderValueLimitBody.decode UserOrderValueLimitBody.decode_encode) ((decodeWhole_encode ErrorResponseBody.encode ErrorResponseBody.decode ErrorResponseBody.decode_encode))), some_bind]
  rfl

end UserOrderLimitUpdateMessage

/-- Dealer Limit Update Message: 26 bytes -/
structure DealerLimitUpdateMessage where
  brokerId : Alpha 5
  reserved1 : Alpha 1
  userId : BitVec 32
  ordQtyBuff : Alpha 8
  ordValBuff : Alpha 8
  deriving DecidableEq, Repr

namespace DealerLimitUpdateMessage

def encode (message : DealerLimitUpdateMessage) : List UInt8 :=
  Alpha.encode message.brokerId
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 4 message.userId
    ++ (Alpha.encode message.ordQtyBuff
    ++ (Alpha.encode message.ordValBuff))))

def decode (bytes : List UInt8) : Option (DealerLimitUpdateMessage × List UInt8) := do
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (userId, bytes) ← decodeUInt 4 bytes
  let (ordQtyBuff, bytes) ← Alpha.decode 8 bytes
  let (ordValBuff, bytes) ← Alpha.decode 8 bytes
  pure ({ brokerId, reserved1, userId, ordQtyBuff, ordValBuff }, bytes)

@[simp] theorem encode_length (message : DealerLimitUpdateMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : DealerLimitUpdateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DealerLimitUpdateMessage) (rest : List UInt8) :
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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : DealerLimitUpdateMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end DealerLimitUpdateMessage

/-- Spread Order Limit Update Message: 26 bytes -/
structure SpreadOrderLimitUpdateMessage where
  brokerId : Alpha 5
  reserved1 : Alpha 1
  userId : BitVec 32
  spdOrdQtyBuff : Alpha 8
  spdOrdValBuff : Alpha 8
  deriving DecidableEq, Repr

namespace SpreadOrderLimitUpdateMessage

def encode (message : SpreadOrderLimitUpdateMessage) : List UInt8 :=
  Alpha.encode message.brokerId
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 4 message.userId
    ++ (Alpha.encode message.spdOrdQtyBuff
    ++ (Alpha.encode message.spdOrdValBuff))))

def decode (bytes : List UInt8) : Option (SpreadOrderLimitUpdateMessage × List UInt8) := do
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (userId, bytes) ← decodeUInt 4 bytes
  let (spdOrdQtyBuff, bytes) ← Alpha.decode 8 bytes
  let (spdOrdValBuff, bytes) ← Alpha.decode 8 bytes
  pure ({ brokerId, reserved1, userId, spdOrdQtyBuff, spdOrdValBuff }, bytes)

@[simp] theorem encode_length (message : SpreadOrderLimitUpdateMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SpreadOrderLimitUpdateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SpreadOrderLimitUpdateMessage) (rest : List UInt8) :
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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SpreadOrderLimitUpdateMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SpreadOrderLimitUpdateMessage

/-- Control Message To Trader Message: 250 bytes -/
structure ControlMessageToTraderMessage where
  traderId : BitVec 32
  actionCode : Alpha 3
  reserved1 : Alpha 1
  broadCastMessageLength : BitVec 16
  broadCastMessage : Alpha 239
  secondReserved1 : Alpha 1
  deriving DecidableEq, Repr

namespace ControlMessageToTraderMessage

def encode (message : ControlMessageToTraderMessage) : List UInt8 :=
  encodeUInt 4 message.traderId
    ++ (Alpha.encode message.actionCode
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.broadCastMessageLength
    ++ (Alpha.encode message.broadCastMessage
    ++ (Alpha.encode message.secondReserved1)))))

def decode (bytes : List UInt8) : Option (ControlMessageToTraderMessage × List UInt8) := do
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (actionCode, bytes) ← Alpha.decode 3 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (broadCastMessageLength, bytes) ← decodeUInt 2 bytes
  let (broadCastMessage, bytes) ← Alpha.decode 239 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  pure ({ traderId, actionCode, reserved1, broadCastMessageLength, broadCastMessage, secondReserved1 }, bytes)

@[simp] theorem encode_length (message : ControlMessageToTraderMessage) : (encode message).length = 250 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : ControlMessageToTraderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ControlMessageToTraderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ControlMessageToTraderMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ControlMessageToTraderMessage

/-- Mba Inquiry Result: 24 bytes -/
structure MbaInquiryResult where
  cumulativeQuantity : BitVec 32
  totalValue : Alpha 8
  wap : BitVec 32
  impactCost : BitVec 32
  orderPrice : BitVec 32
  deriving DecidableEq, Repr

namespace MbaInquiryResult

def encode (message : MbaInquiryResult) : List UInt8 :=
  encodeUInt 4 message.cumulativeQuantity
    ++ (Alpha.encode message.totalValue
    ++ (encodeUInt 4 message.wap
    ++ (encodeUInt 4 message.impactCost
    ++ (encodeUInt 4 message.orderPrice))))

def decode (bytes : List UInt8) : Option (MbaInquiryResult × List UInt8) := do
  let (cumulativeQuantity, bytes) ← decodeUInt 4 bytes
  let (totalValue, bytes) ← Alpha.decode 8 bytes
  let (wap, bytes) ← decodeUInt 4 bytes
  let (impactCost, bytes) ← decodeUInt 4 bytes
  let (orderPrice, bytes) ← decodeUInt 4 bytes
  pure ({ cumulativeQuantity, totalValue, wap, impactCost, orderPrice }, bytes)

@[simp] theorem encode_length (message : MbaInquiryResult) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : MbaInquiryResult) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MbaInquiryResult) (rest : List UInt8) :
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

end MbaInquiryResult

/-- Mba Inquiry Response Message: 32 bytes -/
structure MbaInquiryResponseMessage where
  token : BitVec 32
  book : BitVec 16
  buySell : BitVec 16
  mbaInquiryResult : MbaInquiryResult
  deriving DecidableEq, Repr

namespace MbaInquiryResponseMessage

def encode (message : MbaInquiryResponseMessage) : List UInt8 :=
  encodeUInt 4 message.token
    ++ (encodeUInt 2 message.book
    ++ (encodeUInt 2 message.buySell
    ++ (MbaInquiryResult.encode message.mbaInquiryResult)))

def decode (bytes : List UInt8) : Option (MbaInquiryResponseMessage × List UInt8) := do
  let (token, bytes) ← decodeUInt 4 bytes
  let (book, bytes) ← decodeUInt 2 bytes
  let (buySell, bytes) ← decodeUInt 2 bytes
  let (mbaInquiryResult, bytes) ← MbaInquiryResult.decode bytes
  pure ({ token, book, buySell, mbaInquiryResult }, bytes)

@[simp] theorem encode_length (message : MbaInquiryResponseMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, MbaInquiryResult.encode_length]

theorem encode_length_pos (message : MbaInquiryResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MbaInquiryResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [MbaInquiryResult.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : MbaInquiryResponseMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end MbaInquiryResponseMessage

/-- Report Header Body: 67 bytes -/
structure ReportHeaderBody where
  orgScope : Alpha 1
  reportDate : BitVec 32
  userType : BitVec 16
  brokerId : Alpha 5
  firmName : Alpha 25
  traderNumber : BitVec 32
  traderName : Alpha 26
  deriving DecidableEq, Repr

namespace ReportHeaderBody

def encode (message : ReportHeaderBody) : List UInt8 :=
  Alpha.encode message.orgScope
    ++ (encodeUInt 4 message.reportDate
    ++ (encodeUInt 2 message.userType
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.firmName
    ++ (encodeUInt 4 message.traderNumber
    ++ (Alpha.encode message.traderName))))))

def decode (bytes : List UInt8) : Option (ReportHeaderBody × List UInt8) := do
  let (orgScope, bytes) ← Alpha.decode 1 bytes
  let (reportDate, bytes) ← decodeUInt 4 bytes
  let (userType, bytes) ← decodeUInt 2 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (firmName, bytes) ← Alpha.decode 25 bytes
  let (traderNumber, bytes) ← decodeUInt 4 bytes
  let (traderName, bytes) ← Alpha.decode 26 bytes
  pure ({ orgScope, reportDate, userType, brokerId, firmName, traderNumber, traderName }, bytes)

@[simp] theorem encode_length (message : ReportHeaderBody) : (encode message).length = 67 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ReportHeaderBody) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReportHeaderBody) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ReportHeaderBody

/-- Mkt Stats Data: 74 bytes -/
structure MktStatsData where
  contractDesc : ContractDesc
  marketType : BitVec 16
  openPrice : BitVec 32
  highPrice : BitVec 32
  lowPrice : BitVec 32
  closingPrice : BitVec 32
  totalQuantityTraded : BitVec 32
  totalValueTraded : Alpha 8
  previousClosePrice : BitVec 32
  openInterest : BitVec 32
  chgOpenInterest : BitVec 32
  indicator : Alpha 4
  deriving DecidableEq, Repr

namespace MktStatsData

def encode (message : MktStatsData) : List UInt8 :=
  ContractDesc.encode message.contractDesc
    ++ (encodeUInt 2 message.marketType
    ++ (encodeUInt 4 message.openPrice
    ++ (encodeUInt 4 message.highPrice
    ++ (encodeUInt 4 message.lowPrice
    ++ (encodeUInt 4 message.closingPrice
    ++ (encodeUInt 4 message.totalQuantityTraded
    ++ (Alpha.encode message.totalValueTraded
    ++ (encodeUInt 4 message.previousClosePrice
    ++ (encodeUInt 4 message.openInterest
    ++ (encodeUInt 4 message.chgOpenInterest
    ++ (Alpha.encode message.indicator)))))))))))

def decode (bytes : List UInt8) : Option (MktStatsData × List UInt8) := do
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (marketType, bytes) ← decodeUInt 2 bytes
  let (openPrice, bytes) ← decodeUInt 4 bytes
  let (highPrice, bytes) ← decodeUInt 4 bytes
  let (lowPrice, bytes) ← decodeUInt 4 bytes
  let (closingPrice, bytes) ← decodeUInt 4 bytes
  let (totalQuantityTraded, bytes) ← decodeUInt 4 bytes
  let (totalValueTraded, bytes) ← Alpha.decode 8 bytes
  let (previousClosePrice, bytes) ← decodeUInt 4 bytes
  let (openInterest, bytes) ← decodeUInt 4 bytes
  let (chgOpenInterest, bytes) ← decodeUInt 4 bytes
  let (indicator, bytes) ← Alpha.decode 4 bytes
  pure ({ contractDesc, marketType, openPrice, highPrice, lowPrice, closingPrice, totalQuantityTraded, totalValueTraded, previousClosePrice, openInterest, chgOpenInterest, indicator }, bytes)

@[simp] theorem encode_length (message : MktStatsData) : (encode message).length = 74 := by
  unfold encode
  simp only [List.length_append, ContractDesc.encode_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : MktStatsData) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MktStatsData) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MktStatsData

/-- Report Statistics Body: 447 bytes -/
structure ReportStatisticsBody where
  reserved1 : Alpha 1
  numberOfRecords : BitVec 16
  mktStatsData : Exact 6 MktStatsData
  deriving DecidableEq, Repr

namespace ReportStatisticsBody

def encode (message : ReportStatisticsBody) : List UInt8 :=
  Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.numberOfRecords
    ++ (encodeMany MktStatsData.encode message.mktStatsData.val))

def decode (bytes : List UInt8) : Option (ReportStatisticsBody × List UInt8) := do
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (numberOfRecords, bytes) ← decodeUInt 2 bytes
  let (mktStatsData_, bytes) ← decodeMany MktStatsData.decode 6 bytes
  if fits_mktStatsData : mktStatsData_.length = 6 then
    pure ({ reserved1, numberOfRecords, mktStatsData := ⟨mktStatsData_, fits_mktStatsData⟩ }, bytes)
  else none

@[simp] theorem encode_length (message : ReportStatisticsBody) : (encode message).length = 447 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, encodeMany_length_const MktStatsData.encode 74 MktStatsData.encode_length, message.mktStatsData.length_eq]

theorem encode_length_pos (message : ReportStatisticsBody) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReportStatisticsBody) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_exact 6 MktStatsData.encode MktStatsData.decode MktStatsData.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.mktStatsData.length_eq]
  rfl

end ReportStatisticsBody

/-- Report Trailer Body: 5 bytes -/
structure ReportTrailerBody where
  numberOfPackets : BitVec 32
  reserved1 : Alpha 1
  deriving DecidableEq, Repr

namespace ReportTrailerBody

def encode (message : ReportTrailerBody) : List UInt8 :=
  encodeUInt 4 message.numberOfPackets
    ++ (Alpha.encode message.reserved1)

def decode (bytes : List UInt8) : Option (ReportTrailerBody × List UInt8) := do
  let (numberOfPackets, bytes) ← decodeUInt 4 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  pure ({ numberOfPackets, reserved1 }, bytes)

@[simp] theorem encode_length (message : ReportTrailerBody) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : ReportTrailerBody) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReportTrailerBody) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ReportTrailerBody

/-- Any Report Body, selected by Message Type -/
inductive ReportBody where
  | reportHeaderBody (message : ReportHeaderBody) -- "H" 0x48
  | reportStatisticsBody (message : ReportStatisticsBody) -- "R" 0x52
  | reportTrailerBody (message : ReportTrailerBody) -- "T" 0x54
  deriving DecidableEq, Repr

namespace ReportBody

/-- The Message Type each message is sent under -/
def tag : ReportBody → BitVec 8
  | .reportHeaderBody _ => 72
  | .reportStatisticsBody _ => 82
  | .reportTrailerBody _ => 84

def encode : ReportBody → List UInt8
  | .reportHeaderBody message => ReportHeaderBody.encode message
  | .reportStatisticsBody message => ReportStatisticsBody.encode message
  | .reportTrailerBody message => ReportTrailerBody.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ReportBody) : (encode message).length ≤ 447 := by
  cases message with
  | reportHeaderBody inner =>
    simp only [encode, ReportHeaderBody.encode_length]
    omega
  | reportStatisticsBody inner =>
    simp only [encode, ReportStatisticsBody.encode_length]
    omega
  | reportTrailerBody inner =>
    simp only [encode, ReportTrailerBody.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (ReportBody × List UInt8) :=
  if tag = 72 then (ReportHeaderBody.decode bytes).map fun (message, rest) => (.reportHeaderBody message, rest)
  else if tag = 82 then (ReportStatisticsBody.decode bytes).map fun (message, rest) => (.reportStatisticsBody message, rest)
  else if tag = 84 then (ReportTrailerBody.decode bytes).map fun (message, rest) => (.reportTrailerBody message, rest)
  else none

@[simp] theorem decode_encode (message : ReportBody) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ReportBody

/-- Market Statistics Report Message -/
structure MarketStatisticsReportMessage where
  reportBody : ReportBody
  deriving DecidableEq, Repr

namespace MarketStatisticsReportMessage

def encode (message : MarketStatisticsReportMessage) : List UInt8 :=
  encodeUInt 1 (ReportBody.tag message.reportBody)
    ++ (ReportBody.encode message.reportBody)

def decode (bytes : List UInt8) : Option (MarketStatisticsReportMessage × List UInt8) := do
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (reportBody, bytes) ← ReportBody.decode messageType bytes
  pure ({ reportBody }, bytes)

theorem encode_length_pos (message : MarketStatisticsReportMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MarketStatisticsReportMessage) : (encode message).length ≤ 448 := by
  unfold encode
  cases message.reportBody with
  | reportHeaderBody inner =>
    simp only [ReportBody.encode, List.length_append, encodeUInt_length, ReportHeaderBody.encode_length]
    omega
  | reportStatisticsBody inner =>
    simp only [ReportBody.encode, List.length_append, encodeUInt_length, ReportStatisticsBody.encode_length]
    omega
  | reportTrailerBody inner =>
    simp only [ReportBody.encode, List.length_append, encodeUInt_length, ReportTrailerBody.encode_length]
    omega

@[simp] theorem decode_encode (message : MarketStatisticsReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ReportBody.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : MarketStatisticsReportMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end MarketStatisticsReportMessage

/-- Spread Report Header Body: 67 bytes -/
structure SpreadReportHeaderBody where
  orgScope : Alpha 1
  reportDate : BitVec 32
  userType : BitVec 16
  brokerNumber : Alpha 5
  brokerName : Alpha 25
  traderNumber : BitVec 32
  traderName : Alpha 26
  deriving DecidableEq, Repr

namespace SpreadReportHeaderBody

def encode (message : SpreadReportHeaderBody) : List UInt8 :=
  Alpha.encode message.orgScope
    ++ (encodeUInt 4 message.reportDate
    ++ (encodeUInt 2 message.userType
    ++ (Alpha.encode message.brokerNumber
    ++ (Alpha.encode message.brokerName
    ++ (encodeUInt 4 message.traderNumber
    ++ (Alpha.encode message.traderName))))))

def decode (bytes : List UInt8) : Option (SpreadReportHeaderBody × List UInt8) := do
  let (orgScope, bytes) ← Alpha.decode 1 bytes
  let (reportDate, bytes) ← decodeUInt 4 bytes
  let (userType, bytes) ← decodeUInt 2 bytes
  let (brokerNumber, bytes) ← Alpha.decode 5 bytes
  let (brokerName, bytes) ← Alpha.decode 25 bytes
  let (traderNumber, bytes) ← decodeUInt 4 bytes
  let (traderName, bytes) ← Alpha.decode 26 bytes
  pure ({ orgScope, reportDate, userType, brokerNumber, brokerName, traderNumber, traderName }, bytes)

@[simp] theorem encode_length (message : SpreadReportHeaderBody) : (encode message).length = 67 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SpreadReportHeaderBody) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SpreadReportHeaderBody) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SpreadReportHeaderBody

/-- Report Data: 78 bytes -/
structure ReportData where
  mkt : BitVec 16
  instrumentName1 : Alpha 6
  symbol1 : Alpha 10
  expiryDate1 : BitVec 32
  strikePrice1 : BitVec 32
  optionType1 : Alpha 2
  caLevel1 : BitVec 16
  instrumentName2 : Alpha 6
  symbol2 : Alpha 10
  expiryDate2 : BitVec 32
  strikePrice2 : BitVec 32
  optionType2 : Alpha 2
  caLevel2 : BitVec 16
  openPriceDiff : BitVec 32
  highPriceDiff : BitVec 32
  lowPriceDiff : BitVec 32
  lastTradePriceDiff : BitVec 32
  numOfContractsTrd : BitVec 32
  deriving DecidableEq, Repr

namespace ReportData

def encode (message : ReportData) : List UInt8 :=
  encodeUInt 2 message.mkt
    ++ (Alpha.encode message.instrumentName1
    ++ (Alpha.encode message.symbol1
    ++ (encodeUInt 4 message.expiryDate1
    ++ (encodeUInt 4 message.strikePrice1
    ++ (Alpha.encode message.optionType1
    ++ (encodeUInt 2 message.caLevel1
    ++ (Alpha.encode message.instrumentName2
    ++ (Alpha.encode message.symbol2
    ++ (encodeUInt 4 message.expiryDate2
    ++ (encodeUInt 4 message.strikePrice2
    ++ (Alpha.encode message.optionType2
    ++ (encodeUInt 2 message.caLevel2
    ++ (encodeUInt 4 message.openPriceDiff
    ++ (encodeUInt 4 message.highPriceDiff
    ++ (encodeUInt 4 message.lowPriceDiff
    ++ (encodeUInt 4 message.lastTradePriceDiff
    ++ (encodeUInt 4 message.numOfContractsTrd)))))))))))))))))

def decode (bytes : List UInt8) : Option (ReportData × List UInt8) := do
  let (mkt, bytes) ← decodeUInt 2 bytes
  let (instrumentName1, bytes) ← Alpha.decode 6 bytes
  let (symbol1, bytes) ← Alpha.decode 10 bytes
  let (expiryDate1, bytes) ← decodeUInt 4 bytes
  let (strikePrice1, bytes) ← decodeUInt 4 bytes
  let (optionType1, bytes) ← Alpha.decode 2 bytes
  let (caLevel1, bytes) ← decodeUInt 2 bytes
  let (instrumentName2, bytes) ← Alpha.decode 6 bytes
  let (symbol2, bytes) ← Alpha.decode 10 bytes
  let (expiryDate2, bytes) ← decodeUInt 4 bytes
  let (strikePrice2, bytes) ← decodeUInt 4 bytes
  let (optionType2, bytes) ← Alpha.decode 2 bytes
  let (caLevel2, bytes) ← decodeUInt 2 bytes
  let (openPriceDiff, bytes) ← decodeUInt 4 bytes
  let (highPriceDiff, bytes) ← decodeUInt 4 bytes
  let (lowPriceDiff, bytes) ← decodeUInt 4 bytes
  let (lastTradePriceDiff, bytes) ← decodeUInt 4 bytes
  let (numOfContractsTrd, bytes) ← decodeUInt 4 bytes
  pure ({ mkt, instrumentName1, symbol1, expiryDate1, strikePrice1, optionType1, caLevel1, instrumentName2, symbol2, expiryDate2, strikePrice2, optionType2, caLevel2, openPriceDiff, highPriceDiff, lowPriceDiff, lastTradePriceDiff, numOfContractsTrd }, bytes)

@[simp] theorem encode_length (message : ReportData) : (encode message).length = 78 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : ReportData) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReportData) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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

end ReportData

/-- Spread Report Statistics Body: 237 bytes -/
structure SpreadReportStatisticsBody where
  reserved1 : Alpha 1
  noOfRecords : BitVec 16
  reportData : Exact 3 ReportData
  deriving DecidableEq, Repr

namespace SpreadReportStatisticsBody

def encode (message : SpreadReportStatisticsBody) : List UInt8 :=
  Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.noOfRecords
    ++ (encodeMany ReportData.encode message.reportData.val))

def decode (bytes : List UInt8) : Option (SpreadReportStatisticsBody × List UInt8) := do
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (noOfRecords, bytes) ← decodeUInt 2 bytes
  let (reportData_, bytes) ← decodeMany ReportData.decode 3 bytes
  if fits_reportData : reportData_.length = 3 then
    pure ({ reserved1, noOfRecords, reportData := ⟨reportData_, fits_reportData⟩ }, bytes)
  else none

@[simp] theorem encode_length (message : SpreadReportStatisticsBody) : (encode message).length = 237 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, encodeMany_length_const ReportData.encode 78 ReportData.encode_length, message.reportData.length_eq]

theorem encode_length_pos (message : SpreadReportStatisticsBody) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SpreadReportStatisticsBody) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_exact 3 ReportData.encode ReportData.decode ReportData.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.reportData.length_eq]
  rfl

end SpreadReportStatisticsBody

/-- Any Spread Report Body, selected by Message Type -/
inductive SpreadReportBody where
  | spreadReportHeaderBody (message : SpreadReportHeaderBody) -- "H" 0x48
  | spreadReportStatisticsBody (message : SpreadReportStatisticsBody) -- "R" 0x52
  | reportTrailerBody (message : ReportTrailerBody) -- "T" 0x54
  deriving DecidableEq, Repr

namespace SpreadReportBody

/-- The Message Type each message is sent under -/
def tag : SpreadReportBody → BitVec 8
  | .spreadReportHeaderBody _ => 72
  | .spreadReportStatisticsBody _ => 82
  | .reportTrailerBody _ => 84

def encode : SpreadReportBody → List UInt8
  | .spreadReportHeaderBody message => SpreadReportHeaderBody.encode message
  | .spreadReportStatisticsBody message => SpreadReportStatisticsBody.encode message
  | .reportTrailerBody message => ReportTrailerBody.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : SpreadReportBody) : (encode message).length ≤ 237 := by
  cases message with
  | spreadReportHeaderBody inner =>
    simp only [encode, SpreadReportHeaderBody.encode_length]
    omega
  | spreadReportStatisticsBody inner =>
    simp only [encode, SpreadReportStatisticsBody.encode_length]
    omega
  | reportTrailerBody inner =>
    simp only [encode, ReportTrailerBody.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (SpreadReportBody × List UInt8) :=
  if tag = 72 then (SpreadReportHeaderBody.decode bytes).map fun (message, rest) => (.spreadReportHeaderBody message, rest)
  else if tag = 82 then (SpreadReportStatisticsBody.decode bytes).map fun (message, rest) => (.spreadReportStatisticsBody message, rest)
  else if tag = 84 then (ReportTrailerBody.decode bytes).map fun (message, rest) => (.reportTrailerBody message, rest)
  else none

@[simp] theorem decode_encode (message : SpreadReportBody) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end SpreadReportBody

/-- Spread Bhavcopy Message -/
structure SpreadBhavcopyMessage where
  spreadReportBody : SpreadReportBody
  deriving DecidableEq, Repr

namespace SpreadBhavcopyMessage

def encode (message : SpreadBhavcopyMessage) : List UInt8 :=
  encodeUInt 1 (SpreadReportBody.tag message.spreadReportBody)
    ++ (SpreadReportBody.encode message.spreadReportBody)

def decode (bytes : List UInt8) : Option (SpreadBhavcopyMessage × List UInt8) := do
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (spreadReportBody, bytes) ← SpreadReportBody.decode messageType bytes
  pure ({ spreadReportBody }, bytes)

theorem encode_length_pos (message : SpreadBhavcopyMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SpreadBhavcopyMessage) : (encode message).length ≤ 238 := by
  unfold encode
  cases message.spreadReportBody with
  | spreadReportHeaderBody inner =>
    simp only [SpreadReportBody.encode, List.length_append, encodeUInt_length, SpreadReportHeaderBody.encode_length]
    omega
  | spreadReportStatisticsBody inner =>
    simp only [SpreadReportBody.encode, List.length_append, encodeUInt_length, SpreadReportStatisticsBody.encode_length]
    omega
  | reportTrailerBody inner =>
    simp only [SpreadReportBody.encode, List.length_append, encodeUInt_length, ReportTrailerBody.encode_length]
    omega

@[simp] theorem decode_encode (message : SpreadBhavcopyMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [SpreadReportBody.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SpreadBhavcopyMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SpreadBhavcopyMessage

/-- Giveup: 80 bytes -/
structure Giveup where
  orderNumber : Alpha 8
  fillNumber : BitVec 32
  instrumentName : Alpha 6
  symbol : Alpha 10
  expiryDate : BitVec 32
  strikePrice : BitVec 32
  optionType : Alpha 2
  caLevel : BitVec 16
  fillVolume : BitVec 32
  fillPrice : BitVec 32
  brokerId : Alpha 5
  filler : Alpha 1
  buySell : BitVec 16
  bookType : BitVec 16
  lastModifiedDateTime : BitVec 32
  initiatedByControl : InitiatedByControl
  openClose : OpenClose
  reserved1 : Alpha 1
  participant : Alpha 12
  giveupFlag : Alpha 1
  deleted : Alpha 1
  secondReserved1 : Alpha 1
  deriving DecidableEq, Repr

namespace Giveup

def encode (message : Giveup) : List UInt8 :=
  Alpha.encode message.orderNumber
    ++ (encodeUInt 4 message.fillNumber
    ++ (Alpha.encode message.instrumentName
    ++ (Alpha.encode message.symbol
    ++ (encodeUInt 4 message.expiryDate
    ++ (encodeUInt 4 message.strikePrice
    ++ (Alpha.encode message.optionType
    ++ (encodeUInt 2 message.caLevel
    ++ (encodeUInt 4 message.fillVolume
    ++ (encodeUInt 4 message.fillPrice
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.filler
    ++ (encodeUInt 2 message.buySell
    ++ (encodeUInt 2 message.bookType
    ++ (encodeUInt 4 message.lastModifiedDateTime
    ++ (InitiatedByControl.encode message.initiatedByControl
    ++ (OpenClose.encode message.openClose
    ++ (Alpha.encode message.reserved1
    ++ (Alpha.encode message.participant
    ++ (Alpha.encode message.giveupFlag
    ++ (Alpha.encode message.deleted
    ++ (Alpha.encode message.secondReserved1)))))))))))))))))))))

def decode (bytes : List UInt8) : Option (Giveup × List UInt8) := do
  let (orderNumber, bytes) ← Alpha.decode 8 bytes
  let (fillNumber, bytes) ← decodeUInt 4 bytes
  let (instrumentName, bytes) ← Alpha.decode 6 bytes
  let (symbol, bytes) ← Alpha.decode 10 bytes
  let (expiryDate, bytes) ← decodeUInt 4 bytes
  let (strikePrice, bytes) ← decodeUInt 4 bytes
  let (optionType, bytes) ← Alpha.decode 2 bytes
  let (caLevel, bytes) ← decodeUInt 2 bytes
  let (fillVolume, bytes) ← decodeUInt 4 bytes
  let (fillPrice, bytes) ← decodeUInt 4 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (filler, bytes) ← Alpha.decode 1 bytes
  let (buySell, bytes) ← decodeUInt 2 bytes
  let (bookType, bytes) ← decodeUInt 2 bytes
  let (lastModifiedDateTime, bytes) ← decodeUInt 4 bytes
  let (initiatedByControl_, bytes) ← InitiatedByControl.decode bytes
  let (openClose, bytes) ← OpenClose.decode bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (participant, bytes) ← Alpha.decode 12 bytes
  let (giveupFlag, bytes) ← Alpha.decode 1 bytes
  let (deleted, bytes) ← Alpha.decode 1 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  pure ({ orderNumber, fillNumber, instrumentName, symbol, expiryDate, strikePrice, optionType, caLevel, fillVolume, fillPrice, brokerId, filler, buySell, bookType, lastModifiedDateTime, initiatedByControl := initiatedByControl_, openClose, reserved1, participant, giveupFlag, deleted, secondReserved1 }, bytes)

@[simp] theorem encode_length (message : Giveup) : (encode message).length = 80 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, InitiatedByControl.encode_length, OpenClose.encode_length]

theorem encode_length_pos (message : Giveup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Giveup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, InitiatedByControl.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpenClose.decode_encode, some_bind]
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

end Giveup

/-- Giveup Confirmation Message: 82 bytes -/
structure GiveupConfirmationMessage where
  reasonCode : BitVec 16
  giveup : Giveup
  deriving DecidableEq, Repr

namespace GiveupConfirmationMessage

def encode (message : GiveupConfirmationMessage) : List UInt8 :=
  encodeUInt 2 message.reasonCode
    ++ (Giveup.encode message.giveup)

def decode (bytes : List UInt8) : Option (GiveupConfirmationMessage × List UInt8) := do
  let (reasonCode, bytes) ← decodeUInt 2 bytes
  let (giveup, bytes) ← Giveup.decode bytes
  pure ({ reasonCode, giveup }, bytes)

@[simp] theorem encode_length (message : GiveupConfirmationMessage) : (encode message).length = 82 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Giveup.encode_length]

theorem encode_length_pos (message : GiveupConfirmationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : GiveupConfirmationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Giveup.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : GiveupConfirmationMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end GiveupConfirmationMessage

/-- Gateway Router Response Message: 84 bytes -/
structure GatewayRouterResponseMessage where
  boxId : BitVec 16
  brokerId : Alpha 5
  filler : Alpha 1
  ipAddress : Alpha 16
  port : BitVec 32
  sessionKey : Alpha 8
  cryptographicKey : Alpha 32
  cryptographicIv : Alpha 16
  deriving DecidableEq, Repr

namespace GatewayRouterResponseMessage

def encode (message : GatewayRouterResponseMessage) : List UInt8 :=
  encodeUInt 2 message.boxId
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.filler
    ++ (Alpha.encode message.ipAddress
    ++ (encodeUInt 4 message.port
    ++ (Alpha.encode message.sessionKey
    ++ (Alpha.encode message.cryptographicKey
    ++ (Alpha.encode message.cryptographicIv)))))))

def decode (bytes : List UInt8) : Option (GatewayRouterResponseMessage × List UInt8) := do
  let (boxId, bytes) ← decodeUInt 2 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (filler, bytes) ← Alpha.decode 1 bytes
  let (ipAddress, bytes) ← Alpha.decode 16 bytes
  let (port, bytes) ← decodeUInt 4 bytes
  let (sessionKey, bytes) ← Alpha.decode 8 bytes
  let (cryptographicKey, bytes) ← Alpha.decode 32 bytes
  let (cryptographicIv, bytes) ← Alpha.decode 16 bytes
  pure ({ boxId, brokerId, filler, ipAddress, port, sessionKey, cryptographicKey, cryptographicIv }, bytes)

@[simp] theorem encode_length (message : GatewayRouterResponseMessage) : (encode message).length = 84 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : GatewayRouterResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : GatewayRouterResponseMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : GatewayRouterResponseMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end GatewayRouterResponseMessage

/-- Secure Box Registration Response Out Message: 0 bytes -/
structure SecureBoxRegistrationResponseOutMessage where
  deriving DecidableEq, Repr

namespace SecureBoxRegistrationResponseOutMessage

def encode (_ : SecureBoxRegistrationResponseOutMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (SecureBoxRegistrationResponseOutMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : SecureBoxRegistrationResponseOutMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : SecureBoxRegistrationResponseOutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SecureBoxRegistrationResponseOutMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SecureBoxRegistrationResponseOutMessage

/-- Box Sign On Request Out Message: 12 bytes -/
structure BoxSignOnRequestOutMessage where
  boxId : BitVec 16
  reserved10 : Alpha 10
  deriving DecidableEq, Repr

namespace BoxSignOnRequestOutMessage

def encode (message : BoxSignOnRequestOutMessage) : List UInt8 :=
  encodeUInt 2 message.boxId
    ++ (Alpha.encode message.reserved10)

def decode (bytes : List UInt8) : Option (BoxSignOnRequestOutMessage × List UInt8) := do
  let (boxId, bytes) ← decodeUInt 2 bytes
  let (reserved10, bytes) ← Alpha.decode 10 bytes
  pure ({ boxId, reserved10 }, bytes)

@[simp] theorem encode_length (message : BoxSignOnRequestOutMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : BoxSignOnRequestOutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BoxSignOnRequestOutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : BoxSignOnRequestOutMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end BoxSignOnRequestOutMessage

/-- Box Sign Off Message: 2 bytes -/
structure BoxSignOffMessage where
  boxId : BitVec 16
  deriving DecidableEq, Repr

namespace BoxSignOffMessage

def encode (message : BoxSignOffMessage) : List UInt8 :=
  encodeUInt 2 message.boxId

def decode (bytes : List UInt8) : Option (BoxSignOffMessage × List UInt8) := do
  let (boxId, bytes) ← decodeUInt 2 bytes
  pure ({ boxId }, bytes)

@[simp] theorem encode_length (message : BoxSignOffMessage) : (encode message).length = 2 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : BoxSignOffMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BoxSignOffMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : BoxSignOffMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end BoxSignOffMessage

/-- Contingency Broadcast Message: 204 bytes -/
structure ContingencyBroadcastMessage where
  streamNumber : BitVec 16
  status : BitVec 16
  reserved200 : Alpha 200
  deriving DecidableEq, Repr

namespace ContingencyBroadcastMessage

def encode (message : ContingencyBroadcastMessage) : List UInt8 :=
  encodeUInt 2 message.streamNumber
    ++ (encodeUInt 2 message.status
    ++ (Alpha.encode message.reserved200))

def decode (bytes : List UInt8) : Option (ContingencyBroadcastMessage × List UInt8) := do
  let (streamNumber, bytes) ← decodeUInt 2 bytes
  let (status, bytes) ← decodeUInt 2 bytes
  let (reserved200, bytes) ← Alpha.decode 200 bytes
  pure ({ streamNumber, status, reserved200 }, bytes)

@[simp] theorem encode_length (message : ContingencyBroadcastMessage) : (encode message).length = 204 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : ContingencyBroadcastMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ContingencyBroadcastMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ContingencyBroadcastMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ContingencyBroadcastMessage

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

/-- Branch Order Value Limit Update Response Message -/
structure BranchOrderValueLimitUpdateResponseMessage where
  branchLimitResponseBody : BranchOrderValueLimitBody ⊕ (ErrorResponseBody)
  deriving DecidableEq, Repr

namespace BranchOrderValueLimitUpdateResponseMessage

def encode (message : BranchOrderValueLimitUpdateResponseMessage) : List UInt8 :=
  encodeEither BranchOrderValueLimitBody.encode (ErrorResponseBody.encode) message.branchLimitResponseBody

def decode (bytes : List UInt8) : Option BranchOrderValueLimitUpdateResponseMessage := do
  let branchLimitResponseBody ← decodeByWidth 96 (decodeWhole BranchOrderValueLimitBody.decode) ((decodeWhole ErrorResponseBody.decode)) bytes
  pure { branchLimitResponseBody }

theorem decode_encode (message : BranchOrderValueLimitUpdateResponseMessage) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeByWidth_encodeEither BranchOrderValueLimitBody.encode (decodeWhole BranchOrderValueLimitBody.decode) (ErrorResponseBody.encode) ((decodeWhole ErrorResponseBody.decode)) 96 BranchOrderValueLimitBody.encode_length (by intro item; simp [ErrorResponseBody.encode_length]) (decodeWhole_encode BranchOrderValueLimitBody.encode BranchOrderValueLimitBody.decode BranchOrderValueLimitBody.decode_encode) ((decodeWhole_encode ErrorResponseBody.encode ErrorResponseBody.decode ErrorResponseBody.decode_encode)), some_bind]
  rfl

end BranchOrderValueLimitUpdateResponseMessage

/-- Reset User Password Response Message: 18 bytes -/
structure ResetUserPasswordResponseMessage where
  userId : BitVec 32
  reserved14 : Alpha 14
  deriving DecidableEq, Repr

namespace ResetUserPasswordResponseMessage

def encode (message : ResetUserPasswordResponseMessage) : List UInt8 :=
  encodeUInt 4 message.userId
    ++ (Alpha.encode message.reserved14)

def decode (bytes : List UInt8) : Option (ResetUserPasswordResponseMessage × List UInt8) := do
  let (userId, bytes) ← decodeUInt 4 bytes
  let (reserved14, bytes) ← Alpha.decode 14 bytes
  pure ({ userId, reserved14 }, bytes)

@[simp] theorem encode_length (message : ResetUserPasswordResponseMessage) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : ResetUserPasswordResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ResetUserPasswordResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ResetUserPasswordResponseMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ResetUserPasswordResponseMessage

/-- Collateral User Status Change Response Message: 6 bytes -/
structure CollateralUserStatusChangeResponseMessage where
  userId : BitVec 32
  colUserBit : ColUserBit
  reserved1 : Alpha 1
  deriving DecidableEq, Repr

namespace CollateralUserStatusChangeResponseMessage

def encode (message : CollateralUserStatusChangeResponseMessage) : List UInt8 :=
  encodeUInt 4 message.userId
    ++ (ColUserBit.encode message.colUserBit
    ++ (Alpha.encode message.reserved1))

def decode (bytes : List UInt8) : Option (CollateralUserStatusChangeResponseMessage × List UInt8) := do
  let (userId, bytes) ← decodeUInt 4 bytes
  let (colUserBit, bytes) ← ColUserBit.decode bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  pure ({ userId, colUserBit, reserved1 }, bytes)

@[simp] theorem encode_length (message : CollateralUserStatusChangeResponseMessage) : (encode message).length = 6 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, ColUserBit.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : CollateralUserStatusChangeResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CollateralUserStatusChangeResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ColUserBit.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : CollateralUserStatusChangeResponseMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end CollateralUserStatusChangeResponseMessage

/-- User Trade Modify Cancel Status Change Response Message: 6 bytes -/
structure UserTradeModifyCancelStatusChangeResponseMessage where
  userId : BitVec 32
  trdModCxlBit : TrdModCxlBit
  reserved1 : Alpha 1
  deriving DecidableEq, Repr

namespace UserTradeModifyCancelStatusChangeResponseMessage

def encode (message : UserTradeModifyCancelStatusChangeResponseMessage) : List UInt8 :=
  encodeUInt 4 message.userId
    ++ (TrdModCxlBit.encode message.trdModCxlBit
    ++ (Alpha.encode message.reserved1))

def decode (bytes : List UInt8) : Option (UserTradeModifyCancelStatusChangeResponseMessage × List UInt8) := do
  let (userId, bytes) ← decodeUInt 4 bytes
  let (trdModCxlBit, bytes) ← TrdModCxlBit.decode bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  pure ({ userId, trdModCxlBit, reserved1 }, bytes)

@[simp] theorem encode_length (message : UserTradeModifyCancelStatusChangeResponseMessage) : (encode message).length = 6 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, TrdModCxlBit.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : UserTradeModifyCancelStatusChangeResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UserTradeModifyCancelStatusChangeResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TrdModCxlBit.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : UserTradeModifyCancelStatusChangeResponseMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end UserTradeModifyCancelStatusChangeResponseMessage

/-- User Address Unlock Confirm Message: 40 bytes -/
structure UserAddressUnlockConfirmMessage where
  userId : BitVec 32
  reserved36 : Alpha 36
  deriving DecidableEq, Repr

namespace UserAddressUnlockConfirmMessage

def encode (message : UserAddressUnlockConfirmMessage) : List UInt8 :=
  encodeUInt 4 message.userId
    ++ (Alpha.encode message.reserved36)

def decode (bytes : List UInt8) : Option (UserAddressUnlockConfirmMessage × List UInt8) := do
  let (userId, bytes) ← decodeUInt 4 bytes
  let (reserved36, bytes) ← Alpha.decode 36 bytes
  pure ({ userId, reserved36 }, bytes)

@[simp] theorem encode_length (message : UserAddressUnlockConfirmMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : UserAddressUnlockConfirmMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UserAddressUnlockConfirmMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : UserAddressUnlockConfirmMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end UserAddressUnlockConfirmMessage

/-- User Address Unlock Approve Message: 40 bytes -/
structure UserAddressUnlockApproveMessage where
  userId : BitVec 32
  reserved36 : Alpha 36
  deriving DecidableEq, Repr

namespace UserAddressUnlockApproveMessage

def encode (message : UserAddressUnlockApproveMessage) : List UInt8 :=
  encodeUInt 4 message.userId
    ++ (Alpha.encode message.reserved36)

def decode (bytes : List UInt8) : Option (UserAddressUnlockApproveMessage × List UInt8) := do
  let (userId, bytes) ← decodeUInt 4 bytes
  let (reserved36, bytes) ← Alpha.decode 36 bytes
  pure ({ userId, reserved36 }, bytes)

@[simp] theorem encode_length (message : UserAddressUnlockApproveMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : UserAddressUnlockApproveMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UserAddressUnlockApproveMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : UserAddressUnlockApproveMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end UserAddressUnlockApproveMessage

/-- Nlt Order Message To Trader Message: 276 bytes -/
structure NltOrderMessageToTraderMessage where
  messageBuffer : Alpha 276
  deriving DecidableEq, Repr

namespace NltOrderMessageToTraderMessage

def encode (message : NltOrderMessageToTraderMessage) : List UInt8 :=
  Alpha.encode message.messageBuffer

def decode (bytes : List UInt8) : Option (NltOrderMessageToTraderMessage × List UInt8) := do
  let (messageBuffer, bytes) ← Alpha.decode 276 bytes
  pure ({ messageBuffer }, bytes)

@[simp] theorem encode_length (message : NltOrderMessageToTraderMessage) : (encode message).length = 276 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : NltOrderMessageToTraderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NltOrderMessageToTraderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : NltOrderMessageToTraderMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end NltOrderMessageToTraderMessage

/-- Nlt Order Inquiry Response Message: 38 bytes -/
structure NltOrderInquiryResponseMessage where
  tokenNo : BitVec 32
  counterOrderMktType : BitVec 16
  price : BitVec 32
  volume : BitVec 32
  bookType : BitVec 16
  reserved8 : Alpha 8
  orderNumber : Alpha 8
  counterBrokerId : Alpha 5
  reserved1 : Alpha 1
  deriving DecidableEq, Repr

namespace NltOrderInquiryResponseMessage

def encode (message : NltOrderInquiryResponseMessage) : List UInt8 :=
  encodeUInt 4 message.tokenNo
    ++ (encodeUInt 2 message.counterOrderMktType
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 2 message.bookType
    ++ (Alpha.encode message.reserved8
    ++ (Alpha.encode message.orderNumber
    ++ (Alpha.encode message.counterBrokerId
    ++ (Alpha.encode message.reserved1))))))))

def decode (bytes : List UInt8) : Option (NltOrderInquiryResponseMessage × List UInt8) := do
  let (tokenNo, bytes) ← decodeUInt 4 bytes
  let (counterOrderMktType, bytes) ← decodeUInt 2 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (bookType, bytes) ← decodeUInt 2 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  let (orderNumber, bytes) ← Alpha.decode 8 bytes
  let (counterBrokerId, bytes) ← Alpha.decode 5 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  pure ({ tokenNo, counterOrderMktType, price, volume, bookType, reserved8, orderNumber, counterBrokerId, reserved1 }, bytes)

@[simp] theorem encode_length (message : NltOrderInquiryResponseMessage) : (encode message).length = 38 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : NltOrderInquiryResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NltOrderInquiryResponseMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : NltOrderInquiryResponseMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end NltOrderInquiryResponseMessage

/-- Nlt Trailer Record Message: 0 bytes -/
structure NltTrailerRecordMessage where
  deriving DecidableEq, Repr

namespace NltTrailerRecordMessage

def encode (_ : NltTrailerRecordMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (NltTrailerRecordMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : NltTrailerRecordMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : NltTrailerRecordMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : NltTrailerRecordMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end NltTrailerRecordMessage

/-- Any Server Message Payload, selected by Transaction Code -/
inductive ServerMessagePayload where
  | signOnRequestOutMessage (message : SignOnRequestOutMessage) -- 2301
  | signOnRequestOutMessage5585 (message : SignOnRequestOutMessage) -- 5585
  | signOffRequestOutMessage (message : SignOffRequestOutMessage) -- 2321
  | systemInformationOutMessage (message : SystemInformationOutMessage) -- 1601
  | systemInformationOutMessage7321 (message : SystemInformationOutMessage) -- 7321
  | updateLocalDatabaseHeaderMessage (message : UpdateLocalDatabaseHeaderMessage) -- 7307
  | updateLocalDatabaseTrailerMessage (message : UpdateLocalDatabaseTrailerMessage) -- 7308
  | updateLocalDatabaseDataMessage (message : UpdateLocalDatabaseDataMessage) -- 7304
  | headerRecordMessage (message : HeaderRecordMessage) -- 7011
  | messageRecordMessage (message : MessageRecordMessage) -- 7021
  | trailerRecordMessage (message : TrailerRecordMessage) -- 7031
  | orderConfirmationMessage (message : OrderConfirmationMessage) -- 2073
  | orderConfirmationMessage2083 (message : OrderConfirmationMessage) -- 2083
  | orderModificationConfirmationMessage (message : OrderModificationConfirmationMessage) -- 2074
  | orderModificationConfirmationMessage2085 (message : OrderModificationConfirmationMessage) -- 2085
  | orderResponseMessage (message : OrderResponseMessage) -- 2001
  | orderResponseMessage2012 (message : OrderResponseMessage) -- 2012
  | orderResponseMessage2041 (message : OrderResponseMessage) -- 2041
  | orderResponseMessage2042 (message : OrderResponseMessage) -- 2042
  | orderResponseMessage2071 (message : OrderResponseMessage) -- 2071
  | orderResponseMessage2072 (message : OrderResponseMessage) -- 2072
  | orderResponseMessage2087 (message : OrderResponseMessage) -- 2087
  | orderResponseMessage2088 (message : OrderResponseMessage) -- 2088
  | orderResponseMessage2089 (message : OrderResponseMessage) -- 2089
  | orderResponseMessage2170 (message : OrderResponseMessage) -- 2170
  | orderResponseMessage2231 (message : OrderResponseMessage) -- 2231
  | orderResponseMessage9002 (message : OrderResponseMessage) -- 9002
  | orderResponseMessage27100 (message : OrderResponseMessage) -- 27100
  | orderCancellationConfirmationMessage (message : OrderCancellationConfirmationMessage) -- 2075
  | tradeInquiryResponseMessage (message : TradeInquiryResponseMessage) -- 2223
  | tradeInquiryResponseMessage2288 (message : TradeInquiryResponseMessage) -- 2288
  | tradeInquiryResponseMessage5441 (message : TradeInquiryResponseMessage) -- 5441
  | tradeInquiryResponseMessage5450 (message : TradeInquiryResponseMessage) -- 5450
  | tradeInquiryResponseMessage5452 (message : TradeInquiryResponseMessage) -- 5452
  | tradeInquiryResponseMessage5453 (message : TradeInquiryResponseMessage) -- 5453
  | tradeConfirmationMessage (message : TradeConfirmationMessage) -- 2090
  | tradeConfirmationMessage2212 (message : TradeConfirmationMessage) -- 2212
  | tradeConfirmationMessage2222 (message : TradeConfirmationMessage) -- 2222
  | tradeConfirmationMessage2282 (message : TradeConfirmationMessage) -- 2282
  | tradeConfirmationMessage2286 (message : TradeConfirmationMessage) -- 2286
  | tradeConfirmationMessage2287 (message : TradeConfirmationMessage) -- 2287
  | tradeConfirmationMessage5449 (message : TradeConfirmationMessage) -- 5449
  | spreadOrderResponseMessage (message : SpreadOrderResponseMessage) -- 2101
  | spreadOrderResponseMessage2103 (message : SpreadOrderResponseMessage) -- 2103
  | spreadOrderResponseMessage2105 (message : SpreadOrderResponseMessage) -- 2105
  | spreadOrderResponseMessage2107 (message : SpreadOrderResponseMessage) -- 2107
  | spreadOrderResponseMessage2119 (message : SpreadOrderResponseMessage) -- 2119
  | spreadOrderResponseMessage2124 (message : SpreadOrderResponseMessage) -- 2124
  | spreadOrderResponseMessage2125 (message : SpreadOrderResponseMessage) -- 2125
  | spreadOrderResponseMessage2126 (message : SpreadOrderResponseMessage) -- 2126
  | spreadOrderResponseMessage2127 (message : SpreadOrderResponseMessage) -- 2127
  | spreadOrderResponseMessage2130 (message : SpreadOrderResponseMessage) -- 2130
  | spreadOrderResponseMessage2131 (message : SpreadOrderResponseMessage) -- 2131
  | spreadOrderResponseMessage2132 (message : SpreadOrderResponseMessage) -- 2132
  | spreadOrderResponseMessage2133 (message : SpreadOrderResponseMessage) -- 2133
  | spreadOrderResponseMessage2136 (message : SpreadOrderResponseMessage) -- 2136
  | spreadOrderResponseMessage2154 (message : SpreadOrderResponseMessage) -- 2154
  | spreadOrderResponseMessage2155 (message : SpreadOrderResponseMessage) -- 2155
  | spreadOrderResponseMessage2156 (message : SpreadOrderResponseMessage) -- 2156
  | spreadOrderResponseMessage9004 (message : SpreadOrderResponseMessage) -- 9004
  | spreadOrderResponseMessage27102 (message : SpreadOrderResponseMessage) -- 27102
  | spreadOrderResponseMessage27103 (message : SpreadOrderResponseMessage) -- 27103
  | spreadOrderResponseMessage27104 (message : SpreadOrderResponseMessage) -- 27104
  | userOrderLimitUpdateMessage (message : UserOrderLimitUpdateMessage) -- 5731
  | dealerLimitUpdateMessage (message : DealerLimitUpdateMessage) -- 5733
  | spreadOrderLimitUpdateMessage (message : SpreadOrderLimitUpdateMessage) -- 5772
  | controlMessageToTraderMessage (message : ControlMessageToTraderMessage) -- 5295
  | mbaInquiryResponseMessage (message : MbaInquiryResponseMessage) -- 1685
  | mbaInquiryResponseMessage1687 (message : MbaInquiryResponseMessage) -- 1687
  | mbaInquiryResponseMessage1689 (message : MbaInquiryResponseMessage) -- 1689
  | marketStatisticsReportMessage (message : MarketStatisticsReportMessage) -- 1833
  | spreadBhavcopyMessage (message : SpreadBhavcopyMessage) -- 6502
  | giveupConfirmationMessage (message : GiveupConfirmationMessage) -- 4506
  | giveupConfirmationMessage4507 (message : GiveupConfirmationMessage) -- 4507
  | gatewayRouterResponseMessage (message : GatewayRouterResponseMessage) -- 2401
  | secureBoxRegistrationResponseOutMessage (message : SecureBoxRegistrationResponseOutMessage) -- 23009
  | boxSignOnRequestOutMessage (message : BoxSignOnRequestOutMessage) -- 23001
  | boxSignOffMessage (message : BoxSignOffMessage) -- 20322
  | contingencyBroadcastMessage (message : ContingencyBroadcastMessage) -- 5294
  | branchOrderValueLimitUpdateResponseMessage (message : BranchOrderValueLimitUpdateResponseMessage) -- 5717
  | resetUserPasswordResponseMessage (message : ResetUserPasswordResponseMessage) -- 5741
  | collateralUserStatusChangeResponseMessage (message : CollateralUserStatusChangeResponseMessage) -- 5745
  | userTradeModifyCancelStatusChangeResponseMessage (message : UserTradeModifyCancelStatusChangeResponseMessage) -- 5739
  | userAddressUnlockConfirmMessage (message : UserAddressUnlockConfirmMessage) -- 5428
  | userAddressUnlockApproveMessage (message : UserAddressUnlockApproveMessage) -- 5483
  | userAddressUnlockApproveMessage5484 (message : UserAddressUnlockApproveMessage) -- 5484
  | nltOrderMessageToTraderMessage (message : NltOrderMessageToTraderMessage) -- 2093
  | nltOrderInquiryResponseMessage (message : NltOrderInquiryResponseMessage) -- 1243
  | nltTrailerRecordMessage (message : NltTrailerRecordMessage) -- 7032
  deriving DecidableEq, Repr

namespace ServerMessagePayload

/-- The Transaction Code each message is sent under -/
def tag : ServerMessagePayload → BitVec 16
  | .signOnRequestOutMessage _ => 2301
  | .signOnRequestOutMessage5585 _ => 5585
  | .signOffRequestOutMessage _ => 2321
  | .systemInformationOutMessage _ => 1601
  | .systemInformationOutMessage7321 _ => 7321
  | .updateLocalDatabaseHeaderMessage _ => 7307
  | .updateLocalDatabaseTrailerMessage _ => 7308
  | .updateLocalDatabaseDataMessage _ => 7304
  | .headerRecordMessage _ => 7011
  | .messageRecordMessage _ => 7021
  | .trailerRecordMessage _ => 7031
  | .orderConfirmationMessage _ => 2073
  | .orderConfirmationMessage2083 _ => 2083
  | .orderModificationConfirmationMessage _ => 2074
  | .orderModificationConfirmationMessage2085 _ => 2085
  | .orderResponseMessage _ => 2001
  | .orderResponseMessage2012 _ => 2012
  | .orderResponseMessage2041 _ => 2041
  | .orderResponseMessage2042 _ => 2042
  | .orderResponseMessage2071 _ => 2071
  | .orderResponseMessage2072 _ => 2072
  | .orderResponseMessage2087 _ => 2087
  | .orderResponseMessage2088 _ => 2088
  | .orderResponseMessage2089 _ => 2089
  | .orderResponseMessage2170 _ => 2170
  | .orderResponseMessage2231 _ => 2231
  | .orderResponseMessage9002 _ => 9002
  | .orderResponseMessage27100 _ => 27100
  | .orderCancellationConfirmationMessage _ => 2075
  | .tradeInquiryResponseMessage _ => 2223
  | .tradeInquiryResponseMessage2288 _ => 2288
  | .tradeInquiryResponseMessage5441 _ => 5441
  | .tradeInquiryResponseMessage5450 _ => 5450
  | .tradeInquiryResponseMessage5452 _ => 5452
  | .tradeInquiryResponseMessage5453 _ => 5453
  | .tradeConfirmationMessage _ => 2090
  | .tradeConfirmationMessage2212 _ => 2212
  | .tradeConfirmationMessage2222 _ => 2222
  | .tradeConfirmationMessage2282 _ => 2282
  | .tradeConfirmationMessage2286 _ => 2286
  | .tradeConfirmationMessage2287 _ => 2287
  | .tradeConfirmationMessage5449 _ => 5449
  | .spreadOrderResponseMessage _ => 2101
  | .spreadOrderResponseMessage2103 _ => 2103
  | .spreadOrderResponseMessage2105 _ => 2105
  | .spreadOrderResponseMessage2107 _ => 2107
  | .spreadOrderResponseMessage2119 _ => 2119
  | .spreadOrderResponseMessage2124 _ => 2124
  | .spreadOrderResponseMessage2125 _ => 2125
  | .spreadOrderResponseMessage2126 _ => 2126
  | .spreadOrderResponseMessage2127 _ => 2127
  | .spreadOrderResponseMessage2130 _ => 2130
  | .spreadOrderResponseMessage2131 _ => 2131
  | .spreadOrderResponseMessage2132 _ => 2132
  | .spreadOrderResponseMessage2133 _ => 2133
  | .spreadOrderResponseMessage2136 _ => 2136
  | .spreadOrderResponseMessage2154 _ => 2154
  | .spreadOrderResponseMessage2155 _ => 2155
  | .spreadOrderResponseMessage2156 _ => 2156
  | .spreadOrderResponseMessage9004 _ => 9004
  | .spreadOrderResponseMessage27102 _ => 27102
  | .spreadOrderResponseMessage27103 _ => 27103
  | .spreadOrderResponseMessage27104 _ => 27104
  | .userOrderLimitUpdateMessage _ => 5731
  | .dealerLimitUpdateMessage _ => 5733
  | .spreadOrderLimitUpdateMessage _ => 5772
  | .controlMessageToTraderMessage _ => 5295
  | .mbaInquiryResponseMessage _ => 1685
  | .mbaInquiryResponseMessage1687 _ => 1687
  | .mbaInquiryResponseMessage1689 _ => 1689
  | .marketStatisticsReportMessage _ => 1833
  | .spreadBhavcopyMessage _ => 6502
  | .giveupConfirmationMessage _ => 4506
  | .giveupConfirmationMessage4507 _ => 4507
  | .gatewayRouterResponseMessage _ => 2401
  | .secureBoxRegistrationResponseOutMessage _ => 23009
  | .boxSignOnRequestOutMessage _ => 23001
  | .boxSignOffMessage _ => 20322
  | .contingencyBroadcastMessage _ => 5294
  | .branchOrderValueLimitUpdateResponseMessage _ => 5717
  | .resetUserPasswordResponseMessage _ => 5741
  | .collateralUserStatusChangeResponseMessage _ => 5745
  | .userTradeModifyCancelStatusChangeResponseMessage _ => 5739
  | .userAddressUnlockConfirmMessage _ => 5428
  | .userAddressUnlockApproveMessage _ => 5483
  | .userAddressUnlockApproveMessage5484 _ => 5484
  | .nltOrderMessageToTraderMessage _ => 2093
  | .nltOrderInquiryResponseMessage _ => 1243
  | .nltTrailerRecordMessage _ => 7032

def encode : ServerMessagePayload → List UInt8
  | .signOnRequestOutMessage message => SignOnRequestOutMessage.encode message
  | .signOnRequestOutMessage5585 message => SignOnRequestOutMessage.encode message
  | .signOffRequestOutMessage message => SignOffRequestOutMessage.encode message
  | .systemInformationOutMessage message => SystemInformationOutMessage.encode message
  | .systemInformationOutMessage7321 message => SystemInformationOutMessage.encode message
  | .updateLocalDatabaseHeaderMessage message => UpdateLocalDatabaseHeaderMessage.encode message
  | .updateLocalDatabaseTrailerMessage message => UpdateLocalDatabaseTrailerMessage.encode message
  | .updateLocalDatabaseDataMessage message => UpdateLocalDatabaseDataMessage.encode message
  | .headerRecordMessage message => HeaderRecordMessage.encode message
  | .messageRecordMessage message => MessageRecordMessage.encode message
  | .trailerRecordMessage message => TrailerRecordMessage.encode message
  | .orderConfirmationMessage message => OrderConfirmationMessage.encode message
  | .orderConfirmationMessage2083 message => OrderConfirmationMessage.encode message
  | .orderModificationConfirmationMessage message => OrderModificationConfirmationMessage.encode message
  | .orderModificationConfirmationMessage2085 message => OrderModificationConfirmationMessage.encode message
  | .orderResponseMessage message => OrderResponseMessage.encode message
  | .orderResponseMessage2012 message => OrderResponseMessage.encode message
  | .orderResponseMessage2041 message => OrderResponseMessage.encode message
  | .orderResponseMessage2042 message => OrderResponseMessage.encode message
  | .orderResponseMessage2071 message => OrderResponseMessage.encode message
  | .orderResponseMessage2072 message => OrderResponseMessage.encode message
  | .orderResponseMessage2087 message => OrderResponseMessage.encode message
  | .orderResponseMessage2088 message => OrderResponseMessage.encode message
  | .orderResponseMessage2089 message => OrderResponseMessage.encode message
  | .orderResponseMessage2170 message => OrderResponseMessage.encode message
  | .orderResponseMessage2231 message => OrderResponseMessage.encode message
  | .orderResponseMessage9002 message => OrderResponseMessage.encode message
  | .orderResponseMessage27100 message => OrderResponseMessage.encode message
  | .orderCancellationConfirmationMessage message => OrderCancellationConfirmationMessage.encode message
  | .tradeInquiryResponseMessage message => TradeInquiryResponseMessage.encode message
  | .tradeInquiryResponseMessage2288 message => TradeInquiryResponseMessage.encode message
  | .tradeInquiryResponseMessage5441 message => TradeInquiryResponseMessage.encode message
  | .tradeInquiryResponseMessage5450 message => TradeInquiryResponseMessage.encode message
  | .tradeInquiryResponseMessage5452 message => TradeInquiryResponseMessage.encode message
  | .tradeInquiryResponseMessage5453 message => TradeInquiryResponseMessage.encode message
  | .tradeConfirmationMessage message => TradeConfirmationMessage.encode message
  | .tradeConfirmationMessage2212 message => TradeConfirmationMessage.encode message
  | .tradeConfirmationMessage2222 message => TradeConfirmationMessage.encode message
  | .tradeConfirmationMessage2282 message => TradeConfirmationMessage.encode message
  | .tradeConfirmationMessage2286 message => TradeConfirmationMessage.encode message
  | .tradeConfirmationMessage2287 message => TradeConfirmationMessage.encode message
  | .tradeConfirmationMessage5449 message => TradeConfirmationMessage.encode message
  | .spreadOrderResponseMessage message => SpreadOrderResponseMessage.encode message
  | .spreadOrderResponseMessage2103 message => SpreadOrderResponseMessage.encode message
  | .spreadOrderResponseMessage2105 message => SpreadOrderResponseMessage.encode message
  | .spreadOrderResponseMessage2107 message => SpreadOrderResponseMessage.encode message
  | .spreadOrderResponseMessage2119 message => SpreadOrderResponseMessage.encode message
  | .spreadOrderResponseMessage2124 message => SpreadOrderResponseMessage.encode message
  | .spreadOrderResponseMessage2125 message => SpreadOrderResponseMessage.encode message
  | .spreadOrderResponseMessage2126 message => SpreadOrderResponseMessage.encode message
  | .spreadOrderResponseMessage2127 message => SpreadOrderResponseMessage.encode message
  | .spreadOrderResponseMessage2130 message => SpreadOrderResponseMessage.encode message
  | .spreadOrderResponseMessage2131 message => SpreadOrderResponseMessage.encode message
  | .spreadOrderResponseMessage2132 message => SpreadOrderResponseMessage.encode message
  | .spreadOrderResponseMessage2133 message => SpreadOrderResponseMessage.encode message
  | .spreadOrderResponseMessage2136 message => SpreadOrderResponseMessage.encode message
  | .spreadOrderResponseMessage2154 message => SpreadOrderResponseMessage.encode message
  | .spreadOrderResponseMessage2155 message => SpreadOrderResponseMessage.encode message
  | .spreadOrderResponseMessage2156 message => SpreadOrderResponseMessage.encode message
  | .spreadOrderResponseMessage9004 message => SpreadOrderResponseMessage.encode message
  | .spreadOrderResponseMessage27102 message => SpreadOrderResponseMessage.encode message
  | .spreadOrderResponseMessage27103 message => SpreadOrderResponseMessage.encode message
  | .spreadOrderResponseMessage27104 message => SpreadOrderResponseMessage.encode message
  | .userOrderLimitUpdateMessage message => UserOrderLimitUpdateMessage.encode message
  | .dealerLimitUpdateMessage message => DealerLimitUpdateMessage.encode message
  | .spreadOrderLimitUpdateMessage message => SpreadOrderLimitUpdateMessage.encode message
  | .controlMessageToTraderMessage message => ControlMessageToTraderMessage.encode message
  | .mbaInquiryResponseMessage message => MbaInquiryResponseMessage.encode message
  | .mbaInquiryResponseMessage1687 message => MbaInquiryResponseMessage.encode message
  | .mbaInquiryResponseMessage1689 message => MbaInquiryResponseMessage.encode message
  | .marketStatisticsReportMessage message => MarketStatisticsReportMessage.encode message
  | .spreadBhavcopyMessage message => SpreadBhavcopyMessage.encode message
  | .giveupConfirmationMessage message => GiveupConfirmationMessage.encode message
  | .giveupConfirmationMessage4507 message => GiveupConfirmationMessage.encode message
  | .gatewayRouterResponseMessage message => GatewayRouterResponseMessage.encode message
  | .secureBoxRegistrationResponseOutMessage message => SecureBoxRegistrationResponseOutMessage.encode message
  | .boxSignOnRequestOutMessage message => BoxSignOnRequestOutMessage.encode message
  | .boxSignOffMessage message => BoxSignOffMessage.encode message
  | .contingencyBroadcastMessage message => ContingencyBroadcastMessage.encode message
  | .branchOrderValueLimitUpdateResponseMessage message => BranchOrderValueLimitUpdateResponseMessage.encode message
  | .resetUserPasswordResponseMessage message => ResetUserPasswordResponseMessage.encode message
  | .collateralUserStatusChangeResponseMessage message => CollateralUserStatusChangeResponseMessage.encode message
  | .userTradeModifyCancelStatusChangeResponseMessage message => UserTradeModifyCancelStatusChangeResponseMessage.encode message
  | .userAddressUnlockConfirmMessage message => UserAddressUnlockConfirmMessage.encode message
  | .userAddressUnlockApproveMessage message => UserAddressUnlockApproveMessage.encode message
  | .userAddressUnlockApproveMessage5484 message => UserAddressUnlockApproveMessage.encode message
  | .nltOrderMessageToTraderMessage message => NltOrderMessageToTraderMessage.encode message
  | .nltOrderInquiryResponseMessage message => NltOrderInquiryResponseMessage.encode message
  | .nltTrailerRecordMessage message => NltTrailerRecordMessage.encode message

/-- Decoded from the whole of the frame: a message that reads to its end takes it all, any other must leave nothing -/
def decode (tag : BitVec 16) (bytes : List UInt8) : Option ServerMessagePayload :=
  if tag = 2301 then (SignOnRequestOutMessage.decode bytes).map fun message => .signOnRequestOutMessage message
  else if tag = 5585 then (SignOnRequestOutMessage.decode bytes).map fun message => .signOnRequestOutMessage5585 message
  else if tag = 2321 then (SignOffRequestOutMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.signOffRequestOutMessage message) else none
  else if tag = 1601 then (SystemInformationOutMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.systemInformationOutMessage message) else none
  else if tag = 7321 then (SystemInformationOutMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.systemInformationOutMessage7321 message) else none
  else if tag = 7307 then (UpdateLocalDatabaseHeaderMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.updateLocalDatabaseHeaderMessage message) else none
  else if tag = 7308 then (UpdateLocalDatabaseTrailerMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.updateLocalDatabaseTrailerMessage message) else none
  else if tag = 7304 then (UpdateLocalDatabaseDataMessage.decode bytes).map fun message => .updateLocalDatabaseDataMessage message
  else if tag = 7011 then (HeaderRecordMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.headerRecordMessage message) else none
  else if tag = 7021 then (MessageRecordMessage.decode bytes).map fun message => .messageRecordMessage message
  else if tag = 7031 then (TrailerRecordMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.trailerRecordMessage message) else none
  else if tag = 2073 then (OrderConfirmationMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderConfirmationMessage message) else none
  else if tag = 2083 then (OrderConfirmationMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderConfirmationMessage2083 message) else none
  else if tag = 2074 then (OrderModificationConfirmationMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderModificationConfirmationMessage message) else none
  else if tag = 2085 then (OrderModificationConfirmationMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderModificationConfirmationMessage2085 message) else none
  else if tag = 2001 then (OrderResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderResponseMessage message) else none
  else if tag = 2012 then (OrderResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderResponseMessage2012 message) else none
  else if tag = 2041 then (OrderResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderResponseMessage2041 message) else none
  else if tag = 2042 then (OrderResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderResponseMessage2042 message) else none
  else if tag = 2071 then (OrderResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderResponseMessage2071 message) else none
  else if tag = 2072 then (OrderResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderResponseMessage2072 message) else none
  else if tag = 2087 then (OrderResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderResponseMessage2087 message) else none
  else if tag = 2088 then (OrderResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderResponseMessage2088 message) else none
  else if tag = 2089 then (OrderResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderResponseMessage2089 message) else none
  else if tag = 2170 then (OrderResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderResponseMessage2170 message) else none
  else if tag = 2231 then (OrderResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderResponseMessage2231 message) else none
  else if tag = 9002 then (OrderResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderResponseMessage9002 message) else none
  else if tag = 27100 then (OrderResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderResponseMessage27100 message) else none
  else if tag = 2075 then (OrderCancellationConfirmationMessage.decode bytes).map fun message => .orderCancellationConfirmationMessage message
  else if tag = 2223 then (TradeInquiryResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tradeInquiryResponseMessage message) else none
  else if tag = 2288 then (TradeInquiryResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tradeInquiryResponseMessage2288 message) else none
  else if tag = 5441 then (TradeInquiryResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tradeInquiryResponseMessage5441 message) else none
  else if tag = 5450 then (TradeInquiryResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tradeInquiryResponseMessage5450 message) else none
  else if tag = 5452 then (TradeInquiryResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tradeInquiryResponseMessage5452 message) else none
  else if tag = 5453 then (TradeInquiryResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tradeInquiryResponseMessage5453 message) else none
  else if tag = 2090 then (TradeConfirmationMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tradeConfirmationMessage message) else none
  else if tag = 2212 then (TradeConfirmationMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tradeConfirmationMessage2212 message) else none
  else if tag = 2222 then (TradeConfirmationMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tradeConfirmationMessage2222 message) else none
  else if tag = 2282 then (TradeConfirmationMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tradeConfirmationMessage2282 message) else none
  else if tag = 2286 then (TradeConfirmationMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tradeConfirmationMessage2286 message) else none
  else if tag = 2287 then (TradeConfirmationMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tradeConfirmationMessage2287 message) else none
  else if tag = 5449 then (TradeConfirmationMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tradeConfirmationMessage5449 message) else none
  else if tag = 2101 then (SpreadOrderResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.spreadOrderResponseMessage message) else none
  else if tag = 2103 then (SpreadOrderResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.spreadOrderResponseMessage2103 message) else none
  else if tag = 2105 then (SpreadOrderResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.spreadOrderResponseMessage2105 message) else none
  else if tag = 2107 then (SpreadOrderResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.spreadOrderResponseMessage2107 message) else none
  else if tag = 2119 then (SpreadOrderResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.spreadOrderResponseMessage2119 message) else none
  else if tag = 2124 then (SpreadOrderResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.spreadOrderResponseMessage2124 message) else none
  else if tag = 2125 then (SpreadOrderResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.spreadOrderResponseMessage2125 message) else none
  else if tag = 2126 then (SpreadOrderResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.spreadOrderResponseMessage2126 message) else none
  else if tag = 2127 then (SpreadOrderResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.spreadOrderResponseMessage2127 message) else none
  else if tag = 2130 then (SpreadOrderResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.spreadOrderResponseMessage2130 message) else none
  else if tag = 2131 then (SpreadOrderResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.spreadOrderResponseMessage2131 message) else none
  else if tag = 2132 then (SpreadOrderResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.spreadOrderResponseMessage2132 message) else none
  else if tag = 2133 then (SpreadOrderResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.spreadOrderResponseMessage2133 message) else none
  else if tag = 2136 then (SpreadOrderResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.spreadOrderResponseMessage2136 message) else none
  else if tag = 2154 then (SpreadOrderResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.spreadOrderResponseMessage2154 message) else none
  else if tag = 2155 then (SpreadOrderResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.spreadOrderResponseMessage2155 message) else none
  else if tag = 2156 then (SpreadOrderResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.spreadOrderResponseMessage2156 message) else none
  else if tag = 9004 then (SpreadOrderResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.spreadOrderResponseMessage9004 message) else none
  else if tag = 27102 then (SpreadOrderResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.spreadOrderResponseMessage27102 message) else none
  else if tag = 27103 then (SpreadOrderResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.spreadOrderResponseMessage27103 message) else none
  else if tag = 27104 then (SpreadOrderResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.spreadOrderResponseMessage27104 message) else none
  else if tag = 5731 then (UserOrderLimitUpdateMessage.decode bytes).map fun message => .userOrderLimitUpdateMessage message
  else if tag = 5733 then (DealerLimitUpdateMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.dealerLimitUpdateMessage message) else none
  else if tag = 5772 then (SpreadOrderLimitUpdateMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.spreadOrderLimitUpdateMessage message) else none
  else if tag = 5295 then (ControlMessageToTraderMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.controlMessageToTraderMessage message) else none
  else if tag = 1685 then (MbaInquiryResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.mbaInquiryResponseMessage message) else none
  else if tag = 1687 then (MbaInquiryResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.mbaInquiryResponseMessage1687 message) else none
  else if tag = 1689 then (MbaInquiryResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.mbaInquiryResponseMessage1689 message) else none
  else if tag = 1833 then (MarketStatisticsReportMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.marketStatisticsReportMessage message) else none
  else if tag = 6502 then (SpreadBhavcopyMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.spreadBhavcopyMessage message) else none
  else if tag = 4506 then (GiveupConfirmationMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.giveupConfirmationMessage message) else none
  else if tag = 4507 then (GiveupConfirmationMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.giveupConfirmationMessage4507 message) else none
  else if tag = 2401 then (GatewayRouterResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.gatewayRouterResponseMessage message) else none
  else if tag = 23009 then (SecureBoxRegistrationResponseOutMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.secureBoxRegistrationResponseOutMessage message) else none
  else if tag = 23001 then (BoxSignOnRequestOutMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.boxSignOnRequestOutMessage message) else none
  else if tag = 20322 then (BoxSignOffMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.boxSignOffMessage message) else none
  else if tag = 5294 then (ContingencyBroadcastMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.contingencyBroadcastMessage message) else none
  else if tag = 5717 then (BranchOrderValueLimitUpdateResponseMessage.decode bytes).map fun message => .branchOrderValueLimitUpdateResponseMessage message
  else if tag = 5741 then (ResetUserPasswordResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.resetUserPasswordResponseMessage message) else none
  else if tag = 5745 then (CollateralUserStatusChangeResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.collateralUserStatusChangeResponseMessage message) else none
  else if tag = 5739 then (UserTradeModifyCancelStatusChangeResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.userTradeModifyCancelStatusChangeResponseMessage message) else none
  else if tag = 5428 then (UserAddressUnlockConfirmMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.userAddressUnlockConfirmMessage message) else none
  else if tag = 5483 then (UserAddressUnlockApproveMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.userAddressUnlockApproveMessage message) else none
  else if tag = 5484 then (UserAddressUnlockApproveMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.userAddressUnlockApproveMessage5484 message) else none
  else if tag = 2093 then (NltOrderMessageToTraderMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.nltOrderMessageToTraderMessage message) else none
  else if tag = 1243 then (NltOrderInquiryResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.nltOrderInquiryResponseMessage message) else none
  else if tag = 7032 then (NltTrailerRecordMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.nltTrailerRecordMessage message) else none
  else none

theorem decode_encode (message : ServerMessagePayload) :
    decode (tag message) (encode message) = some message := by
  cases message with
  | signOnRequestOutMessage message => simp [decode, encode, tag, SignOnRequestOutMessage.decode_encode]
  | signOnRequestOutMessage5585 message => simp [decode, encode, tag, SignOnRequestOutMessage.decode_encode]
  | signOffRequestOutMessage message => simp [decode, encode, tag, SignOffRequestOutMessage.decode_encode_nil]
  | systemInformationOutMessage message => simp [decode, encode, tag, SystemInformationOutMessage.decode_encode_nil]
  | systemInformationOutMessage7321 message => simp [decode, encode, tag, SystemInformationOutMessage.decode_encode_nil]
  | updateLocalDatabaseHeaderMessage message => simp [decode, encode, tag, UpdateLocalDatabaseHeaderMessage.decode_encode_nil]
  | updateLocalDatabaseTrailerMessage message => simp [decode, encode, tag, UpdateLocalDatabaseTrailerMessage.decode_encode_nil]
  | updateLocalDatabaseDataMessage message => simp [decode, encode, tag, UpdateLocalDatabaseDataMessage.decode_encode]
  | headerRecordMessage message => simp [decode, encode, tag, HeaderRecordMessage.decode_encode_nil]
  | messageRecordMessage message => simp [decode, encode, tag, MessageRecordMessage.decode_encode]
  | trailerRecordMessage message => simp [decode, encode, tag, TrailerRecordMessage.decode_encode_nil]
  | orderConfirmationMessage message => simp [decode, encode, tag, OrderConfirmationMessage.decode_encode_nil]
  | orderConfirmationMessage2083 message => simp [decode, encode, tag, OrderConfirmationMessage.decode_encode_nil]
  | orderModificationConfirmationMessage message => simp [decode, encode, tag, OrderModificationConfirmationMessage.decode_encode_nil]
  | orderModificationConfirmationMessage2085 message => simp [decode, encode, tag, OrderModificationConfirmationMessage.decode_encode_nil]
  | orderResponseMessage message => simp [decode, encode, tag, OrderResponseMessage.decode_encode_nil]
  | orderResponseMessage2012 message => simp [decode, encode, tag, OrderResponseMessage.decode_encode_nil]
  | orderResponseMessage2041 message => simp [decode, encode, tag, OrderResponseMessage.decode_encode_nil]
  | orderResponseMessage2042 message => simp [decode, encode, tag, OrderResponseMessage.decode_encode_nil]
  | orderResponseMessage2071 message => simp [decode, encode, tag, OrderResponseMessage.decode_encode_nil]
  | orderResponseMessage2072 message => simp [decode, encode, tag, OrderResponseMessage.decode_encode_nil]
  | orderResponseMessage2087 message => simp [decode, encode, tag, OrderResponseMessage.decode_encode_nil]
  | orderResponseMessage2088 message => simp [decode, encode, tag, OrderResponseMessage.decode_encode_nil]
  | orderResponseMessage2089 message => simp [decode, encode, tag, OrderResponseMessage.decode_encode_nil]
  | orderResponseMessage2170 message => simp [decode, encode, tag, OrderResponseMessage.decode_encode_nil]
  | orderResponseMessage2231 message => simp [decode, encode, tag, OrderResponseMessage.decode_encode_nil]
  | orderResponseMessage9002 message => simp [decode, encode, tag, OrderResponseMessage.decode_encode_nil]
  | orderResponseMessage27100 message => simp [decode, encode, tag, OrderResponseMessage.decode_encode_nil]
  | orderCancellationConfirmationMessage message => simp [decode, encode, tag, OrderCancellationConfirmationMessage.decode_encode]
  | tradeInquiryResponseMessage message => simp [decode, encode, tag, TradeInquiryResponseMessage.decode_encode_nil]
  | tradeInquiryResponseMessage2288 message => simp [decode, encode, tag, TradeInquiryResponseMessage.decode_encode_nil]
  | tradeInquiryResponseMessage5441 message => simp [decode, encode, tag, TradeInquiryResponseMessage.decode_encode_nil]
  | tradeInquiryResponseMessage5450 message => simp [decode, encode, tag, TradeInquiryResponseMessage.decode_encode_nil]
  | tradeInquiryResponseMessage5452 message => simp [decode, encode, tag, TradeInquiryResponseMessage.decode_encode_nil]
  | tradeInquiryResponseMessage5453 message => simp [decode, encode, tag, TradeInquiryResponseMessage.decode_encode_nil]
  | tradeConfirmationMessage message => simp [decode, encode, tag, TradeConfirmationMessage.decode_encode_nil]
  | tradeConfirmationMessage2212 message => simp [decode, encode, tag, TradeConfirmationMessage.decode_encode_nil]
  | tradeConfirmationMessage2222 message => simp [decode, encode, tag, TradeConfirmationMessage.decode_encode_nil]
  | tradeConfirmationMessage2282 message => simp [decode, encode, tag, TradeConfirmationMessage.decode_encode_nil]
  | tradeConfirmationMessage2286 message => simp [decode, encode, tag, TradeConfirmationMessage.decode_encode_nil]
  | tradeConfirmationMessage2287 message => simp [decode, encode, tag, TradeConfirmationMessage.decode_encode_nil]
  | tradeConfirmationMessage5449 message => simp [decode, encode, tag, TradeConfirmationMessage.decode_encode_nil]
  | spreadOrderResponseMessage message => simp [decode, encode, tag, SpreadOrderResponseMessage.decode_encode_nil]
  | spreadOrderResponseMessage2103 message => simp [decode, encode, tag, SpreadOrderResponseMessage.decode_encode_nil]
  | spreadOrderResponseMessage2105 message => simp [decode, encode, tag, SpreadOrderResponseMessage.decode_encode_nil]
  | spreadOrderResponseMessage2107 message => simp [decode, encode, tag, SpreadOrderResponseMessage.decode_encode_nil]
  | spreadOrderResponseMessage2119 message => simp [decode, encode, tag, SpreadOrderResponseMessage.decode_encode_nil]
  | spreadOrderResponseMessage2124 message => simp [decode, encode, tag, SpreadOrderResponseMessage.decode_encode_nil]
  | spreadOrderResponseMessage2125 message => simp [decode, encode, tag, SpreadOrderResponseMessage.decode_encode_nil]
  | spreadOrderResponseMessage2126 message => simp [decode, encode, tag, SpreadOrderResponseMessage.decode_encode_nil]
  | spreadOrderResponseMessage2127 message => simp [decode, encode, tag, SpreadOrderResponseMessage.decode_encode_nil]
  | spreadOrderResponseMessage2130 message => simp [decode, encode, tag, SpreadOrderResponseMessage.decode_encode_nil]
  | spreadOrderResponseMessage2131 message => simp [decode, encode, tag, SpreadOrderResponseMessage.decode_encode_nil]
  | spreadOrderResponseMessage2132 message => simp [decode, encode, tag, SpreadOrderResponseMessage.decode_encode_nil]
  | spreadOrderResponseMessage2133 message => simp [decode, encode, tag, SpreadOrderResponseMessage.decode_encode_nil]
  | spreadOrderResponseMessage2136 message => simp [decode, encode, tag, SpreadOrderResponseMessage.decode_encode_nil]
  | spreadOrderResponseMessage2154 message => simp [decode, encode, tag, SpreadOrderResponseMessage.decode_encode_nil]
  | spreadOrderResponseMessage2155 message => simp [decode, encode, tag, SpreadOrderResponseMessage.decode_encode_nil]
  | spreadOrderResponseMessage2156 message => simp [decode, encode, tag, SpreadOrderResponseMessage.decode_encode_nil]
  | spreadOrderResponseMessage9004 message => simp [decode, encode, tag, SpreadOrderResponseMessage.decode_encode_nil]
  | spreadOrderResponseMessage27102 message => simp [decode, encode, tag, SpreadOrderResponseMessage.decode_encode_nil]
  | spreadOrderResponseMessage27103 message => simp [decode, encode, tag, SpreadOrderResponseMessage.decode_encode_nil]
  | spreadOrderResponseMessage27104 message => simp [decode, encode, tag, SpreadOrderResponseMessage.decode_encode_nil]
  | userOrderLimitUpdateMessage message => simp [decode, encode, tag, UserOrderLimitUpdateMessage.decode_encode]
  | dealerLimitUpdateMessage message => simp [decode, encode, tag, DealerLimitUpdateMessage.decode_encode_nil]
  | spreadOrderLimitUpdateMessage message => simp [decode, encode, tag, SpreadOrderLimitUpdateMessage.decode_encode_nil]
  | controlMessageToTraderMessage message => simp [decode, encode, tag, ControlMessageToTraderMessage.decode_encode_nil]
  | mbaInquiryResponseMessage message => simp [decode, encode, tag, MbaInquiryResponseMessage.decode_encode_nil]
  | mbaInquiryResponseMessage1687 message => simp [decode, encode, tag, MbaInquiryResponseMessage.decode_encode_nil]
  | mbaInquiryResponseMessage1689 message => simp [decode, encode, tag, MbaInquiryResponseMessage.decode_encode_nil]
  | marketStatisticsReportMessage message => simp [decode, encode, tag, MarketStatisticsReportMessage.decode_encode_nil]
  | spreadBhavcopyMessage message => simp [decode, encode, tag, SpreadBhavcopyMessage.decode_encode_nil]
  | giveupConfirmationMessage message => simp [decode, encode, tag, GiveupConfirmationMessage.decode_encode_nil]
  | giveupConfirmationMessage4507 message => simp [decode, encode, tag, GiveupConfirmationMessage.decode_encode_nil]
  | gatewayRouterResponseMessage message => simp [decode, encode, tag, GatewayRouterResponseMessage.decode_encode_nil]
  | secureBoxRegistrationResponseOutMessage message => simp [decode, encode, tag, SecureBoxRegistrationResponseOutMessage.decode_encode_nil]
  | boxSignOnRequestOutMessage message => simp [decode, encode, tag, BoxSignOnRequestOutMessage.decode_encode_nil]
  | boxSignOffMessage message => simp [decode, encode, tag, BoxSignOffMessage.decode_encode_nil]
  | contingencyBroadcastMessage message => simp [decode, encode, tag, ContingencyBroadcastMessage.decode_encode_nil]
  | branchOrderValueLimitUpdateResponseMessage message => simp [decode, encode, tag, BranchOrderValueLimitUpdateResponseMessage.decode_encode]
  | resetUserPasswordResponseMessage message => simp [decode, encode, tag, ResetUserPasswordResponseMessage.decode_encode_nil]
  | collateralUserStatusChangeResponseMessage message => simp [decode, encode, tag, CollateralUserStatusChangeResponseMessage.decode_encode_nil]
  | userTradeModifyCancelStatusChangeResponseMessage message => simp [decode, encode, tag, UserTradeModifyCancelStatusChangeResponseMessage.decode_encode_nil]
  | userAddressUnlockConfirmMessage message => simp [decode, encode, tag, UserAddressUnlockConfirmMessage.decode_encode_nil]
  | userAddressUnlockApproveMessage message => simp [decode, encode, tag, UserAddressUnlockApproveMessage.decode_encode_nil]
  | userAddressUnlockApproveMessage5484 message => simp [decode, encode, tag, UserAddressUnlockApproveMessage.decode_encode_nil]
  | nltOrderMessageToTraderMessage message => simp [decode, encode, tag, NltOrderMessageToTraderMessage.decode_encode_nil]
  | nltOrderInquiryResponseMessage message => simp [decode, encode, tag, NltOrderInquiryResponseMessage.decode_encode_nil]
  | nltTrailerRecordMessage message => simp [decode, encode, tag, NltTrailerRecordMessage.decode_encode_nil]

end ServerMessagePayload

/-- Server Message: the body, which the record carries with the proof it fits its frame -/
structure ServerMessageBody where
  logTime : BitVec 32
  alphaChar : Alpha 2
  traderId : BitVec 32
  errorCode : BitVec 16
  headerTimestamp : Alpha 8
  timeStamp1 : Alpha 8
  timeStamp2 : Alpha 8
  serverMessagePayload : ServerMessagePayload
  deriving DecidableEq, Repr

namespace ServerMessageBody

def encodeBody (message : ServerMessageBody) : List UInt8 :=
  ServerMessagePayload.encode message.serverMessagePayload

def decodeBody (transactionCode : BitVec 16) (logTime : BitVec 32) (alphaChar : Alpha 2) (traderId : BitVec 32) (errorCode : BitVec 16) (headerTimestamp : Alpha 8) (timeStamp1 : Alpha 8) (timeStamp2 : Alpha 8) (bytes : List UInt8) : Option ServerMessageBody := do
  let serverMessagePayload ← ServerMessagePayload.decode transactionCode bytes
  pure { logTime, alphaChar, traderId, errorCode, headerTimestamp, timeStamp1, timeStamp2, serverMessagePayload }

theorem decodeBody_encodeBody (message : ServerMessageBody) : decodeBody (ServerMessagePayload.tag message.serverMessagePayload) message.logTime message.alphaChar message.traderId message.errorCode message.headerTimestamp message.timeStamp1 message.timeStamp2 (encodeBody message) = some message := by
  unfold decodeBody encodeBody
  rw [ServerMessagePayload.decode_encode, some_bind]
  rfl

end ServerMessageBody

/-- Server Message: the body with the proof its encoding fits Message Length, whose 2 bytes no bound of the fields fits -/
abbrev ServerMessage := Fitting ServerMessageBody.encodeBody 40 65536

namespace ServerMessage

def encode (message : ServerMessage) : List UInt8 :=
  encodeUInt 2 (ServerMessagePayload.tag message.val.serverMessagePayload)
    ++ (encodeUInt 4 message.val.logTime
    ++ (Alpha.encode message.val.alphaChar
    ++ (encodeUInt 4 message.val.traderId
    ++ (encodeUInt 2 message.val.errorCode
    ++ (Alpha.encode message.val.headerTimestamp
    ++ (Alpha.encode message.val.timeStamp1
    ++ (Alpha.encode message.val.timeStamp2
    ++ (encodeFramed 2 40 ServerMessageBody.encodeBody message.val))))))))

def decode (bytes : List UInt8) : Option (ServerMessage × List UInt8) := do
  let (transactionCode, bytes) ← decodeUInt 2 bytes
  let (logTime, bytes) ← decodeUInt 4 bytes
  let (alphaChar, bytes) ← Alpha.decode 2 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (errorCode, bytes) ← decodeUInt 2 bytes
  let (headerTimestamp, bytes) ← Alpha.decode 8 bytes
  let (timeStamp1, bytes) ← Alpha.decode 8 bytes
  let (timeStamp2, bytes) ← Alpha.decode 8 bytes
  decodeFittingAll 2 40 ServerMessageBody.encodeBody (ServerMessageBody.decodeBody transactionCode logTime alphaChar traderId errorCode headerTimestamp timeStamp1 timeStamp2) bytes

@[simp] theorem decode_encode (message : ServerMessage) (rest : List UInt8) :
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
  exact decodeFittingAll_encodeFramed 2 40 ServerMessageBody.encodeBody (ServerMessageBody.decodeBody (ServerMessagePayload.tag message.val.serverMessagePayload) message.val.logTime message.val.alphaChar message.val.traderId message.val.errorCode message.val.headerTimestamp message.val.timeStamp1 message.val.timeStamp2) message (ServerMessageBody.decodeBody_encodeBody message.val) rest

theorem encode_length_pos (message : ServerMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, Alpha.encode_length, List.length_append, ← Nat.add_assoc, encodeFramed_length]
  omega

/-- The most bytes an encoding can take: what the prefix can count, by the fit the message carries -/
theorem encode_length_le (message : ServerMessage) : (encode message).length ≤ 65535 := by
  have fits := message.fits
  unfold encode
  simp only [encodeUInt_length, Alpha.encode_length, List.length_append, ← Nat.add_assoc, encodeFramed_length]
  omega

end ServerMessage

/-- Server Packet -/
structure ServerPacket where
  serverMessage : List ServerMessage
  deriving DecidableEq, Repr

namespace ServerPacket

def encode (message : ServerPacket) : List UInt8 :=
  encodeMany ServerMessage.encode message.serverMessage

def decode (bytes : List UInt8) : Option ServerPacket := do
  let serverMessage ← decodeAll ServerMessage.decode bytes.length bytes
  pure { serverMessage }

theorem decode_encode (message : ServerPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany ServerMessage.encode ServerMessage.decode ServerMessage.decode_encode ServerMessage.encode_length_pos message.serverMessage _ (encodeMany_length_ge ServerMessage.encode ServerMessage.encode_length_pos message.serverMessage), some_bind]
  rfl

end ServerPacket

end Omi.NseNseixOrderentryNnfV112Server
