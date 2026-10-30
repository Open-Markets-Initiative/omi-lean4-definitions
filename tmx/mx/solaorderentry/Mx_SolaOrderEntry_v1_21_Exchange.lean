import Wire

/-!
# TMX Group Sola Order Entry v1.21

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.TmxMxSolaorderentrySailV121Exchange

/-- Status: one byte code -/
def Status.codes : List UInt8 :=
  [0x20, 0x41, 0x43, 0x45, 0x46, 0x47, 0x49, 0x4D, 0x4E, 0x51, 0x53, 0x54, 0x55, 0x57, 0x58]

inductive Status where
  | putInTheOrderBookHavingPossiblyBeenPartiallyExecuted -- Put In The Order Book Having Possibly Been Partially Executed
  | cancelledByTheTrader -- Cancelled By The Trader
  | eliminatedByTheCircuitBreaker -- Eliminated By The Circuit Breaker
  | orderEliminatedByTheSystem -- Order Eliminated By The System
  | eliminatedDueToWashTradePrevention -- Eliminated Due To Wash Trade Prevention
  | cancelledByTheFirmSupervisorUserGlobalCancel -- Cancelled By The Firm Supervisor User Global Cancel
  | eliminatedOnParticipantDisconnection -- Eliminated On Participant Disconnection
  | eliminatedByMod -- Eliminated By Mod
  | eliminatedDueToWashTradePreventionInNonTradingState -- Eliminated Due To Wash Trade Prevention In Non Trading State
  | eliminatedDueToWashTradePreventionAgainstQuote -- Eliminated Due To Wash Trade Prevention Against Quote
  | putInTheOrderBookAsStopOrder -- Put In The Order Book As Stop Order
  | eliminatedDueToTradeLimitExceeded -- Eliminated Due To Trade Limit Exceeded
  | eliminatedDueToUnpricedLeg -- Eliminated Due To Unpriced Leg
  | cancelPending -- Cancel Pending
  | orderExecutedInFullOrPartiallyAndTheRemainingPartCouldNotBePutInTheOrderBookFak -- Order Executed In Full Or Partially And The Remaining Part Could Not Be Put In The Order Book Fak
  | unlisted (byte : { byte : UInt8 // byte ∉ Status.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Status

def toByte : Status → UInt8
  | .putInTheOrderBookHavingPossiblyBeenPartiallyExecuted => 0x20
  | .cancelledByTheTrader => 0x41
  | .eliminatedByTheCircuitBreaker => 0x43
  | .orderEliminatedByTheSystem => 0x45
  | .eliminatedDueToWashTradePrevention => 0x46
  | .cancelledByTheFirmSupervisorUserGlobalCancel => 0x47
  | .eliminatedOnParticipantDisconnection => 0x49
  | .eliminatedByMod => 0x4D
  | .eliminatedDueToWashTradePreventionInNonTradingState => 0x4E
  | .eliminatedDueToWashTradePreventionAgainstQuote => 0x51
  | .putInTheOrderBookAsStopOrder => 0x53
  | .eliminatedDueToTradeLimitExceeded => 0x54
  | .eliminatedDueToUnpricedLeg => 0x55
  | .cancelPending => 0x57
  | .orderExecutedInFullOrPartiallyAndTheRemainingPartCouldNotBePutInTheOrderBookFak => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Status :=
  if byte = 0x20 then .putInTheOrderBookHavingPossiblyBeenPartiallyExecuted
  else if byte = 0x41 then .cancelledByTheTrader
  else if byte = 0x43 then .eliminatedByTheCircuitBreaker
  else if byte = 0x45 then .orderEliminatedByTheSystem
  else if byte = 0x46 then .eliminatedDueToWashTradePrevention
  else if byte = 0x47 then .cancelledByTheFirmSupervisorUserGlobalCancel
  else if byte = 0x49 then .eliminatedOnParticipantDisconnection
  else if byte = 0x4D then .eliminatedByMod
  else if byte = 0x4E then .eliminatedDueToWashTradePreventionInNonTradingState
  else if byte = 0x51 then .eliminatedDueToWashTradePreventionAgainstQuote
  else if byte = 0x53 then .putInTheOrderBookAsStopOrder
  else if byte = 0x54 then .eliminatedDueToTradeLimitExceeded
  else if byte = 0x55 then .eliminatedDueToUnpricedLeg
  else if byte = 0x57 then .cancelPending
  else .orderExecutedInFullOrPartiallyAndTheRemainingPartCouldNotBePutInTheOrderBookFak

def ofByte (byte : UInt8) : Status :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Status) : ofByte value.toByte = value := by
  cases value with
  | putInTheOrderBookHavingPossiblyBeenPartiallyExecuted => decide
  | cancelledByTheTrader => decide
  | eliminatedByTheCircuitBreaker => decide
  | orderEliminatedByTheSystem => decide
  | eliminatedDueToWashTradePrevention => decide
  | cancelledByTheFirmSupervisorUserGlobalCancel => decide
  | eliminatedOnParticipantDisconnection => decide
  | eliminatedByMod => decide
  | eliminatedDueToWashTradePreventionInNonTradingState => decide
  | eliminatedDueToWashTradePreventionAgainstQuote => decide
  | putInTheOrderBookAsStopOrder => decide
  | eliminatedDueToTradeLimitExceeded => decide
  | eliminatedDueToUnpricedLeg => decide
  | cancelPending => decide
  | orderExecutedInFullOrPartiallyAndTheRemainingPartCouldNotBePutInTheOrderBookFak => decide
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

/-- Verb Side: one byte code -/
def VerbSide.codes : List UInt8 :=
  [0x42, 0x53]

inductive VerbSide where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ VerbSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace VerbSide

def toByte : VerbSide → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : VerbSide :=
  if byte = 0x42 then .buy
  else .sell

def ofByte (byte : UInt8) : VerbSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : VerbSide) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : VerbSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (VerbSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : VerbSide) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : VerbSide) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : VerbSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end VerbSide

/-- Account Type: one byte code -/
def AccountType.codes : List UInt8 :=
  [0x31, 0x32, 0x34, 0x35, 0x44, 0x48, 0x49, 0x4C, 0x4E, 0x4F, 0x52, 0x53]

inductive AccountType where
  | customer -- Customer
  | house -- House
  | pro -- Pro
  | nonClient -- Non Client
  | nonClientShareholder -- Non Client Shareholder
  | customerShareholder -- Customer Shareholder
  | customerInsider -- Customer Insider
  | proShareholder -- Pro Shareholder
  | houseInsider -- House Insider
  | houseShareholder -- House Shareholder
  | nonClientInsider -- Non Client Insider
  | proInsider -- Pro Insider
  | unlisted (byte : { byte : UInt8 // byte ∉ AccountType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AccountType

def toByte : AccountType → UInt8
  | .customer => 0x31
  | .house => 0x32
  | .pro => 0x34
  | .nonClient => 0x35
  | .nonClientShareholder => 0x44
  | .customerShareholder => 0x48
  | .customerInsider => 0x49
  | .proShareholder => 0x4C
  | .houseInsider => 0x4E
  | .houseShareholder => 0x4F
  | .nonClientInsider => 0x52
  | .proInsider => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AccountType :=
  if byte = 0x31 then .customer
  else if byte = 0x32 then .house
  else if byte = 0x34 then .pro
  else if byte = 0x35 then .nonClient
  else if byte = 0x44 then .nonClientShareholder
  else if byte = 0x48 then .customerShareholder
  else if byte = 0x49 then .customerInsider
  else if byte = 0x4C then .proShareholder
  else if byte = 0x4E then .houseInsider
  else if byte = 0x4F then .houseShareholder
  else if byte = 0x52 then .nonClientInsider
  else .proInsider

def ofByte (byte : UInt8) : AccountType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AccountType) : ofByte value.toByte = value := by
  cases value with
  | customer => decide
  | house => decide
  | pro => decide
  | nonClient => decide
  | nonClientShareholder => decide
  | customerShareholder => decide
  | customerInsider => decide
  | proShareholder => decide
  | houseInsider => decide
  | houseShareholder => decide
  | nonClientInsider => decide
  | proInsider => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AccountType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AccountType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AccountType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : AccountType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : AccountType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AccountType

/-- Open Close: one byte code -/
def OpenClose.codes : List UInt8 :=
  [0x4F, 0x43, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x41, 0x42, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x50]

inductive OpenClose where
  | allLegsAreOpenOrSingleSecurity -- All Legs Are Open Or Single Security
  | allLegsAreClosedOrSingleSecurity -- All Legs Are Closed Or Single Security
  | leg1OpenLeg2Close -- Leg 1 Open, Leg 2 Close
  | leg1CloseLeg2Open -- Leg 1 Close, Leg 2 Open
  | leg1OpenLeg2OpenLeg3Close -- Leg 1 Open, Leg 2 Open, Leg 3 Close
  | leg1OpenLeg2CloseLeg3Open -- Leg 1 Open, Leg 2 Close, Leg 3 Open
  | leg1OpenLeg2CloseLeg3Close -- Leg 1 Open, Leg 2 Close, Leg 3 Close
  | leg1CloseLeg2OpenLeg3Open -- Leg 1 Close, Leg 2 Open, Leg 3 Open
  | leg1CloseLeg2OpenLeg3Close -- Leg 1 Close, Leg 2 Open, Leg 3 Close
  | leg1CloseLeg2CloseLeg3Open -- Leg 1 Close, Leg 2 Close, Leg 3 Open
  | leg1OpenLeg2OpenLeg3OpenLeg4Close -- Leg 1 Open, Leg 2 Open, Leg 3 Open, Leg 4 Close
  | leg1OpenLeg2OpenLeg3CloseLeg4Open -- Leg 1 Open, Leg 2 Open, Leg 3 Close, Leg 4 Open
  | leg1OpenLeg2OpenLeg3CloseLeg4Close -- Leg 1 Open, Leg 2 Open, Leg 3 Close, Leg 4 Close
  | leg1OpenLeg2CloseLeg3OpenLeg4Open -- Leg 1 Open, Leg 2 Close, Leg 3 Open, Leg 4 Open
  | leg1OpenLeg2CloseLeg3OpenLeg4Close -- Leg 1 Open, Leg 2 Close, Leg 3 Open, Leg 4 Close
  | leg1OpenLeg2CloseLeg3CloseLeg4Open -- Leg 1 Open, Leg 2 Close, Leg 3 Close, Leg 4 Open
  | leg1OpenLeg2CloseLeg3CloseLeg4Close -- Leg 1 Open, Leg 2 Close, Leg 3 Close, Leg 4 Close
  | leg1CloseLeg2OpenLeg3OpenLeg4Open -- Leg 1 Close, Leg 2 Open, Leg 3 Open, Leg 4 Open
  | leg1CloseLeg2OpenLeg3OpenLeg4Close -- Leg 1 Close, Leg 2 Open, Leg 3 Open, Leg 4 Close
  | leg1CloseLeg2OpenLeg3CloseLeg4Open -- Leg 1 Close, Leg 2 Open, Leg 3 Close, Leg 4 Open
  | leg1CloseLeg2OpenLeg3CloseLeg4Close -- Leg 1 Close, Leg 2 Open, Leg 3 Close, Leg 4 Close
  | leg1CloseLeg2CloseLeg3OpenLeg4Open -- Leg 1 Close, Leg 2 Close, Leg 3 Open, Leg 4 Open
  | leg1CloseLeg2CloseLeg3OpenLeg4Close -- Leg 1 Close, Leg 2 Close, Leg 3 Open, Leg 4 Close
  | leg1CloseLeg2CloseLeg3CloseLeg4Open -- Leg 1 Close, Leg 2 Close, Leg 3 Close, Leg 4 Open
  | unlisted (byte : { byte : UInt8 // byte ∉ OpenClose.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OpenClose

def toByte : OpenClose → UInt8
  | .allLegsAreOpenOrSingleSecurity => 0x4F
  | .allLegsAreClosedOrSingleSecurity => 0x43
  | .leg1OpenLeg2Close => 0x31
  | .leg1CloseLeg2Open => 0x32
  | .leg1OpenLeg2OpenLeg3Close => 0x33
  | .leg1OpenLeg2CloseLeg3Open => 0x34
  | .leg1OpenLeg2CloseLeg3Close => 0x35
  | .leg1CloseLeg2OpenLeg3Open => 0x36
  | .leg1CloseLeg2OpenLeg3Close => 0x37
  | .leg1CloseLeg2CloseLeg3Open => 0x38
  | .leg1OpenLeg2OpenLeg3OpenLeg4Close => 0x41
  | .leg1OpenLeg2OpenLeg3CloseLeg4Open => 0x42
  | .leg1OpenLeg2OpenLeg3CloseLeg4Close => 0x44
  | .leg1OpenLeg2CloseLeg3OpenLeg4Open => 0x45
  | .leg1OpenLeg2CloseLeg3OpenLeg4Close => 0x46
  | .leg1OpenLeg2CloseLeg3CloseLeg4Open => 0x47
  | .leg1OpenLeg2CloseLeg3CloseLeg4Close => 0x48
  | .leg1CloseLeg2OpenLeg3OpenLeg4Open => 0x49
  | .leg1CloseLeg2OpenLeg3OpenLeg4Close => 0x4A
  | .leg1CloseLeg2OpenLeg3CloseLeg4Open => 0x4B
  | .leg1CloseLeg2OpenLeg3CloseLeg4Close => 0x4C
  | .leg1CloseLeg2CloseLeg3OpenLeg4Open => 0x4D
  | .leg1CloseLeg2CloseLeg3OpenLeg4Close => 0x4E
  | .leg1CloseLeg2CloseLeg3CloseLeg4Open => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OpenClose :=
  if byte = 0x4F then .allLegsAreOpenOrSingleSecurity
  else if byte = 0x43 then .allLegsAreClosedOrSingleSecurity
  else if byte = 0x31 then .leg1OpenLeg2Close
  else if byte = 0x32 then .leg1CloseLeg2Open
  else if byte = 0x33 then .leg1OpenLeg2OpenLeg3Close
  else if byte = 0x34 then .leg1OpenLeg2CloseLeg3Open
  else if byte = 0x35 then .leg1OpenLeg2CloseLeg3Close
  else if byte = 0x36 then .leg1CloseLeg2OpenLeg3Open
  else if byte = 0x37 then .leg1CloseLeg2OpenLeg3Close
  else if byte = 0x38 then .leg1CloseLeg2CloseLeg3Open
  else if byte = 0x41 then .leg1OpenLeg2OpenLeg3OpenLeg4Close
  else if byte = 0x42 then .leg1OpenLeg2OpenLeg3CloseLeg4Open
  else if byte = 0x44 then .leg1OpenLeg2OpenLeg3CloseLeg4Close
  else if byte = 0x45 then .leg1OpenLeg2CloseLeg3OpenLeg4Open
  else if byte = 0x46 then .leg1OpenLeg2CloseLeg3OpenLeg4Close
  else if byte = 0x47 then .leg1OpenLeg2CloseLeg3CloseLeg4Open
  else if byte = 0x48 then .leg1OpenLeg2CloseLeg3CloseLeg4Close
  else if byte = 0x49 then .leg1CloseLeg2OpenLeg3OpenLeg4Open
  else if byte = 0x4A then .leg1CloseLeg2OpenLeg3OpenLeg4Close
  else if byte = 0x4B then .leg1CloseLeg2OpenLeg3CloseLeg4Open
  else if byte = 0x4C then .leg1CloseLeg2OpenLeg3CloseLeg4Close
  else if byte = 0x4D then .leg1CloseLeg2CloseLeg3OpenLeg4Open
  else if byte = 0x4E then .leg1CloseLeg2CloseLeg3OpenLeg4Close
  else .leg1CloseLeg2CloseLeg3CloseLeg4Open

def ofByte (byte : UInt8) : OpenClose :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OpenClose) : ofByte value.toByte = value := by
  cases value with
  | allLegsAreOpenOrSingleSecurity => decide
  | allLegsAreClosedOrSingleSecurity => decide
  | leg1OpenLeg2Close => decide
  | leg1CloseLeg2Open => decide
  | leg1OpenLeg2OpenLeg3Close => decide
  | leg1OpenLeg2CloseLeg3Open => decide
  | leg1OpenLeg2CloseLeg3Close => decide
  | leg1CloseLeg2OpenLeg3Open => decide
  | leg1CloseLeg2OpenLeg3Close => decide
  | leg1CloseLeg2CloseLeg3Open => decide
  | leg1OpenLeg2OpenLeg3OpenLeg4Close => decide
  | leg1OpenLeg2OpenLeg3CloseLeg4Open => decide
  | leg1OpenLeg2OpenLeg3CloseLeg4Close => decide
  | leg1OpenLeg2CloseLeg3OpenLeg4Open => decide
  | leg1OpenLeg2CloseLeg3OpenLeg4Close => decide
  | leg1OpenLeg2CloseLeg3CloseLeg4Open => decide
  | leg1OpenLeg2CloseLeg3CloseLeg4Close => decide
  | leg1CloseLeg2OpenLeg3OpenLeg4Open => decide
  | leg1CloseLeg2OpenLeg3OpenLeg4Close => decide
  | leg1CloseLeg2OpenLeg3CloseLeg4Open => decide
  | leg1CloseLeg2OpenLeg3CloseLeg4Close => decide
  | leg1CloseLeg2CloseLeg3OpenLeg4Open => decide
  | leg1CloseLeg2CloseLeg3OpenLeg4Close => decide
  | leg1CloseLeg2CloseLeg3CloseLeg4Open => decide
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

/-- Hedge Spec: one byte code -/
def HedgeSpec.codes : List UInt8 :=
  [0x48, 0x53]

inductive HedgeSpec where
  | hedger -- Hedger
  | speculator -- Speculator
  | unlisted (byte : { byte : UInt8 // byte ∉ HedgeSpec.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace HedgeSpec

def toByte : HedgeSpec → UInt8
  | .hedger => 0x48
  | .speculator => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : HedgeSpec :=
  if byte = 0x48 then .hedger
  else .speculator

def ofByte (byte : UInt8) : HedgeSpec :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : HedgeSpec) : ofByte value.toByte = value := by
  cases value with
  | hedger => decide
  | speculator => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : HedgeSpec) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (HedgeSpec × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : HedgeSpec) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : HedgeSpec) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : HedgeSpec) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end HedgeSpec

/-- Type Of Cancellation Only Q Quotes Only Can Be Returned: one byte code -/
def TypeOfCancellationOnlyQQuotesOnlyCanBeReturned.codes : List UInt8 :=
  [0x41, 0x51, 0x4F, 0x53, 0x4D]

inductive TypeOfCancellationOnlyQQuotesOnlyCanBeReturned where
  | all -- All
  | quotesOnly -- Quotes Only
  | ordersOnly -- Orders Only
  | stopOrdersOnly -- Stop Orders Only
  | marketOrdersOnly -- Market Orders Only
  | unlisted (byte : { byte : UInt8 // byte ∉ TypeOfCancellationOnlyQQuotesOnlyCanBeReturned.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TypeOfCancellationOnlyQQuotesOnlyCanBeReturned

def toByte : TypeOfCancellationOnlyQQuotesOnlyCanBeReturned → UInt8
  | .all => 0x41
  | .quotesOnly => 0x51
  | .ordersOnly => 0x4F
  | .stopOrdersOnly => 0x53
  | .marketOrdersOnly => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TypeOfCancellationOnlyQQuotesOnlyCanBeReturned :=
  if byte = 0x41 then .all
  else if byte = 0x51 then .quotesOnly
  else if byte = 0x4F then .ordersOnly
  else if byte = 0x53 then .stopOrdersOnly
  else .marketOrdersOnly

def ofByte (byte : UInt8) : TypeOfCancellationOnlyQQuotesOnlyCanBeReturned :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TypeOfCancellationOnlyQQuotesOnlyCanBeReturned) : ofByte value.toByte = value := by
  cases value with
  | all => decide
  | quotesOnly => decide
  | ordersOnly => decide
  | stopOrdersOnly => decide
  | marketOrdersOnly => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TypeOfCancellationOnlyQQuotesOnlyCanBeReturned) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TypeOfCancellationOnlyQQuotesOnlyCanBeReturned × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TypeOfCancellationOnlyQQuotesOnlyCanBeReturned) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TypeOfCancellationOnlyQQuotesOnlyCanBeReturned) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TypeOfCancellationOnlyQQuotesOnlyCanBeReturned) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TypeOfCancellationOnlyQQuotesOnlyCanBeReturned

/-- Creation Status: one byte code -/
def CreationStatus.codes : List UInt8 :=
  [0x43, 0x4D]

inductive CreationStatus where
  | createdAsSpecified -- Created as specified
  | createdWithModifications -- Created with modifications
  | unlisted (byte : { byte : UInt8 // byte ∉ CreationStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CreationStatus

def toByte : CreationStatus → UInt8
  | .createdAsSpecified => 0x43
  | .createdWithModifications => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CreationStatus :=
  if byte = 0x43 then .createdAsSpecified
  else .createdWithModifications

def ofByte (byte : UInt8) : CreationStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CreationStatus) : ofByte value.toByte = value := by
  cases value with
  | createdAsSpecified => decide
  | createdWithModifications => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CreationStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CreationStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CreationStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CreationStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CreationStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CreationStatus

/-- Leg Verb: one byte code -/
def LegVerb.codes : List UInt8 :=
  [0x42, 0x53]

inductive LegVerb where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ LegVerb.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LegVerb

def toByte : LegVerb → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LegVerb :=
  if byte = 0x42 then .buy
  else .sell

def ofByte (byte : UInt8) : LegVerb :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LegVerb) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LegVerb) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LegVerb × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LegVerb) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : LegVerb) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : LegVerb) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LegVerb

/-- Usage Status: one byte code -/
def UsageStatus.codes : List UInt8 :=
  [0x49, 0x4C, 0x52, 0x57]

inductive UsageStatus where
  | info -- Info
  | limit -- Limit
  | rejection -- Rejection
  | warning -- Warning
  | unlisted (byte : { byte : UInt8 // byte ∉ UsageStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace UsageStatus

def toByte : UsageStatus → UInt8
  | .info => 0x49
  | .limit => 0x4C
  | .rejection => 0x52
  | .warning => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : UsageStatus :=
  if byte = 0x49 then .info
  else if byte = 0x4C then .limit
  else if byte = 0x52 then .rejection
  else .warning

def ofByte (byte : UInt8) : UsageStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : UsageStatus) : ofByte value.toByte = value := by
  cases value with
  | info => decide
  | limit => decide
  | rejection => decide
  | warning => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : UsageStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (UsageStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : UsageStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : UsageStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : UsageStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end UsageStatus

/-- Limit Type: one byte code -/
def LimitType.codes : List UInt8 :=
  [0x31, 0x32, 0x33, 0x34, 0x35, 0x36]

inductive LimitType where
  | netExposure -- Net Exposure
  | longExposure -- Long Exposure
  | shortExposure -- Short Exposure
  | netPosition -- Net Position
  | longPosition -- Long Position
  | shortPosition -- Short Position
  | unlisted (byte : { byte : UInt8 // byte ∉ LimitType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LimitType

def toByte : LimitType → UInt8
  | .netExposure => 0x31
  | .longExposure => 0x32
  | .shortExposure => 0x33
  | .netPosition => 0x34
  | .longPosition => 0x35
  | .shortPosition => 0x36
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LimitType :=
  if byte = 0x31 then .netExposure
  else if byte = 0x32 then .longExposure
  else if byte = 0x33 then .shortExposure
  else if byte = 0x34 then .netPosition
  else if byte = 0x35 then .longPosition
  else .shortPosition

def ofByte (byte : UInt8) : LimitType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LimitType) : ofByte value.toByte = value := by
  cases value with
  | netExposure => decide
  | longExposure => decide
  | shortExposure => decide
  | netPosition => decide
  | longPosition => decide
  | shortPosition => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LimitType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LimitType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LimitType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : LimitType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : LimitType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LimitType

/-- Group State: one byte code -/
def GroupState.codes : List UInt8 :=
  [0x43, 0x45, 0x50, 0x4F, 0x53, 0x46, 0x4E, 0x4D, 0x42, 0x49, 0x5A]

inductive GroupState where
  | consultationStart -- Consultation Start
  | noCancelPeriod -- No Cancel Period
  | preOpening -- Pre Opening
  | opening -- Opening
  | continuousTradingSession -- Continuous Trading Session
  | consultationEnd -- Consultation End
  | modIntervention -- Mod Intervention
  | miniBatch -- Mini Batch
  | postSession -- Post Session
  | prohibited -- Prohibited
  | interrupted -- Interrupted
  | unlisted (byte : { byte : UInt8 // byte ∉ GroupState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace GroupState

def toByte : GroupState → UInt8
  | .consultationStart => 0x43
  | .noCancelPeriod => 0x45
  | .preOpening => 0x50
  | .opening => 0x4F
  | .continuousTradingSession => 0x53
  | .consultationEnd => 0x46
  | .modIntervention => 0x4E
  | .miniBatch => 0x4D
  | .postSession => 0x42
  | .prohibited => 0x49
  | .interrupted => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : GroupState :=
  if byte = 0x43 then .consultationStart
  else if byte = 0x45 then .noCancelPeriod
  else if byte = 0x50 then .preOpening
  else if byte = 0x4F then .opening
  else if byte = 0x53 then .continuousTradingSession
  else if byte = 0x46 then .consultationEnd
  else if byte = 0x4E then .modIntervention
  else if byte = 0x4D then .miniBatch
  else if byte = 0x42 then .postSession
  else if byte = 0x49 then .prohibited
  else .interrupted

def ofByte (byte : UInt8) : GroupState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : GroupState) : ofByte value.toByte = value := by
  cases value with
  | consultationStart => decide
  | noCancelPeriod => decide
  | preOpening => decide
  | opening => decide
  | continuousTradingSession => decide
  | consultationEnd => decide
  | modIntervention => decide
  | miniBatch => decide
  | postSession => decide
  | prohibited => decide
  | interrupted => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : GroupState) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (GroupState × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : GroupState) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : GroupState) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : GroupState) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end GroupState

/-- Instrument State: one byte code -/
def InstrumentState.codes : List UInt8 :=
  [0x4E, 0x46, 0x52]

inductive InstrumentState where
  | normal -- Normal
  | forbidden -- Forbidden
  | ordersAndQuotesAreProcessedInPreOpeningIfTheGroupIsInTradingStatus -- Orders And Quotes Are Processed In Pre Opening If The Group Is In Trading Status
  | unlisted (byte : { byte : UInt8 // byte ∉ InstrumentState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InstrumentState

def toByte : InstrumentState → UInt8
  | .normal => 0x4E
  | .forbidden => 0x46
  | .ordersAndQuotesAreProcessedInPreOpeningIfTheGroupIsInTradingStatus => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : InstrumentState :=
  if byte = 0x4E then .normal
  else if byte = 0x46 then .forbidden
  else .ordersAndQuotesAreProcessedInPreOpeningIfTheGroupIsInTradingStatus

def ofByte (byte : UInt8) : InstrumentState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InstrumentState) : ofByte value.toByte = value := by
  cases value with
  | normal => decide
  | forbidden => decide
  | ordersAndQuotesAreProcessedInPreOpeningIfTheGroupIsInTradingStatus => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : InstrumentState) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (InstrumentState × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : InstrumentState) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : InstrumentState) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : InstrumentState) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end InstrumentState

/-- Special Trade Indicator: one byte code -/
def SpecialTradeIndicator.codes : List UInt8 :=
  [0x20, 0x41, 0x42, 0x43, 0x44, 0x45, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x4F, 0x50, 0x51, 0x54, 0x55, 0x56, 0x5A]

inductive SpecialTradeIndicator where
  | normalTrade -- Normal Trade
  | asOfTrade -- As Of Trade
  | blockTrade -- Block Trade
  | contingentTrade -- Contingent Trade
  | cross -- Cross
  | exchangeForPhysical -- Exchange For Physical
  | hiddenTrade -- Hidden Trade
  | implied -- Implied
  | deltaTrade -- Delta Trade
  | committedBlock -- Committed Block
  | lateTrade -- Late Trade
  | forFutureUse -- For Future Use
  | forFutureUse_4e -- For Future Use
  | forFutureUse_4f -- For Future Use
  | forFutureUse_50 -- For Future Use
  | forFutureUse_51 -- For Future Use
  | committed -- Committed
  | basisOnClose -- Basis On Close
  | tradeCorrection -- Trade Correction
  | priceVolumeAdjustmentTrade -- Price Volume Adjustment Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ SpecialTradeIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SpecialTradeIndicator

def toByte : SpecialTradeIndicator → UInt8
  | .normalTrade => 0x20
  | .asOfTrade => 0x41
  | .blockTrade => 0x42
  | .contingentTrade => 0x43
  | .cross => 0x44
  | .exchangeForPhysical => 0x45
  | .hiddenTrade => 0x48
  | .implied => 0x49
  | .deltaTrade => 0x4A
  | .committedBlock => 0x4B
  | .lateTrade => 0x4C
  | .forFutureUse => 0x4D
  | .forFutureUse_4e => 0x4E
  | .forFutureUse_4f => 0x4F
  | .forFutureUse_50 => 0x50
  | .forFutureUse_51 => 0x51
  | .committed => 0x54
  | .basisOnClose => 0x55
  | .tradeCorrection => 0x56
  | .priceVolumeAdjustmentTrade => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SpecialTradeIndicator :=
  if byte = 0x20 then .normalTrade
  else if byte = 0x41 then .asOfTrade
  else if byte = 0x42 then .blockTrade
  else if byte = 0x43 then .contingentTrade
  else if byte = 0x44 then .cross
  else if byte = 0x45 then .exchangeForPhysical
  else if byte = 0x48 then .hiddenTrade
  else if byte = 0x49 then .implied
  else if byte = 0x4A then .deltaTrade
  else if byte = 0x4B then .committedBlock
  else if byte = 0x4C then .lateTrade
  else if byte = 0x4D then .forFutureUse
  else if byte = 0x4E then .forFutureUse_4e
  else if byte = 0x4F then .forFutureUse_4f
  else if byte = 0x50 then .forFutureUse_50
  else if byte = 0x51 then .forFutureUse_51
  else if byte = 0x54 then .committed
  else if byte = 0x55 then .basisOnClose
  else if byte = 0x56 then .tradeCorrection
  else .priceVolumeAdjustmentTrade

def ofByte (byte : UInt8) : SpecialTradeIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SpecialTradeIndicator) : ofByte value.toByte = value := by
  cases value with
  | normalTrade => decide
  | asOfTrade => decide
  | blockTrade => decide
  | contingentTrade => decide
  | cross => decide
  | exchangeForPhysical => decide
  | hiddenTrade => decide
  | implied => decide
  | deltaTrade => decide
  | committedBlock => decide
  | lateTrade => decide
  | forFutureUse => decide
  | forFutureUse_4e => decide
  | forFutureUse_4f => decide
  | forFutureUse_50 => decide
  | forFutureUse_51 => decide
  | committed => decide
  | basisOnClose => decide
  | tradeCorrection => decide
  | priceVolumeAdjustmentTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SpecialTradeIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SpecialTradeIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SpecialTradeIndicator) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SpecialTradeIndicator) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SpecialTradeIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SpecialTradeIndicator

/-- Price Type: one byte code -/
def PriceType.codes : List UInt8 :=
  [0x43, 0x4C, 0x4F, 0x4D]

inductive PriceType where
  | committed -- Committed
  | limitPriceSetInMessage -- Limit Price Set In Message
  | atOpeningPrice -- At Opening Price
  | atBestOppositePriceTopOrder -- At Best Opposite Price Top Order
  | unlisted (byte : { byte : UInt8 // byte ∉ PriceType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PriceType

def toByte : PriceType → UInt8
  | .committed => 0x43
  | .limitPriceSetInMessage => 0x4C
  | .atOpeningPrice => 0x4F
  | .atBestOppositePriceTopOrder => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PriceType :=
  if byte = 0x43 then .committed
  else if byte = 0x4C then .limitPriceSetInMessage
  else if byte = 0x4F then .atOpeningPrice
  else .atBestOppositePriceTopOrder

def ofByte (byte : UInt8) : PriceType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PriceType) : ofByte value.toByte = value := by
  cases value with
  | committed => decide
  | limitPriceSetInMessage => decide
  | atOpeningPrice => decide
  | atBestOppositePriceTopOrder => decide
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

/-- Trade Type: one byte code -/
def TradeType.codes : List UInt8 :=
  [0x46, 0x4D, 0x4F]

inductive TradeType where
  | tradedDuringContinuousTradingFollowingFifoAlgorithm -- Traded During Continuous Trading Following Fifo Algorithm
  | tradeEnteredByMod -- Trade Entered By Mod
  | tradedDuringOpening -- Traded During Opening
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeType

def toByte : TradeType → UInt8
  | .tradedDuringContinuousTradingFollowingFifoAlgorithm => 0x46
  | .tradeEnteredByMod => 0x4D
  | .tradedDuringOpening => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeType :=
  if byte = 0x46 then .tradedDuringContinuousTradingFollowingFifoAlgorithm
  else if byte = 0x4D then .tradeEnteredByMod
  else .tradedDuringOpening

def ofByte (byte : UInt8) : TradeType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeType) : ofByte value.toByte = value := by
  cases value with
  | tradedDuringContinuousTradingFollowingFifoAlgorithm => decide
  | tradeEnteredByMod => decide
  | tradedDuringOpening => decide
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

/-- Verb: one byte code -/
def Verb.codes : List UInt8 :=
  [0x42, 0x53]

inductive Verb where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ Verb.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Verb

def toByte : Verb → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Verb :=
  if byte = 0x42 then .buy
  else .sell

def ofByte (byte : UInt8) : Verb :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Verb) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Verb) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Verb × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Verb) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Verb) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Verb) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Verb

/-- Order Type: one byte code -/
def OrderType.codes : List UInt8 :=
  [0x4F, 0x51]

inductive OrderType where
  | order -- Order
  | quote -- Quote
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderType

def toByte : OrderType → UInt8
  | .order => 0x4F
  | .quote => 0x51
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderType :=
  if byte = 0x4F then .order
  else .quote

def ofByte (byte : UInt8) : OrderType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderType) : ofByte value.toByte = value := by
  cases value with
  | order => decide
  | quote => decide
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

/-- Cancel Reason: one byte code -/
def CancelReason.codes : List UInt8 :=
  [0x41, 0x43, 0x47, 0x49, 0x4D, 0x4E, 0x50, 0x52, 0x53, 0x54, 0x56, 0x57]

inductive CancelReason where
  | cancelledByTrader -- Cancelled By Trader
  | cancelledByCircuitBreaker -- Cancelled By Circuit Breaker
  | cancelledBySupervisor -- Cancelled By Supervisor
  | eliminatedByDisconnection -- Eliminated By Disconnection
  | cancelledByMod -- Cancelled By Mod
  | bqmMaximumDeltaVolumeHasBeenReached -- Bqm Maximum Delta Volume Has Been Reached
  | bqmMaximumNumberOfTradesHasBeenReached -- Bqm Maximum Number Of Trades Has Been Reached
  | bqmMaximumValueHasBeenReached -- Bqm Maximum Value Has Been Reached
  | cancelledBySystem -- Cancelled By System
  | bqmMaximumVolumeHasBeenReached -- Bqm Maximum Volume Has Been Reached
  | bqmMaximumDeltaValueHasBeenReached -- Bqm Maximum Delta Value Has Been Reached
  | cancelPending -- Cancel Pending
  | unlisted (byte : { byte : UInt8 // byte ∉ CancelReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CancelReason

def toByte : CancelReason → UInt8
  | .cancelledByTrader => 0x41
  | .cancelledByCircuitBreaker => 0x43
  | .cancelledBySupervisor => 0x47
  | .eliminatedByDisconnection => 0x49
  | .cancelledByMod => 0x4D
  | .bqmMaximumDeltaVolumeHasBeenReached => 0x4E
  | .bqmMaximumNumberOfTradesHasBeenReached => 0x50
  | .bqmMaximumValueHasBeenReached => 0x52
  | .cancelledBySystem => 0x53
  | .bqmMaximumVolumeHasBeenReached => 0x54
  | .bqmMaximumDeltaValueHasBeenReached => 0x56
  | .cancelPending => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CancelReason :=
  if byte = 0x41 then .cancelledByTrader
  else if byte = 0x43 then .cancelledByCircuitBreaker
  else if byte = 0x47 then .cancelledBySupervisor
  else if byte = 0x49 then .eliminatedByDisconnection
  else if byte = 0x4D then .cancelledByMod
  else if byte = 0x4E then .bqmMaximumDeltaVolumeHasBeenReached
  else if byte = 0x50 then .bqmMaximumNumberOfTradesHasBeenReached
  else if byte = 0x52 then .bqmMaximumValueHasBeenReached
  else if byte = 0x53 then .cancelledBySystem
  else if byte = 0x54 then .bqmMaximumVolumeHasBeenReached
  else if byte = 0x56 then .bqmMaximumDeltaValueHasBeenReached
  else .cancelPending

def ofByte (byte : UInt8) : CancelReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CancelReason) : ofByte value.toByte = value := by
  cases value with
  | cancelledByTrader => decide
  | cancelledByCircuitBreaker => decide
  | cancelledBySupervisor => decide
  | eliminatedByDisconnection => decide
  | cancelledByMod => decide
  | bqmMaximumDeltaVolumeHasBeenReached => decide
  | bqmMaximumNumberOfTradesHasBeenReached => decide
  | bqmMaximumValueHasBeenReached => decide
  | cancelledBySystem => decide
  | bqmMaximumVolumeHasBeenReached => decide
  | bqmMaximumDeltaValueHasBeenReached => decide
  | cancelPending => decide
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

/-- Market Side: one byte code -/
def MarketSide.codes : List UInt8 :=
  [0x42, 0x53, 0x32]

inductive MarketSide where
  | buy -- Buy
  | sell -- Sell
  | both -- Both
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketSide

def toByte : MarketSide → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .both => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketSide :=
  if byte = 0x42 then .buy
  else if byte = 0x53 then .sell
  else .both

def ofByte (byte : UInt8) : MarketSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketSide) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | both => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarketSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketSide) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : MarketSide) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : MarketSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarketSide

/-- Connection Acknowledgement: 12 bytes -/
structure ConnectionAcknowledgement where
  currentSessionId : Alpha 4
  lastUserSequenceIdReceived : Alpha 8
  deriving DecidableEq, Repr

namespace ConnectionAcknowledgement

def encode (message : ConnectionAcknowledgement) : List UInt8 :=
  Alpha.encode message.currentSessionId
    ++ (Alpha.encode message.lastUserSequenceIdReceived)

def decode (bytes : List UInt8) : Option (ConnectionAcknowledgement × List UInt8) := do
  let (currentSessionId, bytes) ← Alpha.decode 4 bytes
  let (lastUserSequenceIdReceived, bytes) ← Alpha.decode 8 bytes
  pure ({ currentSessionId, lastUserSequenceIdReceived }, bytes)

@[simp] theorem encode_length (message : ConnectionAcknowledgement) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : ConnectionAcknowledgement) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ConnectionAcknowledgement) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ConnectionAcknowledgement

/-- Disconnection Instruction Acknowledgement: 12 bytes -/
structure DisconnectionInstructionAcknowledgement where
  currentSessionId : Alpha 4
  lastUserSequenceIdReceived : Alpha 8
  deriving DecidableEq, Repr

namespace DisconnectionInstructionAcknowledgement

def encode (message : DisconnectionInstructionAcknowledgement) : List UInt8 :=
  Alpha.encode message.currentSessionId
    ++ (Alpha.encode message.lastUserSequenceIdReceived)

def decode (bytes : List UInt8) : Option (DisconnectionInstructionAcknowledgement × List UInt8) := do
  let (currentSessionId, bytes) ← Alpha.decode 4 bytes
  let (lastUserSequenceIdReceived, bytes) ← Alpha.decode 8 bytes
  pure ({ currentSessionId, lastUserSequenceIdReceived }, bytes)

@[simp] theorem encode_length (message : DisconnectionInstructionAcknowledgement) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : DisconnectionInstructionAcknowledgement) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DisconnectionInstructionAcknowledgement) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end DisconnectionInstructionAcknowledgement

/-- Heartbeat Question: 20 bytes -/
structure HeartbeatQuestion where
  userSequenceIdFirstUserSequenceIdForNextcurrentHeartbeatPeriod : Alpha 8
  lastExchangeMessageIdSentToParticipant : Alpha 6
  tradingEngineTimestampLocalHhmmss : Alpha 6
  deriving DecidableEq, Repr

namespace HeartbeatQuestion

def encode (message : HeartbeatQuestion) : List UInt8 :=
  Alpha.encode message.userSequenceIdFirstUserSequenceIdForNextcurrentHeartbeatPeriod
    ++ (Alpha.encode message.lastExchangeMessageIdSentToParticipant
    ++ (Alpha.encode message.tradingEngineTimestampLocalHhmmss))

def decode (bytes : List UInt8) : Option (HeartbeatQuestion × List UInt8) := do
  let (userSequenceIdFirstUserSequenceIdForNextcurrentHeartbeatPeriod, bytes) ← Alpha.decode 8 bytes
  let (lastExchangeMessageIdSentToParticipant, bytes) ← Alpha.decode 6 bytes
  let (tradingEngineTimestampLocalHhmmss, bytes) ← Alpha.decode 6 bytes
  pure ({ userSequenceIdFirstUserSequenceIdForNextcurrentHeartbeatPeriod, lastExchangeMessageIdSentToParticipant, tradingEngineTimestampLocalHhmmss }, bytes)

@[simp] theorem encode_length (message : HeartbeatQuestion) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : HeartbeatQuestion) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : HeartbeatQuestion) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end HeartbeatQuestion

/-- Out Of Sequence: 22 bytes -/
structure OutOfSequence where
  receivedUserSequenceId : Alpha 8
  expectedLastUserSequenceId : Alpha 8
  userMessageTimestampLocalHhmmss : Alpha 6
  deriving DecidableEq, Repr

namespace OutOfSequence

def encode (message : OutOfSequence) : List UInt8 :=
  Alpha.encode message.receivedUserSequenceId
    ++ (Alpha.encode message.expectedLastUserSequenceId
    ++ (Alpha.encode message.userMessageTimestampLocalHhmmss))

def decode (bytes : List UInt8) : Option (OutOfSequence × List UInt8) := do
  let (receivedUserSequenceId, bytes) ← Alpha.decode 8 bytes
  let (expectedLastUserSequenceId, bytes) ← Alpha.decode 8 bytes
  let (userMessageTimestampLocalHhmmss, bytes) ← Alpha.decode 6 bytes
  pure ({ receivedUserSequenceId, expectedLastUserSequenceId, userMessageTimestampLocalHhmmss }, bytes)

@[simp] theorem encode_length (message : OutOfSequence) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : OutOfSequence) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OutOfSequence) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OutOfSequence

/-- Technical Error Notice: 218 bytes -/
structure TechnicalErrorNotice where
  receivedMessageType : Alpha 2
  precedingUserSequenceIdReceivedZeroesIfNone : Alpha 8
  errorCode : Alpha 4
  errorPosition : Alpha 4
  errorMessage : Alpha 100
  startOfMessageInError : Alpha 100
  deriving DecidableEq, Repr

namespace TechnicalErrorNotice

def encode (message : TechnicalErrorNotice) : List UInt8 :=
  Alpha.encode message.receivedMessageType
    ++ (Alpha.encode message.precedingUserSequenceIdReceivedZeroesIfNone
    ++ (Alpha.encode message.errorCode
    ++ (Alpha.encode message.errorPosition
    ++ (Alpha.encode message.errorMessage
    ++ (Alpha.encode message.startOfMessageInError)))))

def decode (bytes : List UInt8) : Option (TechnicalErrorNotice × List UInt8) := do
  let (receivedMessageType, bytes) ← Alpha.decode 2 bytes
  let (precedingUserSequenceIdReceivedZeroesIfNone, bytes) ← Alpha.decode 8 bytes
  let (errorCode, bytes) ← Alpha.decode 4 bytes
  let (errorPosition, bytes) ← Alpha.decode 4 bytes
  let (errorMessage, bytes) ← Alpha.decode 100 bytes
  let (startOfMessageInError, bytes) ← Alpha.decode 100 bytes
  pure ({ receivedMessageType, precedingUserSequenceIdReceivedZeroesIfNone, errorCode, errorPosition, errorMessage, startOfMessageInError }, bytes)

@[simp] theorem encode_length (message : TechnicalErrorNotice) : (encode message).length = 218 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : TechnicalErrorNotice) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TechnicalErrorNotice) (rest : List UInt8) :
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

end TechnicalErrorNotice

/-- Disconnection Acknowledgement: 12 bytes -/
structure DisconnectionAcknowledgement where
  currentSessionId : Alpha 4
  lastUserSequenceIdReceived : Alpha 8
  deriving DecidableEq, Repr

namespace DisconnectionAcknowledgement

def encode (message : DisconnectionAcknowledgement) : List UInt8 :=
  Alpha.encode message.currentSessionId
    ++ (Alpha.encode message.lastUserSequenceIdReceived)

def decode (bytes : List UInt8) : Option (DisconnectionAcknowledgement × List UInt8) := do
  let (currentSessionId, bytes) ← Alpha.decode 4 bytes
  let (lastUserSequenceIdReceived, bytes) ← Alpha.decode 8 bytes
  pure ({ currentSessionId, lastUserSequenceIdReceived }, bytes)

@[simp] theorem encode_length (message : DisconnectionAcknowledgement) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : DisconnectionAcknowledgement) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DisconnectionAcknowledgement) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end DisconnectionAcknowledgement

/-- End Of Transmission: 18 bytes -/
structure EndOfTransmission where
  endedSessionId : Alpha 4
  lastUserSequenceIdReceivedIfNoBusinessMessageHasBeenReceivedOnThisConnectionThisFieldIsEqualToZeroes : Alpha 8
  tradingEngineTimestampLocalHhmmss : Alpha 6
  deriving DecidableEq, Repr

namespace EndOfTransmission

def encode (message : EndOfTransmission) : List UInt8 :=
  Alpha.encode message.endedSessionId
    ++ (Alpha.encode message.lastUserSequenceIdReceivedIfNoBusinessMessageHasBeenReceivedOnThisConnectionThisFieldIsEqualToZeroes
    ++ (Alpha.encode message.tradingEngineTimestampLocalHhmmss))

def decode (bytes : List UInt8) : Option (EndOfTransmission × List UInt8) := do
  let (endedSessionId, bytes) ← Alpha.decode 4 bytes
  let (lastUserSequenceIdReceivedIfNoBusinessMessageHasBeenReceivedOnThisConnectionThisFieldIsEqualToZeroes, bytes) ← Alpha.decode 8 bytes
  let (tradingEngineTimestampLocalHhmmss, bytes) ← Alpha.decode 6 bytes
  pure ({ endedSessionId, lastUserSequenceIdReceivedIfNoBusinessMessageHasBeenReceivedOnThisConnectionThisFieldIsEqualToZeroes, tradingEngineTimestampLocalHhmmss }, bytes)

@[simp] theorem encode_length (message : EndOfTransmission) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : EndOfTransmission) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EndOfTransmission) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end EndOfTransmission

/-- Outgoing Messages Header: 22 bytes -/
structure OutgoingMessagesHeader where
  tradingEngineTimestampLocalHhmmss : Alpha 6
  userSequenceId : Alpha 8
  exchangeMessageId : Alpha 6
  gapSequenceId : Alpha 2
  deriving DecidableEq, Repr

namespace OutgoingMessagesHeader

def encode (message : OutgoingMessagesHeader) : List UInt8 :=
  Alpha.encode message.tradingEngineTimestampLocalHhmmss
    ++ (Alpha.encode message.userSequenceId
    ++ (Alpha.encode message.exchangeMessageId
    ++ (Alpha.encode message.gapSequenceId)))

def decode (bytes : List UInt8) : Option (OutgoingMessagesHeader × List UInt8) := do
  let (tradingEngineTimestampLocalHhmmss, bytes) ← Alpha.decode 6 bytes
  let (userSequenceId, bytes) ← Alpha.decode 8 bytes
  let (exchangeMessageId, bytes) ← Alpha.decode 6 bytes
  let (gapSequenceId, bytes) ← Alpha.decode 2 bytes
  pure ({ tradingEngineTimestampLocalHhmmss, userSequenceId, exchangeMessageId, gapSequenceId }, bytes)

@[simp] theorem encode_length (message : OutgoingMessagesHeader) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : OutgoingMessagesHeader) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OutgoingMessagesHeader) (rest : List UInt8) :
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

end OutgoingMessagesHeader

/-- Clearing Data: 20 bytes -/
structure ClearingData where
  clearingInstruction : Alpha 12
  accountType : AccountType
  openClose : OpenClose
  hedgeSpec : HedgeSpec
  filler5 : Alpha 5
  deriving DecidableEq, Repr

namespace ClearingData

def encode (message : ClearingData) : List UInt8 :=
  Alpha.encode message.clearingInstruction
    ++ (AccountType.encode message.accountType
    ++ (OpenClose.encode message.openClose
    ++ (HedgeSpec.encode message.hedgeSpec
    ++ (Alpha.encode message.filler5))))

def decode (bytes : List UInt8) : Option (ClearingData × List UInt8) := do
  let (clearingInstruction, bytes) ← Alpha.decode 12 bytes
  let (accountType, bytes) ← AccountType.decode bytes
  let (openClose, bytes) ← OpenClose.decode bytes
  let (hedgeSpec, bytes) ← HedgeSpec.decode bytes
  let (filler5, bytes) ← Alpha.decode 5 bytes
  pure ({ clearingInstruction, accountType, openClose, hedgeSpec, filler5 }, bytes)

@[simp] theorem encode_length (message : ClearingData) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, AccountType.encode_length, OpenClose.encode_length, HedgeSpec.encode_length]

theorem encode_length_pos (message : ClearingData) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ClearingData) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AccountType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpenClose.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, HedgeSpec.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ClearingData

/-- Owner Data: 50 bytes -/
structure OwnerData where
  memo : Alpha 50
  deriving DecidableEq, Repr

namespace OwnerData

def encode (message : OwnerData) : List UInt8 :=
  Alpha.encode message.memo

def decode (bytes : List UInt8) : Option (OwnerData × List UInt8) := do
  let (memo, bytes) ← Alpha.decode 50 bytes
  pure ({ memo }, bytes)

@[simp] theorem encode_length (message : OwnerData) : (encode message).length = 50 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : OwnerData) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OwnerData) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end OwnerData

/-- Order Reply: 134 bytes -/
structure OrderReply where
  outgoingMessagesHeader : OutgoingMessagesHeader
  group : Alpha 2
  instrument : Alpha 4
  traderId : Alpha 8
  orderId : Alpha 8
  status : Status
  verbSide : VerbSide
  quantityRemaining : Alpha 8
  assignedPrice : Alpha 10
  clearingData : ClearingData
  ownerData : OwnerData
  deriving DecidableEq, Repr

namespace OrderReply

def encode (message : OrderReply) : List UInt8 :=
  OutgoingMessagesHeader.encode message.outgoingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.orderId
    ++ (Status.encode message.status
    ++ (VerbSide.encode message.verbSide
    ++ (Alpha.encode message.quantityRemaining
    ++ (Alpha.encode message.assignedPrice
    ++ (ClearingData.encode message.clearingData
    ++ (OwnerData.encode message.ownerData))))))))))

def decode (bytes : List UInt8) : Option (OrderReply × List UInt8) := do
  let (outgoingMessagesHeader, bytes) ← OutgoingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (orderId, bytes) ← Alpha.decode 8 bytes
  let (status, bytes) ← Status.decode bytes
  let (verbSide, bytes) ← VerbSide.decode bytes
  let (quantityRemaining, bytes) ← Alpha.decode 8 bytes
  let (assignedPrice, bytes) ← Alpha.decode 10 bytes
  let (clearingData, bytes) ← ClearingData.decode bytes
  let (ownerData, bytes) ← OwnerData.decode bytes
  pure ({ outgoingMessagesHeader, group, instrument, traderId, orderId, status, verbSide, quantityRemaining, assignedPrice, clearingData, ownerData }, bytes)

@[simp] theorem encode_length (message : OrderReply) : (encode message).length = 134 := by
  unfold encode
  simp only [List.length_append, OutgoingMessagesHeader.encode_length, Alpha.encode_length, Status.encode_length, VerbSide.encode_length, ClearingData.encode_length, OwnerData.encode_length]

theorem encode_length_pos (message : OrderReply) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderReply) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OutgoingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Status.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, VerbSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ClearingData.decode_encode, some_bind]
  dsimp only
  rw [OwnerData.decode_encode, some_bind]
  rfl

end OrderReply

/-- Error Notice: 126 bytes -/
structure ErrorNotice where
  outgoingMessagesHeader : OutgoingMessagesHeader
  errorCode : Alpha 4
  errorDescription : Alpha 100
  deriving DecidableEq, Repr

namespace ErrorNotice

def encode (message : ErrorNotice) : List UInt8 :=
  OutgoingMessagesHeader.encode message.outgoingMessagesHeader
    ++ (Alpha.encode message.errorCode
    ++ (Alpha.encode message.errorDescription))

def decode (bytes : List UInt8) : Option (ErrorNotice × List UInt8) := do
  let (outgoingMessagesHeader, bytes) ← OutgoingMessagesHeader.decode bytes
  let (errorCode, bytes) ← Alpha.decode 4 bytes
  let (errorDescription, bytes) ← Alpha.decode 100 bytes
  pure ({ outgoingMessagesHeader, errorCode, errorDescription }, bytes)

@[simp] theorem encode_length (message : ErrorNotice) : (encode message).length = 126 := by
  unfold encode
  simp only [List.length_append, OutgoingMessagesHeader.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : ErrorNotice) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ErrorNotice) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OutgoingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ErrorNotice

/-- Bulk Quote Data Acknowledgement: 40 bytes -/
structure BulkQuoteDataAcknowledgement where
  outgoingMessagesHeader : OutgoingMessagesHeader
  group : Alpha 2
  traderId : Alpha 8
  quoteIdIdentifiesTradersQuoteOnThisGroup : Alpha 8
  deriving DecidableEq, Repr

namespace BulkQuoteDataAcknowledgement

def encode (message : BulkQuoteDataAcknowledgement) : List UInt8 :=
  OutgoingMessagesHeader.encode message.outgoingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.quoteIdIdentifiesTradersQuoteOnThisGroup)))

def decode (bytes : List UInt8) : Option (BulkQuoteDataAcknowledgement × List UInt8) := do
  let (outgoingMessagesHeader, bytes) ← OutgoingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (quoteIdIdentifiesTradersQuoteOnThisGroup, bytes) ← Alpha.decode 8 bytes
  pure ({ outgoingMessagesHeader, group, traderId, quoteIdIdentifiesTradersQuoteOnThisGroup }, bytes)

@[simp] theorem encode_length (message : BulkQuoteDataAcknowledgement) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, OutgoingMessagesHeader.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : BulkQuoteDataAcknowledgement) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BulkQuoteDataAcknowledgement) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OutgoingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BulkQuoteDataAcknowledgement

/-- Order Acknowledgement: 148 bytes -/
structure OrderAcknowledgement where
  outgoingMessagesHeader : OutgoingMessagesHeader
  group : Alpha 2
  instrument : Alpha 4
  traderId : Alpha 8
  orderId : Alpha 8
  status : Status
  verbSide : VerbSide
  quantity : Alpha 8
  assignedPrice : Alpha 10
  clearingData : ClearingData
  ownerData : OwnerData
  originalOrderId : Alpha 8
  filler6 : Alpha 6
  deriving DecidableEq, Repr

namespace OrderAcknowledgement

def encode (message : OrderAcknowledgement) : List UInt8 :=
  OutgoingMessagesHeader.encode message.outgoingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.orderId
    ++ (Status.encode message.status
    ++ (VerbSide.encode message.verbSide
    ++ (Alpha.encode message.quantity
    ++ (Alpha.encode message.assignedPrice
    ++ (ClearingData.encode message.clearingData
    ++ (OwnerData.encode message.ownerData
    ++ (Alpha.encode message.originalOrderId
    ++ (Alpha.encode message.filler6))))))))))))

def decode (bytes : List UInt8) : Option (OrderAcknowledgement × List UInt8) := do
  let (outgoingMessagesHeader, bytes) ← OutgoingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (orderId, bytes) ← Alpha.decode 8 bytes
  let (status, bytes) ← Status.decode bytes
  let (verbSide, bytes) ← VerbSide.decode bytes
  let (quantity, bytes) ← Alpha.decode 8 bytes
  let (assignedPrice, bytes) ← Alpha.decode 10 bytes
  let (clearingData, bytes) ← ClearingData.decode bytes
  let (ownerData, bytes) ← OwnerData.decode bytes
  let (originalOrderId, bytes) ← Alpha.decode 8 bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  pure ({ outgoingMessagesHeader, group, instrument, traderId, orderId, status, verbSide, quantity, assignedPrice, clearingData, ownerData, originalOrderId, filler6 }, bytes)

@[simp] theorem encode_length (message : OrderAcknowledgement) : (encode message).length = 148 := by
  unfold encode
  simp only [List.length_append, OutgoingMessagesHeader.encode_length, Alpha.encode_length, Status.encode_length, VerbSide.encode_length, ClearingData.encode_length, OwnerData.encode_length]

theorem encode_length_pos (message : OrderAcknowledgement) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderAcknowledgement) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OutgoingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Status.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, VerbSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ClearingData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OwnerData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderAcknowledgement

/-- Global Cancellation Confirmation: 33 bytes -/
structure GlobalCancellationConfirmation where
  outgoingMessagesHeader : OutgoingMessagesHeader
  group : Alpha 2
  traderId : Alpha 8
  typeOfCancellationOnlyQQuotesOnlyCanBeReturned : TypeOfCancellationOnlyQQuotesOnlyCanBeReturned
  deriving DecidableEq, Repr

namespace GlobalCancellationConfirmation

def encode (message : GlobalCancellationConfirmation) : List UInt8 :=
  OutgoingMessagesHeader.encode message.outgoingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.traderId
    ++ (TypeOfCancellationOnlyQQuotesOnlyCanBeReturned.encode message.typeOfCancellationOnlyQQuotesOnlyCanBeReturned)))

def decode (bytes : List UInt8) : Option (GlobalCancellationConfirmation × List UInt8) := do
  let (outgoingMessagesHeader, bytes) ← OutgoingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (typeOfCancellationOnlyQQuotesOnlyCanBeReturned, bytes) ← TypeOfCancellationOnlyQQuotesOnlyCanBeReturned.decode bytes
  pure ({ outgoingMessagesHeader, group, traderId, typeOfCancellationOnlyQQuotesOnlyCanBeReturned }, bytes)

@[simp] theorem encode_length (message : GlobalCancellationConfirmation) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, OutgoingMessagesHeader.encode_length, Alpha.encode_length, TypeOfCancellationOnlyQQuotesOnlyCanBeReturned.encode_length]

theorem encode_length_pos (message : GlobalCancellationConfirmation) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : GlobalCancellationConfirmation) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OutgoingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [TypeOfCancellationOnlyQQuotesOnlyCanBeReturned.decode_encode, some_bind]
  rfl

end GlobalCancellationConfirmation

/-- Order Modification Acknowledgement: 148 bytes -/
structure OrderModificationAcknowledgement where
  outgoingMessagesHeader : OutgoingMessagesHeader
  group : Alpha 2
  instrument : Alpha 4
  traderId : Alpha 8
  orderId : Alpha 8
  status : Status
  verbSide : VerbSide
  quantity : Alpha 8
  assignedPrice : Alpha 10
  clearingData : ClearingData
  ownerData : OwnerData
  originalOrderId : Alpha 8
  filler6 : Alpha 6
  deriving DecidableEq, Repr

namespace OrderModificationAcknowledgement

def encode (message : OrderModificationAcknowledgement) : List UInt8 :=
  OutgoingMessagesHeader.encode message.outgoingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.orderId
    ++ (Status.encode message.status
    ++ (VerbSide.encode message.verbSide
    ++ (Alpha.encode message.quantity
    ++ (Alpha.encode message.assignedPrice
    ++ (ClearingData.encode message.clearingData
    ++ (OwnerData.encode message.ownerData
    ++ (Alpha.encode message.originalOrderId
    ++ (Alpha.encode message.filler6))))))))))))

def decode (bytes : List UInt8) : Option (OrderModificationAcknowledgement × List UInt8) := do
  let (outgoingMessagesHeader, bytes) ← OutgoingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (orderId, bytes) ← Alpha.decode 8 bytes
  let (status, bytes) ← Status.decode bytes
  let (verbSide, bytes) ← VerbSide.decode bytes
  let (quantity, bytes) ← Alpha.decode 8 bytes
  let (assignedPrice, bytes) ← Alpha.decode 10 bytes
  let (clearingData, bytes) ← ClearingData.decode bytes
  let (ownerData, bytes) ← OwnerData.decode bytes
  let (originalOrderId, bytes) ← Alpha.decode 8 bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  pure ({ outgoingMessagesHeader, group, instrument, traderId, orderId, status, verbSide, quantity, assignedPrice, clearingData, ownerData, originalOrderId, filler6 }, bytes)

@[simp] theorem encode_length (message : OrderModificationAcknowledgement) : (encode message).length = 148 := by
  unfold encode
  simp only [List.length_append, OutgoingMessagesHeader.encode_length, Alpha.encode_length, Status.encode_length, VerbSide.encode_length, ClearingData.encode_length, OwnerData.encode_length]

theorem encode_length_pos (message : OrderModificationAcknowledgement) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderModificationAcknowledgement) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OutgoingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Status.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, VerbSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ClearingData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OwnerData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderModificationAcknowledgement

/-- New Strategy Instrument Acknowledgement Leg Definition Repeating Block: 16 bytes -/
structure NewStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock where
  legGroup : Alpha 2
  legInstrument : Alpha 4
  legVerb : LegVerb
  filler1 : Alpha 1
  legQuantityRatio : Alpha 8
  deriving DecidableEq, Repr

namespace NewStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock

def encode (message : NewStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock) : List UInt8 :=
  Alpha.encode message.legGroup
    ++ (Alpha.encode message.legInstrument
    ++ (LegVerb.encode message.legVerb
    ++ (Alpha.encode message.filler1
    ++ (Alpha.encode message.legQuantityRatio))))

def decode (bytes : List UInt8) : Option (NewStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock × List UInt8) := do
  let (legGroup, bytes) ← Alpha.decode 2 bytes
  let (legInstrument, bytes) ← Alpha.decode 4 bytes
  let (legVerb, bytes) ← LegVerb.decode bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (legQuantityRatio, bytes) ← Alpha.decode 8 bytes
  pure ({ legGroup, legInstrument, legVerb, filler1, legQuantityRatio }, bytes)

@[simp] theorem encode_length (message : NewStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, LegVerb.encode_length]

theorem encode_length_pos (message : NewStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LegVerb.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end NewStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock

/-- New Strategy Instrument Acknowledgement -/
structure NewStrategyInstrumentAcknowledgement where
  outgoingMessagesHeader : OutgoingMessagesHeader
  strategyGroup : Alpha 2
  strategyInstrument : Alpha 4
  creationStatus : CreationStatus
  newStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock : Digited 2 NewStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock
  deriving DecidableEq, Repr

namespace NewStrategyInstrumentAcknowledgement

def encode (message : NewStrategyInstrumentAcknowledgement) : List UInt8 :=
  OutgoingMessagesHeader.encode message.outgoingMessagesHeader
    ++ (Alpha.encode message.strategyGroup
    ++ (Alpha.encode message.strategyInstrument
    ++ (CreationStatus.encode message.creationStatus
    ++ (encodeDigits 2 message.newStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock.val.length
    ++ (encodeMany NewStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock.encode message.newStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock.val)))))

def decode (bytes : List UInt8) : Option (NewStrategyInstrumentAcknowledgement × List UInt8) := do
  let (outgoingMessagesHeader, bytes) ← OutgoingMessagesHeader.decode bytes
  let (strategyGroup, bytes) ← Alpha.decode 2 bytes
  let (strategyInstrument, bytes) ← Alpha.decode 4 bytes
  let (creationStatus, bytes) ← CreationStatus.decode bytes
  let (numberOfLegs, bytes) ← decodeDigits 2 bytes
  let (newStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock_, bytes) ← decodeMany NewStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock.decode numberOfLegs bytes
  if fits_newStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock : newStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock_.length < 10 ^ 2 then
    pure ({ outgoingMessagesHeader, strategyGroup, strategyInstrument, creationStatus, newStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock := ⟨newStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock_, fits_newStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock⟩ }, bytes)
  else none

theorem encode_length_pos (message : NewStrategyInstrumentAcknowledgement) : (encode message).length > 0 := by
  unfold encode
  simp only [OutgoingMessagesHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : NewStrategyInstrumentAcknowledgement) : (encode message).length ≤ 1615 := by
  have bound_newStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock := message.newStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, OutgoingMessagesHeader.encode_length, Alpha.encode_length, CreationStatus.encode_length, encodeDigits_length, encodeMany_length_const NewStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock.encode 16 NewStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock.encode_length]
  omega

@[simp] theorem decode_encode (message : NewStrategyInstrumentAcknowledgement) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OutgoingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CreationStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.newStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany NewStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock.encode NewStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock.decode NewStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.newStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock.length_lt]
  rfl

end NewStrategyInstrumentAcknowledgement

/-- Standard Acknowledgement: 32 bytes -/
structure StandardAcknowledgement where
  outgoingMessagesHeader : OutgoingMessagesHeader
  traderId : Alpha 8
  originalMessageTypeAfGzMlOxOrRq : Alpha 2
  deriving DecidableEq, Repr

namespace StandardAcknowledgement

def encode (message : StandardAcknowledgement) : List UInt8 :=
  OutgoingMessagesHeader.encode message.outgoingMessagesHeader
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.originalMessageTypeAfGzMlOxOrRq))

def decode (bytes : List UInt8) : Option (StandardAcknowledgement × List UInt8) := do
  let (outgoingMessagesHeader, bytes) ← OutgoingMessagesHeader.decode bytes
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (originalMessageTypeAfGzMlOxOrRq, bytes) ← Alpha.decode 2 bytes
  pure ({ outgoingMessagesHeader, traderId, originalMessageTypeAfGzMlOxOrRq }, bytes)

@[simp] theorem encode_length (message : StandardAcknowledgement) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, OutgoingMessagesHeader.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : StandardAcknowledgement) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StandardAcknowledgement) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OutgoingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StandardAcknowledgement

/-- Order Cancellation Acknowledgement: 148 bytes -/
structure OrderCancellationAcknowledgement where
  outgoingMessagesHeader : OutgoingMessagesHeader
  group : Alpha 2
  instrument : Alpha 4
  traderId : Alpha 8
  orderId : Alpha 8
  status : Status
  verbSide : VerbSide
  quantity : Alpha 8
  assignedPrice : Alpha 10
  clearingData : ClearingData
  ownerData : OwnerData
  originalOrderId : Alpha 8
  filler6 : Alpha 6
  deriving DecidableEq, Repr

namespace OrderCancellationAcknowledgement

def encode (message : OrderCancellationAcknowledgement) : List UInt8 :=
  OutgoingMessagesHeader.encode message.outgoingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.orderId
    ++ (Status.encode message.status
    ++ (VerbSide.encode message.verbSide
    ++ (Alpha.encode message.quantity
    ++ (Alpha.encode message.assignedPrice
    ++ (ClearingData.encode message.clearingData
    ++ (OwnerData.encode message.ownerData
    ++ (Alpha.encode message.originalOrderId
    ++ (Alpha.encode message.filler6))))))))))))

def decode (bytes : List UInt8) : Option (OrderCancellationAcknowledgement × List UInt8) := do
  let (outgoingMessagesHeader, bytes) ← OutgoingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (orderId, bytes) ← Alpha.decode 8 bytes
  let (status, bytes) ← Status.decode bytes
  let (verbSide, bytes) ← VerbSide.decode bytes
  let (quantity, bytes) ← Alpha.decode 8 bytes
  let (assignedPrice, bytes) ← Alpha.decode 10 bytes
  let (clearingData, bytes) ← ClearingData.decode bytes
  let (ownerData, bytes) ← OwnerData.decode bytes
  let (originalOrderId, bytes) ← Alpha.decode 8 bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  pure ({ outgoingMessagesHeader, group, instrument, traderId, orderId, status, verbSide, quantity, assignedPrice, clearingData, ownerData, originalOrderId, filler6 }, bytes)

@[simp] theorem encode_length (message : OrderCancellationAcknowledgement) : (encode message).length = 148 := by
  unfold encode
  simp only [List.length_append, OutgoingMessagesHeader.encode_length, Alpha.encode_length, Status.encode_length, VerbSide.encode_length, ClearingData.encode_length, OwnerData.encode_length]

theorem encode_length_pos (message : OrderCancellationAcknowledgement) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancellationAcknowledgement) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OutgoingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Status.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, VerbSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ClearingData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OwnerData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderCancellationAcknowledgement

/-- Bulk Quote Acknowledgement Occurrence: 7 bytes -/
structure BulkQuoteAcknowledgementOccurrence where
  quoteNumber : Alpha 3
  errorCode : Alpha 4
  deriving DecidableEq, Repr

namespace BulkQuoteAcknowledgementOccurrence

def encode (message : BulkQuoteAcknowledgementOccurrence) : List UInt8 :=
  Alpha.encode message.quoteNumber
    ++ (Alpha.encode message.errorCode)

def decode (bytes : List UInt8) : Option (BulkQuoteAcknowledgementOccurrence × List UInt8) := do
  let (quoteNumber, bytes) ← Alpha.decode 3 bytes
  let (errorCode, bytes) ← Alpha.decode 4 bytes
  pure ({ quoteNumber, errorCode }, bytes)

@[simp] theorem encode_length (message : BulkQuoteAcknowledgementOccurrence) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : BulkQuoteAcknowledgementOccurrence) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BulkQuoteAcknowledgementOccurrence) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BulkQuoteAcknowledgementOccurrence

/-- Bulk Quote Acknowledgement -/
structure BulkQuoteAcknowledgement where
  outgoingMessagesHeader : OutgoingMessagesHeader
  group : Alpha 2
  quoteIdentifierOnThisGroup : Alpha 8
  bulkQuoteAcknowledgementOccurrence : Digited 3 BulkQuoteAcknowledgementOccurrence
  deriving DecidableEq, Repr

namespace BulkQuoteAcknowledgement

def encode (message : BulkQuoteAcknowledgement) : List UInt8 :=
  OutgoingMessagesHeader.encode message.outgoingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.quoteIdentifierOnThisGroup
    ++ (encodeDigits 3 message.bulkQuoteAcknowledgementOccurrence.val.length
    ++ (encodeMany BulkQuoteAcknowledgementOccurrence.encode message.bulkQuoteAcknowledgementOccurrence.val))))

def decode (bytes : List UInt8) : Option (BulkQuoteAcknowledgement × List UInt8) := do
  let (outgoingMessagesHeader, bytes) ← OutgoingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (quoteIdentifierOnThisGroup, bytes) ← Alpha.decode 8 bytes
  let (numberOfQuotesInError, bytes) ← decodeDigits 3 bytes
  let (bulkQuoteAcknowledgementOccurrence_, bytes) ← decodeMany BulkQuoteAcknowledgementOccurrence.decode numberOfQuotesInError bytes
  if fits_bulkQuoteAcknowledgementOccurrence : bulkQuoteAcknowledgementOccurrence_.length < 10 ^ 3 then
    pure ({ outgoingMessagesHeader, group, quoteIdentifierOnThisGroup, bulkQuoteAcknowledgementOccurrence := ⟨bulkQuoteAcknowledgementOccurrence_, fits_bulkQuoteAcknowledgementOccurrence⟩ }, bytes)
  else none

theorem encode_length_pos (message : BulkQuoteAcknowledgement) : (encode message).length > 0 := by
  unfold encode
  simp only [OutgoingMessagesHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : BulkQuoteAcknowledgement) : (encode message).length ≤ 7028 := by
  have bound_bulkQuoteAcknowledgementOccurrence := message.bulkQuoteAcknowledgementOccurrence.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, OutgoingMessagesHeader.encode_length, Alpha.encode_length, encodeDigits_length, encodeMany_length_const BulkQuoteAcknowledgementOccurrence.encode 7 BulkQuoteAcknowledgementOccurrence.encode_length]
  omega

@[simp] theorem decode_encode (message : BulkQuoteAcknowledgement) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OutgoingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.bulkQuoteAcknowledgementOccurrence.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany BulkQuoteAcknowledgementOccurrence.encode BulkQuoteAcknowledgementOccurrence.decode BulkQuoteAcknowledgementOccurrence.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.bulkQuoteAcknowledgementOccurrence.length_lt]
  rfl

end BulkQuoteAcknowledgement

/-- Bulk Command Acknowledgement Occurrence: 8 bytes -/
structure BulkCommandAcknowledgementOccurrence where
  commandNumber : Alpha 4
  errorCode : Alpha 4
  deriving DecidableEq, Repr

namespace BulkCommandAcknowledgementOccurrence

def encode (message : BulkCommandAcknowledgementOccurrence) : List UInt8 :=
  Alpha.encode message.commandNumber
    ++ (Alpha.encode message.errorCode)

def decode (bytes : List UInt8) : Option (BulkCommandAcknowledgementOccurrence × List UInt8) := do
  let (commandNumber, bytes) ← Alpha.decode 4 bytes
  let (errorCode, bytes) ← Alpha.decode 4 bytes
  pure ({ commandNumber, errorCode }, bytes)

@[simp] theorem encode_length (message : BulkCommandAcknowledgementOccurrence) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : BulkCommandAcknowledgementOccurrence) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BulkCommandAcknowledgementOccurrence) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BulkCommandAcknowledgementOccurrence

/-- Bulk Command Acknowledgement -/
structure BulkCommandAcknowledgement where
  outgoingMessagesHeader : OutgoingMessagesHeader
  bulkCommandAcknowledgementOccurrence : Digited 4 BulkCommandAcknowledgementOccurrence
  deriving DecidableEq, Repr

namespace BulkCommandAcknowledgement

def encode (message : BulkCommandAcknowledgement) : List UInt8 :=
  OutgoingMessagesHeader.encode message.outgoingMessagesHeader
    ++ (encodeDigits 4 message.bulkCommandAcknowledgementOccurrence.val.length
    ++ (encodeMany BulkCommandAcknowledgementOccurrence.encode message.bulkCommandAcknowledgementOccurrence.val))

def decode (bytes : List UInt8) : Option (BulkCommandAcknowledgement × List UInt8) := do
  let (outgoingMessagesHeader, bytes) ← OutgoingMessagesHeader.decode bytes
  let (numberOfCommands, bytes) ← decodeDigits 4 bytes
  let (bulkCommandAcknowledgementOccurrence_, bytes) ← decodeMany BulkCommandAcknowledgementOccurrence.decode numberOfCommands bytes
  if fits_bulkCommandAcknowledgementOccurrence : bulkCommandAcknowledgementOccurrence_.length < 10 ^ 4 then
    pure ({ outgoingMessagesHeader, bulkCommandAcknowledgementOccurrence := ⟨bulkCommandAcknowledgementOccurrence_, fits_bulkCommandAcknowledgementOccurrence⟩ }, bytes)
  else none

theorem encode_length_pos (message : BulkCommandAcknowledgement) : (encode message).length > 0 := by
  unfold encode
  simp only [OutgoingMessagesHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : BulkCommandAcknowledgement) : (encode message).length ≤ 80018 := by
  have bound_bulkCommandAcknowledgementOccurrence := message.bulkCommandAcknowledgementOccurrence.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, OutgoingMessagesHeader.encode_length, encodeDigits_length, encodeMany_length_const BulkCommandAcknowledgementOccurrence.encode 8 BulkCommandAcknowledgementOccurrence.encode_length]
  omega

@[simp] theorem decode_encode (message : BulkCommandAcknowledgement) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OutgoingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.bulkCommandAcknowledgementOccurrence.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany BulkCommandAcknowledgementOccurrence.encode BulkCommandAcknowledgementOccurrence.decode BulkCommandAcknowledgementOccurrence.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.bulkCommandAcknowledgementOccurrence.length_lt]
  rfl

end BulkCommandAcknowledgement

/-- Risk Limits Usage Occurrence: 28 bytes -/
structure RiskLimitsUsageOccurrence where
  usageTrader : Alpha 4
  usageGroup : Alpha 2
  usageStatus : UsageStatus
  limitType : LimitType
  currentUsage : Alpha 10
  limitValue : Alpha 10
  deriving DecidableEq, Repr

namespace RiskLimitsUsageOccurrence

def encode (message : RiskLimitsUsageOccurrence) : List UInt8 :=
  Alpha.encode message.usageTrader
    ++ (Alpha.encode message.usageGroup
    ++ (UsageStatus.encode message.usageStatus
    ++ (LimitType.encode message.limitType
    ++ (Alpha.encode message.currentUsage
    ++ (Alpha.encode message.limitValue)))))

def decode (bytes : List UInt8) : Option (RiskLimitsUsageOccurrence × List UInt8) := do
  let (usageTrader, bytes) ← Alpha.decode 4 bytes
  let (usageGroup, bytes) ← Alpha.decode 2 bytes
  let (usageStatus, bytes) ← UsageStatus.decode bytes
  let (limitType, bytes) ← LimitType.decode bytes
  let (currentUsage, bytes) ← Alpha.decode 10 bytes
  let (limitValue, bytes) ← Alpha.decode 10 bytes
  pure ({ usageTrader, usageGroup, usageStatus, limitType, currentUsage, limitValue }, bytes)

@[simp] theorem encode_length (message : RiskLimitsUsageOccurrence) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, UsageStatus.encode_length, LimitType.encode_length]

theorem encode_length_pos (message : RiskLimitsUsageOccurrence) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RiskLimitsUsageOccurrence) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, UsageStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LimitType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end RiskLimitsUsageOccurrence

/-- Risk Limits Usage -/
structure RiskLimitsUsage where
  outgoingMessagesHeader : OutgoingMessagesHeader
  riskLimitsUsageOccurrence : Digited 4 RiskLimitsUsageOccurrence
  deriving DecidableEq, Repr

namespace RiskLimitsUsage

def encode (message : RiskLimitsUsage) : List UInt8 :=
  OutgoingMessagesHeader.encode message.outgoingMessagesHeader
    ++ (encodeDigits 4 message.riskLimitsUsageOccurrence.val.length
    ++ (encodeMany RiskLimitsUsageOccurrence.encode message.riskLimitsUsageOccurrence.val))

def decode (bytes : List UInt8) : Option (RiskLimitsUsage × List UInt8) := do
  let (outgoingMessagesHeader, bytes) ← OutgoingMessagesHeader.decode bytes
  let (numberOfUsageBlocks, bytes) ← decodeDigits 4 bytes
  let (riskLimitsUsageOccurrence_, bytes) ← decodeMany RiskLimitsUsageOccurrence.decode numberOfUsageBlocks bytes
  if fits_riskLimitsUsageOccurrence : riskLimitsUsageOccurrence_.length < 10 ^ 4 then
    pure ({ outgoingMessagesHeader, riskLimitsUsageOccurrence := ⟨riskLimitsUsageOccurrence_, fits_riskLimitsUsageOccurrence⟩ }, bytes)
  else none

theorem encode_length_pos (message : RiskLimitsUsage) : (encode message).length > 0 := by
  unfold encode
  simp only [OutgoingMessagesHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : RiskLimitsUsage) : (encode message).length ≤ 279998 := by
  have bound_riskLimitsUsageOccurrence := message.riskLimitsUsageOccurrence.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, OutgoingMessagesHeader.encode_length, encodeDigits_length, encodeMany_length_const RiskLimitsUsageOccurrence.encode 28 RiskLimitsUsageOccurrence.encode_length]
  omega

@[simp] theorem decode_encode (message : RiskLimitsUsage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OutgoingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.riskLimitsUsageOccurrence.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany RiskLimitsUsageOccurrence.encode RiskLimitsUsageOccurrence.decode RiskLimitsUsageOccurrence.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.riskLimitsUsageOccurrence.length_lt]
  rfl

end RiskLimitsUsage

/-- Excluded Instrument Notice Occurrence: 4 bytes -/
structure ExcludedInstrumentNoticeOccurrence where
  instrument : Alpha 4
  deriving DecidableEq, Repr

namespace ExcludedInstrumentNoticeOccurrence

def encode (message : ExcludedInstrumentNoticeOccurrence) : List UInt8 :=
  Alpha.encode message.instrument

def decode (bytes : List UInt8) : Option (ExcludedInstrumentNoticeOccurrence × List UInt8) := do
  let (instrument, bytes) ← Alpha.decode 4 bytes
  pure ({ instrument }, bytes)

@[simp] theorem encode_length (message : ExcludedInstrumentNoticeOccurrence) : (encode message).length = 4 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : ExcludedInstrumentNoticeOccurrence) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExcludedInstrumentNoticeOccurrence) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end ExcludedInstrumentNoticeOccurrence

/-- Excluded Instrument Notice -/
structure ExcludedInstrumentNotice where
  outgoingMessagesHeader : OutgoingMessagesHeader
  group : Alpha 2
  filler2 : Alpha 2
  traderId : Alpha 8
  filler4 : Alpha 4
  excludedInstrumentNoticeOccurrence : Digited 4 ExcludedInstrumentNoticeOccurrence
  deriving DecidableEq, Repr

namespace ExcludedInstrumentNotice

def encode (message : ExcludedInstrumentNotice) : List UInt8 :=
  OutgoingMessagesHeader.encode message.outgoingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.filler2
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.filler4
    ++ (encodeDigits 4 message.excludedInstrumentNoticeOccurrence.val.length
    ++ (encodeMany ExcludedInstrumentNoticeOccurrence.encode message.excludedInstrumentNoticeOccurrence.val))))))

def decode (bytes : List UInt8) : Option (ExcludedInstrumentNotice × List UInt8) := do
  let (outgoingMessagesHeader, bytes) ← OutgoingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (filler2, bytes) ← Alpha.decode 2 bytes
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (filler4, bytes) ← Alpha.decode 4 bytes
  let (nbOfInstruments, bytes) ← decodeDigits 4 bytes
  let (excludedInstrumentNoticeOccurrence_, bytes) ← decodeMany ExcludedInstrumentNoticeOccurrence.decode nbOfInstruments bytes
  if fits_excludedInstrumentNoticeOccurrence : excludedInstrumentNoticeOccurrence_.length < 10 ^ 4 then
    pure ({ outgoingMessagesHeader, group, filler2, traderId, filler4, excludedInstrumentNoticeOccurrence := ⟨excludedInstrumentNoticeOccurrence_, fits_excludedInstrumentNoticeOccurrence⟩ }, bytes)
  else none

theorem encode_length_pos (message : ExcludedInstrumentNotice) : (encode message).length > 0 := by
  unfold encode
  simp only [OutgoingMessagesHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ExcludedInstrumentNotice) : (encode message).length ≤ 40038 := by
  have bound_excludedInstrumentNoticeOccurrence := message.excludedInstrumentNoticeOccurrence.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, OutgoingMessagesHeader.encode_length, Alpha.encode_length, encodeDigits_length, encodeMany_length_const ExcludedInstrumentNoticeOccurrence.encode 4 ExcludedInstrumentNoticeOccurrence.encode_length]
  omega

@[simp] theorem decode_encode (message : ExcludedInstrumentNotice) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OutgoingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.excludedInstrumentNoticeOccurrence.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany ExcludedInstrumentNoticeOccurrence.encode ExcludedInstrumentNoticeOccurrence.decode ExcludedInstrumentNoticeOccurrence.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.excludedInstrumentNoticeOccurrence.length_lt]
  rfl

end ExcludedInstrumentNotice

/-- Group State Change: 25 bytes -/
structure GroupStateChange where
  outgoingMessagesHeader : OutgoingMessagesHeader
  group : Alpha 2
  groupState : GroupState
  deriving DecidableEq, Repr

namespace GroupStateChange

def encode (message : GroupStateChange) : List UInt8 :=
  OutgoingMessagesHeader.encode message.outgoingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (GroupState.encode message.groupState))

def decode (bytes : List UInt8) : Option (GroupStateChange × List UInt8) := do
  let (outgoingMessagesHeader, bytes) ← OutgoingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (groupState, bytes) ← GroupState.decode bytes
  pure ({ outgoingMessagesHeader, group, groupState }, bytes)

@[simp] theorem encode_length (message : GroupStateChange) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, OutgoingMessagesHeader.encode_length, Alpha.encode_length, GroupState.encode_length]

theorem encode_length_pos (message : GroupStateChange) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : GroupStateChange) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OutgoingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [GroupState.decode_encode, some_bind]
  rfl

end GroupStateChange

/-- Instrument State Change: 29 bytes -/
structure InstrumentStateChange where
  outgoingMessagesHeader : OutgoingMessagesHeader
  group : Alpha 2
  instrument : Alpha 4
  instrumentState : InstrumentState
  deriving DecidableEq, Repr

namespace InstrumentStateChange

def encode (message : InstrumentStateChange) : List UInt8 :=
  OutgoingMessagesHeader.encode message.outgoingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (InstrumentState.encode message.instrumentState)))

def decode (bytes : List UInt8) : Option (InstrumentStateChange × List UInt8) := do
  let (outgoingMessagesHeader, bytes) ← OutgoingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (instrumentState, bytes) ← InstrumentState.decode bytes
  pure ({ outgoingMessagesHeader, group, instrument, instrumentState }, bytes)

@[simp] theorem encode_length (message : InstrumentStateChange) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, OutgoingMessagesHeader.encode_length, Alpha.encode_length, InstrumentState.encode_length]

theorem encode_length_pos (message : InstrumentStateChange) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentStateChange) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OutgoingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [InstrumentState.decode_encode, some_bind]
  rfl

end InstrumentStateChange

/-- Leg Execution Notice: 235 bytes -/
structure LegExecutionNotice where
  outgoingMessagesHeader : OutgoingMessagesHeader
  group : Alpha 2
  instrument : Alpha 4
  traderId : Alpha 8
  referenceIdOrderIdOrQuoteId : Alpha 8
  verbSide : VerbSide
  quantityTraded : Alpha 8
  tradePrice : Alpha 10
  tradingEngineTimestampOfTheTradeLocalHhmmss : Alpha 6
  clearingData : ClearingData
  ownerData : OwnerData
  specialTradeIndicator : SpecialTradeIndicator
  priceType : PriceType
  tradeType : TradeType
  filler6 : Alpha 6
  tradeNumber : Alpha 8
  tradeMemo : Alpha 50
  originalReferenceId : Alpha 8
  idCodeForTheCounterpartParticipant : Alpha 4
  strategyGroup : Alpha 2
  strategyInstrumentId : Alpha 4
  strategyVerbSide : Alpha 1
  strategyTradeNumber : Alpha 8
  legNumber : Alpha 2
  deriving DecidableEq, Repr

namespace LegExecutionNotice

def encode (message : LegExecutionNotice) : List UInt8 :=
  OutgoingMessagesHeader.encode message.outgoingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.referenceIdOrderIdOrQuoteId
    ++ (VerbSide.encode message.verbSide
    ++ (Alpha.encode message.quantityTraded
    ++ (Alpha.encode message.tradePrice
    ++ (Alpha.encode message.tradingEngineTimestampOfTheTradeLocalHhmmss
    ++ (ClearingData.encode message.clearingData
    ++ (OwnerData.encode message.ownerData
    ++ (SpecialTradeIndicator.encode message.specialTradeIndicator
    ++ (PriceType.encode message.priceType
    ++ (TradeType.encode message.tradeType
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.tradeNumber
    ++ (Alpha.encode message.tradeMemo
    ++ (Alpha.encode message.originalReferenceId
    ++ (Alpha.encode message.idCodeForTheCounterpartParticipant
    ++ (Alpha.encode message.strategyGroup
    ++ (Alpha.encode message.strategyInstrumentId
    ++ (Alpha.encode message.strategyVerbSide
    ++ (Alpha.encode message.strategyTradeNumber
    ++ (Alpha.encode message.legNumber)))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (LegExecutionNotice × List UInt8) := do
  let (outgoingMessagesHeader, bytes) ← OutgoingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (referenceIdOrderIdOrQuoteId, bytes) ← Alpha.decode 8 bytes
  let (verbSide, bytes) ← VerbSide.decode bytes
  let (quantityTraded, bytes) ← Alpha.decode 8 bytes
  let (tradePrice, bytes) ← Alpha.decode 10 bytes
  let (tradingEngineTimestampOfTheTradeLocalHhmmss, bytes) ← Alpha.decode 6 bytes
  let (clearingData, bytes) ← ClearingData.decode bytes
  let (ownerData, bytes) ← OwnerData.decode bytes
  let (specialTradeIndicator, bytes) ← SpecialTradeIndicator.decode bytes
  let (priceType, bytes) ← PriceType.decode bytes
  let (tradeType, bytes) ← TradeType.decode bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  let (tradeMemo, bytes) ← Alpha.decode 50 bytes
  let (originalReferenceId, bytes) ← Alpha.decode 8 bytes
  let (idCodeForTheCounterpartParticipant, bytes) ← Alpha.decode 4 bytes
  let (strategyGroup, bytes) ← Alpha.decode 2 bytes
  let (strategyInstrumentId, bytes) ← Alpha.decode 4 bytes
  let (strategyVerbSide, bytes) ← Alpha.decode 1 bytes
  let (strategyTradeNumber, bytes) ← Alpha.decode 8 bytes
  let (legNumber, bytes) ← Alpha.decode 2 bytes
  pure ({ outgoingMessagesHeader, group, instrument, traderId, referenceIdOrderIdOrQuoteId, verbSide, quantityTraded, tradePrice, tradingEngineTimestampOfTheTradeLocalHhmmss, clearingData, ownerData, specialTradeIndicator, priceType, tradeType, filler6, tradeNumber, tradeMemo, originalReferenceId, idCodeForTheCounterpartParticipant, strategyGroup, strategyInstrumentId, strategyVerbSide, strategyTradeNumber, legNumber }, bytes)

@[simp] theorem encode_length (message : LegExecutionNotice) : (encode message).length = 235 := by
  unfold encode
  simp only [List.length_append, OutgoingMessagesHeader.encode_length, Alpha.encode_length, VerbSide.encode_length, ClearingData.encode_length, OwnerData.encode_length, SpecialTradeIndicator.encode_length, PriceType.encode_length, TradeType.encode_length]

theorem encode_length_pos (message : LegExecutionNotice) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LegExecutionNotice) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OutgoingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, VerbSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ClearingData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OwnerData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SpecialTradeIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PriceType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeType.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LegExecutionNotice

/-- Counterpart Owner Data: 50 bytes -/
structure CounterpartOwnerData where
  memo : Alpha 50
  deriving DecidableEq, Repr

namespace CounterpartOwnerData

def encode (message : CounterpartOwnerData) : List UInt8 :=
  Alpha.encode message.memo

def decode (bytes : List UInt8) : Option (CounterpartOwnerData × List UInt8) := do
  let (memo, bytes) ← Alpha.decode 50 bytes
  pure ({ memo }, bytes)

@[simp] theorem encode_length (message : CounterpartOwnerData) : (encode message).length = 50 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : CounterpartOwnerData) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CounterpartOwnerData) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end CounterpartOwnerData

/-- Overstepped Order Or Quote Notice: 112 bytes -/
structure OversteppedOrderOrQuoteNotice where
  outgoingMessagesHeader : OutgoingMessagesHeader
  group : Alpha 2
  instrument : Alpha 4
  verb : Verb
  orderType : OrderType
  traderId : Alpha 8
  orderId : Alpha 8
  counterpartTraderId : Alpha 8
  counterpartOrderId : Alpha 8
  counterpartOwnerData : CounterpartOwnerData
  deriving DecidableEq, Repr

namespace OversteppedOrderOrQuoteNotice

def encode (message : OversteppedOrderOrQuoteNotice) : List UInt8 :=
  OutgoingMessagesHeader.encode message.outgoingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Verb.encode message.verb
    ++ (OrderType.encode message.orderType
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.orderId
    ++ (Alpha.encode message.counterpartTraderId
    ++ (Alpha.encode message.counterpartOrderId
    ++ (CounterpartOwnerData.encode message.counterpartOwnerData)))))))))

def decode (bytes : List UInt8) : Option (OversteppedOrderOrQuoteNotice × List UInt8) := do
  let (outgoingMessagesHeader, bytes) ← OutgoingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (verb, bytes) ← Verb.decode bytes
  let (orderType, bytes) ← OrderType.decode bytes
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (orderId, bytes) ← Alpha.decode 8 bytes
  let (counterpartTraderId, bytes) ← Alpha.decode 8 bytes
  let (counterpartOrderId, bytes) ← Alpha.decode 8 bytes
  let (counterpartOwnerData, bytes) ← CounterpartOwnerData.decode bytes
  pure ({ outgoingMessagesHeader, group, instrument, verb, orderType, traderId, orderId, counterpartTraderId, counterpartOrderId, counterpartOwnerData }, bytes)

@[simp] theorem encode_length (message : OversteppedOrderOrQuoteNotice) : (encode message).length = 112 := by
  unfold encode
  simp only [List.length_append, OutgoingMessagesHeader.encode_length, Alpha.encode_length, Verb.encode_length, OrderType.encode_length, CounterpartOwnerData.encode_length]

theorem encode_length_pos (message : OversteppedOrderOrQuoteNotice) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OversteppedOrderOrQuoteNotice) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OutgoingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Verb.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [CounterpartOwnerData.decode_encode, some_bind]
  rfl

end OversteppedOrderOrQuoteNotice

/-- Cancellation Of All Quotes Notice: 37 bytes -/
structure CancellationOfAllQuotesNotice where
  outgoingMessagesHeader : OutgoingMessagesHeader
  group : Alpha 2
  instrument : Alpha 4
  traderId : Alpha 8
  cancelReason : CancelReason
  deriving DecidableEq, Repr

namespace CancellationOfAllQuotesNotice

def encode (message : CancellationOfAllQuotesNotice) : List UInt8 :=
  OutgoingMessagesHeader.encode message.outgoingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.traderId
    ++ (CancelReason.encode message.cancelReason))))

def decode (bytes : List UInt8) : Option (CancellationOfAllQuotesNotice × List UInt8) := do
  let (outgoingMessagesHeader, bytes) ← OutgoingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (cancelReason, bytes) ← CancelReason.decode bytes
  pure ({ outgoingMessagesHeader, group, instrument, traderId, cancelReason }, bytes)

@[simp] theorem encode_length (message : CancellationOfAllQuotesNotice) : (encode message).length = 37 := by
  unfold encode
  simp only [List.length_append, OutgoingMessagesHeader.encode_length, Alpha.encode_length, CancelReason.encode_length]

theorem encode_length_pos (message : CancellationOfAllQuotesNotice) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CancellationOfAllQuotesNotice) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OutgoingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [CancelReason.decode_encode, some_bind]
  rfl

end CancellationOfAllQuotesNotice

/-- Execution Notice: 218 bytes -/
structure ExecutionNotice where
  outgoingMessagesHeader : OutgoingMessagesHeader
  group : Alpha 2
  instrument : Alpha 4
  traderId : Alpha 8
  referenceIdOrderIdOrQuoteId : Alpha 8
  verbSide : VerbSide
  quantityTraded : Alpha 8
  tradePrice : Alpha 10
  tradingEngineTimestampOfTheTradeLocalHhmmss : Alpha 6
  clearingData : ClearingData
  ownerData : OwnerData
  specialTradeIndicator : SpecialTradeIndicator
  priceType : PriceType
  tradeType : TradeType
  filler6 : Alpha 6
  tradeNumber : Alpha 8
  tradeMemo : Alpha 50
  originalReferenceId : Alpha 8
  idCodeForTheCounterpartParticipant : Alpha 4
  deriving DecidableEq, Repr

namespace ExecutionNotice

def encode (message : ExecutionNotice) : List UInt8 :=
  OutgoingMessagesHeader.encode message.outgoingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.referenceIdOrderIdOrQuoteId
    ++ (VerbSide.encode message.verbSide
    ++ (Alpha.encode message.quantityTraded
    ++ (Alpha.encode message.tradePrice
    ++ (Alpha.encode message.tradingEngineTimestampOfTheTradeLocalHhmmss
    ++ (ClearingData.encode message.clearingData
    ++ (OwnerData.encode message.ownerData
    ++ (SpecialTradeIndicator.encode message.specialTradeIndicator
    ++ (PriceType.encode message.priceType
    ++ (TradeType.encode message.tradeType
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.tradeNumber
    ++ (Alpha.encode message.tradeMemo
    ++ (Alpha.encode message.originalReferenceId
    ++ (Alpha.encode message.idCodeForTheCounterpartParticipant))))))))))))))))))

def decode (bytes : List UInt8) : Option (ExecutionNotice × List UInt8) := do
  let (outgoingMessagesHeader, bytes) ← OutgoingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (referenceIdOrderIdOrQuoteId, bytes) ← Alpha.decode 8 bytes
  let (verbSide, bytes) ← VerbSide.decode bytes
  let (quantityTraded, bytes) ← Alpha.decode 8 bytes
  let (tradePrice, bytes) ← Alpha.decode 10 bytes
  let (tradingEngineTimestampOfTheTradeLocalHhmmss, bytes) ← Alpha.decode 6 bytes
  let (clearingData, bytes) ← ClearingData.decode bytes
  let (ownerData, bytes) ← OwnerData.decode bytes
  let (specialTradeIndicator, bytes) ← SpecialTradeIndicator.decode bytes
  let (priceType, bytes) ← PriceType.decode bytes
  let (tradeType, bytes) ← TradeType.decode bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  let (tradeMemo, bytes) ← Alpha.decode 50 bytes
  let (originalReferenceId, bytes) ← Alpha.decode 8 bytes
  let (idCodeForTheCounterpartParticipant, bytes) ← Alpha.decode 4 bytes
  pure ({ outgoingMessagesHeader, group, instrument, traderId, referenceIdOrderIdOrQuoteId, verbSide, quantityTraded, tradePrice, tradingEngineTimestampOfTheTradeLocalHhmmss, clearingData, ownerData, specialTradeIndicator, priceType, tradeType, filler6, tradeNumber, tradeMemo, originalReferenceId, idCodeForTheCounterpartParticipant }, bytes)

@[simp] theorem encode_length (message : ExecutionNotice) : (encode message).length = 218 := by
  unfold encode
  simp only [List.length_append, OutgoingMessagesHeader.encode_length, Alpha.encode_length, VerbSide.encode_length, ClearingData.encode_length, OwnerData.encode_length, SpecialTradeIndicator.encode_length, PriceType.encode_length, TradeType.encode_length]

theorem encode_length_pos (message : ExecutionNotice) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExecutionNotice) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OutgoingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, VerbSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ClearingData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OwnerData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SpecialTradeIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PriceType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeType.decode_encode, some_bind]
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

end ExecutionNotice

/-- Execution Cancellation Notice: 218 bytes -/
structure ExecutionCancellationNotice where
  outgoingMessagesHeader : OutgoingMessagesHeader
  group : Alpha 2
  instrument : Alpha 4
  traderId : Alpha 8
  referenceIdOrderIdOrQuoteId : Alpha 8
  verbSide : VerbSide
  quantityTraded : Alpha 8
  tradePrice : Alpha 10
  tradingEngineTimestampOfTheTradeLocalHhmmss : Alpha 6
  clearingData : ClearingData
  ownerData : OwnerData
  specialTradeIndicator : SpecialTradeIndicator
  priceType : PriceType
  tradeType : TradeType
  filler6 : Alpha 6
  tradeNumber : Alpha 8
  tradeMemo : Alpha 50
  originalReferenceId : Alpha 8
  idCodeForTheCounterpartParticipant : Alpha 4
  deriving DecidableEq, Repr

namespace ExecutionCancellationNotice

def encode (message : ExecutionCancellationNotice) : List UInt8 :=
  OutgoingMessagesHeader.encode message.outgoingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.referenceIdOrderIdOrQuoteId
    ++ (VerbSide.encode message.verbSide
    ++ (Alpha.encode message.quantityTraded
    ++ (Alpha.encode message.tradePrice
    ++ (Alpha.encode message.tradingEngineTimestampOfTheTradeLocalHhmmss
    ++ (ClearingData.encode message.clearingData
    ++ (OwnerData.encode message.ownerData
    ++ (SpecialTradeIndicator.encode message.specialTradeIndicator
    ++ (PriceType.encode message.priceType
    ++ (TradeType.encode message.tradeType
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.tradeNumber
    ++ (Alpha.encode message.tradeMemo
    ++ (Alpha.encode message.originalReferenceId
    ++ (Alpha.encode message.idCodeForTheCounterpartParticipant))))))))))))))))))

def decode (bytes : List UInt8) : Option (ExecutionCancellationNotice × List UInt8) := do
  let (outgoingMessagesHeader, bytes) ← OutgoingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (referenceIdOrderIdOrQuoteId, bytes) ← Alpha.decode 8 bytes
  let (verbSide, bytes) ← VerbSide.decode bytes
  let (quantityTraded, bytes) ← Alpha.decode 8 bytes
  let (tradePrice, bytes) ← Alpha.decode 10 bytes
  let (tradingEngineTimestampOfTheTradeLocalHhmmss, bytes) ← Alpha.decode 6 bytes
  let (clearingData, bytes) ← ClearingData.decode bytes
  let (ownerData, bytes) ← OwnerData.decode bytes
  let (specialTradeIndicator, bytes) ← SpecialTradeIndicator.decode bytes
  let (priceType, bytes) ← PriceType.decode bytes
  let (tradeType, bytes) ← TradeType.decode bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  let (tradeMemo, bytes) ← Alpha.decode 50 bytes
  let (originalReferenceId, bytes) ← Alpha.decode 8 bytes
  let (idCodeForTheCounterpartParticipant, bytes) ← Alpha.decode 4 bytes
  pure ({ outgoingMessagesHeader, group, instrument, traderId, referenceIdOrderIdOrQuoteId, verbSide, quantityTraded, tradePrice, tradingEngineTimestampOfTheTradeLocalHhmmss, clearingData, ownerData, specialTradeIndicator, priceType, tradeType, filler6, tradeNumber, tradeMemo, originalReferenceId, idCodeForTheCounterpartParticipant }, bytes)

@[simp] theorem encode_length (message : ExecutionCancellationNotice) : (encode message).length = 218 := by
  unfold encode
  simp only [List.length_append, OutgoingMessagesHeader.encode_length, Alpha.encode_length, VerbSide.encode_length, ClearingData.encode_length, OwnerData.encode_length, SpecialTradeIndicator.encode_length, PriceType.encode_length, TradeType.encode_length]

theorem encode_length_pos (message : ExecutionCancellationNotice) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExecutionCancellationNotice) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OutgoingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, VerbSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ClearingData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OwnerData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SpecialTradeIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PriceType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeType.decode_encode, some_bind]
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

end ExecutionCancellationNotice

/-- Leg Execution Cancellation Notice: 235 bytes -/
structure LegExecutionCancellationNotice where
  outgoingMessagesHeader : OutgoingMessagesHeader
  group : Alpha 2
  instrument : Alpha 4
  traderId : Alpha 8
  referenceIdOrderIdOrQuoteId : Alpha 8
  verbSide : VerbSide
  quantityTraded : Alpha 8
  tradePrice : Alpha 10
  tradingEngineTimestampOfTheTradeLocalHhmmss : Alpha 6
  clearingData : ClearingData
  ownerData : OwnerData
  specialTradeIndicator : SpecialTradeIndicator
  priceType : PriceType
  tradeType : TradeType
  filler6 : Alpha 6
  tradeNumber : Alpha 8
  tradeMemo : Alpha 50
  originalReferenceId : Alpha 8
  idCodeForTheCounterpartParticipant : Alpha 4
  strategyGroup : Alpha 2
  strategyInstrumentId : Alpha 4
  strategyVerbSide : Alpha 1
  strategyTradeNumber : Alpha 8
  legNumber : Alpha 2
  deriving DecidableEq, Repr

namespace LegExecutionCancellationNotice

def encode (message : LegExecutionCancellationNotice) : List UInt8 :=
  OutgoingMessagesHeader.encode message.outgoingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.referenceIdOrderIdOrQuoteId
    ++ (VerbSide.encode message.verbSide
    ++ (Alpha.encode message.quantityTraded
    ++ (Alpha.encode message.tradePrice
    ++ (Alpha.encode message.tradingEngineTimestampOfTheTradeLocalHhmmss
    ++ (ClearingData.encode message.clearingData
    ++ (OwnerData.encode message.ownerData
    ++ (SpecialTradeIndicator.encode message.specialTradeIndicator
    ++ (PriceType.encode message.priceType
    ++ (TradeType.encode message.tradeType
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.tradeNumber
    ++ (Alpha.encode message.tradeMemo
    ++ (Alpha.encode message.originalReferenceId
    ++ (Alpha.encode message.idCodeForTheCounterpartParticipant
    ++ (Alpha.encode message.strategyGroup
    ++ (Alpha.encode message.strategyInstrumentId
    ++ (Alpha.encode message.strategyVerbSide
    ++ (Alpha.encode message.strategyTradeNumber
    ++ (Alpha.encode message.legNumber)))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (LegExecutionCancellationNotice × List UInt8) := do
  let (outgoingMessagesHeader, bytes) ← OutgoingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (referenceIdOrderIdOrQuoteId, bytes) ← Alpha.decode 8 bytes
  let (verbSide, bytes) ← VerbSide.decode bytes
  let (quantityTraded, bytes) ← Alpha.decode 8 bytes
  let (tradePrice, bytes) ← Alpha.decode 10 bytes
  let (tradingEngineTimestampOfTheTradeLocalHhmmss, bytes) ← Alpha.decode 6 bytes
  let (clearingData, bytes) ← ClearingData.decode bytes
  let (ownerData, bytes) ← OwnerData.decode bytes
  let (specialTradeIndicator, bytes) ← SpecialTradeIndicator.decode bytes
  let (priceType, bytes) ← PriceType.decode bytes
  let (tradeType, bytes) ← TradeType.decode bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  let (tradeMemo, bytes) ← Alpha.decode 50 bytes
  let (originalReferenceId, bytes) ← Alpha.decode 8 bytes
  let (idCodeForTheCounterpartParticipant, bytes) ← Alpha.decode 4 bytes
  let (strategyGroup, bytes) ← Alpha.decode 2 bytes
  let (strategyInstrumentId, bytes) ← Alpha.decode 4 bytes
  let (strategyVerbSide, bytes) ← Alpha.decode 1 bytes
  let (strategyTradeNumber, bytes) ← Alpha.decode 8 bytes
  let (legNumber, bytes) ← Alpha.decode 2 bytes
  pure ({ outgoingMessagesHeader, group, instrument, traderId, referenceIdOrderIdOrQuoteId, verbSide, quantityTraded, tradePrice, tradingEngineTimestampOfTheTradeLocalHhmmss, clearingData, ownerData, specialTradeIndicator, priceType, tradeType, filler6, tradeNumber, tradeMemo, originalReferenceId, idCodeForTheCounterpartParticipant, strategyGroup, strategyInstrumentId, strategyVerbSide, strategyTradeNumber, legNumber }, bytes)

@[simp] theorem encode_length (message : LegExecutionCancellationNotice) : (encode message).length = 235 := by
  unfold encode
  simp only [List.length_append, OutgoingMessagesHeader.encode_length, Alpha.encode_length, VerbSide.encode_length, ClearingData.encode_length, OwnerData.encode_length, SpecialTradeIndicator.encode_length, PriceType.encode_length, TradeType.encode_length]

theorem encode_length_pos (message : LegExecutionCancellationNotice) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LegExecutionCancellationNotice) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OutgoingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, VerbSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ClearingData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OwnerData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SpecialTradeIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PriceType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeType.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LegExecutionCancellationNotice

/-- Order Cancellation Notice By Mod Or System: 148 bytes -/
structure OrderCancellationNoticeByModOrSystem where
  outgoingMessagesHeader : OutgoingMessagesHeader
  group : Alpha 2
  instrument : Alpha 4
  traderId : Alpha 8
  orderId : Alpha 8
  status : Status
  verbSide : VerbSide
  quantity : Alpha 8
  assignedPrice : Alpha 10
  clearingData : ClearingData
  ownerData : OwnerData
  originalOrderId : Alpha 8
  filler6 : Alpha 6
  deriving DecidableEq, Repr

namespace OrderCancellationNoticeByModOrSystem

def encode (message : OrderCancellationNoticeByModOrSystem) : List UInt8 :=
  OutgoingMessagesHeader.encode message.outgoingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.orderId
    ++ (Status.encode message.status
    ++ (VerbSide.encode message.verbSide
    ++ (Alpha.encode message.quantity
    ++ (Alpha.encode message.assignedPrice
    ++ (ClearingData.encode message.clearingData
    ++ (OwnerData.encode message.ownerData
    ++ (Alpha.encode message.originalOrderId
    ++ (Alpha.encode message.filler6))))))))))))

def decode (bytes : List UInt8) : Option (OrderCancellationNoticeByModOrSystem × List UInt8) := do
  let (outgoingMessagesHeader, bytes) ← OutgoingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (orderId, bytes) ← Alpha.decode 8 bytes
  let (status, bytes) ← Status.decode bytes
  let (verbSide, bytes) ← VerbSide.decode bytes
  let (quantity, bytes) ← Alpha.decode 8 bytes
  let (assignedPrice, bytes) ← Alpha.decode 10 bytes
  let (clearingData, bytes) ← ClearingData.decode bytes
  let (ownerData, bytes) ← OwnerData.decode bytes
  let (originalOrderId, bytes) ← Alpha.decode 8 bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  pure ({ outgoingMessagesHeader, group, instrument, traderId, orderId, status, verbSide, quantity, assignedPrice, clearingData, ownerData, originalOrderId, filler6 }, bytes)

@[simp] theorem encode_length (message : OrderCancellationNoticeByModOrSystem) : (encode message).length = 148 := by
  unfold encode
  simp only [List.length_append, OutgoingMessagesHeader.encode_length, Alpha.encode_length, Status.encode_length, VerbSide.encode_length, ClearingData.encode_length, OwnerData.encode_length]

theorem encode_length_pos (message : OrderCancellationNoticeByModOrSystem) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancellationNoticeByModOrSystem) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OutgoingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Status.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, VerbSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ClearingData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OwnerData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderCancellationNoticeByModOrSystem

/-- Request For Quote With Side Acknowledgement: 37 bytes -/
structure RequestForQuoteWithSideAcknowledgement where
  outgoingMessagesHeader : OutgoingMessagesHeader
  group : Alpha 2
  instrument : Alpha 4
  quantity : Alpha 8
  marketSide : MarketSide
  deriving DecidableEq, Repr

namespace RequestForQuoteWithSideAcknowledgement

def encode (message : RequestForQuoteWithSideAcknowledgement) : List UInt8 :=
  OutgoingMessagesHeader.encode message.outgoingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.quantity
    ++ (MarketSide.encode message.marketSide))))

def decode (bytes : List UInt8) : Option (RequestForQuoteWithSideAcknowledgement × List UInt8) := do
  let (outgoingMessagesHeader, bytes) ← OutgoingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (quantity, bytes) ← Alpha.decode 8 bytes
  let (marketSide, bytes) ← MarketSide.decode bytes
  pure ({ outgoingMessagesHeader, group, instrument, quantity, marketSide }, bytes)

@[simp] theorem encode_length (message : RequestForQuoteWithSideAcknowledgement) : (encode message).length = 37 := by
  unfold encode
  simp only [List.length_append, OutgoingMessagesHeader.encode_length, Alpha.encode_length, MarketSide.encode_length]

theorem encode_length_pos (message : RequestForQuoteWithSideAcknowledgement) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RequestForQuoteWithSideAcknowledgement) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OutgoingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [MarketSide.decode_encode, some_bind]
  rfl

end RequestForQuoteWithSideAcknowledgement

/-- Any Exchange Message, selected by Message Type -/
inductive ExchangeMessage where
  | connectionAcknowledgement (message : ConnectionAcknowledgement) -- "TK" 0x544B
  | disconnectionInstructionAcknowledgement (message : DisconnectionInstructionAcknowledgement) -- "TM" 0x544D
  | heartbeatQuestion (message : HeartbeatQuestion) -- "TH" 0x5448
  | outOfSequence (message : OutOfSequence) -- "TO" 0x544F
  | technicalErrorNotice (message : TechnicalErrorNotice) -- "TE" 0x5445
  | disconnectionAcknowledgement (message : DisconnectionAcknowledgement) -- "TL" 0x544C
  | endOfTransmission (message : EndOfTransmission) -- "TT" 0x5454
  | orderReply (message : OrderReply) -- "AE" 0x4145
  | errorNotice (message : ErrorNotice) -- "ER" 0x4552
  | bulkQuoteDataAcknowledgement (message : BulkQuoteDataAcknowledgement) -- "KD" 0x4B44
  | orderAcknowledgement (message : OrderAcknowledgement) -- "KE" 0x4B45
  | globalCancellationConfirmation (message : GlobalCancellationConfirmation) -- "KG" 0x4B47
  | orderModificationAcknowledgement (message : OrderModificationAcknowledgement) -- "KM" 0x4B4D
  | newStrategyInstrumentAcknowledgement (message : NewStrategyInstrumentAcknowledgement) -- "KN" 0x4B4E
  | standardAcknowledgement (message : StandardAcknowledgement) -- "KO" 0x4B4F
  | orderCancellationAcknowledgement (message : OrderCancellationAcknowledgement) -- "KZ" 0x4B5A
  | bulkQuoteAcknowledgement (message : BulkQuoteAcknowledgement) -- "LA" 0x4C41
  | bulkCommandAcknowledgement (message : BulkCommandAcknowledgement) -- "LB" 0x4C42
  | riskLimitsUsage (message : RiskLimitsUsage) -- "MN" 0x4D4E
  | excludedInstrumentNotice (message : ExcludedInstrumentNotice) -- "NE" 0x4E45
  | groupStateChange (message : GroupStateChange) -- "NG" 0x4E47
  | instrumentStateChange (message : InstrumentStateChange) -- "NI" 0x4E49
  | legExecutionNotice (message : LegExecutionNotice) -- "NL" 0x4E4C
  | oversteppedOrderOrQuoteNotice (message : OversteppedOrderOrQuoteNotice) -- "NO" 0x4E4F
  | cancellationOfAllQuotesNotice (message : CancellationOfAllQuotesNotice) -- "NP" 0x4E50
  | executionNotice (message : ExecutionNotice) -- "NT" 0x4E54
  | executionCancellationNotice (message : ExecutionCancellationNotice) -- "NX" 0x4E58
  | legExecutionCancellationNotice (message : LegExecutionCancellationNotice) -- "NY" 0x4E59
  | orderCancellationNoticeByModOrSystem (message : OrderCancellationNoticeByModOrSystem) -- "NZ" 0x4E5A
  | requestForQuoteWithSideAcknowledgement (message : RequestForQuoteWithSideAcknowledgement) -- "QW" 0x5157
  deriving DecidableEq, Repr

namespace ExchangeMessage

/-- The Message Type each message is sent under -/
def tag : ExchangeMessage → BitVec 16
  | .connectionAcknowledgement _ => 21579
  | .disconnectionInstructionAcknowledgement _ => 21581
  | .heartbeatQuestion _ => 21576
  | .outOfSequence _ => 21583
  | .technicalErrorNotice _ => 21573
  | .disconnectionAcknowledgement _ => 21580
  | .endOfTransmission _ => 21588
  | .orderReply _ => 16709
  | .errorNotice _ => 17746
  | .bulkQuoteDataAcknowledgement _ => 19268
  | .orderAcknowledgement _ => 19269
  | .globalCancellationConfirmation _ => 19271
  | .orderModificationAcknowledgement _ => 19277
  | .newStrategyInstrumentAcknowledgement _ => 19278
  | .standardAcknowledgement _ => 19279
  | .orderCancellationAcknowledgement _ => 19290
  | .bulkQuoteAcknowledgement _ => 19521
  | .bulkCommandAcknowledgement _ => 19522
  | .riskLimitsUsage _ => 19790
  | .excludedInstrumentNotice _ => 20037
  | .groupStateChange _ => 20039
  | .instrumentStateChange _ => 20041
  | .legExecutionNotice _ => 20044
  | .oversteppedOrderOrQuoteNotice _ => 20047
  | .cancellationOfAllQuotesNotice _ => 20048
  | .executionNotice _ => 20052
  | .executionCancellationNotice _ => 20056
  | .legExecutionCancellationNotice _ => 20057
  | .orderCancellationNoticeByModOrSystem _ => 20058
  | .requestForQuoteWithSideAcknowledgement _ => 20823

def encode : ExchangeMessage → List UInt8
  | .connectionAcknowledgement message => ConnectionAcknowledgement.encode message
  | .disconnectionInstructionAcknowledgement message => DisconnectionInstructionAcknowledgement.encode message
  | .heartbeatQuestion message => HeartbeatQuestion.encode message
  | .outOfSequence message => OutOfSequence.encode message
  | .technicalErrorNotice message => TechnicalErrorNotice.encode message
  | .disconnectionAcknowledgement message => DisconnectionAcknowledgement.encode message
  | .endOfTransmission message => EndOfTransmission.encode message
  | .orderReply message => OrderReply.encode message
  | .errorNotice message => ErrorNotice.encode message
  | .bulkQuoteDataAcknowledgement message => BulkQuoteDataAcknowledgement.encode message
  | .orderAcknowledgement message => OrderAcknowledgement.encode message
  | .globalCancellationConfirmation message => GlobalCancellationConfirmation.encode message
  | .orderModificationAcknowledgement message => OrderModificationAcknowledgement.encode message
  | .newStrategyInstrumentAcknowledgement message => NewStrategyInstrumentAcknowledgement.encode message
  | .standardAcknowledgement message => StandardAcknowledgement.encode message
  | .orderCancellationAcknowledgement message => OrderCancellationAcknowledgement.encode message
  | .bulkQuoteAcknowledgement message => BulkQuoteAcknowledgement.encode message
  | .bulkCommandAcknowledgement message => BulkCommandAcknowledgement.encode message
  | .riskLimitsUsage message => RiskLimitsUsage.encode message
  | .excludedInstrumentNotice message => ExcludedInstrumentNotice.encode message
  | .groupStateChange message => GroupStateChange.encode message
  | .instrumentStateChange message => InstrumentStateChange.encode message
  | .legExecutionNotice message => LegExecutionNotice.encode message
  | .oversteppedOrderOrQuoteNotice message => OversteppedOrderOrQuoteNotice.encode message
  | .cancellationOfAllQuotesNotice message => CancellationOfAllQuotesNotice.encode message
  | .executionNotice message => ExecutionNotice.encode message
  | .executionCancellationNotice message => ExecutionCancellationNotice.encode message
  | .legExecutionCancellationNotice message => LegExecutionCancellationNotice.encode message
  | .orderCancellationNoticeByModOrSystem message => OrderCancellationNoticeByModOrSystem.encode message
  | .requestForQuoteWithSideAcknowledgement message => RequestForQuoteWithSideAcknowledgement.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ExchangeMessage) : (encode message).length ≤ 279998 := by
  cases message with
  | connectionAcknowledgement inner =>
    simp only [encode, ConnectionAcknowledgement.encode_length]
    omega
  | disconnectionInstructionAcknowledgement inner =>
    simp only [encode, DisconnectionInstructionAcknowledgement.encode_length]
    omega
  | heartbeatQuestion inner =>
    simp only [encode, HeartbeatQuestion.encode_length]
    omega
  | outOfSequence inner =>
    simp only [encode, OutOfSequence.encode_length]
    omega
  | technicalErrorNotice inner =>
    simp only [encode, TechnicalErrorNotice.encode_length]
    omega
  | disconnectionAcknowledgement inner =>
    simp only [encode, DisconnectionAcknowledgement.encode_length]
    omega
  | endOfTransmission inner =>
    simp only [encode, EndOfTransmission.encode_length]
    omega
  | orderReply inner =>
    simp only [encode, OrderReply.encode_length]
    omega
  | errorNotice inner =>
    simp only [encode, ErrorNotice.encode_length]
    omega
  | bulkQuoteDataAcknowledgement inner =>
    simp only [encode, BulkQuoteDataAcknowledgement.encode_length]
    omega
  | orderAcknowledgement inner =>
    simp only [encode, OrderAcknowledgement.encode_length]
    omega
  | globalCancellationConfirmation inner =>
    simp only [encode, GlobalCancellationConfirmation.encode_length]
    omega
  | orderModificationAcknowledgement inner =>
    simp only [encode, OrderModificationAcknowledgement.encode_length]
    omega
  | newStrategyInstrumentAcknowledgement inner =>
    have bound_inner := NewStrategyInstrumentAcknowledgement.encode_length_le inner
    simp only [encode]
    omega
  | standardAcknowledgement inner =>
    simp only [encode, StandardAcknowledgement.encode_length]
    omega
  | orderCancellationAcknowledgement inner =>
    simp only [encode, OrderCancellationAcknowledgement.encode_length]
    omega
  | bulkQuoteAcknowledgement inner =>
    have bound_inner := BulkQuoteAcknowledgement.encode_length_le inner
    simp only [encode]
    omega
  | bulkCommandAcknowledgement inner =>
    have bound_inner := BulkCommandAcknowledgement.encode_length_le inner
    simp only [encode]
    omega
  | riskLimitsUsage inner =>
    have bound_inner := RiskLimitsUsage.encode_length_le inner
    simp only [encode]
    omega
  | excludedInstrumentNotice inner =>
    have bound_inner := ExcludedInstrumentNotice.encode_length_le inner
    simp only [encode]
    omega
  | groupStateChange inner =>
    simp only [encode, GroupStateChange.encode_length]
    omega
  | instrumentStateChange inner =>
    simp only [encode, InstrumentStateChange.encode_length]
    omega
  | legExecutionNotice inner =>
    simp only [encode, LegExecutionNotice.encode_length]
    omega
  | oversteppedOrderOrQuoteNotice inner =>
    simp only [encode, OversteppedOrderOrQuoteNotice.encode_length]
    omega
  | cancellationOfAllQuotesNotice inner =>
    simp only [encode, CancellationOfAllQuotesNotice.encode_length]
    omega
  | executionNotice inner =>
    simp only [encode, ExecutionNotice.encode_length]
    omega
  | executionCancellationNotice inner =>
    simp only [encode, ExecutionCancellationNotice.encode_length]
    omega
  | legExecutionCancellationNotice inner =>
    simp only [encode, LegExecutionCancellationNotice.encode_length]
    omega
  | orderCancellationNoticeByModOrSystem inner =>
    simp only [encode, OrderCancellationNoticeByModOrSystem.encode_length]
    omega
  | requestForQuoteWithSideAcknowledgement inner =>
    simp only [encode, RequestForQuoteWithSideAcknowledgement.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (ExchangeMessage × List UInt8) :=
  if tag = 21579 then (ConnectionAcknowledgement.decode bytes).map fun (message, rest) => (.connectionAcknowledgement message, rest)
  else if tag = 21581 then (DisconnectionInstructionAcknowledgement.decode bytes).map fun (message, rest) => (.disconnectionInstructionAcknowledgement message, rest)
  else if tag = 21576 then (HeartbeatQuestion.decode bytes).map fun (message, rest) => (.heartbeatQuestion message, rest)
  else if tag = 21583 then (OutOfSequence.decode bytes).map fun (message, rest) => (.outOfSequence message, rest)
  else if tag = 21573 then (TechnicalErrorNotice.decode bytes).map fun (message, rest) => (.technicalErrorNotice message, rest)
  else if tag = 21580 then (DisconnectionAcknowledgement.decode bytes).map fun (message, rest) => (.disconnectionAcknowledgement message, rest)
  else if tag = 21588 then (EndOfTransmission.decode bytes).map fun (message, rest) => (.endOfTransmission message, rest)
  else if tag = 16709 then (OrderReply.decode bytes).map fun (message, rest) => (.orderReply message, rest)
  else if tag = 17746 then (ErrorNotice.decode bytes).map fun (message, rest) => (.errorNotice message, rest)
  else if tag = 19268 then (BulkQuoteDataAcknowledgement.decode bytes).map fun (message, rest) => (.bulkQuoteDataAcknowledgement message, rest)
  else if tag = 19269 then (OrderAcknowledgement.decode bytes).map fun (message, rest) => (.orderAcknowledgement message, rest)
  else if tag = 19271 then (GlobalCancellationConfirmation.decode bytes).map fun (message, rest) => (.globalCancellationConfirmation message, rest)
  else if tag = 19277 then (OrderModificationAcknowledgement.decode bytes).map fun (message, rest) => (.orderModificationAcknowledgement message, rest)
  else if tag = 19278 then (NewStrategyInstrumentAcknowledgement.decode bytes).map fun (message, rest) => (.newStrategyInstrumentAcknowledgement message, rest)
  else if tag = 19279 then (StandardAcknowledgement.decode bytes).map fun (message, rest) => (.standardAcknowledgement message, rest)
  else if tag = 19290 then (OrderCancellationAcknowledgement.decode bytes).map fun (message, rest) => (.orderCancellationAcknowledgement message, rest)
  else if tag = 19521 then (BulkQuoteAcknowledgement.decode bytes).map fun (message, rest) => (.bulkQuoteAcknowledgement message, rest)
  else if tag = 19522 then (BulkCommandAcknowledgement.decode bytes).map fun (message, rest) => (.bulkCommandAcknowledgement message, rest)
  else if tag = 19790 then (RiskLimitsUsage.decode bytes).map fun (message, rest) => (.riskLimitsUsage message, rest)
  else if tag = 20037 then (ExcludedInstrumentNotice.decode bytes).map fun (message, rest) => (.excludedInstrumentNotice message, rest)
  else if tag = 20039 then (GroupStateChange.decode bytes).map fun (message, rest) => (.groupStateChange message, rest)
  else if tag = 20041 then (InstrumentStateChange.decode bytes).map fun (message, rest) => (.instrumentStateChange message, rest)
  else if tag = 20044 then (LegExecutionNotice.decode bytes).map fun (message, rest) => (.legExecutionNotice message, rest)
  else if tag = 20047 then (OversteppedOrderOrQuoteNotice.decode bytes).map fun (message, rest) => (.oversteppedOrderOrQuoteNotice message, rest)
  else if tag = 20048 then (CancellationOfAllQuotesNotice.decode bytes).map fun (message, rest) => (.cancellationOfAllQuotesNotice message, rest)
  else if tag = 20052 then (ExecutionNotice.decode bytes).map fun (message, rest) => (.executionNotice message, rest)
  else if tag = 20056 then (ExecutionCancellationNotice.decode bytes).map fun (message, rest) => (.executionCancellationNotice message, rest)
  else if tag = 20057 then (LegExecutionCancellationNotice.decode bytes).map fun (message, rest) => (.legExecutionCancellationNotice message, rest)
  else if tag = 20058 then (OrderCancellationNoticeByModOrSystem.decode bytes).map fun (message, rest) => (.orderCancellationNoticeByModOrSystem message, rest)
  else if tag = 20823 then (RequestForQuoteWithSideAcknowledgement.decode bytes).map fun (message, rest) => (.requestForQuoteWithSideAcknowledgement message, rest)
  else none

@[simp] theorem decode_encode (message : ExchangeMessage) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ExchangeMessage

/-- Exchange Packet -/
structure ExchangePacket where
  messageLength : BitVec 32
  exchangeMessage : ExchangeMessage
  endOfText : BitVec 8
  alignmentPadding : Capped 3
  deriving DecidableEq, Repr

namespace ExchangePacket

def encode (message : ExchangePacket) : List UInt8 :=
  encodeUIntLE 4 message.messageLength
    ++ (encodeUInt 2 (ExchangeMessage.tag message.exchangeMessage)
    ++ (ExchangeMessage.encode message.exchangeMessage
    ++ (encodeUInt 1 message.endOfText
    ++ (message.alignmentPadding.val))))

def decode (bytes : List UInt8) : Option ExchangePacket := do
  let (messageLength, bytes) ← decodeUIntLE 4 bytes
  let (messageType, bytes) ← decodeUInt 2 bytes
  let (exchangeMessage, bytes) ← ExchangeMessage.decode messageType bytes
  let (endOfText, bytes) ← decodeUInt 1 bytes
  let alignmentPadding_ := bytes
  if fits_alignmentPadding : alignmentPadding_.length ≤ 3 then
    pure { messageLength, exchangeMessage, endOfText, alignmentPadding := ⟨alignmentPadding_, fits_alignmentPadding⟩ }
  else none

theorem encode_length_pos (message : ExchangePacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ExchangePacket) : (encode message).length ≤ 280008 := by
  have bound_alignmentPadding := message.alignmentPadding.length_le
  unfold encode
  cases message.exchangeMessage with
  | connectionAcknowledgement inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, ConnectionAcknowledgement.encode_length]
    omega
  | disconnectionInstructionAcknowledgement inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, DisconnectionInstructionAcknowledgement.encode_length]
    omega
  | heartbeatQuestion inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, HeartbeatQuestion.encode_length]
    omega
  | outOfSequence inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, OutOfSequence.encode_length]
    omega
  | technicalErrorNotice inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, TechnicalErrorNotice.encode_length]
    omega
  | disconnectionAcknowledgement inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, DisconnectionAcknowledgement.encode_length]
    omega
  | endOfTransmission inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, EndOfTransmission.encode_length]
    omega
  | orderReply inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, OrderReply.encode_length]
    omega
  | errorNotice inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, ErrorNotice.encode_length]
    omega
  | bulkQuoteDataAcknowledgement inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, BulkQuoteDataAcknowledgement.encode_length]
    omega
  | orderAcknowledgement inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, OrderAcknowledgement.encode_length]
    omega
  | globalCancellationConfirmation inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, GlobalCancellationConfirmation.encode_length]
    omega
  | orderModificationAcknowledgement inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, OrderModificationAcknowledgement.encode_length]
    omega
  | newStrategyInstrumentAcknowledgement inner =>
    have bound_inner := NewStrategyInstrumentAcknowledgement.encode_length_le inner
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
    omega
  | standardAcknowledgement inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, StandardAcknowledgement.encode_length]
    omega
  | orderCancellationAcknowledgement inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, OrderCancellationAcknowledgement.encode_length]
    omega
  | bulkQuoteAcknowledgement inner =>
    have bound_inner := BulkQuoteAcknowledgement.encode_length_le inner
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
    omega
  | bulkCommandAcknowledgement inner =>
    have bound_inner := BulkCommandAcknowledgement.encode_length_le inner
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
    omega
  | riskLimitsUsage inner =>
    have bound_inner := RiskLimitsUsage.encode_length_le inner
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
    omega
  | excludedInstrumentNotice inner =>
    have bound_inner := ExcludedInstrumentNotice.encode_length_le inner
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
    omega
  | groupStateChange inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, GroupStateChange.encode_length]
    omega
  | instrumentStateChange inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, InstrumentStateChange.encode_length]
    omega
  | legExecutionNotice inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, LegExecutionNotice.encode_length]
    omega
  | oversteppedOrderOrQuoteNotice inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, OversteppedOrderOrQuoteNotice.encode_length]
    omega
  | cancellationOfAllQuotesNotice inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, CancellationOfAllQuotesNotice.encode_length]
    omega
  | executionNotice inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, ExecutionNotice.encode_length]
    omega
  | executionCancellationNotice inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, ExecutionCancellationNotice.encode_length]
    omega
  | legExecutionCancellationNotice inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, LegExecutionCancellationNotice.encode_length]
    omega
  | orderCancellationNoticeByModOrSystem inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, OrderCancellationNoticeByModOrSystem.encode_length]
    omega
  | requestForQuoteWithSideAcknowledgement inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, RequestForQuoteWithSideAcknowledgement.encode_length]
    omega

theorem decode_encode (message : ExchangePacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ExchangeMessage.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [dite_eq_left message.alignmentPadding.length_le]
  rfl

end ExchangePacket

end Omi.TmxMxSolaorderentrySailV121Exchange
