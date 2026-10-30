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

namespace Omi.TmxMxSolaorderentrySailV121Firm

/-- Disconnection Instruction Note Cancel Quotes Only Q Quotes Only: one byte code -/
def DisconnectionInstructionNoteCancelQuotesOnlyQQuotesOnly.codes : List UInt8 :=
  [0x41, 0x51, 0x4F, 0x53, 0x4D]

inductive DisconnectionInstructionNoteCancelQuotesOnlyQQuotesOnly where
  | all -- All
  | quotesOnly -- Quotes Only
  | ordersOnly -- Orders Only
  | stopOrdersOnly -- Stop Orders Only
  | marketOrdersOnly -- Market Orders Only
  | unlisted (byte : { byte : UInt8 // byte ∉ DisconnectionInstructionNoteCancelQuotesOnlyQQuotesOnly.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DisconnectionInstructionNoteCancelQuotesOnlyQQuotesOnly

def toByte : DisconnectionInstructionNoteCancelQuotesOnlyQQuotesOnly → UInt8
  | .all => 0x41
  | .quotesOnly => 0x51
  | .ordersOnly => 0x4F
  | .stopOrdersOnly => 0x53
  | .marketOrdersOnly => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DisconnectionInstructionNoteCancelQuotesOnlyQQuotesOnly :=
  if byte = 0x41 then .all
  else if byte = 0x51 then .quotesOnly
  else if byte = 0x4F then .ordersOnly
  else if byte = 0x53 then .stopOrdersOnly
  else .marketOrdersOnly

def ofByte (byte : UInt8) : DisconnectionInstructionNoteCancelQuotesOnlyQQuotesOnly :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DisconnectionInstructionNoteCancelQuotesOnlyQQuotesOnly) : ofByte value.toByte = value := by
  cases value with
  | all => decide
  | quotesOnly => decide
  | ordersOnly => decide
  | stopOrdersOnly => decide
  | marketOrdersOnly => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DisconnectionInstructionNoteCancelQuotesOnlyQQuotesOnly) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DisconnectionInstructionNoteCancelQuotesOnlyQQuotesOnly × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DisconnectionInstructionNoteCancelQuotesOnlyQQuotesOnly) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : DisconnectionInstructionNoteCancelQuotesOnlyQQuotesOnly) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : DisconnectionInstructionNoteCancelQuotesOnlyQQuotesOnly) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DisconnectionInstructionNoteCancelQuotesOnlyQQuotesOnly

/-- Active Y On N Off: one byte code -/
def ActiveYOnNOff.codes : List UInt8 :=
  [0x59, 0x4E]

inductive ActiveYOnNOff where
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ ActiveYOnNOff.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ActiveYOnNOff

def toByte : ActiveYOnNOff → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ActiveYOnNOff :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : ActiveYOnNOff :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ActiveYOnNOff) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ActiveYOnNOff) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ActiveYOnNOff × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ActiveYOnNOff) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ActiveYOnNOff) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ActiveYOnNOff) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ActiveYOnNOff

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

/-- Firm Level Risk Option: one byte code -/
def FirmLevelRiskOption.codes : List UInt8 :=
  [0x20, 0x54, 0x4E, 0x50]

inductive FirmLevelRiskOption where
  | nettingIsDisabled -- Netting Is Disabled
  | cancelPostTraderTeamLevelNetting -- Cancel Post Trader Team Level Netting
  | nettingIsEnabled -- Netting Is Enabled
  | cancelPostFirmLevelNetting -- Cancel Post Firm Level Netting
  | unlisted (byte : { byte : UInt8 // byte ∉ FirmLevelRiskOption.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace FirmLevelRiskOption

def toByte : FirmLevelRiskOption → UInt8
  | .nettingIsDisabled => 0x20
  | .cancelPostTraderTeamLevelNetting => 0x54
  | .nettingIsEnabled => 0x4E
  | .cancelPostFirmLevelNetting => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : FirmLevelRiskOption :=
  if byte = 0x20 then .nettingIsDisabled
  else if byte = 0x54 then .cancelPostTraderTeamLevelNetting
  else if byte = 0x4E then .nettingIsEnabled
  else .cancelPostFirmLevelNetting

def ofByte (byte : UInt8) : FirmLevelRiskOption :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : FirmLevelRiskOption) : ofByte value.toByte = value := by
  cases value with
  | nettingIsDisabled => decide
  | cancelPostTraderTeamLevelNetting => decide
  | nettingIsEnabled => decide
  | cancelPostFirmLevelNetting => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : FirmLevelRiskOption) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (FirmLevelRiskOption × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : FirmLevelRiskOption) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : FirmLevelRiskOption) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : FirmLevelRiskOption) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end FirmLevelRiskOption

/-- Team Level Risk Option: one byte code -/
def TeamLevelRiskOption.codes : List UInt8 :=
  [0x20, 0x54, 0x4E, 0x50]

inductive TeamLevelRiskOption where
  | nettingIsDisabled -- Netting Is Disabled
  | cancelPostTraderTeamLevelNetting -- Cancel Post Trader Team Level Netting
  | nettingIsEnabled -- Netting Is Enabled
  | cancelPostFirmLevelNetting -- Cancel Post Firm Level Netting
  | unlisted (byte : { byte : UInt8 // byte ∉ TeamLevelRiskOption.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TeamLevelRiskOption

def toByte : TeamLevelRiskOption → UInt8
  | .nettingIsDisabled => 0x20
  | .cancelPostTraderTeamLevelNetting => 0x54
  | .nettingIsEnabled => 0x4E
  | .cancelPostFirmLevelNetting => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TeamLevelRiskOption :=
  if byte = 0x20 then .nettingIsDisabled
  else if byte = 0x54 then .cancelPostTraderTeamLevelNetting
  else if byte = 0x4E then .nettingIsEnabled
  else .cancelPostFirmLevelNetting

def ofByte (byte : UInt8) : TeamLevelRiskOption :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TeamLevelRiskOption) : ofByte value.toByte = value := by
  cases value with
  | nettingIsDisabled => decide
  | cancelPostTraderTeamLevelNetting => decide
  | nettingIsEnabled => decide
  | cancelPostFirmLevelNetting => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TeamLevelRiskOption) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TeamLevelRiskOption × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TeamLevelRiskOption) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TeamLevelRiskOption) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TeamLevelRiskOption) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TeamLevelRiskOption

/-- Type Of Cancellation Q Quotes Only: one byte code -/
def TypeOfCancellationQQuotesOnly.codes : List UInt8 :=
  [0x41, 0x51, 0x4F, 0x53, 0x4D]

inductive TypeOfCancellationQQuotesOnly where
  | all -- All
  | quotesOnly -- Quotes Only
  | ordersOnly -- Orders Only
  | stopOrdersOnly -- Stop Orders Only
  | marketOrdersOnly -- Market Orders Only
  | unlisted (byte : { byte : UInt8 // byte ∉ TypeOfCancellationQQuotesOnly.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TypeOfCancellationQQuotesOnly

def toByte : TypeOfCancellationQQuotesOnly → UInt8
  | .all => 0x41
  | .quotesOnly => 0x51
  | .ordersOnly => 0x4F
  | .stopOrdersOnly => 0x53
  | .marketOrdersOnly => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TypeOfCancellationQQuotesOnly :=
  if byte = 0x41 then .all
  else if byte = 0x51 then .quotesOnly
  else if byte = 0x4F then .ordersOnly
  else if byte = 0x53 then .stopOrdersOnly
  else .marketOrdersOnly

def ofByte (byte : UInt8) : TypeOfCancellationQQuotesOnly :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TypeOfCancellationQQuotesOnly) : ofByte value.toByte = value := by
  cases value with
  | all => decide
  | quotesOnly => decide
  | ordersOnly => decide
  | stopOrdersOnly => decide
  | marketOrdersOnly => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TypeOfCancellationQQuotesOnly) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TypeOfCancellationQQuotesOnly × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TypeOfCancellationQQuotesOnly) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TypeOfCancellationQQuotesOnly) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TypeOfCancellationQQuotesOnly) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TypeOfCancellationQQuotesOnly

/-- Type Of Cancellation: one byte code -/
def TypeOfCancellation.codes : List UInt8 :=
  [0x41, 0x51, 0x4F, 0x53, 0x4D]

inductive TypeOfCancellation where
  | all -- All
  | quotesOnly -- Quotes Only
  | ordersOnly -- Orders Only
  | stopOrdersOnly -- Stop Orders Only
  | marketOrdersOnly -- Market Orders Only
  | unlisted (byte : { byte : UInt8 // byte ∉ TypeOfCancellation.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TypeOfCancellation

def toByte : TypeOfCancellation → UInt8
  | .all => 0x41
  | .quotesOnly => 0x51
  | .ordersOnly => 0x4F
  | .stopOrdersOnly => 0x53
  | .marketOrdersOnly => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TypeOfCancellation :=
  if byte = 0x41 then .all
  else if byte = 0x51 then .quotesOnly
  else if byte = 0x4F then .ordersOnly
  else if byte = 0x53 then .stopOrdersOnly
  else .marketOrdersOnly

def ofByte (byte : UInt8) : TypeOfCancellation :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TypeOfCancellation) : ofByte value.toByte = value := by
  cases value with
  | all => decide
  | quotesOnly => decide
  | ordersOnly => decide
  | stopOrdersOnly => decide
  | marketOrdersOnly => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TypeOfCancellation) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TypeOfCancellation × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TypeOfCancellation) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TypeOfCancellation) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TypeOfCancellation) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TypeOfCancellation

/-- Reset All Groups: one byte code -/
def ResetAllGroups.codes : List UInt8 :=
  [0x59, 0x4E]

inductive ResetAllGroups where
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ ResetAllGroups.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ResetAllGroups

def toByte : ResetAllGroups → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ResetAllGroups :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : ResetAllGroups :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ResetAllGroups) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ResetAllGroups) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ResetAllGroups × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ResetAllGroups) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ResetAllGroups) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ResetAllGroups) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ResetAllGroups

/-- Net Exposure Action: one byte code -/
def NetExposureAction.codes : List UInt8 :=
  [0x3F, 0x45, 0x4E, 0x57]

inductive NetExposureAction where
  | notSet -- Not Set
  | enforceLimit -- Enforce Limit
  | none_ -- None
  | warning -- Warning
  | unlisted (byte : { byte : UInt8 // byte ∉ NetExposureAction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace NetExposureAction

def toByte : NetExposureAction → UInt8
  | .notSet => 0x3F
  | .enforceLimit => 0x45
  | .none_ => 0x4E
  | .warning => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : NetExposureAction :=
  if byte = 0x3F then .notSet
  else if byte = 0x45 then .enforceLimit
  else if byte = 0x4E then .none_
  else .warning

def ofByte (byte : UInt8) : NetExposureAction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : NetExposureAction) : ofByte value.toByte = value := by
  cases value with
  | notSet => decide
  | enforceLimit => decide
  | none_ => decide
  | warning => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : NetExposureAction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (NetExposureAction × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : NetExposureAction) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : NetExposureAction) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : NetExposureAction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end NetExposureAction

/-- Long Exposure Action: one byte code -/
def LongExposureAction.codes : List UInt8 :=
  [0x3F, 0x45, 0x4E, 0x57]

inductive LongExposureAction where
  | notSet -- Not Set
  | enforceLimit -- Enforce Limit
  | none_ -- None
  | warning -- Warning
  | unlisted (byte : { byte : UInt8 // byte ∉ LongExposureAction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LongExposureAction

def toByte : LongExposureAction → UInt8
  | .notSet => 0x3F
  | .enforceLimit => 0x45
  | .none_ => 0x4E
  | .warning => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LongExposureAction :=
  if byte = 0x3F then .notSet
  else if byte = 0x45 then .enforceLimit
  else if byte = 0x4E then .none_
  else .warning

def ofByte (byte : UInt8) : LongExposureAction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LongExposureAction) : ofByte value.toByte = value := by
  cases value with
  | notSet => decide
  | enforceLimit => decide
  | none_ => decide
  | warning => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LongExposureAction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LongExposureAction × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LongExposureAction) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : LongExposureAction) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : LongExposureAction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LongExposureAction

/-- Short Exposure Action: one byte code -/
def ShortExposureAction.codes : List UInt8 :=
  [0x3F, 0x45, 0x4E, 0x57]

inductive ShortExposureAction where
  | notSet -- Not Set
  | enforceLimit -- Enforce Limit
  | none_ -- None
  | warning -- Warning
  | unlisted (byte : { byte : UInt8 // byte ∉ ShortExposureAction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ShortExposureAction

def toByte : ShortExposureAction → UInt8
  | .notSet => 0x3F
  | .enforceLimit => 0x45
  | .none_ => 0x4E
  | .warning => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ShortExposureAction :=
  if byte = 0x3F then .notSet
  else if byte = 0x45 then .enforceLimit
  else if byte = 0x4E then .none_
  else .warning

def ofByte (byte : UInt8) : ShortExposureAction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ShortExposureAction) : ofByte value.toByte = value := by
  cases value with
  | notSet => decide
  | enforceLimit => decide
  | none_ => decide
  | warning => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ShortExposureAction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ShortExposureAction × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ShortExposureAction) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ShortExposureAction) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ShortExposureAction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ShortExposureAction

/-- Net Position Action: one byte code -/
def NetPositionAction.codes : List UInt8 :=
  [0x3F, 0x45, 0x4E, 0x57]

inductive NetPositionAction where
  | notSet -- Not Set
  | enforceLimit -- Enforce Limit
  | none_ -- None
  | warning -- Warning
  | unlisted (byte : { byte : UInt8 // byte ∉ NetPositionAction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace NetPositionAction

def toByte : NetPositionAction → UInt8
  | .notSet => 0x3F
  | .enforceLimit => 0x45
  | .none_ => 0x4E
  | .warning => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : NetPositionAction :=
  if byte = 0x3F then .notSet
  else if byte = 0x45 then .enforceLimit
  else if byte = 0x4E then .none_
  else .warning

def ofByte (byte : UInt8) : NetPositionAction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : NetPositionAction) : ofByte value.toByte = value := by
  cases value with
  | notSet => decide
  | enforceLimit => decide
  | none_ => decide
  | warning => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : NetPositionAction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (NetPositionAction × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : NetPositionAction) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : NetPositionAction) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : NetPositionAction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end NetPositionAction

/-- Long Position Action: one byte code -/
def LongPositionAction.codes : List UInt8 :=
  [0x3F, 0x45, 0x4E, 0x57]

inductive LongPositionAction where
  | notSet -- Not Set
  | enforceLimit -- Enforce Limit
  | none_ -- None
  | warning -- Warning
  | unlisted (byte : { byte : UInt8 // byte ∉ LongPositionAction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LongPositionAction

def toByte : LongPositionAction → UInt8
  | .notSet => 0x3F
  | .enforceLimit => 0x45
  | .none_ => 0x4E
  | .warning => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LongPositionAction :=
  if byte = 0x3F then .notSet
  else if byte = 0x45 then .enforceLimit
  else if byte = 0x4E then .none_
  else .warning

def ofByte (byte : UInt8) : LongPositionAction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LongPositionAction) : ofByte value.toByte = value := by
  cases value with
  | notSet => decide
  | enforceLimit => decide
  | none_ => decide
  | warning => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LongPositionAction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LongPositionAction × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LongPositionAction) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : LongPositionAction) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : LongPositionAction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LongPositionAction

/-- Short Position Action: one byte code -/
def ShortPositionAction.codes : List UInt8 :=
  [0x3F, 0x45, 0x4E, 0x57]

inductive ShortPositionAction where
  | notSet -- Not Set
  | enforceLimit -- Enforce Limit
  | none_ -- None
  | warning -- Warning
  | unlisted (byte : { byte : UInt8 // byte ∉ ShortPositionAction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ShortPositionAction

def toByte : ShortPositionAction → UInt8
  | .notSet => 0x3F
  | .enforceLimit => 0x45
  | .none_ => 0x4E
  | .warning => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ShortPositionAction :=
  if byte = 0x3F then .notSet
  else if byte = 0x45 then .enforceLimit
  else if byte = 0x4E then .none_
  else .warning

def ofByte (byte : UInt8) : ShortPositionAction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ShortPositionAction) : ofByte value.toByte = value := by
  cases value with
  | notSet => decide
  | enforceLimit => decide
  | none_ => decide
  | warning => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ShortPositionAction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ShortPositionAction × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ShortPositionAction) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ShortPositionAction) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ShortPositionAction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ShortPositionAction

/-- Global Net Exposure Action: one byte code -/
def GlobalNetExposureAction.codes : List UInt8 :=
  [0x3F, 0x45, 0x4E, 0x57]

inductive GlobalNetExposureAction where
  | notSet -- Not Set
  | enforceLimit -- Enforce Limit
  | none_ -- None
  | warning -- Warning
  | unlisted (byte : { byte : UInt8 // byte ∉ GlobalNetExposureAction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace GlobalNetExposureAction

def toByte : GlobalNetExposureAction → UInt8
  | .notSet => 0x3F
  | .enforceLimit => 0x45
  | .none_ => 0x4E
  | .warning => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : GlobalNetExposureAction :=
  if byte = 0x3F then .notSet
  else if byte = 0x45 then .enforceLimit
  else if byte = 0x4E then .none_
  else .warning

def ofByte (byte : UInt8) : GlobalNetExposureAction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : GlobalNetExposureAction) : ofByte value.toByte = value := by
  cases value with
  | notSet => decide
  | enforceLimit => decide
  | none_ => decide
  | warning => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : GlobalNetExposureAction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (GlobalNetExposureAction × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : GlobalNetExposureAction) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : GlobalNetExposureAction) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : GlobalNetExposureAction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end GlobalNetExposureAction

/-- Default Net Exposure Action: one byte code -/
def DefaultNetExposureAction.codes : List UInt8 :=
  [0x3F, 0x45, 0x4E, 0x57]

inductive DefaultNetExposureAction where
  | notSet -- Not Set
  | enforceLimit -- Enforce Limit
  | none_ -- None
  | warning -- Warning
  | unlisted (byte : { byte : UInt8 // byte ∉ DefaultNetExposureAction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DefaultNetExposureAction

def toByte : DefaultNetExposureAction → UInt8
  | .notSet => 0x3F
  | .enforceLimit => 0x45
  | .none_ => 0x4E
  | .warning => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DefaultNetExposureAction :=
  if byte = 0x3F then .notSet
  else if byte = 0x45 then .enforceLimit
  else if byte = 0x4E then .none_
  else .warning

def ofByte (byte : UInt8) : DefaultNetExposureAction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DefaultNetExposureAction) : ofByte value.toByte = value := by
  cases value with
  | notSet => decide
  | enforceLimit => decide
  | none_ => decide
  | warning => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DefaultNetExposureAction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DefaultNetExposureAction × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DefaultNetExposureAction) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : DefaultNetExposureAction) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : DefaultNetExposureAction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DefaultNetExposureAction

/-- Default Long Exposure Action: one byte code -/
def DefaultLongExposureAction.codes : List UInt8 :=
  [0x3F, 0x45, 0x4E, 0x57]

inductive DefaultLongExposureAction where
  | notSet -- Not Set
  | enforceLimit -- Enforce Limit
  | none_ -- None
  | warning -- Warning
  | unlisted (byte : { byte : UInt8 // byte ∉ DefaultLongExposureAction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DefaultLongExposureAction

def toByte : DefaultLongExposureAction → UInt8
  | .notSet => 0x3F
  | .enforceLimit => 0x45
  | .none_ => 0x4E
  | .warning => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DefaultLongExposureAction :=
  if byte = 0x3F then .notSet
  else if byte = 0x45 then .enforceLimit
  else if byte = 0x4E then .none_
  else .warning

def ofByte (byte : UInt8) : DefaultLongExposureAction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DefaultLongExposureAction) : ofByte value.toByte = value := by
  cases value with
  | notSet => decide
  | enforceLimit => decide
  | none_ => decide
  | warning => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DefaultLongExposureAction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DefaultLongExposureAction × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DefaultLongExposureAction) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : DefaultLongExposureAction) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : DefaultLongExposureAction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DefaultLongExposureAction

/-- Default Short Exposure Action: one byte code -/
def DefaultShortExposureAction.codes : List UInt8 :=
  [0x3F, 0x45, 0x4E, 0x57]

inductive DefaultShortExposureAction where
  | notSet -- Not Set
  | enforceLimit -- Enforce Limit
  | none_ -- None
  | warning -- Warning
  | unlisted (byte : { byte : UInt8 // byte ∉ DefaultShortExposureAction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DefaultShortExposureAction

def toByte : DefaultShortExposureAction → UInt8
  | .notSet => 0x3F
  | .enforceLimit => 0x45
  | .none_ => 0x4E
  | .warning => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DefaultShortExposureAction :=
  if byte = 0x3F then .notSet
  else if byte = 0x45 then .enforceLimit
  else if byte = 0x4E then .none_
  else .warning

def ofByte (byte : UInt8) : DefaultShortExposureAction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DefaultShortExposureAction) : ofByte value.toByte = value := by
  cases value with
  | notSet => decide
  | enforceLimit => decide
  | none_ => decide
  | warning => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DefaultShortExposureAction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DefaultShortExposureAction × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DefaultShortExposureAction) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : DefaultShortExposureAction) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : DefaultShortExposureAction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DefaultShortExposureAction

/-- Default Net Position Action: one byte code -/
def DefaultNetPositionAction.codes : List UInt8 :=
  [0x3F, 0x45, 0x4E, 0x57]

inductive DefaultNetPositionAction where
  | notSet -- Not Set
  | enforceLimit -- Enforce Limit
  | none_ -- None
  | warning -- Warning
  | unlisted (byte : { byte : UInt8 // byte ∉ DefaultNetPositionAction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DefaultNetPositionAction

def toByte : DefaultNetPositionAction → UInt8
  | .notSet => 0x3F
  | .enforceLimit => 0x45
  | .none_ => 0x4E
  | .warning => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DefaultNetPositionAction :=
  if byte = 0x3F then .notSet
  else if byte = 0x45 then .enforceLimit
  else if byte = 0x4E then .none_
  else .warning

def ofByte (byte : UInt8) : DefaultNetPositionAction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DefaultNetPositionAction) : ofByte value.toByte = value := by
  cases value with
  | notSet => decide
  | enforceLimit => decide
  | none_ => decide
  | warning => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DefaultNetPositionAction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DefaultNetPositionAction × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DefaultNetPositionAction) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : DefaultNetPositionAction) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : DefaultNetPositionAction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DefaultNetPositionAction

/-- Default Long Position Action: one byte code -/
def DefaultLongPositionAction.codes : List UInt8 :=
  [0x3F, 0x45, 0x4E, 0x57]

inductive DefaultLongPositionAction where
  | notSet -- Not Set
  | enforceLimit -- Enforce Limit
  | none_ -- None
  | warning -- Warning
  | unlisted (byte : { byte : UInt8 // byte ∉ DefaultLongPositionAction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DefaultLongPositionAction

def toByte : DefaultLongPositionAction → UInt8
  | .notSet => 0x3F
  | .enforceLimit => 0x45
  | .none_ => 0x4E
  | .warning => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DefaultLongPositionAction :=
  if byte = 0x3F then .notSet
  else if byte = 0x45 then .enforceLimit
  else if byte = 0x4E then .none_
  else .warning

def ofByte (byte : UInt8) : DefaultLongPositionAction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DefaultLongPositionAction) : ofByte value.toByte = value := by
  cases value with
  | notSet => decide
  | enforceLimit => decide
  | none_ => decide
  | warning => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DefaultLongPositionAction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DefaultLongPositionAction × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DefaultLongPositionAction) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : DefaultLongPositionAction) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : DefaultLongPositionAction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DefaultLongPositionAction

/-- Default Short Position Action: one byte code -/
def DefaultShortPositionAction.codes : List UInt8 :=
  [0x3F, 0x45, 0x4E, 0x57]

inductive DefaultShortPositionAction where
  | notSet -- Not Set
  | enforceLimit -- Enforce Limit
  | none_ -- None
  | warning -- Warning
  | unlisted (byte : { byte : UInt8 // byte ∉ DefaultShortPositionAction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DefaultShortPositionAction

def toByte : DefaultShortPositionAction → UInt8
  | .notSet => 0x3F
  | .enforceLimit => 0x45
  | .none_ => 0x4E
  | .warning => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DefaultShortPositionAction :=
  if byte = 0x3F then .notSet
  else if byte = 0x45 then .enforceLimit
  else if byte = 0x4E then .none_
  else .warning

def ofByte (byte : UInt8) : DefaultShortPositionAction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DefaultShortPositionAction) : ofByte value.toByte = value := by
  cases value with
  | notSet => decide
  | enforceLimit => decide
  | none_ => decide
  | warning => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DefaultShortPositionAction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DefaultShortPositionAction × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DefaultShortPositionAction) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : DefaultShortPositionAction) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : DefaultShortPositionAction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DefaultShortPositionAction

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

/-- Special Price Term: one byte code -/
def SpecialPriceTerm.codes : List UInt8 :=
  [0x20, 0x53]

inductive SpecialPriceTerm where
  | none_ -- None
  | stopOrder -- Stop Order
  | unlisted (byte : { byte : UInt8 // byte ∉ SpecialPriceTerm.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SpecialPriceTerm

def toByte : SpecialPriceTerm → UInt8
  | .none_ => 0x20
  | .stopOrder => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SpecialPriceTerm :=
  if byte = 0x20 then .none_
  else .stopOrder

def ofByte (byte : UInt8) : SpecialPriceTerm :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SpecialPriceTerm) : ofByte value.toByte = value := by
  cases value with
  | none_ => decide
  | stopOrder => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SpecialPriceTerm) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SpecialPriceTerm × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SpecialPriceTerm) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SpecialPriceTerm) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SpecialPriceTerm) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SpecialPriceTerm

/-- Quantity Term: one byte code -/
def QuantityTerm.codes : List UInt8 :=
  [0x20, 0x44, 0x4D]

inductive QuantityTerm where
  | none_ -- None
  | disclosed -- Disclosed
  | minimum -- Minimum
  | unlisted (byte : { byte : UInt8 // byte ∉ QuantityTerm.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace QuantityTerm

def toByte : QuantityTerm → UInt8
  | .none_ => 0x20
  | .disclosed => 0x44
  | .minimum => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : QuantityTerm :=
  if byte = 0x20 then .none_
  else if byte = 0x44 then .disclosed
  else .minimum

def ofByte (byte : UInt8) : QuantityTerm :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : QuantityTerm) : ofByte value.toByte = value := by
  cases value with
  | none_ => decide
  | disclosed => decide
  | minimum => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : QuantityTerm) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (QuantityTerm × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : QuantityTerm) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : QuantityTerm) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : QuantityTerm) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end QuantityTerm

/-- Duration Type: one byte code -/
def DurationType.codes : List UInt8 :=
  [0x44, 0x45, 0x46, 0x4A, 0x50, 0x57]

inductive DurationType where
  | goodTillDate -- Good Till Date
  | fillAndKill -- Fill And Kill
  | goodTillCancel -- Good Till Cancel
  | day -- Day
  | preOpening -- Pre Opening
  | whileConnected -- While Connected
  | unlisted (byte : { byte : UInt8 // byte ∉ DurationType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DurationType

def toByte : DurationType → UInt8
  | .goodTillDate => 0x44
  | .fillAndKill => 0x45
  | .goodTillCancel => 0x46
  | .day => 0x4A
  | .preOpening => 0x50
  | .whileConnected => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DurationType :=
  if byte = 0x44 then .goodTillDate
  else if byte = 0x45 then .fillAndKill
  else if byte = 0x46 then .goodTillCancel
  else if byte = 0x4A then .day
  else if byte = 0x50 then .preOpening
  else .whileConnected

def ofByte (byte : UInt8) : DurationType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DurationType) : ofByte value.toByte = value := by
  cases value with
  | goodTillDate => decide
  | fillAndKill => decide
  | goodTillCancel => decide
  | day => decide
  | preOpening => decide
  | whileConnected => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DurationType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DurationType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DurationType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : DurationType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : DurationType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DurationType

/-- Anti Wash Instruction: one byte code -/
def AntiWashInstruction.codes : List UInt8 :=
  [0x42, 0x49, 0x4F]

inductive AntiWashInstruction where
  | cancelBothInboundOrderAndOppositeRestingOrder -- Cancel Both Inbound Order And Opposite Resting Order
  | cancelInboundOrder -- Cancel Inbound Order
  | cancelOppositeRestingOrder -- Cancel Opposite Resting Order
  | unlisted (byte : { byte : UInt8 // byte ∉ AntiWashInstruction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AntiWashInstruction

def toByte : AntiWashInstruction → UInt8
  | .cancelBothInboundOrderAndOppositeRestingOrder => 0x42
  | .cancelInboundOrder => 0x49
  | .cancelOppositeRestingOrder => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AntiWashInstruction :=
  if byte = 0x42 then .cancelBothInboundOrderAndOppositeRestingOrder
  else if byte = 0x49 then .cancelInboundOrder
  else .cancelOppositeRestingOrder

def ofByte (byte : UInt8) : AntiWashInstruction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AntiWashInstruction) : ofByte value.toByte = value := by
  cases value with
  | cancelBothInboundOrderAndOppositeRestingOrder => decide
  | cancelInboundOrder => decide
  | cancelOppositeRestingOrder => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AntiWashInstruction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AntiWashInstruction × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AntiWashInstruction) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : AntiWashInstruction) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : AntiWashInstruction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AntiWashInstruction

/-- Quantity Sign: one byte code -/
def QuantitySign.codes : List UInt8 :=
  [0x2B, 0x2D, 0x3D]

inductive QuantitySign where
  | addsTheIncomingQuantityToTheBookedQuantity -- Adds The Incoming Quantity To The Booked Quantity
  | subtractsTheIncomingQuantityFromTheBookedQuantity -- Subtracts The Incoming Quantity From The Booked Quantity
  | replacesTheBookedQuantityWithTheIncomingQuantity -- Replaces The Booked Quantity With The Incoming Quantity
  | unlisted (byte : { byte : UInt8 // byte ∉ QuantitySign.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace QuantitySign

def toByte : QuantitySign → UInt8
  | .addsTheIncomingQuantityToTheBookedQuantity => 0x2B
  | .subtractsTheIncomingQuantityFromTheBookedQuantity => 0x2D
  | .replacesTheBookedQuantityWithTheIncomingQuantity => 0x3D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : QuantitySign :=
  if byte = 0x2B then .addsTheIncomingQuantityToTheBookedQuantity
  else if byte = 0x2D then .subtractsTheIncomingQuantityFromTheBookedQuantity
  else .replacesTheBookedQuantityWithTheIncomingQuantity

def ofByte (byte : UInt8) : QuantitySign :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : QuantitySign) : ofByte value.toByte = value := by
  cases value with
  | addsTheIncomingQuantityToTheBookedQuantity => decide
  | subtractsTheIncomingQuantityFromTheBookedQuantity => decide
  | replacesTheBookedQuantityWithTheIncomingQuantity => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : QuantitySign) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (QuantitySign × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : QuantitySign) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : QuantitySign) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : QuantitySign) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end QuantitySign

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

/-- Quantity Sign Or: one byte code -/
def QuantitySignOr.codes : List UInt8 :=
  [0x2B, 0x2D, 0x3D]

inductive QuantitySignOr where
  | addsTheIncomingQuantityToTheBookedQuantity -- Adds The Incoming Quantity To The Booked Quantity
  | subtractsTheIncomingQuantityFromTheBookedQuantity -- Subtracts The Incoming Quantity From The Booked Quantity
  | replacesTheBookedQuantityWithTheIncomingQuantity -- Replaces The Booked Quantity With The Incoming Quantity
  | unlisted (byte : { byte : UInt8 // byte ∉ QuantitySignOr.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace QuantitySignOr

def toByte : QuantitySignOr → UInt8
  | .addsTheIncomingQuantityToTheBookedQuantity => 0x2B
  | .subtractsTheIncomingQuantityFromTheBookedQuantity => 0x2D
  | .replacesTheBookedQuantityWithTheIncomingQuantity => 0x3D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : QuantitySignOr :=
  if byte = 0x2B then .addsTheIncomingQuantityToTheBookedQuantity
  else if byte = 0x2D then .subtractsTheIncomingQuantityFromTheBookedQuantity
  else .replacesTheBookedQuantityWithTheIncomingQuantity

def ofByte (byte : UInt8) : QuantitySignOr :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : QuantitySignOr) : ofByte value.toByte = value := by
  cases value with
  | addsTheIncomingQuantityToTheBookedQuantity => decide
  | subtractsTheIncomingQuantityFromTheBookedQuantity => decide
  | replacesTheBookedQuantityWithTheIncomingQuantity => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : QuantitySignOr) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (QuantitySignOr × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : QuantitySignOr) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : QuantitySignOr) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : QuantitySignOr) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end QuantitySignOr

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

/-- Protection Type Advanced Protection Advanced Protection Disabled: one byte code -/
def ProtectionTypeAdvancedProtectionAdvancedProtectionDisabled.codes : List UInt8 :=
  [0x41, 0x4E]

inductive ProtectionTypeAdvancedProtectionAdvancedProtectionDisabled where
  | advancedProtection -- Advanced Protection
  | advancedProtectionDisabled -- Advanced Protection Disabled
  | unlisted (byte : { byte : UInt8 // byte ∉ ProtectionTypeAdvancedProtectionAdvancedProtectionDisabled.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ProtectionTypeAdvancedProtectionAdvancedProtectionDisabled

def toByte : ProtectionTypeAdvancedProtectionAdvancedProtectionDisabled → UInt8
  | .advancedProtection => 0x41
  | .advancedProtectionDisabled => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ProtectionTypeAdvancedProtectionAdvancedProtectionDisabled :=
  if byte = 0x41 then .advancedProtection
  else .advancedProtectionDisabled

def ofByte (byte : UInt8) : ProtectionTypeAdvancedProtectionAdvancedProtectionDisabled :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ProtectionTypeAdvancedProtectionAdvancedProtectionDisabled) : ofByte value.toByte = value := by
  cases value with
  | advancedProtection => decide
  | advancedProtectionDisabled => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ProtectionTypeAdvancedProtectionAdvancedProtectionDisabled) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ProtectionTypeAdvancedProtectionAdvancedProtectionDisabled × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ProtectionTypeAdvancedProtectionAdvancedProtectionDisabled) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ProtectionTypeAdvancedProtectionAdvancedProtectionDisabled) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ProtectionTypeAdvancedProtectionAdvancedProtectionDisabled) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ProtectionTypeAdvancedProtectionAdvancedProtectionDisabled

/-- User Connection Occurrence: 2 bytes -/
structure UserConnectionOccurrence where
  messageTypesToBeReceived : Alpha 2
  deriving DecidableEq, Repr

namespace UserConnectionOccurrence

def encode (message : UserConnectionOccurrence) : List UInt8 :=
  Alpha.encode message.messageTypesToBeReceived

def decode (bytes : List UInt8) : Option (UserConnectionOccurrence × List UInt8) := do
  let (messageTypesToBeReceived, bytes) ← Alpha.decode 2 bytes
  pure ({ messageTypesToBeReceived }, bytes)

@[simp] theorem encode_length (message : UserConnectionOccurrence) : (encode message).length = 2 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : UserConnectionOccurrence) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UserConnectionOccurrence) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end UserConnectionOccurrence

/-- User Connection -/
structure UserConnection where
  protocolId : Alpha 2
  userId : Alpha 8
  passwordMd5Encryption : Alpha 8
  sessionId : Alpha 4
  userMessageTimestampLocalHhmmss : Alpha 6
  exchangeMessageId : Alpha 6
  inactivityInterval : Alpha 2
  userConnectionOccurrence : Digited 2 UserConnectionOccurrence
  deriving DecidableEq, Repr

namespace UserConnection

def encode (message : UserConnection) : List UInt8 :=
  Alpha.encode message.protocolId
    ++ (Alpha.encode message.userId
    ++ (Alpha.encode message.passwordMd5Encryption
    ++ (Alpha.encode message.sessionId
    ++ (Alpha.encode message.userMessageTimestampLocalHhmmss
    ++ (Alpha.encode message.exchangeMessageId
    ++ (Alpha.encode message.inactivityInterval
    ++ (encodeDigits 2 message.userConnectionOccurrence.val.length
    ++ (encodeMany UserConnectionOccurrence.encode message.userConnectionOccurrence.val))))))))

def decode (bytes : List UInt8) : Option (UserConnection × List UInt8) := do
  let (protocolId, bytes) ← Alpha.decode 2 bytes
  let (userId, bytes) ← Alpha.decode 8 bytes
  let (passwordMd5Encryption, bytes) ← Alpha.decode 8 bytes
  let (sessionId, bytes) ← Alpha.decode 4 bytes
  let (userMessageTimestampLocalHhmmss, bytes) ← Alpha.decode 6 bytes
  let (exchangeMessageId, bytes) ← Alpha.decode 6 bytes
  let (inactivityInterval, bytes) ← Alpha.decode 2 bytes
  let (numberOfMessageTypesToBeReceived, bytes) ← decodeDigits 2 bytes
  let (userConnectionOccurrence_, bytes) ← decodeMany UserConnectionOccurrence.decode numberOfMessageTypesToBeReceived bytes
  if fits_userConnectionOccurrence : userConnectionOccurrence_.length < 10 ^ 2 then
    pure ({ protocolId, userId, passwordMd5Encryption, sessionId, userMessageTimestampLocalHhmmss, exchangeMessageId, inactivityInterval, userConnectionOccurrence := ⟨userConnectionOccurrence_, fits_userConnectionOccurrence⟩ }, bytes)
  else none

theorem encode_length_pos (message : UserConnection) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : UserConnection) : (encode message).length ≤ 236 := by
  have bound_userConnectionOccurrence := message.userConnectionOccurrence.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeDigits_length, encodeMany_length_const UserConnectionOccurrence.encode 2 UserConnectionOccurrence.encode_length]
  omega

@[simp] theorem decode_encode (message : UserConnection) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.userConnectionOccurrence.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany UserConnectionOccurrence.encode UserConnectionOccurrence.decode UserConnectionOccurrence.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.userConnectionOccurrence.length_lt]
  rfl

end UserConnection

/-- Disconnection Instruction Occurrence: 10 bytes -/
structure DisconnectionInstructionOccurrence where
  traderId : Alpha 8
  disconnectionInstructionNoteCancelQuotesOnlyQQuotesOnly : DisconnectionInstructionNoteCancelQuotesOnlyQQuotesOnly
  activeYOnNOff : ActiveYOnNOff
  deriving DecidableEq, Repr

namespace DisconnectionInstructionOccurrence

def encode (message : DisconnectionInstructionOccurrence) : List UInt8 :=
  Alpha.encode message.traderId
    ++ (DisconnectionInstructionNoteCancelQuotesOnlyQQuotesOnly.encode message.disconnectionInstructionNoteCancelQuotesOnlyQQuotesOnly
    ++ (ActiveYOnNOff.encode message.activeYOnNOff))

def decode (bytes : List UInt8) : Option (DisconnectionInstructionOccurrence × List UInt8) := do
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (disconnectionInstructionNoteCancelQuotesOnlyQQuotesOnly, bytes) ← DisconnectionInstructionNoteCancelQuotesOnlyQQuotesOnly.decode bytes
  let (activeYOnNOff, bytes) ← ActiveYOnNOff.decode bytes
  pure ({ traderId, disconnectionInstructionNoteCancelQuotesOnlyQQuotesOnly, activeYOnNOff }, bytes)

@[simp] theorem encode_length (message : DisconnectionInstructionOccurrence) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, DisconnectionInstructionNoteCancelQuotesOnlyQQuotesOnly.encode_length, ActiveYOnNOff.encode_length]

theorem encode_length_pos (message : DisconnectionInstructionOccurrence) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DisconnectionInstructionOccurrence) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DisconnectionInstructionNoteCancelQuotesOnlyQQuotesOnly.decode_encode, some_bind]
  dsimp only
  rw [ActiveYOnNOff.decode_encode, some_bind]
  rfl

end DisconnectionInstructionOccurrence

/-- Disconnection Instruction -/
structure DisconnectionInstruction where
  disconnectionInstructionOccurrence : Digited 2 DisconnectionInstructionOccurrence
  deriving DecidableEq, Repr

namespace DisconnectionInstruction

def encode (message : DisconnectionInstruction) : List UInt8 :=
  encodeDigits 2 message.disconnectionInstructionOccurrence.val.length
    ++ (encodeMany DisconnectionInstructionOccurrence.encode message.disconnectionInstructionOccurrence.val)

def decode (bytes : List UInt8) : Option (DisconnectionInstruction × List UInt8) := do
  let (numberOfInstructionsPresentInTheMessage, bytes) ← decodeDigits 2 bytes
  let (disconnectionInstructionOccurrence_, bytes) ← decodeMany DisconnectionInstructionOccurrence.decode numberOfInstructionsPresentInTheMessage bytes
  if fits_disconnectionInstructionOccurrence : disconnectionInstructionOccurrence_.length < 10 ^ 2 then
    pure ({ disconnectionInstructionOccurrence := ⟨disconnectionInstructionOccurrence_, fits_disconnectionInstructionOccurrence⟩ }, bytes)
  else none

theorem encode_length_pos (message : DisconnectionInstruction) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeDigits_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DisconnectionInstruction) : (encode message).length ≤ 992 := by
  have bound_disconnectionInstructionOccurrence := message.disconnectionInstructionOccurrence.length_lt
  unfold encode
  simp only [List.length_append, encodeDigits_length, encodeMany_length_const DisconnectionInstructionOccurrence.encode 10 DisconnectionInstructionOccurrence.encode_length]
  omega

@[simp] theorem decode_encode (message : DisconnectionInstruction) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.disconnectionInstructionOccurrence.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany DisconnectionInstructionOccurrence.encode DisconnectionInstructionOccurrence.decode DisconnectionInstructionOccurrence.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.disconnectionInstructionOccurrence.length_lt]
  rfl

end DisconnectionInstruction

/-- Heartbeat Response: 20 bytes -/
structure HeartbeatResponse where
  userSequenceIdFirstUserSequenceIdForNextcurrentHeartbeatPeriod : Alpha 8
  lastExchangeMessageIdSentToParticipant : Alpha 6
  userMessageTimestampLocalHhmmss : Alpha 6
  deriving DecidableEq, Repr

namespace HeartbeatResponse

def encode (message : HeartbeatResponse) : List UInt8 :=
  Alpha.encode message.userSequenceIdFirstUserSequenceIdForNextcurrentHeartbeatPeriod
    ++ (Alpha.encode message.lastExchangeMessageIdSentToParticipant
    ++ (Alpha.encode message.userMessageTimestampLocalHhmmss))

def decode (bytes : List UInt8) : Option (HeartbeatResponse × List UInt8) := do
  let (userSequenceIdFirstUserSequenceIdForNextcurrentHeartbeatPeriod, bytes) ← Alpha.decode 8 bytes
  let (lastExchangeMessageIdSentToParticipant, bytes) ← Alpha.decode 6 bytes
  let (userMessageTimestampLocalHhmmss, bytes) ← Alpha.decode 6 bytes
  pure ({ userSequenceIdFirstUserSequenceIdForNextcurrentHeartbeatPeriod, lastExchangeMessageIdSentToParticipant, userMessageTimestampLocalHhmmss }, bytes)

@[simp] theorem encode_length (message : HeartbeatResponse) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : HeartbeatResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : HeartbeatResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end HeartbeatResponse

/-- User Disconnection: 12 bytes -/
structure UserDisconnection where
  userId : Alpha 8
  sessionId : Alpha 4
  deriving DecidableEq, Repr

namespace UserDisconnection

def encode (message : UserDisconnection) : List UInt8 :=
  Alpha.encode message.userId
    ++ (Alpha.encode message.sessionId)

def decode (bytes : List UInt8) : Option (UserDisconnection × List UInt8) := do
  let (userId, bytes) ← Alpha.decode 8 bytes
  let (sessionId, bytes) ← Alpha.decode 4 bytes
  pure ({ userId, sessionId }, bytes)

@[simp] theorem encode_length (message : UserDisconnection) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : UserDisconnection) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UserDisconnection) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end UserDisconnection

/-- Incoming Messages Header: 22 bytes -/
structure IncomingMessagesHeader where
  userTimestampLocalHhmmss : Alpha 6
  traderId : Alpha 8
  userSequenceId : Alpha 8
  deriving DecidableEq, Repr

namespace IncomingMessagesHeader

def encode (message : IncomingMessagesHeader) : List UInt8 :=
  Alpha.encode message.userTimestampLocalHhmmss
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.userSequenceId))

def decode (bytes : List UInt8) : Option (IncomingMessagesHeader × List UInt8) := do
  let (userTimestampLocalHhmmss, bytes) ← Alpha.decode 6 bytes
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (userSequenceId, bytes) ← Alpha.decode 8 bytes
  pure ({ userTimestampLocalHhmmss, traderId, userSequenceId }, bytes)

@[simp] theorem encode_length (message : IncomingMessagesHeader) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : IncomingMessagesHeader) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IncomingMessagesHeader) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end IncomingMessagesHeader

/-- Order Request: 22 bytes -/
structure OrderRequest where
  incomingMessagesHeader : IncomingMessagesHeader
  deriving DecidableEq, Repr

namespace OrderRequest

def encode (message : OrderRequest) : List UInt8 :=
  IncomingMessagesHeader.encode message.incomingMessagesHeader

def decode (bytes : List UInt8) : Option (OrderRequest × List UInt8) := do
  let (incomingMessagesHeader, bytes) ← IncomingMessagesHeader.decode bytes
  pure ({ incomingMessagesHeader }, bytes)

@[simp] theorem encode_length (message : OrderRequest) : (encode message).length = 22 := by
  unfold encode
  simp only [IncomingMessagesHeader.encode_length]

theorem encode_length_pos (message : OrderRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [IncomingMessagesHeader.decode_encode, some_bind]
  rfl

end OrderRequest

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

/-- Bulk Quote Data: 174 bytes -/
structure BulkQuoteData where
  incomingMessagesHeader : IncomingMessagesHeader
  group : Alpha 2
  clearingData : ClearingData
  ownerData : OwnerData
  maximumNumberTrades : Alpha 2
  minimumVolume : Alpha 8
  filler2 : Alpha 2
  calculationTimeInterval : Alpha 8
  maximumTotalVolume : Alpha 8
  maximumTotalValue : Alpha 8
  deltaMaximumVolume : Alpha 8
  deltaMaximumValue : Alpha 8
  antiWashId : Alpha 8
  filler20 : Alpha 20
  deriving DecidableEq, Repr

namespace BulkQuoteData

def encode (message : BulkQuoteData) : List UInt8 :=
  IncomingMessagesHeader.encode message.incomingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (ClearingData.encode message.clearingData
    ++ (OwnerData.encode message.ownerData
    ++ (Alpha.encode message.maximumNumberTrades
    ++ (Alpha.encode message.minimumVolume
    ++ (Alpha.encode message.filler2
    ++ (Alpha.encode message.calculationTimeInterval
    ++ (Alpha.encode message.maximumTotalVolume
    ++ (Alpha.encode message.maximumTotalValue
    ++ (Alpha.encode message.deltaMaximumVolume
    ++ (Alpha.encode message.deltaMaximumValue
    ++ (Alpha.encode message.antiWashId
    ++ (Alpha.encode message.filler20)))))))))))))

def decode (bytes : List UInt8) : Option (BulkQuoteData × List UInt8) := do
  let (incomingMessagesHeader, bytes) ← IncomingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (clearingData, bytes) ← ClearingData.decode bytes
  let (ownerData, bytes) ← OwnerData.decode bytes
  let (maximumNumberTrades, bytes) ← Alpha.decode 2 bytes
  let (minimumVolume, bytes) ← Alpha.decode 8 bytes
  let (filler2, bytes) ← Alpha.decode 2 bytes
  let (calculationTimeInterval, bytes) ← Alpha.decode 8 bytes
  let (maximumTotalVolume, bytes) ← Alpha.decode 8 bytes
  let (maximumTotalValue, bytes) ← Alpha.decode 8 bytes
  let (deltaMaximumVolume, bytes) ← Alpha.decode 8 bytes
  let (deltaMaximumValue, bytes) ← Alpha.decode 8 bytes
  let (antiWashId, bytes) ← Alpha.decode 8 bytes
  let (filler20, bytes) ← Alpha.decode 20 bytes
  pure ({ incomingMessagesHeader, group, clearingData, ownerData, maximumNumberTrades, minimumVolume, filler2, calculationTimeInterval, maximumTotalVolume, maximumTotalValue, deltaMaximumVolume, deltaMaximumValue, antiWashId, filler20 }, bytes)

@[simp] theorem encode_length (message : BulkQuoteData) : (encode message).length = 174 := by
  unfold encode
  simp only [List.length_append, IncomingMessagesHeader.encode_length, Alpha.encode_length, ClearingData.encode_length, OwnerData.encode_length]

theorem encode_length_pos (message : BulkQuoteData) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BulkQuoteData) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, IncomingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ClearingData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OwnerData.decode_encode, some_bind]
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

end BulkQuoteData

/-- Firm Risk Config Trader Team Trader: 4 bytes -/
structure FirmRiskConfigTraderTeamTrader where
  trader : Alpha 4
  deriving DecidableEq, Repr

namespace FirmRiskConfigTraderTeamTrader

def encode (message : FirmRiskConfigTraderTeamTrader) : List UInt8 :=
  Alpha.encode message.trader

def decode (bytes : List UInt8) : Option (FirmRiskConfigTraderTeamTrader × List UInt8) := do
  let (trader, bytes) ← Alpha.decode 4 bytes
  pure ({ trader }, bytes)

@[simp] theorem encode_length (message : FirmRiskConfigTraderTeamTrader) : (encode message).length = 4 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : FirmRiskConfigTraderTeamTrader) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FirmRiskConfigTraderTeamTrader) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end FirmRiskConfigTraderTeamTrader

/-- Firm Risk Config Trader Team -/
structure FirmRiskConfigTraderTeam where
  teamLevelRiskOption : TeamLevelRiskOption
  firmRiskConfigTraderTeamTrader : Digited 3 FirmRiskConfigTraderTeamTrader
  deriving DecidableEq, Repr

namespace FirmRiskConfigTraderTeam

def encode (message : FirmRiskConfigTraderTeam) : List UInt8 :=
  TeamLevelRiskOption.encode message.teamLevelRiskOption
    ++ (encodeDigits 3 message.firmRiskConfigTraderTeamTrader.val.length
    ++ (encodeMany FirmRiskConfigTraderTeamTrader.encode message.firmRiskConfigTraderTeamTrader.val))

def decode (bytes : List UInt8) : Option (FirmRiskConfigTraderTeam × List UInt8) := do
  let (teamLevelRiskOption, bytes) ← TeamLevelRiskOption.decode bytes
  let (numberOfTradersInTeam, bytes) ← decodeDigits 3 bytes
  let (firmRiskConfigTraderTeamTrader_, bytes) ← decodeMany FirmRiskConfigTraderTeamTrader.decode numberOfTradersInTeam bytes
  if fits_firmRiskConfigTraderTeamTrader : firmRiskConfigTraderTeamTrader_.length < 10 ^ 3 then
    pure ({ teamLevelRiskOption, firmRiskConfigTraderTeamTrader := ⟨firmRiskConfigTraderTeamTrader_, fits_firmRiskConfigTraderTeamTrader⟩ }, bytes)
  else none

theorem encode_length_pos (message : FirmRiskConfigTraderTeam) : (encode message).length > 0 := by
  unfold encode
  simp only [TeamLevelRiskOption.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : FirmRiskConfigTraderTeam) : (encode message).length ≤ 4000 := by
  have bound_firmRiskConfigTraderTeamTrader := message.firmRiskConfigTraderTeamTrader.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, TeamLevelRiskOption.encode_length, encodeDigits_length, encodeMany_length_const FirmRiskConfigTraderTeamTrader.encode 4 FirmRiskConfigTraderTeamTrader.encode_length]
  omega

@[simp] theorem decode_encode (message : FirmRiskConfigTraderTeam) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, TeamLevelRiskOption.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.firmRiskConfigTraderTeamTrader.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany FirmRiskConfigTraderTeamTrader.encode FirmRiskConfigTraderTeamTrader.decode FirmRiskConfigTraderTeamTrader.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.firmRiskConfigTraderTeamTrader.length_lt]
  rfl

end FirmRiskConfigTraderTeam

/-- Firm Risk Config -/
structure FirmRiskConfig where
  incomingMessagesHeader : IncomingMessagesHeader
  firmLevelRiskOption : FirmLevelRiskOption
  firmRiskConfigTraderTeam : Digited 3 FirmRiskConfigTraderTeam
  deriving DecidableEq, Repr

namespace FirmRiskConfig

def encode (message : FirmRiskConfig) : List UInt8 :=
  IncomingMessagesHeader.encode message.incomingMessagesHeader
    ++ (FirmLevelRiskOption.encode message.firmLevelRiskOption
    ++ (encodeDigits 3 message.firmRiskConfigTraderTeam.val.length
    ++ (encodeMany FirmRiskConfigTraderTeam.encode message.firmRiskConfigTraderTeam.val)))

def decode (bytes : List UInt8) : Option (FirmRiskConfig × List UInt8) := do
  let (incomingMessagesHeader, bytes) ← IncomingMessagesHeader.decode bytes
  let (firmLevelRiskOption, bytes) ← FirmLevelRiskOption.decode bytes
  let (numberOfTraderTeams, bytes) ← decodeDigits 3 bytes
  let (firmRiskConfigTraderTeam_, bytes) ← decodeMany FirmRiskConfigTraderTeam.decode numberOfTraderTeams bytes
  if fits_firmRiskConfigTraderTeam : firmRiskConfigTraderTeam_.length < 10 ^ 3 then
    pure ({ incomingMessagesHeader, firmLevelRiskOption, firmRiskConfigTraderTeam := ⟨firmRiskConfigTraderTeam_, fits_firmRiskConfigTraderTeam⟩ }, bytes)
  else none

theorem encode_length_pos (message : FirmRiskConfig) : (encode message).length > 0 := by
  unfold encode
  simp only [IncomingMessagesHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : FirmRiskConfig) : (encode message).length ≤ 3996026 := by
  have bound_firmRiskConfigTraderTeam := message.firmRiskConfigTraderTeam.length_lt
  have bound_firmRiskConfigTraderTeam_items := encodeMany_length_le FirmRiskConfigTraderTeam.encode 4000 FirmRiskConfigTraderTeam.encode_length_le message.firmRiskConfigTraderTeam.val
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, IncomingMessagesHeader.encode_length, FirmLevelRiskOption.encode_length, encodeDigits_length]
  omega

@[simp] theorem decode_encode (message : FirmRiskConfig) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, IncomingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FirmLevelRiskOption.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.firmRiskConfigTraderTeam.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany FirmRiskConfigTraderTeam.encode FirmRiskConfigTraderTeam.decode FirmRiskConfigTraderTeam.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.firmRiskConfigTraderTeam.length_lt]
  rfl

end FirmRiskConfig

/-- Global Cancellation: 25 bytes -/
structure GlobalCancellation where
  incomingMessagesHeader : IncomingMessagesHeader
  group : Alpha 2
  typeOfCancellationQQuotesOnly : TypeOfCancellationQQuotesOnly
  deriving DecidableEq, Repr

namespace GlobalCancellation

def encode (message : GlobalCancellation) : List UInt8 :=
  IncomingMessagesHeader.encode message.incomingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (TypeOfCancellationQQuotesOnly.encode message.typeOfCancellationQQuotesOnly))

def decode (bytes : List UInt8) : Option (GlobalCancellation × List UInt8) := do
  let (incomingMessagesHeader, bytes) ← IncomingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (typeOfCancellationQQuotesOnly, bytes) ← TypeOfCancellationQQuotesOnly.decode bytes
  pure ({ incomingMessagesHeader, group, typeOfCancellationQQuotesOnly }, bytes)

@[simp] theorem encode_length (message : GlobalCancellation) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, IncomingMessagesHeader.encode_length, Alpha.encode_length, TypeOfCancellationQQuotesOnly.encode_length]

theorem encode_length_pos (message : GlobalCancellation) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : GlobalCancellation) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, IncomingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [TypeOfCancellationQQuotesOnly.decode_encode, some_bind]
  rfl

end GlobalCancellation

/-- User Global Cancellation: 37 bytes -/
structure UserGlobalCancellation where
  incomingMessagesHeader : IncomingMessagesHeader
  groupFilter : Alpha 2
  instrumentFilter : Alpha 4
  typeOfCancellation : TypeOfCancellation
  accountTypeFilter : Alpha 8
  deriving DecidableEq, Repr

namespace UserGlobalCancellation

def encode (message : UserGlobalCancellation) : List UInt8 :=
  IncomingMessagesHeader.encode message.incomingMessagesHeader
    ++ (Alpha.encode message.groupFilter
    ++ (Alpha.encode message.instrumentFilter
    ++ (TypeOfCancellation.encode message.typeOfCancellation
    ++ (Alpha.encode message.accountTypeFilter))))

def decode (bytes : List UInt8) : Option (UserGlobalCancellation × List UInt8) := do
  let (incomingMessagesHeader, bytes) ← IncomingMessagesHeader.decode bytes
  let (groupFilter, bytes) ← Alpha.decode 2 bytes
  let (instrumentFilter, bytes) ← Alpha.decode 4 bytes
  let (typeOfCancellation, bytes) ← TypeOfCancellation.decode bytes
  let (accountTypeFilter, bytes) ← Alpha.decode 8 bytes
  pure ({ incomingMessagesHeader, groupFilter, instrumentFilter, typeOfCancellation, accountTypeFilter }, bytes)

@[simp] theorem encode_length (message : UserGlobalCancellation) : (encode message).length = 37 := by
  unfold encode
  simp only [List.length_append, IncomingMessagesHeader.encode_length, Alpha.encode_length, TypeOfCancellation.encode_length]

theorem encode_length_pos (message : UserGlobalCancellation) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UserGlobalCancellation) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, IncomingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TypeOfCancellation.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end UserGlobalCancellation

/-- Set Group Risk Limits Occurrence: 76 bytes -/
structure SetGroupRiskLimitsOccurrence where
  trader : Alpha 4
  group : Alpha 2
  netExposureAction : NetExposureAction
  longExposureAction : LongExposureAction
  shortExposureAction : ShortExposureAction
  netPositionAction : NetPositionAction
  longPositionAction : LongPositionAction
  shortPositionAction : ShortPositionAction
  maximumOrderQuantity : Alpha 8
  netPositionLimit : Alpha 8
  longPositionLimit : Alpha 8
  shortPositionLimit : Alpha 8
  netExposureLimit : Alpha 10
  longExposureLimit : Alpha 10
  shortExposureLimit : Alpha 10
  filler2 : Alpha 2
  deriving DecidableEq, Repr

namespace SetGroupRiskLimitsOccurrence

def encode (message : SetGroupRiskLimitsOccurrence) : List UInt8 :=
  Alpha.encode message.trader
    ++ (Alpha.encode message.group
    ++ (NetExposureAction.encode message.netExposureAction
    ++ (LongExposureAction.encode message.longExposureAction
    ++ (ShortExposureAction.encode message.shortExposureAction
    ++ (NetPositionAction.encode message.netPositionAction
    ++ (LongPositionAction.encode message.longPositionAction
    ++ (ShortPositionAction.encode message.shortPositionAction
    ++ (Alpha.encode message.maximumOrderQuantity
    ++ (Alpha.encode message.netPositionLimit
    ++ (Alpha.encode message.longPositionLimit
    ++ (Alpha.encode message.shortPositionLimit
    ++ (Alpha.encode message.netExposureLimit
    ++ (Alpha.encode message.longExposureLimit
    ++ (Alpha.encode message.shortExposureLimit
    ++ (Alpha.encode message.filler2)))))))))))))))

def decode (bytes : List UInt8) : Option (SetGroupRiskLimitsOccurrence × List UInt8) := do
  let (trader, bytes) ← Alpha.decode 4 bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (netExposureAction, bytes) ← NetExposureAction.decode bytes
  let (longExposureAction, bytes) ← LongExposureAction.decode bytes
  let (shortExposureAction, bytes) ← ShortExposureAction.decode bytes
  let (netPositionAction, bytes) ← NetPositionAction.decode bytes
  let (longPositionAction, bytes) ← LongPositionAction.decode bytes
  let (shortPositionAction, bytes) ← ShortPositionAction.decode bytes
  let (maximumOrderQuantity, bytes) ← Alpha.decode 8 bytes
  let (netPositionLimit, bytes) ← Alpha.decode 8 bytes
  let (longPositionLimit, bytes) ← Alpha.decode 8 bytes
  let (shortPositionLimit, bytes) ← Alpha.decode 8 bytes
  let (netExposureLimit, bytes) ← Alpha.decode 10 bytes
  let (longExposureLimit, bytes) ← Alpha.decode 10 bytes
  let (shortExposureLimit, bytes) ← Alpha.decode 10 bytes
  let (filler2, bytes) ← Alpha.decode 2 bytes
  pure ({ trader, group, netExposureAction, longExposureAction, shortExposureAction, netPositionAction, longPositionAction, shortPositionAction, maximumOrderQuantity, netPositionLimit, longPositionLimit, shortPositionLimit, netExposureLimit, longExposureLimit, shortExposureLimit, filler2 }, bytes)

@[simp] theorem encode_length (message : SetGroupRiskLimitsOccurrence) : (encode message).length = 76 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, NetExposureAction.encode_length, LongExposureAction.encode_length, ShortExposureAction.encode_length, NetPositionAction.encode_length, LongPositionAction.encode_length, ShortPositionAction.encode_length]

theorem encode_length_pos (message : SetGroupRiskLimitsOccurrence) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SetGroupRiskLimitsOccurrence) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetExposureAction.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LongExposureAction.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ShortExposureAction.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetPositionAction.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LongPositionAction.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ShortPositionAction.decode_encode, some_bind]
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

end SetGroupRiskLimitsOccurrence

/-- Set Group Risk Limits -/
structure SetGroupRiskLimits where
  incomingMessagesHeader : IncomingMessagesHeader
  resetAllGroups : ResetAllGroups
  setGroupRiskLimitsOccurrence : Digited 3 SetGroupRiskLimitsOccurrence
  deriving DecidableEq, Repr

namespace SetGroupRiskLimits

def encode (message : SetGroupRiskLimits) : List UInt8 :=
  IncomingMessagesHeader.encode message.incomingMessagesHeader
    ++ (ResetAllGroups.encode message.resetAllGroups
    ++ (encodeDigits 3 message.setGroupRiskLimitsOccurrence.val.length
    ++ (encodeMany SetGroupRiskLimitsOccurrence.encode message.setGroupRiskLimitsOccurrence.val)))

def decode (bytes : List UInt8) : Option (SetGroupRiskLimits × List UInt8) := do
  let (incomingMessagesHeader, bytes) ← IncomingMessagesHeader.decode bytes
  let (resetAllGroups, bytes) ← ResetAllGroups.decode bytes
  let (numberOfGroupLimits, bytes) ← decodeDigits 3 bytes
  let (setGroupRiskLimitsOccurrence_, bytes) ← decodeMany SetGroupRiskLimitsOccurrence.decode numberOfGroupLimits bytes
  if fits_setGroupRiskLimitsOccurrence : setGroupRiskLimitsOccurrence_.length < 10 ^ 3 then
    pure ({ incomingMessagesHeader, resetAllGroups, setGroupRiskLimitsOccurrence := ⟨setGroupRiskLimitsOccurrence_, fits_setGroupRiskLimitsOccurrence⟩ }, bytes)
  else none

theorem encode_length_pos (message : SetGroupRiskLimits) : (encode message).length > 0 := by
  unfold encode
  simp only [IncomingMessagesHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SetGroupRiskLimits) : (encode message).length ≤ 75950 := by
  have bound_setGroupRiskLimitsOccurrence := message.setGroupRiskLimitsOccurrence.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, IncomingMessagesHeader.encode_length, ResetAllGroups.encode_length, encodeDigits_length, encodeMany_length_const SetGroupRiskLimitsOccurrence.encode 76 SetGroupRiskLimitsOccurrence.encode_length]
  omega

@[simp] theorem decode_encode (message : SetGroupRiskLimits) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, IncomingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ResetAllGroups.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.setGroupRiskLimitsOccurrence.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany SetGroupRiskLimitsOccurrence.encode SetGroupRiskLimitsOccurrence.decode SetGroupRiskLimitsOccurrence.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.setGroupRiskLimitsOccurrence.length_lt]
  rfl

end SetGroupRiskLimits

/-- Set Global Risk Limits: 101 bytes -/
structure SetGlobalRiskLimits where
  incomingMessagesHeader : IncomingMessagesHeader
  globalNetExposureAction : GlobalNetExposureAction
  defaultNetExposureAction : DefaultNetExposureAction
  defaultLongExposureAction : DefaultLongExposureAction
  defaultShortExposureAction : DefaultShortExposureAction
  defaultNetPositionAction : DefaultNetPositionAction
  defaultLongPositionAction : DefaultLongPositionAction
  defaultShortPositionAction : DefaultShortPositionAction
  globalNetExposureLimit : Alpha 10
  defaultMaximumOrderQuantity : Alpha 8
  defaultNetExposureLimit : Alpha 10
  defaultLongExposureLimit : Alpha 10
  defaultShortExposureLimit : Alpha 10
  defaultNetPositionLimit : Alpha 8
  defaultLongPositionLimit : Alpha 8
  defaultShortPositionLimit : Alpha 8
  deriving DecidableEq, Repr

namespace SetGlobalRiskLimits

def encode (message : SetGlobalRiskLimits) : List UInt8 :=
  IncomingMessagesHeader.encode message.incomingMessagesHeader
    ++ (GlobalNetExposureAction.encode message.globalNetExposureAction
    ++ (DefaultNetExposureAction.encode message.defaultNetExposureAction
    ++ (DefaultLongExposureAction.encode message.defaultLongExposureAction
    ++ (DefaultShortExposureAction.encode message.defaultShortExposureAction
    ++ (DefaultNetPositionAction.encode message.defaultNetPositionAction
    ++ (DefaultLongPositionAction.encode message.defaultLongPositionAction
    ++ (DefaultShortPositionAction.encode message.defaultShortPositionAction
    ++ (Alpha.encode message.globalNetExposureLimit
    ++ (Alpha.encode message.defaultMaximumOrderQuantity
    ++ (Alpha.encode message.defaultNetExposureLimit
    ++ (Alpha.encode message.defaultLongExposureLimit
    ++ (Alpha.encode message.defaultShortExposureLimit
    ++ (Alpha.encode message.defaultNetPositionLimit
    ++ (Alpha.encode message.defaultLongPositionLimit
    ++ (Alpha.encode message.defaultShortPositionLimit)))))))))))))))

def decode (bytes : List UInt8) : Option (SetGlobalRiskLimits × List UInt8) := do
  let (incomingMessagesHeader, bytes) ← IncomingMessagesHeader.decode bytes
  let (globalNetExposureAction, bytes) ← GlobalNetExposureAction.decode bytes
  let (defaultNetExposureAction, bytes) ← DefaultNetExposureAction.decode bytes
  let (defaultLongExposureAction, bytes) ← DefaultLongExposureAction.decode bytes
  let (defaultShortExposureAction, bytes) ← DefaultShortExposureAction.decode bytes
  let (defaultNetPositionAction, bytes) ← DefaultNetPositionAction.decode bytes
  let (defaultLongPositionAction, bytes) ← DefaultLongPositionAction.decode bytes
  let (defaultShortPositionAction, bytes) ← DefaultShortPositionAction.decode bytes
  let (globalNetExposureLimit, bytes) ← Alpha.decode 10 bytes
  let (defaultMaximumOrderQuantity, bytes) ← Alpha.decode 8 bytes
  let (defaultNetExposureLimit, bytes) ← Alpha.decode 10 bytes
  let (defaultLongExposureLimit, bytes) ← Alpha.decode 10 bytes
  let (defaultShortExposureLimit, bytes) ← Alpha.decode 10 bytes
  let (defaultNetPositionLimit, bytes) ← Alpha.decode 8 bytes
  let (defaultLongPositionLimit, bytes) ← Alpha.decode 8 bytes
  let (defaultShortPositionLimit, bytes) ← Alpha.decode 8 bytes
  pure ({ incomingMessagesHeader, globalNetExposureAction, defaultNetExposureAction, defaultLongExposureAction, defaultShortExposureAction, defaultNetPositionAction, defaultLongPositionAction, defaultShortPositionAction, globalNetExposureLimit, defaultMaximumOrderQuantity, defaultNetExposureLimit, defaultLongExposureLimit, defaultShortExposureLimit, defaultNetPositionLimit, defaultLongPositionLimit, defaultShortPositionLimit }, bytes)

@[simp] theorem encode_length (message : SetGlobalRiskLimits) : (encode message).length = 101 := by
  unfold encode
  simp only [List.length_append, IncomingMessagesHeader.encode_length, GlobalNetExposureAction.encode_length, DefaultNetExposureAction.encode_length, DefaultLongExposureAction.encode_length, DefaultShortExposureAction.encode_length, DefaultNetPositionAction.encode_length, DefaultLongPositionAction.encode_length, DefaultShortPositionAction.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : SetGlobalRiskLimits) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SetGlobalRiskLimits) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, IncomingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, GlobalNetExposureAction.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DefaultNetExposureAction.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DefaultLongExposureAction.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DefaultShortExposureAction.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DefaultNetPositionAction.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DefaultLongPositionAction.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DefaultShortPositionAction.decode_encode, some_bind]
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

end SetGlobalRiskLimits

/-- Order Entry: 181 bytes -/
structure OrderEntry where
  incomingMessagesHeader : IncomingMessagesHeader
  group : Alpha 2
  instrument : Alpha 4
  priceType : PriceType
  verbSide : VerbSide
  quantity : Alpha 8
  price : Alpha 10
  specialPriceTerm : SpecialPriceTerm
  additionalPrice : Alpha 10
  quantityTerm : QuantityTerm
  additionalQuantity : Alpha 8
  durationType : DurationType
  gtdDate : Alpha 8
  executingParticipant : Alpha 4
  filler1 : Alpha 1
  clearingData : ClearingData
  ownerData : OwnerData
  antiWashId : Alpha 8
  antiWashInstruction : AntiWashInstruction
  filler20 : Alpha 20
  deriving DecidableEq, Repr

namespace OrderEntry

def encode (message : OrderEntry) : List UInt8 :=
  IncomingMessagesHeader.encode message.incomingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (PriceType.encode message.priceType
    ++ (VerbSide.encode message.verbSide
    ++ (Alpha.encode message.quantity
    ++ (Alpha.encode message.price
    ++ (SpecialPriceTerm.encode message.specialPriceTerm
    ++ (Alpha.encode message.additionalPrice
    ++ (QuantityTerm.encode message.quantityTerm
    ++ (Alpha.encode message.additionalQuantity
    ++ (DurationType.encode message.durationType
    ++ (Alpha.encode message.gtdDate
    ++ (Alpha.encode message.executingParticipant
    ++ (Alpha.encode message.filler1
    ++ (ClearingData.encode message.clearingData
    ++ (OwnerData.encode message.ownerData
    ++ (Alpha.encode message.antiWashId
    ++ (AntiWashInstruction.encode message.antiWashInstruction
    ++ (Alpha.encode message.filler20)))))))))))))))))))

def decode (bytes : List UInt8) : Option (OrderEntry × List UInt8) := do
  let (incomingMessagesHeader, bytes) ← IncomingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (priceType, bytes) ← PriceType.decode bytes
  let (verbSide, bytes) ← VerbSide.decode bytes
  let (quantity, bytes) ← Alpha.decode 8 bytes
  let (price, bytes) ← Alpha.decode 10 bytes
  let (specialPriceTerm, bytes) ← SpecialPriceTerm.decode bytes
  let (additionalPrice, bytes) ← Alpha.decode 10 bytes
  let (quantityTerm, bytes) ← QuantityTerm.decode bytes
  let (additionalQuantity, bytes) ← Alpha.decode 8 bytes
  let (durationType, bytes) ← DurationType.decode bytes
  let (gtdDate, bytes) ← Alpha.decode 8 bytes
  let (executingParticipant, bytes) ← Alpha.decode 4 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (clearingData, bytes) ← ClearingData.decode bytes
  let (ownerData, bytes) ← OwnerData.decode bytes
  let (antiWashId, bytes) ← Alpha.decode 8 bytes
  let (antiWashInstruction, bytes) ← AntiWashInstruction.decode bytes
  let (filler20, bytes) ← Alpha.decode 20 bytes
  pure ({ incomingMessagesHeader, group, instrument, priceType, verbSide, quantity, price, specialPriceTerm, additionalPrice, quantityTerm, additionalQuantity, durationType, gtdDate, executingParticipant, filler1, clearingData, ownerData, antiWashId, antiWashInstruction, filler20 }, bytes)

@[simp] theorem encode_length (message : OrderEntry) : (encode message).length = 181 := by
  unfold encode
  simp only [List.length_append, IncomingMessagesHeader.encode_length, Alpha.encode_length, PriceType.encode_length, VerbSide.encode_length, SpecialPriceTerm.encode_length, QuantityTerm.encode_length, DurationType.encode_length, ClearingData.encode_length, OwnerData.encode_length, AntiWashInstruction.encode_length]

theorem encode_length_pos (message : OrderEntry) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderEntry) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, IncomingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PriceType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, VerbSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SpecialPriceTerm.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, QuantityTerm.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DurationType.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AntiWashInstruction.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderEntry

/-- Order Modification: 190 bytes -/
structure OrderModification where
  incomingMessagesHeader : IncomingMessagesHeader
  group : Alpha 2
  instrument : Alpha 4
  priceType : PriceType
  verbSide : VerbSide
  quantitySign : QuantitySign
  quantity : Alpha 8
  price : Alpha 10
  specialPriceTerm : SpecialPriceTerm
  additionalPrice : Alpha 10
  quantityTerm : QuantityTerm
  additionalQuantity : Alpha 8
  durationType : DurationType
  gtdDate : Alpha 8
  filler4 : Alpha 4
  filler1 : Alpha 1
  modifiedOrderId : Alpha 8
  clearingData : ClearingData
  ownerData : OwnerData
  antiWashId : Alpha 8
  antiWashInstruction : AntiWashInstruction
  filler20 : Alpha 20
  deriving DecidableEq, Repr

namespace OrderModification

def encode (message : OrderModification) : List UInt8 :=
  IncomingMessagesHeader.encode message.incomingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (PriceType.encode message.priceType
    ++ (VerbSide.encode message.verbSide
    ++ (QuantitySign.encode message.quantitySign
    ++ (Alpha.encode message.quantity
    ++ (Alpha.encode message.price
    ++ (SpecialPriceTerm.encode message.specialPriceTerm
    ++ (Alpha.encode message.additionalPrice
    ++ (QuantityTerm.encode message.quantityTerm
    ++ (Alpha.encode message.additionalQuantity
    ++ (DurationType.encode message.durationType
    ++ (Alpha.encode message.gtdDate
    ++ (Alpha.encode message.filler4
    ++ (Alpha.encode message.filler1
    ++ (Alpha.encode message.modifiedOrderId
    ++ (ClearingData.encode message.clearingData
    ++ (OwnerData.encode message.ownerData
    ++ (Alpha.encode message.antiWashId
    ++ (AntiWashInstruction.encode message.antiWashInstruction
    ++ (Alpha.encode message.filler20)))))))))))))))))))))

def decode (bytes : List UInt8) : Option (OrderModification × List UInt8) := do
  let (incomingMessagesHeader, bytes) ← IncomingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (priceType, bytes) ← PriceType.decode bytes
  let (verbSide, bytes) ← VerbSide.decode bytes
  let (quantitySign, bytes) ← QuantitySign.decode bytes
  let (quantity, bytes) ← Alpha.decode 8 bytes
  let (price, bytes) ← Alpha.decode 10 bytes
  let (specialPriceTerm, bytes) ← SpecialPriceTerm.decode bytes
  let (additionalPrice, bytes) ← Alpha.decode 10 bytes
  let (quantityTerm, bytes) ← QuantityTerm.decode bytes
  let (additionalQuantity, bytes) ← Alpha.decode 8 bytes
  let (durationType, bytes) ← DurationType.decode bytes
  let (gtdDate, bytes) ← Alpha.decode 8 bytes
  let (filler4, bytes) ← Alpha.decode 4 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (modifiedOrderId, bytes) ← Alpha.decode 8 bytes
  let (clearingData, bytes) ← ClearingData.decode bytes
  let (ownerData, bytes) ← OwnerData.decode bytes
  let (antiWashId, bytes) ← Alpha.decode 8 bytes
  let (antiWashInstruction, bytes) ← AntiWashInstruction.decode bytes
  let (filler20, bytes) ← Alpha.decode 20 bytes
  pure ({ incomingMessagesHeader, group, instrument, priceType, verbSide, quantitySign, quantity, price, specialPriceTerm, additionalPrice, quantityTerm, additionalQuantity, durationType, gtdDate, filler4, filler1, modifiedOrderId, clearingData, ownerData, antiWashId, antiWashInstruction, filler20 }, bytes)

@[simp] theorem encode_length (message : OrderModification) : (encode message).length = 190 := by
  unfold encode
  simp only [List.length_append, IncomingMessagesHeader.encode_length, Alpha.encode_length, PriceType.encode_length, VerbSide.encode_length, QuantitySign.encode_length, SpecialPriceTerm.encode_length, QuantityTerm.encode_length, DurationType.encode_length, ClearingData.encode_length, OwnerData.encode_length, AntiWashInstruction.encode_length]

theorem encode_length_pos (message : OrderModification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderModification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, IncomingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PriceType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, VerbSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, QuantitySign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SpecialPriceTerm.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, QuantityTerm.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DurationType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AntiWashInstruction.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderModification

/-- New Strategy Instrument Leg Definition Repeating Block: 16 bytes -/
structure NewStrategyInstrumentLegDefinitionRepeatingBlock where
  legGroup : Alpha 2
  legInstrument : Alpha 4
  legVerb : LegVerb
  filler1 : Alpha 1
  legQuantityRatio : Alpha 8
  deriving DecidableEq, Repr

namespace NewStrategyInstrumentLegDefinitionRepeatingBlock

def encode (message : NewStrategyInstrumentLegDefinitionRepeatingBlock) : List UInt8 :=
  Alpha.encode message.legGroup
    ++ (Alpha.encode message.legInstrument
    ++ (LegVerb.encode message.legVerb
    ++ (Alpha.encode message.filler1
    ++ (Alpha.encode message.legQuantityRatio))))

def decode (bytes : List UInt8) : Option (NewStrategyInstrumentLegDefinitionRepeatingBlock × List UInt8) := do
  let (legGroup, bytes) ← Alpha.decode 2 bytes
  let (legInstrument, bytes) ← Alpha.decode 4 bytes
  let (legVerb, bytes) ← LegVerb.decode bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (legQuantityRatio, bytes) ← Alpha.decode 8 bytes
  pure ({ legGroup, legInstrument, legVerb, filler1, legQuantityRatio }, bytes)

@[simp] theorem encode_length (message : NewStrategyInstrumentLegDefinitionRepeatingBlock) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, LegVerb.encode_length]

theorem encode_length_pos (message : NewStrategyInstrumentLegDefinitionRepeatingBlock) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewStrategyInstrumentLegDefinitionRepeatingBlock) (rest : List UInt8) :
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

end NewStrategyInstrumentLegDefinitionRepeatingBlock

/-- New Strategy Instrument -/
structure NewStrategyInstrument where
  incomingMessagesHeader : IncomingMessagesHeader
  newStrategyInstrumentLegDefinitionRepeatingBlock : Digited 2 NewStrategyInstrumentLegDefinitionRepeatingBlock
  deriving DecidableEq, Repr

namespace NewStrategyInstrument

def encode (message : NewStrategyInstrument) : List UInt8 :=
  IncomingMessagesHeader.encode message.incomingMessagesHeader
    ++ (encodeDigits 2 message.newStrategyInstrumentLegDefinitionRepeatingBlock.val.length
    ++ (encodeMany NewStrategyInstrumentLegDefinitionRepeatingBlock.encode message.newStrategyInstrumentLegDefinitionRepeatingBlock.val))

def decode (bytes : List UInt8) : Option (NewStrategyInstrument × List UInt8) := do
  let (incomingMessagesHeader, bytes) ← IncomingMessagesHeader.decode bytes
  let (numberOfLegs, bytes) ← decodeDigits 2 bytes
  let (newStrategyInstrumentLegDefinitionRepeatingBlock_, bytes) ← decodeMany NewStrategyInstrumentLegDefinitionRepeatingBlock.decode numberOfLegs bytes
  if fits_newStrategyInstrumentLegDefinitionRepeatingBlock : newStrategyInstrumentLegDefinitionRepeatingBlock_.length < 10 ^ 2 then
    pure ({ incomingMessagesHeader, newStrategyInstrumentLegDefinitionRepeatingBlock := ⟨newStrategyInstrumentLegDefinitionRepeatingBlock_, fits_newStrategyInstrumentLegDefinitionRepeatingBlock⟩ }, bytes)
  else none

theorem encode_length_pos (message : NewStrategyInstrument) : (encode message).length > 0 := by
  unfold encode
  simp only [IncomingMessagesHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : NewStrategyInstrument) : (encode message).length ≤ 1608 := by
  have bound_newStrategyInstrumentLegDefinitionRepeatingBlock := message.newStrategyInstrumentLegDefinitionRepeatingBlock.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, IncomingMessagesHeader.encode_length, encodeDigits_length, encodeMany_length_const NewStrategyInstrumentLegDefinitionRepeatingBlock.encode 16 NewStrategyInstrumentLegDefinitionRepeatingBlock.encode_length]
  omega

@[simp] theorem decode_encode (message : NewStrategyInstrument) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, IncomingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.newStrategyInstrumentLegDefinitionRepeatingBlock.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany NewStrategyInstrumentLegDefinitionRepeatingBlock.encode NewStrategyInstrumentLegDefinitionRepeatingBlock.decode NewStrategyInstrumentLegDefinitionRepeatingBlock.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.newStrategyInstrumentLegDefinitionRepeatingBlock.length_lt]
  rfl

end NewStrategyInstrument

/-- Buying Clearing Data: 20 bytes -/
structure BuyingClearingData where
  clearingInstruction : Alpha 12
  accountType : AccountType
  openClose : OpenClose
  hedgeSpec : HedgeSpec
  filler5 : Alpha 5
  deriving DecidableEq, Repr

namespace BuyingClearingData

def encode (message : BuyingClearingData) : List UInt8 :=
  Alpha.encode message.clearingInstruction
    ++ (AccountType.encode message.accountType
    ++ (OpenClose.encode message.openClose
    ++ (HedgeSpec.encode message.hedgeSpec
    ++ (Alpha.encode message.filler5))))

def decode (bytes : List UInt8) : Option (BuyingClearingData × List UInt8) := do
  let (clearingInstruction, bytes) ← Alpha.decode 12 bytes
  let (accountType, bytes) ← AccountType.decode bytes
  let (openClose, bytes) ← OpenClose.decode bytes
  let (hedgeSpec, bytes) ← HedgeSpec.decode bytes
  let (filler5, bytes) ← Alpha.decode 5 bytes
  pure ({ clearingInstruction, accountType, openClose, hedgeSpec, filler5 }, bytes)

@[simp] theorem encode_length (message : BuyingClearingData) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, AccountType.encode_length, OpenClose.encode_length, HedgeSpec.encode_length]

theorem encode_length_pos (message : BuyingClearingData) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BuyingClearingData) (rest : List UInt8) :
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

end BuyingClearingData

/-- Selling Clearing Data: 20 bytes -/
structure SellingClearingData where
  clearingInstruction : Alpha 12
  accountType : AccountType
  openClose : OpenClose
  hedgeSpec : HedgeSpec
  filler5 : Alpha 5
  deriving DecidableEq, Repr

namespace SellingClearingData

def encode (message : SellingClearingData) : List UInt8 :=
  Alpha.encode message.clearingInstruction
    ++ (AccountType.encode message.accountType
    ++ (OpenClose.encode message.openClose
    ++ (HedgeSpec.encode message.hedgeSpec
    ++ (Alpha.encode message.filler5))))

def decode (bytes : List UInt8) : Option (SellingClearingData × List UInt8) := do
  let (clearingInstruction, bytes) ← Alpha.decode 12 bytes
  let (accountType, bytes) ← AccountType.decode bytes
  let (openClose, bytes) ← OpenClose.decode bytes
  let (hedgeSpec, bytes) ← HedgeSpec.decode bytes
  let (filler5, bytes) ← Alpha.decode 5 bytes
  pure ({ clearingInstruction, accountType, openClose, hedgeSpec, filler5 }, bytes)

@[simp] theorem encode_length (message : SellingClearingData) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, AccountType.encode_length, OpenClose.encode_length, HedgeSpec.encode_length]

theorem encode_length_pos (message : SellingClearingData) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SellingClearingData) (rest : List UInt8) :
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

end SellingClearingData

/-- Buying Owner Data: 50 bytes -/
structure BuyingOwnerData where
  memo : Alpha 50
  deriving DecidableEq, Repr

namespace BuyingOwnerData

def encode (message : BuyingOwnerData) : List UInt8 :=
  Alpha.encode message.memo

def decode (bytes : List UInt8) : Option (BuyingOwnerData × List UInt8) := do
  let (memo, bytes) ← Alpha.decode 50 bytes
  pure ({ memo }, bytes)

@[simp] theorem encode_length (message : BuyingOwnerData) : (encode message).length = 50 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : BuyingOwnerData) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BuyingOwnerData) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end BuyingOwnerData

/-- Selling Owner Data: 50 bytes -/
structure SellingOwnerData where
  memo : Alpha 50
  deriving DecidableEq, Repr

namespace SellingOwnerData

def encode (message : SellingOwnerData) : List UInt8 :=
  Alpha.encode message.memo

def decode (bytes : List UInt8) : Option (SellingOwnerData × List UInt8) := do
  let (memo, bytes) ← Alpha.decode 50 bytes
  pure ({ memo }, bytes)

@[simp] theorem encode_length (message : SellingOwnerData) : (encode message).length = 50 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : SellingOwnerData) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SellingOwnerData) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end SellingOwnerData

/-- Cross Entry: 207 bytes -/
structure CrossEntry where
  incomingMessagesHeader : IncomingMessagesHeader
  group : Alpha 2
  instrument : Alpha 4
  filler1 : Alpha 1
  quantity : Alpha 8
  price : Alpha 10
  buyingClearingData : BuyingClearingData
  sellingClearingData : SellingClearingData
  buyingOwnerData : BuyingOwnerData
  sellingOwnerData : SellingOwnerData
  filler20 : Alpha 20
  deriving DecidableEq, Repr

namespace CrossEntry

def encode (message : CrossEntry) : List UInt8 :=
  IncomingMessagesHeader.encode message.incomingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.filler1
    ++ (Alpha.encode message.quantity
    ++ (Alpha.encode message.price
    ++ (BuyingClearingData.encode message.buyingClearingData
    ++ (SellingClearingData.encode message.sellingClearingData
    ++ (BuyingOwnerData.encode message.buyingOwnerData
    ++ (SellingOwnerData.encode message.sellingOwnerData
    ++ (Alpha.encode message.filler20))))))))))

def decode (bytes : List UInt8) : Option (CrossEntry × List UInt8) := do
  let (incomingMessagesHeader, bytes) ← IncomingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (quantity, bytes) ← Alpha.decode 8 bytes
  let (price, bytes) ← Alpha.decode 10 bytes
  let (buyingClearingData, bytes) ← BuyingClearingData.decode bytes
  let (sellingClearingData, bytes) ← SellingClearingData.decode bytes
  let (buyingOwnerData, bytes) ← BuyingOwnerData.decode bytes
  let (sellingOwnerData, bytes) ← SellingOwnerData.decode bytes
  let (filler20, bytes) ← Alpha.decode 20 bytes
  pure ({ incomingMessagesHeader, group, instrument, filler1, quantity, price, buyingClearingData, sellingClearingData, buyingOwnerData, sellingOwnerData, filler20 }, bytes)

@[simp] theorem encode_length (message : CrossEntry) : (encode message).length = 207 := by
  unfold encode
  simp only [List.length_append, IncomingMessagesHeader.encode_length, Alpha.encode_length, BuyingClearingData.encode_length, SellingClearingData.encode_length, BuyingOwnerData.encode_length, SellingOwnerData.encode_length]

theorem encode_length_pos (message : CrossEntry) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CrossEntry) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, IncomingMessagesHeader.decode_encode, some_bind]
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
  rw [List.append_assoc, BuyingClearingData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SellingClearingData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BuyingOwnerData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SellingOwnerData.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end CrossEntry

/-- Bulk Quote Price 4 Quantity 2 Occurrence: 14 bytes -/
structure BulkQuotePrice4Quantity2Occurrence where
  group : Alpha 2
  instrument : Alpha 4
  verbSide : VerbSide
  quantitySignOr : QuantitySignOr
  quantity2 : Alpha 2
  price4 : Alpha 4
  deriving DecidableEq, Repr

namespace BulkQuotePrice4Quantity2Occurrence

def encode (message : BulkQuotePrice4Quantity2Occurrence) : List UInt8 :=
  Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (VerbSide.encode message.verbSide
    ++ (QuantitySignOr.encode message.quantitySignOr
    ++ (Alpha.encode message.quantity2
    ++ (Alpha.encode message.price4)))))

def decode (bytes : List UInt8) : Option (BulkQuotePrice4Quantity2Occurrence × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (verbSide, bytes) ← VerbSide.decode bytes
  let (quantitySignOr, bytes) ← QuantitySignOr.decode bytes
  let (quantity2, bytes) ← Alpha.decode 2 bytes
  let (price4, bytes) ← Alpha.decode 4 bytes
  pure ({ group, instrument, verbSide, quantitySignOr, quantity2, price4 }, bytes)

@[simp] theorem encode_length (message : BulkQuotePrice4Quantity2Occurrence) : (encode message).length = 14 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, VerbSide.encode_length, QuantitySignOr.encode_length]

theorem encode_length_pos (message : BulkQuotePrice4Quantity2Occurrence) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BulkQuotePrice4Quantity2Occurrence) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, VerbSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, QuantitySignOr.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BulkQuotePrice4Quantity2Occurrence

/-- Bulk Quote Price 4 Quantity 2 -/
structure BulkQuotePrice4Quantity2 where
  incomingMessagesHeader : IncomingMessagesHeader
  group : Alpha 2
  quoteIdentifierOnThisGroup : Alpha 8
  bulkQuotePrice4Quantity2Occurrence : Digited 3 BulkQuotePrice4Quantity2Occurrence
  deriving DecidableEq, Repr

namespace BulkQuotePrice4Quantity2

def encode (message : BulkQuotePrice4Quantity2) : List UInt8 :=
  IncomingMessagesHeader.encode message.incomingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.quoteIdentifierOnThisGroup
    ++ (encodeDigits 3 message.bulkQuotePrice4Quantity2Occurrence.val.length
    ++ (encodeMany BulkQuotePrice4Quantity2Occurrence.encode message.bulkQuotePrice4Quantity2Occurrence.val))))

def decode (bytes : List UInt8) : Option (BulkQuotePrice4Quantity2 × List UInt8) := do
  let (incomingMessagesHeader, bytes) ← IncomingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (quoteIdentifierOnThisGroup, bytes) ← Alpha.decode 8 bytes
  let (numberOfQuotes, bytes) ← decodeDigits 3 bytes
  let (bulkQuotePrice4Quantity2Occurrence_, bytes) ← decodeMany BulkQuotePrice4Quantity2Occurrence.decode numberOfQuotes bytes
  if fits_bulkQuotePrice4Quantity2Occurrence : bulkQuotePrice4Quantity2Occurrence_.length < 10 ^ 3 then
    pure ({ incomingMessagesHeader, group, quoteIdentifierOnThisGroup, bulkQuotePrice4Quantity2Occurrence := ⟨bulkQuotePrice4Quantity2Occurrence_, fits_bulkQuotePrice4Quantity2Occurrence⟩ }, bytes)
  else none

theorem encode_length_pos (message : BulkQuotePrice4Quantity2) : (encode message).length > 0 := by
  unfold encode
  simp only [IncomingMessagesHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : BulkQuotePrice4Quantity2) : (encode message).length ≤ 14021 := by
  have bound_bulkQuotePrice4Quantity2Occurrence := message.bulkQuotePrice4Quantity2Occurrence.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, IncomingMessagesHeader.encode_length, Alpha.encode_length, encodeDigits_length, encodeMany_length_const BulkQuotePrice4Quantity2Occurrence.encode 14 BulkQuotePrice4Quantity2Occurrence.encode_length]
  omega

@[simp] theorem decode_encode (message : BulkQuotePrice4Quantity2) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, IncomingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.bulkQuotePrice4Quantity2Occurrence.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany BulkQuotePrice4Quantity2Occurrence.encode BulkQuotePrice4Quantity2Occurrence.decode BulkQuotePrice4Quantity2Occurrence.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.bulkQuotePrice4Quantity2Occurrence.length_lt]
  rfl

end BulkQuotePrice4Quantity2

/-- Bulk Quote Price 6 Quantity 2 Occurrence: 16 bytes -/
structure BulkQuotePrice6Quantity2Occurrence where
  group : Alpha 2
  instrument : Alpha 4
  verbSide : VerbSide
  quantitySignOr : QuantitySignOr
  quantity2 : Alpha 2
  price6 : Alpha 6
  deriving DecidableEq, Repr

namespace BulkQuotePrice6Quantity2Occurrence

def encode (message : BulkQuotePrice6Quantity2Occurrence) : List UInt8 :=
  Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (VerbSide.encode message.verbSide
    ++ (QuantitySignOr.encode message.quantitySignOr
    ++ (Alpha.encode message.quantity2
    ++ (Alpha.encode message.price6)))))

def decode (bytes : List UInt8) : Option (BulkQuotePrice6Quantity2Occurrence × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (verbSide, bytes) ← VerbSide.decode bytes
  let (quantitySignOr, bytes) ← QuantitySignOr.decode bytes
  let (quantity2, bytes) ← Alpha.decode 2 bytes
  let (price6, bytes) ← Alpha.decode 6 bytes
  pure ({ group, instrument, verbSide, quantitySignOr, quantity2, price6 }, bytes)

@[simp] theorem encode_length (message : BulkQuotePrice6Quantity2Occurrence) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, VerbSide.encode_length, QuantitySignOr.encode_length]

theorem encode_length_pos (message : BulkQuotePrice6Quantity2Occurrence) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BulkQuotePrice6Quantity2Occurrence) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, VerbSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, QuantitySignOr.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BulkQuotePrice6Quantity2Occurrence

/-- Bulk Quote Price 6 Quantity 2 -/
structure BulkQuotePrice6Quantity2 where
  incomingMessagesHeader : IncomingMessagesHeader
  group : Alpha 2
  quoteIdentifierOnThisGroup : Alpha 8
  bulkQuotePrice6Quantity2Occurrence : Digited 3 BulkQuotePrice6Quantity2Occurrence
  deriving DecidableEq, Repr

namespace BulkQuotePrice6Quantity2

def encode (message : BulkQuotePrice6Quantity2) : List UInt8 :=
  IncomingMessagesHeader.encode message.incomingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.quoteIdentifierOnThisGroup
    ++ (encodeDigits 3 message.bulkQuotePrice6Quantity2Occurrence.val.length
    ++ (encodeMany BulkQuotePrice6Quantity2Occurrence.encode message.bulkQuotePrice6Quantity2Occurrence.val))))

def decode (bytes : List UInt8) : Option (BulkQuotePrice6Quantity2 × List UInt8) := do
  let (incomingMessagesHeader, bytes) ← IncomingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (quoteIdentifierOnThisGroup, bytes) ← Alpha.decode 8 bytes
  let (numberOfQuotes, bytes) ← decodeDigits 3 bytes
  let (bulkQuotePrice6Quantity2Occurrence_, bytes) ← decodeMany BulkQuotePrice6Quantity2Occurrence.decode numberOfQuotes bytes
  if fits_bulkQuotePrice6Quantity2Occurrence : bulkQuotePrice6Quantity2Occurrence_.length < 10 ^ 3 then
    pure ({ incomingMessagesHeader, group, quoteIdentifierOnThisGroup, bulkQuotePrice6Quantity2Occurrence := ⟨bulkQuotePrice6Quantity2Occurrence_, fits_bulkQuotePrice6Quantity2Occurrence⟩ }, bytes)
  else none

theorem encode_length_pos (message : BulkQuotePrice6Quantity2) : (encode message).length > 0 := by
  unfold encode
  simp only [IncomingMessagesHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : BulkQuotePrice6Quantity2) : (encode message).length ≤ 16019 := by
  have bound_bulkQuotePrice6Quantity2Occurrence := message.bulkQuotePrice6Quantity2Occurrence.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, IncomingMessagesHeader.encode_length, Alpha.encode_length, encodeDigits_length, encodeMany_length_const BulkQuotePrice6Quantity2Occurrence.encode 16 BulkQuotePrice6Quantity2Occurrence.encode_length]
  omega

@[simp] theorem decode_encode (message : BulkQuotePrice6Quantity2) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, IncomingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.bulkQuotePrice6Quantity2Occurrence.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany BulkQuotePrice6Quantity2Occurrence.encode BulkQuotePrice6Quantity2Occurrence.decode BulkQuotePrice6Quantity2Occurrence.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.bulkQuotePrice6Quantity2Occurrence.length_lt]
  rfl

end BulkQuotePrice6Quantity2

/-- Bulk Quote Price 8 Quantity 2 Occurrence: 18 bytes -/
structure BulkQuotePrice8Quantity2Occurrence where
  group : Alpha 2
  instrument : Alpha 4
  verbSide : VerbSide
  quantitySignOr : QuantitySignOr
  quantity2 : Alpha 2
  price8 : Alpha 8
  deriving DecidableEq, Repr

namespace BulkQuotePrice8Quantity2Occurrence

def encode (message : BulkQuotePrice8Quantity2Occurrence) : List UInt8 :=
  Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (VerbSide.encode message.verbSide
    ++ (QuantitySignOr.encode message.quantitySignOr
    ++ (Alpha.encode message.quantity2
    ++ (Alpha.encode message.price8)))))

def decode (bytes : List UInt8) : Option (BulkQuotePrice8Quantity2Occurrence × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (verbSide, bytes) ← VerbSide.decode bytes
  let (quantitySignOr, bytes) ← QuantitySignOr.decode bytes
  let (quantity2, bytes) ← Alpha.decode 2 bytes
  let (price8, bytes) ← Alpha.decode 8 bytes
  pure ({ group, instrument, verbSide, quantitySignOr, quantity2, price8 }, bytes)

@[simp] theorem encode_length (message : BulkQuotePrice8Quantity2Occurrence) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, VerbSide.encode_length, QuantitySignOr.encode_length]

theorem encode_length_pos (message : BulkQuotePrice8Quantity2Occurrence) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BulkQuotePrice8Quantity2Occurrence) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, VerbSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, QuantitySignOr.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BulkQuotePrice8Quantity2Occurrence

/-- Bulk Quote Price 8 Quantity 2 -/
structure BulkQuotePrice8Quantity2 where
  incomingMessagesHeader : IncomingMessagesHeader
  group : Alpha 2
  quoteIdentifierOnThisGroup : Alpha 8
  bulkQuotePrice8Quantity2Occurrence : Digited 3 BulkQuotePrice8Quantity2Occurrence
  deriving DecidableEq, Repr

namespace BulkQuotePrice8Quantity2

def encode (message : BulkQuotePrice8Quantity2) : List UInt8 :=
  IncomingMessagesHeader.encode message.incomingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.quoteIdentifierOnThisGroup
    ++ (encodeDigits 3 message.bulkQuotePrice8Quantity2Occurrence.val.length
    ++ (encodeMany BulkQuotePrice8Quantity2Occurrence.encode message.bulkQuotePrice8Quantity2Occurrence.val))))

def decode (bytes : List UInt8) : Option (BulkQuotePrice8Quantity2 × List UInt8) := do
  let (incomingMessagesHeader, bytes) ← IncomingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (quoteIdentifierOnThisGroup, bytes) ← Alpha.decode 8 bytes
  let (numberOfQuotes, bytes) ← decodeDigits 3 bytes
  let (bulkQuotePrice8Quantity2Occurrence_, bytes) ← decodeMany BulkQuotePrice8Quantity2Occurrence.decode numberOfQuotes bytes
  if fits_bulkQuotePrice8Quantity2Occurrence : bulkQuotePrice8Quantity2Occurrence_.length < 10 ^ 3 then
    pure ({ incomingMessagesHeader, group, quoteIdentifierOnThisGroup, bulkQuotePrice8Quantity2Occurrence := ⟨bulkQuotePrice8Quantity2Occurrence_, fits_bulkQuotePrice8Quantity2Occurrence⟩ }, bytes)
  else none

theorem encode_length_pos (message : BulkQuotePrice8Quantity2) : (encode message).length > 0 := by
  unfold encode
  simp only [IncomingMessagesHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : BulkQuotePrice8Quantity2) : (encode message).length ≤ 18017 := by
  have bound_bulkQuotePrice8Quantity2Occurrence := message.bulkQuotePrice8Quantity2Occurrence.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, IncomingMessagesHeader.encode_length, Alpha.encode_length, encodeDigits_length, encodeMany_length_const BulkQuotePrice8Quantity2Occurrence.encode 18 BulkQuotePrice8Quantity2Occurrence.encode_length]
  omega

@[simp] theorem decode_encode (message : BulkQuotePrice8Quantity2) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, IncomingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.bulkQuotePrice8Quantity2Occurrence.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany BulkQuotePrice8Quantity2Occurrence.encode BulkQuotePrice8Quantity2Occurrence.decode BulkQuotePrice8Quantity2Occurrence.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.bulkQuotePrice8Quantity2Occurrence.length_lt]
  rfl

end BulkQuotePrice8Quantity2

/-- Bulk Quote Price 10 Quantity 2 Occurrence: 20 bytes -/
structure BulkQuotePrice10Quantity2Occurrence where
  group : Alpha 2
  instrument : Alpha 4
  verbSide : VerbSide
  quantitySignOr : QuantitySignOr
  quantity2 : Alpha 2
  price : Alpha 10
  deriving DecidableEq, Repr

namespace BulkQuotePrice10Quantity2Occurrence

def encode (message : BulkQuotePrice10Quantity2Occurrence) : List UInt8 :=
  Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (VerbSide.encode message.verbSide
    ++ (QuantitySignOr.encode message.quantitySignOr
    ++ (Alpha.encode message.quantity2
    ++ (Alpha.encode message.price)))))

def decode (bytes : List UInt8) : Option (BulkQuotePrice10Quantity2Occurrence × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (verbSide, bytes) ← VerbSide.decode bytes
  let (quantitySignOr, bytes) ← QuantitySignOr.decode bytes
  let (quantity2, bytes) ← Alpha.decode 2 bytes
  let (price, bytes) ← Alpha.decode 10 bytes
  pure ({ group, instrument, verbSide, quantitySignOr, quantity2, price }, bytes)

@[simp] theorem encode_length (message : BulkQuotePrice10Quantity2Occurrence) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, VerbSide.encode_length, QuantitySignOr.encode_length]

theorem encode_length_pos (message : BulkQuotePrice10Quantity2Occurrence) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BulkQuotePrice10Quantity2Occurrence) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, VerbSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, QuantitySignOr.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BulkQuotePrice10Quantity2Occurrence

/-- Bulk Quote Price 10 Quantity 2 -/
structure BulkQuotePrice10Quantity2 where
  incomingMessagesHeader : IncomingMessagesHeader
  group : Alpha 2
  quoteIdentifierOnThisGroup : Alpha 8
  bulkQuotePrice10Quantity2Occurrence : Digited 3 BulkQuotePrice10Quantity2Occurrence
  deriving DecidableEq, Repr

namespace BulkQuotePrice10Quantity2

def encode (message : BulkQuotePrice10Quantity2) : List UInt8 :=
  IncomingMessagesHeader.encode message.incomingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.quoteIdentifierOnThisGroup
    ++ (encodeDigits 3 message.bulkQuotePrice10Quantity2Occurrence.val.length
    ++ (encodeMany BulkQuotePrice10Quantity2Occurrence.encode message.bulkQuotePrice10Quantity2Occurrence.val))))

def decode (bytes : List UInt8) : Option (BulkQuotePrice10Quantity2 × List UInt8) := do
  let (incomingMessagesHeader, bytes) ← IncomingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (quoteIdentifierOnThisGroup, bytes) ← Alpha.decode 8 bytes
  let (numberOfQuotes, bytes) ← decodeDigits 3 bytes
  let (bulkQuotePrice10Quantity2Occurrence_, bytes) ← decodeMany BulkQuotePrice10Quantity2Occurrence.decode numberOfQuotes bytes
  if fits_bulkQuotePrice10Quantity2Occurrence : bulkQuotePrice10Quantity2Occurrence_.length < 10 ^ 3 then
    pure ({ incomingMessagesHeader, group, quoteIdentifierOnThisGroup, bulkQuotePrice10Quantity2Occurrence := ⟨bulkQuotePrice10Quantity2Occurrence_, fits_bulkQuotePrice10Quantity2Occurrence⟩ }, bytes)
  else none

theorem encode_length_pos (message : BulkQuotePrice10Quantity2) : (encode message).length > 0 := by
  unfold encode
  simp only [IncomingMessagesHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : BulkQuotePrice10Quantity2) : (encode message).length ≤ 20015 := by
  have bound_bulkQuotePrice10Quantity2Occurrence := message.bulkQuotePrice10Quantity2Occurrence.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, IncomingMessagesHeader.encode_length, Alpha.encode_length, encodeDigits_length, encodeMany_length_const BulkQuotePrice10Quantity2Occurrence.encode 20 BulkQuotePrice10Quantity2Occurrence.encode_length]
  omega

@[simp] theorem decode_encode (message : BulkQuotePrice10Quantity2) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, IncomingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.bulkQuotePrice10Quantity2Occurrence.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany BulkQuotePrice10Quantity2Occurrence.encode BulkQuotePrice10Quantity2Occurrence.decode BulkQuotePrice10Quantity2Occurrence.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.bulkQuotePrice10Quantity2Occurrence.length_lt]
  rfl

end BulkQuotePrice10Quantity2

/-- Bulk Quote Price 4 Quantity 4 Occurrence: 16 bytes -/
structure BulkQuotePrice4Quantity4Occurrence where
  group : Alpha 2
  instrument : Alpha 4
  verbSide : VerbSide
  quantitySignOr : QuantitySignOr
  quantity4 : Alpha 4
  price4 : Alpha 4
  deriving DecidableEq, Repr

namespace BulkQuotePrice4Quantity4Occurrence

def encode (message : BulkQuotePrice4Quantity4Occurrence) : List UInt8 :=
  Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (VerbSide.encode message.verbSide
    ++ (QuantitySignOr.encode message.quantitySignOr
    ++ (Alpha.encode message.quantity4
    ++ (Alpha.encode message.price4)))))

def decode (bytes : List UInt8) : Option (BulkQuotePrice4Quantity4Occurrence × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (verbSide, bytes) ← VerbSide.decode bytes
  let (quantitySignOr, bytes) ← QuantitySignOr.decode bytes
  let (quantity4, bytes) ← Alpha.decode 4 bytes
  let (price4, bytes) ← Alpha.decode 4 bytes
  pure ({ group, instrument, verbSide, quantitySignOr, quantity4, price4 }, bytes)

@[simp] theorem encode_length (message : BulkQuotePrice4Quantity4Occurrence) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, VerbSide.encode_length, QuantitySignOr.encode_length]

theorem encode_length_pos (message : BulkQuotePrice4Quantity4Occurrence) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BulkQuotePrice4Quantity4Occurrence) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, VerbSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, QuantitySignOr.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BulkQuotePrice4Quantity4Occurrence

/-- Bulk Quote Price 4 Quantity 4 -/
structure BulkQuotePrice4Quantity4 where
  incomingMessagesHeader : IncomingMessagesHeader
  group : Alpha 2
  quoteIdentifierOnThisGroup : Alpha 8
  bulkQuotePrice4Quantity4Occurrence : Digited 3 BulkQuotePrice4Quantity4Occurrence
  deriving DecidableEq, Repr

namespace BulkQuotePrice4Quantity4

def encode (message : BulkQuotePrice4Quantity4) : List UInt8 :=
  IncomingMessagesHeader.encode message.incomingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.quoteIdentifierOnThisGroup
    ++ (encodeDigits 3 message.bulkQuotePrice4Quantity4Occurrence.val.length
    ++ (encodeMany BulkQuotePrice4Quantity4Occurrence.encode message.bulkQuotePrice4Quantity4Occurrence.val))))

def decode (bytes : List UInt8) : Option (BulkQuotePrice4Quantity4 × List UInt8) := do
  let (incomingMessagesHeader, bytes) ← IncomingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (quoteIdentifierOnThisGroup, bytes) ← Alpha.decode 8 bytes
  let (numberOfQuotes, bytes) ← decodeDigits 3 bytes
  let (bulkQuotePrice4Quantity4Occurrence_, bytes) ← decodeMany BulkQuotePrice4Quantity4Occurrence.decode numberOfQuotes bytes
  if fits_bulkQuotePrice4Quantity4Occurrence : bulkQuotePrice4Quantity4Occurrence_.length < 10 ^ 3 then
    pure ({ incomingMessagesHeader, group, quoteIdentifierOnThisGroup, bulkQuotePrice4Quantity4Occurrence := ⟨bulkQuotePrice4Quantity4Occurrence_, fits_bulkQuotePrice4Quantity4Occurrence⟩ }, bytes)
  else none

theorem encode_length_pos (message : BulkQuotePrice4Quantity4) : (encode message).length > 0 := by
  unfold encode
  simp only [IncomingMessagesHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : BulkQuotePrice4Quantity4) : (encode message).length ≤ 16019 := by
  have bound_bulkQuotePrice4Quantity4Occurrence := message.bulkQuotePrice4Quantity4Occurrence.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, IncomingMessagesHeader.encode_length, Alpha.encode_length, encodeDigits_length, encodeMany_length_const BulkQuotePrice4Quantity4Occurrence.encode 16 BulkQuotePrice4Quantity4Occurrence.encode_length]
  omega

@[simp] theorem decode_encode (message : BulkQuotePrice4Quantity4) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, IncomingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.bulkQuotePrice4Quantity4Occurrence.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany BulkQuotePrice4Quantity4Occurrence.encode BulkQuotePrice4Quantity4Occurrence.decode BulkQuotePrice4Quantity4Occurrence.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.bulkQuotePrice4Quantity4Occurrence.length_lt]
  rfl

end BulkQuotePrice4Quantity4

/-- Bulk Quote Price 6 Quantity 4 Occurrence: 18 bytes -/
structure BulkQuotePrice6Quantity4Occurrence where
  group : Alpha 2
  instrument : Alpha 4
  verbSide : VerbSide
  quantitySignOr : QuantitySignOr
  quantity4 : Alpha 4
  price6 : Alpha 6
  deriving DecidableEq, Repr

namespace BulkQuotePrice6Quantity4Occurrence

def encode (message : BulkQuotePrice6Quantity4Occurrence) : List UInt8 :=
  Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (VerbSide.encode message.verbSide
    ++ (QuantitySignOr.encode message.quantitySignOr
    ++ (Alpha.encode message.quantity4
    ++ (Alpha.encode message.price6)))))

def decode (bytes : List UInt8) : Option (BulkQuotePrice6Quantity4Occurrence × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (verbSide, bytes) ← VerbSide.decode bytes
  let (quantitySignOr, bytes) ← QuantitySignOr.decode bytes
  let (quantity4, bytes) ← Alpha.decode 4 bytes
  let (price6, bytes) ← Alpha.decode 6 bytes
  pure ({ group, instrument, verbSide, quantitySignOr, quantity4, price6 }, bytes)

@[simp] theorem encode_length (message : BulkQuotePrice6Quantity4Occurrence) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, VerbSide.encode_length, QuantitySignOr.encode_length]

theorem encode_length_pos (message : BulkQuotePrice6Quantity4Occurrence) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BulkQuotePrice6Quantity4Occurrence) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, VerbSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, QuantitySignOr.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BulkQuotePrice6Quantity4Occurrence

/-- Bulk Quote Price 6 Quantity 4 -/
structure BulkQuotePrice6Quantity4 where
  incomingMessagesHeader : IncomingMessagesHeader
  group : Alpha 2
  quoteIdentifierOnThisGroup : Alpha 8
  bulkQuotePrice6Quantity4Occurrence : Digited 3 BulkQuotePrice6Quantity4Occurrence
  deriving DecidableEq, Repr

namespace BulkQuotePrice6Quantity4

def encode (message : BulkQuotePrice6Quantity4) : List UInt8 :=
  IncomingMessagesHeader.encode message.incomingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.quoteIdentifierOnThisGroup
    ++ (encodeDigits 3 message.bulkQuotePrice6Quantity4Occurrence.val.length
    ++ (encodeMany BulkQuotePrice6Quantity4Occurrence.encode message.bulkQuotePrice6Quantity4Occurrence.val))))

def decode (bytes : List UInt8) : Option (BulkQuotePrice6Quantity4 × List UInt8) := do
  let (incomingMessagesHeader, bytes) ← IncomingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (quoteIdentifierOnThisGroup, bytes) ← Alpha.decode 8 bytes
  let (numberOfQuotes, bytes) ← decodeDigits 3 bytes
  let (bulkQuotePrice6Quantity4Occurrence_, bytes) ← decodeMany BulkQuotePrice6Quantity4Occurrence.decode numberOfQuotes bytes
  if fits_bulkQuotePrice6Quantity4Occurrence : bulkQuotePrice6Quantity4Occurrence_.length < 10 ^ 3 then
    pure ({ incomingMessagesHeader, group, quoteIdentifierOnThisGroup, bulkQuotePrice6Quantity4Occurrence := ⟨bulkQuotePrice6Quantity4Occurrence_, fits_bulkQuotePrice6Quantity4Occurrence⟩ }, bytes)
  else none

theorem encode_length_pos (message : BulkQuotePrice6Quantity4) : (encode message).length > 0 := by
  unfold encode
  simp only [IncomingMessagesHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : BulkQuotePrice6Quantity4) : (encode message).length ≤ 18017 := by
  have bound_bulkQuotePrice6Quantity4Occurrence := message.bulkQuotePrice6Quantity4Occurrence.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, IncomingMessagesHeader.encode_length, Alpha.encode_length, encodeDigits_length, encodeMany_length_const BulkQuotePrice6Quantity4Occurrence.encode 18 BulkQuotePrice6Quantity4Occurrence.encode_length]
  omega

@[simp] theorem decode_encode (message : BulkQuotePrice6Quantity4) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, IncomingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.bulkQuotePrice6Quantity4Occurrence.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany BulkQuotePrice6Quantity4Occurrence.encode BulkQuotePrice6Quantity4Occurrence.decode BulkQuotePrice6Quantity4Occurrence.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.bulkQuotePrice6Quantity4Occurrence.length_lt]
  rfl

end BulkQuotePrice6Quantity4

/-- Bulk Quote Price 8 Quantity 4 Occurrence: 20 bytes -/
structure BulkQuotePrice8Quantity4Occurrence where
  group : Alpha 2
  instrument : Alpha 4
  verbSide : VerbSide
  quantitySignOr : QuantitySignOr
  quantity4 : Alpha 4
  price8 : Alpha 8
  deriving DecidableEq, Repr

namespace BulkQuotePrice8Quantity4Occurrence

def encode (message : BulkQuotePrice8Quantity4Occurrence) : List UInt8 :=
  Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (VerbSide.encode message.verbSide
    ++ (QuantitySignOr.encode message.quantitySignOr
    ++ (Alpha.encode message.quantity4
    ++ (Alpha.encode message.price8)))))

def decode (bytes : List UInt8) : Option (BulkQuotePrice8Quantity4Occurrence × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (verbSide, bytes) ← VerbSide.decode bytes
  let (quantitySignOr, bytes) ← QuantitySignOr.decode bytes
  let (quantity4, bytes) ← Alpha.decode 4 bytes
  let (price8, bytes) ← Alpha.decode 8 bytes
  pure ({ group, instrument, verbSide, quantitySignOr, quantity4, price8 }, bytes)

@[simp] theorem encode_length (message : BulkQuotePrice8Quantity4Occurrence) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, VerbSide.encode_length, QuantitySignOr.encode_length]

theorem encode_length_pos (message : BulkQuotePrice8Quantity4Occurrence) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BulkQuotePrice8Quantity4Occurrence) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, VerbSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, QuantitySignOr.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BulkQuotePrice8Quantity4Occurrence

/-- Bulk Quote Price 8 Quantity 4 -/
structure BulkQuotePrice8Quantity4 where
  incomingMessagesHeader : IncomingMessagesHeader
  group : Alpha 2
  quoteIdentifierOnThisGroup : Alpha 8
  bulkQuotePrice8Quantity4Occurrence : Digited 3 BulkQuotePrice8Quantity4Occurrence
  deriving DecidableEq, Repr

namespace BulkQuotePrice8Quantity4

def encode (message : BulkQuotePrice8Quantity4) : List UInt8 :=
  IncomingMessagesHeader.encode message.incomingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.quoteIdentifierOnThisGroup
    ++ (encodeDigits 3 message.bulkQuotePrice8Quantity4Occurrence.val.length
    ++ (encodeMany BulkQuotePrice8Quantity4Occurrence.encode message.bulkQuotePrice8Quantity4Occurrence.val))))

def decode (bytes : List UInt8) : Option (BulkQuotePrice8Quantity4 × List UInt8) := do
  let (incomingMessagesHeader, bytes) ← IncomingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (quoteIdentifierOnThisGroup, bytes) ← Alpha.decode 8 bytes
  let (numberOfQuotes, bytes) ← decodeDigits 3 bytes
  let (bulkQuotePrice8Quantity4Occurrence_, bytes) ← decodeMany BulkQuotePrice8Quantity4Occurrence.decode numberOfQuotes bytes
  if fits_bulkQuotePrice8Quantity4Occurrence : bulkQuotePrice8Quantity4Occurrence_.length < 10 ^ 3 then
    pure ({ incomingMessagesHeader, group, quoteIdentifierOnThisGroup, bulkQuotePrice8Quantity4Occurrence := ⟨bulkQuotePrice8Quantity4Occurrence_, fits_bulkQuotePrice8Quantity4Occurrence⟩ }, bytes)
  else none

theorem encode_length_pos (message : BulkQuotePrice8Quantity4) : (encode message).length > 0 := by
  unfold encode
  simp only [IncomingMessagesHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : BulkQuotePrice8Quantity4) : (encode message).length ≤ 20015 := by
  have bound_bulkQuotePrice8Quantity4Occurrence := message.bulkQuotePrice8Quantity4Occurrence.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, IncomingMessagesHeader.encode_length, Alpha.encode_length, encodeDigits_length, encodeMany_length_const BulkQuotePrice8Quantity4Occurrence.encode 20 BulkQuotePrice8Quantity4Occurrence.encode_length]
  omega

@[simp] theorem decode_encode (message : BulkQuotePrice8Quantity4) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, IncomingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.bulkQuotePrice8Quantity4Occurrence.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany BulkQuotePrice8Quantity4Occurrence.encode BulkQuotePrice8Quantity4Occurrence.decode BulkQuotePrice8Quantity4Occurrence.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.bulkQuotePrice8Quantity4Occurrence.length_lt]
  rfl

end BulkQuotePrice8Quantity4

/-- Bulk Quote Price 10 Quantity 4 Occurrence: 22 bytes -/
structure BulkQuotePrice10Quantity4Occurrence where
  group : Alpha 2
  instrument : Alpha 4
  verbSide : VerbSide
  quantitySignOr : QuantitySignOr
  quantity4 : Alpha 4
  price : Alpha 10
  deriving DecidableEq, Repr

namespace BulkQuotePrice10Quantity4Occurrence

def encode (message : BulkQuotePrice10Quantity4Occurrence) : List UInt8 :=
  Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (VerbSide.encode message.verbSide
    ++ (QuantitySignOr.encode message.quantitySignOr
    ++ (Alpha.encode message.quantity4
    ++ (Alpha.encode message.price)))))

def decode (bytes : List UInt8) : Option (BulkQuotePrice10Quantity4Occurrence × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (verbSide, bytes) ← VerbSide.decode bytes
  let (quantitySignOr, bytes) ← QuantitySignOr.decode bytes
  let (quantity4, bytes) ← Alpha.decode 4 bytes
  let (price, bytes) ← Alpha.decode 10 bytes
  pure ({ group, instrument, verbSide, quantitySignOr, quantity4, price }, bytes)

@[simp] theorem encode_length (message : BulkQuotePrice10Quantity4Occurrence) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, VerbSide.encode_length, QuantitySignOr.encode_length]

theorem encode_length_pos (message : BulkQuotePrice10Quantity4Occurrence) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BulkQuotePrice10Quantity4Occurrence) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, VerbSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, QuantitySignOr.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BulkQuotePrice10Quantity4Occurrence

/-- Bulk Quote Price 10 Quantity 4 -/
structure BulkQuotePrice10Quantity4 where
  incomingMessagesHeader : IncomingMessagesHeader
  group : Alpha 2
  quoteIdentifierOnThisGroup : Alpha 8
  bulkQuotePrice10Quantity4Occurrence : Digited 3 BulkQuotePrice10Quantity4Occurrence
  deriving DecidableEq, Repr

namespace BulkQuotePrice10Quantity4

def encode (message : BulkQuotePrice10Quantity4) : List UInt8 :=
  IncomingMessagesHeader.encode message.incomingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.quoteIdentifierOnThisGroup
    ++ (encodeDigits 3 message.bulkQuotePrice10Quantity4Occurrence.val.length
    ++ (encodeMany BulkQuotePrice10Quantity4Occurrence.encode message.bulkQuotePrice10Quantity4Occurrence.val))))

def decode (bytes : List UInt8) : Option (BulkQuotePrice10Quantity4 × List UInt8) := do
  let (incomingMessagesHeader, bytes) ← IncomingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (quoteIdentifierOnThisGroup, bytes) ← Alpha.decode 8 bytes
  let (numberOfQuotes, bytes) ← decodeDigits 3 bytes
  let (bulkQuotePrice10Quantity4Occurrence_, bytes) ← decodeMany BulkQuotePrice10Quantity4Occurrence.decode numberOfQuotes bytes
  if fits_bulkQuotePrice10Quantity4Occurrence : bulkQuotePrice10Quantity4Occurrence_.length < 10 ^ 3 then
    pure ({ incomingMessagesHeader, group, quoteIdentifierOnThisGroup, bulkQuotePrice10Quantity4Occurrence := ⟨bulkQuotePrice10Quantity4Occurrence_, fits_bulkQuotePrice10Quantity4Occurrence⟩ }, bytes)
  else none

theorem encode_length_pos (message : BulkQuotePrice10Quantity4) : (encode message).length > 0 := by
  unfold encode
  simp only [IncomingMessagesHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : BulkQuotePrice10Quantity4) : (encode message).length ≤ 22013 := by
  have bound_bulkQuotePrice10Quantity4Occurrence := message.bulkQuotePrice10Quantity4Occurrence.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, IncomingMessagesHeader.encode_length, Alpha.encode_length, encodeDigits_length, encodeMany_length_const BulkQuotePrice10Quantity4Occurrence.encode 22 BulkQuotePrice10Quantity4Occurrence.encode_length]
  omega

@[simp] theorem decode_encode (message : BulkQuotePrice10Quantity4) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, IncomingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.bulkQuotePrice10Quantity4Occurrence.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany BulkQuotePrice10Quantity4Occurrence.encode BulkQuotePrice10Quantity4Occurrence.decode BulkQuotePrice10Quantity4Occurrence.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.bulkQuotePrice10Quantity4Occurrence.length_lt]
  rfl

end BulkQuotePrice10Quantity4

/-- Bulk Quote Price 4 Quantity 6 Occurrence: 18 bytes -/
structure BulkQuotePrice4Quantity6Occurrence where
  group : Alpha 2
  instrument : Alpha 4
  verbSide : VerbSide
  quantitySignOr : QuantitySignOr
  quantity6 : Alpha 6
  price4 : Alpha 4
  deriving DecidableEq, Repr

namespace BulkQuotePrice4Quantity6Occurrence

def encode (message : BulkQuotePrice4Quantity6Occurrence) : List UInt8 :=
  Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (VerbSide.encode message.verbSide
    ++ (QuantitySignOr.encode message.quantitySignOr
    ++ (Alpha.encode message.quantity6
    ++ (Alpha.encode message.price4)))))

def decode (bytes : List UInt8) : Option (BulkQuotePrice4Quantity6Occurrence × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (verbSide, bytes) ← VerbSide.decode bytes
  let (quantitySignOr, bytes) ← QuantitySignOr.decode bytes
  let (quantity6, bytes) ← Alpha.decode 6 bytes
  let (price4, bytes) ← Alpha.decode 4 bytes
  pure ({ group, instrument, verbSide, quantitySignOr, quantity6, price4 }, bytes)

@[simp] theorem encode_length (message : BulkQuotePrice4Quantity6Occurrence) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, VerbSide.encode_length, QuantitySignOr.encode_length]

theorem encode_length_pos (message : BulkQuotePrice4Quantity6Occurrence) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BulkQuotePrice4Quantity6Occurrence) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, VerbSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, QuantitySignOr.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BulkQuotePrice4Quantity6Occurrence

/-- Bulk Quote Price 4 Quantity 6 -/
structure BulkQuotePrice4Quantity6 where
  incomingMessagesHeader : IncomingMessagesHeader
  group : Alpha 2
  quoteIdentifierOnThisGroup : Alpha 8
  bulkQuotePrice4Quantity6Occurrence : Digited 3 BulkQuotePrice4Quantity6Occurrence
  deriving DecidableEq, Repr

namespace BulkQuotePrice4Quantity6

def encode (message : BulkQuotePrice4Quantity6) : List UInt8 :=
  IncomingMessagesHeader.encode message.incomingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.quoteIdentifierOnThisGroup
    ++ (encodeDigits 3 message.bulkQuotePrice4Quantity6Occurrence.val.length
    ++ (encodeMany BulkQuotePrice4Quantity6Occurrence.encode message.bulkQuotePrice4Quantity6Occurrence.val))))

def decode (bytes : List UInt8) : Option (BulkQuotePrice4Quantity6 × List UInt8) := do
  let (incomingMessagesHeader, bytes) ← IncomingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (quoteIdentifierOnThisGroup, bytes) ← Alpha.decode 8 bytes
  let (numberOfQuotes, bytes) ← decodeDigits 3 bytes
  let (bulkQuotePrice4Quantity6Occurrence_, bytes) ← decodeMany BulkQuotePrice4Quantity6Occurrence.decode numberOfQuotes bytes
  if fits_bulkQuotePrice4Quantity6Occurrence : bulkQuotePrice4Quantity6Occurrence_.length < 10 ^ 3 then
    pure ({ incomingMessagesHeader, group, quoteIdentifierOnThisGroup, bulkQuotePrice4Quantity6Occurrence := ⟨bulkQuotePrice4Quantity6Occurrence_, fits_bulkQuotePrice4Quantity6Occurrence⟩ }, bytes)
  else none

theorem encode_length_pos (message : BulkQuotePrice4Quantity6) : (encode message).length > 0 := by
  unfold encode
  simp only [IncomingMessagesHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : BulkQuotePrice4Quantity6) : (encode message).length ≤ 18017 := by
  have bound_bulkQuotePrice4Quantity6Occurrence := message.bulkQuotePrice4Quantity6Occurrence.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, IncomingMessagesHeader.encode_length, Alpha.encode_length, encodeDigits_length, encodeMany_length_const BulkQuotePrice4Quantity6Occurrence.encode 18 BulkQuotePrice4Quantity6Occurrence.encode_length]
  omega

@[simp] theorem decode_encode (message : BulkQuotePrice4Quantity6) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, IncomingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.bulkQuotePrice4Quantity6Occurrence.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany BulkQuotePrice4Quantity6Occurrence.encode BulkQuotePrice4Quantity6Occurrence.decode BulkQuotePrice4Quantity6Occurrence.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.bulkQuotePrice4Quantity6Occurrence.length_lt]
  rfl

end BulkQuotePrice4Quantity6

/-- Bulk Quote Price 6 Quantity 6 Occurrence: 20 bytes -/
structure BulkQuotePrice6Quantity6Occurrence where
  group : Alpha 2
  instrument : Alpha 4
  verbSide : VerbSide
  quantitySignOr : QuantitySignOr
  quantity6 : Alpha 6
  price6 : Alpha 6
  deriving DecidableEq, Repr

namespace BulkQuotePrice6Quantity6Occurrence

def encode (message : BulkQuotePrice6Quantity6Occurrence) : List UInt8 :=
  Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (VerbSide.encode message.verbSide
    ++ (QuantitySignOr.encode message.quantitySignOr
    ++ (Alpha.encode message.quantity6
    ++ (Alpha.encode message.price6)))))

def decode (bytes : List UInt8) : Option (BulkQuotePrice6Quantity6Occurrence × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (verbSide, bytes) ← VerbSide.decode bytes
  let (quantitySignOr, bytes) ← QuantitySignOr.decode bytes
  let (quantity6, bytes) ← Alpha.decode 6 bytes
  let (price6, bytes) ← Alpha.decode 6 bytes
  pure ({ group, instrument, verbSide, quantitySignOr, quantity6, price6 }, bytes)

@[simp] theorem encode_length (message : BulkQuotePrice6Quantity6Occurrence) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, VerbSide.encode_length, QuantitySignOr.encode_length]

theorem encode_length_pos (message : BulkQuotePrice6Quantity6Occurrence) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BulkQuotePrice6Quantity6Occurrence) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, VerbSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, QuantitySignOr.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BulkQuotePrice6Quantity6Occurrence

/-- Bulk Quote Price 6 Quantity 6 -/
structure BulkQuotePrice6Quantity6 where
  incomingMessagesHeader : IncomingMessagesHeader
  group : Alpha 2
  quoteIdentifierOnThisGroup : Alpha 8
  bulkQuotePrice6Quantity6Occurrence : Digited 3 BulkQuotePrice6Quantity6Occurrence
  deriving DecidableEq, Repr

namespace BulkQuotePrice6Quantity6

def encode (message : BulkQuotePrice6Quantity6) : List UInt8 :=
  IncomingMessagesHeader.encode message.incomingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.quoteIdentifierOnThisGroup
    ++ (encodeDigits 3 message.bulkQuotePrice6Quantity6Occurrence.val.length
    ++ (encodeMany BulkQuotePrice6Quantity6Occurrence.encode message.bulkQuotePrice6Quantity6Occurrence.val))))

def decode (bytes : List UInt8) : Option (BulkQuotePrice6Quantity6 × List UInt8) := do
  let (incomingMessagesHeader, bytes) ← IncomingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (quoteIdentifierOnThisGroup, bytes) ← Alpha.decode 8 bytes
  let (numberOfQuotes, bytes) ← decodeDigits 3 bytes
  let (bulkQuotePrice6Quantity6Occurrence_, bytes) ← decodeMany BulkQuotePrice6Quantity6Occurrence.decode numberOfQuotes bytes
  if fits_bulkQuotePrice6Quantity6Occurrence : bulkQuotePrice6Quantity6Occurrence_.length < 10 ^ 3 then
    pure ({ incomingMessagesHeader, group, quoteIdentifierOnThisGroup, bulkQuotePrice6Quantity6Occurrence := ⟨bulkQuotePrice6Quantity6Occurrence_, fits_bulkQuotePrice6Quantity6Occurrence⟩ }, bytes)
  else none

theorem encode_length_pos (message : BulkQuotePrice6Quantity6) : (encode message).length > 0 := by
  unfold encode
  simp only [IncomingMessagesHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : BulkQuotePrice6Quantity6) : (encode message).length ≤ 20015 := by
  have bound_bulkQuotePrice6Quantity6Occurrence := message.bulkQuotePrice6Quantity6Occurrence.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, IncomingMessagesHeader.encode_length, Alpha.encode_length, encodeDigits_length, encodeMany_length_const BulkQuotePrice6Quantity6Occurrence.encode 20 BulkQuotePrice6Quantity6Occurrence.encode_length]
  omega

@[simp] theorem decode_encode (message : BulkQuotePrice6Quantity6) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, IncomingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.bulkQuotePrice6Quantity6Occurrence.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany BulkQuotePrice6Quantity6Occurrence.encode BulkQuotePrice6Quantity6Occurrence.decode BulkQuotePrice6Quantity6Occurrence.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.bulkQuotePrice6Quantity6Occurrence.length_lt]
  rfl

end BulkQuotePrice6Quantity6

/-- Bulk Quote Price 8 Quantity 6 Occurrence: 22 bytes -/
structure BulkQuotePrice8Quantity6Occurrence where
  group : Alpha 2
  instrument : Alpha 4
  verbSide : VerbSide
  quantitySignOr : QuantitySignOr
  quantity6 : Alpha 6
  price8 : Alpha 8
  deriving DecidableEq, Repr

namespace BulkQuotePrice8Quantity6Occurrence

def encode (message : BulkQuotePrice8Quantity6Occurrence) : List UInt8 :=
  Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (VerbSide.encode message.verbSide
    ++ (QuantitySignOr.encode message.quantitySignOr
    ++ (Alpha.encode message.quantity6
    ++ (Alpha.encode message.price8)))))

def decode (bytes : List UInt8) : Option (BulkQuotePrice8Quantity6Occurrence × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (verbSide, bytes) ← VerbSide.decode bytes
  let (quantitySignOr, bytes) ← QuantitySignOr.decode bytes
  let (quantity6, bytes) ← Alpha.decode 6 bytes
  let (price8, bytes) ← Alpha.decode 8 bytes
  pure ({ group, instrument, verbSide, quantitySignOr, quantity6, price8 }, bytes)

@[simp] theorem encode_length (message : BulkQuotePrice8Quantity6Occurrence) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, VerbSide.encode_length, QuantitySignOr.encode_length]

theorem encode_length_pos (message : BulkQuotePrice8Quantity6Occurrence) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BulkQuotePrice8Quantity6Occurrence) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, VerbSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, QuantitySignOr.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BulkQuotePrice8Quantity6Occurrence

/-- Bulk Quote Price 8 Quantity 6 -/
structure BulkQuotePrice8Quantity6 where
  incomingMessagesHeader : IncomingMessagesHeader
  group : Alpha 2
  quoteIdentifierOnThisGroup : Alpha 8
  bulkQuotePrice8Quantity6Occurrence : Digited 3 BulkQuotePrice8Quantity6Occurrence
  deriving DecidableEq, Repr

namespace BulkQuotePrice8Quantity6

def encode (message : BulkQuotePrice8Quantity6) : List UInt8 :=
  IncomingMessagesHeader.encode message.incomingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.quoteIdentifierOnThisGroup
    ++ (encodeDigits 3 message.bulkQuotePrice8Quantity6Occurrence.val.length
    ++ (encodeMany BulkQuotePrice8Quantity6Occurrence.encode message.bulkQuotePrice8Quantity6Occurrence.val))))

def decode (bytes : List UInt8) : Option (BulkQuotePrice8Quantity6 × List UInt8) := do
  let (incomingMessagesHeader, bytes) ← IncomingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (quoteIdentifierOnThisGroup, bytes) ← Alpha.decode 8 bytes
  let (numberOfQuotes, bytes) ← decodeDigits 3 bytes
  let (bulkQuotePrice8Quantity6Occurrence_, bytes) ← decodeMany BulkQuotePrice8Quantity6Occurrence.decode numberOfQuotes bytes
  if fits_bulkQuotePrice8Quantity6Occurrence : bulkQuotePrice8Quantity6Occurrence_.length < 10 ^ 3 then
    pure ({ incomingMessagesHeader, group, quoteIdentifierOnThisGroup, bulkQuotePrice8Quantity6Occurrence := ⟨bulkQuotePrice8Quantity6Occurrence_, fits_bulkQuotePrice8Quantity6Occurrence⟩ }, bytes)
  else none

theorem encode_length_pos (message : BulkQuotePrice8Quantity6) : (encode message).length > 0 := by
  unfold encode
  simp only [IncomingMessagesHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : BulkQuotePrice8Quantity6) : (encode message).length ≤ 22013 := by
  have bound_bulkQuotePrice8Quantity6Occurrence := message.bulkQuotePrice8Quantity6Occurrence.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, IncomingMessagesHeader.encode_length, Alpha.encode_length, encodeDigits_length, encodeMany_length_const BulkQuotePrice8Quantity6Occurrence.encode 22 BulkQuotePrice8Quantity6Occurrence.encode_length]
  omega

@[simp] theorem decode_encode (message : BulkQuotePrice8Quantity6) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, IncomingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.bulkQuotePrice8Quantity6Occurrence.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany BulkQuotePrice8Quantity6Occurrence.encode BulkQuotePrice8Quantity6Occurrence.decode BulkQuotePrice8Quantity6Occurrence.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.bulkQuotePrice8Quantity6Occurrence.length_lt]
  rfl

end BulkQuotePrice8Quantity6

/-- Bulk Quote Price 10 Quantity 6 Occurrence: 24 bytes -/
structure BulkQuotePrice10Quantity6Occurrence where
  group : Alpha 2
  instrument : Alpha 4
  verbSide : VerbSide
  quantitySignOr : QuantitySignOr
  quantity6 : Alpha 6
  price : Alpha 10
  deriving DecidableEq, Repr

namespace BulkQuotePrice10Quantity6Occurrence

def encode (message : BulkQuotePrice10Quantity6Occurrence) : List UInt8 :=
  Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (VerbSide.encode message.verbSide
    ++ (QuantitySignOr.encode message.quantitySignOr
    ++ (Alpha.encode message.quantity6
    ++ (Alpha.encode message.price)))))

def decode (bytes : List UInt8) : Option (BulkQuotePrice10Quantity6Occurrence × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (verbSide, bytes) ← VerbSide.decode bytes
  let (quantitySignOr, bytes) ← QuantitySignOr.decode bytes
  let (quantity6, bytes) ← Alpha.decode 6 bytes
  let (price, bytes) ← Alpha.decode 10 bytes
  pure ({ group, instrument, verbSide, quantitySignOr, quantity6, price }, bytes)

@[simp] theorem encode_length (message : BulkQuotePrice10Quantity6Occurrence) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, VerbSide.encode_length, QuantitySignOr.encode_length]

theorem encode_length_pos (message : BulkQuotePrice10Quantity6Occurrence) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BulkQuotePrice10Quantity6Occurrence) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, VerbSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, QuantitySignOr.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BulkQuotePrice10Quantity6Occurrence

/-- Bulk Quote Price 10 Quantity 6 -/
structure BulkQuotePrice10Quantity6 where
  incomingMessagesHeader : IncomingMessagesHeader
  group : Alpha 2
  quoteIdentifierOnThisGroup : Alpha 8
  bulkQuotePrice10Quantity6Occurrence : Digited 3 BulkQuotePrice10Quantity6Occurrence
  deriving DecidableEq, Repr

namespace BulkQuotePrice10Quantity6

def encode (message : BulkQuotePrice10Quantity6) : List UInt8 :=
  IncomingMessagesHeader.encode message.incomingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.quoteIdentifierOnThisGroup
    ++ (encodeDigits 3 message.bulkQuotePrice10Quantity6Occurrence.val.length
    ++ (encodeMany BulkQuotePrice10Quantity6Occurrence.encode message.bulkQuotePrice10Quantity6Occurrence.val))))

def decode (bytes : List UInt8) : Option (BulkQuotePrice10Quantity6 × List UInt8) := do
  let (incomingMessagesHeader, bytes) ← IncomingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (quoteIdentifierOnThisGroup, bytes) ← Alpha.decode 8 bytes
  let (numberOfQuotes, bytes) ← decodeDigits 3 bytes
  let (bulkQuotePrice10Quantity6Occurrence_, bytes) ← decodeMany BulkQuotePrice10Quantity6Occurrence.decode numberOfQuotes bytes
  if fits_bulkQuotePrice10Quantity6Occurrence : bulkQuotePrice10Quantity6Occurrence_.length < 10 ^ 3 then
    pure ({ incomingMessagesHeader, group, quoteIdentifierOnThisGroup, bulkQuotePrice10Quantity6Occurrence := ⟨bulkQuotePrice10Quantity6Occurrence_, fits_bulkQuotePrice10Quantity6Occurrence⟩ }, bytes)
  else none

theorem encode_length_pos (message : BulkQuotePrice10Quantity6) : (encode message).length > 0 := by
  unfold encode
  simp only [IncomingMessagesHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : BulkQuotePrice10Quantity6) : (encode message).length ≤ 24011 := by
  have bound_bulkQuotePrice10Quantity6Occurrence := message.bulkQuotePrice10Quantity6Occurrence.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, IncomingMessagesHeader.encode_length, Alpha.encode_length, encodeDigits_length, encodeMany_length_const BulkQuotePrice10Quantity6Occurrence.encode 24 BulkQuotePrice10Quantity6Occurrence.encode_length]
  omega

@[simp] theorem decode_encode (message : BulkQuotePrice10Quantity6) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, IncomingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.bulkQuotePrice10Quantity6Occurrence.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany BulkQuotePrice10Quantity6Occurrence.encode BulkQuotePrice10Quantity6Occurrence.decode BulkQuotePrice10Quantity6Occurrence.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.bulkQuotePrice10Quantity6Occurrence.length_lt]
  rfl

end BulkQuotePrice10Quantity6

/-- Bulk Quote Price 4 Quantity 8 Occurrence: 20 bytes -/
structure BulkQuotePrice4Quantity8Occurrence where
  group : Alpha 2
  instrument : Alpha 4
  verbSide : VerbSide
  quantitySignOr : QuantitySignOr
  quantity : Alpha 8
  price4 : Alpha 4
  deriving DecidableEq, Repr

namespace BulkQuotePrice4Quantity8Occurrence

def encode (message : BulkQuotePrice4Quantity8Occurrence) : List UInt8 :=
  Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (VerbSide.encode message.verbSide
    ++ (QuantitySignOr.encode message.quantitySignOr
    ++ (Alpha.encode message.quantity
    ++ (Alpha.encode message.price4)))))

def decode (bytes : List UInt8) : Option (BulkQuotePrice4Quantity8Occurrence × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (verbSide, bytes) ← VerbSide.decode bytes
  let (quantitySignOr, bytes) ← QuantitySignOr.decode bytes
  let (quantity, bytes) ← Alpha.decode 8 bytes
  let (price4, bytes) ← Alpha.decode 4 bytes
  pure ({ group, instrument, verbSide, quantitySignOr, quantity, price4 }, bytes)

@[simp] theorem encode_length (message : BulkQuotePrice4Quantity8Occurrence) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, VerbSide.encode_length, QuantitySignOr.encode_length]

theorem encode_length_pos (message : BulkQuotePrice4Quantity8Occurrence) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BulkQuotePrice4Quantity8Occurrence) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, VerbSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, QuantitySignOr.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BulkQuotePrice4Quantity8Occurrence

/-- Bulk Quote Price 4 Quantity 8 -/
structure BulkQuotePrice4Quantity8 where
  incomingMessagesHeader : IncomingMessagesHeader
  group : Alpha 2
  quoteIdentifierOnThisGroup : Alpha 8
  bulkQuotePrice4Quantity8Occurrence : Digited 3 BulkQuotePrice4Quantity8Occurrence
  deriving DecidableEq, Repr

namespace BulkQuotePrice4Quantity8

def encode (message : BulkQuotePrice4Quantity8) : List UInt8 :=
  IncomingMessagesHeader.encode message.incomingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.quoteIdentifierOnThisGroup
    ++ (encodeDigits 3 message.bulkQuotePrice4Quantity8Occurrence.val.length
    ++ (encodeMany BulkQuotePrice4Quantity8Occurrence.encode message.bulkQuotePrice4Quantity8Occurrence.val))))

def decode (bytes : List UInt8) : Option (BulkQuotePrice4Quantity8 × List UInt8) := do
  let (incomingMessagesHeader, bytes) ← IncomingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (quoteIdentifierOnThisGroup, bytes) ← Alpha.decode 8 bytes
  let (numberOfQuotes, bytes) ← decodeDigits 3 bytes
  let (bulkQuotePrice4Quantity8Occurrence_, bytes) ← decodeMany BulkQuotePrice4Quantity8Occurrence.decode numberOfQuotes bytes
  if fits_bulkQuotePrice4Quantity8Occurrence : bulkQuotePrice4Quantity8Occurrence_.length < 10 ^ 3 then
    pure ({ incomingMessagesHeader, group, quoteIdentifierOnThisGroup, bulkQuotePrice4Quantity8Occurrence := ⟨bulkQuotePrice4Quantity8Occurrence_, fits_bulkQuotePrice4Quantity8Occurrence⟩ }, bytes)
  else none

theorem encode_length_pos (message : BulkQuotePrice4Quantity8) : (encode message).length > 0 := by
  unfold encode
  simp only [IncomingMessagesHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : BulkQuotePrice4Quantity8) : (encode message).length ≤ 20015 := by
  have bound_bulkQuotePrice4Quantity8Occurrence := message.bulkQuotePrice4Quantity8Occurrence.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, IncomingMessagesHeader.encode_length, Alpha.encode_length, encodeDigits_length, encodeMany_length_const BulkQuotePrice4Quantity8Occurrence.encode 20 BulkQuotePrice4Quantity8Occurrence.encode_length]
  omega

@[simp] theorem decode_encode (message : BulkQuotePrice4Quantity8) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, IncomingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.bulkQuotePrice4Quantity8Occurrence.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany BulkQuotePrice4Quantity8Occurrence.encode BulkQuotePrice4Quantity8Occurrence.decode BulkQuotePrice4Quantity8Occurrence.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.bulkQuotePrice4Quantity8Occurrence.length_lt]
  rfl

end BulkQuotePrice4Quantity8

/-- Bulk Quote Price 6 Quantity 8 Occurrence: 22 bytes -/
structure BulkQuotePrice6Quantity8Occurrence where
  group : Alpha 2
  instrument : Alpha 4
  verbSide : VerbSide
  quantitySignOr : QuantitySignOr
  quantity : Alpha 8
  price6 : Alpha 6
  deriving DecidableEq, Repr

namespace BulkQuotePrice6Quantity8Occurrence

def encode (message : BulkQuotePrice6Quantity8Occurrence) : List UInt8 :=
  Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (VerbSide.encode message.verbSide
    ++ (QuantitySignOr.encode message.quantitySignOr
    ++ (Alpha.encode message.quantity
    ++ (Alpha.encode message.price6)))))

def decode (bytes : List UInt8) : Option (BulkQuotePrice6Quantity8Occurrence × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (verbSide, bytes) ← VerbSide.decode bytes
  let (quantitySignOr, bytes) ← QuantitySignOr.decode bytes
  let (quantity, bytes) ← Alpha.decode 8 bytes
  let (price6, bytes) ← Alpha.decode 6 bytes
  pure ({ group, instrument, verbSide, quantitySignOr, quantity, price6 }, bytes)

@[simp] theorem encode_length (message : BulkQuotePrice6Quantity8Occurrence) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, VerbSide.encode_length, QuantitySignOr.encode_length]

theorem encode_length_pos (message : BulkQuotePrice6Quantity8Occurrence) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BulkQuotePrice6Quantity8Occurrence) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, VerbSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, QuantitySignOr.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BulkQuotePrice6Quantity8Occurrence

/-- Bulk Quote Price 6 Quantity 8 -/
structure BulkQuotePrice6Quantity8 where
  incomingMessagesHeader : IncomingMessagesHeader
  group : Alpha 2
  quoteIdentifierOnThisGroup : Alpha 8
  bulkQuotePrice6Quantity8Occurrence : Digited 3 BulkQuotePrice6Quantity8Occurrence
  deriving DecidableEq, Repr

namespace BulkQuotePrice6Quantity8

def encode (message : BulkQuotePrice6Quantity8) : List UInt8 :=
  IncomingMessagesHeader.encode message.incomingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.quoteIdentifierOnThisGroup
    ++ (encodeDigits 3 message.bulkQuotePrice6Quantity8Occurrence.val.length
    ++ (encodeMany BulkQuotePrice6Quantity8Occurrence.encode message.bulkQuotePrice6Quantity8Occurrence.val))))

def decode (bytes : List UInt8) : Option (BulkQuotePrice6Quantity8 × List UInt8) := do
  let (incomingMessagesHeader, bytes) ← IncomingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (quoteIdentifierOnThisGroup, bytes) ← Alpha.decode 8 bytes
  let (numberOfQuotes, bytes) ← decodeDigits 3 bytes
  let (bulkQuotePrice6Quantity8Occurrence_, bytes) ← decodeMany BulkQuotePrice6Quantity8Occurrence.decode numberOfQuotes bytes
  if fits_bulkQuotePrice6Quantity8Occurrence : bulkQuotePrice6Quantity8Occurrence_.length < 10 ^ 3 then
    pure ({ incomingMessagesHeader, group, quoteIdentifierOnThisGroup, bulkQuotePrice6Quantity8Occurrence := ⟨bulkQuotePrice6Quantity8Occurrence_, fits_bulkQuotePrice6Quantity8Occurrence⟩ }, bytes)
  else none

theorem encode_length_pos (message : BulkQuotePrice6Quantity8) : (encode message).length > 0 := by
  unfold encode
  simp only [IncomingMessagesHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : BulkQuotePrice6Quantity8) : (encode message).length ≤ 22013 := by
  have bound_bulkQuotePrice6Quantity8Occurrence := message.bulkQuotePrice6Quantity8Occurrence.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, IncomingMessagesHeader.encode_length, Alpha.encode_length, encodeDigits_length, encodeMany_length_const BulkQuotePrice6Quantity8Occurrence.encode 22 BulkQuotePrice6Quantity8Occurrence.encode_length]
  omega

@[simp] theorem decode_encode (message : BulkQuotePrice6Quantity8) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, IncomingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.bulkQuotePrice6Quantity8Occurrence.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany BulkQuotePrice6Quantity8Occurrence.encode BulkQuotePrice6Quantity8Occurrence.decode BulkQuotePrice6Quantity8Occurrence.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.bulkQuotePrice6Quantity8Occurrence.length_lt]
  rfl

end BulkQuotePrice6Quantity8

/-- Bulk Quote Price 8 Quantity 8 Occurrence: 24 bytes -/
structure BulkQuotePrice8Quantity8Occurrence where
  group : Alpha 2
  instrument : Alpha 4
  verbSide : VerbSide
  quantitySignOr : QuantitySignOr
  quantity : Alpha 8
  price8 : Alpha 8
  deriving DecidableEq, Repr

namespace BulkQuotePrice8Quantity8Occurrence

def encode (message : BulkQuotePrice8Quantity8Occurrence) : List UInt8 :=
  Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (VerbSide.encode message.verbSide
    ++ (QuantitySignOr.encode message.quantitySignOr
    ++ (Alpha.encode message.quantity
    ++ (Alpha.encode message.price8)))))

def decode (bytes : List UInt8) : Option (BulkQuotePrice8Quantity8Occurrence × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (verbSide, bytes) ← VerbSide.decode bytes
  let (quantitySignOr, bytes) ← QuantitySignOr.decode bytes
  let (quantity, bytes) ← Alpha.decode 8 bytes
  let (price8, bytes) ← Alpha.decode 8 bytes
  pure ({ group, instrument, verbSide, quantitySignOr, quantity, price8 }, bytes)

@[simp] theorem encode_length (message : BulkQuotePrice8Quantity8Occurrence) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, VerbSide.encode_length, QuantitySignOr.encode_length]

theorem encode_length_pos (message : BulkQuotePrice8Quantity8Occurrence) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BulkQuotePrice8Quantity8Occurrence) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, VerbSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, QuantitySignOr.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BulkQuotePrice8Quantity8Occurrence

/-- Bulk Quote Price 8 Quantity 8 -/
structure BulkQuotePrice8Quantity8 where
  incomingMessagesHeader : IncomingMessagesHeader
  group : Alpha 2
  quoteIdentifierOnThisGroup : Alpha 8
  bulkQuotePrice8Quantity8Occurrence : Digited 3 BulkQuotePrice8Quantity8Occurrence
  deriving DecidableEq, Repr

namespace BulkQuotePrice8Quantity8

def encode (message : BulkQuotePrice8Quantity8) : List UInt8 :=
  IncomingMessagesHeader.encode message.incomingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.quoteIdentifierOnThisGroup
    ++ (encodeDigits 3 message.bulkQuotePrice8Quantity8Occurrence.val.length
    ++ (encodeMany BulkQuotePrice8Quantity8Occurrence.encode message.bulkQuotePrice8Quantity8Occurrence.val))))

def decode (bytes : List UInt8) : Option (BulkQuotePrice8Quantity8 × List UInt8) := do
  let (incomingMessagesHeader, bytes) ← IncomingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (quoteIdentifierOnThisGroup, bytes) ← Alpha.decode 8 bytes
  let (numberOfQuotes, bytes) ← decodeDigits 3 bytes
  let (bulkQuotePrice8Quantity8Occurrence_, bytes) ← decodeMany BulkQuotePrice8Quantity8Occurrence.decode numberOfQuotes bytes
  if fits_bulkQuotePrice8Quantity8Occurrence : bulkQuotePrice8Quantity8Occurrence_.length < 10 ^ 3 then
    pure ({ incomingMessagesHeader, group, quoteIdentifierOnThisGroup, bulkQuotePrice8Quantity8Occurrence := ⟨bulkQuotePrice8Quantity8Occurrence_, fits_bulkQuotePrice8Quantity8Occurrence⟩ }, bytes)
  else none

theorem encode_length_pos (message : BulkQuotePrice8Quantity8) : (encode message).length > 0 := by
  unfold encode
  simp only [IncomingMessagesHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : BulkQuotePrice8Quantity8) : (encode message).length ≤ 24011 := by
  have bound_bulkQuotePrice8Quantity8Occurrence := message.bulkQuotePrice8Quantity8Occurrence.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, IncomingMessagesHeader.encode_length, Alpha.encode_length, encodeDigits_length, encodeMany_length_const BulkQuotePrice8Quantity8Occurrence.encode 24 BulkQuotePrice8Quantity8Occurrence.encode_length]
  omega

@[simp] theorem decode_encode (message : BulkQuotePrice8Quantity8) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, IncomingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.bulkQuotePrice8Quantity8Occurrence.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany BulkQuotePrice8Quantity8Occurrence.encode BulkQuotePrice8Quantity8Occurrence.decode BulkQuotePrice8Quantity8Occurrence.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.bulkQuotePrice8Quantity8Occurrence.length_lt]
  rfl

end BulkQuotePrice8Quantity8

/-- Bulk Quote Occurrence: 26 bytes -/
structure BulkQuoteOccurrence where
  group : Alpha 2
  instrument : Alpha 4
  verbSide : VerbSide
  quantitySignOr : QuantitySignOr
  quantity : Alpha 8
  price : Alpha 10
  deriving DecidableEq, Repr

namespace BulkQuoteOccurrence

def encode (message : BulkQuoteOccurrence) : List UInt8 :=
  Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (VerbSide.encode message.verbSide
    ++ (QuantitySignOr.encode message.quantitySignOr
    ++ (Alpha.encode message.quantity
    ++ (Alpha.encode message.price)))))

def decode (bytes : List UInt8) : Option (BulkQuoteOccurrence × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (verbSide, bytes) ← VerbSide.decode bytes
  let (quantitySignOr, bytes) ← QuantitySignOr.decode bytes
  let (quantity, bytes) ← Alpha.decode 8 bytes
  let (price, bytes) ← Alpha.decode 10 bytes
  pure ({ group, instrument, verbSide, quantitySignOr, quantity, price }, bytes)

@[simp] theorem encode_length (message : BulkQuoteOccurrence) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, VerbSide.encode_length, QuantitySignOr.encode_length]

theorem encode_length_pos (message : BulkQuoteOccurrence) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BulkQuoteOccurrence) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, VerbSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, QuantitySignOr.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BulkQuoteOccurrence

/-- Bulk Quote -/
structure BulkQuote where
  incomingMessagesHeader : IncomingMessagesHeader
  group : Alpha 2
  quoteIdentifierOnThisGroup : Alpha 8
  bulkQuoteOccurrence : Digited 3 BulkQuoteOccurrence
  deriving DecidableEq, Repr

namespace BulkQuote

def encode (message : BulkQuote) : List UInt8 :=
  IncomingMessagesHeader.encode message.incomingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.quoteIdentifierOnThisGroup
    ++ (encodeDigits 3 message.bulkQuoteOccurrence.val.length
    ++ (encodeMany BulkQuoteOccurrence.encode message.bulkQuoteOccurrence.val))))

def decode (bytes : List UInt8) : Option (BulkQuote × List UInt8) := do
  let (incomingMessagesHeader, bytes) ← IncomingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (quoteIdentifierOnThisGroup, bytes) ← Alpha.decode 8 bytes
  let (numberOfQuotes, bytes) ← decodeDigits 3 bytes
  let (bulkQuoteOccurrence_, bytes) ← decodeMany BulkQuoteOccurrence.decode numberOfQuotes bytes
  if fits_bulkQuoteOccurrence : bulkQuoteOccurrence_.length < 10 ^ 3 then
    pure ({ incomingMessagesHeader, group, quoteIdentifierOnThisGroup, bulkQuoteOccurrence := ⟨bulkQuoteOccurrence_, fits_bulkQuoteOccurrence⟩ }, bytes)
  else none

theorem encode_length_pos (message : BulkQuote) : (encode message).length > 0 := by
  unfold encode
  simp only [IncomingMessagesHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : BulkQuote) : (encode message).length ≤ 26009 := by
  have bound_bulkQuoteOccurrence := message.bulkQuoteOccurrence.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, IncomingMessagesHeader.encode_length, Alpha.encode_length, encodeDigits_length, encodeMany_length_const BulkQuoteOccurrence.encode 26 BulkQuoteOccurrence.encode_length]
  omega

@[simp] theorem decode_encode (message : BulkQuote) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, IncomingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.bulkQuoteOccurrence.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany BulkQuoteOccurrence.encode BulkQuoteOccurrence.decode BulkQuoteOccurrence.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.bulkQuoteOccurrence.length_lt]
  rfl

end BulkQuote

/-- Sail Request For Quote With Side: 37 bytes -/
structure SailRequestForQuoteWithSide where
  incomingMessagesHeader : IncomingMessagesHeader
  group : Alpha 2
  instrument : Alpha 4
  quantity : Alpha 8
  marketSide : MarketSide
  deriving DecidableEq, Repr

namespace SailRequestForQuoteWithSide

def encode (message : SailRequestForQuoteWithSide) : List UInt8 :=
  IncomingMessagesHeader.encode message.incomingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.quantity
    ++ (MarketSide.encode message.marketSide))))

def decode (bytes : List UInt8) : Option (SailRequestForQuoteWithSide × List UInt8) := do
  let (incomingMessagesHeader, bytes) ← IncomingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (quantity, bytes) ← Alpha.decode 8 bytes
  let (marketSide, bytes) ← MarketSide.decode bytes
  pure ({ incomingMessagesHeader, group, instrument, quantity, marketSide }, bytes)

@[simp] theorem encode_length (message : SailRequestForQuoteWithSide) : (encode message).length = 37 := by
  unfold encode
  simp only [List.length_append, IncomingMessagesHeader.encode_length, Alpha.encode_length, MarketSide.encode_length]

theorem encode_length_pos (message : SailRequestForQuoteWithSide) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SailRequestForQuoteWithSide) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, IncomingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [MarketSide.decode_encode, some_bind]
  rfl

end SailRequestForQuoteWithSide

/-- Bulk Quote Participant Bqp Protection Subscription: 25 bytes -/
structure BulkQuoteParticipantBqpProtectionSubscription where
  incomingMessagesHeader : IncomingMessagesHeader
  group : Alpha 2
  protectionTypeAdvancedProtectionAdvancedProtectionDisabled : ProtectionTypeAdvancedProtectionAdvancedProtectionDisabled
  deriving DecidableEq, Repr

namespace BulkQuoteParticipantBqpProtectionSubscription

def encode (message : BulkQuoteParticipantBqpProtectionSubscription) : List UInt8 :=
  IncomingMessagesHeader.encode message.incomingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (ProtectionTypeAdvancedProtectionAdvancedProtectionDisabled.encode message.protectionTypeAdvancedProtectionAdvancedProtectionDisabled))

def decode (bytes : List UInt8) : Option (BulkQuoteParticipantBqpProtectionSubscription × List UInt8) := do
  let (incomingMessagesHeader, bytes) ← IncomingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (protectionTypeAdvancedProtectionAdvancedProtectionDisabled, bytes) ← ProtectionTypeAdvancedProtectionAdvancedProtectionDisabled.decode bytes
  pure ({ incomingMessagesHeader, group, protectionTypeAdvancedProtectionAdvancedProtectionDisabled }, bytes)

@[simp] theorem encode_length (message : BulkQuoteParticipantBqpProtectionSubscription) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, IncomingMessagesHeader.encode_length, Alpha.encode_length, ProtectionTypeAdvancedProtectionAdvancedProtectionDisabled.encode_length]

theorem encode_length_pos (message : BulkQuoteParticipantBqpProtectionSubscription) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BulkQuoteParticipantBqpProtectionSubscription) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, IncomingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [ProtectionTypeAdvancedProtectionAdvancedProtectionDisabled.decode_encode, some_bind]
  rfl

end BulkQuoteParticipantBqpProtectionSubscription

/-- Request For Quote: 36 bytes -/
structure RequestForQuote where
  incomingMessagesHeader : IncomingMessagesHeader
  group : Alpha 2
  instrument : Alpha 4
  quantity : Alpha 8
  deriving DecidableEq, Repr

namespace RequestForQuote

def encode (message : RequestForQuote) : List UInt8 :=
  IncomingMessagesHeader.encode message.incomingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.quantity)))

def decode (bytes : List UInt8) : Option (RequestForQuote × List UInt8) := do
  let (incomingMessagesHeader, bytes) ← IncomingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (quantity, bytes) ← Alpha.decode 8 bytes
  pure ({ incomingMessagesHeader, group, instrument, quantity }, bytes)

@[simp] theorem encode_length (message : RequestForQuote) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, IncomingMessagesHeader.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : RequestForQuote) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RequestForQuote) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, IncomingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end RequestForQuote

/-- Order Cancellation: 36 bytes -/
structure OrderCancellation where
  incomingMessagesHeader : IncomingMessagesHeader
  group : Alpha 2
  instrument : Alpha 4
  cancelledOrderId : Alpha 8
  deriving DecidableEq, Repr

namespace OrderCancellation

def encode (message : OrderCancellation) : List UInt8 :=
  IncomingMessagesHeader.encode message.incomingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.cancelledOrderId)))

def decode (bytes : List UInt8) : Option (OrderCancellation × List UInt8) := do
  let (incomingMessagesHeader, bytes) ← IncomingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (cancelledOrderId, bytes) ← Alpha.decode 8 bytes
  pure ({ incomingMessagesHeader, group, instrument, cancelledOrderId }, bytes)

@[simp] theorem encode_length (message : OrderCancellation) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, IncomingMessagesHeader.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderCancellation) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancellation) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, IncomingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderCancellation

/-- Any Firm Message, selected by Message Type -/
inductive FirmMessage where
  | userConnection (message : UserConnection) -- "TC" 0x5443
  | disconnectionInstruction (message : DisconnectionInstruction) -- "TA" 0x5441
  | heartbeatResponse (message : HeartbeatResponse) -- "TI" 0x5449
  | userDisconnection (message : UserDisconnection) -- "TD" 0x5444
  | orderRequest (message : OrderRequest) -- "AF" 0x4146
  | bulkQuoteData (message : BulkQuoteData) -- "BD" 0x4244
  | firmRiskConfig (message : FirmRiskConfig) -- "CR" 0x4352
  | globalCancellation (message : GlobalCancellation) -- "GC" 0x4743
  | userGlobalCancellation (message : UserGlobalCancellation) -- "GZ" 0x475A
  | setGroupRiskLimits (message : SetGroupRiskLimits) -- "MK" 0x4D4B
  | setGlobalRiskLimits (message : SetGlobalRiskLimits) -- "ML" 0x4D4C
  | orderEntry (message : OrderEntry) -- "OE" 0x4F45
  | orderModification (message : OrderModification) -- "OM" 0x4F4D
  | newStrategyInstrument (message : NewStrategyInstrument) -- "ON" 0x4F4E
  | crossEntry (message : CrossEntry) -- "OX" 0x4F58
  | bulkQuotePrice4Quantity2 (message : BulkQuotePrice4Quantity2) -- "QA" 0x5141
  | bulkQuotePrice6Quantity2 (message : BulkQuotePrice6Quantity2) -- "QB" 0x5142
  | bulkQuotePrice8Quantity2 (message : BulkQuotePrice8Quantity2) -- "QC" 0x5143
  | bulkQuotePrice10Quantity2 (message : BulkQuotePrice10Quantity2) -- "QD" 0x5144
  | bulkQuotePrice4Quantity4 (message : BulkQuotePrice4Quantity4) -- "QE" 0x5145
  | bulkQuotePrice6Quantity4 (message : BulkQuotePrice6Quantity4) -- "QF" 0x5146
  | bulkQuotePrice8Quantity4 (message : BulkQuotePrice8Quantity4) -- "QG" 0x5147
  | bulkQuotePrice10Quantity4 (message : BulkQuotePrice10Quantity4) -- "QH" 0x5148
  | bulkQuotePrice4Quantity6 (message : BulkQuotePrice4Quantity6) -- "QI" 0x5149
  | bulkQuotePrice6Quantity6 (message : BulkQuotePrice6Quantity6) -- "QJ" 0x514A
  | bulkQuotePrice8Quantity6 (message : BulkQuotePrice8Quantity6) -- "QK" 0x514B
  | bulkQuotePrice10Quantity6 (message : BulkQuotePrice10Quantity6) -- "QL" 0x514C
  | bulkQuotePrice4Quantity8 (message : BulkQuotePrice4Quantity8) -- "QM" 0x514D
  | bulkQuotePrice6Quantity8 (message : BulkQuotePrice6Quantity8) -- "QN" 0x514E
  | bulkQuotePrice8Quantity8 (message : BulkQuotePrice8Quantity8) -- "QO" 0x514F
  | bulkQuote (message : BulkQuote) -- "QP" 0x5150
  | sailRequestForQuoteWithSide (message : SailRequestForQuoteWithSide) -- "QS" 0x5153
  | bulkQuoteParticipantBqpProtectionSubscription (message : BulkQuoteParticipantBqpProtectionSubscription) -- "RP" 0x5250
  | requestForQuote (message : RequestForQuote) -- "RQ" 0x5251
  | orderCancellation (message : OrderCancellation) -- "XE" 0x5845
  deriving DecidableEq, Repr

namespace FirmMessage

/-- The Message Type each message is sent under -/
def tag : FirmMessage → BitVec 16
  | .userConnection _ => 21571
  | .disconnectionInstruction _ => 21569
  | .heartbeatResponse _ => 21577
  | .userDisconnection _ => 21572
  | .orderRequest _ => 16710
  | .bulkQuoteData _ => 16964
  | .firmRiskConfig _ => 17234
  | .globalCancellation _ => 18243
  | .userGlobalCancellation _ => 18266
  | .setGroupRiskLimits _ => 19787
  | .setGlobalRiskLimits _ => 19788
  | .orderEntry _ => 20293
  | .orderModification _ => 20301
  | .newStrategyInstrument _ => 20302
  | .crossEntry _ => 20312
  | .bulkQuotePrice4Quantity2 _ => 20801
  | .bulkQuotePrice6Quantity2 _ => 20802
  | .bulkQuotePrice8Quantity2 _ => 20803
  | .bulkQuotePrice10Quantity2 _ => 20804
  | .bulkQuotePrice4Quantity4 _ => 20805
  | .bulkQuotePrice6Quantity4 _ => 20806
  | .bulkQuotePrice8Quantity4 _ => 20807
  | .bulkQuotePrice10Quantity4 _ => 20808
  | .bulkQuotePrice4Quantity6 _ => 20809
  | .bulkQuotePrice6Quantity6 _ => 20810
  | .bulkQuotePrice8Quantity6 _ => 20811
  | .bulkQuotePrice10Quantity6 _ => 20812
  | .bulkQuotePrice4Quantity8 _ => 20813
  | .bulkQuotePrice6Quantity8 _ => 20814
  | .bulkQuotePrice8Quantity8 _ => 20815
  | .bulkQuote _ => 20816
  | .sailRequestForQuoteWithSide _ => 20819
  | .bulkQuoteParticipantBqpProtectionSubscription _ => 21072
  | .requestForQuote _ => 21073
  | .orderCancellation _ => 22597

def encode : FirmMessage → List UInt8
  | .userConnection message => UserConnection.encode message
  | .disconnectionInstruction message => DisconnectionInstruction.encode message
  | .heartbeatResponse message => HeartbeatResponse.encode message
  | .userDisconnection message => UserDisconnection.encode message
  | .orderRequest message => OrderRequest.encode message
  | .bulkQuoteData message => BulkQuoteData.encode message
  | .firmRiskConfig message => FirmRiskConfig.encode message
  | .globalCancellation message => GlobalCancellation.encode message
  | .userGlobalCancellation message => UserGlobalCancellation.encode message
  | .setGroupRiskLimits message => SetGroupRiskLimits.encode message
  | .setGlobalRiskLimits message => SetGlobalRiskLimits.encode message
  | .orderEntry message => OrderEntry.encode message
  | .orderModification message => OrderModification.encode message
  | .newStrategyInstrument message => NewStrategyInstrument.encode message
  | .crossEntry message => CrossEntry.encode message
  | .bulkQuotePrice4Quantity2 message => BulkQuotePrice4Quantity2.encode message
  | .bulkQuotePrice6Quantity2 message => BulkQuotePrice6Quantity2.encode message
  | .bulkQuotePrice8Quantity2 message => BulkQuotePrice8Quantity2.encode message
  | .bulkQuotePrice10Quantity2 message => BulkQuotePrice10Quantity2.encode message
  | .bulkQuotePrice4Quantity4 message => BulkQuotePrice4Quantity4.encode message
  | .bulkQuotePrice6Quantity4 message => BulkQuotePrice6Quantity4.encode message
  | .bulkQuotePrice8Quantity4 message => BulkQuotePrice8Quantity4.encode message
  | .bulkQuotePrice10Quantity4 message => BulkQuotePrice10Quantity4.encode message
  | .bulkQuotePrice4Quantity6 message => BulkQuotePrice4Quantity6.encode message
  | .bulkQuotePrice6Quantity6 message => BulkQuotePrice6Quantity6.encode message
  | .bulkQuotePrice8Quantity6 message => BulkQuotePrice8Quantity6.encode message
  | .bulkQuotePrice10Quantity6 message => BulkQuotePrice10Quantity6.encode message
  | .bulkQuotePrice4Quantity8 message => BulkQuotePrice4Quantity8.encode message
  | .bulkQuotePrice6Quantity8 message => BulkQuotePrice6Quantity8.encode message
  | .bulkQuotePrice8Quantity8 message => BulkQuotePrice8Quantity8.encode message
  | .bulkQuote message => BulkQuote.encode message
  | .sailRequestForQuoteWithSide message => SailRequestForQuoteWithSide.encode message
  | .bulkQuoteParticipantBqpProtectionSubscription message => BulkQuoteParticipantBqpProtectionSubscription.encode message
  | .requestForQuote message => RequestForQuote.encode message
  | .orderCancellation message => OrderCancellation.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : FirmMessage) : (encode message).length ≤ 3996026 := by
  cases message with
  | userConnection inner =>
    have bound_inner := UserConnection.encode_length_le inner
    simp only [encode]
    omega
  | disconnectionInstruction inner =>
    have bound_inner := DisconnectionInstruction.encode_length_le inner
    simp only [encode]
    omega
  | heartbeatResponse inner =>
    simp only [encode, HeartbeatResponse.encode_length]
    omega
  | userDisconnection inner =>
    simp only [encode, UserDisconnection.encode_length]
    omega
  | orderRequest inner =>
    simp only [encode, OrderRequest.encode_length]
    omega
  | bulkQuoteData inner =>
    simp only [encode, BulkQuoteData.encode_length]
    omega
  | firmRiskConfig inner =>
    have bound_inner := FirmRiskConfig.encode_length_le inner
    simp only [encode]
    omega
  | globalCancellation inner =>
    simp only [encode, GlobalCancellation.encode_length]
    omega
  | userGlobalCancellation inner =>
    simp only [encode, UserGlobalCancellation.encode_length]
    omega
  | setGroupRiskLimits inner =>
    have bound_inner := SetGroupRiskLimits.encode_length_le inner
    simp only [encode]
    omega
  | setGlobalRiskLimits inner =>
    simp only [encode, SetGlobalRiskLimits.encode_length]
    omega
  | orderEntry inner =>
    simp only [encode, OrderEntry.encode_length]
    omega
  | orderModification inner =>
    simp only [encode, OrderModification.encode_length]
    omega
  | newStrategyInstrument inner =>
    have bound_inner := NewStrategyInstrument.encode_length_le inner
    simp only [encode]
    omega
  | crossEntry inner =>
    simp only [encode, CrossEntry.encode_length]
    omega
  | bulkQuotePrice4Quantity2 inner =>
    have bound_inner := BulkQuotePrice4Quantity2.encode_length_le inner
    simp only [encode]
    omega
  | bulkQuotePrice6Quantity2 inner =>
    have bound_inner := BulkQuotePrice6Quantity2.encode_length_le inner
    simp only [encode]
    omega
  | bulkQuotePrice8Quantity2 inner =>
    have bound_inner := BulkQuotePrice8Quantity2.encode_length_le inner
    simp only [encode]
    omega
  | bulkQuotePrice10Quantity2 inner =>
    have bound_inner := BulkQuotePrice10Quantity2.encode_length_le inner
    simp only [encode]
    omega
  | bulkQuotePrice4Quantity4 inner =>
    have bound_inner := BulkQuotePrice4Quantity4.encode_length_le inner
    simp only [encode]
    omega
  | bulkQuotePrice6Quantity4 inner =>
    have bound_inner := BulkQuotePrice6Quantity4.encode_length_le inner
    simp only [encode]
    omega
  | bulkQuotePrice8Quantity4 inner =>
    have bound_inner := BulkQuotePrice8Quantity4.encode_length_le inner
    simp only [encode]
    omega
  | bulkQuotePrice10Quantity4 inner =>
    have bound_inner := BulkQuotePrice10Quantity4.encode_length_le inner
    simp only [encode]
    omega
  | bulkQuotePrice4Quantity6 inner =>
    have bound_inner := BulkQuotePrice4Quantity6.encode_length_le inner
    simp only [encode]
    omega
  | bulkQuotePrice6Quantity6 inner =>
    have bound_inner := BulkQuotePrice6Quantity6.encode_length_le inner
    simp only [encode]
    omega
  | bulkQuotePrice8Quantity6 inner =>
    have bound_inner := BulkQuotePrice8Quantity6.encode_length_le inner
    simp only [encode]
    omega
  | bulkQuotePrice10Quantity6 inner =>
    have bound_inner := BulkQuotePrice10Quantity6.encode_length_le inner
    simp only [encode]
    omega
  | bulkQuotePrice4Quantity8 inner =>
    have bound_inner := BulkQuotePrice4Quantity8.encode_length_le inner
    simp only [encode]
    omega
  | bulkQuotePrice6Quantity8 inner =>
    have bound_inner := BulkQuotePrice6Quantity8.encode_length_le inner
    simp only [encode]
    omega
  | bulkQuotePrice8Quantity8 inner =>
    have bound_inner := BulkQuotePrice8Quantity8.encode_length_le inner
    simp only [encode]
    omega
  | bulkQuote inner =>
    have bound_inner := BulkQuote.encode_length_le inner
    simp only [encode]
    omega
  | sailRequestForQuoteWithSide inner =>
    simp only [encode, SailRequestForQuoteWithSide.encode_length]
    omega
  | bulkQuoteParticipantBqpProtectionSubscription inner =>
    simp only [encode, BulkQuoteParticipantBqpProtectionSubscription.encode_length]
    omega
  | requestForQuote inner =>
    simp only [encode, RequestForQuote.encode_length]
    omega
  | orderCancellation inner =>
    simp only [encode, OrderCancellation.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (FirmMessage × List UInt8) :=
  if tag = 21571 then (UserConnection.decode bytes).map fun (message, rest) => (.userConnection message, rest)
  else if tag = 21569 then (DisconnectionInstruction.decode bytes).map fun (message, rest) => (.disconnectionInstruction message, rest)
  else if tag = 21577 then (HeartbeatResponse.decode bytes).map fun (message, rest) => (.heartbeatResponse message, rest)
  else if tag = 21572 then (UserDisconnection.decode bytes).map fun (message, rest) => (.userDisconnection message, rest)
  else if tag = 16710 then (OrderRequest.decode bytes).map fun (message, rest) => (.orderRequest message, rest)
  else if tag = 16964 then (BulkQuoteData.decode bytes).map fun (message, rest) => (.bulkQuoteData message, rest)
  else if tag = 17234 then (FirmRiskConfig.decode bytes).map fun (message, rest) => (.firmRiskConfig message, rest)
  else if tag = 18243 then (GlobalCancellation.decode bytes).map fun (message, rest) => (.globalCancellation message, rest)
  else if tag = 18266 then (UserGlobalCancellation.decode bytes).map fun (message, rest) => (.userGlobalCancellation message, rest)
  else if tag = 19787 then (SetGroupRiskLimits.decode bytes).map fun (message, rest) => (.setGroupRiskLimits message, rest)
  else if tag = 19788 then (SetGlobalRiskLimits.decode bytes).map fun (message, rest) => (.setGlobalRiskLimits message, rest)
  else if tag = 20293 then (OrderEntry.decode bytes).map fun (message, rest) => (.orderEntry message, rest)
  else if tag = 20301 then (OrderModification.decode bytes).map fun (message, rest) => (.orderModification message, rest)
  else if tag = 20302 then (NewStrategyInstrument.decode bytes).map fun (message, rest) => (.newStrategyInstrument message, rest)
  else if tag = 20312 then (CrossEntry.decode bytes).map fun (message, rest) => (.crossEntry message, rest)
  else if tag = 20801 then (BulkQuotePrice4Quantity2.decode bytes).map fun (message, rest) => (.bulkQuotePrice4Quantity2 message, rest)
  else if tag = 20802 then (BulkQuotePrice6Quantity2.decode bytes).map fun (message, rest) => (.bulkQuotePrice6Quantity2 message, rest)
  else if tag = 20803 then (BulkQuotePrice8Quantity2.decode bytes).map fun (message, rest) => (.bulkQuotePrice8Quantity2 message, rest)
  else if tag = 20804 then (BulkQuotePrice10Quantity2.decode bytes).map fun (message, rest) => (.bulkQuotePrice10Quantity2 message, rest)
  else if tag = 20805 then (BulkQuotePrice4Quantity4.decode bytes).map fun (message, rest) => (.bulkQuotePrice4Quantity4 message, rest)
  else if tag = 20806 then (BulkQuotePrice6Quantity4.decode bytes).map fun (message, rest) => (.bulkQuotePrice6Quantity4 message, rest)
  else if tag = 20807 then (BulkQuotePrice8Quantity4.decode bytes).map fun (message, rest) => (.bulkQuotePrice8Quantity4 message, rest)
  else if tag = 20808 then (BulkQuotePrice10Quantity4.decode bytes).map fun (message, rest) => (.bulkQuotePrice10Quantity4 message, rest)
  else if tag = 20809 then (BulkQuotePrice4Quantity6.decode bytes).map fun (message, rest) => (.bulkQuotePrice4Quantity6 message, rest)
  else if tag = 20810 then (BulkQuotePrice6Quantity6.decode bytes).map fun (message, rest) => (.bulkQuotePrice6Quantity6 message, rest)
  else if tag = 20811 then (BulkQuotePrice8Quantity6.decode bytes).map fun (message, rest) => (.bulkQuotePrice8Quantity6 message, rest)
  else if tag = 20812 then (BulkQuotePrice10Quantity6.decode bytes).map fun (message, rest) => (.bulkQuotePrice10Quantity6 message, rest)
  else if tag = 20813 then (BulkQuotePrice4Quantity8.decode bytes).map fun (message, rest) => (.bulkQuotePrice4Quantity8 message, rest)
  else if tag = 20814 then (BulkQuotePrice6Quantity8.decode bytes).map fun (message, rest) => (.bulkQuotePrice6Quantity8 message, rest)
  else if tag = 20815 then (BulkQuotePrice8Quantity8.decode bytes).map fun (message, rest) => (.bulkQuotePrice8Quantity8 message, rest)
  else if tag = 20816 then (BulkQuote.decode bytes).map fun (message, rest) => (.bulkQuote message, rest)
  else if tag = 20819 then (SailRequestForQuoteWithSide.decode bytes).map fun (message, rest) => (.sailRequestForQuoteWithSide message, rest)
  else if tag = 21072 then (BulkQuoteParticipantBqpProtectionSubscription.decode bytes).map fun (message, rest) => (.bulkQuoteParticipantBqpProtectionSubscription message, rest)
  else if tag = 21073 then (RequestForQuote.decode bytes).map fun (message, rest) => (.requestForQuote message, rest)
  else if tag = 22597 then (OrderCancellation.decode bytes).map fun (message, rest) => (.orderCancellation message, rest)
  else none

@[simp] theorem decode_encode (message : FirmMessage) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end FirmMessage

/-- Firm Packet -/
structure FirmPacket where
  messageLength : BitVec 32
  firmMessage : FirmMessage
  endOfText : BitVec 8
  alignmentPadding : Capped 3
  deriving DecidableEq, Repr

namespace FirmPacket

def encode (message : FirmPacket) : List UInt8 :=
  encodeUIntLE 4 message.messageLength
    ++ (encodeUInt 2 (FirmMessage.tag message.firmMessage)
    ++ (FirmMessage.encode message.firmMessage
    ++ (encodeUInt 1 message.endOfText
    ++ (message.alignmentPadding.val))))

def decode (bytes : List UInt8) : Option FirmPacket := do
  let (messageLength, bytes) ← decodeUIntLE 4 bytes
  let (messageType, bytes) ← decodeUInt 2 bytes
  let (firmMessage, bytes) ← FirmMessage.decode messageType bytes
  let (endOfText, bytes) ← decodeUInt 1 bytes
  let alignmentPadding_ := bytes
  if fits_alignmentPadding : alignmentPadding_.length ≤ 3 then
    pure { messageLength, firmMessage, endOfText, alignmentPadding := ⟨alignmentPadding_, fits_alignmentPadding⟩ }
  else none

theorem encode_length_pos (message : FirmPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : FirmPacket) : (encode message).length ≤ 3996036 := by
  have bound_alignmentPadding := message.alignmentPadding.length_le
  unfold encode
  cases message.firmMessage with
  | userConnection inner =>
    have bound_inner := UserConnection.encode_length_le inner
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
    omega
  | disconnectionInstruction inner =>
    have bound_inner := DisconnectionInstruction.encode_length_le inner
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
    omega
  | heartbeatResponse inner =>
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, HeartbeatResponse.encode_length]
    omega
  | userDisconnection inner =>
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, UserDisconnection.encode_length]
    omega
  | orderRequest inner =>
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, OrderRequest.encode_length]
    omega
  | bulkQuoteData inner =>
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, BulkQuoteData.encode_length]
    omega
  | firmRiskConfig inner =>
    have bound_inner := FirmRiskConfig.encode_length_le inner
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
    omega
  | globalCancellation inner =>
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, GlobalCancellation.encode_length]
    omega
  | userGlobalCancellation inner =>
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, UserGlobalCancellation.encode_length]
    omega
  | setGroupRiskLimits inner =>
    have bound_inner := SetGroupRiskLimits.encode_length_le inner
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
    omega
  | setGlobalRiskLimits inner =>
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, SetGlobalRiskLimits.encode_length]
    omega
  | orderEntry inner =>
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, OrderEntry.encode_length]
    omega
  | orderModification inner =>
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, OrderModification.encode_length]
    omega
  | newStrategyInstrument inner =>
    have bound_inner := NewStrategyInstrument.encode_length_le inner
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
    omega
  | crossEntry inner =>
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, CrossEntry.encode_length]
    omega
  | bulkQuotePrice4Quantity2 inner =>
    have bound_inner := BulkQuotePrice4Quantity2.encode_length_le inner
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
    omega
  | bulkQuotePrice6Quantity2 inner =>
    have bound_inner := BulkQuotePrice6Quantity2.encode_length_le inner
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
    omega
  | bulkQuotePrice8Quantity2 inner =>
    have bound_inner := BulkQuotePrice8Quantity2.encode_length_le inner
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
    omega
  | bulkQuotePrice10Quantity2 inner =>
    have bound_inner := BulkQuotePrice10Quantity2.encode_length_le inner
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
    omega
  | bulkQuotePrice4Quantity4 inner =>
    have bound_inner := BulkQuotePrice4Quantity4.encode_length_le inner
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
    omega
  | bulkQuotePrice6Quantity4 inner =>
    have bound_inner := BulkQuotePrice6Quantity4.encode_length_le inner
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
    omega
  | bulkQuotePrice8Quantity4 inner =>
    have bound_inner := BulkQuotePrice8Quantity4.encode_length_le inner
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
    omega
  | bulkQuotePrice10Quantity4 inner =>
    have bound_inner := BulkQuotePrice10Quantity4.encode_length_le inner
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
    omega
  | bulkQuotePrice4Quantity6 inner =>
    have bound_inner := BulkQuotePrice4Quantity6.encode_length_le inner
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
    omega
  | bulkQuotePrice6Quantity6 inner =>
    have bound_inner := BulkQuotePrice6Quantity6.encode_length_le inner
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
    omega
  | bulkQuotePrice8Quantity6 inner =>
    have bound_inner := BulkQuotePrice8Quantity6.encode_length_le inner
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
    omega
  | bulkQuotePrice10Quantity6 inner =>
    have bound_inner := BulkQuotePrice10Quantity6.encode_length_le inner
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
    omega
  | bulkQuotePrice4Quantity8 inner =>
    have bound_inner := BulkQuotePrice4Quantity8.encode_length_le inner
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
    omega
  | bulkQuotePrice6Quantity8 inner =>
    have bound_inner := BulkQuotePrice6Quantity8.encode_length_le inner
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
    omega
  | bulkQuotePrice8Quantity8 inner =>
    have bound_inner := BulkQuotePrice8Quantity8.encode_length_le inner
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
    omega
  | bulkQuote inner =>
    have bound_inner := BulkQuote.encode_length_le inner
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
    omega
  | sailRequestForQuoteWithSide inner =>
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, SailRequestForQuoteWithSide.encode_length]
    omega
  | bulkQuoteParticipantBqpProtectionSubscription inner =>
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, BulkQuoteParticipantBqpProtectionSubscription.encode_length]
    omega
  | requestForQuote inner =>
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, RequestForQuote.encode_length]
    omega
  | orderCancellation inner =>
    simp only [FirmMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, OrderCancellation.encode_length]
    omega

theorem decode_encode (message : FirmPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [FirmMessage.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [dite_eq_left message.alignmentPadding.length_le]
  rfl

end FirmPacket

end Omi.TmxMxSolaorderentrySailV121Firm
