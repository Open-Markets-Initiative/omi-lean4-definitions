import Wire

/-!
# Qatar Stock Exchange Qse Cash Market Data v2.6

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.QseQsecashMarketdataXdpV26

/-- Order Entry Rejection: one byte code -/
def OrderEntryRejection.codes : List UInt8 :=
  [0x30, 0x4E, 0x59]

inductive OrderEntryRejection where
  | notApplicable -- Not Applicable
  | orderEntryAllowed -- Order Entry Allowed
  | orderEntryForbidden -- Order Entry Forbidden
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderEntryRejection.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderEntryRejection

def toByte : OrderEntryRejection → UInt8
  | .notApplicable => 0x30
  | .orderEntryAllowed => 0x4E
  | .orderEntryForbidden => 0x59
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderEntryRejection :=
  if byte = 0x30 then .notApplicable
  else if byte = 0x4E then .orderEntryAllowed
  else .orderEntryForbidden

def ofByte (byte : UInt8) : OrderEntryRejection :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderEntryRejection) : ofByte value.toByte = value := by
  cases value with
  | notApplicable => decide
  | orderEntryAllowed => decide
  | orderEntryForbidden => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderEntryRejection) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderEntryRejection × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderEntryRejection) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OrderEntryRejection) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OrderEntryRejection) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderEntryRejection

/-- Instrument State: one byte code -/
def InstrumentState.codes : List UInt8 :=
  [0x30, 0x41, 0x48, 0x43]

inductive InstrumentState where
  | notApplicable -- Not Applicable
  | auction -- Auction
  | halted -- Halted
  | closed -- Closed
  | unlisted (byte : { byte : UInt8 // byte ∉ InstrumentState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InstrumentState

def toByte : InstrumentState → UInt8
  | .notApplicable => 0x30
  | .auction => 0x41
  | .halted => 0x48
  | .closed => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : InstrumentState :=
  if byte = 0x30 then .notApplicable
  else if byte = 0x41 then .auction
  else if byte = 0x48 then .halted
  else .closed

def ofByte (byte : UInt8) : InstrumentState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InstrumentState) : ofByte value.toByte = value := by
  cases value with
  | notApplicable => decide
  | auction => decide
  | halted => decide
  | closed => decide
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

/-- Instrument Trading Status: one byte code -/
def InstrumentTradingStatus.codes : List UInt8 :=
  [0x53]

inductive InstrumentTradingStatus where
  | suspended -- Suspended
  | unlisted (byte : { byte : UInt8 // byte ∉ InstrumentTradingStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InstrumentTradingStatus

def toByte : InstrumentTradingStatus → UInt8
  | .suspended => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : InstrumentTradingStatus :=
  .suspended

def ofByte (byte : UInt8) : InstrumentTradingStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InstrumentTradingStatus) : ofByte value.toByte = value := by
  cases value with
  | suspended => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : InstrumentTradingStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (InstrumentTradingStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : InstrumentTradingStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : InstrumentTradingStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : InstrumentTradingStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end InstrumentTradingStatus

/-- Halt Reason: one byte code -/
def HaltReason.codes : List UInt8 :=
  [0x30, 0x52, 0x43, 0x4D]

inductive HaltReason where
  | notApplicable -- Not Applicable
  | haltedNoLiquidityProvider -- Halted No Liquidity Provider
  | openingPriceOutsideCollars -- Opening Price Outside Collars
  | manuelHaltingByMarketOperations -- Manuel Halting By Market Operations
  | unlisted (byte : { byte : UInt8 // byte ∉ HaltReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace HaltReason

def toByte : HaltReason → UInt8
  | .notApplicable => 0x30
  | .haltedNoLiquidityProvider => 0x52
  | .openingPriceOutsideCollars => 0x43
  | .manuelHaltingByMarketOperations => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : HaltReason :=
  if byte = 0x30 then .notApplicable
  else if byte = 0x52 then .haltedNoLiquidityProvider
  else if byte = 0x43 then .openingPriceOutsideCollars
  else .manuelHaltingByMarketOperations

def ofByte (byte : UInt8) : HaltReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : HaltReason) : ofByte value.toByte = value := by
  cases value with
  | notApplicable => decide
  | haltedNoLiquidityProvider => decide
  | openingPriceOutsideCollars => decide
  | manuelHaltingByMarketOperations => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : HaltReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (HaltReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : HaltReason) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : HaltReason) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : HaltReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end HaltReason

/-- Action Affecting State: one byte code -/
def ActionAffectingState.codes : List UInt8 :=
  [0x30, 0x43, 0x44, 0x4D, 0x4E, 0x4F, 0x50, 0x52]

inductive ActionAffectingState where
  | notApplicable -- Not Applicable
  | tradingOnTheInstrumentAtTheOpeningSentBeforeO -- Trading On The Instrument At The Opening Sent Before O
  | cancelledProgrammedOpening -- Cancelled Programmed Opening
  | instrumentManuallyHaltedByMarketOperations -- Instrument Manually Halted By Market Operations
  | instrumentIsBeingInitializedBeginningOfTheTradingDay -- Instrument Is Being Initialized Beginning Of The Trading Day
  | instrumentOpened -- Instrument Opened
  | deferredProgrammedOpening -- Deferred Programmed Opening
  | automaticHaltingAtTheClassAuction -- Automatic Halting At The Class Auction
  | unlisted (byte : { byte : UInt8 // byte ∉ ActionAffectingState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ActionAffectingState

def toByte : ActionAffectingState → UInt8
  | .notApplicable => 0x30
  | .tradingOnTheInstrumentAtTheOpeningSentBeforeO => 0x43
  | .cancelledProgrammedOpening => 0x44
  | .instrumentManuallyHaltedByMarketOperations => 0x4D
  | .instrumentIsBeingInitializedBeginningOfTheTradingDay => 0x4E
  | .instrumentOpened => 0x4F
  | .deferredProgrammedOpening => 0x50
  | .automaticHaltingAtTheClassAuction => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ActionAffectingState :=
  if byte = 0x30 then .notApplicable
  else if byte = 0x43 then .tradingOnTheInstrumentAtTheOpeningSentBeforeO
  else if byte = 0x44 then .cancelledProgrammedOpening
  else if byte = 0x4D then .instrumentManuallyHaltedByMarketOperations
  else if byte = 0x4E then .instrumentIsBeingInitializedBeginningOfTheTradingDay
  else if byte = 0x4F then .instrumentOpened
  else if byte = 0x50 then .deferredProgrammedOpening
  else .automaticHaltingAtTheClassAuction

def ofByte (byte : UInt8) : ActionAffectingState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ActionAffectingState) : ofByte value.toByte = value := by
  cases value with
  | notApplicable => decide
  | tradingOnTheInstrumentAtTheOpeningSentBeforeO => decide
  | cancelledProgrammedOpening => decide
  | instrumentManuallyHaltedByMarketOperations => decide
  | instrumentIsBeingInitializedBeginningOfTheTradingDay => decide
  | instrumentOpened => decide
  | deferredProgrammedOpening => decide
  | automaticHaltingAtTheClassAuction => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ActionAffectingState) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ActionAffectingState × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ActionAffectingState) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ActionAffectingState) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ActionAffectingState) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ActionAffectingState

/-- Instrument State Tcs: one byte code -/
def InstrumentStateTcs.codes : List UInt8 :=
  [0x30, 0x53, 0x41]

inductive InstrumentStateTcs where
  | notApplicable -- Not Applicable
  | instrumentIsForbidden -- Instrument Is Forbidden
  | instrumentIsAuthorized -- Instrument Is Authorized
  | unlisted (byte : { byte : UInt8 // byte ∉ InstrumentStateTcs.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InstrumentStateTcs

def toByte : InstrumentStateTcs → UInt8
  | .notApplicable => 0x30
  | .instrumentIsForbidden => 0x53
  | .instrumentIsAuthorized => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : InstrumentStateTcs :=
  if byte = 0x30 then .notApplicable
  else if byte = 0x53 then .instrumentIsForbidden
  else .instrumentIsAuthorized

def ofByte (byte : UInt8) : InstrumentStateTcs :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InstrumentStateTcs) : ofByte value.toByte = value := by
  cases value with
  | notApplicable => decide
  | instrumentIsForbidden => decide
  | instrumentIsAuthorized => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : InstrumentStateTcs) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (InstrumentStateTcs × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : InstrumentStateTcs) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : InstrumentStateTcs) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : InstrumentStateTcs) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end InstrumentStateTcs

/-- Period Side: one byte code -/
def PeriodSide.codes : List UInt8 :=
  [0x30, 0x41, 0x56]

inductive PeriodSide where
  | notApplicable -- Not Applicable
  | bidOnlyPeriod -- Bid Only Period
  | offerOnlyPeriod -- Offer Only Period
  | unlisted (byte : { byte : UInt8 // byte ∉ PeriodSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PeriodSide

def toByte : PeriodSide → UInt8
  | .notApplicable => 0x30
  | .bidOnlyPeriod => 0x41
  | .offerOnlyPeriod => 0x56
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PeriodSide :=
  if byte = 0x30 then .notApplicable
  else if byte = 0x41 then .bidOnlyPeriod
  else .offerOnlyPeriod

def ofByte (byte : UInt8) : PeriodSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PeriodSide) : ofByte value.toByte = value := by
  cases value with
  | notApplicable => decide
  | bidOnlyPeriod => decide
  | offerOnlyPeriod => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PeriodSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PeriodSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PeriodSide) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : PeriodSide) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : PeriodSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PeriodSide

/-- Instrument Group State: one byte code -/
def InstrumentGroupState.codes : List UInt8 :=
  [0x50, 0x43, 0x4F, 0x53, 0x52, 0x4E, 0x46, 0x5A, 0x49]

inductive InstrumentGroupState where
  | preOpening -- Pre Opening
  | beginningOfDayConsultation -- Beginning Of Day Consultation
  | opening -- Opening
  | marketSession -- Market Session
  | tradingAtLast -- Trading At Last
  | surveillanceIntervention -- Surveillance Intervention
  | endOfDayInquiry -- End Of Day Inquiry
  | interrupted -- Interrupted
  | forbidden -- Forbidden
  | unlisted (byte : { byte : UInt8 // byte ∉ InstrumentGroupState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InstrumentGroupState

def toByte : InstrumentGroupState → UInt8
  | .preOpening => 0x50
  | .beginningOfDayConsultation => 0x43
  | .opening => 0x4F
  | .marketSession => 0x53
  | .tradingAtLast => 0x52
  | .surveillanceIntervention => 0x4E
  | .endOfDayInquiry => 0x46
  | .interrupted => 0x5A
  | .forbidden => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : InstrumentGroupState :=
  if byte = 0x50 then .preOpening
  else if byte = 0x43 then .beginningOfDayConsultation
  else if byte = 0x4F then .opening
  else if byte = 0x53 then .marketSession
  else if byte = 0x52 then .tradingAtLast
  else if byte = 0x4E then .surveillanceIntervention
  else if byte = 0x46 then .endOfDayInquiry
  else if byte = 0x5A then .interrupted
  else .forbidden

def ofByte (byte : UInt8) : InstrumentGroupState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InstrumentGroupState) : ofByte value.toByte = value := by
  cases value with
  | preOpening => decide
  | beginningOfDayConsultation => decide
  | opening => decide
  | marketSession => decide
  | tradingAtLast => decide
  | surveillanceIntervention => decide
  | endOfDayInquiry => decide
  | interrupted => decide
  | forbidden => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : InstrumentGroupState) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (InstrumentGroupState × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : InstrumentGroupState) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : InstrumentGroupState) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : InstrumentGroupState) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end InstrumentGroupState

/-- Session Type: one byte code -/
def SessionType.codes : List UInt8 :=
  [0x45, 0x43, 0x4C]

inductive SessionType where
  | early -- Early
  | coreSession -- Core Session
  | late -- Late
  | unlisted (byte : { byte : UInt8 // byte ∉ SessionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SessionType

def toByte : SessionType → UInt8
  | .early => 0x45
  | .coreSession => 0x43
  | .late => 0x4C
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SessionType :=
  if byte = 0x45 then .early
  else if byte = 0x43 then .coreSession
  else .late

def ofByte (byte : UInt8) : SessionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SessionType) : ofByte value.toByte = value := by
  cases value with
  | early => decide
  | coreSession => decide
  | late => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SessionType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SessionType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SessionType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SessionType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SessionType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SessionType

/-- Priority Indicator: one byte code -/
def PriorityIndicator.codes : List UInt8 :=
  [0x4F, 0x4E]

inductive PriorityIndicator where
  | urgentMessage -- Urgent Message
  | nonUrgentMessage -- Non Urgent Message
  | unlisted (byte : { byte : UInt8 // byte ∉ PriorityIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PriorityIndicator

def toByte : PriorityIndicator → UInt8
  | .urgentMessage => 0x4F
  | .nonUrgentMessage => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PriorityIndicator :=
  if byte = 0x4F then .urgentMessage
  else .nonUrgentMessage

def ofByte (byte : UInt8) : PriorityIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PriorityIndicator) : ofByte value.toByte = value := by
  cases value with
  | urgentMessage => decide
  | nonUrgentMessage => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PriorityIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PriorityIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PriorityIndicator) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : PriorityIndicator) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : PriorityIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PriorityIndicator

/-- Type Of Message: one byte code -/
def TypeOfMessage.codes : List UInt8 :=
  [0x42, 0x54, 0x52]

inductive TypeOfMessage where
  | marketInformationContents -- Market Information Contents
  | technicalInformation -- Technical Information
  | marketAndTechnicalInformation -- Market And Technical Information
  | unlisted (byte : { byte : UInt8 // byte ∉ TypeOfMessage.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TypeOfMessage

def toByte : TypeOfMessage → UInt8
  | .marketInformationContents => 0x42
  | .technicalInformation => 0x54
  | .marketAndTechnicalInformation => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TypeOfMessage :=
  if byte = 0x42 then .marketInformationContents
  else if byte = 0x54 then .technicalInformation
  else .marketAndTechnicalInformation

def ofByte (byte : UInt8) : TypeOfMessage :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TypeOfMessage) : ofByte value.toByte = value := by
  cases value with
  | marketInformationContents => decide
  | technicalInformation => decide
  | marketAndTechnicalInformation => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TypeOfMessage) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TypeOfMessage × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TypeOfMessage) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TypeOfMessage) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TypeOfMessage) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TypeOfMessage

/-- Collar Type: one byte code -/
def CollarType.codes : List UInt8 :=
  [0x44, 0x53]

inductive CollarType where
  | dynamicCollars -- Dynamic Collars
  | staticThresholds -- Static Thresholds
  | unlisted (byte : { byte : UInt8 // byte ∉ CollarType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CollarType

def toByte : CollarType → UInt8
  | .dynamicCollars => 0x44
  | .staticThresholds => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CollarType :=
  if byte = 0x44 then .dynamicCollars
  else .staticThresholds

def ofByte (byte : UInt8) : CollarType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CollarType) : ofByte value.toByte = value := by
  cases value with
  | dynamicCollars => decide
  | staticThresholds => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CollarType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CollarType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CollarType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CollarType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CollarType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CollarType

/-- Period Indicator: one byte code -/
def PeriodIndicator.codes : List UInt8 :=
  [0x4D, 0x45]

inductive PeriodIndicator where
  | morningEffectiveForTheCurrentDay -- Morning Effective For The Current Day
  | eveningEffectiveForTheNextTradingDay -- Evening Effective For The Next Trading Day
  | unlisted (byte : { byte : UInt8 // byte ∉ PeriodIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PeriodIndicator

def toByte : PeriodIndicator → UInt8
  | .morningEffectiveForTheCurrentDay => 0x4D
  | .eveningEffectiveForTheNextTradingDay => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PeriodIndicator :=
  if byte = 0x4D then .morningEffectiveForTheCurrentDay
  else .eveningEffectiveForTheNextTradingDay

def ofByte (byte : UInt8) : PeriodIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PeriodIndicator) : ofByte value.toByte = value := by
  cases value with
  | morningEffectiveForTheCurrentDay => decide
  | eveningEffectiveForTheNextTradingDay => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PeriodIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PeriodIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PeriodIndicator) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : PeriodIndicator) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : PeriodIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PeriodIndicator

/-- Instrument Category: one byte code -/
def InstrumentCategory.codes : List UInt8 :=
  [0x41, 0x4F, 0x57, 0x54, 0x44]

inductive InstrumentCategory where
  | stock -- Stock
  | bond -- Bond
  | warrantAndCertificate -- Warrant And Certificate
  | tracker -- Tracker
  | miscellaneous -- Miscellaneous
  | unlisted (byte : { byte : UInt8 // byte ∉ InstrumentCategory.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InstrumentCategory

def toByte : InstrumentCategory → UInt8
  | .stock => 0x41
  | .bond => 0x4F
  | .warrantAndCertificate => 0x57
  | .tracker => 0x54
  | .miscellaneous => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : InstrumentCategory :=
  if byte = 0x41 then .stock
  else if byte = 0x4F then .bond
  else if byte = 0x57 then .warrantAndCertificate
  else if byte = 0x54 then .tracker
  else .miscellaneous

def ofByte (byte : UInt8) : InstrumentCategory :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InstrumentCategory) : ofByte value.toByte = value := by
  cases value with
  | stock => decide
  | bond => decide
  | warrantAndCertificate => decide
  | tracker => decide
  | miscellaneous => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : InstrumentCategory) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (InstrumentCategory × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : InstrumentCategory) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : InstrumentCategory) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : InstrumentCategory) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end InstrumentCategory

/-- Type Of Derivatives: one byte code -/
def TypeOfDerivatives.codes : List UInt8 :=
  [0x31, 0x34, 0x36, 0x39]

inductive TypeOfDerivatives where
  | inavIndicativeNetAssetValueForEtfExchangeTraded -- Inav Indicative Net Asset Value For Etf Exchange Traded
  | supportsShortTermsOptions -- Supports Short Terms Options
  | supportsLongTermOptions -- Supports Long Term Options
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ TypeOfDerivatives.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TypeOfDerivatives

def toByte : TypeOfDerivatives → UInt8
  | .inavIndicativeNetAssetValueForEtfExchangeTraded => 0x31
  | .supportsShortTermsOptions => 0x34
  | .supportsLongTermOptions => 0x36
  | .no => 0x39
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TypeOfDerivatives :=
  if byte = 0x31 then .inavIndicativeNetAssetValueForEtfExchangeTraded
  else if byte = 0x34 then .supportsShortTermsOptions
  else if byte = 0x36 then .supportsLongTermOptions
  else .no

def ofByte (byte : UInt8) : TypeOfDerivatives :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TypeOfDerivatives) : ofByte value.toByte = value := by
  cases value with
  | inavIndicativeNetAssetValueForEtfExchangeTraded => decide
  | supportsShortTermsOptions => decide
  | supportsLongTermOptions => decide
  | no => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TypeOfDerivatives) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TypeOfDerivatives × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TypeOfDerivatives) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TypeOfDerivatives) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TypeOfDerivatives) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TypeOfDerivatives

/-- Repo Indicator: one byte code -/
def RepoIndicator.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33, 0x38]

inductive RepoIndicator where
  | instrumentNeitherEligibleForTheSrdNorEligibleForTheLoan -- Instrument Neither Eligible For The Srd Nor Eligible For The Loan
  | instrumentEligibleForTheSrdAndForTheLoanAndLending -- Instrument Eligible For The Srd And For The Loan And Lending
  | instrumentEligibleForTheSrdButNotForTheLoanAndLending -- Instrument Eligible For The Srd But Not For The Loan And Lending
  | instrumentEligibleForTheLoanAndLendingMarketButNotForThe -- Instrument Eligible For The Loan And Lending Market But Not For The
  | nonSignificant -- Non Significant
  | unlisted (byte : { byte : UInt8 // byte ∉ RepoIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RepoIndicator

def toByte : RepoIndicator → UInt8
  | .instrumentNeitherEligibleForTheSrdNorEligibleForTheLoan => 0x30
  | .instrumentEligibleForTheSrdAndForTheLoanAndLending => 0x31
  | .instrumentEligibleForTheSrdButNotForTheLoanAndLending => 0x32
  | .instrumentEligibleForTheLoanAndLendingMarketButNotForThe => 0x33
  | .nonSignificant => 0x38
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RepoIndicator :=
  if byte = 0x30 then .instrumentNeitherEligibleForTheSrdNorEligibleForTheLoan
  else if byte = 0x31 then .instrumentEligibleForTheSrdAndForTheLoanAndLending
  else if byte = 0x32 then .instrumentEligibleForTheSrdButNotForTheLoanAndLending
  else if byte = 0x33 then .instrumentEligibleForTheLoanAndLendingMarketButNotForThe
  else .nonSignificant

def ofByte (byte : UInt8) : RepoIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RepoIndicator) : ofByte value.toByte = value := by
  cases value with
  | instrumentNeitherEligibleForTheSrdNorEligibleForTheLoan => decide
  | instrumentEligibleForTheSrdAndForTheLoanAndLending => decide
  | instrumentEligibleForTheSrdButNotForTheLoanAndLending => decide
  | instrumentEligibleForTheLoanAndLendingMarketButNotForThe => decide
  | nonSignificant => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RepoIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RepoIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RepoIndicator) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : RepoIndicator) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : RepoIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RepoIndicator

/-- Algo: one byte code -/
def Algo.codes : List UInt8 :=
  [0x46, 0x4F]

inductive Algo where
  | fifo -- Fifo
  | fifoOrigin -- Fifo Origin
  | unlisted (byte : { byte : UInt8 // byte ∉ Algo.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Algo

def toByte : Algo → UInt8
  | .fifo => 0x46
  | .fifoOrigin => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Algo :=
  if byte = 0x46 then .fifo
  else .fifoOrigin

def ofByte (byte : UInt8) : Algo :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Algo) : ofByte value.toByte = value := by
  cases value with
  | fifo => decide
  | fifoOrigin => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Algo) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Algo × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Algo) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Algo) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Algo) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Algo

/-- Small Trade Indicator: one byte code -/
def SmallTradeIndicator.codes : List UInt8 :=
  [0x31, 0x32]

inductive SmallTradeIndicator where
  | notASmallTrade -- Not A Small Trade
  | smallTrade -- Small Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ SmallTradeIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SmallTradeIndicator

def toByte : SmallTradeIndicator → UInt8
  | .notASmallTrade => 0x31
  | .smallTrade => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SmallTradeIndicator :=
  if byte = 0x31 then .notASmallTrade
  else .smallTrade

def ofByte (byte : UInt8) : SmallTradeIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SmallTradeIndicator) : ofByte value.toByte = value := by
  cases value with
  | notASmallTrade => decide
  | smallTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SmallTradeIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SmallTradeIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SmallTradeIndicator) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SmallTradeIndicator) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SmallTradeIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SmallTradeIndicator

/-- Trad Cond 2: one byte code -/
def TradCond2.codes : List UInt8 :=
  [0x30, 0x31]

inductive TradCond2 where
  | notLastOfASeriesOfTradesAtTheSamePrice -- Not Last Of A Series Of Trades At The Same Price
  | lastOfASeriesOfTradeAtTheSamePrice -- Last Of A Series Of Trade At The Same Price
  | unlisted (byte : { byte : UInt8 // byte ∉ TradCond2.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradCond2

def toByte : TradCond2 → UInt8
  | .notLastOfASeriesOfTradesAtTheSamePrice => 0x30
  | .lastOfASeriesOfTradeAtTheSamePrice => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradCond2 :=
  if byte = 0x30 then .notLastOfASeriesOfTradesAtTheSamePrice
  else .lastOfASeriesOfTradeAtTheSamePrice

def ofByte (byte : UInt8) : TradCond2 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradCond2) : ofByte value.toByte = value := by
  cases value with
  | notLastOfASeriesOfTradesAtTheSamePrice => decide
  | lastOfASeriesOfTradeAtTheSamePrice => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradCond2) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradCond2 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradCond2) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TradCond2) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TradCond2) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradCond2

/-- Trad Cond 3: one byte code -/
def TradCond3.codes : List UInt8 :=
  [0x30, 0x31, 0x34]

inductive TradCond3 where
  | tradeDoesNotStemFromACrossOrder -- Trade Does Not Stem From A Cross Order
  | tradeStemsFromACrossOrder -- Trade Stems From A Cross Order
  | valuationTrade -- Valuation Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ TradCond3.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradCond3

def toByte : TradCond3 → UInt8
  | .tradeDoesNotStemFromACrossOrder => 0x30
  | .tradeStemsFromACrossOrder => 0x31
  | .valuationTrade => 0x34
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradCond3 :=
  if byte = 0x30 then .tradeDoesNotStemFromACrossOrder
  else if byte = 0x31 then .tradeStemsFromACrossOrder
  else .valuationTrade

def ofByte (byte : UInt8) : TradCond3 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradCond3) : ofByte value.toByte = value := by
  cases value with
  | tradeDoesNotStemFromACrossOrder => decide
  | tradeStemsFromACrossOrder => decide
  | valuationTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradCond3) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradCond3 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradCond3) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TradCond3) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TradCond3) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradCond3

/-- Trade Origin: one byte code -/
def TradeOrigin.codes : List UInt8 :=
  [0x42, 0x4F]

inductive TradeOrigin where
  | ordersFromTheBook -- Orders From The Book
  | blockTrade -- Block Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeOrigin.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeOrigin

def toByte : TradeOrigin → UInt8
  | .ordersFromTheBook => 0x42
  | .blockTrade => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeOrigin :=
  if byte = 0x42 then .ordersFromTheBook
  else .blockTrade

def ofByte (byte : UInt8) : TradeOrigin :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeOrigin) : ofByte value.toByte = value := by
  cases value with
  | ordersFromTheBook => decide
  | blockTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeOrigin) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeOrigin × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeOrigin) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TradeOrigin) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TradeOrigin) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeOrigin

/-- Opening Trade Indicator: one byte code -/
def OpeningTradeIndicator.codes : List UInt8 :=
  [0x4F, 0x53]

inductive OpeningTradeIndicator where
  | opening -- Opening
  | coreSession -- Core Session
  | unlisted (byte : { byte : UInt8 // byte ∉ OpeningTradeIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OpeningTradeIndicator

def toByte : OpeningTradeIndicator → UInt8
  | .opening => 0x4F
  | .coreSession => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OpeningTradeIndicator :=
  if byte = 0x4F then .opening
  else .coreSession

def ofByte (byte : UInt8) : OpeningTradeIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OpeningTradeIndicator) : ofByte value.toByte = value := by
  cases value with
  | opening => decide
  | coreSession => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OpeningTradeIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OpeningTradeIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OpeningTradeIndicator) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OpeningTradeIndicator) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OpeningTradeIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OpeningTradeIndicator

/-- Tick Direction: one byte code -/
def TickDirection.codes : List UInt8 :=
  [0x2B, 0x2D, 0x30]

inductive TickDirection where
  | positive -- Positive
  | negative -- Negative
  | noVariationOrDataFieldNotSignificant -- No Variation Or Data Field Not Significant
  | unlisted (byte : { byte : UInt8 // byte ∉ TickDirection.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TickDirection

def toByte : TickDirection → UInt8
  | .positive => 0x2B
  | .negative => 0x2D
  | .noVariationOrDataFieldNotSignificant => 0x30
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TickDirection :=
  if byte = 0x2B then .positive
  else if byte = 0x2D then .negative
  else .noVariationOrDataFieldNotSignificant

def ofByte (byte : UInt8) : TickDirection :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TickDirection) : ofByte value.toByte = value := by
  cases value with
  | positive => decide
  | negative => decide
  | noVariationOrDataFieldNotSignificant => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TickDirection) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TickDirection × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TickDirection) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TickDirection) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TickDirection) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TickDirection

/-- Instrument Valuation Price: one byte code -/
def InstrumentValuationPrice.codes : List UInt8 :=
  [0x30, 0x31]

inductive InstrumentValuationPrice where
  | notAValuationPrice -- Not A Valuation Price
  | valuationPrice -- Valuation Price
  | unlisted (byte : { byte : UInt8 // byte ∉ InstrumentValuationPrice.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InstrumentValuationPrice

def toByte : InstrumentValuationPrice → UInt8
  | .notAValuationPrice => 0x30
  | .valuationPrice => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : InstrumentValuationPrice :=
  if byte = 0x30 then .notAValuationPrice
  else .valuationPrice

def ofByte (byte : UInt8) : InstrumentValuationPrice :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InstrumentValuationPrice) : ofByte value.toByte = value := by
  cases value with
  | notAValuationPrice => decide
  | valuationPrice => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : InstrumentValuationPrice) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (InstrumentValuationPrice × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : InstrumentValuationPrice) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : InstrumentValuationPrice) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : InstrumentValuationPrice) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end InstrumentValuationPrice

/-- Quote Condition: one byte code -/
def QuoteCondition.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33]

inductive QuoteCondition where
  | noLiquidityProviderLp -- No Liquidity Provider Lp
  | lpOnlyOnAskSide -- Lp Only On Ask Side
  | lpOnlyOnBidSide -- Lp Only On Bid Side
  | lpOnAskAndBidSides -- Lp On Ask And Bid Sides
  | unlisted (byte : { byte : UInt8 // byte ∉ QuoteCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace QuoteCondition

def toByte : QuoteCondition → UInt8
  | .noLiquidityProviderLp => 0x30
  | .lpOnlyOnAskSide => 0x31
  | .lpOnlyOnBidSide => 0x32
  | .lpOnAskAndBidSides => 0x33
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : QuoteCondition :=
  if byte = 0x30 then .noLiquidityProviderLp
  else if byte = 0x31 then .lpOnlyOnAskSide
  else if byte = 0x32 then .lpOnlyOnBidSide
  else .lpOnAskAndBidSides

def ofByte (byte : UInt8) : QuoteCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : QuoteCondition) : ofByte value.toByte = value := by
  cases value with
  | noLiquidityProviderLp => decide
  | lpOnlyOnAskSide => decide
  | lpOnlyOnBidSide => decide
  | lpOnAskAndBidSides => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : QuoteCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (QuoteCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : QuoteCondition) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : QuoteCondition) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : QuoteCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end QuoteCondition

/-- Order Type: one byte code -/
def OrderType.codes : List UInt8 :=
  [0x31, 0x32, 0x4B, 0x50]

inductive OrderType where
  | marketOrder -- Market Order
  | limitOrder -- Limit Order
  | marketToLimitOrder -- Market To Limit Order
  | pegOrder -- Peg Order
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderType

def toByte : OrderType → UInt8
  | .marketOrder => 0x31
  | .limitOrder => 0x32
  | .marketToLimitOrder => 0x4B
  | .pegOrder => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderType :=
  if byte = 0x31 then .marketOrder
  else if byte = 0x32 then .limitOrder
  else if byte = 0x4B then .marketToLimitOrder
  else .pegOrder

def ofByte (byte : UInt8) : OrderType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderType) : ofByte value.toByte = value := by
  cases value with
  | marketOrder => decide
  | limitOrder => decide
  | marketToLimitOrder => decide
  | pegOrder => decide
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

/-- Action Type: one byte code -/
def ActionType.codes : List UInt8 :=
  [0x41, 0x44, 0x50, 0x46, 0x59]

inductive ActionType where
  | newOrder -- New Order
  | deletionOfOrderIdentifiedByOrderId -- Deletion Of Order Identified By Order Id
  | deletionOfOrderIdentifiedByOrderIdAndAllPrecedingOrders -- Deletion Of Order Identified By Order Id And All Preceding Orders
  | deletionOfAllOrdersForTheGivenInstrumentDependingOnThe -- Deletion Of All Orders For The Given Instrument Depending On The
  | retransmissionOfAllOrdersForTheGivenInstrument -- Retransmission Of All Orders For The Given Instrument
  | unlisted (byte : { byte : UInt8 // byte ∉ ActionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ActionType

def toByte : ActionType → UInt8
  | .newOrder => 0x41
  | .deletionOfOrderIdentifiedByOrderId => 0x44
  | .deletionOfOrderIdentifiedByOrderIdAndAllPrecedingOrders => 0x50
  | .deletionOfAllOrdersForTheGivenInstrumentDependingOnThe => 0x46
  | .retransmissionOfAllOrdersForTheGivenInstrument => 0x59
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ActionType :=
  if byte = 0x41 then .newOrder
  else if byte = 0x44 then .deletionOfOrderIdentifiedByOrderId
  else if byte = 0x50 then .deletionOfOrderIdentifiedByOrderIdAndAllPrecedingOrders
  else if byte = 0x46 then .deletionOfAllOrdersForTheGivenInstrumentDependingOnThe
  else .retransmissionOfAllOrdersForTheGivenInstrument

def ofByte (byte : UInt8) : ActionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ActionType) : ofByte value.toByte = value := by
  cases value with
  | newOrder => decide
  | deletionOfOrderIdentifiedByOrderId => decide
  | deletionOfOrderIdentifiedByOrderIdAndAllPrecedingOrders => decide
  | deletionOfAllOrdersForTheGivenInstrumentDependingOnThe => decide
  | retransmissionOfAllOrdersForTheGivenInstrument => decide
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

/-- Rebroadcast Indicator: one byte code -/
def RebroadcastIndicator.codes : List UInt8 :=
  [0x30, 0x31]

inductive RebroadcastIndicator where
  | currentDay -- Current Day
  | previousDay -- Previous Day
  | unlisted (byte : { byte : UInt8 // byte ∉ RebroadcastIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RebroadcastIndicator

def toByte : RebroadcastIndicator → UInt8
  | .currentDay => 0x30
  | .previousDay => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RebroadcastIndicator :=
  if byte = 0x30 then .currentDay
  else .previousDay

def ofByte (byte : UInt8) : RebroadcastIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RebroadcastIndicator) : ofByte value.toByte = value := by
  cases value with
  | currentDay => decide
  | previousDay => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RebroadcastIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RebroadcastIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RebroadcastIndicator) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : RebroadcastIndicator) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : RebroadcastIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RebroadcastIndicator

/-- Stock State Change Message: 48 bytes -/
structure StockStateChangeMessage where
  symbolIndex : BitVec 32
  sourceSeqNum : BitVec 32
  sourceTime : BitVec 32
  systemId : BitVec 32
  sourceTimeMicroSecs : BitVec 16
  fillerBinaryInt2 : Alpha 2
  startDateHalting : Alpha 8
  startTimeHalting : Alpha 6
  progOpeningTime : Alpha 6
  orderEntryRejection : OrderEntryRejection
  instrumentState : InstrumentState
  instrumentTradingStatus : InstrumentTradingStatus
  haltReason : HaltReason
  actionAffectingState : ActionAffectingState
  instrumentStateTcs : InstrumentStateTcs
  periodSide : PeriodSide
  fillerBinaryInt1 : Alpha 1
  deriving DecidableEq, Repr

namespace StockStateChangeMessage

def encode (message : StockStateChangeMessage) : List UInt8 :=
  encodeUInt 4 message.symbolIndex
    ++ (encodeUInt 4 message.sourceSeqNum
    ++ (encodeUInt 4 message.sourceTime
    ++ (encodeUInt 4 message.systemId
    ++ (encodeUInt 2 message.sourceTimeMicroSecs
    ++ (Alpha.encode message.fillerBinaryInt2
    ++ (Alpha.encode message.startDateHalting
    ++ (Alpha.encode message.startTimeHalting
    ++ (Alpha.encode message.progOpeningTime
    ++ (OrderEntryRejection.encode message.orderEntryRejection
    ++ (InstrumentState.encode message.instrumentState
    ++ (InstrumentTradingStatus.encode message.instrumentTradingStatus
    ++ (HaltReason.encode message.haltReason
    ++ (ActionAffectingState.encode message.actionAffectingState
    ++ (InstrumentStateTcs.encode message.instrumentStateTcs
    ++ (PeriodSide.encode message.periodSide
    ++ (Alpha.encode message.fillerBinaryInt1))))))))))))))))

def decode (bytes : List UInt8) : Option (StockStateChangeMessage × List UInt8) := do
  let (symbolIndex, bytes) ← decodeUInt 4 bytes
  let (sourceSeqNum, bytes) ← decodeUInt 4 bytes
  let (sourceTime, bytes) ← decodeUInt 4 bytes
  let (systemId, bytes) ← decodeUInt 4 bytes
  let (sourceTimeMicroSecs, bytes) ← decodeUInt 2 bytes
  let (fillerBinaryInt2, bytes) ← Alpha.decode 2 bytes
  let (startDateHalting, bytes) ← Alpha.decode 8 bytes
  let (startTimeHalting, bytes) ← Alpha.decode 6 bytes
  let (progOpeningTime, bytes) ← Alpha.decode 6 bytes
  let (orderEntryRejection, bytes) ← OrderEntryRejection.decode bytes
  let (instrumentState, bytes) ← InstrumentState.decode bytes
  let (instrumentTradingStatus, bytes) ← InstrumentTradingStatus.decode bytes
  let (haltReason, bytes) ← HaltReason.decode bytes
  let (actionAffectingState, bytes) ← ActionAffectingState.decode bytes
  let (instrumentStateTcs, bytes) ← InstrumentStateTcs.decode bytes
  let (periodSide, bytes) ← PeriodSide.decode bytes
  let (fillerBinaryInt1, bytes) ← Alpha.decode 1 bytes
  pure ({ symbolIndex, sourceSeqNum, sourceTime, systemId, sourceTimeMicroSecs, fillerBinaryInt2, startDateHalting, startTimeHalting, progOpeningTime, orderEntryRejection, instrumentState, instrumentTradingStatus, haltReason, actionAffectingState, instrumentStateTcs, periodSide, fillerBinaryInt1 }, bytes)

@[simp] theorem encode_length (message : StockStateChangeMessage) : (encode message).length = 48 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, OrderEntryRejection.encode_length, InstrumentState.encode_length, InstrumentTradingStatus.encode_length, HaltReason.encode_length, ActionAffectingState.encode_length, InstrumentStateTcs.encode_length, PeriodSide.encode_length]

theorem encode_length_pos (message : StockStateChangeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StockStateChangeMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderEntryRejection.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentState.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentTradingStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, HaltReason.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ActionAffectingState.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentStateTcs.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PeriodSide.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StockStateChangeMessage

/-- Class State Change Message: 24 bytes -/
structure ClassStateChangeMessage where
  sourceSeqNum : BitVec 32
  sourceTime : BitVec 32
  systemId : BitVec 32
  sourceTimeMicroSecs : BitVec 16
  instrumentGroupCode : Alpha 3
  instrumentGroupState : InstrumentGroupState
  sessionType : SessionType
  fillerBinaryInt1 : Alpha 1
  classState : Alpha 4
  deriving DecidableEq, Repr

namespace ClassStateChangeMessage

def encode (message : ClassStateChangeMessage) : List UInt8 :=
  encodeUInt 4 message.sourceSeqNum
    ++ (encodeUInt 4 message.sourceTime
    ++ (encodeUInt 4 message.systemId
    ++ (encodeUInt 2 message.sourceTimeMicroSecs
    ++ (Alpha.encode message.instrumentGroupCode
    ++ (InstrumentGroupState.encode message.instrumentGroupState
    ++ (SessionType.encode message.sessionType
    ++ (Alpha.encode message.fillerBinaryInt1
    ++ (Alpha.encode message.classState))))))))

def decode (bytes : List UInt8) : Option (ClassStateChangeMessage × List UInt8) := do
  let (sourceSeqNum, bytes) ← decodeUInt 4 bytes
  let (sourceTime, bytes) ← decodeUInt 4 bytes
  let (systemId, bytes) ← decodeUInt 4 bytes
  let (sourceTimeMicroSecs, bytes) ← decodeUInt 2 bytes
  let (instrumentGroupCode, bytes) ← Alpha.decode 3 bytes
  let (instrumentGroupState, bytes) ← InstrumentGroupState.decode bytes
  let (sessionType, bytes) ← SessionType.decode bytes
  let (fillerBinaryInt1, bytes) ← Alpha.decode 1 bytes
  let (classState, bytes) ← Alpha.decode 4 bytes
  pure ({ sourceSeqNum, sourceTime, systemId, sourceTimeMicroSecs, instrumentGroupCode, instrumentGroupState, sessionType, fillerBinaryInt1, classState }, bytes)

@[simp] theorem encode_length (message : ClassStateChangeMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, InstrumentGroupState.encode_length, SessionType.encode_length]

theorem encode_length_pos (message : ClassStateChangeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ClassStateChangeMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentGroupState.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SessionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ClassStateChangeMessage

/-- Mail Message: 964 bytes -/
structure MailMessage where
  sourceSeqNum : BitVec 32
  sourceTime : BitVec 32
  systemId : BitVec 32
  sourceTimeMicroSecs : BitVec 16
  eMailMsgNumber : BitVec 16
  numberOfMessage : BitVec 16
  sequenceNumber : BitVec 16
  instrumentGroupCode : Alpha 3
  fillerAsciiStr1 : Alpha 1
  priorityIndicator : PriorityIndicator
  typeOfMessage : TypeOfMessage
  addressType : Alpha 2
  title : Alpha 80
  text : Alpha 854
  fillerAsciiStr2 : Alpha 2
  deriving DecidableEq, Repr

namespace MailMessage

def encode (message : MailMessage) : List UInt8 :=
  encodeUInt 4 message.sourceSeqNum
    ++ (encodeUInt 4 message.sourceTime
    ++ (encodeUInt 4 message.systemId
    ++ (encodeUInt 2 message.sourceTimeMicroSecs
    ++ (encodeUInt 2 message.eMailMsgNumber
    ++ (encodeUInt 2 message.numberOfMessage
    ++ (encodeUInt 2 message.sequenceNumber
    ++ (Alpha.encode message.instrumentGroupCode
    ++ (Alpha.encode message.fillerAsciiStr1
    ++ (PriorityIndicator.encode message.priorityIndicator
    ++ (TypeOfMessage.encode message.typeOfMessage
    ++ (Alpha.encode message.addressType
    ++ (Alpha.encode message.title
    ++ (Alpha.encode message.text
    ++ (Alpha.encode message.fillerAsciiStr2))))))))))))))

def decode (bytes : List UInt8) : Option (MailMessage × List UInt8) := do
  let (sourceSeqNum, bytes) ← decodeUInt 4 bytes
  let (sourceTime, bytes) ← decodeUInt 4 bytes
  let (systemId, bytes) ← decodeUInt 4 bytes
  let (sourceTimeMicroSecs, bytes) ← decodeUInt 2 bytes
  let (eMailMsgNumber, bytes) ← decodeUInt 2 bytes
  let (numberOfMessage, bytes) ← decodeUInt 2 bytes
  let (sequenceNumber, bytes) ← decodeUInt 2 bytes
  let (instrumentGroupCode, bytes) ← Alpha.decode 3 bytes
  let (fillerAsciiStr1, bytes) ← Alpha.decode 1 bytes
  let (priorityIndicator, bytes) ← PriorityIndicator.decode bytes
  let (typeOfMessage, bytes) ← TypeOfMessage.decode bytes
  let (addressType, bytes) ← Alpha.decode 2 bytes
  let (title, bytes) ← Alpha.decode 80 bytes
  let (text, bytes) ← Alpha.decode 854 bytes
  let (fillerAsciiStr2, bytes) ← Alpha.decode 2 bytes
  pure ({ sourceSeqNum, sourceTime, systemId, sourceTimeMicroSecs, eMailMsgNumber, numberOfMessage, sequenceNumber, instrumentGroupCode, fillerAsciiStr1, priorityIndicator, typeOfMessage, addressType, title, text, fillerAsciiStr2 }, bytes)

@[simp] theorem encode_length (message : MailMessage) : (encode message).length = 964 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, PriorityIndicator.encode_length, TypeOfMessage.encode_length]

theorem encode_length_pos (message : MailMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MailMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PriorityIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TypeOfMessage.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MailMessage

/-- Indicative Matching Price Message: 32 bytes -/
structure IndicativeMatchingPriceMessage where
  symbolIndex : BitVec 32
  sourceSeqNum : BitVec 32
  sourceTime : BitVec 32
  imPrice : BitVec 32
  variation : BitVec 32
  systemId : BitVec 32
  sourceTimeMicroSecs : BitVec 16
  priceScaleCode : BitVec 8
  variationScaleCode : BitVec 8
  imVolume : BitVec 32
  deriving DecidableEq, Repr

namespace IndicativeMatchingPriceMessage

def encode (message : IndicativeMatchingPriceMessage) : List UInt8 :=
  encodeUInt 4 message.symbolIndex
    ++ (encodeUInt 4 message.sourceSeqNum
    ++ (encodeUInt 4 message.sourceTime
    ++ (encodeUInt 4 message.imPrice
    ++ (encodeUInt 4 message.variation
    ++ (encodeUInt 4 message.systemId
    ++ (encodeUInt 2 message.sourceTimeMicroSecs
    ++ (encodeUInt 1 message.priceScaleCode
    ++ (encodeUInt 1 message.variationScaleCode
    ++ (encodeUInt 4 message.imVolume)))))))))

def decode (bytes : List UInt8) : Option (IndicativeMatchingPriceMessage × List UInt8) := do
  let (symbolIndex, bytes) ← decodeUInt 4 bytes
  let (sourceSeqNum, bytes) ← decodeUInt 4 bytes
  let (sourceTime, bytes) ← decodeUInt 4 bytes
  let (imPrice, bytes) ← decodeUInt 4 bytes
  let (variation, bytes) ← decodeUInt 4 bytes
  let (systemId, bytes) ← decodeUInt 4 bytes
  let (sourceTimeMicroSecs, bytes) ← decodeUInt 2 bytes
  let (priceScaleCode, bytes) ← decodeUInt 1 bytes
  let (variationScaleCode, bytes) ← decodeUInt 1 bytes
  let (imVolume, bytes) ← decodeUInt 4 bytes
  pure ({ symbolIndex, sourceSeqNum, sourceTime, imPrice, variation, systemId, sourceTimeMicroSecs, priceScaleCode, variationScaleCode, imVolume }, bytes)

@[simp] theorem encode_length (message : IndicativeMatchingPriceMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : IndicativeMatchingPriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IndicativeMatchingPriceMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end IndicativeMatchingPriceMessage

/-- Collars Message: 32 bytes -/
structure CollarsMessage where
  symbolIndex : BitVec 32
  sourceSeqNum : BitVec 32
  sourceTime : BitVec 32
  highCollar : BitVec 32
  lowCollar : BitVec 32
  systemId : BitVec 32
  sourceTimeMicroSecs : BitVec 16
  highScaleCode : BitVec 8
  lowScaleCode : BitVec 8
  collarType : CollarType
  fillerAsciiStr3 : Alpha 3
  deriving DecidableEq, Repr

namespace CollarsMessage

def encode (message : CollarsMessage) : List UInt8 :=
  encodeUInt 4 message.symbolIndex
    ++ (encodeUInt 4 message.sourceSeqNum
    ++ (encodeUInt 4 message.sourceTime
    ++ (encodeUInt 4 message.highCollar
    ++ (encodeUInt 4 message.lowCollar
    ++ (encodeUInt 4 message.systemId
    ++ (encodeUInt 2 message.sourceTimeMicroSecs
    ++ (encodeUInt 1 message.highScaleCode
    ++ (encodeUInt 1 message.lowScaleCode
    ++ (CollarType.encode message.collarType
    ++ (Alpha.encode message.fillerAsciiStr3))))))))))

def decode (bytes : List UInt8) : Option (CollarsMessage × List UInt8) := do
  let (symbolIndex, bytes) ← decodeUInt 4 bytes
  let (sourceSeqNum, bytes) ← decodeUInt 4 bytes
  let (sourceTime, bytes) ← decodeUInt 4 bytes
  let (highCollar, bytes) ← decodeUInt 4 bytes
  let (lowCollar, bytes) ← decodeUInt 4 bytes
  let (systemId, bytes) ← decodeUInt 4 bytes
  let (sourceTimeMicroSecs, bytes) ← decodeUInt 2 bytes
  let (highScaleCode, bytes) ← decodeUInt 1 bytes
  let (lowScaleCode, bytes) ← decodeUInt 1 bytes
  let (collarType, bytes) ← CollarType.decode bytes
  let (fillerAsciiStr3, bytes) ← Alpha.decode 3 bytes
  pure ({ symbolIndex, sourceSeqNum, sourceTime, highCollar, lowCollar, systemId, sourceTimeMicroSecs, highScaleCode, lowScaleCode, collarType, fillerAsciiStr3 }, bytes)

@[simp] theorem encode_length (message : CollarsMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, CollarType.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : CollarsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CollarsMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, CollarType.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end CollarsMessage

/-- Session Timetable Message: 80 bytes -/
structure SessionTimetableMessage where
  sourceSeqNum : BitVec 32
  sourceTime : BitVec 32
  systemId : BitVec 32
  sourceTimeMicroSecs : BitVec 16
  instrumentGroupCode : Alpha 3
  sessionType : SessionType
  timePreOpening1 : Alpha 6
  timeOpening1 : Alpha 6
  timeClosing1 : Alpha 6
  timePreOpening2 : Alpha 6
  timeOpening2 : Alpha 6
  timeClosing2 : Alpha 6
  timePreOpening3 : Alpha 6
  timeOpening3 : Alpha 6
  timeClosing3 : Alpha 6
  eodTime : Alpha 6
  fillerAsciiStr2 : Alpha 2
  deriving DecidableEq, Repr

namespace SessionTimetableMessage

def encode (message : SessionTimetableMessage) : List UInt8 :=
  encodeUInt 4 message.sourceSeqNum
    ++ (encodeUInt 4 message.sourceTime
    ++ (encodeUInt 4 message.systemId
    ++ (encodeUInt 2 message.sourceTimeMicroSecs
    ++ (Alpha.encode message.instrumentGroupCode
    ++ (SessionType.encode message.sessionType
    ++ (Alpha.encode message.timePreOpening1
    ++ (Alpha.encode message.timeOpening1
    ++ (Alpha.encode message.timeClosing1
    ++ (Alpha.encode message.timePreOpening2
    ++ (Alpha.encode message.timeOpening2
    ++ (Alpha.encode message.timeClosing2
    ++ (Alpha.encode message.timePreOpening3
    ++ (Alpha.encode message.timeOpening3
    ++ (Alpha.encode message.timeClosing3
    ++ (Alpha.encode message.eodTime
    ++ (Alpha.encode message.fillerAsciiStr2))))))))))))))))

def decode (bytes : List UInt8) : Option (SessionTimetableMessage × List UInt8) := do
  let (sourceSeqNum, bytes) ← decodeUInt 4 bytes
  let (sourceTime, bytes) ← decodeUInt 4 bytes
  let (systemId, bytes) ← decodeUInt 4 bytes
  let (sourceTimeMicroSecs, bytes) ← decodeUInt 2 bytes
  let (instrumentGroupCode, bytes) ← Alpha.decode 3 bytes
  let (sessionType, bytes) ← SessionType.decode bytes
  let (timePreOpening1, bytes) ← Alpha.decode 6 bytes
  let (timeOpening1, bytes) ← Alpha.decode 6 bytes
  let (timeClosing1, bytes) ← Alpha.decode 6 bytes
  let (timePreOpening2, bytes) ← Alpha.decode 6 bytes
  let (timeOpening2, bytes) ← Alpha.decode 6 bytes
  let (timeClosing2, bytes) ← Alpha.decode 6 bytes
  let (timePreOpening3, bytes) ← Alpha.decode 6 bytes
  let (timeOpening3, bytes) ← Alpha.decode 6 bytes
  let (timeClosing3, bytes) ← Alpha.decode 6 bytes
  let (eodTime, bytes) ← Alpha.decode 6 bytes
  let (fillerAsciiStr2, bytes) ← Alpha.decode 2 bytes
  pure ({ sourceSeqNum, sourceTime, systemId, sourceTimeMicroSecs, instrumentGroupCode, sessionType, timePreOpening1, timeOpening1, timeClosing1, timePreOpening2, timeOpening2, timeClosing2, timePreOpening3, timeOpening3, timeClosing3, eodTime, fillerAsciiStr2 }, bytes)

@[simp] theorem encode_length (message : SessionTimetableMessage) : (encode message).length = 80 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, SessionType.encode_length]

theorem encode_length_pos (message : SessionTimetableMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SessionTimetableMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SessionType.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SessionTimetableMessage

/-- Global Market Activity Summary Message: 30 bytes -/
structure GlobalMarketActivitySummaryMessage where
  sourceSeqNum : BitVec 32
  sourceTime : BitVec 32
  systemId : BitVec 32
  sourceTimeMicroSecs : BitVec 16
  nbTrades : BitVec 32
  qtyShares : BitVec 32
  amountTraded : BitVec 32
  priceScaleCode : BitVec 8
  fillerAsciiStr3 : Alpha 3
  deriving DecidableEq, Repr

namespace GlobalMarketActivitySummaryMessage

def encode (message : GlobalMarketActivitySummaryMessage) : List UInt8 :=
  encodeUInt 4 message.sourceSeqNum
    ++ (encodeUInt 4 message.sourceTime
    ++ (encodeUInt 4 message.systemId
    ++ (encodeUInt 2 message.sourceTimeMicroSecs
    ++ (encodeUInt 4 message.nbTrades
    ++ (encodeUInt 4 message.qtyShares
    ++ (encodeUInt 4 message.amountTraded
    ++ (encodeUInt 1 message.priceScaleCode
    ++ (Alpha.encode message.fillerAsciiStr3))))))))

def decode (bytes : List UInt8) : Option (GlobalMarketActivitySummaryMessage × List UInt8) := do
  let (sourceSeqNum, bytes) ← decodeUInt 4 bytes
  let (sourceTime, bytes) ← decodeUInt 4 bytes
  let (systemId, bytes) ← decodeUInt 4 bytes
  let (sourceTimeMicroSecs, bytes) ← decodeUInt 2 bytes
  let (nbTrades, bytes) ← decodeUInt 4 bytes
  let (qtyShares, bytes) ← decodeUInt 4 bytes
  let (amountTraded, bytes) ← decodeUInt 4 bytes
  let (priceScaleCode, bytes) ← decodeUInt 1 bytes
  let (fillerAsciiStr3, bytes) ← Alpha.decode 3 bytes
  pure ({ sourceSeqNum, sourceTime, systemId, sourceTimeMicroSecs, nbTrades, qtyShares, amountTraded, priceScaleCode, fillerAsciiStr3 }, bytes)

@[simp] theorem encode_length (message : GlobalMarketActivitySummaryMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : GlobalMarketActivitySummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : GlobalMarketActivitySummaryMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end GlobalMarketActivitySummaryMessage

/-- Start Referential Message: 4 bytes -/
structure StartReferentialMessage where
  indicator : Alpha 1
  fillerAsciiStr3 : Alpha 3
  deriving DecidableEq, Repr

namespace StartReferentialMessage

def encode (message : StartReferentialMessage) : List UInt8 :=
  Alpha.encode message.indicator
    ++ (Alpha.encode message.fillerAsciiStr3)

def decode (bytes : List UInt8) : Option (StartReferentialMessage × List UInt8) := do
  let (indicator, bytes) ← Alpha.decode 1 bytes
  let (fillerAsciiStr3, bytes) ← Alpha.decode 3 bytes
  pure ({ indicator, fillerAsciiStr3 }, bytes)

@[simp] theorem encode_length (message : StartReferentialMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : StartReferentialMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StartReferentialMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StartReferentialMessage

/-- End Referential Message: 4 bytes -/
structure EndReferentialMessage where
  indicator : Alpha 1
  fillerAsciiStr3 : Alpha 3
  deriving DecidableEq, Repr

namespace EndReferentialMessage

def encode (message : EndReferentialMessage) : List UInt8 :=
  Alpha.encode message.indicator
    ++ (Alpha.encode message.fillerAsciiStr3)

def decode (bytes : List UInt8) : Option (EndReferentialMessage × List UInt8) := do
  let (indicator, bytes) ← Alpha.decode 1 bytes
  let (fillerAsciiStr3, bytes) ← Alpha.decode 3 bytes
  pure ({ indicator, fillerAsciiStr3 }, bytes)

@[simp] theorem encode_length (message : EndReferentialMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : EndReferentialMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EndReferentialMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end EndReferentialMessage

/-- Referential Message: 492 bytes -/
structure ReferentialMessage where
  symbolIndex : BitVec 32
  sourceSeqNum : BitVec 32
  sourceTime : BitVec 32
  lastAdjPrice : BitVec 32
  systemId : BitVec 32
  prevVolumeTraded : BitVec 32
  fixPriceTick : BitVec 32
  sourceTimeMicroSecs : BitVec 16
  stockExchangeCode : BitVec 16
  typeOfInstrument : BitVec 16
  eventDate : Alpha 8
  instrumentName : Alpha 18
  periodIndicator : PeriodIndicator
  typeOfMarketAdmission : Alpha 1
  issuingCountryCode : Alpha 3
  tradingCurrency : Alpha 3
  instrumentGroupCode : Alpha 3
  instrumentCategory : InstrumentCategory
  instrumentCode : Alpha 12
  dateOfLastTrade : Alpha 8
  underlyingRepoIsinCode : Alpha 12
  repoExpiryDate : Alpha 8
  firstSettlementDate : Alpha 8
  typeOfDerivatives : TypeOfDerivatives
  bicDepositary : Alpha 11
  icb : Alpha 4
  mic : Alpha 4
  underlyingWisinCode : Alpha 12
  depositaryList : Alpha 25
  mainDepositary : Alpha 5
  typeOfCorporateEvent : Alpha 2
  timeLagEuronextUtc : Alpha 5
  timeLagMiFidRegUtc : Alpha 5
  cfi : Alpha 6
  quantityNotation : Alpha 4
  indexSetOfVarPriceTick : Alpha 2
  marketFeedCode : Alpha 2
  micList : Alpha 24
  industryCode : Alpha 4
  industryText : Alpha 100
  financialMarketCode : Alpha 3
  usIndicators : Alpha 7
  fillerAsciiStr2 : Alpha 2
  prevDayCapitalTraded : BitVec 64
  nomMktPrice : BitVec 64
  lotSize : BitVec 64
  numberInstrumentCirc : BitVec 64
  sharesOut : BitVec 64
  authShares : BitVec 64
  headingNumber : BitVec 16
  sectionNumber : BitVec 8
  repoIndicator : RepoIndicator
  lastAdjPriceScaleCode : BitVec 8
  typeOfUnitExp : BitVec 8
  marketIndicator : BitVec 8
  prevDayCapitalTradedScaleCode : BitVec 8
  taxCode : BitVec 8
  nomMkdtPriceScaleCode : BitVec 8
  lotSizeScaleCode : BitVec 8
  fixPriceTickScaleCode : BitVec 8
  mnemo : Alpha 5
  tradingCode : Alpha 12
  fillerAsciiStr3 : Alpha 3
  strikePrice : BitVec 32
  strikeCurrency : Alpha 3
  strikeScaleCode : BitVec 8
  currencyCoef : BitVec 32
  currencyCoefScaleCode : BitVec 8
  tradingCurrencyIndicator : BitVec 8
  strikeCurrencyIndicator : BitVec 8
  marketSegment : Alpha 2
  algo : Algo
  localName : Alpha 30
  smallTrade : BitVec 32
  fillerBinaryInt12 : Alpha 12
  deriving DecidableEq, Repr

namespace ReferentialMessage

def encode (message : ReferentialMessage) : List UInt8 :=
  encodeUInt 4 message.symbolIndex
    ++ (encodeUInt 4 message.sourceSeqNum
    ++ (encodeUInt 4 message.sourceTime
    ++ (encodeUInt 4 message.lastAdjPrice
    ++ (encodeUInt 4 message.systemId
    ++ (encodeUInt 4 message.prevVolumeTraded
    ++ (encodeUInt 4 message.fixPriceTick
    ++ (encodeUInt 2 message.sourceTimeMicroSecs
    ++ (encodeUInt 2 message.stockExchangeCode
    ++ (encodeUInt 2 message.typeOfInstrument
    ++ (Alpha.encode message.eventDate
    ++ (Alpha.encode message.instrumentName
    ++ (PeriodIndicator.encode message.periodIndicator
    ++ (Alpha.encode message.typeOfMarketAdmission
    ++ (Alpha.encode message.issuingCountryCode
    ++ (Alpha.encode message.tradingCurrency
    ++ (Alpha.encode message.instrumentGroupCode
    ++ (InstrumentCategory.encode message.instrumentCategory
    ++ (Alpha.encode message.instrumentCode
    ++ (Alpha.encode message.dateOfLastTrade
    ++ (Alpha.encode message.underlyingRepoIsinCode
    ++ (Alpha.encode message.repoExpiryDate
    ++ (Alpha.encode message.firstSettlementDate
    ++ (TypeOfDerivatives.encode message.typeOfDerivatives
    ++ (Alpha.encode message.bicDepositary
    ++ (Alpha.encode message.icb
    ++ (Alpha.encode message.mic
    ++ (Alpha.encode message.underlyingWisinCode
    ++ (Alpha.encode message.depositaryList
    ++ (Alpha.encode message.mainDepositary
    ++ (Alpha.encode message.typeOfCorporateEvent
    ++ (Alpha.encode message.timeLagEuronextUtc
    ++ (Alpha.encode message.timeLagMiFidRegUtc
    ++ (Alpha.encode message.cfi
    ++ (Alpha.encode message.quantityNotation
    ++ (Alpha.encode message.indexSetOfVarPriceTick
    ++ (Alpha.encode message.marketFeedCode
    ++ (Alpha.encode message.micList
    ++ (Alpha.encode message.industryCode
    ++ (Alpha.encode message.industryText
    ++ (Alpha.encode message.financialMarketCode
    ++ (Alpha.encode message.usIndicators
    ++ (Alpha.encode message.fillerAsciiStr2
    ++ (encodeUInt 8 message.prevDayCapitalTraded
    ++ (encodeUInt 8 message.nomMktPrice
    ++ (encodeUInt 8 message.lotSize
    ++ (encodeUInt 8 message.numberInstrumentCirc
    ++ (encodeUInt 8 message.sharesOut
    ++ (encodeUInt 8 message.authShares
    ++ (encodeUInt 2 message.headingNumber
    ++ (encodeUInt 1 message.sectionNumber
    ++ (RepoIndicator.encode message.repoIndicator
    ++ (encodeUInt 1 message.lastAdjPriceScaleCode
    ++ (encodeUInt 1 message.typeOfUnitExp
    ++ (encodeUInt 1 message.marketIndicator
    ++ (encodeUInt 1 message.prevDayCapitalTradedScaleCode
    ++ (encodeUInt 1 message.taxCode
    ++ (encodeUInt 1 message.nomMkdtPriceScaleCode
    ++ (encodeUInt 1 message.lotSizeScaleCode
    ++ (encodeUInt 1 message.fixPriceTickScaleCode
    ++ (Alpha.encode message.mnemo
    ++ (Alpha.encode message.tradingCode
    ++ (Alpha.encode message.fillerAsciiStr3
    ++ (encodeUInt 4 message.strikePrice
    ++ (Alpha.encode message.strikeCurrency
    ++ (encodeUInt 1 message.strikeScaleCode
    ++ (encodeUInt 4 message.currencyCoef
    ++ (encodeUInt 1 message.currencyCoefScaleCode
    ++ (encodeUInt 1 message.tradingCurrencyIndicator
    ++ (encodeUInt 1 message.strikeCurrencyIndicator
    ++ (Alpha.encode message.marketSegment
    ++ (Algo.encode message.algo
    ++ (Alpha.encode message.localName
    ++ (encodeUInt 4 message.smallTrade
    ++ (Alpha.encode message.fillerBinaryInt12))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ReferentialMessage × List UInt8) := do
  let (symbolIndex, bytes) ← decodeUInt 4 bytes
  let (sourceSeqNum, bytes) ← decodeUInt 4 bytes
  let (sourceTime, bytes) ← decodeUInt 4 bytes
  let (lastAdjPrice, bytes) ← decodeUInt 4 bytes
  let (systemId, bytes) ← decodeUInt 4 bytes
  let (prevVolumeTraded, bytes) ← decodeUInt 4 bytes
  let (fixPriceTick, bytes) ← decodeUInt 4 bytes
  let (sourceTimeMicroSecs, bytes) ← decodeUInt 2 bytes
  let (stockExchangeCode, bytes) ← decodeUInt 2 bytes
  let (typeOfInstrument, bytes) ← decodeUInt 2 bytes
  let (eventDate, bytes) ← Alpha.decode 8 bytes
  let (instrumentName, bytes) ← Alpha.decode 18 bytes
  let (periodIndicator, bytes) ← PeriodIndicator.decode bytes
  let (typeOfMarketAdmission, bytes) ← Alpha.decode 1 bytes
  let (issuingCountryCode, bytes) ← Alpha.decode 3 bytes
  let (tradingCurrency, bytes) ← Alpha.decode 3 bytes
  let (instrumentGroupCode, bytes) ← Alpha.decode 3 bytes
  let (instrumentCategory, bytes) ← InstrumentCategory.decode bytes
  let (instrumentCode, bytes) ← Alpha.decode 12 bytes
  let (dateOfLastTrade, bytes) ← Alpha.decode 8 bytes
  let (underlyingRepoIsinCode, bytes) ← Alpha.decode 12 bytes
  let (repoExpiryDate, bytes) ← Alpha.decode 8 bytes
  let (firstSettlementDate, bytes) ← Alpha.decode 8 bytes
  let (typeOfDerivatives, bytes) ← TypeOfDerivatives.decode bytes
  let (bicDepositary, bytes) ← Alpha.decode 11 bytes
  let (icb, bytes) ← Alpha.decode 4 bytes
  let (mic, bytes) ← Alpha.decode 4 bytes
  let (underlyingWisinCode, bytes) ← Alpha.decode 12 bytes
  let (depositaryList, bytes) ← Alpha.decode 25 bytes
  let (mainDepositary, bytes) ← Alpha.decode 5 bytes
  let (typeOfCorporateEvent, bytes) ← Alpha.decode 2 bytes
  let (timeLagEuronextUtc, bytes) ← Alpha.decode 5 bytes
  let (timeLagMiFidRegUtc, bytes) ← Alpha.decode 5 bytes
  let (cfi, bytes) ← Alpha.decode 6 bytes
  let (quantityNotation, bytes) ← Alpha.decode 4 bytes
  let (indexSetOfVarPriceTick, bytes) ← Alpha.decode 2 bytes
  let (marketFeedCode, bytes) ← Alpha.decode 2 bytes
  let (micList, bytes) ← Alpha.decode 24 bytes
  let (industryCode, bytes) ← Alpha.decode 4 bytes
  let (industryText, bytes) ← Alpha.decode 100 bytes
  let (financialMarketCode, bytes) ← Alpha.decode 3 bytes
  let (usIndicators, bytes) ← Alpha.decode 7 bytes
  let (fillerAsciiStr2, bytes) ← Alpha.decode 2 bytes
  let (prevDayCapitalTraded, bytes) ← decodeUInt 8 bytes
  let (nomMktPrice, bytes) ← decodeUInt 8 bytes
  let (lotSize, bytes) ← decodeUInt 8 bytes
  let (numberInstrumentCirc, bytes) ← decodeUInt 8 bytes
  let (sharesOut, bytes) ← decodeUInt 8 bytes
  let (authShares, bytes) ← decodeUInt 8 bytes
  let (headingNumber, bytes) ← decodeUInt 2 bytes
  let (sectionNumber, bytes) ← decodeUInt 1 bytes
  let (repoIndicator, bytes) ← RepoIndicator.decode bytes
  let (lastAdjPriceScaleCode, bytes) ← decodeUInt 1 bytes
  let (typeOfUnitExp, bytes) ← decodeUInt 1 bytes
  let (marketIndicator, bytes) ← decodeUInt 1 bytes
  let (prevDayCapitalTradedScaleCode, bytes) ← decodeUInt 1 bytes
  let (taxCode, bytes) ← decodeUInt 1 bytes
  let (nomMkdtPriceScaleCode, bytes) ← decodeUInt 1 bytes
  let (lotSizeScaleCode, bytes) ← decodeUInt 1 bytes
  let (fixPriceTickScaleCode, bytes) ← decodeUInt 1 bytes
  let (mnemo, bytes) ← Alpha.decode 5 bytes
  let (tradingCode, bytes) ← Alpha.decode 12 bytes
  let (fillerAsciiStr3, bytes) ← Alpha.decode 3 bytes
  let (strikePrice, bytes) ← decodeUInt 4 bytes
  let (strikeCurrency, bytes) ← Alpha.decode 3 bytes
  let (strikeScaleCode, bytes) ← decodeUInt 1 bytes
  let (currencyCoef, bytes) ← decodeUInt 4 bytes
  let (currencyCoefScaleCode, bytes) ← decodeUInt 1 bytes
  let (tradingCurrencyIndicator, bytes) ← decodeUInt 1 bytes
  let (strikeCurrencyIndicator, bytes) ← decodeUInt 1 bytes
  let (marketSegment, bytes) ← Alpha.decode 2 bytes
  let (algo, bytes) ← Algo.decode bytes
  let (localName, bytes) ← Alpha.decode 30 bytes
  let (smallTrade, bytes) ← decodeUInt 4 bytes
  let (fillerBinaryInt12, bytes) ← Alpha.decode 12 bytes
  pure ({ symbolIndex, sourceSeqNum, sourceTime, lastAdjPrice, systemId, prevVolumeTraded, fixPriceTick, sourceTimeMicroSecs, stockExchangeCode, typeOfInstrument, eventDate, instrumentName, periodIndicator, typeOfMarketAdmission, issuingCountryCode, tradingCurrency, instrumentGroupCode, instrumentCategory, instrumentCode, dateOfLastTrade, underlyingRepoIsinCode, repoExpiryDate, firstSettlementDate, typeOfDerivatives, bicDepositary, icb, mic, underlyingWisinCode, depositaryList, mainDepositary, typeOfCorporateEvent, timeLagEuronextUtc, timeLagMiFidRegUtc, cfi, quantityNotation, indexSetOfVarPriceTick, marketFeedCode, micList, industryCode, industryText, financialMarketCode, usIndicators, fillerAsciiStr2, prevDayCapitalTraded, nomMktPrice, lotSize, numberInstrumentCirc, sharesOut, authShares, headingNumber, sectionNumber, repoIndicator, lastAdjPriceScaleCode, typeOfUnitExp, marketIndicator, prevDayCapitalTradedScaleCode, taxCode, nomMkdtPriceScaleCode, lotSizeScaleCode, fixPriceTickScaleCode, mnemo, tradingCode, fillerAsciiStr3, strikePrice, strikeCurrency, strikeScaleCode, currencyCoef, currencyCoefScaleCode, tradingCurrencyIndicator, strikeCurrencyIndicator, marketSegment, algo, localName, smallTrade, fillerBinaryInt12 }, bytes)

@[simp] theorem encode_length (message : ReferentialMessage) : (encode message).length = 492 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, PeriodIndicator.encode_length, InstrumentCategory.encode_length, TypeOfDerivatives.encode_length, RepoIndicator.encode_length, Algo.encode_length]

theorem encode_length_pos (message : ReferentialMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ReferentialMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, PeriodIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentCategory.decode_encode, some_bind]
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
  rw [List.append_assoc, TypeOfDerivatives.decode_encode, some_bind]
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
  rw [List.append_assoc, RepoIndicator.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Algo.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ReferentialMessage

/-- Trade Creation Message: 40 bytes -/
structure TradeCreationMessage where
  symbolIndex : BitVec 32
  sourceTime : BitVec 32
  tradeIdNumber : BitVec 32
  quoteLinkId : BitVec 32
  sourceSeqNum : BitVec 32
  price : BitVec 32
  volume : BitVec 32
  systemId : BitVec 32
  sourceTimeMicroSecs : BitVec 16
  smallTradeIndicator : SmallTradeIndicator
  tradCond2 : TradCond2
  tradCond3 : TradCond3
  tradeOrigin : TradeOrigin
  openingTradeIndicator : OpeningTradeIndicator
  priceScaleCode : BitVec 8
  deriving DecidableEq, Repr

namespace TradeCreationMessage

def encode (message : TradeCreationMessage) : List UInt8 :=
  encodeUInt 4 message.symbolIndex
    ++ (encodeUInt 4 message.sourceTime
    ++ (encodeUInt 4 message.tradeIdNumber
    ++ (encodeUInt 4 message.quoteLinkId
    ++ (encodeUInt 4 message.sourceSeqNum
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 4 message.systemId
    ++ (encodeUInt 2 message.sourceTimeMicroSecs
    ++ (SmallTradeIndicator.encode message.smallTradeIndicator
    ++ (TradCond2.encode message.tradCond2
    ++ (TradCond3.encode message.tradCond3
    ++ (TradeOrigin.encode message.tradeOrigin
    ++ (OpeningTradeIndicator.encode message.openingTradeIndicator
    ++ (encodeUInt 1 message.priceScaleCode))))))))))))))

def decode (bytes : List UInt8) : Option (TradeCreationMessage × List UInt8) := do
  let (symbolIndex, bytes) ← decodeUInt 4 bytes
  let (sourceTime, bytes) ← decodeUInt 4 bytes
  let (tradeIdNumber, bytes) ← decodeUInt 4 bytes
  let (quoteLinkId, bytes) ← decodeUInt 4 bytes
  let (sourceSeqNum, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (systemId, bytes) ← decodeUInt 4 bytes
  let (sourceTimeMicroSecs, bytes) ← decodeUInt 2 bytes
  let (smallTradeIndicator, bytes) ← SmallTradeIndicator.decode bytes
  let (tradCond2, bytes) ← TradCond2.decode bytes
  let (tradCond3, bytes) ← TradCond3.decode bytes
  let (tradeOrigin, bytes) ← TradeOrigin.decode bytes
  let (openingTradeIndicator, bytes) ← OpeningTradeIndicator.decode bytes
  let (priceScaleCode, bytes) ← decodeUInt 1 bytes
  pure ({ symbolIndex, sourceTime, tradeIdNumber, quoteLinkId, sourceSeqNum, price, volume, systemId, sourceTimeMicroSecs, smallTradeIndicator, tradCond2, tradCond3, tradeOrigin, openingTradeIndicator, priceScaleCode }, bytes)

@[simp] theorem encode_length (message : TradeCreationMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, SmallTradeIndicator.encode_length, TradCond2.encode_length, TradCond3.encode_length, TradeOrigin.encode_length, OpeningTradeIndicator.encode_length]

theorem encode_length_pos (message : TradeCreationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCreationMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, SmallTradeIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradCond2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradCond3.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeOrigin.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpeningTradeIndicator.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TradeCreationMessage

/-- Trade Cancellation Message: 24 bytes -/
structure TradeCancellationMessage where
  symbolIndex : BitVec 32
  sourceTime : BitVec 32
  sourceSeqNum : BitVec 32
  originalTradeIdNumber : BitVec 32
  systemId : BitVec 32
  sourceTimeMicroSecs : BitVec 16
  fillerBinaryInt2 : Alpha 2
  deriving DecidableEq, Repr

namespace TradeCancellationMessage

def encode (message : TradeCancellationMessage) : List UInt8 :=
  encodeUInt 4 message.symbolIndex
    ++ (encodeUInt 4 message.sourceTime
    ++ (encodeUInt 4 message.sourceSeqNum
    ++ (encodeUInt 4 message.originalTradeIdNumber
    ++ (encodeUInt 4 message.systemId
    ++ (encodeUInt 2 message.sourceTimeMicroSecs
    ++ (Alpha.encode message.fillerBinaryInt2))))))

def decode (bytes : List UInt8) : Option (TradeCancellationMessage × List UInt8) := do
  let (symbolIndex, bytes) ← decodeUInt 4 bytes
  let (sourceTime, bytes) ← decodeUInt 4 bytes
  let (sourceSeqNum, bytes) ← decodeUInt 4 bytes
  let (originalTradeIdNumber, bytes) ← decodeUInt 4 bytes
  let (systemId, bytes) ← decodeUInt 4 bytes
  let (sourceTimeMicroSecs, bytes) ← decodeUInt 2 bytes
  let (fillerBinaryInt2, bytes) ← Alpha.decode 2 bytes
  pure ({ symbolIndex, sourceTime, sourceSeqNum, originalTradeIdNumber, systemId, sourceTimeMicroSecs, fillerBinaryInt2 }, bytes)

@[simp] theorem encode_length (message : TradeCancellationMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : TradeCancellationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCancellationMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeCancellationMessage

/-- Trade Full Information Message: 60 bytes -/
structure TradeFullInformationMessage where
  symbolIndex : BitVec 32
  sourceTime : BitVec 32
  tradeIdNumber : BitVec 32
  quoteLinkId : BitVec 32
  sourceSeqNum : BitVec 32
  price : BitVec 32
  volume : BitVec 32
  cumulativeQuantity : BitVec 32
  highestPrice : BitVec 32
  lowestPrice : BitVec 32
  variationLastPrice : BitVec 32
  systemId : BitVec 32
  sourceTimeMicroSecs : BitVec 16
  fillerBinaryInt2 : Alpha 2
  smallTradeIndicator : SmallTradeIndicator
  tradCond2 : TradCond2
  tradCond3 : TradCond3
  tradeOrigin : TradeOrigin
  tickDirection : TickDirection
  openingTradeIndicator : OpeningTradeIndicator
  variationScaleCode : BitVec 8
  priceScaleCode : BitVec 8
  deriving DecidableEq, Repr

namespace TradeFullInformationMessage

def encode (message : TradeFullInformationMessage) : List UInt8 :=
  encodeUInt 4 message.symbolIndex
    ++ (encodeUInt 4 message.sourceTime
    ++ (encodeUInt 4 message.tradeIdNumber
    ++ (encodeUInt 4 message.quoteLinkId
    ++ (encodeUInt 4 message.sourceSeqNum
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 4 message.cumulativeQuantity
    ++ (encodeUInt 4 message.highestPrice
    ++ (encodeUInt 4 message.lowestPrice
    ++ (encodeUInt 4 message.variationLastPrice
    ++ (encodeUInt 4 message.systemId
    ++ (encodeUInt 2 message.sourceTimeMicroSecs
    ++ (Alpha.encode message.fillerBinaryInt2
    ++ (SmallTradeIndicator.encode message.smallTradeIndicator
    ++ (TradCond2.encode message.tradCond2
    ++ (TradCond3.encode message.tradCond3
    ++ (TradeOrigin.encode message.tradeOrigin
    ++ (TickDirection.encode message.tickDirection
    ++ (OpeningTradeIndicator.encode message.openingTradeIndicator
    ++ (encodeUInt 1 message.variationScaleCode
    ++ (encodeUInt 1 message.priceScaleCode)))))))))))))))))))))

def decode (bytes : List UInt8) : Option (TradeFullInformationMessage × List UInt8) := do
  let (symbolIndex, bytes) ← decodeUInt 4 bytes
  let (sourceTime, bytes) ← decodeUInt 4 bytes
  let (tradeIdNumber, bytes) ← decodeUInt 4 bytes
  let (quoteLinkId, bytes) ← decodeUInt 4 bytes
  let (sourceSeqNum, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (cumulativeQuantity, bytes) ← decodeUInt 4 bytes
  let (highestPrice, bytes) ← decodeUInt 4 bytes
  let (lowestPrice, bytes) ← decodeUInt 4 bytes
  let (variationLastPrice, bytes) ← decodeUInt 4 bytes
  let (systemId, bytes) ← decodeUInt 4 bytes
  let (sourceTimeMicroSecs, bytes) ← decodeUInt 2 bytes
  let (fillerBinaryInt2, bytes) ← Alpha.decode 2 bytes
  let (smallTradeIndicator, bytes) ← SmallTradeIndicator.decode bytes
  let (tradCond2, bytes) ← TradCond2.decode bytes
  let (tradCond3, bytes) ← TradCond3.decode bytes
  let (tradeOrigin, bytes) ← TradeOrigin.decode bytes
  let (tickDirection, bytes) ← TickDirection.decode bytes
  let (openingTradeIndicator, bytes) ← OpeningTradeIndicator.decode bytes
  let (variationScaleCode, bytes) ← decodeUInt 1 bytes
  let (priceScaleCode, bytes) ← decodeUInt 1 bytes
  pure ({ symbolIndex, sourceTime, tradeIdNumber, quoteLinkId, sourceSeqNum, price, volume, cumulativeQuantity, highestPrice, lowestPrice, variationLastPrice, systemId, sourceTimeMicroSecs, fillerBinaryInt2, smallTradeIndicator, tradCond2, tradCond3, tradeOrigin, tickDirection, openingTradeIndicator, variationScaleCode, priceScaleCode }, bytes)

@[simp] theorem encode_length (message : TradeFullInformationMessage) : (encode message).length = 60 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, SmallTradeIndicator.encode_length, TradCond2.encode_length, TradCond3.encode_length, TradeOrigin.encode_length, TickDirection.encode_length, OpeningTradeIndicator.encode_length]

theorem encode_length_pos (message : TradeFullInformationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeFullInformationMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, SmallTradeIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradCond2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradCond3.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeOrigin.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TickDirection.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpeningTradeIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TradeFullInformationMessage

/-- Price Update Message: 40 bytes -/
structure PriceUpdateMessage where
  symbolIndex : BitVec 32
  sourceTime : BitVec 32
  sourceSeqNum : BitVec 32
  price : BitVec 32
  highestPrice : BitVec 32
  lowestPrice : BitVec 32
  variationLastPrice : BitVec 32
  systemId : BitVec 32
  sourceTimeMicroSecs : BitVec 16
  typeOfPrice : BitVec 16
  fillerBinaryInt2 : Alpha 2
  priceScaleCode : BitVec 8
  variationScaleCode : BitVec 8
  deriving DecidableEq, Repr

namespace PriceUpdateMessage

def encode (message : PriceUpdateMessage) : List UInt8 :=
  encodeUInt 4 message.symbolIndex
    ++ (encodeUInt 4 message.sourceTime
    ++ (encodeUInt 4 message.sourceSeqNum
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.highestPrice
    ++ (encodeUInt 4 message.lowestPrice
    ++ (encodeUInt 4 message.variationLastPrice
    ++ (encodeUInt 4 message.systemId
    ++ (encodeUInt 2 message.sourceTimeMicroSecs
    ++ (encodeUInt 2 message.typeOfPrice
    ++ (Alpha.encode message.fillerBinaryInt2
    ++ (encodeUInt 1 message.priceScaleCode
    ++ (encodeUInt 1 message.variationScaleCode))))))))))))

def decode (bytes : List UInt8) : Option (PriceUpdateMessage × List UInt8) := do
  let (symbolIndex, bytes) ← decodeUInt 4 bytes
  let (sourceTime, bytes) ← decodeUInt 4 bytes
  let (sourceSeqNum, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (highestPrice, bytes) ← decodeUInt 4 bytes
  let (lowestPrice, bytes) ← decodeUInt 4 bytes
  let (variationLastPrice, bytes) ← decodeUInt 4 bytes
  let (systemId, bytes) ← decodeUInt 4 bytes
  let (sourceTimeMicroSecs, bytes) ← decodeUInt 2 bytes
  let (typeOfPrice, bytes) ← decodeUInt 2 bytes
  let (fillerBinaryInt2, bytes) ← Alpha.decode 2 bytes
  let (priceScaleCode, bytes) ← decodeUInt 1 bytes
  let (variationScaleCode, bytes) ← decodeUInt 1 bytes
  pure ({ symbolIndex, sourceTime, sourceSeqNum, price, highestPrice, lowestPrice, variationLastPrice, systemId, sourceTimeMicroSecs, typeOfPrice, fillerBinaryInt2, priceScaleCode, variationScaleCode }, bytes)

@[simp] theorem encode_length (message : PriceUpdateMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : PriceUpdateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PriceUpdateMessage) (rest : List UInt8) :
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end PriceUpdateMessage

/-- Auction Summary Message: 48 bytes -/
structure AuctionSummaryMessage where
  symbolIndex : BitVec 32
  sourceTime : BitVec 32
  sourceSeqNum : BitVec 32
  firstPrice : BitVec 32
  lastPrice : BitVec 32
  highestPrice : BitVec 32
  lowestPrice : BitVec 32
  cumulativeQuantity : BitVec 32
  variation : BitVec 32
  systemId : BitVec 32
  sourceTimeMicroSecs : BitVec 16
  typeOfLastPrice : BitVec 16
  tickDirection : TickDirection
  instrumentValuationPrice : InstrumentValuationPrice
  priceScaleCode : BitVec 8
  variationScaleCode : BitVec 8
  deriving DecidableEq, Repr

namespace AuctionSummaryMessage

def encode (message : AuctionSummaryMessage) : List UInt8 :=
  encodeUInt 4 message.symbolIndex
    ++ (encodeUInt 4 message.sourceTime
    ++ (encodeUInt 4 message.sourceSeqNum
    ++ (encodeUInt 4 message.firstPrice
    ++ (encodeUInt 4 message.lastPrice
    ++ (encodeUInt 4 message.highestPrice
    ++ (encodeUInt 4 message.lowestPrice
    ++ (encodeUInt 4 message.cumulativeQuantity
    ++ (encodeUInt 4 message.variation
    ++ (encodeUInt 4 message.systemId
    ++ (encodeUInt 2 message.sourceTimeMicroSecs
    ++ (encodeUInt 2 message.typeOfLastPrice
    ++ (TickDirection.encode message.tickDirection
    ++ (InstrumentValuationPrice.encode message.instrumentValuationPrice
    ++ (encodeUInt 1 message.priceScaleCode
    ++ (encodeUInt 1 message.variationScaleCode)))))))))))))))

def decode (bytes : List UInt8) : Option (AuctionSummaryMessage × List UInt8) := do
  let (symbolIndex, bytes) ← decodeUInt 4 bytes
  let (sourceTime, bytes) ← decodeUInt 4 bytes
  let (sourceSeqNum, bytes) ← decodeUInt 4 bytes
  let (firstPrice, bytes) ← decodeUInt 4 bytes
  let (lastPrice, bytes) ← decodeUInt 4 bytes
  let (highestPrice, bytes) ← decodeUInt 4 bytes
  let (lowestPrice, bytes) ← decodeUInt 4 bytes
  let (cumulativeQuantity, bytes) ← decodeUInt 4 bytes
  let (variation, bytes) ← decodeUInt 4 bytes
  let (systemId, bytes) ← decodeUInt 4 bytes
  let (sourceTimeMicroSecs, bytes) ← decodeUInt 2 bytes
  let (typeOfLastPrice, bytes) ← decodeUInt 2 bytes
  let (tickDirection, bytes) ← TickDirection.decode bytes
  let (instrumentValuationPrice, bytes) ← InstrumentValuationPrice.decode bytes
  let (priceScaleCode, bytes) ← decodeUInt 1 bytes
  let (variationScaleCode, bytes) ← decodeUInt 1 bytes
  pure ({ symbolIndex, sourceTime, sourceSeqNum, firstPrice, lastPrice, highestPrice, lowestPrice, cumulativeQuantity, variation, systemId, sourceTimeMicroSecs, typeOfLastPrice, tickDirection, instrumentValuationPrice, priceScaleCode, variationScaleCode }, bytes)

@[simp] theorem encode_length (message : AuctionSummaryMessage) : (encode message).length = 48 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, TickDirection.encode_length, InstrumentValuationPrice.encode_length]

theorem encode_length_pos (message : AuctionSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AuctionSummaryMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, TickDirection.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentValuationPrice.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AuctionSummaryMessage

/-- Vwap Closing Price Message: 44 bytes -/
structure VwapClosingPriceMessage where
  symbolIndex : BitVec 32
  sourceTime : BitVec 32
  sourceSeqNum : BitVec 32
  sendingIndicator : BitVec 16
  closingPriceRule : BitVec 16
  closingPrice : BitVec 32
  adjustedClosingPrice : BitVec 32
  nbTrades : BitVec 32
  qtyShares : BitVec 32
  amountTraded : BitVec 32
  systemId : BitVec 32
  priceScaleCode : BitVec 8
  fillerAsciiStr3 : Alpha 3
  deriving DecidableEq, Repr

namespace VwapClosingPriceMessage

def encode (message : VwapClosingPriceMessage) : List UInt8 :=
  encodeUInt 4 message.symbolIndex
    ++ (encodeUInt 4 message.sourceTime
    ++ (encodeUInt 4 message.sourceSeqNum
    ++ (encodeUInt 2 message.sendingIndicator
    ++ (encodeUInt 2 message.closingPriceRule
    ++ (encodeUInt 4 message.closingPrice
    ++ (encodeUInt 4 message.adjustedClosingPrice
    ++ (encodeUInt 4 message.nbTrades
    ++ (encodeUInt 4 message.qtyShares
    ++ (encodeUInt 4 message.amountTraded
    ++ (encodeUInt 4 message.systemId
    ++ (encodeUInt 1 message.priceScaleCode
    ++ (Alpha.encode message.fillerAsciiStr3))))))))))))

def decode (bytes : List UInt8) : Option (VwapClosingPriceMessage × List UInt8) := do
  let (symbolIndex, bytes) ← decodeUInt 4 bytes
  let (sourceTime, bytes) ← decodeUInt 4 bytes
  let (sourceSeqNum, bytes) ← decodeUInt 4 bytes
  let (sendingIndicator, bytes) ← decodeUInt 2 bytes
  let (closingPriceRule, bytes) ← decodeUInt 2 bytes
  let (closingPrice, bytes) ← decodeUInt 4 bytes
  let (adjustedClosingPrice, bytes) ← decodeUInt 4 bytes
  let (nbTrades, bytes) ← decodeUInt 4 bytes
  let (qtyShares, bytes) ← decodeUInt 4 bytes
  let (amountTraded, bytes) ← decodeUInt 4 bytes
  let (systemId, bytes) ← decodeUInt 4 bytes
  let (priceScaleCode, bytes) ← decodeUInt 1 bytes
  let (fillerAsciiStr3, bytes) ← Alpha.decode 3 bytes
  pure ({ symbolIndex, sourceTime, sourceSeqNum, sendingIndicator, closingPriceRule, closingPrice, adjustedClosingPrice, nbTrades, qtyShares, amountTraded, systemId, priceScaleCode, fillerAsciiStr3 }, bytes)

@[simp] theorem encode_length (message : VwapClosingPriceMessage) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : VwapClosingPriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : VwapClosingPriceMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end VwapClosingPriceMessage

/-- Quotes Message: 48 bytes -/
structure QuotesMessage where
  symbolIndex : BitVec 32
  sourceSeqNum : BitVec 32
  sourceTime : BitVec 32
  quoteLinkId : BitVec 32
  askPrice : BitVec 32
  askSize : BitVec 32
  bidPrice : BitVec 32
  bidSize : BitVec 32
  systemId : BitVec 32
  numberAskOrders : BitVec 16
  numberBidOrders : BitVec 16
  sourceTimeMicroSecs : BitVec 16
  typeOfAskPrice : BitVec 8
  typeOfBidPrice : BitVec 8
  quoteCondition : QuoteCondition
  quoteNumber : BitVec 8
  priceScaleCode : BitVec 8
  fillerAsciiStr1 : Alpha 1
  deriving DecidableEq, Repr

namespace QuotesMessage

def encode (message : QuotesMessage) : List UInt8 :=
  encodeUInt 4 message.symbolIndex
    ++ (encodeUInt 4 message.sourceSeqNum
    ++ (encodeUInt 4 message.sourceTime
    ++ (encodeUInt 4 message.quoteLinkId
    ++ (encodeUInt 4 message.askPrice
    ++ (encodeUInt 4 message.askSize
    ++ (encodeUInt 4 message.bidPrice
    ++ (encodeUInt 4 message.bidSize
    ++ (encodeUInt 4 message.systemId
    ++ (encodeUInt 2 message.numberAskOrders
    ++ (encodeUInt 2 message.numberBidOrders
    ++ (encodeUInt 2 message.sourceTimeMicroSecs
    ++ (encodeUInt 1 message.typeOfAskPrice
    ++ (encodeUInt 1 message.typeOfBidPrice
    ++ (QuoteCondition.encode message.quoteCondition
    ++ (encodeUInt 1 message.quoteNumber
    ++ (encodeUInt 1 message.priceScaleCode
    ++ (Alpha.encode message.fillerAsciiStr1)))))))))))))))))

def decode (bytes : List UInt8) : Option (QuotesMessage × List UInt8) := do
  let (symbolIndex, bytes) ← decodeUInt 4 bytes
  let (sourceSeqNum, bytes) ← decodeUInt 4 bytes
  let (sourceTime, bytes) ← decodeUInt 4 bytes
  let (quoteLinkId, bytes) ← decodeUInt 4 bytes
  let (askPrice, bytes) ← decodeUInt 4 bytes
  let (askSize, bytes) ← decodeUInt 4 bytes
  let (bidPrice, bytes) ← decodeUInt 4 bytes
  let (bidSize, bytes) ← decodeUInt 4 bytes
  let (systemId, bytes) ← decodeUInt 4 bytes
  let (numberAskOrders, bytes) ← decodeUInt 2 bytes
  let (numberBidOrders, bytes) ← decodeUInt 2 bytes
  let (sourceTimeMicroSecs, bytes) ← decodeUInt 2 bytes
  let (typeOfAskPrice, bytes) ← decodeUInt 1 bytes
  let (typeOfBidPrice, bytes) ← decodeUInt 1 bytes
  let (quoteCondition, bytes) ← QuoteCondition.decode bytes
  let (quoteNumber, bytes) ← decodeUInt 1 bytes
  let (priceScaleCode, bytes) ← decodeUInt 1 bytes
  let (fillerAsciiStr1, bytes) ← Alpha.decode 1 bytes
  pure ({ symbolIndex, sourceSeqNum, sourceTime, quoteLinkId, askPrice, askSize, bidPrice, bidSize, systemId, numberAskOrders, numberBidOrders, sourceTimeMicroSecs, typeOfAskPrice, typeOfBidPrice, quoteCondition, quoteNumber, priceScaleCode, fillerAsciiStr1 }, bytes)

@[simp] theorem encode_length (message : QuotesMessage) : (encode message).length = 48 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, QuoteCondition.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : QuotesMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuotesMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, QuoteCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end QuotesMessage

/-- Order Update Market Sheet Message: 60 bytes -/
structure OrderUpdateMarketSheetMessage where
  symbolIndex : BitVec 32
  sourceTime : BitVec 32
  sourceSeqNum : BitVec 32
  price : BitVec 32
  aggregatedVolume : BitVec 32
  volume : BitVec 32
  linkId : BitVec 32
  orderId : BitVec 32
  systemId : BitVec 32
  sourceTimeMicroSecs : BitVec 16
  numberOrders : BitVec 16
  side : Alpha 1
  orderType : OrderType
  actionType : ActionType
  priceScaleCode : BitVec 8
  orderDate : BitVec 32
  orderPriorityDate : BitVec 32
  orderPriorityTime : BitVec 32
  orderPriorityMicroSecs : BitVec 16
  orderOrigin : Alpha 1
  fillerBinaryInt1 : Alpha 1
  deriving DecidableEq, Repr

namespace OrderUpdateMarketSheetMessage

def encode (message : OrderUpdateMarketSheetMessage) : List UInt8 :=
  encodeUInt 4 message.symbolIndex
    ++ (encodeUInt 4 message.sourceTime
    ++ (encodeUInt 4 message.sourceSeqNum
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.aggregatedVolume
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 4 message.linkId
    ++ (encodeUInt 4 message.orderId
    ++ (encodeUInt 4 message.systemId
    ++ (encodeUInt 2 message.sourceTimeMicroSecs
    ++ (encodeUInt 2 message.numberOrders
    ++ (Alpha.encode message.side
    ++ (OrderType.encode message.orderType
    ++ (ActionType.encode message.actionType
    ++ (encodeUInt 1 message.priceScaleCode
    ++ (encodeUInt 4 message.orderDate
    ++ (encodeUInt 4 message.orderPriorityDate
    ++ (encodeUInt 4 message.orderPriorityTime
    ++ (encodeUInt 2 message.orderPriorityMicroSecs
    ++ (Alpha.encode message.orderOrigin
    ++ (Alpha.encode message.fillerBinaryInt1))))))))))))))))))))

def decode (bytes : List UInt8) : Option (OrderUpdateMarketSheetMessage × List UInt8) := do
  let (symbolIndex, bytes) ← decodeUInt 4 bytes
  let (sourceTime, bytes) ← decodeUInt 4 bytes
  let (sourceSeqNum, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (aggregatedVolume, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (linkId, bytes) ← decodeUInt 4 bytes
  let (orderId, bytes) ← decodeUInt 4 bytes
  let (systemId, bytes) ← decodeUInt 4 bytes
  let (sourceTimeMicroSecs, bytes) ← decodeUInt 2 bytes
  let (numberOrders, bytes) ← decodeUInt 2 bytes
  let (side, bytes) ← Alpha.decode 1 bytes
  let (orderType, bytes) ← OrderType.decode bytes
  let (actionType, bytes) ← ActionType.decode bytes
  let (priceScaleCode, bytes) ← decodeUInt 1 bytes
  let (orderDate, bytes) ← decodeUInt 4 bytes
  let (orderPriorityDate, bytes) ← decodeUInt 4 bytes
  let (orderPriorityTime, bytes) ← decodeUInt 4 bytes
  let (orderPriorityMicroSecs, bytes) ← decodeUInt 2 bytes
  let (orderOrigin, bytes) ← Alpha.decode 1 bytes
  let (fillerBinaryInt1, bytes) ← Alpha.decode 1 bytes
  pure ({ symbolIndex, sourceTime, sourceSeqNum, price, aggregatedVolume, volume, linkId, orderId, systemId, sourceTimeMicroSecs, numberOrders, side, orderType, actionType, priceScaleCode, orderDate, orderPriorityDate, orderPriorityTime, orderPriorityMicroSecs, orderOrigin, fillerBinaryInt1 }, bytes)

@[simp] theorem encode_length (message : OrderUpdateMarketSheetMessage) : (encode message).length = 60 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, OrderType.encode_length, ActionType.encode_length]

theorem encode_length_pos (message : OrderUpdateMarketSheetMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderUpdateMarketSheetMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, OrderType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ActionType.decode_encode, some_bind]
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

end OrderUpdateMarketSheetMessage

/-- Orderbook Retransmission Delimiter Message: 12 bytes -/
structure OrderbookRetransmissionDelimiterMessage where
  sourceTime : BitVec 32
  sourceSeqNum : BitVec 32
  tradingEngineId : Alpha 2
  instanceId : BitVec 8
  retransmissionIndicator : Alpha 1
  deriving DecidableEq, Repr

namespace OrderbookRetransmissionDelimiterMessage

def encode (message : OrderbookRetransmissionDelimiterMessage) : List UInt8 :=
  encodeUInt 4 message.sourceTime
    ++ (encodeUInt 4 message.sourceSeqNum
    ++ (Alpha.encode message.tradingEngineId
    ++ (encodeUInt 1 message.instanceId
    ++ (Alpha.encode message.retransmissionIndicator))))

def decode (bytes : List UInt8) : Option (OrderbookRetransmissionDelimiterMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUInt 4 bytes
  let (sourceSeqNum, bytes) ← decodeUInt 4 bytes
  let (tradingEngineId, bytes) ← Alpha.decode 2 bytes
  let (instanceId, bytes) ← decodeUInt 1 bytes
  let (retransmissionIndicator, bytes) ← Alpha.decode 1 bytes
  pure ({ sourceTime, sourceSeqNum, tradingEngineId, instanceId, retransmissionIndicator }, bytes)

@[simp] theorem encode_length (message : OrderbookRetransmissionDelimiterMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderbookRetransmissionDelimiterMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderbookRetransmissionDelimiterMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderbookRetransmissionDelimiterMessage

/-- Real Time Index Message: 48 bytes -/
structure RealTimeIndexMessage where
  symbolIndex : BitVec 32
  sourceTime : BitVec 32
  indexLevel : BitVec 32
  forerunnerLevel : BitVec 32
  sessionHigh : BitVec 32
  sessionLow : BitVec 32
  percentageOfCapitalization : BitVec 32
  variationFromPreviousDaysPrice : BitVec 32
  systemId : BitVec 32
  sourceTimeMicroSecs : BitVec 16
  numOfSecuritiesQuoted : BitVec 16
  indexLevelCode : Alpha 1
  typeOfLevel : Alpha 1
  levelScaleCode : BitVec 8
  percentageScaleCode : BitVec 8
  variationScaleCode : BitVec 8
  rebroadcastIndicator : RebroadcastIndicator
  fillerAsciiStr2 : Alpha 2
  deriving DecidableEq, Repr

namespace RealTimeIndexMessage

def encode (message : RealTimeIndexMessage) : List UInt8 :=
  encodeUInt 4 message.symbolIndex
    ++ (encodeUInt 4 message.sourceTime
    ++ (encodeUInt 4 message.indexLevel
    ++ (encodeUInt 4 message.forerunnerLevel
    ++ (encodeUInt 4 message.sessionHigh
    ++ (encodeUInt 4 message.sessionLow
    ++ (encodeUInt 4 message.percentageOfCapitalization
    ++ (encodeUInt 4 message.variationFromPreviousDaysPrice
    ++ (encodeUInt 4 message.systemId
    ++ (encodeUInt 2 message.sourceTimeMicroSecs
    ++ (encodeUInt 2 message.numOfSecuritiesQuoted
    ++ (Alpha.encode message.indexLevelCode
    ++ (Alpha.encode message.typeOfLevel
    ++ (encodeUInt 1 message.levelScaleCode
    ++ (encodeUInt 1 message.percentageScaleCode
    ++ (encodeUInt 1 message.variationScaleCode
    ++ (RebroadcastIndicator.encode message.rebroadcastIndicator
    ++ (Alpha.encode message.fillerAsciiStr2)))))))))))))))))

def decode (bytes : List UInt8) : Option (RealTimeIndexMessage × List UInt8) := do
  let (symbolIndex, bytes) ← decodeUInt 4 bytes
  let (sourceTime, bytes) ← decodeUInt 4 bytes
  let (indexLevel, bytes) ← decodeUInt 4 bytes
  let (forerunnerLevel, bytes) ← decodeUInt 4 bytes
  let (sessionHigh, bytes) ← decodeUInt 4 bytes
  let (sessionLow, bytes) ← decodeUInt 4 bytes
  let (percentageOfCapitalization, bytes) ← decodeUInt 4 bytes
  let (variationFromPreviousDaysPrice, bytes) ← decodeUInt 4 bytes
  let (systemId, bytes) ← decodeUInt 4 bytes
  let (sourceTimeMicroSecs, bytes) ← decodeUInt 2 bytes
  let (numOfSecuritiesQuoted, bytes) ← decodeUInt 2 bytes
  let (indexLevelCode, bytes) ← Alpha.decode 1 bytes
  let (typeOfLevel, bytes) ← Alpha.decode 1 bytes
  let (levelScaleCode, bytes) ← decodeUInt 1 bytes
  let (percentageScaleCode, bytes) ← decodeUInt 1 bytes
  let (variationScaleCode, bytes) ← decodeUInt 1 bytes
  let (rebroadcastIndicator, bytes) ← RebroadcastIndicator.decode bytes
  let (fillerAsciiStr2, bytes) ← Alpha.decode 2 bytes
  pure ({ symbolIndex, sourceTime, indexLevel, forerunnerLevel, sessionHigh, sessionLow, percentageOfCapitalization, variationFromPreviousDaysPrice, systemId, sourceTimeMicroSecs, numOfSecuritiesQuoted, indexLevelCode, typeOfLevel, levelScaleCode, percentageScaleCode, variationScaleCode, rebroadcastIndicator, fillerAsciiStr2 }, bytes)

@[simp] theorem encode_length (message : RealTimeIndexMessage) : (encode message).length = 48 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, RebroadcastIndicator.encode_length]

theorem encode_length_pos (message : RealTimeIndexMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RealTimeIndexMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, RebroadcastIndicator.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end RealTimeIndexMessage

/-- Index Summary Message: 88 bytes -/
structure IndexSummaryMessage where
  symbolIndex : BitVec 32
  sourceTime : BitVec 32
  preliminaryOpeningLevel : BitVec 32
  preliminaryOpeningTime : BitVec 32
  firstLevel : BitVec 32
  firstTime : BitVec 32
  openingReferenceLevel : BitVec 32
  openingReferenceTime : BitVec 32
  closingReferenceLevel : BitVec 32
  closingReferenceTime : BitVec 32
  percentVariationPrevClos : BitVec 32
  highLevel : BitVec 32
  highTime : BitVec 32
  lowLevel : BitVec 32
  lowTime : BitVec 32
  clearingLevel : BitVec 32
  clearingTime : BitVec 32
  liquidationLevel : BitVec 32
  liquidationTime : BitVec 32
  systemId : BitVec 32
  sourceTimeMicroSecs : BitVec 16
  typeOfLevel : Alpha 1
  levelScaleCode : BitVec 8
  variationScaleCode : BitVec 8
  fillerAsciiStr3 : Alpha 3
  deriving DecidableEq, Repr

namespace IndexSummaryMessage

def encode (message : IndexSummaryMessage) : List UInt8 :=
  encodeUInt 4 message.symbolIndex
    ++ (encodeUInt 4 message.sourceTime
    ++ (encodeUInt 4 message.preliminaryOpeningLevel
    ++ (encodeUInt 4 message.preliminaryOpeningTime
    ++ (encodeUInt 4 message.firstLevel
    ++ (encodeUInt 4 message.firstTime
    ++ (encodeUInt 4 message.openingReferenceLevel
    ++ (encodeUInt 4 message.openingReferenceTime
    ++ (encodeUInt 4 message.closingReferenceLevel
    ++ (encodeUInt 4 message.closingReferenceTime
    ++ (encodeUInt 4 message.percentVariationPrevClos
    ++ (encodeUInt 4 message.highLevel
    ++ (encodeUInt 4 message.highTime
    ++ (encodeUInt 4 message.lowLevel
    ++ (encodeUInt 4 message.lowTime
    ++ (encodeUInt 4 message.clearingLevel
    ++ (encodeUInt 4 message.clearingTime
    ++ (encodeUInt 4 message.liquidationLevel
    ++ (encodeUInt 4 message.liquidationTime
    ++ (encodeUInt 4 message.systemId
    ++ (encodeUInt 2 message.sourceTimeMicroSecs
    ++ (Alpha.encode message.typeOfLevel
    ++ (encodeUInt 1 message.levelScaleCode
    ++ (encodeUInt 1 message.variationScaleCode
    ++ (Alpha.encode message.fillerAsciiStr3))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (IndexSummaryMessage × List UInt8) := do
  let (symbolIndex, bytes) ← decodeUInt 4 bytes
  let (sourceTime, bytes) ← decodeUInt 4 bytes
  let (preliminaryOpeningLevel, bytes) ← decodeUInt 4 bytes
  let (preliminaryOpeningTime, bytes) ← decodeUInt 4 bytes
  let (firstLevel, bytes) ← decodeUInt 4 bytes
  let (firstTime, bytes) ← decodeUInt 4 bytes
  let (openingReferenceLevel, bytes) ← decodeUInt 4 bytes
  let (openingReferenceTime, bytes) ← decodeUInt 4 bytes
  let (closingReferenceLevel, bytes) ← decodeUInt 4 bytes
  let (closingReferenceTime, bytes) ← decodeUInt 4 bytes
  let (percentVariationPrevClos, bytes) ← decodeUInt 4 bytes
  let (highLevel, bytes) ← decodeUInt 4 bytes
  let (highTime, bytes) ← decodeUInt 4 bytes
  let (lowLevel, bytes) ← decodeUInt 4 bytes
  let (lowTime, bytes) ← decodeUInt 4 bytes
  let (clearingLevel, bytes) ← decodeUInt 4 bytes
  let (clearingTime, bytes) ← decodeUInt 4 bytes
  let (liquidationLevel, bytes) ← decodeUInt 4 bytes
  let (liquidationTime, bytes) ← decodeUInt 4 bytes
  let (systemId, bytes) ← decodeUInt 4 bytes
  let (sourceTimeMicroSecs, bytes) ← decodeUInt 2 bytes
  let (typeOfLevel, bytes) ← Alpha.decode 1 bytes
  let (levelScaleCode, bytes) ← decodeUInt 1 bytes
  let (variationScaleCode, bytes) ← decodeUInt 1 bytes
  let (fillerAsciiStr3, bytes) ← Alpha.decode 3 bytes
  pure ({ symbolIndex, sourceTime, preliminaryOpeningLevel, preliminaryOpeningTime, firstLevel, firstTime, openingReferenceLevel, openingReferenceTime, closingReferenceLevel, closingReferenceTime, percentVariationPrevClos, highLevel, highTime, lowLevel, lowTime, clearingLevel, clearingTime, liquidationLevel, liquidationTime, systemId, sourceTimeMicroSecs, typeOfLevel, levelScaleCode, variationScaleCode, fillerAsciiStr3 }, bytes)

@[simp] theorem encode_length (message : IndexSummaryMessage) : (encode message).length = 88 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : IndexSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : IndexSummaryMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end IndexSummaryMessage

/-- Index Composition Message: 48 bytes -/
structure IndexCompositionMessage where
  symbolIndex : BitVec 32
  sourceTime : BitVec 32
  instrumentWeight : BitVec 32
  instrumentFactor : BitVec 32
  previousClose : BitVec 32
  systemId : BitVec 32
  sourceTimeMicroSecs : BitVec 16
  numberOfConponents : BitVec 16
  instrumentIdOfComponent : Alpha 12
  mnemo : Alpha 5
  indexFrequency : Alpha 1
  priceScaleCode : BitVec 8
  levelScaleCode : BitVec 8
  deriving DecidableEq, Repr

namespace IndexCompositionMessage

def encode (message : IndexCompositionMessage) : List UInt8 :=
  encodeUInt 4 message.symbolIndex
    ++ (encodeUInt 4 message.sourceTime
    ++ (encodeUInt 4 message.instrumentWeight
    ++ (encodeUInt 4 message.instrumentFactor
    ++ (encodeUInt 4 message.previousClose
    ++ (encodeUInt 4 message.systemId
    ++ (encodeUInt 2 message.sourceTimeMicroSecs
    ++ (encodeUInt 2 message.numberOfConponents
    ++ (Alpha.encode message.instrumentIdOfComponent
    ++ (Alpha.encode message.mnemo
    ++ (Alpha.encode message.indexFrequency
    ++ (encodeUInt 1 message.priceScaleCode
    ++ (encodeUInt 1 message.levelScaleCode))))))))))))

def decode (bytes : List UInt8) : Option (IndexCompositionMessage × List UInt8) := do
  let (symbolIndex, bytes) ← decodeUInt 4 bytes
  let (sourceTime, bytes) ← decodeUInt 4 bytes
  let (instrumentWeight, bytes) ← decodeUInt 4 bytes
  let (instrumentFactor, bytes) ← decodeUInt 4 bytes
  let (previousClose, bytes) ← decodeUInt 4 bytes
  let (systemId, bytes) ← decodeUInt 4 bytes
  let (sourceTimeMicroSecs, bytes) ← decodeUInt 2 bytes
  let (numberOfConponents, bytes) ← decodeUInt 2 bytes
  let (instrumentIdOfComponent, bytes) ← Alpha.decode 12 bytes
  let (mnemo, bytes) ← Alpha.decode 5 bytes
  let (indexFrequency, bytes) ← Alpha.decode 1 bytes
  let (priceScaleCode, bytes) ← decodeUInt 1 bytes
  let (levelScaleCode, bytes) ← decodeUInt 1 bytes
  pure ({ symbolIndex, sourceTime, instrumentWeight, instrumentFactor, previousClose, systemId, sourceTimeMicroSecs, numberOfConponents, instrumentIdOfComponent, mnemo, indexFrequency, priceScaleCode, levelScaleCode }, bytes)

@[simp] theorem encode_length (message : IndexCompositionMessage) : (encode message).length = 48 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : IndexCompositionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IndexCompositionMessage) (rest : List UInt8) :
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end IndexCompositionMessage

/-- Start Refresh Message: 4 bytes -/
structure StartRefreshMessage where
  lastSeqNum : BitVec 32
  deriving DecidableEq, Repr

namespace StartRefreshMessage

def encode (message : StartRefreshMessage) : List UInt8 :=
  encodeUInt 4 message.lastSeqNum

def decode (bytes : List UInt8) : Option (StartRefreshMessage × List UInt8) := do
  let (lastSeqNum, bytes) ← decodeUInt 4 bytes
  pure ({ lastSeqNum }, bytes)

@[simp] theorem encode_length (message : StartRefreshMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : StartRefreshMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StartRefreshMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end StartRefreshMessage

/-- End Refresh Message: 4 bytes -/
structure EndRefreshMessage where
  lastSeqNum : BitVec 32
  deriving DecidableEq, Repr

namespace EndRefreshMessage

def encode (message : EndRefreshMessage) : List UInt8 :=
  encodeUInt 4 message.lastSeqNum

def decode (bytes : List UInt8) : Option (EndRefreshMessage × List UInt8) := do
  let (lastSeqNum, bytes) ← decodeUInt 4 bytes
  pure ({ lastSeqNum }, bytes)

@[simp] theorem encode_length (message : EndRefreshMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : EndRefreshMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EndRefreshMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end EndRefreshMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | stockStateChangeMessage (message : StockStateChangeMessage) -- 505
  | classStateChangeMessage (message : ClassStateChangeMessage) -- 516
  | mailMessage (message : MailMessage) -- 523
  | indicativeMatchingPriceMessage (message : IndicativeMatchingPriceMessage) -- 530
  | collarsMessage (message : CollarsMessage) -- 537
  | sessionTimetableMessage (message : SessionTimetableMessage) -- 539
  | globalMarketActivitySummaryMessage (message : GlobalMarketActivitySummaryMessage) -- 545
  | startReferentialMessage (message : StartReferentialMessage) -- 550
  | endReferentialMessage (message : EndReferentialMessage) -- 551
  | referentialMessage (message : ReferentialMessage) -- 555
  | tradeCreationMessage (message : TradeCreationMessage) -- 220
  | tradeCancellationMessage (message : TradeCancellationMessage) -- 221
  | tradeFullInformationMessage (message : TradeFullInformationMessage) -- 240
  | priceUpdateMessage (message : PriceUpdateMessage) -- 241
  | auctionSummaryMessage (message : AuctionSummaryMessage) -- 245
  | vwapClosingPriceMessage (message : VwapClosingPriceMessage) -- 247
  | quotesMessage (message : QuotesMessage) -- 140
  | orderUpdateMarketSheetMessage (message : OrderUpdateMarketSheetMessage) -- 230
  | orderbookRetransmissionDelimiterMessage (message : OrderbookRetransmissionDelimiterMessage) -- 231
  | realTimeIndexMessage (message : RealTimeIndexMessage) -- 542
  | indexSummaryMessage (message : IndexSummaryMessage) -- 543
  | indexCompositionMessage (message : IndexCompositionMessage) -- 544
  | startRefreshMessage (message : StartRefreshMessage) -- 580
  | endRefreshMessage (message : EndRefreshMessage) -- 581
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 16
  | .stockStateChangeMessage _ => 505
  | .classStateChangeMessage _ => 516
  | .mailMessage _ => 523
  | .indicativeMatchingPriceMessage _ => 530
  | .collarsMessage _ => 537
  | .sessionTimetableMessage _ => 539
  | .globalMarketActivitySummaryMessage _ => 545
  | .startReferentialMessage _ => 550
  | .endReferentialMessage _ => 551
  | .referentialMessage _ => 555
  | .tradeCreationMessage _ => 220
  | .tradeCancellationMessage _ => 221
  | .tradeFullInformationMessage _ => 240
  | .priceUpdateMessage _ => 241
  | .auctionSummaryMessage _ => 245
  | .vwapClosingPriceMessage _ => 247
  | .quotesMessage _ => 140
  | .orderUpdateMarketSheetMessage _ => 230
  | .orderbookRetransmissionDelimiterMessage _ => 231
  | .realTimeIndexMessage _ => 542
  | .indexSummaryMessage _ => 543
  | .indexCompositionMessage _ => 544
  | .startRefreshMessage _ => 580
  | .endRefreshMessage _ => 581

def encode : Payload → List UInt8
  | .stockStateChangeMessage message => StockStateChangeMessage.encode message
  | .classStateChangeMessage message => ClassStateChangeMessage.encode message
  | .mailMessage message => MailMessage.encode message
  | .indicativeMatchingPriceMessage message => IndicativeMatchingPriceMessage.encode message
  | .collarsMessage message => CollarsMessage.encode message
  | .sessionTimetableMessage message => SessionTimetableMessage.encode message
  | .globalMarketActivitySummaryMessage message => GlobalMarketActivitySummaryMessage.encode message
  | .startReferentialMessage message => StartReferentialMessage.encode message
  | .endReferentialMessage message => EndReferentialMessage.encode message
  | .referentialMessage message => ReferentialMessage.encode message
  | .tradeCreationMessage message => TradeCreationMessage.encode message
  | .tradeCancellationMessage message => TradeCancellationMessage.encode message
  | .tradeFullInformationMessage message => TradeFullInformationMessage.encode message
  | .priceUpdateMessage message => PriceUpdateMessage.encode message
  | .auctionSummaryMessage message => AuctionSummaryMessage.encode message
  | .vwapClosingPriceMessage message => VwapClosingPriceMessage.encode message
  | .quotesMessage message => QuotesMessage.encode message
  | .orderUpdateMarketSheetMessage message => OrderUpdateMarketSheetMessage.encode message
  | .orderbookRetransmissionDelimiterMessage message => OrderbookRetransmissionDelimiterMessage.encode message
  | .realTimeIndexMessage message => RealTimeIndexMessage.encode message
  | .indexSummaryMessage message => IndexSummaryMessage.encode message
  | .indexCompositionMessage message => IndexCompositionMessage.encode message
  | .startRefreshMessage message => StartRefreshMessage.encode message
  | .endRefreshMessage message => EndRefreshMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 964 := by
  cases message with
  | stockStateChangeMessage inner =>
    simp only [encode, StockStateChangeMessage.encode_length]
    omega
  | classStateChangeMessage inner =>
    simp only [encode, ClassStateChangeMessage.encode_length]
    omega
  | mailMessage inner =>
    simp only [encode, MailMessage.encode_length]
    omega
  | indicativeMatchingPriceMessage inner =>
    simp only [encode, IndicativeMatchingPriceMessage.encode_length]
    omega
  | collarsMessage inner =>
    simp only [encode, CollarsMessage.encode_length]
    omega
  | sessionTimetableMessage inner =>
    simp only [encode, SessionTimetableMessage.encode_length]
    omega
  | globalMarketActivitySummaryMessage inner =>
    simp only [encode, GlobalMarketActivitySummaryMessage.encode_length]
    omega
  | startReferentialMessage inner =>
    simp only [encode, StartReferentialMessage.encode_length]
    omega
  | endReferentialMessage inner =>
    simp only [encode, EndReferentialMessage.encode_length]
    omega
  | referentialMessage inner =>
    simp only [encode, ReferentialMessage.encode_length]
    omega
  | tradeCreationMessage inner =>
    simp only [encode, TradeCreationMessage.encode_length]
    omega
  | tradeCancellationMessage inner =>
    simp only [encode, TradeCancellationMessage.encode_length]
    omega
  | tradeFullInformationMessage inner =>
    simp only [encode, TradeFullInformationMessage.encode_length]
    omega
  | priceUpdateMessage inner =>
    simp only [encode, PriceUpdateMessage.encode_length]
    omega
  | auctionSummaryMessage inner =>
    simp only [encode, AuctionSummaryMessage.encode_length]
    omega
  | vwapClosingPriceMessage inner =>
    simp only [encode, VwapClosingPriceMessage.encode_length]
    omega
  | quotesMessage inner =>
    simp only [encode, QuotesMessage.encode_length]
    omega
  | orderUpdateMarketSheetMessage inner =>
    simp only [encode, OrderUpdateMarketSheetMessage.encode_length]
    omega
  | orderbookRetransmissionDelimiterMessage inner =>
    simp only [encode, OrderbookRetransmissionDelimiterMessage.encode_length]
    omega
  | realTimeIndexMessage inner =>
    simp only [encode, RealTimeIndexMessage.encode_length]
    omega
  | indexSummaryMessage inner =>
    simp only [encode, IndexSummaryMessage.encode_length]
    omega
  | indexCompositionMessage inner =>
    simp only [encode, IndexCompositionMessage.encode_length]
    omega
  | startRefreshMessage inner =>
    simp only [encode, StartRefreshMessage.encode_length]
    omega
  | endRefreshMessage inner =>
    simp only [encode, EndRefreshMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 505 then (StockStateChangeMessage.decode bytes).map fun (message, rest) => (.stockStateChangeMessage message, rest)
  else if tag = 516 then (ClassStateChangeMessage.decode bytes).map fun (message, rest) => (.classStateChangeMessage message, rest)
  else if tag = 523 then (MailMessage.decode bytes).map fun (message, rest) => (.mailMessage message, rest)
  else if tag = 530 then (IndicativeMatchingPriceMessage.decode bytes).map fun (message, rest) => (.indicativeMatchingPriceMessage message, rest)
  else if tag = 537 then (CollarsMessage.decode bytes).map fun (message, rest) => (.collarsMessage message, rest)
  else if tag = 539 then (SessionTimetableMessage.decode bytes).map fun (message, rest) => (.sessionTimetableMessage message, rest)
  else if tag = 545 then (GlobalMarketActivitySummaryMessage.decode bytes).map fun (message, rest) => (.globalMarketActivitySummaryMessage message, rest)
  else if tag = 550 then (StartReferentialMessage.decode bytes).map fun (message, rest) => (.startReferentialMessage message, rest)
  else if tag = 551 then (EndReferentialMessage.decode bytes).map fun (message, rest) => (.endReferentialMessage message, rest)
  else if tag = 555 then (ReferentialMessage.decode bytes).map fun (message, rest) => (.referentialMessage message, rest)
  else if tag = 220 then (TradeCreationMessage.decode bytes).map fun (message, rest) => (.tradeCreationMessage message, rest)
  else if tag = 221 then (TradeCancellationMessage.decode bytes).map fun (message, rest) => (.tradeCancellationMessage message, rest)
  else if tag = 240 then (TradeFullInformationMessage.decode bytes).map fun (message, rest) => (.tradeFullInformationMessage message, rest)
  else if tag = 241 then (PriceUpdateMessage.decode bytes).map fun (message, rest) => (.priceUpdateMessage message, rest)
  else if tag = 245 then (AuctionSummaryMessage.decode bytes).map fun (message, rest) => (.auctionSummaryMessage message, rest)
  else if tag = 247 then (VwapClosingPriceMessage.decode bytes).map fun (message, rest) => (.vwapClosingPriceMessage message, rest)
  else if tag = 140 then (QuotesMessage.decode bytes).map fun (message, rest) => (.quotesMessage message, rest)
  else if tag = 230 then (OrderUpdateMarketSheetMessage.decode bytes).map fun (message, rest) => (.orderUpdateMarketSheetMessage message, rest)
  else if tag = 231 then (OrderbookRetransmissionDelimiterMessage.decode bytes).map fun (message, rest) => (.orderbookRetransmissionDelimiterMessage message, rest)
  else if tag = 542 then (RealTimeIndexMessage.decode bytes).map fun (message, rest) => (.realTimeIndexMessage message, rest)
  else if tag = 543 then (IndexSummaryMessage.decode bytes).map fun (message, rest) => (.indexSummaryMessage message, rest)
  else if tag = 544 then (IndexCompositionMessage.decode bytes).map fun (message, rest) => (.indexCompositionMessage message, rest)
  else if tag = 580 then (StartRefreshMessage.decode bytes).map fun (message, rest) => (.startRefreshMessage message, rest)
  else if tag = 581 then (EndRefreshMessage.decode bytes).map fun (message, rest) => (.endRefreshMessage message, rest)
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
  encodeUInt 2 (Payload.tag message.payload)
    ++ (Payload.encode message.payload)

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (messageType, bytes) ← decodeUInt 2 bytes
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
  | stockStateChangeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, StockStateChangeMessage.encode_length]
    omega
  | classStateChangeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ClassStateChangeMessage.encode_length]
    omega
  | mailMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MailMessage.encode_length]
    omega
  | indicativeMatchingPriceMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, IndicativeMatchingPriceMessage.encode_length]
    omega
  | collarsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, CollarsMessage.encode_length]
    omega
  | sessionTimetableMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SessionTimetableMessage.encode_length]
    omega
  | globalMarketActivitySummaryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, GlobalMarketActivitySummaryMessage.encode_length]
    omega
  | startReferentialMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, StartReferentialMessage.encode_length]
    omega
  | endReferentialMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, EndReferentialMessage.encode_length]
    omega
  | referentialMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ReferentialMessage.encode_length]
    omega
  | tradeCreationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeCreationMessage.encode_length]
    omega
  | tradeCancellationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeCancellationMessage.encode_length]
    omega
  | tradeFullInformationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeFullInformationMessage.encode_length]
    omega
  | priceUpdateMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, PriceUpdateMessage.encode_length]
    omega
  | auctionSummaryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, AuctionSummaryMessage.encode_length]
    omega
  | vwapClosingPriceMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, VwapClosingPriceMessage.encode_length]
    omega
  | quotesMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, QuotesMessage.encode_length]
    omega
  | orderUpdateMarketSheetMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderUpdateMarketSheetMessage.encode_length]
    omega
  | orderbookRetransmissionDelimiterMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderbookRetransmissionDelimiterMessage.encode_length]
    omega
  | realTimeIndexMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, RealTimeIndexMessage.encode_length]
    omega
  | indexSummaryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, IndexSummaryMessage.encode_length]
    omega
  | indexCompositionMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, IndexCompositionMessage.encode_length]
    omega
  | startRefreshMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, StartRefreshMessage.encode_length]
    omega
  | endRefreshMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, EndRefreshMessage.encode_length]
    omega

/-- Size rule: Message Size counts the bytes after it, so it is written from the body and checked on decode -/
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

/-- Message Buffer -/
structure MessageBuffer (numberMsgEntries : BitVec 8) where
  message : Exact numberMsgEntries.toNat Message
  deriving DecidableEq, Repr

namespace MessageBuffer

def encode {numberMsgEntries : BitVec 8} (message : MessageBuffer numberMsgEntries) : List UInt8 :=
  encodeMany Message.encode message.message.val

def decode (numberMsgEntries : BitVec 8) (bytes : List UInt8) : Option (MessageBuffer numberMsgEntries × List UInt8) := do
  let (message_, bytes) ← decodeMany Message.decode numberMsgEntries.toNat bytes
  if fits_message : message_.length = numberMsgEntries.toNat then
    pure ({ message := ⟨message_, fits_message⟩ }, bytes)
  else none

@[simp] theorem decode_encode (numberMsgEntries : BitVec 8) (message : MessageBuffer numberMsgEntries) (rest : List UInt8) :
    decode numberMsgEntries (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeMany_exact numberMsgEntries.toNat Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_eq]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (numberMsgEntries : BitVec 8) (message : MessageBuffer numberMsgEntries) : decode numberMsgEntries (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode numberMsgEntries message []

end MessageBuffer

/-- Message Buffer -/
structure MessageBufferZlib where
  payload : List UInt8
  deriving DecidableEq, Repr

namespace MessageBufferZlib

def encode (message : MessageBufferZlib) : List UInt8 :=
  encodeMany Byte.encode message.payload

def decode (bytes : List UInt8) : Option MessageBufferZlib := do
  let payload ← decodeAll Byte.decode bytes.length bytes
  pure { payload }

theorem decode_encode (message : MessageBufferZlib) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany Byte.encode Byte.decode Byte.decode_encode Byte.encode_length_pos message.payload _ (encodeMany_length_ge Byte.encode Byte.encode_length_pos message.payload), some_bind]
  rfl

end MessageBufferZlib

/-- The Message Buffer, as bytes when Delivery Flag says it was Zlib transformed and as it lies when it says it was not -/
inductive MessageBufferBody (numberMsgEntries : BitVec 8) where
  | zlib (tag : { v : BitVec 8 // v = 17 }) (message : MessageBufferZlib) -- tag = 17
  | plain (tag : { v : BitVec 8 // ¬ (v = 17) }) (message : MessageBuffer numberMsgEntries) -- every other value
  deriving DecidableEq, Repr

namespace MessageBufferBody

/-- The Delivery Flag each body is read by -/
def tag {numberMsgEntries : BitVec 8} : MessageBufferBody numberMsgEntries → BitVec 8
  | .zlib tag _ => tag.val
  | .plain tag _ => tag.val

def encode {numberMsgEntries : BitVec 8} : MessageBufferBody numberMsgEntries → List UInt8
  | .zlib _ message => MessageBufferZlib.encode message
  | .plain _ message => MessageBuffer.encode message

/-- Decoded from the whole of what holds it: a body that reads to its end takes it all, any other must leave nothing -/
def decode (numberMsgEntries : BitVec 8) (tag : BitVec 8) (bytes : List UInt8) : Option (MessageBufferBody numberMsgEntries) :=
  if h : tag = 17 then (MessageBufferZlib.decode bytes).map fun message => .zlib ⟨tag, h⟩ message
  else (MessageBuffer.decode numberMsgEntries bytes).bind fun (message, rest) => if rest.isEmpty then some (.plain ⟨tag, h⟩ message) else none

theorem decode_encode (numberMsgEntries : BitVec 8) (message : MessageBufferBody numberMsgEntries) :
    decode numberMsgEntries (tag message) (encode message) = some message := by
  cases message with
  | zlib t m =>
    obtain ⟨v, h⟩ := t
    simp only [tag, encode, decode, h, reduceDIte, MessageBufferZlib.decode_encode, Option.map_some]
  | plain t m =>
    obtain ⟨v, h⟩ := t
    simp only [tag, encode, decode, h, reduceDIte, MessageBuffer.decode_encode_nil]
    rfl

end MessageBufferBody

/-- Packet -/
structure Packet where
  packetLength : BitVec 16
  packetType : BitVec 16
  packetSequenceNumber : BitVec 32
  sendTime : BitVec 32
  serviceId : BitVec 16
  numberMsgEntries : BitVec 8
  messageBuffer : MessageBufferBody numberMsgEntries
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUInt 2 message.packetLength
    ++ (encodeUInt 2 message.packetType
    ++ (encodeUInt 4 message.packetSequenceNumber
    ++ (encodeUInt 4 message.sendTime
    ++ (encodeUInt 2 message.serviceId
    ++ (encodeUInt 1 (MessageBufferBody.tag message.messageBuffer)
    ++ (encodeUInt 1 message.numberMsgEntries
    ++ (MessageBufferBody.encode message.messageBuffer)))))))

def decode (bytes : List UInt8) : Option Packet := do
  let (packetLength, bytes) ← decodeUInt 2 bytes
  let (packetType, bytes) ← decodeUInt 2 bytes
  let (packetSequenceNumber, bytes) ← decodeUInt 4 bytes
  let (sendTime, bytes) ← decodeUInt 4 bytes
  let (serviceId, bytes) ← decodeUInt 2 bytes
  let (deliveryFlag, bytes) ← decodeUInt 1 bytes
  let (numberMsgEntries, bytes) ← decodeUInt 1 bytes
  let messageBuffer ← MessageBufferBody.decode numberMsgEntries deliveryFlag bytes
  pure { packetLength, packetType, packetSequenceNumber, sendTime, serviceId, numberMsgEntries, messageBuffer }

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [MessageBufferBody.decode_encode, some_bind]
  rfl

end Packet

end Omi.QseQsecashMarketdataXdpV26
