import Wire

/-!
# Giełda Papierów Wartościowych w Warszawie BondSpot Market Information v6.8

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.GpwBondspotMarketinformationXdpV68

/-- Session Type: one byte code -/
def SessionType.codes : List UInt8 :=
  [0x45, 0x43, 0x4C]

inductive SessionType where
  | earlyNotUsed -- Early Not Used
  | coreSession -- Core Session
  | lateNotUsed -- Late Not Used
  | unlisted (byte : { byte : UInt8 // byte ∉ SessionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SessionType

def toByte : SessionType → UInt8
  | .earlyNotUsed => 0x45
  | .coreSession => 0x43
  | .lateNotUsed => 0x4C
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SessionType :=
  if byte = 0x45 then .earlyNotUsed
  else if byte = 0x43 then .coreSession
  else .lateNotUsed

def ofByte (byte : UInt8) : SessionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SessionType) : ofByte value.toByte = value := by
  cases value with
  | earlyNotUsed => decide
  | coreSession => decide
  | lateNotUsed => decide
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

/-- Instrument Category: one byte code -/
def InstrumentCategory.codes : List UInt8 :=
  [0x41, 0x57, 0x54, 0x49, 0x46, 0x58, 0x5A, 0x4F]

inductive InstrumentCategory where
  | stock -- Stock
  | warrantAndCertificate -- Warrant And Certificate
  | tracker -- Tracker
  | index -- Index
  | future -- Future
  | option -- Option
  | bondQuotedOnInformationFixing -- Bond Quoted On Information Fixing
  | treasuryBillsAndBondsNotQuotedOnInformationFixing -- Treasury Bills And Bonds Not Quoted On Information Fixing
  | unlisted (byte : { byte : UInt8 // byte ∉ InstrumentCategory.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InstrumentCategory

def toByte : InstrumentCategory → UInt8
  | .stock => 0x41
  | .warrantAndCertificate => 0x57
  | .tracker => 0x54
  | .index => 0x49
  | .future => 0x46
  | .option => 0x58
  | .bondQuotedOnInformationFixing => 0x5A
  | .treasuryBillsAndBondsNotQuotedOnInformationFixing => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : InstrumentCategory :=
  if byte = 0x41 then .stock
  else if byte = 0x57 then .warrantAndCertificate
  else if byte = 0x54 then .tracker
  else if byte = 0x49 then .index
  else if byte = 0x46 then .future
  else if byte = 0x58 then .option
  else if byte = 0x5A then .bondQuotedOnInformationFixing
  else .treasuryBillsAndBondsNotQuotedOnInformationFixing

def ofByte (byte : UInt8) : InstrumentCategory :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InstrumentCategory) : ofByte value.toByte = value := by
  cases value with
  | stock => decide
  | warrantAndCertificate => decide
  | tracker => decide
  | index => decide
  | future => decide
  | option => decide
  | bondQuotedOnInformationFixing => decide
  | treasuryBillsAndBondsNotQuotedOnInformationFixing => decide
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
  | inavIndicativeNetAssetValueForEtfExchangeTradedFunds -- Inav Indicative Net Asset Value For Etf Exchange Traded Funds
  | supportsShortTermsOptions -- Supports Short Terms Options
  | supportsLongTermOptions -- Supports Long Term Options
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ TypeOfDerivatives.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TypeOfDerivatives

def toByte : TypeOfDerivatives → UInt8
  | .inavIndicativeNetAssetValueForEtfExchangeTradedFunds => 0x31
  | .supportsShortTermsOptions => 0x34
  | .supportsLongTermOptions => 0x36
  | .no => 0x39
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TypeOfDerivatives :=
  if byte = 0x31 then .inavIndicativeNetAssetValueForEtfExchangeTradedFunds
  else if byte = 0x34 then .supportsShortTermsOptions
  else if byte = 0x36 then .supportsLongTermOptions
  else .no

def ofByte (byte : UInt8) : TypeOfDerivatives :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TypeOfDerivatives) : ofByte value.toByte = value := by
  cases value with
  | inavIndicativeNetAssetValueForEtfExchangeTradedFunds => decide
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

/-- Ss Market Maker: one byte code -/
def SsMarketMaker.codes : List UInt8 :=
  [0x59, 0x4E, 0x20]

inductive SsMarketMaker where
  | shortSaleIsAuthorized -- Short Sale Is Authorized
  | shortSaleIsForbiddenWhichThe561SessionSummaryMessageWordsAsSuspended -- Short Sale Is Forbidden Which The 561 Session Summary Message Words As Suspended
  | notSignificantForWarrantsAndDerivativesInstrumentsAsWellAsInstrumentsTradedOnIpoAndToSegments -- Not Significant For Warrants And Derivatives Instruments As Well As Instruments Traded On Ipo And To Segments
  | unlisted (byte : { byte : UInt8 // byte ∉ SsMarketMaker.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SsMarketMaker

def toByte : SsMarketMaker → UInt8
  | .shortSaleIsAuthorized => 0x59
  | .shortSaleIsForbiddenWhichThe561SessionSummaryMessageWordsAsSuspended => 0x4E
  | .notSignificantForWarrantsAndDerivativesInstrumentsAsWellAsInstrumentsTradedOnIpoAndToSegments => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SsMarketMaker :=
  if byte = 0x59 then .shortSaleIsAuthorized
  else if byte = 0x4E then .shortSaleIsForbiddenWhichThe561SessionSummaryMessageWordsAsSuspended
  else .notSignificantForWarrantsAndDerivativesInstrumentsAsWellAsInstrumentsTradedOnIpoAndToSegments

def ofByte (byte : UInt8) : SsMarketMaker :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SsMarketMaker) : ofByte value.toByte = value := by
  cases value with
  | shortSaleIsAuthorized => decide
  | shortSaleIsForbiddenWhichThe561SessionSummaryMessageWordsAsSuspended => decide
  | notSignificantForWarrantsAndDerivativesInstrumentsAsWellAsInstrumentsTradedOnIpoAndToSegments => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SsMarketMaker) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SsMarketMaker × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SsMarketMaker) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SsMarketMaker) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SsMarketMaker) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SsMarketMaker

/-- Ss Non Market Maker: one byte code -/
def SsNonMarketMaker.codes : List UInt8 :=
  [0x59, 0x4E, 0x20]

inductive SsNonMarketMaker where
  | shortSaleIsAuthorized -- Short Sale Is Authorized
  | shortSaleIsForbiddenWhichThe561SessionSummaryMessageWordsAsSuspended -- Short Sale Is Forbidden Which The 561 Session Summary Message Words As Suspended
  | notSignificantForWarrantsAndDerivativesInstrumentsAsWellAsInstrumentsTradedOnIpoAndToSegments -- Not Significant For Warrants And Derivatives Instruments As Well As Instruments Traded On Ipo And To Segments
  | unlisted (byte : { byte : UInt8 // byte ∉ SsNonMarketMaker.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SsNonMarketMaker

def toByte : SsNonMarketMaker → UInt8
  | .shortSaleIsAuthorized => 0x59
  | .shortSaleIsForbiddenWhichThe561SessionSummaryMessageWordsAsSuspended => 0x4E
  | .notSignificantForWarrantsAndDerivativesInstrumentsAsWellAsInstrumentsTradedOnIpoAndToSegments => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SsNonMarketMaker :=
  if byte = 0x59 then .shortSaleIsAuthorized
  else if byte = 0x4E then .shortSaleIsForbiddenWhichThe561SessionSummaryMessageWordsAsSuspended
  else .notSignificantForWarrantsAndDerivativesInstrumentsAsWellAsInstrumentsTradedOnIpoAndToSegments

def ofByte (byte : UInt8) : SsNonMarketMaker :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SsNonMarketMaker) : ofByte value.toByte = value := by
  cases value with
  | shortSaleIsAuthorized => decide
  | shortSaleIsForbiddenWhichThe561SessionSummaryMessageWordsAsSuspended => decide
  | notSignificantForWarrantsAndDerivativesInstrumentsAsWellAsInstrumentsTradedOnIpoAndToSegments => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SsNonMarketMaker) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SsNonMarketMaker × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SsNonMarketMaker) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SsNonMarketMaker) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SsNonMarketMaker) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SsNonMarketMaker

/-- Option Type: one byte code -/
def OptionType.codes : List UInt8 :=
  [0x43, 0x50]

inductive OptionType where
  | call -- Call
  | put -- Put
  | unlisted (byte : { byte : UInt8 // byte ∉ OptionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OptionType

def toByte : OptionType → UInt8
  | .call => 0x43
  | .put => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OptionType :=
  if byte = 0x43 then .call
  else .put

def ofByte (byte : UInt8) : OptionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OptionType) : ofByte value.toByte = value := by
  cases value with
  | call => decide
  | put => decide
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

/-- Delivery Type: one byte code -/
def DeliveryType.codes : List UInt8 :=
  [0x43, 0x50]

inductive DeliveryType where
  | cashSettlement -- Cash Settlement
  | physicalDelivery -- Physical Delivery
  | unlisted (byte : { byte : UInt8 // byte ∉ DeliveryType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DeliveryType

def toByte : DeliveryType → UInt8
  | .cashSettlement => 0x43
  | .physicalDelivery => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DeliveryType :=
  if byte = 0x43 then .cashSettlement
  else .physicalDelivery

def ofByte (byte : UInt8) : DeliveryType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DeliveryType) : ofByte value.toByte = value := by
  cases value with
  | cashSettlement => decide
  | physicalDelivery => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DeliveryType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DeliveryType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DeliveryType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : DeliveryType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : DeliveryType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DeliveryType

/-- Exercise Type: one byte code -/
def ExerciseType.codes : List UInt8 :=
  [0x41, 0x45]

inductive ExerciseType where
  | american -- American
  | european -- European
  | unlisted (byte : { byte : UInt8 // byte ∉ ExerciseType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExerciseType

def toByte : ExerciseType → UInt8
  | .american => 0x41
  | .european => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExerciseType :=
  if byte = 0x41 then .american
  else .european

def ofByte (byte : UInt8) : ExerciseType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExerciseType) : ofByte value.toByte = value := by
  cases value with
  | american => decide
  | european => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ExerciseType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ExerciseType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ExerciseType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ExerciseType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ExerciseType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ExerciseType

/-- Status Indicator: one byte code -/
def StatusIndicator.codes : List UInt8 :=
  [0x5A, 0x20]

inductive StatusIndicator where
  | suspended -- Suspended
  | active -- Active
  | unlisted (byte : { byte : UInt8 // byte ∉ StatusIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace StatusIndicator

def toByte : StatusIndicator → UInt8
  | .suspended => 0x5A
  | .active => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : StatusIndicator :=
  if byte = 0x5A then .suspended
  else .active

def ofByte (byte : UInt8) : StatusIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : StatusIndicator) : ofByte value.toByte = value := by
  cases value with
  | suspended => decide
  | active => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : StatusIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (StatusIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : StatusIndicator) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : StatusIndicator) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : StatusIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end StatusIndicator

/-- Market: one byte code -/
def Market.codes : List UInt8 :=
  [0x50, 0x52, 0x5A, 0x43, 0x4F, 0x4E]

inductive Market where
  | primaryMarket -- Primary Market
  | parallelMarket -- Parallel Market
  | newConnectMarketPriceDrivenMarket -- New Connect Market Price Driven Market
  | newConnectMarketorderDrivenMarket -- New Connect Marketorder Driven Market
  | catalystRegulatedMarket -- Catalyst Regulated Market
  | catalystAso -- Catalyst Aso
  | unlisted (byte : { byte : UInt8 // byte ∉ Market.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Market

def toByte : Market → UInt8
  | .primaryMarket => 0x50
  | .parallelMarket => 0x52
  | .newConnectMarketPriceDrivenMarket => 0x5A
  | .newConnectMarketorderDrivenMarket => 0x43
  | .catalystRegulatedMarket => 0x4F
  | .catalystAso => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Market :=
  if byte = 0x50 then .primaryMarket
  else if byte = 0x52 then .parallelMarket
  else if byte = 0x5A then .newConnectMarketPriceDrivenMarket
  else if byte = 0x43 then .newConnectMarketorderDrivenMarket
  else if byte = 0x4F then .catalystRegulatedMarket
  else .catalystAso

def ofByte (byte : UInt8) : Market :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Market) : ofByte value.toByte = value := by
  cases value with
  | primaryMarket => decide
  | parallelMarket => decide
  | newConnectMarketPriceDrivenMarket => decide
  | newConnectMarketorderDrivenMarket => decide
  | catalystRegulatedMarket => decide
  | catalystAso => decide
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

/-- Marker Pct Change Price: one byte code -/
def MarkerPctChangePrice.codes : List UInt8 :=
  [0x2B, 0x2D, 0x20]

inductive MarkerPctChangePrice where
  | increase -- Increase
  | decrease -- Decrease
  | noChange -- No Change
  | unlisted (byte : { byte : UInt8 // byte ∉ MarkerPctChangePrice.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarkerPctChangePrice

def toByte : MarkerPctChangePrice → UInt8
  | .increase => 0x2B
  | .decrease => 0x2D
  | .noChange => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarkerPctChangePrice :=
  if byte = 0x2B then .increase
  else if byte = 0x2D then .decrease
  else .noChange

def ofByte (byte : UInt8) : MarkerPctChangePrice :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarkerPctChangePrice) : ofByte value.toByte = value := by
  cases value with
  | increase => decide
  | decrease => decide
  | noChange => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarkerPctChangePrice) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarkerPctChangePrice × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarkerPctChangePrice) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : MarkerPctChangePrice) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : MarkerPctChangePrice) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarkerPctChangePrice

/-- Symbol Delta: one byte code -/
def SymbolDelta.codes : List UInt8 :=
  [0x2B, 0x2D, 0x20]

inductive SymbolDelta where
  | positiveValue -- Positive Value
  | negativeValue -- Negative Value
  | zeroValue -- Zero Value
  | unlisted (byte : { byte : UInt8 // byte ∉ SymbolDelta.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SymbolDelta

def toByte : SymbolDelta → UInt8
  | .positiveValue => 0x2B
  | .negativeValue => 0x2D
  | .zeroValue => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SymbolDelta :=
  if byte = 0x2B then .positiveValue
  else if byte = 0x2D then .negativeValue
  else .zeroValue

def ofByte (byte : UInt8) : SymbolDelta :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SymbolDelta) : ofByte value.toByte = value := by
  cases value with
  | positiveValue => decide
  | negativeValue => decide
  | zeroValue => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SymbolDelta) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SymbolDelta × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SymbolDelta) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SymbolDelta) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SymbolDelta) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SymbolDelta

/-- Symbol Gamma: one byte code -/
def SymbolGamma.codes : List UInt8 :=
  [0x2B, 0x2D, 0x20]

inductive SymbolGamma where
  | positiveValue -- Positive Value
  | negativeValue -- Negative Value
  | zeroValue -- Zero Value
  | unlisted (byte : { byte : UInt8 // byte ∉ SymbolGamma.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SymbolGamma

def toByte : SymbolGamma → UInt8
  | .positiveValue => 0x2B
  | .negativeValue => 0x2D
  | .zeroValue => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SymbolGamma :=
  if byte = 0x2B then .positiveValue
  else if byte = 0x2D then .negativeValue
  else .zeroValue

def ofByte (byte : UInt8) : SymbolGamma :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SymbolGamma) : ofByte value.toByte = value := by
  cases value with
  | positiveValue => decide
  | negativeValue => decide
  | zeroValue => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SymbolGamma) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SymbolGamma × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SymbolGamma) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SymbolGamma) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SymbolGamma) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SymbolGamma

/-- Symbol Rho: one byte code -/
def SymbolRho.codes : List UInt8 :=
  [0x2B, 0x2D, 0x20]

inductive SymbolRho where
  | positiveValue -- Positive Value
  | negativeValue -- Negative Value
  | zeroValue -- Zero Value
  | unlisted (byte : { byte : UInt8 // byte ∉ SymbolRho.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SymbolRho

def toByte : SymbolRho → UInt8
  | .positiveValue => 0x2B
  | .negativeValue => 0x2D
  | .zeroValue => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SymbolRho :=
  if byte = 0x2B then .positiveValue
  else if byte = 0x2D then .negativeValue
  else .zeroValue

def ofByte (byte : UInt8) : SymbolRho :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SymbolRho) : ofByte value.toByte = value := by
  cases value with
  | positiveValue => decide
  | negativeValue => decide
  | zeroValue => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SymbolRho) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SymbolRho × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SymbolRho) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SymbolRho) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SymbolRho) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SymbolRho

/-- Symbol Theta: one byte code -/
def SymbolTheta.codes : List UInt8 :=
  [0x2B, 0x2D, 0x20]

inductive SymbolTheta where
  | positiveValue -- Positive Value
  | negativeValue -- Negative Value
  | zeroValue -- Zero Value
  | unlisted (byte : { byte : UInt8 // byte ∉ SymbolTheta.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SymbolTheta

def toByte : SymbolTheta → UInt8
  | .positiveValue => 0x2B
  | .negativeValue => 0x2D
  | .zeroValue => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SymbolTheta :=
  if byte = 0x2B then .positiveValue
  else if byte = 0x2D then .negativeValue
  else .zeroValue

def ofByte (byte : UInt8) : SymbolTheta :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SymbolTheta) : ofByte value.toByte = value := by
  cases value with
  | positiveValue => decide
  | negativeValue => decide
  | zeroValue => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SymbolTheta) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SymbolTheta × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SymbolTheta) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SymbolTheta) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SymbolTheta) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SymbolTheta

/-- Symbol Vega: one byte code -/
def SymbolVega.codes : List UInt8 :=
  [0x2B, 0x2D, 0x20]

inductive SymbolVega where
  | positiveValue -- Positive Value
  | negativeValue -- Negative Value
  | zeroValue -- Zero Value
  | unlisted (byte : { byte : UInt8 // byte ∉ SymbolVega.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SymbolVega

def toByte : SymbolVega → UInt8
  | .positiveValue => 0x2B
  | .negativeValue => 0x2D
  | .zeroValue => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SymbolVega :=
  if byte = 0x2B then .positiveValue
  else if byte = 0x2D then .negativeValue
  else .zeroValue

def ofByte (byte : UInt8) : SymbolVega :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SymbolVega) : ofByte value.toByte = value := by
  cases value with
  | positiveValue => decide
  | negativeValue => decide
  | zeroValue => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SymbolVega) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SymbolVega × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SymbolVega) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SymbolVega) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SymbolVega) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SymbolVega

/-- Class State Change Message: 24 bytes -/
structure ClassStateChangeMessage where
  sourceSeqNum : BitVec 32
  sourceTime : BitVec 32
  systemId : BitVec 32
  sourceTimeMicroSecs : BitVec 16
  instrumentGroupCode : Alpha 3
  instrumentGroupState : Alpha 1
  sessionType : SessionType
  reserved1 : Alpha 1
  classState : Alpha 4
  deriving DecidableEq, Repr

namespace ClassStateChangeMessage

def encode (message : ClassStateChangeMessage) : List UInt8 :=
  encodeUInt 4 message.sourceSeqNum
    ++ (encodeUInt 4 message.sourceTime
    ++ (encodeUInt 4 message.systemId
    ++ (encodeUInt 2 message.sourceTimeMicroSecs
    ++ (Alpha.encode message.instrumentGroupCode
    ++ (Alpha.encode message.instrumentGroupState
    ++ (SessionType.encode message.sessionType
    ++ (Alpha.encode message.reserved1
    ++ (Alpha.encode message.classState))))))))

def decode (bytes : List UInt8) : Option (ClassStateChangeMessage × List UInt8) := do
  let (sourceSeqNum, bytes) ← decodeUInt 4 bytes
  let (sourceTime, bytes) ← decodeUInt 4 bytes
  let (systemId, bytes) ← decodeUInt 4 bytes
  let (sourceTimeMicroSecs, bytes) ← decodeUInt 2 bytes
  let (instrumentGroupCode, bytes) ← Alpha.decode 3 bytes
  let (instrumentGroupState, bytes) ← Alpha.decode 1 bytes
  let (sessionType, bytes) ← SessionType.decode bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (classState, bytes) ← Alpha.decode 4 bytes
  pure ({ sourceSeqNum, sourceTime, systemId, sourceTimeMicroSecs, instrumentGroupCode, instrumentGroupState, sessionType, reserved1, classState }, bytes)

@[simp] theorem encode_length (message : ClassStateChangeMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, SessionType.encode_length]

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SessionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ClassStateChangeMessage

/-- Mail Message: 1098 bytes -/
structure MailMessage where
  sourceSeqNum : BitVec 32
  sourceTime : BitVec 32
  systemId : BitVec 32
  sourceTimeMicroSecs : BitVec 16
  scope : Alpha 1
  title : Alpha 80
  text : Alpha 1000
  reserved3 : Alpha 3
  deriving DecidableEq, Repr

namespace MailMessage

def encode (message : MailMessage) : List UInt8 :=
  encodeUInt 4 message.sourceSeqNum
    ++ (encodeUInt 4 message.sourceTime
    ++ (encodeUInt 4 message.systemId
    ++ (encodeUInt 2 message.sourceTimeMicroSecs
    ++ (Alpha.encode message.scope
    ++ (Alpha.encode message.title
    ++ (Alpha.encode message.text
    ++ (Alpha.encode message.reserved3)))))))

def decode (bytes : List UInt8) : Option (MailMessage × List UInt8) := do
  let (sourceSeqNum, bytes) ← decodeUInt 4 bytes
  let (sourceTime, bytes) ← decodeUInt 4 bytes
  let (systemId, bytes) ← decodeUInt 4 bytes
  let (sourceTimeMicroSecs, bytes) ← decodeUInt 2 bytes
  let (scope, bytes) ← Alpha.decode 1 bytes
  let (title, bytes) ← Alpha.decode 80 bytes
  let (text, bytes) ← Alpha.decode 1000 bytes
  let (reserved3, bytes) ← Alpha.decode 3 bytes
  pure ({ sourceSeqNum, sourceTime, systemId, sourceTimeMicroSecs, scope, title, text, reserved3 }, bytes)

@[simp] theorem encode_length (message : MailMessage) : (encode message).length = 1098 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MailMessage

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
  reserved3 : Alpha 3
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
    ++ (Alpha.encode message.reserved3))))))))))

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
  let (reserved3, bytes) ← Alpha.decode 3 bytes
  pure ({ symbolIndex, sourceSeqNum, sourceTime, highCollar, lowCollar, systemId, sourceTimeMicroSecs, highScaleCode, lowScaleCode, collarType, reserved3 }, bytes)

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

/-- Class Phase: 8 bytes -/
structure ClassPhase where
  classStateTime : Alpha 4
  classState : Alpha 4
  deriving DecidableEq, Repr

namespace ClassPhase

def encode (message : ClassPhase) : List UInt8 :=
  Alpha.encode message.classStateTime
    ++ (Alpha.encode message.classState)

def decode (bytes : List UInt8) : Option (ClassPhase × List UInt8) := do
  let (classStateTime, bytes) ← Alpha.decode 4 bytes
  let (classState, bytes) ← Alpha.decode 4 bytes
  pure ({ classStateTime, classState }, bytes)

@[simp] theorem encode_length (message : ClassPhase) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : ClassPhase) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ClassPhase) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ClassPhase

/-- Session Timetable Message: 140 bytes -/
structure SessionTimetableMessage where
  sourceSeqNum : BitVec 32
  sourceTime : BitVec 32
  systemId : BitVec 32
  sourceTimeMicroSecs : BitVec 16
  instrumentGroupCode : Alpha 3
  reserved1 : Alpha 1
  classPhaseNumber : BitVec 16
  classPhase : Exact 15 ClassPhase
  deriving DecidableEq, Repr

namespace SessionTimetableMessage

def encode (message : SessionTimetableMessage) : List UInt8 :=
  encodeUInt 4 message.sourceSeqNum
    ++ (encodeUInt 4 message.sourceTime
    ++ (encodeUInt 4 message.systemId
    ++ (encodeUInt 2 message.sourceTimeMicroSecs
    ++ (Alpha.encode message.instrumentGroupCode
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.classPhaseNumber
    ++ (encodeMany ClassPhase.encode message.classPhase.val)))))))

def decode (bytes : List UInt8) : Option (SessionTimetableMessage × List UInt8) := do
  let (sourceSeqNum, bytes) ← decodeUInt 4 bytes
  let (sourceTime, bytes) ← decodeUInt 4 bytes
  let (systemId, bytes) ← decodeUInt 4 bytes
  let (sourceTimeMicroSecs, bytes) ← decodeUInt 2 bytes
  let (instrumentGroupCode, bytes) ← Alpha.decode 3 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (classPhaseNumber, bytes) ← decodeUInt 2 bytes
  let (classPhase_, bytes) ← decodeMany ClassPhase.decode 15 bytes
  if fits_classPhase : classPhase_.length = 15 then
    pure ({ sourceSeqNum, sourceTime, systemId, sourceTimeMicroSecs, instrumentGroupCode, reserved1, classPhaseNumber, classPhase := ⟨classPhase_, fits_classPhase⟩ }, bytes)
  else none

@[simp] theorem encode_length (message : SessionTimetableMessage) : (encode message).length = 140 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, encodeMany_length_const ClassPhase.encode 8 ClassPhase.encode_length, message.classPhase.length_eq]

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_exact 15 ClassPhase.encode ClassPhase.decode ClassPhase.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.classPhase.length_eq]
  rfl

end SessionTimetableMessage

/-- Start Referential Message: 4 bytes -/
structure StartReferentialMessage where
  indicator : Alpha 1
  reserved3 : Alpha 3
  deriving DecidableEq, Repr

namespace StartReferentialMessage

def encode (message : StartReferentialMessage) : List UInt8 :=
  Alpha.encode message.indicator
    ++ (Alpha.encode message.reserved3)

def decode (bytes : List UInt8) : Option (StartReferentialMessage × List UInt8) := do
  let (indicator, bytes) ← Alpha.decode 1 bytes
  let (reserved3, bytes) ← Alpha.decode 3 bytes
  pure ({ indicator, reserved3 }, bytes)

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
  reserved3 : Alpha 3
  deriving DecidableEq, Repr

namespace EndReferentialMessage

def encode (message : EndReferentialMessage) : List UInt8 :=
  Alpha.encode message.indicator
    ++ (Alpha.encode message.reserved3)

def decode (bytes : List UInt8) : Option (EndReferentialMessage × List UInt8) := do
  let (indicator, bytes) ← Alpha.decode 1 bytes
  let (reserved3, bytes) ← Alpha.decode 3 bytes
  pure ({ indicator, reserved3 }, bytes)

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

/-- Depositary List: 5 bytes -/
structure DepositaryList where
  depositary : Alpha 5
  deriving DecidableEq, Repr

namespace DepositaryList

def encode (message : DepositaryList) : List UInt8 :=
  Alpha.encode message.depositary

def decode (bytes : List UInt8) : Option (DepositaryList × List UInt8) := do
  let (depositary, bytes) ← Alpha.decode 5 bytes
  pure ({ depositary }, bytes)

@[simp] theorem encode_length (message : DepositaryList) : (encode message).length = 5 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : DepositaryList) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DepositaryList) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end DepositaryList

/-- Referential Message: 540 bytes -/
structure ReferentialMessage where
  symbolIndex : BitVec 32
  sourceSeqNum : BitVec 32
  sourceTime : BitVec 32
  lastAdjPrice : BitVec 32
  systemId : BitVec 32
  prevVolumeTraded : BitVec 32
  reserved4 : Alpha 4
  sourceTimeMicroSecs : BitVec 16
  stockExchangeCode : BitVec 16
  typeOfInstrument : BitVec 16
  eventDate : Alpha 8
  instrumentName : Alpha 18
  periodIndicator : Alpha 1
  typeOfMarketAdmission : Alpha 1
  issuingCountryCode : Alpha 3
  tradingCurrency : Alpha 3
  instrumentGroupCode : Alpha 3
  instrumentCategory : InstrumentCategory
  instrumentCode : Alpha 12
  dateOfLastTrade : Alpha 8
  underlyingRepoIsinCode : Alpha 12
  expiryDate : Alpha 8
  firstSettlementDate : Alpha 8
  typeOfDerivatives : TypeOfDerivatives
  bicDepositary : Alpha 11
  icb : Alpha 4
  mic : Alpha 4
  underlyingIsinCode : Alpha 12
  depositaryList : Exact 5 DepositaryList
  mainDepositary : Alpha 5
  typeOfCorporateEvent : Alpha 2
  timeLagEuronextUtc : Alpha 5
  timeLagMiFidRegUtc : Alpha 5
  cfi : Alpha 6
  secondReserved4 : Alpha 4
  indexSetOfVarPriceTick : Alpha 2
  marketFeedCode : Alpha 2
  micList : Alpha 24
  industryCode : Alpha 4
  industryText : Alpha 100
  financialMarketCode : Alpha 3
  usIndicators : Alpha 7
  reserved2 : Alpha 2
  prevDayCapitalTraded : BitVec 64
  lotSize : BitVec 64
  numberInstrumentCirc : BitVec 64
  sharesOut : BitVec 64
  authShares : BitVec 64
  priceNotation : Alpha 4
  repoIndicator : Alpha 1
  notionalAmount : Alpha 20
  notionalCurrency : Alpha 3
  lastAdjPriceScaleCode : BitVec 8
  marketIndicator : BitVec 8
  prevDayCapitalTradedScaleCode : BitVec 8
  taxCode : BitVec 8
  reserved1 : Alpha 1
  lotSizeScaleCode : BitVec 8
  secondReserved1 : Alpha 1
  mnemo : Alpha 5
  tradingCode : Alpha 12
  thirdReserved4 : Alpha 4
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
  blockSize : BitVec 32
  ssMarketMaker : SsMarketMaker
  ssNonMarketMaker : SsNonMarketMaker
  settlementDelay : Alpha 2
  optionType : OptionType
  deliveryType : DeliveryType
  exerciseType : ExerciseType
  multiplierScaleCode : BitVec 8
  warrantThresholdMinScaleCode : BitVec 8
  warrantThresholdMaxScaleCode : BitVec 8
  secondReserved2 : Alpha 2
  warrantThresholdMin : BitVec 32
  warrantThresholdMax : BitVec 32
  minQuantity : BitVec 32
  maxQuantity : BitVec 32
  multiplier : BitVec 32
  fourthReserved4 : Alpha 4
  maxValue : BitVec 64
  deriving DecidableEq, Repr

namespace ReferentialMessage

def encode (message : ReferentialMessage) : List UInt8 :=
  encodeUInt 4 message.symbolIndex
    ++ (encodeUInt 4 message.sourceSeqNum
    ++ (encodeUInt 4 message.sourceTime
    ++ (encodeUInt 4 message.lastAdjPrice
    ++ (encodeUInt 4 message.systemId
    ++ (encodeUInt 4 message.prevVolumeTraded
    ++ (Alpha.encode message.reserved4
    ++ (encodeUInt 2 message.sourceTimeMicroSecs
    ++ (encodeUInt 2 message.stockExchangeCode
    ++ (encodeUInt 2 message.typeOfInstrument
    ++ (Alpha.encode message.eventDate
    ++ (Alpha.encode message.instrumentName
    ++ (Alpha.encode message.periodIndicator
    ++ (Alpha.encode message.typeOfMarketAdmission
    ++ (Alpha.encode message.issuingCountryCode
    ++ (Alpha.encode message.tradingCurrency
    ++ (Alpha.encode message.instrumentGroupCode
    ++ (InstrumentCategory.encode message.instrumentCategory
    ++ (Alpha.encode message.instrumentCode
    ++ (Alpha.encode message.dateOfLastTrade
    ++ (Alpha.encode message.underlyingRepoIsinCode
    ++ (Alpha.encode message.expiryDate
    ++ (Alpha.encode message.firstSettlementDate
    ++ (TypeOfDerivatives.encode message.typeOfDerivatives
    ++ (Alpha.encode message.bicDepositary
    ++ (Alpha.encode message.icb
    ++ (Alpha.encode message.mic
    ++ (Alpha.encode message.underlyingIsinCode
    ++ (encodeMany DepositaryList.encode message.depositaryList.val
    ++ (Alpha.encode message.mainDepositary
    ++ (Alpha.encode message.typeOfCorporateEvent
    ++ (Alpha.encode message.timeLagEuronextUtc
    ++ (Alpha.encode message.timeLagMiFidRegUtc
    ++ (Alpha.encode message.cfi
    ++ (Alpha.encode message.secondReserved4
    ++ (Alpha.encode message.indexSetOfVarPriceTick
    ++ (Alpha.encode message.marketFeedCode
    ++ (Alpha.encode message.micList
    ++ (Alpha.encode message.industryCode
    ++ (Alpha.encode message.industryText
    ++ (Alpha.encode message.financialMarketCode
    ++ (Alpha.encode message.usIndicators
    ++ (Alpha.encode message.reserved2
    ++ (encodeUInt 8 message.prevDayCapitalTraded
    ++ (encodeUInt 8 message.lotSize
    ++ (encodeUInt 8 message.numberInstrumentCirc
    ++ (encodeUInt 8 message.sharesOut
    ++ (encodeUInt 8 message.authShares
    ++ (Alpha.encode message.priceNotation
    ++ (Alpha.encode message.repoIndicator
    ++ (Alpha.encode message.notionalAmount
    ++ (Alpha.encode message.notionalCurrency
    ++ (encodeUInt 1 message.lastAdjPriceScaleCode
    ++ (encodeUInt 1 message.marketIndicator
    ++ (encodeUInt 1 message.prevDayCapitalTradedScaleCode
    ++ (encodeUInt 1 message.taxCode
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 1 message.lotSizeScaleCode
    ++ (Alpha.encode message.secondReserved1
    ++ (Alpha.encode message.mnemo
    ++ (Alpha.encode message.tradingCode
    ++ (Alpha.encode message.thirdReserved4
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
    ++ (encodeUInt 4 message.blockSize
    ++ (SsMarketMaker.encode message.ssMarketMaker
    ++ (SsNonMarketMaker.encode message.ssNonMarketMaker
    ++ (Alpha.encode message.settlementDelay
    ++ (OptionType.encode message.optionType
    ++ (DeliveryType.encode message.deliveryType
    ++ (ExerciseType.encode message.exerciseType
    ++ (encodeUInt 1 message.multiplierScaleCode
    ++ (encodeUInt 1 message.warrantThresholdMinScaleCode
    ++ (encodeUInt 1 message.warrantThresholdMaxScaleCode
    ++ (Alpha.encode message.secondReserved2
    ++ (encodeUInt 4 message.warrantThresholdMin
    ++ (encodeUInt 4 message.warrantThresholdMax
    ++ (encodeUInt 4 message.minQuantity
    ++ (encodeUInt 4 message.maxQuantity
    ++ (encodeUInt 4 message.multiplier
    ++ (Alpha.encode message.fourthReserved4
    ++ (encodeUInt 8 message.maxValue)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ReferentialMessage × List UInt8) := do
  let (symbolIndex, bytes) ← decodeUInt 4 bytes
  let (sourceSeqNum, bytes) ← decodeUInt 4 bytes
  let (sourceTime, bytes) ← decodeUInt 4 bytes
  let (lastAdjPrice, bytes) ← decodeUInt 4 bytes
  let (systemId, bytes) ← decodeUInt 4 bytes
  let (prevVolumeTraded, bytes) ← decodeUInt 4 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (sourceTimeMicroSecs, bytes) ← decodeUInt 2 bytes
  let (stockExchangeCode, bytes) ← decodeUInt 2 bytes
  let (typeOfInstrument, bytes) ← decodeUInt 2 bytes
  let (eventDate, bytes) ← Alpha.decode 8 bytes
  let (instrumentName, bytes) ← Alpha.decode 18 bytes
  let (periodIndicator, bytes) ← Alpha.decode 1 bytes
  let (typeOfMarketAdmission, bytes) ← Alpha.decode 1 bytes
  let (issuingCountryCode, bytes) ← Alpha.decode 3 bytes
  let (tradingCurrency, bytes) ← Alpha.decode 3 bytes
  let (instrumentGroupCode, bytes) ← Alpha.decode 3 bytes
  let (instrumentCategory, bytes) ← InstrumentCategory.decode bytes
  let (instrumentCode, bytes) ← Alpha.decode 12 bytes
  let (dateOfLastTrade, bytes) ← Alpha.decode 8 bytes
  let (underlyingRepoIsinCode, bytes) ← Alpha.decode 12 bytes
  let (expiryDate, bytes) ← Alpha.decode 8 bytes
  let (firstSettlementDate, bytes) ← Alpha.decode 8 bytes
  let (typeOfDerivatives, bytes) ← TypeOfDerivatives.decode bytes
  let (bicDepositary, bytes) ← Alpha.decode 11 bytes
  let (icb, bytes) ← Alpha.decode 4 bytes
  let (mic, bytes) ← Alpha.decode 4 bytes
  let (underlyingIsinCode, bytes) ← Alpha.decode 12 bytes
  let (depositaryList_, bytes) ← decodeMany DepositaryList.decode 5 bytes
  let (mainDepositary, bytes) ← Alpha.decode 5 bytes
  let (typeOfCorporateEvent, bytes) ← Alpha.decode 2 bytes
  let (timeLagEuronextUtc, bytes) ← Alpha.decode 5 bytes
  let (timeLagMiFidRegUtc, bytes) ← Alpha.decode 5 bytes
  let (cfi, bytes) ← Alpha.decode 6 bytes
  let (secondReserved4, bytes) ← Alpha.decode 4 bytes
  let (indexSetOfVarPriceTick, bytes) ← Alpha.decode 2 bytes
  let (marketFeedCode, bytes) ← Alpha.decode 2 bytes
  let (micList, bytes) ← Alpha.decode 24 bytes
  let (industryCode, bytes) ← Alpha.decode 4 bytes
  let (industryText, bytes) ← Alpha.decode 100 bytes
  let (financialMarketCode, bytes) ← Alpha.decode 3 bytes
  let (usIndicators, bytes) ← Alpha.decode 7 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (prevDayCapitalTraded, bytes) ← decodeUInt 8 bytes
  let (lotSize, bytes) ← decodeUInt 8 bytes
  let (numberInstrumentCirc, bytes) ← decodeUInt 8 bytes
  let (sharesOut, bytes) ← decodeUInt 8 bytes
  let (authShares, bytes) ← decodeUInt 8 bytes
  let (priceNotation, bytes) ← Alpha.decode 4 bytes
  let (repoIndicator, bytes) ← Alpha.decode 1 bytes
  let (notionalAmount, bytes) ← Alpha.decode 20 bytes
  let (notionalCurrency, bytes) ← Alpha.decode 3 bytes
  let (lastAdjPriceScaleCode, bytes) ← decodeUInt 1 bytes
  let (marketIndicator, bytes) ← decodeUInt 1 bytes
  let (prevDayCapitalTradedScaleCode, bytes) ← decodeUInt 1 bytes
  let (taxCode, bytes) ← decodeUInt 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (lotSizeScaleCode, bytes) ← decodeUInt 1 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  let (mnemo, bytes) ← Alpha.decode 5 bytes
  let (tradingCode, bytes) ← Alpha.decode 12 bytes
  let (thirdReserved4, bytes) ← Alpha.decode 4 bytes
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
  let (blockSize, bytes) ← decodeUInt 4 bytes
  let (ssMarketMaker, bytes) ← SsMarketMaker.decode bytes
  let (ssNonMarketMaker, bytes) ← SsNonMarketMaker.decode bytes
  let (settlementDelay, bytes) ← Alpha.decode 2 bytes
  let (optionType, bytes) ← OptionType.decode bytes
  let (deliveryType, bytes) ← DeliveryType.decode bytes
  let (exerciseType, bytes) ← ExerciseType.decode bytes
  let (multiplierScaleCode, bytes) ← decodeUInt 1 bytes
  let (warrantThresholdMinScaleCode, bytes) ← decodeUInt 1 bytes
  let (warrantThresholdMaxScaleCode, bytes) ← decodeUInt 1 bytes
  let (secondReserved2, bytes) ← Alpha.decode 2 bytes
  let (warrantThresholdMin, bytes) ← decodeUInt 4 bytes
  let (warrantThresholdMax, bytes) ← decodeUInt 4 bytes
  let (minQuantity, bytes) ← decodeUInt 4 bytes
  let (maxQuantity, bytes) ← decodeUInt 4 bytes
  let (multiplier, bytes) ← decodeUInt 4 bytes
  let (fourthReserved4, bytes) ← Alpha.decode 4 bytes
  let (maxValue, bytes) ← decodeUInt 8 bytes
  if fits_depositaryList : depositaryList_.length = 5 then
    pure ({ symbolIndex, sourceSeqNum, sourceTime, lastAdjPrice, systemId, prevVolumeTraded, reserved4, sourceTimeMicroSecs, stockExchangeCode, typeOfInstrument, eventDate, instrumentName, periodIndicator, typeOfMarketAdmission, issuingCountryCode, tradingCurrency, instrumentGroupCode, instrumentCategory, instrumentCode, dateOfLastTrade, underlyingRepoIsinCode, expiryDate, firstSettlementDate, typeOfDerivatives, bicDepositary, icb, mic, underlyingIsinCode, depositaryList := ⟨depositaryList_, fits_depositaryList⟩, mainDepositary, typeOfCorporateEvent, timeLagEuronextUtc, timeLagMiFidRegUtc, cfi, secondReserved4, indexSetOfVarPriceTick, marketFeedCode, micList, industryCode, industryText, financialMarketCode, usIndicators, reserved2, prevDayCapitalTraded, lotSize, numberInstrumentCirc, sharesOut, authShares, priceNotation, repoIndicator, notionalAmount, notionalCurrency, lastAdjPriceScaleCode, marketIndicator, prevDayCapitalTradedScaleCode, taxCode, reserved1, lotSizeScaleCode, secondReserved1, mnemo, tradingCode, thirdReserved4, strikePrice, strikeCurrency, strikeScaleCode, currencyCoef, currencyCoefScaleCode, tradingCurrencyIndicator, strikeCurrencyIndicator, marketSegment, algo, localName, blockSize, ssMarketMaker, ssNonMarketMaker, settlementDelay, optionType, deliveryType, exerciseType, multiplierScaleCode, warrantThresholdMinScaleCode, warrantThresholdMaxScaleCode, secondReserved2, warrantThresholdMin, warrantThresholdMax, minQuantity, maxQuantity, multiplier, fourthReserved4, maxValue }, bytes)
  else none

@[simp] theorem encode_length (message : ReferentialMessage) : (encode message).length = 540 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, InstrumentCategory.encode_length, TypeOfDerivatives.encode_length, encodeMany_length_const DepositaryList.encode 5 DepositaryList.encode_length, message.depositaryList.length_eq, Algo.encode_length, SsMarketMaker.encode_length, SsNonMarketMaker.encode_length, OptionType.encode_length, DeliveryType.encode_length, ExerciseType.encode_length]

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
  rw [List.append_assoc, decodeMany_exact 5 DepositaryList.encode DepositaryList.decode DepositaryList.decode_encode, some_bind]
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
  rw [List.append_assoc, SsMarketMaker.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SsNonMarketMaker.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OptionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DeliveryType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExerciseType.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [dite_eq_left message.depositaryList.length_eq]
  rfl

end ReferentialMessage

/-- Session Summary Message: 260 bytes -/
structure SessionSummaryMessage where
  symbolIndex : BitVec 32
  sourceTime : BitVec 32
  sourceSeqNum : BitVec 32
  date : BitVec 32
  multiplier : BitVec 32
  accumulatedInterest : BitVec 32
  openingPrice : BitVec 32
  maximumPrice : BitVec 32
  minimumPrice : BitVec 32
  closingPrice : BitVec 32
  impliedVolatility : BitVec 32
  averageWeightedPrice : BitVec 32
  referencePrice : BitVec 32
  pctChangePrice : BitVec 32
  dividendRate : BitVec 32
  settlementPrice : BitVec 32
  settlementValue : BitVec 32
  reserved4 : Alpha 4
  openPositions : BitVec 32
  tradingVolume : BitVec 32
  transactionsNumber : BitVec 32
  tradingValue : BitVec 64
  currencyPrice : BitVec 32
  delta : BitVec 32
  gamma : BitVec 32
  rho : BitVec 32
  theta : BitVec 32
  vega : BitVec 32
  endTrading : BitVec 32
  numberOfInstruments : BitVec 32
  tradingValueCurrency : BitVec 64
  interestRate : BitVec 32
  volatility : BitVec 32
  strikePrice : BitVec 32
  shortSellingTradesNumber : BitVec 32
  volumeShortSellingTrades : BitVec 32
  valueShortSellingTrades : BitVec 32
  lastTradeDate : BitVec 32
  lastTradePrice : BitVec 32
  blockTradesNumber : BitVec 32
  volumeBlockTrades : BitVec 32
  valueBlockTrades : BitVec 32
  vwapBlocktrade : BitVec 32
  maximumBlockPrice : BitVec 32
  minimumBlockPrice : BitVec 32
  systemId : BitVec 32
  sourceTimeMicroSecs : BitVec 16
  multiplierScaleCode : BitVec 8
  accumulatedInterestScaleCode : BitVec 8
  openingPriceScaleCode : BitVec 8
  maximumPriceScaleCode : BitVec 8
  minimumPriceScaleCode : BitVec 8
  closingPriceScaleCode : BitVec 8
  impliedVolatilityScaleCode : BitVec 8
  averageWeightedPriceScaleCode : BitVec 8
  referencePriceScaleCode : BitVec 8
  pctChangePriceScaleCode : BitVec 8
  dividendRateScaleCode : BitVec 8
  settlementPriceScaleCode : BitVec 8
  settlementValueScaleCode : BitVec 8
  reserved1 : Alpha 1
  tradingValueScaleCode : BitVec 8
  currencyPriceScaleCode : BitVec 8
  deltaScaleCode : BitVec 8
  gammaScaleCode : BitVec 8
  rhoScaleCode : BitVec 8
  thetaScaleCode : BitVec 8
  vegaScaleCode : BitVec 8
  tradingValueCurrencyScaleCode : BitVec 8
  interestRateScaleCode : BitVec 8
  volatilityScaleCode : BitVec 8
  strikePriceScaleCode : BitVec 8
  valueShortSellingTradesScaleCode : BitVec 8
  lastTradePriceScaleCode : BitVec 8
  valueBlockTradesScaleCode : BitVec 8
  vwapBlocktradeScaleCode : BitVec 8
  maximumBlockPriceScaleCode : BitVec 8
  minimumBlockPriceScaleCode : BitVec 8
  statusIndicator : StatusIndicator
  sector : Alpha 3
  market : Market
  secondReserved1 : Alpha 1
  shortSale : Alpha 1
  markerPctChangePrice : MarkerPctChangePrice
  symbolDelta : SymbolDelta
  symbolGamma : SymbolGamma
  symbolRho : SymbolRho
  symbolTheta : SymbolTheta
  symbolVega : SymbolVega
  thirdReserved1 : Alpha 1
  fourthReserved1 : Alpha 1
  fifthReserved1 : Alpha 1
  sixthReserved1 : Alpha 1
  seventhReserved1 : Alpha 1
  eighthReserved1 : Alpha 1
  segment : Alpha 2
  lowerLiquidity : Alpha 1
  dividend : Alpha 2
  subscriptionRight : Alpha 2
  split : Alpha 2
  interimDividendRight : Alpha 2
  quotationSystem : Alpha 2
  liquiditySupportPge : Alpha 2
  ninthReserved1 : Alpha 1
  deriving DecidableEq, Repr

namespace SessionSummaryMessage

def encode (message : SessionSummaryMessage) : List UInt8 :=
  encodeUInt 4 message.symbolIndex
    ++ (encodeUInt 4 message.sourceTime
    ++ (encodeUInt 4 message.sourceSeqNum
    ++ (encodeUInt 4 message.date
    ++ (encodeUInt 4 message.multiplier
    ++ (encodeUInt 4 message.accumulatedInterest
    ++ (encodeUInt 4 message.openingPrice
    ++ (encodeUInt 4 message.maximumPrice
    ++ (encodeUInt 4 message.minimumPrice
    ++ (encodeUInt 4 message.closingPrice
    ++ (encodeUInt 4 message.impliedVolatility
    ++ (encodeUInt 4 message.averageWeightedPrice
    ++ (encodeUInt 4 message.referencePrice
    ++ (encodeUInt 4 message.pctChangePrice
    ++ (encodeUInt 4 message.dividendRate
    ++ (encodeUInt 4 message.settlementPrice
    ++ (encodeUInt 4 message.settlementValue
    ++ (Alpha.encode message.reserved4
    ++ (encodeUInt 4 message.openPositions
    ++ (encodeUInt 4 message.tradingVolume
    ++ (encodeUInt 4 message.transactionsNumber
    ++ (encodeUInt 8 message.tradingValue
    ++ (encodeUInt 4 message.currencyPrice
    ++ (encodeUInt 4 message.delta
    ++ (encodeUInt 4 message.gamma
    ++ (encodeUInt 4 message.rho
    ++ (encodeUInt 4 message.theta
    ++ (encodeUInt 4 message.vega
    ++ (encodeUInt 4 message.endTrading
    ++ (encodeUInt 4 message.numberOfInstruments
    ++ (encodeUInt 8 message.tradingValueCurrency
    ++ (encodeUInt 4 message.interestRate
    ++ (encodeUInt 4 message.volatility
    ++ (encodeUInt 4 message.strikePrice
    ++ (encodeUInt 4 message.shortSellingTradesNumber
    ++ (encodeUInt 4 message.volumeShortSellingTrades
    ++ (encodeUInt 4 message.valueShortSellingTrades
    ++ (encodeUInt 4 message.lastTradeDate
    ++ (encodeUInt 4 message.lastTradePrice
    ++ (encodeUInt 4 message.blockTradesNumber
    ++ (encodeUInt 4 message.volumeBlockTrades
    ++ (encodeUInt 4 message.valueBlockTrades
    ++ (encodeUInt 4 message.vwapBlocktrade
    ++ (encodeUInt 4 message.maximumBlockPrice
    ++ (encodeUInt 4 message.minimumBlockPrice
    ++ (encodeUInt 4 message.systemId
    ++ (encodeUInt 2 message.sourceTimeMicroSecs
    ++ (encodeUInt 1 message.multiplierScaleCode
    ++ (encodeUInt 1 message.accumulatedInterestScaleCode
    ++ (encodeUInt 1 message.openingPriceScaleCode
    ++ (encodeUInt 1 message.maximumPriceScaleCode
    ++ (encodeUInt 1 message.minimumPriceScaleCode
    ++ (encodeUInt 1 message.closingPriceScaleCode
    ++ (encodeUInt 1 message.impliedVolatilityScaleCode
    ++ (encodeUInt 1 message.averageWeightedPriceScaleCode
    ++ (encodeUInt 1 message.referencePriceScaleCode
    ++ (encodeUInt 1 message.pctChangePriceScaleCode
    ++ (encodeUInt 1 message.dividendRateScaleCode
    ++ (encodeUInt 1 message.settlementPriceScaleCode
    ++ (encodeUInt 1 message.settlementValueScaleCode
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 1 message.tradingValueScaleCode
    ++ (encodeUInt 1 message.currencyPriceScaleCode
    ++ (encodeUInt 1 message.deltaScaleCode
    ++ (encodeUInt 1 message.gammaScaleCode
    ++ (encodeUInt 1 message.rhoScaleCode
    ++ (encodeUInt 1 message.thetaScaleCode
    ++ (encodeUInt 1 message.vegaScaleCode
    ++ (encodeUInt 1 message.tradingValueCurrencyScaleCode
    ++ (encodeUInt 1 message.interestRateScaleCode
    ++ (encodeUInt 1 message.volatilityScaleCode
    ++ (encodeUInt 1 message.strikePriceScaleCode
    ++ (encodeUInt 1 message.valueShortSellingTradesScaleCode
    ++ (encodeUInt 1 message.lastTradePriceScaleCode
    ++ (encodeUInt 1 message.valueBlockTradesScaleCode
    ++ (encodeUInt 1 message.vwapBlocktradeScaleCode
    ++ (encodeUInt 1 message.maximumBlockPriceScaleCode
    ++ (encodeUInt 1 message.minimumBlockPriceScaleCode
    ++ (StatusIndicator.encode message.statusIndicator
    ++ (Alpha.encode message.sector
    ++ (Market.encode message.market
    ++ (Alpha.encode message.secondReserved1
    ++ (Alpha.encode message.shortSale
    ++ (MarkerPctChangePrice.encode message.markerPctChangePrice
    ++ (SymbolDelta.encode message.symbolDelta
    ++ (SymbolGamma.encode message.symbolGamma
    ++ (SymbolRho.encode message.symbolRho
    ++ (SymbolTheta.encode message.symbolTheta
    ++ (SymbolVega.encode message.symbolVega
    ++ (Alpha.encode message.thirdReserved1
    ++ (Alpha.encode message.fourthReserved1
    ++ (Alpha.encode message.fifthReserved1
    ++ (Alpha.encode message.sixthReserved1
    ++ (Alpha.encode message.seventhReserved1
    ++ (Alpha.encode message.eighthReserved1
    ++ (Alpha.encode message.segment
    ++ (Alpha.encode message.lowerLiquidity
    ++ (Alpha.encode message.dividend
    ++ (Alpha.encode message.subscriptionRight
    ++ (Alpha.encode message.split
    ++ (Alpha.encode message.interimDividendRight
    ++ (Alpha.encode message.quotationSystem
    ++ (Alpha.encode message.liquiditySupportPge
    ++ (Alpha.encode message.ninthReserved1)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SessionSummaryMessage × List UInt8) := do
  let (symbolIndex, bytes) ← decodeUInt 4 bytes
  let (sourceTime, bytes) ← decodeUInt 4 bytes
  let (sourceSeqNum, bytes) ← decodeUInt 4 bytes
  let (date, bytes) ← decodeUInt 4 bytes
  let (multiplier, bytes) ← decodeUInt 4 bytes
  let (accumulatedInterest, bytes) ← decodeUInt 4 bytes
  let (openingPrice, bytes) ← decodeUInt 4 bytes
  let (maximumPrice, bytes) ← decodeUInt 4 bytes
  let (minimumPrice, bytes) ← decodeUInt 4 bytes
  let (closingPrice, bytes) ← decodeUInt 4 bytes
  let (impliedVolatility, bytes) ← decodeUInt 4 bytes
  let (averageWeightedPrice, bytes) ← decodeUInt 4 bytes
  let (referencePrice, bytes) ← decodeUInt 4 bytes
  let (pctChangePrice, bytes) ← decodeUInt 4 bytes
  let (dividendRate, bytes) ← decodeUInt 4 bytes
  let (settlementPrice, bytes) ← decodeUInt 4 bytes
  let (settlementValue, bytes) ← decodeUInt 4 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (openPositions, bytes) ← decodeUInt 4 bytes
  let (tradingVolume, bytes) ← decodeUInt 4 bytes
  let (transactionsNumber, bytes) ← decodeUInt 4 bytes
  let (tradingValue, bytes) ← decodeUInt 8 bytes
  let (currencyPrice, bytes) ← decodeUInt 4 bytes
  let (delta, bytes) ← decodeUInt 4 bytes
  let (gamma, bytes) ← decodeUInt 4 bytes
  let (rho, bytes) ← decodeUInt 4 bytes
  let (theta, bytes) ← decodeUInt 4 bytes
  let (vega, bytes) ← decodeUInt 4 bytes
  let (endTrading, bytes) ← decodeUInt 4 bytes
  let (numberOfInstruments, bytes) ← decodeUInt 4 bytes
  let (tradingValueCurrency, bytes) ← decodeUInt 8 bytes
  let (interestRate, bytes) ← decodeUInt 4 bytes
  let (volatility, bytes) ← decodeUInt 4 bytes
  let (strikePrice, bytes) ← decodeUInt 4 bytes
  let (shortSellingTradesNumber, bytes) ← decodeUInt 4 bytes
  let (volumeShortSellingTrades, bytes) ← decodeUInt 4 bytes
  let (valueShortSellingTrades, bytes) ← decodeUInt 4 bytes
  let (lastTradeDate, bytes) ← decodeUInt 4 bytes
  let (lastTradePrice, bytes) ← decodeUInt 4 bytes
  let (blockTradesNumber, bytes) ← decodeUInt 4 bytes
  let (volumeBlockTrades, bytes) ← decodeUInt 4 bytes
  let (valueBlockTrades, bytes) ← decodeUInt 4 bytes
  let (vwapBlocktrade, bytes) ← decodeUInt 4 bytes
  let (maximumBlockPrice, bytes) ← decodeUInt 4 bytes
  let (minimumBlockPrice, bytes) ← decodeUInt 4 bytes
  let (systemId, bytes) ← decodeUInt 4 bytes
  let (sourceTimeMicroSecs, bytes) ← decodeUInt 2 bytes
  let (multiplierScaleCode, bytes) ← decodeUInt 1 bytes
  let (accumulatedInterestScaleCode, bytes) ← decodeUInt 1 bytes
  let (openingPriceScaleCode, bytes) ← decodeUInt 1 bytes
  let (maximumPriceScaleCode, bytes) ← decodeUInt 1 bytes
  let (minimumPriceScaleCode, bytes) ← decodeUInt 1 bytes
  let (closingPriceScaleCode, bytes) ← decodeUInt 1 bytes
  let (impliedVolatilityScaleCode, bytes) ← decodeUInt 1 bytes
  let (averageWeightedPriceScaleCode, bytes) ← decodeUInt 1 bytes
  let (referencePriceScaleCode, bytes) ← decodeUInt 1 bytes
  let (pctChangePriceScaleCode, bytes) ← decodeUInt 1 bytes
  let (dividendRateScaleCode, bytes) ← decodeUInt 1 bytes
  let (settlementPriceScaleCode, bytes) ← decodeUInt 1 bytes
  let (settlementValueScaleCode, bytes) ← decodeUInt 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (tradingValueScaleCode, bytes) ← decodeUInt 1 bytes
  let (currencyPriceScaleCode, bytes) ← decodeUInt 1 bytes
  let (deltaScaleCode, bytes) ← decodeUInt 1 bytes
  let (gammaScaleCode, bytes) ← decodeUInt 1 bytes
  let (rhoScaleCode, bytes) ← decodeUInt 1 bytes
  let (thetaScaleCode, bytes) ← decodeUInt 1 bytes
  let (vegaScaleCode, bytes) ← decodeUInt 1 bytes
  let (tradingValueCurrencyScaleCode, bytes) ← decodeUInt 1 bytes
  let (interestRateScaleCode, bytes) ← decodeUInt 1 bytes
  let (volatilityScaleCode, bytes) ← decodeUInt 1 bytes
  let (strikePriceScaleCode, bytes) ← decodeUInt 1 bytes
  let (valueShortSellingTradesScaleCode, bytes) ← decodeUInt 1 bytes
  let (lastTradePriceScaleCode, bytes) ← decodeUInt 1 bytes
  let (valueBlockTradesScaleCode, bytes) ← decodeUInt 1 bytes
  let (vwapBlocktradeScaleCode, bytes) ← decodeUInt 1 bytes
  let (maximumBlockPriceScaleCode, bytes) ← decodeUInt 1 bytes
  let (minimumBlockPriceScaleCode, bytes) ← decodeUInt 1 bytes
  let (statusIndicator, bytes) ← StatusIndicator.decode bytes
  let (sector, bytes) ← Alpha.decode 3 bytes
  let (market, bytes) ← Market.decode bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  let (shortSale, bytes) ← Alpha.decode 1 bytes
  let (markerPctChangePrice, bytes) ← MarkerPctChangePrice.decode bytes
  let (symbolDelta, bytes) ← SymbolDelta.decode bytes
  let (symbolGamma, bytes) ← SymbolGamma.decode bytes
  let (symbolRho, bytes) ← SymbolRho.decode bytes
  let (symbolTheta, bytes) ← SymbolTheta.decode bytes
  let (symbolVega, bytes) ← SymbolVega.decode bytes
  let (thirdReserved1, bytes) ← Alpha.decode 1 bytes
  let (fourthReserved1, bytes) ← Alpha.decode 1 bytes
  let (fifthReserved1, bytes) ← Alpha.decode 1 bytes
  let (sixthReserved1, bytes) ← Alpha.decode 1 bytes
  let (seventhReserved1, bytes) ← Alpha.decode 1 bytes
  let (eighthReserved1, bytes) ← Alpha.decode 1 bytes
  let (segment, bytes) ← Alpha.decode 2 bytes
  let (lowerLiquidity, bytes) ← Alpha.decode 1 bytes
  let (dividend, bytes) ← Alpha.decode 2 bytes
  let (subscriptionRight, bytes) ← Alpha.decode 2 bytes
  let (split, bytes) ← Alpha.decode 2 bytes
  let (interimDividendRight, bytes) ← Alpha.decode 2 bytes
  let (quotationSystem, bytes) ← Alpha.decode 2 bytes
  let (liquiditySupportPge, bytes) ← Alpha.decode 2 bytes
  let (ninthReserved1, bytes) ← Alpha.decode 1 bytes
  pure ({ symbolIndex, sourceTime, sourceSeqNum, date, multiplier, accumulatedInterest, openingPrice, maximumPrice, minimumPrice, closingPrice, impliedVolatility, averageWeightedPrice, referencePrice, pctChangePrice, dividendRate, settlementPrice, settlementValue, reserved4, openPositions, tradingVolume, transactionsNumber, tradingValue, currencyPrice, delta, gamma, rho, theta, vega, endTrading, numberOfInstruments, tradingValueCurrency, interestRate, volatility, strikePrice, shortSellingTradesNumber, volumeShortSellingTrades, valueShortSellingTrades, lastTradeDate, lastTradePrice, blockTradesNumber, volumeBlockTrades, valueBlockTrades, vwapBlocktrade, maximumBlockPrice, minimumBlockPrice, systemId, sourceTimeMicroSecs, multiplierScaleCode, accumulatedInterestScaleCode, openingPriceScaleCode, maximumPriceScaleCode, minimumPriceScaleCode, closingPriceScaleCode, impliedVolatilityScaleCode, averageWeightedPriceScaleCode, referencePriceScaleCode, pctChangePriceScaleCode, dividendRateScaleCode, settlementPriceScaleCode, settlementValueScaleCode, reserved1, tradingValueScaleCode, currencyPriceScaleCode, deltaScaleCode, gammaScaleCode, rhoScaleCode, thetaScaleCode, vegaScaleCode, tradingValueCurrencyScaleCode, interestRateScaleCode, volatilityScaleCode, strikePriceScaleCode, valueShortSellingTradesScaleCode, lastTradePriceScaleCode, valueBlockTradesScaleCode, vwapBlocktradeScaleCode, maximumBlockPriceScaleCode, minimumBlockPriceScaleCode, statusIndicator, sector, market, secondReserved1, shortSale, markerPctChangePrice, symbolDelta, symbolGamma, symbolRho, symbolTheta, symbolVega, thirdReserved1, fourthReserved1, fifthReserved1, sixthReserved1, seventhReserved1, eighthReserved1, segment, lowerLiquidity, dividend, subscriptionRight, split, interimDividendRight, quotationSystem, liquiditySupportPge, ninthReserved1 }, bytes)

@[simp] theorem encode_length (message : SessionSummaryMessage) : (encode message).length = 260 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, StatusIndicator.encode_length, Market.encode_length, MarkerPctChangePrice.encode_length, SymbolDelta.encode_length, SymbolGamma.encode_length, SymbolRho.encode_length, SymbolTheta.encode_length, SymbolVega.encode_length]

theorem encode_length_pos (message : SessionSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SessionSummaryMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, StatusIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Market.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarkerPctChangePrice.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SymbolDelta.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SymbolGamma.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SymbolRho.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SymbolTheta.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SymbolVega.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end SessionSummaryMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | classStateChangeMessage (message : ClassStateChangeMessage) -- 516
  | mailMessage (message : MailMessage) -- 523
  | collarsMessage (message : CollarsMessage) -- 537
  | sessionTimetableMessage (message : SessionTimetableMessage) -- 539
  | startReferentialMessage (message : StartReferentialMessage) -- 550
  | endReferentialMessage (message : EndReferentialMessage) -- 551
  | referentialMessage (message : ReferentialMessage) -- 556
  | sessionSummaryMessage (message : SessionSummaryMessage) -- 561
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 16
  | .classStateChangeMessage _ => 516
  | .mailMessage _ => 523
  | .collarsMessage _ => 537
  | .sessionTimetableMessage _ => 539
  | .startReferentialMessage _ => 550
  | .endReferentialMessage _ => 551
  | .referentialMessage _ => 556
  | .sessionSummaryMessage _ => 561

def encode : Payload → List UInt8
  | .classStateChangeMessage message => ClassStateChangeMessage.encode message
  | .mailMessage message => MailMessage.encode message
  | .collarsMessage message => CollarsMessage.encode message
  | .sessionTimetableMessage message => SessionTimetableMessage.encode message
  | .startReferentialMessage message => StartReferentialMessage.encode message
  | .endReferentialMessage message => EndReferentialMessage.encode message
  | .referentialMessage message => ReferentialMessage.encode message
  | .sessionSummaryMessage message => SessionSummaryMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 1098 := by
  cases message with
  | classStateChangeMessage inner =>
    simp only [encode, ClassStateChangeMessage.encode_length]
    omega
  | mailMessage inner =>
    simp only [encode, MailMessage.encode_length]
    omega
  | collarsMessage inner =>
    simp only [encode, CollarsMessage.encode_length]
    omega
  | sessionTimetableMessage inner =>
    simp only [encode, SessionTimetableMessage.encode_length]
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
  | sessionSummaryMessage inner =>
    simp only [encode, SessionSummaryMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 516 then (ClassStateChangeMessage.decode bytes).map fun (message, rest) => (.classStateChangeMessage message, rest)
  else if tag = 523 then (MailMessage.decode bytes).map fun (message, rest) => (.mailMessage message, rest)
  else if tag = 537 then (CollarsMessage.decode bytes).map fun (message, rest) => (.collarsMessage message, rest)
  else if tag = 539 then (SessionTimetableMessage.decode bytes).map fun (message, rest) => (.sessionTimetableMessage message, rest)
  else if tag = 550 then (StartReferentialMessage.decode bytes).map fun (message, rest) => (.startReferentialMessage message, rest)
  else if tag = 551 then (EndReferentialMessage.decode bytes).map fun (message, rest) => (.endReferentialMessage message, rest)
  else if tag = 556 then (ReferentialMessage.decode bytes).map fun (message, rest) => (.referentialMessage message, rest)
  else if tag = 561 then (SessionSummaryMessage.decode bytes).map fun (message, rest) => (.sessionSummaryMessage message, rest)
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
  | classStateChangeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ClassStateChangeMessage.encode_length]
    omega
  | mailMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MailMessage.encode_length]
    omega
  | collarsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, CollarsMessage.encode_length]
    omega
  | sessionTimetableMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SessionTimetableMessage.encode_length]
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
  | sessionSummaryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SessionSummaryMessage.encode_length]
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
  | zlib (tag : { v : BitVec 8 // 15 < v }) (message : MessageBufferZlib) -- 15 < tag
  | plain (tag : { v : BitVec 8 // ¬ (15 < v) }) (message : MessageBuffer numberMsgEntries) -- every other value
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
  if h : 15 < tag then (MessageBufferZlib.decode bytes).map fun message => .zlib ⟨tag, h⟩ message
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

end Omi.GpwBondspotMarketinformationXdpV68
