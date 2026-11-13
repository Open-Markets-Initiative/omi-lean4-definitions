import Wire

/-!
# Hong Kong Exchanges and Clearing Orion Market Data Cash FullTick Retransmission v1.44

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.

Note: Message's Msg Size is written from its body but not checked on decode, since the body has no
bound the prefix must fit; the body is read by its content

License: MIT No Attribution
-/

namespace Omi.HkexHkexsecuritiesFulltickretransOmdV144

/-- Order Type: one byte code -/
def OrderType.codes : List UInt8 :=
  [0x31, 0x32]

inductive OrderType where
  | market -- Market
  | limit -- Limit
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderType

def toByte : OrderType → UInt8
  | .market => 0x31
  | .limit => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderType :=
  if byte = 0x31 then .market
  else .limit

def ofByte (byte : UInt8) : OrderType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderType) : ofByte value.toByte = value := by
  cases value with
  | market => decide
  | limit => decide
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

/-- Order Imbalance Direction: one byte code -/
def OrderImbalanceDirection.codes : List UInt8 :=
  [0x4E, 0x42, 0x53, 0x20]

inductive OrderImbalanceDirection where
  | buyEqualsSell -- Buy Equals Sell
  | buySurplus -- Buy Surplus
  | sellSurplus -- Sell Surplus
  | notApplicableIepNotAvailable -- Not Applicable Iep Not Available
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderImbalanceDirection.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderImbalanceDirection

def toByte : OrderImbalanceDirection → UInt8
  | .buyEqualsSell => 0x4E
  | .buySurplus => 0x42
  | .sellSurplus => 0x53
  | .notApplicableIepNotAvailable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderImbalanceDirection :=
  if byte = 0x4E then .buyEqualsSell
  else if byte = 0x42 then .buySurplus
  else if byte = 0x53 then .sellSurplus
  else .notApplicableIepNotAvailable

def ofByte (byte : UInt8) : OrderImbalanceDirection :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderImbalanceDirection) : ofByte value.toByte = value := by
  cases value with
  | buyEqualsSell => decide
  | buySurplus => decide
  | sellSurplus => decide
  | notApplicableIepNotAvailable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderImbalanceDirection) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderImbalanceDirection × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderImbalanceDirection) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OrderImbalanceDirection) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OrderImbalanceDirection) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderImbalanceDirection

/-- Vcm Flag: one byte code -/
def VcmFlag.codes : List UInt8 :=
  [0x59, 0x4E]

inductive VcmFlag where
  | vcmApplicable -- Vcm Applicable
  | vcmNotApplicable -- Vcm Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ VcmFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace VcmFlag

def toByte : VcmFlag → UInt8
  | .vcmApplicable => 0x59
  | .vcmNotApplicable => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : VcmFlag :=
  if byte = 0x59 then .vcmApplicable
  else .vcmNotApplicable

def ofByte (byte : UInt8) : VcmFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : VcmFlag) : ofByte value.toByte = value := by
  cases value with
  | vcmApplicable => decide
  | vcmNotApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : VcmFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (VcmFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : VcmFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : VcmFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : VcmFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end VcmFlag

/-- Short Sell Flag: one byte code -/
def ShortSellFlag.codes : List UInt8 :=
  [0x59, 0x4E]

inductive ShortSellFlag where
  | shortSellAllowed -- Short Sell Allowed
  | shortSellNotAllowed -- Short Sell Not Allowed
  | unlisted (byte : { byte : UInt8 // byte ∉ ShortSellFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ShortSellFlag

def toByte : ShortSellFlag → UInt8
  | .shortSellAllowed => 0x59
  | .shortSellNotAllowed => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ShortSellFlag :=
  if byte = 0x59 then .shortSellAllowed
  else .shortSellNotAllowed

def ofByte (byte : UInt8) : ShortSellFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ShortSellFlag) : ofByte value.toByte = value := by
  cases value with
  | shortSellAllowed => decide
  | shortSellNotAllowed => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ShortSellFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ShortSellFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ShortSellFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ShortSellFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ShortSellFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ShortSellFlag

/-- Cas Flag: one byte code -/
def CasFlag.codes : List UInt8 :=
  [0x59, 0x4E]

inductive CasFlag where
  | casApplicable -- Cas Applicable
  | casNotApplicable -- Cas Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ CasFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CasFlag

def toByte : CasFlag → UInt8
  | .casApplicable => 0x59
  | .casNotApplicable => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CasFlag :=
  if byte = 0x59 then .casApplicable
  else .casNotApplicable

def ofByte (byte : UInt8) : CasFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CasFlag) : ofByte value.toByte = value := by
  cases value with
  | casApplicable => decide
  | casNotApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CasFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CasFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CasFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CasFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CasFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CasFlag

/-- Ccass Flag: one byte code -/
def CcassFlag.codes : List UInt8 :=
  [0x59, 0x4E]

inductive CcassFlag where
  | ccassSecurity -- Ccass Security
  | nonCcassSecurity -- Non Ccass Security
  | unlisted (byte : { byte : UInt8 // byte ∉ CcassFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CcassFlag

def toByte : CcassFlag → UInt8
  | .ccassSecurity => 0x59
  | .nonCcassSecurity => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CcassFlag :=
  if byte = 0x59 then .ccassSecurity
  else .nonCcassSecurity

def ofByte (byte : UInt8) : CcassFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CcassFlag) : ofByte value.toByte = value := by
  cases value with
  | ccassSecurity => decide
  | nonCcassSecurity => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CcassFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CcassFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CcassFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CcassFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CcassFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CcassFlag

/-- Dummy Security Flag: one byte code -/
def DummySecurityFlag.codes : List UInt8 :=
  [0x59, 0x4E]

inductive DummySecurityFlag where
  | dummySecurity -- Dummy Security
  | normalSecurity -- Normal Security
  | unlisted (byte : { byte : UInt8 // byte ∉ DummySecurityFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DummySecurityFlag

def toByte : DummySecurityFlag → UInt8
  | .dummySecurity => 0x59
  | .normalSecurity => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DummySecurityFlag :=
  if byte = 0x59 then .dummySecurity
  else .normalSecurity

def ofByte (byte : UInt8) : DummySecurityFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DummySecurityFlag) : ofByte value.toByte = value := by
  cases value with
  | dummySecurity => decide
  | normalSecurity => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DummySecurityFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DummySecurityFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DummySecurityFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : DummySecurityFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : DummySecurityFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DummySecurityFlag

/-- Stamp Duty Flag: one byte code -/
def StampDutyFlag.codes : List UInt8 :=
  [0x59, 0x4E]

inductive StampDutyFlag where
  | stampDutyRequired -- Stamp Duty Required
  | stampDutyNotRequired -- Stamp Duty Not Required
  | unlisted (byte : { byte : UInt8 // byte ∉ StampDutyFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace StampDutyFlag

def toByte : StampDutyFlag → UInt8
  | .stampDutyRequired => 0x59
  | .stampDutyNotRequired => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : StampDutyFlag :=
  if byte = 0x59 then .stampDutyRequired
  else .stampDutyNotRequired

def ofByte (byte : UInt8) : StampDutyFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : StampDutyFlag) : ofByte value.toByte = value := by
  cases value with
  | stampDutyRequired => decide
  | stampDutyNotRequired => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : StampDutyFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (StampDutyFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : StampDutyFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : StampDutyFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : StampDutyFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end StampDutyFlag

/-- Pos Flag: one byte code -/
def PosFlag.codes : List UInt8 :=
  [0x59, 0x4E]

inductive PosFlag where
  | posApplicable -- Pos Applicable
  | posNotApplicable -- Pos Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ PosFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PosFlag

def toByte : PosFlag → UInt8
  | .posApplicable => 0x59
  | .posNotApplicable => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PosFlag :=
  if byte = 0x59 then .posApplicable
  else .posNotApplicable

def ofByte (byte : UInt8) : PosFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PosFlag) : ofByte value.toByte = value := by
  cases value with
  | posApplicable => decide
  | posNotApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PosFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PosFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PosFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : PosFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : PosFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PosFlag

/-- Efn Flag: one byte code -/
def EfnFlag.codes : List UInt8 :=
  [0x59, 0x4E]

inductive EfnFlag where
  | efn -- Efn
  | nonEfn -- Non Efn
  | unlisted (byte : { byte : UInt8 // byte ∉ EfnFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EfnFlag

def toByte : EfnFlag → UInt8
  | .efn => 0x59
  | .nonEfn => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EfnFlag :=
  if byte = 0x59 then .efn
  else .nonEfn

def ofByte (byte : UInt8) : EfnFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EfnFlag) : ofByte value.toByte = value := by
  cases value with
  | efn => decide
  | nonEfn => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : EfnFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (EfnFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : EfnFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : EfnFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : EfnFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end EfnFlag

/-- Investor Type: one byte code -/
def InvestorType.codes : List UInt8 :=
  [0x52, 0x50]

inductive InvestorType where
  | retailInvestor -- Retail Investor
  | professionalInvestor -- Professional Investor
  | unlisted (byte : { byte : UInt8 // byte ∉ InvestorType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InvestorType

def toByte : InvestorType → UInt8
  | .retailInvestor => 0x52
  | .professionalInvestor => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : InvestorType :=
  if byte = 0x52 then .retailInvestor
  else .professionalInvestor

def ofByte (byte : UInt8) : InvestorType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InvestorType) : ofByte value.toByte = value := by
  cases value with
  | retailInvestor => decide
  | professionalInvestor => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : InvestorType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (InvestorType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : InvestorType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : InvestorType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : InvestorType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end InvestorType

/-- Call Put Flag: one byte code -/
def CallPutFlag.codes : List UInt8 :=
  [0x43, 0x50, 0x4F]

inductive CallPutFlag where
  | callOrBull -- Call Or Bull
  | putOrBearRange -- Put Or Bear Range
  | others -- Others
  | unlisted (byte : { byte : UInt8 // byte ∉ CallPutFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CallPutFlag

def toByte : CallPutFlag → UInt8
  | .callOrBull => 0x43
  | .putOrBearRange => 0x50
  | .others => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CallPutFlag :=
  if byte = 0x43 then .callOrBull
  else if byte = 0x50 then .putOrBearRange
  else .others

def ofByte (byte : UInt8) : CallPutFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CallPutFlag) : ofByte value.toByte = value := by
  cases value with
  | callOrBull => decide
  | putOrBearRange => decide
  | others => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CallPutFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CallPutFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CallPutFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CallPutFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CallPutFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CallPutFlag

/-- Style: one byte code -/
def Style.codes : List UInt8 :=
  [0x41, 0x45, 0x20]

inductive Style where
  | americanStyle -- American Style
  | europeanStyle -- European Style
  | other -- Other
  | unlisted (byte : { byte : UInt8 // byte ∉ Style.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Style

def toByte : Style → UInt8
  | .americanStyle => 0x41
  | .europeanStyle => 0x45
  | .other => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Style :=
  if byte = 0x41 then .americanStyle
  else if byte = 0x45 then .europeanStyle
  else .other

def ofByte (byte : UInt8) : Style :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Style) : ofByte value.toByte = value := by
  cases value with
  | americanStyle => decide
  | europeanStyle => decide
  | other => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Style) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Style × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Style) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Style) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Style) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Style

/-- Warrant Type: one byte code -/
def WarrantType.codes : List UInt8 :=
  [0x4E, 0x58, 0x30]

inductive WarrantType where
  | normalInstrument -- Normal Instrument
  | exoticInstrument -- Exotic Instrument
  | notAvailable -- Not Available
  | unlisted (byte : { byte : UInt8 // byte ∉ WarrantType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace WarrantType

def toByte : WarrantType → UInt8
  | .normalInstrument => 0x4E
  | .exoticInstrument => 0x58
  | .notAvailable => 0x30
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : WarrantType :=
  if byte = 0x4E then .normalInstrument
  else if byte = 0x58 then .exoticInstrument
  else .notAvailable

def ofByte (byte : UInt8) : WarrantType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : WarrantType) : ofByte value.toByte = value := by
  cases value with
  | normalInstrument => decide
  | exoticInstrument => decide
  | notAvailable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : WarrantType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (WarrantType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : WarrantType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : WarrantType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : WarrantType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end WarrantType

/-- Trading Ses Control Flag: one byte code -/
def TradingSesControlFlag.codes : List UInt8 :=
  [0x30, 0x31]

inductive TradingSesControlFlag where
  | automaticDefault -- Automatic Default
  | manualInvalidatesTheNormalScheduleForTheDay -- Manual Invalidates The Normal Schedule For The Day
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingSesControlFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingSesControlFlag

def toByte : TradingSesControlFlag → UInt8
  | .automaticDefault => 0x30
  | .manualInvalidatesTheNormalScheduleForTheDay => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingSesControlFlag :=
  if byte = 0x30 then .automaticDefault
  else .manualInvalidatesTheNormalScheduleForTheDay

def ofByte (byte : UInt8) : TradingSesControlFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingSesControlFlag) : ofByte value.toByte = value := by
  cases value with
  | automaticDefault => decide
  | manualInvalidatesTheNormalScheduleForTheDay => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradingSesControlFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradingSesControlFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradingSesControlFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TradingSesControlFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TradingSesControlFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradingSesControlFlag

/-- Add Order Message: 28 bytes -/
structure AddOrderMessage where
  securityCode : BitVec 32
  orderId : BitVec 64
  price : BitVec 32
  quantity : BitVec 32
  side : BitVec 16
  orderType : OrderType
  filler1 : Alpha 1
  orderBookPosition : BitVec 32
  deriving DecidableEq, Repr

namespace AddOrderMessage

def encode (message : AddOrderMessage) : List UInt8 :=
  encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 2 message.side
    ++ (OrderType.encode message.orderType
    ++ (Alpha.encode message.filler1
    ++ (encodeUIntLE 4 message.orderBookPosition)))))))

def decode (bytes : List UInt8) : Option (AddOrderMessage × List UInt8) := do
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← decodeUIntLE 2 bytes
  let (orderType, bytes) ← OrderType.decode bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (orderBookPosition, bytes) ← decodeUIntLE 4 bytes
  pure ({ securityCode, orderId, price, quantity, side, orderType, filler1, orderBookPosition }, bytes)

@[simp] theorem encode_length (message : AddOrderMessage) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, OrderType.encode_length, Alpha.encode_length]

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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrderType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end AddOrderMessage

/-- Sequence Reset Message: 4 bytes -/
structure SequenceResetMessage where
  newSeqNo : BitVec 32
  deriving DecidableEq, Repr

namespace SequenceResetMessage

def encode (message : SequenceResetMessage) : List UInt8 :=
  encodeUIntLE 4 message.newSeqNo

def decode (bytes : List UInt8) : Option (SequenceResetMessage × List UInt8) := do
  let (newSeqNo, bytes) ← decodeUIntLE 4 bytes
  pure ({ newSeqNo }, bytes)

@[simp] theorem encode_length (message : SequenceResetMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : SequenceResetMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SequenceResetMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SequenceResetMessage

/-- Disaster Recovery Signal Message: 4 bytes -/
structure DisasterRecoverySignalMessage where
  drStatus : BitVec 32
  deriving DecidableEq, Repr

namespace DisasterRecoverySignalMessage

def encode (message : DisasterRecoverySignalMessage) : List UInt8 :=
  encodeUIntLE 4 message.drStatus

def decode (bytes : List UInt8) : Option (DisasterRecoverySignalMessage × List UInt8) := do
  let (drStatus, bytes) ← decodeUIntLE 4 bytes
  pure ({ drStatus }, bytes)

@[simp] theorem encode_length (message : DisasterRecoverySignalMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : DisasterRecoverySignalMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DisasterRecoverySignalMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end DisasterRecoverySignalMessage

/-- Delete Order Message: 16 bytes -/
structure DeleteOrderMessage where
  securityCode : BitVec 32
  orderId : BitVec 64
  side : BitVec 16
  filler2 : Alpha 2
  deriving DecidableEq, Repr

namespace DeleteOrderMessage

def encode (message : DeleteOrderMessage) : List UInt8 :=
  encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 2 message.side
    ++ (Alpha.encode message.filler2)))

def decode (bytes : List UInt8) : Option (DeleteOrderMessage × List UInt8) := do
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← decodeUIntLE 2 bytes
  let (filler2, bytes) ← Alpha.decode 2 bytes
  pure ({ securityCode, orderId, side, filler2 }, bytes)

@[simp] theorem encode_length (message : DeleteOrderMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : DeleteOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DeleteOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end DeleteOrderMessage

/-- Indicative Equilibrium Price Message: 16 bytes -/
structure IndicativeEquilibriumPriceMessage where
  securityCode : BitVec 32
  price : BitVec 32
  aggregateQuantity : BitVec 64
  deriving DecidableEq, Repr

namespace IndicativeEquilibriumPriceMessage

def encode (message : IndicativeEquilibriumPriceMessage) : List UInt8 :=
  encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 8 message.aggregateQuantity))

def decode (bytes : List UInt8) : Option (IndicativeEquilibriumPriceMessage × List UInt8) := do
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (aggregateQuantity, bytes) ← decodeUIntLE 8 bytes
  pure ({ securityCode, price, aggregateQuantity }, bytes)

@[simp] theorem encode_length (message : IndicativeEquilibriumPriceMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : IndicativeEquilibriumPriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IndicativeEquilibriumPriceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end IndicativeEquilibriumPriceMessage

/-- Modify Order Message: 24 bytes -/
structure ModifyOrderMessage where
  securityCode : BitVec 32
  orderId : BitVec 64
  quantity : BitVec 32
  side : BitVec 16
  filler2 : Alpha 2
  orderBookPosition : BitVec 32
  deriving DecidableEq, Repr

namespace ModifyOrderMessage

def encode (message : ModifyOrderMessage) : List UInt8 :=
  encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 2 message.side
    ++ (Alpha.encode message.filler2
    ++ (encodeUIntLE 4 message.orderBookPosition)))))

def decode (bytes : List UInt8) : Option (ModifyOrderMessage × List UInt8) := do
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← decodeUIntLE 2 bytes
  let (filler2, bytes) ← Alpha.decode 2 bytes
  let (orderBookPosition, bytes) ← decodeUIntLE 4 bytes
  pure ({ securityCode, orderId, quantity, side, filler2, orderBookPosition }, bytes)

@[simp] theorem encode_length (message : ModifyOrderMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : ModifyOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ModifyOrderMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ModifyOrderMessage

/-- Order Imbalance Message: 16 bytes -/
structure OrderImbalanceMessage where
  securityCode : BitVec 32
  orderImbalanceDirection : OrderImbalanceDirection
  filler1 : Alpha 1
  orderImbalanceQuantity : BitVec 64
  filler2 : Alpha 2
  deriving DecidableEq, Repr

namespace OrderImbalanceMessage

def encode (message : OrderImbalanceMessage) : List UInt8 :=
  encodeUIntLE 4 message.securityCode
    ++ (OrderImbalanceDirection.encode message.orderImbalanceDirection
    ++ (Alpha.encode message.filler1
    ++ (encodeUIntLE 8 message.orderImbalanceQuantity
    ++ (Alpha.encode message.filler2))))

def decode (bytes : List UInt8) : Option (OrderImbalanceMessage × List UInt8) := do
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (orderImbalanceDirection, bytes) ← OrderImbalanceDirection.decode bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (orderImbalanceQuantity, bytes) ← decodeUIntLE 8 bytes
  let (filler2, bytes) ← Alpha.decode 2 bytes
  pure ({ securityCode, orderImbalanceDirection, filler1, orderImbalanceQuantity, filler2 }, bytes)

@[simp] theorem encode_length (message : OrderImbalanceMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, OrderImbalanceDirection.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderImbalanceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderImbalanceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrderImbalanceDirection.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderImbalanceMessage

/-- Market Definition Message: 36 bytes -/
structure MarketDefinitionMessage where
  marketCode : Alpha 4
  marketName : Alpha 25
  currencyCode : Alpha 3
  numberOfSecurities : BitVec 32
  deriving DecidableEq, Repr

namespace MarketDefinitionMessage

def encode (message : MarketDefinitionMessage) : List UInt8 :=
  Alpha.encode message.marketCode
    ++ (Alpha.encode message.marketName
    ++ (Alpha.encode message.currencyCode
    ++ (encodeUIntLE 4 message.numberOfSecurities)))

def decode (bytes : List UInt8) : Option (MarketDefinitionMessage × List UInt8) := do
  let (marketCode, bytes) ← Alpha.decode 4 bytes
  let (marketName, bytes) ← Alpha.decode 25 bytes
  let (currencyCode, bytes) ← Alpha.decode 3 bytes
  let (numberOfSecurities, bytes) ← decodeUIntLE 4 bytes
  pure ({ marketCode, marketName, currencyCode, numberOfSecurities }, bytes)

@[simp] theorem encode_length (message : MarketDefinitionMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : MarketDefinitionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketDefinitionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end MarketDefinitionMessage

/-- Underlying Security: 8 bytes -/
structure UnderlyingSecurity where
  underlyingSecurityCode : BitVec 32
  filler4 : Alpha 4
  deriving DecidableEq, Repr

namespace UnderlyingSecurity

def encode (message : UnderlyingSecurity) : List UInt8 :=
  encodeUIntLE 4 message.underlyingSecurityCode
    ++ (Alpha.encode message.filler4)

def decode (bytes : List UInt8) : Option (UnderlyingSecurity × List UInt8) := do
  let (underlyingSecurityCode, bytes) ← decodeUIntLE 4 bytes
  let (filler4, bytes) ← Alpha.decode 4 bytes
  pure ({ underlyingSecurityCode, filler4 }, bytes)

@[simp] theorem encode_length (message : UnderlyingSecurity) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : UnderlyingSecurity) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UnderlyingSecurity) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end UnderlyingSecurity

/-- Security Definition Message -/
structure SecurityDefinitionMessage where
  securityCode : BitVec 32
  marketCode : Alpha 4
  isinCode : Alpha 12
  instrumentType : Alpha 4
  productType : BitVec 8
  filler1 : Alpha 1
  spreadTableCode : Alpha 2
  securityShortName : Alpha 40
  currencyCode : Alpha 3
  securityNameGccs : Alpha 60
  securityNameGb : Alpha 60
  lotSize : BitVec 32
  filler4 : Alpha 4
  previousClosingPrice : BitVec 32
  vcmFlag : VcmFlag
  shortSellFlag : ShortSellFlag
  casFlag : CasFlag
  ccassFlag : CcassFlag
  dummySecurityFlag : DummySecurityFlag
  secondFiller1 : Alpha 1
  stampDutyFlag : StampDutyFlag
  thirdFiller1 : Alpha 1
  listingDate : BitVec 32
  delistingDate : BitVec 32
  freeText : Alpha 38
  filler62 : Alpha 62
  posFlag : PosFlag
  posUpperLimit : BitVec 32
  posLowerLimit : BitVec 32
  domainStmtSecurityCode : BitVec 32
  filler37 : Alpha 37
  efnFlag : EfnFlag
  accruedInterest : BitVec 32
  couponRate : BitVec 32
  fourthFiller1 : Alpha 1
  faceValue : BitVec 64
  decimalsInFaceValue : BitVec 8
  faceValueCurrency : Alpha 3
  bondMaturityDate : BitVec 32
  investorType : InvestorType
  filler44 : Alpha 44
  conversionRatio : BitVec 32
  strikePrice1 : BitVec 32
  strikePrice2 : BitVec 32
  warrantMaturityDate : BitVec 32
  callPutFlag : CallPutFlag
  style : Style
  filler2 : Alpha 2
  warrantType : WarrantType
  callPrice : BitVec 32
  decimalsInCallPrice : BitVec 8
  entitlement : BitVec 32
  decimalsInEntitlement : BitVec 8
  noWarrantsPerEntitlement : BitVec 32
  filler63 : Alpha 63
  underlyingSecurity : Bounded 2 UnderlyingSecurity
  deriving DecidableEq, Repr

namespace SecurityDefinitionMessage

def encode (message : SecurityDefinitionMessage) : List UInt8 :=
  encodeUIntLE 4 message.securityCode
    ++ (Alpha.encode message.marketCode
    ++ (Alpha.encode message.isinCode
    ++ (Alpha.encode message.instrumentType
    ++ (encodeUInt 1 message.productType
    ++ (Alpha.encode message.filler1
    ++ (Alpha.encode message.spreadTableCode
    ++ (Alpha.encode message.securityShortName
    ++ (Alpha.encode message.currencyCode
    ++ (Alpha.encode message.securityNameGccs
    ++ (Alpha.encode message.securityNameGb
    ++ (encodeUIntLE 4 message.lotSize
    ++ (Alpha.encode message.filler4
    ++ (encodeUIntLE 4 message.previousClosingPrice
    ++ (VcmFlag.encode message.vcmFlag
    ++ (ShortSellFlag.encode message.shortSellFlag
    ++ (CasFlag.encode message.casFlag
    ++ (CcassFlag.encode message.ccassFlag
    ++ (DummySecurityFlag.encode message.dummySecurityFlag
    ++ (Alpha.encode message.secondFiller1
    ++ (StampDutyFlag.encode message.stampDutyFlag
    ++ (Alpha.encode message.thirdFiller1
    ++ (encodeUIntLE 4 message.listingDate
    ++ (encodeUIntLE 4 message.delistingDate
    ++ (Alpha.encode message.freeText
    ++ (Alpha.encode message.filler62
    ++ (PosFlag.encode message.posFlag
    ++ (encodeUIntLE 4 message.posUpperLimit
    ++ (encodeUIntLE 4 message.posLowerLimit
    ++ (encodeUIntLE 4 message.domainStmtSecurityCode
    ++ (Alpha.encode message.filler37
    ++ (EfnFlag.encode message.efnFlag
    ++ (encodeUIntLE 4 message.accruedInterest
    ++ (encodeUIntLE 4 message.couponRate
    ++ (Alpha.encode message.fourthFiller1
    ++ (encodeUIntLE 8 message.faceValue
    ++ (encodeUInt 1 message.decimalsInFaceValue
    ++ (Alpha.encode message.faceValueCurrency
    ++ (encodeUIntLE 4 message.bondMaturityDate
    ++ (InvestorType.encode message.investorType
    ++ (Alpha.encode message.filler44
    ++ (encodeUIntLE 4 message.conversionRatio
    ++ (encodeUIntLE 4 message.strikePrice1
    ++ (encodeUIntLE 4 message.strikePrice2
    ++ (encodeUIntLE 4 message.warrantMaturityDate
    ++ (CallPutFlag.encode message.callPutFlag
    ++ (Style.encode message.style
    ++ (Alpha.encode message.filler2
    ++ (WarrantType.encode message.warrantType
    ++ (encodeUIntLE 4 message.callPrice
    ++ (encodeUInt 1 message.decimalsInCallPrice
    ++ (encodeUIntLE 4 message.entitlement
    ++ (encodeUInt 1 message.decimalsInEntitlement
    ++ (encodeUIntLE 4 message.noWarrantsPerEntitlement
    ++ (Alpha.encode message.filler63
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.underlyingSecurity.val.length)
    ++ (encodeMany UnderlyingSecurity.encode message.underlyingSecurity.val))))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SecurityDefinitionMessage × List UInt8) := do
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (marketCode, bytes) ← Alpha.decode 4 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (instrumentType, bytes) ← Alpha.decode 4 bytes
  let (productType, bytes) ← decodeUInt 1 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (spreadTableCode, bytes) ← Alpha.decode 2 bytes
  let (securityShortName, bytes) ← Alpha.decode 40 bytes
  let (currencyCode, bytes) ← Alpha.decode 3 bytes
  let (securityNameGccs, bytes) ← Alpha.decode 60 bytes
  let (securityNameGb, bytes) ← Alpha.decode 60 bytes
  let (lotSize, bytes) ← decodeUIntLE 4 bytes
  let (filler4, bytes) ← Alpha.decode 4 bytes
  let (previousClosingPrice, bytes) ← decodeUIntLE 4 bytes
  let (vcmFlag, bytes) ← VcmFlag.decode bytes
  let (shortSellFlag, bytes) ← ShortSellFlag.decode bytes
  let (casFlag, bytes) ← CasFlag.decode bytes
  let (ccassFlag, bytes) ← CcassFlag.decode bytes
  let (dummySecurityFlag, bytes) ← DummySecurityFlag.decode bytes
  let (secondFiller1, bytes) ← Alpha.decode 1 bytes
  let (stampDutyFlag, bytes) ← StampDutyFlag.decode bytes
  let (thirdFiller1, bytes) ← Alpha.decode 1 bytes
  let (listingDate, bytes) ← decodeUIntLE 4 bytes
  let (delistingDate, bytes) ← decodeUIntLE 4 bytes
  let (freeText, bytes) ← Alpha.decode 38 bytes
  let (filler62, bytes) ← Alpha.decode 62 bytes
  let (posFlag, bytes) ← PosFlag.decode bytes
  let (posUpperLimit, bytes) ← decodeUIntLE 4 bytes
  let (posLowerLimit, bytes) ← decodeUIntLE 4 bytes
  let (domainStmtSecurityCode, bytes) ← decodeUIntLE 4 bytes
  let (filler37, bytes) ← Alpha.decode 37 bytes
  let (efnFlag, bytes) ← EfnFlag.decode bytes
  let (accruedInterest, bytes) ← decodeUIntLE 4 bytes
  let (couponRate, bytes) ← decodeUIntLE 4 bytes
  let (fourthFiller1, bytes) ← Alpha.decode 1 bytes
  let (faceValue, bytes) ← decodeUIntLE 8 bytes
  let (decimalsInFaceValue, bytes) ← decodeUInt 1 bytes
  let (faceValueCurrency, bytes) ← Alpha.decode 3 bytes
  let (bondMaturityDate, bytes) ← decodeUIntLE 4 bytes
  let (investorType, bytes) ← InvestorType.decode bytes
  let (filler44, bytes) ← Alpha.decode 44 bytes
  let (conversionRatio, bytes) ← decodeUIntLE 4 bytes
  let (strikePrice1, bytes) ← decodeUIntLE 4 bytes
  let (strikePrice2, bytes) ← decodeUIntLE 4 bytes
  let (warrantMaturityDate, bytes) ← decodeUIntLE 4 bytes
  let (callPutFlag, bytes) ← CallPutFlag.decode bytes
  let (style, bytes) ← Style.decode bytes
  let (filler2, bytes) ← Alpha.decode 2 bytes
  let (warrantType, bytes) ← WarrantType.decode bytes
  let (callPrice, bytes) ← decodeUIntLE 4 bytes
  let (decimalsInCallPrice, bytes) ← decodeUInt 1 bytes
  let (entitlement, bytes) ← decodeUIntLE 4 bytes
  let (decimalsInEntitlement, bytes) ← decodeUInt 1 bytes
  let (noWarrantsPerEntitlement, bytes) ← decodeUIntLE 4 bytes
  let (filler63, bytes) ← Alpha.decode 63 bytes
  let (noUnderlyingSecurities, bytes) ← decodeUIntLE 2 bytes
  let (underlyingSecurity_, bytes) ← decodeMany UnderlyingSecurity.decode noUnderlyingSecurities.toNat bytes
  if fits_underlyingSecurity : underlyingSecurity_.length < 256 ^ 2 then
    pure ({ securityCode, marketCode, isinCode, instrumentType, productType, filler1, spreadTableCode, securityShortName, currencyCode, securityNameGccs, securityNameGb, lotSize, filler4, previousClosingPrice, vcmFlag, shortSellFlag, casFlag, ccassFlag, dummySecurityFlag, secondFiller1, stampDutyFlag, thirdFiller1, listingDate, delistingDate, freeText, filler62, posFlag, posUpperLimit, posLowerLimit, domainStmtSecurityCode, filler37, efnFlag, accruedInterest, couponRate, fourthFiller1, faceValue, decimalsInFaceValue, faceValueCurrency, bondMaturityDate, investorType, filler44, conversionRatio, strikePrice1, strikePrice2, warrantMaturityDate, callPutFlag, style, filler2, warrantType, callPrice, decimalsInCallPrice, entitlement, decimalsInEntitlement, noWarrantsPerEntitlement, filler63, underlyingSecurity := ⟨underlyingSecurity_, fits_underlyingSecurity⟩ }, bytes)
  else none

theorem encode_length_pos (message : SecurityDefinitionMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SecurityDefinitionMessage) : (encode message).length ≤ 524820 := by
  have bound_underlyingSecurity := message.underlyingSecurity.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length, VcmFlag.encode_length, ShortSellFlag.encode_length, CasFlag.encode_length, CcassFlag.encode_length, DummySecurityFlag.encode_length, StampDutyFlag.encode_length, PosFlag.encode_length, EfnFlag.encode_length, InvestorType.encode_length, CallPutFlag.encode_length, Style.encode_length, WarrantType.encode_length, encodeMany_length_const UnderlyingSecurity.encode 8 UnderlyingSecurity.encode_length]
  omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SecurityDefinitionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, VcmFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ShortSellFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CasFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CcassFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DummySecurityFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StampDutyFlag.decode_encode, some_bind]
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
  rw [List.append_assoc, PosFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, EfnFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, InvestorType.decode_encode, some_bind]
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
  rw [List.append_assoc, CallPutFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Style.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, WarrantType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 UnderlyingSecurity.encode UnderlyingSecurity.decode UnderlyingSecurity.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.underlyingSecurity.length_lt]
  rfl

end SecurityDefinitionMessage

/-- Liquidity Provider: 2 bytes -/
structure LiquidityProvider where
  lpBrokerNumber : BitVec 16
  deriving DecidableEq, Repr

namespace LiquidityProvider

def encode (message : LiquidityProvider) : List UInt8 :=
  encodeUIntLE 2 message.lpBrokerNumber

def decode (bytes : List UInt8) : Option (LiquidityProvider × List UInt8) := do
  let (lpBrokerNumber, bytes) ← decodeUIntLE 2 bytes
  pure ({ lpBrokerNumber }, bytes)

@[simp] theorem encode_length (message : LiquidityProvider) : (encode message).length = 2 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : LiquidityProvider) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LiquidityProvider) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end LiquidityProvider

/-- Liquidity Provider Message -/
structure LiquidityProviderMessage where
  securityCode : BitVec 32
  liquidityProvider : Bounded 2 LiquidityProvider
  deriving DecidableEq, Repr

namespace LiquidityProviderMessage

def encode (message : LiquidityProviderMessage) : List UInt8 :=
  encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.liquidityProvider.val.length)
    ++ (encodeMany LiquidityProvider.encode message.liquidityProvider.val))

def decode (bytes : List UInt8) : Option (LiquidityProviderMessage × List UInt8) := do
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (noLiquidityProviders, bytes) ← decodeUIntLE 2 bytes
  let (liquidityProvider_, bytes) ← decodeMany LiquidityProvider.decode noLiquidityProviders.toNat bytes
  if fits_liquidityProvider : liquidityProvider_.length < 256 ^ 2 then
    pure ({ securityCode, liquidityProvider := ⟨liquidityProvider_, fits_liquidityProvider⟩ }, bytes)
  else none

theorem encode_length_pos (message : LiquidityProviderMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : LiquidityProviderMessage) : (encode message).length ≤ 131076 := by
  have bound_liquidityProvider := message.liquidityProvider.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeMany_length_const LiquidityProvider.encode 2 LiquidityProvider.encode_length]
  omega

@[simp] theorem decode_encode (message : LiquidityProviderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 LiquidityProvider.encode LiquidityProvider.decode LiquidityProvider.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.liquidityProvider.length_lt]
  rfl

end LiquidityProviderMessage

/-- Currency Rate Message: 12 bytes -/
structure CurrencyRateMessage where
  currencyCode : Alpha 3
  filler1 : Alpha 1
  currencyFactor : BitVec 16
  filler2 : Alpha 2
  currencyRate : BitVec 32
  deriving DecidableEq, Repr

namespace CurrencyRateMessage

def encode (message : CurrencyRateMessage) : List UInt8 :=
  Alpha.encode message.currencyCode
    ++ (Alpha.encode message.filler1
    ++ (encodeUIntLE 2 message.currencyFactor
    ++ (Alpha.encode message.filler2
    ++ (encodeUIntLE 4 message.currencyRate))))

def decode (bytes : List UInt8) : Option (CurrencyRateMessage × List UInt8) := do
  let (currencyCode, bytes) ← Alpha.decode 3 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (currencyFactor, bytes) ← decodeUIntLE 2 bytes
  let (filler2, bytes) ← Alpha.decode 2 bytes
  let (currencyRate, bytes) ← decodeUIntLE 4 bytes
  pure ({ currencyCode, filler1, currencyFactor, filler2, currencyRate }, bytes)

@[simp] theorem encode_length (message : CurrencyRateMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : CurrencyRateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CurrencyRateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end CurrencyRateMessage

/-- Reference Price Message: 16 bytes -/
structure ReferencePriceMessage where
  securityCode : BitVec 32
  referencePrice : BitVec 32
  lowerPrice : BitVec 32
  upperPrice : BitVec 32
  deriving DecidableEq, Repr

namespace ReferencePriceMessage

def encode (message : ReferencePriceMessage) : List UInt8 :=
  encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 4 message.referencePrice
    ++ (encodeUIntLE 4 message.lowerPrice
    ++ (encodeUIntLE 4 message.upperPrice)))

def decode (bytes : List UInt8) : Option (ReferencePriceMessage × List UInt8) := do
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (referencePrice, bytes) ← decodeUIntLE 4 bytes
  let (lowerPrice, bytes) ← decodeUIntLE 4 bytes
  let (upperPrice, bytes) ← decodeUIntLE 4 bytes
  pure ({ securityCode, referencePrice, lowerPrice, upperPrice }, bytes)

@[simp] theorem encode_length (message : ReferencePriceMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : ReferencePriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReferencePriceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ReferencePriceMessage

/-- Refresh Complete Message: 4 bytes -/
structure RefreshCompleteMessage where
  lastSeqNum : BitVec 32
  deriving DecidableEq, Repr

namespace RefreshCompleteMessage

def encode (message : RefreshCompleteMessage) : List UInt8 :=
  encodeUIntLE 4 message.lastSeqNum

def decode (bytes : List UInt8) : Option (RefreshCompleteMessage × List UInt8) := do
  let (lastSeqNum, bytes) ← decodeUIntLE 4 bytes
  pure ({ lastSeqNum }, bytes)

@[simp] theorem encode_length (message : RefreshCompleteMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : RefreshCompleteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RefreshCompleteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end RefreshCompleteMessage

/-- Logon Message: 12 bytes -/
structure LogonMessage where
  username : Alpha 12
  deriving DecidableEq, Repr

namespace LogonMessage

def encode (message : LogonMessage) : List UInt8 :=
  Alpha.encode message.username

def decode (bytes : List UInt8) : Option (LogonMessage × List UInt8) := do
  let (username, bytes) ← Alpha.decode 12 bytes
  pure ({ username }, bytes)

@[simp] theorem encode_length (message : LogonMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : LogonMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogonMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end LogonMessage

/-- Logon Response Message: 4 bytes -/
structure LogonResponseMessage where
  sessionStatus : BitVec 8
  filler3 : Alpha 3
  deriving DecidableEq, Repr

namespace LogonResponseMessage

def encode (message : LogonResponseMessage) : List UInt8 :=
  encodeUInt 1 message.sessionStatus
    ++ (Alpha.encode message.filler3)

def decode (bytes : List UInt8) : Option (LogonResponseMessage × List UInt8) := do
  let (sessionStatus, bytes) ← decodeUInt 1 bytes
  let (filler3, bytes) ← Alpha.decode 3 bytes
  pure ({ sessionStatus, filler3 }, bytes)

@[simp] theorem encode_length (message : LogonResponseMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : LogonResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogonResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LogonResponseMessage

/-- Retransmission Request Message: 12 bytes -/
structure RetransmissionRequestMessage where
  channelId : BitVec 16
  filler2 : Alpha 2
  beginSeqNum : BitVec 32
  endSeqNum : BitVec 32
  deriving DecidableEq, Repr

namespace RetransmissionRequestMessage

def encode (message : RetransmissionRequestMessage) : List UInt8 :=
  encodeUIntLE 2 message.channelId
    ++ (Alpha.encode message.filler2
    ++ (encodeUIntLE 4 message.beginSeqNum
    ++ (encodeUIntLE 4 message.endSeqNum)))

def decode (bytes : List UInt8) : Option (RetransmissionRequestMessage × List UInt8) := do
  let (channelId, bytes) ← decodeUIntLE 2 bytes
  let (filler2, bytes) ← Alpha.decode 2 bytes
  let (beginSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (endSeqNum, bytes) ← decodeUIntLE 4 bytes
  pure ({ channelId, filler2, beginSeqNum, endSeqNum }, bytes)

@[simp] theorem encode_length (message : RetransmissionRequestMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : RetransmissionRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RetransmissionRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end RetransmissionRequestMessage

/-- Retransmission Response Message: 12 bytes -/
structure RetransmissionResponseMessage where
  channelId : BitVec 16
  retransStatus : BitVec 8
  filler1 : Alpha 1
  beginSeqNum : BitVec 32
  endSeqNum : BitVec 32
  deriving DecidableEq, Repr

namespace RetransmissionResponseMessage

def encode (message : RetransmissionResponseMessage) : List UInt8 :=
  encodeUIntLE 2 message.channelId
    ++ (encodeUInt 1 message.retransStatus
    ++ (Alpha.encode message.filler1
    ++ (encodeUIntLE 4 message.beginSeqNum
    ++ (encodeUIntLE 4 message.endSeqNum))))

def decode (bytes : List UInt8) : Option (RetransmissionResponseMessage × List UInt8) := do
  let (channelId, bytes) ← decodeUIntLE 2 bytes
  let (retransStatus, bytes) ← decodeUInt 1 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (beginSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (endSeqNum, bytes) ← decodeUIntLE 4 bytes
  pure ({ channelId, retransStatus, filler1, beginSeqNum, endSeqNum }, bytes)

@[simp] theorem encode_length (message : RetransmissionResponseMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : RetransmissionResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RetransmissionResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end RetransmissionResponseMessage

/-- Trading Session Status Message: 28 bytes -/
structure TradingSessionStatusMessage where
  marketCode : Alpha 4
  filler1 : Alpha 1
  tradingSessionSubId : BitVec 8
  tradingSesStatus : BitVec 8
  tradingSesControlFlag : TradingSesControlFlag
  filler4 : Alpha 4
  startDateTime : BitVec 64
  endDateTime : BitVec 64
  deriving DecidableEq, Repr

namespace TradingSessionStatusMessage

def encode (message : TradingSessionStatusMessage) : List UInt8 :=
  Alpha.encode message.marketCode
    ++ (Alpha.encode message.filler1
    ++ (encodeUInt 1 message.tradingSessionSubId
    ++ (encodeUInt 1 message.tradingSesStatus
    ++ (TradingSesControlFlag.encode message.tradingSesControlFlag
    ++ (Alpha.encode message.filler4
    ++ (encodeUIntLE 8 message.startDateTime
    ++ (encodeUIntLE 8 message.endDateTime)))))))

def decode (bytes : List UInt8) : Option (TradingSessionStatusMessage × List UInt8) := do
  let (marketCode, bytes) ← Alpha.decode 4 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (tradingSessionSubId, bytes) ← decodeUInt 1 bytes
  let (tradingSesStatus, bytes) ← decodeUInt 1 bytes
  let (tradingSesControlFlag, bytes) ← TradingSesControlFlag.decode bytes
  let (filler4, bytes) ← Alpha.decode 4 bytes
  let (startDateTime, bytes) ← decodeUIntLE 8 bytes
  let (endDateTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ marketCode, filler1, tradingSessionSubId, tradingSesStatus, tradingSesControlFlag, filler4, startDateTime, endDateTime }, bytes)

@[simp] theorem encode_length (message : TradingSessionStatusMessage) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, TradingSesControlFlag.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : TradingSessionStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradingSessionStatusMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, TradingSesControlFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradingSessionStatusMessage

/-- Security Status Message: 8 bytes -/
structure SecurityStatusMessage where
  securityCode : BitVec 32
  suspensionIndicator : BitVec 8
  filler3 : Alpha 3
  deriving DecidableEq, Repr

namespace SecurityStatusMessage

def encode (message : SecurityStatusMessage) : List UInt8 :=
  encodeUIntLE 4 message.securityCode
    ++ (encodeUInt 1 message.suspensionIndicator
    ++ (Alpha.encode message.filler3))

def decode (bytes : List UInt8) : Option (SecurityStatusMessage × List UInt8) := do
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (suspensionIndicator, bytes) ← decodeUInt 1 bytes
  let (filler3, bytes) ← Alpha.decode 3 bytes
  pure ({ securityCode, suspensionIndicator, filler3 }, bytes)

@[simp] theorem encode_length (message : SecurityStatusMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : SecurityStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SecurityStatusMessage

/-- Trade Message: 28 bytes -/
structure TradeMessage where
  securityCode : BitVec 32
  tradeId : BitVec 32
  price : BitVec 32
  quantity : BitVec 32
  trdType : BitVec 16
  filler2 : Alpha 2
  tradeTime : BitVec 64
  deriving DecidableEq, Repr

namespace TradeMessage

def encode (message : TradeMessage) : List UInt8 :=
  encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 4 message.tradeId
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 2 message.trdType
    ++ (Alpha.encode message.filler2
    ++ (encodeUIntLE 8 message.tradeTime))))))

def decode (bytes : List UInt8) : Option (TradeMessage × List UInt8) := do
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (trdType, bytes) ← decodeUIntLE 2 bytes
  let (filler2, bytes) ← Alpha.decode 2 bytes
  let (tradeTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ securityCode, tradeId, price, quantity, trdType, filler2, tradeTime }, bytes)

@[simp] theorem encode_length (message : TradeMessage) : (encode message).length = 28 := by
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

end TradeMessage

/-- Trade Cancel Message: 8 bytes -/
structure TradeCancelMessage where
  securityCode : BitVec 32
  tradeId : BitVec 32
  deriving DecidableEq, Repr

namespace TradeCancelMessage

def encode (message : TradeCancelMessage) : List UInt8 :=
  encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 4 message.tradeId)

def decode (bytes : List UInt8) : Option (TradeCancelMessage × List UInt8) := do
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  pure ({ securityCode, tradeId }, bytes)

@[simp] theorem encode_length (message : TradeCancelMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : TradeCancelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCancelMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeCancelMessage

/-- Vcm Trigger Message: 32 bytes -/
structure VcmTriggerMessage where
  securityCode : BitVec 32
  coolingOffStartTime : BitVec 64
  coolingOffEndTime : BitVec 64
  vcmReferencePrice : BitVec 32
  vcmLowerPrice : BitVec 32
  vcmUpperPrice : BitVec 32
  deriving DecidableEq, Repr

namespace VcmTriggerMessage

def encode (message : VcmTriggerMessage) : List UInt8 :=
  encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.coolingOffStartTime
    ++ (encodeUIntLE 8 message.coolingOffEndTime
    ++ (encodeUIntLE 4 message.vcmReferencePrice
    ++ (encodeUIntLE 4 message.vcmLowerPrice
    ++ (encodeUIntLE 4 message.vcmUpperPrice)))))

def decode (bytes : List UInt8) : Option (VcmTriggerMessage × List UInt8) := do
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (coolingOffStartTime, bytes) ← decodeUIntLE 8 bytes
  let (coolingOffEndTime, bytes) ← decodeUIntLE 8 bytes
  let (vcmReferencePrice, bytes) ← decodeUIntLE 4 bytes
  let (vcmLowerPrice, bytes) ← decodeUIntLE 4 bytes
  let (vcmUpperPrice, bytes) ← decodeUIntLE 4 bytes
  pure ({ securityCode, coolingOffStartTime, coolingOffEndTime, vcmReferencePrice, vcmLowerPrice, vcmUpperPrice }, bytes)

@[simp] theorem encode_length (message : VcmTriggerMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : VcmTriggerMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : VcmTriggerMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end VcmTriggerMessage

/-- Any Payload, selected by Msg Type -/
inductive Payload where
  | addOrderMessage (message : AddOrderMessage) -- 30
  | sequenceResetMessage (message : SequenceResetMessage) -- 100
  | disasterRecoverySignalMessage (message : DisasterRecoverySignalMessage) -- 105
  | deleteOrderMessage (message : DeleteOrderMessage) -- 32
  | indicativeEquilibriumPriceMessage (message : IndicativeEquilibriumPriceMessage) -- 41
  | modifyOrderMessage (message : ModifyOrderMessage) -- 31
  | orderImbalanceMessage (message : OrderImbalanceMessage) -- 56
  | marketDefinitionMessage (message : MarketDefinitionMessage) -- 10
  | securityDefinitionMessage (message : SecurityDefinitionMessage) -- 11
  | liquidityProviderMessage (message : LiquidityProviderMessage) -- 13
  | currencyRateMessage (message : CurrencyRateMessage) -- 14
  | referencePriceMessage (message : ReferencePriceMessage) -- 43
  | refreshCompleteMessage (message : RefreshCompleteMessage) -- 203
  | logonMessage (message : LogonMessage) -- 101
  | logonResponseMessage (message : LogonResponseMessage) -- 102
  | retransmissionRequestMessage (message : RetransmissionRequestMessage) -- 201
  | retransmissionResponseMessage (message : RetransmissionResponseMessage) -- 202
  | tradingSessionStatusMessage (message : TradingSessionStatusMessage) -- 20
  | securityStatusMessage (message : SecurityStatusMessage) -- 21
  | tradeMessage (message : TradeMessage) -- 50
  | tradeCancelMessage (message : TradeCancelMessage) -- 51
  | vcmTriggerMessage (message : VcmTriggerMessage) -- 23
  deriving DecidableEq, Repr

namespace Payload

/-- The Msg Type each message is sent under -/
def tag : Payload → BitVec 16
  | .addOrderMessage _ => 30
  | .sequenceResetMessage _ => 100
  | .disasterRecoverySignalMessage _ => 105
  | .deleteOrderMessage _ => 32
  | .indicativeEquilibriumPriceMessage _ => 41
  | .modifyOrderMessage _ => 31
  | .orderImbalanceMessage _ => 56
  | .marketDefinitionMessage _ => 10
  | .securityDefinitionMessage _ => 11
  | .liquidityProviderMessage _ => 13
  | .currencyRateMessage _ => 14
  | .referencePriceMessage _ => 43
  | .refreshCompleteMessage _ => 203
  | .logonMessage _ => 101
  | .logonResponseMessage _ => 102
  | .retransmissionRequestMessage _ => 201
  | .retransmissionResponseMessage _ => 202
  | .tradingSessionStatusMessage _ => 20
  | .securityStatusMessage _ => 21
  | .tradeMessage _ => 50
  | .tradeCancelMessage _ => 51
  | .vcmTriggerMessage _ => 23

def encode : Payload → List UInt8
  | .addOrderMessage message => AddOrderMessage.encode message
  | .sequenceResetMessage message => SequenceResetMessage.encode message
  | .disasterRecoverySignalMessage message => DisasterRecoverySignalMessage.encode message
  | .deleteOrderMessage message => DeleteOrderMessage.encode message
  | .indicativeEquilibriumPriceMessage message => IndicativeEquilibriumPriceMessage.encode message
  | .modifyOrderMessage message => ModifyOrderMessage.encode message
  | .orderImbalanceMessage message => OrderImbalanceMessage.encode message
  | .marketDefinitionMessage message => MarketDefinitionMessage.encode message
  | .securityDefinitionMessage message => SecurityDefinitionMessage.encode message
  | .liquidityProviderMessage message => LiquidityProviderMessage.encode message
  | .currencyRateMessage message => CurrencyRateMessage.encode message
  | .referencePriceMessage message => ReferencePriceMessage.encode message
  | .refreshCompleteMessage message => RefreshCompleteMessage.encode message
  | .logonMessage message => LogonMessage.encode message
  | .logonResponseMessage message => LogonResponseMessage.encode message
  | .retransmissionRequestMessage message => RetransmissionRequestMessage.encode message
  | .retransmissionResponseMessage message => RetransmissionResponseMessage.encode message
  | .tradingSessionStatusMessage message => TradingSessionStatusMessage.encode message
  | .securityStatusMessage message => SecurityStatusMessage.encode message
  | .tradeMessage message => TradeMessage.encode message
  | .tradeCancelMessage message => TradeCancelMessage.encode message
  | .vcmTriggerMessage message => VcmTriggerMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 524820 := by
  cases message with
  | addOrderMessage inner =>
    simp only [encode, AddOrderMessage.encode_length]
    omega
  | sequenceResetMessage inner =>
    simp only [encode, SequenceResetMessage.encode_length]
    omega
  | disasterRecoverySignalMessage inner =>
    simp only [encode, DisasterRecoverySignalMessage.encode_length]
    omega
  | deleteOrderMessage inner =>
    simp only [encode, DeleteOrderMessage.encode_length]
    omega
  | indicativeEquilibriumPriceMessage inner =>
    simp only [encode, IndicativeEquilibriumPriceMessage.encode_length]
    omega
  | modifyOrderMessage inner =>
    simp only [encode, ModifyOrderMessage.encode_length]
    omega
  | orderImbalanceMessage inner =>
    simp only [encode, OrderImbalanceMessage.encode_length]
    omega
  | marketDefinitionMessage inner =>
    simp only [encode, MarketDefinitionMessage.encode_length]
    omega
  | securityDefinitionMessage inner =>
    have bound_inner := SecurityDefinitionMessage.encode_length_le inner
    simp only [encode]
    omega
  | liquidityProviderMessage inner =>
    have bound_inner := LiquidityProviderMessage.encode_length_le inner
    simp only [encode]
    omega
  | currencyRateMessage inner =>
    simp only [encode, CurrencyRateMessage.encode_length]
    omega
  | referencePriceMessage inner =>
    simp only [encode, ReferencePriceMessage.encode_length]
    omega
  | refreshCompleteMessage inner =>
    simp only [encode, RefreshCompleteMessage.encode_length]
    omega
  | logonMessage inner =>
    simp only [encode, LogonMessage.encode_length]
    omega
  | logonResponseMessage inner =>
    simp only [encode, LogonResponseMessage.encode_length]
    omega
  | retransmissionRequestMessage inner =>
    simp only [encode, RetransmissionRequestMessage.encode_length]
    omega
  | retransmissionResponseMessage inner =>
    simp only [encode, RetransmissionResponseMessage.encode_length]
    omega
  | tradingSessionStatusMessage inner =>
    simp only [encode, TradingSessionStatusMessage.encode_length]
    omega
  | securityStatusMessage inner =>
    simp only [encode, SecurityStatusMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [encode, TradeMessage.encode_length]
    omega
  | tradeCancelMessage inner =>
    simp only [encode, TradeCancelMessage.encode_length]
    omega
  | vcmTriggerMessage inner =>
    simp only [encode, VcmTriggerMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 30 then (AddOrderMessage.decode bytes).map fun (message, rest) => (.addOrderMessage message, rest)
  else if tag = 100 then (SequenceResetMessage.decode bytes).map fun (message, rest) => (.sequenceResetMessage message, rest)
  else if tag = 105 then (DisasterRecoverySignalMessage.decode bytes).map fun (message, rest) => (.disasterRecoverySignalMessage message, rest)
  else if tag = 32 then (DeleteOrderMessage.decode bytes).map fun (message, rest) => (.deleteOrderMessage message, rest)
  else if tag = 41 then (IndicativeEquilibriumPriceMessage.decode bytes).map fun (message, rest) => (.indicativeEquilibriumPriceMessage message, rest)
  else if tag = 31 then (ModifyOrderMessage.decode bytes).map fun (message, rest) => (.modifyOrderMessage message, rest)
  else if tag = 56 then (OrderImbalanceMessage.decode bytes).map fun (message, rest) => (.orderImbalanceMessage message, rest)
  else if tag = 10 then (MarketDefinitionMessage.decode bytes).map fun (message, rest) => (.marketDefinitionMessage message, rest)
  else if tag = 11 then (SecurityDefinitionMessage.decode bytes).map fun (message, rest) => (.securityDefinitionMessage message, rest)
  else if tag = 13 then (LiquidityProviderMessage.decode bytes).map fun (message, rest) => (.liquidityProviderMessage message, rest)
  else if tag = 14 then (CurrencyRateMessage.decode bytes).map fun (message, rest) => (.currencyRateMessage message, rest)
  else if tag = 43 then (ReferencePriceMessage.decode bytes).map fun (message, rest) => (.referencePriceMessage message, rest)
  else if tag = 203 then (RefreshCompleteMessage.decode bytes).map fun (message, rest) => (.refreshCompleteMessage message, rest)
  else if tag = 101 then (LogonMessage.decode bytes).map fun (message, rest) => (.logonMessage message, rest)
  else if tag = 102 then (LogonResponseMessage.decode bytes).map fun (message, rest) => (.logonResponseMessage message, rest)
  else if tag = 201 then (RetransmissionRequestMessage.decode bytes).map fun (message, rest) => (.retransmissionRequestMessage message, rest)
  else if tag = 202 then (RetransmissionResponseMessage.decode bytes).map fun (message, rest) => (.retransmissionResponseMessage message, rest)
  else if tag = 20 then (TradingSessionStatusMessage.decode bytes).map fun (message, rest) => (.tradingSessionStatusMessage message, rest)
  else if tag = 21 then (SecurityStatusMessage.decode bytes).map fun (message, rest) => (.securityStatusMessage message, rest)
  else if tag = 50 then (TradeMessage.decode bytes).map fun (message, rest) => (.tradeMessage message, rest)
  else if tag = 51 then (TradeCancelMessage.decode bytes).map fun (message, rest) => (.tradeCancelMessage message, rest)
  else if tag = 23 then (VcmTriggerMessage.decode bytes).map fun (message, rest) => (.vcmTriggerMessage message, rest)
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
  encodeUIntLE 2 (Payload.tag message.payload)
    ++ (Payload.encode message.payload)

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (msgType, bytes) ← decodeUIntLE 2 bytes
  let (payload, bytes) ← Payload.decode msgType bytes
  pure ({ payload }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Size rule: Msg Size counts the bytes after it plus 2, so it is written from the body; the body has no bound the prefix must fit, so it is read by its content and the prefix is not checked -/
def encode (message : Message) : List UInt8 :=
  encodeUIntLE 2 (BitVec.ofNat (8 * 2) ((encodeBody message).length + 2)) ++ encodeBody message

def decode (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (_, bytes) ← decodeUIntLE 2 bytes
  decodeBody bytes

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  exact decodeBody_encodeBody message rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]
  omega

end Message

/-- Packet -/
structure Packet where
  pktSize : BitVec 16
  filler : Alpha 1
  seqNum : BitVec 32
  sendTime : BitVec 64
  message : Bounded 1 Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUIntLE 2 message.pktSize
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.message.val.length)
    ++ (Alpha.encode message.filler
    ++ (encodeUIntLE 4 message.seqNum
    ++ (encodeUIntLE 8 message.sendTime
    ++ (encodeMany Message.encode message.message.val)))))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (pktSize, bytes) ← decodeUIntLE 2 bytes
  let (msgCount, bytes) ← decodeUInt 1 bytes
  let (filler, bytes) ← Alpha.decode 1 bytes
  let (seqNum, bytes) ← decodeUIntLE 4 bytes
  let (sendTime, bytes) ← decodeUIntLE 8 bytes
  let (message_, bytes) ← decodeMany Message.decode msgCount.toNat bytes
  if fits_message : message_.length < 256 ^ 1 then
    pure ({ pktSize, filler, seqNum, sendTime, message := ⟨message_, fits_message⟩ }, bytes)
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt]
  rfl

end Packet

end Omi.HkexHkexsecuritiesFulltickretransOmdV144
