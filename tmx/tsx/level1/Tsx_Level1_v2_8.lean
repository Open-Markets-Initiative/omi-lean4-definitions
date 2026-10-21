import Wire

/-!
# TMX Group Level 1 v2.8

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.TmxTsxLevel1QrtmdV28

/-- Retransmission Identifier: one byte code -/
def RetransmissionIdentifier.codes : List UInt8 :=
  [0x30]

inductive RetransmissionIdentifier where
  | normalTransmission -- Normal Transmission
  | unlisted (byte : { byte : UInt8 // byte ∉ RetransmissionIdentifier.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RetransmissionIdentifier

def toByte : RetransmissionIdentifier → UInt8
  | .normalTransmission => 0x30
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : RetransmissionIdentifier :=
  .normalTransmission

def ofByte (byte : UInt8) : RetransmissionIdentifier :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RetransmissionIdentifier) : ofByte value.toByte = value := by
  cases value with
  | normalTransmission => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RetransmissionIdentifier) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RetransmissionIdentifier × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RetransmissionIdentifier) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : RetransmissionIdentifier) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : RetransmissionIdentifier) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RetransmissionIdentifier

/-- Continuation Identifier: one byte code -/
def ContinuationIdentifier.codes : List UInt8 :=
  [0x30]

inductive ContinuationIdentifier where
  | standAloneMessage -- Stand Alone Message
  | unlisted (byte : { byte : UInt8 // byte ∉ ContinuationIdentifier.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ContinuationIdentifier

def toByte : ContinuationIdentifier → UInt8
  | .standAloneMessage => 0x30
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : ContinuationIdentifier :=
  .standAloneMessage

def ofByte (byte : UInt8) : ContinuationIdentifier :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ContinuationIdentifier) : ofByte value.toByte = value := by
  cases value with
  | standAloneMessage => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ContinuationIdentifier) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ContinuationIdentifier × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ContinuationIdentifier) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ContinuationIdentifier) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ContinuationIdentifier) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ContinuationIdentifier

/-- Cross Type: one byte code -/
def CrossType.codes : List UInt8 :=
  [0x49, 0x42, 0x43, 0x44, 0x52, 0x53, 0x56, 0x20]

inductive CrossType where
  | internal -- Internal
  | basis -- Basis
  | contingent -- Contingent
  | derivativeRelated -- Derivative Related
  | regular -- Regular
  | specialTradingSession -- Special Trading Session
  | volumeWeightedAveragePrice -- Volume Weighted Average Price
  | default -- Default
  | unlisted (byte : { byte : UInt8 // byte ∉ CrossType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CrossType

def toByte : CrossType → UInt8
  | .internal => 0x49
  | .basis => 0x42
  | .contingent => 0x43
  | .derivativeRelated => 0x44
  | .regular => 0x52
  | .specialTradingSession => 0x53
  | .volumeWeightedAveragePrice => 0x56
  | .default => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CrossType :=
  if byte = 0x49 then .internal
  else if byte = 0x42 then .basis
  else if byte = 0x43 then .contingent
  else if byte = 0x44 then .derivativeRelated
  else if byte = 0x52 then .regular
  else if byte = 0x53 then .specialTradingSession
  else if byte = 0x56 then .volumeWeightedAveragePrice
  else .default

def ofByte (byte : UInt8) : CrossType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CrossType) : ofByte value.toByte = value := by
  cases value with
  | internal => decide
  | basis => decide
  | contingent => decide
  | derivativeRelated => decide
  | regular => decide
  | specialTradingSession => decide
  | volumeWeightedAveragePrice => decide
  | default => decide
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

/-- Moc: one byte code -/
def Moc.codes : List UInt8 :=
  [0x59, 0x4E]

inductive Moc where
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ Moc.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Moc

def toByte : Moc → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Moc :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : Moc :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Moc) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Moc) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Moc × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Moc) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Moc) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Moc) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Moc

/-- Bypass: one byte code -/
def Bypass.codes : List UInt8 :=
  [0x59, 0x4E]

inductive Bypass where
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ Bypass.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Bypass

def toByte : Bypass → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Bypass :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : Bypass :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Bypass) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Bypass) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Bypass × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Bypass) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Bypass) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Bypass) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Bypass

/-- Opening Trade: one byte code -/
def OpeningTrade.codes : List UInt8 :=
  [0x59, 0x4E]

inductive OpeningTrade where
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ OpeningTrade.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OpeningTrade

def toByte : OpeningTrade → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OpeningTrade :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : OpeningTrade :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OpeningTrade) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
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

/-- Settlement Terms: one byte code -/
def SettlementTerms.codes : List UInt8 :=
  [0x20, 0x43, 0x4E, 0x4D, 0x54, 0x44]

inductive SettlementTerms where
  | default -- Default
  | cash -- Cash
  | nonNet -- Non Net
  | derivativesRelatedContingentEquityTrade -- Derivatives Related Contingent Equity Trade
  | cashToday -- Cash Today
  | settlementDate -- Settlement Date
  | unlisted (byte : { byte : UInt8 // byte ∉ SettlementTerms.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SettlementTerms

def toByte : SettlementTerms → UInt8
  | .default => 0x20
  | .cash => 0x43
  | .nonNet => 0x4E
  | .derivativesRelatedContingentEquityTrade => 0x4D
  | .cashToday => 0x54
  | .settlementDate => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SettlementTerms :=
  if byte = 0x20 then .default
  else if byte = 0x43 then .cash
  else if byte = 0x4E then .nonNet
  else if byte = 0x4D then .derivativesRelatedContingentEquityTrade
  else if byte = 0x54 then .cashToday
  else .settlementDate

def ofByte (byte : UInt8) : SettlementTerms :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SettlementTerms) : ofByte value.toByte = value := by
  cases value with
  | default => decide
  | cash => decide
  | nonNet => decide
  | derivativesRelatedContingentEquityTrade => decide
  | cashToday => decide
  | settlementDate => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SettlementTerms) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SettlementTerms × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SettlementTerms) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SettlementTerms) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SettlementTerms) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SettlementTerms

/-- Listing Market: one byte code -/
def ListingMarket.codes : List UInt8 :=
  [0x54, 0x56, 0x4E, 0x51, 0x53, 0x4D, 0x58]

inductive ListingMarket where
  | tsx -- Tsx
  | tsxv -- Tsxv
  | navex -- Navex
  | nasdaq -- Nasdaq
  | nyse -- Nyse
  | nyseMkt -- Nyse Mkt
  | noMarket -- No Market
  | unlisted (byte : { byte : UInt8 // byte ∉ ListingMarket.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ListingMarket

def toByte : ListingMarket → UInt8
  | .tsx => 0x54
  | .tsxv => 0x56
  | .navex => 0x4E
  | .nasdaq => 0x51
  | .nyse => 0x53
  | .nyseMkt => 0x4D
  | .noMarket => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ListingMarket :=
  if byte = 0x54 then .tsx
  else if byte = 0x56 then .tsxv
  else if byte = 0x4E then .navex
  else if byte = 0x51 then .nasdaq
  else if byte = 0x53 then .nyse
  else if byte = 0x4D then .nyseMkt
  else .noMarket

def ofByte (byte : UInt8) : ListingMarket :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ListingMarket) : ofByte value.toByte = value := by
  cases value with
  | tsx => decide
  | tsxv => decide
  | navex => decide
  | nasdaq => decide
  | nyse => decide
  | nyseMkt => decide
  | noMarket => decide
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

/-- Product Type: one byte code -/
def ProductType.codes : List UInt8 :=
  [0x42, 0x45, 0x4D, 0x46, 0x55, 0x4F]

inductive ProductType where
  | debenture -- Debenture
  | equity -- Equity
  | mutualFund -- Mutual Fund
  | etf -- Etf
  | usEquity -- Us Equity
  | bond -- Bond
  | unlisted (byte : { byte : UInt8 // byte ∉ ProductType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ProductType

def toByte : ProductType → UInt8
  | .debenture => 0x42
  | .equity => 0x45
  | .mutualFund => 0x4D
  | .etf => 0x46
  | .usEquity => 0x55
  | .bond => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ProductType :=
  if byte = 0x42 then .debenture
  else if byte = 0x45 then .equity
  else if byte = 0x4D then .mutualFund
  else if byte = 0x46 then .etf
  else if byte = 0x55 then .usEquity
  else .bond

def ofByte (byte : UInt8) : ProductType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ProductType) : ofByte value.toByte = value := by
  cases value with
  | debenture => decide
  | equity => decide
  | mutualFund => decide
  | etf => decide
  | usEquity => decide
  | bond => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ProductType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ProductType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ProductType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ProductType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ProductType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ProductType

/-- Is Mid Only: one byte code -/
def IsMidOnly.codes : List UInt8 :=
  [0x59, 0x4E]

inductive IsMidOnly where
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ IsMidOnly.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace IsMidOnly

def toByte : IsMidOnly → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : IsMidOnly :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : IsMidOnly :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : IsMidOnly) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : IsMidOnly) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (IsMidOnly × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : IsMidOnly) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : IsMidOnly) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : IsMidOnly) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end IsMidOnly

/-- Is Dark: one byte code -/
def IsDark.codes : List UInt8 :=
  [0x59, 0x4E]

inductive IsDark where
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ IsDark.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace IsDark

def toByte : IsDark → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : IsDark :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : IsDark :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : IsDark) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : IsDark) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (IsDark × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : IsDark) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : IsDark) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : IsDark) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end IsDark

/-- Is Conditional: one byte code -/
def IsConditional.codes : List UInt8 :=
  [0x59, 0x4E]

inductive IsConditional where
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ IsConditional.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace IsConditional

def toByte : IsConditional → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : IsConditional :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : IsConditional :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : IsConditional) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : IsConditional) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (IsConditional × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : IsConditional) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : IsConditional) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : IsConditional) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end IsConditional

/-- Moc Eligible: one byte code -/
def MocEligible.codes : List UInt8 :=
  [0x59, 0x4E]

inductive MocEligible where
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ MocEligible.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MocEligible

def toByte : MocEligible → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MocEligible :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : MocEligible :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MocEligible) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
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

/-- Test Symbol: one byte code -/
def TestSymbol.codes : List UInt8 :=
  [0x59, 0x4E]

inductive TestSymbol where
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ TestSymbol.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TestSymbol

def toByte : TestSymbol → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TestSymbol :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : TestSymbol :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TestSymbol) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TestSymbol) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TestSymbol × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TestSymbol) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TestSymbol) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TestSymbol) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TestSymbol

/-- Imbalance Side: one byte code -/
def ImbalanceSide.codes : List UInt8 :=
  [0x42, 0x53, 0x20]

inductive ImbalanceSide where
  | buy -- Buy
  | sell -- Sell
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ ImbalanceSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ImbalanceSide

def toByte : ImbalanceSide → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ImbalanceSide :=
  if byte = 0x42 then .buy
  else if byte = 0x53 then .sell
  else .notApplicable

def ofByte (byte : UInt8) : ImbalanceSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ImbalanceSide) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ImbalanceSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ImbalanceSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ImbalanceSide) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ImbalanceSide) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ImbalanceSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ImbalanceSide

/-- Market Order Imbalance Side: one byte code -/
def MarketOrderImbalanceSide.codes : List UInt8 :=
  [0x42, 0x53, 0x20]

inductive MarketOrderImbalanceSide where
  | buy -- Buy
  | sell -- Sell
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketOrderImbalanceSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketOrderImbalanceSide

def toByte : MarketOrderImbalanceSide → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketOrderImbalanceSide :=
  if byte = 0x42 then .buy
  else if byte = 0x53 then .sell
  else .notApplicable

def ofByte (byte : UInt8) : MarketOrderImbalanceSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketOrderImbalanceSide) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarketOrderImbalanceSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketOrderImbalanceSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketOrderImbalanceSide) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : MarketOrderImbalanceSide) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : MarketOrderImbalanceSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarketOrderImbalanceSide

/-- Bulletin Indicator: one byte code -/
def BulletinIndicator.codes : List UInt8 :=
  [0x59, 0x4E]

inductive BulletinIndicator where
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ BulletinIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BulletinIndicator

def toByte : BulletinIndicator → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BulletinIndicator :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : BulletinIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BulletinIndicator) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BulletinIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BulletinIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BulletinIndicator) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : BulletinIndicator) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : BulletinIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BulletinIndicator

/-- Price Marker: one byte code -/
def PriceMarker.codes : List UInt8 :=
  [0x43, 0x4F]

inductive PriceMarker where
  | indicativeClosingPrice -- Indicative Closing Price
  | calculatedOpeningPrice -- Calculated Opening Price
  | unlisted (byte : { byte : UInt8 // byte ∉ PriceMarker.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PriceMarker

def toByte : PriceMarker → UInt8
  | .indicativeClosingPrice => 0x43
  | .calculatedOpeningPrice => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PriceMarker :=
  if byte = 0x43 then .indicativeClosingPrice
  else .calculatedOpeningPrice

def ofByte (byte : UInt8) : PriceMarker :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PriceMarker) : ofByte value.toByte = value := by
  cases value with
  | indicativeClosingPrice => decide
  | calculatedOpeningPrice => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PriceMarker) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PriceMarker × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PriceMarker) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : PriceMarker) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : PriceMarker) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PriceMarker

/-- Market State: one byte code -/
def MarketState.codes : List UInt8 :=
  [0x50, 0x4F, 0x53, 0x43, 0x52, 0x46, 0x4E, 0x4D, 0x54, 0x41, 0x45, 0x4C, 0x4A, 0x47, 0x48, 0x4B, 0x58, 0x59]

inductive MarketState where
  | preOpen -- Pre Open
  | opening -- Opening
  | open_ -- Open
  | closed -- Closed
  | extendedHoursOpen -- Extended Hours Open
  | extendedHoursClose -- Extended Hours Close
  | extendedHoursCxls -- Extended Hours Cxls
  | mocImbalance -- Moc Imbalance
  | mocFreeze -- Moc Freeze
  | ccpDetermination -- Ccp Determination
  | priceMovementExtension -- Price Movement Extension
  | closing -- Closing
  | navexClosed -- Navex Closed
  | navexOrderEntry -- Navex Order Entry
  | navexOrderEntryClose -- Navex Order Entry Close
  | navexAmExecution -- Navex Am Execution
  | navexPmExecution -- Navex Pm Execution
  | navexClose -- Navex Close
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketState

def toByte : MarketState → UInt8
  | .preOpen => 0x50
  | .opening => 0x4F
  | .open_ => 0x53
  | .closed => 0x43
  | .extendedHoursOpen => 0x52
  | .extendedHoursClose => 0x46
  | .extendedHoursCxls => 0x4E
  | .mocImbalance => 0x4D
  | .mocFreeze => 0x54
  | .ccpDetermination => 0x41
  | .priceMovementExtension => 0x45
  | .closing => 0x4C
  | .navexClosed => 0x4A
  | .navexOrderEntry => 0x47
  | .navexOrderEntryClose => 0x48
  | .navexAmExecution => 0x4B
  | .navexPmExecution => 0x58
  | .navexClose => 0x59
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketState :=
  if byte = 0x50 then .preOpen
  else if byte = 0x4F then .opening
  else if byte = 0x53 then .open_
  else if byte = 0x43 then .closed
  else if byte = 0x52 then .extendedHoursOpen
  else if byte = 0x46 then .extendedHoursClose
  else if byte = 0x4E then .extendedHoursCxls
  else if byte = 0x4D then .mocImbalance
  else if byte = 0x54 then .mocFreeze
  else if byte = 0x41 then .ccpDetermination
  else if byte = 0x45 then .priceMovementExtension
  else if byte = 0x4C then .closing
  else if byte = 0x4A then .navexClosed
  else if byte = 0x47 then .navexOrderEntry
  else if byte = 0x48 then .navexOrderEntryClose
  else if byte = 0x4B then .navexAmExecution
  else if byte = 0x58 then .navexPmExecution
  else .navexClose

def ofByte (byte : UInt8) : MarketState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketState) : ofByte value.toByte = value := by
  cases value with
  | preOpen => decide
  | opening => decide
  | open_ => decide
  | closed => decide
  | extendedHoursOpen => decide
  | extendedHoursClose => decide
  | extendedHoursCxls => decide
  | mocImbalance => decide
  | mocFreeze => decide
  | ccpDetermination => decide
  | priceMovementExtension => decide
  | closing => decide
  | navexClosed => decide
  | navexOrderEntry => decide
  | navexOrderEntryClose => decide
  | navexAmExecution => decide
  | navexPmExecution => decide
  | navexClose => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarketState) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketState × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketState) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : MarketState) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : MarketState) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarketState

/-- Trade Message: 105 bytes -/
structure TradeMessage where
  symbol : Alpha 12
  volume : Alpha 9
  tradePrice : Alpha 11
  buyerId : Alpha 3
  sellerId : Alpha 3
  tradeTimeStamp : Alpha 6
  lastSale : Alpha 11
  tradeId : Alpha 9
  crossType : CrossType
  moc : Moc
  bypass : Bypass
  openingTrade : OpeningTrade
  settlementTerms : SettlementTerms
  tradingSystemTimeStamp : Alpha 23
  listingMarket : ListingMarket
  productType : ProductType
  tradeDate : Alpha 8
  isMidOnly : IsMidOnly
  isDark : IsDark
  isConditional : IsConditional
  deriving DecidableEq, Repr

namespace TradeMessage

def encode (message : TradeMessage) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.tradePrice
    ++ (Alpha.encode message.buyerId
    ++ (Alpha.encode message.sellerId
    ++ (Alpha.encode message.tradeTimeStamp
    ++ (Alpha.encode message.lastSale
    ++ (Alpha.encode message.tradeId
    ++ (CrossType.encode message.crossType
    ++ (Moc.encode message.moc
    ++ (Bypass.encode message.bypass
    ++ (OpeningTrade.encode message.openingTrade
    ++ (SettlementTerms.encode message.settlementTerms
    ++ (Alpha.encode message.tradingSystemTimeStamp
    ++ (ListingMarket.encode message.listingMarket
    ++ (ProductType.encode message.productType
    ++ (Alpha.encode message.tradeDate
    ++ (IsMidOnly.encode message.isMidOnly
    ++ (IsDark.encode message.isDark
    ++ (IsConditional.encode message.isConditional)))))))))))))))))))

def decode (bytes : List UInt8) : Option (TradeMessage × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (volume, bytes) ← Alpha.decode 9 bytes
  let (tradePrice, bytes) ← Alpha.decode 11 bytes
  let (buyerId, bytes) ← Alpha.decode 3 bytes
  let (sellerId, bytes) ← Alpha.decode 3 bytes
  let (tradeTimeStamp, bytes) ← Alpha.decode 6 bytes
  let (lastSale, bytes) ← Alpha.decode 11 bytes
  let (tradeId, bytes) ← Alpha.decode 9 bytes
  let (crossType, bytes) ← CrossType.decode bytes
  let (moc, bytes) ← Moc.decode bytes
  let (bypass, bytes) ← Bypass.decode bytes
  let (openingTrade, bytes) ← OpeningTrade.decode bytes
  let (settlementTerms, bytes) ← SettlementTerms.decode bytes
  let (tradingSystemTimeStamp, bytes) ← Alpha.decode 23 bytes
  let (listingMarket, bytes) ← ListingMarket.decode bytes
  let (productType, bytes) ← ProductType.decode bytes
  let (tradeDate, bytes) ← Alpha.decode 8 bytes
  let (isMidOnly, bytes) ← IsMidOnly.decode bytes
  let (isDark, bytes) ← IsDark.decode bytes
  let (isConditional, bytes) ← IsConditional.decode bytes
  pure ({ symbol, volume, tradePrice, buyerId, sellerId, tradeTimeStamp, lastSale, tradeId, crossType, moc, bypass, openingTrade, settlementTerms, tradingSystemTimeStamp, listingMarket, productType, tradeDate, isMidOnly, isDark, isConditional }, bytes)

@[simp] theorem encode_length (message : TradeMessage) : (encode message).length = 105 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, CrossType.encode_length, Moc.encode_length, Bypass.encode_length, OpeningTrade.encode_length, SettlementTerms.encode_length, ListingMarket.encode_length, ProductType.encode_length, IsMidOnly.encode_length, IsDark.encode_length, IsConditional.encode_length]

theorem encode_length_pos (message : TradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, CrossType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Moc.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Bypass.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpeningTrade.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SettlementTerms.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ListingMarket.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ProductType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, IsMidOnly.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, IsDark.decode_encode, some_bind]
  dsimp only
  rw [IsConditional.decode_encode, some_bind]
  rfl

end TradeMessage

/-- Symbol Status Message: 164 bytes -/
structure SymbolStatusMessage where
  symbol : Alpha 12
  tradingSystemTimeStamp : Alpha 23
  exchangeId : Alpha 3
  cusip : Alpha 12
  boardLot : Alpha 9
  currency : Alpha 1
  faceValue : Alpha 9
  lastSale : Alpha 11
  mocEligible : MocEligible
  productType : ProductType
  symbolName : Alpha 40
  stockGroup : Alpha 2
  stockState : Alpha 2
  listingMarket : ListingMarket
  buyMaximumQuantity : Alpha 9
  buyMinimumQuantity : Alpha 9
  sellMaximumQuantity : Alpha 9
  sellMinimumQuantity : Alpha 9
  testSymbol : TestSymbol
  deriving DecidableEq, Repr

namespace SymbolStatusMessage

def encode (message : SymbolStatusMessage) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (Alpha.encode message.tradingSystemTimeStamp
    ++ (Alpha.encode message.exchangeId
    ++ (Alpha.encode message.cusip
    ++ (Alpha.encode message.boardLot
    ++ (Alpha.encode message.currency
    ++ (Alpha.encode message.faceValue
    ++ (Alpha.encode message.lastSale
    ++ (MocEligible.encode message.mocEligible
    ++ (ProductType.encode message.productType
    ++ (Alpha.encode message.symbolName
    ++ (Alpha.encode message.stockGroup
    ++ (Alpha.encode message.stockState
    ++ (ListingMarket.encode message.listingMarket
    ++ (Alpha.encode message.buyMaximumQuantity
    ++ (Alpha.encode message.buyMinimumQuantity
    ++ (Alpha.encode message.sellMaximumQuantity
    ++ (Alpha.encode message.sellMinimumQuantity
    ++ (TestSymbol.encode message.testSymbol))))))))))))))))))

def decode (bytes : List UInt8) : Option (SymbolStatusMessage × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (tradingSystemTimeStamp, bytes) ← Alpha.decode 23 bytes
  let (exchangeId, bytes) ← Alpha.decode 3 bytes
  let (cusip, bytes) ← Alpha.decode 12 bytes
  let (boardLot, bytes) ← Alpha.decode 9 bytes
  let (currency, bytes) ← Alpha.decode 1 bytes
  let (faceValue, bytes) ← Alpha.decode 9 bytes
  let (lastSale, bytes) ← Alpha.decode 11 bytes
  let (mocEligible, bytes) ← MocEligible.decode bytes
  let (productType, bytes) ← ProductType.decode bytes
  let (symbolName, bytes) ← Alpha.decode 40 bytes
  let (stockGroup, bytes) ← Alpha.decode 2 bytes
  let (stockState, bytes) ← Alpha.decode 2 bytes
  let (listingMarket, bytes) ← ListingMarket.decode bytes
  let (buyMaximumQuantity, bytes) ← Alpha.decode 9 bytes
  let (buyMinimumQuantity, bytes) ← Alpha.decode 9 bytes
  let (sellMaximumQuantity, bytes) ← Alpha.decode 9 bytes
  let (sellMinimumQuantity, bytes) ← Alpha.decode 9 bytes
  let (testSymbol, bytes) ← TestSymbol.decode bytes
  pure ({ symbol, tradingSystemTimeStamp, exchangeId, cusip, boardLot, currency, faceValue, lastSale, mocEligible, productType, symbolName, stockGroup, stockState, listingMarket, buyMaximumQuantity, buyMinimumQuantity, sellMaximumQuantity, sellMinimumQuantity, testSymbol }, bytes)

@[simp] theorem encode_length (message : SymbolStatusMessage) : (encode message).length = 164 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, MocEligible.encode_length, ProductType.encode_length, ListingMarket.encode_length, TestSymbol.encode_length]

theorem encode_length_pos (message : SymbolStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SymbolStatusMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, MocEligible.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ProductType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ListingMarket.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [TestSymbol.decode_encode, some_bind]
  rfl

end SymbolStatusMessage

/-- Moc Imbalance Notification Message: 102 bytes -/
structure MocImbalanceNotificationMessage where
  symbol : Alpha 12
  imbalanceSide : ImbalanceSide
  imbalanceVolume : Alpha 9
  imbalanceReferencePrice : Alpha 11
  pairedVolume : Alpha 9
  marketOrderImbalanceVolume : Alpha 9
  marketOrderImbalanceSide : MarketOrderImbalanceSide
  nearIndicativeClosingPrice : Alpha 11
  farIndicativeClosingPrice : Alpha 11
  priceVariation : Alpha 5
  tradingSystemTimeStamp : Alpha 23
  deriving DecidableEq, Repr

namespace MocImbalanceNotificationMessage

def encode (message : MocImbalanceNotificationMessage) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (ImbalanceSide.encode message.imbalanceSide
    ++ (Alpha.encode message.imbalanceVolume
    ++ (Alpha.encode message.imbalanceReferencePrice
    ++ (Alpha.encode message.pairedVolume
    ++ (Alpha.encode message.marketOrderImbalanceVolume
    ++ (MarketOrderImbalanceSide.encode message.marketOrderImbalanceSide
    ++ (Alpha.encode message.nearIndicativeClosingPrice
    ++ (Alpha.encode message.farIndicativeClosingPrice
    ++ (Alpha.encode message.priceVariation
    ++ (Alpha.encode message.tradingSystemTimeStamp))))))))))

def decode (bytes : List UInt8) : Option (MocImbalanceNotificationMessage × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (imbalanceSide, bytes) ← ImbalanceSide.decode bytes
  let (imbalanceVolume, bytes) ← Alpha.decode 9 bytes
  let (imbalanceReferencePrice, bytes) ← Alpha.decode 11 bytes
  let (pairedVolume, bytes) ← Alpha.decode 9 bytes
  let (marketOrderImbalanceVolume, bytes) ← Alpha.decode 9 bytes
  let (marketOrderImbalanceSide, bytes) ← MarketOrderImbalanceSide.decode bytes
  let (nearIndicativeClosingPrice, bytes) ← Alpha.decode 11 bytes
  let (farIndicativeClosingPrice, bytes) ← Alpha.decode 11 bytes
  let (priceVariation, bytes) ← Alpha.decode 5 bytes
  let (tradingSystemTimeStamp, bytes) ← Alpha.decode 23 bytes
  pure ({ symbol, imbalanceSide, imbalanceVolume, imbalanceReferencePrice, pairedVolume, marketOrderImbalanceVolume, marketOrderImbalanceSide, nearIndicativeClosingPrice, farIndicativeClosingPrice, priceVariation, tradingSystemTimeStamp }, bytes)

@[simp] theorem encode_length (message : MocImbalanceNotificationMessage) : (encode message).length = 102 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ImbalanceSide.encode_length, MarketOrderImbalanceSide.encode_length]

theorem encode_length_pos (message : MocImbalanceNotificationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MocImbalanceNotificationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ImbalanceSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketOrderImbalanceSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MocImbalanceNotificationMessage

/-- Moc Price Movement Delay Message: 59 bytes -/
structure MocPriceMovementDelayMessage where
  symbol : Alpha 12
  tradingSystemTimeStamp : Alpha 23
  stockState : Alpha 2
  ccp : Alpha 11
  vwap : Alpha 11
  deriving DecidableEq, Repr

namespace MocPriceMovementDelayMessage

def encode (message : MocPriceMovementDelayMessage) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (Alpha.encode message.tradingSystemTimeStamp
    ++ (Alpha.encode message.stockState
    ++ (Alpha.encode message.ccp
    ++ (Alpha.encode message.vwap))))

def decode (bytes : List UInt8) : Option (MocPriceMovementDelayMessage × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (tradingSystemTimeStamp, bytes) ← Alpha.decode 23 bytes
  let (stockState, bytes) ← Alpha.decode 2 bytes
  let (ccp, bytes) ← Alpha.decode 11 bytes
  let (vwap, bytes) ← Alpha.decode 11 bytes
  pure ({ symbol, tradingSystemTimeStamp, stockState, ccp, vwap }, bytes)

@[simp] theorem encode_length (message : MocPriceMovementDelayMessage) : (encode message).length = 59 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : MocPriceMovementDelayMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MocPriceMovementDelayMessage) (rest : List UInt8) :
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

end MocPriceMovementDelayMessage

/-- Stock State Message: 85 bytes -/
structure StockStateMessage where
  symbol : Alpha 12
  tradingSystemTimeStamp : Alpha 23
  comment : Alpha 40
  stockState : Alpha 2
  openingTime : Alpha 6
  listingMarket : ListingMarket
  productType : ProductType
  deriving DecidableEq, Repr

namespace StockStateMessage

def encode (message : StockStateMessage) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (Alpha.encode message.tradingSystemTimeStamp
    ++ (Alpha.encode message.comment
    ++ (Alpha.encode message.stockState
    ++ (Alpha.encode message.openingTime
    ++ (ListingMarket.encode message.listingMarket
    ++ (ProductType.encode message.productType))))))

def decode (bytes : List UInt8) : Option (StockStateMessage × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (tradingSystemTimeStamp, bytes) ← Alpha.decode 23 bytes
  let (comment, bytes) ← Alpha.decode 40 bytes
  let (stockState, bytes) ← Alpha.decode 2 bytes
  let (openingTime, bytes) ← Alpha.decode 6 bytes
  let (listingMarket, bytes) ← ListingMarket.decode bytes
  let (productType, bytes) ← ProductType.decode bytes
  pure ({ symbol, tradingSystemTimeStamp, comment, stockState, openingTime, listingMarket, productType }, bytes)

@[simp] theorem encode_length (message : StockStateMessage) : (encode message).length = 85 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ListingMarket.encode_length, ProductType.encode_length]

theorem encode_length_pos (message : StockStateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StockStateMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, ListingMarket.decode_encode, some_bind]
  dsimp only
  rw [ProductType.decode_encode, some_bind]
  rfl

end StockStateMessage

/-- Quote Message: 71 bytes -/
structure QuoteMessage where
  symbol : Alpha 12
  bidPrice : Alpha 9
  bidSize : Alpha 9
  askPrice : Alpha 9
  askSize : Alpha 9
  tradingSystemTimeStamp : Alpha 23
  deriving DecidableEq, Repr

namespace QuoteMessage

def encode (message : QuoteMessage) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (Alpha.encode message.bidPrice
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.askPrice
    ++ (Alpha.encode message.askSize
    ++ (Alpha.encode message.tradingSystemTimeStamp)))))

def decode (bytes : List UInt8) : Option (QuoteMessage × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (bidPrice, bytes) ← Alpha.decode 9 bytes
  let (bidSize, bytes) ← Alpha.decode 9 bytes
  let (askPrice, bytes) ← Alpha.decode 9 bytes
  let (askSize, bytes) ← Alpha.decode 9 bytes
  let (tradingSystemTimeStamp, bytes) ← Alpha.decode 23 bytes
  pure ({ symbol, bidPrice, bidSize, askPrice, askSize, tradingSystemTimeStamp }, bytes)

@[simp] theorem encode_length (message : QuoteMessage) : (encode message).length = 71 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : QuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteMessage) (rest : List UInt8) :
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

end QuoteMessage

/-- General Message: 104 bytes -/
structure GeneralMessage where
  tradingSystemTimeStamp : Alpha 23
  bulletinIndicator : BulletinIndicator
  messageText : Alpha 80
  deriving DecidableEq, Repr

namespace GeneralMessage

def encode (message : GeneralMessage) : List UInt8 :=
  Alpha.encode message.tradingSystemTimeStamp
    ++ (BulletinIndicator.encode message.bulletinIndicator
    ++ (Alpha.encode message.messageText))

def decode (bytes : List UInt8) : Option (GeneralMessage × List UInt8) := do
  let (tradingSystemTimeStamp, bytes) ← Alpha.decode 23 bytes
  let (bulletinIndicator, bytes) ← BulletinIndicator.decode bytes
  let (messageText, bytes) ← Alpha.decode 80 bytes
  pure ({ tradingSystemTimeStamp, bulletinIndicator, messageText }, bytes)

@[simp] theorem encode_length (message : GeneralMessage) : (encode message).length = 104 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, BulletinIndicator.encode_length]

theorem encode_length_pos (message : GeneralMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : GeneralMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BulletinIndicator.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end GeneralMessage

/-- Trade Cancellation Message: 97 bytes -/
structure TradeCancellationMessage where
  symbol : Alpha 12
  volume : Alpha 9
  tradePrice : Alpha 11
  buyerId : Alpha 3
  sellerId : Alpha 3
  tradeTimeStamp : Alpha 6
  originalTradeId : Alpha 9
  lastSale : Alpha 11
  tradingSystemTimeStamp : Alpha 23
  listingMarket : ListingMarket
  productType : ProductType
  tradeDate : Alpha 8
  deriving DecidableEq, Repr

namespace TradeCancellationMessage

def encode (message : TradeCancellationMessage) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.tradePrice
    ++ (Alpha.encode message.buyerId
    ++ (Alpha.encode message.sellerId
    ++ (Alpha.encode message.tradeTimeStamp
    ++ (Alpha.encode message.originalTradeId
    ++ (Alpha.encode message.lastSale
    ++ (Alpha.encode message.tradingSystemTimeStamp
    ++ (ListingMarket.encode message.listingMarket
    ++ (ProductType.encode message.productType
    ++ (Alpha.encode message.tradeDate)))))))))))

def decode (bytes : List UInt8) : Option (TradeCancellationMessage × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (volume, bytes) ← Alpha.decode 9 bytes
  let (tradePrice, bytes) ← Alpha.decode 11 bytes
  let (buyerId, bytes) ← Alpha.decode 3 bytes
  let (sellerId, bytes) ← Alpha.decode 3 bytes
  let (tradeTimeStamp, bytes) ← Alpha.decode 6 bytes
  let (originalTradeId, bytes) ← Alpha.decode 9 bytes
  let (lastSale, bytes) ← Alpha.decode 11 bytes
  let (tradingSystemTimeStamp, bytes) ← Alpha.decode 23 bytes
  let (listingMarket, bytes) ← ListingMarket.decode bytes
  let (productType, bytes) ← ProductType.decode bytes
  let (tradeDate, bytes) ← Alpha.decode 8 bytes
  pure ({ symbol, volume, tradePrice, buyerId, sellerId, tradeTimeStamp, originalTradeId, lastSale, tradingSystemTimeStamp, listingMarket, productType, tradeDate }, bytes)

@[simp] theorem encode_length (message : TradeCancellationMessage) : (encode message).length = 97 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ListingMarket.encode_length, ProductType.encode_length]

theorem encode_length_pos (message : TradeCancellationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCancellationMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ListingMarket.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ProductType.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeCancellationMessage

/-- Indicative Price Message: 44 bytes -/
structure IndicativePriceMessage where
  symbol : Alpha 12
  cusip : Alpha 12
  indicativePrice : Alpha 11
  priceMarker : PriceMarker
  businessDate : Alpha 8
  deriving DecidableEq, Repr

namespace IndicativePriceMessage

def encode (message : IndicativePriceMessage) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (Alpha.encode message.cusip
    ++ (Alpha.encode message.indicativePrice
    ++ (PriceMarker.encode message.priceMarker
    ++ (Alpha.encode message.businessDate))))

def decode (bytes : List UInt8) : Option (IndicativePriceMessage × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (cusip, bytes) ← Alpha.decode 12 bytes
  let (indicativePrice, bytes) ← Alpha.decode 11 bytes
  let (priceMarker, bytes) ← PriceMarker.decode bytes
  let (businessDate, bytes) ← Alpha.decode 8 bytes
  pure ({ symbol, cusip, indicativePrice, priceMarker, businessDate }, bytes)

@[simp] theorem encode_length (message : IndicativePriceMessage) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, PriceMarker.encode_length]

theorem encode_length_pos (message : IndicativePriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IndicativePriceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PriceMarker.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end IndicativePriceMessage

/-- Calculated Opening Price Message: 59 bytes -/
structure CalculatedOpeningPriceMessage where
  symbol : Alpha 12
  cusip : Alpha 12
  cop : Alpha 11
  priceMarker : PriceMarker
  tradingSystemTimeStamp : Alpha 23
  deriving DecidableEq, Repr

namespace CalculatedOpeningPriceMessage

def encode (message : CalculatedOpeningPriceMessage) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (Alpha.encode message.cusip
    ++ (Alpha.encode message.cop
    ++ (PriceMarker.encode message.priceMarker
    ++ (Alpha.encode message.tradingSystemTimeStamp))))

def decode (bytes : List UInt8) : Option (CalculatedOpeningPriceMessage × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (cusip, bytes) ← Alpha.decode 12 bytes
  let (cop, bytes) ← Alpha.decode 11 bytes
  let (priceMarker, bytes) ← PriceMarker.decode bytes
  let (tradingSystemTimeStamp, bytes) ← Alpha.decode 23 bytes
  pure ({ symbol, cusip, cop, priceMarker, tradingSystemTimeStamp }, bytes)

@[simp] theorem encode_length (message : CalculatedOpeningPriceMessage) : (encode message).length = 59 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, PriceMarker.encode_length]

theorem encode_length_pos (message : CalculatedOpeningPriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CalculatedOpeningPriceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PriceMarker.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end CalculatedOpeningPriceMessage

/-- Tsx Tsxv Closing Price Message: 61 bytes -/
structure TsxTsxvClosingPriceMessage where
  symbol : Alpha 12
  cusip : Alpha 12
  tsxTsxvClosingPrice : Alpha 11
  tsxTsxvLastBid : Alpha 9
  tsxTsxvLastAsk : Alpha 9
  businessDate : Alpha 8
  deriving DecidableEq, Repr

namespace TsxTsxvClosingPriceMessage

def encode (message : TsxTsxvClosingPriceMessage) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (Alpha.encode message.cusip
    ++ (Alpha.encode message.tsxTsxvClosingPrice
    ++ (Alpha.encode message.tsxTsxvLastBid
    ++ (Alpha.encode message.tsxTsxvLastAsk
    ++ (Alpha.encode message.businessDate)))))

def decode (bytes : List UInt8) : Option (TsxTsxvClosingPriceMessage × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (cusip, bytes) ← Alpha.decode 12 bytes
  let (tsxTsxvClosingPrice, bytes) ← Alpha.decode 11 bytes
  let (tsxTsxvLastBid, bytes) ← Alpha.decode 9 bytes
  let (tsxTsxvLastAsk, bytes) ← Alpha.decode 9 bytes
  let (businessDate, bytes) ← Alpha.decode 8 bytes
  pure ({ symbol, cusip, tsxTsxvClosingPrice, tsxTsxvLastBid, tsxTsxvLastAsk, businessDate }, bytes)

@[simp] theorem encode_length (message : TsxTsxvClosingPriceMessage) : (encode message).length = 61 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : TsxTsxvClosingPriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TsxTsxvClosingPriceMessage) (rest : List UInt8) :
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

end TsxTsxvClosingPriceMessage

/-- Market State Message: 26 bytes -/
structure MarketStateMessage where
  tradingSystemTimeStamp : Alpha 23
  stockGroup : Alpha 2
  marketState : MarketState
  deriving DecidableEq, Repr

namespace MarketStateMessage

def encode (message : MarketStateMessage) : List UInt8 :=
  Alpha.encode message.tradingSystemTimeStamp
    ++ (Alpha.encode message.stockGroup
    ++ (MarketState.encode message.marketState))

def decode (bytes : List UInt8) : Option (MarketStateMessage × List UInt8) := do
  let (tradingSystemTimeStamp, bytes) ← Alpha.decode 23 bytes
  let (stockGroup, bytes) ← Alpha.decode 2 bytes
  let (marketState, bytes) ← MarketState.decode bytes
  pure ({ tradingSystemTimeStamp, stockGroup, marketState }, bytes)

@[simp] theorem encode_length (message : MarketStateMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, MarketState.encode_length]

theorem encode_length_pos (message : MarketStateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketStateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [MarketState.decode_encode, some_bind]
  rfl

end MarketStateMessage

/-- Trading Tier Status Message: 40 bytes -/
structure TradingTierStatusMessage where
  exchangeId : Alpha 3
  totalNumberOfSymbols : Alpha 5
  totalNumberOfStockGroups : Alpha 3
  tradingSystemTimeStamp : Alpha 23
  tradingTierId : Alpha 6
  deriving DecidableEq, Repr

namespace TradingTierStatusMessage

def encode (message : TradingTierStatusMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.totalNumberOfSymbols
    ++ (Alpha.encode message.totalNumberOfStockGroups
    ++ (Alpha.encode message.tradingSystemTimeStamp
    ++ (Alpha.encode message.tradingTierId))))

def decode (bytes : List UInt8) : Option (TradingTierStatusMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 3 bytes
  let (totalNumberOfSymbols, bytes) ← Alpha.decode 5 bytes
  let (totalNumberOfStockGroups, bytes) ← Alpha.decode 3 bytes
  let (tradingSystemTimeStamp, bytes) ← Alpha.decode 23 bytes
  let (tradingTierId, bytes) ← Alpha.decode 6 bytes
  pure ({ exchangeId, totalNumberOfSymbols, totalNumberOfStockGroups, tradingSystemTimeStamp, tradingTierId }, bytes)

@[simp] theorem encode_length (message : TradingTierStatusMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : TradingTierStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradingTierStatusMessage) (rest : List UInt8) :
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

end TradingTierStatusMessage

/-- Trade Correction Message: 114 bytes -/
structure TradeCorrectionMessage where
  symbol : Alpha 12
  volume : Alpha 9
  tradePrice : Alpha 11
  buyerId : Alpha 3
  sellerId : Alpha 3
  tradeTimeStamp : Alpha 6
  lastSale : Alpha 11
  tradeId : Alpha 9
  crossType : CrossType
  moc : Moc
  bypass : Bypass
  openingTrade : OpeningTrade
  settlementTerms : SettlementTerms
  originalTradeId : Alpha 9
  tradingSystemTimeStamp : Alpha 23
  listingMarket : ListingMarket
  productType : ProductType
  tradeDate : Alpha 8
  isMidOnly : IsMidOnly
  isDark : IsDark
  isConditional : IsConditional
  deriving DecidableEq, Repr

namespace TradeCorrectionMessage

def encode (message : TradeCorrectionMessage) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.tradePrice
    ++ (Alpha.encode message.buyerId
    ++ (Alpha.encode message.sellerId
    ++ (Alpha.encode message.tradeTimeStamp
    ++ (Alpha.encode message.lastSale
    ++ (Alpha.encode message.tradeId
    ++ (CrossType.encode message.crossType
    ++ (Moc.encode message.moc
    ++ (Bypass.encode message.bypass
    ++ (OpeningTrade.encode message.openingTrade
    ++ (SettlementTerms.encode message.settlementTerms
    ++ (Alpha.encode message.originalTradeId
    ++ (Alpha.encode message.tradingSystemTimeStamp
    ++ (ListingMarket.encode message.listingMarket
    ++ (ProductType.encode message.productType
    ++ (Alpha.encode message.tradeDate
    ++ (IsMidOnly.encode message.isMidOnly
    ++ (IsDark.encode message.isDark
    ++ (IsConditional.encode message.isConditional))))))))))))))))))))

def decode (bytes : List UInt8) : Option (TradeCorrectionMessage × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (volume, bytes) ← Alpha.decode 9 bytes
  let (tradePrice, bytes) ← Alpha.decode 11 bytes
  let (buyerId, bytes) ← Alpha.decode 3 bytes
  let (sellerId, bytes) ← Alpha.decode 3 bytes
  let (tradeTimeStamp, bytes) ← Alpha.decode 6 bytes
  let (lastSale, bytes) ← Alpha.decode 11 bytes
  let (tradeId, bytes) ← Alpha.decode 9 bytes
  let (crossType, bytes) ← CrossType.decode bytes
  let (moc, bytes) ← Moc.decode bytes
  let (bypass, bytes) ← Bypass.decode bytes
  let (openingTrade, bytes) ← OpeningTrade.decode bytes
  let (settlementTerms, bytes) ← SettlementTerms.decode bytes
  let (originalTradeId, bytes) ← Alpha.decode 9 bytes
  let (tradingSystemTimeStamp, bytes) ← Alpha.decode 23 bytes
  let (listingMarket, bytes) ← ListingMarket.decode bytes
  let (productType, bytes) ← ProductType.decode bytes
  let (tradeDate, bytes) ← Alpha.decode 8 bytes
  let (isMidOnly, bytes) ← IsMidOnly.decode bytes
  let (isDark, bytes) ← IsDark.decode bytes
  let (isConditional, bytes) ← IsConditional.decode bytes
  pure ({ symbol, volume, tradePrice, buyerId, sellerId, tradeTimeStamp, lastSale, tradeId, crossType, moc, bypass, openingTrade, settlementTerms, originalTradeId, tradingSystemTimeStamp, listingMarket, productType, tradeDate, isMidOnly, isDark, isConditional }, bytes)

@[simp] theorem encode_length (message : TradeCorrectionMessage) : (encode message).length = 114 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, CrossType.encode_length, Moc.encode_length, Bypass.encode_length, OpeningTrade.encode_length, SettlementTerms.encode_length, ListingMarket.encode_length, ProductType.encode_length, IsMidOnly.encode_length, IsDark.encode_length, IsConditional.encode_length]

theorem encode_length_pos (message : TradeCorrectionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCorrectionMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, CrossType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Moc.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Bypass.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpeningTrade.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SettlementTerms.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ListingMarket.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ProductType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, IsMidOnly.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, IsDark.decode_encode, some_bind]
  dsimp only
  rw [IsConditional.decode_encode, some_bind]
  rfl

end TradeCorrectionMessage

/-- Any Message Body, selected by Message Type -/
inductive MessageBody where
  | tradeMessage (message : TradeMessage) -- "A " 0x4120
  | symbolStatusMessage (message : SymbolStatusMessage) -- "B " 0x4220
  | mocImbalanceNotificationMessage (message : MocImbalanceNotificationMessage) -- "C " 0x4320
  | mocPriceMovementDelayMessage (message : MocPriceMovementDelayMessage) -- "CA" 0x4341
  | stockStateMessage (message : StockStateMessage) -- "D " 0x4420
  | quoteMessage (message : QuoteMessage) -- "E " 0x4520
  | generalMessage (message : GeneralMessage) -- "G " 0x4720
  | tradeCancellationMessage (message : TradeCancellationMessage) -- "H " 0x4820
  | indicativePriceMessage (message : IndicativePriceMessage) -- "I " 0x4920
  | calculatedOpeningPriceMessage (message : CalculatedOpeningPriceMessage) -- "O " 0x4F20
  | tsxTsxvClosingPriceMessage (message : TsxTsxvClosingPriceMessage) -- "R " 0x5220
  | marketStateMessage (message : MarketStateMessage) -- "S " 0x5320
  | tradingTierStatusMessage (message : TradingTierStatusMessage) -- "T " 0x5420
  | tradeCorrectionMessage (message : TradeCorrectionMessage) -- "X " 0x5820
  deriving DecidableEq, Repr

namespace MessageBody

/-- The Message Type each message is sent under -/
def tag : MessageBody → BitVec 16
  | .tradeMessage _ => 16672
  | .symbolStatusMessage _ => 16928
  | .mocImbalanceNotificationMessage _ => 17184
  | .mocPriceMovementDelayMessage _ => 17217
  | .stockStateMessage _ => 17440
  | .quoteMessage _ => 17696
  | .generalMessage _ => 18208
  | .tradeCancellationMessage _ => 18464
  | .indicativePriceMessage _ => 18720
  | .calculatedOpeningPriceMessage _ => 20256
  | .tsxTsxvClosingPriceMessage _ => 21024
  | .marketStateMessage _ => 21280
  | .tradingTierStatusMessage _ => 21536
  | .tradeCorrectionMessage _ => 22560

def encode : MessageBody → List UInt8
  | .tradeMessage message => TradeMessage.encode message
  | .symbolStatusMessage message => SymbolStatusMessage.encode message
  | .mocImbalanceNotificationMessage message => MocImbalanceNotificationMessage.encode message
  | .mocPriceMovementDelayMessage message => MocPriceMovementDelayMessage.encode message
  | .stockStateMessage message => StockStateMessage.encode message
  | .quoteMessage message => QuoteMessage.encode message
  | .generalMessage message => GeneralMessage.encode message
  | .tradeCancellationMessage message => TradeCancellationMessage.encode message
  | .indicativePriceMessage message => IndicativePriceMessage.encode message
  | .calculatedOpeningPriceMessage message => CalculatedOpeningPriceMessage.encode message
  | .tsxTsxvClosingPriceMessage message => TsxTsxvClosingPriceMessage.encode message
  | .marketStateMessage message => MarketStateMessage.encode message
  | .tradingTierStatusMessage message => TradingTierStatusMessage.encode message
  | .tradeCorrectionMessage message => TradeCorrectionMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : MessageBody) : (encode message).length ≤ 164 := by
  cases message with
  | tradeMessage inner =>
    simp only [encode, TradeMessage.encode_length]
    omega
  | symbolStatusMessage inner =>
    simp only [encode, SymbolStatusMessage.encode_length]
    omega
  | mocImbalanceNotificationMessage inner =>
    simp only [encode, MocImbalanceNotificationMessage.encode_length]
    omega
  | mocPriceMovementDelayMessage inner =>
    simp only [encode, MocPriceMovementDelayMessage.encode_length]
    omega
  | stockStateMessage inner =>
    simp only [encode, StockStateMessage.encode_length]
    omega
  | quoteMessage inner =>
    simp only [encode, QuoteMessage.encode_length]
    omega
  | generalMessage inner =>
    simp only [encode, GeneralMessage.encode_length]
    omega
  | tradeCancellationMessage inner =>
    simp only [encode, TradeCancellationMessage.encode_length]
    omega
  | indicativePriceMessage inner =>
    simp only [encode, IndicativePriceMessage.encode_length]
    omega
  | calculatedOpeningPriceMessage inner =>
    simp only [encode, CalculatedOpeningPriceMessage.encode_length]
    omega
  | tsxTsxvClosingPriceMessage inner =>
    simp only [encode, TsxTsxvClosingPriceMessage.encode_length]
    omega
  | marketStateMessage inner =>
    simp only [encode, MarketStateMessage.encode_length]
    omega
  | tradingTierStatusMessage inner =>
    simp only [encode, TradingTierStatusMessage.encode_length]
    omega
  | tradeCorrectionMessage inner =>
    simp only [encode, TradeCorrectionMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (MessageBody × List UInt8) :=
  if tag = 16672 then (TradeMessage.decode bytes).map fun (message, rest) => (.tradeMessage message, rest)
  else if tag = 16928 then (SymbolStatusMessage.decode bytes).map fun (message, rest) => (.symbolStatusMessage message, rest)
  else if tag = 17184 then (MocImbalanceNotificationMessage.decode bytes).map fun (message, rest) => (.mocImbalanceNotificationMessage message, rest)
  else if tag = 17217 then (MocPriceMovementDelayMessage.decode bytes).map fun (message, rest) => (.mocPriceMovementDelayMessage message, rest)
  else if tag = 17440 then (StockStateMessage.decode bytes).map fun (message, rest) => (.stockStateMessage message, rest)
  else if tag = 17696 then (QuoteMessage.decode bytes).map fun (message, rest) => (.quoteMessage message, rest)
  else if tag = 18208 then (GeneralMessage.decode bytes).map fun (message, rest) => (.generalMessage message, rest)
  else if tag = 18464 then (TradeCancellationMessage.decode bytes).map fun (message, rest) => (.tradeCancellationMessage message, rest)
  else if tag = 18720 then (IndicativePriceMessage.decode bytes).map fun (message, rest) => (.indicativePriceMessage message, rest)
  else if tag = 20256 then (CalculatedOpeningPriceMessage.decode bytes).map fun (message, rest) => (.calculatedOpeningPriceMessage message, rest)
  else if tag = 21024 then (TsxTsxvClosingPriceMessage.decode bytes).map fun (message, rest) => (.tsxTsxvClosingPriceMessage message, rest)
  else if tag = 21280 then (MarketStateMessage.decode bytes).map fun (message, rest) => (.marketStateMessage message, rest)
  else if tag = 21536 then (TradingTierStatusMessage.decode bytes).map fun (message, rest) => (.tradingTierStatusMessage message, rest)
  else if tag = 22560 then (TradeCorrectionMessage.decode bytes).map fun (message, rest) => (.tradeCorrectionMessage message, rest)
  else none

@[simp] theorem decode_encode (message : MessageBody) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end MessageBody

/-- Packet -/
structure Packet where
  qrtmdStx : BitVec 8
  messageLength : Alpha 4
  sequenceNumber : Alpha 9
  serviceIdentifier : Alpha 3
  retransmissionIdentifier : RetransmissionIdentifier
  continuationIdentifier : ContinuationIdentifier
  exchangeIdentifier : Alpha 2
  messageBody : MessageBody
  qrtmdEtx : BitVec 8
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUInt 1 message.qrtmdStx
    ++ (Alpha.encode message.messageLength
    ++ (Alpha.encode message.sequenceNumber
    ++ (Alpha.encode message.serviceIdentifier
    ++ (RetransmissionIdentifier.encode message.retransmissionIdentifier
    ++ (ContinuationIdentifier.encode message.continuationIdentifier
    ++ (encodeUInt 2 (MessageBody.tag message.messageBody)
    ++ (Alpha.encode message.exchangeIdentifier
    ++ (MessageBody.encode message.messageBody
    ++ (encodeUInt 1 message.qrtmdEtx)))))))))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (qrtmdStx, bytes) ← decodeUInt 1 bytes
  let (messageLength, bytes) ← Alpha.decode 4 bytes
  let (sequenceNumber, bytes) ← Alpha.decode 9 bytes
  let (serviceIdentifier, bytes) ← Alpha.decode 3 bytes
  let (retransmissionIdentifier, bytes) ← RetransmissionIdentifier.decode bytes
  let (continuationIdentifier, bytes) ← ContinuationIdentifier.decode bytes
  let (messageType, bytes) ← decodeUInt 2 bytes
  let (exchangeIdentifier, bytes) ← Alpha.decode 2 bytes
  let (messageBody, bytes) ← MessageBody.decode messageType bytes
  let (qrtmdEtx, bytes) ← decodeUInt 1 bytes
  pure ({ qrtmdStx, messageLength, sequenceNumber, serviceIdentifier, retransmissionIdentifier, continuationIdentifier, exchangeIdentifier, messageBody, qrtmdEtx }, bytes)

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Packet) : (encode message).length ≤ 188 := by
  unfold encode
  cases message.messageBody with
  | tradeMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, RetransmissionIdentifier.encode_length, ContinuationIdentifier.encode_length, TradeMessage.encode_length]
    omega
  | symbolStatusMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, RetransmissionIdentifier.encode_length, ContinuationIdentifier.encode_length, SymbolStatusMessage.encode_length]
    omega
  | mocImbalanceNotificationMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, RetransmissionIdentifier.encode_length, ContinuationIdentifier.encode_length, MocImbalanceNotificationMessage.encode_length]
    omega
  | mocPriceMovementDelayMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, RetransmissionIdentifier.encode_length, ContinuationIdentifier.encode_length, MocPriceMovementDelayMessage.encode_length]
    omega
  | stockStateMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, RetransmissionIdentifier.encode_length, ContinuationIdentifier.encode_length, StockStateMessage.encode_length]
    omega
  | quoteMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, RetransmissionIdentifier.encode_length, ContinuationIdentifier.encode_length, QuoteMessage.encode_length]
    omega
  | generalMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, RetransmissionIdentifier.encode_length, ContinuationIdentifier.encode_length, GeneralMessage.encode_length]
    omega
  | tradeCancellationMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, RetransmissionIdentifier.encode_length, ContinuationIdentifier.encode_length, TradeCancellationMessage.encode_length]
    omega
  | indicativePriceMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, RetransmissionIdentifier.encode_length, ContinuationIdentifier.encode_length, IndicativePriceMessage.encode_length]
    omega
  | calculatedOpeningPriceMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, RetransmissionIdentifier.encode_length, ContinuationIdentifier.encode_length, CalculatedOpeningPriceMessage.encode_length]
    omega
  | tsxTsxvClosingPriceMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, RetransmissionIdentifier.encode_length, ContinuationIdentifier.encode_length, TsxTsxvClosingPriceMessage.encode_length]
    omega
  | marketStateMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, RetransmissionIdentifier.encode_length, ContinuationIdentifier.encode_length, MarketStateMessage.encode_length]
    omega
  | tradingTierStatusMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, RetransmissionIdentifier.encode_length, ContinuationIdentifier.encode_length, TradingTierStatusMessage.encode_length]
    omega
  | tradeCorrectionMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, RetransmissionIdentifier.encode_length, ContinuationIdentifier.encode_length, TradeCorrectionMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
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
  rw [List.append_assoc, RetransmissionIdentifier.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ContinuationIdentifier.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MessageBody.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end Packet

end Omi.TmxTsxLevel1QrtmdV28
