import Wire

/-!
# Japan Exchange Group IssueBasicInformation v19.5

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.JpxTseequitiesIssuebasicinformationFlexV195

/-- Exchange Code: one byte code -/
def ExchangeCode.codes : List UInt8 :=
  [0x31, 0x33, 0x36, 0x38, 0x30, 0x20]

inductive ExchangeCode where
  | tokyoStockExchange -- Tokyo Stock Exchange
  | nagoyaStockExchange -- Nagoya Stock Exchange
  | fukuokaStockExchange -- Fukuoka Stock Exchange
  | sapporoSecuritiesExchange -- Sapporo Securities Exchange
  | other -- Other
  | controlMessage -- Control Message
  | unlisted (byte : { byte : UInt8 // byte ∉ ExchangeCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExchangeCode

def toByte : ExchangeCode → UInt8
  | .tokyoStockExchange => 0x31
  | .nagoyaStockExchange => 0x33
  | .fukuokaStockExchange => 0x36
  | .sapporoSecuritiesExchange => 0x38
  | .other => 0x30
  | .controlMessage => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExchangeCode :=
  if byte = 0x31 then .tokyoStockExchange
  else if byte = 0x33 then .nagoyaStockExchange
  else if byte = 0x36 then .fukuokaStockExchange
  else if byte = 0x38 then .sapporoSecuritiesExchange
  else if byte = 0x30 then .other
  else .controlMessage

def ofByte (byte : UInt8) : ExchangeCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExchangeCode) : ofByte value.toByte = value := by
  cases value with
  | tokyoStockExchange => decide
  | nagoyaStockExchange => decide
  | fukuokaStockExchange => decide
  | sapporoSecuritiesExchange => decide
  | other => decide
  | controlMessage => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ExchangeCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ExchangeCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ExchangeCode) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ExchangeCode) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ExchangeCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ExchangeCode

/-- CB Reserved Code: one byte code -/
def CbReservedCode.codes : List UInt8 :=
  [0x34, 0x38, 0x39, 0x20]

inductive CbReservedCode where
  | sw -- SW
  | exchangeableBond -- Exchangeable Bond
  | cb -- CB
  | otherBond -- Other Bond
  | unlisted (byte : { byte : UInt8 // byte ∉ CbReservedCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CbReservedCode

def toByte : CbReservedCode → UInt8
  | .sw => 0x34
  | .exchangeableBond => 0x38
  | .cb => 0x39
  | .otherBond => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CbReservedCode :=
  if byte = 0x34 then .sw
  else if byte = 0x38 then .exchangeableBond
  else if byte = 0x39 then .cb
  else .otherBond

def ofByte (byte : UInt8) : CbReservedCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CbReservedCode) : ofByte value.toByte = value := by
  cases value with
  | sw => decide
  | exchangeableBond => decide
  | cb => decide
  | otherBond => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CbReservedCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CbReservedCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CbReservedCode) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CbReservedCode) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CbReservedCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CbReservedCode

/-- Isin Flag: one byte code -/
def IsinFlag.codes : List UInt8 :=
  [0x31, 0x20]

inductive IsinFlag where
  | identifiableByTheInternationalStandardCode -- Identifiable By The International Standard Code
  | otherThanTheAbove -- Other Than The Above
  | unlisted (byte : { byte : UInt8 // byte ∉ IsinFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace IsinFlag

def toByte : IsinFlag → UInt8
  | .identifiableByTheInternationalStandardCode => 0x31
  | .otherThanTheAbove => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : IsinFlag :=
  if byte = 0x31 then .identifiableByTheInternationalStandardCode
  else .otherThanTheAbove

def ofByte (byte : UInt8) : IsinFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : IsinFlag) : ofByte value.toByte = value := by
  cases value with
  | identifiableByTheInternationalStandardCode => decide
  | otherThanTheAbove => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : IsinFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (IsinFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : IsinFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : IsinFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : IsinFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end IsinFlag

/-- New Listing Flag: one byte code -/
def NewListingFlag.codes : List UInt8 :=
  [0x31, 0x20]

inductive NewListingFlag where
  | newlyListedIssue -- Newly Listed Issue
  | otherThanTheAbove -- Other Than The Above
  | unlisted (byte : { byte : UInt8 // byte ∉ NewListingFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace NewListingFlag

def toByte : NewListingFlag → UInt8
  | .newlyListedIssue => 0x31
  | .otherThanTheAbove => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : NewListingFlag :=
  if byte = 0x31 then .newlyListedIssue
  else .otherThanTheAbove

def ofByte (byte : UInt8) : NewListingFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : NewListingFlag) : ofByte value.toByte = value := by
  cases value with
  | newlyListedIssue => decide
  | otherThanTheAbove => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : NewListingFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (NewListingFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : NewListingFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : NewListingFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : NewListingFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end NewListingFlag

/-- When Issued Transaction Flag: one byte code -/
def WhenIssuedTransactionFlag.codes : List UInt8 :=
  [0x31, 0x20]

inductive WhenIssuedTransactionFlag where
  | whenIssuedTransactionIssue -- When Issued Transaction Issue
  | otherThanTheAbove -- Other Than The Above
  | unlisted (byte : { byte : UInt8 // byte ∉ WhenIssuedTransactionFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace WhenIssuedTransactionFlag

def toByte : WhenIssuedTransactionFlag → UInt8
  | .whenIssuedTransactionIssue => 0x31
  | .otherThanTheAbove => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : WhenIssuedTransactionFlag :=
  if byte = 0x31 then .whenIssuedTransactionIssue
  else .otherThanTheAbove

def ofByte (byte : UInt8) : WhenIssuedTransactionFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : WhenIssuedTransactionFlag) : ofByte value.toByte = value := by
  cases value with
  | whenIssuedTransactionIssue => decide
  | otherThanTheAbove => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : WhenIssuedTransactionFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (WhenIssuedTransactionFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : WhenIssuedTransactionFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : WhenIssuedTransactionFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : WhenIssuedTransactionFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end WhenIssuedTransactionFlag

/-- Short Selling Price Restriction Applied Flag At The Regular Distribution: one byte code -/
def ShortSellingPriceRestrictionAppliedFlagAtTheRegularDistribution.codes : List UInt8 :=
  [0x31, 0x20]

inductive ShortSellingPriceRestrictionAppliedFlagAtTheRegularDistribution where
  | theIssueThatShortSellingRegulationIsApplied -- The Issue That Short Selling Regulation Is Applied
  | otherThanTheAbove -- Other Than The Above
  | unlisted (byte : { byte : UInt8 // byte ∉ ShortSellingPriceRestrictionAppliedFlagAtTheRegularDistribution.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ShortSellingPriceRestrictionAppliedFlagAtTheRegularDistribution

def toByte : ShortSellingPriceRestrictionAppliedFlagAtTheRegularDistribution → UInt8
  | .theIssueThatShortSellingRegulationIsApplied => 0x31
  | .otherThanTheAbove => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ShortSellingPriceRestrictionAppliedFlagAtTheRegularDistribution :=
  if byte = 0x31 then .theIssueThatShortSellingRegulationIsApplied
  else .otherThanTheAbove

def ofByte (byte : UInt8) : ShortSellingPriceRestrictionAppliedFlagAtTheRegularDistribution :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ShortSellingPriceRestrictionAppliedFlagAtTheRegularDistribution) : ofByte value.toByte = value := by
  cases value with
  | theIssueThatShortSellingRegulationIsApplied => decide
  | otherThanTheAbove => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ShortSellingPriceRestrictionAppliedFlagAtTheRegularDistribution) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ShortSellingPriceRestrictionAppliedFlagAtTheRegularDistribution × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ShortSellingPriceRestrictionAppliedFlagAtTheRegularDistribution) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ShortSellingPriceRestrictionAppliedFlagAtTheRegularDistribution) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ShortSellingPriceRestrictionAppliedFlagAtTheRegularDistribution) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ShortSellingPriceRestrictionAppliedFlagAtTheRegularDistribution

/-- Loan Margin Flag: one byte code -/
def LoanMarginFlag.codes : List UInt8 :=
  [0x31, 0x32, 0x30]

inductive LoanMarginFlag where
  | loanIssue -- Loan Issue
  | marginTransactionIssue -- Margin Transaction Issue
  | otherThanTheAbove -- Other Than The Above
  | unlisted (byte : { byte : UInt8 // byte ∉ LoanMarginFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LoanMarginFlag

def toByte : LoanMarginFlag → UInt8
  | .loanIssue => 0x31
  | .marginTransactionIssue => 0x32
  | .otherThanTheAbove => 0x30
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LoanMarginFlag :=
  if byte = 0x31 then .loanIssue
  else if byte = 0x32 then .marginTransactionIssue
  else .otherThanTheAbove

def ofByte (byte : UInt8) : LoanMarginFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LoanMarginFlag) : ofByte value.toByte = value := by
  cases value with
  | loanIssue => decide
  | marginTransactionIssue => decide
  | otherThanTheAbove => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LoanMarginFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LoanMarginFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LoanMarginFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : LoanMarginFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : LoanMarginFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LoanMarginFlag

/-- Securities To Be Delisted Under Supervision Classification: one byte code -/
def SecuritiesToBeDelistedUnderSupervisionClassification.codes : List UInt8 :=
  [0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x30]

inductive SecuritiesToBeDelistedUnderSupervisionClassification where
  | underSupervisionPresentlyUnderExamination -- Under Supervision Presently Under Examination
  | underSupervisionPresentlyUnderConfirmation -- Under Supervision Presently Under Confirmation
  | underSupervisionPresentlyUnderExaminationAndConfirmation -- Under Supervision Presently Under Examination And Confirmation
  | underSupervisionPresentlyUnderExaminationAndOnSpecialAlert -- Under Supervision Presently Under Examination And On Special Alert
  | underSupervisionPresentlyUnderConfirmationAndOnSpecialAlert -- Under Supervision Presently Under Confirmation And On Special Alert
  | underSupervisionPresentlyUnderExaminationAndConfirmationAndOnSpecialAlert -- Under Supervision Presently Under Examination And Confirmation And On Special Alert
  | toBeDelisted -- To Be Delisted
  | toBeDelistedAndOnSpecialAlert -- To Be Delisted And On Special Alert
  | onSpecialAlert -- On Special Alert
  | noneSpecified -- None Specified
  | unlisted (byte : { byte : UInt8 // byte ∉ SecuritiesToBeDelistedUnderSupervisionClassification.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SecuritiesToBeDelistedUnderSupervisionClassification

def toByte : SecuritiesToBeDelistedUnderSupervisionClassification → UInt8
  | .underSupervisionPresentlyUnderExamination => 0x31
  | .underSupervisionPresentlyUnderConfirmation => 0x32
  | .underSupervisionPresentlyUnderExaminationAndConfirmation => 0x33
  | .underSupervisionPresentlyUnderExaminationAndOnSpecialAlert => 0x34
  | .underSupervisionPresentlyUnderConfirmationAndOnSpecialAlert => 0x35
  | .underSupervisionPresentlyUnderExaminationAndConfirmationAndOnSpecialAlert => 0x36
  | .toBeDelisted => 0x37
  | .toBeDelistedAndOnSpecialAlert => 0x38
  | .onSpecialAlert => 0x39
  | .noneSpecified => 0x30
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SecuritiesToBeDelistedUnderSupervisionClassification :=
  if byte = 0x31 then .underSupervisionPresentlyUnderExamination
  else if byte = 0x32 then .underSupervisionPresentlyUnderConfirmation
  else if byte = 0x33 then .underSupervisionPresentlyUnderExaminationAndConfirmation
  else if byte = 0x34 then .underSupervisionPresentlyUnderExaminationAndOnSpecialAlert
  else if byte = 0x35 then .underSupervisionPresentlyUnderConfirmationAndOnSpecialAlert
  else if byte = 0x36 then .underSupervisionPresentlyUnderExaminationAndConfirmationAndOnSpecialAlert
  else if byte = 0x37 then .toBeDelisted
  else if byte = 0x38 then .toBeDelistedAndOnSpecialAlert
  else if byte = 0x39 then .onSpecialAlert
  else .noneSpecified

def ofByte (byte : UInt8) : SecuritiesToBeDelistedUnderSupervisionClassification :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SecuritiesToBeDelistedUnderSupervisionClassification) : ofByte value.toByte = value := by
  cases value with
  | underSupervisionPresentlyUnderExamination => decide
  | underSupervisionPresentlyUnderConfirmation => decide
  | underSupervisionPresentlyUnderExaminationAndConfirmation => decide
  | underSupervisionPresentlyUnderExaminationAndOnSpecialAlert => decide
  | underSupervisionPresentlyUnderConfirmationAndOnSpecialAlert => decide
  | underSupervisionPresentlyUnderExaminationAndConfirmationAndOnSpecialAlert => decide
  | toBeDelisted => decide
  | toBeDelistedAndOnSpecialAlert => decide
  | onSpecialAlert => decide
  | noneSpecified => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SecuritiesToBeDelistedUnderSupervisionClassification) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SecuritiesToBeDelistedUnderSupervisionClassification × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SecuritiesToBeDelistedUnderSupervisionClassification) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SecuritiesToBeDelistedUnderSupervisionClassification) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SecuritiesToBeDelistedUnderSupervisionClassification) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SecuritiesToBeDelistedUnderSupervisionClassification

/-- Arbitrary 1: one byte code -/
def Arbitrary1.codes : List UInt8 :=
  [0x31, 0x20]

inductive Arbitrary1 where
  | constituentIssueOfTopixCore30 -- Constituent Issue Of Topix Core 30
  | otherThanTheAbove -- Other Than The Above
  | unlisted (byte : { byte : UInt8 // byte ∉ Arbitrary1.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Arbitrary1

def toByte : Arbitrary1 → UInt8
  | .constituentIssueOfTopixCore30 => 0x31
  | .otherThanTheAbove => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Arbitrary1 :=
  if byte = 0x31 then .constituentIssueOfTopixCore30
  else .otherThanTheAbove

def ofByte (byte : UInt8) : Arbitrary1 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Arbitrary1) : ofByte value.toByte = value := by
  cases value with
  | constituentIssueOfTopixCore30 => decide
  | otherThanTheAbove => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Arbitrary1) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Arbitrary1 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Arbitrary1) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Arbitrary1) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Arbitrary1) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Arbitrary1

/-- Arbitrary 2: one byte code -/
def Arbitrary2.codes : List UInt8 :=
  [0x31, 0x20]

inductive Arbitrary2 where
  | constituentIssueOfTopixLarge70 -- Constituent Issue Of Topix Large 70
  | otherThanTheAbove -- Other Than The Above
  | unlisted (byte : { byte : UInt8 // byte ∉ Arbitrary2.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Arbitrary2

def toByte : Arbitrary2 → UInt8
  | .constituentIssueOfTopixLarge70 => 0x31
  | .otherThanTheAbove => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Arbitrary2 :=
  if byte = 0x31 then .constituentIssueOfTopixLarge70
  else .otherThanTheAbove

def ofByte (byte : UInt8) : Arbitrary2 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Arbitrary2) : ofByte value.toByte = value := by
  cases value with
  | constituentIssueOfTopixLarge70 => decide
  | otherThanTheAbove => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Arbitrary2) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Arbitrary2 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Arbitrary2) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Arbitrary2) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Arbitrary2) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Arbitrary2

/-- Arbitrary 3: one byte code -/
def Arbitrary3.codes : List UInt8 :=
  [0x31, 0x20]

inductive Arbitrary3 where
  | constituentIssueOfTopix100 -- Constituent Issue Of Topix 100
  | otherThanTheAbove -- Other Than The Above
  | unlisted (byte : { byte : UInt8 // byte ∉ Arbitrary3.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Arbitrary3

def toByte : Arbitrary3 → UInt8
  | .constituentIssueOfTopix100 => 0x31
  | .otherThanTheAbove => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Arbitrary3 :=
  if byte = 0x31 then .constituentIssueOfTopix100
  else .otherThanTheAbove

def ofByte (byte : UInt8) : Arbitrary3 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Arbitrary3) : ofByte value.toByte = value := by
  cases value with
  | constituentIssueOfTopix100 => decide
  | otherThanTheAbove => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Arbitrary3) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Arbitrary3 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Arbitrary3) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Arbitrary3) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Arbitrary3) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Arbitrary3

/-- Arbitrary 4: one byte code -/
def Arbitrary4.codes : List UInt8 :=
  [0x31, 0x20]

inductive Arbitrary4 where
  | constituentIssueOfMid400 -- Constituent Issue Of Mid 400
  | otherThanTheAbove -- Other Than The Above
  | unlisted (byte : { byte : UInt8 // byte ∉ Arbitrary4.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Arbitrary4

def toByte : Arbitrary4 → UInt8
  | .constituentIssueOfMid400 => 0x31
  | .otherThanTheAbove => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Arbitrary4 :=
  if byte = 0x31 then .constituentIssueOfMid400
  else .otherThanTheAbove

def ofByte (byte : UInt8) : Arbitrary4 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Arbitrary4) : ofByte value.toByte = value := by
  cases value with
  | constituentIssueOfMid400 => decide
  | otherThanTheAbove => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Arbitrary4) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Arbitrary4 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Arbitrary4) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Arbitrary4) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Arbitrary4) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Arbitrary4

/-- Arbitrary 5: one byte code -/
def Arbitrary5.codes : List UInt8 :=
  [0x31, 0x20]

inductive Arbitrary5 where
  | constituentIssueOfTopix500 -- Constituent Issue Of Topix 500
  | otherThanTheAbove -- Other Than The Above
  | unlisted (byte : { byte : UInt8 // byte ∉ Arbitrary5.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Arbitrary5

def toByte : Arbitrary5 → UInt8
  | .constituentIssueOfTopix500 => 0x31
  | .otherThanTheAbove => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Arbitrary5 :=
  if byte = 0x31 then .constituentIssueOfTopix500
  else .otherThanTheAbove

def ofByte (byte : UInt8) : Arbitrary5 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Arbitrary5) : ofByte value.toByte = value := by
  cases value with
  | constituentIssueOfTopix500 => decide
  | otherThanTheAbove => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Arbitrary5) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Arbitrary5 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Arbitrary5) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Arbitrary5) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Arbitrary5) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Arbitrary5

/-- Arbitrary 6: one byte code -/
def Arbitrary6.codes : List UInt8 :=
  [0x31, 0x20]

inductive Arbitrary6 where
  | constituentIssueOfTopixSmall -- Constituent Issue Of Topix Small
  | otherThanTheAbove -- Other Than The Above
  | unlisted (byte : { byte : UInt8 // byte ∉ Arbitrary6.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Arbitrary6

def toByte : Arbitrary6 → UInt8
  | .constituentIssueOfTopixSmall => 0x31
  | .otherThanTheAbove => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Arbitrary6 :=
  if byte = 0x31 then .constituentIssueOfTopixSmall
  else .otherThanTheAbove

def ofByte (byte : UInt8) : Arbitrary6 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Arbitrary6) : ofByte value.toByte = value := by
  cases value with
  | constituentIssueOfTopixSmall => decide
  | otherThanTheAbove => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Arbitrary6) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Arbitrary6 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Arbitrary6) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Arbitrary6) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Arbitrary6) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Arbitrary6

/-- Arbitrary 7: one byte code -/
def Arbitrary7.codes : List UInt8 :=
  [0x31, 0x20]

inductive Arbitrary7 where
  | constituentIssueOfTopix1000 -- Constituent Issue Of Topix 1000
  | otherThanTheAbove -- Other Than The Above
  | unlisted (byte : { byte : UInt8 // byte ∉ Arbitrary7.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Arbitrary7

def toByte : Arbitrary7 → UInt8
  | .constituentIssueOfTopix1000 => 0x31
  | .otherThanTheAbove => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Arbitrary7 :=
  if byte = 0x31 then .constituentIssueOfTopix1000
  else .otherThanTheAbove

def ofByte (byte : UInt8) : Arbitrary7 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Arbitrary7) : ofByte value.toByte = value := by
  cases value with
  | constituentIssueOfTopix1000 => decide
  | otherThanTheAbove => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Arbitrary7) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Arbitrary7 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Arbitrary7) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Arbitrary7) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Arbitrary7) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Arbitrary7

/-- Arbitrary 11: one byte code -/
def Arbitrary11.codes : List UInt8 :=
  [0x31, 0x20]

inductive Arbitrary11 where
  | constituentIssueOfTseGrowthMarket250Index -- Constituent Issue Of Tse Growth Market 250 Index
  | otherThanTheAbove -- Other Than The Above
  | unlisted (byte : { byte : UInt8 // byte ∉ Arbitrary11.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Arbitrary11

def toByte : Arbitrary11 → UInt8
  | .constituentIssueOfTseGrowthMarket250Index => 0x31
  | .otherThanTheAbove => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Arbitrary11 :=
  if byte = 0x31 then .constituentIssueOfTseGrowthMarket250Index
  else .otherThanTheAbove

def ofByte (byte : UInt8) : Arbitrary11 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Arbitrary11) : ofByte value.toByte = value := by
  cases value with
  | constituentIssueOfTseGrowthMarket250Index => decide
  | otherThanTheAbove => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Arbitrary11) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Arbitrary11 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Arbitrary11) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Arbitrary11) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Arbitrary11) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Arbitrary11

/-- Arbitrary 16: one byte code -/
def Arbitrary16.codes : List UInt8 :=
  [0x31, 0x20]

inductive Arbitrary16 where
  | constituentIssueOfReitGeneral -- Constituent Issue Of Reit General
  | otherThanTheAbove -- Other Than The Above
  | unlisted (byte : { byte : UInt8 // byte ∉ Arbitrary16.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Arbitrary16

def toByte : Arbitrary16 → UInt8
  | .constituentIssueOfReitGeneral => 0x31
  | .otherThanTheAbove => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Arbitrary16 :=
  if byte = 0x31 then .constituentIssueOfReitGeneral
  else .otherThanTheAbove

def ofByte (byte : UInt8) : Arbitrary16 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Arbitrary16) : ofByte value.toByte = value := by
  cases value with
  | constituentIssueOfReitGeneral => decide
  | otherThanTheAbove => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Arbitrary16) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Arbitrary16 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Arbitrary16) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Arbitrary16) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Arbitrary16) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Arbitrary16

/-- Market Limit Orders: one byte code -/
def MarketLimitOrders.codes : List UInt8 :=
  [0x31, 0x32, 0x20]

inductive MarketLimitOrders where
  | onlyMarketOrderIsProhibited -- Only Market Order Is Prohibited
  | bothMarketAndLimitOrdersAreProhibited -- Both Market And Limit Orders Are Prohibited
  | otherThanTheAbove -- Other Than The Above
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketLimitOrders.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketLimitOrders

def toByte : MarketLimitOrders → UInt8
  | .onlyMarketOrderIsProhibited => 0x31
  | .bothMarketAndLimitOrdersAreProhibited => 0x32
  | .otherThanTheAbove => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketLimitOrders :=
  if byte = 0x31 then .onlyMarketOrderIsProhibited
  else if byte = 0x32 then .bothMarketAndLimitOrdersAreProhibited
  else .otherThanTheAbove

def ofByte (byte : UInt8) : MarketLimitOrders :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketLimitOrders) : ofByte value.toByte = value := by
  cases value with
  | onlyMarketOrderIsProhibited => decide
  | bothMarketAndLimitOrdersAreProhibited => decide
  | otherThanTheAbove => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarketLimitOrders) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketLimitOrders × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketLimitOrders) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : MarketLimitOrders) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : MarketLimitOrders) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarketLimitOrders

/-- Side: one byte code -/
def Side.codes : List UInt8 :=
  [0x31, 0x32, 0x33, 0x20]

inductive Side where
  | bothSellAndBuyOrdersAreProhibited -- Both Sell And Buy Orders Are Prohibited
  | onlySellOrderIsProhibited -- Only Sell Order Is Prohibited
  | onlyBuyOrderIsProhibited -- Only Buy Order Is Prohibited
  | otherThanTheAbove -- Other Than The Above
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .bothSellAndBuyOrdersAreProhibited => 0x31
  | .onlySellOrderIsProhibited => 0x32
  | .onlyBuyOrderIsProhibited => 0x33
  | .otherThanTheAbove => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x31 then .bothSellAndBuyOrdersAreProhibited
  else if byte = 0x32 then .onlySellOrderIsProhibited
  else if byte = 0x33 then .onlyBuyOrderIsProhibited
  else .otherThanTheAbove

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | bothSellAndBuyOrdersAreProhibited => decide
  | onlySellOrderIsProhibited => decide
  | onlyBuyOrderIsProhibited => decide
  | otherThanTheAbove => decide
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

/-- Proprietary Brokerage: one byte code -/
def ProprietaryBrokerage.codes : List UInt8 :=
  [0x31, 0x32, 0x20]

inductive ProprietaryBrokerage where
  | onlyProprietaryOrderIsProhibited -- Only Proprietary Order Is Prohibited
  | bothProprietaryAndBrokerageOrdersAreProhibited -- Both Proprietary And Brokerage Orders Are Prohibited
  | otherThanTheAbove -- Other Than The Above
  | unlisted (byte : { byte : UInt8 // byte ∉ ProprietaryBrokerage.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ProprietaryBrokerage

def toByte : ProprietaryBrokerage → UInt8
  | .onlyProprietaryOrderIsProhibited => 0x31
  | .bothProprietaryAndBrokerageOrdersAreProhibited => 0x32
  | .otherThanTheAbove => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ProprietaryBrokerage :=
  if byte = 0x31 then .onlyProprietaryOrderIsProhibited
  else if byte = 0x32 then .bothProprietaryAndBrokerageOrdersAreProhibited
  else .otherThanTheAbove

def ofByte (byte : UInt8) : ProprietaryBrokerage :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ProprietaryBrokerage) : ofByte value.toByte = value := by
  cases value with
  | onlyProprietaryOrderIsProhibited => decide
  | bothProprietaryAndBrokerageOrdersAreProhibited => decide
  | otherThanTheAbove => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ProprietaryBrokerage) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ProprietaryBrokerage × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ProprietaryBrokerage) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ProprietaryBrokerage) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ProprietaryBrokerage) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ProprietaryBrokerage

/-- All Orders Prohibition: one byte code -/
def AllOrdersProhibition.codes : List UInt8 :=
  [0x31, 0x20]

inductive AllOrdersProhibition where
  | prohibitedForAllOrders -- Prohibited For All Orders
  | otherThanTheAbove -- Other Than The Above
  | unlisted (byte : { byte : UInt8 // byte ∉ AllOrdersProhibition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AllOrdersProhibition

def toByte : AllOrdersProhibition → UInt8
  | .prohibitedForAllOrders => 0x31
  | .otherThanTheAbove => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AllOrdersProhibition :=
  if byte = 0x31 then .prohibitedForAllOrders
  else .otherThanTheAbove

def ofByte (byte : UInt8) : AllOrdersProhibition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AllOrdersProhibition) : ofByte value.toByte = value := by
  cases value with
  | prohibitedForAllOrders => decide
  | otherThanTheAbove => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AllOrdersProhibition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AllOrdersProhibition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AllOrdersProhibition) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : AllOrdersProhibition) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : AllOrdersProhibition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AllOrdersProhibition

/-- Unit Flag: one byte code -/
def UnitFlag.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33, 0x34, 0x20]

inductive UnitFlag where
  | toTheFourthDecimalPlace -- To The Fourth Decimal Place
  | toTheThirdDecimalPlace -- To The Third Decimal Place
  | toTheSecondDecimalPlace -- To The Second Decimal Place
  | toTheFirstDecimalPlace -- To The First Decimal Place
  | noDecimalPlaces -- No Decimal Places
  | noNumericalValue -- No Numerical Value
  | unlisted (byte : { byte : UInt8 // byte ∉ UnitFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace UnitFlag

def toByte : UnitFlag → UInt8
  | .toTheFourthDecimalPlace => 0x30
  | .toTheThirdDecimalPlace => 0x31
  | .toTheSecondDecimalPlace => 0x32
  | .toTheFirstDecimalPlace => 0x33
  | .noDecimalPlaces => 0x34
  | .noNumericalValue => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : UnitFlag :=
  if byte = 0x30 then .toTheFourthDecimalPlace
  else if byte = 0x31 then .toTheThirdDecimalPlace
  else if byte = 0x32 then .toTheSecondDecimalPlace
  else if byte = 0x33 then .toTheFirstDecimalPlace
  else if byte = 0x34 then .noDecimalPlaces
  else .noNumericalValue

def ofByte (byte : UInt8) : UnitFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : UnitFlag) : ofByte value.toByte = value := by
  cases value with
  | toTheFourthDecimalPlace => decide
  | toTheThirdDecimalPlace => decide
  | toTheSecondDecimalPlace => decide
  | toTheFirstDecimalPlace => decide
  | noDecimalPlaces => decide
  | noNumericalValue => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : UnitFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (UnitFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : UnitFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : UnitFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : UnitFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end UnitFlag

/-- Sign: one byte code -/
def Sign.codes : List UInt8 :=
  [0x2B, 0x20]

inductive Sign where
  | positive -- Positive
  | noSign -- No Sign
  | unlisted (byte : { byte : UInt8 // byte ∉ Sign.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Sign

def toByte : Sign → UInt8
  | .positive => 0x2B
  | .noSign => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Sign :=
  if byte = 0x2B then .positive
  else .noSign

def ofByte (byte : UInt8) : Sign :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Sign) : ofByte value.toByte = value := by
  cases value with
  | positive => decide
  | noSign => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Sign) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Sign × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Sign) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Sign) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Sign) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Sign

/-- Base Price Price Of The Middle Of The Book: one byte code -/
def BasePricePriceOfTheMiddleOfTheBook.codes : List UInt8 :=
  [0x31, 0x32]

inductive BasePricePriceOfTheMiddleOfTheBook where
  | basePrice -- Base Price
  | priceOfTheMiddleOfTheBook -- Price Of The Middle Of The Book
  | unlisted (byte : { byte : UInt8 // byte ∉ BasePricePriceOfTheMiddleOfTheBook.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BasePricePriceOfTheMiddleOfTheBook

def toByte : BasePricePriceOfTheMiddleOfTheBook → UInt8
  | .basePrice => 0x31
  | .priceOfTheMiddleOfTheBook => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BasePricePriceOfTheMiddleOfTheBook :=
  if byte = 0x31 then .basePrice
  else .priceOfTheMiddleOfTheBook

def ofByte (byte : UInt8) : BasePricePriceOfTheMiddleOfTheBook :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BasePricePriceOfTheMiddleOfTheBook) : ofByte value.toByte = value := by
  cases value with
  | basePrice => decide
  | priceOfTheMiddleOfTheBook => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BasePricePriceOfTheMiddleOfTheBook) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BasePricePriceOfTheMiddleOfTheBook × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BasePricePriceOfTheMiddleOfTheBook) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : BasePricePriceOfTheMiddleOfTheBook) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : BasePricePriceOfTheMiddleOfTheBook) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BasePricePriceOfTheMiddleOfTheBook

/-- Test Mode Flag: one byte code -/
def TestModeFlag.codes : List UInt8 :=
  [0x31, 0x32]

inductive TestModeFlag where
  | realOperation -- Real Operation
  | testOperation -- Test Operation
  | unlisted (byte : { byte : UInt8 // byte ∉ TestModeFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TestModeFlag

def toByte : TestModeFlag → UInt8
  | .realOperation => 0x31
  | .testOperation => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TestModeFlag :=
  if byte = 0x31 then .realOperation
  else .testOperation

def ofByte (byte : UInt8) : TestModeFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TestModeFlag) : ofByte value.toByte = value := by
  cases value with
  | realOperation => decide
  | testOperation => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TestModeFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TestModeFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TestModeFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TestModeFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TestModeFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TestModeFlag

/-- Start End Flag: one byte code -/
def StartEndFlag.codes : List UInt8 :=
  [0x31, 0x32, 0x20]

inductive StartEndFlag where
  | start -- Start
  | end_ -- End
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ StartEndFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace StartEndFlag

def toByte : StartEndFlag → UInt8
  | .start => 0x31
  | .end_ => 0x32
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : StartEndFlag :=
  if byte = 0x31 then .start
  else if byte = 0x32 then .end_
  else .notApplicable

def ofByte (byte : UInt8) : StartEndFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : StartEndFlag) : ofByte value.toByte = value := by
  cases value with
  | start => decide
  | end_ => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : StartEndFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (StartEndFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : StartEndFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : StartEndFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : StartEndFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end StartEndFlag

/-- Message Serial No: 11 bytes -/
structure MessageSerialNo where
  multicastGroupNumber : Alpha 3
  sequenceNumber : Alpha 8
  deriving DecidableEq, Repr

namespace MessageSerialNo

def encode (message : MessageSerialNo) : List UInt8 :=
  Alpha.encode message.multicastGroupNumber
    ++ (Alpha.encode message.sequenceNumber)

def decode (bytes : List UInt8) : Option (MessageSerialNo × List UInt8) := do
  let (multicastGroupNumber, bytes) ← Alpha.decode 3 bytes
  let (sequenceNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ multicastGroupNumber, sequenceNumber }, bytes)

@[simp] theorem encode_length (message : MessageSerialNo) : (encode message).length = 11 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : MessageSerialNo) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MessageSerialNo) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MessageSerialNo

/-- Issue Realtime Medium Classification: 2 bytes -/
structure IssueRealtimeMediumClassificationValue where
  issueRealtimeMediumClassification : Alpha 2
  deriving DecidableEq, Repr

namespace IssueRealtimeMediumClassificationValue

def encode (message : IssueRealtimeMediumClassificationValue) : List UInt8 :=
  Alpha.encode message.issueRealtimeMediumClassification

def decode (bytes : List UInt8) : Option (IssueRealtimeMediumClassificationValue × List UInt8) := do
  let (issueRealtimeMediumClassification, bytes) ← Alpha.decode 2 bytes
  pure ({ issueRealtimeMediumClassification }, bytes)

@[simp] theorem encode_length (message : IssueRealtimeMediumClassificationValue) : (encode message).length = 2 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : IssueRealtimeMediumClassificationValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IssueRealtimeMediumClassificationValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end IssueRealtimeMediumClassificationValue

/-- Statistics Medium Classification: 2 bytes -/
structure StatisticsMediumClassificationValue where
  statisticsMediumClassification : Alpha 2
  deriving DecidableEq, Repr

namespace StatisticsMediumClassificationValue

def encode (message : StatisticsMediumClassificationValue) : List UInt8 :=
  Alpha.encode message.statisticsMediumClassification

def decode (bytes : List UInt8) : Option (StatisticsMediumClassificationValue × List UInt8) := do
  let (statisticsMediumClassification, bytes) ← Alpha.decode 2 bytes
  pure ({ statisticsMediumClassification }, bytes)

@[simp] theorem encode_length (message : StatisticsMediumClassificationValue) : (encode message).length = 2 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : StatisticsMediumClassificationValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StatisticsMediumClassificationValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end StatisticsMediumClassificationValue

/-- Index Medium Classification: 2 bytes -/
structure IndexMediumClassificationValue where
  indexMediumClassification : Alpha 2
  deriving DecidableEq, Repr

namespace IndexMediumClassificationValue

def encode (message : IndexMediumClassificationValue) : List UInt8 :=
  Alpha.encode message.indexMediumClassification

def decode (bytes : List UInt8) : Option (IndexMediumClassificationValue × List UInt8) := do
  let (indexMediumClassification, bytes) ← Alpha.decode 2 bytes
  pure ({ indexMediumClassification }, bytes)

@[simp] theorem encode_length (message : IndexMediumClassificationValue) : (encode message).length = 2 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : IndexMediumClassificationValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IndexMediumClassificationValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end IndexMediumClassificationValue

/-- Issue Basic Medium Classification: 2 bytes -/
structure IssueBasicMediumClassificationValue where
  issueBasicMediumClassification : Alpha 2
  deriving DecidableEq, Repr

namespace IssueBasicMediumClassificationValue

def encode (message : IssueBasicMediumClassificationValue) : List UInt8 :=
  Alpha.encode message.issueBasicMediumClassification

def decode (bytes : List UInt8) : Option (IssueBasicMediumClassificationValue × List UInt8) := do
  let (issueBasicMediumClassification, bytes) ← Alpha.decode 2 bytes
  pure ({ issueBasicMediumClassification }, bytes)

@[simp] theorem encode_length (message : IssueBasicMediumClassificationValue) : (encode message).length = 2 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : IssueBasicMediumClassificationValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IssueBasicMediumClassificationValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end IssueBasicMediumClassificationValue

/-- Control Medium Classification: 2 bytes -/
structure ControlMediumClassificationValue where
  controlMediumClassification : Alpha 2
  deriving DecidableEq, Repr

namespace ControlMediumClassificationValue

def encode (message : ControlMediumClassificationValue) : List UInt8 :=
  Alpha.encode message.controlMediumClassification

def decode (bytes : List UInt8) : Option (ControlMediumClassificationValue × List UInt8) := do
  let (controlMediumClassification, bytes) ← Alpha.decode 2 bytes
  pure ({ controlMediumClassification }, bytes)

@[simp] theorem encode_length (message : ControlMediumClassificationValue) : (encode message).length = 2 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : ControlMediumClassificationValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ControlMediumClassificationValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end ControlMediumClassificationValue

/-- Any Message Type Medium Classification, selected by Message Type Large Classification -/
inductive MessageTypeMediumClassification where
  | issueRealtimeMediumClassification (message : IssueRealtimeMediumClassificationValue) -- "1" 0x31
  | statisticsMediumClassification (message : StatisticsMediumClassificationValue) -- "2" 0x32
  | indexMediumClassification (message : IndexMediumClassificationValue) -- "3" 0x33
  | issueBasicMediumClassification (message : IssueBasicMediumClassificationValue) -- "4" 0x34
  | controlMediumClassification (message : ControlMediumClassificationValue) -- "9" 0x39
  deriving DecidableEq, Repr

namespace MessageTypeMediumClassification

/-- The Message Type Large Classification each message is sent under -/
def tag : MessageTypeMediumClassification → BitVec 8
  | .issueRealtimeMediumClassification _ => 49
  | .statisticsMediumClassification _ => 50
  | .indexMediumClassification _ => 51
  | .issueBasicMediumClassification _ => 52
  | .controlMediumClassification _ => 57

def encode : MessageTypeMediumClassification → List UInt8
  | .issueRealtimeMediumClassification message => IssueRealtimeMediumClassificationValue.encode message
  | .statisticsMediumClassification message => StatisticsMediumClassificationValue.encode message
  | .indexMediumClassification message => IndexMediumClassificationValue.encode message
  | .issueBasicMediumClassification message => IssueBasicMediumClassificationValue.encode message
  | .controlMediumClassification message => ControlMediumClassificationValue.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : MessageTypeMediumClassification) : (encode message).length ≤ 2 := by
  cases message with
  | issueRealtimeMediumClassification inner =>
    simp only [encode, IssueRealtimeMediumClassificationValue.encode_length]
    omega
  | statisticsMediumClassification inner =>
    simp only [encode, StatisticsMediumClassificationValue.encode_length]
    omega
  | indexMediumClassification inner =>
    simp only [encode, IndexMediumClassificationValue.encode_length]
    omega
  | issueBasicMediumClassification inner =>
    simp only [encode, IssueBasicMediumClassificationValue.encode_length]
    omega
  | controlMediumClassification inner =>
    simp only [encode, ControlMediumClassificationValue.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (MessageTypeMediumClassification × List UInt8) :=
  if tag = 49 then (IssueRealtimeMediumClassificationValue.decode bytes).map fun (message, rest) => (.issueRealtimeMediumClassification message, rest)
  else if tag = 50 then (StatisticsMediumClassificationValue.decode bytes).map fun (message, rest) => (.statisticsMediumClassification message, rest)
  else if tag = 51 then (IndexMediumClassificationValue.decode bytes).map fun (message, rest) => (.indexMediumClassification message, rest)
  else if tag = 52 then (IssueBasicMediumClassificationValue.decode bytes).map fun (message, rest) => (.issueBasicMediumClassification message, rest)
  else if tag = 57 then (ControlMediumClassificationValue.decode bytes).map fun (message, rest) => (.controlMediumClassification message, rest)
  else none

@[simp] theorem decode_encode (message : MessageTypeMediumClassification) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end MessageTypeMediumClassification

/-- Message Type -/
structure MessageType where
  messageTypeMediumClassification : MessageTypeMediumClassification
  deriving DecidableEq, Repr

namespace MessageType

def encode (message : MessageType) : List UInt8 :=
  encodeUInt 1 (MessageTypeMediumClassification.tag message.messageTypeMediumClassification)
    ++ (MessageTypeMediumClassification.encode message.messageTypeMediumClassification)

def decode (bytes : List UInt8) : Option (MessageType × List UInt8) := do
  let (messageTypeLargeClassification, bytes) ← decodeUInt 1 bytes
  let (messageTypeMediumClassification, bytes) ← MessageTypeMediumClassification.decode messageTypeLargeClassification bytes
  pure ({ messageTypeMediumClassification }, bytes)

theorem encode_length_pos (message : MessageType) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MessageType) : (encode message).length ≤ 3 := by
  unfold encode
  cases message.messageTypeMediumClassification with
  | issueRealtimeMediumClassification inner =>
    simp only [MessageTypeMediumClassification.encode, List.length_append, encodeUInt_length, IssueRealtimeMediumClassificationValue.encode_length]
    omega
  | statisticsMediumClassification inner =>
    simp only [MessageTypeMediumClassification.encode, List.length_append, encodeUInt_length, StatisticsMediumClassificationValue.encode_length]
    omega
  | indexMediumClassification inner =>
    simp only [MessageTypeMediumClassification.encode, List.length_append, encodeUInt_length, IndexMediumClassificationValue.encode_length]
    omega
  | issueBasicMediumClassification inner =>
    simp only [MessageTypeMediumClassification.encode, List.length_append, encodeUInt_length, IssueBasicMediumClassificationValue.encode_length]
    omega
  | controlMediumClassification inner =>
    simp only [MessageTypeMediumClassification.encode, List.length_append, encodeUInt_length, ControlMediumClassificationValue.encode_length]
    omega

@[simp] theorem decode_encode (message : MessageType) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [MessageTypeMediumClassification.decode_encode, some_bind]
  rfl

end MessageType

/-- Stock Issue Code: 12 bytes -/
structure StockIssueCode where
  stockSpace : Alpha 7
  stockProperNameCode : Alpha 4
  stockReservedCode : Alpha 1
  deriving DecidableEq, Repr

namespace StockIssueCode

def encode (message : StockIssueCode) : List UInt8 :=
  Alpha.encode message.stockSpace
    ++ (Alpha.encode message.stockProperNameCode
    ++ (Alpha.encode message.stockReservedCode))

def decode (bytes : List UInt8) : Option (StockIssueCode × List UInt8) := do
  let (stockSpace, bytes) ← Alpha.decode 7 bytes
  let (stockProperNameCode, bytes) ← Alpha.decode 4 bytes
  let (stockReservedCode, bytes) ← Alpha.decode 1 bytes
  pure ({ stockSpace, stockProperNameCode, stockReservedCode }, bytes)

@[simp] theorem encode_length (message : StockIssueCode) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : StockIssueCode) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StockIssueCode) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StockIssueCode

/-- CB Issue Code: 12 bytes -/
structure CbIssueCode where
  cbSpace : Alpha 3
  cbReservedCode : CbReservedCode
  timeSymbol : Alpha 4
  cbProperNameCode : Alpha 4
  deriving DecidableEq, Repr

namespace CbIssueCode

def encode (message : CbIssueCode) : List UInt8 :=
  Alpha.encode message.cbSpace
    ++ (CbReservedCode.encode message.cbReservedCode
    ++ (Alpha.encode message.timeSymbol
    ++ (Alpha.encode message.cbProperNameCode)))

def decode (bytes : List UInt8) : Option (CbIssueCode × List UInt8) := do
  let (cbSpace, bytes) ← Alpha.decode 3 bytes
  let (cbReservedCode, bytes) ← CbReservedCode.decode bytes
  let (timeSymbol, bytes) ← Alpha.decode 4 bytes
  let (cbProperNameCode, bytes) ← Alpha.decode 4 bytes
  pure ({ cbSpace, cbReservedCode, timeSymbol, cbProperNameCode }, bytes)

@[simp] theorem encode_length (message : CbIssueCode) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, CbReservedCode.encode_length]

theorem encode_length_pos (message : CbIssueCode) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CbIssueCode) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CbReservedCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end CbIssueCode

/-- Blank Issue Code: 12 bytes -/
structure BlankIssueCodeValue where
  blankIssueCode : Alpha 12
  deriving DecidableEq, Repr

namespace BlankIssueCodeValue

def encode (message : BlankIssueCodeValue) : List UInt8 :=
  Alpha.encode message.blankIssueCode

def decode (bytes : List UInt8) : Option (BlankIssueCodeValue × List UInt8) := do
  let (blankIssueCode, bytes) ← Alpha.decode 12 bytes
  pure ({ blankIssueCode }, bytes)

@[simp] theorem encode_length (message : BlankIssueCodeValue) : (encode message).length = 12 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : BlankIssueCodeValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BlankIssueCodeValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end BlankIssueCodeValue

/-- Any Issue Code, selected by Issue Classification Large Classification -/
inductive IssueCode where
  | stockIssueCode (message : StockIssueCode) -- "01" 0x3031
  | cbIssueCode (message : CbIssueCode) -- "02" 0x3032
  | blankIssueCode (tag : { v : BitVec 16 // v ≠ 12337 ∧ v ≠ 12338 }) (message : BlankIssueCodeValue) -- any other value: the bytes it states
  deriving DecidableEq, Repr

namespace IssueCode

/-- The Issue Classification Large Classification each message is sent under -/
def tag : IssueCode → BitVec 16
  | .stockIssueCode _ => 12337
  | .cbIssueCode _ => 12338
  | .blankIssueCode tag _ => tag.val

def encode : IssueCode → List UInt8
  | .stockIssueCode message => StockIssueCode.encode message
  | .cbIssueCode message => CbIssueCode.encode message
  | .blankIssueCode _ message => BlankIssueCodeValue.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : IssueCode) : (encode message).length ≤ 12 := by
  cases message with
  | stockIssueCode inner =>
    simp only [encode, StockIssueCode.encode_length]
    omega
  | cbIssueCode inner =>
    simp only [encode, CbIssueCode.encode_length]
    omega
  | blankIssueCode _ inner =>
    simp only [encode, BlankIssueCodeValue.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (IssueCode × List UInt8) :=
  if h0 : tag = 12337 then (StockIssueCode.decode bytes).map fun (message, rest) => (.stockIssueCode message, rest)
  else if h1 : tag = 12338 then (CbIssueCode.decode bytes).map fun (message, rest) => (.cbIssueCode message, rest)
  else (BlankIssueCodeValue.decode bytes).map fun (message, rest) => (.blankIssueCode ⟨tag, h0, h1⟩ message, rest)

@[simp] theorem decode_encode (message : IssueCode) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message with
  | stockIssueCode m => simp [decode, encode, tag]
  | cbIssueCode m => simp [decode, encode, tag]
  | blankIssueCode t m =>
    obtain ⟨v, h0, h1⟩ := t
    simp only [tag, encode, decode, h0, h1, reduceDIte, BlankIssueCodeValue.decode_encode, Option.map_some]

end IssueCode

/-- Service Header -/
structure ServiceHeader where
  messageLength : Alpha 6
  messageSerialNo : MessageSerialNo
  messageType : MessageType
  exchangeCode : ExchangeCode
  sessionDistinction : Alpha 2
  issueClassificationMediumClassification : Alpha 2
  issueCode : IssueCode
  deriving DecidableEq, Repr

namespace ServiceHeader

def encode (message : ServiceHeader) : List UInt8 :=
  Alpha.encode message.messageLength
    ++ (MessageSerialNo.encode message.messageSerialNo
    ++ (MessageType.encode message.messageType
    ++ (ExchangeCode.encode message.exchangeCode
    ++ (Alpha.encode message.sessionDistinction
    ++ (encodeUInt 2 (IssueCode.tag message.issueCode)
    ++ (Alpha.encode message.issueClassificationMediumClassification
    ++ (IssueCode.encode message.issueCode)))))))

def decode (bytes : List UInt8) : Option (ServiceHeader × List UInt8) := do
  let (messageLength, bytes) ← Alpha.decode 6 bytes
  let (messageSerialNo, bytes) ← MessageSerialNo.decode bytes
  let (messageType, bytes) ← MessageType.decode bytes
  let (exchangeCode, bytes) ← ExchangeCode.decode bytes
  let (sessionDistinction, bytes) ← Alpha.decode 2 bytes
  let (issueClassificationLargeClassification, bytes) ← decodeUInt 2 bytes
  let (issueClassificationMediumClassification, bytes) ← Alpha.decode 2 bytes
  let (issueCode, bytes) ← IssueCode.decode issueClassificationLargeClassification bytes
  pure ({ messageLength, messageSerialNo, messageType, exchangeCode, sessionDistinction, issueClassificationMediumClassification, issueCode }, bytes)

theorem encode_length_pos (message : ServiceHeader) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : ServiceHeader) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MessageSerialNo.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MessageType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExchangeCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [IssueCode.decode_encode, some_bind]
  rfl

end ServiceHeader

/-- Index Constituent Issue: 20 bytes -/
structure IndexConstituentIssue where
  arbitrary1 : Arbitrary1
  arbitrary2 : Arbitrary2
  arbitrary3 : Arbitrary3
  arbitrary4 : Arbitrary4
  arbitrary5 : Arbitrary5
  arbitrary6 : Arbitrary6
  arbitrary7 : Arbitrary7
  arbitrary8To10 : Alpha 3
  arbitrary11 : Arbitrary11
  arbitrary12To15 : Alpha 4
  arbitrary16 : Arbitrary16
  arbitrary17To19 : Alpha 3
  arbitrary20 : Alpha 1
  deriving DecidableEq, Repr

namespace IndexConstituentIssue

def encode (message : IndexConstituentIssue) : List UInt8 :=
  Arbitrary1.encode message.arbitrary1
    ++ (Arbitrary2.encode message.arbitrary2
    ++ (Arbitrary3.encode message.arbitrary3
    ++ (Arbitrary4.encode message.arbitrary4
    ++ (Arbitrary5.encode message.arbitrary5
    ++ (Arbitrary6.encode message.arbitrary6
    ++ (Arbitrary7.encode message.arbitrary7
    ++ (Alpha.encode message.arbitrary8To10
    ++ (Arbitrary11.encode message.arbitrary11
    ++ (Alpha.encode message.arbitrary12To15
    ++ (Arbitrary16.encode message.arbitrary16
    ++ (Alpha.encode message.arbitrary17To19
    ++ (Alpha.encode message.arbitrary20))))))))))))

def decode (bytes : List UInt8) : Option (IndexConstituentIssue × List UInt8) := do
  let (arbitrary1, bytes) ← Arbitrary1.decode bytes
  let (arbitrary2, bytes) ← Arbitrary2.decode bytes
  let (arbitrary3, bytes) ← Arbitrary3.decode bytes
  let (arbitrary4, bytes) ← Arbitrary4.decode bytes
  let (arbitrary5, bytes) ← Arbitrary5.decode bytes
  let (arbitrary6, bytes) ← Arbitrary6.decode bytes
  let (arbitrary7, bytes) ← Arbitrary7.decode bytes
  let (arbitrary8To10, bytes) ← Alpha.decode 3 bytes
  let (arbitrary11, bytes) ← Arbitrary11.decode bytes
  let (arbitrary12To15, bytes) ← Alpha.decode 4 bytes
  let (arbitrary16, bytes) ← Arbitrary16.decode bytes
  let (arbitrary17To19, bytes) ← Alpha.decode 3 bytes
  let (arbitrary20, bytes) ← Alpha.decode 1 bytes
  pure ({ arbitrary1, arbitrary2, arbitrary3, arbitrary4, arbitrary5, arbitrary6, arbitrary7, arbitrary8To10, arbitrary11, arbitrary12To15, arbitrary16, arbitrary17To19, arbitrary20 }, bytes)

@[simp] theorem encode_length (message : IndexConstituentIssue) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, Arbitrary1.encode_length, Arbitrary2.encode_length, Arbitrary3.encode_length, Arbitrary4.encode_length, Arbitrary5.encode_length, Arbitrary6.encode_length, Arbitrary7.encode_length, Alpha.encode_length, Arbitrary11.encode_length, Arbitrary16.encode_length]

theorem encode_length_pos (message : IndexConstituentIssue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IndexConstituentIssue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Arbitrary1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Arbitrary2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Arbitrary3.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Arbitrary4.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Arbitrary5.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Arbitrary6.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Arbitrary7.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Arbitrary11.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Arbitrary16.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end IndexConstituentIssue

/-- New Orders Prohibition: 4 bytes -/
structure NewOrdersProhibition where
  marketLimitOrders : MarketLimitOrders
  side : Side
  proprietaryBrokerage : ProprietaryBrokerage
  reserved1 : Alpha 1
  deriving DecidableEq, Repr

namespace NewOrdersProhibition

def encode (message : NewOrdersProhibition) : List UInt8 :=
  MarketLimitOrders.encode message.marketLimitOrders
    ++ (Side.encode message.side
    ++ (ProprietaryBrokerage.encode message.proprietaryBrokerage
    ++ (Alpha.encode message.reserved1)))

def decode (bytes : List UInt8) : Option (NewOrdersProhibition × List UInt8) := do
  let (marketLimitOrders, bytes) ← MarketLimitOrders.decode bytes
  let (side, bytes) ← Side.decode bytes
  let (proprietaryBrokerage, bytes) ← ProprietaryBrokerage.decode bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  pure ({ marketLimitOrders, side, proprietaryBrokerage, reserved1 }, bytes)

@[simp] theorem encode_length (message : NewOrdersProhibition) : (encode message).length = 4 := by
  unfold encode
  simp only [List.length_append, MarketLimitOrders.encode_length, Side.encode_length, ProprietaryBrokerage.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : NewOrdersProhibition) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewOrdersProhibition) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, MarketLimitOrders.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ProprietaryBrokerage.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end NewOrdersProhibition

/-- Margin Transactions Prohibition: 3 bytes -/
structure MarginTransactionsProhibition where
  side : Side
  proprietaryBrokerage : ProprietaryBrokerage
  reserved1 : Alpha 1
  deriving DecidableEq, Repr

namespace MarginTransactionsProhibition

def encode (message : MarginTransactionsProhibition) : List UInt8 :=
  Side.encode message.side
    ++ (ProprietaryBrokerage.encode message.proprietaryBrokerage
    ++ (Alpha.encode message.reserved1))

def decode (bytes : List UInt8) : Option (MarginTransactionsProhibition × List UInt8) := do
  let (side, bytes) ← Side.decode bytes
  let (proprietaryBrokerage, bytes) ← ProprietaryBrokerage.decode bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  pure ({ side, proprietaryBrokerage, reserved1 }, bytes)

@[simp] theorem encode_length (message : MarginTransactionsProhibition) : (encode message).length = 3 := by
  unfold encode
  simp only [List.length_append, Side.encode_length, ProprietaryBrokerage.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : MarginTransactionsProhibition) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarginTransactionsProhibition) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ProprietaryBrokerage.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MarginTransactionsProhibition

/-- Short Selling Prohibition: 2 bytes -/
structure ShortSellingProhibition where
  proprietaryBrokerage : ProprietaryBrokerage
  reserved1 : Alpha 1
  deriving DecidableEq, Repr

namespace ShortSellingProhibition

def encode (message : ShortSellingProhibition) : List UInt8 :=
  ProprietaryBrokerage.encode message.proprietaryBrokerage
    ++ (Alpha.encode message.reserved1)

def decode (bytes : List UInt8) : Option (ShortSellingProhibition × List UInt8) := do
  let (proprietaryBrokerage, bytes) ← ProprietaryBrokerage.decode bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  pure ({ proprietaryBrokerage, reserved1 }, bytes)

@[simp] theorem encode_length (message : ShortSellingProhibition) : (encode message).length = 2 := by
  unfold encode
  simp only [List.length_append, ProprietaryBrokerage.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : ShortSellingProhibition) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ShortSellingProhibition) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ProprietaryBrokerage.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ShortSellingProhibition

/-- Order Prohibition Status At The Regular Distribution: 10 bytes -/
structure OrderProhibitionStatusAtTheRegularDistribution where
  newOrdersProhibition : NewOrdersProhibition
  marginTransactionsProhibition : MarginTransactionsProhibition
  shortSellingProhibition : ShortSellingProhibition
  allOrdersProhibition : AllOrdersProhibition
  deriving DecidableEq, Repr

namespace OrderProhibitionStatusAtTheRegularDistribution

def encode (message : OrderProhibitionStatusAtTheRegularDistribution) : List UInt8 :=
  NewOrdersProhibition.encode message.newOrdersProhibition
    ++ (MarginTransactionsProhibition.encode message.marginTransactionsProhibition
    ++ (ShortSellingProhibition.encode message.shortSellingProhibition
    ++ (AllOrdersProhibition.encode message.allOrdersProhibition)))

def decode (bytes : List UInt8) : Option (OrderProhibitionStatusAtTheRegularDistribution × List UInt8) := do
  let (newOrdersProhibition, bytes) ← NewOrdersProhibition.decode bytes
  let (marginTransactionsProhibition, bytes) ← MarginTransactionsProhibition.decode bytes
  let (shortSellingProhibition, bytes) ← ShortSellingProhibition.decode bytes
  let (allOrdersProhibition, bytes) ← AllOrdersProhibition.decode bytes
  pure ({ newOrdersProhibition, marginTransactionsProhibition, shortSellingProhibition, allOrdersProhibition }, bytes)

@[simp] theorem encode_length (message : OrderProhibitionStatusAtTheRegularDistribution) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, NewOrdersProhibition.encode_length, MarginTransactionsProhibition.encode_length, ShortSellingProhibition.encode_length, AllOrdersProhibition.encode_length]

theorem encode_length_pos (message : OrderProhibitionStatusAtTheRegularDistribution) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderProhibitionStatusAtTheRegularDistribution) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, NewOrdersProhibition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarginTransactionsProhibition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ShortSellingProhibition.decode_encode, some_bind]
  dsimp only
  rw [AllOrdersProhibition.decode_encode, some_bind]
  rfl

end OrderProhibitionStatusAtTheRegularDistribution

/-- Issue Information Message: 123 bytes -/
structure IssueInformationMessage where
  reserved2 : Alpha 2
  serialNo : Alpha 6
  applicableBusinessDay : Alpha 8
  reserved1 : Alpha 1
  issueName : Alpha 20
  securityTypeEtcIdentificationCode : Alpha 2
  isinFlag : IsinFlag
  newSecurityCode : Alpha 12
  industryCode : Alpha 4
  newListingFlag : NewListingFlag
  whenIssuedTransactionFlag : WhenIssuedTransactionFlag
  shortSellingPriceRestrictionAppliedFlagAtTheRegularDistribution : ShortSellingPriceRestrictionAppliedFlagAtTheRegularDistribution
  loanMarginFlag : LoanMarginFlag
  exDividendExRightFlag : Alpha 2
  securitiesToBeDelistedUnderSupervisionClassification : SecuritiesToBeDelistedUnderSupervisionClassification
  reserved5 : Alpha 5
  unitOfTrading : Alpha 14
  indexConstituentIssue : IndexConstituentIssue
  orderProhibitionStatusAtTheRegularDistribution : OrderProhibitionStatusAtTheRegularDistribution
  reserved11 : Alpha 11
  deriving DecidableEq, Repr

namespace IssueInformationMessage

def encode (message : IssueInformationMessage) : List UInt8 :=
  Alpha.encode message.reserved2
    ++ (Alpha.encode message.serialNo
    ++ (Alpha.encode message.applicableBusinessDay
    ++ (Alpha.encode message.reserved1
    ++ (Alpha.encode message.issueName
    ++ (Alpha.encode message.securityTypeEtcIdentificationCode
    ++ (IsinFlag.encode message.isinFlag
    ++ (Alpha.encode message.newSecurityCode
    ++ (Alpha.encode message.industryCode
    ++ (NewListingFlag.encode message.newListingFlag
    ++ (WhenIssuedTransactionFlag.encode message.whenIssuedTransactionFlag
    ++ (ShortSellingPriceRestrictionAppliedFlagAtTheRegularDistribution.encode message.shortSellingPriceRestrictionAppliedFlagAtTheRegularDistribution
    ++ (LoanMarginFlag.encode message.loanMarginFlag
    ++ (Alpha.encode message.exDividendExRightFlag
    ++ (SecuritiesToBeDelistedUnderSupervisionClassification.encode message.securitiesToBeDelistedUnderSupervisionClassification
    ++ (Alpha.encode message.reserved5
    ++ (Alpha.encode message.unitOfTrading
    ++ (IndexConstituentIssue.encode message.indexConstituentIssue
    ++ (OrderProhibitionStatusAtTheRegularDistribution.encode message.orderProhibitionStatusAtTheRegularDistribution
    ++ (Alpha.encode message.reserved11)))))))))))))))))))

def decode (bytes : List UInt8) : Option (IssueInformationMessage × List UInt8) := do
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (serialNo, bytes) ← Alpha.decode 6 bytes
  let (applicableBusinessDay, bytes) ← Alpha.decode 8 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (issueName, bytes) ← Alpha.decode 20 bytes
  let (securityTypeEtcIdentificationCode, bytes) ← Alpha.decode 2 bytes
  let (isinFlag, bytes) ← IsinFlag.decode bytes
  let (newSecurityCode, bytes) ← Alpha.decode 12 bytes
  let (industryCode, bytes) ← Alpha.decode 4 bytes
  let (newListingFlag, bytes) ← NewListingFlag.decode bytes
  let (whenIssuedTransactionFlag, bytes) ← WhenIssuedTransactionFlag.decode bytes
  let (shortSellingPriceRestrictionAppliedFlagAtTheRegularDistribution, bytes) ← ShortSellingPriceRestrictionAppliedFlagAtTheRegularDistribution.decode bytes
  let (loanMarginFlag, bytes) ← LoanMarginFlag.decode bytes
  let (exDividendExRightFlag, bytes) ← Alpha.decode 2 bytes
  let (securitiesToBeDelistedUnderSupervisionClassification, bytes) ← SecuritiesToBeDelistedUnderSupervisionClassification.decode bytes
  let (reserved5, bytes) ← Alpha.decode 5 bytes
  let (unitOfTrading, bytes) ← Alpha.decode 14 bytes
  let (indexConstituentIssue, bytes) ← IndexConstituentIssue.decode bytes
  let (orderProhibitionStatusAtTheRegularDistribution, bytes) ← OrderProhibitionStatusAtTheRegularDistribution.decode bytes
  let (reserved11, bytes) ← Alpha.decode 11 bytes
  pure ({ reserved2, serialNo, applicableBusinessDay, reserved1, issueName, securityTypeEtcIdentificationCode, isinFlag, newSecurityCode, industryCode, newListingFlag, whenIssuedTransactionFlag, shortSellingPriceRestrictionAppliedFlagAtTheRegularDistribution, loanMarginFlag, exDividendExRightFlag, securitiesToBeDelistedUnderSupervisionClassification, reserved5, unitOfTrading, indexConstituentIssue, orderProhibitionStatusAtTheRegularDistribution, reserved11 }, bytes)

@[simp] theorem encode_length (message : IssueInformationMessage) : (encode message).length = 123 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, IsinFlag.encode_length, NewListingFlag.encode_length, WhenIssuedTransactionFlag.encode_length, ShortSellingPriceRestrictionAppliedFlagAtTheRegularDistribution.encode_length, LoanMarginFlag.encode_length, SecuritiesToBeDelistedUnderSupervisionClassification.encode_length, IndexConstituentIssue.encode_length, OrderProhibitionStatusAtTheRegularDistribution.encode_length]

theorem encode_length_pos (message : IssueInformationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IssueInformationMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, IsinFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NewListingFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, WhenIssuedTransactionFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ShortSellingPriceRestrictionAppliedFlagAtTheRegularDistribution.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LoanMarginFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecuritiesToBeDelistedUnderSupervisionClassification.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, IndexConstituentIssue.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderProhibitionStatusAtTheRegularDistribution.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end IssueInformationMessage

/-- Base Price: 16 bytes -/
structure BasePrice where
  unitFlag : UnitFlag
  price : Alpha 14
  sign : Sign
  deriving DecidableEq, Repr

namespace BasePrice

def encode (message : BasePrice) : List UInt8 :=
  UnitFlag.encode message.unitFlag
    ++ (Alpha.encode message.price
    ++ (Sign.encode message.sign))

def decode (bytes : List UInt8) : Option (BasePrice × List UInt8) := do
  let (unitFlag, bytes) ← UnitFlag.decode bytes
  let (price, bytes) ← Alpha.decode 14 bytes
  let (sign, bytes) ← Sign.decode bytes
  pure ({ unitFlag, price, sign }, bytes)

@[simp] theorem encode_length (message : BasePrice) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, UnitFlag.encode_length, Alpha.encode_length, Sign.encode_length]

theorem encode_length_pos (message : BasePrice) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BasePrice) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, UnitFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Sign.decode_encode, some_bind]
  rfl

end BasePrice

/-- Limit Price Maximum: 16 bytes -/
structure LimitPriceMaximum where
  unitFlag : UnitFlag
  price : Alpha 14
  sign : Sign
  deriving DecidableEq, Repr

namespace LimitPriceMaximum

def encode (message : LimitPriceMaximum) : List UInt8 :=
  UnitFlag.encode message.unitFlag
    ++ (Alpha.encode message.price
    ++ (Sign.encode message.sign))

def decode (bytes : List UInt8) : Option (LimitPriceMaximum × List UInt8) := do
  let (unitFlag, bytes) ← UnitFlag.decode bytes
  let (price, bytes) ← Alpha.decode 14 bytes
  let (sign, bytes) ← Sign.decode bytes
  pure ({ unitFlag, price, sign }, bytes)

@[simp] theorem encode_length (message : LimitPriceMaximum) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, UnitFlag.encode_length, Alpha.encode_length, Sign.encode_length]

theorem encode_length_pos (message : LimitPriceMaximum) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LimitPriceMaximum) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, UnitFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Sign.decode_encode, some_bind]
  rfl

end LimitPriceMaximum

/-- Limit Price Minimum: 16 bytes -/
structure LimitPriceMinimum where
  unitFlag : UnitFlag
  price : Alpha 14
  sign : Sign
  deriving DecidableEq, Repr

namespace LimitPriceMinimum

def encode (message : LimitPriceMinimum) : List UInt8 :=
  UnitFlag.encode message.unitFlag
    ++ (Alpha.encode message.price
    ++ (Sign.encode message.sign))

def decode (bytes : List UInt8) : Option (LimitPriceMinimum × List UInt8) := do
  let (unitFlag, bytes) ← UnitFlag.decode bytes
  let (price, bytes) ← Alpha.decode 14 bytes
  let (sign, bytes) ← Sign.decode bytes
  pure ({ unitFlag, price, sign }, bytes)

@[simp] theorem encode_length (message : LimitPriceMinimum) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, UnitFlag.encode_length, Alpha.encode_length, Sign.encode_length]

theorem encode_length_pos (message : LimitPriceMinimum) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LimitPriceMinimum) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, UnitFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Sign.decode_encode, some_bind]
  rfl

end LimitPriceMinimum

/-- Base Price Information Message: 66 bytes -/
structure BasePriceInformationMessage where
  reserved2 : Alpha 2
  basedBusinessDay : Alpha 8
  basePrice : BasePrice
  limitPriceMaximum : LimitPriceMaximum
  limitPriceMinimum : LimitPriceMinimum
  basePricePriceOfTheMiddleOfTheBook : BasePricePriceOfTheMiddleOfTheBook
  numberOfTickSizeTable : Alpha 2
  reserved1 : Alpha 1
  reserved4 : Alpha 4
  deriving DecidableEq, Repr

namespace BasePriceInformationMessage

def encode (message : BasePriceInformationMessage) : List UInt8 :=
  Alpha.encode message.reserved2
    ++ (Alpha.encode message.basedBusinessDay
    ++ (BasePrice.encode message.basePrice
    ++ (LimitPriceMaximum.encode message.limitPriceMaximum
    ++ (LimitPriceMinimum.encode message.limitPriceMinimum
    ++ (BasePricePriceOfTheMiddleOfTheBook.encode message.basePricePriceOfTheMiddleOfTheBook
    ++ (Alpha.encode message.numberOfTickSizeTable
    ++ (Alpha.encode message.reserved1
    ++ (Alpha.encode message.reserved4))))))))

def decode (bytes : List UInt8) : Option (BasePriceInformationMessage × List UInt8) := do
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (basedBusinessDay, bytes) ← Alpha.decode 8 bytes
  let (basePrice, bytes) ← BasePrice.decode bytes
  let (limitPriceMaximum, bytes) ← LimitPriceMaximum.decode bytes
  let (limitPriceMinimum, bytes) ← LimitPriceMinimum.decode bytes
  let (basePricePriceOfTheMiddleOfTheBook, bytes) ← BasePricePriceOfTheMiddleOfTheBook.decode bytes
  let (numberOfTickSizeTable, bytes) ← Alpha.decode 2 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  pure ({ reserved2, basedBusinessDay, basePrice, limitPriceMaximum, limitPriceMinimum, basePricePriceOfTheMiddleOfTheBook, numberOfTickSizeTable, reserved1, reserved4 }, bytes)

@[simp] theorem encode_length (message : BasePriceInformationMessage) : (encode message).length = 66 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, BasePrice.encode_length, LimitPriceMaximum.encode_length, LimitPriceMinimum.encode_length, BasePricePriceOfTheMiddleOfTheBook.encode_length]

theorem encode_length_pos (message : BasePriceInformationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BasePriceInformationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BasePrice.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LimitPriceMaximum.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LimitPriceMinimum.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BasePricePriceOfTheMiddleOfTheBook.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BasePriceInformationMessage

/-- Multicast Group Number Information Message: 14 bytes -/
structure MulticastGroupNumberInformationMessage where
  reserved2 : Alpha 2
  applicableBusinessDay : Alpha 8
  issueMulticastGroupNumber : Alpha 3
  reserved1 : Alpha 1
  deriving DecidableEq, Repr

namespace MulticastGroupNumberInformationMessage

def encode (message : MulticastGroupNumberInformationMessage) : List UInt8 :=
  Alpha.encode message.reserved2
    ++ (Alpha.encode message.applicableBusinessDay
    ++ (Alpha.encode message.issueMulticastGroupNumber
    ++ (Alpha.encode message.reserved1)))

def decode (bytes : List UInt8) : Option (MulticastGroupNumberInformationMessage × List UInt8) := do
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (applicableBusinessDay, bytes) ← Alpha.decode 8 bytes
  let (issueMulticastGroupNumber, bytes) ← Alpha.decode 3 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  pure ({ reserved2, applicableBusinessDay, issueMulticastGroupNumber, reserved1 }, bytes)

@[simp] theorem encode_length (message : MulticastGroupNumberInformationMessage) : (encode message).length = 14 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : MulticastGroupNumberInformationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MulticastGroupNumberInformationMessage) (rest : List UInt8) :
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

end MulticastGroupNumberInformationMessage

/-- Control Message: 10 bytes -/
structure ControlMessage where
  reserved2 : Alpha 2
  testModeFlag : TestModeFlag
  startEndFlag : StartEndFlag
  time : Alpha 6
  deriving DecidableEq, Repr

namespace ControlMessage

def encode (message : ControlMessage) : List UInt8 :=
  Alpha.encode message.reserved2
    ++ (TestModeFlag.encode message.testModeFlag
    ++ (StartEndFlag.encode message.startEndFlag
    ++ (Alpha.encode message.time)))

def decode (bytes : List UInt8) : Option (ControlMessage × List UInt8) := do
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (testModeFlag, bytes) ← TestModeFlag.decode bytes
  let (startEndFlag, bytes) ← StartEndFlag.decode bytes
  let (time, bytes) ← Alpha.decode 6 bytes
  pure ({ reserved2, testModeFlag, startEndFlag, time }, bytes)

@[simp] theorem encode_length (message : ControlMessage) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, TestModeFlag.encode_length, StartEndFlag.encode_length]

theorem encode_length_pos (message : ControlMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ControlMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TestModeFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StartEndFlag.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ControlMessage

/-- Any Payload, selected by Tag ID -/
inductive Payload where
  | issueInformationMessage (message : IssueInformationMessage) -- "II" 0x4949
  | basePriceInformationMessage (message : BasePriceInformationMessage) -- "BP" 0x4250
  | multicastGroupNumberInformationMessage (message : MulticastGroupNumberInformationMessage) -- "MG" 0x4D47
  | controlMessage (message : ControlMessage) -- "LC" 0x4C43
  deriving DecidableEq, Repr

namespace Payload

/-- The Tag ID each message is sent under -/
def tag : Payload → BitVec 16
  | .issueInformationMessage _ => 18761
  | .basePriceInformationMessage _ => 16976
  | .multicastGroupNumberInformationMessage _ => 19783
  | .controlMessage _ => 19523

def encode : Payload → List UInt8
  | .issueInformationMessage message => IssueInformationMessage.encode message
  | .basePriceInformationMessage message => BasePriceInformationMessage.encode message
  | .multicastGroupNumberInformationMessage message => MulticastGroupNumberInformationMessage.encode message
  | .controlMessage message => ControlMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 123 := by
  cases message with
  | issueInformationMessage inner =>
    simp only [encode, IssueInformationMessage.encode_length]
    omega
  | basePriceInformationMessage inner =>
    simp only [encode, BasePriceInformationMessage.encode_length]
    omega
  | multicastGroupNumberInformationMessage inner =>
    simp only [encode, MulticastGroupNumberInformationMessage.encode_length]
    omega
  | controlMessage inner =>
    simp only [encode, ControlMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 18761 then (IssueInformationMessage.decode bytes).map fun (message, rest) => (.issueInformationMessage message, rest)
  else if tag = 16976 then (BasePriceInformationMessage.decode bytes).map fun (message, rest) => (.basePriceInformationMessage message, rest)
  else if tag = 19783 then (MulticastGroupNumberInformationMessage.decode bytes).map fun (message, rest) => (.multicastGroupNumberInformationMessage message, rest)
  else if tag = 19523 then (ControlMessage.decode bytes).map fun (message, rest) => (.controlMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Tag Information -/
structure TagInformation where
  payload : Payload
  separationOfTag : BitVec 8
  deriving DecidableEq, Repr

namespace TagInformation

def encode (message : TagInformation) : List UInt8 :=
  encodeUInt 2 (Payload.tag message.payload)
    ++ (Payload.encode message.payload
    ++ (encodeUInt 1 message.separationOfTag))

def decode (bytes : List UInt8) : Option (TagInformation × List UInt8) := do
  let (tagId, bytes) ← decodeUInt 2 bytes
  let (payload, bytes) ← Payload.decode tagId bytes
  let (separationOfTag, bytes) ← decodeUInt 1 bytes
  pure ({ payload, separationOfTag }, bytes)

theorem encode_length_pos (message : TagInformation) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TagInformation) : (encode message).length ≤ 126 := by
  unfold encode
  cases message.payload with
  | issueInformationMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, IssueInformationMessage.encode_length]
    omega
  | basePriceInformationMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, BasePriceInformationMessage.encode_length]
    omega
  | multicastGroupNumberInformationMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MulticastGroupNumberInformationMessage.encode_length]
    omega
  | controlMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ControlMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : TagInformation) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Payload.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TagInformation

/-- Udp Packet -/
structure UdpPacket where
  startOfMessage : BitVec 8
  serviceHeader : ServiceHeader
  separationBetweenServiceHeaderAndDataSection : BitVec 8
  tagInformation : List TagInformation
  deriving DecidableEq, Repr

namespace UdpPacket

def encode (message : UdpPacket) : List UInt8 :=
  encodeUInt 1 message.startOfMessage
    ++ (ServiceHeader.encode message.serviceHeader
    ++ (encodeUInt 1 message.separationBetweenServiceHeaderAndDataSection
    ++ (encodeMany TagInformation.encode message.tagInformation)))

def decode (bytes : List UInt8) : Option UdpPacket := do
  let (startOfMessage, bytes) ← decodeUInt 1 bytes
  let (serviceHeader, bytes) ← ServiceHeader.decode bytes
  let (separationBetweenServiceHeaderAndDataSection, bytes) ← decodeUInt 1 bytes
  let tagInformation ← decodeAll TagInformation.decode bytes.length bytes
  pure { startOfMessage, serviceHeader, separationBetweenServiceHeaderAndDataSection, tagInformation }

theorem encode_length_pos (message : UdpPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

theorem decode_encode (message : UdpPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ServiceHeader.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeAll_encodeMany TagInformation.encode TagInformation.decode TagInformation.decode_encode TagInformation.encode_length_pos message.tagInformation _ (encodeMany_length_ge TagInformation.encode TagInformation.encode_length_pos message.tagInformation), some_bind]
  rfl

end UdpPacket

end Omi.JpxTseequitiesIssuebasicinformationFlexV195
