import Wire

/-!
# Japan Exchange Group Standard v19.5

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.JpxFseequitiesStandardFlexV195

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

/-- Change Flag: one byte code -/
def ChangeFlag.codes : List UInt8 :=
  [0x31, 0x20]

inductive ChangeFlag where
  | changed -- Changed
  | notChanged -- Not Changed
  | unlisted (byte : { byte : UInt8 // byte ∉ ChangeFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ChangeFlag

def toByte : ChangeFlag → UInt8
  | .changed => 0x31
  | .notChanged => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ChangeFlag :=
  if byte = 0x31 then .changed
  else .notChanged

def ofByte (byte : UInt8) : ChangeFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ChangeFlag) : ofByte value.toByte = value := by
  cases value with
  | changed => decide
  | notChanged => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ChangeFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ChangeFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ChangeFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ChangeFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ChangeFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ChangeFlag

/-- Short Selling Regulation Flag: one byte code -/
def ShortSellingRegulationFlag.codes : List UInt8 :=
  [0x30, 0x31]

inductive ShortSellingRegulationFlag where
  | shortSellingRegulationDoesNotApply -- Short Selling Regulation Does Not Apply
  | shortSellingRegulationIsApplied -- Short Selling Regulation Is Applied
  | unlisted (byte : { byte : UInt8 // byte ∉ ShortSellingRegulationFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ShortSellingRegulationFlag

def toByte : ShortSellingRegulationFlag → UInt8
  | .shortSellingRegulationDoesNotApply => 0x30
  | .shortSellingRegulationIsApplied => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ShortSellingRegulationFlag :=
  if byte = 0x30 then .shortSellingRegulationDoesNotApply
  else .shortSellingRegulationIsApplied

def ofByte (byte : UInt8) : ShortSellingRegulationFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ShortSellingRegulationFlag) : ofByte value.toByte = value := by
  cases value with
  | shortSellingRegulationDoesNotApply => decide
  | shortSellingRegulationIsApplied => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ShortSellingRegulationFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ShortSellingRegulationFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ShortSellingRegulationFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ShortSellingRegulationFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ShortSellingRegulationFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ShortSellingRegulationFlag

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

/-- Limit Up Flag: one byte code -/
def LimitUpFlag.codes : List UInt8 :=
  [0x31, 0x20]

inductive LimitUpFlag where
  | limitUp -- Limit Up
  | otherThanTheAbove -- Other Than The Above
  | unlisted (byte : { byte : UInt8 // byte ∉ LimitUpFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LimitUpFlag

def toByte : LimitUpFlag → UInt8
  | .limitUp => 0x31
  | .otherThanTheAbove => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LimitUpFlag :=
  if byte = 0x31 then .limitUp
  else .otherThanTheAbove

def ofByte (byte : UInt8) : LimitUpFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LimitUpFlag) : ofByte value.toByte = value := by
  cases value with
  | limitUp => decide
  | otherThanTheAbove => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LimitUpFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LimitUpFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LimitUpFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : LimitUpFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : LimitUpFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LimitUpFlag

/-- Limit Down Flag: one byte code -/
def LimitDownFlag.codes : List UInt8 :=
  [0x31, 0x20]

inductive LimitDownFlag where
  | limitDown -- Limit Down
  | otherThanTheAbove -- Other Than The Above
  | unlisted (byte : { byte : UInt8 // byte ∉ LimitDownFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LimitDownFlag

def toByte : LimitDownFlag → UInt8
  | .limitDown => 0x31
  | .otherThanTheAbove => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LimitDownFlag :=
  if byte = 0x31 then .limitDown
  else .otherThanTheAbove

def ofByte (byte : UInt8) : LimitDownFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LimitDownFlag) : ofByte value.toByte = value := by
  cases value with
  | limitDown => decide
  | otherThanTheAbove => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LimitDownFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LimitDownFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LimitDownFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : LimitDownFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : LimitDownFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LimitDownFlag

/-- Current Change Flag: one byte code -/
def CurrentChangeFlag.codes : List UInt8 :=
  [0x31, 0x32, 0x33, 0x34, 0x20]

inductive CurrentChangeFlag where
  | changedGoingUp -- Changed Going Up
  | changedGoingDown -- Changed Going Down
  | changedSame -- Changed Same
  | changedOtherThanAbove -- Changed Other Than Above
  | otherThanTheAbove -- Other Than The Above
  | unlisted (byte : { byte : UInt8 // byte ∉ CurrentChangeFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CurrentChangeFlag

def toByte : CurrentChangeFlag → UInt8
  | .changedGoingUp => 0x31
  | .changedGoingDown => 0x32
  | .changedSame => 0x33
  | .changedOtherThanAbove => 0x34
  | .otherThanTheAbove => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CurrentChangeFlag :=
  if byte = 0x31 then .changedGoingUp
  else if byte = 0x32 then .changedGoingDown
  else if byte = 0x33 then .changedSame
  else if byte = 0x34 then .changedOtherThanAbove
  else .otherThanTheAbove

def ofByte (byte : UInt8) : CurrentChangeFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CurrentChangeFlag) : ofByte value.toByte = value := by
  cases value with
  | changedGoingUp => decide
  | changedGoingDown => decide
  | changedSame => decide
  | changedOtherThanAbove => decide
  | otherThanTheAbove => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CurrentChangeFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CurrentChangeFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CurrentChangeFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CurrentChangeFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CurrentChangeFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CurrentChangeFlag

/-- Stq Reference Point Flag: one byte code -/
def StqReferencePointFlag.codes : List UInt8 :=
  [0x31, 0x20]

inductive StqReferencePointFlag where
  | referenceExecutionSetByThisTrade -- Reference Execution Set By This Trade
  | otherThanTheAbove -- Other Than The Above
  | unlisted (byte : { byte : UInt8 // byte ∉ StqReferencePointFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace StqReferencePointFlag

def toByte : StqReferencePointFlag → UInt8
  | .referenceExecutionSetByThisTrade => 0x31
  | .otherThanTheAbove => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : StqReferencePointFlag :=
  if byte = 0x31 then .referenceExecutionSetByThisTrade
  else .otherThanTheAbove

def ofByte (byte : UInt8) : StqReferencePointFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : StqReferencePointFlag) : ofByte value.toByte = value := by
  cases value with
  | referenceExecutionSetByThisTrade => decide
  | otherThanTheAbove => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : StqReferencePointFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (StqReferencePointFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : StqReferencePointFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : StqReferencePointFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : StqReferencePointFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end StqReferencePointFlag

/-- Closing Price Input Flag: one byte code -/
def ClosingPriceInputFlag.codes : List UInt8 :=
  [0x31, 0x32, 0x20]

inductive ClosingPriceInputFlag where
  | tradeNotEstablishedAtClosing -- Trade Not Established At Closing
  | tradeEstablishedWithClosing -- Trade Established With Closing
  | otherThanTheAbove -- Other Than The Above
  | unlisted (byte : { byte : UInt8 // byte ∉ ClosingPriceInputFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ClosingPriceInputFlag

def toByte : ClosingPriceInputFlag → UInt8
  | .tradeNotEstablishedAtClosing => 0x31
  | .tradeEstablishedWithClosing => 0x32
  | .otherThanTheAbove => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ClosingPriceInputFlag :=
  if byte = 0x31 then .tradeNotEstablishedAtClosing
  else if byte = 0x32 then .tradeEstablishedWithClosing
  else .otherThanTheAbove

def ofByte (byte : UInt8) : ClosingPriceInputFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ClosingPriceInputFlag) : ofByte value.toByte = value := by
  cases value with
  | tradeNotEstablishedAtClosing => decide
  | tradeEstablishedWithClosing => decide
  | otherThanTheAbove => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ClosingPriceInputFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ClosingPriceInputFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ClosingPriceInputFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ClosingPriceInputFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ClosingPriceInputFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ClosingPriceInputFlag

/-- Quote Flag: one byte code -/
def QuoteFlag.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x20]

inductive QuoteFlag where
  | quoteBeforeOpening -- Quote Before Opening
  | generalQuote -- General Quote
  | generalQuoteUnderTransaction -- General Quote Under Transaction
  | specialQuote -- Special Quote
  | sequentialTradeQuote -- Sequential Trade Quote
  | temporaryQuoteAtTheBeginningOfPreClosing -- Temporary Quote At The Beginning Of Pre Closing
  | quoteAfterSpecialExecution -- Quote After Special Execution
  | specialQuoteBeforeTradingHalt -- Special Quote Before Trading Halt
  | sequentialTradeQuoteBeforeTradingHalt -- Sequential Trade Quote Before Trading Halt
  | noQuotesOrAllQuotesAreCancelled -- No Quotes Or All Quotes Are Cancelled
  | unlisted (byte : { byte : UInt8 // byte ∉ QuoteFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace QuoteFlag

def toByte : QuoteFlag → UInt8
  | .quoteBeforeOpening => 0x30
  | .generalQuote => 0x31
  | .generalQuoteUnderTransaction => 0x32
  | .specialQuote => 0x33
  | .sequentialTradeQuote => 0x34
  | .temporaryQuoteAtTheBeginningOfPreClosing => 0x35
  | .quoteAfterSpecialExecution => 0x36
  | .specialQuoteBeforeTradingHalt => 0x37
  | .sequentialTradeQuoteBeforeTradingHalt => 0x38
  | .noQuotesOrAllQuotesAreCancelled => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : QuoteFlag :=
  if byte = 0x30 then .quoteBeforeOpening
  else if byte = 0x31 then .generalQuote
  else if byte = 0x32 then .generalQuoteUnderTransaction
  else if byte = 0x33 then .specialQuote
  else if byte = 0x34 then .sequentialTradeQuote
  else if byte = 0x35 then .temporaryQuoteAtTheBeginningOfPreClosing
  else if byte = 0x36 then .quoteAfterSpecialExecution
  else if byte = 0x37 then .specialQuoteBeforeTradingHalt
  else if byte = 0x38 then .sequentialTradeQuoteBeforeTradingHalt
  else .noQuotesOrAllQuotesAreCancelled

def ofByte (byte : UInt8) : QuoteFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : QuoteFlag) : ofByte value.toByte = value := by
  cases value with
  | quoteBeforeOpening => decide
  | generalQuote => decide
  | generalQuoteUnderTransaction => decide
  | specialQuote => decide
  | sequentialTradeQuote => decide
  | temporaryQuoteAtTheBeginningOfPreClosing => decide
  | quoteAfterSpecialExecution => decide
  | specialQuoteBeforeTradingHalt => decide
  | sequentialTradeQuoteBeforeTradingHalt => decide
  | noQuotesOrAllQuotesAreCancelled => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : QuoteFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (QuoteFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : QuoteFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : QuoteFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : QuoteFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end QuoteFlag

/-- Trading Volume Turnover Unit Flag: one byte code -/
def TradingVolumeTurnoverUnitFlag.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x20]

inductive TradingVolumeTurnoverUnitFlag where
  | one -- One
  | ten -- Ten
  | hundred -- Hundred
  | thousand -- Thousand
  | tenThousand -- Ten Thousand
  | hundredThousand -- Hundred Thousand
  | million -- Million
  | tenMillion -- Ten Million
  | hundredMillion -- Hundred Million
  | billion -- Billion
  | noNumericalValue -- No Numerical Value
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingVolumeTurnoverUnitFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingVolumeTurnoverUnitFlag

def toByte : TradingVolumeTurnoverUnitFlag → UInt8
  | .one => 0x30
  | .ten => 0x31
  | .hundred => 0x32
  | .thousand => 0x33
  | .tenThousand => 0x34
  | .hundredThousand => 0x35
  | .million => 0x36
  | .tenMillion => 0x37
  | .hundredMillion => 0x38
  | .billion => 0x39
  | .noNumericalValue => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingVolumeTurnoverUnitFlag :=
  if byte = 0x30 then .one
  else if byte = 0x31 then .ten
  else if byte = 0x32 then .hundred
  else if byte = 0x33 then .thousand
  else if byte = 0x34 then .tenThousand
  else if byte = 0x35 then .hundredThousand
  else if byte = 0x36 then .million
  else if byte = 0x37 then .tenMillion
  else if byte = 0x38 then .hundredMillion
  else if byte = 0x39 then .billion
  else .noNumericalValue

def ofByte (byte : UInt8) : TradingVolumeTurnoverUnitFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingVolumeTurnoverUnitFlag) : ofByte value.toByte = value := by
  cases value with
  | one => decide
  | ten => decide
  | hundred => decide
  | thousand => decide
  | tenThousand => decide
  | hundredThousand => decide
  | million => decide
  | tenMillion => decide
  | hundredMillion => decide
  | billion => decide
  | noNumericalValue => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradingVolumeTurnoverUnitFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradingVolumeTurnoverUnitFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradingVolumeTurnoverUnitFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TradingVolumeTurnoverUnitFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TradingVolumeTurnoverUnitFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradingVolumeTurnoverUnitFlag

/-- Lot Size Unit Flag: one byte code -/
def LotSizeUnitFlag.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33, 0x34, 0x20]

inductive LotSizeUnitFlag where
  | toTheFourthDecimalPlace -- To The Fourth Decimal Place
  | toTheThirdDecimalPlace -- To The Third Decimal Place
  | toTheSecondDecimalPlace -- To The Second Decimal Place
  | toTheFirstDecimalPlace -- To The First Decimal Place
  | noDecimalPlaces -- No Decimal Places
  | noNumericalValue -- No Numerical Value
  | unlisted (byte : { byte : UInt8 // byte ∉ LotSizeUnitFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LotSizeUnitFlag

def toByte : LotSizeUnitFlag → UInt8
  | .toTheFourthDecimalPlace => 0x30
  | .toTheThirdDecimalPlace => 0x31
  | .toTheSecondDecimalPlace => 0x32
  | .toTheFirstDecimalPlace => 0x33
  | .noDecimalPlaces => 0x34
  | .noNumericalValue => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LotSizeUnitFlag :=
  if byte = 0x30 then .toTheFourthDecimalPlace
  else if byte = 0x31 then .toTheThirdDecimalPlace
  else if byte = 0x32 then .toTheSecondDecimalPlace
  else if byte = 0x33 then .toTheFirstDecimalPlace
  else if byte = 0x34 then .noDecimalPlaces
  else .noNumericalValue

def ofByte (byte : UInt8) : LotSizeUnitFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LotSizeUnitFlag) : ofByte value.toByte = value := by
  cases value with
  | toTheFourthDecimalPlace => decide
  | toTheThirdDecimalPlace => decide
  | toTheSecondDecimalPlace => decide
  | toTheFirstDecimalPlace => decide
  | noDecimalPlaces => decide
  | noNumericalValue => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LotSizeUnitFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LotSizeUnitFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LotSizeUnitFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : LotSizeUnitFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : LotSizeUnitFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LotSizeUnitFlag

/-- Test Mode Flag: one byte code -/
def TestModeFlag.codes : List UInt8 :=
  [0x31, 0x32]

inductive TestModeFlag where
  | productionOperation -- Production Operation
  | testOperation -- Test Operation
  | unlisted (byte : { byte : UInt8 // byte ∉ TestModeFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TestModeFlag

def toByte : TestModeFlag → UInt8
  | .productionOperation => 0x31
  | .testOperation => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TestModeFlag :=
  if byte = 0x31 then .productionOperation
  else .testOperation

def ofByte (byte : UInt8) : TestModeFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TestModeFlag) : ofByte value.toByte = value := by
  cases value with
  | productionOperation => decide
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
  | healthCheckControl -- Health Check Control
  | unlisted (byte : { byte : UInt8 // byte ∉ StartEndFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace StartEndFlag

def toByte : StartEndFlag → UInt8
  | .start => 0x31
  | .end_ => 0x32
  | .healthCheckControl => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : StartEndFlag :=
  if byte = 0x31 then .start
  else if byte = 0x32 then .end_
  else .healthCheckControl

def ofByte (byte : UInt8) : StartEndFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : StartEndFlag) : ofByte value.toByte = value := by
  cases value with
  | start => decide
  | end_ => decide
  | healthCheckControl => decide
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

/-- Update No Message: 8 bytes -/
structure UpdateNoMessage where
  updateNo : Alpha 8
  deriving DecidableEq, Repr

namespace UpdateNoMessage

def encode (message : UpdateNoMessage) : List UInt8 :=
  Alpha.encode message.updateNo

def decode (bytes : List UInt8) : Option (UpdateNoMessage × List UInt8) := do
  let (updateNo, bytes) ← Alpha.decode 8 bytes
  pure ({ updateNo }, bytes)

@[simp] theorem encode_length (message : UpdateNoMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : UpdateNoMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UpdateNoMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end UpdateNoMessage

/-- Status Information: 5 bytes -/
structure StatusInformation where
  issueStatus : Alpha 2
  statusFlag : Alpha 2
  shortSellingRegulationFlag : ShortSellingRegulationFlag
  deriving DecidableEq, Repr

namespace StatusInformation

def encode (message : StatusInformation) : List UInt8 :=
  Alpha.encode message.issueStatus
    ++ (Alpha.encode message.statusFlag
    ++ (ShortSellingRegulationFlag.encode message.shortSellingRegulationFlag))

def decode (bytes : List UInt8) : Option (StatusInformation × List UInt8) := do
  let (issueStatus, bytes) ← Alpha.decode 2 bytes
  let (statusFlag, bytes) ← Alpha.decode 2 bytes
  let (shortSellingRegulationFlag, bytes) ← ShortSellingRegulationFlag.decode bytes
  pure ({ issueStatus, statusFlag, shortSellingRegulationFlag }, bytes)

@[simp] theorem encode_length (message : StatusInformation) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ShortSellingRegulationFlag.encode_length]

theorem encode_length_pos (message : StatusInformation) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StatusInformation) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [ShortSellingRegulationFlag.decode_encode, some_bind]
  rfl

end StatusInformation

/-- Status Information Message: 24 bytes -/
structure StatusInformationMessage where
  reserved2 : Alpha 2
  changeFlag : ChangeFlag
  statusInformation : StatusInformation
  timeC12 : Alpha 12
  reserved4 : Alpha 4
  deriving DecidableEq, Repr

namespace StatusInformationMessage

def encode (message : StatusInformationMessage) : List UInt8 :=
  Alpha.encode message.reserved2
    ++ (ChangeFlag.encode message.changeFlag
    ++ (StatusInformation.encode message.statusInformation
    ++ (Alpha.encode message.timeC12
    ++ (Alpha.encode message.reserved4))))

def decode (bytes : List UInt8) : Option (StatusInformationMessage × List UInt8) := do
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (changeFlag, bytes) ← ChangeFlag.decode bytes
  let (statusInformation, bytes) ← StatusInformation.decode bytes
  let (timeC12, bytes) ← Alpha.decode 12 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  pure ({ reserved2, changeFlag, statusInformation, timeC12, reserved4 }, bytes)

@[simp] theorem encode_length (message : StatusInformationMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ChangeFlag.encode_length, StatusInformation.encode_length]

theorem encode_length_pos (message : StatusInformationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StatusInformationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ChangeFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StatusInformation.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StatusInformationMessage

/-- Price: 16 bytes -/
structure Price where
  unitFlag : UnitFlag
  priceC14 : Alpha 14
  sign : Sign
  deriving DecidableEq, Repr

namespace Price

def encode (message : Price) : List UInt8 :=
  UnitFlag.encode message.unitFlag
    ++ (Alpha.encode message.priceC14
    ++ (Sign.encode message.sign))

def decode (bytes : List UInt8) : Option (Price × List UInt8) := do
  let (unitFlag, bytes) ← UnitFlag.decode bytes
  let (priceC14, bytes) ← Alpha.decode 14 bytes
  let (sign, bytes) ← Sign.decode bytes
  pure ({ unitFlag, priceC14, sign }, bytes)

@[simp] theorem encode_length (message : Price) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, UnitFlag.encode_length, Alpha.encode_length, Sign.encode_length]

theorem encode_length_pos (message : Price) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Price) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, UnitFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Sign.decode_encode, some_bind]
  rfl

end Price

/-- Open: 23 bytes -/
structure Open where
  price : Price
  timeC6 : Alpha 6
  changeFlag : ChangeFlag
  deriving DecidableEq, Repr

namespace Open

def encode (message : Open) : List UInt8 :=
  Price.encode message.price
    ++ (Alpha.encode message.timeC6
    ++ (ChangeFlag.encode message.changeFlag))

def decode (bytes : List UInt8) : Option (Open × List UInt8) := do
  let (price, bytes) ← Price.decode bytes
  let (timeC6, bytes) ← Alpha.decode 6 bytes
  let (changeFlag, bytes) ← ChangeFlag.decode bytes
  pure ({ price, timeC6, changeFlag }, bytes)

@[simp] theorem encode_length (message : Open) : (encode message).length = 23 := by
  unfold encode
  simp only [List.length_append, Price.encode_length, Alpha.encode_length, ChangeFlag.encode_length]

theorem encode_length_pos (message : Open) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Open) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Price.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [ChangeFlag.decode_encode, some_bind]
  rfl

end Open

/-- High: 24 bytes -/
structure High where
  limitUpFlag : LimitUpFlag
  price : Price
  timeC6 : Alpha 6
  changeFlag : ChangeFlag
  deriving DecidableEq, Repr

namespace High

def encode (message : High) : List UInt8 :=
  LimitUpFlag.encode message.limitUpFlag
    ++ (Price.encode message.price
    ++ (Alpha.encode message.timeC6
    ++ (ChangeFlag.encode message.changeFlag)))

def decode (bytes : List UInt8) : Option (High × List UInt8) := do
  let (limitUpFlag, bytes) ← LimitUpFlag.decode bytes
  let (price, bytes) ← Price.decode bytes
  let (timeC6, bytes) ← Alpha.decode 6 bytes
  let (changeFlag, bytes) ← ChangeFlag.decode bytes
  pure ({ limitUpFlag, price, timeC6, changeFlag }, bytes)

@[simp] theorem encode_length (message : High) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, LimitUpFlag.encode_length, Price.encode_length, Alpha.encode_length, ChangeFlag.encode_length]

theorem encode_length_pos (message : High) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : High) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LimitUpFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Price.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [ChangeFlag.decode_encode, some_bind]
  rfl

end High

/-- Low: 24 bytes -/
structure Low where
  limitDownFlag : LimitDownFlag
  price : Price
  timeC6 : Alpha 6
  changeFlag : ChangeFlag
  deriving DecidableEq, Repr

namespace Low

def encode (message : Low) : List UInt8 :=
  LimitDownFlag.encode message.limitDownFlag
    ++ (Price.encode message.price
    ++ (Alpha.encode message.timeC6
    ++ (ChangeFlag.encode message.changeFlag)))

def decode (bytes : List UInt8) : Option (Low × List UInt8) := do
  let (limitDownFlag, bytes) ← LimitDownFlag.decode bytes
  let (price, bytes) ← Price.decode bytes
  let (timeC6, bytes) ← Alpha.decode 6 bytes
  let (changeFlag, bytes) ← ChangeFlag.decode bytes
  pure ({ limitDownFlag, price, timeC6, changeFlag }, bytes)

@[simp] theorem encode_length (message : Low) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, LimitDownFlag.encode_length, Price.encode_length, Alpha.encode_length, ChangeFlag.encode_length]

theorem encode_length_pos (message : Low) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Low) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LimitDownFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Price.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [ChangeFlag.decode_encode, some_bind]
  rfl

end Low

/-- Current: 32 bytes -/
structure Current where
  price : Price
  timeC12 : Alpha 12
  currentChangeFlag : CurrentChangeFlag
  stqReferencePointFlag : StqReferencePointFlag
  reserved1 : Alpha 1
  closingPriceInputFlag : ClosingPriceInputFlag
  deriving DecidableEq, Repr

namespace Current

def encode (message : Current) : List UInt8 :=
  Price.encode message.price
    ++ (Alpha.encode message.timeC12
    ++ (CurrentChangeFlag.encode message.currentChangeFlag
    ++ (StqReferencePointFlag.encode message.stqReferencePointFlag
    ++ (Alpha.encode message.reserved1
    ++ (ClosingPriceInputFlag.encode message.closingPriceInputFlag)))))

def decode (bytes : List UInt8) : Option (Current × List UInt8) := do
  let (price, bytes) ← Price.decode bytes
  let (timeC12, bytes) ← Alpha.decode 12 bytes
  let (currentChangeFlag, bytes) ← CurrentChangeFlag.decode bytes
  let (stqReferencePointFlag, bytes) ← StqReferencePointFlag.decode bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (closingPriceInputFlag, bytes) ← ClosingPriceInputFlag.decode bytes
  pure ({ price, timeC12, currentChangeFlag, stqReferencePointFlag, reserved1, closingPriceInputFlag }, bytes)

@[simp] theorem encode_length (message : Current) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, Price.encode_length, Alpha.encode_length, CurrentChangeFlag.encode_length, StqReferencePointFlag.encode_length, ClosingPriceInputFlag.encode_length]

theorem encode_length_pos (message : Current) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Current) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Price.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CurrentChangeFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StqReferencePointFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [ClosingPriceInputFlag.decode_encode, some_bind]
  rfl

end Current

/-- Open High Low And Current Price Message: 105 bytes -/
structure OpenHighLowAndCurrentPriceMessage where
  reserved2 : Alpha 2
  open_ : Open
  high : High
  low : Low
  current : Current
  deriving DecidableEq, Repr

namespace OpenHighLowAndCurrentPriceMessage

def encode (message : OpenHighLowAndCurrentPriceMessage) : List UInt8 :=
  Alpha.encode message.reserved2
    ++ (Open.encode message.open_
    ++ (High.encode message.high
    ++ (Low.encode message.low
    ++ (Current.encode message.current))))

def decode (bytes : List UInt8) : Option (OpenHighLowAndCurrentPriceMessage × List UInt8) := do
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (open_, bytes) ← Open.decode bytes
  let (high, bytes) ← High.decode bytes
  let (low, bytes) ← Low.decode bytes
  let (current, bytes) ← Current.decode bytes
  pure ({ reserved2, open_, high, low, current }, bytes)

@[simp] theorem encode_length (message : OpenHighLowAndCurrentPriceMessage) : (encode message).length = 105 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, Open.encode_length, High.encode_length, Low.encode_length, Current.encode_length]

theorem encode_length_pos (message : OpenHighLowAndCurrentPriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OpenHighLowAndCurrentPriceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Open.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, High.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Low.decode_encode, some_bind]
  dsimp only
  rw [Current.decode_encode, some_bind]
  rfl

end OpenHighLowAndCurrentPriceMessage

/-- Quote Quantity: 16 bytes -/
structure QuoteQuantity where
  tradingVolumeTurnoverUnitFlag : TradingVolumeTurnoverUnitFlag
  quantity : Alpha 14
  sign : Sign
  deriving DecidableEq, Repr

namespace QuoteQuantity

def encode (message : QuoteQuantity) : List UInt8 :=
  TradingVolumeTurnoverUnitFlag.encode message.tradingVolumeTurnoverUnitFlag
    ++ (Alpha.encode message.quantity
    ++ (Sign.encode message.sign))

def decode (bytes : List UInt8) : Option (QuoteQuantity × List UInt8) := do
  let (tradingVolumeTurnoverUnitFlag, bytes) ← TradingVolumeTurnoverUnitFlag.decode bytes
  let (quantity, bytes) ← Alpha.decode 14 bytes
  let (sign, bytes) ← Sign.decode bytes
  pure ({ tradingVolumeTurnoverUnitFlag, quantity, sign }, bytes)

@[simp] theorem encode_length (message : QuoteQuantity) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, TradingVolumeTurnoverUnitFlag.encode_length, Alpha.encode_length, Sign.encode_length]

theorem encode_length_pos (message : QuoteQuantity) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteQuantity) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, TradingVolumeTurnoverUnitFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Sign.decode_encode, some_bind]
  rfl

end QuoteQuantity

/-- Ask Quote: 46 bytes -/
structure AskQuote where
  changeFlag : ChangeFlag
  price : Price
  timeC12 : Alpha 12
  quoteFlag : QuoteFlag
  quoteQuantity : QuoteQuantity
  deriving DecidableEq, Repr

namespace AskQuote

def encode (message : AskQuote) : List UInt8 :=
  ChangeFlag.encode message.changeFlag
    ++ (Price.encode message.price
    ++ (Alpha.encode message.timeC12
    ++ (QuoteFlag.encode message.quoteFlag
    ++ (QuoteQuantity.encode message.quoteQuantity))))

def decode (bytes : List UInt8) : Option (AskQuote × List UInt8) := do
  let (changeFlag, bytes) ← ChangeFlag.decode bytes
  let (price, bytes) ← Price.decode bytes
  let (timeC12, bytes) ← Alpha.decode 12 bytes
  let (quoteFlag, bytes) ← QuoteFlag.decode bytes
  let (quoteQuantity, bytes) ← QuoteQuantity.decode bytes
  pure ({ changeFlag, price, timeC12, quoteFlag, quoteQuantity }, bytes)

@[simp] theorem encode_length (message : AskQuote) : (encode message).length = 46 := by
  unfold encode
  simp only [List.length_append, ChangeFlag.encode_length, Price.encode_length, Alpha.encode_length, QuoteFlag.encode_length, QuoteQuantity.encode_length]

theorem encode_length_pos (message : AskQuote) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AskQuote) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ChangeFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Price.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, QuoteFlag.decode_encode, some_bind]
  dsimp only
  rw [QuoteQuantity.decode_encode, some_bind]
  rfl

end AskQuote

/-- Bid Quote: 46 bytes -/
structure BidQuote where
  changeFlag : ChangeFlag
  price : Price
  timeC12 : Alpha 12
  quoteFlag : QuoteFlag
  quoteQuantity : QuoteQuantity
  deriving DecidableEq, Repr

namespace BidQuote

def encode (message : BidQuote) : List UInt8 :=
  ChangeFlag.encode message.changeFlag
    ++ (Price.encode message.price
    ++ (Alpha.encode message.timeC12
    ++ (QuoteFlag.encode message.quoteFlag
    ++ (QuoteQuantity.encode message.quoteQuantity))))

def decode (bytes : List UInt8) : Option (BidQuote × List UInt8) := do
  let (changeFlag, bytes) ← ChangeFlag.decode bytes
  let (price, bytes) ← Price.decode bytes
  let (timeC12, bytes) ← Alpha.decode 12 bytes
  let (quoteFlag, bytes) ← QuoteFlag.decode bytes
  let (quoteQuantity, bytes) ← QuoteQuantity.decode bytes
  pure ({ changeFlag, price, timeC12, quoteFlag, quoteQuantity }, bytes)

@[simp] theorem encode_length (message : BidQuote) : (encode message).length = 46 := by
  unfold encode
  simp only [List.length_append, ChangeFlag.encode_length, Price.encode_length, Alpha.encode_length, QuoteFlag.encode_length, QuoteQuantity.encode_length]

theorem encode_length_pos (message : BidQuote) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BidQuote) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ChangeFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Price.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, QuoteFlag.decode_encode, some_bind]
  dsimp only
  rw [QuoteQuantity.decode_encode, some_bind]
  rfl

end BidQuote

/-- Quote 1 Message: 94 bytes -/
structure Quote1Message where
  reserved2 : Alpha 2
  askQuote : AskQuote
  bidQuote : BidQuote
  deriving DecidableEq, Repr

namespace Quote1Message

def encode (message : Quote1Message) : List UInt8 :=
  Alpha.encode message.reserved2
    ++ (AskQuote.encode message.askQuote
    ++ (BidQuote.encode message.bidQuote))

def decode (bytes : List UInt8) : Option (Quote1Message × List UInt8) := do
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (askQuote, bytes) ← AskQuote.decode bytes
  let (bidQuote, bytes) ← BidQuote.decode bytes
  pure ({ reserved2, askQuote, bidQuote }, bytes)

@[simp] theorem encode_length (message : Quote1Message) : (encode message).length = 94 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, AskQuote.encode_length, BidQuote.encode_length]

theorem encode_length_pos (message : Quote1Message) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Quote1Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskQuote.decode_encode, some_bind]
  dsimp only
  rw [BidQuote.decode_encode, some_bind]
  rfl

end Quote1Message

/-- Quote 2 Message: 94 bytes -/
structure Quote2Message where
  reserved2 : Alpha 2
  askQuote : AskQuote
  bidQuote : BidQuote
  deriving DecidableEq, Repr

namespace Quote2Message

def encode (message : Quote2Message) : List UInt8 :=
  Alpha.encode message.reserved2
    ++ (AskQuote.encode message.askQuote
    ++ (BidQuote.encode message.bidQuote))

def decode (bytes : List UInt8) : Option (Quote2Message × List UInt8) := do
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (askQuote, bytes) ← AskQuote.decode bytes
  let (bidQuote, bytes) ← BidQuote.decode bytes
  pure ({ reserved2, askQuote, bidQuote }, bytes)

@[simp] theorem encode_length (message : Quote2Message) : (encode message).length = 94 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, AskQuote.encode_length, BidQuote.encode_length]

theorem encode_length_pos (message : Quote2Message) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Quote2Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskQuote.decode_encode, some_bind]
  dsimp only
  rw [BidQuote.decode_encode, some_bind]
  rfl

end Quote2Message

/-- Quote 3 Message: 94 bytes -/
structure Quote3Message where
  reserved2 : Alpha 2
  askQuote : AskQuote
  bidQuote : BidQuote
  deriving DecidableEq, Repr

namespace Quote3Message

def encode (message : Quote3Message) : List UInt8 :=
  Alpha.encode message.reserved2
    ++ (AskQuote.encode message.askQuote
    ++ (BidQuote.encode message.bidQuote))

def decode (bytes : List UInt8) : Option (Quote3Message × List UInt8) := do
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (askQuote, bytes) ← AskQuote.decode bytes
  let (bidQuote, bytes) ← BidQuote.decode bytes
  pure ({ reserved2, askQuote, bidQuote }, bytes)

@[simp] theorem encode_length (message : Quote3Message) : (encode message).length = 94 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, AskQuote.encode_length, BidQuote.encode_length]

theorem encode_length_pos (message : Quote3Message) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Quote3Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskQuote.decode_encode, some_bind]
  dsimp only
  rw [BidQuote.decode_encode, some_bind]
  rfl

end Quote3Message

/-- Quote 4 Message: 94 bytes -/
structure Quote4Message where
  reserved2 : Alpha 2
  askQuote : AskQuote
  bidQuote : BidQuote
  deriving DecidableEq, Repr

namespace Quote4Message

def encode (message : Quote4Message) : List UInt8 :=
  Alpha.encode message.reserved2
    ++ (AskQuote.encode message.askQuote
    ++ (BidQuote.encode message.bidQuote))

def decode (bytes : List UInt8) : Option (Quote4Message × List UInt8) := do
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (askQuote, bytes) ← AskQuote.decode bytes
  let (bidQuote, bytes) ← BidQuote.decode bytes
  pure ({ reserved2, askQuote, bidQuote }, bytes)

@[simp] theorem encode_length (message : Quote4Message) : (encode message).length = 94 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, AskQuote.encode_length, BidQuote.encode_length]

theorem encode_length_pos (message : Quote4Message) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Quote4Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskQuote.decode_encode, some_bind]
  dsimp only
  rw [BidQuote.decode_encode, some_bind]
  rfl

end Quote4Message

/-- Quote 5 Message: 94 bytes -/
structure Quote5Message where
  reserved2 : Alpha 2
  askQuote : AskQuote
  bidQuote : BidQuote
  deriving DecidableEq, Repr

namespace Quote5Message

def encode (message : Quote5Message) : List UInt8 :=
  Alpha.encode message.reserved2
    ++ (AskQuote.encode message.askQuote
    ++ (BidQuote.encode message.bidQuote))

def decode (bytes : List UInt8) : Option (Quote5Message × List UInt8) := do
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (askQuote, bytes) ← AskQuote.decode bytes
  let (bidQuote, bytes) ← BidQuote.decode bytes
  pure ({ reserved2, askQuote, bidQuote }, bytes)

@[simp] theorem encode_length (message : Quote5Message) : (encode message).length = 94 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, AskQuote.encode_length, BidQuote.encode_length]

theorem encode_length_pos (message : Quote5Message) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Quote5Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskQuote.decode_encode, some_bind]
  dsimp only
  rw [BidQuote.decode_encode, some_bind]
  rfl

end Quote5Message

/-- Quote 6 Message: 94 bytes -/
structure Quote6Message where
  reserved2 : Alpha 2
  askQuote : AskQuote
  bidQuote : BidQuote
  deriving DecidableEq, Repr

namespace Quote6Message

def encode (message : Quote6Message) : List UInt8 :=
  Alpha.encode message.reserved2
    ++ (AskQuote.encode message.askQuote
    ++ (BidQuote.encode message.bidQuote))

def decode (bytes : List UInt8) : Option (Quote6Message × List UInt8) := do
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (askQuote, bytes) ← AskQuote.decode bytes
  let (bidQuote, bytes) ← BidQuote.decode bytes
  pure ({ reserved2, askQuote, bidQuote }, bytes)

@[simp] theorem encode_length (message : Quote6Message) : (encode message).length = 94 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, AskQuote.encode_length, BidQuote.encode_length]

theorem encode_length_pos (message : Quote6Message) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Quote6Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskQuote.decode_encode, some_bind]
  dsimp only
  rw [BidQuote.decode_encode, some_bind]
  rfl

end Quote6Message

/-- Quote 7 Message: 94 bytes -/
structure Quote7Message where
  reserved2 : Alpha 2
  askQuote : AskQuote
  bidQuote : BidQuote
  deriving DecidableEq, Repr

namespace Quote7Message

def encode (message : Quote7Message) : List UInt8 :=
  Alpha.encode message.reserved2
    ++ (AskQuote.encode message.askQuote
    ++ (BidQuote.encode message.bidQuote))

def decode (bytes : List UInt8) : Option (Quote7Message × List UInt8) := do
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (askQuote, bytes) ← AskQuote.decode bytes
  let (bidQuote, bytes) ← BidQuote.decode bytes
  pure ({ reserved2, askQuote, bidQuote }, bytes)

@[simp] theorem encode_length (message : Quote7Message) : (encode message).length = 94 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, AskQuote.encode_length, BidQuote.encode_length]

theorem encode_length_pos (message : Quote7Message) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Quote7Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskQuote.decode_encode, some_bind]
  dsimp only
  rw [BidQuote.decode_encode, some_bind]
  rfl

end Quote7Message

/-- Quote 8 Message: 94 bytes -/
structure Quote8Message where
  reserved2 : Alpha 2
  askQuote : AskQuote
  bidQuote : BidQuote
  deriving DecidableEq, Repr

namespace Quote8Message

def encode (message : Quote8Message) : List UInt8 :=
  Alpha.encode message.reserved2
    ++ (AskQuote.encode message.askQuote
    ++ (BidQuote.encode message.bidQuote))

def decode (bytes : List UInt8) : Option (Quote8Message × List UInt8) := do
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (askQuote, bytes) ← AskQuote.decode bytes
  let (bidQuote, bytes) ← BidQuote.decode bytes
  pure ({ reserved2, askQuote, bidQuote }, bytes)

@[simp] theorem encode_length (message : Quote8Message) : (encode message).length = 94 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, AskQuote.encode_length, BidQuote.encode_length]

theorem encode_length_pos (message : Quote8Message) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Quote8Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskQuote.decode_encode, some_bind]
  dsimp only
  rw [BidQuote.decode_encode, some_bind]
  rfl

end Quote8Message

/-- Quote 9 Message: 94 bytes -/
structure Quote9Message where
  reserved2 : Alpha 2
  askQuote : AskQuote
  bidQuote : BidQuote
  deriving DecidableEq, Repr

namespace Quote9Message

def encode (message : Quote9Message) : List UInt8 :=
  Alpha.encode message.reserved2
    ++ (AskQuote.encode message.askQuote
    ++ (BidQuote.encode message.bidQuote))

def decode (bytes : List UInt8) : Option (Quote9Message × List UInt8) := do
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (askQuote, bytes) ← AskQuote.decode bytes
  let (bidQuote, bytes) ← BidQuote.decode bytes
  pure ({ reserved2, askQuote, bidQuote }, bytes)

@[simp] theorem encode_length (message : Quote9Message) : (encode message).length = 94 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, AskQuote.encode_length, BidQuote.encode_length]

theorem encode_length_pos (message : Quote9Message) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Quote9Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskQuote.decode_encode, some_bind]
  dsimp only
  rw [BidQuote.decode_encode, some_bind]
  rfl

end Quote9Message

/-- Quote 10 Message: 94 bytes -/
structure Quote10Message where
  reserved2 : Alpha 2
  askQuote : AskQuote
  bidQuote : BidQuote
  deriving DecidableEq, Repr

namespace Quote10Message

def encode (message : Quote10Message) : List UInt8 :=
  Alpha.encode message.reserved2
    ++ (AskQuote.encode message.askQuote
    ++ (BidQuote.encode message.bidQuote))

def decode (bytes : List UInt8) : Option (Quote10Message × List UInt8) := do
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (askQuote, bytes) ← AskQuote.decode bytes
  let (bidQuote, bytes) ← BidQuote.decode bytes
  pure ({ reserved2, askQuote, bidQuote }, bytes)

@[simp] theorem encode_length (message : Quote10Message) : (encode message).length = 94 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, AskQuote.encode_length, BidQuote.encode_length]

theorem encode_length_pos (message : Quote10Message) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Quote10Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskQuote.decode_encode, some_bind]
  dsimp only
  rw [BidQuote.decode_encode, some_bind]
  rfl

end Quote10Message

/-- Sell Order: 29 bytes -/
structure SellOrder where
  changeFlag : ChangeFlag
  timeC12 : Alpha 12
  quoteQuantity : QuoteQuantity
  deriving DecidableEq, Repr

namespace SellOrder

def encode (message : SellOrder) : List UInt8 :=
  ChangeFlag.encode message.changeFlag
    ++ (Alpha.encode message.timeC12
    ++ (QuoteQuantity.encode message.quoteQuantity))

def decode (bytes : List UInt8) : Option (SellOrder × List UInt8) := do
  let (changeFlag, bytes) ← ChangeFlag.decode bytes
  let (timeC12, bytes) ← Alpha.decode 12 bytes
  let (quoteQuantity, bytes) ← QuoteQuantity.decode bytes
  pure ({ changeFlag, timeC12, quoteQuantity }, bytes)

@[simp] theorem encode_length (message : SellOrder) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, ChangeFlag.encode_length, Alpha.encode_length, QuoteQuantity.encode_length]

theorem encode_length_pos (message : SellOrder) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SellOrder) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ChangeFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [QuoteQuantity.decode_encode, some_bind]
  rfl

end SellOrder

/-- Buy Order: 29 bytes -/
structure BuyOrder where
  changeFlag : ChangeFlag
  timeC12 : Alpha 12
  quoteQuantity : QuoteQuantity
  deriving DecidableEq, Repr

namespace BuyOrder

def encode (message : BuyOrder) : List UInt8 :=
  ChangeFlag.encode message.changeFlag
    ++ (Alpha.encode message.timeC12
    ++ (QuoteQuantity.encode message.quoteQuantity))

def decode (bytes : List UInt8) : Option (BuyOrder × List UInt8) := do
  let (changeFlag, bytes) ← ChangeFlag.decode bytes
  let (timeC12, bytes) ← Alpha.decode 12 bytes
  let (quoteQuantity, bytes) ← QuoteQuantity.decode bytes
  pure ({ changeFlag, timeC12, quoteQuantity }, bytes)

@[simp] theorem encode_length (message : BuyOrder) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, ChangeFlag.encode_length, Alpha.encode_length, QuoteQuantity.encode_length]

theorem encode_length_pos (message : BuyOrder) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BuyOrder) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ChangeFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [QuoteQuantity.decode_encode, some_bind]
  rfl

end BuyOrder

/-- Market Order Message: 60 bytes -/
structure MarketOrderMessage where
  reserved2 : Alpha 2
  sellOrder : SellOrder
  buyOrder : BuyOrder
  deriving DecidableEq, Repr

namespace MarketOrderMessage

def encode (message : MarketOrderMessage) : List UInt8 :=
  Alpha.encode message.reserved2
    ++ (SellOrder.encode message.sellOrder
    ++ (BuyOrder.encode message.buyOrder))

def decode (bytes : List UInt8) : Option (MarketOrderMessage × List UInt8) := do
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (sellOrder, bytes) ← SellOrder.decode bytes
  let (buyOrder, bytes) ← BuyOrder.decode bytes
  pure ({ reserved2, sellOrder, buyOrder }, bytes)

@[simp] theorem encode_length (message : MarketOrderMessage) : (encode message).length = 60 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, SellOrder.encode_length, BuyOrder.encode_length]

theorem encode_length_pos (message : MarketOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SellOrder.decode_encode, some_bind]
  dsimp only
  rw [BuyOrder.decode_encode, some_bind]
  rfl

end MarketOrderMessage

/-- Over Quote: 29 bytes -/
structure OverQuote where
  changeFlag : ChangeFlag
  timeC12 : Alpha 12
  quoteQuantity : QuoteQuantity
  deriving DecidableEq, Repr

namespace OverQuote

def encode (message : OverQuote) : List UInt8 :=
  ChangeFlag.encode message.changeFlag
    ++ (Alpha.encode message.timeC12
    ++ (QuoteQuantity.encode message.quoteQuantity))

def decode (bytes : List UInt8) : Option (OverQuote × List UInt8) := do
  let (changeFlag, bytes) ← ChangeFlag.decode bytes
  let (timeC12, bytes) ← Alpha.decode 12 bytes
  let (quoteQuantity, bytes) ← QuoteQuantity.decode bytes
  pure ({ changeFlag, timeC12, quoteQuantity }, bytes)

@[simp] theorem encode_length (message : OverQuote) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, ChangeFlag.encode_length, Alpha.encode_length, QuoteQuantity.encode_length]

theorem encode_length_pos (message : OverQuote) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OverQuote) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ChangeFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [QuoteQuantity.decode_encode, some_bind]
  rfl

end OverQuote

/-- Under Quote: 29 bytes -/
structure UnderQuote where
  changeFlag : ChangeFlag
  timeC12 : Alpha 12
  quoteQuantity : QuoteQuantity
  deriving DecidableEq, Repr

namespace UnderQuote

def encode (message : UnderQuote) : List UInt8 :=
  ChangeFlag.encode message.changeFlag
    ++ (Alpha.encode message.timeC12
    ++ (QuoteQuantity.encode message.quoteQuantity))

def decode (bytes : List UInt8) : Option (UnderQuote × List UInt8) := do
  let (changeFlag, bytes) ← ChangeFlag.decode bytes
  let (timeC12, bytes) ← Alpha.decode 12 bytes
  let (quoteQuantity, bytes) ← QuoteQuantity.decode bytes
  pure ({ changeFlag, timeC12, quoteQuantity }, bytes)

@[simp] theorem encode_length (message : UnderQuote) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, ChangeFlag.encode_length, Alpha.encode_length, QuoteQuantity.encode_length]

theorem encode_length_pos (message : UnderQuote) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UnderQuote) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ChangeFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [QuoteQuantity.decode_encode, some_bind]
  rfl

end UnderQuote

/-- Over Under Message: 60 bytes -/
structure OverUnderMessage where
  reserved2 : Alpha 2
  overQuote : OverQuote
  underQuote : UnderQuote
  deriving DecidableEq, Repr

namespace OverUnderMessage

def encode (message : OverUnderMessage) : List UInt8 :=
  Alpha.encode message.reserved2
    ++ (OverQuote.encode message.overQuote
    ++ (UnderQuote.encode message.underQuote))

def decode (bytes : List UInt8) : Option (OverUnderMessage × List UInt8) := do
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (overQuote, bytes) ← OverQuote.decode bytes
  let (underQuote, bytes) ← UnderQuote.decode bytes
  pure ({ reserved2, overQuote, underQuote }, bytes)

@[simp] theorem encode_length (message : OverUnderMessage) : (encode message).length = 60 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, OverQuote.encode_length, UnderQuote.encode_length]

theorem encode_length_pos (message : OverUnderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OverUnderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OverQuote.decode_encode, some_bind]
  dsimp only
  rw [UnderQuote.decode_encode, some_bind]
  rfl

end OverUnderMessage

/-- Trading Volume: 23 bytes -/
structure TradingVolume where
  reserved1 : Alpha 1
  tradingVolumeTurnoverUnitFlag : TradingVolumeTurnoverUnitFlag
  tradingVolumeC14 : Alpha 14
  timeC6 : Alpha 6
  secondReserved1 : Alpha 1
  deriving DecidableEq, Repr

namespace TradingVolume

def encode (message : TradingVolume) : List UInt8 :=
  Alpha.encode message.reserved1
    ++ (TradingVolumeTurnoverUnitFlag.encode message.tradingVolumeTurnoverUnitFlag
    ++ (Alpha.encode message.tradingVolumeC14
    ++ (Alpha.encode message.timeC6
    ++ (Alpha.encode message.secondReserved1))))

def decode (bytes : List UInt8) : Option (TradingVolume × List UInt8) := do
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (tradingVolumeTurnoverUnitFlag, bytes) ← TradingVolumeTurnoverUnitFlag.decode bytes
  let (tradingVolumeC14, bytes) ← Alpha.decode 14 bytes
  let (timeC6, bytes) ← Alpha.decode 6 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  pure ({ reserved1, tradingVolumeTurnoverUnitFlag, tradingVolumeC14, timeC6, secondReserved1 }, bytes)

@[simp] theorem encode_length (message : TradingVolume) : (encode message).length = 23 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, TradingVolumeTurnoverUnitFlag.encode_length]

theorem encode_length_pos (message : TradingVolume) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradingVolume) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradingVolumeTurnoverUnitFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradingVolume

/-- Trading Volume Message: 25 bytes -/
structure TradingVolumeMessage where
  reserved2 : Alpha 2
  tradingVolume : TradingVolume
  deriving DecidableEq, Repr

namespace TradingVolumeMessage

def encode (message : TradingVolumeMessage) : List UInt8 :=
  Alpha.encode message.reserved2
    ++ (TradingVolume.encode message.tradingVolume)

def decode (bytes : List UInt8) : Option (TradingVolumeMessage × List UInt8) := do
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (tradingVolume, bytes) ← TradingVolume.decode bytes
  pure ({ reserved2, tradingVolume }, bytes)

@[simp] theorem encode_length (message : TradingVolumeMessage) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, TradingVolume.encode_length]

theorem encode_length_pos (message : TradingVolumeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradingVolumeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [TradingVolume.decode_encode, some_bind]
  rfl

end TradingVolumeMessage

/-- Turnover In Yen Value: 23 bytes -/
structure TurnoverInYenValue where
  reserved1 : Alpha 1
  tradingVolumeTurnoverUnitFlag : TradingVolumeTurnoverUnitFlag
  turnoverValue : Alpha 14
  timeC6 : Alpha 6
  secondReserved1 : Alpha 1
  deriving DecidableEq, Repr

namespace TurnoverInYenValue

def encode (message : TurnoverInYenValue) : List UInt8 :=
  Alpha.encode message.reserved1
    ++ (TradingVolumeTurnoverUnitFlag.encode message.tradingVolumeTurnoverUnitFlag
    ++ (Alpha.encode message.turnoverValue
    ++ (Alpha.encode message.timeC6
    ++ (Alpha.encode message.secondReserved1))))

def decode (bytes : List UInt8) : Option (TurnoverInYenValue × List UInt8) := do
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (tradingVolumeTurnoverUnitFlag, bytes) ← TradingVolumeTurnoverUnitFlag.decode bytes
  let (turnoverValue, bytes) ← Alpha.decode 14 bytes
  let (timeC6, bytes) ← Alpha.decode 6 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  pure ({ reserved1, tradingVolumeTurnoverUnitFlag, turnoverValue, timeC6, secondReserved1 }, bytes)

@[simp] theorem encode_length (message : TurnoverInYenValue) : (encode message).length = 23 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, TradingVolumeTurnoverUnitFlag.encode_length]

theorem encode_length_pos (message : TurnoverInYenValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TurnoverInYenValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradingVolumeTurnoverUnitFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TurnoverInYenValue

/-- Turnover Message: 25 bytes -/
structure TurnoverMessage where
  reserved2 : Alpha 2
  turnoverInYenValue : TurnoverInYenValue
  deriving DecidableEq, Repr

namespace TurnoverMessage

def encode (message : TurnoverMessage) : List UInt8 :=
  Alpha.encode message.reserved2
    ++ (TurnoverInYenValue.encode message.turnoverInYenValue)

def decode (bytes : List UInt8) : Option (TurnoverMessage × List UInt8) := do
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (turnoverInYenValue, bytes) ← TurnoverInYenValue.decode bytes
  pure ({ reserved2, turnoverInYenValue }, bytes)

@[simp] theorem encode_length (message : TurnoverMessage) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, TurnoverInYenValue.encode_length]

theorem encode_length_pos (message : TurnoverMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TurnoverMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [TurnoverInYenValue.decode_encode, some_bind]
  rfl

end TurnoverMessage

/-- All Day Vwap: 24 bytes -/
structure AllDayVwap where
  reserved1 : Alpha 1
  lotSizeUnitFlag : LotSizeUnitFlag
  allDayVwapC14 : Alpha 14
  sign : Sign
  timeC6 : Alpha 6
  secondReserved1 : Alpha 1
  deriving DecidableEq, Repr

namespace AllDayVwap

def encode (message : AllDayVwap) : List UInt8 :=
  Alpha.encode message.reserved1
    ++ (LotSizeUnitFlag.encode message.lotSizeUnitFlag
    ++ (Alpha.encode message.allDayVwapC14
    ++ (Sign.encode message.sign
    ++ (Alpha.encode message.timeC6
    ++ (Alpha.encode message.secondReserved1)))))

def decode (bytes : List UInt8) : Option (AllDayVwap × List UInt8) := do
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (lotSizeUnitFlag, bytes) ← LotSizeUnitFlag.decode bytes
  let (allDayVwapC14, bytes) ← Alpha.decode 14 bytes
  let (sign, bytes) ← Sign.decode bytes
  let (timeC6, bytes) ← Alpha.decode 6 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  pure ({ reserved1, lotSizeUnitFlag, allDayVwapC14, sign, timeC6, secondReserved1 }, bytes)

@[simp] theorem encode_length (message : AllDayVwap) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, LotSizeUnitFlag.encode_length, Sign.encode_length]

theorem encode_length_pos (message : AllDayVwap) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AllDayVwap) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LotSizeUnitFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Sign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end AllDayVwap

/-- Current Session Vwap: 24 bytes -/
structure CurrentSessionVwap where
  reserved1 : Alpha 1
  lotSizeUnitFlag : LotSizeUnitFlag
  currentSessionVwapC14 : Alpha 14
  sign : Sign
  timeC6 : Alpha 6
  secondReserved1 : Alpha 1
  deriving DecidableEq, Repr

namespace CurrentSessionVwap

def encode (message : CurrentSessionVwap) : List UInt8 :=
  Alpha.encode message.reserved1
    ++ (LotSizeUnitFlag.encode message.lotSizeUnitFlag
    ++ (Alpha.encode message.currentSessionVwapC14
    ++ (Sign.encode message.sign
    ++ (Alpha.encode message.timeC6
    ++ (Alpha.encode message.secondReserved1)))))

def decode (bytes : List UInt8) : Option (CurrentSessionVwap × List UInt8) := do
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (lotSizeUnitFlag, bytes) ← LotSizeUnitFlag.decode bytes
  let (currentSessionVwapC14, bytes) ← Alpha.decode 14 bytes
  let (sign, bytes) ← Sign.decode bytes
  let (timeC6, bytes) ← Alpha.decode 6 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  pure ({ reserved1, lotSizeUnitFlag, currentSessionVwapC14, sign, timeC6, secondReserved1 }, bytes)

@[simp] theorem encode_length (message : CurrentSessionVwap) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, LotSizeUnitFlag.encode_length, Sign.encode_length]

theorem encode_length_pos (message : CurrentSessionVwap) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CurrentSessionVwap) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LotSizeUnitFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Sign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end CurrentSessionVwap

/-- Vwap Message: 50 bytes -/
structure VwapMessage where
  reserved2 : Alpha 2
  allDayVwap : AllDayVwap
  currentSessionVwap : CurrentSessionVwap
  deriving DecidableEq, Repr

namespace VwapMessage

def encode (message : VwapMessage) : List UInt8 :=
  Alpha.encode message.reserved2
    ++ (AllDayVwap.encode message.allDayVwap
    ++ (CurrentSessionVwap.encode message.currentSessionVwap))

def decode (bytes : List UInt8) : Option (VwapMessage × List UInt8) := do
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (allDayVwap, bytes) ← AllDayVwap.decode bytes
  let (currentSessionVwap, bytes) ← CurrentSessionVwap.decode bytes
  pure ({ reserved2, allDayVwap, currentSessionVwap }, bytes)

@[simp] theorem encode_length (message : VwapMessage) : (encode message).length = 50 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, AllDayVwap.encode_length, CurrentSessionVwap.encode_length]

theorem encode_length_pos (message : VwapMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : VwapMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AllDayVwap.decode_encode, some_bind]
  dsimp only
  rw [CurrentSessionVwap.decode_encode, some_bind]
  rfl

end VwapMessage

/-- Parity Estimated Price: 23 bytes -/
structure ParityEstimatedPrice where
  unitFlag : UnitFlag
  parityEstimatedPriceC14 : Alpha 14
  sign : Sign
  timeC6 : Alpha 6
  reserved1 : Alpha 1
  deriving DecidableEq, Repr

namespace ParityEstimatedPrice

def encode (message : ParityEstimatedPrice) : List UInt8 :=
  UnitFlag.encode message.unitFlag
    ++ (Alpha.encode message.parityEstimatedPriceC14
    ++ (Sign.encode message.sign
    ++ (Alpha.encode message.timeC6
    ++ (Alpha.encode message.reserved1))))

def decode (bytes : List UInt8) : Option (ParityEstimatedPrice × List UInt8) := do
  let (unitFlag, bytes) ← UnitFlag.decode bytes
  let (parityEstimatedPriceC14, bytes) ← Alpha.decode 14 bytes
  let (sign, bytes) ← Sign.decode bytes
  let (timeC6, bytes) ← Alpha.decode 6 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  pure ({ unitFlag, parityEstimatedPriceC14, sign, timeC6, reserved1 }, bytes)

@[simp] theorem encode_length (message : ParityEstimatedPrice) : (encode message).length = 23 := by
  unfold encode
  simp only [List.length_append, UnitFlag.encode_length, Alpha.encode_length, Sign.encode_length]

theorem encode_length_pos (message : ParityEstimatedPrice) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ParityEstimatedPrice) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, UnitFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Sign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ParityEstimatedPrice

/-- Parity Message: 25 bytes -/
structure ParityMessage where
  reserved2 : Alpha 2
  parityEstimatedPrice : ParityEstimatedPrice
  deriving DecidableEq, Repr

namespace ParityMessage

def encode (message : ParityMessage) : List UInt8 :=
  Alpha.encode message.reserved2
    ++ (ParityEstimatedPrice.encode message.parityEstimatedPrice)

def decode (bytes : List UInt8) : Option (ParityMessage × List UInt8) := do
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (parityEstimatedPrice, bytes) ← ParityEstimatedPrice.decode bytes
  pure ({ reserved2, parityEstimatedPrice }, bytes)

@[simp] theorem encode_length (message : ParityMessage) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ParityEstimatedPrice.encode_length]

theorem encode_length_pos (message : ParityMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ParityMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [ParityEstimatedPrice.decode_encode, some_bind]
  rfl

end ParityMessage

/-- Direct Yield: 9 bytes -/
structure DirectYield where
  directYieldC8 : Alpha 8
  sign : Sign
  deriving DecidableEq, Repr

namespace DirectYield

def encode (message : DirectYield) : List UInt8 :=
  Alpha.encode message.directYieldC8
    ++ (Sign.encode message.sign)

def decode (bytes : List UInt8) : Option (DirectYield × List UInt8) := do
  let (directYieldC8, bytes) ← Alpha.decode 8 bytes
  let (sign, bytes) ← Sign.decode bytes
  pure ({ directYieldC8, sign }, bytes)

@[simp] theorem encode_length (message : DirectYield) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, Sign.encode_length]

theorem encode_length_pos (message : DirectYield) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DirectYield) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Sign.decode_encode, some_bind]
  rfl

end DirectYield

/-- Final Yield: 9 bytes -/
structure FinalYield where
  finalYieldC8 : Alpha 8
  sign : Sign
  deriving DecidableEq, Repr

namespace FinalYield

def encode (message : FinalYield) : List UInt8 :=
  Alpha.encode message.finalYieldC8
    ++ (Sign.encode message.sign)

def decode (bytes : List UInt8) : Option (FinalYield × List UInt8) := do
  let (finalYieldC8, bytes) ← Alpha.decode 8 bytes
  let (sign, bytes) ← Sign.decode bytes
  pure ({ finalYieldC8, sign }, bytes)

@[simp] theorem encode_length (message : FinalYield) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, Sign.encode_length]

theorem encode_length_pos (message : FinalYield) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FinalYield) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Sign.decode_encode, some_bind]
  rfl

end FinalYield

/-- Yield Message: 27 bytes -/
structure YieldMessage where
  reserved2 : Alpha 2
  directYield : DirectYield
  finalYield : FinalYield
  timeC6 : Alpha 6
  reserved1 : Alpha 1
  deriving DecidableEq, Repr

namespace YieldMessage

def encode (message : YieldMessage) : List UInt8 :=
  Alpha.encode message.reserved2
    ++ (DirectYield.encode message.directYield
    ++ (FinalYield.encode message.finalYield
    ++ (Alpha.encode message.timeC6
    ++ (Alpha.encode message.reserved1))))

def decode (bytes : List UInt8) : Option (YieldMessage × List UInt8) := do
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (directYield, bytes) ← DirectYield.decode bytes
  let (finalYield, bytes) ← FinalYield.decode bytes
  let (timeC6, bytes) ← Alpha.decode 6 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  pure ({ reserved2, directYield, finalYield, timeC6, reserved1 }, bytes)

@[simp] theorem encode_length (message : YieldMessage) : (encode message).length = 27 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, DirectYield.encode_length, FinalYield.encode_length]

theorem encode_length_pos (message : YieldMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : YieldMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DirectYield.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FinalYield.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end YieldMessage

/-- Control Message: 10 bytes -/
structure ControlMessage where
  reserved2 : Alpha 2
  testModeFlag : TestModeFlag
  startEndFlag : StartEndFlag
  timeC6 : Alpha 6
  deriving DecidableEq, Repr

namespace ControlMessage

def encode (message : ControlMessage) : List UInt8 :=
  Alpha.encode message.reserved2
    ++ (TestModeFlag.encode message.testModeFlag
    ++ (StartEndFlag.encode message.startEndFlag
    ++ (Alpha.encode message.timeC6)))

def decode (bytes : List UInt8) : Option (ControlMessage × List UInt8) := do
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (testModeFlag, bytes) ← TestModeFlag.decode bytes
  let (startEndFlag, bytes) ← StartEndFlag.decode bytes
  let (timeC6, bytes) ← Alpha.decode 6 bytes
  pure ({ reserved2, testModeFlag, startEndFlag, timeC6 }, bytes)

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
  | updateNoMessage (message : UpdateNoMessage) -- "NO" 0x4E4F
  | statusInformationMessage (message : StatusInformationMessage) -- "ST" 0x5354
  | openHighLowAndCurrentPriceMessage (message : OpenHighLowAndCurrentPriceMessage) -- "4P" 0x3450
  | quote1Message (message : Quote1Message) -- "Q1" 0x5131
  | quote2Message (message : Quote2Message) -- "Q2" 0x5132
  | quote3Message (message : Quote3Message) -- "Q3" 0x5133
  | quote4Message (message : Quote4Message) -- "Q4" 0x5134
  | quote5Message (message : Quote5Message) -- "Q5" 0x5135
  | quote6Message (message : Quote6Message) -- "Q6" 0x5136
  | quote7Message (message : Quote7Message) -- "Q7" 0x5137
  | quote8Message (message : Quote8Message) -- "Q8" 0x5138
  | quote9Message (message : Quote9Message) -- "Q9" 0x5139
  | quote10Message (message : Quote10Message) -- "QA" 0x5141
  | marketOrderMessage (message : MarketOrderMessage) -- "QM" 0x514D
  | overUnderMessage (message : OverUnderMessage) -- "QO" 0x514F
  | tradingVolumeMessage (message : TradingVolumeMessage) -- "VL" 0x564C
  | turnoverMessage (message : TurnoverMessage) -- "VA" 0x5641
  | vwapMessage (message : VwapMessage) -- "VW" 0x5657
  | parityMessage (message : ParityMessage) -- "PA" 0x5041
  | yieldMessage (message : YieldMessage) -- "YI" 0x5949
  | controlMessage (message : ControlMessage) -- "LC" 0x4C43
  deriving DecidableEq, Repr

namespace Payload

/-- The Tag ID each message is sent under -/
def tag : Payload → BitVec 16
  | .updateNoMessage _ => 20047
  | .statusInformationMessage _ => 21332
  | .openHighLowAndCurrentPriceMessage _ => 13392
  | .quote1Message _ => 20785
  | .quote2Message _ => 20786
  | .quote3Message _ => 20787
  | .quote4Message _ => 20788
  | .quote5Message _ => 20789
  | .quote6Message _ => 20790
  | .quote7Message _ => 20791
  | .quote8Message _ => 20792
  | .quote9Message _ => 20793
  | .quote10Message _ => 20801
  | .marketOrderMessage _ => 20813
  | .overUnderMessage _ => 20815
  | .tradingVolumeMessage _ => 22092
  | .turnoverMessage _ => 22081
  | .vwapMessage _ => 22103
  | .parityMessage _ => 20545
  | .yieldMessage _ => 22857
  | .controlMessage _ => 19523

def encode : Payload → List UInt8
  | .updateNoMessage message => UpdateNoMessage.encode message
  | .statusInformationMessage message => StatusInformationMessage.encode message
  | .openHighLowAndCurrentPriceMessage message => OpenHighLowAndCurrentPriceMessage.encode message
  | .quote1Message message => Quote1Message.encode message
  | .quote2Message message => Quote2Message.encode message
  | .quote3Message message => Quote3Message.encode message
  | .quote4Message message => Quote4Message.encode message
  | .quote5Message message => Quote5Message.encode message
  | .quote6Message message => Quote6Message.encode message
  | .quote7Message message => Quote7Message.encode message
  | .quote8Message message => Quote8Message.encode message
  | .quote9Message message => Quote9Message.encode message
  | .quote10Message message => Quote10Message.encode message
  | .marketOrderMessage message => MarketOrderMessage.encode message
  | .overUnderMessage message => OverUnderMessage.encode message
  | .tradingVolumeMessage message => TradingVolumeMessage.encode message
  | .turnoverMessage message => TurnoverMessage.encode message
  | .vwapMessage message => VwapMessage.encode message
  | .parityMessage message => ParityMessage.encode message
  | .yieldMessage message => YieldMessage.encode message
  | .controlMessage message => ControlMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 105 := by
  cases message with
  | updateNoMessage inner =>
    simp only [encode, UpdateNoMessage.encode_length]
    omega
  | statusInformationMessage inner =>
    simp only [encode, StatusInformationMessage.encode_length]
    omega
  | openHighLowAndCurrentPriceMessage inner =>
    simp only [encode, OpenHighLowAndCurrentPriceMessage.encode_length]
    omega
  | quote1Message inner =>
    simp only [encode, Quote1Message.encode_length]
    omega
  | quote2Message inner =>
    simp only [encode, Quote2Message.encode_length]
    omega
  | quote3Message inner =>
    simp only [encode, Quote3Message.encode_length]
    omega
  | quote4Message inner =>
    simp only [encode, Quote4Message.encode_length]
    omega
  | quote5Message inner =>
    simp only [encode, Quote5Message.encode_length]
    omega
  | quote6Message inner =>
    simp only [encode, Quote6Message.encode_length]
    omega
  | quote7Message inner =>
    simp only [encode, Quote7Message.encode_length]
    omega
  | quote8Message inner =>
    simp only [encode, Quote8Message.encode_length]
    omega
  | quote9Message inner =>
    simp only [encode, Quote9Message.encode_length]
    omega
  | quote10Message inner =>
    simp only [encode, Quote10Message.encode_length]
    omega
  | marketOrderMessage inner =>
    simp only [encode, MarketOrderMessage.encode_length]
    omega
  | overUnderMessage inner =>
    simp only [encode, OverUnderMessage.encode_length]
    omega
  | tradingVolumeMessage inner =>
    simp only [encode, TradingVolumeMessage.encode_length]
    omega
  | turnoverMessage inner =>
    simp only [encode, TurnoverMessage.encode_length]
    omega
  | vwapMessage inner =>
    simp only [encode, VwapMessage.encode_length]
    omega
  | parityMessage inner =>
    simp only [encode, ParityMessage.encode_length]
    omega
  | yieldMessage inner =>
    simp only [encode, YieldMessage.encode_length]
    omega
  | controlMessage inner =>
    simp only [encode, ControlMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 20047 then (UpdateNoMessage.decode bytes).map fun (message, rest) => (.updateNoMessage message, rest)
  else if tag = 21332 then (StatusInformationMessage.decode bytes).map fun (message, rest) => (.statusInformationMessage message, rest)
  else if tag = 13392 then (OpenHighLowAndCurrentPriceMessage.decode bytes).map fun (message, rest) => (.openHighLowAndCurrentPriceMessage message, rest)
  else if tag = 20785 then (Quote1Message.decode bytes).map fun (message, rest) => (.quote1Message message, rest)
  else if tag = 20786 then (Quote2Message.decode bytes).map fun (message, rest) => (.quote2Message message, rest)
  else if tag = 20787 then (Quote3Message.decode bytes).map fun (message, rest) => (.quote3Message message, rest)
  else if tag = 20788 then (Quote4Message.decode bytes).map fun (message, rest) => (.quote4Message message, rest)
  else if tag = 20789 then (Quote5Message.decode bytes).map fun (message, rest) => (.quote5Message message, rest)
  else if tag = 20790 then (Quote6Message.decode bytes).map fun (message, rest) => (.quote6Message message, rest)
  else if tag = 20791 then (Quote7Message.decode bytes).map fun (message, rest) => (.quote7Message message, rest)
  else if tag = 20792 then (Quote8Message.decode bytes).map fun (message, rest) => (.quote8Message message, rest)
  else if tag = 20793 then (Quote9Message.decode bytes).map fun (message, rest) => (.quote9Message message, rest)
  else if tag = 20801 then (Quote10Message.decode bytes).map fun (message, rest) => (.quote10Message message, rest)
  else if tag = 20813 then (MarketOrderMessage.decode bytes).map fun (message, rest) => (.marketOrderMessage message, rest)
  else if tag = 20815 then (OverUnderMessage.decode bytes).map fun (message, rest) => (.overUnderMessage message, rest)
  else if tag = 22092 then (TradingVolumeMessage.decode bytes).map fun (message, rest) => (.tradingVolumeMessage message, rest)
  else if tag = 22081 then (TurnoverMessage.decode bytes).map fun (message, rest) => (.turnoverMessage message, rest)
  else if tag = 22103 then (VwapMessage.decode bytes).map fun (message, rest) => (.vwapMessage message, rest)
  else if tag = 20545 then (ParityMessage.decode bytes).map fun (message, rest) => (.parityMessage message, rest)
  else if tag = 22857 then (YieldMessage.decode bytes).map fun (message, rest) => (.yieldMessage message, rest)
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
theorem encode_length_le (message : TagInformation) : (encode message).length ≤ 108 := by
  unfold encode
  cases message.payload with
  | updateNoMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, UpdateNoMessage.encode_length]
    omega
  | statusInformationMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, StatusInformationMessage.encode_length]
    omega
  | openHighLowAndCurrentPriceMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, OpenHighLowAndCurrentPriceMessage.encode_length]
    omega
  | quote1Message inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Quote1Message.encode_length]
    omega
  | quote2Message inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Quote2Message.encode_length]
    omega
  | quote3Message inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Quote3Message.encode_length]
    omega
  | quote4Message inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Quote4Message.encode_length]
    omega
  | quote5Message inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Quote5Message.encode_length]
    omega
  | quote6Message inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Quote6Message.encode_length]
    omega
  | quote7Message inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Quote7Message.encode_length]
    omega
  | quote8Message inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Quote8Message.encode_length]
    omega
  | quote9Message inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Quote9Message.encode_length]
    omega
  | quote10Message inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Quote10Message.encode_length]
    omega
  | marketOrderMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MarketOrderMessage.encode_length]
    omega
  | overUnderMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, OverUnderMessage.encode_length]
    omega
  | tradingVolumeMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, TradingVolumeMessage.encode_length]
    omega
  | turnoverMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, TurnoverMessage.encode_length]
    omega
  | vwapMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, VwapMessage.encode_length]
    omega
  | parityMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ParityMessage.encode_length]
    omega
  | yieldMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, YieldMessage.encode_length]
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

end Omi.JpxFseequitiesStandardFlexV195
