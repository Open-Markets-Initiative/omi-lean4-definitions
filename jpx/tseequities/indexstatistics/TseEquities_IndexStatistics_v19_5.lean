import Wire

/-!
# Japan Exchange Group IndexStatistics v19.5

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.JpxTseequitiesIndexstatisticsFlexV195

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

/-- Sign: one byte code -/
def Sign.codes : List UInt8 :=
  [0x2B, 0x2D, 0x20]

inductive Sign where
  | positive -- Positive
  | negative -- Negative
  | noSign -- No Sign
  | unlisted (byte : { byte : UInt8 // byte ∉ Sign.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Sign

def toByte : Sign → UInt8
  | .positive => 0x2B
  | .negative => 0x2D
  | .noSign => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Sign :=
  if byte = 0x2B then .positive
  else if byte = 0x2D then .negative
  else .noSign

def ofByte (byte : UInt8) : Sign :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Sign) : ofByte value.toByte = value := by
  cases value with
  | positive => decide
  | negative => decide
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

/-- Second Unit Flag: one byte code -/
def SecondUnitFlag.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33, 0x34, 0x20]

inductive SecondUnitFlag where
  | toTheFourthDecimalPlace -- To The Fourth Decimal Place
  | toTheThirdDecimalPlace -- To The Third Decimal Place
  | toTheSecondDecimalPlace -- To The Second Decimal Place
  | toTheFirstDecimalPlace -- To The First Decimal Place
  | noDecimalPlaces -- No Decimal Places
  | noNumericalValue -- No Numerical Value
  | unlisted (byte : { byte : UInt8 // byte ∉ SecondUnitFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SecondUnitFlag

def toByte : SecondUnitFlag → UInt8
  | .toTheFourthDecimalPlace => 0x30
  | .toTheThirdDecimalPlace => 0x31
  | .toTheSecondDecimalPlace => 0x32
  | .toTheFirstDecimalPlace => 0x33
  | .noDecimalPlaces => 0x34
  | .noNumericalValue => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SecondUnitFlag :=
  if byte = 0x30 then .toTheFourthDecimalPlace
  else if byte = 0x31 then .toTheThirdDecimalPlace
  else if byte = 0x32 then .toTheSecondDecimalPlace
  else if byte = 0x33 then .toTheFirstDecimalPlace
  else if byte = 0x34 then .noDecimalPlaces
  else .noNumericalValue

def ofByte (byte : UInt8) : SecondUnitFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SecondUnitFlag) : ofByte value.toByte = value := by
  cases value with
  | toTheFourthDecimalPlace => decide
  | toTheThirdDecimalPlace => decide
  | toTheSecondDecimalPlace => decide
  | toTheFirstDecimalPlace => decide
  | noDecimalPlaces => decide
  | noNumericalValue => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SecondUnitFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SecondUnitFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SecondUnitFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SecondUnitFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SecondUnitFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SecondUnitFlag

/-- Second Sign: one byte code -/
def SecondSign.codes : List UInt8 :=
  [0x2B, 0x2D, 0x20]

inductive SecondSign where
  | positive -- Positive
  | negative -- Negative
  | noSign -- No Sign
  | unlisted (byte : { byte : UInt8 // byte ∉ SecondSign.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SecondSign

def toByte : SecondSign → UInt8
  | .positive => 0x2B
  | .negative => 0x2D
  | .noSign => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SecondSign :=
  if byte = 0x2B then .positive
  else if byte = 0x2D then .negative
  else .noSign

def ofByte (byte : UInt8) : SecondSign :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SecondSign) : ofByte value.toByte = value := by
  cases value with
  | positive => decide
  | negative => decide
  | noSign => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SecondSign) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SecondSign × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SecondSign) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SecondSign) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SecondSign) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SecondSign

/-- Net Change Distinction: one byte code -/
def NetChangeDistinction.codes : List UInt8 :=
  [0x31, 0x32]

inductive NetChangeDistinction where
  | up -- Up
  | down -- Down
  | unlisted (byte : { byte : UInt8 // byte ∉ NetChangeDistinction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace NetChangeDistinction

def toByte : NetChangeDistinction → UInt8
  | .up => 0x31
  | .down => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : NetChangeDistinction :=
  if byte = 0x31 then .up
  else .down

def ofByte (byte : UInt8) : NetChangeDistinction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : NetChangeDistinction) : ofByte value.toByte = value := by
  cases value with
  | up => decide
  | down => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : NetChangeDistinction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (NetChangeDistinction × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : NetChangeDistinction) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : NetChangeDistinction) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : NetChangeDistinction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end NetChangeDistinction

/-- State Sign: one byte code -/
def StateSign.codes : List UInt8 :=
  [0x31, 0x32, 0x33, 0x34, 0x20]

inductive StateSign where
  | askSpecialQuote -- Ask Special Quote
  | bidSpecialQuote -- Bid Special Quote
  | askContinuousExecutionQuote -- Ask Continuous Execution Quote
  | bidContinuousExecutionQuote -- Bid Continuous Execution Quote
  | otherThanTheAbove -- Other Than The Above
  | unlisted (byte : { byte : UInt8 // byte ∉ StateSign.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace StateSign

def toByte : StateSign → UInt8
  | .askSpecialQuote => 0x31
  | .bidSpecialQuote => 0x32
  | .askContinuousExecutionQuote => 0x33
  | .bidContinuousExecutionQuote => 0x34
  | .otherThanTheAbove => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : StateSign :=
  if byte = 0x31 then .askSpecialQuote
  else if byte = 0x32 then .bidSpecialQuote
  else if byte = 0x33 then .askContinuousExecutionQuote
  else if byte = 0x34 then .bidContinuousExecutionQuote
  else .otherThanTheAbove

def ofByte (byte : UInt8) : StateSign :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : StateSign) : ofByte value.toByte = value := by
  cases value with
  | askSpecialQuote => decide
  | bidSpecialQuote => decide
  | askContinuousExecutionQuote => decide
  | bidContinuousExecutionQuote => decide
  | otherThanTheAbove => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : StateSign) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (StateSign × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : StateSign) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : StateSign) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : StateSign) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end StateSign

/-- Comparison Type: one byte code -/
def ComparisonType.codes : List UInt8 :=
  [0x31, 0x20]

inductive ComparisonType where
  | changeFromBasePriceForTheDay -- Change From Base Price For The Day
  | changeFromTheLastPriceFromThePreviousDay -- Change From The Last Price From The Previous Day
  | unlisted (byte : { byte : UInt8 // byte ∉ ComparisonType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ComparisonType

def toByte : ComparisonType → UInt8
  | .changeFromBasePriceForTheDay => 0x31
  | .changeFromTheLastPriceFromThePreviousDay => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ComparisonType :=
  if byte = 0x31 then .changeFromBasePriceForTheDay
  else .changeFromTheLastPriceFromThePreviousDay

def ofByte (byte : UInt8) : ComparisonType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ComparisonType) : ofByte value.toByte = value := by
  cases value with
  | changeFromBasePriceForTheDay => decide
  | changeFromTheLastPriceFromThePreviousDay => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ComparisonType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ComparisonType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ComparisonType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ComparisonType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ComparisonType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ComparisonType

/-- Second Trading Volume/Turnover Unit Flag: one byte code -/
def SecondTradingVolumeturnoverUnitFlag.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x20]

inductive SecondTradingVolumeturnoverUnitFlag where
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
  | unlisted (byte : { byte : UInt8 // byte ∉ SecondTradingVolumeturnoverUnitFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SecondTradingVolumeturnoverUnitFlag

def toByte : SecondTradingVolumeturnoverUnitFlag → UInt8
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
def listed (byte : UInt8) : SecondTradingVolumeturnoverUnitFlag :=
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

def ofByte (byte : UInt8) : SecondTradingVolumeturnoverUnitFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SecondTradingVolumeturnoverUnitFlag) : ofByte value.toByte = value := by
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

def encode (value : SecondTradingVolumeturnoverUnitFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SecondTradingVolumeturnoverUnitFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SecondTradingVolumeturnoverUnitFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SecondTradingVolumeturnoverUnitFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SecondTradingVolumeturnoverUnitFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SecondTradingVolumeturnoverUnitFlag

/-- Third Trading Volume/Turnover Unit Flag: one byte code -/
def ThirdTradingVolumeturnoverUnitFlag.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x20]

inductive ThirdTradingVolumeturnoverUnitFlag where
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
  | unlisted (byte : { byte : UInt8 // byte ∉ ThirdTradingVolumeturnoverUnitFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ThirdTradingVolumeturnoverUnitFlag

def toByte : ThirdTradingVolumeturnoverUnitFlag → UInt8
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
def listed (byte : UInt8) : ThirdTradingVolumeturnoverUnitFlag :=
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

def ofByte (byte : UInt8) : ThirdTradingVolumeturnoverUnitFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ThirdTradingVolumeturnoverUnitFlag) : ofByte value.toByte = value := by
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

def encode (value : ThirdTradingVolumeturnoverUnitFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ThirdTradingVolumeturnoverUnitFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ThirdTradingVolumeturnoverUnitFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ThirdTradingVolumeturnoverUnitFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ThirdTradingVolumeturnoverUnitFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ThirdTradingVolumeturnoverUnitFlag

/-- Fourth Trading Volume/Turnover Unit Flag: one byte code -/
def FourthTradingVolumeturnoverUnitFlag.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x20]

inductive FourthTradingVolumeturnoverUnitFlag where
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
  | unlisted (byte : { byte : UInt8 // byte ∉ FourthTradingVolumeturnoverUnitFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace FourthTradingVolumeturnoverUnitFlag

def toByte : FourthTradingVolumeturnoverUnitFlag → UInt8
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
def listed (byte : UInt8) : FourthTradingVolumeturnoverUnitFlag :=
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

def ofByte (byte : UInt8) : FourthTradingVolumeturnoverUnitFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : FourthTradingVolumeturnoverUnitFlag) : ofByte value.toByte = value := by
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

def encode (value : FourthTradingVolumeturnoverUnitFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (FourthTradingVolumeturnoverUnitFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : FourthTradingVolumeturnoverUnitFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : FourthTradingVolumeturnoverUnitFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : FourthTradingVolumeturnoverUnitFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end FourthTradingVolumeturnoverUnitFlag

/-- Flag: one byte code -/
def Flag.codes : List UInt8 :=
  [0x31, 0x33, 0x20]

inductive Flag where
  | finalIndexFlag -- Final Index Flag
  | finalIndexCorrectionFlag -- Final Index Correction Flag
  | otherThanTheAbove -- Other Than The Above
  | unlisted (byte : { byte : UInt8 // byte ∉ Flag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Flag

def toByte : Flag → UInt8
  | .finalIndexFlag => 0x31
  | .finalIndexCorrectionFlag => 0x33
  | .otherThanTheAbove => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Flag :=
  if byte = 0x31 then .finalIndexFlag
  else if byte = 0x33 then .finalIndexCorrectionFlag
  else .otherThanTheAbove

def ofByte (byte : UInt8) : Flag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Flag) : ofByte value.toByte = value := by
  cases value with
  | finalIndexFlag => decide
  | finalIndexCorrectionFlag => decide
  | otherThanTheAbove => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Flag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Flag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Flag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Flag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Flag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Flag

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

/-- Startend Flag: one byte code -/
def StartendFlag.codes : List UInt8 :=
  [0x31, 0x32, 0x20]

inductive StartendFlag where
  | start -- Start
  | end_ -- End
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ StartendFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace StartendFlag

def toByte : StartendFlag → UInt8
  | .start => 0x31
  | .end_ => 0x32
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : StartendFlag :=
  if byte = 0x31 then .start
  else if byte = 0x32 then .end_
  else .notApplicable

def ofByte (byte : UInt8) : StartendFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : StartendFlag) : ofByte value.toByte = value := by
  cases value with
  | start => decide
  | end_ => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : StartendFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (StartendFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : StartendFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : StartendFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : StartendFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end StartendFlag

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

/-- Total Market Value: 15 bytes -/
structure TotalMarketValue where
  tradingVolumeTurnoverUnitFlag : TradingVolumeTurnoverUnitFlag
  totalMarketValueC14 : Alpha 14
  deriving DecidableEq, Repr

namespace TotalMarketValue

def encode (message : TotalMarketValue) : List UInt8 :=
  TradingVolumeTurnoverUnitFlag.encode message.tradingVolumeTurnoverUnitFlag
    ++ (Alpha.encode message.totalMarketValueC14)

def decode (bytes : List UInt8) : Option (TotalMarketValue × List UInt8) := do
  let (tradingVolumeTurnoverUnitFlag, bytes) ← TradingVolumeTurnoverUnitFlag.decode bytes
  let (totalMarketValueC14, bytes) ← Alpha.decode 14 bytes
  pure ({ tradingVolumeTurnoverUnitFlag, totalMarketValueC14 }, bytes)

@[simp] theorem encode_length (message : TotalMarketValue) : (encode message).length = 15 := by
  unfold encode
  simp only [List.length_append, TradingVolumeTurnoverUnitFlag.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : TotalMarketValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TotalMarketValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, TradingVolumeTurnoverUnitFlag.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TotalMarketValue

/-- Market Value Day On Day Comparison: 16 bytes -/
structure MarketValueDayOnDayComparison where
  tradingVolumeTurnoverUnitFlag : TradingVolumeTurnoverUnitFlag
  dayOnDayComparisonC14 : Alpha 14
  sign : Sign
  deriving DecidableEq, Repr

namespace MarketValueDayOnDayComparison

def encode (message : MarketValueDayOnDayComparison) : List UInt8 :=
  TradingVolumeTurnoverUnitFlag.encode message.tradingVolumeTurnoverUnitFlag
    ++ (Alpha.encode message.dayOnDayComparisonC14
    ++ (Sign.encode message.sign))

def decode (bytes : List UInt8) : Option (MarketValueDayOnDayComparison × List UInt8) := do
  let (tradingVolumeTurnoverUnitFlag, bytes) ← TradingVolumeTurnoverUnitFlag.decode bytes
  let (dayOnDayComparisonC14, bytes) ← Alpha.decode 14 bytes
  let (sign, bytes) ← Sign.decode bytes
  pure ({ tradingVolumeTurnoverUnitFlag, dayOnDayComparisonC14, sign }, bytes)

@[simp] theorem encode_length (message : MarketValueDayOnDayComparison) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, TradingVolumeTurnoverUnitFlag.encode_length, Alpha.encode_length, Sign.encode_length]

theorem encode_length_pos (message : MarketValueDayOnDayComparison) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketValueDayOnDayComparison) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, TradingVolumeTurnoverUnitFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Sign.decode_encode, some_bind]
  rfl

end MarketValueDayOnDayComparison

/-- Market Value Message: 43 bytes -/
structure MarketValueMessage where
  reserved2 : Alpha 2
  timeC6Hhmm : Alpha 6
  issueClassificationCode : Alpha 4
  totalMarketValue : TotalMarketValue
  marketValueDayOnDayComparison : MarketValueDayOnDayComparison
  deriving DecidableEq, Repr

namespace MarketValueMessage

def encode (message : MarketValueMessage) : List UInt8 :=
  Alpha.encode message.reserved2
    ++ (Alpha.encode message.timeC6Hhmm
    ++ (Alpha.encode message.issueClassificationCode
    ++ (TotalMarketValue.encode message.totalMarketValue
    ++ (MarketValueDayOnDayComparison.encode message.marketValueDayOnDayComparison))))

def decode (bytes : List UInt8) : Option (MarketValueMessage × List UInt8) := do
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (timeC6Hhmm, bytes) ← Alpha.decode 6 bytes
  let (issueClassificationCode, bytes) ← Alpha.decode 4 bytes
  let (totalMarketValue, bytes) ← TotalMarketValue.decode bytes
  let (marketValueDayOnDayComparison, bytes) ← MarketValueDayOnDayComparison.decode bytes
  pure ({ reserved2, timeC6Hhmm, issueClassificationCode, totalMarketValue, marketValueDayOnDayComparison }, bytes)

@[simp] theorem encode_length (message : MarketValueMessage) : (encode message).length = 43 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, TotalMarketValue.encode_length, MarketValueDayOnDayComparison.encode_length]

theorem encode_length_pos (message : MarketValueMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketValueMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TotalMarketValue.decode_encode, some_bind]
  dsimp only
  rw [MarketValueDayOnDayComparison.decode_encode, some_bind]
  rfl

end MarketValueMessage

/-- Simple Yield: 9 bytes -/
structure SimpleYield where
  simpleYieldC8 : Alpha 8
  sign : Sign
  deriving DecidableEq, Repr

namespace SimpleYield

def encode (message : SimpleYield) : List UInt8 :=
  Alpha.encode message.simpleYieldC8
    ++ (Sign.encode message.sign)

def decode (bytes : List UInt8) : Option (SimpleYield × List UInt8) := do
  let (simpleYieldC8, bytes) ← Alpha.decode 8 bytes
  let (sign, bytes) ← Sign.decode bytes
  pure ({ simpleYieldC8, sign }, bytes)

@[simp] theorem encode_length (message : SimpleYield) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, Sign.encode_length]

theorem encode_length_pos (message : SimpleYield) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SimpleYield) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Sign.decode_encode, some_bind]
  rfl

end SimpleYield

/-- Yield Day On Day Comparison: 9 bytes -/
structure YieldDayOnDayComparison where
  dayOnDayComparisonC8 : Alpha 8
  sign : Sign
  deriving DecidableEq, Repr

namespace YieldDayOnDayComparison

def encode (message : YieldDayOnDayComparison) : List UInt8 :=
  Alpha.encode message.dayOnDayComparisonC8
    ++ (Sign.encode message.sign)

def decode (bytes : List UInt8) : Option (YieldDayOnDayComparison × List UInt8) := do
  let (dayOnDayComparisonC8, bytes) ← Alpha.decode 8 bytes
  let (sign, bytes) ← Sign.decode bytes
  pure ({ dayOnDayComparisonC8, sign }, bytes)

@[simp] theorem encode_length (message : YieldDayOnDayComparison) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, Sign.encode_length]

theorem encode_length_pos (message : YieldDayOnDayComparison) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : YieldDayOnDayComparison) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Sign.decode_encode, some_bind]
  rfl

end YieldDayOnDayComparison

/-- Simple Yield Message: 30 bytes -/
structure SimpleYieldMessage where
  reserved2 : Alpha 2
  timeC6Hhmm : Alpha 6
  issueClassificationCode : Alpha 4
  simpleYield : SimpleYield
  yieldDayOnDayComparison : YieldDayOnDayComparison
  deriving DecidableEq, Repr

namespace SimpleYieldMessage

def encode (message : SimpleYieldMessage) : List UInt8 :=
  Alpha.encode message.reserved2
    ++ (Alpha.encode message.timeC6Hhmm
    ++ (Alpha.encode message.issueClassificationCode
    ++ (SimpleYield.encode message.simpleYield
    ++ (YieldDayOnDayComparison.encode message.yieldDayOnDayComparison))))

def decode (bytes : List UInt8) : Option (SimpleYieldMessage × List UInt8) := do
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (timeC6Hhmm, bytes) ← Alpha.decode 6 bytes
  let (issueClassificationCode, bytes) ← Alpha.decode 4 bytes
  let (simpleYield, bytes) ← SimpleYield.decode bytes
  let (yieldDayOnDayComparison, bytes) ← YieldDayOnDayComparison.decode bytes
  pure ({ reserved2, timeC6Hhmm, issueClassificationCode, simpleYield, yieldDayOnDayComparison }, bytes)

@[simp] theorem encode_length (message : SimpleYieldMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, SimpleYield.encode_length, YieldDayOnDayComparison.encode_length]

theorem encode_length_pos (message : SimpleYieldMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SimpleYieldMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SimpleYield.decode_encode, some_bind]
  dsimp only
  rw [YieldDayOnDayComparison.decode_encode, some_bind]
  rfl

end SimpleYieldMessage

/-- Weighted Yield: 9 bytes -/
structure WeightedYield where
  weightedYieldC8 : Alpha 8
  sign : Sign
  deriving DecidableEq, Repr

namespace WeightedYield

def encode (message : WeightedYield) : List UInt8 :=
  Alpha.encode message.weightedYieldC8
    ++ (Sign.encode message.sign)

def decode (bytes : List UInt8) : Option (WeightedYield × List UInt8) := do
  let (weightedYieldC8, bytes) ← Alpha.decode 8 bytes
  let (sign, bytes) ← Sign.decode bytes
  pure ({ weightedYieldC8, sign }, bytes)

@[simp] theorem encode_length (message : WeightedYield) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, Sign.encode_length]

theorem encode_length_pos (message : WeightedYield) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : WeightedYield) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Sign.decode_encode, some_bind]
  rfl

end WeightedYield

/-- Weighted Yield Message: 30 bytes -/
structure WeightedYieldMessage where
  reserved2 : Alpha 2
  timeC6Hhmm : Alpha 6
  issueClassificationCode : Alpha 4
  weightedYield : WeightedYield
  yieldDayOnDayComparison : YieldDayOnDayComparison
  deriving DecidableEq, Repr

namespace WeightedYieldMessage

def encode (message : WeightedYieldMessage) : List UInt8 :=
  Alpha.encode message.reserved2
    ++ (Alpha.encode message.timeC6Hhmm
    ++ (Alpha.encode message.issueClassificationCode
    ++ (WeightedYield.encode message.weightedYield
    ++ (YieldDayOnDayComparison.encode message.yieldDayOnDayComparison))))

def decode (bytes : List UInt8) : Option (WeightedYieldMessage × List UInt8) := do
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (timeC6Hhmm, bytes) ← Alpha.decode 6 bytes
  let (issueClassificationCode, bytes) ← Alpha.decode 4 bytes
  let (weightedYield, bytes) ← WeightedYield.decode bytes
  let (yieldDayOnDayComparison, bytes) ← YieldDayOnDayComparison.decode bytes
  pure ({ reserved2, timeC6Hhmm, issueClassificationCode, weightedYield, yieldDayOnDayComparison }, bytes)

@[simp] theorem encode_length (message : WeightedYieldMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, WeightedYield.encode_length, YieldDayOnDayComparison.encode_length]

theorem encode_length_pos (message : WeightedYieldMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : WeightedYieldMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, WeightedYield.decode_encode, some_bind]
  dsimp only
  rw [YieldDayOnDayComparison.decode_encode, some_bind]
  rfl

end WeightedYieldMessage

/-- Simple Stock Price Average: 16 bytes -/
structure SimpleStockPriceAverage where
  unitFlag : UnitFlag
  simpleStockPriceAverageC14 : Alpha 14
  sign : Sign
  deriving DecidableEq, Repr

namespace SimpleStockPriceAverage

def encode (message : SimpleStockPriceAverage) : List UInt8 :=
  UnitFlag.encode message.unitFlag
    ++ (Alpha.encode message.simpleStockPriceAverageC14
    ++ (Sign.encode message.sign))

def decode (bytes : List UInt8) : Option (SimpleStockPriceAverage × List UInt8) := do
  let (unitFlag, bytes) ← UnitFlag.decode bytes
  let (simpleStockPriceAverageC14, bytes) ← Alpha.decode 14 bytes
  let (sign, bytes) ← Sign.decode bytes
  pure ({ unitFlag, simpleStockPriceAverageC14, sign }, bytes)

@[simp] theorem encode_length (message : SimpleStockPriceAverage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, UnitFlag.encode_length, Alpha.encode_length, Sign.encode_length]

theorem encode_length_pos (message : SimpleStockPriceAverage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SimpleStockPriceAverage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, UnitFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Sign.decode_encode, some_bind]
  rfl

end SimpleStockPriceAverage

/-- Stock Price Average Day On Day Comparison: 16 bytes -/
structure StockPriceAverageDayOnDayComparison where
  unitFlag : UnitFlag
  dayOnDayComparisonC14 : Alpha 14
  sign : Sign
  deriving DecidableEq, Repr

namespace StockPriceAverageDayOnDayComparison

def encode (message : StockPriceAverageDayOnDayComparison) : List UInt8 :=
  UnitFlag.encode message.unitFlag
    ++ (Alpha.encode message.dayOnDayComparisonC14
    ++ (Sign.encode message.sign))

def decode (bytes : List UInt8) : Option (StockPriceAverageDayOnDayComparison × List UInt8) := do
  let (unitFlag, bytes) ← UnitFlag.decode bytes
  let (dayOnDayComparisonC14, bytes) ← Alpha.decode 14 bytes
  let (sign, bytes) ← Sign.decode bytes
  pure ({ unitFlag, dayOnDayComparisonC14, sign }, bytes)

@[simp] theorem encode_length (message : StockPriceAverageDayOnDayComparison) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, UnitFlag.encode_length, Alpha.encode_length, Sign.encode_length]

theorem encode_length_pos (message : StockPriceAverageDayOnDayComparison) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StockPriceAverageDayOnDayComparison) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, UnitFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Sign.decode_encode, some_bind]
  rfl

end StockPriceAverageDayOnDayComparison

/-- Simple Stock Price Average Message: 44 bytes -/
structure SimpleStockPriceAverageMessage where
  reserved2 : Alpha 2
  outputTime : Alpha 6
  issueClassificationCode : Alpha 4
  simpleStockPriceAverage : SimpleStockPriceAverage
  stockPriceAverageDayOnDayComparison : StockPriceAverageDayOnDayComparison
  deriving DecidableEq, Repr

namespace SimpleStockPriceAverageMessage

def encode (message : SimpleStockPriceAverageMessage) : List UInt8 :=
  Alpha.encode message.reserved2
    ++ (Alpha.encode message.outputTime
    ++ (Alpha.encode message.issueClassificationCode
    ++ (SimpleStockPriceAverage.encode message.simpleStockPriceAverage
    ++ (StockPriceAverageDayOnDayComparison.encode message.stockPriceAverageDayOnDayComparison))))

def decode (bytes : List UInt8) : Option (SimpleStockPriceAverageMessage × List UInt8) := do
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (outputTime, bytes) ← Alpha.decode 6 bytes
  let (issueClassificationCode, bytes) ← Alpha.decode 4 bytes
  let (simpleStockPriceAverage, bytes) ← SimpleStockPriceAverage.decode bytes
  let (stockPriceAverageDayOnDayComparison, bytes) ← StockPriceAverageDayOnDayComparison.decode bytes
  pure ({ reserved2, outputTime, issueClassificationCode, simpleStockPriceAverage, stockPriceAverageDayOnDayComparison }, bytes)

@[simp] theorem encode_length (message : SimpleStockPriceAverageMessage) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, SimpleStockPriceAverage.encode_length, StockPriceAverageDayOnDayComparison.encode_length]

theorem encode_length_pos (message : SimpleStockPriceAverageMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SimpleStockPriceAverageMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SimpleStockPriceAverage.decode_encode, some_bind]
  dsimp only
  rw [StockPriceAverageDayOnDayComparison.decode_encode, some_bind]
  rfl

end SimpleStockPriceAverageMessage

/-- Weighted Stock Price Average: 16 bytes -/
structure WeightedStockPriceAverage where
  unitFlag : UnitFlag
  weightedStockPriceAverageC14 : Alpha 14
  sign : Sign
  deriving DecidableEq, Repr

namespace WeightedStockPriceAverage

def encode (message : WeightedStockPriceAverage) : List UInt8 :=
  UnitFlag.encode message.unitFlag
    ++ (Alpha.encode message.weightedStockPriceAverageC14
    ++ (Sign.encode message.sign))

def decode (bytes : List UInt8) : Option (WeightedStockPriceAverage × List UInt8) := do
  let (unitFlag, bytes) ← UnitFlag.decode bytes
  let (weightedStockPriceAverageC14, bytes) ← Alpha.decode 14 bytes
  let (sign, bytes) ← Sign.decode bytes
  pure ({ unitFlag, weightedStockPriceAverageC14, sign }, bytes)

@[simp] theorem encode_length (message : WeightedStockPriceAverage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, UnitFlag.encode_length, Alpha.encode_length, Sign.encode_length]

theorem encode_length_pos (message : WeightedStockPriceAverage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : WeightedStockPriceAverage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, UnitFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Sign.decode_encode, some_bind]
  rfl

end WeightedStockPriceAverage

/-- Weighted Stock Price Average Message: 44 bytes -/
structure WeightedStockPriceAverageMessage where
  reserved2 : Alpha 2
  outputTime : Alpha 6
  issueClassificationCode : Alpha 4
  weightedStockPriceAverage : WeightedStockPriceAverage
  stockPriceAverageDayOnDayComparison : StockPriceAverageDayOnDayComparison
  deriving DecidableEq, Repr

namespace WeightedStockPriceAverageMessage

def encode (message : WeightedStockPriceAverageMessage) : List UInt8 :=
  Alpha.encode message.reserved2
    ++ (Alpha.encode message.outputTime
    ++ (Alpha.encode message.issueClassificationCode
    ++ (WeightedStockPriceAverage.encode message.weightedStockPriceAverage
    ++ (StockPriceAverageDayOnDayComparison.encode message.stockPriceAverageDayOnDayComparison))))

def decode (bytes : List UInt8) : Option (WeightedStockPriceAverageMessage × List UInt8) := do
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (outputTime, bytes) ← Alpha.decode 6 bytes
  let (issueClassificationCode, bytes) ← Alpha.decode 4 bytes
  let (weightedStockPriceAverage, bytes) ← WeightedStockPriceAverage.decode bytes
  let (stockPriceAverageDayOnDayComparison, bytes) ← StockPriceAverageDayOnDayComparison.decode bytes
  pure ({ reserved2, outputTime, issueClassificationCode, weightedStockPriceAverage, stockPriceAverageDayOnDayComparison }, bytes)

@[simp] theorem encode_length (message : WeightedStockPriceAverageMessage) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, WeightedStockPriceAverage.encode_length, StockPriceAverageDayOnDayComparison.encode_length]

theorem encode_length_pos (message : WeightedStockPriceAverageMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : WeightedStockPriceAverageMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, WeightedStockPriceAverage.decode_encode, some_bind]
  dsimp only
  rw [StockPriceAverageDayOnDayComparison.decode_encode, some_bind]
  rfl

end WeightedStockPriceAverageMessage

/-- Simple Stock Price Average By Industry Message: 44 bytes -/
structure SimpleStockPriceAverageByIndustryMessage where
  reserved2 : Alpha 2
  outputTime : Alpha 6
  industryCode : Alpha 4
  simpleStockPriceAverage : SimpleStockPriceAverage
  stockPriceAverageDayOnDayComparison : StockPriceAverageDayOnDayComparison
  deriving DecidableEq, Repr

namespace SimpleStockPriceAverageByIndustryMessage

def encode (message : SimpleStockPriceAverageByIndustryMessage) : List UInt8 :=
  Alpha.encode message.reserved2
    ++ (Alpha.encode message.outputTime
    ++ (Alpha.encode message.industryCode
    ++ (SimpleStockPriceAverage.encode message.simpleStockPriceAverage
    ++ (StockPriceAverageDayOnDayComparison.encode message.stockPriceAverageDayOnDayComparison))))

def decode (bytes : List UInt8) : Option (SimpleStockPriceAverageByIndustryMessage × List UInt8) := do
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (outputTime, bytes) ← Alpha.decode 6 bytes
  let (industryCode, bytes) ← Alpha.decode 4 bytes
  let (simpleStockPriceAverage, bytes) ← SimpleStockPriceAverage.decode bytes
  let (stockPriceAverageDayOnDayComparison, bytes) ← StockPriceAverageDayOnDayComparison.decode bytes
  pure ({ reserved2, outputTime, industryCode, simpleStockPriceAverage, stockPriceAverageDayOnDayComparison }, bytes)

@[simp] theorem encode_length (message : SimpleStockPriceAverageByIndustryMessage) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, SimpleStockPriceAverage.encode_length, StockPriceAverageDayOnDayComparison.encode_length]

theorem encode_length_pos (message : SimpleStockPriceAverageByIndustryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SimpleStockPriceAverageByIndustryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SimpleStockPriceAverage.decode_encode, some_bind]
  dsimp only
  rw [StockPriceAverageDayOnDayComparison.decode_encode, some_bind]
  rfl

end SimpleStockPriceAverageByIndustryMessage

/-- Overall Simple Average: 32 bytes -/
structure OverallSimpleAverage where
  unitFlag : UnitFlag
  simpleAverageC14 : Alpha 14
  sign : Sign
  secondUnitFlag : SecondUnitFlag
  dayOnDayComparisonC14 : Alpha 14
  secondSign : SecondSign
  deriving DecidableEq, Repr

namespace OverallSimpleAverage

def encode (message : OverallSimpleAverage) : List UInt8 :=
  UnitFlag.encode message.unitFlag
    ++ (Alpha.encode message.simpleAverageC14
    ++ (Sign.encode message.sign
    ++ (SecondUnitFlag.encode message.secondUnitFlag
    ++ (Alpha.encode message.dayOnDayComparisonC14
    ++ (SecondSign.encode message.secondSign)))))

def decode (bytes : List UInt8) : Option (OverallSimpleAverage × List UInt8) := do
  let (unitFlag, bytes) ← UnitFlag.decode bytes
  let (simpleAverageC14, bytes) ← Alpha.decode 14 bytes
  let (sign, bytes) ← Sign.decode bytes
  let (secondUnitFlag, bytes) ← SecondUnitFlag.decode bytes
  let (dayOnDayComparisonC14, bytes) ← Alpha.decode 14 bytes
  let (secondSign, bytes) ← SecondSign.decode bytes
  pure ({ unitFlag, simpleAverageC14, sign, secondUnitFlag, dayOnDayComparisonC14, secondSign }, bytes)

@[simp] theorem encode_length (message : OverallSimpleAverage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, UnitFlag.encode_length, Alpha.encode_length, Sign.encode_length, SecondUnitFlag.encode_length, SecondSign.encode_length]

theorem encode_length_pos (message : OverallSimpleAverage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OverallSimpleAverage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, UnitFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Sign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecondUnitFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [SecondSign.decode_encode, some_bind]
  rfl

end OverallSimpleAverage

/-- Overall Divergence Average: 18 bytes -/
structure OverallDivergenceAverage where
  divergenceAverageC8 : Alpha 8
  sign : Sign
  dayOnDayComparisonC8 : Alpha 8
  secondSign : SecondSign
  deriving DecidableEq, Repr

namespace OverallDivergenceAverage

def encode (message : OverallDivergenceAverage) : List UInt8 :=
  Alpha.encode message.divergenceAverageC8
    ++ (Sign.encode message.sign
    ++ (Alpha.encode message.dayOnDayComparisonC8
    ++ (SecondSign.encode message.secondSign)))

def decode (bytes : List UInt8) : Option (OverallDivergenceAverage × List UInt8) := do
  let (divergenceAverageC8, bytes) ← Alpha.decode 8 bytes
  let (sign, bytes) ← Sign.decode bytes
  let (dayOnDayComparisonC8, bytes) ← Alpha.decode 8 bytes
  let (secondSign, bytes) ← SecondSign.decode bytes
  pure ({ divergenceAverageC8, sign, dayOnDayComparisonC8, secondSign }, bytes)

@[simp] theorem encode_length (message : OverallDivergenceAverage) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, Sign.encode_length, SecondSign.encode_length]

theorem encode_length_pos (message : OverallDivergenceAverage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OverallDivergenceAverage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Sign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [SecondSign.decode_encode, some_bind]
  rfl

end OverallDivergenceAverage

/-- Overall Parity Average: 32 bytes -/
structure OverallParityAverage where
  unitFlag : UnitFlag
  parityAverageC14 : Alpha 14
  sign : Sign
  secondUnitFlag : SecondUnitFlag
  dayOnDayComparisonC14 : Alpha 14
  secondSign : SecondSign
  deriving DecidableEq, Repr

namespace OverallParityAverage

def encode (message : OverallParityAverage) : List UInt8 :=
  UnitFlag.encode message.unitFlag
    ++ (Alpha.encode message.parityAverageC14
    ++ (Sign.encode message.sign
    ++ (SecondUnitFlag.encode message.secondUnitFlag
    ++ (Alpha.encode message.dayOnDayComparisonC14
    ++ (SecondSign.encode message.secondSign)))))

def decode (bytes : List UInt8) : Option (OverallParityAverage × List UInt8) := do
  let (unitFlag, bytes) ← UnitFlag.decode bytes
  let (parityAverageC14, bytes) ← Alpha.decode 14 bytes
  let (sign, bytes) ← Sign.decode bytes
  let (secondUnitFlag, bytes) ← SecondUnitFlag.decode bytes
  let (dayOnDayComparisonC14, bytes) ← Alpha.decode 14 bytes
  let (secondSign, bytes) ← SecondSign.decode bytes
  pure ({ unitFlag, parityAverageC14, sign, secondUnitFlag, dayOnDayComparisonC14, secondSign }, bytes)

@[simp] theorem encode_length (message : OverallParityAverage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, UnitFlag.encode_length, Alpha.encode_length, Sign.encode_length, SecondUnitFlag.encode_length, SecondSign.encode_length]

theorem encode_length_pos (message : OverallParityAverage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OverallParityAverage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, UnitFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Sign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecondUnitFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [SecondSign.decode_encode, some_bind]
  rfl

end OverallParityAverage

/-- Overall Direct Yield Average: 18 bytes -/
structure OverallDirectYieldAverage where
  directYieldAverageC8 : Alpha 8
  sign : Sign
  dayOnDayComparisonC8 : Alpha 8
  secondSign : SecondSign
  deriving DecidableEq, Repr

namespace OverallDirectYieldAverage

def encode (message : OverallDirectYieldAverage) : List UInt8 :=
  Alpha.encode message.directYieldAverageC8
    ++ (Sign.encode message.sign
    ++ (Alpha.encode message.dayOnDayComparisonC8
    ++ (SecondSign.encode message.secondSign)))

def decode (bytes : List UInt8) : Option (OverallDirectYieldAverage × List UInt8) := do
  let (directYieldAverageC8, bytes) ← Alpha.decode 8 bytes
  let (sign, bytes) ← Sign.decode bytes
  let (dayOnDayComparisonC8, bytes) ← Alpha.decode 8 bytes
  let (secondSign, bytes) ← SecondSign.decode bytes
  pure ({ directYieldAverageC8, sign, dayOnDayComparisonC8, secondSign }, bytes)

@[simp] theorem encode_length (message : OverallDirectYieldAverage) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, Sign.encode_length, SecondSign.encode_length]

theorem encode_length_pos (message : OverallDirectYieldAverage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OverallDirectYieldAverage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Sign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [SecondSign.decode_encode, some_bind]
  rfl

end OverallDirectYieldAverage

/-- Overall: 100 bytes -/
structure Overall where
  overallSimpleAverage : OverallSimpleAverage
  overallDivergenceAverage : OverallDivergenceAverage
  overallParityAverage : OverallParityAverage
  overallDirectYieldAverage : OverallDirectYieldAverage
  deriving DecidableEq, Repr

namespace Overall

def encode (message : Overall) : List UInt8 :=
  OverallSimpleAverage.encode message.overallSimpleAverage
    ++ (OverallDivergenceAverage.encode message.overallDivergenceAverage
    ++ (OverallParityAverage.encode message.overallParityAverage
    ++ (OverallDirectYieldAverage.encode message.overallDirectYieldAverage)))

def decode (bytes : List UInt8) : Option (Overall × List UInt8) := do
  let (overallSimpleAverage, bytes) ← OverallSimpleAverage.decode bytes
  let (overallDivergenceAverage, bytes) ← OverallDivergenceAverage.decode bytes
  let (overallParityAverage, bytes) ← OverallParityAverage.decode bytes
  let (overallDirectYieldAverage, bytes) ← OverallDirectYieldAverage.decode bytes
  pure ({ overallSimpleAverage, overallDivergenceAverage, overallParityAverage, overallDirectYieldAverage }, bytes)

@[simp] theorem encode_length (message : Overall) : (encode message).length = 100 := by
  unfold encode
  simp only [List.length_append, OverallSimpleAverage.encode_length, OverallDivergenceAverage.encode_length, OverallParityAverage.encode_length, OverallDirectYieldAverage.encode_length]

theorem encode_length_pos (message : Overall) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Overall) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OverallSimpleAverage.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OverallDivergenceAverage.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OverallParityAverage.decode_encode, some_bind]
  dsimp only
  rw [OverallDirectYieldAverage.decode_encode, some_bind]
  rfl

end Overall

/-- Simple Average: 16 bytes -/
structure SimpleAverage where
  unitFlag : UnitFlag
  simpleAverageC14 : Alpha 14
  sign : Sign
  deriving DecidableEq, Repr

namespace SimpleAverage

def encode (message : SimpleAverage) : List UInt8 :=
  UnitFlag.encode message.unitFlag
    ++ (Alpha.encode message.simpleAverageC14
    ++ (Sign.encode message.sign))

def decode (bytes : List UInt8) : Option (SimpleAverage × List UInt8) := do
  let (unitFlag, bytes) ← UnitFlag.decode bytes
  let (simpleAverageC14, bytes) ← Alpha.decode 14 bytes
  let (sign, bytes) ← Sign.decode bytes
  pure ({ unitFlag, simpleAverageC14, sign }, bytes)

@[simp] theorem encode_length (message : SimpleAverage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, UnitFlag.encode_length, Alpha.encode_length, Sign.encode_length]

theorem encode_length_pos (message : SimpleAverage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SimpleAverage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, UnitFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Sign.decode_encode, some_bind]
  rfl

end SimpleAverage

/-- Divergence Average: 9 bytes -/
structure DivergenceAverage where
  divergenceAverageC8 : Alpha 8
  sign : Sign
  deriving DecidableEq, Repr

namespace DivergenceAverage

def encode (message : DivergenceAverage) : List UInt8 :=
  Alpha.encode message.divergenceAverageC8
    ++ (Sign.encode message.sign)

def decode (bytes : List UInt8) : Option (DivergenceAverage × List UInt8) := do
  let (divergenceAverageC8, bytes) ← Alpha.decode 8 bytes
  let (sign, bytes) ← Sign.decode bytes
  pure ({ divergenceAverageC8, sign }, bytes)

@[simp] theorem encode_length (message : DivergenceAverage) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, Sign.encode_length]

theorem encode_length_pos (message : DivergenceAverage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DivergenceAverage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Sign.decode_encode, some_bind]
  rfl

end DivergenceAverage

/-- Parity Average: 16 bytes -/
structure ParityAverage where
  unitFlag : UnitFlag
  parityAverageC14 : Alpha 14
  sign : Sign
  deriving DecidableEq, Repr

namespace ParityAverage

def encode (message : ParityAverage) : List UInt8 :=
  UnitFlag.encode message.unitFlag
    ++ (Alpha.encode message.parityAverageC14
    ++ (Sign.encode message.sign))

def decode (bytes : List UInt8) : Option (ParityAverage × List UInt8) := do
  let (unitFlag, bytes) ← UnitFlag.decode bytes
  let (parityAverageC14, bytes) ← Alpha.decode 14 bytes
  let (sign, bytes) ← Sign.decode bytes
  pure ({ unitFlag, parityAverageC14, sign }, bytes)

@[simp] theorem encode_length (message : ParityAverage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, UnitFlag.encode_length, Alpha.encode_length, Sign.encode_length]

theorem encode_length_pos (message : ParityAverage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ParityAverage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, UnitFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Sign.decode_encode, some_bind]
  rfl

end ParityAverage

/-- Direct Yield Average: 9 bytes -/
structure DirectYieldAverage where
  directYieldAverageC8 : Alpha 8
  sign : Sign
  deriving DecidableEq, Repr

namespace DirectYieldAverage

def encode (message : DirectYieldAverage) : List UInt8 :=
  Alpha.encode message.directYieldAverageC8
    ++ (Sign.encode message.sign)

def decode (bytes : List UInt8) : Option (DirectYieldAverage × List UInt8) := do
  let (directYieldAverageC8, bytes) ← Alpha.decode 8 bytes
  let (sign, bytes) ← Sign.decode bytes
  pure ({ directYieldAverageC8, sign }, bytes)

@[simp] theorem encode_length (message : DirectYieldAverage) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, Sign.encode_length]

theorem encode_length_pos (message : DirectYieldAverage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DirectYieldAverage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Sign.decode_encode, some_bind]
  rfl

end DirectYieldAverage

/-- Parity 100 Or Higher: 50 bytes -/
structure Parity100OrHigher where
  simpleAverage : SimpleAverage
  divergenceAverage : DivergenceAverage
  parityAverage : ParityAverage
  directYieldAverage : DirectYieldAverage
  deriving DecidableEq, Repr

namespace Parity100OrHigher

def encode (message : Parity100OrHigher) : List UInt8 :=
  SimpleAverage.encode message.simpleAverage
    ++ (DivergenceAverage.encode message.divergenceAverage
    ++ (ParityAverage.encode message.parityAverage
    ++ (DirectYieldAverage.encode message.directYieldAverage)))

def decode (bytes : List UInt8) : Option (Parity100OrHigher × List UInt8) := do
  let (simpleAverage, bytes) ← SimpleAverage.decode bytes
  let (divergenceAverage, bytes) ← DivergenceAverage.decode bytes
  let (parityAverage, bytes) ← ParityAverage.decode bytes
  let (directYieldAverage, bytes) ← DirectYieldAverage.decode bytes
  pure ({ simpleAverage, divergenceAverage, parityAverage, directYieldAverage }, bytes)

@[simp] theorem encode_length (message : Parity100OrHigher) : (encode message).length = 50 := by
  unfold encode
  simp only [List.length_append, SimpleAverage.encode_length, DivergenceAverage.encode_length, ParityAverage.encode_length, DirectYieldAverage.encode_length]

theorem encode_length_pos (message : Parity100OrHigher) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Parity100OrHigher) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, SimpleAverage.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DivergenceAverage.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ParityAverage.decode_encode, some_bind]
  dsimp only
  rw [DirectYieldAverage.decode_encode, some_bind]
  rfl

end Parity100OrHigher

/-- Parity Less Than 100: 50 bytes -/
structure ParityLessThan100 where
  simpleAverage : SimpleAverage
  divergenceAverage : DivergenceAverage
  parityAverage : ParityAverage
  directYieldAverage : DirectYieldAverage
  deriving DecidableEq, Repr

namespace ParityLessThan100

def encode (message : ParityLessThan100) : List UInt8 :=
  SimpleAverage.encode message.simpleAverage
    ++ (DivergenceAverage.encode message.divergenceAverage
    ++ (ParityAverage.encode message.parityAverage
    ++ (DirectYieldAverage.encode message.directYieldAverage)))

def decode (bytes : List UInt8) : Option (ParityLessThan100 × List UInt8) := do
  let (simpleAverage, bytes) ← SimpleAverage.decode bytes
  let (divergenceAverage, bytes) ← DivergenceAverage.decode bytes
  let (parityAverage, bytes) ← ParityAverage.decode bytes
  let (directYieldAverage, bytes) ← DirectYieldAverage.decode bytes
  pure ({ simpleAverage, divergenceAverage, parityAverage, directYieldAverage }, bytes)

@[simp] theorem encode_length (message : ParityLessThan100) : (encode message).length = 50 := by
  unfold encode
  simp only [List.length_append, SimpleAverage.encode_length, DivergenceAverage.encode_length, ParityAverage.encode_length, DirectYieldAverage.encode_length]

theorem encode_length_pos (message : ParityLessThan100) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ParityLessThan100) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, SimpleAverage.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DivergenceAverage.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ParityAverage.decode_encode, some_bind]
  dsimp only
  rw [DirectYieldAverage.decode_encode, some_bind]
  rfl

end ParityLessThan100

/-- Japanese Yen Cb Indicator Message: 208 bytes -/
structure JapaneseYenCbIndicatorMessage where
  reserved2 : Alpha 2
  outputTime : Alpha 6
  overall : Overall
  parity100OrHigher : Parity100OrHigher
  parityLessThan100 : ParityLessThan100
  deriving DecidableEq, Repr

namespace JapaneseYenCbIndicatorMessage

def encode (message : JapaneseYenCbIndicatorMessage) : List UInt8 :=
  Alpha.encode message.reserved2
    ++ (Alpha.encode message.outputTime
    ++ (Overall.encode message.overall
    ++ (Parity100OrHigher.encode message.parity100OrHigher
    ++ (ParityLessThan100.encode message.parityLessThan100))))

def decode (bytes : List UInt8) : Option (JapaneseYenCbIndicatorMessage × List UInt8) := do
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (outputTime, bytes) ← Alpha.decode 6 bytes
  let (overall, bytes) ← Overall.decode bytes
  let (parity100OrHigher, bytes) ← Parity100OrHigher.decode bytes
  let (parityLessThan100, bytes) ← ParityLessThan100.decode bytes
  pure ({ reserved2, outputTime, overall, parity100OrHigher, parityLessThan100 }, bytes)

@[simp] theorem encode_length (message : JapaneseYenCbIndicatorMessage) : (encode message).length = 208 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, Overall.encode_length, Parity100OrHigher.encode_length, ParityLessThan100.encode_length]

theorem encode_length_pos (message : JapaneseYenCbIndicatorMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : JapaneseYenCbIndicatorMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Overall.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Parity100OrHigher.decode_encode, some_bind]
  dsimp only
  rw [ParityLessThan100.decode_encode, some_bind]
  rfl

end JapaneseYenCbIndicatorMessage

/-- Number Of Active Issues: 10 bytes -/
structure NumberOfActiveIssues where
  numberOfIssues : Alpha 5
  ratio : Alpha 5
  deriving DecidableEq, Repr

namespace NumberOfActiveIssues

def encode (message : NumberOfActiveIssues) : List UInt8 :=
  Alpha.encode message.numberOfIssues
    ++ (Alpha.encode message.ratio)

def decode (bytes : List UInt8) : Option (NumberOfActiveIssues × List UInt8) := do
  let (numberOfIssues, bytes) ← Alpha.decode 5 bytes
  let (ratio, bytes) ← Alpha.decode 5 bytes
  pure ({ numberOfIssues, ratio }, bytes)

@[simp] theorem encode_length (message : NumberOfActiveIssues) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : NumberOfActiveIssues) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NumberOfActiveIssues) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end NumberOfActiveIssues

/-- Number Of Gainers: 10 bytes -/
structure NumberOfGainers where
  numberOfIssues : Alpha 5
  ratio : Alpha 5
  deriving DecidableEq, Repr

namespace NumberOfGainers

def encode (message : NumberOfGainers) : List UInt8 :=
  Alpha.encode message.numberOfIssues
    ++ (Alpha.encode message.ratio)

def decode (bytes : List UInt8) : Option (NumberOfGainers × List UInt8) := do
  let (numberOfIssues, bytes) ← Alpha.decode 5 bytes
  let (ratio, bytes) ← Alpha.decode 5 bytes
  pure ({ numberOfIssues, ratio }, bytes)

@[simp] theorem encode_length (message : NumberOfGainers) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : NumberOfGainers) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NumberOfGainers) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end NumberOfGainers

/-- Number Of Decliners: 10 bytes -/
structure NumberOfDecliners where
  numberOfIssues : Alpha 5
  ratio : Alpha 5
  deriving DecidableEq, Repr

namespace NumberOfDecliners

def encode (message : NumberOfDecliners) : List UInt8 :=
  Alpha.encode message.numberOfIssues
    ++ (Alpha.encode message.ratio)

def decode (bytes : List UInt8) : Option (NumberOfDecliners × List UInt8) := do
  let (numberOfIssues, bytes) ← Alpha.decode 5 bytes
  let (ratio, bytes) ← Alpha.decode 5 bytes
  pure ({ numberOfIssues, ratio }, bytes)

@[simp] theorem encode_length (message : NumberOfDecliners) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : NumberOfDecliners) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NumberOfDecliners) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end NumberOfDecliners

/-- Number Of Issues With No Change: 10 bytes -/
structure NumberOfIssuesWithNoChange where
  numberOfIssues : Alpha 5
  ratio : Alpha 5
  deriving DecidableEq, Repr

namespace NumberOfIssuesWithNoChange

def encode (message : NumberOfIssuesWithNoChange) : List UInt8 :=
  Alpha.encode message.numberOfIssues
    ++ (Alpha.encode message.ratio)

def decode (bytes : List UInt8) : Option (NumberOfIssuesWithNoChange × List UInt8) := do
  let (numberOfIssues, bytes) ← Alpha.decode 5 bytes
  let (ratio, bytes) ← Alpha.decode 5 bytes
  pure ({ numberOfIssues, ratio }, bytes)

@[simp] theorem encode_length (message : NumberOfIssuesWithNoChange) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : NumberOfIssuesWithNoChange) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NumberOfIssuesWithNoChange) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end NumberOfIssuesWithNoChange

/-- Number Of Issues With No Comparison: 10 bytes -/
structure NumberOfIssuesWithNoComparison where
  numberOfIssues : Alpha 5
  ratio : Alpha 5
  deriving DecidableEq, Repr

namespace NumberOfIssuesWithNoComparison

def encode (message : NumberOfIssuesWithNoComparison) : List UInt8 :=
  Alpha.encode message.numberOfIssues
    ++ (Alpha.encode message.ratio)

def decode (bytes : List UInt8) : Option (NumberOfIssuesWithNoComparison × List UInt8) := do
  let (numberOfIssues, bytes) ← Alpha.decode 5 bytes
  let (ratio, bytes) ← Alpha.decode 5 bytes
  pure ({ numberOfIssues, ratio }, bytes)

@[simp] theorem encode_length (message : NumberOfIssuesWithNoComparison) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : NumberOfIssuesWithNoComparison) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NumberOfIssuesWithNoComparison) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end NumberOfIssuesWithNoComparison

/-- Number Of Inactive Issues: 10 bytes -/
structure NumberOfInactiveIssues where
  numberOfIssues : Alpha 5
  ratio : Alpha 5
  deriving DecidableEq, Repr

namespace NumberOfInactiveIssues

def encode (message : NumberOfInactiveIssues) : List UInt8 :=
  Alpha.encode message.numberOfIssues
    ++ (Alpha.encode message.ratio)

def decode (bytes : List UInt8) : Option (NumberOfInactiveIssues × List UInt8) := do
  let (numberOfIssues, bytes) ← Alpha.decode 5 bytes
  let (ratio, bytes) ← Alpha.decode 5 bytes
  pure ({ numberOfIssues, ratio }, bytes)

@[simp] theorem encode_length (message : NumberOfInactiveIssues) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : NumberOfInactiveIssues) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NumberOfInactiveIssues) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end NumberOfInactiveIssues

/-- Number Of Gainers Decliners Message: 82 bytes -/
structure NumberOfGainersDeclinersMessage where
  reserved2 : Alpha 2
  outputTime : Alpha 6
  issueClassificationCode : Alpha 4
  numberOfListedCompanies : Alpha 5
  numberOfListedIssues : Alpha 5
  numberOfActiveIssues : NumberOfActiveIssues
  numberOfGainers : NumberOfGainers
  numberOfDecliners : NumberOfDecliners
  numberOfIssuesWithNoChange : NumberOfIssuesWithNoChange
  numberOfIssuesWithNoComparison : NumberOfIssuesWithNoComparison
  numberOfInactiveIssues : NumberOfInactiveIssues
  deriving DecidableEq, Repr

namespace NumberOfGainersDeclinersMessage

def encode (message : NumberOfGainersDeclinersMessage) : List UInt8 :=
  Alpha.encode message.reserved2
    ++ (Alpha.encode message.outputTime
    ++ (Alpha.encode message.issueClassificationCode
    ++ (Alpha.encode message.numberOfListedCompanies
    ++ (Alpha.encode message.numberOfListedIssues
    ++ (NumberOfActiveIssues.encode message.numberOfActiveIssues
    ++ (NumberOfGainers.encode message.numberOfGainers
    ++ (NumberOfDecliners.encode message.numberOfDecliners
    ++ (NumberOfIssuesWithNoChange.encode message.numberOfIssuesWithNoChange
    ++ (NumberOfIssuesWithNoComparison.encode message.numberOfIssuesWithNoComparison
    ++ (NumberOfInactiveIssues.encode message.numberOfInactiveIssues))))))))))

def decode (bytes : List UInt8) : Option (NumberOfGainersDeclinersMessage × List UInt8) := do
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (outputTime, bytes) ← Alpha.decode 6 bytes
  let (issueClassificationCode, bytes) ← Alpha.decode 4 bytes
  let (numberOfListedCompanies, bytes) ← Alpha.decode 5 bytes
  let (numberOfListedIssues, bytes) ← Alpha.decode 5 bytes
  let (numberOfActiveIssues, bytes) ← NumberOfActiveIssues.decode bytes
  let (numberOfGainers, bytes) ← NumberOfGainers.decode bytes
  let (numberOfDecliners, bytes) ← NumberOfDecliners.decode bytes
  let (numberOfIssuesWithNoChange, bytes) ← NumberOfIssuesWithNoChange.decode bytes
  let (numberOfIssuesWithNoComparison, bytes) ← NumberOfIssuesWithNoComparison.decode bytes
  let (numberOfInactiveIssues, bytes) ← NumberOfInactiveIssues.decode bytes
  pure ({ reserved2, outputTime, issueClassificationCode, numberOfListedCompanies, numberOfListedIssues, numberOfActiveIssues, numberOfGainers, numberOfDecliners, numberOfIssuesWithNoChange, numberOfIssuesWithNoComparison, numberOfInactiveIssues }, bytes)

@[simp] theorem encode_length (message : NumberOfGainersDeclinersMessage) : (encode message).length = 82 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, NumberOfActiveIssues.encode_length, NumberOfGainers.encode_length, NumberOfDecliners.encode_length, NumberOfIssuesWithNoChange.encode_length, NumberOfIssuesWithNoComparison.encode_length, NumberOfInactiveIssues.encode_length]

theorem encode_length_pos (message : NumberOfGainersDeclinersMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NumberOfGainersDeclinersMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, NumberOfActiveIssues.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NumberOfGainers.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NumberOfDecliners.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NumberOfIssuesWithNoChange.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NumberOfIssuesWithNoComparison.decode_encode, some_bind]
  dsimp only
  rw [NumberOfInactiveIssues.decode_encode, some_bind]
  rfl

end NumberOfGainersDeclinersMessage

/-- Estimated Total Trading Volume: 15 bytes -/
structure EstimatedTotalTradingVolume where
  tradingVolumeTurnoverUnitFlag : TradingVolumeTurnoverUnitFlag
  estimatedTotalTradingVolumeC14 : Alpha 14
  deriving DecidableEq, Repr

namespace EstimatedTotalTradingVolume

def encode (message : EstimatedTotalTradingVolume) : List UInt8 :=
  TradingVolumeTurnoverUnitFlag.encode message.tradingVolumeTurnoverUnitFlag
    ++ (Alpha.encode message.estimatedTotalTradingVolumeC14)

def decode (bytes : List UInt8) : Option (EstimatedTotalTradingVolume × List UInt8) := do
  let (tradingVolumeTurnoverUnitFlag, bytes) ← TradingVolumeTurnoverUnitFlag.decode bytes
  let (estimatedTotalTradingVolumeC14, bytes) ← Alpha.decode 14 bytes
  pure ({ tradingVolumeTurnoverUnitFlag, estimatedTotalTradingVolumeC14 }, bytes)

@[simp] theorem encode_length (message : EstimatedTotalTradingVolume) : (encode message).length = 15 := by
  unfold encode
  simp only [List.length_append, TradingVolumeTurnoverUnitFlag.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : EstimatedTotalTradingVolume) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EstimatedTotalTradingVolume) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, TradingVolumeTurnoverUnitFlag.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end EstimatedTotalTradingVolume

/-- Estimated Total Trading Volume Message: 29 bytes -/
structure EstimatedTotalTradingVolumeMessage where
  reserved2 : Alpha 2
  outputTime : Alpha 6
  issueClassificationCode : Alpha 4
  otherClassificationCode : Alpha 2
  estimatedTotalTradingVolume : EstimatedTotalTradingVolume
  deriving DecidableEq, Repr

namespace EstimatedTotalTradingVolumeMessage

def encode (message : EstimatedTotalTradingVolumeMessage) : List UInt8 :=
  Alpha.encode message.reserved2
    ++ (Alpha.encode message.outputTime
    ++ (Alpha.encode message.issueClassificationCode
    ++ (Alpha.encode message.otherClassificationCode
    ++ (EstimatedTotalTradingVolume.encode message.estimatedTotalTradingVolume))))

def decode (bytes : List UInt8) : Option (EstimatedTotalTradingVolumeMessage × List UInt8) := do
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (outputTime, bytes) ← Alpha.decode 6 bytes
  let (issueClassificationCode, bytes) ← Alpha.decode 4 bytes
  let (otherClassificationCode, bytes) ← Alpha.decode 2 bytes
  let (estimatedTotalTradingVolume, bytes) ← EstimatedTotalTradingVolume.decode bytes
  pure ({ reserved2, outputTime, issueClassificationCode, otherClassificationCode, estimatedTotalTradingVolume }, bytes)

@[simp] theorem encode_length (message : EstimatedTotalTradingVolumeMessage) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, EstimatedTotalTradingVolume.encode_length]

theorem encode_length_pos (message : EstimatedTotalTradingVolumeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EstimatedTotalTradingVolumeMessage) (rest : List UInt8) :
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
  rw [EstimatedTotalTradingVolume.decode_encode, some_bind]
  rfl

end EstimatedTotalTradingVolumeMessage

/-- Estimated Total Turnover: 16 bytes -/
structure EstimatedTotalTurnover where
  tradingVolumeTurnoverUnitFlag : TradingVolumeTurnoverUnitFlag
  estimatedTotalTurnoverC14 : Alpha 14
  reserved1 : Alpha 1
  deriving DecidableEq, Repr

namespace EstimatedTotalTurnover

def encode (message : EstimatedTotalTurnover) : List UInt8 :=
  TradingVolumeTurnoverUnitFlag.encode message.tradingVolumeTurnoverUnitFlag
    ++ (Alpha.encode message.estimatedTotalTurnoverC14
    ++ (Alpha.encode message.reserved1))

def decode (bytes : List UInt8) : Option (EstimatedTotalTurnover × List UInt8) := do
  let (tradingVolumeTurnoverUnitFlag, bytes) ← TradingVolumeTurnoverUnitFlag.decode bytes
  let (estimatedTotalTurnoverC14, bytes) ← Alpha.decode 14 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  pure ({ tradingVolumeTurnoverUnitFlag, estimatedTotalTurnoverC14, reserved1 }, bytes)

@[simp] theorem encode_length (message : EstimatedTotalTurnover) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, TradingVolumeTurnoverUnitFlag.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : EstimatedTotalTurnover) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EstimatedTotalTurnover) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, TradingVolumeTurnoverUnitFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end EstimatedTotalTurnover

/-- Estimated Total Turnover Message: 30 bytes -/
structure EstimatedTotalTurnoverMessage where
  reserved2 : Alpha 2
  outputTime : Alpha 6
  issueClassificationCode : Alpha 4
  otherClassificationFlag : Alpha 2
  estimatedTotalTurnover : EstimatedTotalTurnover
  deriving DecidableEq, Repr

namespace EstimatedTotalTurnoverMessage

def encode (message : EstimatedTotalTurnoverMessage) : List UInt8 :=
  Alpha.encode message.reserved2
    ++ (Alpha.encode message.outputTime
    ++ (Alpha.encode message.issueClassificationCode
    ++ (Alpha.encode message.otherClassificationFlag
    ++ (EstimatedTotalTurnover.encode message.estimatedTotalTurnover))))

def decode (bytes : List UInt8) : Option (EstimatedTotalTurnoverMessage × List UInt8) := do
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (outputTime, bytes) ← Alpha.decode 6 bytes
  let (issueClassificationCode, bytes) ← Alpha.decode 4 bytes
  let (otherClassificationFlag, bytes) ← Alpha.decode 2 bytes
  let (estimatedTotalTurnover, bytes) ← EstimatedTotalTurnover.decode bytes
  pure ({ reserved2, outputTime, issueClassificationCode, otherClassificationFlag, estimatedTotalTurnover }, bytes)

@[simp] theorem encode_length (message : EstimatedTotalTurnoverMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, EstimatedTotalTurnover.encode_length]

theorem encode_length_pos (message : EstimatedTotalTurnoverMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EstimatedTotalTurnoverMessage) (rest : List UInt8) :
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
  rw [EstimatedTotalTurnover.decode_encode, some_bind]
  rfl

end EstimatedTotalTurnoverMessage

/-- Vwap By Market: 33 bytes -/
structure VwapByMarket where
  unitFlag : UnitFlag
  vwapByMarketC14 : Alpha 14
  sign : Sign
  reserved1 : Alpha 1
  secondUnitFlag : SecondUnitFlag
  dayOnDayComparisonC14 : Alpha 14
  secondSign : SecondSign
  deriving DecidableEq, Repr

namespace VwapByMarket

def encode (message : VwapByMarket) : List UInt8 :=
  UnitFlag.encode message.unitFlag
    ++ (Alpha.encode message.vwapByMarketC14
    ++ (Sign.encode message.sign
    ++ (Alpha.encode message.reserved1
    ++ (SecondUnitFlag.encode message.secondUnitFlag
    ++ (Alpha.encode message.dayOnDayComparisonC14
    ++ (SecondSign.encode message.secondSign))))))

def decode (bytes : List UInt8) : Option (VwapByMarket × List UInt8) := do
  let (unitFlag, bytes) ← UnitFlag.decode bytes
  let (vwapByMarketC14, bytes) ← Alpha.decode 14 bytes
  let (sign, bytes) ← Sign.decode bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (secondUnitFlag, bytes) ← SecondUnitFlag.decode bytes
  let (dayOnDayComparisonC14, bytes) ← Alpha.decode 14 bytes
  let (secondSign, bytes) ← SecondSign.decode bytes
  pure ({ unitFlag, vwapByMarketC14, sign, reserved1, secondUnitFlag, dayOnDayComparisonC14, secondSign }, bytes)

@[simp] theorem encode_length (message : VwapByMarket) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, UnitFlag.encode_length, Alpha.encode_length, Sign.encode_length, SecondUnitFlag.encode_length, SecondSign.encode_length]

theorem encode_length_pos (message : VwapByMarket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : VwapByMarket) (rest : List UInt8) :
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
  rw [List.append_assoc, SecondUnitFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [SecondSign.decode_encode, some_bind]
  rfl

end VwapByMarket

/-- Vwap By Market Message: 45 bytes -/
structure VwapByMarketMessage where
  reserved2 : Alpha 2
  outputTime : Alpha 6
  issueClassificationCode : Alpha 4
  vwapByMarket : VwapByMarket
  deriving DecidableEq, Repr

namespace VwapByMarketMessage

def encode (message : VwapByMarketMessage) : List UInt8 :=
  Alpha.encode message.reserved2
    ++ (Alpha.encode message.outputTime
    ++ (Alpha.encode message.issueClassificationCode
    ++ (VwapByMarket.encode message.vwapByMarket)))

def decode (bytes : List UInt8) : Option (VwapByMarketMessage × List UInt8) := do
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (outputTime, bytes) ← Alpha.decode 6 bytes
  let (issueClassificationCode, bytes) ← Alpha.decode 4 bytes
  let (vwapByMarket, bytes) ← VwapByMarket.decode bytes
  pure ({ reserved2, outputTime, issueClassificationCode, vwapByMarket }, bytes)

@[simp] theorem encode_length (message : VwapByMarketMessage) : (encode message).length = 45 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, VwapByMarket.encode_length]

theorem encode_length_pos (message : VwapByMarketMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : VwapByMarketMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [VwapByMarket.decode_encode, some_bind]
  rfl

end VwapByMarketMessage

/-- Top Rank By Trading Volume: 30 bytes -/
structure TopRankByTradingVolume where
  rank : Alpha 2
  rankedIssueCode : Alpha 12
  reserved1 : Alpha 1
  tradingVolumeTurnoverUnitFlag : TradingVolumeTurnoverUnitFlag
  tradingVolumeC14 : Alpha 14
  deriving DecidableEq, Repr

namespace TopRankByTradingVolume

def encode (message : TopRankByTradingVolume) : List UInt8 :=
  Alpha.encode message.rank
    ++ (Alpha.encode message.rankedIssueCode
    ++ (Alpha.encode message.reserved1
    ++ (TradingVolumeTurnoverUnitFlag.encode message.tradingVolumeTurnoverUnitFlag
    ++ (Alpha.encode message.tradingVolumeC14))))

def decode (bytes : List UInt8) : Option (TopRankByTradingVolume × List UInt8) := do
  let (rank, bytes) ← Alpha.decode 2 bytes
  let (rankedIssueCode, bytes) ← Alpha.decode 12 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (tradingVolumeTurnoverUnitFlag, bytes) ← TradingVolumeTurnoverUnitFlag.decode bytes
  let (tradingVolumeC14, bytes) ← Alpha.decode 14 bytes
  pure ({ rank, rankedIssueCode, reserved1, tradingVolumeTurnoverUnitFlag, tradingVolumeC14 }, bytes)

@[simp] theorem encode_length (message : TopRankByTradingVolume) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, TradingVolumeTurnoverUnitFlag.encode_length]

theorem encode_length_pos (message : TopRankByTradingVolume) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TopRankByTradingVolume) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradingVolumeTurnoverUnitFlag.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TopRankByTradingVolume

/-- Ranking By Trading Volume Message: 912 bytes -/
structure RankingByTradingVolumeMessage where
  reserved2 : Alpha 2
  outputTime : Alpha 6
  issueClassificationCode : Alpha 4
  topRankByTradingVolume : Exact 30 TopRankByTradingVolume
  deriving DecidableEq, Repr

namespace RankingByTradingVolumeMessage

def encode (message : RankingByTradingVolumeMessage) : List UInt8 :=
  Alpha.encode message.reserved2
    ++ (Alpha.encode message.outputTime
    ++ (Alpha.encode message.issueClassificationCode
    ++ (encodeMany TopRankByTradingVolume.encode message.topRankByTradingVolume.val)))

def decode (bytes : List UInt8) : Option (RankingByTradingVolumeMessage × List UInt8) := do
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (outputTime, bytes) ← Alpha.decode 6 bytes
  let (issueClassificationCode, bytes) ← Alpha.decode 4 bytes
  let (topRankByTradingVolume_, bytes) ← decodeMany TopRankByTradingVolume.decode 30 bytes
  if fits_topRankByTradingVolume : topRankByTradingVolume_.length = 30 then
    pure ({ reserved2, outputTime, issueClassificationCode, topRankByTradingVolume := ⟨topRankByTradingVolume_, fits_topRankByTradingVolume⟩ }, bytes)
  else none

@[simp] theorem encode_length (message : RankingByTradingVolumeMessage) : (encode message).length = 912 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeMany_length_const TopRankByTradingVolume.encode 30 TopRankByTradingVolume.encode_length, message.topRankByTradingVolume.length_eq]

theorem encode_length_pos (message : RankingByTradingVolumeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RankingByTradingVolumeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_exact 30 TopRankByTradingVolume.encode TopRankByTradingVolume.decode TopRankByTradingVolume.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.topRankByTradingVolume.length_eq]
  rfl

end RankingByTradingVolumeMessage

/-- Top Rank By Turnover: 30 bytes -/
structure TopRankByTurnover where
  rank : Alpha 2
  rankedIssueCode : Alpha 12
  reserved1 : Alpha 1
  tradingVolumeTurnoverUnitFlag : TradingVolumeTurnoverUnitFlag
  turnoverC14 : Alpha 14
  deriving DecidableEq, Repr

namespace TopRankByTurnover

def encode (message : TopRankByTurnover) : List UInt8 :=
  Alpha.encode message.rank
    ++ (Alpha.encode message.rankedIssueCode
    ++ (Alpha.encode message.reserved1
    ++ (TradingVolumeTurnoverUnitFlag.encode message.tradingVolumeTurnoverUnitFlag
    ++ (Alpha.encode message.turnoverC14))))

def decode (bytes : List UInt8) : Option (TopRankByTurnover × List UInt8) := do
  let (rank, bytes) ← Alpha.decode 2 bytes
  let (rankedIssueCode, bytes) ← Alpha.decode 12 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (tradingVolumeTurnoverUnitFlag, bytes) ← TradingVolumeTurnoverUnitFlag.decode bytes
  let (turnoverC14, bytes) ← Alpha.decode 14 bytes
  pure ({ rank, rankedIssueCode, reserved1, tradingVolumeTurnoverUnitFlag, turnoverC14 }, bytes)

@[simp] theorem encode_length (message : TopRankByTurnover) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, TradingVolumeTurnoverUnitFlag.encode_length]

theorem encode_length_pos (message : TopRankByTurnover) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TopRankByTurnover) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradingVolumeTurnoverUnitFlag.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TopRankByTurnover

/-- Ranking By Turnover Message: 912 bytes -/
structure RankingByTurnoverMessage where
  reserved2 : Alpha 2
  outputTime : Alpha 6
  issueClassificationCode : Alpha 4
  topRankByTurnover : Exact 30 TopRankByTurnover
  deriving DecidableEq, Repr

namespace RankingByTurnoverMessage

def encode (message : RankingByTurnoverMessage) : List UInt8 :=
  Alpha.encode message.reserved2
    ++ (Alpha.encode message.outputTime
    ++ (Alpha.encode message.issueClassificationCode
    ++ (encodeMany TopRankByTurnover.encode message.topRankByTurnover.val)))

def decode (bytes : List UInt8) : Option (RankingByTurnoverMessage × List UInt8) := do
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (outputTime, bytes) ← Alpha.decode 6 bytes
  let (issueClassificationCode, bytes) ← Alpha.decode 4 bytes
  let (topRankByTurnover_, bytes) ← decodeMany TopRankByTurnover.decode 30 bytes
  if fits_topRankByTurnover : topRankByTurnover_.length = 30 then
    pure ({ reserved2, outputTime, issueClassificationCode, topRankByTurnover := ⟨topRankByTurnover_, fits_topRankByTurnover⟩ }, bytes)
  else none

@[simp] theorem encode_length (message : RankingByTurnoverMessage) : (encode message).length = 912 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeMany_length_const TopRankByTurnover.encode 30 TopRankByTurnover.encode_length, message.topRankByTurnover.length_eq]

theorem encode_length_pos (message : RankingByTurnoverMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RankingByTurnoverMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_exact 30 TopRankByTurnover.encode TopRankByTurnover.decode TopRankByTurnover.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.topRankByTurnover.length_eq]
  rfl

end RankingByTurnoverMessage

/-- Top Rank By Net Change: 48 bytes -/
structure TopRankByNetChange where
  rank : Alpha 2
  rankedIssueCode : Alpha 12
  stateSign : StateSign
  unitFlag : UnitFlag
  currentPriceC14 : Alpha 14
  sign : Sign
  comparisonType : ComparisonType
  secondUnitFlag : SecondUnitFlag
  netChange : Alpha 14
  secondSign : SecondSign
  deriving DecidableEq, Repr

namespace TopRankByNetChange

def encode (message : TopRankByNetChange) : List UInt8 :=
  Alpha.encode message.rank
    ++ (Alpha.encode message.rankedIssueCode
    ++ (StateSign.encode message.stateSign
    ++ (UnitFlag.encode message.unitFlag
    ++ (Alpha.encode message.currentPriceC14
    ++ (Sign.encode message.sign
    ++ (ComparisonType.encode message.comparisonType
    ++ (SecondUnitFlag.encode message.secondUnitFlag
    ++ (Alpha.encode message.netChange
    ++ (SecondSign.encode message.secondSign)))))))))

def decode (bytes : List UInt8) : Option (TopRankByNetChange × List UInt8) := do
  let (rank, bytes) ← Alpha.decode 2 bytes
  let (rankedIssueCode, bytes) ← Alpha.decode 12 bytes
  let (stateSign, bytes) ← StateSign.decode bytes
  let (unitFlag, bytes) ← UnitFlag.decode bytes
  let (currentPriceC14, bytes) ← Alpha.decode 14 bytes
  let (sign, bytes) ← Sign.decode bytes
  let (comparisonType, bytes) ← ComparisonType.decode bytes
  let (secondUnitFlag, bytes) ← SecondUnitFlag.decode bytes
  let (netChange, bytes) ← Alpha.decode 14 bytes
  let (secondSign, bytes) ← SecondSign.decode bytes
  pure ({ rank, rankedIssueCode, stateSign, unitFlag, currentPriceC14, sign, comparisonType, secondUnitFlag, netChange, secondSign }, bytes)

@[simp] theorem encode_length (message : TopRankByNetChange) : (encode message).length = 48 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, StateSign.encode_length, UnitFlag.encode_length, Sign.encode_length, ComparisonType.encode_length, SecondUnitFlag.encode_length, SecondSign.encode_length]

theorem encode_length_pos (message : TopRankByNetChange) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TopRankByNetChange) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StateSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, UnitFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Sign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ComparisonType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecondUnitFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [SecondSign.decode_encode, some_bind]
  rfl

end TopRankByNetChange

/-- Ranking By Net Change Message: 1453 bytes -/
structure RankingByNetChangeMessage where
  reserved2 : Alpha 2
  outputTime : Alpha 6
  issueClassificationCode : Alpha 4
  netChangeDistinction : NetChangeDistinction
  topRankByNetChange : Exact 30 TopRankByNetChange
  deriving DecidableEq, Repr

namespace RankingByNetChangeMessage

def encode (message : RankingByNetChangeMessage) : List UInt8 :=
  Alpha.encode message.reserved2
    ++ (Alpha.encode message.outputTime
    ++ (Alpha.encode message.issueClassificationCode
    ++ (NetChangeDistinction.encode message.netChangeDistinction
    ++ (encodeMany TopRankByNetChange.encode message.topRankByNetChange.val))))

def decode (bytes : List UInt8) : Option (RankingByNetChangeMessage × List UInt8) := do
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (outputTime, bytes) ← Alpha.decode 6 bytes
  let (issueClassificationCode, bytes) ← Alpha.decode 4 bytes
  let (netChangeDistinction, bytes) ← NetChangeDistinction.decode bytes
  let (topRankByNetChange_, bytes) ← decodeMany TopRankByNetChange.decode 30 bytes
  if fits_topRankByNetChange : topRankByNetChange_.length = 30 then
    pure ({ reserved2, outputTime, issueClassificationCode, netChangeDistinction, topRankByNetChange := ⟨topRankByNetChange_, fits_topRankByNetChange⟩ }, bytes)
  else none

@[simp] theorem encode_length (message : RankingByNetChangeMessage) : (encode message).length = 1453 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, NetChangeDistinction.encode_length, encodeMany_length_const TopRankByNetChange.encode 48 TopRankByNetChange.encode_length, message.topRankByNetChange.length_eq]

theorem encode_length_pos (message : RankingByNetChangeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RankingByNetChangeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeDistinction.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_exact 30 TopRankByNetChange.encode TopRankByNetChange.decode TopRankByNetChange.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.topRankByNetChange.length_eq]
  rfl

end RankingByNetChangeMessage

/-- Top Rank By Net Change Rate: 41 bytes -/
structure TopRankByNetChangeRate where
  rank : Alpha 2
  rankedIssueCode : Alpha 12
  stateSign : StateSign
  unitFlag : UnitFlag
  currentPriceC14 : Alpha 14
  sign : Sign
  comparisonType : ComparisonType
  netChangeRate : Alpha 8
  secondSign : SecondSign
  deriving DecidableEq, Repr

namespace TopRankByNetChangeRate

def encode (message : TopRankByNetChangeRate) : List UInt8 :=
  Alpha.encode message.rank
    ++ (Alpha.encode message.rankedIssueCode
    ++ (StateSign.encode message.stateSign
    ++ (UnitFlag.encode message.unitFlag
    ++ (Alpha.encode message.currentPriceC14
    ++ (Sign.encode message.sign
    ++ (ComparisonType.encode message.comparisonType
    ++ (Alpha.encode message.netChangeRate
    ++ (SecondSign.encode message.secondSign))))))))

def decode (bytes : List UInt8) : Option (TopRankByNetChangeRate × List UInt8) := do
  let (rank, bytes) ← Alpha.decode 2 bytes
  let (rankedIssueCode, bytes) ← Alpha.decode 12 bytes
  let (stateSign, bytes) ← StateSign.decode bytes
  let (unitFlag, bytes) ← UnitFlag.decode bytes
  let (currentPriceC14, bytes) ← Alpha.decode 14 bytes
  let (sign, bytes) ← Sign.decode bytes
  let (comparisonType, bytes) ← ComparisonType.decode bytes
  let (netChangeRate, bytes) ← Alpha.decode 8 bytes
  let (secondSign, bytes) ← SecondSign.decode bytes
  pure ({ rank, rankedIssueCode, stateSign, unitFlag, currentPriceC14, sign, comparisonType, netChangeRate, secondSign }, bytes)

@[simp] theorem encode_length (message : TopRankByNetChangeRate) : (encode message).length = 41 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, StateSign.encode_length, UnitFlag.encode_length, Sign.encode_length, ComparisonType.encode_length, SecondSign.encode_length]

theorem encode_length_pos (message : TopRankByNetChangeRate) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TopRankByNetChangeRate) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StateSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, UnitFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Sign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ComparisonType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [SecondSign.decode_encode, some_bind]
  rfl

end TopRankByNetChangeRate

/-- Ranking By Net Change Rate Message: 1243 bytes -/
structure RankingByNetChangeRateMessage where
  reserved2 : Alpha 2
  outputTime : Alpha 6
  issueClassificationCode : Alpha 4
  netChangeDistinction : NetChangeDistinction
  topRankByNetChangeRate : Exact 30 TopRankByNetChangeRate
  deriving DecidableEq, Repr

namespace RankingByNetChangeRateMessage

def encode (message : RankingByNetChangeRateMessage) : List UInt8 :=
  Alpha.encode message.reserved2
    ++ (Alpha.encode message.outputTime
    ++ (Alpha.encode message.issueClassificationCode
    ++ (NetChangeDistinction.encode message.netChangeDistinction
    ++ (encodeMany TopRankByNetChangeRate.encode message.topRankByNetChangeRate.val))))

def decode (bytes : List UInt8) : Option (RankingByNetChangeRateMessage × List UInt8) := do
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (outputTime, bytes) ← Alpha.decode 6 bytes
  let (issueClassificationCode, bytes) ← Alpha.decode 4 bytes
  let (netChangeDistinction, bytes) ← NetChangeDistinction.decode bytes
  let (topRankByNetChangeRate_, bytes) ← decodeMany TopRankByNetChangeRate.decode 30 bytes
  if fits_topRankByNetChangeRate : topRankByNetChangeRate_.length = 30 then
    pure ({ reserved2, outputTime, issueClassificationCode, netChangeDistinction, topRankByNetChangeRate := ⟨topRankByNetChangeRate_, fits_topRankByNetChangeRate⟩ }, bytes)
  else none

@[simp] theorem encode_length (message : RankingByNetChangeRateMessage) : (encode message).length = 1243 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, NetChangeDistinction.encode_length, encodeMany_length_const TopRankByNetChangeRate.encode 41 TopRankByNetChangeRate.encode_length, message.topRankByNetChangeRate.length_eq]

theorem encode_length_pos (message : RankingByNetChangeRateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RankingByNetChangeRateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeDistinction.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_exact 30 TopRankByNetChangeRate.encode TopRankByNetChangeRate.decode TopRankByNetChangeRate.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.topRankByNetChangeRate.length_eq]
  rfl

end RankingByNetChangeRateMessage

/-- Trading Volume: 60 bytes -/
structure TradingVolume where
  tradingVolumeTurnoverUnitFlag : TradingVolumeTurnoverUnitFlag
  singleIssueTransactionC14 : Alpha 14
  secondTradingVolumeturnoverUnitFlag : SecondTradingVolumeturnoverUnitFlag
  closingPriceTransaction : Alpha 14
  thirdTradingVolumeturnoverUnitFlag : ThirdTradingVolumeturnoverUnitFlag
  basketTransactionC14 : Alpha 14
  fourthTradingVolumeturnoverUnitFlag : FourthTradingVolumeturnoverUnitFlag
  aggregateTradingVolume : Alpha 14
  deriving DecidableEq, Repr

namespace TradingVolume

def encode (message : TradingVolume) : List UInt8 :=
  TradingVolumeTurnoverUnitFlag.encode message.tradingVolumeTurnoverUnitFlag
    ++ (Alpha.encode message.singleIssueTransactionC14
    ++ (SecondTradingVolumeturnoverUnitFlag.encode message.secondTradingVolumeturnoverUnitFlag
    ++ (Alpha.encode message.closingPriceTransaction
    ++ (ThirdTradingVolumeturnoverUnitFlag.encode message.thirdTradingVolumeturnoverUnitFlag
    ++ (Alpha.encode message.basketTransactionC14
    ++ (FourthTradingVolumeturnoverUnitFlag.encode message.fourthTradingVolumeturnoverUnitFlag
    ++ (Alpha.encode message.aggregateTradingVolume)))))))

def decode (bytes : List UInt8) : Option (TradingVolume × List UInt8) := do
  let (tradingVolumeTurnoverUnitFlag, bytes) ← TradingVolumeTurnoverUnitFlag.decode bytes
  let (singleIssueTransactionC14, bytes) ← Alpha.decode 14 bytes
  let (secondTradingVolumeturnoverUnitFlag, bytes) ← SecondTradingVolumeturnoverUnitFlag.decode bytes
  let (closingPriceTransaction, bytes) ← Alpha.decode 14 bytes
  let (thirdTradingVolumeturnoverUnitFlag, bytes) ← ThirdTradingVolumeturnoverUnitFlag.decode bytes
  let (basketTransactionC14, bytes) ← Alpha.decode 14 bytes
  let (fourthTradingVolumeturnoverUnitFlag, bytes) ← FourthTradingVolumeturnoverUnitFlag.decode bytes
  let (aggregateTradingVolume, bytes) ← Alpha.decode 14 bytes
  pure ({ tradingVolumeTurnoverUnitFlag, singleIssueTransactionC14, secondTradingVolumeturnoverUnitFlag, closingPriceTransaction, thirdTradingVolumeturnoverUnitFlag, basketTransactionC14, fourthTradingVolumeturnoverUnitFlag, aggregateTradingVolume }, bytes)

@[simp] theorem encode_length (message : TradingVolume) : (encode message).length = 60 := by
  unfold encode
  simp only [List.length_append, TradingVolumeTurnoverUnitFlag.encode_length, Alpha.encode_length, SecondTradingVolumeturnoverUnitFlag.encode_length, ThirdTradingVolumeturnoverUnitFlag.encode_length, FourthTradingVolumeturnoverUnitFlag.encode_length]

theorem encode_length_pos (message : TradingVolume) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradingVolume) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, TradingVolumeTurnoverUnitFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecondTradingVolumeturnoverUnitFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ThirdTradingVolumeturnoverUnitFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FourthTradingVolumeturnoverUnitFlag.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradingVolume

/-- Turnover: 60 bytes -/
structure Turnover where
  tradingVolumeTurnoverUnitFlag : TradingVolumeTurnoverUnitFlag
  singleIssueTransactionC14 : Alpha 14
  secondTradingVolumeturnoverUnitFlag : SecondTradingVolumeturnoverUnitFlag
  closingPriceTransaction : Alpha 14
  thirdTradingVolumeturnoverUnitFlag : ThirdTradingVolumeturnoverUnitFlag
  basketTransactionC14 : Alpha 14
  fourthTradingVolumeturnoverUnitFlag : FourthTradingVolumeturnoverUnitFlag
  aggregateTurnover : Alpha 14
  deriving DecidableEq, Repr

namespace Turnover

def encode (message : Turnover) : List UInt8 :=
  TradingVolumeTurnoverUnitFlag.encode message.tradingVolumeTurnoverUnitFlag
    ++ (Alpha.encode message.singleIssueTransactionC14
    ++ (SecondTradingVolumeturnoverUnitFlag.encode message.secondTradingVolumeturnoverUnitFlag
    ++ (Alpha.encode message.closingPriceTransaction
    ++ (ThirdTradingVolumeturnoverUnitFlag.encode message.thirdTradingVolumeturnoverUnitFlag
    ++ (Alpha.encode message.basketTransactionC14
    ++ (FourthTradingVolumeturnoverUnitFlag.encode message.fourthTradingVolumeturnoverUnitFlag
    ++ (Alpha.encode message.aggregateTurnover)))))))

def decode (bytes : List UInt8) : Option (Turnover × List UInt8) := do
  let (tradingVolumeTurnoverUnitFlag, bytes) ← TradingVolumeTurnoverUnitFlag.decode bytes
  let (singleIssueTransactionC14, bytes) ← Alpha.decode 14 bytes
  let (secondTradingVolumeturnoverUnitFlag, bytes) ← SecondTradingVolumeturnoverUnitFlag.decode bytes
  let (closingPriceTransaction, bytes) ← Alpha.decode 14 bytes
  let (thirdTradingVolumeturnoverUnitFlag, bytes) ← ThirdTradingVolumeturnoverUnitFlag.decode bytes
  let (basketTransactionC14, bytes) ← Alpha.decode 14 bytes
  let (fourthTradingVolumeturnoverUnitFlag, bytes) ← FourthTradingVolumeturnoverUnitFlag.decode bytes
  let (aggregateTurnover, bytes) ← Alpha.decode 14 bytes
  pure ({ tradingVolumeTurnoverUnitFlag, singleIssueTransactionC14, secondTradingVolumeturnoverUnitFlag, closingPriceTransaction, thirdTradingVolumeturnoverUnitFlag, basketTransactionC14, fourthTradingVolumeturnoverUnitFlag, aggregateTurnover }, bytes)

@[simp] theorem encode_length (message : Turnover) : (encode message).length = 60 := by
  unfold encode
  simp only [List.length_append, TradingVolumeTurnoverUnitFlag.encode_length, Alpha.encode_length, SecondTradingVolumeturnoverUnitFlag.encode_length, ThirdTradingVolumeturnoverUnitFlag.encode_length, FourthTradingVolumeturnoverUnitFlag.encode_length]

theorem encode_length_pos (message : Turnover) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Turnover) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, TradingVolumeTurnoverUnitFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecondTradingVolumeturnoverUnitFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ThirdTradingVolumeturnoverUnitFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FourthTradingVolumeturnoverUnitFlag.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end Turnover

/-- Number Of Transactions: 16 bytes -/
structure NumberOfTransactions where
  singleIssueTransactionC8 : Alpha 8
  basketTransactionC8 : Alpha 8
  deriving DecidableEq, Repr

namespace NumberOfTransactions

def encode (message : NumberOfTransactions) : List UInt8 :=
  Alpha.encode message.singleIssueTransactionC8
    ++ (Alpha.encode message.basketTransactionC8)

def decode (bytes : List UInt8) : Option (NumberOfTransactions × List UInt8) := do
  let (singleIssueTransactionC8, bytes) ← Alpha.decode 8 bytes
  let (basketTransactionC8, bytes) ← Alpha.decode 8 bytes
  pure ({ singleIssueTransactionC8, basketTransactionC8 }, bytes)

@[simp] theorem encode_length (message : NumberOfTransactions) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : NumberOfTransactions) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NumberOfTransactions) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end NumberOfTransactions

/-- ToSTNeT Statistics Message: 146 bytes -/
structure TostnetStatisticsMessage where
  reserved2 : Alpha 2
  outputTime : Alpha 6
  otherClassificationFlag : Alpha 2
  tradingVolume : TradingVolume
  turnover : Turnover
  numberOfTransactions : NumberOfTransactions
  deriving DecidableEq, Repr

namespace TostnetStatisticsMessage

def encode (message : TostnetStatisticsMessage) : List UInt8 :=
  Alpha.encode message.reserved2
    ++ (Alpha.encode message.outputTime
    ++ (Alpha.encode message.otherClassificationFlag
    ++ (TradingVolume.encode message.tradingVolume
    ++ (Turnover.encode message.turnover
    ++ (NumberOfTransactions.encode message.numberOfTransactions)))))

def decode (bytes : List UInt8) : Option (TostnetStatisticsMessage × List UInt8) := do
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (outputTime, bytes) ← Alpha.decode 6 bytes
  let (otherClassificationFlag, bytes) ← Alpha.decode 2 bytes
  let (tradingVolume, bytes) ← TradingVolume.decode bytes
  let (turnover, bytes) ← Turnover.decode bytes
  let (numberOfTransactions, bytes) ← NumberOfTransactions.decode bytes
  pure ({ reserved2, outputTime, otherClassificationFlag, tradingVolume, turnover, numberOfTransactions }, bytes)

@[simp] theorem encode_length (message : TostnetStatisticsMessage) : (encode message).length = 146 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, TradingVolume.encode_length, Turnover.encode_length, NumberOfTransactions.encode_length]

theorem encode_length_pos (message : TostnetStatisticsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TostnetStatisticsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradingVolume.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Turnover.decode_encode, some_bind]
  dsimp only
  rw [NumberOfTransactions.decode_encode, some_bind]
  rfl

end TostnetStatisticsMessage

/-- Open: 23 bytes -/
structure Open where
  unitFlag : UnitFlag
  indexValue : Alpha 14
  sign : Sign
  timeC6Hhmmss : Alpha 6
  flag : Flag
  deriving DecidableEq, Repr

namespace Open

def encode (message : Open) : List UInt8 :=
  UnitFlag.encode message.unitFlag
    ++ (Alpha.encode message.indexValue
    ++ (Sign.encode message.sign
    ++ (Alpha.encode message.timeC6Hhmmss
    ++ (Flag.encode message.flag))))

def decode (bytes : List UInt8) : Option (Open × List UInt8) := do
  let (unitFlag, bytes) ← UnitFlag.decode bytes
  let (indexValue, bytes) ← Alpha.decode 14 bytes
  let (sign, bytes) ← Sign.decode bytes
  let (timeC6Hhmmss, bytes) ← Alpha.decode 6 bytes
  let (flag, bytes) ← Flag.decode bytes
  pure ({ unitFlag, indexValue, sign, timeC6Hhmmss, flag }, bytes)

@[simp] theorem encode_length (message : Open) : (encode message).length = 23 := by
  unfold encode
  simp only [List.length_append, UnitFlag.encode_length, Alpha.encode_length, Sign.encode_length, Flag.encode_length]

theorem encode_length_pos (message : Open) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Open) (rest : List UInt8) :
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
  rw [Flag.decode_encode, some_bind]
  rfl

end Open

/-- Highest: 23 bytes -/
structure Highest where
  unitFlag : UnitFlag
  indexValue : Alpha 14
  sign : Sign
  timeC6Hhmmss : Alpha 6
  flag : Flag
  deriving DecidableEq, Repr

namespace Highest

def encode (message : Highest) : List UInt8 :=
  UnitFlag.encode message.unitFlag
    ++ (Alpha.encode message.indexValue
    ++ (Sign.encode message.sign
    ++ (Alpha.encode message.timeC6Hhmmss
    ++ (Flag.encode message.flag))))

def decode (bytes : List UInt8) : Option (Highest × List UInt8) := do
  let (unitFlag, bytes) ← UnitFlag.decode bytes
  let (indexValue, bytes) ← Alpha.decode 14 bytes
  let (sign, bytes) ← Sign.decode bytes
  let (timeC6Hhmmss, bytes) ← Alpha.decode 6 bytes
  let (flag, bytes) ← Flag.decode bytes
  pure ({ unitFlag, indexValue, sign, timeC6Hhmmss, flag }, bytes)

@[simp] theorem encode_length (message : Highest) : (encode message).length = 23 := by
  unfold encode
  simp only [List.length_append, UnitFlag.encode_length, Alpha.encode_length, Sign.encode_length, Flag.encode_length]

theorem encode_length_pos (message : Highest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Highest) (rest : List UInt8) :
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
  rw [Flag.decode_encode, some_bind]
  rfl

end Highest

/-- Lowest: 23 bytes -/
structure Lowest where
  unitFlag : UnitFlag
  indexValue : Alpha 14
  sign : Sign
  timeC6Hhmmss : Alpha 6
  flag : Flag
  deriving DecidableEq, Repr

namespace Lowest

def encode (message : Lowest) : List UInt8 :=
  UnitFlag.encode message.unitFlag
    ++ (Alpha.encode message.indexValue
    ++ (Sign.encode message.sign
    ++ (Alpha.encode message.timeC6Hhmmss
    ++ (Flag.encode message.flag))))

def decode (bytes : List UInt8) : Option (Lowest × List UInt8) := do
  let (unitFlag, bytes) ← UnitFlag.decode bytes
  let (indexValue, bytes) ← Alpha.decode 14 bytes
  let (sign, bytes) ← Sign.decode bytes
  let (timeC6Hhmmss, bytes) ← Alpha.decode 6 bytes
  let (flag, bytes) ← Flag.decode bytes
  pure ({ unitFlag, indexValue, sign, timeC6Hhmmss, flag }, bytes)

@[simp] theorem encode_length (message : Lowest) : (encode message).length = 23 := by
  unfold encode
  simp only [List.length_append, UnitFlag.encode_length, Alpha.encode_length, Sign.encode_length, Flag.encode_length]

theorem encode_length_pos (message : Lowest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Lowest) (rest : List UInt8) :
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
  rw [Flag.decode_encode, some_bind]
  rfl

end Lowest

/-- Current Price: 23 bytes -/
structure CurrentPrice where
  unitFlag : UnitFlag
  indexValue : Alpha 14
  sign : Sign
  timeC6Hhmmss : Alpha 6
  flag : Flag
  deriving DecidableEq, Repr

namespace CurrentPrice

def encode (message : CurrentPrice) : List UInt8 :=
  UnitFlag.encode message.unitFlag
    ++ (Alpha.encode message.indexValue
    ++ (Sign.encode message.sign
    ++ (Alpha.encode message.timeC6Hhmmss
    ++ (Flag.encode message.flag))))

def decode (bytes : List UInt8) : Option (CurrentPrice × List UInt8) := do
  let (unitFlag, bytes) ← UnitFlag.decode bytes
  let (indexValue, bytes) ← Alpha.decode 14 bytes
  let (sign, bytes) ← Sign.decode bytes
  let (timeC6Hhmmss, bytes) ← Alpha.decode 6 bytes
  let (flag, bytes) ← Flag.decode bytes
  pure ({ unitFlag, indexValue, sign, timeC6Hhmmss, flag }, bytes)

@[simp] theorem encode_length (message : CurrentPrice) : (encode message).length = 23 := by
  unfold encode
  simp only [List.length_append, UnitFlag.encode_length, Alpha.encode_length, Sign.encode_length, Flag.encode_length]

theorem encode_length_pos (message : CurrentPrice) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CurrentPrice) (rest : List UInt8) :
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
  rw [Flag.decode_encode, some_bind]
  rfl

end CurrentPrice

/-- Index Day On Day Comparison: 25 bytes -/
structure IndexDayOnDayComparison where
  netChangeRate : Alpha 8
  sign : Sign
  unitFlag : UnitFlag
  netChange : Alpha 14
  secondSign : SecondSign
  deriving DecidableEq, Repr

namespace IndexDayOnDayComparison

def encode (message : IndexDayOnDayComparison) : List UInt8 :=
  Alpha.encode message.netChangeRate
    ++ (Sign.encode message.sign
    ++ (UnitFlag.encode message.unitFlag
    ++ (Alpha.encode message.netChange
    ++ (SecondSign.encode message.secondSign))))

def decode (bytes : List UInt8) : Option (IndexDayOnDayComparison × List UInt8) := do
  let (netChangeRate, bytes) ← Alpha.decode 8 bytes
  let (sign, bytes) ← Sign.decode bytes
  let (unitFlag, bytes) ← UnitFlag.decode bytes
  let (netChange, bytes) ← Alpha.decode 14 bytes
  let (secondSign, bytes) ← SecondSign.decode bytes
  pure ({ netChangeRate, sign, unitFlag, netChange, secondSign }, bytes)

@[simp] theorem encode_length (message : IndexDayOnDayComparison) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, Sign.encode_length, UnitFlag.encode_length, SecondSign.encode_length]

theorem encode_length_pos (message : IndexDayOnDayComparison) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IndexDayOnDayComparison) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Sign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, UnitFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [SecondSign.decode_encode, some_bind]
  rfl

end IndexDayOnDayComparison

/-- Index Open High Low And Closing Prices Message: 123 bytes -/
structure IndexOpenHighLowAndClosingPricesMessage where
  reserved2 : Alpha 2
  indexType : Alpha 4
  open_ : Open
  highest : Highest
  lowest : Lowest
  currentPrice : CurrentPrice
  indexDayOnDayComparison : IndexDayOnDayComparison
  deriving DecidableEq, Repr

namespace IndexOpenHighLowAndClosingPricesMessage

def encode (message : IndexOpenHighLowAndClosingPricesMessage) : List UInt8 :=
  Alpha.encode message.reserved2
    ++ (Alpha.encode message.indexType
    ++ (Open.encode message.open_
    ++ (Highest.encode message.highest
    ++ (Lowest.encode message.lowest
    ++ (CurrentPrice.encode message.currentPrice
    ++ (IndexDayOnDayComparison.encode message.indexDayOnDayComparison))))))

def decode (bytes : List UInt8) : Option (IndexOpenHighLowAndClosingPricesMessage × List UInt8) := do
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (indexType, bytes) ← Alpha.decode 4 bytes
  let (open_, bytes) ← Open.decode bytes
  let (highest, bytes) ← Highest.decode bytes
  let (lowest, bytes) ← Lowest.decode bytes
  let (currentPrice, bytes) ← CurrentPrice.decode bytes
  let (indexDayOnDayComparison, bytes) ← IndexDayOnDayComparison.decode bytes
  pure ({ reserved2, indexType, open_, highest, lowest, currentPrice, indexDayOnDayComparison }, bytes)

@[simp] theorem encode_length (message : IndexOpenHighLowAndClosingPricesMessage) : (encode message).length = 123 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, Open.encode_length, Highest.encode_length, Lowest.encode_length, CurrentPrice.encode_length, IndexDayOnDayComparison.encode_length]

theorem encode_length_pos (message : IndexOpenHighLowAndClosingPricesMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IndexOpenHighLowAndClosingPricesMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Open.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Highest.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Lowest.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CurrentPrice.decode_encode, some_bind]
  dsimp only
  rw [IndexDayOnDayComparison.decode_encode, some_bind]
  rfl

end IndexOpenHighLowAndClosingPricesMessage

/-- Index: 22 bytes -/
structure Index where
  unitFlag : UnitFlag
  indexValue : Alpha 14
  sign : Sign
  timeC6Hhmmss : Alpha 6
  deriving DecidableEq, Repr

namespace Index

def encode (message : Index) : List UInt8 :=
  UnitFlag.encode message.unitFlag
    ++ (Alpha.encode message.indexValue
    ++ (Sign.encode message.sign
    ++ (Alpha.encode message.timeC6Hhmmss)))

def decode (bytes : List UInt8) : Option (Index × List UInt8) := do
  let (unitFlag, bytes) ← UnitFlag.decode bytes
  let (indexValue, bytes) ← Alpha.decode 14 bytes
  let (sign, bytes) ← Sign.decode bytes
  let (timeC6Hhmmss, bytes) ← Alpha.decode 6 bytes
  pure ({ unitFlag, indexValue, sign, timeC6Hhmmss }, bytes)

@[simp] theorem encode_length (message : Index) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, UnitFlag.encode_length, Alpha.encode_length, Sign.encode_length]

theorem encode_length_pos (message : Index) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Index) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, UnitFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Sign.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end Index

/-- Special Quotation Message: 29 bytes -/
structure SpecialQuotationMessage where
  reserved2 : Alpha 2
  sqType : Alpha 4
  index : Index
  reserved1 : Alpha 1
  deriving DecidableEq, Repr

namespace SpecialQuotationMessage

def encode (message : SpecialQuotationMessage) : List UInt8 :=
  Alpha.encode message.reserved2
    ++ (Alpha.encode message.sqType
    ++ (Index.encode message.index
    ++ (Alpha.encode message.reserved1)))

def decode (bytes : List UInt8) : Option (SpecialQuotationMessage × List UInt8) := do
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (sqType, bytes) ← Alpha.decode 4 bytes
  let (index, bytes) ← Index.decode bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  pure ({ reserved2, sqType, index, reserved1 }, bytes)

@[simp] theorem encode_length (message : SpecialQuotationMessage) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, Index.encode_length]

theorem encode_length_pos (message : SpecialQuotationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SpecialQuotationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Index.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SpecialQuotationMessage

/-- Control Message: 10 bytes -/
structure ControlMessage where
  reserved2 : Alpha 2
  testModeFlag : TestModeFlag
  startendFlag : StartendFlag
  timeC6Hhmm : Alpha 6
  deriving DecidableEq, Repr

namespace ControlMessage

def encode (message : ControlMessage) : List UInt8 :=
  Alpha.encode message.reserved2
    ++ (TestModeFlag.encode message.testModeFlag
    ++ (StartendFlag.encode message.startendFlag
    ++ (Alpha.encode message.timeC6Hhmm)))

def decode (bytes : List UInt8) : Option (ControlMessage × List UInt8) := do
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (testModeFlag, bytes) ← TestModeFlag.decode bytes
  let (startendFlag, bytes) ← StartendFlag.decode bytes
  let (timeC6Hhmm, bytes) ← Alpha.decode 6 bytes
  pure ({ reserved2, testModeFlag, startendFlag, timeC6Hhmm }, bytes)

@[simp] theorem encode_length (message : ControlMessage) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, TestModeFlag.encode_length, StartendFlag.encode_length]

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
  rw [List.append_assoc, StartendFlag.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ControlMessage

/-- Any Payload, selected by Tag ID -/
inductive Payload where
  | marketValueMessage (message : MarketValueMessage) -- "MV" 0x4D56
  | simpleYieldMessage (message : SimpleYieldMessage) -- "YS" 0x5953
  | weightedYieldMessage (message : WeightedYieldMessage) -- "YW" 0x5957
  | simpleStockPriceAverageMessage (message : SimpleStockPriceAverageMessage) -- "AP" 0x4150
  | weightedStockPriceAverageMessage (message : WeightedStockPriceAverageMessage) -- "AW" 0x4157
  | simpleStockPriceAverageByIndustryMessage (message : SimpleStockPriceAverageByIndustryMessage) -- "AT" 0x4154
  | japaneseYenCbIndicatorMessage (message : JapaneseYenCbIndicatorMessage) -- "IY" 0x4959
  | numberOfGainersDeclinersMessage (message : NumberOfGainersDeclinersMessage) -- "NC" 0x4E43
  | estimatedTotalTradingVolumeMessage (message : EstimatedTotalTradingVolumeMessage) -- "TV" 0x5456
  | estimatedTotalTurnoverMessage (message : EstimatedTotalTurnoverMessage) -- "TA" 0x5441
  | vwapByMarketMessage (message : VwapByMarketMessage) -- "VS" 0x5653
  | rankingByTradingVolumeMessage (message : RankingByTradingVolumeMessage) -- "RO" 0x524F
  | rankingByTurnoverMessage (message : RankingByTurnoverMessage) -- "RA" 0x5241
  | rankingByNetChangeMessage (message : RankingByNetChangeMessage) -- "RC" 0x5243
  | rankingByNetChangeRateMessage (message : RankingByNetChangeRateMessage) -- "RP" 0x5250
  | tostnetStatisticsMessage (message : TostnetStatisticsMessage) -- "TS" 0x5453
  | indexOpenHighLowAndClosingPricesMessage (message : IndexOpenHighLowAndClosingPricesMessage) -- "4I" 0x3449
  | specialQuotationMessage (message : SpecialQuotationMessage) -- "SQ" 0x5351
  | controlMessage (message : ControlMessage) -- "LC" 0x4C43
  deriving DecidableEq, Repr

namespace Payload

/-- The Tag ID each message is sent under -/
def tag : Payload → BitVec 16
  | .marketValueMessage _ => 19798
  | .simpleYieldMessage _ => 22867
  | .weightedYieldMessage _ => 22871
  | .simpleStockPriceAverageMessage _ => 16720
  | .weightedStockPriceAverageMessage _ => 16727
  | .simpleStockPriceAverageByIndustryMessage _ => 16724
  | .japaneseYenCbIndicatorMessage _ => 18777
  | .numberOfGainersDeclinersMessage _ => 20035
  | .estimatedTotalTradingVolumeMessage _ => 21590
  | .estimatedTotalTurnoverMessage _ => 21569
  | .vwapByMarketMessage _ => 22099
  | .rankingByTradingVolumeMessage _ => 21071
  | .rankingByTurnoverMessage _ => 21057
  | .rankingByNetChangeMessage _ => 21059
  | .rankingByNetChangeRateMessage _ => 21072
  | .tostnetStatisticsMessage _ => 21587
  | .indexOpenHighLowAndClosingPricesMessage _ => 13385
  | .specialQuotationMessage _ => 21329
  | .controlMessage _ => 19523

def encode : Payload → List UInt8
  | .marketValueMessage message => MarketValueMessage.encode message
  | .simpleYieldMessage message => SimpleYieldMessage.encode message
  | .weightedYieldMessage message => WeightedYieldMessage.encode message
  | .simpleStockPriceAverageMessage message => SimpleStockPriceAverageMessage.encode message
  | .weightedStockPriceAverageMessage message => WeightedStockPriceAverageMessage.encode message
  | .simpleStockPriceAverageByIndustryMessage message => SimpleStockPriceAverageByIndustryMessage.encode message
  | .japaneseYenCbIndicatorMessage message => JapaneseYenCbIndicatorMessage.encode message
  | .numberOfGainersDeclinersMessage message => NumberOfGainersDeclinersMessage.encode message
  | .estimatedTotalTradingVolumeMessage message => EstimatedTotalTradingVolumeMessage.encode message
  | .estimatedTotalTurnoverMessage message => EstimatedTotalTurnoverMessage.encode message
  | .vwapByMarketMessage message => VwapByMarketMessage.encode message
  | .rankingByTradingVolumeMessage message => RankingByTradingVolumeMessage.encode message
  | .rankingByTurnoverMessage message => RankingByTurnoverMessage.encode message
  | .rankingByNetChangeMessage message => RankingByNetChangeMessage.encode message
  | .rankingByNetChangeRateMessage message => RankingByNetChangeRateMessage.encode message
  | .tostnetStatisticsMessage message => TostnetStatisticsMessage.encode message
  | .indexOpenHighLowAndClosingPricesMessage message => IndexOpenHighLowAndClosingPricesMessage.encode message
  | .specialQuotationMessage message => SpecialQuotationMessage.encode message
  | .controlMessage message => ControlMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 1453 := by
  cases message with
  | marketValueMessage inner =>
    simp only [encode, MarketValueMessage.encode_length]
    omega
  | simpleYieldMessage inner =>
    simp only [encode, SimpleYieldMessage.encode_length]
    omega
  | weightedYieldMessage inner =>
    simp only [encode, WeightedYieldMessage.encode_length]
    omega
  | simpleStockPriceAverageMessage inner =>
    simp only [encode, SimpleStockPriceAverageMessage.encode_length]
    omega
  | weightedStockPriceAverageMessage inner =>
    simp only [encode, WeightedStockPriceAverageMessage.encode_length]
    omega
  | simpleStockPriceAverageByIndustryMessage inner =>
    simp only [encode, SimpleStockPriceAverageByIndustryMessage.encode_length]
    omega
  | japaneseYenCbIndicatorMessage inner =>
    simp only [encode, JapaneseYenCbIndicatorMessage.encode_length]
    omega
  | numberOfGainersDeclinersMessage inner =>
    simp only [encode, NumberOfGainersDeclinersMessage.encode_length]
    omega
  | estimatedTotalTradingVolumeMessage inner =>
    simp only [encode, EstimatedTotalTradingVolumeMessage.encode_length]
    omega
  | estimatedTotalTurnoverMessage inner =>
    simp only [encode, EstimatedTotalTurnoverMessage.encode_length]
    omega
  | vwapByMarketMessage inner =>
    simp only [encode, VwapByMarketMessage.encode_length]
    omega
  | rankingByTradingVolumeMessage inner =>
    simp only [encode, RankingByTradingVolumeMessage.encode_length]
    omega
  | rankingByTurnoverMessage inner =>
    simp only [encode, RankingByTurnoverMessage.encode_length]
    omega
  | rankingByNetChangeMessage inner =>
    simp only [encode, RankingByNetChangeMessage.encode_length]
    omega
  | rankingByNetChangeRateMessage inner =>
    simp only [encode, RankingByNetChangeRateMessage.encode_length]
    omega
  | tostnetStatisticsMessage inner =>
    simp only [encode, TostnetStatisticsMessage.encode_length]
    omega
  | indexOpenHighLowAndClosingPricesMessage inner =>
    simp only [encode, IndexOpenHighLowAndClosingPricesMessage.encode_length]
    omega
  | specialQuotationMessage inner =>
    simp only [encode, SpecialQuotationMessage.encode_length]
    omega
  | controlMessage inner =>
    simp only [encode, ControlMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 19798 then (MarketValueMessage.decode bytes).map fun (message, rest) => (.marketValueMessage message, rest)
  else if tag = 22867 then (SimpleYieldMessage.decode bytes).map fun (message, rest) => (.simpleYieldMessage message, rest)
  else if tag = 22871 then (WeightedYieldMessage.decode bytes).map fun (message, rest) => (.weightedYieldMessage message, rest)
  else if tag = 16720 then (SimpleStockPriceAverageMessage.decode bytes).map fun (message, rest) => (.simpleStockPriceAverageMessage message, rest)
  else if tag = 16727 then (WeightedStockPriceAverageMessage.decode bytes).map fun (message, rest) => (.weightedStockPriceAverageMessage message, rest)
  else if tag = 16724 then (SimpleStockPriceAverageByIndustryMessage.decode bytes).map fun (message, rest) => (.simpleStockPriceAverageByIndustryMessage message, rest)
  else if tag = 18777 then (JapaneseYenCbIndicatorMessage.decode bytes).map fun (message, rest) => (.japaneseYenCbIndicatorMessage message, rest)
  else if tag = 20035 then (NumberOfGainersDeclinersMessage.decode bytes).map fun (message, rest) => (.numberOfGainersDeclinersMessage message, rest)
  else if tag = 21590 then (EstimatedTotalTradingVolumeMessage.decode bytes).map fun (message, rest) => (.estimatedTotalTradingVolumeMessage message, rest)
  else if tag = 21569 then (EstimatedTotalTurnoverMessage.decode bytes).map fun (message, rest) => (.estimatedTotalTurnoverMessage message, rest)
  else if tag = 22099 then (VwapByMarketMessage.decode bytes).map fun (message, rest) => (.vwapByMarketMessage message, rest)
  else if tag = 21071 then (RankingByTradingVolumeMessage.decode bytes).map fun (message, rest) => (.rankingByTradingVolumeMessage message, rest)
  else if tag = 21057 then (RankingByTurnoverMessage.decode bytes).map fun (message, rest) => (.rankingByTurnoverMessage message, rest)
  else if tag = 21059 then (RankingByNetChangeMessage.decode bytes).map fun (message, rest) => (.rankingByNetChangeMessage message, rest)
  else if tag = 21072 then (RankingByNetChangeRateMessage.decode bytes).map fun (message, rest) => (.rankingByNetChangeRateMessage message, rest)
  else if tag = 21587 then (TostnetStatisticsMessage.decode bytes).map fun (message, rest) => (.tostnetStatisticsMessage message, rest)
  else if tag = 13385 then (IndexOpenHighLowAndClosingPricesMessage.decode bytes).map fun (message, rest) => (.indexOpenHighLowAndClosingPricesMessage message, rest)
  else if tag = 21329 then (SpecialQuotationMessage.decode bytes).map fun (message, rest) => (.specialQuotationMessage message, rest)
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
theorem encode_length_le (message : TagInformation) : (encode message).length ≤ 1456 := by
  unfold encode
  cases message.payload with
  | marketValueMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MarketValueMessage.encode_length]
    omega
  | simpleYieldMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, SimpleYieldMessage.encode_length]
    omega
  | weightedYieldMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, WeightedYieldMessage.encode_length]
    omega
  | simpleStockPriceAverageMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, SimpleStockPriceAverageMessage.encode_length]
    omega
  | weightedStockPriceAverageMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, WeightedStockPriceAverageMessage.encode_length]
    omega
  | simpleStockPriceAverageByIndustryMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, SimpleStockPriceAverageByIndustryMessage.encode_length]
    omega
  | japaneseYenCbIndicatorMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, JapaneseYenCbIndicatorMessage.encode_length]
    omega
  | numberOfGainersDeclinersMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, NumberOfGainersDeclinersMessage.encode_length]
    omega
  | estimatedTotalTradingVolumeMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, EstimatedTotalTradingVolumeMessage.encode_length]
    omega
  | estimatedTotalTurnoverMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, EstimatedTotalTurnoverMessage.encode_length]
    omega
  | vwapByMarketMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, VwapByMarketMessage.encode_length]
    omega
  | rankingByTradingVolumeMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, RankingByTradingVolumeMessage.encode_length]
    omega
  | rankingByTurnoverMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, RankingByTurnoverMessage.encode_length]
    omega
  | rankingByNetChangeMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, RankingByNetChangeMessage.encode_length]
    omega
  | rankingByNetChangeRateMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, RankingByNetChangeRateMessage.encode_length]
    omega
  | tostnetStatisticsMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, TostnetStatisticsMessage.encode_length]
    omega
  | indexOpenHighLowAndClosingPricesMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, IndexOpenHighLowAndClosingPricesMessage.encode_length]
    omega
  | specialQuotationMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, SpecialQuotationMessage.encode_length]
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

end Omi.JpxTseequitiesIndexstatisticsFlexV195
