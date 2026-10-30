import Wire

/-!
# Japan Exchange Group ToSTNeT v19.5

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.JpxTseequitiesTostnetFlexV195

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

/-- Market Identification Flag: one byte code -/
def MarketIdentificationFlag.codes : List UInt8 :=
  [0x31, 0x32, 0x33]

inductive MarketIdentificationFlag where
  | singleIssueTransaction -- Single Issue Transaction
  | basketTransaction -- Basket Transaction
  | closingPriceTransaction -- Closing Price Transaction
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketIdentificationFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketIdentificationFlag

def toByte : MarketIdentificationFlag → UInt8
  | .singleIssueTransaction => 0x31
  | .basketTransaction => 0x32
  | .closingPriceTransaction => 0x33
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketIdentificationFlag :=
  if byte = 0x31 then .singleIssueTransaction
  else if byte = 0x32 then .basketTransaction
  else .closingPriceTransaction

def ofByte (byte : UInt8) : MarketIdentificationFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketIdentificationFlag) : ofByte value.toByte = value := by
  cases value with
  | singleIssueTransaction => decide
  | basketTransaction => decide
  | closingPriceTransaction => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarketIdentificationFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketIdentificationFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketIdentificationFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : MarketIdentificationFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : MarketIdentificationFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarketIdentificationFlag

/-- Transaction Identification Flag: one byte code -/
def TransactionIdentificationFlag.codes : List UInt8 :=
  [0x31, 0x32, 0x33, 0x20, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x4F, 0x50]

inductive TransactionIdentificationFlag where
  | dayTransaction -- Day Transaction
  | ordinaryTransactionT2VwapTransaction -- Ordinary Transaction T 2 Vwap Transaction
  | dayTransactionVwapTransaction -- Day Transaction Vwap Transaction
  | ordinaryTransactionT2 -- Ordinary Transaction T 2
  | ordinaryTransactionT1 -- Ordinary Transaction T 1
  | ordinaryTransactionT1VwapTransaction -- Ordinary Transaction T 1 Vwap Transaction
  | ordinaryTransactionT3 -- Ordinary Transaction T 3
  | ordinaryTransactionT3VwapTransaction -- Ordinary Transaction T 3 Vwap Transaction
  | ordinaryTransactionT4 -- Ordinary Transaction T 4
  | ordinaryTransactionT4VwapTransaction -- Ordinary Transaction T 4 Vwap Transaction
  | ordinaryTransactionT5 -- Ordinary Transaction T 5
  | ordinaryTransactionT5VwapTransaction -- Ordinary Transaction T 5 Vwap Transaction
  | ordinaryTransactionT6 -- Ordinary Transaction T 6
  | ordinaryTransactionT6VwapTransaction -- Ordinary Transaction T 6 Vwap Transaction
  | ordinaryTransactionT7 -- Ordinary Transaction T 7
  | ordinaryTransactionT7VwapTransaction -- Ordinary Transaction T 7 Vwap Transaction
  | ordinaryTransactionT8 -- Ordinary Transaction T 8
  | ordinaryTransactionT8VwapTransaction -- Ordinary Transaction T 8 Vwap Transaction
  | ordinaryTransactionT9 -- Ordinary Transaction T 9
  | ordinaryTransactionT9VwapTransaction -- Ordinary Transaction T 9 Vwap Transaction
  | unlisted (byte : { byte : UInt8 // byte ∉ TransactionIdentificationFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TransactionIdentificationFlag

def toByte : TransactionIdentificationFlag → UInt8
  | .dayTransaction => 0x31
  | .ordinaryTransactionT2VwapTransaction => 0x32
  | .dayTransactionVwapTransaction => 0x33
  | .ordinaryTransactionT2 => 0x20
  | .ordinaryTransactionT1 => 0x41
  | .ordinaryTransactionT1VwapTransaction => 0x42
  | .ordinaryTransactionT3 => 0x43
  | .ordinaryTransactionT3VwapTransaction => 0x44
  | .ordinaryTransactionT4 => 0x45
  | .ordinaryTransactionT4VwapTransaction => 0x46
  | .ordinaryTransactionT5 => 0x47
  | .ordinaryTransactionT5VwapTransaction => 0x48
  | .ordinaryTransactionT6 => 0x49
  | .ordinaryTransactionT6VwapTransaction => 0x4A
  | .ordinaryTransactionT7 => 0x4B
  | .ordinaryTransactionT7VwapTransaction => 0x4C
  | .ordinaryTransactionT8 => 0x4D
  | .ordinaryTransactionT8VwapTransaction => 0x4E
  | .ordinaryTransactionT9 => 0x4F
  | .ordinaryTransactionT9VwapTransaction => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TransactionIdentificationFlag :=
  if byte = 0x31 then .dayTransaction
  else if byte = 0x32 then .ordinaryTransactionT2VwapTransaction
  else if byte = 0x33 then .dayTransactionVwapTransaction
  else if byte = 0x20 then .ordinaryTransactionT2
  else if byte = 0x41 then .ordinaryTransactionT1
  else if byte = 0x42 then .ordinaryTransactionT1VwapTransaction
  else if byte = 0x43 then .ordinaryTransactionT3
  else if byte = 0x44 then .ordinaryTransactionT3VwapTransaction
  else if byte = 0x45 then .ordinaryTransactionT4
  else if byte = 0x46 then .ordinaryTransactionT4VwapTransaction
  else if byte = 0x47 then .ordinaryTransactionT5
  else if byte = 0x48 then .ordinaryTransactionT5VwapTransaction
  else if byte = 0x49 then .ordinaryTransactionT6
  else if byte = 0x4A then .ordinaryTransactionT6VwapTransaction
  else if byte = 0x4B then .ordinaryTransactionT7
  else if byte = 0x4C then .ordinaryTransactionT7VwapTransaction
  else if byte = 0x4D then .ordinaryTransactionT8
  else if byte = 0x4E then .ordinaryTransactionT8VwapTransaction
  else if byte = 0x4F then .ordinaryTransactionT9
  else .ordinaryTransactionT9VwapTransaction

def ofByte (byte : UInt8) : TransactionIdentificationFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TransactionIdentificationFlag) : ofByte value.toByte = value := by
  cases value with
  | dayTransaction => decide
  | ordinaryTransactionT2VwapTransaction => decide
  | dayTransactionVwapTransaction => decide
  | ordinaryTransactionT2 => decide
  | ordinaryTransactionT1 => decide
  | ordinaryTransactionT1VwapTransaction => decide
  | ordinaryTransactionT3 => decide
  | ordinaryTransactionT3VwapTransaction => decide
  | ordinaryTransactionT4 => decide
  | ordinaryTransactionT4VwapTransaction => decide
  | ordinaryTransactionT5 => decide
  | ordinaryTransactionT5VwapTransaction => decide
  | ordinaryTransactionT6 => decide
  | ordinaryTransactionT6VwapTransaction => decide
  | ordinaryTransactionT7 => decide
  | ordinaryTransactionT7VwapTransaction => decide
  | ordinaryTransactionT8 => decide
  | ordinaryTransactionT8VwapTransaction => decide
  | ordinaryTransactionT9 => decide
  | ordinaryTransactionT9VwapTransaction => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TransactionIdentificationFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TransactionIdentificationFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TransactionIdentificationFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TransactionIdentificationFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TransactionIdentificationFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TransactionIdentificationFlag

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

/-- Trading Halt: 8 bytes -/
structure TradingHalt where
  stateFlag : Alpha 2
  timeC6 : Alpha 6
  deriving DecidableEq, Repr

namespace TradingHalt

def encode (message : TradingHalt) : List UInt8 :=
  Alpha.encode message.stateFlag
    ++ (Alpha.encode message.timeC6)

def decode (bytes : List UInt8) : Option (TradingHalt × List UInt8) := do
  let (stateFlag, bytes) ← Alpha.decode 2 bytes
  let (timeC6, bytes) ← Alpha.decode 6 bytes
  pure ({ stateFlag, timeC6 }, bytes)

@[simp] theorem encode_length (message : TradingHalt) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : TradingHalt) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradingHalt) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradingHalt

/-- Price: 30 bytes -/
structure Price where
  priceCode : Alpha 2
  lotSizeUnitFlag : LotSizeUnitFlag
  priceC14 : Alpha 14
  sign : Sign
  timeC12 : Alpha 12
  deriving DecidableEq, Repr

namespace Price

def encode (message : Price) : List UInt8 :=
  Alpha.encode message.priceCode
    ++ (LotSizeUnitFlag.encode message.lotSizeUnitFlag
    ++ (Alpha.encode message.priceC14
    ++ (Sign.encode message.sign
    ++ (Alpha.encode message.timeC12))))

def decode (bytes : List UInt8) : Option (Price × List UInt8) := do
  let (priceCode, bytes) ← Alpha.decode 2 bytes
  let (lotSizeUnitFlag, bytes) ← LotSizeUnitFlag.decode bytes
  let (priceC14, bytes) ← Alpha.decode 14 bytes
  let (sign, bytes) ← Sign.decode bytes
  let (timeC12, bytes) ← Alpha.decode 12 bytes
  pure ({ priceCode, lotSizeUnitFlag, priceC14, sign, timeC12 }, bytes)

@[simp] theorem encode_length (message : Price) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, LotSizeUnitFlag.encode_length, Sign.encode_length]

theorem encode_length_pos (message : Price) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Price) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end Price

/-- Trading Volume: 15 bytes -/
structure TradingVolume where
  tradingVolumeTurnoverUnitFlag : TradingVolumeTurnoverUnitFlag
  tradingVolumeC14 : Alpha 14
  deriving DecidableEq, Repr

namespace TradingVolume

def encode (message : TradingVolume) : List UInt8 :=
  TradingVolumeTurnoverUnitFlag.encode message.tradingVolumeTurnoverUnitFlag
    ++ (Alpha.encode message.tradingVolumeC14)

def decode (bytes : List UInt8) : Option (TradingVolume × List UInt8) := do
  let (tradingVolumeTurnoverUnitFlag, bytes) ← TradingVolumeTurnoverUnitFlag.decode bytes
  let (tradingVolumeC14, bytes) ← Alpha.decode 14 bytes
  pure ({ tradingVolumeTurnoverUnitFlag, tradingVolumeC14 }, bytes)

@[simp] theorem encode_length (message : TradingVolume) : (encode message).length = 15 := by
  unfold encode
  simp only [List.length_append, TradingVolumeTurnoverUnitFlag.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : TradingVolume) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradingVolume) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, TradingVolumeTurnoverUnitFlag.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradingVolume

/-- Turnover: 15 bytes -/
structure Turnover where
  tradingVolumeTurnoverUnitFlag : TradingVolumeTurnoverUnitFlag
  turnoverC14 : Alpha 14
  deriving DecidableEq, Repr

namespace Turnover

def encode (message : Turnover) : List UInt8 :=
  TradingVolumeTurnoverUnitFlag.encode message.tradingVolumeTurnoverUnitFlag
    ++ (Alpha.encode message.turnoverC14)

def decode (bytes : List UInt8) : Option (Turnover × List UInt8) := do
  let (tradingVolumeTurnoverUnitFlag, bytes) ← TradingVolumeTurnoverUnitFlag.decode bytes
  let (turnoverC14, bytes) ← Alpha.decode 14 bytes
  pure ({ tradingVolumeTurnoverUnitFlag, turnoverC14 }, bytes)

@[simp] theorem encode_length (message : Turnover) : (encode message).length = 15 := by
  unfold encode
  simp only [List.length_append, TradingVolumeTurnoverUnitFlag.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : Turnover) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Turnover) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, TradingVolumeTurnoverUnitFlag.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end Turnover

/-- ToSTNeT By-Issue Information Message: 72 bytes -/
structure TostnetByissueInformationMessage where
  reserved2 : Alpha 2
  marketIdentificationFlag : MarketIdentificationFlag
  tradingHalt : TradingHalt
  transactionIdentificationFlag : TransactionIdentificationFlag
  price : Price
  tradingVolume : TradingVolume
  turnover : Turnover
  deriving DecidableEq, Repr

namespace TostnetByissueInformationMessage

def encode (message : TostnetByissueInformationMessage) : List UInt8 :=
  Alpha.encode message.reserved2
    ++ (MarketIdentificationFlag.encode message.marketIdentificationFlag
    ++ (TradingHalt.encode message.tradingHalt
    ++ (TransactionIdentificationFlag.encode message.transactionIdentificationFlag
    ++ (Price.encode message.price
    ++ (TradingVolume.encode message.tradingVolume
    ++ (Turnover.encode message.turnover))))))

def decode (bytes : List UInt8) : Option (TostnetByissueInformationMessage × List UInt8) := do
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (marketIdentificationFlag, bytes) ← MarketIdentificationFlag.decode bytes
  let (tradingHalt, bytes) ← TradingHalt.decode bytes
  let (transactionIdentificationFlag, bytes) ← TransactionIdentificationFlag.decode bytes
  let (price, bytes) ← Price.decode bytes
  let (tradingVolume, bytes) ← TradingVolume.decode bytes
  let (turnover, bytes) ← Turnover.decode bytes
  pure ({ reserved2, marketIdentificationFlag, tradingHalt, transactionIdentificationFlag, price, tradingVolume, turnover }, bytes)

@[simp] theorem encode_length (message : TostnetByissueInformationMessage) : (encode message).length = 72 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, MarketIdentificationFlag.encode_length, TradingHalt.encode_length, TransactionIdentificationFlag.encode_length, Price.encode_length, TradingVolume.encode_length, Turnover.encode_length]

theorem encode_length_pos (message : TostnetByissueInformationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TostnetByissueInformationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketIdentificationFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradingHalt.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TransactionIdentificationFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Price.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradingVolume.decode_encode, some_bind]
  dsimp only
  rw [Turnover.decode_encode, some_bind]
  rfl

end TostnetByissueInformationMessage

/-- State: 8 bytes -/
structure State where
  marketStateFlag : Alpha 2
  timeC6 : Alpha 6
  deriving DecidableEq, Repr

namespace State

def encode (message : State) : List UInt8 :=
  Alpha.encode message.marketStateFlag
    ++ (Alpha.encode message.timeC6)

def decode (bytes : List UInt8) : Option (State × List UInt8) := do
  let (marketStateFlag, bytes) ← Alpha.decode 2 bytes
  let (timeC6, bytes) ← Alpha.decode 6 bytes
  pure ({ marketStateFlag, timeC6 }, bytes)

@[simp] theorem encode_length (message : State) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : State) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : State) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end State

/-- ToSTNeT Market Information Message: 11 bytes -/
structure TostnetMarketInformationMessage where
  reserved2 : Alpha 2
  marketIdentificationFlag : MarketIdentificationFlag
  state : State
  deriving DecidableEq, Repr

namespace TostnetMarketInformationMessage

def encode (message : TostnetMarketInformationMessage) : List UInt8 :=
  Alpha.encode message.reserved2
    ++ (MarketIdentificationFlag.encode message.marketIdentificationFlag
    ++ (State.encode message.state))

def decode (bytes : List UInt8) : Option (TostnetMarketInformationMessage × List UInt8) := do
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (marketIdentificationFlag, bytes) ← MarketIdentificationFlag.decode bytes
  let (state, bytes) ← State.decode bytes
  pure ({ reserved2, marketIdentificationFlag, state }, bytes)

@[simp] theorem encode_length (message : TostnetMarketInformationMessage) : (encode message).length = 11 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, MarketIdentificationFlag.encode_length, State.encode_length]

theorem encode_length_pos (message : TostnetMarketInformationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TostnetMarketInformationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketIdentificationFlag.decode_encode, some_bind]
  dsimp only
  rw [State.decode_encode, some_bind]
  rfl

end TostnetMarketInformationMessage

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
  | tostnetByissueInformationMessage (message : TostnetByissueInformationMessage) -- "TI" 0x5449
  | tostnetMarketInformationMessage (message : TostnetMarketInformationMessage) -- "TM" 0x544D
  | controlMessage (message : ControlMessage) -- "LC" 0x4C43
  deriving DecidableEq, Repr

namespace Payload

/-- The Tag ID each message is sent under -/
def tag : Payload → BitVec 16
  | .tostnetByissueInformationMessage _ => 21577
  | .tostnetMarketInformationMessage _ => 21581
  | .controlMessage _ => 19523

def encode : Payload → List UInt8
  | .tostnetByissueInformationMessage message => TostnetByissueInformationMessage.encode message
  | .tostnetMarketInformationMessage message => TostnetMarketInformationMessage.encode message
  | .controlMessage message => ControlMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 72 := by
  cases message with
  | tostnetByissueInformationMessage inner =>
    simp only [encode, TostnetByissueInformationMessage.encode_length]
    omega
  | tostnetMarketInformationMessage inner =>
    simp only [encode, TostnetMarketInformationMessage.encode_length]
    omega
  | controlMessage inner =>
    simp only [encode, ControlMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 21577 then (TostnetByissueInformationMessage.decode bytes).map fun (message, rest) => (.tostnetByissueInformationMessage message, rest)
  else if tag = 21581 then (TostnetMarketInformationMessage.decode bytes).map fun (message, rest) => (.tostnetMarketInformationMessage message, rest)
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
theorem encode_length_le (message : TagInformation) : (encode message).length ≤ 75 := by
  unfold encode
  cases message.payload with
  | tostnetByissueInformationMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, TostnetByissueInformationMessage.encode_length]
    omega
  | tostnetMarketInformationMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, TostnetMarketInformationMessage.encode_length]
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

end Omi.JpxTseequitiesTostnetFlexV195
