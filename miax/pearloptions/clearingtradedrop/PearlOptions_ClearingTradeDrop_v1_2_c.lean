import Wire

/-!
# Miami International Holdings Clearing Trade Drop v1.2.c

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.

Note: Sequenced Data Packet is not framed: its length Sesm Packet Length is not an integer it reads

Note: Unsequenced Data Packet is not framed: its length Sesm Packet Length is not an integer it
reads

Note: a Sesm Tcp Packet that ends the session is the last of sesmTcpPacket: the decoder turns away
one that is followed, and the record carries the proof it is not

License: MIT No Attribution
-/

namespace Omi.MiaxPearloptionsClearingtradedropCtdV12C

/-- System Status: one byte code -/
def SystemStatus.codes : List UInt8 :=
  [0x43, 0x31, 0x32]

inductive SystemStatus where
  | endOfApplicationMessages -- End Of Application Messages
  | startOfTestSession -- Start Of Test Session
  | endOfTestSession -- End Of Test Session
  | unlisted (byte : { byte : UInt8 // byte ∉ SystemStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SystemStatus

def toByte : SystemStatus → UInt8
  | .endOfApplicationMessages => 0x43
  | .startOfTestSession => 0x31
  | .endOfTestSession => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SystemStatus :=
  if byte = 0x43 then .endOfApplicationMessages
  else if byte = 0x31 then .startOfTestSession
  else .endOfTestSession

def ofByte (byte : UInt8) : SystemStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SystemStatus) : ofByte value.toByte = value := by
  cases value with
  | endOfApplicationMessages => decide
  | startOfTestSession => decide
  | endOfTestSession => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SystemStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SystemStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SystemStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SystemStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SystemStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SystemStatus

/-- Trade Action: one byte code -/
def TradeAction.codes : List UInt8 :=
  [0x4E, 0x43, 0x58]

inductive TradeAction where
  | newTrade -- New Trade
  | tradeCorrection -- Trade Correction
  | tradeCancel -- Trade Cancel
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeAction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeAction

def toByte : TradeAction → UInt8
  | .newTrade => 0x4E
  | .tradeCorrection => 0x43
  | .tradeCancel => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeAction :=
  if byte = 0x4E then .newTrade
  else if byte = 0x43 then .tradeCorrection
  else .tradeCancel

def ofByte (byte : UInt8) : TradeAction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeAction) : ofByte value.toByte = value := by
  cases value with
  | newTrade => decide
  | tradeCorrection => decide
  | tradeCancel => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeAction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeAction × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeAction) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TradeAction) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TradeAction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeAction

/-- Trade Type: one byte code -/
def TradeType.codes : List UInt8 :=
  [0x41, 0x4D]

inductive TradeType where
  | automatic -- Automatic
  | manual -- Manual
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeType

def toByte : TradeType → UInt8
  | .automatic => 0x41
  | .manual => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeType :=
  if byte = 0x41 then .automatic
  else .manual

def ofByte (byte : UInt8) : TradeType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeType) : ofByte value.toByte = value := by
  cases value with
  | automatic => decide
  | manual => decide
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

/-- Correction Type: one byte code -/
def CorrectionType.codes : List UInt8 :=
  [0x31, 0x32, 0x33, 0x34, 0x35]

inductive CorrectionType where
  | notApplicable -- Not Applicable
  | priceAndorSizeChange -- Price Andor Size Change
  | thisSideClearingChange -- This Side Clearing Change
  | contraSideClearingChange -- Contra Side Clearing Change
  | bothSideClearingChange -- Both Side Clearing Change
  | unlisted (byte : { byte : UInt8 // byte ∉ CorrectionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CorrectionType

def toByte : CorrectionType → UInt8
  | .notApplicable => 0x31
  | .priceAndorSizeChange => 0x32
  | .thisSideClearingChange => 0x33
  | .contraSideClearingChange => 0x34
  | .bothSideClearingChange => 0x35
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CorrectionType :=
  if byte = 0x31 then .notApplicable
  else if byte = 0x32 then .priceAndorSizeChange
  else if byte = 0x33 then .thisSideClearingChange
  else if byte = 0x34 then .contraSideClearingChange
  else .bothSideClearingChange

def ofByte (byte : UInt8) : CorrectionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CorrectionType) : ofByte value.toByte = value := by
  cases value with
  | notApplicable => decide
  | priceAndorSizeChange => decide
  | thisSideClearingChange => decide
  | contraSideClearingChange => decide
  | bothSideClearingChange => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CorrectionType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CorrectionType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CorrectionType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CorrectionType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CorrectionType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CorrectionType

/-- Underlying Type: one byte code -/
def UnderlyingType.codes : List UInt8 :=
  [0x46, 0x49, 0x45]

inductive UnderlyingType where
  | etf -- Etf
  | index -- Index
  | equity -- Equity
  | unlisted (byte : { byte : UInt8 // byte ∉ UnderlyingType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace UnderlyingType

def toByte : UnderlyingType → UInt8
  | .etf => 0x46
  | .index => 0x49
  | .equity => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : UnderlyingType :=
  if byte = 0x46 then .etf
  else if byte = 0x49 then .index
  else .equity

def ofByte (byte : UInt8) : UnderlyingType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : UnderlyingType) : ofByte value.toByte = value := by
  cases value with
  | etf => decide
  | index => decide
  | equity => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : UnderlyingType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (UnderlyingType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : UnderlyingType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : UnderlyingType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : UnderlyingType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end UnderlyingType

/-- Call Or Put: one byte code -/
def CallOrPut.codes : List UInt8 :=
  [0x43, 0x50]

inductive CallOrPut where
  | call -- Call
  | put -- Put
  | unlisted (byte : { byte : UInt8 // byte ∉ CallOrPut.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CallOrPut

def toByte : CallOrPut → UInt8
  | .call => 0x43
  | .put => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CallOrPut :=
  if byte = 0x43 then .call
  else .put

def ofByte (byte : UInt8) : CallOrPut :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CallOrPut) : ofByte value.toByte = value := by
  cases value with
  | call => decide
  | put => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CallOrPut) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CallOrPut × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CallOrPut) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CallOrPut) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CallOrPut) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CallOrPut

/-- Side: one byte code -/
def Side.codes : List UInt8 :=
  [0x42, 0x53]

inductive Side where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x42 then .buy
  else .sell

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
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

/-- Trade Condition: one byte code -/
def TradeCondition.codes : List UInt8 :=
  [0x20, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x4F, 0x50, 0x51, 0x52, 0x53, 0x54, 0x58, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x6A, 0x6B, 0x6C, 0x6D, 0x6E, 0x6F, 0x70, 0x71, 0x72, 0x73, 0x74]

inductive TradeCondition where
  | regular -- Regular
  | cancelOfTradePreviouslyReportedOtherThanAsTheLastOrOpening -- Cancel Of Trade Previously Reported Other Than As The Last Or Opening
  | lateAndIsOutOfSequence -- Late And Is Out Of Sequence
  | cancelOfTheLastReportedTrade -- Cancel Of The Last Reported Trade
  | lateAndIsInCorrectSequence -- Late And Is In Correct Sequence
  | cancelOfTheFirstReportedTrade -- Cancel Of The First Reported Trade
  | lateReportOfTheOpeningTradeAndIsOutOfSequence -- Late Report Of The Opening Trade And Is Out Of Sequence
  | cancelOfTheOnlyReportedTrade -- Cancel Of The Only Reported Trade
  | lateReportOfTheOpeningTradeAndIsInCorrectSequence -- Late Report Of The Opening Trade And Is In Correct Sequence
  | auto -- Auto
  | reopeningOfAnOption -- Reopening Of An Option
  | reservedK -- Reserved K
  | reservedL -- Reserved L
  | reservedM -- Reserved M
  | reservedN -- Reserved N
  | reservedO -- Reserved O
  | reservedP -- Reserved P
  | reservedQ -- Reserved Q
  | executionOfAStoppedOrder -- Execution Of A Stopped Order
  | executionOfAnIsoOrder -- Execution Of An Iso Order
  | reservedT -- Reserved T
  | tradeThroughExempt -- Trade Through Exempt
  | pairedPrime -- Paired Prime
  | reservedB -- Reserved b
  | primeCustomerToCustomerCrossOrPrimeQcc -- Prime Customer To Customer Cross Or Prime Qcc
  | reservedD -- Reserved d
  | reservedE -- Reserved e
  | complexNotStockTiedNoLegging -- Complex Not Stock Tied No Legging
  | complexPrimeNotStockTiedNoLegging -- Complex Prime Not Stock Tied No Legging
  | complexPrimeCustomerToCustomerCrossOrQccNotStockTied -- Complex Prime Customer To Customer Cross Or Qcc Not Stock Tied
  | reservedI -- Reserved i
  | complexLeggingNotStockTied -- Complex Legging Not Stock Tied
  | complexPrimeStockTiedNoLegging -- Complex Prime Stock Tied No Legging
  | complexPrimeLeggingNotStockTied -- Complex Prime Legging Not Stock Tied
  | reservedLowerCaseM -- Reserved Lower Case M
  | complexStockTiedNoLegging -- Complex Stock Tied No Legging
  | complexCustomerToCustomerCrossOrQccStockTied -- Complex Customer To Customer Cross Or Qcc Stock Tied
  | reservedLowerCaseP -- Reserved Lower Case P
  | reservedLowerCaseQ -- Reserved Lower Case Q
  | reservedR -- Reserved r
  | reservedS -- Reserved s
  | reservedLowerCaseT -- Reserved Lower Case T
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeCondition

def toByte : TradeCondition → UInt8
  | .regular => 0x20
  | .cancelOfTradePreviouslyReportedOtherThanAsTheLastOrOpening => 0x41
  | .lateAndIsOutOfSequence => 0x42
  | .cancelOfTheLastReportedTrade => 0x43
  | .lateAndIsInCorrectSequence => 0x44
  | .cancelOfTheFirstReportedTrade => 0x45
  | .lateReportOfTheOpeningTradeAndIsOutOfSequence => 0x46
  | .cancelOfTheOnlyReportedTrade => 0x47
  | .lateReportOfTheOpeningTradeAndIsInCorrectSequence => 0x48
  | .auto => 0x49
  | .reopeningOfAnOption => 0x4A
  | .reservedK => 0x4B
  | .reservedL => 0x4C
  | .reservedM => 0x4D
  | .reservedN => 0x4E
  | .reservedO => 0x4F
  | .reservedP => 0x50
  | .reservedQ => 0x51
  | .executionOfAStoppedOrder => 0x52
  | .executionOfAnIsoOrder => 0x53
  | .reservedT => 0x54
  | .tradeThroughExempt => 0x58
  | .pairedPrime => 0x61
  | .reservedB => 0x62
  | .primeCustomerToCustomerCrossOrPrimeQcc => 0x63
  | .reservedD => 0x64
  | .reservedE => 0x65
  | .complexNotStockTiedNoLegging => 0x66
  | .complexPrimeNotStockTiedNoLegging => 0x67
  | .complexPrimeCustomerToCustomerCrossOrQccNotStockTied => 0x68
  | .reservedI => 0x69
  | .complexLeggingNotStockTied => 0x6A
  | .complexPrimeStockTiedNoLegging => 0x6B
  | .complexPrimeLeggingNotStockTied => 0x6C
  | .reservedLowerCaseM => 0x6D
  | .complexStockTiedNoLegging => 0x6E
  | .complexCustomerToCustomerCrossOrQccStockTied => 0x6F
  | .reservedLowerCaseP => 0x70
  | .reservedLowerCaseQ => 0x71
  | .reservedR => 0x72
  | .reservedS => 0x73
  | .reservedLowerCaseT => 0x74
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeCondition :=
  if byte = 0x20 then .regular
  else if byte = 0x41 then .cancelOfTradePreviouslyReportedOtherThanAsTheLastOrOpening
  else if byte = 0x42 then .lateAndIsOutOfSequence
  else if byte = 0x43 then .cancelOfTheLastReportedTrade
  else if byte = 0x44 then .lateAndIsInCorrectSequence
  else if byte = 0x45 then .cancelOfTheFirstReportedTrade
  else if byte = 0x46 then .lateReportOfTheOpeningTradeAndIsOutOfSequence
  else if byte = 0x47 then .cancelOfTheOnlyReportedTrade
  else if byte = 0x48 then .lateReportOfTheOpeningTradeAndIsInCorrectSequence
  else if byte = 0x49 then .auto
  else if byte = 0x4A then .reopeningOfAnOption
  else if byte = 0x4B then .reservedK
  else if byte = 0x4C then .reservedL
  else if byte = 0x4D then .reservedM
  else if byte = 0x4E then .reservedN
  else if byte = 0x4F then .reservedO
  else if byte = 0x50 then .reservedP
  else if byte = 0x51 then .reservedQ
  else if byte = 0x52 then .executionOfAStoppedOrder
  else if byte = 0x53 then .executionOfAnIsoOrder
  else if byte = 0x54 then .reservedT
  else if byte = 0x58 then .tradeThroughExempt
  else if byte = 0x61 then .pairedPrime
  else if byte = 0x62 then .reservedB
  else if byte = 0x63 then .primeCustomerToCustomerCrossOrPrimeQcc
  else if byte = 0x64 then .reservedD
  else if byte = 0x65 then .reservedE
  else if byte = 0x66 then .complexNotStockTiedNoLegging
  else if byte = 0x67 then .complexPrimeNotStockTiedNoLegging
  else if byte = 0x68 then .complexPrimeCustomerToCustomerCrossOrQccNotStockTied
  else if byte = 0x69 then .reservedI
  else if byte = 0x6A then .complexLeggingNotStockTied
  else if byte = 0x6B then .complexPrimeStockTiedNoLegging
  else if byte = 0x6C then .complexPrimeLeggingNotStockTied
  else if byte = 0x6D then .reservedLowerCaseM
  else if byte = 0x6E then .complexStockTiedNoLegging
  else if byte = 0x6F then .complexCustomerToCustomerCrossOrQccStockTied
  else if byte = 0x70 then .reservedLowerCaseP
  else if byte = 0x71 then .reservedLowerCaseQ
  else if byte = 0x72 then .reservedR
  else if byte = 0x73 then .reservedS
  else .reservedLowerCaseT

def ofByte (byte : UInt8) : TradeCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeCondition) : ofByte value.toByte = value := by
  cases value with
  | regular => decide
  | cancelOfTradePreviouslyReportedOtherThanAsTheLastOrOpening => decide
  | lateAndIsOutOfSequence => decide
  | cancelOfTheLastReportedTrade => decide
  | lateAndIsInCorrectSequence => decide
  | cancelOfTheFirstReportedTrade => decide
  | lateReportOfTheOpeningTradeAndIsOutOfSequence => decide
  | cancelOfTheOnlyReportedTrade => decide
  | lateReportOfTheOpeningTradeAndIsInCorrectSequence => decide
  | auto => decide
  | reopeningOfAnOption => decide
  | reservedK => decide
  | reservedL => decide
  | reservedM => decide
  | reservedN => decide
  | reservedO => decide
  | reservedP => decide
  | reservedQ => decide
  | executionOfAStoppedOrder => decide
  | executionOfAnIsoOrder => decide
  | reservedT => decide
  | tradeThroughExempt => decide
  | pairedPrime => decide
  | reservedB => decide
  | primeCustomerToCustomerCrossOrPrimeQcc => decide
  | reservedD => decide
  | reservedE => decide
  | complexNotStockTiedNoLegging => decide
  | complexPrimeNotStockTiedNoLegging => decide
  | complexPrimeCustomerToCustomerCrossOrQccNotStockTied => decide
  | reservedI => decide
  | complexLeggingNotStockTied => decide
  | complexPrimeStockTiedNoLegging => decide
  | complexPrimeLeggingNotStockTied => decide
  | reservedLowerCaseM => decide
  | complexStockTiedNoLegging => decide
  | complexCustomerToCustomerCrossOrQccStockTied => decide
  | reservedLowerCaseP => decide
  | reservedLowerCaseQ => decide
  | reservedR => decide
  | reservedS => decide
  | reservedLowerCaseT => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeCondition) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TradeCondition) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TradeCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeCondition

/-- Class Fee Type: one byte code -/
def ClassFeeType.codes : List UInt8 :=
  [0x4D]

inductive ClassFeeType where
  | makerTakerFeeBased -- Maker Taker Fee Based
  | unlisted (byte : { byte : UInt8 // byte ∉ ClassFeeType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ClassFeeType

def toByte : ClassFeeType → UInt8
  | .makerTakerFeeBased => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : ClassFeeType :=
  .makerTakerFeeBased

def ofByte (byte : UInt8) : ClassFeeType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ClassFeeType) : ofByte value.toByte = value := by
  cases value with
  | makerTakerFeeBased => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ClassFeeType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ClassFeeType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ClassFeeType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ClassFeeType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ClassFeeType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ClassFeeType

/-- Pearl Bbo Posting Increment Indicator: one byte code -/
def PearlBboPostingIncrementIndicator.codes : List UInt8 :=
  [0x50, 0x4E, 0x44]

inductive PearlBboPostingIncrementIndicator where
  | penny -- Penny
  | pennyNickel -- Penny Nickel
  | nickelDime -- Nickel Dime
  | unlisted (byte : { byte : UInt8 // byte ∉ PearlBboPostingIncrementIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PearlBboPostingIncrementIndicator

def toByte : PearlBboPostingIncrementIndicator → UInt8
  | .penny => 0x50
  | .pennyNickel => 0x4E
  | .nickelDime => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PearlBboPostingIncrementIndicator :=
  if byte = 0x50 then .penny
  else if byte = 0x4E then .pennyNickel
  else .nickelDime

def ofByte (byte : UInt8) : PearlBboPostingIncrementIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PearlBboPostingIncrementIndicator) : ofByte value.toByte = value := by
  cases value with
  | penny => decide
  | pennyNickel => decide
  | nickelDime => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PearlBboPostingIncrementIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PearlBboPostingIncrementIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PearlBboPostingIncrementIndicator) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : PearlBboPostingIncrementIndicator) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : PearlBboPostingIncrementIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PearlBboPostingIncrementIndicator

/-- Execution Exchange: one byte code -/
def ExecutionExchange.codes : List UInt8 :=
  [0x41, 0x4E, 0x42, 0x43, 0x57, 0x49, 0x48, 0x4A, 0x51, 0x58, 0x54, 0x5A, 0x45, 0x4D, 0x44, 0x55, 0x20]

inductive ExecutionExchange where
  | nyseAmex -- Nyse Amex
  | nyseArca -- Nyse Arca
  | box -- Box
  | cboe -- Cboe
  | c2 -- C 2
  | ise -- Ise
  | iseGemini -- Ise Gemini
  | iseMercury -- Ise Mercury
  | nasdaqOmxOptionsMarket -- Nasdaq Omx Options Market
  | nasdaqOmxPhlxOptionsMarket -- Nasdaq Omx Phlx Options Market
  | nasdaqBx -- Nasdaq Bx
  | bats -- Bats
  | edgxOptionsMarket -- Edgx Options Market
  | miax -- Miax
  | miaxEmerald -- Miax Emerald
  | memxOptions -- Memx Options
  | tradedAtPearl -- Traded At Pearl
  | unlisted (byte : { byte : UInt8 // byte ∉ ExecutionExchange.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExecutionExchange

def toByte : ExecutionExchange → UInt8
  | .nyseAmex => 0x41
  | .nyseArca => 0x4E
  | .box => 0x42
  | .cboe => 0x43
  | .c2 => 0x57
  | .ise => 0x49
  | .iseGemini => 0x48
  | .iseMercury => 0x4A
  | .nasdaqOmxOptionsMarket => 0x51
  | .nasdaqOmxPhlxOptionsMarket => 0x58
  | .nasdaqBx => 0x54
  | .bats => 0x5A
  | .edgxOptionsMarket => 0x45
  | .miax => 0x4D
  | .miaxEmerald => 0x44
  | .memxOptions => 0x55
  | .tradedAtPearl => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExecutionExchange :=
  if byte = 0x41 then .nyseAmex
  else if byte = 0x4E then .nyseArca
  else if byte = 0x42 then .box
  else if byte = 0x43 then .cboe
  else if byte = 0x57 then .c2
  else if byte = 0x49 then .ise
  else if byte = 0x48 then .iseGemini
  else if byte = 0x4A then .iseMercury
  else if byte = 0x51 then .nasdaqOmxOptionsMarket
  else if byte = 0x58 then .nasdaqOmxPhlxOptionsMarket
  else if byte = 0x54 then .nasdaqBx
  else if byte = 0x5A then .bats
  else if byte = 0x45 then .edgxOptionsMarket
  else if byte = 0x4D then .miax
  else if byte = 0x44 then .miaxEmerald
  else if byte = 0x55 then .memxOptions
  else .tradedAtPearl

def ofByte (byte : UInt8) : ExecutionExchange :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExecutionExchange) : ofByte value.toByte = value := by
  cases value with
  | nyseAmex => decide
  | nyseArca => decide
  | box => decide
  | cboe => decide
  | c2 => decide
  | ise => decide
  | iseGemini => decide
  | iseMercury => decide
  | nasdaqOmxOptionsMarket => decide
  | nasdaqOmxPhlxOptionsMarket => decide
  | nasdaqBx => decide
  | bats => decide
  | edgxOptionsMarket => decide
  | miax => decide
  | miaxEmerald => decide
  | memxOptions => decide
  | tradedAtPearl => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ExecutionExchange) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ExecutionExchange × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ExecutionExchange) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ExecutionExchange) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ExecutionExchange) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ExecutionExchange

/-- Market State: one byte code -/
def MarketState.codes : List UInt8 :=
  [0x54, 0x4F, 0x20, 0x2A]

inductive MarketState where
  | freeTrading -- Free Trading
  | opening -- Opening
  | notApplicable -- Not Applicable
  | downgradedForOlderVersion -- Downgraded For Older Version
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketState

def toByte : MarketState → UInt8
  | .freeTrading => 0x54
  | .opening => 0x4F
  | .notApplicable => 0x20
  | .downgradedForOlderVersion => 0x2A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketState :=
  if byte = 0x54 then .freeTrading
  else if byte = 0x4F then .opening
  else if byte = 0x20 then .notApplicable
  else .downgradedForOlderVersion

def ofByte (byte : UInt8) : MarketState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketState) : ofByte value.toByte = value := by
  cases value with
  | freeTrading => decide
  | opening => decide
  | notApplicable => decide
  | downgradedForOlderVersion => decide
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

/-- Free Trading Condition: one byte code -/
def FreeTradingCondition.codes : List UInt8 :=
  [0x31, 0x32, 0x20, 0x2A]

inductive FreeTradingCondition where
  | regular -- Regular
  | abboUncrossed -- Abbo Uncrossed
  | notApplicable -- Not Applicable
  | downgradedForOlderVersion -- Downgraded For Older Version
  | unlisted (byte : { byte : UInt8 // byte ∉ FreeTradingCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace FreeTradingCondition

def toByte : FreeTradingCondition → UInt8
  | .regular => 0x31
  | .abboUncrossed => 0x32
  | .notApplicable => 0x20
  | .downgradedForOlderVersion => 0x2A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : FreeTradingCondition :=
  if byte = 0x31 then .regular
  else if byte = 0x32 then .abboUncrossed
  else if byte = 0x20 then .notApplicable
  else .downgradedForOlderVersion

def ofByte (byte : UInt8) : FreeTradingCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : FreeTradingCondition) : ofByte value.toByte = value := by
  cases value with
  | regular => decide
  | abboUncrossed => decide
  | notApplicable => decide
  | downgradedForOlderVersion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : FreeTradingCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (FreeTradingCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : FreeTradingCondition) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : FreeTradingCondition) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : FreeTradingCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end FreeTradingCondition

/-- Open Close Indicator: one byte code -/
def OpenCloseIndicator.codes : List UInt8 :=
  [0x4F, 0x43]

inductive OpenCloseIndicator where
  | openingPosition -- Opening Position
  | closingPosition -- Closing Position
  | unlisted (byte : { byte : UInt8 // byte ∉ OpenCloseIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OpenCloseIndicator

def toByte : OpenCloseIndicator → UInt8
  | .openingPosition => 0x4F
  | .closingPosition => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OpenCloseIndicator :=
  if byte = 0x4F then .openingPosition
  else .closingPosition

def ofByte (byte : UInt8) : OpenCloseIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OpenCloseIndicator) : ofByte value.toByte = value := by
  cases value with
  | openingPosition => decide
  | closingPosition => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OpenCloseIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OpenCloseIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OpenCloseIndicator) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OpenCloseIndicator) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OpenCloseIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OpenCloseIndicator

/-- Liquidity Type: one byte code -/
def LiquidityType.codes : List UInt8 :=
  [0x46, 0x42, 0x20, 0x2A]

inductive LiquidityType where
  | fixOrder -- Fix Order
  | binaryOrder -- Binary Order
  | notApplicable -- Not Applicable
  | downgradedForOlderVersion -- Downgraded For Older Version
  | unlisted (byte : { byte : UInt8 // byte ∉ LiquidityType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LiquidityType

def toByte : LiquidityType → UInt8
  | .fixOrder => 0x46
  | .binaryOrder => 0x42
  | .notApplicable => 0x20
  | .downgradedForOlderVersion => 0x2A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LiquidityType :=
  if byte = 0x46 then .fixOrder
  else if byte = 0x42 then .binaryOrder
  else if byte = 0x20 then .notApplicable
  else .downgradedForOlderVersion

def ofByte (byte : UInt8) : LiquidityType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LiquidityType) : ofByte value.toByte = value := by
  cases value with
  | fixOrder => decide
  | binaryOrder => decide
  | notApplicable => decide
  | downgradedForOlderVersion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LiquidityType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LiquidityType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LiquidityType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : LiquidityType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : LiquidityType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LiquidityType

/-- Liquidity Indicator: one byte code -/
def LiquidityIndicator.codes : List UInt8 :=
  [0x4D, 0x54, 0x20]

inductive LiquidityIndicator where
  | maker -- Maker
  | taker -- Taker
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ LiquidityIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LiquidityIndicator

def toByte : LiquidityIndicator → UInt8
  | .maker => 0x4D
  | .taker => 0x54
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LiquidityIndicator :=
  if byte = 0x4D then .maker
  else if byte = 0x54 then .taker
  else .notApplicable

def ofByte (byte : UInt8) : LiquidityIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LiquidityIndicator) : ofByte value.toByte = value := by
  cases value with
  | maker => decide
  | taker => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LiquidityIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LiquidityIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LiquidityIndicator) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : LiquidityIndicator) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : LiquidityIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LiquidityIndicator

/-- Time In Force: one byte code -/
def TimeInForce.codes : List UInt8 :=
  [0x30, 0x31, 0x33, 0x2A]

inductive TimeInForce where
  | day -- Day
  | gtc -- Gtc
  | ioc -- Ioc
  | downgradedForOlderVersion -- Downgraded For Older Version
  | unlisted (byte : { byte : UInt8 // byte ∉ TimeInForce.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TimeInForce

def toByte : TimeInForce → UInt8
  | .day => 0x30
  | .gtc => 0x31
  | .ioc => 0x33
  | .downgradedForOlderVersion => 0x2A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TimeInForce :=
  if byte = 0x30 then .day
  else if byte = 0x31 then .gtc
  else if byte = 0x33 then .ioc
  else .downgradedForOlderVersion

def ofByte (byte : UInt8) : TimeInForce :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TimeInForce) : ofByte value.toByte = value := by
  cases value with
  | day => decide
  | gtc => decide
  | ioc => decide
  | downgradedForOlderVersion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TimeInForce) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TimeInForce × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TimeInForce) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TimeInForce) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TimeInForce) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TimeInForce

/-- Member Type: one byte code -/
def MemberType.codes : List UInt8 :=
  [0x45, 0x4D, 0x52]

inductive MemberType where
  | electronicExchangeMember -- Electronic Exchange Member
  | marketMaker -- Market Maker
  | routingBroker -- Routing Broker
  | unlisted (byte : { byte : UInt8 // byte ∉ MemberType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MemberType

def toByte : MemberType → UInt8
  | .electronicExchangeMember => 0x45
  | .marketMaker => 0x4D
  | .routingBroker => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MemberType :=
  if byte = 0x45 then .electronicExchangeMember
  else if byte = 0x4D then .marketMaker
  else .routingBroker

def ofByte (byte : UInt8) : MemberType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MemberType) : ofByte value.toByte = value := by
  cases value with
  | electronicExchangeMember => decide
  | marketMaker => decide
  | routingBroker => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MemberType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MemberType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MemberType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : MemberType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : MemberType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MemberType

/-- Origin: one byte code -/
def Origin.codes : List UInt8 :=
  [0x43, 0x4E, 0x46, 0x42, 0x50, 0x41]

inductive Origin where
  | priorityCustomer -- Priority Customer
  | nonPriorityCustomer -- Non Priority Customer
  | firm -- Firm
  | brokerDealer -- Broker Dealer
  | memberMarketMaker -- Member Market Maker
  | awayExchangeMarketMaker -- Away Exchange Market Maker
  | unlisted (byte : { byte : UInt8 // byte ∉ Origin.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Origin

def toByte : Origin → UInt8
  | .priorityCustomer => 0x43
  | .nonPriorityCustomer => 0x4E
  | .firm => 0x46
  | .brokerDealer => 0x42
  | .memberMarketMaker => 0x50
  | .awayExchangeMarketMaker => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Origin :=
  if byte = 0x43 then .priorityCustomer
  else if byte = 0x4E then .nonPriorityCustomer
  else if byte = 0x46 then .firm
  else if byte = 0x42 then .brokerDealer
  else if byte = 0x50 then .memberMarketMaker
  else .awayExchangeMarketMaker

def ofByte (byte : UInt8) : Origin :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Origin) : ofByte value.toByte = value := by
  cases value with
  | priorityCustomer => decide
  | nonPriorityCustomer => decide
  | firm => decide
  | brokerDealer => decide
  | memberMarketMaker => decide
  | awayExchangeMarketMaker => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Origin) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Origin × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Origin) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Origin) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Origin) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Origin

/-- Contra Member Type: one byte code -/
def ContraMemberType.codes : List UInt8 :=
  [0x45, 0x4D, 0x52]

inductive ContraMemberType where
  | electronicExchangeMember -- Electronic Exchange Member
  | marketMaker -- Market Maker
  | routingBroker -- Routing Broker
  | unlisted (byte : { byte : UInt8 // byte ∉ ContraMemberType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ContraMemberType

def toByte : ContraMemberType → UInt8
  | .electronicExchangeMember => 0x45
  | .marketMaker => 0x4D
  | .routingBroker => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ContraMemberType :=
  if byte = 0x45 then .electronicExchangeMember
  else if byte = 0x4D then .marketMaker
  else .routingBroker

def ofByte (byte : UInt8) : ContraMemberType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ContraMemberType) : ofByte value.toByte = value := by
  cases value with
  | electronicExchangeMember => decide
  | marketMaker => decide
  | routingBroker => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ContraMemberType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ContraMemberType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ContraMemberType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ContraMemberType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ContraMemberType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ContraMemberType

/-- Contra Origin: one byte code -/
def ContraOrigin.codes : List UInt8 :=
  [0x43, 0x4E, 0x46, 0x42, 0x50, 0x41]

inductive ContraOrigin where
  | priorityCustomer -- Priority Customer
  | nonPriorityCustomer -- Non Priority Customer
  | firm -- Firm
  | brokerDealer -- Broker Dealer
  | memberMarketMaker -- Member Market Maker
  | awayExchangeMarketMaker -- Away Exchange Market Maker
  | unlisted (byte : { byte : UInt8 // byte ∉ ContraOrigin.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ContraOrigin

def toByte : ContraOrigin → UInt8
  | .priorityCustomer => 0x43
  | .nonPriorityCustomer => 0x4E
  | .firm => 0x46
  | .brokerDealer => 0x42
  | .memberMarketMaker => 0x50
  | .awayExchangeMarketMaker => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ContraOrigin :=
  if byte = 0x43 then .priorityCustomer
  else if byte = 0x4E then .nonPriorityCustomer
  else if byte = 0x46 then .firm
  else if byte = 0x42 then .brokerDealer
  else if byte = 0x50 then .memberMarketMaker
  else .awayExchangeMarketMaker

def ofByte (byte : UInt8) : ContraOrigin :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ContraOrigin) : ofByte value.toByte = value := by
  cases value with
  | priorityCustomer => decide
  | nonPriorityCustomer => decide
  | firm => decide
  | brokerDealer => decide
  | memberMarketMaker => decide
  | awayExchangeMarketMaker => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ContraOrigin) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ContraOrigin × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ContraOrigin) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ContraOrigin) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ContraOrigin) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ContraOrigin

/-- Contra Time In Force: one byte code -/
def ContraTimeInForce.codes : List UInt8 :=
  [0x30, 0x31, 0x33, 0x2A]

inductive ContraTimeInForce where
  | day -- Day
  | gtc -- Gtc
  | ioc -- Ioc
  | downgradedForOlderVersion -- Downgraded For Older Version
  | unlisted (byte : { byte : UInt8 // byte ∉ ContraTimeInForce.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ContraTimeInForce

def toByte : ContraTimeInForce → UInt8
  | .day => 0x30
  | .gtc => 0x31
  | .ioc => 0x33
  | .downgradedForOlderVersion => 0x2A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ContraTimeInForce :=
  if byte = 0x30 then .day
  else if byte = 0x31 then .gtc
  else if byte = 0x33 then .ioc
  else .downgradedForOlderVersion

def ofByte (byte : UInt8) : ContraTimeInForce :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ContraTimeInForce) : ofByte value.toByte = value := by
  cases value with
  | day => decide
  | gtc => decide
  | ioc => decide
  | downgradedForOlderVersion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ContraTimeInForce) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ContraTimeInForce × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ContraTimeInForce) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ContraTimeInForce) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ContraTimeInForce) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ContraTimeInForce

/-- Metric Type: one byte code -/
def MetricType.codes : List UInt8 :=
  [0x43, 0x4F, 0x2A]

inductive MetricType where
  | rateOfExecutedOrderContracts -- Rate Of Executed Order Contracts
  | rateOfNewReplaceOrdersReceived -- Rate Of New Replace Orders Received
  | downgradedForOlderVersion -- Downgraded For Older Version
  | unlisted (byte : { byte : UInt8 // byte ∉ MetricType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MetricType

def toByte : MetricType → UInt8
  | .rateOfExecutedOrderContracts => 0x43
  | .rateOfNewReplaceOrdersReceived => 0x4F
  | .downgradedForOlderVersion => 0x2A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MetricType :=
  if byte = 0x43 then .rateOfExecutedOrderContracts
  else if byte = 0x4F then .rateOfNewReplaceOrdersReceived
  else .downgradedForOlderVersion

def ofByte (byte : UInt8) : MetricType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MetricType) : ofByte value.toByte = value := by
  cases value with
  | rateOfExecutedOrderContracts => decide
  | rateOfNewReplaceOrdersReceived => decide
  | downgradedForOlderVersion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MetricType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MetricType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MetricType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : MetricType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : MetricType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MetricType

/-- Protection Type: one byte code -/
def ProtectionType.codes : List UInt8 :=
  [0x42, 0x4D, 0x57, 0x2A]

inductive ProtectionType where
  | block -- Block
  | blockAndMassCancel -- Block And Mass Cancel
  | warningOnly -- Warning Only
  | downgradedForOlderVersion -- Downgraded For Older Version
  | unlisted (byte : { byte : UInt8 // byte ∉ ProtectionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ProtectionType

def toByte : ProtectionType → UInt8
  | .block => 0x42
  | .blockAndMassCancel => 0x4D
  | .warningOnly => 0x57
  | .downgradedForOlderVersion => 0x2A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ProtectionType :=
  if byte = 0x42 then .block
  else if byte = 0x4D then .blockAndMassCancel
  else if byte = 0x57 then .warningOnly
  else .downgradedForOlderVersion

def ofByte (byte : UInt8) : ProtectionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ProtectionType) : ofByte value.toByte = value := by
  cases value with
  | block => decide
  | blockAndMassCancel => decide
  | warningOnly => decide
  | downgradedForOlderVersion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ProtectionType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ProtectionType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ProtectionType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ProtectionType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ProtectionType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ProtectionType

/-- Event Type: one byte code -/
def EventType.codes : List UInt8 :=
  [0x53, 0x54, 0x52, 0x57, 0x44, 0x41, 0x50, 0x55, 0x2A]

inductive EventType where
  | periodStatusPulseNotification -- Period Status Pulse Notification
  | safeguardTrigger -- Safeguard Trigger
  | resetRiskMetric -- Reset Risk Metric
  | warningOnly -- Warning Only
  | metricDeleted -- Metric Deleted
  | metricAdded -- Metric Added
  | metricPaused -- Metric Paused
  | metricUnPaused -- Metric Un Paused
  | downgradedForOlderVersion -- Downgraded For Older Version
  | unlisted (byte : { byte : UInt8 // byte ∉ EventType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventType

def toByte : EventType → UInt8
  | .periodStatusPulseNotification => 0x53
  | .safeguardTrigger => 0x54
  | .resetRiskMetric => 0x52
  | .warningOnly => 0x57
  | .metricDeleted => 0x44
  | .metricAdded => 0x41
  | .metricPaused => 0x50
  | .metricUnPaused => 0x55
  | .downgradedForOlderVersion => 0x2A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventType :=
  if byte = 0x53 then .periodStatusPulseNotification
  else if byte = 0x54 then .safeguardTrigger
  else if byte = 0x52 then .resetRiskMetric
  else if byte = 0x57 then .warningOnly
  else if byte = 0x44 then .metricDeleted
  else if byte = 0x41 then .metricAdded
  else if byte = 0x50 then .metricPaused
  else if byte = 0x55 then .metricUnPaused
  else .downgradedForOlderVersion

def ofByte (byte : UInt8) : EventType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventType) : ofByte value.toByte = value := by
  cases value with
  | periodStatusPulseNotification => decide
  | safeguardTrigger => decide
  | resetRiskMetric => decide
  | warningOnly => decide
  | metricDeleted => decide
  | metricAdded => decide
  | metricPaused => decide
  | metricUnPaused => decide
  | downgradedForOlderVersion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : EventType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (EventType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : EventType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : EventType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : EventType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end EventType

/-- Login Status: one byte code -/
def LoginStatus.codes : List UInt8 :=
  [0x20, 0x58, 0x53, 0x4E, 0x49, 0x41, 0x4C]

inductive LoginStatus where
  | loginSuccessful -- Login Successful
  | rejected -- Rejected
  | requestedSessionIsNotAvailable -- Requested Session Is Not Available
  | invalidStartSequenceNumberRequested -- Invalid Start Sequence Number Requested
  | incompatibleSessionProtocolVersion -- Incompatible Session Protocol Version
  | incompatibleApplicationProtocolVersion -- Incompatible Application Protocol Version
  | requestRejectedBecauseClientAlreadyLoggedIn -- Request Rejected Because Client Already Logged In
  | unlisted (byte : { byte : UInt8 // byte ∉ LoginStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LoginStatus

def toByte : LoginStatus → UInt8
  | .loginSuccessful => 0x20
  | .rejected => 0x58
  | .requestedSessionIsNotAvailable => 0x53
  | .invalidStartSequenceNumberRequested => 0x4E
  | .incompatibleSessionProtocolVersion => 0x49
  | .incompatibleApplicationProtocolVersion => 0x41
  | .requestRejectedBecauseClientAlreadyLoggedIn => 0x4C
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LoginStatus :=
  if byte = 0x20 then .loginSuccessful
  else if byte = 0x58 then .rejected
  else if byte = 0x53 then .requestedSessionIsNotAvailable
  else if byte = 0x4E then .invalidStartSequenceNumberRequested
  else if byte = 0x49 then .incompatibleSessionProtocolVersion
  else if byte = 0x41 then .incompatibleApplicationProtocolVersion
  else .requestRejectedBecauseClientAlreadyLoggedIn

def ofByte (byte : UInt8) : LoginStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LoginStatus) : ofByte value.toByte = value := by
  cases value with
  | loginSuccessful => decide
  | rejected => decide
  | requestedSessionIsNotAvailable => decide
  | invalidStartSequenceNumberRequested => decide
  | incompatibleSessionProtocolVersion => decide
  | incompatibleApplicationProtocolVersion => decide
  | requestRejectedBecauseClientAlreadyLoggedIn => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LoginStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LoginStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LoginStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : LoginStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : LoginStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LoginStatus

/-- Logout Reason: one byte code -/
def LogoutReason.codes : List UInt8 :=
  [0x20, 0x42, 0x4C, 0x41]

inductive LogoutReason where
  | gracefulLogout -- Graceful Logout
  | badSesmPacket -- Bad Sesm Packet
  | timedOutWaitingForLoginPacket -- Timed Out Waiting For Login Packet
  | applicationTerminatingConnection -- Application Terminating Connection
  | unlisted (byte : { byte : UInt8 // byte ∉ LogoutReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LogoutReason

def toByte : LogoutReason → UInt8
  | .gracefulLogout => 0x20
  | .badSesmPacket => 0x42
  | .timedOutWaitingForLoginPacket => 0x4C
  | .applicationTerminatingConnection => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LogoutReason :=
  if byte = 0x20 then .gracefulLogout
  else if byte = 0x42 then .badSesmPacket
  else if byte = 0x4C then .timedOutWaitingForLoginPacket
  else .applicationTerminatingConnection

def ofByte (byte : UInt8) : LogoutReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LogoutReason) : ofByte value.toByte = value := by
  cases value with
  | gracefulLogout => decide
  | badSesmPacket => decide
  | timedOutWaitingForLoginPacket => decide
  | applicationTerminatingConnection => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LogoutReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LogoutReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LogoutReason) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : LogoutReason) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : LogoutReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LogoutReason

/-- Goodbye Reason: one byte code -/
def GoodbyeReason.codes : List UInt8 :=
  [0x42, 0x4C, 0x41]

inductive GoodbyeReason where
  | badSesmPacket -- Bad Sesm Packet
  | timedOutWaitingForLoginPacket -- Timed Out Waiting For Login Packet
  | applicationTerminatingConnection -- Application Terminating Connection
  | unlisted (byte : { byte : UInt8 // byte ∉ GoodbyeReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace GoodbyeReason

def toByte : GoodbyeReason → UInt8
  | .badSesmPacket => 0x42
  | .timedOutWaitingForLoginPacket => 0x4C
  | .applicationTerminatingConnection => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : GoodbyeReason :=
  if byte = 0x42 then .badSesmPacket
  else if byte = 0x4C then .timedOutWaitingForLoginPacket
  else .applicationTerminatingConnection

def ofByte (byte : UInt8) : GoodbyeReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : GoodbyeReason) : ofByte value.toByte = value := by
  cases value with
  | badSesmPacket => decide
  | timedOutWaitingForLoginPacket => decide
  | applicationTerminatingConnection => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : GoodbyeReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (GoodbyeReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : GoodbyeReason) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : GoodbyeReason) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : GoodbyeReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end GoodbyeReason

/-- System State: 21 bytes -/
structure SystemState where
  notificationTime : BitVec 64
  ctdVersion : Alpha 8
  tradingSessionId : BitVec 32
  systemStatus : SystemStatus
  deriving DecidableEq, Repr

namespace SystemState

def encode (message : SystemState) : List UInt8 :=
  encodeUIntLE 8 message.notificationTime
    ++ (Alpha.encode message.ctdVersion
    ++ (encodeUIntLE 4 message.tradingSessionId
    ++ (SystemStatus.encode message.systemStatus)))

def decode (bytes : List UInt8) : Option (SystemState × List UInt8) := do
  let (notificationTime, bytes) ← decodeUIntLE 8 bytes
  let (ctdVersion, bytes) ← Alpha.decode 8 bytes
  let (tradingSessionId, bytes) ← decodeUIntLE 4 bytes
  let (systemStatus, bytes) ← SystemStatus.decode bytes
  pure ({ notificationTime, ctdVersion, tradingSessionId, systemStatus }, bytes)

@[simp] theorem encode_length (message : SystemState) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, SystemStatus.encode_length]

theorem encode_length_pos (message : SystemState) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemState) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [SystemStatus.decode_encode, some_bind]
  rfl

end SystemState

/-- Trade Message: 318 bytes -/
structure TradeMessage where
  processingTime : BitVec 64
  tradeTime : BitVec 64
  tradeAsOfDate : BitVec 32
  tradeAction : TradeAction
  tradeType : TradeType
  tradeId : BitVec 32
  executionId : BitVec 64
  correctionNumber : BitVec 8
  transactionId : BitVec 32
  referenceTradeTime : BitVec 64
  referenceTradeId : BitVec 32
  referenceCorrectionNumber : BitVec 8
  correctionType : CorrectionType
  reserved20 : Alpha 20
  productId : BitVec 32
  underlyingSymbol : Alpha 11
  underlyingType : UnderlyingType
  securitySymbol : Alpha 6
  expirationDate : BitVec 32
  strikePrice : BitVec 32
  callOrPut : CallOrPut
  reserved8 : Alpha 8
  side : Side
  price : BitVec 32
  size : BitVec 32
  tradeCondition : TradeCondition
  secondReserved8 : Alpha 8
  classFeeType : ClassFeeType
  pearlBboPostingIncrementIndicator : PearlBboPostingIncrementIndicator
  executionExchange : ExecutionExchange
  routedOrderQuantity : BitVec 32
  marketState : MarketState
  freeTradingCondition : FreeTradingCondition
  secondReserved20 : Alpha 20
  executingMpid : Alpha 4
  orderDate : BitVec 32
  fixOrderId : Alpha 30
  clientOrderId : BitVec 32
  clientMessageId : BitVec 32
  bulkLiquidityIndex : BitVec 8
  openCloseIndicator : OpenCloseIndicator
  liquidityType : LiquidityType
  liquidityIndicator : LiquidityIndicator
  timeInForce : TimeInForce
  thirdReserved20 : Alpha 20
  clearingMpid : Alpha 4
  memberType : MemberType
  origin : Origin
  clearingNumber : BitVec 32
  cmta : BitVec 32
  multiAccount : Alpha 5
  accountId : Alpha 10
  supplementaryId : Alpha 13
  reserved16 : Alpha 16
  mpid : Alpha 4
  contraMemberType : ContraMemberType
  contraOrigin : ContraOrigin
  contraClearingNumber : BitVec 32
  contraCmta : BitVec 32
  contraTimeInForce : ContraTimeInForce
  reserved15 : Alpha 15
  deriving DecidableEq, Repr

namespace TradeMessage

def encode (message : TradeMessage) : List UInt8 :=
  encodeUIntLE 8 message.processingTime
    ++ (encodeUIntLE 8 message.tradeTime
    ++ (encodeUIntLE 4 message.tradeAsOfDate
    ++ (TradeAction.encode message.tradeAction
    ++ (TradeType.encode message.tradeType
    ++ (encodeUIntLE 4 message.tradeId
    ++ (encodeUIntLE 8 message.executionId
    ++ (encodeUInt 1 message.correctionNumber
    ++ (encodeUIntLE 4 message.transactionId
    ++ (encodeUIntLE 8 message.referenceTradeTime
    ++ (encodeUIntLE 4 message.referenceTradeId
    ++ (encodeUInt 1 message.referenceCorrectionNumber
    ++ (CorrectionType.encode message.correctionType
    ++ (Alpha.encode message.reserved20
    ++ (encodeUIntLE 4 message.productId
    ++ (Alpha.encode message.underlyingSymbol
    ++ (UnderlyingType.encode message.underlyingType
    ++ (Alpha.encode message.securitySymbol
    ++ (encodeUIntLE 4 message.expirationDate
    ++ (encodeUIntLE 4 message.strikePrice
    ++ (CallOrPut.encode message.callOrPut
    ++ (Alpha.encode message.reserved8
    ++ (Side.encode message.side
    ++ (encodeUIntLE 4 message.price
    ++ (encodeUIntLE 4 message.size
    ++ (TradeCondition.encode message.tradeCondition
    ++ (Alpha.encode message.secondReserved8
    ++ (ClassFeeType.encode message.classFeeType
    ++ (PearlBboPostingIncrementIndicator.encode message.pearlBboPostingIncrementIndicator
    ++ (ExecutionExchange.encode message.executionExchange
    ++ (encodeUIntLE 4 message.routedOrderQuantity
    ++ (MarketState.encode message.marketState
    ++ (FreeTradingCondition.encode message.freeTradingCondition
    ++ (Alpha.encode message.secondReserved20
    ++ (Alpha.encode message.executingMpid
    ++ (encodeUIntLE 4 message.orderDate
    ++ (Alpha.encode message.fixOrderId
    ++ (encodeUIntLE 4 message.clientOrderId
    ++ (encodeUIntLE 4 message.clientMessageId
    ++ (encodeUInt 1 message.bulkLiquidityIndex
    ++ (OpenCloseIndicator.encode message.openCloseIndicator
    ++ (LiquidityType.encode message.liquidityType
    ++ (LiquidityIndicator.encode message.liquidityIndicator
    ++ (TimeInForce.encode message.timeInForce
    ++ (Alpha.encode message.thirdReserved20
    ++ (Alpha.encode message.clearingMpid
    ++ (MemberType.encode message.memberType
    ++ (Origin.encode message.origin
    ++ (encodeUIntLE 4 message.clearingNumber
    ++ (encodeUIntLE 4 message.cmta
    ++ (Alpha.encode message.multiAccount
    ++ (Alpha.encode message.accountId
    ++ (Alpha.encode message.supplementaryId
    ++ (Alpha.encode message.reserved16
    ++ (Alpha.encode message.mpid
    ++ (ContraMemberType.encode message.contraMemberType
    ++ (ContraOrigin.encode message.contraOrigin
    ++ (encodeUIntLE 4 message.contraClearingNumber
    ++ (encodeUIntLE 4 message.contraCmta
    ++ (ContraTimeInForce.encode message.contraTimeInForce
    ++ (Alpha.encode message.reserved15))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TradeMessage × List UInt8) := do
  let (processingTime, bytes) ← decodeUIntLE 8 bytes
  let (tradeTime, bytes) ← decodeUIntLE 8 bytes
  let (tradeAsOfDate, bytes) ← decodeUIntLE 4 bytes
  let (tradeAction, bytes) ← TradeAction.decode bytes
  let (tradeType, bytes) ← TradeType.decode bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (executionId, bytes) ← decodeUIntLE 8 bytes
  let (correctionNumber, bytes) ← decodeUInt 1 bytes
  let (transactionId, bytes) ← decodeUIntLE 4 bytes
  let (referenceTradeTime, bytes) ← decodeUIntLE 8 bytes
  let (referenceTradeId, bytes) ← decodeUIntLE 4 bytes
  let (referenceCorrectionNumber, bytes) ← decodeUInt 1 bytes
  let (correctionType, bytes) ← CorrectionType.decode bytes
  let (reserved20, bytes) ← Alpha.decode 20 bytes
  let (productId, bytes) ← decodeUIntLE 4 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 11 bytes
  let (underlyingType, bytes) ← UnderlyingType.decode bytes
  let (securitySymbol, bytes) ← Alpha.decode 6 bytes
  let (expirationDate, bytes) ← decodeUIntLE 4 bytes
  let (strikePrice, bytes) ← decodeUIntLE 4 bytes
  let (callOrPut, bytes) ← CallOrPut.decode bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (price, bytes) ← decodeUIntLE 4 bytes
  let (size, bytes) ← decodeUIntLE 4 bytes
  let (tradeCondition, bytes) ← TradeCondition.decode bytes
  let (secondReserved8, bytes) ← Alpha.decode 8 bytes
  let (classFeeType, bytes) ← ClassFeeType.decode bytes
  let (pearlBboPostingIncrementIndicator, bytes) ← PearlBboPostingIncrementIndicator.decode bytes
  let (executionExchange, bytes) ← ExecutionExchange.decode bytes
  let (routedOrderQuantity, bytes) ← decodeUIntLE 4 bytes
  let (marketState, bytes) ← MarketState.decode bytes
  let (freeTradingCondition, bytes) ← FreeTradingCondition.decode bytes
  let (secondReserved20, bytes) ← Alpha.decode 20 bytes
  let (executingMpid, bytes) ← Alpha.decode 4 bytes
  let (orderDate, bytes) ← decodeUIntLE 4 bytes
  let (fixOrderId, bytes) ← Alpha.decode 30 bytes
  let (clientOrderId, bytes) ← decodeUIntLE 4 bytes
  let (clientMessageId, bytes) ← decodeUIntLE 4 bytes
  let (bulkLiquidityIndex, bytes) ← decodeUInt 1 bytes
  let (openCloseIndicator, bytes) ← OpenCloseIndicator.decode bytes
  let (liquidityType, bytes) ← LiquidityType.decode bytes
  let (liquidityIndicator, bytes) ← LiquidityIndicator.decode bytes
  let (timeInForce, bytes) ← TimeInForce.decode bytes
  let (thirdReserved20, bytes) ← Alpha.decode 20 bytes
  let (clearingMpid, bytes) ← Alpha.decode 4 bytes
  let (memberType, bytes) ← MemberType.decode bytes
  let (origin, bytes) ← Origin.decode bytes
  let (clearingNumber, bytes) ← decodeUIntLE 4 bytes
  let (cmta, bytes) ← decodeUIntLE 4 bytes
  let (multiAccount, bytes) ← Alpha.decode 5 bytes
  let (accountId, bytes) ← Alpha.decode 10 bytes
  let (supplementaryId, bytes) ← Alpha.decode 13 bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (contraMemberType, bytes) ← ContraMemberType.decode bytes
  let (contraOrigin, bytes) ← ContraOrigin.decode bytes
  let (contraClearingNumber, bytes) ← decodeUIntLE 4 bytes
  let (contraCmta, bytes) ← decodeUIntLE 4 bytes
  let (contraTimeInForce, bytes) ← ContraTimeInForce.decode bytes
  let (reserved15, bytes) ← Alpha.decode 15 bytes
  pure ({ processingTime, tradeTime, tradeAsOfDate, tradeAction, tradeType, tradeId, executionId, correctionNumber, transactionId, referenceTradeTime, referenceTradeId, referenceCorrectionNumber, correctionType, reserved20, productId, underlyingSymbol, underlyingType, securitySymbol, expirationDate, strikePrice, callOrPut, reserved8, side, price, size, tradeCondition, secondReserved8, classFeeType, pearlBboPostingIncrementIndicator, executionExchange, routedOrderQuantity, marketState, freeTradingCondition, secondReserved20, executingMpid, orderDate, fixOrderId, clientOrderId, clientMessageId, bulkLiquidityIndex, openCloseIndicator, liquidityType, liquidityIndicator, timeInForce, thirdReserved20, clearingMpid, memberType, origin, clearingNumber, cmta, multiAccount, accountId, supplementaryId, reserved16, mpid, contraMemberType, contraOrigin, contraClearingNumber, contraCmta, contraTimeInForce, reserved15 }, bytes)

@[simp] theorem encode_length (message : TradeMessage) : (encode message).length = 318 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, TradeAction.encode_length, TradeType.encode_length, encodeUInt_length, CorrectionType.encode_length, Alpha.encode_length, UnderlyingType.encode_length, CallOrPut.encode_length, Side.encode_length, TradeCondition.encode_length, ClassFeeType.encode_length, PearlBboPostingIncrementIndicator.encode_length, ExecutionExchange.encode_length, MarketState.encode_length, FreeTradingCondition.encode_length, OpenCloseIndicator.encode_length, LiquidityType.encode_length, LiquidityIndicator.encode_length, TimeInForce.encode_length, MemberType.encode_length, Origin.encode_length, ContraMemberType.encode_length, ContraOrigin.encode_length, ContraTimeInForce.encode_length]

theorem encode_length_pos (message : TradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : TradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TradeAction.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, CorrectionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, UnderlyingType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, CallOrPut.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TradeCondition.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ClassFeeType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PearlBboPostingIncrementIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExecutionExchange.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, MarketState.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FreeTradingCondition.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OpenCloseIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LiquidityType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LiquidityIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TimeInForce.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MemberType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Origin.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [List.append_assoc, ContraMemberType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ContraOrigin.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, ContraTimeInForce.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeMessage

/-- Risk Notification Message: 160 bytes -/
structure RiskNotificationMessage where
  processingTime : BitVec 64
  mpidGroupId : Alpha 32
  metricId : Alpha 32
  routeId : Alpha 32
  metricType : MetricType
  protectionType : ProtectionType
  eventType : EventType
  eventId : BitVec 32
  configuredCountingTimePeriod : BitVec 32
  configuredMaxQuantity : BitVec 32
  currentQuantity : BitVec 32
  maxPeakQuantity : BitVec 32
  percentageLevel : BitVec 8
  reserved32 : Alpha 32
  deriving DecidableEq, Repr

namespace RiskNotificationMessage

def encode (message : RiskNotificationMessage) : List UInt8 :=
  encodeUIntLE 8 message.processingTime
    ++ (Alpha.encode message.mpidGroupId
    ++ (Alpha.encode message.metricId
    ++ (Alpha.encode message.routeId
    ++ (MetricType.encode message.metricType
    ++ (ProtectionType.encode message.protectionType
    ++ (EventType.encode message.eventType
    ++ (encodeUIntLE 4 message.eventId
    ++ (encodeUIntLE 4 message.configuredCountingTimePeriod
    ++ (encodeUIntLE 4 message.configuredMaxQuantity
    ++ (encodeUIntLE 4 message.currentQuantity
    ++ (encodeUIntLE 4 message.maxPeakQuantity
    ++ (encodeUInt 1 message.percentageLevel
    ++ (Alpha.encode message.reserved32)))))))))))))

def decode (bytes : List UInt8) : Option (RiskNotificationMessage × List UInt8) := do
  let (processingTime, bytes) ← decodeUIntLE 8 bytes
  let (mpidGroupId, bytes) ← Alpha.decode 32 bytes
  let (metricId, bytes) ← Alpha.decode 32 bytes
  let (routeId, bytes) ← Alpha.decode 32 bytes
  let (metricType, bytes) ← MetricType.decode bytes
  let (protectionType, bytes) ← ProtectionType.decode bytes
  let (eventType, bytes) ← EventType.decode bytes
  let (eventId, bytes) ← decodeUIntLE 4 bytes
  let (configuredCountingTimePeriod, bytes) ← decodeUIntLE 4 bytes
  let (configuredMaxQuantity, bytes) ← decodeUIntLE 4 bytes
  let (currentQuantity, bytes) ← decodeUIntLE 4 bytes
  let (maxPeakQuantity, bytes) ← decodeUIntLE 4 bytes
  let (percentageLevel, bytes) ← decodeUInt 1 bytes
  let (reserved32, bytes) ← Alpha.decode 32 bytes
  pure ({ processingTime, mpidGroupId, metricId, routeId, metricType, protectionType, eventType, eventId, configuredCountingTimePeriod, configuredMaxQuantity, currentQuantity, maxPeakQuantity, percentageLevel, reserved32 }, bytes)

@[simp] theorem encode_length (message : RiskNotificationMessage) : (encode message).length = 160 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, MetricType.encode_length, ProtectionType.encode_length, EventType.encode_length, encodeUInt_length]

theorem encode_length_pos (message : RiskNotificationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RiskNotificationMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, MetricType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ProtectionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, EventType.decode_encode, some_bind]
  dsimp only
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end RiskNotificationMessage

/-- Any Sequenced Message, selected by Sequenced Message Type -/
inductive SequencedMessage where
  | systemState (message : SystemState) -- "S" 0x53
  | tradeMessage (message : TradeMessage) -- "T" 0x54
  | riskNotificationMessage (message : RiskNotificationMessage) -- "R" 0x52
  deriving DecidableEq, Repr

namespace SequencedMessage

/-- The Sequenced Message Type each message is sent under -/
def tag : SequencedMessage → BitVec 8
  | .systemState _ => 83
  | .tradeMessage _ => 84
  | .riskNotificationMessage _ => 82

def encode : SequencedMessage → List UInt8
  | .systemState message => SystemState.encode message
  | .tradeMessage message => TradeMessage.encode message
  | .riskNotificationMessage message => RiskNotificationMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : SequencedMessage) : (encode message).length ≤ 318 := by
  cases message with
  | systemState inner =>
    simp only [encode, SystemState.encode_length]
    omega
  | tradeMessage inner =>
    simp only [encode, TradeMessage.encode_length]
    omega
  | riskNotificationMessage inner =>
    simp only [encode, RiskNotificationMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (SequencedMessage × List UInt8) :=
  if tag = 83 then (SystemState.decode bytes).map fun (message, rest) => (.systemState message, rest)
  else if tag = 84 then (TradeMessage.decode bytes).map fun (message, rest) => (.tradeMessage message, rest)
  else if tag = 82 then (RiskNotificationMessage.decode bytes).map fun (message, rest) => (.riskNotificationMessage message, rest)
  else none

@[simp] theorem decode_encode (message : SequencedMessage) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end SequencedMessage

/-- Sequenced Data Packet -/
structure SequencedDataPacket where
  sequenceNumber : BitVec 64
  sequencedMessage : SequencedMessage
  deriving DecidableEq, Repr

namespace SequencedDataPacket

def encode (message : SequencedDataPacket) : List UInt8 :=
  encodeUIntLE 8 message.sequenceNumber
    ++ (encodeUInt 1 (SequencedMessage.tag message.sequencedMessage)
    ++ (SequencedMessage.encode message.sequencedMessage))

def decode (bytes : List UInt8) : Option (SequencedDataPacket × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 8 bytes
  let (sequencedMessageType, bytes) ← decodeUInt 1 bytes
  let (sequencedMessage, bytes) ← SequencedMessage.decode sequencedMessageType bytes
  pure ({ sequenceNumber, sequencedMessage }, bytes)

theorem encode_length_pos (message : SequencedDataPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SequencedDataPacket) : (encode message).length ≤ 327 := by
  unfold encode
  cases message.sequencedMessage with
  | systemState inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, SystemState.encode_length]
    omega
  | tradeMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, TradeMessage.encode_length]
    omega
  | riskNotificationMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, RiskNotificationMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : SequencedDataPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [SequencedMessage.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SequencedDataPacket) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SequencedDataPacket

/-- Any Unsequenced Message, selected by Unsequenced Message Type -/
inductive UnsequencedMessage where
  | riskNotificationMessage (message : RiskNotificationMessage) -- "R" 0x52
  deriving DecidableEq, Repr

namespace UnsequencedMessage

/-- The Unsequenced Message Type each message is sent under -/
def tag : UnsequencedMessage → BitVec 8
  | .riskNotificationMessage _ => 82

def encode : UnsequencedMessage → List UInt8
  | .riskNotificationMessage message => RiskNotificationMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : UnsequencedMessage) : (encode message).length ≤ 160 := by
  cases message with
  | riskNotificationMessage inner =>
    simp only [encode, RiskNotificationMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (UnsequencedMessage × List UInt8) :=
  if tag = 82 then (RiskNotificationMessage.decode bytes).map fun (message, rest) => (.riskNotificationMessage message, rest)
  else none

@[simp] theorem decode_encode (message : UnsequencedMessage) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end UnsequencedMessage

/-- Unsequenced Data Packet -/
structure UnsequencedDataPacket where
  unsequencedMessage : UnsequencedMessage
  deriving DecidableEq, Repr

namespace UnsequencedDataPacket

def encode (message : UnsequencedDataPacket) : List UInt8 :=
  encodeUInt 1 (UnsequencedMessage.tag message.unsequencedMessage)
    ++ (UnsequencedMessage.encode message.unsequencedMessage)

def decode (bytes : List UInt8) : Option (UnsequencedDataPacket × List UInt8) := do
  let (unsequencedMessageType, bytes) ← decodeUInt 1 bytes
  let (unsequencedMessage, bytes) ← UnsequencedMessage.decode unsequencedMessageType bytes
  pure ({ unsequencedMessage }, bytes)

theorem encode_length_pos (message : UnsequencedDataPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : UnsequencedDataPacket) : (encode message).length ≤ 161 := by
  unfold encode
  cases message.unsequencedMessage with
  | riskNotificationMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, RiskNotificationMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : UnsequencedDataPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [UnsequencedMessage.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : UnsequencedDataPacket) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end UnsequencedDataPacket

/-- Login Request: 35 bytes -/
structure LoginRequest where
  sesmVersion : Alpha 5
  username : Alpha 5
  computerId : Alpha 8
  applicationProtocol : Alpha 8
  requestedSession : BitVec 8
  requestedSequenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace LoginRequest

def encode (message : LoginRequest) : List UInt8 :=
  Alpha.encode message.sesmVersion
    ++ (Alpha.encode message.username
    ++ (Alpha.encode message.computerId
    ++ (Alpha.encode message.applicationProtocol
    ++ (encodeUInt 1 message.requestedSession
    ++ (encodeUIntLE 8 message.requestedSequenceNumber)))))

def decode (bytes : List UInt8) : Option (LoginRequest × List UInt8) := do
  let (sesmVersion, bytes) ← Alpha.decode 5 bytes
  let (username, bytes) ← Alpha.decode 5 bytes
  let (computerId, bytes) ← Alpha.decode 8 bytes
  let (applicationProtocol, bytes) ← Alpha.decode 8 bytes
  let (requestedSession, bytes) ← decodeUInt 1 bytes
  let (requestedSequenceNumber, bytes) ← decodeUIntLE 8 bytes
  pure ({ sesmVersion, username, computerId, applicationProtocol, requestedSession, requestedSequenceNumber }, bytes)

@[simp] theorem encode_length (message : LoginRequest) : (encode message).length = 35 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, encodeUIntLE_length]

theorem encode_length_pos (message : LoginRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginRequest) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LoginRequest) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end LoginRequest

/-- Login Response: 10 bytes -/
structure LoginResponse where
  loginStatus : LoginStatus
  sessionId : BitVec 8
  highestSequenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace LoginResponse

def encode (message : LoginResponse) : List UInt8 :=
  LoginStatus.encode message.loginStatus
    ++ (encodeUInt 1 message.sessionId
    ++ (encodeUIntLE 8 message.highestSequenceNumber))

def decode (bytes : List UInt8) : Option (LoginResponse × List UInt8) := do
  let (loginStatus, bytes) ← LoginStatus.decode bytes
  let (sessionId, bytes) ← decodeUInt 1 bytes
  let (highestSequenceNumber, bytes) ← decodeUIntLE 8 bytes
  pure ({ loginStatus, sessionId, highestSequenceNumber }, bytes)

@[simp] theorem encode_length (message : LoginResponse) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, LoginStatus.encode_length, encodeUInt_length, encodeUIntLE_length]

theorem encode_length_pos (message : LoginResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LoginStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LoginResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end LoginResponse

/-- Synchronization Complete: 0 bytes -/
structure SynchronizationComplete where
  deriving DecidableEq, Repr

namespace SynchronizationComplete

def encode (_ : SynchronizationComplete) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (SynchronizationComplete × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : SynchronizationComplete) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : SynchronizationComplete) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SynchronizationComplete) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SynchronizationComplete

/-- Retransmission Request: 16 bytes -/
structure RetransmissionRequest where
  startSequenceNumber : BitVec 64
  endSequenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace RetransmissionRequest

def encode (message : RetransmissionRequest) : List UInt8 :=
  encodeUIntLE 8 message.startSequenceNumber
    ++ (encodeUIntLE 8 message.endSequenceNumber)

def decode (bytes : List UInt8) : Option (RetransmissionRequest × List UInt8) := do
  let (startSequenceNumber, bytes) ← decodeUIntLE 8 bytes
  let (endSequenceNumber, bytes) ← decodeUIntLE 8 bytes
  pure ({ startSequenceNumber, endSequenceNumber }, bytes)

@[simp] theorem encode_length (message : RetransmissionRequest) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : RetransmissionRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RetransmissionRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : RetransmissionRequest) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end RetransmissionRequest

/-- Logout Request -/
structure LogoutRequest where
  logoutReason : LogoutReason
  logoutText : Capped 65207
  deriving DecidableEq, Repr

namespace LogoutRequest

def encode (message : LogoutRequest) : List UInt8 :=
  LogoutReason.encode message.logoutReason
    ++ (message.logoutText.val)

def decode (bytes : List UInt8) : Option LogoutRequest := do
  let (logoutReason, bytes) ← LogoutReason.decode bytes
  let logoutText_ := bytes
  if fits_logoutText : logoutText_.length ≤ 65207 then
    pure { logoutReason, logoutText := ⟨logoutText_, fits_logoutText⟩ }
  else none

theorem encode_length_pos (message : LogoutRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [LogoutReason.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : LogoutRequest) : (encode message).length ≤ 65208 := by
  have bound_logoutText := message.logoutText.length_le
  unfold encode
  simp only [List.length_append, LogoutReason.encode_length]
  omega

theorem decode_encode (message : LogoutRequest) : decode (encode message) = some message := by
  unfold decode encode
  rw [LogoutReason.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.logoutText.length_le]
  rfl

end LogoutRequest

/-- Goodbye Packet -/
structure GoodbyePacket where
  goodbyeReason : GoodbyeReason
  logoutText : Capped 65207
  deriving DecidableEq, Repr

namespace GoodbyePacket

def encode (message : GoodbyePacket) : List UInt8 :=
  GoodbyeReason.encode message.goodbyeReason
    ++ (message.logoutText.val)

def decode (bytes : List UInt8) : Option GoodbyePacket := do
  let (goodbyeReason, bytes) ← GoodbyeReason.decode bytes
  let logoutText_ := bytes
  if fits_logoutText : logoutText_.length ≤ 65207 then
    pure { goodbyeReason, logoutText := ⟨logoutText_, fits_logoutText⟩ }
  else none

theorem encode_length_pos (message : GoodbyePacket) : (encode message).length > 0 := by
  unfold encode
  simp only [GoodbyeReason.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : GoodbyePacket) : (encode message).length ≤ 65208 := by
  have bound_logoutText := message.logoutText.length_le
  unfold encode
  simp only [List.length_append, GoodbyeReason.encode_length]
  omega

theorem decode_encode (message : GoodbyePacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [GoodbyeReason.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.logoutText.length_le]
  rfl

end GoodbyePacket

/-- End Of Session: 0 bytes -/
structure EndOfSession where
  deriving DecidableEq, Repr

namespace EndOfSession

def encode (_ : EndOfSession) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (EndOfSession × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : EndOfSession) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : EndOfSession) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : EndOfSession) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end EndOfSession

/-- Server Heartbeat: 0 bytes -/
structure ServerHeartbeat where
  deriving DecidableEq, Repr

namespace ServerHeartbeat

def encode (_ : ServerHeartbeat) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (ServerHeartbeat × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : ServerHeartbeat) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : ServerHeartbeat) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ServerHeartbeat) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ServerHeartbeat

/-- Client Heartbeat: 0 bytes -/
structure ClientHeartbeat where
  deriving DecidableEq, Repr

namespace ClientHeartbeat

def encode (_ : ClientHeartbeat) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (ClientHeartbeat × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : ClientHeartbeat) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : ClientHeartbeat) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ClientHeartbeat) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ClientHeartbeat

/-- Test Packet -/
structure TestPacket where
  testText : Capped 65207
  deriving DecidableEq, Repr

namespace TestPacket

def encode (message : TestPacket) : List UInt8 :=
  message.testText.val

def decode (bytes : List UInt8) : Option TestPacket := do
  let testText_ := bytes
  if fits_testText : testText_.length ≤ 65207 then
    pure { testText := ⟨testText_, fits_testText⟩ }
  else none

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TestPacket) : (encode message).length ≤ 65207 := by
  have bound_testText := message.testText.length_le
  unfold encode
  omega

theorem decode_encode (message : TestPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [dite_eq_left message.testText.length_le]
  rfl

end TestPacket

/-- Any Sesm Payload, selected by Sesm Packet Type -/
inductive SesmPayload where
  | sequencedDataPacket (message : SequencedDataPacket) -- "S" 0x53
  | unsequencedDataPacket (message : UnsequencedDataPacket) -- "U" 0x55
  | loginRequest (message : LoginRequest) -- "L" 0x4C
  | loginResponse (message : LoginResponse) -- "R" 0x52
  | synchronizationComplete (message : SynchronizationComplete) -- "C" 0x43
  | retransmissionRequest (message : RetransmissionRequest) -- "A" 0x41
  | logoutRequest (message : LogoutRequest) -- "X" 0x58
  | goodbyePacket (message : GoodbyePacket) -- "G" 0x47
  | endOfSession (message : EndOfSession) -- "E" 0x45
  | serverHeartbeat (message : ServerHeartbeat) -- "0" 0x30
  | clientHeartbeat (message : ClientHeartbeat) -- "1" 0x31
  | testPacket (message : TestPacket) -- "T" 0x54
  deriving DecidableEq, Repr

namespace SesmPayload

/-- The Sesm Packet Type each message is sent under -/
def tag : SesmPayload → BitVec 8
  | .sequencedDataPacket _ => 83
  | .unsequencedDataPacket _ => 85
  | .loginRequest _ => 76
  | .loginResponse _ => 82
  | .synchronizationComplete _ => 67
  | .retransmissionRequest _ => 65
  | .logoutRequest _ => 88
  | .goodbyePacket _ => 71
  | .endOfSession _ => 69
  | .serverHeartbeat _ => 48
  | .clientHeartbeat _ => 49
  | .testPacket _ => 84

def encode : SesmPayload → List UInt8
  | .sequencedDataPacket message => SequencedDataPacket.encode message
  | .unsequencedDataPacket message => UnsequencedDataPacket.encode message
  | .loginRequest message => LoginRequest.encode message
  | .loginResponse message => LoginResponse.encode message
  | .synchronizationComplete message => SynchronizationComplete.encode message
  | .retransmissionRequest message => RetransmissionRequest.encode message
  | .logoutRequest message => LogoutRequest.encode message
  | .goodbyePacket message => GoodbyePacket.encode message
  | .endOfSession message => EndOfSession.encode message
  | .serverHeartbeat message => ServerHeartbeat.encode message
  | .clientHeartbeat message => ClientHeartbeat.encode message
  | .testPacket message => TestPacket.encode message

/-- Does the message end the session? Nothing in its packet may follow it -/
def endsSession : SesmPayload → Bool
  | .endOfSession _ => true
  | _ => false

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : SesmPayload) : (encode message).length ≤ 65208 := by
  cases message with
  | sequencedDataPacket inner =>
    have bound_inner := SequencedDataPacket.encode_length_le inner
    simp only [encode]
    omega
  | unsequencedDataPacket inner =>
    have bound_inner := UnsequencedDataPacket.encode_length_le inner
    simp only [encode]
    omega
  | loginRequest inner =>
    simp only [encode, LoginRequest.encode_length]
    omega
  | loginResponse inner =>
    simp only [encode, LoginResponse.encode_length]
    omega
  | synchronizationComplete inner =>
    simp only [encode, SynchronizationComplete.encode_length]
    omega
  | retransmissionRequest inner =>
    simp only [encode, RetransmissionRequest.encode_length]
    omega
  | logoutRequest inner =>
    have bound_inner := LogoutRequest.encode_length_le inner
    simp only [encode]
    omega
  | goodbyePacket inner =>
    have bound_inner := GoodbyePacket.encode_length_le inner
    simp only [encode]
    omega
  | endOfSession inner =>
    simp only [encode, EndOfSession.encode_length]
    omega
  | serverHeartbeat inner =>
    simp only [encode, ServerHeartbeat.encode_length]
    omega
  | clientHeartbeat inner =>
    simp only [encode, ClientHeartbeat.encode_length]
    omega
  | testPacket inner =>
    have bound_inner := TestPacket.encode_length_le inner
    simp only [encode]
    omega

/-- Decoded from the whole of the frame: a message that reads to its end takes it all, any other must leave nothing -/
def decode (tag : BitVec 8) (bytes : List UInt8) : Option SesmPayload :=
  if tag = 83 then (SequencedDataPacket.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.sequencedDataPacket message) else none
  else if tag = 85 then (UnsequencedDataPacket.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.unsequencedDataPacket message) else none
  else if tag = 76 then (LoginRequest.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.loginRequest message) else none
  else if tag = 82 then (LoginResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.loginResponse message) else none
  else if tag = 67 then (SynchronizationComplete.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.synchronizationComplete message) else none
  else if tag = 65 then (RetransmissionRequest.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.retransmissionRequest message) else none
  else if tag = 88 then (LogoutRequest.decode bytes).map fun message => .logoutRequest message
  else if tag = 71 then (GoodbyePacket.decode bytes).map fun message => .goodbyePacket message
  else if tag = 69 then (EndOfSession.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.endOfSession message) else none
  else if tag = 48 then (ServerHeartbeat.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.serverHeartbeat message) else none
  else if tag = 49 then (ClientHeartbeat.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.clientHeartbeat message) else none
  else if tag = 84 then (TestPacket.decode bytes).map fun message => .testPacket message
  else none

theorem decode_encode (message : SesmPayload) :
    decode (tag message) (encode message) = some message := by
  cases message with
  | sequencedDataPacket message => simp [decode, encode, tag, SequencedDataPacket.decode_encode_nil]
  | unsequencedDataPacket message => simp [decode, encode, tag, UnsequencedDataPacket.decode_encode_nil]
  | loginRequest message => simp [decode, encode, tag, LoginRequest.decode_encode_nil]
  | loginResponse message => simp [decode, encode, tag, LoginResponse.decode_encode_nil]
  | synchronizationComplete message => simp [decode, encode, tag, SynchronizationComplete.decode_encode_nil]
  | retransmissionRequest message => simp [decode, encode, tag, RetransmissionRequest.decode_encode_nil]
  | logoutRequest message => simp [decode, encode, tag, LogoutRequest.decode_encode]
  | goodbyePacket message => simp [decode, encode, tag, GoodbyePacket.decode_encode]
  | endOfSession message => simp [decode, encode, tag, EndOfSession.decode_encode_nil]
  | serverHeartbeat message => simp [decode, encode, tag, ServerHeartbeat.decode_encode_nil]
  | clientHeartbeat message => simp [decode, encode, tag, ClientHeartbeat.decode_encode_nil]
  | testPacket message => simp [decode, encode, tag, TestPacket.decode_encode]

end SesmPayload

/-- Sesm Tcp Packet -/
structure SesmTcpPacket where
  sesmPayload : SesmPayload
  deriving DecidableEq, Repr

namespace SesmTcpPacket

def encodeBody (message : SesmTcpPacket) : List UInt8 :=
  encodeUInt 1 (SesmPayload.tag message.sesmPayload)
    ++ (SesmPayload.encode message.sesmPayload)

def decodeBody (bytes : List UInt8) : Option SesmTcpPacket := do
  let (sesmPacketType, bytes) ← decodeUInt 1 bytes
  let sesmPayload ← SesmPayload.decode sesmPacketType bytes
  pure { sesmPayload }

theorem decodeBody_encodeBody (message : SesmTcpPacket) : decodeBody (encodeBody message) = some message := by
  unfold decodeBody encodeBody
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [SesmPayload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : SesmTcpPacket) : (encodeBody message).length + 0 < 256 ^ 2 := by
  unfold encodeBody
  cases message.sesmPayload with
  | sequencedDataPacket inner =>
    have bound_inner := SequencedDataPacket.encode_length_le inner
    simp only [SesmPayload.encode, List.length_append, encodeUInt_length]
    omega
  | unsequencedDataPacket inner =>
    have bound_inner := UnsequencedDataPacket.encode_length_le inner
    simp only [SesmPayload.encode, List.length_append, encodeUInt_length]
    omega
  | loginRequest inner =>
    simp only [SesmPayload.encode, List.length_append, encodeUInt_length, LoginRequest.encode_length]
    omega
  | loginResponse inner =>
    simp only [SesmPayload.encode, List.length_append, encodeUInt_length, LoginResponse.encode_length]
    omega
  | synchronizationComplete inner =>
    simp only [SesmPayload.encode, List.length_append, encodeUInt_length, SynchronizationComplete.encode_length]
    omega
  | retransmissionRequest inner =>
    simp only [SesmPayload.encode, List.length_append, encodeUInt_length, RetransmissionRequest.encode_length]
    omega
  | logoutRequest inner =>
    have bound_inner := LogoutRequest.encode_length_le inner
    simp only [SesmPayload.encode, List.length_append, encodeUInt_length]
    omega
  | goodbyePacket inner =>
    have bound_inner := GoodbyePacket.encode_length_le inner
    simp only [SesmPayload.encode, List.length_append, encodeUInt_length]
    omega
  | endOfSession inner =>
    simp only [SesmPayload.encode, List.length_append, encodeUInt_length, EndOfSession.encode_length]
    omega
  | serverHeartbeat inner =>
    simp only [SesmPayload.encode, List.length_append, encodeUInt_length, ServerHeartbeat.encode_length]
    omega
  | clientHeartbeat inner =>
    simp only [SesmPayload.encode, List.length_append, encodeUInt_length, ClientHeartbeat.encode_length]
    omega
  | testPacket inner =>
    have bound_inner := TestPacket.encode_length_le inner
    simp only [SesmPayload.encode, List.length_append, encodeUInt_length]
    omega

/-- Size rule: Sesm Packet Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : SesmTcpPacket → List UInt8 :=
  encodeFramedLE 2 0 encodeBody

def decode : List UInt8 → Option (SesmTcpPacket × List UInt8) :=
  decodeFramedAllLE 2 0 decodeBody

@[simp] theorem decode_encode (message : SesmTcpPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedAllLE_encodeFramedLE 2 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : SesmTcpPacket) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

/-- Does the message end the session? Nothing in its packet may follow it -/
def endsSession (message : SesmTcpPacket) : Bool :=
  SesmPayload.endsSession message.sesmPayload

end SesmTcpPacket

/-- Packet -/
structure Packet where
  sesmTcpPacket : List SesmTcpPacket
  sesmTcpPacket_last : endsLast SesmTcpPacket.endsSession sesmTcpPacket = true
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeMany SesmTcpPacket.encode message.sesmTcpPacket

def decode (bytes : List UInt8) : Option Packet := do
  let sesmTcpPacket ← decodeAll SesmTcpPacket.decode bytes.length bytes
  if last_sesmTcpPacket : endsLast SesmTcpPacket.endsSession sesmTcpPacket = true then
    pure { sesmTcpPacket, sesmTcpPacket_last := last_sesmTcpPacket }
  else none

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany SesmTcpPacket.encode SesmTcpPacket.decode SesmTcpPacket.decode_encode SesmTcpPacket.encode_length_pos message.sesmTcpPacket _ (encodeMany_length_ge SesmTcpPacket.encode SesmTcpPacket.encode_length_pos message.sesmTcpPacket), some_bind]
  rw [dite_eq_left message.sesmTcpPacket_last]
  rfl

end Packet

end Omi.MiaxPearloptionsClearingtradedropCtdV12C
