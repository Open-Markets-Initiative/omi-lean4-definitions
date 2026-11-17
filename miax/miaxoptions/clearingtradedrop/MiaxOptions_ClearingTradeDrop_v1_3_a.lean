import Wire

/-!
# Miami International Holdings Clearing Trade Drop v1.3.a

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

namespace Omi.MiaxMiaxoptionsClearingtradedropCtdV13A

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
  [0x20, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x4F, 0x50, 0x51, 0x52, 0x53, 0x54, 0x58]

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
  | reserved -- Reserved
  | reopeningOfAnOption -- Reopening Of An Option
  | reserved_4b -- Reserved
  | reserved_4c -- Reserved
  | reserved_4d -- Reserved
  | reserved_4e -- Reserved
  | reserved_4f -- Reserved
  | reserved_50 -- Reserved
  | reserved_51 -- Reserved
  | executionOfAStoppedOrder -- Execution Of A Stopped Order
  | executionOfAnIsoOrder -- Execution Of An Iso Order
  | reserved_54 -- Reserved
  | tradeThroughExempt -- Trade Through Exempt
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
  | .reserved => 0x49
  | .reopeningOfAnOption => 0x4A
  | .reserved_4b => 0x4B
  | .reserved_4c => 0x4C
  | .reserved_4d => 0x4D
  | .reserved_4e => 0x4E
  | .reserved_4f => 0x4F
  | .reserved_50 => 0x50
  | .reserved_51 => 0x51
  | .executionOfAStoppedOrder => 0x52
  | .executionOfAnIsoOrder => 0x53
  | .reserved_54 => 0x54
  | .tradeThroughExempt => 0x58
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
  else if byte = 0x49 then .reserved
  else if byte = 0x4A then .reopeningOfAnOption
  else if byte = 0x4B then .reserved_4b
  else if byte = 0x4C then .reserved_4c
  else if byte = 0x4D then .reserved_4d
  else if byte = 0x4E then .reserved_4e
  else if byte = 0x4F then .reserved_4f
  else if byte = 0x50 then .reserved_50
  else if byte = 0x51 then .reserved_51
  else if byte = 0x52 then .executionOfAStoppedOrder
  else if byte = 0x53 then .executionOfAnIsoOrder
  else if byte = 0x54 then .reserved_54
  else .tradeThroughExempt

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
  | reserved => decide
  | reopeningOfAnOption => decide
  | reserved_4b => decide
  | reserved_4c => decide
  | reserved_4d => decide
  | reserved_4e => decide
  | reserved_4f => decide
  | reserved_50 => decide
  | reserved_51 => decide
  | executionOfAStoppedOrder => decide
  | executionOfAnIsoOrder => decide
  | reserved_54 => decide
  | tradeThroughExempt => decide
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
  [0x43, 0x4D]

inductive ClassFeeType where
  | conventionalFeeBased -- Conventional Fee Based
  | makerTakerFeeBased -- Maker Taker Fee Based
  | unlisted (byte : { byte : UInt8 // byte ∉ ClassFeeType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ClassFeeType

def toByte : ClassFeeType → UInt8
  | .conventionalFeeBased => 0x43
  | .makerTakerFeeBased => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ClassFeeType :=
  if byte = 0x43 then .conventionalFeeBased
  else .makerTakerFeeBased

def ofByte (byte : UInt8) : ClassFeeType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ClassFeeType) : ofByte value.toByte = value := by
  cases value with
  | conventionalFeeBased => decide
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

/-- Miax Bbo Posting Increment Indicator: one byte code -/
def MiaxBboPostingIncrementIndicator.codes : List UInt8 :=
  [0x50, 0x4E, 0x44]

inductive MiaxBboPostingIncrementIndicator where
  | penny -- Penny
  | pennyNickel -- Penny Nickel
  | nickelDime -- Nickel Dime
  | unlisted (byte : { byte : UInt8 // byte ∉ MiaxBboPostingIncrementIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MiaxBboPostingIncrementIndicator

def toByte : MiaxBboPostingIncrementIndicator → UInt8
  | .penny => 0x50
  | .pennyNickel => 0x4E
  | .nickelDime => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MiaxBboPostingIncrementIndicator :=
  if byte = 0x50 then .penny
  else if byte = 0x4E then .pennyNickel
  else .nickelDime

def ofByte (byte : UInt8) : MiaxBboPostingIncrementIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MiaxBboPostingIncrementIndicator) : ofByte value.toByte = value := by
  cases value with
  | penny => decide
  | pennyNickel => decide
  | nickelDime => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MiaxBboPostingIncrementIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MiaxBboPostingIncrementIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MiaxBboPostingIncrementIndicator) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : MiaxBboPostingIncrementIndicator) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : MiaxBboPostingIncrementIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MiaxBboPostingIncrementIndicator

/-- Execution Exchange: one byte code -/
def ExecutionExchange.codes : List UInt8 :=
  [0x41, 0x4E, 0x42, 0x43, 0x57, 0x49, 0x48, 0x51, 0x58, 0x54, 0x5A, 0x20]

inductive ExecutionExchange where
  | nyseAmex -- Nyse Amex
  | nyseArca -- Nyse Arca
  | box -- Box
  | cboe -- Cboe
  | c2 -- C 2
  | ise -- Ise
  | iseTopaz -- Ise Topaz
  | nasdaqOmxOptionsMarket -- Nasdaq Omx Options Market
  | nasdaqOmxPhlxOptionsMarket -- Nasdaq Omx Phlx Options Market
  | nasdaqBx -- Nasdaq Bx
  | bats -- Bats
  | tradedAtMiax -- Traded At Miax
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
  | .iseTopaz => 0x48
  | .nasdaqOmxOptionsMarket => 0x51
  | .nasdaqOmxPhlxOptionsMarket => 0x58
  | .nasdaqBx => 0x54
  | .bats => 0x5A
  | .tradedAtMiax => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExecutionExchange :=
  if byte = 0x41 then .nyseAmex
  else if byte = 0x4E then .nyseArca
  else if byte = 0x42 then .box
  else if byte = 0x43 then .cboe
  else if byte = 0x57 then .c2
  else if byte = 0x49 then .ise
  else if byte = 0x48 then .iseTopaz
  else if byte = 0x51 then .nasdaqOmxOptionsMarket
  else if byte = 0x58 then .nasdaqOmxPhlxOptionsMarket
  else if byte = 0x54 then .nasdaqBx
  else if byte = 0x5A then .bats
  else .tradedAtMiax

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
  | iseTopaz => decide
  | nasdaqOmxOptionsMarket => decide
  | nasdaqOmxPhlxOptionsMarket => decide
  | nasdaqBx => decide
  | bats => decide
  | tradedAtMiax => decide
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

/-- Market Maker Role: one byte code -/
def MarketMakerRole.codes : List UInt8 :=
  [0x50, 0x4C, 0x52, 0x55, 0x20]

inductive MarketMakerRole where
  | plmm -- Plmm
  | lmm -- Lmm
  | rmm -- Rmm
  | umm -- Umm
  | other -- Other
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketMakerRole.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketMakerRole

def toByte : MarketMakerRole → UInt8
  | .plmm => 0x50
  | .lmm => 0x4C
  | .rmm => 0x52
  | .umm => 0x55
  | .other => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketMakerRole :=
  if byte = 0x50 then .plmm
  else if byte = 0x4C then .lmm
  else if byte = 0x52 then .rmm
  else if byte = 0x55 then .umm
  else .other

def ofByte (byte : UInt8) : MarketMakerRole :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketMakerRole) : ofByte value.toByte = value := by
  cases value with
  | plmm => decide
  | lmm => decide
  | rmm => decide
  | umm => decide
  | other => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarketMakerRole) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketMakerRole × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketMakerRole) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : MarketMakerRole) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : MarketMakerRole) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarketMakerRole

/-- Traded With Directed Mm: one byte code -/
def TradedWithDirectedMm.codes : List UInt8 :=
  [0x59, 0x4E, 0x20]

inductive TradedWithDirectedMm where
  | yes -- Yes
  | no -- No
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ TradedWithDirectedMm.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradedWithDirectedMm

def toByte : TradedWithDirectedMm → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradedWithDirectedMm :=
  if byte = 0x59 then .yes
  else if byte = 0x4E then .no
  else .notApplicable

def ofByte (byte : UInt8) : TradedWithDirectedMm :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradedWithDirectedMm) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradedWithDirectedMm) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradedWithDirectedMm × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradedWithDirectedMm) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TradedWithDirectedMm) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TradedWithDirectedMm) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradedWithDirectedMm

/-- Market State: one byte code -/
def MarketState.codes : List UInt8 :=
  [0x54, 0x41, 0x48, 0x4E, 0x20]

inductive MarketState where
  | freeTrading -- Free Trading
  | auction -- Auction
  | halted -- Halted
  | nonTradable -- Non Tradable
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketState

def toByte : MarketState → UInt8
  | .freeTrading => 0x54
  | .auction => 0x41
  | .halted => 0x48
  | .nonTradable => 0x4E
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketState :=
  if byte = 0x54 then .freeTrading
  else if byte = 0x41 then .auction
  else if byte = 0x48 then .halted
  else if byte = 0x4E then .nonTradable
  else .notApplicable

def ofByte (byte : UInt8) : MarketState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketState) : ofByte value.toByte = value := by
  cases value with
  | freeTrading => decide
  | auction => decide
  | halted => decide
  | nonTradable => decide
  | notApplicable => decide
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

/-- Auction Type: one byte code -/
def AuctionType.codes : List UInt8 :=
  [0x20, 0x31, 0x32, 0x33, 0x34, 0x35]

inductive AuctionType where
  | notApplicable -- Not Applicable
  | opening -- Opening
  | reopening -- Reopening
  | closing -- Closing
  | routing -- Routing
  | liquidityRefresh -- Liquidity Refresh
  | unlisted (byte : { byte : UInt8 // byte ∉ AuctionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AuctionType

def toByte : AuctionType → UInt8
  | .notApplicable => 0x20
  | .opening => 0x31
  | .reopening => 0x32
  | .closing => 0x33
  | .routing => 0x34
  | .liquidityRefresh => 0x35
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AuctionType :=
  if byte = 0x20 then .notApplicable
  else if byte = 0x31 then .opening
  else if byte = 0x32 then .reopening
  else if byte = 0x33 then .closing
  else if byte = 0x34 then .routing
  else .liquidityRefresh

def ofByte (byte : UInt8) : AuctionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AuctionType) : ofByte value.toByte = value := by
  cases value with
  | notApplicable => decide
  | opening => decide
  | reopening => decide
  | closing => decide
  | routing => decide
  | liquidityRefresh => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AuctionType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AuctionType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AuctionType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : AuctionType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : AuctionType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AuctionType

/-- Directed Status: one byte code -/
def DirectedStatus.codes : List UInt8 :=
  [0x45, 0x4E, 0x58]

inductive DirectedStatus where
  | externallyDirected -- Externally Directed
  | nonDirected -- Non Directed
  | dfcInvalid -- Dfc Invalid
  | unlisted (byte : { byte : UInt8 // byte ∉ DirectedStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DirectedStatus

def toByte : DirectedStatus → UInt8
  | .externallyDirected => 0x45
  | .nonDirected => 0x4E
  | .dfcInvalid => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DirectedStatus :=
  if byte = 0x45 then .externallyDirected
  else if byte = 0x4E then .nonDirected
  else .dfcInvalid

def ofByte (byte : UInt8) : DirectedStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DirectedStatus) : ofByte value.toByte = value := by
  cases value with
  | externallyDirected => decide
  | nonDirected => decide
  | dfcInvalid => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DirectedStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DirectedStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DirectedStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : DirectedStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : DirectedStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DirectedStatus

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
  [0x4F, 0x51, 0x45, 0x20]

inductive LiquidityType where
  | order -- Order
  | quote -- Quote
  | eQuote -- E Quote
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ LiquidityType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LiquidityType

def toByte : LiquidityType → UInt8
  | .order => 0x4F
  | .quote => 0x51
  | .eQuote => 0x45
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LiquidityType :=
  if byte = 0x4F then .order
  else if byte = 0x51 then .quote
  else if byte = 0x45 then .eQuote
  else .notApplicable

def ofByte (byte : UInt8) : LiquidityType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LiquidityType) : ofByte value.toByte = value := by
  cases value with
  | order => decide
  | quote => decide
  | eQuote => decide
  | notApplicable => decide
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

/-- Mm Priority Indicator: one byte code -/
def MmPriorityIndicator.codes : List UInt8 :=
  [0x59, 0x4E, 0x20]

inductive MmPriorityIndicator where
  | yes -- Yes
  | no -- No
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ MmPriorityIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MmPriorityIndicator

def toByte : MmPriorityIndicator → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MmPriorityIndicator :=
  if byte = 0x59 then .yes
  else if byte = 0x4E then .no
  else .notApplicable

def ofByte (byte : UInt8) : MmPriorityIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MmPriorityIndicator) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MmPriorityIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MmPriorityIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MmPriorityIndicator) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : MmPriorityIndicator) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : MmPriorityIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MmPriorityIndicator

/-- Liquidity Indicator: one byte code -/
def LiquidityIndicator.codes : List UInt8 :=
  [0x41, 0x52, 0x20]

inductive LiquidityIndicator where
  | add -- Add
  | remove -- Remove
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ LiquidityIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LiquidityIndicator

def toByte : LiquidityIndicator → UInt8
  | .add => 0x41
  | .remove => 0x52
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LiquidityIndicator :=
  if byte = 0x41 then .add
  else if byte = 0x52 then .remove
  else .notApplicable

def ofByte (byte : UInt8) : LiquidityIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LiquidityIndicator) : ofByte value.toByte = value := by
  cases value with
  | add => decide
  | remove => decide
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

/-- Liquidity Timer Role: one byte code -/
def LiquidityTimerRole.codes : List UInt8 :=
  [0x49, 0x4A, 0x54, 0x42, 0x41, 0x52, 0x20]

inductive LiquidityTimerRole where
  | initiator -- Initiator
  | joiner -- Joiner
  | receivedBeforeOnSameSide -- Received Before On Same Side
  | receivedOnOppositeSideBefore -- Received On Opposite Side Before
  | receivedOnOppositeSideAfter -- Received On Opposite Side After
  | response -- Response
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ LiquidityTimerRole.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LiquidityTimerRole

def toByte : LiquidityTimerRole → UInt8
  | .initiator => 0x49
  | .joiner => 0x4A
  | .receivedBeforeOnSameSide => 0x54
  | .receivedOnOppositeSideBefore => 0x42
  | .receivedOnOppositeSideAfter => 0x41
  | .response => 0x52
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LiquidityTimerRole :=
  if byte = 0x49 then .initiator
  else if byte = 0x4A then .joiner
  else if byte = 0x54 then .receivedBeforeOnSameSide
  else if byte = 0x42 then .receivedOnOppositeSideBefore
  else if byte = 0x41 then .receivedOnOppositeSideAfter
  else if byte = 0x52 then .response
  else .notApplicable

def ofByte (byte : UInt8) : LiquidityTimerRole :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LiquidityTimerRole) : ofByte value.toByte = value := by
  cases value with
  | initiator => decide
  | joiner => decide
  | receivedBeforeOnSameSide => decide
  | receivedOnOppositeSideBefore => decide
  | receivedOnOppositeSideAfter => decide
  | response => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LiquidityTimerRole) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LiquidityTimerRole × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LiquidityTimerRole) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : LiquidityTimerRole) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : LiquidityTimerRole) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LiquidityTimerRole

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
  [0x43, 0x4E, 0x46, 0x42, 0x4D, 0x41]

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
  | .memberMarketMaker => 0x4D
  | .awayExchangeMarketMaker => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Origin :=
  if byte = 0x43 then .priorityCustomer
  else if byte = 0x4E then .nonPriorityCustomer
  else if byte = 0x46 then .firm
  else if byte = 0x42 then .brokerDealer
  else if byte = 0x4D then .memberMarketMaker
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
  [0x43, 0x4E, 0x46, 0x42, 0x4D, 0x41]

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
  | .memberMarketMaker => 0x4D
  | .awayExchangeMarketMaker => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ContraOrigin :=
  if byte = 0x43 then .priorityCustomer
  else if byte = 0x4E then .nonPriorityCustomer
  else if byte = 0x46 then .firm
  else if byte = 0x42 then .brokerDealer
  else if byte = 0x4D then .memberMarketMaker
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

/-- Trade Message: 310 bytes -/
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
  eventId : BitVec 32
  reserved16 : Alpha 16
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
  miaxBboPostingIncrementIndicator : MiaxBboPostingIncrementIndicator
  executionExchange : ExecutionExchange
  routedOrderQuantity : BitVec 32
  marketMakerRole : MarketMakerRole
  tradedWithDirectedMm : TradedWithDirectedMm
  marketState : MarketState
  auctionType : AuctionType
  directedStatus : DirectedStatus
  secondReserved16 : Alpha 16
  executingMpid : Alpha 4
  orderDate : BitVec 32
  fixOrderId : Alpha 30
  clientMessageId : BitVec 32
  bulkQuoteIndex : BitVec 8
  openCloseIndicator : OpenCloseIndicator
  liquidityType : LiquidityType
  mmPriorityIndicator : MmPriorityIndicator
  liquidityIndicator : LiquidityIndicator
  liquidityTimerRole : LiquidityTimerRole
  thirdReserved16 : Alpha 16
  mpid : Alpha 4
  memberType : MemberType
  origin : Origin
  clearingNumber : BitVec 32
  cmta : BitVec 32
  multiAccount : Alpha 5
  accountId : Alpha 10
  supplementaryId : Alpha 13
  fourthReserved16 : Alpha 16
  contraMpid : Alpha 4
  contraMemberType : ContraMemberType
  contraOrigin : ContraOrigin
  contraClearingNumber : BitVec 32
  contraCmta : BitVec 32
  fifthReserved16 : Alpha 16
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
    ++ (encodeUIntLE 4 message.eventId
    ++ (Alpha.encode message.reserved16
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
    ++ (MiaxBboPostingIncrementIndicator.encode message.miaxBboPostingIncrementIndicator
    ++ (ExecutionExchange.encode message.executionExchange
    ++ (encodeUIntLE 4 message.routedOrderQuantity
    ++ (MarketMakerRole.encode message.marketMakerRole
    ++ (TradedWithDirectedMm.encode message.tradedWithDirectedMm
    ++ (MarketState.encode message.marketState
    ++ (AuctionType.encode message.auctionType
    ++ (DirectedStatus.encode message.directedStatus
    ++ (Alpha.encode message.secondReserved16
    ++ (Alpha.encode message.executingMpid
    ++ (encodeUIntLE 4 message.orderDate
    ++ (Alpha.encode message.fixOrderId
    ++ (encodeUIntLE 4 message.clientMessageId
    ++ (encodeUInt 1 message.bulkQuoteIndex
    ++ (OpenCloseIndicator.encode message.openCloseIndicator
    ++ (LiquidityType.encode message.liquidityType
    ++ (MmPriorityIndicator.encode message.mmPriorityIndicator
    ++ (LiquidityIndicator.encode message.liquidityIndicator
    ++ (LiquidityTimerRole.encode message.liquidityTimerRole
    ++ (Alpha.encode message.thirdReserved16
    ++ (Alpha.encode message.mpid
    ++ (MemberType.encode message.memberType
    ++ (Origin.encode message.origin
    ++ (encodeUIntLE 4 message.clearingNumber
    ++ (encodeUIntLE 4 message.cmta
    ++ (Alpha.encode message.multiAccount
    ++ (Alpha.encode message.accountId
    ++ (Alpha.encode message.supplementaryId
    ++ (Alpha.encode message.fourthReserved16
    ++ (Alpha.encode message.contraMpid
    ++ (ContraMemberType.encode message.contraMemberType
    ++ (ContraOrigin.encode message.contraOrigin
    ++ (encodeUIntLE 4 message.contraClearingNumber
    ++ (encodeUIntLE 4 message.contraCmta
    ++ (Alpha.encode message.fifthReserved16)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

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
  let (eventId, bytes) ← decodeUIntLE 4 bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
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
  let (miaxBboPostingIncrementIndicator, bytes) ← MiaxBboPostingIncrementIndicator.decode bytes
  let (executionExchange, bytes) ← ExecutionExchange.decode bytes
  let (routedOrderQuantity, bytes) ← decodeUIntLE 4 bytes
  let (marketMakerRole, bytes) ← MarketMakerRole.decode bytes
  let (tradedWithDirectedMm, bytes) ← TradedWithDirectedMm.decode bytes
  let (marketState, bytes) ← MarketState.decode bytes
  let (auctionType, bytes) ← AuctionType.decode bytes
  let (directedStatus, bytes) ← DirectedStatus.decode bytes
  let (secondReserved16, bytes) ← Alpha.decode 16 bytes
  let (executingMpid, bytes) ← Alpha.decode 4 bytes
  let (orderDate, bytes) ← decodeUIntLE 4 bytes
  let (fixOrderId, bytes) ← Alpha.decode 30 bytes
  let (clientMessageId, bytes) ← decodeUIntLE 4 bytes
  let (bulkQuoteIndex, bytes) ← decodeUInt 1 bytes
  let (openCloseIndicator, bytes) ← OpenCloseIndicator.decode bytes
  let (liquidityType, bytes) ← LiquidityType.decode bytes
  let (mmPriorityIndicator, bytes) ← MmPriorityIndicator.decode bytes
  let (liquidityIndicator, bytes) ← LiquidityIndicator.decode bytes
  let (liquidityTimerRole, bytes) ← LiquidityTimerRole.decode bytes
  let (thirdReserved16, bytes) ← Alpha.decode 16 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (memberType, bytes) ← MemberType.decode bytes
  let (origin, bytes) ← Origin.decode bytes
  let (clearingNumber, bytes) ← decodeUIntLE 4 bytes
  let (cmta, bytes) ← decodeUIntLE 4 bytes
  let (multiAccount, bytes) ← Alpha.decode 5 bytes
  let (accountId, bytes) ← Alpha.decode 10 bytes
  let (supplementaryId, bytes) ← Alpha.decode 13 bytes
  let (fourthReserved16, bytes) ← Alpha.decode 16 bytes
  let (contraMpid, bytes) ← Alpha.decode 4 bytes
  let (contraMemberType, bytes) ← ContraMemberType.decode bytes
  let (contraOrigin, bytes) ← ContraOrigin.decode bytes
  let (contraClearingNumber, bytes) ← decodeUIntLE 4 bytes
  let (contraCmta, bytes) ← decodeUIntLE 4 bytes
  let (fifthReserved16, bytes) ← Alpha.decode 16 bytes
  pure ({ processingTime, tradeTime, tradeAsOfDate, tradeAction, tradeType, tradeId, executionId, correctionNumber, transactionId, referenceTradeTime, referenceTradeId, referenceCorrectionNumber, correctionType, eventId, reserved16, productId, underlyingSymbol, underlyingType, securitySymbol, expirationDate, strikePrice, callOrPut, reserved8, side, price, size, tradeCondition, secondReserved8, classFeeType, miaxBboPostingIncrementIndicator, executionExchange, routedOrderQuantity, marketMakerRole, tradedWithDirectedMm, marketState, auctionType, directedStatus, secondReserved16, executingMpid, orderDate, fixOrderId, clientMessageId, bulkQuoteIndex, openCloseIndicator, liquidityType, mmPriorityIndicator, liquidityIndicator, liquidityTimerRole, thirdReserved16, mpid, memberType, origin, clearingNumber, cmta, multiAccount, accountId, supplementaryId, fourthReserved16, contraMpid, contraMemberType, contraOrigin, contraClearingNumber, contraCmta, fifthReserved16 }, bytes)

@[simp] theorem encode_length (message : TradeMessage) : (encode message).length = 310 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, TradeAction.encode_length, TradeType.encode_length, encodeUInt_length, CorrectionType.encode_length, Alpha.encode_length, UnderlyingType.encode_length, CallOrPut.encode_length, Side.encode_length, TradeCondition.encode_length, ClassFeeType.encode_length, MiaxBboPostingIncrementIndicator.encode_length, ExecutionExchange.encode_length, MarketMakerRole.encode_length, TradedWithDirectedMm.encode_length, MarketState.encode_length, AuctionType.encode_length, DirectedStatus.encode_length, OpenCloseIndicator.encode_length, LiquidityType.encode_length, MmPriorityIndicator.encode_length, LiquidityIndicator.encode_length, LiquidityTimerRole.encode_length, MemberType.encode_length, Origin.encode_length, ContraMemberType.encode_length, ContraOrigin.encode_length]

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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [List.append_assoc, MiaxBboPostingIncrementIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExecutionExchange.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, MarketMakerRole.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradedWithDirectedMm.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MarketState.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AuctionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DirectedStatus.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OpenCloseIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LiquidityType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MmPriorityIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LiquidityIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LiquidityTimerRole.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeMessage

/-- Any Sequenced Message, selected by Sequenced Message Type -/
inductive SequencedMessage where
  | systemState (message : SystemState) -- "S" 0x53
  | tradeMessage (message : TradeMessage) -- "T" 0x54
  deriving DecidableEq, Repr

namespace SequencedMessage

/-- The Sequenced Message Type each message is sent under -/
def tag : SequencedMessage → BitVec 8
  | .systemState _ => 83
  | .tradeMessage _ => 84

def encode : SequencedMessage → List UInt8
  | .systemState message => SystemState.encode message
  | .tradeMessage message => TradeMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : SequencedMessage) : (encode message).length ≤ 310 := by
  cases message with
  | systemState inner =>
    simp only [encode, SystemState.encode_length]
    omega
  | tradeMessage inner =>
    simp only [encode, TradeMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (SequencedMessage × List UInt8) :=
  if tag = 83 then (SystemState.decode bytes).map fun (message, rest) => (.systemState message, rest)
  else if tag = 84 then (TradeMessage.decode bytes).map fun (message, rest) => (.tradeMessage message, rest)
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
theorem encode_length_le (message : SequencedDataPacket) : (encode message).length ≤ 319 := by
  unfold encode
  cases message.sequencedMessage with
  | systemState inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, SystemState.encode_length]
    omega
  | tradeMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, TradeMessage.encode_length]
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

/-- Unsequenced Data Packet: 1 bytes -/
structure UnsequencedDataPacket where
  unsequencedMessageType : Alpha 1
  deriving DecidableEq, Repr

namespace UnsequencedDataPacket

def encode (message : UnsequencedDataPacket) : List UInt8 :=
  Alpha.encode message.unsequencedMessageType

def decode (bytes : List UInt8) : Option (UnsequencedDataPacket × List UInt8) := do
  let (unsequencedMessageType, bytes) ← Alpha.decode 1 bytes
  pure ({ unsequencedMessageType }, bytes)

@[simp] theorem encode_length (message : UnsequencedDataPacket) : (encode message).length = 1 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : UnsequencedDataPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UnsequencedDataPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
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
  logoutText : Capped 65215
  deriving DecidableEq, Repr

namespace LogoutRequest

def encode (message : LogoutRequest) : List UInt8 :=
  LogoutReason.encode message.logoutReason
    ++ (message.logoutText.val)

def decode (bytes : List UInt8) : Option LogoutRequest := do
  let (logoutReason, bytes) ← LogoutReason.decode bytes
  let logoutText_ := bytes
  if fits_logoutText : logoutText_.length ≤ 65215 then
    pure { logoutReason, logoutText := ⟨logoutText_, fits_logoutText⟩ }
  else none

theorem encode_length_pos (message : LogoutRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [LogoutReason.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : LogoutRequest) : (encode message).length ≤ 65216 := by
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
  logoutText : Capped 65215
  deriving DecidableEq, Repr

namespace GoodbyePacket

def encode (message : GoodbyePacket) : List UInt8 :=
  GoodbyeReason.encode message.goodbyeReason
    ++ (message.logoutText.val)

def decode (bytes : List UInt8) : Option GoodbyePacket := do
  let (goodbyeReason, bytes) ← GoodbyeReason.decode bytes
  let logoutText_ := bytes
  if fits_logoutText : logoutText_.length ≤ 65215 then
    pure { goodbyeReason, logoutText := ⟨logoutText_, fits_logoutText⟩ }
  else none

theorem encode_length_pos (message : GoodbyePacket) : (encode message).length > 0 := by
  unfold encode
  simp only [GoodbyeReason.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : GoodbyePacket) : (encode message).length ≤ 65216 := by
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
  testText : Capped 65215
  deriving DecidableEq, Repr

namespace TestPacket

def encode (message : TestPacket) : List UInt8 :=
  message.testText.val

def decode (bytes : List UInt8) : Option TestPacket := do
  let testText_ := bytes
  if fits_testText : testText_.length ≤ 65215 then
    pure { testText := ⟨testText_, fits_testText⟩ }
  else none

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TestPacket) : (encode message).length ≤ 65215 := by
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
theorem encode_length_le (message : SesmPayload) : (encode message).length ≤ 65216 := by
  cases message with
  | sequencedDataPacket inner =>
    have bound_inner := SequencedDataPacket.encode_length_le inner
    simp only [encode]
    omega
  | unsequencedDataPacket inner =>
    simp only [encode, UnsequencedDataPacket.encode_length]
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
    simp only [SesmPayload.encode, List.length_append, encodeUInt_length, UnsequencedDataPacket.encode_length]
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

end Omi.MiaxMiaxoptionsClearingtradedropCtdV13A
