import Wire

/-!
# Beijing Stock Exchange Bjse Order Entry v1.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.

License: MIT No Attribution
-/

namespace Omi.BjseBjsesecuritiesOrderentryBjsebinaryV11

/-- Side: one byte code -/
def Side.codes : List UInt8 :=
  [0x31, 0x32, 0x47, 0x46, 0x44, 0x45]

inductive Side where
  | buy -- Buy
  | sell -- Sell
  | borrow -- Borrow
  | lend -- Lend
  | subscribe -- Subscribe
  | redeem -- Redeem
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .buy => 0x31
  | .sell => 0x32
  | .borrow => 0x47
  | .lend => 0x46
  | .subscribe => 0x44
  | .redeem => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x31 then .buy
  else if byte = 0x32 then .sell
  else if byte = 0x47 then .borrow
  else if byte = 0x46 then .lend
  else if byte = 0x44 then .subscribe
  else .redeem

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | borrow => decide
  | lend => decide
  | subscribe => decide
  | redeem => decide
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

/-- Ord Type: one byte code -/
def OrdType.codes : List UInt8 :=
  [0x31, 0x32, 0x55]

inductive OrdType where
  | market -- Market
  | limit -- Limit
  | bestOwnSide -- Best Own Side
  | unlisted (byte : { byte : UInt8 // byte ∉ OrdType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrdType

def toByte : OrdType → UInt8
  | .market => 0x31
  | .limit => 0x32
  | .bestOwnSide => 0x55
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrdType :=
  if byte = 0x31 then .market
  else if byte = 0x32 then .limit
  else .bestOwnSide

def ofByte (byte : UInt8) : OrdType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrdType) : ofByte value.toByte = value := by
  cases value with
  | market => decide
  | limit => decide
  | bestOwnSide => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrdType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrdType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrdType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OrdType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OrdType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrdType

/-- Time In Force: one byte code -/
def TimeInForce.codes : List UInt8 :=
  [0x30, 0x33]

inductive TimeInForce where
  | day -- Day
  | immediateOrCancel -- Immediate Or Cancel
  | unlisted (byte : { byte : UInt8 // byte ∉ TimeInForce.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TimeInForce

def toByte : TimeInForce → UInt8
  | .day => 0x30
  | .immediateOrCancel => 0x33
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TimeInForce :=
  if byte = 0x30 then .day
  else .immediateOrCancel

def ofByte (byte : UInt8) : TimeInForce :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TimeInForce) : ofByte value.toByte = value := by
  cases value with
  | day => decide
  | immediateOrCancel => decide
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

/-- Cash Margin: one byte code -/
def CashMargin.codes : List UInt8 :=
  [0x31, 0x32, 0x33]

inductive CashMargin where
  | cash -- Cash
  | open_ -- Open
  | close -- Close
  | unlisted (byte : { byte : UInt8 // byte ∉ CashMargin.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CashMargin

def toByte : CashMargin → UInt8
  | .cash => 0x31
  | .open_ => 0x32
  | .close => 0x33
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CashMargin :=
  if byte = 0x31 then .cash
  else if byte = 0x32 then .open_
  else .close

def ofByte (byte : UInt8) : CashMargin :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CashMargin) : ofByte value.toByte = value := by
  cases value with
  | cash => decide
  | open_ => decide
  | close => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CashMargin) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CashMargin × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CashMargin) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CashMargin) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CashMargin) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CashMargin

/-- Settl Type: one byte code -/
def SettlType.codes : List UInt8 :=
  [0x31, 0x32]

inductive SettlType where
  | grossTradeByTrade -- Gross Trade By Trade
  | multilateralNet -- Multilateral Net
  | unlisted (byte : { byte : UInt8 // byte ∉ SettlType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SettlType

def toByte : SettlType → UInt8
  | .grossTradeByTrade => 0x31
  | .multilateralNet => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SettlType :=
  if byte = 0x31 then .grossTradeByTrade
  else .multilateralNet

def ofByte (byte : UInt8) : SettlType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SettlType) : ofByte value.toByte = value := by
  cases value with
  | grossTradeByTrade => decide
  | multilateralNet => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SettlType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SettlType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SettlType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SettlType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SettlType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SettlType

/-- Settl Period: one byte code -/
def SettlPeriod.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33]

inductive SettlPeriod where
  | tPlus0 -- T Plus 0
  | tPlus1 -- T Plus 1
  | tPlus2 -- T Plus 2
  | tPlus3 -- T Plus 3
  | unlisted (byte : { byte : UInt8 // byte ∉ SettlPeriod.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SettlPeriod

def toByte : SettlPeriod → UInt8
  | .tPlus0 => 0x30
  | .tPlus1 => 0x31
  | .tPlus2 => 0x32
  | .tPlus3 => 0x33
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SettlPeriod :=
  if byte = 0x30 then .tPlus0
  else if byte = 0x31 then .tPlus1
  else if byte = 0x32 then .tPlus2
  else .tPlus3

def ofByte (byte : UInt8) : SettlPeriod :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SettlPeriod) : ofByte value.toByte = value := by
  cases value with
  | tPlus0 => decide
  | tPlus1 => decide
  | tPlus2 => decide
  | tPlus3 => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SettlPeriod) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SettlPeriod × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SettlPeriod) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SettlPeriod) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SettlPeriod) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SettlPeriod

/-- Ord Status: one byte code -/
def OrdStatus.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x34, 0x38]

inductive OrdStatus where
  | new -- New
  | partiallyFilled -- Partially Filled
  | filled -- Filled
  | cancelled -- Cancelled
  | reject -- Reject
  | unlisted (byte : { byte : UInt8 // byte ∉ OrdStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrdStatus

def toByte : OrdStatus → UInt8
  | .new => 0x30
  | .partiallyFilled => 0x31
  | .filled => 0x32
  | .cancelled => 0x34
  | .reject => 0x38
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrdStatus :=
  if byte = 0x30 then .new
  else if byte = 0x31 then .partiallyFilled
  else if byte = 0x32 then .filled
  else if byte = 0x34 then .cancelled
  else .reject

def ofByte (byte : UInt8) : OrdStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrdStatus) : ofByte value.toByte = value := by
  cases value with
  | new => decide
  | partiallyFilled => decide
  | filled => decide
  | cancelled => decide
  | reject => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrdStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrdStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrdStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OrdStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OrdStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrdStatus

/-- Exec Type: one byte code -/
def ExecType.codes : List UInt8 :=
  [0x30, 0x34, 0x38, 0x46]

inductive ExecType where
  | new -- New
  | cancelled -- Cancelled
  | reject -- Reject
  | trade -- Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ ExecType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExecType

def toByte : ExecType → UInt8
  | .new => 0x30
  | .cancelled => 0x34
  | .reject => 0x38
  | .trade => 0x46
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExecType :=
  if byte = 0x30 then .new
  else if byte = 0x34 then .cancelled
  else if byte = 0x38 then .reject
  else .trade

def ofByte (byte : UInt8) : ExecType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExecType) : ofByte value.toByte = value := by
  cases value with
  | new => decide
  | cancelled => decide
  | reject => decide
  | trade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ExecType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ExecType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ExecType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ExecType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ExecType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ExecType

/-- Trade Handling Instr: one byte code -/
def TradeHandlingInstr.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33, 0x35]

inductive TradeHandlingInstr where
  | tradeConfirm -- Trade Confirm
  | twoPartyReport -- Two Party Report
  | onePartyReportForMatching -- One Party Report For Matching
  | onePartyReportForPassThrough -- One Party Report For Pass Through
  | twoPartyReportForClaim -- Two Party Report For Claim
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeHandlingInstr.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeHandlingInstr

def toByte : TradeHandlingInstr → UInt8
  | .tradeConfirm => 0x30
  | .twoPartyReport => 0x31
  | .onePartyReportForMatching => 0x32
  | .onePartyReportForPassThrough => 0x33
  | .twoPartyReportForClaim => 0x35
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeHandlingInstr :=
  if byte = 0x30 then .tradeConfirm
  else if byte = 0x31 then .twoPartyReport
  else if byte = 0x32 then .onePartyReportForMatching
  else if byte = 0x33 then .onePartyReportForPassThrough
  else .twoPartyReportForClaim

def ofByte (byte : UInt8) : TradeHandlingInstr :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeHandlingInstr) : ofByte value.toByte = value := by
  cases value with
  | tradeConfirm => decide
  | twoPartyReport => decide
  | onePartyReportForMatching => decide
  | onePartyReportForPassThrough => decide
  | twoPartyReportForClaim => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeHandlingInstr) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeHandlingInstr × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeHandlingInstr) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TradeHandlingInstr) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TradeHandlingInstr) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeHandlingInstr

/-- Logon Message: 92 bytes -/
structure LogonMessage where
  senderCompId : Alpha 20
  targetCompId : Alpha 20
  heartBtInt : BitVec 32
  password : Alpha 16
  defaultApplVerId : Alpha 32
  deriving DecidableEq, Repr

namespace LogonMessage

def encode (message : LogonMessage) : List UInt8 :=
  Alpha.encode message.senderCompId
    ++ (Alpha.encode message.targetCompId
    ++ (encodeUInt 4 message.heartBtInt
    ++ (Alpha.encode message.password
    ++ (Alpha.encode message.defaultApplVerId))))

def decode (bytes : List UInt8) : Option (LogonMessage × List UInt8) := do
  let (senderCompId, bytes) ← Alpha.decode 20 bytes
  let (targetCompId, bytes) ← Alpha.decode 20 bytes
  let (heartBtInt, bytes) ← decodeUInt 4 bytes
  let (password, bytes) ← Alpha.decode 16 bytes
  let (defaultApplVerId, bytes) ← Alpha.decode 32 bytes
  pure ({ senderCompId, targetCompId, heartBtInt, password, defaultApplVerId }, bytes)

@[simp] theorem encode_length (message : LogonMessage) : (encode message).length = 92 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : LogonMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogonMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LogonMessage

/-- Logout Message: 204 bytes -/
structure LogoutMessage where
  sessionStatus : BitVec 32
  text : Alpha 200
  deriving DecidableEq, Repr

namespace LogoutMessage

def encode (message : LogoutMessage) : List UInt8 :=
  encodeUInt 4 message.sessionStatus
    ++ (Alpha.encode message.text)

def decode (bytes : List UInt8) : Option (LogoutMessage × List UInt8) := do
  let (sessionStatus, bytes) ← decodeUInt 4 bytes
  let (text, bytes) ← Alpha.decode 200 bytes
  pure ({ sessionStatus, text }, bytes)

@[simp] theorem encode_length (message : LogoutMessage) : (encode message).length = 204 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : LogoutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogoutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LogoutMessage

/-- Heartbeat Message: 0 bytes -/
structure HeartbeatMessage where
  deriving DecidableEq, Repr

namespace HeartbeatMessage

def encode (_ : HeartbeatMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (HeartbeatMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : HeartbeatMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : HeartbeatMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end HeartbeatMessage

/-- Business Reject Message: 103 bytes -/
structure BusinessRejectMessage where
  applId : Alpha 3
  transactTime : BitVec 64
  submittingPbuid : Alpha 6
  securityId : Alpha 8
  securityIdSource : Alpha 4
  refSeqNum : BitVec 64
  refMsgType : BitVec 32
  businessRejectRefId : Alpha 10
  businessRejectReason : BitVec 16
  businessRejectText : Alpha 50
  deriving DecidableEq, Repr

namespace BusinessRejectMessage

def encode (message : BusinessRejectMessage) : List UInt8 :=
  Alpha.encode message.applId
    ++ (encodeUInt 8 message.transactTime
    ++ (Alpha.encode message.submittingPbuid
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 8 message.refSeqNum
    ++ (encodeUInt 4 message.refMsgType
    ++ (Alpha.encode message.businessRejectRefId
    ++ (encodeUInt 2 message.businessRejectReason
    ++ (Alpha.encode message.businessRejectText)))))))))

def decode (bytes : List UInt8) : Option (BusinessRejectMessage × List UInt8) := do
  let (applId, bytes) ← Alpha.decode 3 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  let (submittingPbuid, bytes) ← Alpha.decode 6 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (refSeqNum, bytes) ← decodeUInt 8 bytes
  let (refMsgType, bytes) ← decodeUInt 4 bytes
  let (businessRejectRefId, bytes) ← Alpha.decode 10 bytes
  let (businessRejectReason, bytes) ← decodeUInt 2 bytes
  let (businessRejectText, bytes) ← Alpha.decode 50 bytes
  pure ({ applId, transactTime, submittingPbuid, securityId, securityIdSource, refSeqNum, refMsgType, businessRejectRefId, businessRejectReason, businessRejectText }, bytes)

@[simp] theorem encode_length (message : BusinessRejectMessage) : (encode message).length = 103 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : BusinessRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BusinessRejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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

end BusinessRejectMessage

/-- Partition Reports: 12 bytes -/
structure PartitionReports where
  partitionNo : BitVec 32
  reportIndex : BitVec 64
  deriving DecidableEq, Repr

namespace PartitionReports

def encode (message : PartitionReports) : List UInt8 :=
  encodeUInt 4 message.partitionNo
    ++ (encodeUInt 8 message.reportIndex)

def decode (bytes : List UInt8) : Option (PartitionReports × List UInt8) := do
  let (partitionNo, bytes) ← decodeUInt 4 bytes
  let (reportIndex, bytes) ← decodeUInt 8 bytes
  pure ({ partitionNo, reportIndex }, bytes)

@[simp] theorem encode_length (message : PartitionReports) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : PartitionReports) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PartitionReports) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end PartitionReports

/-- Report Synchronization Message -/
structure ReportSynchronizationMessage where
  partitionReports : Bounded 4 PartitionReports
  deriving DecidableEq, Repr

namespace ReportSynchronizationMessage

def encode (message : ReportSynchronizationMessage) : List UInt8 :=
  encodeUInt 4 (BitVec.ofNat (8 * 4) message.partitionReports.val.length)
    ++ (encodeMany PartitionReports.encode message.partitionReports.val)

def decode (bytes : List UInt8) : Option (ReportSynchronizationMessage × List UInt8) := do
  let (noPartitions, bytes) ← decodeUInt 4 bytes
  let (partitionReports_, bytes) ← decodeMany PartitionReports.decode noPartitions.toNat bytes
  if fits_partitionReports : partitionReports_.length < 256 ^ 4 then
    pure ({ partitionReports := ⟨partitionReports_, fits_partitionReports⟩ }, bytes)
  else none

theorem encode_length_pos (message : ReportSynchronizationMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ReportSynchronizationMessage) : (encode message).length ≤ 51539607544 := by
  have bound_partitionReports := message.partitionReports.length_lt
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeMany_length_const PartitionReports.encode 12 PartitionReports.encode_length]
  omega

@[simp] theorem decode_encode (message : ReportSynchronizationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 4 PartitionReports.encode PartitionReports.decode PartitionReports.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.partitionReports.length_lt]
  rfl

end ReportSynchronizationMessage

/-- Platform State Info Message: 4 bytes -/
structure PlatformStateInfoMessage where
  platformId : BitVec 16
  platformState : BitVec 16
  deriving DecidableEq, Repr

namespace PlatformStateInfoMessage

def encode (message : PlatformStateInfoMessage) : List UInt8 :=
  encodeUInt 2 message.platformId
    ++ (encodeUInt 2 message.platformState)

def decode (bytes : List UInt8) : Option (PlatformStateInfoMessage × List UInt8) := do
  let (platformId, bytes) ← decodeUInt 2 bytes
  let (platformState, bytes) ← decodeUInt 2 bytes
  pure ({ platformId, platformState }, bytes)

@[simp] theorem encode_length (message : PlatformStateInfoMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : PlatformStateInfoMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PlatformStateInfoMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end PlatformStateInfoMessage

/-- Report Finished Message: 14 bytes -/
structure ReportFinishedMessage where
  partitionNo : BitVec 32
  reportIndex : BitVec 64
  platformId : BitVec 16
  deriving DecidableEq, Repr

namespace ReportFinishedMessage

def encode (message : ReportFinishedMessage) : List UInt8 :=
  encodeUInt 4 message.partitionNo
    ++ (encodeUInt 8 message.reportIndex
    ++ (encodeUInt 2 message.platformId))

def decode (bytes : List UInt8) : Option (ReportFinishedMessage × List UInt8) := do
  let (partitionNo, bytes) ← decodeUInt 4 bytes
  let (reportIndex, bytes) ← decodeUInt 8 bytes
  let (platformId, bytes) ← decodeUInt 2 bytes
  pure ({ partitionNo, reportIndex, platformId }, bytes)

@[simp] theorem encode_length (message : ReportFinishedMessage) : (encode message).length = 14 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : ReportFinishedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReportFinishedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ReportFinishedMessage

/-- Partitions: 4 bytes -/
structure Partitions where
  partitionNo : BitVec 32
  deriving DecidableEq, Repr

namespace Partitions

def encode (message : Partitions) : List UInt8 :=
  encodeUInt 4 message.partitionNo

def decode (bytes : List UInt8) : Option (Partitions × List UInt8) := do
  let (partitionNo, bytes) ← decodeUInt 4 bytes
  pure ({ partitionNo }, bytes)

@[simp] theorem encode_length (message : Partitions) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : Partitions) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Partitions) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end Partitions

/-- Platform Info Message -/
structure PlatformInfoMessage where
  platformId : BitVec 16
  partitions : Bounded 4 Partitions
  deriving DecidableEq, Repr

namespace PlatformInfoMessage

def encode (message : PlatformInfoMessage) : List UInt8 :=
  encodeUInt 2 message.platformId
    ++ (encodeUInt 4 (BitVec.ofNat (8 * 4) message.partitions.val.length)
    ++ (encodeMany Partitions.encode message.partitions.val))

def decode (bytes : List UInt8) : Option (PlatformInfoMessage × List UInt8) := do
  let (platformId, bytes) ← decodeUInt 2 bytes
  let (noPartitions, bytes) ← decodeUInt 4 bytes
  let (partitions_, bytes) ← decodeMany Partitions.decode noPartitions.toNat bytes
  if fits_partitions : partitions_.length < 256 ^ 4 then
    pure ({ platformId, partitions := ⟨partitions_, fits_partitions⟩ }, bytes)
  else none

theorem encode_length_pos (message : PlatformInfoMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : PlatformInfoMessage) : (encode message).length ≤ 17179869186 := by
  have bound_partitions := message.partitions.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const Partitions.encode 4 Partitions.encode_length]
  omega

@[simp] theorem decode_encode (message : PlatformInfoMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 4 Partitions.encode Partitions.decode Partitions.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.partitions.length_lt]
  rfl

end PlatformInfoMessage

/-- Trading Session Status Message: 42 bytes -/
structure TradingSessionStatusMessage where
  marketId : Alpha 8
  marketSegmentId : Alpha 8
  tradingSessionId : Alpha 4
  tradingSessionSubId : Alpha 4
  tradSesStatus : BitVec 16
  tradSesStartTime : BitVec 64
  tradSesEndTime : BitVec 64
  deriving DecidableEq, Repr

namespace TradingSessionStatusMessage

def encode (message : TradingSessionStatusMessage) : List UInt8 :=
  Alpha.encode message.marketId
    ++ (Alpha.encode message.marketSegmentId
    ++ (Alpha.encode message.tradingSessionId
    ++ (Alpha.encode message.tradingSessionSubId
    ++ (encodeUInt 2 message.tradSesStatus
    ++ (encodeUInt 8 message.tradSesStartTime
    ++ (encodeUInt 8 message.tradSesEndTime))))))

def decode (bytes : List UInt8) : Option (TradingSessionStatusMessage × List UInt8) := do
  let (marketId, bytes) ← Alpha.decode 8 bytes
  let (marketSegmentId, bytes) ← Alpha.decode 8 bytes
  let (tradingSessionId, bytes) ← Alpha.decode 4 bytes
  let (tradingSessionSubId, bytes) ← Alpha.decode 4 bytes
  let (tradSesStatus, bytes) ← decodeUInt 2 bytes
  let (tradSesStartTime, bytes) ← decodeUInt 8 bytes
  let (tradSesEndTime, bytes) ← decodeUInt 8 bytes
  pure ({ marketId, marketSegmentId, tradingSessionId, tradingSessionSubId, tradSesStatus, tradSesStartTime, tradSesEndTime }, bytes)

@[simp] theorem encode_length (message : TradingSessionStatusMessage) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TradingSessionStatusMessage

/-- Bond Spot Matching New Order Message: 131 bytes -/
structure BondSpotMatchingNewOrderMessage where
  applId : Alpha 3
  submittingPbuid : Alpha 6
  securityId : Alpha 8
  securityIdSource : Alpha 4
  ownerType : BitVec 16
  clearingFirm : Alpha 2
  transactTime : BitVec 64
  userInfo : Alpha 32
  clOrdId : Alpha 10
  accountId : Alpha 10
  branchId : Alpha 2
  orderRestrictions : Alpha 4
  side : Side
  ordType : OrdType
  orderQty : BitVec 64
  price : BitVec 64
  stopPx : BitVec 64
  minQty : BitVec 64
  maxPriceLevels : BitVec 16
  timeInForce : TimeInForce
  cashMargin : CashMargin
  settlType : SettlType
  settlPeriod : SettlPeriod
  deriving DecidableEq, Repr

namespace BondSpotMatchingNewOrderMessage

def encode (message : BondSpotMatchingNewOrderMessage) : List UInt8 :=
  Alpha.encode message.applId
    ++ (Alpha.encode message.submittingPbuid
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 2 message.ownerType
    ++ (Alpha.encode message.clearingFirm
    ++ (encodeUInt 8 message.transactTime
    ++ (Alpha.encode message.userInfo
    ++ (Alpha.encode message.clOrdId
    ++ (Alpha.encode message.accountId
    ++ (Alpha.encode message.branchId
    ++ (Alpha.encode message.orderRestrictions
    ++ (Side.encode message.side
    ++ (OrdType.encode message.ordType
    ++ (encodeUInt 8 message.orderQty
    ++ (encodeUInt 8 message.price
    ++ (encodeUInt 8 message.stopPx
    ++ (encodeUInt 8 message.minQty
    ++ (encodeUInt 2 message.maxPriceLevels
    ++ (TimeInForce.encode message.timeInForce
    ++ (CashMargin.encode message.cashMargin
    ++ (SettlType.encode message.settlType
    ++ (SettlPeriod.encode message.settlPeriod))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (BondSpotMatchingNewOrderMessage × List UInt8) := do
  let (applId, bytes) ← Alpha.decode 3 bytes
  let (submittingPbuid, bytes) ← Alpha.decode 6 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (ownerType, bytes) ← decodeUInt 2 bytes
  let (clearingFirm, bytes) ← Alpha.decode 2 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  let (userInfo, bytes) ← Alpha.decode 32 bytes
  let (clOrdId, bytes) ← Alpha.decode 10 bytes
  let (accountId, bytes) ← Alpha.decode 10 bytes
  let (branchId, bytes) ← Alpha.decode 2 bytes
  let (orderRestrictions, bytes) ← Alpha.decode 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (ordType, bytes) ← OrdType.decode bytes
  let (orderQty, bytes) ← decodeUInt 8 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (stopPx, bytes) ← decodeUInt 8 bytes
  let (minQty, bytes) ← decodeUInt 8 bytes
  let (maxPriceLevels, bytes) ← decodeUInt 2 bytes
  let (timeInForce, bytes) ← TimeInForce.decode bytes
  let (cashMargin, bytes) ← CashMargin.decode bytes
  let (settlType, bytes) ← SettlType.decode bytes
  let (settlPeriod, bytes) ← SettlPeriod.decode bytes
  pure ({ applId, submittingPbuid, securityId, securityIdSource, ownerType, clearingFirm, transactTime, userInfo, clOrdId, accountId, branchId, orderRestrictions, side, ordType, orderQty, price, stopPx, minQty, maxPriceLevels, timeInForce, cashMargin, settlType, settlPeriod }, bytes)

@[simp] theorem encode_length (message : BondSpotMatchingNewOrderMessage) : (encode message).length = 131 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, Side.encode_length, OrdType.encode_length, TimeInForce.encode_length, CashMargin.encode_length, SettlType.encode_length, SettlPeriod.encode_length]

theorem encode_length_pos (message : BondSpotMatchingNewOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BondSpotMatchingNewOrderMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrdType.decode_encode, some_bind]
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
  rw [List.append_assoc, TimeInForce.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CashMargin.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SettlType.decode_encode, some_bind]
  dsimp only
  rw [SettlPeriod.decode_encode, some_bind]
  rfl

end BondSpotMatchingNewOrderMessage

/-- Centralized Auction New Order Message: 129 bytes -/
structure CentralizedAuctionNewOrderMessage where
  applId : Alpha 3
  submittingPbuid : Alpha 6
  securityId : Alpha 8
  securityIdSource : Alpha 4
  ownerType : BitVec 16
  clearingFirm : Alpha 2
  transactTime : BitVec 64
  userInfo : Alpha 32
  clOrdId : Alpha 10
  accountId : Alpha 10
  branchId : Alpha 2
  orderRestrictions : Alpha 4
  side : Side
  ordType : OrdType
  orderQty : BitVec 64
  price : BitVec 64
  stopPx : BitVec 64
  minQty : BitVec 64
  maxPriceLevels : BitVec 16
  timeInForce : TimeInForce
  cashMargin : CashMargin
  deriving DecidableEq, Repr

namespace CentralizedAuctionNewOrderMessage

def encode (message : CentralizedAuctionNewOrderMessage) : List UInt8 :=
  Alpha.encode message.applId
    ++ (Alpha.encode message.submittingPbuid
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 2 message.ownerType
    ++ (Alpha.encode message.clearingFirm
    ++ (encodeUInt 8 message.transactTime
    ++ (Alpha.encode message.userInfo
    ++ (Alpha.encode message.clOrdId
    ++ (Alpha.encode message.accountId
    ++ (Alpha.encode message.branchId
    ++ (Alpha.encode message.orderRestrictions
    ++ (Side.encode message.side
    ++ (OrdType.encode message.ordType
    ++ (encodeUInt 8 message.orderQty
    ++ (encodeUInt 8 message.price
    ++ (encodeUInt 8 message.stopPx
    ++ (encodeUInt 8 message.minQty
    ++ (encodeUInt 2 message.maxPriceLevels
    ++ (TimeInForce.encode message.timeInForce
    ++ (CashMargin.encode message.cashMargin))))))))))))))))))))

def decode (bytes : List UInt8) : Option (CentralizedAuctionNewOrderMessage × List UInt8) := do
  let (applId, bytes) ← Alpha.decode 3 bytes
  let (submittingPbuid, bytes) ← Alpha.decode 6 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (ownerType, bytes) ← decodeUInt 2 bytes
  let (clearingFirm, bytes) ← Alpha.decode 2 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  let (userInfo, bytes) ← Alpha.decode 32 bytes
  let (clOrdId, bytes) ← Alpha.decode 10 bytes
  let (accountId, bytes) ← Alpha.decode 10 bytes
  let (branchId, bytes) ← Alpha.decode 2 bytes
  let (orderRestrictions, bytes) ← Alpha.decode 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (ordType, bytes) ← OrdType.decode bytes
  let (orderQty, bytes) ← decodeUInt 8 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (stopPx, bytes) ← decodeUInt 8 bytes
  let (minQty, bytes) ← decodeUInt 8 bytes
  let (maxPriceLevels, bytes) ← decodeUInt 2 bytes
  let (timeInForce, bytes) ← TimeInForce.decode bytes
  let (cashMargin, bytes) ← CashMargin.decode bytes
  pure ({ applId, submittingPbuid, securityId, securityIdSource, ownerType, clearingFirm, transactTime, userInfo, clOrdId, accountId, branchId, orderRestrictions, side, ordType, orderQty, price, stopPx, minQty, maxPriceLevels, timeInForce, cashMargin }, bytes)

@[simp] theorem encode_length (message : CentralizedAuctionNewOrderMessage) : (encode message).length = 129 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, Side.encode_length, OrdType.encode_length, TimeInForce.encode_length, CashMargin.encode_length]

theorem encode_length_pos (message : CentralizedAuctionNewOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CentralizedAuctionNewOrderMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrdType.decode_encode, some_bind]
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
  rw [List.append_assoc, TimeInForce.decode_encode, some_bind]
  dsimp only
  rw [CashMargin.decode_encode, some_bind]
  rfl

end CentralizedAuctionNewOrderMessage

/-- Conversion New Order Message: 109 bytes -/
structure ConversionNewOrderMessage where
  applId : Alpha 3
  submittingPbuid : Alpha 6
  securityId : Alpha 8
  securityIdSource : Alpha 4
  ownerType : BitVec 16
  clearingFirm : Alpha 2
  transactTime : BitVec 64
  userInfo : Alpha 32
  clOrdId : Alpha 10
  accountId : Alpha 10
  branchId : Alpha 2
  orderRestrictions : Alpha 4
  side : Side
  ordType : OrdType
  orderQty : BitVec 64
  price : BitVec 64
  deriving DecidableEq, Repr

namespace ConversionNewOrderMessage

def encode (message : ConversionNewOrderMessage) : List UInt8 :=
  Alpha.encode message.applId
    ++ (Alpha.encode message.submittingPbuid
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 2 message.ownerType
    ++ (Alpha.encode message.clearingFirm
    ++ (encodeUInt 8 message.transactTime
    ++ (Alpha.encode message.userInfo
    ++ (Alpha.encode message.clOrdId
    ++ (Alpha.encode message.accountId
    ++ (Alpha.encode message.branchId
    ++ (Alpha.encode message.orderRestrictions
    ++ (Side.encode message.side
    ++ (OrdType.encode message.ordType
    ++ (encodeUInt 8 message.orderQty
    ++ (encodeUInt 8 message.price)))))))))))))))

def decode (bytes : List UInt8) : Option (ConversionNewOrderMessage × List UInt8) := do
  let (applId, bytes) ← Alpha.decode 3 bytes
  let (submittingPbuid, bytes) ← Alpha.decode 6 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (ownerType, bytes) ← decodeUInt 2 bytes
  let (clearingFirm, bytes) ← Alpha.decode 2 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  let (userInfo, bytes) ← Alpha.decode 32 bytes
  let (clOrdId, bytes) ← Alpha.decode 10 bytes
  let (accountId, bytes) ← Alpha.decode 10 bytes
  let (branchId, bytes) ← Alpha.decode 2 bytes
  let (orderRestrictions, bytes) ← Alpha.decode 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (ordType, bytes) ← OrdType.decode bytes
  let (orderQty, bytes) ← decodeUInt 8 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  pure ({ applId, submittingPbuid, securityId, securityIdSource, ownerType, clearingFirm, transactTime, userInfo, clOrdId, accountId, branchId, orderRestrictions, side, ordType, orderQty, price }, bytes)

@[simp] theorem encode_length (message : ConversionNewOrderMessage) : (encode message).length = 109 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, Side.encode_length, OrdType.encode_length]

theorem encode_length_pos (message : ConversionNewOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ConversionNewOrderMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrdType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ConversionNewOrderMessage

/-- Inquiry New Order Message: 109 bytes -/
structure InquiryNewOrderMessage where
  applId : Alpha 3
  submittingPbuid : Alpha 6
  securityId : Alpha 8
  securityIdSource : Alpha 4
  ownerType : BitVec 16
  clearingFirm : Alpha 2
  transactTime : BitVec 64
  userInfo : Alpha 32
  clOrdId : Alpha 10
  accountId : Alpha 10
  branchId : Alpha 2
  orderRestrictions : Alpha 4
  side : Side
  ordType : OrdType
  orderQty : BitVec 64
  price : BitVec 64
  deriving DecidableEq, Repr

namespace InquiryNewOrderMessage

def encode (message : InquiryNewOrderMessage) : List UInt8 :=
  Alpha.encode message.applId
    ++ (Alpha.encode message.submittingPbuid
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 2 message.ownerType
    ++ (Alpha.encode message.clearingFirm
    ++ (encodeUInt 8 message.transactTime
    ++ (Alpha.encode message.userInfo
    ++ (Alpha.encode message.clOrdId
    ++ (Alpha.encode message.accountId
    ++ (Alpha.encode message.branchId
    ++ (Alpha.encode message.orderRestrictions
    ++ (Side.encode message.side
    ++ (OrdType.encode message.ordType
    ++ (encodeUInt 8 message.orderQty
    ++ (encodeUInt 8 message.price)))))))))))))))

def decode (bytes : List UInt8) : Option (InquiryNewOrderMessage × List UInt8) := do
  let (applId, bytes) ← Alpha.decode 3 bytes
  let (submittingPbuid, bytes) ← Alpha.decode 6 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (ownerType, bytes) ← decodeUInt 2 bytes
  let (clearingFirm, bytes) ← Alpha.decode 2 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  let (userInfo, bytes) ← Alpha.decode 32 bytes
  let (clOrdId, bytes) ← Alpha.decode 10 bytes
  let (accountId, bytes) ← Alpha.decode 10 bytes
  let (branchId, bytes) ← Alpha.decode 2 bytes
  let (orderRestrictions, bytes) ← Alpha.decode 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (ordType, bytes) ← OrdType.decode bytes
  let (orderQty, bytes) ← decodeUInt 8 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  pure ({ applId, submittingPbuid, securityId, securityIdSource, ownerType, clearingFirm, transactTime, userInfo, clOrdId, accountId, branchId, orderRestrictions, side, ordType, orderQty, price }, bytes)

@[simp] theorem encode_length (message : InquiryNewOrderMessage) : (encode message).length = 109 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, Side.encode_length, OrdType.encode_length]

theorem encode_length_pos (message : InquiryNewOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InquiryNewOrderMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrdType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end InquiryNewOrderMessage

/-- Subscription New Order Message: 109 bytes -/
structure SubscriptionNewOrderMessage where
  applId : Alpha 3
  submittingPbuid : Alpha 6
  securityId : Alpha 8
  securityIdSource : Alpha 4
  ownerType : BitVec 16
  clearingFirm : Alpha 2
  transactTime : BitVec 64
  userInfo : Alpha 32
  clOrdId : Alpha 10
  accountId : Alpha 10
  branchId : Alpha 2
  orderRestrictions : Alpha 4
  side : Side
  ordType : OrdType
  orderQty : BitVec 64
  price : BitVec 64
  deriving DecidableEq, Repr

namespace SubscriptionNewOrderMessage

def encode (message : SubscriptionNewOrderMessage) : List UInt8 :=
  Alpha.encode message.applId
    ++ (Alpha.encode message.submittingPbuid
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 2 message.ownerType
    ++ (Alpha.encode message.clearingFirm
    ++ (encodeUInt 8 message.transactTime
    ++ (Alpha.encode message.userInfo
    ++ (Alpha.encode message.clOrdId
    ++ (Alpha.encode message.accountId
    ++ (Alpha.encode message.branchId
    ++ (Alpha.encode message.orderRestrictions
    ++ (Side.encode message.side
    ++ (OrdType.encode message.ordType
    ++ (encodeUInt 8 message.orderQty
    ++ (encodeUInt 8 message.price)))))))))))))))

def decode (bytes : List UInt8) : Option (SubscriptionNewOrderMessage × List UInt8) := do
  let (applId, bytes) ← Alpha.decode 3 bytes
  let (submittingPbuid, bytes) ← Alpha.decode 6 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (ownerType, bytes) ← decodeUInt 2 bytes
  let (clearingFirm, bytes) ← Alpha.decode 2 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  let (userInfo, bytes) ← Alpha.decode 32 bytes
  let (clOrdId, bytes) ← Alpha.decode 10 bytes
  let (accountId, bytes) ← Alpha.decode 10 bytes
  let (branchId, bytes) ← Alpha.decode 2 bytes
  let (orderRestrictions, bytes) ← Alpha.decode 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (ordType, bytes) ← OrdType.decode bytes
  let (orderQty, bytes) ← decodeUInt 8 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  pure ({ applId, submittingPbuid, securityId, securityIdSource, ownerType, clearingFirm, transactTime, userInfo, clOrdId, accountId, branchId, orderRestrictions, side, ordType, orderQty, price }, bytes)

@[simp] theorem encode_length (message : SubscriptionNewOrderMessage) : (encode message).length = 109 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, Side.encode_length, OrdType.encode_length]

theorem encode_length_pos (message : SubscriptionNewOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SubscriptionNewOrderMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrdType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SubscriptionNewOrderMessage

/-- Put Back New Order Message: 109 bytes -/
structure PutBackNewOrderMessage where
  applId : Alpha 3
  submittingPbuid : Alpha 6
  securityId : Alpha 8
  securityIdSource : Alpha 4
  ownerType : BitVec 16
  clearingFirm : Alpha 2
  transactTime : BitVec 64
  userInfo : Alpha 32
  clOrdId : Alpha 10
  accountId : Alpha 10
  branchId : Alpha 2
  orderRestrictions : Alpha 4
  side : Side
  ordType : OrdType
  orderQty : BitVec 64
  price : BitVec 64
  deriving DecidableEq, Repr

namespace PutBackNewOrderMessage

def encode (message : PutBackNewOrderMessage) : List UInt8 :=
  Alpha.encode message.applId
    ++ (Alpha.encode message.submittingPbuid
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 2 message.ownerType
    ++ (Alpha.encode message.clearingFirm
    ++ (encodeUInt 8 message.transactTime
    ++ (Alpha.encode message.userInfo
    ++ (Alpha.encode message.clOrdId
    ++ (Alpha.encode message.accountId
    ++ (Alpha.encode message.branchId
    ++ (Alpha.encode message.orderRestrictions
    ++ (Side.encode message.side
    ++ (OrdType.encode message.ordType
    ++ (encodeUInt 8 message.orderQty
    ++ (encodeUInt 8 message.price)))))))))))))))

def decode (bytes : List UInt8) : Option (PutBackNewOrderMessage × List UInt8) := do
  let (applId, bytes) ← Alpha.decode 3 bytes
  let (submittingPbuid, bytes) ← Alpha.decode 6 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (ownerType, bytes) ← decodeUInt 2 bytes
  let (clearingFirm, bytes) ← Alpha.decode 2 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  let (userInfo, bytes) ← Alpha.decode 32 bytes
  let (clOrdId, bytes) ← Alpha.decode 10 bytes
  let (accountId, bytes) ← Alpha.decode 10 bytes
  let (branchId, bytes) ← Alpha.decode 2 bytes
  let (orderRestrictions, bytes) ← Alpha.decode 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (ordType, bytes) ← OrdType.decode bytes
  let (orderQty, bytes) ← decodeUInt 8 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  pure ({ applId, submittingPbuid, securityId, securityIdSource, ownerType, clearingFirm, transactTime, userInfo, clOrdId, accountId, branchId, orderRestrictions, side, ordType, orderQty, price }, bytes)

@[simp] theorem encode_length (message : PutBackNewOrderMessage) : (encode message).length = 109 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, Side.encode_length, OrdType.encode_length]

theorem encode_length_pos (message : PutBackNewOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PutBackNewOrderMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrdType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end PutBackNewOrderMessage

/-- Tender Offer Acceptance New Order Message: 109 bytes -/
structure TenderOfferAcceptanceNewOrderMessage where
  applId : Alpha 3
  submittingPbuid : Alpha 6
  securityId : Alpha 8
  securityIdSource : Alpha 4
  ownerType : BitVec 16
  clearingFirm : Alpha 2
  transactTime : BitVec 64
  userInfo : Alpha 32
  clOrdId : Alpha 10
  accountId : Alpha 10
  branchId : Alpha 2
  orderRestrictions : Alpha 4
  side : Side
  ordType : OrdType
  orderQty : BitVec 64
  price : BitVec 64
  deriving DecidableEq, Repr

namespace TenderOfferAcceptanceNewOrderMessage

def encode (message : TenderOfferAcceptanceNewOrderMessage) : List UInt8 :=
  Alpha.encode message.applId
    ++ (Alpha.encode message.submittingPbuid
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 2 message.ownerType
    ++ (Alpha.encode message.clearingFirm
    ++ (encodeUInt 8 message.transactTime
    ++ (Alpha.encode message.userInfo
    ++ (Alpha.encode message.clOrdId
    ++ (Alpha.encode message.accountId
    ++ (Alpha.encode message.branchId
    ++ (Alpha.encode message.orderRestrictions
    ++ (Side.encode message.side
    ++ (OrdType.encode message.ordType
    ++ (encodeUInt 8 message.orderQty
    ++ (encodeUInt 8 message.price)))))))))))))))

def decode (bytes : List UInt8) : Option (TenderOfferAcceptanceNewOrderMessage × List UInt8) := do
  let (applId, bytes) ← Alpha.decode 3 bytes
  let (submittingPbuid, bytes) ← Alpha.decode 6 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (ownerType, bytes) ← decodeUInt 2 bytes
  let (clearingFirm, bytes) ← Alpha.decode 2 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  let (userInfo, bytes) ← Alpha.decode 32 bytes
  let (clOrdId, bytes) ← Alpha.decode 10 bytes
  let (accountId, bytes) ← Alpha.decode 10 bytes
  let (branchId, bytes) ← Alpha.decode 2 bytes
  let (orderRestrictions, bytes) ← Alpha.decode 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (ordType, bytes) ← OrdType.decode bytes
  let (orderQty, bytes) ← decodeUInt 8 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  pure ({ applId, submittingPbuid, securityId, securityIdSource, ownerType, clearingFirm, transactTime, userInfo, clOrdId, accountId, branchId, orderRestrictions, side, ordType, orderQty, price }, bytes)

@[simp] theorem encode_length (message : TenderOfferAcceptanceNewOrderMessage) : (encode message).length = 109 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, Side.encode_length, OrdType.encode_length]

theorem encode_length_pos (message : TenderOfferAcceptanceNewOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TenderOfferAcceptanceNewOrderMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrdType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TenderOfferAcceptanceNewOrderMessage

/-- Refinancing Securities Lending Non Agreed New Order Message: 114 bytes -/
structure RefinancingSecuritiesLendingNonAgreedNewOrderMessage where
  applId : Alpha 3
  submittingPbuid : Alpha 6
  securityId : Alpha 8
  securityIdSource : Alpha 4
  ownerType : BitVec 16
  clearingFirm : Alpha 2
  transactTime : BitVec 64
  userInfo : Alpha 32
  clOrdId : Alpha 10
  accountId : Alpha 10
  branchId : Alpha 2
  orderRestrictions : Alpha 4
  side : Side
  ordType : OrdType
  orderQty : BitVec 64
  price : BitVec 64
  expirationDays : BitVec 16
  expirationType : BitVec 8
  shareProperty : Alpha 2
  deriving DecidableEq, Repr

namespace RefinancingSecuritiesLendingNonAgreedNewOrderMessage

def encode (message : RefinancingSecuritiesLendingNonAgreedNewOrderMessage) : List UInt8 :=
  Alpha.encode message.applId
    ++ (Alpha.encode message.submittingPbuid
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 2 message.ownerType
    ++ (Alpha.encode message.clearingFirm
    ++ (encodeUInt 8 message.transactTime
    ++ (Alpha.encode message.userInfo
    ++ (Alpha.encode message.clOrdId
    ++ (Alpha.encode message.accountId
    ++ (Alpha.encode message.branchId
    ++ (Alpha.encode message.orderRestrictions
    ++ (Side.encode message.side
    ++ (OrdType.encode message.ordType
    ++ (encodeUInt 8 message.orderQty
    ++ (encodeUInt 8 message.price
    ++ (encodeUInt 2 message.expirationDays
    ++ (encodeUInt 1 message.expirationType
    ++ (Alpha.encode message.shareProperty))))))))))))))))))

def decode (bytes : List UInt8) : Option (RefinancingSecuritiesLendingNonAgreedNewOrderMessage × List UInt8) := do
  let (applId, bytes) ← Alpha.decode 3 bytes
  let (submittingPbuid, bytes) ← Alpha.decode 6 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (ownerType, bytes) ← decodeUInt 2 bytes
  let (clearingFirm, bytes) ← Alpha.decode 2 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  let (userInfo, bytes) ← Alpha.decode 32 bytes
  let (clOrdId, bytes) ← Alpha.decode 10 bytes
  let (accountId, bytes) ← Alpha.decode 10 bytes
  let (branchId, bytes) ← Alpha.decode 2 bytes
  let (orderRestrictions, bytes) ← Alpha.decode 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (ordType, bytes) ← OrdType.decode bytes
  let (orderQty, bytes) ← decodeUInt 8 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (expirationDays, bytes) ← decodeUInt 2 bytes
  let (expirationType, bytes) ← decodeUInt 1 bytes
  let (shareProperty, bytes) ← Alpha.decode 2 bytes
  pure ({ applId, submittingPbuid, securityId, securityIdSource, ownerType, clearingFirm, transactTime, userInfo, clOrdId, accountId, branchId, orderRestrictions, side, ordType, orderQty, price, expirationDays, expirationType, shareProperty }, bytes)

@[simp] theorem encode_length (message : RefinancingSecuritiesLendingNonAgreedNewOrderMessage) : (encode message).length = 114 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, Side.encode_length, OrdType.encode_length]

theorem encode_length_pos (message : RefinancingSecuritiesLendingNonAgreedNewOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RefinancingSecuritiesLendingNonAgreedNewOrderMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrdType.decode_encode, some_bind]
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

end RefinancingSecuritiesLendingNonAgreedNewOrderMessage

/-- Order Cancel Request Message: 121 bytes -/
structure OrderCancelRequestMessage where
  applId : Alpha 3
  submittingPbuid : Alpha 6
  securityId : Alpha 8
  securityIdSource : Alpha 4
  ownerType : BitVec 16
  clearingFirm : Alpha 2
  transactTime : BitVec 64
  userInfo : Alpha 32
  clOrdId : Alpha 10
  origClOrdId : Alpha 10
  accountId : Alpha 10
  branchId : Alpha 2
  orderId : Alpha 16
  orderQty : BitVec 64
  deriving DecidableEq, Repr

namespace OrderCancelRequestMessage

def encode (message : OrderCancelRequestMessage) : List UInt8 :=
  Alpha.encode message.applId
    ++ (Alpha.encode message.submittingPbuid
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 2 message.ownerType
    ++ (Alpha.encode message.clearingFirm
    ++ (encodeUInt 8 message.transactTime
    ++ (Alpha.encode message.userInfo
    ++ (Alpha.encode message.clOrdId
    ++ (Alpha.encode message.origClOrdId
    ++ (Alpha.encode message.accountId
    ++ (Alpha.encode message.branchId
    ++ (Alpha.encode message.orderId
    ++ (encodeUInt 8 message.orderQty)))))))))))))

def decode (bytes : List UInt8) : Option (OrderCancelRequestMessage × List UInt8) := do
  let (applId, bytes) ← Alpha.decode 3 bytes
  let (submittingPbuid, bytes) ← Alpha.decode 6 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (ownerType, bytes) ← decodeUInt 2 bytes
  let (clearingFirm, bytes) ← Alpha.decode 2 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  let (userInfo, bytes) ← Alpha.decode 32 bytes
  let (clOrdId, bytes) ← Alpha.decode 10 bytes
  let (origClOrdId, bytes) ← Alpha.decode 10 bytes
  let (accountId, bytes) ← Alpha.decode 10 bytes
  let (branchId, bytes) ← Alpha.decode 2 bytes
  let (orderId, bytes) ← Alpha.decode 16 bytes
  let (orderQty, bytes) ← decodeUInt 8 bytes
  pure ({ applId, submittingPbuid, securityId, securityIdSource, ownerType, clearingFirm, transactTime, userInfo, clOrdId, origClOrdId, accountId, branchId, orderId, orderQty }, bytes)

@[simp] theorem encode_length (message : OrderCancelRequestMessage) : (encode message).length = 121 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : OrderCancelRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancelRequestMessage) (rest : List UInt8) :
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderCancelRequestMessage

/-- Cancel Reject Message: 150 bytes -/
structure CancelRejectMessage where
  partitionNo : BitVec 32
  reportIndex : BitVec 64
  applId : Alpha 3
  reportingPbuid : Alpha 6
  submittingPbuid : Alpha 6
  securityId : Alpha 8
  securityIdSource : Alpha 4
  ownerType : BitVec 16
  clearingFirm : Alpha 2
  transactTime : BitVec 64
  userInfo : Alpha 32
  clOrdId : Alpha 10
  origClOrdId : Alpha 10
  accountId : Alpha 10
  branchId : Alpha 2
  ordStatus : OrdStatus
  cxlRejReason : BitVec 16
  rejectText : Alpha 16
  orderId : Alpha 16
  deriving DecidableEq, Repr

namespace CancelRejectMessage

def encode (message : CancelRejectMessage) : List UInt8 :=
  encodeUInt 4 message.partitionNo
    ++ (encodeUInt 8 message.reportIndex
    ++ (Alpha.encode message.applId
    ++ (Alpha.encode message.reportingPbuid
    ++ (Alpha.encode message.submittingPbuid
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 2 message.ownerType
    ++ (Alpha.encode message.clearingFirm
    ++ (encodeUInt 8 message.transactTime
    ++ (Alpha.encode message.userInfo
    ++ (Alpha.encode message.clOrdId
    ++ (Alpha.encode message.origClOrdId
    ++ (Alpha.encode message.accountId
    ++ (Alpha.encode message.branchId
    ++ (OrdStatus.encode message.ordStatus
    ++ (encodeUInt 2 message.cxlRejReason
    ++ (Alpha.encode message.rejectText
    ++ (Alpha.encode message.orderId))))))))))))))))))

def decode (bytes : List UInt8) : Option (CancelRejectMessage × List UInt8) := do
  let (partitionNo, bytes) ← decodeUInt 4 bytes
  let (reportIndex, bytes) ← decodeUInt 8 bytes
  let (applId, bytes) ← Alpha.decode 3 bytes
  let (reportingPbuid, bytes) ← Alpha.decode 6 bytes
  let (submittingPbuid, bytes) ← Alpha.decode 6 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (ownerType, bytes) ← decodeUInt 2 bytes
  let (clearingFirm, bytes) ← Alpha.decode 2 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  let (userInfo, bytes) ← Alpha.decode 32 bytes
  let (clOrdId, bytes) ← Alpha.decode 10 bytes
  let (origClOrdId, bytes) ← Alpha.decode 10 bytes
  let (accountId, bytes) ← Alpha.decode 10 bytes
  let (branchId, bytes) ← Alpha.decode 2 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (cxlRejReason, bytes) ← decodeUInt 2 bytes
  let (rejectText, bytes) ← Alpha.decode 16 bytes
  let (orderId, bytes) ← Alpha.decode 16 bytes
  pure ({ partitionNo, reportIndex, applId, reportingPbuid, submittingPbuid, securityId, securityIdSource, ownerType, clearingFirm, transactTime, userInfo, clOrdId, origClOrdId, accountId, branchId, ordStatus, cxlRejReason, rejectText, orderId }, bytes)

@[simp] theorem encode_length (message : CancelRejectMessage) : (encode message).length = 150 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, OrdStatus.encode_length]

theorem encode_length_pos (message : CancelRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CancelRejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end CancelRejectMessage

/-- Bond Spot Matching Execution Report Message: 209 bytes -/
structure BondSpotMatchingExecutionReportMessage where
  partitionNo : BitVec 32
  reportIndex : BitVec 64
  applId : Alpha 3
  reportingPbuid : Alpha 6
  submittingPbuid : Alpha 6
  securityId : Alpha 8
  securityIdSource : Alpha 4
  ownerType : BitVec 16
  clearingFirm : Alpha 2
  transactTime : BitVec 64
  userInfo : Alpha 32
  orderId : Alpha 16
  clOrdId : Alpha 10
  origClOrdId : Alpha 10
  execId : Alpha 16
  execType : ExecType
  ordStatus : OrdStatus
  ordRejReason : BitVec 16
  leavesQty : BitVec 64
  cumQty : BitVec 64
  side : Side
  ordType : OrdType
  orderQty : BitVec 64
  price : BitVec 64
  accountId : Alpha 10
  branchId : Alpha 2
  orderRestrictions : Alpha 4
  stopPx : BitVec 64
  minQty : BitVec 64
  maxPriceLevels : BitVec 16
  timeInForce : TimeInForce
  cashMargin : CashMargin
  deriving DecidableEq, Repr

namespace BondSpotMatchingExecutionReportMessage

def encode (message : BondSpotMatchingExecutionReportMessage) : List UInt8 :=
  encodeUInt 4 message.partitionNo
    ++ (encodeUInt 8 message.reportIndex
    ++ (Alpha.encode message.applId
    ++ (Alpha.encode message.reportingPbuid
    ++ (Alpha.encode message.submittingPbuid
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 2 message.ownerType
    ++ (Alpha.encode message.clearingFirm
    ++ (encodeUInt 8 message.transactTime
    ++ (Alpha.encode message.userInfo
    ++ (Alpha.encode message.orderId
    ++ (Alpha.encode message.clOrdId
    ++ (Alpha.encode message.origClOrdId
    ++ (Alpha.encode message.execId
    ++ (ExecType.encode message.execType
    ++ (OrdStatus.encode message.ordStatus
    ++ (encodeUInt 2 message.ordRejReason
    ++ (encodeUInt 8 message.leavesQty
    ++ (encodeUInt 8 message.cumQty
    ++ (Side.encode message.side
    ++ (OrdType.encode message.ordType
    ++ (encodeUInt 8 message.orderQty
    ++ (encodeUInt 8 message.price
    ++ (Alpha.encode message.accountId
    ++ (Alpha.encode message.branchId
    ++ (Alpha.encode message.orderRestrictions
    ++ (encodeUInt 8 message.stopPx
    ++ (encodeUInt 8 message.minQty
    ++ (encodeUInt 2 message.maxPriceLevels
    ++ (TimeInForce.encode message.timeInForce
    ++ (CashMargin.encode message.cashMargin)))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (BondSpotMatchingExecutionReportMessage × List UInt8) := do
  let (partitionNo, bytes) ← decodeUInt 4 bytes
  let (reportIndex, bytes) ← decodeUInt 8 bytes
  let (applId, bytes) ← Alpha.decode 3 bytes
  let (reportingPbuid, bytes) ← Alpha.decode 6 bytes
  let (submittingPbuid, bytes) ← Alpha.decode 6 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (ownerType, bytes) ← decodeUInt 2 bytes
  let (clearingFirm, bytes) ← Alpha.decode 2 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  let (userInfo, bytes) ← Alpha.decode 32 bytes
  let (orderId, bytes) ← Alpha.decode 16 bytes
  let (clOrdId, bytes) ← Alpha.decode 10 bytes
  let (origClOrdId, bytes) ← Alpha.decode 10 bytes
  let (execId, bytes) ← Alpha.decode 16 bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (ordRejReason, bytes) ← decodeUInt 2 bytes
  let (leavesQty, bytes) ← decodeUInt 8 bytes
  let (cumQty, bytes) ← decodeUInt 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (ordType, bytes) ← OrdType.decode bytes
  let (orderQty, bytes) ← decodeUInt 8 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (accountId, bytes) ← Alpha.decode 10 bytes
  let (branchId, bytes) ← Alpha.decode 2 bytes
  let (orderRestrictions, bytes) ← Alpha.decode 4 bytes
  let (stopPx, bytes) ← decodeUInt 8 bytes
  let (minQty, bytes) ← decodeUInt 8 bytes
  let (maxPriceLevels, bytes) ← decodeUInt 2 bytes
  let (timeInForce, bytes) ← TimeInForce.decode bytes
  let (cashMargin, bytes) ← CashMargin.decode bytes
  pure ({ partitionNo, reportIndex, applId, reportingPbuid, submittingPbuid, securityId, securityIdSource, ownerType, clearingFirm, transactTime, userInfo, orderId, clOrdId, origClOrdId, execId, execType, ordStatus, ordRejReason, leavesQty, cumQty, side, ordType, orderQty, price, accountId, branchId, orderRestrictions, stopPx, minQty, maxPriceLevels, timeInForce, cashMargin }, bytes)

@[simp] theorem encode_length (message : BondSpotMatchingExecutionReportMessage) : (encode message).length = 209 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, ExecType.encode_length, OrdStatus.encode_length, Side.encode_length, OrdType.encode_length, TimeInForce.encode_length, CashMargin.encode_length]

theorem encode_length_pos (message : BondSpotMatchingExecutionReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : BondSpotMatchingExecutionReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrdType.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TimeInForce.decode_encode, some_bind]
  dsimp only
  rw [CashMargin.decode_encode, some_bind]
  rfl

end BondSpotMatchingExecutionReportMessage

/-- Centralized Auction Execution Report Message: 209 bytes -/
structure CentralizedAuctionExecutionReportMessage where
  partitionNo : BitVec 32
  reportIndex : BitVec 64
  applId : Alpha 3
  reportingPbuid : Alpha 6
  submittingPbuid : Alpha 6
  securityId : Alpha 8
  securityIdSource : Alpha 4
  ownerType : BitVec 16
  clearingFirm : Alpha 2
  transactTime : BitVec 64
  userInfo : Alpha 32
  orderId : Alpha 16
  clOrdId : Alpha 10
  origClOrdId : Alpha 10
  execId : Alpha 16
  execType : ExecType
  ordStatus : OrdStatus
  ordRejReason : BitVec 16
  leavesQty : BitVec 64
  cumQty : BitVec 64
  side : Side
  ordType : OrdType
  orderQty : BitVec 64
  price : BitVec 64
  accountId : Alpha 10
  branchId : Alpha 2
  orderRestrictions : Alpha 4
  stopPx : BitVec 64
  minQty : BitVec 64
  maxPriceLevels : BitVec 16
  timeInForce : TimeInForce
  cashMargin : CashMargin
  deriving DecidableEq, Repr

namespace CentralizedAuctionExecutionReportMessage

def encode (message : CentralizedAuctionExecutionReportMessage) : List UInt8 :=
  encodeUInt 4 message.partitionNo
    ++ (encodeUInt 8 message.reportIndex
    ++ (Alpha.encode message.applId
    ++ (Alpha.encode message.reportingPbuid
    ++ (Alpha.encode message.submittingPbuid
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 2 message.ownerType
    ++ (Alpha.encode message.clearingFirm
    ++ (encodeUInt 8 message.transactTime
    ++ (Alpha.encode message.userInfo
    ++ (Alpha.encode message.orderId
    ++ (Alpha.encode message.clOrdId
    ++ (Alpha.encode message.origClOrdId
    ++ (Alpha.encode message.execId
    ++ (ExecType.encode message.execType
    ++ (OrdStatus.encode message.ordStatus
    ++ (encodeUInt 2 message.ordRejReason
    ++ (encodeUInt 8 message.leavesQty
    ++ (encodeUInt 8 message.cumQty
    ++ (Side.encode message.side
    ++ (OrdType.encode message.ordType
    ++ (encodeUInt 8 message.orderQty
    ++ (encodeUInt 8 message.price
    ++ (Alpha.encode message.accountId
    ++ (Alpha.encode message.branchId
    ++ (Alpha.encode message.orderRestrictions
    ++ (encodeUInt 8 message.stopPx
    ++ (encodeUInt 8 message.minQty
    ++ (encodeUInt 2 message.maxPriceLevels
    ++ (TimeInForce.encode message.timeInForce
    ++ (CashMargin.encode message.cashMargin)))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (CentralizedAuctionExecutionReportMessage × List UInt8) := do
  let (partitionNo, bytes) ← decodeUInt 4 bytes
  let (reportIndex, bytes) ← decodeUInt 8 bytes
  let (applId, bytes) ← Alpha.decode 3 bytes
  let (reportingPbuid, bytes) ← Alpha.decode 6 bytes
  let (submittingPbuid, bytes) ← Alpha.decode 6 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (ownerType, bytes) ← decodeUInt 2 bytes
  let (clearingFirm, bytes) ← Alpha.decode 2 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  let (userInfo, bytes) ← Alpha.decode 32 bytes
  let (orderId, bytes) ← Alpha.decode 16 bytes
  let (clOrdId, bytes) ← Alpha.decode 10 bytes
  let (origClOrdId, bytes) ← Alpha.decode 10 bytes
  let (execId, bytes) ← Alpha.decode 16 bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (ordRejReason, bytes) ← decodeUInt 2 bytes
  let (leavesQty, bytes) ← decodeUInt 8 bytes
  let (cumQty, bytes) ← decodeUInt 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (ordType, bytes) ← OrdType.decode bytes
  let (orderQty, bytes) ← decodeUInt 8 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (accountId, bytes) ← Alpha.decode 10 bytes
  let (branchId, bytes) ← Alpha.decode 2 bytes
  let (orderRestrictions, bytes) ← Alpha.decode 4 bytes
  let (stopPx, bytes) ← decodeUInt 8 bytes
  let (minQty, bytes) ← decodeUInt 8 bytes
  let (maxPriceLevels, bytes) ← decodeUInt 2 bytes
  let (timeInForce, bytes) ← TimeInForce.decode bytes
  let (cashMargin, bytes) ← CashMargin.decode bytes
  pure ({ partitionNo, reportIndex, applId, reportingPbuid, submittingPbuid, securityId, securityIdSource, ownerType, clearingFirm, transactTime, userInfo, orderId, clOrdId, origClOrdId, execId, execType, ordStatus, ordRejReason, leavesQty, cumQty, side, ordType, orderQty, price, accountId, branchId, orderRestrictions, stopPx, minQty, maxPriceLevels, timeInForce, cashMargin }, bytes)

@[simp] theorem encode_length (message : CentralizedAuctionExecutionReportMessage) : (encode message).length = 209 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, ExecType.encode_length, OrdStatus.encode_length, Side.encode_length, OrdType.encode_length, TimeInForce.encode_length, CashMargin.encode_length]

theorem encode_length_pos (message : CentralizedAuctionExecutionReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : CentralizedAuctionExecutionReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrdType.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TimeInForce.decode_encode, some_bind]
  dsimp only
  rw [CashMargin.decode_encode, some_bind]
  rfl

end CentralizedAuctionExecutionReportMessage

/-- Conversion Execution Report Message: 189 bytes -/
structure ConversionExecutionReportMessage where
  partitionNo : BitVec 32
  reportIndex : BitVec 64
  applId : Alpha 3
  reportingPbuid : Alpha 6
  submittingPbuid : Alpha 6
  securityId : Alpha 8
  securityIdSource : Alpha 4
  ownerType : BitVec 16
  clearingFirm : Alpha 2
  transactTime : BitVec 64
  userInfo : Alpha 32
  orderId : Alpha 16
  clOrdId : Alpha 10
  origClOrdId : Alpha 10
  execId : Alpha 16
  execType : ExecType
  ordStatus : OrdStatus
  ordRejReason : BitVec 16
  leavesQty : BitVec 64
  cumQty : BitVec 64
  side : Side
  ordType : OrdType
  orderQty : BitVec 64
  price : BitVec 64
  accountId : Alpha 10
  branchId : Alpha 2
  orderRestrictions : Alpha 4
  deriving DecidableEq, Repr

namespace ConversionExecutionReportMessage

def encode (message : ConversionExecutionReportMessage) : List UInt8 :=
  encodeUInt 4 message.partitionNo
    ++ (encodeUInt 8 message.reportIndex
    ++ (Alpha.encode message.applId
    ++ (Alpha.encode message.reportingPbuid
    ++ (Alpha.encode message.submittingPbuid
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 2 message.ownerType
    ++ (Alpha.encode message.clearingFirm
    ++ (encodeUInt 8 message.transactTime
    ++ (Alpha.encode message.userInfo
    ++ (Alpha.encode message.orderId
    ++ (Alpha.encode message.clOrdId
    ++ (Alpha.encode message.origClOrdId
    ++ (Alpha.encode message.execId
    ++ (ExecType.encode message.execType
    ++ (OrdStatus.encode message.ordStatus
    ++ (encodeUInt 2 message.ordRejReason
    ++ (encodeUInt 8 message.leavesQty
    ++ (encodeUInt 8 message.cumQty
    ++ (Side.encode message.side
    ++ (OrdType.encode message.ordType
    ++ (encodeUInt 8 message.orderQty
    ++ (encodeUInt 8 message.price
    ++ (Alpha.encode message.accountId
    ++ (Alpha.encode message.branchId
    ++ (Alpha.encode message.orderRestrictions))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ConversionExecutionReportMessage × List UInt8) := do
  let (partitionNo, bytes) ← decodeUInt 4 bytes
  let (reportIndex, bytes) ← decodeUInt 8 bytes
  let (applId, bytes) ← Alpha.decode 3 bytes
  let (reportingPbuid, bytes) ← Alpha.decode 6 bytes
  let (submittingPbuid, bytes) ← Alpha.decode 6 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (ownerType, bytes) ← decodeUInt 2 bytes
  let (clearingFirm, bytes) ← Alpha.decode 2 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  let (userInfo, bytes) ← Alpha.decode 32 bytes
  let (orderId, bytes) ← Alpha.decode 16 bytes
  let (clOrdId, bytes) ← Alpha.decode 10 bytes
  let (origClOrdId, bytes) ← Alpha.decode 10 bytes
  let (execId, bytes) ← Alpha.decode 16 bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (ordRejReason, bytes) ← decodeUInt 2 bytes
  let (leavesQty, bytes) ← decodeUInt 8 bytes
  let (cumQty, bytes) ← decodeUInt 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (ordType, bytes) ← OrdType.decode bytes
  let (orderQty, bytes) ← decodeUInt 8 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (accountId, bytes) ← Alpha.decode 10 bytes
  let (branchId, bytes) ← Alpha.decode 2 bytes
  let (orderRestrictions, bytes) ← Alpha.decode 4 bytes
  pure ({ partitionNo, reportIndex, applId, reportingPbuid, submittingPbuid, securityId, securityIdSource, ownerType, clearingFirm, transactTime, userInfo, orderId, clOrdId, origClOrdId, execId, execType, ordStatus, ordRejReason, leavesQty, cumQty, side, ordType, orderQty, price, accountId, branchId, orderRestrictions }, bytes)

@[simp] theorem encode_length (message : ConversionExecutionReportMessage) : (encode message).length = 189 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, ExecType.encode_length, OrdStatus.encode_length, Side.encode_length, OrdType.encode_length]

theorem encode_length_pos (message : ConversionExecutionReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ConversionExecutionReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrdType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ConversionExecutionReportMessage

/-- Inquiry Execution Report Message: 189 bytes -/
structure InquiryExecutionReportMessage where
  partitionNo : BitVec 32
  reportIndex : BitVec 64
  applId : Alpha 3
  reportingPbuid : Alpha 6
  submittingPbuid : Alpha 6
  securityId : Alpha 8
  securityIdSource : Alpha 4
  ownerType : BitVec 16
  clearingFirm : Alpha 2
  transactTime : BitVec 64
  userInfo : Alpha 32
  orderId : Alpha 16
  clOrdId : Alpha 10
  origClOrdId : Alpha 10
  execId : Alpha 16
  execType : ExecType
  ordStatus : OrdStatus
  ordRejReason : BitVec 16
  leavesQty : BitVec 64
  cumQty : BitVec 64
  side : Side
  ordType : OrdType
  orderQty : BitVec 64
  price : BitVec 64
  accountId : Alpha 10
  branchId : Alpha 2
  orderRestrictions : Alpha 4
  deriving DecidableEq, Repr

namespace InquiryExecutionReportMessage

def encode (message : InquiryExecutionReportMessage) : List UInt8 :=
  encodeUInt 4 message.partitionNo
    ++ (encodeUInt 8 message.reportIndex
    ++ (Alpha.encode message.applId
    ++ (Alpha.encode message.reportingPbuid
    ++ (Alpha.encode message.submittingPbuid
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 2 message.ownerType
    ++ (Alpha.encode message.clearingFirm
    ++ (encodeUInt 8 message.transactTime
    ++ (Alpha.encode message.userInfo
    ++ (Alpha.encode message.orderId
    ++ (Alpha.encode message.clOrdId
    ++ (Alpha.encode message.origClOrdId
    ++ (Alpha.encode message.execId
    ++ (ExecType.encode message.execType
    ++ (OrdStatus.encode message.ordStatus
    ++ (encodeUInt 2 message.ordRejReason
    ++ (encodeUInt 8 message.leavesQty
    ++ (encodeUInt 8 message.cumQty
    ++ (Side.encode message.side
    ++ (OrdType.encode message.ordType
    ++ (encodeUInt 8 message.orderQty
    ++ (encodeUInt 8 message.price
    ++ (Alpha.encode message.accountId
    ++ (Alpha.encode message.branchId
    ++ (Alpha.encode message.orderRestrictions))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (InquiryExecutionReportMessage × List UInt8) := do
  let (partitionNo, bytes) ← decodeUInt 4 bytes
  let (reportIndex, bytes) ← decodeUInt 8 bytes
  let (applId, bytes) ← Alpha.decode 3 bytes
  let (reportingPbuid, bytes) ← Alpha.decode 6 bytes
  let (submittingPbuid, bytes) ← Alpha.decode 6 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (ownerType, bytes) ← decodeUInt 2 bytes
  let (clearingFirm, bytes) ← Alpha.decode 2 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  let (userInfo, bytes) ← Alpha.decode 32 bytes
  let (orderId, bytes) ← Alpha.decode 16 bytes
  let (clOrdId, bytes) ← Alpha.decode 10 bytes
  let (origClOrdId, bytes) ← Alpha.decode 10 bytes
  let (execId, bytes) ← Alpha.decode 16 bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (ordRejReason, bytes) ← decodeUInt 2 bytes
  let (leavesQty, bytes) ← decodeUInt 8 bytes
  let (cumQty, bytes) ← decodeUInt 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (ordType, bytes) ← OrdType.decode bytes
  let (orderQty, bytes) ← decodeUInt 8 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (accountId, bytes) ← Alpha.decode 10 bytes
  let (branchId, bytes) ← Alpha.decode 2 bytes
  let (orderRestrictions, bytes) ← Alpha.decode 4 bytes
  pure ({ partitionNo, reportIndex, applId, reportingPbuid, submittingPbuid, securityId, securityIdSource, ownerType, clearingFirm, transactTime, userInfo, orderId, clOrdId, origClOrdId, execId, execType, ordStatus, ordRejReason, leavesQty, cumQty, side, ordType, orderQty, price, accountId, branchId, orderRestrictions }, bytes)

@[simp] theorem encode_length (message : InquiryExecutionReportMessage) : (encode message).length = 189 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, ExecType.encode_length, OrdStatus.encode_length, Side.encode_length, OrdType.encode_length]

theorem encode_length_pos (message : InquiryExecutionReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : InquiryExecutionReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrdType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end InquiryExecutionReportMessage

/-- Subscription Execution Report Message: 189 bytes -/
structure SubscriptionExecutionReportMessage where
  partitionNo : BitVec 32
  reportIndex : BitVec 64
  applId : Alpha 3
  reportingPbuid : Alpha 6
  submittingPbuid : Alpha 6
  securityId : Alpha 8
  securityIdSource : Alpha 4
  ownerType : BitVec 16
  clearingFirm : Alpha 2
  transactTime : BitVec 64
  userInfo : Alpha 32
  orderId : Alpha 16
  clOrdId : Alpha 10
  origClOrdId : Alpha 10
  execId : Alpha 16
  execType : ExecType
  ordStatus : OrdStatus
  ordRejReason : BitVec 16
  leavesQty : BitVec 64
  cumQty : BitVec 64
  side : Side
  ordType : OrdType
  orderQty : BitVec 64
  price : BitVec 64
  accountId : Alpha 10
  branchId : Alpha 2
  orderRestrictions : Alpha 4
  deriving DecidableEq, Repr

namespace SubscriptionExecutionReportMessage

def encode (message : SubscriptionExecutionReportMessage) : List UInt8 :=
  encodeUInt 4 message.partitionNo
    ++ (encodeUInt 8 message.reportIndex
    ++ (Alpha.encode message.applId
    ++ (Alpha.encode message.reportingPbuid
    ++ (Alpha.encode message.submittingPbuid
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 2 message.ownerType
    ++ (Alpha.encode message.clearingFirm
    ++ (encodeUInt 8 message.transactTime
    ++ (Alpha.encode message.userInfo
    ++ (Alpha.encode message.orderId
    ++ (Alpha.encode message.clOrdId
    ++ (Alpha.encode message.origClOrdId
    ++ (Alpha.encode message.execId
    ++ (ExecType.encode message.execType
    ++ (OrdStatus.encode message.ordStatus
    ++ (encodeUInt 2 message.ordRejReason
    ++ (encodeUInt 8 message.leavesQty
    ++ (encodeUInt 8 message.cumQty
    ++ (Side.encode message.side
    ++ (OrdType.encode message.ordType
    ++ (encodeUInt 8 message.orderQty
    ++ (encodeUInt 8 message.price
    ++ (Alpha.encode message.accountId
    ++ (Alpha.encode message.branchId
    ++ (Alpha.encode message.orderRestrictions))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SubscriptionExecutionReportMessage × List UInt8) := do
  let (partitionNo, bytes) ← decodeUInt 4 bytes
  let (reportIndex, bytes) ← decodeUInt 8 bytes
  let (applId, bytes) ← Alpha.decode 3 bytes
  let (reportingPbuid, bytes) ← Alpha.decode 6 bytes
  let (submittingPbuid, bytes) ← Alpha.decode 6 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (ownerType, bytes) ← decodeUInt 2 bytes
  let (clearingFirm, bytes) ← Alpha.decode 2 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  let (userInfo, bytes) ← Alpha.decode 32 bytes
  let (orderId, bytes) ← Alpha.decode 16 bytes
  let (clOrdId, bytes) ← Alpha.decode 10 bytes
  let (origClOrdId, bytes) ← Alpha.decode 10 bytes
  let (execId, bytes) ← Alpha.decode 16 bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (ordRejReason, bytes) ← decodeUInt 2 bytes
  let (leavesQty, bytes) ← decodeUInt 8 bytes
  let (cumQty, bytes) ← decodeUInt 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (ordType, bytes) ← OrdType.decode bytes
  let (orderQty, bytes) ← decodeUInt 8 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (accountId, bytes) ← Alpha.decode 10 bytes
  let (branchId, bytes) ← Alpha.decode 2 bytes
  let (orderRestrictions, bytes) ← Alpha.decode 4 bytes
  pure ({ partitionNo, reportIndex, applId, reportingPbuid, submittingPbuid, securityId, securityIdSource, ownerType, clearingFirm, transactTime, userInfo, orderId, clOrdId, origClOrdId, execId, execType, ordStatus, ordRejReason, leavesQty, cumQty, side, ordType, orderQty, price, accountId, branchId, orderRestrictions }, bytes)

@[simp] theorem encode_length (message : SubscriptionExecutionReportMessage) : (encode message).length = 189 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, ExecType.encode_length, OrdStatus.encode_length, Side.encode_length, OrdType.encode_length]

theorem encode_length_pos (message : SubscriptionExecutionReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SubscriptionExecutionReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrdType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SubscriptionExecutionReportMessage

/-- Put Back Execution Report Message: 189 bytes -/
structure PutBackExecutionReportMessage where
  partitionNo : BitVec 32
  reportIndex : BitVec 64
  applId : Alpha 3
  reportingPbuid : Alpha 6
  submittingPbuid : Alpha 6
  securityId : Alpha 8
  securityIdSource : Alpha 4
  ownerType : BitVec 16
  clearingFirm : Alpha 2
  transactTime : BitVec 64
  userInfo : Alpha 32
  orderId : Alpha 16
  clOrdId : Alpha 10
  origClOrdId : Alpha 10
  execId : Alpha 16
  execType : ExecType
  ordStatus : OrdStatus
  ordRejReason : BitVec 16
  leavesQty : BitVec 64
  cumQty : BitVec 64
  side : Side
  ordType : OrdType
  orderQty : BitVec 64
  price : BitVec 64
  accountId : Alpha 10
  branchId : Alpha 2
  orderRestrictions : Alpha 4
  deriving DecidableEq, Repr

namespace PutBackExecutionReportMessage

def encode (message : PutBackExecutionReportMessage) : List UInt8 :=
  encodeUInt 4 message.partitionNo
    ++ (encodeUInt 8 message.reportIndex
    ++ (Alpha.encode message.applId
    ++ (Alpha.encode message.reportingPbuid
    ++ (Alpha.encode message.submittingPbuid
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 2 message.ownerType
    ++ (Alpha.encode message.clearingFirm
    ++ (encodeUInt 8 message.transactTime
    ++ (Alpha.encode message.userInfo
    ++ (Alpha.encode message.orderId
    ++ (Alpha.encode message.clOrdId
    ++ (Alpha.encode message.origClOrdId
    ++ (Alpha.encode message.execId
    ++ (ExecType.encode message.execType
    ++ (OrdStatus.encode message.ordStatus
    ++ (encodeUInt 2 message.ordRejReason
    ++ (encodeUInt 8 message.leavesQty
    ++ (encodeUInt 8 message.cumQty
    ++ (Side.encode message.side
    ++ (OrdType.encode message.ordType
    ++ (encodeUInt 8 message.orderQty
    ++ (encodeUInt 8 message.price
    ++ (Alpha.encode message.accountId
    ++ (Alpha.encode message.branchId
    ++ (Alpha.encode message.orderRestrictions))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (PutBackExecutionReportMessage × List UInt8) := do
  let (partitionNo, bytes) ← decodeUInt 4 bytes
  let (reportIndex, bytes) ← decodeUInt 8 bytes
  let (applId, bytes) ← Alpha.decode 3 bytes
  let (reportingPbuid, bytes) ← Alpha.decode 6 bytes
  let (submittingPbuid, bytes) ← Alpha.decode 6 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (ownerType, bytes) ← decodeUInt 2 bytes
  let (clearingFirm, bytes) ← Alpha.decode 2 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  let (userInfo, bytes) ← Alpha.decode 32 bytes
  let (orderId, bytes) ← Alpha.decode 16 bytes
  let (clOrdId, bytes) ← Alpha.decode 10 bytes
  let (origClOrdId, bytes) ← Alpha.decode 10 bytes
  let (execId, bytes) ← Alpha.decode 16 bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (ordRejReason, bytes) ← decodeUInt 2 bytes
  let (leavesQty, bytes) ← decodeUInt 8 bytes
  let (cumQty, bytes) ← decodeUInt 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (ordType, bytes) ← OrdType.decode bytes
  let (orderQty, bytes) ← decodeUInt 8 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (accountId, bytes) ← Alpha.decode 10 bytes
  let (branchId, bytes) ← Alpha.decode 2 bytes
  let (orderRestrictions, bytes) ← Alpha.decode 4 bytes
  pure ({ partitionNo, reportIndex, applId, reportingPbuid, submittingPbuid, securityId, securityIdSource, ownerType, clearingFirm, transactTime, userInfo, orderId, clOrdId, origClOrdId, execId, execType, ordStatus, ordRejReason, leavesQty, cumQty, side, ordType, orderQty, price, accountId, branchId, orderRestrictions }, bytes)

@[simp] theorem encode_length (message : PutBackExecutionReportMessage) : (encode message).length = 189 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, ExecType.encode_length, OrdStatus.encode_length, Side.encode_length, OrdType.encode_length]

theorem encode_length_pos (message : PutBackExecutionReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : PutBackExecutionReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrdType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end PutBackExecutionReportMessage

/-- Tender Offer Acceptance Execution Report Message: 189 bytes -/
structure TenderOfferAcceptanceExecutionReportMessage where
  partitionNo : BitVec 32
  reportIndex : BitVec 64
  applId : Alpha 3
  reportingPbuid : Alpha 6
  submittingPbuid : Alpha 6
  securityId : Alpha 8
  securityIdSource : Alpha 4
  ownerType : BitVec 16
  clearingFirm : Alpha 2
  transactTime : BitVec 64
  userInfo : Alpha 32
  orderId : Alpha 16
  clOrdId : Alpha 10
  origClOrdId : Alpha 10
  execId : Alpha 16
  execType : ExecType
  ordStatus : OrdStatus
  ordRejReason : BitVec 16
  leavesQty : BitVec 64
  cumQty : BitVec 64
  side : Side
  ordType : OrdType
  orderQty : BitVec 64
  price : BitVec 64
  accountId : Alpha 10
  branchId : Alpha 2
  orderRestrictions : Alpha 4
  deriving DecidableEq, Repr

namespace TenderOfferAcceptanceExecutionReportMessage

def encode (message : TenderOfferAcceptanceExecutionReportMessage) : List UInt8 :=
  encodeUInt 4 message.partitionNo
    ++ (encodeUInt 8 message.reportIndex
    ++ (Alpha.encode message.applId
    ++ (Alpha.encode message.reportingPbuid
    ++ (Alpha.encode message.submittingPbuid
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 2 message.ownerType
    ++ (Alpha.encode message.clearingFirm
    ++ (encodeUInt 8 message.transactTime
    ++ (Alpha.encode message.userInfo
    ++ (Alpha.encode message.orderId
    ++ (Alpha.encode message.clOrdId
    ++ (Alpha.encode message.origClOrdId
    ++ (Alpha.encode message.execId
    ++ (ExecType.encode message.execType
    ++ (OrdStatus.encode message.ordStatus
    ++ (encodeUInt 2 message.ordRejReason
    ++ (encodeUInt 8 message.leavesQty
    ++ (encodeUInt 8 message.cumQty
    ++ (Side.encode message.side
    ++ (OrdType.encode message.ordType
    ++ (encodeUInt 8 message.orderQty
    ++ (encodeUInt 8 message.price
    ++ (Alpha.encode message.accountId
    ++ (Alpha.encode message.branchId
    ++ (Alpha.encode message.orderRestrictions))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TenderOfferAcceptanceExecutionReportMessage × List UInt8) := do
  let (partitionNo, bytes) ← decodeUInt 4 bytes
  let (reportIndex, bytes) ← decodeUInt 8 bytes
  let (applId, bytes) ← Alpha.decode 3 bytes
  let (reportingPbuid, bytes) ← Alpha.decode 6 bytes
  let (submittingPbuid, bytes) ← Alpha.decode 6 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (ownerType, bytes) ← decodeUInt 2 bytes
  let (clearingFirm, bytes) ← Alpha.decode 2 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  let (userInfo, bytes) ← Alpha.decode 32 bytes
  let (orderId, bytes) ← Alpha.decode 16 bytes
  let (clOrdId, bytes) ← Alpha.decode 10 bytes
  let (origClOrdId, bytes) ← Alpha.decode 10 bytes
  let (execId, bytes) ← Alpha.decode 16 bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (ordRejReason, bytes) ← decodeUInt 2 bytes
  let (leavesQty, bytes) ← decodeUInt 8 bytes
  let (cumQty, bytes) ← decodeUInt 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (ordType, bytes) ← OrdType.decode bytes
  let (orderQty, bytes) ← decodeUInt 8 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (accountId, bytes) ← Alpha.decode 10 bytes
  let (branchId, bytes) ← Alpha.decode 2 bytes
  let (orderRestrictions, bytes) ← Alpha.decode 4 bytes
  pure ({ partitionNo, reportIndex, applId, reportingPbuid, submittingPbuid, securityId, securityIdSource, ownerType, clearingFirm, transactTime, userInfo, orderId, clOrdId, origClOrdId, execId, execType, ordStatus, ordRejReason, leavesQty, cumQty, side, ordType, orderQty, price, accountId, branchId, orderRestrictions }, bytes)

@[simp] theorem encode_length (message : TenderOfferAcceptanceExecutionReportMessage) : (encode message).length = 189 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, ExecType.encode_length, OrdStatus.encode_length, Side.encode_length, OrdType.encode_length]

theorem encode_length_pos (message : TenderOfferAcceptanceExecutionReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : TenderOfferAcceptanceExecutionReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrdType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TenderOfferAcceptanceExecutionReportMessage

/-- Refinancing Securities Lending Non Agreed Execution Report Message: 194 bytes -/
structure RefinancingSecuritiesLendingNonAgreedExecutionReportMessage where
  partitionNo : BitVec 32
  reportIndex : BitVec 64
  applId : Alpha 3
  reportingPbuid : Alpha 6
  submittingPbuid : Alpha 6
  securityId : Alpha 8
  securityIdSource : Alpha 4
  ownerType : BitVec 16
  clearingFirm : Alpha 2
  transactTime : BitVec 64
  userInfo : Alpha 32
  orderId : Alpha 16
  clOrdId : Alpha 10
  origClOrdId : Alpha 10
  execId : Alpha 16
  execType : ExecType
  ordStatus : OrdStatus
  ordRejReason : BitVec 16
  leavesQty : BitVec 64
  cumQty : BitVec 64
  side : Side
  ordType : OrdType
  orderQty : BitVec 64
  price : BitVec 64
  accountId : Alpha 10
  branchId : Alpha 2
  orderRestrictions : Alpha 4
  expirationDays : BitVec 16
  expirationType : BitVec 8
  shareProperty : Alpha 2
  deriving DecidableEq, Repr

namespace RefinancingSecuritiesLendingNonAgreedExecutionReportMessage

def encode (message : RefinancingSecuritiesLendingNonAgreedExecutionReportMessage) : List UInt8 :=
  encodeUInt 4 message.partitionNo
    ++ (encodeUInt 8 message.reportIndex
    ++ (Alpha.encode message.applId
    ++ (Alpha.encode message.reportingPbuid
    ++ (Alpha.encode message.submittingPbuid
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 2 message.ownerType
    ++ (Alpha.encode message.clearingFirm
    ++ (encodeUInt 8 message.transactTime
    ++ (Alpha.encode message.userInfo
    ++ (Alpha.encode message.orderId
    ++ (Alpha.encode message.clOrdId
    ++ (Alpha.encode message.origClOrdId
    ++ (Alpha.encode message.execId
    ++ (ExecType.encode message.execType
    ++ (OrdStatus.encode message.ordStatus
    ++ (encodeUInt 2 message.ordRejReason
    ++ (encodeUInt 8 message.leavesQty
    ++ (encodeUInt 8 message.cumQty
    ++ (Side.encode message.side
    ++ (OrdType.encode message.ordType
    ++ (encodeUInt 8 message.orderQty
    ++ (encodeUInt 8 message.price
    ++ (Alpha.encode message.accountId
    ++ (Alpha.encode message.branchId
    ++ (Alpha.encode message.orderRestrictions
    ++ (encodeUInt 2 message.expirationDays
    ++ (encodeUInt 1 message.expirationType
    ++ (Alpha.encode message.shareProperty)))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (RefinancingSecuritiesLendingNonAgreedExecutionReportMessage × List UInt8) := do
  let (partitionNo, bytes) ← decodeUInt 4 bytes
  let (reportIndex, bytes) ← decodeUInt 8 bytes
  let (applId, bytes) ← Alpha.decode 3 bytes
  let (reportingPbuid, bytes) ← Alpha.decode 6 bytes
  let (submittingPbuid, bytes) ← Alpha.decode 6 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (ownerType, bytes) ← decodeUInt 2 bytes
  let (clearingFirm, bytes) ← Alpha.decode 2 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  let (userInfo, bytes) ← Alpha.decode 32 bytes
  let (orderId, bytes) ← Alpha.decode 16 bytes
  let (clOrdId, bytes) ← Alpha.decode 10 bytes
  let (origClOrdId, bytes) ← Alpha.decode 10 bytes
  let (execId, bytes) ← Alpha.decode 16 bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (ordRejReason, bytes) ← decodeUInt 2 bytes
  let (leavesQty, bytes) ← decodeUInt 8 bytes
  let (cumQty, bytes) ← decodeUInt 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (ordType, bytes) ← OrdType.decode bytes
  let (orderQty, bytes) ← decodeUInt 8 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (accountId, bytes) ← Alpha.decode 10 bytes
  let (branchId, bytes) ← Alpha.decode 2 bytes
  let (orderRestrictions, bytes) ← Alpha.decode 4 bytes
  let (expirationDays, bytes) ← decodeUInt 2 bytes
  let (expirationType, bytes) ← decodeUInt 1 bytes
  let (shareProperty, bytes) ← Alpha.decode 2 bytes
  pure ({ partitionNo, reportIndex, applId, reportingPbuid, submittingPbuid, securityId, securityIdSource, ownerType, clearingFirm, transactTime, userInfo, orderId, clOrdId, origClOrdId, execId, execType, ordStatus, ordRejReason, leavesQty, cumQty, side, ordType, orderQty, price, accountId, branchId, orderRestrictions, expirationDays, expirationType, shareProperty }, bytes)

@[simp] theorem encode_length (message : RefinancingSecuritiesLendingNonAgreedExecutionReportMessage) : (encode message).length = 194 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, ExecType.encode_length, OrdStatus.encode_length, Side.encode_length, OrdType.encode_length]

theorem encode_length_pos (message : RefinancingSecuritiesLendingNonAgreedExecutionReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : RefinancingSecuritiesLendingNonAgreedExecutionReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrdType.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end RefinancingSecuritiesLendingNonAgreedExecutionReportMessage

/-- Bond Spot Matching Trade Execution Report Message: 175 bytes -/
structure BondSpotMatchingTradeExecutionReportMessage where
  partitionNo : BitVec 32
  reportIndex : BitVec 64
  applId : Alpha 3
  reportingPbuid : Alpha 6
  submittingPbuid : Alpha 6
  securityId : Alpha 8
  securityIdSource : Alpha 4
  ownerType : BitVec 16
  clearingFirm : Alpha 2
  transactTime : BitVec 64
  userInfo : Alpha 32
  orderId : Alpha 16
  clOrdId : Alpha 10
  execId : Alpha 16
  execType : ExecType
  ordStatus : OrdStatus
  lastPx : BitVec 64
  lastQty : BitVec 64
  leavesQty : BitVec 64
  cumQty : BitVec 64
  side : Side
  accountId : Alpha 10
  branchId : Alpha 2
  cashMargin : CashMargin
  settlType : SettlType
  settlPeriod : SettlPeriod
  deriving DecidableEq, Repr

namespace BondSpotMatchingTradeExecutionReportMessage

def encode (message : BondSpotMatchingTradeExecutionReportMessage) : List UInt8 :=
  encodeUInt 4 message.partitionNo
    ++ (encodeUInt 8 message.reportIndex
    ++ (Alpha.encode message.applId
    ++ (Alpha.encode message.reportingPbuid
    ++ (Alpha.encode message.submittingPbuid
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 2 message.ownerType
    ++ (Alpha.encode message.clearingFirm
    ++ (encodeUInt 8 message.transactTime
    ++ (Alpha.encode message.userInfo
    ++ (Alpha.encode message.orderId
    ++ (Alpha.encode message.clOrdId
    ++ (Alpha.encode message.execId
    ++ (ExecType.encode message.execType
    ++ (OrdStatus.encode message.ordStatus
    ++ (encodeUInt 8 message.lastPx
    ++ (encodeUInt 8 message.lastQty
    ++ (encodeUInt 8 message.leavesQty
    ++ (encodeUInt 8 message.cumQty
    ++ (Side.encode message.side
    ++ (Alpha.encode message.accountId
    ++ (Alpha.encode message.branchId
    ++ (CashMargin.encode message.cashMargin
    ++ (SettlType.encode message.settlType
    ++ (SettlPeriod.encode message.settlPeriod)))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (BondSpotMatchingTradeExecutionReportMessage × List UInt8) := do
  let (partitionNo, bytes) ← decodeUInt 4 bytes
  let (reportIndex, bytes) ← decodeUInt 8 bytes
  let (applId, bytes) ← Alpha.decode 3 bytes
  let (reportingPbuid, bytes) ← Alpha.decode 6 bytes
  let (submittingPbuid, bytes) ← Alpha.decode 6 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (ownerType, bytes) ← decodeUInt 2 bytes
  let (clearingFirm, bytes) ← Alpha.decode 2 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  let (userInfo, bytes) ← Alpha.decode 32 bytes
  let (orderId, bytes) ← Alpha.decode 16 bytes
  let (clOrdId, bytes) ← Alpha.decode 10 bytes
  let (execId, bytes) ← Alpha.decode 16 bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (lastPx, bytes) ← decodeUInt 8 bytes
  let (lastQty, bytes) ← decodeUInt 8 bytes
  let (leavesQty, bytes) ← decodeUInt 8 bytes
  let (cumQty, bytes) ← decodeUInt 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (accountId, bytes) ← Alpha.decode 10 bytes
  let (branchId, bytes) ← Alpha.decode 2 bytes
  let (cashMargin, bytes) ← CashMargin.decode bytes
  let (settlType, bytes) ← SettlType.decode bytes
  let (settlPeriod, bytes) ← SettlPeriod.decode bytes
  pure ({ partitionNo, reportIndex, applId, reportingPbuid, submittingPbuid, securityId, securityIdSource, ownerType, clearingFirm, transactTime, userInfo, orderId, clOrdId, execId, execType, ordStatus, lastPx, lastQty, leavesQty, cumQty, side, accountId, branchId, cashMargin, settlType, settlPeriod }, bytes)

@[simp] theorem encode_length (message : BondSpotMatchingTradeExecutionReportMessage) : (encode message).length = 175 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, ExecType.encode_length, OrdStatus.encode_length, Side.encode_length, CashMargin.encode_length, SettlType.encode_length, SettlPeriod.encode_length]

theorem encode_length_pos (message : BondSpotMatchingTradeExecutionReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : BondSpotMatchingTradeExecutionReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CashMargin.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SettlType.decode_encode, some_bind]
  dsimp only
  rw [SettlPeriod.decode_encode, some_bind]
  rfl

end BondSpotMatchingTradeExecutionReportMessage

/-- Centralized Auction Trade Execution Report Message: 173 bytes -/
structure CentralizedAuctionTradeExecutionReportMessage where
  partitionNo : BitVec 32
  reportIndex : BitVec 64
  applId : Alpha 3
  reportingPbuid : Alpha 6
  submittingPbuid : Alpha 6
  securityId : Alpha 8
  securityIdSource : Alpha 4
  ownerType : BitVec 16
  clearingFirm : Alpha 2
  transactTime : BitVec 64
  userInfo : Alpha 32
  orderId : Alpha 16
  clOrdId : Alpha 10
  execId : Alpha 16
  execType : ExecType
  ordStatus : OrdStatus
  lastPx : BitVec 64
  lastQty : BitVec 64
  leavesQty : BitVec 64
  cumQty : BitVec 64
  side : Side
  accountId : Alpha 10
  branchId : Alpha 2
  cashMargin : CashMargin
  deriving DecidableEq, Repr

namespace CentralizedAuctionTradeExecutionReportMessage

def encode (message : CentralizedAuctionTradeExecutionReportMessage) : List UInt8 :=
  encodeUInt 4 message.partitionNo
    ++ (encodeUInt 8 message.reportIndex
    ++ (Alpha.encode message.applId
    ++ (Alpha.encode message.reportingPbuid
    ++ (Alpha.encode message.submittingPbuid
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 2 message.ownerType
    ++ (Alpha.encode message.clearingFirm
    ++ (encodeUInt 8 message.transactTime
    ++ (Alpha.encode message.userInfo
    ++ (Alpha.encode message.orderId
    ++ (Alpha.encode message.clOrdId
    ++ (Alpha.encode message.execId
    ++ (ExecType.encode message.execType
    ++ (OrdStatus.encode message.ordStatus
    ++ (encodeUInt 8 message.lastPx
    ++ (encodeUInt 8 message.lastQty
    ++ (encodeUInt 8 message.leavesQty
    ++ (encodeUInt 8 message.cumQty
    ++ (Side.encode message.side
    ++ (Alpha.encode message.accountId
    ++ (Alpha.encode message.branchId
    ++ (CashMargin.encode message.cashMargin)))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (CentralizedAuctionTradeExecutionReportMessage × List UInt8) := do
  let (partitionNo, bytes) ← decodeUInt 4 bytes
  let (reportIndex, bytes) ← decodeUInt 8 bytes
  let (applId, bytes) ← Alpha.decode 3 bytes
  let (reportingPbuid, bytes) ← Alpha.decode 6 bytes
  let (submittingPbuid, bytes) ← Alpha.decode 6 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (ownerType, bytes) ← decodeUInt 2 bytes
  let (clearingFirm, bytes) ← Alpha.decode 2 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  let (userInfo, bytes) ← Alpha.decode 32 bytes
  let (orderId, bytes) ← Alpha.decode 16 bytes
  let (clOrdId, bytes) ← Alpha.decode 10 bytes
  let (execId, bytes) ← Alpha.decode 16 bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (lastPx, bytes) ← decodeUInt 8 bytes
  let (lastQty, bytes) ← decodeUInt 8 bytes
  let (leavesQty, bytes) ← decodeUInt 8 bytes
  let (cumQty, bytes) ← decodeUInt 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (accountId, bytes) ← Alpha.decode 10 bytes
  let (branchId, bytes) ← Alpha.decode 2 bytes
  let (cashMargin, bytes) ← CashMargin.decode bytes
  pure ({ partitionNo, reportIndex, applId, reportingPbuid, submittingPbuid, securityId, securityIdSource, ownerType, clearingFirm, transactTime, userInfo, orderId, clOrdId, execId, execType, ordStatus, lastPx, lastQty, leavesQty, cumQty, side, accountId, branchId, cashMargin }, bytes)

@[simp] theorem encode_length (message : CentralizedAuctionTradeExecutionReportMessage) : (encode message).length = 173 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, ExecType.encode_length, OrdStatus.encode_length, Side.encode_length, CashMargin.encode_length]

theorem encode_length_pos (message : CentralizedAuctionTradeExecutionReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CentralizedAuctionTradeExecutionReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [CashMargin.decode_encode, some_bind]
  rfl

end CentralizedAuctionTradeExecutionReportMessage

/-- Refinancing Securities Lending Non Agreed Trade Execution Report Message: 181 bytes -/
structure RefinancingSecuritiesLendingNonAgreedTradeExecutionReportMessage where
  partitionNo : BitVec 32
  reportIndex : BitVec 64
  applId : Alpha 3
  reportingPbuid : Alpha 6
  submittingPbuid : Alpha 6
  securityId : Alpha 8
  securityIdSource : Alpha 4
  ownerType : BitVec 16
  clearingFirm : Alpha 2
  transactTime : BitVec 64
  userInfo : Alpha 32
  orderId : Alpha 16
  clOrdId : Alpha 10
  execId : Alpha 16
  execType : ExecType
  ordStatus : OrdStatus
  lastPx : BitVec 64
  lastQty : BitVec 64
  leavesQty : BitVec 64
  cumQty : BitVec 64
  side : Side
  accountId : Alpha 10
  branchId : Alpha 2
  expirationDays : BitVec 16
  expirationType : BitVec 8
  maturityDate : BitVec 32
  shareProperty : Alpha 2
  deriving DecidableEq, Repr

namespace RefinancingSecuritiesLendingNonAgreedTradeExecutionReportMessage

def encode (message : RefinancingSecuritiesLendingNonAgreedTradeExecutionReportMessage) : List UInt8 :=
  encodeUInt 4 message.partitionNo
    ++ (encodeUInt 8 message.reportIndex
    ++ (Alpha.encode message.applId
    ++ (Alpha.encode message.reportingPbuid
    ++ (Alpha.encode message.submittingPbuid
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 2 message.ownerType
    ++ (Alpha.encode message.clearingFirm
    ++ (encodeUInt 8 message.transactTime
    ++ (Alpha.encode message.userInfo
    ++ (Alpha.encode message.orderId
    ++ (Alpha.encode message.clOrdId
    ++ (Alpha.encode message.execId
    ++ (ExecType.encode message.execType
    ++ (OrdStatus.encode message.ordStatus
    ++ (encodeUInt 8 message.lastPx
    ++ (encodeUInt 8 message.lastQty
    ++ (encodeUInt 8 message.leavesQty
    ++ (encodeUInt 8 message.cumQty
    ++ (Side.encode message.side
    ++ (Alpha.encode message.accountId
    ++ (Alpha.encode message.branchId
    ++ (encodeUInt 2 message.expirationDays
    ++ (encodeUInt 1 message.expirationType
    ++ (encodeUInt 4 message.maturityDate
    ++ (Alpha.encode message.shareProperty))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (RefinancingSecuritiesLendingNonAgreedTradeExecutionReportMessage × List UInt8) := do
  let (partitionNo, bytes) ← decodeUInt 4 bytes
  let (reportIndex, bytes) ← decodeUInt 8 bytes
  let (applId, bytes) ← Alpha.decode 3 bytes
  let (reportingPbuid, bytes) ← Alpha.decode 6 bytes
  let (submittingPbuid, bytes) ← Alpha.decode 6 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (ownerType, bytes) ← decodeUInt 2 bytes
  let (clearingFirm, bytes) ← Alpha.decode 2 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  let (userInfo, bytes) ← Alpha.decode 32 bytes
  let (orderId, bytes) ← Alpha.decode 16 bytes
  let (clOrdId, bytes) ← Alpha.decode 10 bytes
  let (execId, bytes) ← Alpha.decode 16 bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (lastPx, bytes) ← decodeUInt 8 bytes
  let (lastQty, bytes) ← decodeUInt 8 bytes
  let (leavesQty, bytes) ← decodeUInt 8 bytes
  let (cumQty, bytes) ← decodeUInt 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (accountId, bytes) ← Alpha.decode 10 bytes
  let (branchId, bytes) ← Alpha.decode 2 bytes
  let (expirationDays, bytes) ← decodeUInt 2 bytes
  let (expirationType, bytes) ← decodeUInt 1 bytes
  let (maturityDate, bytes) ← decodeUInt 4 bytes
  let (shareProperty, bytes) ← Alpha.decode 2 bytes
  pure ({ partitionNo, reportIndex, applId, reportingPbuid, submittingPbuid, securityId, securityIdSource, ownerType, clearingFirm, transactTime, userInfo, orderId, clOrdId, execId, execType, ordStatus, lastPx, lastQty, leavesQty, cumQty, side, accountId, branchId, expirationDays, expirationType, maturityDate, shareProperty }, bytes)

@[simp] theorem encode_length (message : RefinancingSecuritiesLendingNonAgreedTradeExecutionReportMessage) : (encode message).length = 181 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, ExecType.encode_length, OrdStatus.encode_length, Side.encode_length]

theorem encode_length_pos (message : RefinancingSecuritiesLendingNonAgreedTradeExecutionReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : RefinancingSecuritiesLendingNonAgreedTradeExecutionReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end RefinancingSecuritiesLendingNonAgreedTradeExecutionReportMessage

/-- Bond Spot Negotiated Trade Capture Report Message: 294 bytes -/
structure BondSpotNegotiatedTradeCaptureReportMessage where
  applId : Alpha 3
  submittingPbuid : Alpha 6
  securityId : Alpha 8
  securityIdSource : Alpha 4
  ownerType : BitVec 16
  clearingFirm : Alpha 2
  transactTime : BitVec 64
  userInfo : Alpha 32
  tradeReportId : Alpha 10
  tradeReportType : BitVec 8
  tradeReportTransType : BitVec 8
  tradeHandlingInstr : TradeHandlingInstr
  tradeReportRefId : Alpha 10
  lastPx : BitVec 64
  lastQty : BitVec 64
  trdType : BitVec 16
  trdSubType : BitVec 16
  confirmId : BitVec 32
  side : Side
  pbuid : Alpha 6
  accountId : Alpha 10
  branchId : Alpha 2
  counterpartyPbuid : Alpha 6
  counterpartyAccountId : Alpha 10
  counterpartyBranchId : Alpha 2
  memberId : Alpha 6
  traderCode : Alpha 5
  counterpartyMemberId : Alpha 6
  counterpartyTraderCode : Alpha 5
  settlType : SettlType
  settlPeriod : SettlPeriod
  cashMargin : CashMargin
  memo : Alpha 120
  deriving DecidableEq, Repr

namespace BondSpotNegotiatedTradeCaptureReportMessage

def encode (message : BondSpotNegotiatedTradeCaptureReportMessage) : List UInt8 :=
  Alpha.encode message.applId
    ++ (Alpha.encode message.submittingPbuid
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 2 message.ownerType
    ++ (Alpha.encode message.clearingFirm
    ++ (encodeUInt 8 message.transactTime
    ++ (Alpha.encode message.userInfo
    ++ (Alpha.encode message.tradeReportId
    ++ (encodeUInt 1 message.tradeReportType
    ++ (encodeUInt 1 message.tradeReportTransType
    ++ (TradeHandlingInstr.encode message.tradeHandlingInstr
    ++ (Alpha.encode message.tradeReportRefId
    ++ (encodeUInt 8 message.lastPx
    ++ (encodeUInt 8 message.lastQty
    ++ (encodeUInt 2 message.trdType
    ++ (encodeUInt 2 message.trdSubType
    ++ (encodeUInt 4 message.confirmId
    ++ (Side.encode message.side
    ++ (Alpha.encode message.pbuid
    ++ (Alpha.encode message.accountId
    ++ (Alpha.encode message.branchId
    ++ (Alpha.encode message.counterpartyPbuid
    ++ (Alpha.encode message.counterpartyAccountId
    ++ (Alpha.encode message.counterpartyBranchId
    ++ (Alpha.encode message.memberId
    ++ (Alpha.encode message.traderCode
    ++ (Alpha.encode message.counterpartyMemberId
    ++ (Alpha.encode message.counterpartyTraderCode
    ++ (SettlType.encode message.settlType
    ++ (SettlPeriod.encode message.settlPeriod
    ++ (CashMargin.encode message.cashMargin
    ++ (Alpha.encode message.memo))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (BondSpotNegotiatedTradeCaptureReportMessage × List UInt8) := do
  let (applId, bytes) ← Alpha.decode 3 bytes
  let (submittingPbuid, bytes) ← Alpha.decode 6 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (ownerType, bytes) ← decodeUInt 2 bytes
  let (clearingFirm, bytes) ← Alpha.decode 2 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  let (userInfo, bytes) ← Alpha.decode 32 bytes
  let (tradeReportId, bytes) ← Alpha.decode 10 bytes
  let (tradeReportType, bytes) ← decodeUInt 1 bytes
  let (tradeReportTransType, bytes) ← decodeUInt 1 bytes
  let (tradeHandlingInstr, bytes) ← TradeHandlingInstr.decode bytes
  let (tradeReportRefId, bytes) ← Alpha.decode 10 bytes
  let (lastPx, bytes) ← decodeUInt 8 bytes
  let (lastQty, bytes) ← decodeUInt 8 bytes
  let (trdType, bytes) ← decodeUInt 2 bytes
  let (trdSubType, bytes) ← decodeUInt 2 bytes
  let (confirmId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (pbuid, bytes) ← Alpha.decode 6 bytes
  let (accountId, bytes) ← Alpha.decode 10 bytes
  let (branchId, bytes) ← Alpha.decode 2 bytes
  let (counterpartyPbuid, bytes) ← Alpha.decode 6 bytes
  let (counterpartyAccountId, bytes) ← Alpha.decode 10 bytes
  let (counterpartyBranchId, bytes) ← Alpha.decode 2 bytes
  let (memberId, bytes) ← Alpha.decode 6 bytes
  let (traderCode, bytes) ← Alpha.decode 5 bytes
  let (counterpartyMemberId, bytes) ← Alpha.decode 6 bytes
  let (counterpartyTraderCode, bytes) ← Alpha.decode 5 bytes
  let (settlType, bytes) ← SettlType.decode bytes
  let (settlPeriod, bytes) ← SettlPeriod.decode bytes
  let (cashMargin, bytes) ← CashMargin.decode bytes
  let (memo, bytes) ← Alpha.decode 120 bytes
  pure ({ applId, submittingPbuid, securityId, securityIdSource, ownerType, clearingFirm, transactTime, userInfo, tradeReportId, tradeReportType, tradeReportTransType, tradeHandlingInstr, tradeReportRefId, lastPx, lastQty, trdType, trdSubType, confirmId, side, pbuid, accountId, branchId, counterpartyPbuid, counterpartyAccountId, counterpartyBranchId, memberId, traderCode, counterpartyMemberId, counterpartyTraderCode, settlType, settlPeriod, cashMargin, memo }, bytes)

@[simp] theorem encode_length (message : BondSpotNegotiatedTradeCaptureReportMessage) : (encode message).length = 294 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, TradeHandlingInstr.encode_length, Side.encode_length, SettlType.encode_length, SettlPeriod.encode_length, CashMargin.encode_length]

theorem encode_length_pos (message : BondSpotNegotiatedTradeCaptureReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : BondSpotNegotiatedTradeCaptureReportMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, TradeHandlingInstr.decode_encode, some_bind]
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
  rw [List.append_assoc, Side.decode_encode, some_bind]
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
  rw [List.append_assoc, SettlType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SettlPeriod.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CashMargin.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BondSpotNegotiatedTradeCaptureReportMessage

/-- Refinancing Securities Lending Agreed Trade Capture Report Message: 154 bytes -/
structure RefinancingSecuritiesLendingAgreedTradeCaptureReportMessage where
  applId : Alpha 3
  submittingPbuid : Alpha 6
  securityId : Alpha 8
  securityIdSource : Alpha 4
  ownerType : BitVec 16
  clearingFirm : Alpha 2
  transactTime : BitVec 64
  userInfo : Alpha 32
  tradeReportId : Alpha 10
  tradeReportType : BitVec 8
  tradeReportTransType : BitVec 8
  tradeHandlingInstr : TradeHandlingInstr
  tradeReportRefId : Alpha 10
  lastPx : BitVec 64
  lastQty : BitVec 64
  trdType : BitVec 16
  trdSubType : BitVec 16
  confirmId : BitVec 32
  side : Side
  pbuid : Alpha 6
  accountId : Alpha 10
  branchId : Alpha 2
  counterpartyPbuid : Alpha 6
  counterpartyAccountId : Alpha 10
  counterpartyBranchId : Alpha 2
  expirationDays : BitVec 16
  expirationType : BitVec 8
  shareProperty : Alpha 2
  deriving DecidableEq, Repr

namespace RefinancingSecuritiesLendingAgreedTradeCaptureReportMessage

def encode (message : RefinancingSecuritiesLendingAgreedTradeCaptureReportMessage) : List UInt8 :=
  Alpha.encode message.applId
    ++ (Alpha.encode message.submittingPbuid
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 2 message.ownerType
    ++ (Alpha.encode message.clearingFirm
    ++ (encodeUInt 8 message.transactTime
    ++ (Alpha.encode message.userInfo
    ++ (Alpha.encode message.tradeReportId
    ++ (encodeUInt 1 message.tradeReportType
    ++ (encodeUInt 1 message.tradeReportTransType
    ++ (TradeHandlingInstr.encode message.tradeHandlingInstr
    ++ (Alpha.encode message.tradeReportRefId
    ++ (encodeUInt 8 message.lastPx
    ++ (encodeUInt 8 message.lastQty
    ++ (encodeUInt 2 message.trdType
    ++ (encodeUInt 2 message.trdSubType
    ++ (encodeUInt 4 message.confirmId
    ++ (Side.encode message.side
    ++ (Alpha.encode message.pbuid
    ++ (Alpha.encode message.accountId
    ++ (Alpha.encode message.branchId
    ++ (Alpha.encode message.counterpartyPbuid
    ++ (Alpha.encode message.counterpartyAccountId
    ++ (Alpha.encode message.counterpartyBranchId
    ++ (encodeUInt 2 message.expirationDays
    ++ (encodeUInt 1 message.expirationType
    ++ (Alpha.encode message.shareProperty)))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (RefinancingSecuritiesLendingAgreedTradeCaptureReportMessage × List UInt8) := do
  let (applId, bytes) ← Alpha.decode 3 bytes
  let (submittingPbuid, bytes) ← Alpha.decode 6 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (ownerType, bytes) ← decodeUInt 2 bytes
  let (clearingFirm, bytes) ← Alpha.decode 2 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  let (userInfo, bytes) ← Alpha.decode 32 bytes
  let (tradeReportId, bytes) ← Alpha.decode 10 bytes
  let (tradeReportType, bytes) ← decodeUInt 1 bytes
  let (tradeReportTransType, bytes) ← decodeUInt 1 bytes
  let (tradeHandlingInstr, bytes) ← TradeHandlingInstr.decode bytes
  let (tradeReportRefId, bytes) ← Alpha.decode 10 bytes
  let (lastPx, bytes) ← decodeUInt 8 bytes
  let (lastQty, bytes) ← decodeUInt 8 bytes
  let (trdType, bytes) ← decodeUInt 2 bytes
  let (trdSubType, bytes) ← decodeUInt 2 bytes
  let (confirmId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (pbuid, bytes) ← Alpha.decode 6 bytes
  let (accountId, bytes) ← Alpha.decode 10 bytes
  let (branchId, bytes) ← Alpha.decode 2 bytes
  let (counterpartyPbuid, bytes) ← Alpha.decode 6 bytes
  let (counterpartyAccountId, bytes) ← Alpha.decode 10 bytes
  let (counterpartyBranchId, bytes) ← Alpha.decode 2 bytes
  let (expirationDays, bytes) ← decodeUInt 2 bytes
  let (expirationType, bytes) ← decodeUInt 1 bytes
  let (shareProperty, bytes) ← Alpha.decode 2 bytes
  pure ({ applId, submittingPbuid, securityId, securityIdSource, ownerType, clearingFirm, transactTime, userInfo, tradeReportId, tradeReportType, tradeReportTransType, tradeHandlingInstr, tradeReportRefId, lastPx, lastQty, trdType, trdSubType, confirmId, side, pbuid, accountId, branchId, counterpartyPbuid, counterpartyAccountId, counterpartyBranchId, expirationDays, expirationType, shareProperty }, bytes)

@[simp] theorem encode_length (message : RefinancingSecuritiesLendingAgreedTradeCaptureReportMessage) : (encode message).length = 154 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, TradeHandlingInstr.encode_length, Side.encode_length]

theorem encode_length_pos (message : RefinancingSecuritiesLendingAgreedTradeCaptureReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : RefinancingSecuritiesLendingAgreedTradeCaptureReportMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, TradeHandlingInstr.decode_encode, some_bind]
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
  rw [List.append_assoc, Side.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end RefinancingSecuritiesLendingAgreedTradeCaptureReportMessage

/-- Mutual Trade Confirmation Trade Capture Report Message: 149 bytes -/
structure MutualTradeConfirmationTradeCaptureReportMessage where
  applId : Alpha 3
  submittingPbuid : Alpha 6
  securityId : Alpha 8
  securityIdSource : Alpha 4
  ownerType : BitVec 16
  clearingFirm : Alpha 2
  transactTime : BitVec 64
  userInfo : Alpha 32
  tradeReportId : Alpha 10
  tradeReportType : BitVec 8
  tradeReportTransType : BitVec 8
  tradeHandlingInstr : TradeHandlingInstr
  tradeReportRefId : Alpha 10
  lastPx : BitVec 64
  lastQty : BitVec 64
  trdType : BitVec 16
  trdSubType : BitVec 16
  confirmId : BitVec 32
  side : Side
  pbuid : Alpha 6
  accountId : Alpha 10
  branchId : Alpha 2
  counterpartyPbuid : Alpha 6
  counterpartyAccountId : Alpha 10
  counterpartyBranchId : Alpha 2
  deriving DecidableEq, Repr

namespace MutualTradeConfirmationTradeCaptureReportMessage

def encode (message : MutualTradeConfirmationTradeCaptureReportMessage) : List UInt8 :=
  Alpha.encode message.applId
    ++ (Alpha.encode message.submittingPbuid
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 2 message.ownerType
    ++ (Alpha.encode message.clearingFirm
    ++ (encodeUInt 8 message.transactTime
    ++ (Alpha.encode message.userInfo
    ++ (Alpha.encode message.tradeReportId
    ++ (encodeUInt 1 message.tradeReportType
    ++ (encodeUInt 1 message.tradeReportTransType
    ++ (TradeHandlingInstr.encode message.tradeHandlingInstr
    ++ (Alpha.encode message.tradeReportRefId
    ++ (encodeUInt 8 message.lastPx
    ++ (encodeUInt 8 message.lastQty
    ++ (encodeUInt 2 message.trdType
    ++ (encodeUInt 2 message.trdSubType
    ++ (encodeUInt 4 message.confirmId
    ++ (Side.encode message.side
    ++ (Alpha.encode message.pbuid
    ++ (Alpha.encode message.accountId
    ++ (Alpha.encode message.branchId
    ++ (Alpha.encode message.counterpartyPbuid
    ++ (Alpha.encode message.counterpartyAccountId
    ++ (Alpha.encode message.counterpartyBranchId))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (MutualTradeConfirmationTradeCaptureReportMessage × List UInt8) := do
  let (applId, bytes) ← Alpha.decode 3 bytes
  let (submittingPbuid, bytes) ← Alpha.decode 6 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (ownerType, bytes) ← decodeUInt 2 bytes
  let (clearingFirm, bytes) ← Alpha.decode 2 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  let (userInfo, bytes) ← Alpha.decode 32 bytes
  let (tradeReportId, bytes) ← Alpha.decode 10 bytes
  let (tradeReportType, bytes) ← decodeUInt 1 bytes
  let (tradeReportTransType, bytes) ← decodeUInt 1 bytes
  let (tradeHandlingInstr, bytes) ← TradeHandlingInstr.decode bytes
  let (tradeReportRefId, bytes) ← Alpha.decode 10 bytes
  let (lastPx, bytes) ← decodeUInt 8 bytes
  let (lastQty, bytes) ← decodeUInt 8 bytes
  let (trdType, bytes) ← decodeUInt 2 bytes
  let (trdSubType, bytes) ← decodeUInt 2 bytes
  let (confirmId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (pbuid, bytes) ← Alpha.decode 6 bytes
  let (accountId, bytes) ← Alpha.decode 10 bytes
  let (branchId, bytes) ← Alpha.decode 2 bytes
  let (counterpartyPbuid, bytes) ← Alpha.decode 6 bytes
  let (counterpartyAccountId, bytes) ← Alpha.decode 10 bytes
  let (counterpartyBranchId, bytes) ← Alpha.decode 2 bytes
  pure ({ applId, submittingPbuid, securityId, securityIdSource, ownerType, clearingFirm, transactTime, userInfo, tradeReportId, tradeReportType, tradeReportTransType, tradeHandlingInstr, tradeReportRefId, lastPx, lastQty, trdType, trdSubType, confirmId, side, pbuid, accountId, branchId, counterpartyPbuid, counterpartyAccountId, counterpartyBranchId }, bytes)

@[simp] theorem encode_length (message : MutualTradeConfirmationTradeCaptureReportMessage) : (encode message).length = 149 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, TradeHandlingInstr.encode_length, Side.encode_length]

theorem encode_length_pos (message : MutualTradeConfirmationTradeCaptureReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : MutualTradeConfirmationTradeCaptureReportMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, TradeHandlingInstr.decode_encode, some_bind]
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
  rw [List.append_assoc, Side.decode_encode, some_bind]
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

end MutualTradeConfirmationTradeCaptureReportMessage

/-- Market Making Mutual Trade Confirmation Trade Capture Report Message: 149 bytes -/
structure MarketMakingMutualTradeConfirmationTradeCaptureReportMessage where
  applId : Alpha 3
  submittingPbuid : Alpha 6
  securityId : Alpha 8
  securityIdSource : Alpha 4
  ownerType : BitVec 16
  clearingFirm : Alpha 2
  transactTime : BitVec 64
  userInfo : Alpha 32
  tradeReportId : Alpha 10
  tradeReportType : BitVec 8
  tradeReportTransType : BitVec 8
  tradeHandlingInstr : TradeHandlingInstr
  tradeReportRefId : Alpha 10
  lastPx : BitVec 64
  lastQty : BitVec 64
  trdType : BitVec 16
  trdSubType : BitVec 16
  confirmId : BitVec 32
  side : Side
  pbuid : Alpha 6
  accountId : Alpha 10
  branchId : Alpha 2
  counterpartyPbuid : Alpha 6
  counterpartyAccountId : Alpha 10
  counterpartyBranchId : Alpha 2
  deriving DecidableEq, Repr

namespace MarketMakingMutualTradeConfirmationTradeCaptureReportMessage

def encode (message : MarketMakingMutualTradeConfirmationTradeCaptureReportMessage) : List UInt8 :=
  Alpha.encode message.applId
    ++ (Alpha.encode message.submittingPbuid
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 2 message.ownerType
    ++ (Alpha.encode message.clearingFirm
    ++ (encodeUInt 8 message.transactTime
    ++ (Alpha.encode message.userInfo
    ++ (Alpha.encode message.tradeReportId
    ++ (encodeUInt 1 message.tradeReportType
    ++ (encodeUInt 1 message.tradeReportTransType
    ++ (TradeHandlingInstr.encode message.tradeHandlingInstr
    ++ (Alpha.encode message.tradeReportRefId
    ++ (encodeUInt 8 message.lastPx
    ++ (encodeUInt 8 message.lastQty
    ++ (encodeUInt 2 message.trdType
    ++ (encodeUInt 2 message.trdSubType
    ++ (encodeUInt 4 message.confirmId
    ++ (Side.encode message.side
    ++ (Alpha.encode message.pbuid
    ++ (Alpha.encode message.accountId
    ++ (Alpha.encode message.branchId
    ++ (Alpha.encode message.counterpartyPbuid
    ++ (Alpha.encode message.counterpartyAccountId
    ++ (Alpha.encode message.counterpartyBranchId))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (MarketMakingMutualTradeConfirmationTradeCaptureReportMessage × List UInt8) := do
  let (applId, bytes) ← Alpha.decode 3 bytes
  let (submittingPbuid, bytes) ← Alpha.decode 6 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (ownerType, bytes) ← decodeUInt 2 bytes
  let (clearingFirm, bytes) ← Alpha.decode 2 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  let (userInfo, bytes) ← Alpha.decode 32 bytes
  let (tradeReportId, bytes) ← Alpha.decode 10 bytes
  let (tradeReportType, bytes) ← decodeUInt 1 bytes
  let (tradeReportTransType, bytes) ← decodeUInt 1 bytes
  let (tradeHandlingInstr, bytes) ← TradeHandlingInstr.decode bytes
  let (tradeReportRefId, bytes) ← Alpha.decode 10 bytes
  let (lastPx, bytes) ← decodeUInt 8 bytes
  let (lastQty, bytes) ← decodeUInt 8 bytes
  let (trdType, bytes) ← decodeUInt 2 bytes
  let (trdSubType, bytes) ← decodeUInt 2 bytes
  let (confirmId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (pbuid, bytes) ← Alpha.decode 6 bytes
  let (accountId, bytes) ← Alpha.decode 10 bytes
  let (branchId, bytes) ← Alpha.decode 2 bytes
  let (counterpartyPbuid, bytes) ← Alpha.decode 6 bytes
  let (counterpartyAccountId, bytes) ← Alpha.decode 10 bytes
  let (counterpartyBranchId, bytes) ← Alpha.decode 2 bytes
  pure ({ applId, submittingPbuid, securityId, securityIdSource, ownerType, clearingFirm, transactTime, userInfo, tradeReportId, tradeReportType, tradeReportTransType, tradeHandlingInstr, tradeReportRefId, lastPx, lastQty, trdType, trdSubType, confirmId, side, pbuid, accountId, branchId, counterpartyPbuid, counterpartyAccountId, counterpartyBranchId }, bytes)

@[simp] theorem encode_length (message : MarketMakingMutualTradeConfirmationTradeCaptureReportMessage) : (encode message).length = 149 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, TradeHandlingInstr.encode_length, Side.encode_length]

theorem encode_length_pos (message : MarketMakingMutualTradeConfirmationTradeCaptureReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : MarketMakingMutualTradeConfirmationTradeCaptureReportMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, TradeHandlingInstr.decode_encode, some_bind]
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
  rw [List.append_assoc, Side.decode_encode, some_bind]
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

end MarketMakingMutualTradeConfirmationTradeCaptureReportMessage

/-- After Hours Block Trade Trade Capture Report Message: 150 bytes -/
structure AfterHoursBlockTradeTradeCaptureReportMessage where
  applId : Alpha 3
  submittingPbuid : Alpha 6
  securityId : Alpha 8
  securityIdSource : Alpha 4
  ownerType : BitVec 16
  clearingFirm : Alpha 2
  transactTime : BitVec 64
  userInfo : Alpha 32
  tradeReportId : Alpha 10
  tradeReportType : BitVec 8
  tradeReportTransType : BitVec 8
  tradeHandlingInstr : TradeHandlingInstr
  tradeReportRefId : Alpha 10
  lastPx : BitVec 64
  lastQty : BitVec 64
  trdType : BitVec 16
  trdSubType : BitVec 16
  confirmId : BitVec 32
  side : Side
  pbuid : Alpha 6
  accountId : Alpha 10
  branchId : Alpha 2
  counterpartyPbuid : Alpha 6
  counterpartyAccountId : Alpha 10
  counterpartyBranchId : Alpha 2
  cashMargin : CashMargin
  deriving DecidableEq, Repr

namespace AfterHoursBlockTradeTradeCaptureReportMessage

def encode (message : AfterHoursBlockTradeTradeCaptureReportMessage) : List UInt8 :=
  Alpha.encode message.applId
    ++ (Alpha.encode message.submittingPbuid
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 2 message.ownerType
    ++ (Alpha.encode message.clearingFirm
    ++ (encodeUInt 8 message.transactTime
    ++ (Alpha.encode message.userInfo
    ++ (Alpha.encode message.tradeReportId
    ++ (encodeUInt 1 message.tradeReportType
    ++ (encodeUInt 1 message.tradeReportTransType
    ++ (TradeHandlingInstr.encode message.tradeHandlingInstr
    ++ (Alpha.encode message.tradeReportRefId
    ++ (encodeUInt 8 message.lastPx
    ++ (encodeUInt 8 message.lastQty
    ++ (encodeUInt 2 message.trdType
    ++ (encodeUInt 2 message.trdSubType
    ++ (encodeUInt 4 message.confirmId
    ++ (Side.encode message.side
    ++ (Alpha.encode message.pbuid
    ++ (Alpha.encode message.accountId
    ++ (Alpha.encode message.branchId
    ++ (Alpha.encode message.counterpartyPbuid
    ++ (Alpha.encode message.counterpartyAccountId
    ++ (Alpha.encode message.counterpartyBranchId
    ++ (CashMargin.encode message.cashMargin)))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (AfterHoursBlockTradeTradeCaptureReportMessage × List UInt8) := do
  let (applId, bytes) ← Alpha.decode 3 bytes
  let (submittingPbuid, bytes) ← Alpha.decode 6 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (ownerType, bytes) ← decodeUInt 2 bytes
  let (clearingFirm, bytes) ← Alpha.decode 2 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  let (userInfo, bytes) ← Alpha.decode 32 bytes
  let (tradeReportId, bytes) ← Alpha.decode 10 bytes
  let (tradeReportType, bytes) ← decodeUInt 1 bytes
  let (tradeReportTransType, bytes) ← decodeUInt 1 bytes
  let (tradeHandlingInstr, bytes) ← TradeHandlingInstr.decode bytes
  let (tradeReportRefId, bytes) ← Alpha.decode 10 bytes
  let (lastPx, bytes) ← decodeUInt 8 bytes
  let (lastQty, bytes) ← decodeUInt 8 bytes
  let (trdType, bytes) ← decodeUInt 2 bytes
  let (trdSubType, bytes) ← decodeUInt 2 bytes
  let (confirmId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (pbuid, bytes) ← Alpha.decode 6 bytes
  let (accountId, bytes) ← Alpha.decode 10 bytes
  let (branchId, bytes) ← Alpha.decode 2 bytes
  let (counterpartyPbuid, bytes) ← Alpha.decode 6 bytes
  let (counterpartyAccountId, bytes) ← Alpha.decode 10 bytes
  let (counterpartyBranchId, bytes) ← Alpha.decode 2 bytes
  let (cashMargin, bytes) ← CashMargin.decode bytes
  pure ({ applId, submittingPbuid, securityId, securityIdSource, ownerType, clearingFirm, transactTime, userInfo, tradeReportId, tradeReportType, tradeReportTransType, tradeHandlingInstr, tradeReportRefId, lastPx, lastQty, trdType, trdSubType, confirmId, side, pbuid, accountId, branchId, counterpartyPbuid, counterpartyAccountId, counterpartyBranchId, cashMargin }, bytes)

@[simp] theorem encode_length (message : AfterHoursBlockTradeTradeCaptureReportMessage) : (encode message).length = 150 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, TradeHandlingInstr.encode_length, Side.encode_length, CashMargin.encode_length]

theorem encode_length_pos (message : AfterHoursBlockTradeTradeCaptureReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : AfterHoursBlockTradeTradeCaptureReportMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, TradeHandlingInstr.decode_encode, some_bind]
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
  rw [List.append_assoc, Side.decode_encode, some_bind]
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
  rw [CashMargin.decode_encode, some_bind]
  rfl

end AfterHoursBlockTradeTradeCaptureReportMessage

/-- Bond Spot Negotiated Trade Capture Report Ack Message: 348 bytes -/
structure BondSpotNegotiatedTradeCaptureReportAckMessage where
  partitionNo : BitVec 32
  reportIndex : BitVec 64
  applId : Alpha 3
  reportingPbuid : Alpha 6
  submittingPbuid : Alpha 6
  securityId : Alpha 8
  securityIdSource : Alpha 4
  ownerType : BitVec 16
  clearingFirm : Alpha 2
  transactTime : BitVec 64
  userInfo : Alpha 32
  tradeId : Alpha 16
  tradeReportId : Alpha 10
  tradeReportType : BitVec 8
  tradeReportTransType : BitVec 8
  tradeHandlingInstr : TradeHandlingInstr
  tradeReportRefId : Alpha 10
  trdAckStatus : BitVec 8
  trdRptStatus : BitVec 8
  tradeReportRejectReason : BitVec 16
  lastPx : BitVec 64
  lastQty : BitVec 64
  trdType : BitVec 16
  trdSubType : BitVec 16
  confirmId : BitVec 32
  execId : Alpha 16
  side : Side
  pbuid : Alpha 6
  accountId : Alpha 10
  branchId : Alpha 2
  counterpartyPbuid : Alpha 6
  counterpartyAccountId : Alpha 10
  counterpartyBranchId : Alpha 2
  memberId : Alpha 6
  traderCode : Alpha 5
  counterpartyMemberId : Alpha 6
  counterpartyTraderCode : Alpha 5
  settlType : SettlType
  settlPeriod : SettlPeriod
  cashMargin : CashMargin
  memo : Alpha 120
  deriving DecidableEq, Repr

namespace BondSpotNegotiatedTradeCaptureReportAckMessage

def encode (message : BondSpotNegotiatedTradeCaptureReportAckMessage) : List UInt8 :=
  encodeUInt 4 message.partitionNo
    ++ (encodeUInt 8 message.reportIndex
    ++ (Alpha.encode message.applId
    ++ (Alpha.encode message.reportingPbuid
    ++ (Alpha.encode message.submittingPbuid
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 2 message.ownerType
    ++ (Alpha.encode message.clearingFirm
    ++ (encodeUInt 8 message.transactTime
    ++ (Alpha.encode message.userInfo
    ++ (Alpha.encode message.tradeId
    ++ (Alpha.encode message.tradeReportId
    ++ (encodeUInt 1 message.tradeReportType
    ++ (encodeUInt 1 message.tradeReportTransType
    ++ (TradeHandlingInstr.encode message.tradeHandlingInstr
    ++ (Alpha.encode message.tradeReportRefId
    ++ (encodeUInt 1 message.trdAckStatus
    ++ (encodeUInt 1 message.trdRptStatus
    ++ (encodeUInt 2 message.tradeReportRejectReason
    ++ (encodeUInt 8 message.lastPx
    ++ (encodeUInt 8 message.lastQty
    ++ (encodeUInt 2 message.trdType
    ++ (encodeUInt 2 message.trdSubType
    ++ (encodeUInt 4 message.confirmId
    ++ (Alpha.encode message.execId
    ++ (Side.encode message.side
    ++ (Alpha.encode message.pbuid
    ++ (Alpha.encode message.accountId
    ++ (Alpha.encode message.branchId
    ++ (Alpha.encode message.counterpartyPbuid
    ++ (Alpha.encode message.counterpartyAccountId
    ++ (Alpha.encode message.counterpartyBranchId
    ++ (Alpha.encode message.memberId
    ++ (Alpha.encode message.traderCode
    ++ (Alpha.encode message.counterpartyMemberId
    ++ (Alpha.encode message.counterpartyTraderCode
    ++ (SettlType.encode message.settlType
    ++ (SettlPeriod.encode message.settlPeriod
    ++ (CashMargin.encode message.cashMargin
    ++ (Alpha.encode message.memo))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (BondSpotNegotiatedTradeCaptureReportAckMessage × List UInt8) := do
  let (partitionNo, bytes) ← decodeUInt 4 bytes
  let (reportIndex, bytes) ← decodeUInt 8 bytes
  let (applId, bytes) ← Alpha.decode 3 bytes
  let (reportingPbuid, bytes) ← Alpha.decode 6 bytes
  let (submittingPbuid, bytes) ← Alpha.decode 6 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (ownerType, bytes) ← decodeUInt 2 bytes
  let (clearingFirm, bytes) ← Alpha.decode 2 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  let (userInfo, bytes) ← Alpha.decode 32 bytes
  let (tradeId, bytes) ← Alpha.decode 16 bytes
  let (tradeReportId, bytes) ← Alpha.decode 10 bytes
  let (tradeReportType, bytes) ← decodeUInt 1 bytes
  let (tradeReportTransType, bytes) ← decodeUInt 1 bytes
  let (tradeHandlingInstr, bytes) ← TradeHandlingInstr.decode bytes
  let (tradeReportRefId, bytes) ← Alpha.decode 10 bytes
  let (trdAckStatus, bytes) ← decodeUInt 1 bytes
  let (trdRptStatus, bytes) ← decodeUInt 1 bytes
  let (tradeReportRejectReason, bytes) ← decodeUInt 2 bytes
  let (lastPx, bytes) ← decodeUInt 8 bytes
  let (lastQty, bytes) ← decodeUInt 8 bytes
  let (trdType, bytes) ← decodeUInt 2 bytes
  let (trdSubType, bytes) ← decodeUInt 2 bytes
  let (confirmId, bytes) ← decodeUInt 4 bytes
  let (execId, bytes) ← Alpha.decode 16 bytes
  let (side, bytes) ← Side.decode bytes
  let (pbuid, bytes) ← Alpha.decode 6 bytes
  let (accountId, bytes) ← Alpha.decode 10 bytes
  let (branchId, bytes) ← Alpha.decode 2 bytes
  let (counterpartyPbuid, bytes) ← Alpha.decode 6 bytes
  let (counterpartyAccountId, bytes) ← Alpha.decode 10 bytes
  let (counterpartyBranchId, bytes) ← Alpha.decode 2 bytes
  let (memberId, bytes) ← Alpha.decode 6 bytes
  let (traderCode, bytes) ← Alpha.decode 5 bytes
  let (counterpartyMemberId, bytes) ← Alpha.decode 6 bytes
  let (counterpartyTraderCode, bytes) ← Alpha.decode 5 bytes
  let (settlType, bytes) ← SettlType.decode bytes
  let (settlPeriod, bytes) ← SettlPeriod.decode bytes
  let (cashMargin, bytes) ← CashMargin.decode bytes
  let (memo, bytes) ← Alpha.decode 120 bytes
  pure ({ partitionNo, reportIndex, applId, reportingPbuid, submittingPbuid, securityId, securityIdSource, ownerType, clearingFirm, transactTime, userInfo, tradeId, tradeReportId, tradeReportType, tradeReportTransType, tradeHandlingInstr, tradeReportRefId, trdAckStatus, trdRptStatus, tradeReportRejectReason, lastPx, lastQty, trdType, trdSubType, confirmId, execId, side, pbuid, accountId, branchId, counterpartyPbuid, counterpartyAccountId, counterpartyBranchId, memberId, traderCode, counterpartyMemberId, counterpartyTraderCode, settlType, settlPeriod, cashMargin, memo }, bytes)

@[simp] theorem encode_length (message : BondSpotNegotiatedTradeCaptureReportAckMessage) : (encode message).length = 348 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, TradeHandlingInstr.encode_length, Side.encode_length, SettlType.encode_length, SettlPeriod.encode_length, CashMargin.encode_length]

theorem encode_length_pos (message : BondSpotNegotiatedTradeCaptureReportAckMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : BondSpotNegotiatedTradeCaptureReportAckMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TradeHandlingInstr.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
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
  rw [List.append_assoc, SettlType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SettlPeriod.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CashMargin.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BondSpotNegotiatedTradeCaptureReportAckMessage

/-- Refinancing Securities Lending Agreed Trade Capture Report Ack Message: 208 bytes -/
structure RefinancingSecuritiesLendingAgreedTradeCaptureReportAckMessage where
  partitionNo : BitVec 32
  reportIndex : BitVec 64
  applId : Alpha 3
  reportingPbuid : Alpha 6
  submittingPbuid : Alpha 6
  securityId : Alpha 8
  securityIdSource : Alpha 4
  ownerType : BitVec 16
  clearingFirm : Alpha 2
  transactTime : BitVec 64
  userInfo : Alpha 32
  tradeId : Alpha 16
  tradeReportId : Alpha 10
  tradeReportType : BitVec 8
  tradeReportTransType : BitVec 8
  tradeHandlingInstr : TradeHandlingInstr
  tradeReportRefId : Alpha 10
  trdAckStatus : BitVec 8
  trdRptStatus : BitVec 8
  tradeReportRejectReason : BitVec 16
  lastPx : BitVec 64
  lastQty : BitVec 64
  trdType : BitVec 16
  trdSubType : BitVec 16
  confirmId : BitVec 32
  execId : Alpha 16
  side : Side
  pbuid : Alpha 6
  accountId : Alpha 10
  branchId : Alpha 2
  counterpartyPbuid : Alpha 6
  counterpartyAccountId : Alpha 10
  counterpartyBranchId : Alpha 2
  expirationDays : BitVec 16
  expirationType : BitVec 8
  shareProperty : Alpha 2
  deriving DecidableEq, Repr

namespace RefinancingSecuritiesLendingAgreedTradeCaptureReportAckMessage

def encode (message : RefinancingSecuritiesLendingAgreedTradeCaptureReportAckMessage) : List UInt8 :=
  encodeUInt 4 message.partitionNo
    ++ (encodeUInt 8 message.reportIndex
    ++ (Alpha.encode message.applId
    ++ (Alpha.encode message.reportingPbuid
    ++ (Alpha.encode message.submittingPbuid
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 2 message.ownerType
    ++ (Alpha.encode message.clearingFirm
    ++ (encodeUInt 8 message.transactTime
    ++ (Alpha.encode message.userInfo
    ++ (Alpha.encode message.tradeId
    ++ (Alpha.encode message.tradeReportId
    ++ (encodeUInt 1 message.tradeReportType
    ++ (encodeUInt 1 message.tradeReportTransType
    ++ (TradeHandlingInstr.encode message.tradeHandlingInstr
    ++ (Alpha.encode message.tradeReportRefId
    ++ (encodeUInt 1 message.trdAckStatus
    ++ (encodeUInt 1 message.trdRptStatus
    ++ (encodeUInt 2 message.tradeReportRejectReason
    ++ (encodeUInt 8 message.lastPx
    ++ (encodeUInt 8 message.lastQty
    ++ (encodeUInt 2 message.trdType
    ++ (encodeUInt 2 message.trdSubType
    ++ (encodeUInt 4 message.confirmId
    ++ (Alpha.encode message.execId
    ++ (Side.encode message.side
    ++ (Alpha.encode message.pbuid
    ++ (Alpha.encode message.accountId
    ++ (Alpha.encode message.branchId
    ++ (Alpha.encode message.counterpartyPbuid
    ++ (Alpha.encode message.counterpartyAccountId
    ++ (Alpha.encode message.counterpartyBranchId
    ++ (encodeUInt 2 message.expirationDays
    ++ (encodeUInt 1 message.expirationType
    ++ (Alpha.encode message.shareProperty)))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (RefinancingSecuritiesLendingAgreedTradeCaptureReportAckMessage × List UInt8) := do
  let (partitionNo, bytes) ← decodeUInt 4 bytes
  let (reportIndex, bytes) ← decodeUInt 8 bytes
  let (applId, bytes) ← Alpha.decode 3 bytes
  let (reportingPbuid, bytes) ← Alpha.decode 6 bytes
  let (submittingPbuid, bytes) ← Alpha.decode 6 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (ownerType, bytes) ← decodeUInt 2 bytes
  let (clearingFirm, bytes) ← Alpha.decode 2 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  let (userInfo, bytes) ← Alpha.decode 32 bytes
  let (tradeId, bytes) ← Alpha.decode 16 bytes
  let (tradeReportId, bytes) ← Alpha.decode 10 bytes
  let (tradeReportType, bytes) ← decodeUInt 1 bytes
  let (tradeReportTransType, bytes) ← decodeUInt 1 bytes
  let (tradeHandlingInstr, bytes) ← TradeHandlingInstr.decode bytes
  let (tradeReportRefId, bytes) ← Alpha.decode 10 bytes
  let (trdAckStatus, bytes) ← decodeUInt 1 bytes
  let (trdRptStatus, bytes) ← decodeUInt 1 bytes
  let (tradeReportRejectReason, bytes) ← decodeUInt 2 bytes
  let (lastPx, bytes) ← decodeUInt 8 bytes
  let (lastQty, bytes) ← decodeUInt 8 bytes
  let (trdType, bytes) ← decodeUInt 2 bytes
  let (trdSubType, bytes) ← decodeUInt 2 bytes
  let (confirmId, bytes) ← decodeUInt 4 bytes
  let (execId, bytes) ← Alpha.decode 16 bytes
  let (side, bytes) ← Side.decode bytes
  let (pbuid, bytes) ← Alpha.decode 6 bytes
  let (accountId, bytes) ← Alpha.decode 10 bytes
  let (branchId, bytes) ← Alpha.decode 2 bytes
  let (counterpartyPbuid, bytes) ← Alpha.decode 6 bytes
  let (counterpartyAccountId, bytes) ← Alpha.decode 10 bytes
  let (counterpartyBranchId, bytes) ← Alpha.decode 2 bytes
  let (expirationDays, bytes) ← decodeUInt 2 bytes
  let (expirationType, bytes) ← decodeUInt 1 bytes
  let (shareProperty, bytes) ← Alpha.decode 2 bytes
  pure ({ partitionNo, reportIndex, applId, reportingPbuid, submittingPbuid, securityId, securityIdSource, ownerType, clearingFirm, transactTime, userInfo, tradeId, tradeReportId, tradeReportType, tradeReportTransType, tradeHandlingInstr, tradeReportRefId, trdAckStatus, trdRptStatus, tradeReportRejectReason, lastPx, lastQty, trdType, trdSubType, confirmId, execId, side, pbuid, accountId, branchId, counterpartyPbuid, counterpartyAccountId, counterpartyBranchId, expirationDays, expirationType, shareProperty }, bytes)

@[simp] theorem encode_length (message : RefinancingSecuritiesLendingAgreedTradeCaptureReportAckMessage) : (encode message).length = 208 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, TradeHandlingInstr.encode_length, Side.encode_length]

theorem encode_length_pos (message : RefinancingSecuritiesLendingAgreedTradeCaptureReportAckMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : RefinancingSecuritiesLendingAgreedTradeCaptureReportAckMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TradeHandlingInstr.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end RefinancingSecuritiesLendingAgreedTradeCaptureReportAckMessage

/-- Mutual Trade Confirmation Trade Capture Report Ack Message: 203 bytes -/
structure MutualTradeConfirmationTradeCaptureReportAckMessage where
  partitionNo : BitVec 32
  reportIndex : BitVec 64
  applId : Alpha 3
  reportingPbuid : Alpha 6
  submittingPbuid : Alpha 6
  securityId : Alpha 8
  securityIdSource : Alpha 4
  ownerType : BitVec 16
  clearingFirm : Alpha 2
  transactTime : BitVec 64
  userInfo : Alpha 32
  tradeId : Alpha 16
  tradeReportId : Alpha 10
  tradeReportType : BitVec 8
  tradeReportTransType : BitVec 8
  tradeHandlingInstr : TradeHandlingInstr
  tradeReportRefId : Alpha 10
  trdAckStatus : BitVec 8
  trdRptStatus : BitVec 8
  tradeReportRejectReason : BitVec 16
  lastPx : BitVec 64
  lastQty : BitVec 64
  trdType : BitVec 16
  trdSubType : BitVec 16
  confirmId : BitVec 32
  execId : Alpha 16
  side : Side
  pbuid : Alpha 6
  accountId : Alpha 10
  branchId : Alpha 2
  counterpartyPbuid : Alpha 6
  counterpartyAccountId : Alpha 10
  counterpartyBranchId : Alpha 2
  deriving DecidableEq, Repr

namespace MutualTradeConfirmationTradeCaptureReportAckMessage

def encode (message : MutualTradeConfirmationTradeCaptureReportAckMessage) : List UInt8 :=
  encodeUInt 4 message.partitionNo
    ++ (encodeUInt 8 message.reportIndex
    ++ (Alpha.encode message.applId
    ++ (Alpha.encode message.reportingPbuid
    ++ (Alpha.encode message.submittingPbuid
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 2 message.ownerType
    ++ (Alpha.encode message.clearingFirm
    ++ (encodeUInt 8 message.transactTime
    ++ (Alpha.encode message.userInfo
    ++ (Alpha.encode message.tradeId
    ++ (Alpha.encode message.tradeReportId
    ++ (encodeUInt 1 message.tradeReportType
    ++ (encodeUInt 1 message.tradeReportTransType
    ++ (TradeHandlingInstr.encode message.tradeHandlingInstr
    ++ (Alpha.encode message.tradeReportRefId
    ++ (encodeUInt 1 message.trdAckStatus
    ++ (encodeUInt 1 message.trdRptStatus
    ++ (encodeUInt 2 message.tradeReportRejectReason
    ++ (encodeUInt 8 message.lastPx
    ++ (encodeUInt 8 message.lastQty
    ++ (encodeUInt 2 message.trdType
    ++ (encodeUInt 2 message.trdSubType
    ++ (encodeUInt 4 message.confirmId
    ++ (Alpha.encode message.execId
    ++ (Side.encode message.side
    ++ (Alpha.encode message.pbuid
    ++ (Alpha.encode message.accountId
    ++ (Alpha.encode message.branchId
    ++ (Alpha.encode message.counterpartyPbuid
    ++ (Alpha.encode message.counterpartyAccountId
    ++ (Alpha.encode message.counterpartyBranchId))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (MutualTradeConfirmationTradeCaptureReportAckMessage × List UInt8) := do
  let (partitionNo, bytes) ← decodeUInt 4 bytes
  let (reportIndex, bytes) ← decodeUInt 8 bytes
  let (applId, bytes) ← Alpha.decode 3 bytes
  let (reportingPbuid, bytes) ← Alpha.decode 6 bytes
  let (submittingPbuid, bytes) ← Alpha.decode 6 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (ownerType, bytes) ← decodeUInt 2 bytes
  let (clearingFirm, bytes) ← Alpha.decode 2 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  let (userInfo, bytes) ← Alpha.decode 32 bytes
  let (tradeId, bytes) ← Alpha.decode 16 bytes
  let (tradeReportId, bytes) ← Alpha.decode 10 bytes
  let (tradeReportType, bytes) ← decodeUInt 1 bytes
  let (tradeReportTransType, bytes) ← decodeUInt 1 bytes
  let (tradeHandlingInstr, bytes) ← TradeHandlingInstr.decode bytes
  let (tradeReportRefId, bytes) ← Alpha.decode 10 bytes
  let (trdAckStatus, bytes) ← decodeUInt 1 bytes
  let (trdRptStatus, bytes) ← decodeUInt 1 bytes
  let (tradeReportRejectReason, bytes) ← decodeUInt 2 bytes
  let (lastPx, bytes) ← decodeUInt 8 bytes
  let (lastQty, bytes) ← decodeUInt 8 bytes
  let (trdType, bytes) ← decodeUInt 2 bytes
  let (trdSubType, bytes) ← decodeUInt 2 bytes
  let (confirmId, bytes) ← decodeUInt 4 bytes
  let (execId, bytes) ← Alpha.decode 16 bytes
  let (side, bytes) ← Side.decode bytes
  let (pbuid, bytes) ← Alpha.decode 6 bytes
  let (accountId, bytes) ← Alpha.decode 10 bytes
  let (branchId, bytes) ← Alpha.decode 2 bytes
  let (counterpartyPbuid, bytes) ← Alpha.decode 6 bytes
  let (counterpartyAccountId, bytes) ← Alpha.decode 10 bytes
  let (counterpartyBranchId, bytes) ← Alpha.decode 2 bytes
  pure ({ partitionNo, reportIndex, applId, reportingPbuid, submittingPbuid, securityId, securityIdSource, ownerType, clearingFirm, transactTime, userInfo, tradeId, tradeReportId, tradeReportType, tradeReportTransType, tradeHandlingInstr, tradeReportRefId, trdAckStatus, trdRptStatus, tradeReportRejectReason, lastPx, lastQty, trdType, trdSubType, confirmId, execId, side, pbuid, accountId, branchId, counterpartyPbuid, counterpartyAccountId, counterpartyBranchId }, bytes)

@[simp] theorem encode_length (message : MutualTradeConfirmationTradeCaptureReportAckMessage) : (encode message).length = 203 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, TradeHandlingInstr.encode_length, Side.encode_length]

theorem encode_length_pos (message : MutualTradeConfirmationTradeCaptureReportAckMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : MutualTradeConfirmationTradeCaptureReportAckMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TradeHandlingInstr.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
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

end MutualTradeConfirmationTradeCaptureReportAckMessage

/-- Market Making Mutual Trade Confirmation Trade Capture Report Ack Message: 203 bytes -/
structure MarketMakingMutualTradeConfirmationTradeCaptureReportAckMessage where
  partitionNo : BitVec 32
  reportIndex : BitVec 64
  applId : Alpha 3
  reportingPbuid : Alpha 6
  submittingPbuid : Alpha 6
  securityId : Alpha 8
  securityIdSource : Alpha 4
  ownerType : BitVec 16
  clearingFirm : Alpha 2
  transactTime : BitVec 64
  userInfo : Alpha 32
  tradeId : Alpha 16
  tradeReportId : Alpha 10
  tradeReportType : BitVec 8
  tradeReportTransType : BitVec 8
  tradeHandlingInstr : TradeHandlingInstr
  tradeReportRefId : Alpha 10
  trdAckStatus : BitVec 8
  trdRptStatus : BitVec 8
  tradeReportRejectReason : BitVec 16
  lastPx : BitVec 64
  lastQty : BitVec 64
  trdType : BitVec 16
  trdSubType : BitVec 16
  confirmId : BitVec 32
  execId : Alpha 16
  side : Side
  pbuid : Alpha 6
  accountId : Alpha 10
  branchId : Alpha 2
  counterpartyPbuid : Alpha 6
  counterpartyAccountId : Alpha 10
  counterpartyBranchId : Alpha 2
  deriving DecidableEq, Repr

namespace MarketMakingMutualTradeConfirmationTradeCaptureReportAckMessage

def encode (message : MarketMakingMutualTradeConfirmationTradeCaptureReportAckMessage) : List UInt8 :=
  encodeUInt 4 message.partitionNo
    ++ (encodeUInt 8 message.reportIndex
    ++ (Alpha.encode message.applId
    ++ (Alpha.encode message.reportingPbuid
    ++ (Alpha.encode message.submittingPbuid
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 2 message.ownerType
    ++ (Alpha.encode message.clearingFirm
    ++ (encodeUInt 8 message.transactTime
    ++ (Alpha.encode message.userInfo
    ++ (Alpha.encode message.tradeId
    ++ (Alpha.encode message.tradeReportId
    ++ (encodeUInt 1 message.tradeReportType
    ++ (encodeUInt 1 message.tradeReportTransType
    ++ (TradeHandlingInstr.encode message.tradeHandlingInstr
    ++ (Alpha.encode message.tradeReportRefId
    ++ (encodeUInt 1 message.trdAckStatus
    ++ (encodeUInt 1 message.trdRptStatus
    ++ (encodeUInt 2 message.tradeReportRejectReason
    ++ (encodeUInt 8 message.lastPx
    ++ (encodeUInt 8 message.lastQty
    ++ (encodeUInt 2 message.trdType
    ++ (encodeUInt 2 message.trdSubType
    ++ (encodeUInt 4 message.confirmId
    ++ (Alpha.encode message.execId
    ++ (Side.encode message.side
    ++ (Alpha.encode message.pbuid
    ++ (Alpha.encode message.accountId
    ++ (Alpha.encode message.branchId
    ++ (Alpha.encode message.counterpartyPbuid
    ++ (Alpha.encode message.counterpartyAccountId
    ++ (Alpha.encode message.counterpartyBranchId))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (MarketMakingMutualTradeConfirmationTradeCaptureReportAckMessage × List UInt8) := do
  let (partitionNo, bytes) ← decodeUInt 4 bytes
  let (reportIndex, bytes) ← decodeUInt 8 bytes
  let (applId, bytes) ← Alpha.decode 3 bytes
  let (reportingPbuid, bytes) ← Alpha.decode 6 bytes
  let (submittingPbuid, bytes) ← Alpha.decode 6 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (ownerType, bytes) ← decodeUInt 2 bytes
  let (clearingFirm, bytes) ← Alpha.decode 2 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  let (userInfo, bytes) ← Alpha.decode 32 bytes
  let (tradeId, bytes) ← Alpha.decode 16 bytes
  let (tradeReportId, bytes) ← Alpha.decode 10 bytes
  let (tradeReportType, bytes) ← decodeUInt 1 bytes
  let (tradeReportTransType, bytes) ← decodeUInt 1 bytes
  let (tradeHandlingInstr, bytes) ← TradeHandlingInstr.decode bytes
  let (tradeReportRefId, bytes) ← Alpha.decode 10 bytes
  let (trdAckStatus, bytes) ← decodeUInt 1 bytes
  let (trdRptStatus, bytes) ← decodeUInt 1 bytes
  let (tradeReportRejectReason, bytes) ← decodeUInt 2 bytes
  let (lastPx, bytes) ← decodeUInt 8 bytes
  let (lastQty, bytes) ← decodeUInt 8 bytes
  let (trdType, bytes) ← decodeUInt 2 bytes
  let (trdSubType, bytes) ← decodeUInt 2 bytes
  let (confirmId, bytes) ← decodeUInt 4 bytes
  let (execId, bytes) ← Alpha.decode 16 bytes
  let (side, bytes) ← Side.decode bytes
  let (pbuid, bytes) ← Alpha.decode 6 bytes
  let (accountId, bytes) ← Alpha.decode 10 bytes
  let (branchId, bytes) ← Alpha.decode 2 bytes
  let (counterpartyPbuid, bytes) ← Alpha.decode 6 bytes
  let (counterpartyAccountId, bytes) ← Alpha.decode 10 bytes
  let (counterpartyBranchId, bytes) ← Alpha.decode 2 bytes
  pure ({ partitionNo, reportIndex, applId, reportingPbuid, submittingPbuid, securityId, securityIdSource, ownerType, clearingFirm, transactTime, userInfo, tradeId, tradeReportId, tradeReportType, tradeReportTransType, tradeHandlingInstr, tradeReportRefId, trdAckStatus, trdRptStatus, tradeReportRejectReason, lastPx, lastQty, trdType, trdSubType, confirmId, execId, side, pbuid, accountId, branchId, counterpartyPbuid, counterpartyAccountId, counterpartyBranchId }, bytes)

@[simp] theorem encode_length (message : MarketMakingMutualTradeConfirmationTradeCaptureReportAckMessage) : (encode message).length = 203 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, TradeHandlingInstr.encode_length, Side.encode_length]

theorem encode_length_pos (message : MarketMakingMutualTradeConfirmationTradeCaptureReportAckMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : MarketMakingMutualTradeConfirmationTradeCaptureReportAckMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TradeHandlingInstr.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
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

end MarketMakingMutualTradeConfirmationTradeCaptureReportAckMessage

/-- After Hours Block Trade Trade Capture Report Ack Message: 204 bytes -/
structure AfterHoursBlockTradeTradeCaptureReportAckMessage where
  partitionNo : BitVec 32
  reportIndex : BitVec 64
  applId : Alpha 3
  reportingPbuid : Alpha 6
  submittingPbuid : Alpha 6
  securityId : Alpha 8
  securityIdSource : Alpha 4
  ownerType : BitVec 16
  clearingFirm : Alpha 2
  transactTime : BitVec 64
  userInfo : Alpha 32
  tradeId : Alpha 16
  tradeReportId : Alpha 10
  tradeReportType : BitVec 8
  tradeReportTransType : BitVec 8
  tradeHandlingInstr : TradeHandlingInstr
  tradeReportRefId : Alpha 10
  trdAckStatus : BitVec 8
  trdRptStatus : BitVec 8
  tradeReportRejectReason : BitVec 16
  lastPx : BitVec 64
  lastQty : BitVec 64
  trdType : BitVec 16
  trdSubType : BitVec 16
  confirmId : BitVec 32
  execId : Alpha 16
  side : Side
  pbuid : Alpha 6
  accountId : Alpha 10
  branchId : Alpha 2
  counterpartyPbuid : Alpha 6
  counterpartyAccountId : Alpha 10
  counterpartyBranchId : Alpha 2
  cashMargin : CashMargin
  deriving DecidableEq, Repr

namespace AfterHoursBlockTradeTradeCaptureReportAckMessage

def encode (message : AfterHoursBlockTradeTradeCaptureReportAckMessage) : List UInt8 :=
  encodeUInt 4 message.partitionNo
    ++ (encodeUInt 8 message.reportIndex
    ++ (Alpha.encode message.applId
    ++ (Alpha.encode message.reportingPbuid
    ++ (Alpha.encode message.submittingPbuid
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 2 message.ownerType
    ++ (Alpha.encode message.clearingFirm
    ++ (encodeUInt 8 message.transactTime
    ++ (Alpha.encode message.userInfo
    ++ (Alpha.encode message.tradeId
    ++ (Alpha.encode message.tradeReportId
    ++ (encodeUInt 1 message.tradeReportType
    ++ (encodeUInt 1 message.tradeReportTransType
    ++ (TradeHandlingInstr.encode message.tradeHandlingInstr
    ++ (Alpha.encode message.tradeReportRefId
    ++ (encodeUInt 1 message.trdAckStatus
    ++ (encodeUInt 1 message.trdRptStatus
    ++ (encodeUInt 2 message.tradeReportRejectReason
    ++ (encodeUInt 8 message.lastPx
    ++ (encodeUInt 8 message.lastQty
    ++ (encodeUInt 2 message.trdType
    ++ (encodeUInt 2 message.trdSubType
    ++ (encodeUInt 4 message.confirmId
    ++ (Alpha.encode message.execId
    ++ (Side.encode message.side
    ++ (Alpha.encode message.pbuid
    ++ (Alpha.encode message.accountId
    ++ (Alpha.encode message.branchId
    ++ (Alpha.encode message.counterpartyPbuid
    ++ (Alpha.encode message.counterpartyAccountId
    ++ (Alpha.encode message.counterpartyBranchId
    ++ (CashMargin.encode message.cashMargin)))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (AfterHoursBlockTradeTradeCaptureReportAckMessage × List UInt8) := do
  let (partitionNo, bytes) ← decodeUInt 4 bytes
  let (reportIndex, bytes) ← decodeUInt 8 bytes
  let (applId, bytes) ← Alpha.decode 3 bytes
  let (reportingPbuid, bytes) ← Alpha.decode 6 bytes
  let (submittingPbuid, bytes) ← Alpha.decode 6 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (ownerType, bytes) ← decodeUInt 2 bytes
  let (clearingFirm, bytes) ← Alpha.decode 2 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  let (userInfo, bytes) ← Alpha.decode 32 bytes
  let (tradeId, bytes) ← Alpha.decode 16 bytes
  let (tradeReportId, bytes) ← Alpha.decode 10 bytes
  let (tradeReportType, bytes) ← decodeUInt 1 bytes
  let (tradeReportTransType, bytes) ← decodeUInt 1 bytes
  let (tradeHandlingInstr, bytes) ← TradeHandlingInstr.decode bytes
  let (tradeReportRefId, bytes) ← Alpha.decode 10 bytes
  let (trdAckStatus, bytes) ← decodeUInt 1 bytes
  let (trdRptStatus, bytes) ← decodeUInt 1 bytes
  let (tradeReportRejectReason, bytes) ← decodeUInt 2 bytes
  let (lastPx, bytes) ← decodeUInt 8 bytes
  let (lastQty, bytes) ← decodeUInt 8 bytes
  let (trdType, bytes) ← decodeUInt 2 bytes
  let (trdSubType, bytes) ← decodeUInt 2 bytes
  let (confirmId, bytes) ← decodeUInt 4 bytes
  let (execId, bytes) ← Alpha.decode 16 bytes
  let (side, bytes) ← Side.decode bytes
  let (pbuid, bytes) ← Alpha.decode 6 bytes
  let (accountId, bytes) ← Alpha.decode 10 bytes
  let (branchId, bytes) ← Alpha.decode 2 bytes
  let (counterpartyPbuid, bytes) ← Alpha.decode 6 bytes
  let (counterpartyAccountId, bytes) ← Alpha.decode 10 bytes
  let (counterpartyBranchId, bytes) ← Alpha.decode 2 bytes
  let (cashMargin, bytes) ← CashMargin.decode bytes
  pure ({ partitionNo, reportIndex, applId, reportingPbuid, submittingPbuid, securityId, securityIdSource, ownerType, clearingFirm, transactTime, userInfo, tradeId, tradeReportId, tradeReportType, tradeReportTransType, tradeHandlingInstr, tradeReportRefId, trdAckStatus, trdRptStatus, tradeReportRejectReason, lastPx, lastQty, trdType, trdSubType, confirmId, execId, side, pbuid, accountId, branchId, counterpartyPbuid, counterpartyAccountId, counterpartyBranchId, cashMargin }, bytes)

@[simp] theorem encode_length (message : AfterHoursBlockTradeTradeCaptureReportAckMessage) : (encode message).length = 204 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, TradeHandlingInstr.encode_length, Side.encode_length, CashMargin.encode_length]

theorem encode_length_pos (message : AfterHoursBlockTradeTradeCaptureReportAckMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : AfterHoursBlockTradeTradeCaptureReportAckMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TradeHandlingInstr.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
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
  rw [CashMargin.decode_encode, some_bind]
  rfl

end AfterHoursBlockTradeTradeCaptureReportAckMessage

/-- Bond Spot Negotiated Trade Capture Report Confirmation Message: 334 bytes -/
structure BondSpotNegotiatedTradeCaptureReportConfirmationMessage where
  partitionNo : BitVec 32
  reportIndex : BitVec 64
  applId : Alpha 3
  reportingPbuid : Alpha 6
  submittingPbuid : Alpha 6
  securityId : Alpha 8
  securityIdSource : Alpha 4
  ownerType : BitVec 16
  clearingFirm : Alpha 2
  transactTime : BitVec 64
  userInfo : Alpha 32
  tradeId : Alpha 16
  tradeReportId : Alpha 10
  tradeReportType : BitVec 8
  tradeReportTransType : BitVec 8
  tradeHandlingInstr : TradeHandlingInstr
  lastPx : BitVec 64
  lastQty : BitVec 64
  trdType : BitVec 16
  trdSubType : BitVec 16
  confirmId : BitVec 32
  execId : Alpha 16
  side : Side
  pbuid : Alpha 6
  accountId : Alpha 10
  branchId : Alpha 2
  counterpartyPbuid : Alpha 6
  counterpartyAccountId : Alpha 10
  counterpartyBranchId : Alpha 2
  memberId : Alpha 6
  traderCode : Alpha 5
  counterpartyMemberId : Alpha 6
  counterpartyTraderCode : Alpha 5
  settlType : SettlType
  settlPeriod : SettlPeriod
  cashMargin : CashMargin
  memo : Alpha 120
  deriving DecidableEq, Repr

namespace BondSpotNegotiatedTradeCaptureReportConfirmationMessage

def encode (message : BondSpotNegotiatedTradeCaptureReportConfirmationMessage) : List UInt8 :=
  encodeUInt 4 message.partitionNo
    ++ (encodeUInt 8 message.reportIndex
    ++ (Alpha.encode message.applId
    ++ (Alpha.encode message.reportingPbuid
    ++ (Alpha.encode message.submittingPbuid
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 2 message.ownerType
    ++ (Alpha.encode message.clearingFirm
    ++ (encodeUInt 8 message.transactTime
    ++ (Alpha.encode message.userInfo
    ++ (Alpha.encode message.tradeId
    ++ (Alpha.encode message.tradeReportId
    ++ (encodeUInt 1 message.tradeReportType
    ++ (encodeUInt 1 message.tradeReportTransType
    ++ (TradeHandlingInstr.encode message.tradeHandlingInstr
    ++ (encodeUInt 8 message.lastPx
    ++ (encodeUInt 8 message.lastQty
    ++ (encodeUInt 2 message.trdType
    ++ (encodeUInt 2 message.trdSubType
    ++ (encodeUInt 4 message.confirmId
    ++ (Alpha.encode message.execId
    ++ (Side.encode message.side
    ++ (Alpha.encode message.pbuid
    ++ (Alpha.encode message.accountId
    ++ (Alpha.encode message.branchId
    ++ (Alpha.encode message.counterpartyPbuid
    ++ (Alpha.encode message.counterpartyAccountId
    ++ (Alpha.encode message.counterpartyBranchId
    ++ (Alpha.encode message.memberId
    ++ (Alpha.encode message.traderCode
    ++ (Alpha.encode message.counterpartyMemberId
    ++ (Alpha.encode message.counterpartyTraderCode
    ++ (SettlType.encode message.settlType
    ++ (SettlPeriod.encode message.settlPeriod
    ++ (CashMargin.encode message.cashMargin
    ++ (Alpha.encode message.memo))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (BondSpotNegotiatedTradeCaptureReportConfirmationMessage × List UInt8) := do
  let (partitionNo, bytes) ← decodeUInt 4 bytes
  let (reportIndex, bytes) ← decodeUInt 8 bytes
  let (applId, bytes) ← Alpha.decode 3 bytes
  let (reportingPbuid, bytes) ← Alpha.decode 6 bytes
  let (submittingPbuid, bytes) ← Alpha.decode 6 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (ownerType, bytes) ← decodeUInt 2 bytes
  let (clearingFirm, bytes) ← Alpha.decode 2 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  let (userInfo, bytes) ← Alpha.decode 32 bytes
  let (tradeId, bytes) ← Alpha.decode 16 bytes
  let (tradeReportId, bytes) ← Alpha.decode 10 bytes
  let (tradeReportType, bytes) ← decodeUInt 1 bytes
  let (tradeReportTransType, bytes) ← decodeUInt 1 bytes
  let (tradeHandlingInstr, bytes) ← TradeHandlingInstr.decode bytes
  let (lastPx, bytes) ← decodeUInt 8 bytes
  let (lastQty, bytes) ← decodeUInt 8 bytes
  let (trdType, bytes) ← decodeUInt 2 bytes
  let (trdSubType, bytes) ← decodeUInt 2 bytes
  let (confirmId, bytes) ← decodeUInt 4 bytes
  let (execId, bytes) ← Alpha.decode 16 bytes
  let (side, bytes) ← Side.decode bytes
  let (pbuid, bytes) ← Alpha.decode 6 bytes
  let (accountId, bytes) ← Alpha.decode 10 bytes
  let (branchId, bytes) ← Alpha.decode 2 bytes
  let (counterpartyPbuid, bytes) ← Alpha.decode 6 bytes
  let (counterpartyAccountId, bytes) ← Alpha.decode 10 bytes
  let (counterpartyBranchId, bytes) ← Alpha.decode 2 bytes
  let (memberId, bytes) ← Alpha.decode 6 bytes
  let (traderCode, bytes) ← Alpha.decode 5 bytes
  let (counterpartyMemberId, bytes) ← Alpha.decode 6 bytes
  let (counterpartyTraderCode, bytes) ← Alpha.decode 5 bytes
  let (settlType, bytes) ← SettlType.decode bytes
  let (settlPeriod, bytes) ← SettlPeriod.decode bytes
  let (cashMargin, bytes) ← CashMargin.decode bytes
  let (memo, bytes) ← Alpha.decode 120 bytes
  pure ({ partitionNo, reportIndex, applId, reportingPbuid, submittingPbuid, securityId, securityIdSource, ownerType, clearingFirm, transactTime, userInfo, tradeId, tradeReportId, tradeReportType, tradeReportTransType, tradeHandlingInstr, lastPx, lastQty, trdType, trdSubType, confirmId, execId, side, pbuid, accountId, branchId, counterpartyPbuid, counterpartyAccountId, counterpartyBranchId, memberId, traderCode, counterpartyMemberId, counterpartyTraderCode, settlType, settlPeriod, cashMargin, memo }, bytes)

@[simp] theorem encode_length (message : BondSpotNegotiatedTradeCaptureReportConfirmationMessage) : (encode message).length = 334 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, TradeHandlingInstr.encode_length, Side.encode_length, SettlType.encode_length, SettlPeriod.encode_length, CashMargin.encode_length]

theorem encode_length_pos (message : BondSpotNegotiatedTradeCaptureReportConfirmationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : BondSpotNegotiatedTradeCaptureReportConfirmationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TradeHandlingInstr.decode_encode, some_bind]
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
  rw [List.append_assoc, Side.decode_encode, some_bind]
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
  rw [List.append_assoc, SettlType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SettlPeriod.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CashMargin.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BondSpotNegotiatedTradeCaptureReportConfirmationMessage

/-- Refinancing Securities Lending Agreed Trade Capture Report Confirmation Message: 198 bytes -/
structure RefinancingSecuritiesLendingAgreedTradeCaptureReportConfirmationMessage where
  partitionNo : BitVec 32
  reportIndex : BitVec 64
  applId : Alpha 3
  reportingPbuid : Alpha 6
  submittingPbuid : Alpha 6
  securityId : Alpha 8
  securityIdSource : Alpha 4
  ownerType : BitVec 16
  clearingFirm : Alpha 2
  transactTime : BitVec 64
  userInfo : Alpha 32
  tradeId : Alpha 16
  tradeReportId : Alpha 10
  tradeReportType : BitVec 8
  tradeReportTransType : BitVec 8
  tradeHandlingInstr : TradeHandlingInstr
  lastPx : BitVec 64
  lastQty : BitVec 64
  trdType : BitVec 16
  trdSubType : BitVec 16
  confirmId : BitVec 32
  execId : Alpha 16
  side : Side
  pbuid : Alpha 6
  accountId : Alpha 10
  branchId : Alpha 2
  counterpartyPbuid : Alpha 6
  counterpartyAccountId : Alpha 10
  counterpartyBranchId : Alpha 2
  expirationDays : BitVec 16
  expirationType : BitVec 8
  maturityDate : BitVec 32
  shareProperty : Alpha 2
  deriving DecidableEq, Repr

namespace RefinancingSecuritiesLendingAgreedTradeCaptureReportConfirmationMessage

def encode (message : RefinancingSecuritiesLendingAgreedTradeCaptureReportConfirmationMessage) : List UInt8 :=
  encodeUInt 4 message.partitionNo
    ++ (encodeUInt 8 message.reportIndex
    ++ (Alpha.encode message.applId
    ++ (Alpha.encode message.reportingPbuid
    ++ (Alpha.encode message.submittingPbuid
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 2 message.ownerType
    ++ (Alpha.encode message.clearingFirm
    ++ (encodeUInt 8 message.transactTime
    ++ (Alpha.encode message.userInfo
    ++ (Alpha.encode message.tradeId
    ++ (Alpha.encode message.tradeReportId
    ++ (encodeUInt 1 message.tradeReportType
    ++ (encodeUInt 1 message.tradeReportTransType
    ++ (TradeHandlingInstr.encode message.tradeHandlingInstr
    ++ (encodeUInt 8 message.lastPx
    ++ (encodeUInt 8 message.lastQty
    ++ (encodeUInt 2 message.trdType
    ++ (encodeUInt 2 message.trdSubType
    ++ (encodeUInt 4 message.confirmId
    ++ (Alpha.encode message.execId
    ++ (Side.encode message.side
    ++ (Alpha.encode message.pbuid
    ++ (Alpha.encode message.accountId
    ++ (Alpha.encode message.branchId
    ++ (Alpha.encode message.counterpartyPbuid
    ++ (Alpha.encode message.counterpartyAccountId
    ++ (Alpha.encode message.counterpartyBranchId
    ++ (encodeUInt 2 message.expirationDays
    ++ (encodeUInt 1 message.expirationType
    ++ (encodeUInt 4 message.maturityDate
    ++ (Alpha.encode message.shareProperty))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (RefinancingSecuritiesLendingAgreedTradeCaptureReportConfirmationMessage × List UInt8) := do
  let (partitionNo, bytes) ← decodeUInt 4 bytes
  let (reportIndex, bytes) ← decodeUInt 8 bytes
  let (applId, bytes) ← Alpha.decode 3 bytes
  let (reportingPbuid, bytes) ← Alpha.decode 6 bytes
  let (submittingPbuid, bytes) ← Alpha.decode 6 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (ownerType, bytes) ← decodeUInt 2 bytes
  let (clearingFirm, bytes) ← Alpha.decode 2 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  let (userInfo, bytes) ← Alpha.decode 32 bytes
  let (tradeId, bytes) ← Alpha.decode 16 bytes
  let (tradeReportId, bytes) ← Alpha.decode 10 bytes
  let (tradeReportType, bytes) ← decodeUInt 1 bytes
  let (tradeReportTransType, bytes) ← decodeUInt 1 bytes
  let (tradeHandlingInstr, bytes) ← TradeHandlingInstr.decode bytes
  let (lastPx, bytes) ← decodeUInt 8 bytes
  let (lastQty, bytes) ← decodeUInt 8 bytes
  let (trdType, bytes) ← decodeUInt 2 bytes
  let (trdSubType, bytes) ← decodeUInt 2 bytes
  let (confirmId, bytes) ← decodeUInt 4 bytes
  let (execId, bytes) ← Alpha.decode 16 bytes
  let (side, bytes) ← Side.decode bytes
  let (pbuid, bytes) ← Alpha.decode 6 bytes
  let (accountId, bytes) ← Alpha.decode 10 bytes
  let (branchId, bytes) ← Alpha.decode 2 bytes
  let (counterpartyPbuid, bytes) ← Alpha.decode 6 bytes
  let (counterpartyAccountId, bytes) ← Alpha.decode 10 bytes
  let (counterpartyBranchId, bytes) ← Alpha.decode 2 bytes
  let (expirationDays, bytes) ← decodeUInt 2 bytes
  let (expirationType, bytes) ← decodeUInt 1 bytes
  let (maturityDate, bytes) ← decodeUInt 4 bytes
  let (shareProperty, bytes) ← Alpha.decode 2 bytes
  pure ({ partitionNo, reportIndex, applId, reportingPbuid, submittingPbuid, securityId, securityIdSource, ownerType, clearingFirm, transactTime, userInfo, tradeId, tradeReportId, tradeReportType, tradeReportTransType, tradeHandlingInstr, lastPx, lastQty, trdType, trdSubType, confirmId, execId, side, pbuid, accountId, branchId, counterpartyPbuid, counterpartyAccountId, counterpartyBranchId, expirationDays, expirationType, maturityDate, shareProperty }, bytes)

@[simp] theorem encode_length (message : RefinancingSecuritiesLendingAgreedTradeCaptureReportConfirmationMessage) : (encode message).length = 198 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, TradeHandlingInstr.encode_length, Side.encode_length]

theorem encode_length_pos (message : RefinancingSecuritiesLendingAgreedTradeCaptureReportConfirmationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : RefinancingSecuritiesLendingAgreedTradeCaptureReportConfirmationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TradeHandlingInstr.decode_encode, some_bind]
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
  rw [List.append_assoc, Side.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end RefinancingSecuritiesLendingAgreedTradeCaptureReportConfirmationMessage

/-- Mutual Trade Confirmation Trade Capture Report Confirmation Message: 189 bytes -/
structure MutualTradeConfirmationTradeCaptureReportConfirmationMessage where
  partitionNo : BitVec 32
  reportIndex : BitVec 64
  applId : Alpha 3
  reportingPbuid : Alpha 6
  submittingPbuid : Alpha 6
  securityId : Alpha 8
  securityIdSource : Alpha 4
  ownerType : BitVec 16
  clearingFirm : Alpha 2
  transactTime : BitVec 64
  userInfo : Alpha 32
  tradeId : Alpha 16
  tradeReportId : Alpha 10
  tradeReportType : BitVec 8
  tradeReportTransType : BitVec 8
  tradeHandlingInstr : TradeHandlingInstr
  lastPx : BitVec 64
  lastQty : BitVec 64
  trdType : BitVec 16
  trdSubType : BitVec 16
  confirmId : BitVec 32
  execId : Alpha 16
  side : Side
  pbuid : Alpha 6
  accountId : Alpha 10
  branchId : Alpha 2
  counterpartyPbuid : Alpha 6
  counterpartyAccountId : Alpha 10
  counterpartyBranchId : Alpha 2
  deriving DecidableEq, Repr

namespace MutualTradeConfirmationTradeCaptureReportConfirmationMessage

def encode (message : MutualTradeConfirmationTradeCaptureReportConfirmationMessage) : List UInt8 :=
  encodeUInt 4 message.partitionNo
    ++ (encodeUInt 8 message.reportIndex
    ++ (Alpha.encode message.applId
    ++ (Alpha.encode message.reportingPbuid
    ++ (Alpha.encode message.submittingPbuid
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 2 message.ownerType
    ++ (Alpha.encode message.clearingFirm
    ++ (encodeUInt 8 message.transactTime
    ++ (Alpha.encode message.userInfo
    ++ (Alpha.encode message.tradeId
    ++ (Alpha.encode message.tradeReportId
    ++ (encodeUInt 1 message.tradeReportType
    ++ (encodeUInt 1 message.tradeReportTransType
    ++ (TradeHandlingInstr.encode message.tradeHandlingInstr
    ++ (encodeUInt 8 message.lastPx
    ++ (encodeUInt 8 message.lastQty
    ++ (encodeUInt 2 message.trdType
    ++ (encodeUInt 2 message.trdSubType
    ++ (encodeUInt 4 message.confirmId
    ++ (Alpha.encode message.execId
    ++ (Side.encode message.side
    ++ (Alpha.encode message.pbuid
    ++ (Alpha.encode message.accountId
    ++ (Alpha.encode message.branchId
    ++ (Alpha.encode message.counterpartyPbuid
    ++ (Alpha.encode message.counterpartyAccountId
    ++ (Alpha.encode message.counterpartyBranchId))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (MutualTradeConfirmationTradeCaptureReportConfirmationMessage × List UInt8) := do
  let (partitionNo, bytes) ← decodeUInt 4 bytes
  let (reportIndex, bytes) ← decodeUInt 8 bytes
  let (applId, bytes) ← Alpha.decode 3 bytes
  let (reportingPbuid, bytes) ← Alpha.decode 6 bytes
  let (submittingPbuid, bytes) ← Alpha.decode 6 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (ownerType, bytes) ← decodeUInt 2 bytes
  let (clearingFirm, bytes) ← Alpha.decode 2 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  let (userInfo, bytes) ← Alpha.decode 32 bytes
  let (tradeId, bytes) ← Alpha.decode 16 bytes
  let (tradeReportId, bytes) ← Alpha.decode 10 bytes
  let (tradeReportType, bytes) ← decodeUInt 1 bytes
  let (tradeReportTransType, bytes) ← decodeUInt 1 bytes
  let (tradeHandlingInstr, bytes) ← TradeHandlingInstr.decode bytes
  let (lastPx, bytes) ← decodeUInt 8 bytes
  let (lastQty, bytes) ← decodeUInt 8 bytes
  let (trdType, bytes) ← decodeUInt 2 bytes
  let (trdSubType, bytes) ← decodeUInt 2 bytes
  let (confirmId, bytes) ← decodeUInt 4 bytes
  let (execId, bytes) ← Alpha.decode 16 bytes
  let (side, bytes) ← Side.decode bytes
  let (pbuid, bytes) ← Alpha.decode 6 bytes
  let (accountId, bytes) ← Alpha.decode 10 bytes
  let (branchId, bytes) ← Alpha.decode 2 bytes
  let (counterpartyPbuid, bytes) ← Alpha.decode 6 bytes
  let (counterpartyAccountId, bytes) ← Alpha.decode 10 bytes
  let (counterpartyBranchId, bytes) ← Alpha.decode 2 bytes
  pure ({ partitionNo, reportIndex, applId, reportingPbuid, submittingPbuid, securityId, securityIdSource, ownerType, clearingFirm, transactTime, userInfo, tradeId, tradeReportId, tradeReportType, tradeReportTransType, tradeHandlingInstr, lastPx, lastQty, trdType, trdSubType, confirmId, execId, side, pbuid, accountId, branchId, counterpartyPbuid, counterpartyAccountId, counterpartyBranchId }, bytes)

@[simp] theorem encode_length (message : MutualTradeConfirmationTradeCaptureReportConfirmationMessage) : (encode message).length = 189 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, TradeHandlingInstr.encode_length, Side.encode_length]

theorem encode_length_pos (message : MutualTradeConfirmationTradeCaptureReportConfirmationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : MutualTradeConfirmationTradeCaptureReportConfirmationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TradeHandlingInstr.decode_encode, some_bind]
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
  rw [List.append_assoc, Side.decode_encode, some_bind]
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

end MutualTradeConfirmationTradeCaptureReportConfirmationMessage

/-- Market Making Mutual Trade Confirmation Trade Capture Report Confirmation Message: 189 bytes -/
structure MarketMakingMutualTradeConfirmationTradeCaptureReportConfirmationMessage where
  partitionNo : BitVec 32
  reportIndex : BitVec 64
  applId : Alpha 3
  reportingPbuid : Alpha 6
  submittingPbuid : Alpha 6
  securityId : Alpha 8
  securityIdSource : Alpha 4
  ownerType : BitVec 16
  clearingFirm : Alpha 2
  transactTime : BitVec 64
  userInfo : Alpha 32
  tradeId : Alpha 16
  tradeReportId : Alpha 10
  tradeReportType : BitVec 8
  tradeReportTransType : BitVec 8
  tradeHandlingInstr : TradeHandlingInstr
  lastPx : BitVec 64
  lastQty : BitVec 64
  trdType : BitVec 16
  trdSubType : BitVec 16
  confirmId : BitVec 32
  execId : Alpha 16
  side : Side
  pbuid : Alpha 6
  accountId : Alpha 10
  branchId : Alpha 2
  counterpartyPbuid : Alpha 6
  counterpartyAccountId : Alpha 10
  counterpartyBranchId : Alpha 2
  deriving DecidableEq, Repr

namespace MarketMakingMutualTradeConfirmationTradeCaptureReportConfirmationMessage

def encode (message : MarketMakingMutualTradeConfirmationTradeCaptureReportConfirmationMessage) : List UInt8 :=
  encodeUInt 4 message.partitionNo
    ++ (encodeUInt 8 message.reportIndex
    ++ (Alpha.encode message.applId
    ++ (Alpha.encode message.reportingPbuid
    ++ (Alpha.encode message.submittingPbuid
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 2 message.ownerType
    ++ (Alpha.encode message.clearingFirm
    ++ (encodeUInt 8 message.transactTime
    ++ (Alpha.encode message.userInfo
    ++ (Alpha.encode message.tradeId
    ++ (Alpha.encode message.tradeReportId
    ++ (encodeUInt 1 message.tradeReportType
    ++ (encodeUInt 1 message.tradeReportTransType
    ++ (TradeHandlingInstr.encode message.tradeHandlingInstr
    ++ (encodeUInt 8 message.lastPx
    ++ (encodeUInt 8 message.lastQty
    ++ (encodeUInt 2 message.trdType
    ++ (encodeUInt 2 message.trdSubType
    ++ (encodeUInt 4 message.confirmId
    ++ (Alpha.encode message.execId
    ++ (Side.encode message.side
    ++ (Alpha.encode message.pbuid
    ++ (Alpha.encode message.accountId
    ++ (Alpha.encode message.branchId
    ++ (Alpha.encode message.counterpartyPbuid
    ++ (Alpha.encode message.counterpartyAccountId
    ++ (Alpha.encode message.counterpartyBranchId))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (MarketMakingMutualTradeConfirmationTradeCaptureReportConfirmationMessage × List UInt8) := do
  let (partitionNo, bytes) ← decodeUInt 4 bytes
  let (reportIndex, bytes) ← decodeUInt 8 bytes
  let (applId, bytes) ← Alpha.decode 3 bytes
  let (reportingPbuid, bytes) ← Alpha.decode 6 bytes
  let (submittingPbuid, bytes) ← Alpha.decode 6 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (ownerType, bytes) ← decodeUInt 2 bytes
  let (clearingFirm, bytes) ← Alpha.decode 2 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  let (userInfo, bytes) ← Alpha.decode 32 bytes
  let (tradeId, bytes) ← Alpha.decode 16 bytes
  let (tradeReportId, bytes) ← Alpha.decode 10 bytes
  let (tradeReportType, bytes) ← decodeUInt 1 bytes
  let (tradeReportTransType, bytes) ← decodeUInt 1 bytes
  let (tradeHandlingInstr, bytes) ← TradeHandlingInstr.decode bytes
  let (lastPx, bytes) ← decodeUInt 8 bytes
  let (lastQty, bytes) ← decodeUInt 8 bytes
  let (trdType, bytes) ← decodeUInt 2 bytes
  let (trdSubType, bytes) ← decodeUInt 2 bytes
  let (confirmId, bytes) ← decodeUInt 4 bytes
  let (execId, bytes) ← Alpha.decode 16 bytes
  let (side, bytes) ← Side.decode bytes
  let (pbuid, bytes) ← Alpha.decode 6 bytes
  let (accountId, bytes) ← Alpha.decode 10 bytes
  let (branchId, bytes) ← Alpha.decode 2 bytes
  let (counterpartyPbuid, bytes) ← Alpha.decode 6 bytes
  let (counterpartyAccountId, bytes) ← Alpha.decode 10 bytes
  let (counterpartyBranchId, bytes) ← Alpha.decode 2 bytes
  pure ({ partitionNo, reportIndex, applId, reportingPbuid, submittingPbuid, securityId, securityIdSource, ownerType, clearingFirm, transactTime, userInfo, tradeId, tradeReportId, tradeReportType, tradeReportTransType, tradeHandlingInstr, lastPx, lastQty, trdType, trdSubType, confirmId, execId, side, pbuid, accountId, branchId, counterpartyPbuid, counterpartyAccountId, counterpartyBranchId }, bytes)

@[simp] theorem encode_length (message : MarketMakingMutualTradeConfirmationTradeCaptureReportConfirmationMessage) : (encode message).length = 189 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, TradeHandlingInstr.encode_length, Side.encode_length]

theorem encode_length_pos (message : MarketMakingMutualTradeConfirmationTradeCaptureReportConfirmationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : MarketMakingMutualTradeConfirmationTradeCaptureReportConfirmationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TradeHandlingInstr.decode_encode, some_bind]
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
  rw [List.append_assoc, Side.decode_encode, some_bind]
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

end MarketMakingMutualTradeConfirmationTradeCaptureReportConfirmationMessage

/-- After Hours Block Trade Trade Capture Report Confirmation Message: 190 bytes -/
structure AfterHoursBlockTradeTradeCaptureReportConfirmationMessage where
  partitionNo : BitVec 32
  reportIndex : BitVec 64
  applId : Alpha 3
  reportingPbuid : Alpha 6
  submittingPbuid : Alpha 6
  securityId : Alpha 8
  securityIdSource : Alpha 4
  ownerType : BitVec 16
  clearingFirm : Alpha 2
  transactTime : BitVec 64
  userInfo : Alpha 32
  tradeId : Alpha 16
  tradeReportId : Alpha 10
  tradeReportType : BitVec 8
  tradeReportTransType : BitVec 8
  tradeHandlingInstr : TradeHandlingInstr
  lastPx : BitVec 64
  lastQty : BitVec 64
  trdType : BitVec 16
  trdSubType : BitVec 16
  confirmId : BitVec 32
  execId : Alpha 16
  side : Side
  pbuid : Alpha 6
  accountId : Alpha 10
  branchId : Alpha 2
  counterpartyPbuid : Alpha 6
  counterpartyAccountId : Alpha 10
  counterpartyBranchId : Alpha 2
  cashMargin : CashMargin
  deriving DecidableEq, Repr

namespace AfterHoursBlockTradeTradeCaptureReportConfirmationMessage

def encode (message : AfterHoursBlockTradeTradeCaptureReportConfirmationMessage) : List UInt8 :=
  encodeUInt 4 message.partitionNo
    ++ (encodeUInt 8 message.reportIndex
    ++ (Alpha.encode message.applId
    ++ (Alpha.encode message.reportingPbuid
    ++ (Alpha.encode message.submittingPbuid
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 2 message.ownerType
    ++ (Alpha.encode message.clearingFirm
    ++ (encodeUInt 8 message.transactTime
    ++ (Alpha.encode message.userInfo
    ++ (Alpha.encode message.tradeId
    ++ (Alpha.encode message.tradeReportId
    ++ (encodeUInt 1 message.tradeReportType
    ++ (encodeUInt 1 message.tradeReportTransType
    ++ (TradeHandlingInstr.encode message.tradeHandlingInstr
    ++ (encodeUInt 8 message.lastPx
    ++ (encodeUInt 8 message.lastQty
    ++ (encodeUInt 2 message.trdType
    ++ (encodeUInt 2 message.trdSubType
    ++ (encodeUInt 4 message.confirmId
    ++ (Alpha.encode message.execId
    ++ (Side.encode message.side
    ++ (Alpha.encode message.pbuid
    ++ (Alpha.encode message.accountId
    ++ (Alpha.encode message.branchId
    ++ (Alpha.encode message.counterpartyPbuid
    ++ (Alpha.encode message.counterpartyAccountId
    ++ (Alpha.encode message.counterpartyBranchId
    ++ (CashMargin.encode message.cashMargin)))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (AfterHoursBlockTradeTradeCaptureReportConfirmationMessage × List UInt8) := do
  let (partitionNo, bytes) ← decodeUInt 4 bytes
  let (reportIndex, bytes) ← decodeUInt 8 bytes
  let (applId, bytes) ← Alpha.decode 3 bytes
  let (reportingPbuid, bytes) ← Alpha.decode 6 bytes
  let (submittingPbuid, bytes) ← Alpha.decode 6 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (ownerType, bytes) ← decodeUInt 2 bytes
  let (clearingFirm, bytes) ← Alpha.decode 2 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  let (userInfo, bytes) ← Alpha.decode 32 bytes
  let (tradeId, bytes) ← Alpha.decode 16 bytes
  let (tradeReportId, bytes) ← Alpha.decode 10 bytes
  let (tradeReportType, bytes) ← decodeUInt 1 bytes
  let (tradeReportTransType, bytes) ← decodeUInt 1 bytes
  let (tradeHandlingInstr, bytes) ← TradeHandlingInstr.decode bytes
  let (lastPx, bytes) ← decodeUInt 8 bytes
  let (lastQty, bytes) ← decodeUInt 8 bytes
  let (trdType, bytes) ← decodeUInt 2 bytes
  let (trdSubType, bytes) ← decodeUInt 2 bytes
  let (confirmId, bytes) ← decodeUInt 4 bytes
  let (execId, bytes) ← Alpha.decode 16 bytes
  let (side, bytes) ← Side.decode bytes
  let (pbuid, bytes) ← Alpha.decode 6 bytes
  let (accountId, bytes) ← Alpha.decode 10 bytes
  let (branchId, bytes) ← Alpha.decode 2 bytes
  let (counterpartyPbuid, bytes) ← Alpha.decode 6 bytes
  let (counterpartyAccountId, bytes) ← Alpha.decode 10 bytes
  let (counterpartyBranchId, bytes) ← Alpha.decode 2 bytes
  let (cashMargin, bytes) ← CashMargin.decode bytes
  pure ({ partitionNo, reportIndex, applId, reportingPbuid, submittingPbuid, securityId, securityIdSource, ownerType, clearingFirm, transactTime, userInfo, tradeId, tradeReportId, tradeReportType, tradeReportTransType, tradeHandlingInstr, lastPx, lastQty, trdType, trdSubType, confirmId, execId, side, pbuid, accountId, branchId, counterpartyPbuid, counterpartyAccountId, counterpartyBranchId, cashMargin }, bytes)

@[simp] theorem encode_length (message : AfterHoursBlockTradeTradeCaptureReportConfirmationMessage) : (encode message).length = 190 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, TradeHandlingInstr.encode_length, Side.encode_length, CashMargin.encode_length]

theorem encode_length_pos (message : AfterHoursBlockTradeTradeCaptureReportConfirmationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : AfterHoursBlockTradeTradeCaptureReportConfirmationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TradeHandlingInstr.decode_encode, some_bind]
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
  rw [List.append_assoc, Side.decode_encode, some_bind]
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
  rw [CashMargin.decode_encode, some_bind]
  rfl

end AfterHoursBlockTradeTradeCaptureReportConfirmationMessage

/-- Any Payload, selected by Msg Type -/
inductive Payload where
  | logonMessage (message : LogonMessage) -- 1
  | logoutMessage (message : LogoutMessage) -- 2
  | heartbeatMessage (message : HeartbeatMessage) -- 3
  | businessRejectMessage (message : BusinessRejectMessage) -- 4
  | reportSynchronizationMessage (message : ReportSynchronizationMessage) -- 5
  | platformStateInfoMessage (message : PlatformStateInfoMessage) -- 6
  | reportFinishedMessage (message : ReportFinishedMessage) -- 7
  | platformInfoMessage (message : PlatformInfoMessage) -- 9
  | tradingSessionStatusMessage (message : TradingSessionStatusMessage) -- 10
  | bondSpotMatchingNewOrderMessage (message : BondSpotMatchingNewOrderMessage) -- 101010
  | centralizedAuctionNewOrderMessage (message : CentralizedAuctionNewOrderMessage) -- 101040
  | conversionNewOrderMessage (message : ConversionNewOrderMessage) -- 101041
  | inquiryNewOrderMessage (message : InquiryNewOrderMessage) -- 101042
  | subscriptionNewOrderMessage (message : SubscriptionNewOrderMessage) -- 101043
  | putBackNewOrderMessage (message : PutBackNewOrderMessage) -- 101044
  | tenderOfferAcceptanceNewOrderMessage (message : TenderOfferAcceptanceNewOrderMessage) -- 101045
  | refinancingSecuritiesLendingNonAgreedNewOrderMessage (message : RefinancingSecuritiesLendingNonAgreedNewOrderMessage) -- 101050
  | orderCancelRequestMessage (message : OrderCancelRequestMessage) -- 102000
  | cancelRejectMessage (message : CancelRejectMessage) -- 201000
  | bondSpotMatchingExecutionReportMessage (message : BondSpotMatchingExecutionReportMessage) -- 202010
  | centralizedAuctionExecutionReportMessage (message : CentralizedAuctionExecutionReportMessage) -- 202040
  | conversionExecutionReportMessage (message : ConversionExecutionReportMessage) -- 202041
  | inquiryExecutionReportMessage (message : InquiryExecutionReportMessage) -- 202042
  | subscriptionExecutionReportMessage (message : SubscriptionExecutionReportMessage) -- 202043
  | putBackExecutionReportMessage (message : PutBackExecutionReportMessage) -- 202044
  | tenderOfferAcceptanceExecutionReportMessage (message : TenderOfferAcceptanceExecutionReportMessage) -- 202045
  | refinancingSecuritiesLendingNonAgreedExecutionReportMessage (message : RefinancingSecuritiesLendingNonAgreedExecutionReportMessage) -- 202050
  | bondSpotMatchingTradeExecutionReportMessage (message : BondSpotMatchingTradeExecutionReportMessage) -- 203010
  | centralizedAuctionTradeExecutionReportMessage (message : CentralizedAuctionTradeExecutionReportMessage) -- 203040
  | refinancingSecuritiesLendingNonAgreedTradeExecutionReportMessage (message : RefinancingSecuritiesLendingNonAgreedTradeExecutionReportMessage) -- 203050
  | bondSpotNegotiatedTradeCaptureReportMessage (message : BondSpotNegotiatedTradeCaptureReportMessage) -- 103031
  | refinancingSecuritiesLendingAgreedTradeCaptureReportMessage (message : RefinancingSecuritiesLendingAgreedTradeCaptureReportMessage) -- 103051
  | mutualTradeConfirmationTradeCaptureReportMessage (message : MutualTradeConfirmationTradeCaptureReportMessage) -- 103060
  | marketMakingMutualTradeConfirmationTradeCaptureReportMessage (message : MarketMakingMutualTradeConfirmationTradeCaptureReportMessage) -- 103061
  | afterHoursBlockTradeTradeCaptureReportMessage (message : AfterHoursBlockTradeTradeCaptureReportMessage) -- 103062
  | bondSpotNegotiatedTradeCaptureReportAckMessage (message : BondSpotNegotiatedTradeCaptureReportAckMessage) -- 204031
  | refinancingSecuritiesLendingAgreedTradeCaptureReportAckMessage (message : RefinancingSecuritiesLendingAgreedTradeCaptureReportAckMessage) -- 204051
  | mutualTradeConfirmationTradeCaptureReportAckMessage (message : MutualTradeConfirmationTradeCaptureReportAckMessage) -- 204060
  | marketMakingMutualTradeConfirmationTradeCaptureReportAckMessage (message : MarketMakingMutualTradeConfirmationTradeCaptureReportAckMessage) -- 204061
  | afterHoursBlockTradeTradeCaptureReportAckMessage (message : AfterHoursBlockTradeTradeCaptureReportAckMessage) -- 204062
  | bondSpotNegotiatedTradeCaptureReportConfirmationMessage (message : BondSpotNegotiatedTradeCaptureReportConfirmationMessage) -- 205031
  | refinancingSecuritiesLendingAgreedTradeCaptureReportConfirmationMessage (message : RefinancingSecuritiesLendingAgreedTradeCaptureReportConfirmationMessage) -- 205051
  | mutualTradeConfirmationTradeCaptureReportConfirmationMessage (message : MutualTradeConfirmationTradeCaptureReportConfirmationMessage) -- 205060
  | marketMakingMutualTradeConfirmationTradeCaptureReportConfirmationMessage (message : MarketMakingMutualTradeConfirmationTradeCaptureReportConfirmationMessage) -- 205061
  | afterHoursBlockTradeTradeCaptureReportConfirmationMessage (message : AfterHoursBlockTradeTradeCaptureReportConfirmationMessage) -- 205062
  deriving DecidableEq, Repr

namespace Payload

/-- The Msg Type each message is sent under -/
def tag : Payload → BitVec 32
  | .logonMessage _ => 1
  | .logoutMessage _ => 2
  | .heartbeatMessage _ => 3
  | .businessRejectMessage _ => 4
  | .reportSynchronizationMessage _ => 5
  | .platformStateInfoMessage _ => 6
  | .reportFinishedMessage _ => 7
  | .platformInfoMessage _ => 9
  | .tradingSessionStatusMessage _ => 10
  | .bondSpotMatchingNewOrderMessage _ => 101010
  | .centralizedAuctionNewOrderMessage _ => 101040
  | .conversionNewOrderMessage _ => 101041
  | .inquiryNewOrderMessage _ => 101042
  | .subscriptionNewOrderMessage _ => 101043
  | .putBackNewOrderMessage _ => 101044
  | .tenderOfferAcceptanceNewOrderMessage _ => 101045
  | .refinancingSecuritiesLendingNonAgreedNewOrderMessage _ => 101050
  | .orderCancelRequestMessage _ => 102000
  | .cancelRejectMessage _ => 201000
  | .bondSpotMatchingExecutionReportMessage _ => 202010
  | .centralizedAuctionExecutionReportMessage _ => 202040
  | .conversionExecutionReportMessage _ => 202041
  | .inquiryExecutionReportMessage _ => 202042
  | .subscriptionExecutionReportMessage _ => 202043
  | .putBackExecutionReportMessage _ => 202044
  | .tenderOfferAcceptanceExecutionReportMessage _ => 202045
  | .refinancingSecuritiesLendingNonAgreedExecutionReportMessage _ => 202050
  | .bondSpotMatchingTradeExecutionReportMessage _ => 203010
  | .centralizedAuctionTradeExecutionReportMessage _ => 203040
  | .refinancingSecuritiesLendingNonAgreedTradeExecutionReportMessage _ => 203050
  | .bondSpotNegotiatedTradeCaptureReportMessage _ => 103031
  | .refinancingSecuritiesLendingAgreedTradeCaptureReportMessage _ => 103051
  | .mutualTradeConfirmationTradeCaptureReportMessage _ => 103060
  | .marketMakingMutualTradeConfirmationTradeCaptureReportMessage _ => 103061
  | .afterHoursBlockTradeTradeCaptureReportMessage _ => 103062
  | .bondSpotNegotiatedTradeCaptureReportAckMessage _ => 204031
  | .refinancingSecuritiesLendingAgreedTradeCaptureReportAckMessage _ => 204051
  | .mutualTradeConfirmationTradeCaptureReportAckMessage _ => 204060
  | .marketMakingMutualTradeConfirmationTradeCaptureReportAckMessage _ => 204061
  | .afterHoursBlockTradeTradeCaptureReportAckMessage _ => 204062
  | .bondSpotNegotiatedTradeCaptureReportConfirmationMessage _ => 205031
  | .refinancingSecuritiesLendingAgreedTradeCaptureReportConfirmationMessage _ => 205051
  | .mutualTradeConfirmationTradeCaptureReportConfirmationMessage _ => 205060
  | .marketMakingMutualTradeConfirmationTradeCaptureReportConfirmationMessage _ => 205061
  | .afterHoursBlockTradeTradeCaptureReportConfirmationMessage _ => 205062

def encode : Payload → List UInt8
  | .logonMessage message => LogonMessage.encode message
  | .logoutMessage message => LogoutMessage.encode message
  | .heartbeatMessage message => HeartbeatMessage.encode message
  | .businessRejectMessage message => BusinessRejectMessage.encode message
  | .reportSynchronizationMessage message => ReportSynchronizationMessage.encode message
  | .platformStateInfoMessage message => PlatformStateInfoMessage.encode message
  | .reportFinishedMessage message => ReportFinishedMessage.encode message
  | .platformInfoMessage message => PlatformInfoMessage.encode message
  | .tradingSessionStatusMessage message => TradingSessionStatusMessage.encode message
  | .bondSpotMatchingNewOrderMessage message => BondSpotMatchingNewOrderMessage.encode message
  | .centralizedAuctionNewOrderMessage message => CentralizedAuctionNewOrderMessage.encode message
  | .conversionNewOrderMessage message => ConversionNewOrderMessage.encode message
  | .inquiryNewOrderMessage message => InquiryNewOrderMessage.encode message
  | .subscriptionNewOrderMessage message => SubscriptionNewOrderMessage.encode message
  | .putBackNewOrderMessage message => PutBackNewOrderMessage.encode message
  | .tenderOfferAcceptanceNewOrderMessage message => TenderOfferAcceptanceNewOrderMessage.encode message
  | .refinancingSecuritiesLendingNonAgreedNewOrderMessage message => RefinancingSecuritiesLendingNonAgreedNewOrderMessage.encode message
  | .orderCancelRequestMessage message => OrderCancelRequestMessage.encode message
  | .cancelRejectMessage message => CancelRejectMessage.encode message
  | .bondSpotMatchingExecutionReportMessage message => BondSpotMatchingExecutionReportMessage.encode message
  | .centralizedAuctionExecutionReportMessage message => CentralizedAuctionExecutionReportMessage.encode message
  | .conversionExecutionReportMessage message => ConversionExecutionReportMessage.encode message
  | .inquiryExecutionReportMessage message => InquiryExecutionReportMessage.encode message
  | .subscriptionExecutionReportMessage message => SubscriptionExecutionReportMessage.encode message
  | .putBackExecutionReportMessage message => PutBackExecutionReportMessage.encode message
  | .tenderOfferAcceptanceExecutionReportMessage message => TenderOfferAcceptanceExecutionReportMessage.encode message
  | .refinancingSecuritiesLendingNonAgreedExecutionReportMessage message => RefinancingSecuritiesLendingNonAgreedExecutionReportMessage.encode message
  | .bondSpotMatchingTradeExecutionReportMessage message => BondSpotMatchingTradeExecutionReportMessage.encode message
  | .centralizedAuctionTradeExecutionReportMessage message => CentralizedAuctionTradeExecutionReportMessage.encode message
  | .refinancingSecuritiesLendingNonAgreedTradeExecutionReportMessage message => RefinancingSecuritiesLendingNonAgreedTradeExecutionReportMessage.encode message
  | .bondSpotNegotiatedTradeCaptureReportMessage message => BondSpotNegotiatedTradeCaptureReportMessage.encode message
  | .refinancingSecuritiesLendingAgreedTradeCaptureReportMessage message => RefinancingSecuritiesLendingAgreedTradeCaptureReportMessage.encode message
  | .mutualTradeConfirmationTradeCaptureReportMessage message => MutualTradeConfirmationTradeCaptureReportMessage.encode message
  | .marketMakingMutualTradeConfirmationTradeCaptureReportMessage message => MarketMakingMutualTradeConfirmationTradeCaptureReportMessage.encode message
  | .afterHoursBlockTradeTradeCaptureReportMessage message => AfterHoursBlockTradeTradeCaptureReportMessage.encode message
  | .bondSpotNegotiatedTradeCaptureReportAckMessage message => BondSpotNegotiatedTradeCaptureReportAckMessage.encode message
  | .refinancingSecuritiesLendingAgreedTradeCaptureReportAckMessage message => RefinancingSecuritiesLendingAgreedTradeCaptureReportAckMessage.encode message
  | .mutualTradeConfirmationTradeCaptureReportAckMessage message => MutualTradeConfirmationTradeCaptureReportAckMessage.encode message
  | .marketMakingMutualTradeConfirmationTradeCaptureReportAckMessage message => MarketMakingMutualTradeConfirmationTradeCaptureReportAckMessage.encode message
  | .afterHoursBlockTradeTradeCaptureReportAckMessage message => AfterHoursBlockTradeTradeCaptureReportAckMessage.encode message
  | .bondSpotNegotiatedTradeCaptureReportConfirmationMessage message => BondSpotNegotiatedTradeCaptureReportConfirmationMessage.encode message
  | .refinancingSecuritiesLendingAgreedTradeCaptureReportConfirmationMessage message => RefinancingSecuritiesLendingAgreedTradeCaptureReportConfirmationMessage.encode message
  | .mutualTradeConfirmationTradeCaptureReportConfirmationMessage message => MutualTradeConfirmationTradeCaptureReportConfirmationMessage.encode message
  | .marketMakingMutualTradeConfirmationTradeCaptureReportConfirmationMessage message => MarketMakingMutualTradeConfirmationTradeCaptureReportConfirmationMessage.encode message
  | .afterHoursBlockTradeTradeCaptureReportConfirmationMessage message => AfterHoursBlockTradeTradeCaptureReportConfirmationMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 51539607544 := by
  cases message with
  | logonMessage inner =>
    simp only [encode, LogonMessage.encode_length]
    omega
  | logoutMessage inner =>
    simp only [encode, LogoutMessage.encode_length]
    omega
  | heartbeatMessage inner =>
    simp only [encode, HeartbeatMessage.encode_length]
    omega
  | businessRejectMessage inner =>
    simp only [encode, BusinessRejectMessage.encode_length]
    omega
  | reportSynchronizationMessage inner =>
    have bound_inner := ReportSynchronizationMessage.encode_length_le inner
    simp only [encode]
    omega
  | platformStateInfoMessage inner =>
    simp only [encode, PlatformStateInfoMessage.encode_length]
    omega
  | reportFinishedMessage inner =>
    simp only [encode, ReportFinishedMessage.encode_length]
    omega
  | platformInfoMessage inner =>
    have bound_inner := PlatformInfoMessage.encode_length_le inner
    simp only [encode]
    omega
  | tradingSessionStatusMessage inner =>
    simp only [encode, TradingSessionStatusMessage.encode_length]
    omega
  | bondSpotMatchingNewOrderMessage inner =>
    simp only [encode, BondSpotMatchingNewOrderMessage.encode_length]
    omega
  | centralizedAuctionNewOrderMessage inner =>
    simp only [encode, CentralizedAuctionNewOrderMessage.encode_length]
    omega
  | conversionNewOrderMessage inner =>
    simp only [encode, ConversionNewOrderMessage.encode_length]
    omega
  | inquiryNewOrderMessage inner =>
    simp only [encode, InquiryNewOrderMessage.encode_length]
    omega
  | subscriptionNewOrderMessage inner =>
    simp only [encode, SubscriptionNewOrderMessage.encode_length]
    omega
  | putBackNewOrderMessage inner =>
    simp only [encode, PutBackNewOrderMessage.encode_length]
    omega
  | tenderOfferAcceptanceNewOrderMessage inner =>
    simp only [encode, TenderOfferAcceptanceNewOrderMessage.encode_length]
    omega
  | refinancingSecuritiesLendingNonAgreedNewOrderMessage inner =>
    simp only [encode, RefinancingSecuritiesLendingNonAgreedNewOrderMessage.encode_length]
    omega
  | orderCancelRequestMessage inner =>
    simp only [encode, OrderCancelRequestMessage.encode_length]
    omega
  | cancelRejectMessage inner =>
    simp only [encode, CancelRejectMessage.encode_length]
    omega
  | bondSpotMatchingExecutionReportMessage inner =>
    simp only [encode, BondSpotMatchingExecutionReportMessage.encode_length]
    omega
  | centralizedAuctionExecutionReportMessage inner =>
    simp only [encode, CentralizedAuctionExecutionReportMessage.encode_length]
    omega
  | conversionExecutionReportMessage inner =>
    simp only [encode, ConversionExecutionReportMessage.encode_length]
    omega
  | inquiryExecutionReportMessage inner =>
    simp only [encode, InquiryExecutionReportMessage.encode_length]
    omega
  | subscriptionExecutionReportMessage inner =>
    simp only [encode, SubscriptionExecutionReportMessage.encode_length]
    omega
  | putBackExecutionReportMessage inner =>
    simp only [encode, PutBackExecutionReportMessage.encode_length]
    omega
  | tenderOfferAcceptanceExecutionReportMessage inner =>
    simp only [encode, TenderOfferAcceptanceExecutionReportMessage.encode_length]
    omega
  | refinancingSecuritiesLendingNonAgreedExecutionReportMessage inner =>
    simp only [encode, RefinancingSecuritiesLendingNonAgreedExecutionReportMessage.encode_length]
    omega
  | bondSpotMatchingTradeExecutionReportMessage inner =>
    simp only [encode, BondSpotMatchingTradeExecutionReportMessage.encode_length]
    omega
  | centralizedAuctionTradeExecutionReportMessage inner =>
    simp only [encode, CentralizedAuctionTradeExecutionReportMessage.encode_length]
    omega
  | refinancingSecuritiesLendingNonAgreedTradeExecutionReportMessage inner =>
    simp only [encode, RefinancingSecuritiesLendingNonAgreedTradeExecutionReportMessage.encode_length]
    omega
  | bondSpotNegotiatedTradeCaptureReportMessage inner =>
    simp only [encode, BondSpotNegotiatedTradeCaptureReportMessage.encode_length]
    omega
  | refinancingSecuritiesLendingAgreedTradeCaptureReportMessage inner =>
    simp only [encode, RefinancingSecuritiesLendingAgreedTradeCaptureReportMessage.encode_length]
    omega
  | mutualTradeConfirmationTradeCaptureReportMessage inner =>
    simp only [encode, MutualTradeConfirmationTradeCaptureReportMessage.encode_length]
    omega
  | marketMakingMutualTradeConfirmationTradeCaptureReportMessage inner =>
    simp only [encode, MarketMakingMutualTradeConfirmationTradeCaptureReportMessage.encode_length]
    omega
  | afterHoursBlockTradeTradeCaptureReportMessage inner =>
    simp only [encode, AfterHoursBlockTradeTradeCaptureReportMessage.encode_length]
    omega
  | bondSpotNegotiatedTradeCaptureReportAckMessage inner =>
    simp only [encode, BondSpotNegotiatedTradeCaptureReportAckMessage.encode_length]
    omega
  | refinancingSecuritiesLendingAgreedTradeCaptureReportAckMessage inner =>
    simp only [encode, RefinancingSecuritiesLendingAgreedTradeCaptureReportAckMessage.encode_length]
    omega
  | mutualTradeConfirmationTradeCaptureReportAckMessage inner =>
    simp only [encode, MutualTradeConfirmationTradeCaptureReportAckMessage.encode_length]
    omega
  | marketMakingMutualTradeConfirmationTradeCaptureReportAckMessage inner =>
    simp only [encode, MarketMakingMutualTradeConfirmationTradeCaptureReportAckMessage.encode_length]
    omega
  | afterHoursBlockTradeTradeCaptureReportAckMessage inner =>
    simp only [encode, AfterHoursBlockTradeTradeCaptureReportAckMessage.encode_length]
    omega
  | bondSpotNegotiatedTradeCaptureReportConfirmationMessage inner =>
    simp only [encode, BondSpotNegotiatedTradeCaptureReportConfirmationMessage.encode_length]
    omega
  | refinancingSecuritiesLendingAgreedTradeCaptureReportConfirmationMessage inner =>
    simp only [encode, RefinancingSecuritiesLendingAgreedTradeCaptureReportConfirmationMessage.encode_length]
    omega
  | mutualTradeConfirmationTradeCaptureReportConfirmationMessage inner =>
    simp only [encode, MutualTradeConfirmationTradeCaptureReportConfirmationMessage.encode_length]
    omega
  | marketMakingMutualTradeConfirmationTradeCaptureReportConfirmationMessage inner =>
    simp only [encode, MarketMakingMutualTradeConfirmationTradeCaptureReportConfirmationMessage.encode_length]
    omega
  | afterHoursBlockTradeTradeCaptureReportConfirmationMessage inner =>
    simp only [encode, AfterHoursBlockTradeTradeCaptureReportConfirmationMessage.encode_length]
    omega

def decode (tag : BitVec 32) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 1 then (LogonMessage.decode bytes).map fun (message, rest) => (.logonMessage message, rest)
  else if tag = 2 then (LogoutMessage.decode bytes).map fun (message, rest) => (.logoutMessage message, rest)
  else if tag = 3 then (HeartbeatMessage.decode bytes).map fun (message, rest) => (.heartbeatMessage message, rest)
  else if tag = 4 then (BusinessRejectMessage.decode bytes).map fun (message, rest) => (.businessRejectMessage message, rest)
  else if tag = 5 then (ReportSynchronizationMessage.decode bytes).map fun (message, rest) => (.reportSynchronizationMessage message, rest)
  else if tag = 6 then (PlatformStateInfoMessage.decode bytes).map fun (message, rest) => (.platformStateInfoMessage message, rest)
  else if tag = 7 then (ReportFinishedMessage.decode bytes).map fun (message, rest) => (.reportFinishedMessage message, rest)
  else if tag = 9 then (PlatformInfoMessage.decode bytes).map fun (message, rest) => (.platformInfoMessage message, rest)
  else if tag = 10 then (TradingSessionStatusMessage.decode bytes).map fun (message, rest) => (.tradingSessionStatusMessage message, rest)
  else if tag = 101010 then (BondSpotMatchingNewOrderMessage.decode bytes).map fun (message, rest) => (.bondSpotMatchingNewOrderMessage message, rest)
  else if tag = 101040 then (CentralizedAuctionNewOrderMessage.decode bytes).map fun (message, rest) => (.centralizedAuctionNewOrderMessage message, rest)
  else if tag = 101041 then (ConversionNewOrderMessage.decode bytes).map fun (message, rest) => (.conversionNewOrderMessage message, rest)
  else if tag = 101042 then (InquiryNewOrderMessage.decode bytes).map fun (message, rest) => (.inquiryNewOrderMessage message, rest)
  else if tag = 101043 then (SubscriptionNewOrderMessage.decode bytes).map fun (message, rest) => (.subscriptionNewOrderMessage message, rest)
  else if tag = 101044 then (PutBackNewOrderMessage.decode bytes).map fun (message, rest) => (.putBackNewOrderMessage message, rest)
  else if tag = 101045 then (TenderOfferAcceptanceNewOrderMessage.decode bytes).map fun (message, rest) => (.tenderOfferAcceptanceNewOrderMessage message, rest)
  else if tag = 101050 then (RefinancingSecuritiesLendingNonAgreedNewOrderMessage.decode bytes).map fun (message, rest) => (.refinancingSecuritiesLendingNonAgreedNewOrderMessage message, rest)
  else if tag = 102000 then (OrderCancelRequestMessage.decode bytes).map fun (message, rest) => (.orderCancelRequestMessage message, rest)
  else if tag = 201000 then (CancelRejectMessage.decode bytes).map fun (message, rest) => (.cancelRejectMessage message, rest)
  else if tag = 202010 then (BondSpotMatchingExecutionReportMessage.decode bytes).map fun (message, rest) => (.bondSpotMatchingExecutionReportMessage message, rest)
  else if tag = 202040 then (CentralizedAuctionExecutionReportMessage.decode bytes).map fun (message, rest) => (.centralizedAuctionExecutionReportMessage message, rest)
  else if tag = 202041 then (ConversionExecutionReportMessage.decode bytes).map fun (message, rest) => (.conversionExecutionReportMessage message, rest)
  else if tag = 202042 then (InquiryExecutionReportMessage.decode bytes).map fun (message, rest) => (.inquiryExecutionReportMessage message, rest)
  else if tag = 202043 then (SubscriptionExecutionReportMessage.decode bytes).map fun (message, rest) => (.subscriptionExecutionReportMessage message, rest)
  else if tag = 202044 then (PutBackExecutionReportMessage.decode bytes).map fun (message, rest) => (.putBackExecutionReportMessage message, rest)
  else if tag = 202045 then (TenderOfferAcceptanceExecutionReportMessage.decode bytes).map fun (message, rest) => (.tenderOfferAcceptanceExecutionReportMessage message, rest)
  else if tag = 202050 then (RefinancingSecuritiesLendingNonAgreedExecutionReportMessage.decode bytes).map fun (message, rest) => (.refinancingSecuritiesLendingNonAgreedExecutionReportMessage message, rest)
  else if tag = 203010 then (BondSpotMatchingTradeExecutionReportMessage.decode bytes).map fun (message, rest) => (.bondSpotMatchingTradeExecutionReportMessage message, rest)
  else if tag = 203040 then (CentralizedAuctionTradeExecutionReportMessage.decode bytes).map fun (message, rest) => (.centralizedAuctionTradeExecutionReportMessage message, rest)
  else if tag = 203050 then (RefinancingSecuritiesLendingNonAgreedTradeExecutionReportMessage.decode bytes).map fun (message, rest) => (.refinancingSecuritiesLendingNonAgreedTradeExecutionReportMessage message, rest)
  else if tag = 103031 then (BondSpotNegotiatedTradeCaptureReportMessage.decode bytes).map fun (message, rest) => (.bondSpotNegotiatedTradeCaptureReportMessage message, rest)
  else if tag = 103051 then (RefinancingSecuritiesLendingAgreedTradeCaptureReportMessage.decode bytes).map fun (message, rest) => (.refinancingSecuritiesLendingAgreedTradeCaptureReportMessage message, rest)
  else if tag = 103060 then (MutualTradeConfirmationTradeCaptureReportMessage.decode bytes).map fun (message, rest) => (.mutualTradeConfirmationTradeCaptureReportMessage message, rest)
  else if tag = 103061 then (MarketMakingMutualTradeConfirmationTradeCaptureReportMessage.decode bytes).map fun (message, rest) => (.marketMakingMutualTradeConfirmationTradeCaptureReportMessage message, rest)
  else if tag = 103062 then (AfterHoursBlockTradeTradeCaptureReportMessage.decode bytes).map fun (message, rest) => (.afterHoursBlockTradeTradeCaptureReportMessage message, rest)
  else if tag = 204031 then (BondSpotNegotiatedTradeCaptureReportAckMessage.decode bytes).map fun (message, rest) => (.bondSpotNegotiatedTradeCaptureReportAckMessage message, rest)
  else if tag = 204051 then (RefinancingSecuritiesLendingAgreedTradeCaptureReportAckMessage.decode bytes).map fun (message, rest) => (.refinancingSecuritiesLendingAgreedTradeCaptureReportAckMessage message, rest)
  else if tag = 204060 then (MutualTradeConfirmationTradeCaptureReportAckMessage.decode bytes).map fun (message, rest) => (.mutualTradeConfirmationTradeCaptureReportAckMessage message, rest)
  else if tag = 204061 then (MarketMakingMutualTradeConfirmationTradeCaptureReportAckMessage.decode bytes).map fun (message, rest) => (.marketMakingMutualTradeConfirmationTradeCaptureReportAckMessage message, rest)
  else if tag = 204062 then (AfterHoursBlockTradeTradeCaptureReportAckMessage.decode bytes).map fun (message, rest) => (.afterHoursBlockTradeTradeCaptureReportAckMessage message, rest)
  else if tag = 205031 then (BondSpotNegotiatedTradeCaptureReportConfirmationMessage.decode bytes).map fun (message, rest) => (.bondSpotNegotiatedTradeCaptureReportConfirmationMessage message, rest)
  else if tag = 205051 then (RefinancingSecuritiesLendingAgreedTradeCaptureReportConfirmationMessage.decode bytes).map fun (message, rest) => (.refinancingSecuritiesLendingAgreedTradeCaptureReportConfirmationMessage message, rest)
  else if tag = 205060 then (MutualTradeConfirmationTradeCaptureReportConfirmationMessage.decode bytes).map fun (message, rest) => (.mutualTradeConfirmationTradeCaptureReportConfirmationMessage message, rest)
  else if tag = 205061 then (MarketMakingMutualTradeConfirmationTradeCaptureReportConfirmationMessage.decode bytes).map fun (message, rest) => (.marketMakingMutualTradeConfirmationTradeCaptureReportConfirmationMessage message, rest)
  else if tag = 205062 then (AfterHoursBlockTradeTradeCaptureReportConfirmationMessage.decode bytes).map fun (message, rest) => (.afterHoursBlockTradeTradeCaptureReportConfirmationMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message Tail: 4 bytes -/
structure MessageTail where
  checksum : BitVec 32
  deriving DecidableEq, Repr

namespace MessageTail

def encode (message : MessageTail) : List UInt8 :=
  encodeUInt 4 message.checksum

def decode (bytes : List UInt8) : Option (MessageTail × List UInt8) := do
  let (checksum, bytes) ← decodeUInt 4 bytes
  pure ({ checksum }, bytes)

@[simp] theorem encode_length (message : MessageTail) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : MessageTail) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MessageTail) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MessageTail

/-- Message -/
structure Message where
  bodyLength : BitVec 32
  payload : Payload
  messageTail : MessageTail
  deriving DecidableEq, Repr

namespace Message

def encode (message : Message) : List UInt8 :=
  encodeUInt 4 (Payload.tag message.payload)
    ++ (encodeUInt 4 message.bodyLength
    ++ (Payload.encode message.payload
    ++ (MessageTail.encode message.messageTail)))

def decode (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (msgType, bytes) ← decodeUInt 4 bytes
  let (bodyLength, bytes) ← decodeUInt 4 bytes
  let (payload, bytes) ← Payload.decode msgType bytes
  let (messageTail, bytes) ← MessageTail.decode bytes
  pure ({ bodyLength, payload, messageTail }, bytes)

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Message) : (encode message).length ≤ 51539607556 := by
  unfold encode
  cases message.payload with
  | logonMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, LogonMessage.encode_length]
    omega
  | logoutMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, LogoutMessage.encode_length]
    omega
  | heartbeatMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, HeartbeatMessage.encode_length]
    omega
  | businessRejectMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, BusinessRejectMessage.encode_length]
    omega
  | reportSynchronizationMessage inner =>
    have bound_inner := ReportSynchronizationMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length]
    omega
  | platformStateInfoMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, PlatformStateInfoMessage.encode_length]
    omega
  | reportFinishedMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, ReportFinishedMessage.encode_length]
    omega
  | platformInfoMessage inner =>
    have bound_inner := PlatformInfoMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length]
    omega
  | tradingSessionStatusMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, TradingSessionStatusMessage.encode_length]
    omega
  | bondSpotMatchingNewOrderMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, BondSpotMatchingNewOrderMessage.encode_length]
    omega
  | centralizedAuctionNewOrderMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, CentralizedAuctionNewOrderMessage.encode_length]
    omega
  | conversionNewOrderMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, ConversionNewOrderMessage.encode_length]
    omega
  | inquiryNewOrderMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, InquiryNewOrderMessage.encode_length]
    omega
  | subscriptionNewOrderMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, SubscriptionNewOrderMessage.encode_length]
    omega
  | putBackNewOrderMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, PutBackNewOrderMessage.encode_length]
    omega
  | tenderOfferAcceptanceNewOrderMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, TenderOfferAcceptanceNewOrderMessage.encode_length]
    omega
  | refinancingSecuritiesLendingNonAgreedNewOrderMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, RefinancingSecuritiesLendingNonAgreedNewOrderMessage.encode_length]
    omega
  | orderCancelRequestMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, OrderCancelRequestMessage.encode_length]
    omega
  | cancelRejectMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, CancelRejectMessage.encode_length]
    omega
  | bondSpotMatchingExecutionReportMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, BondSpotMatchingExecutionReportMessage.encode_length]
    omega
  | centralizedAuctionExecutionReportMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, CentralizedAuctionExecutionReportMessage.encode_length]
    omega
  | conversionExecutionReportMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, ConversionExecutionReportMessage.encode_length]
    omega
  | inquiryExecutionReportMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, InquiryExecutionReportMessage.encode_length]
    omega
  | subscriptionExecutionReportMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, SubscriptionExecutionReportMessage.encode_length]
    omega
  | putBackExecutionReportMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, PutBackExecutionReportMessage.encode_length]
    omega
  | tenderOfferAcceptanceExecutionReportMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, TenderOfferAcceptanceExecutionReportMessage.encode_length]
    omega
  | refinancingSecuritiesLendingNonAgreedExecutionReportMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, RefinancingSecuritiesLendingNonAgreedExecutionReportMessage.encode_length]
    omega
  | bondSpotMatchingTradeExecutionReportMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, BondSpotMatchingTradeExecutionReportMessage.encode_length]
    omega
  | centralizedAuctionTradeExecutionReportMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, CentralizedAuctionTradeExecutionReportMessage.encode_length]
    omega
  | refinancingSecuritiesLendingNonAgreedTradeExecutionReportMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, RefinancingSecuritiesLendingNonAgreedTradeExecutionReportMessage.encode_length]
    omega
  | bondSpotNegotiatedTradeCaptureReportMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, BondSpotNegotiatedTradeCaptureReportMessage.encode_length]
    omega
  | refinancingSecuritiesLendingAgreedTradeCaptureReportMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, RefinancingSecuritiesLendingAgreedTradeCaptureReportMessage.encode_length]
    omega
  | mutualTradeConfirmationTradeCaptureReportMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, MutualTradeConfirmationTradeCaptureReportMessage.encode_length]
    omega
  | marketMakingMutualTradeConfirmationTradeCaptureReportMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, MarketMakingMutualTradeConfirmationTradeCaptureReportMessage.encode_length]
    omega
  | afterHoursBlockTradeTradeCaptureReportMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, AfterHoursBlockTradeTradeCaptureReportMessage.encode_length]
    omega
  | bondSpotNegotiatedTradeCaptureReportAckMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, BondSpotNegotiatedTradeCaptureReportAckMessage.encode_length]
    omega
  | refinancingSecuritiesLendingAgreedTradeCaptureReportAckMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, RefinancingSecuritiesLendingAgreedTradeCaptureReportAckMessage.encode_length]
    omega
  | mutualTradeConfirmationTradeCaptureReportAckMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, MutualTradeConfirmationTradeCaptureReportAckMessage.encode_length]
    omega
  | marketMakingMutualTradeConfirmationTradeCaptureReportAckMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, MarketMakingMutualTradeConfirmationTradeCaptureReportAckMessage.encode_length]
    omega
  | afterHoursBlockTradeTradeCaptureReportAckMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, AfterHoursBlockTradeTradeCaptureReportAckMessage.encode_length]
    omega
  | bondSpotNegotiatedTradeCaptureReportConfirmationMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, BondSpotNegotiatedTradeCaptureReportConfirmationMessage.encode_length]
    omega
  | refinancingSecuritiesLendingAgreedTradeCaptureReportConfirmationMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, RefinancingSecuritiesLendingAgreedTradeCaptureReportConfirmationMessage.encode_length]
    omega
  | mutualTradeConfirmationTradeCaptureReportConfirmationMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, MutualTradeConfirmationTradeCaptureReportConfirmationMessage.encode_length]
    omega
  | marketMakingMutualTradeConfirmationTradeCaptureReportConfirmationMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, MarketMakingMutualTradeConfirmationTradeCaptureReportConfirmationMessage.encode_length]
    omega
  | afterHoursBlockTradeTradeCaptureReportConfirmationMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MessageTail.encode_length, AfterHoursBlockTradeTradeCaptureReportConfirmationMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Payload.decode_encode, some_bind]
  dsimp only
  rw [MessageTail.decode_encode, some_bind]
  rfl

end Message

end Omi.BjseBjsesecuritiesOrderentryBjsebinaryV11
