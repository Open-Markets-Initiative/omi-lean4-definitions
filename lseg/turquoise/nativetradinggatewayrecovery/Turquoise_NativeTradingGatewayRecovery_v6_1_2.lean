import Wire

/-!
# London Stock Exchange Native Trading Gateway Recovery v6.1.2

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.

License: MIT No Attribution
-/

namespace Omi.LsegTurquoiseNativetradinggatewayrecoveryNtgiV612

/-- Exec Type: one byte code -/
def ExecType.codes : List UInt8 :=
  [0x30, 0x34, 0x35, 0x36, 0x38, 0x43, 0x44, 0x46, 0x48, 0x4C]

inductive ExecType where
  | new -- New
  | cancelled -- Cancelled
  | replaced -- Replaced
  | pendingCancel -- Pending Cancel
  | rejected -- Rejected
  | expired -- Expired
  | restated -- Restated
  | trade -- Trade
  | tradeCancel -- Trade Cancel
  | triggered -- Triggered
  | unlisted (byte : { byte : UInt8 // byte ∉ ExecType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExecType

def toByte : ExecType → UInt8
  | .new => 0x30
  | .cancelled => 0x34
  | .replaced => 0x35
  | .pendingCancel => 0x36
  | .rejected => 0x38
  | .expired => 0x43
  | .restated => 0x44
  | .trade => 0x46
  | .tradeCancel => 0x48
  | .triggered => 0x4C
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExecType :=
  if byte = 0x30 then .new
  else if byte = 0x34 then .cancelled
  else if byte = 0x35 then .replaced
  else if byte = 0x36 then .pendingCancel
  else if byte = 0x38 then .rejected
  else if byte = 0x43 then .expired
  else if byte = 0x44 then .restated
  else if byte = 0x46 then .trade
  else if byte = 0x48 then .tradeCancel
  else .triggered

def ofByte (byte : UInt8) : ExecType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExecType) : ofByte value.toByte = value := by
  cases value with
  | new => decide
  | cancelled => decide
  | replaced => decide
  | pendingCancel => decide
  | rejected => decide
  | expired => decide
  | restated => decide
  | trade => decide
  | tradeCancel => decide
  | triggered => decide
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

/-- Trade Liquidity Indicator: one byte code -/
def TradeLiquidityIndicator.codes : List UInt8 :=
  [0x41, 0x52, 0x43, 0x53, 0x42]

inductive TradeLiquidityIndicator where
  | addedLiquidity -- Added Liquidity
  | removedLiquidity -- Removed Liquidity
  | turquoiseDarkUncrossOrPeriodicAuctionsExecution -- Turquoise Dark Uncross Or Periodic Auctions Execution
  | turquoiseBlockDiscoveryExecutionTurquoiseDarkUncross -- Turquoise Block Discovery Execution Turquoise Dark Uncross
  | btfTrade -- Btf Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeLiquidityIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeLiquidityIndicator

def toByte : TradeLiquidityIndicator → UInt8
  | .addedLiquidity => 0x41
  | .removedLiquidity => 0x52
  | .turquoiseDarkUncrossOrPeriodicAuctionsExecution => 0x43
  | .turquoiseBlockDiscoveryExecutionTurquoiseDarkUncross => 0x53
  | .btfTrade => 0x42
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeLiquidityIndicator :=
  if byte = 0x41 then .addedLiquidity
  else if byte = 0x52 then .removedLiquidity
  else if byte = 0x43 then .turquoiseDarkUncrossOrPeriodicAuctionsExecution
  else if byte = 0x53 then .turquoiseBlockDiscoveryExecutionTurquoiseDarkUncross
  else .btfTrade

def ofByte (byte : UInt8) : TradeLiquidityIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeLiquidityIndicator) : ofByte value.toByte = value := by
  cases value with
  | addedLiquidity => decide
  | removedLiquidity => decide
  | turquoiseDarkUncrossOrPeriodicAuctionsExecution => decide
  | turquoiseBlockDiscoveryExecutionTurquoiseDarkUncross => decide
  | btfTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeLiquidityIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeLiquidityIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeLiquidityIndicator) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TradeLiquidityIndicator) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TradeLiquidityIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeLiquidityIndicator

/-- Logon Message: 76 bytes -/
structure LogonMessage where
  compId : Alpha 25
  password : Alpha 25
  newPassword : Alpha 25
  messageVersion : BitVec 8
  deriving DecidableEq, Repr

namespace LogonMessage

def encode (message : LogonMessage) : List UInt8 :=
  Alpha.encode message.compId
    ++ (Alpha.encode message.password
    ++ (Alpha.encode message.newPassword
    ++ (encodeUInt 1 message.messageVersion)))

def decode (bytes : List UInt8) : Option (LogonMessage × List UInt8) := do
  let (compId, bytes) ← Alpha.decode 25 bytes
  let (password, bytes) ← Alpha.decode 25 bytes
  let (newPassword, bytes) ← Alpha.decode 25 bytes
  let (messageVersion, bytes) ← decodeUInt 1 bytes
  pure ({ compId, password, newPassword, messageVersion }, bytes)

@[simp] theorem encode_length (message : LogonMessage) : (encode message).length = 76 := by
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end LogonMessage

/-- Logon Reply Message: 34 bytes -/
structure LogonReplyMessage where
  rejectCode : BitVec 32
  passwordExpiryDayCount : Alpha 30
  deriving DecidableEq, Repr

namespace LogonReplyMessage

def encode (message : LogonReplyMessage) : List UInt8 :=
  encodeUIntLE 4 message.rejectCode
    ++ (Alpha.encode message.passwordExpiryDayCount)

def decode (bytes : List UInt8) : Option (LogonReplyMessage × List UInt8) := do
  let (rejectCode, bytes) ← decodeUIntLE 4 bytes
  let (passwordExpiryDayCount, bytes) ← Alpha.decode 30 bytes
  pure ({ rejectCode, passwordExpiryDayCount }, bytes)

@[simp] theorem encode_length (message : LogonReplyMessage) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : LogonReplyMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogonReplyMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LogonReplyMessage

/-- Logout Message: 20 bytes -/
structure LogoutMessage where
  logoutReason : Alpha 20
  deriving DecidableEq, Repr

namespace LogoutMessage

def encode (message : LogoutMessage) : List UInt8 :=
  Alpha.encode message.logoutReason

def decode (bytes : List UInt8) : Option (LogoutMessage × List UInt8) := do
  let (logoutReason, bytes) ← Alpha.decode 20 bytes
  pure ({ logoutReason }, bytes)

@[simp] theorem encode_length (message : LogoutMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : LogoutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogoutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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

/-- Missed Message Request Message: 5 bytes -/
structure MissedMessageRequestMessage where
  appId : BitVec 8
  lastMsgSeqNum : BitVec 32
  deriving DecidableEq, Repr

namespace MissedMessageRequestMessage

def encode (message : MissedMessageRequestMessage) : List UInt8 :=
  encodeUInt 1 message.appId
    ++ (encodeUIntLE 4 message.lastMsgSeqNum)

def decode (bytes : List UInt8) : Option (MissedMessageRequestMessage × List UInt8) := do
  let (appId, bytes) ← decodeUInt 1 bytes
  let (lastMsgSeqNum, bytes) ← decodeUIntLE 4 bytes
  pure ({ appId, lastMsgSeqNum }, bytes)

@[simp] theorem encode_length (message : MissedMessageRequestMessage) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeUIntLE_length]

theorem encode_length_pos (message : MissedMessageRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MissedMessageRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end MissedMessageRequestMessage

/-- Missed Message Request Ack Message: 1 bytes -/
structure MissedMessageRequestAckMessage where
  missedMessageRequestAckResponseType : BitVec 8
  deriving DecidableEq, Repr

namespace MissedMessageRequestAckMessage

def encode (message : MissedMessageRequestAckMessage) : List UInt8 :=
  encodeUInt 1 message.missedMessageRequestAckResponseType

def decode (bytes : List UInt8) : Option (MissedMessageRequestAckMessage × List UInt8) := do
  let (missedMessageRequestAckResponseType, bytes) ← decodeUInt 1 bytes
  pure ({ missedMessageRequestAckResponseType }, bytes)

@[simp] theorem encode_length (message : MissedMessageRequestAckMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : MissedMessageRequestAckMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MissedMessageRequestAckMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MissedMessageRequestAckMessage

/-- Missed Message Report Message: 1 bytes -/
structure MissedMessageReportMessage where
  missedMessageReportResponseType : BitVec 8
  deriving DecidableEq, Repr

namespace MissedMessageReportMessage

def encode (message : MissedMessageReportMessage) : List UInt8 :=
  encodeUInt 1 message.missedMessageReportResponseType

def decode (bytes : List UInt8) : Option (MissedMessageReportMessage × List UInt8) := do
  let (missedMessageReportResponseType, bytes) ← decodeUInt 1 bytes
  pure ({ missedMessageReportResponseType }, bytes)

@[simp] theorem encode_length (message : MissedMessageReportMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : MissedMessageReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MissedMessageReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MissedMessageReportMessage

/-- Reject Message: 55 bytes -/
structure RejectMessage where
  rejectCode : BitVec 32
  rejectReason : Alpha 30
  rejectedMessageType : Alpha 1
  clientOrderId : Alpha 20
  deriving DecidableEq, Repr

namespace RejectMessage

def encode (message : RejectMessage) : List UInt8 :=
  encodeUIntLE 4 message.rejectCode
    ++ (Alpha.encode message.rejectReason
    ++ (Alpha.encode message.rejectedMessageType
    ++ (Alpha.encode message.clientOrderId)))

def decode (bytes : List UInt8) : Option (RejectMessage × List UInt8) := do
  let (rejectCode, bytes) ← decodeUIntLE 4 bytes
  let (rejectReason, bytes) ← Alpha.decode 30 bytes
  let (rejectedMessageType, bytes) ← Alpha.decode 1 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  pure ({ rejectCode, rejectReason, rejectedMessageType, clientOrderId }, bytes)

@[simp] theorem encode_length (message : RejectMessage) : (encode message).length = 55 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : RejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end RejectMessage

/-- System Status Message: 2 bytes -/
structure SystemStatusMessage where
  appId : BitVec 8
  appStatus : BitVec 8
  deriving DecidableEq, Repr

namespace SystemStatusMessage

def encode (message : SystemStatusMessage) : List UInt8 :=
  encodeUInt 1 message.appId
    ++ (encodeUInt 1 message.appStatus)

def decode (bytes : List UInt8) : Option (SystemStatusMessage × List UInt8) := do
  let (appId, bytes) ← decodeUInt 1 bytes
  let (appStatus, bytes) ← decodeUInt 1 bytes
  pure ({ appId, appStatus }, bytes)

@[simp] theorem encode_length (message : SystemStatusMessage) : (encode message).length = 2 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : SystemStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SystemStatusMessage

/-- Transact Time: 8 bytes -/
structure TransactTime where
  seconds : BitVec 32
  nanoseconds : BitVec 32
  deriving DecidableEq, Repr

namespace TransactTime

def encode (message : TransactTime) : List UInt8 :=
  encodeUIntLE 4 message.seconds
    ++ (encodeUIntLE 4 message.nanoseconds)

def decode (bytes : List UInt8) : Option (TransactTime × List UInt8) := do
  let (seconds, bytes) ← decodeUIntLE 4 bytes
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  pure ({ seconds, nanoseconds }, bytes)

@[simp] theorem encode_length (message : TransactTime) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : TransactTime) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TransactTime) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TransactTime

/-- Execution Report Message: 179 bytes -/
structure ExecutionReportMessage where
  appId : BitVec 8
  sequenceNo : BitVec 32
  executionId : Alpha 12
  clientOrderId : Alpha 20
  orderId : Alpha 12
  execType : ExecType
  executionReportRefId : Alpha 12
  orderStatus : BitVec 8
  orderRejectCode : BitVec 32
  executedPrice : BitVec 64
  executedQty : BitVec 32
  leavesQty : BitVec 32
  waiverFlags : BitVec 8
  displayQty : BitVec 32
  commonSymbol : Alpha 8
  side : BitVec 8
  secondaryOrderId : BitVec 64
  counterparty : Alpha 11
  tradeLiquidityIndicator : TradeLiquidityIndicator
  tradeMatchId : BitVec 64
  transactTime : TransactTime
  targetBook : BitVec 8
  typeOfTrade : BitVec 8
  capacity : BitVec 8
  reserved1 : Alpha 1
  publicOrderId : Alpha 12
  minimumQuantity : BitVec 32
  reputationalScore : BitVec 8
  lastMarket : BitVec 8
  pegPriceType : BitVec 8
  ownerType : BitVec 8
  waiverFlags2 : BitVec 8
  reserved21 : Alpha 21
  deriving DecidableEq, Repr

namespace ExecutionReportMessage

def encode (message : ExecutionReportMessage) : List UInt8 :=
  encodeUInt 1 message.appId
    ++ (encodeUIntLE 4 message.sequenceNo
    ++ (Alpha.encode message.executionId
    ++ (Alpha.encode message.clientOrderId
    ++ (Alpha.encode message.orderId
    ++ (ExecType.encode message.execType
    ++ (Alpha.encode message.executionReportRefId
    ++ (encodeUInt 1 message.orderStatus
    ++ (encodeUIntLE 4 message.orderRejectCode
    ++ (encodeUIntLE 8 message.executedPrice
    ++ (encodeUIntLE 4 message.executedQty
    ++ (encodeUIntLE 4 message.leavesQty
    ++ (encodeUInt 1 message.waiverFlags
    ++ (encodeUIntLE 4 message.displayQty
    ++ (Alpha.encode message.commonSymbol
    ++ (encodeUInt 1 message.side
    ++ (encodeUIntLE 8 message.secondaryOrderId
    ++ (Alpha.encode message.counterparty
    ++ (TradeLiquidityIndicator.encode message.tradeLiquidityIndicator
    ++ (encodeUIntLE 8 message.tradeMatchId
    ++ (TransactTime.encode message.transactTime
    ++ (encodeUInt 1 message.targetBook
    ++ (encodeUInt 1 message.typeOfTrade
    ++ (encodeUInt 1 message.capacity
    ++ (Alpha.encode message.reserved1
    ++ (Alpha.encode message.publicOrderId
    ++ (encodeUIntLE 4 message.minimumQuantity
    ++ (encodeUInt 1 message.reputationalScore
    ++ (encodeUInt 1 message.lastMarket
    ++ (encodeUInt 1 message.pegPriceType
    ++ (encodeUInt 1 message.ownerType
    ++ (encodeUInt 1 message.waiverFlags2
    ++ (Alpha.encode message.reserved21))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ExecutionReportMessage × List UInt8) := do
  let (appId, bytes) ← decodeUInt 1 bytes
  let (sequenceNo, bytes) ← decodeUIntLE 4 bytes
  let (executionId, bytes) ← Alpha.decode 12 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (orderId, bytes) ← Alpha.decode 12 bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (executionReportRefId, bytes) ← Alpha.decode 12 bytes
  let (orderStatus, bytes) ← decodeUInt 1 bytes
  let (orderRejectCode, bytes) ← decodeUIntLE 4 bytes
  let (executedPrice, bytes) ← decodeUIntLE 8 bytes
  let (executedQty, bytes) ← decodeUIntLE 4 bytes
  let (leavesQty, bytes) ← decodeUIntLE 4 bytes
  let (waiverFlags, bytes) ← decodeUInt 1 bytes
  let (displayQty, bytes) ← decodeUIntLE 4 bytes
  let (commonSymbol, bytes) ← Alpha.decode 8 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (secondaryOrderId, bytes) ← decodeUIntLE 8 bytes
  let (counterparty, bytes) ← Alpha.decode 11 bytes
  let (tradeLiquidityIndicator, bytes) ← TradeLiquidityIndicator.decode bytes
  let (tradeMatchId, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← TransactTime.decode bytes
  let (targetBook, bytes) ← decodeUInt 1 bytes
  let (typeOfTrade, bytes) ← decodeUInt 1 bytes
  let (capacity, bytes) ← decodeUInt 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (publicOrderId, bytes) ← Alpha.decode 12 bytes
  let (minimumQuantity, bytes) ← decodeUIntLE 4 bytes
  let (reputationalScore, bytes) ← decodeUInt 1 bytes
  let (lastMarket, bytes) ← decodeUInt 1 bytes
  let (pegPriceType, bytes) ← decodeUInt 1 bytes
  let (ownerType, bytes) ← decodeUInt 1 bytes
  let (waiverFlags2, bytes) ← decodeUInt 1 bytes
  let (reserved21, bytes) ← Alpha.decode 21 bytes
  pure ({ appId, sequenceNo, executionId, clientOrderId, orderId, execType, executionReportRefId, orderStatus, orderRejectCode, executedPrice, executedQty, leavesQty, waiverFlags, displayQty, commonSymbol, side, secondaryOrderId, counterparty, tradeLiquidityIndicator, tradeMatchId, transactTime, targetBook, typeOfTrade, capacity, reserved1, publicOrderId, minimumQuantity, reputationalScore, lastMarket, pegPriceType, ownerType, waiverFlags2, reserved21 }, bytes)

@[simp] theorem encode_length (message : ExecutionReportMessage) : (encode message).length = 179 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeUIntLE_length, Alpha.encode_length, ExecType.encode_length, TradeLiquidityIndicator.encode_length, TransactTime.encode_length]

theorem encode_length_pos (message : ExecutionReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ExecutionReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeLiquidityIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TransactTime.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end ExecutionReportMessage

/-- Order Cancel Reject Message: 59 bytes -/
structure OrderCancelRejectMessage where
  appId : BitVec 8
  sequenceNo : BitVec 32
  clientOrderId : Alpha 20
  orderId : Alpha 12
  cancelRejectReason : BitVec 32
  transactTime : TransactTime
  reserved10 : Alpha 10
  deriving DecidableEq, Repr

namespace OrderCancelRejectMessage

def encode (message : OrderCancelRejectMessage) : List UInt8 :=
  encodeUInt 1 message.appId
    ++ (encodeUIntLE 4 message.sequenceNo
    ++ (Alpha.encode message.clientOrderId
    ++ (Alpha.encode message.orderId
    ++ (encodeUIntLE 4 message.cancelRejectReason
    ++ (TransactTime.encode message.transactTime
    ++ (Alpha.encode message.reserved10))))))

def decode (bytes : List UInt8) : Option (OrderCancelRejectMessage × List UInt8) := do
  let (appId, bytes) ← decodeUInt 1 bytes
  let (sequenceNo, bytes) ← decodeUIntLE 4 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (orderId, bytes) ← Alpha.decode 12 bytes
  let (cancelRejectReason, bytes) ← decodeUIntLE 4 bytes
  let (transactTime, bytes) ← TransactTime.decode bytes
  let (reserved10, bytes) ← Alpha.decode 10 bytes
  pure ({ appId, sequenceNo, clientOrderId, orderId, cancelRejectReason, transactTime, reserved10 }, bytes)

@[simp] theorem encode_length (message : OrderCancelRejectMessage) : (encode message).length = 59 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeUIntLE_length, Alpha.encode_length, TransactTime.encode_length]

theorem encode_length_pos (message : OrderCancelRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancelRejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TransactTime.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderCancelRejectMessage

/-- Order Mass Cancel Report Message: 52 bytes -/
structure OrderMassCancelReportMessage where
  appId : BitVec 8
  sequenceNo : BitVec 32
  clientOrderId : Alpha 20
  massCancelResponse : BitVec 8
  massCancelRejectReason : BitVec 32
  reserved4 : Alpha 4
  transactTime : TransactTime
  reserved10 : Alpha 10
  deriving DecidableEq, Repr

namespace OrderMassCancelReportMessage

def encode (message : OrderMassCancelReportMessage) : List UInt8 :=
  encodeUInt 1 message.appId
    ++ (encodeUIntLE 4 message.sequenceNo
    ++ (Alpha.encode message.clientOrderId
    ++ (encodeUInt 1 message.massCancelResponse
    ++ (encodeUIntLE 4 message.massCancelRejectReason
    ++ (Alpha.encode message.reserved4
    ++ (TransactTime.encode message.transactTime
    ++ (Alpha.encode message.reserved10)))))))

def decode (bytes : List UInt8) : Option (OrderMassCancelReportMessage × List UInt8) := do
  let (appId, bytes) ← decodeUInt 1 bytes
  let (sequenceNo, bytes) ← decodeUIntLE 4 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (massCancelResponse, bytes) ← decodeUInt 1 bytes
  let (massCancelRejectReason, bytes) ← decodeUIntLE 4 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (transactTime, bytes) ← TransactTime.decode bytes
  let (reserved10, bytes) ← Alpha.decode 10 bytes
  pure ({ appId, sequenceNo, clientOrderId, massCancelResponse, massCancelRejectReason, reserved4, transactTime, reserved10 }, bytes)

@[simp] theorem encode_length (message : OrderMassCancelReportMessage) : (encode message).length = 52 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeUIntLE_length, Alpha.encode_length, TransactTime.encode_length]

theorem encode_length_pos (message : OrderMassCancelReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderMassCancelReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TransactTime.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderMassCancelReportMessage

/-- Business Reject Message: 59 bytes -/
structure BusinessRejectMessage where
  appId : BitVec 8
  sequenceNo : BitVec 32
  rejectCode : BitVec 32
  clientOrderId : Alpha 20
  orderId : Alpha 12
  transactTime : TransactTime
  reserved10 : Alpha 10
  deriving DecidableEq, Repr

namespace BusinessRejectMessage

def encode (message : BusinessRejectMessage) : List UInt8 :=
  encodeUInt 1 message.appId
    ++ (encodeUIntLE 4 message.sequenceNo
    ++ (encodeUIntLE 4 message.rejectCode
    ++ (Alpha.encode message.clientOrderId
    ++ (Alpha.encode message.orderId
    ++ (TransactTime.encode message.transactTime
    ++ (Alpha.encode message.reserved10))))))

def decode (bytes : List UInt8) : Option (BusinessRejectMessage × List UInt8) := do
  let (appId, bytes) ← decodeUInt 1 bytes
  let (sequenceNo, bytes) ← decodeUIntLE 4 bytes
  let (rejectCode, bytes) ← decodeUIntLE 4 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (orderId, bytes) ← Alpha.decode 12 bytes
  let (transactTime, bytes) ← TransactTime.decode bytes
  let (reserved10, bytes) ← Alpha.decode 10 bytes
  pure ({ appId, sequenceNo, rejectCode, clientOrderId, orderId, transactTime, reserved10 }, bytes)

@[simp] theorem encode_length (message : BusinessRejectMessage) : (encode message).length = 59 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeUIntLE_length, Alpha.encode_length, TransactTime.encode_length]

theorem encode_length_pos (message : BusinessRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BusinessRejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TransactTime.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BusinessRejectMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | logonMessage (message : LogonMessage) -- "A" 0x41
  | logonReplyMessage (message : LogonReplyMessage) -- "B" 0x42
  | logoutMessage (message : LogoutMessage) -- "5" 0x35
  | heartbeatMessage (message : HeartbeatMessage) -- "0" 0x30
  | missedMessageRequestMessage (message : MissedMessageRequestMessage) -- "M" 0x4D
  | missedMessageRequestAckMessage (message : MissedMessageRequestAckMessage) -- "N" 0x4E
  | missedMessageReportMessage (message : MissedMessageReportMessage) -- "P" 0x50
  | rejectMessage (message : RejectMessage) -- "3" 0x33
  | systemStatusMessage (message : SystemStatusMessage) -- "n" 0x6E
  | executionReportMessage (message : ExecutionReportMessage) -- "8" 0x38
  | orderCancelRejectMessage (message : OrderCancelRejectMessage) -- "9" 0x39
  | orderMassCancelReportMessage (message : OrderMassCancelReportMessage) -- "r" 0x72
  | businessRejectMessage (message : BusinessRejectMessage) -- "j" 0x6A
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .logonMessage _ => 65
  | .logonReplyMessage _ => 66
  | .logoutMessage _ => 53
  | .heartbeatMessage _ => 48
  | .missedMessageRequestMessage _ => 77
  | .missedMessageRequestAckMessage _ => 78
  | .missedMessageReportMessage _ => 80
  | .rejectMessage _ => 51
  | .systemStatusMessage _ => 110
  | .executionReportMessage _ => 56
  | .orderCancelRejectMessage _ => 57
  | .orderMassCancelReportMessage _ => 114
  | .businessRejectMessage _ => 106

def encode : Payload → List UInt8
  | .logonMessage message => LogonMessage.encode message
  | .logonReplyMessage message => LogonReplyMessage.encode message
  | .logoutMessage message => LogoutMessage.encode message
  | .heartbeatMessage message => HeartbeatMessage.encode message
  | .missedMessageRequestMessage message => MissedMessageRequestMessage.encode message
  | .missedMessageRequestAckMessage message => MissedMessageRequestAckMessage.encode message
  | .missedMessageReportMessage message => MissedMessageReportMessage.encode message
  | .rejectMessage message => RejectMessage.encode message
  | .systemStatusMessage message => SystemStatusMessage.encode message
  | .executionReportMessage message => ExecutionReportMessage.encode message
  | .orderCancelRejectMessage message => OrderCancelRejectMessage.encode message
  | .orderMassCancelReportMessage message => OrderMassCancelReportMessage.encode message
  | .businessRejectMessage message => BusinessRejectMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 179 := by
  cases message with
  | logonMessage inner =>
    simp only [encode, LogonMessage.encode_length]
    omega
  | logonReplyMessage inner =>
    simp only [encode, LogonReplyMessage.encode_length]
    omega
  | logoutMessage inner =>
    simp only [encode, LogoutMessage.encode_length]
    omega
  | heartbeatMessage inner =>
    simp only [encode, HeartbeatMessage.encode_length]
    omega
  | missedMessageRequestMessage inner =>
    simp only [encode, MissedMessageRequestMessage.encode_length]
    omega
  | missedMessageRequestAckMessage inner =>
    simp only [encode, MissedMessageRequestAckMessage.encode_length]
    omega
  | missedMessageReportMessage inner =>
    simp only [encode, MissedMessageReportMessage.encode_length]
    omega
  | rejectMessage inner =>
    simp only [encode, RejectMessage.encode_length]
    omega
  | systemStatusMessage inner =>
    simp only [encode, SystemStatusMessage.encode_length]
    omega
  | executionReportMessage inner =>
    simp only [encode, ExecutionReportMessage.encode_length]
    omega
  | orderCancelRejectMessage inner =>
    simp only [encode, OrderCancelRejectMessage.encode_length]
    omega
  | orderMassCancelReportMessage inner =>
    simp only [encode, OrderMassCancelReportMessage.encode_length]
    omega
  | businessRejectMessage inner =>
    simp only [encode, BusinessRejectMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 65 then (LogonMessage.decode bytes).map fun (message, rest) => (.logonMessage message, rest)
  else if tag = 66 then (LogonReplyMessage.decode bytes).map fun (message, rest) => (.logonReplyMessage message, rest)
  else if tag = 53 then (LogoutMessage.decode bytes).map fun (message, rest) => (.logoutMessage message, rest)
  else if tag = 48 then (HeartbeatMessage.decode bytes).map fun (message, rest) => (.heartbeatMessage message, rest)
  else if tag = 77 then (MissedMessageRequestMessage.decode bytes).map fun (message, rest) => (.missedMessageRequestMessage message, rest)
  else if tag = 78 then (MissedMessageRequestAckMessage.decode bytes).map fun (message, rest) => (.missedMessageRequestAckMessage message, rest)
  else if tag = 80 then (MissedMessageReportMessage.decode bytes).map fun (message, rest) => (.missedMessageReportMessage message, rest)
  else if tag = 51 then (RejectMessage.decode bytes).map fun (message, rest) => (.rejectMessage message, rest)
  else if tag = 110 then (SystemStatusMessage.decode bytes).map fun (message, rest) => (.systemStatusMessage message, rest)
  else if tag = 56 then (ExecutionReportMessage.decode bytes).map fun (message, rest) => (.executionReportMessage message, rest)
  else if tag = 57 then (OrderCancelRejectMessage.decode bytes).map fun (message, rest) => (.orderCancelRejectMessage message, rest)
  else if tag = 114 then (OrderMassCancelReportMessage.decode bytes).map fun (message, rest) => (.orderMassCancelReportMessage message, rest)
  else if tag = 106 then (BusinessRejectMessage.decode bytes).map fun (message, rest) => (.businessRejectMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message -/
structure Message where
  startOfMessage : BitVec 8
  payload : Payload
  deriving DecidableEq, Repr

namespace Message

def encodeBody (message : Message) : List UInt8 :=
  encodeUInt 1 (Payload.tag message.payload)
    ++ (Payload.encode message.payload)

def decodeBody (startOfMessage : BitVec 8) (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (payload, bytes) ← Payload.decode messageType bytes
  pure ({ startOfMessage, payload }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody message.startOfMessage (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 0 < 256 ^ 2 := by
  unfold encodeBody
  cases message.payload with
  | logonMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, LogonMessage.encode_length]
    omega
  | logonReplyMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, LogonReplyMessage.encode_length]
    omega
  | logoutMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, LogoutMessage.encode_length]
    omega
  | heartbeatMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, HeartbeatMessage.encode_length]
    omega
  | missedMessageRequestMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MissedMessageRequestMessage.encode_length]
    omega
  | missedMessageRequestAckMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MissedMessageRequestAckMessage.encode_length]
    omega
  | missedMessageReportMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MissedMessageReportMessage.encode_length]
    omega
  | rejectMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, RejectMessage.encode_length]
    omega
  | systemStatusMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SystemStatusMessage.encode_length]
    omega
  | executionReportMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ExecutionReportMessage.encode_length]
    omega
  | orderCancelRejectMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderCancelRejectMessage.encode_length]
    omega
  | orderMassCancelReportMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderMassCancelReportMessage.encode_length]
    omega
  | businessRejectMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, BusinessRejectMessage.encode_length]
    omega

/-- Size rule: Message Length counts the bytes after it, so it is written from the body and checked on decode; Start Of Message is read ahead of it -/
def encode (message : Message) : List UInt8 :=
  encodeUInt 1 message.startOfMessage
    ++ (encodeFramedLE 2 0 encodeBody message)

def decode (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (startOfMessage, bytes) ← decodeUInt 1 bytes
  decodeFramedLE 2 0 (decodeBody startOfMessage) bytes

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  exact decodeFramedLE_encodeFramedLE 2 0 encodeBody (decodeBody message.startOfMessage) message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, encodeFramedLE_length]
  omega

end Message

/-- Packet -/
structure Packet where
  message : List Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeMany Message.encode message.message

def decode (bytes : List UInt8) : Option Packet := do
  let message ← decodeAll Message.decode bytes.length bytes
  pure { message }

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany Message.encode Message.decode Message.decode_encode Message.encode_length_pos message.message _ (encodeMany_length_ge Message.encode Message.encode_length_pos message.message), some_bind]
  rfl

end Packet

end Omi.LsegTurquoiseNativetradinggatewayrecoveryNtgiV612
