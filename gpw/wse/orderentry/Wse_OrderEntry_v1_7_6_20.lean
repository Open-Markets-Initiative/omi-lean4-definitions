import Wire

/-!
# Giełda Papierów Wartościowych w Warszawie Warsaw Stock Exchange Native Order Gateway v1.7.6

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.GpwWseOrderentryWatsV17620

/-- Login: 20 bytes -/
structure Login where
  version : BitVec 16
  token : Alpha 8
  connectionId : BitVec 16
  nextExpectedSeqNum : BitVec 32
  lastSentSeqNum : BitVec 32
  deriving DecidableEq, Repr

namespace Login

def encode (message : Login) : List UInt8 :=
  encodeUIntLE 2 message.version
    ++ (Alpha.encode message.token
    ++ (encodeUIntLE 2 message.connectionId
    ++ (encodeUIntLE 4 message.nextExpectedSeqNum
    ++ (encodeUIntLE 4 message.lastSentSeqNum))))

def decode (bytes : List UInt8) : Option (Login × List UInt8) := do
  let (version, bytes) ← decodeUIntLE 2 bytes
  let (token, bytes) ← Alpha.decode 8 bytes
  let (connectionId, bytes) ← decodeUIntLE 2 bytes
  let (nextExpectedSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (lastSentSeqNum, bytes) ← decodeUIntLE 4 bytes
  pure ({ version, token, connectionId, nextExpectedSeqNum, lastSentSeqNum }, bytes)

@[simp] theorem encode_length (message : Login) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : Login) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Login) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end Login

/-- Login Response: 11 bytes -/
structure LoginResponse where
  resultLoginResult : BitVec 8
  nextExpectedSeqNum : BitVec 32
  lastReplaySeqNum : BitVec 32
  sessionId : BitVec 16
  deriving DecidableEq, Repr

namespace LoginResponse

def encode (message : LoginResponse) : List UInt8 :=
  encodeUIntLE 1 message.resultLoginResult
    ++ (encodeUIntLE 4 message.nextExpectedSeqNum
    ++ (encodeUIntLE 4 message.lastReplaySeqNum
    ++ (encodeUIntLE 2 message.sessionId)))

def decode (bytes : List UInt8) : Option (LoginResponse × List UInt8) := do
  let (resultLoginResult, bytes) ← decodeUIntLE 1 bytes
  let (nextExpectedSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (lastReplaySeqNum, bytes) ← decodeUIntLE 4 bytes
  let (sessionId, bytes) ← decodeUIntLE 2 bytes
  pure ({ resultLoginResult, nextExpectedSeqNum, lastReplaySeqNum, sessionId }, bytes)

@[simp] theorem encode_length (message : LoginResponse) : (encode message).length = 11 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : LoginResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginResponse) (rest : List UInt8) :
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

end LoginResponse

/-- Connection Close: 1 bytes -/
structure ConnectionClose where
  reasonConnectionCloseReason : BitVec 8
  deriving DecidableEq, Repr

namespace ConnectionClose

def encode (message : ConnectionClose) : List UInt8 :=
  encodeUIntLE 1 message.reasonConnectionCloseReason

def decode (bytes : List UInt8) : Option (ConnectionClose × List UInt8) := do
  let (reasonConnectionCloseReason, bytes) ← decodeUIntLE 1 bytes
  pure ({ reasonConnectionCloseReason }, bytes)

@[simp] theorem encode_length (message : ConnectionClose) : (encode message).length = 1 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : ConnectionClose) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ConnectionClose) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ConnectionClose

/-- Reject: 5 bytes -/
structure Reject where
  refSeqNum : BitVec 32
  rejectReason : BitVec 8
  deriving DecidableEq, Repr

namespace Reject

def encode (message : Reject) : List UInt8 :=
  encodeUIntLE 4 message.refSeqNum
    ++ (encodeUIntLE 1 message.rejectReason)

def decode (bytes : List UInt8) : Option (Reject × List UInt8) := do
  let (refSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (rejectReason, bytes) ← decodeUIntLE 1 bytes
  pure ({ refSeqNum, rejectReason }, bytes)

@[simp] theorem encode_length (message : Reject) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : Reject) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Reject) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end Reject

/-- Test: 8 bytes -/
structure Test where
  targetTimestamp : BitVec 64
  deriving DecidableEq, Repr

namespace Test

def encode (message : Test) : List UInt8 :=
  encodeUIntLE 8 message.targetTimestamp

def decode (bytes : List UInt8) : Option (Test × List UInt8) := do
  let (targetTimestamp, bytes) ← decodeUIntLE 8 bytes
  pure ({ targetTimestamp }, bytes)

@[simp] theorem encode_length (message : Test) : (encode message).length = 8 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : Test) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Test) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end Test

/-- Test Event: 201 bytes -/
structure TestEvent where
  scenarioName : Alpha 200
  eventType : BitVec 8
  deriving DecidableEq, Repr

namespace TestEvent

def encode (message : TestEvent) : List UInt8 :=
  Alpha.encode message.scenarioName
    ++ (encodeUIntLE 1 message.eventType)

def decode (bytes : List UInt8) : Option (TestEvent × List UInt8) := do
  let (scenarioName, bytes) ← Alpha.decode 200 bytes
  let (eventType, bytes) ← decodeUIntLE 1 bytes
  pure ({ scenarioName, eventType }, bytes)

@[simp] theorem encode_length (message : TestEvent) : (encode message).length = 201 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : TestEvent) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TestEvent) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TestEvent

/-- Trading Session Status: 9 bytes -/
structure TradingSessionStatus where
  marketId : Alpha 4
  date : BitVec 32
  tradingSessionEvent : BitVec 8
  deriving DecidableEq, Repr

namespace TradingSessionStatus

def encode (message : TradingSessionStatus) : List UInt8 :=
  Alpha.encode message.marketId
    ++ (encodeUIntLE 4 message.date
    ++ (encodeUIntLE 1 message.tradingSessionEvent))

def decode (bytes : List UInt8) : Option (TradingSessionStatus × List UInt8) := do
  let (marketId, bytes) ← Alpha.decode 4 bytes
  let (date, bytes) ← decodeUIntLE 4 bytes
  let (tradingSessionEvent, bytes) ← decodeUIntLE 1 bytes
  pure ({ marketId, date, tradingSessionEvent }, bytes)

@[simp] theorem encode_length (message : TradingSessionStatus) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : TradingSessionStatus) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradingSessionStatus) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradingSessionStatus

/-- Client: 5 bytes -/
structure Client where
  shortCode : BitVec 32
  qualifier : BitVec 8
  deriving DecidableEq, Repr

namespace Client

def encode (message : Client) : List UInt8 :=
  encodeUIntLE 4 message.shortCode
    ++ (encodeUIntLE 1 message.qualifier)

def decode (bytes : List UInt8) : Option (Client × List UInt8) := do
  let (shortCode, bytes) ← decodeUIntLE 4 bytes
  let (qualifier, bytes) ← decodeUIntLE 1 bytes
  pure ({ shortCode, qualifier }, bytes)

@[simp] theorem encode_length (message : Client) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : Client) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Client) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end Client

/-- Executing Trader: 5 bytes -/
structure ExecutingTrader where
  shortCode : BitVec 32
  qualifier : BitVec 8
  deriving DecidableEq, Repr

namespace ExecutingTrader

def encode (message : ExecutingTrader) : List UInt8 :=
  encodeUIntLE 4 message.shortCode
    ++ (encodeUIntLE 1 message.qualifier)

def decode (bytes : List UInt8) : Option (ExecutingTrader × List UInt8) := do
  let (shortCode, bytes) ← decodeUIntLE 4 bytes
  let (qualifier, bytes) ← decodeUIntLE 1 bytes
  pure ({ shortCode, qualifier }, bytes)

@[simp] theorem encode_length (message : ExecutingTrader) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : ExecutingTrader) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExecutingTrader) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ExecutingTrader

/-- Investment Decision Maker: 5 bytes -/
structure InvestmentDecisionMaker where
  shortCode : BitVec 32
  qualifier : BitVec 8
  deriving DecidableEq, Repr

namespace InvestmentDecisionMaker

def encode (message : InvestmentDecisionMaker) : List UInt8 :=
  encodeUIntLE 4 message.shortCode
    ++ (encodeUIntLE 1 message.qualifier)

def decode (bytes : List UInt8) : Option (InvestmentDecisionMaker × List UInt8) := do
  let (shortCode, bytes) ← decodeUIntLE 4 bytes
  let (qualifier, bytes) ← decodeUIntLE 1 bytes
  pure ({ shortCode, qualifier }, bytes)

@[simp] theorem encode_length (message : InvestmentDecisionMaker) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : InvestmentDecisionMaker) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InvestmentDecisionMaker) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end InvestmentDecisionMaker

/-- Mifid Fields: 15 bytes -/
structure MifidFields where
  client : Client
  executingTrader : ExecutingTrader
  investmentDecisionMaker : InvestmentDecisionMaker
  deriving DecidableEq, Repr

namespace MifidFields

def encode (message : MifidFields) : List UInt8 :=
  Client.encode message.client
    ++ (ExecutingTrader.encode message.executingTrader
    ++ (InvestmentDecisionMaker.encode message.investmentDecisionMaker))

def decode (bytes : List UInt8) : Option (MifidFields × List UInt8) := do
  let (client, bytes) ← Client.decode bytes
  let (executingTrader, bytes) ← ExecutingTrader.decode bytes
  let (investmentDecisionMaker, bytes) ← InvestmentDecisionMaker.decode bytes
  pure ({ client, executingTrader, investmentDecisionMaker }, bytes)

@[simp] theorem encode_length (message : MifidFields) : (encode message).length = 15 := by
  unfold encode
  simp only [List.length_append, Client.encode_length, ExecutingTrader.encode_length, InvestmentDecisionMaker.encode_length]

theorem encode_length_pos (message : MifidFields) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MifidFields) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Client.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExecutingTrader.decode_encode, some_bind]
  dsimp only
  rw [InvestmentDecisionMaker.decode_encode, some_bind]
  rfl

end MifidFields

/-- Order Add: 151 bytes -/
structure OrderAdd where
  stpId : BitVec 8
  instrumentId : BitVec 32
  orderType : BitVec 8
  timeInForce : BitVec 8
  side : BitVec 8
  price : BitVec 64
  triggerPrice : BitVec 64
  quantity : BitVec 64
  displayQty : BitVec 64
  capacity : BitVec 8
  account : Alpha 16
  accountType : BitVec 8
  flags : BitVec 8
  mifidFields : MifidFields
  expire : BitVec 64
  memo : Alpha 18
  clientOrderId : Alpha 20
  clearingMemberCode : Alpha 20
  clearingMemberClearingIdentifier : BitVec 8
  execInst : BitVec 8
  feeStructureId : BitVec 8
  interestedParty : Alpha 8
  deriving DecidableEq, Repr

namespace OrderAdd

def encode (message : OrderAdd) : List UInt8 :=
  encodeUIntLE 1 message.stpId
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 1 message.orderType
    ++ (encodeUIntLE 1 message.timeInForce
    ++ (encodeUIntLE 1 message.side
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.triggerPrice
    ++ (encodeUIntLE 8 message.quantity
    ++ (encodeUIntLE 8 message.displayQty
    ++ (encodeUIntLE 1 message.capacity
    ++ (Alpha.encode message.account
    ++ (encodeUIntLE 1 message.accountType
    ++ (encodeUIntLE 1 message.flags
    ++ (MifidFields.encode message.mifidFields
    ++ (encodeUIntLE 8 message.expire
    ++ (Alpha.encode message.memo
    ++ (Alpha.encode message.clientOrderId
    ++ (Alpha.encode message.clearingMemberCode
    ++ (encodeUIntLE 1 message.clearingMemberClearingIdentifier
    ++ (encodeUIntLE 1 message.execInst
    ++ (encodeUIntLE 1 message.feeStructureId
    ++ (Alpha.encode message.interestedParty)))))))))))))))))))))

def decode (bytes : List UInt8) : Option (OrderAdd × List UInt8) := do
  let (stpId, bytes) ← decodeUIntLE 1 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (orderType, bytes) ← decodeUIntLE 1 bytes
  let (timeInForce, bytes) ← decodeUIntLE 1 bytes
  let (side, bytes) ← decodeUIntLE 1 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (triggerPrice, bytes) ← decodeUIntLE 8 bytes
  let (quantity, bytes) ← decodeUIntLE 8 bytes
  let (displayQty, bytes) ← decodeUIntLE 8 bytes
  let (capacity, bytes) ← decodeUIntLE 1 bytes
  let (account, bytes) ← Alpha.decode 16 bytes
  let (accountType, bytes) ← decodeUIntLE 1 bytes
  let (flags, bytes) ← decodeUIntLE 1 bytes
  let (mifidFields, bytes) ← MifidFields.decode bytes
  let (expire, bytes) ← decodeUIntLE 8 bytes
  let (memo, bytes) ← Alpha.decode 18 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (clearingMemberCode, bytes) ← Alpha.decode 20 bytes
  let (clearingMemberClearingIdentifier, bytes) ← decodeUIntLE 1 bytes
  let (execInst, bytes) ← decodeUIntLE 1 bytes
  let (feeStructureId, bytes) ← decodeUIntLE 1 bytes
  let (interestedParty, bytes) ← Alpha.decode 8 bytes
  pure ({ stpId, instrumentId, orderType, timeInForce, side, price, triggerPrice, quantity, displayQty, capacity, account, accountType, flags, mifidFields, expire, memo, clientOrderId, clearingMemberCode, clearingMemberClearingIdentifier, execInst, feeStructureId, interestedParty }, bytes)

@[simp] theorem encode_length (message : OrderAdd) : (encode message).length = 151 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, MifidFields.encode_length]

theorem encode_length_pos (message : OrderAdd) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderAdd) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, MifidFields.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderAdd

/-- Order Add Response: 56 bytes -/
structure OrderAddResponse where
  orderId : BitVec 64
  publicOrderId : BitVec 64
  displayQty : BitVec 64
  filled : BitVec 64
  statusOrderStatus : BitVec 8
  reasonOrderRejectionReason : BitVec 16
  execTypeReason : BitVec 8
  clientOrderId : Alpha 20
  deriving DecidableEq, Repr

namespace OrderAddResponse

def encode (message : OrderAddResponse) : List UInt8 :=
  encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.publicOrderId
    ++ (encodeUIntLE 8 message.displayQty
    ++ (encodeUIntLE 8 message.filled
    ++ (encodeUIntLE 1 message.statusOrderStatus
    ++ (encodeUIntLE 2 message.reasonOrderRejectionReason
    ++ (encodeUIntLE 1 message.execTypeReason
    ++ (Alpha.encode message.clientOrderId)))))))

def decode (bytes : List UInt8) : Option (OrderAddResponse × List UInt8) := do
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (publicOrderId, bytes) ← decodeUIntLE 8 bytes
  let (displayQty, bytes) ← decodeUIntLE 8 bytes
  let (filled, bytes) ← decodeUIntLE 8 bytes
  let (statusOrderStatus, bytes) ← decodeUIntLE 1 bytes
  let (reasonOrderRejectionReason, bytes) ← decodeUIntLE 2 bytes
  let (execTypeReason, bytes) ← decodeUIntLE 1 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  pure ({ orderId, publicOrderId, displayQty, filled, statusOrderStatus, reasonOrderRejectionReason, execTypeReason, clientOrderId }, bytes)

@[simp] theorem encode_length (message : OrderAddResponse) : (encode message).length = 56 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderAddResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderAddResponse) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderAddResponse

/-- Order Cancel: 43 bytes -/
structure OrderCancel where
  orderId : BitVec 64
  mifidFields : MifidFields
  clientOrderId : Alpha 20
  deriving DecidableEq, Repr

namespace OrderCancel

def encode (message : OrderCancel) : List UInt8 :=
  encodeUIntLE 8 message.orderId
    ++ (MifidFields.encode message.mifidFields
    ++ (Alpha.encode message.clientOrderId))

def decode (bytes : List UInt8) : Option (OrderCancel × List UInt8) := do
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (mifidFields, bytes) ← MifidFields.decode bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  pure ({ orderId, mifidFields, clientOrderId }, bytes)

@[simp] theorem encode_length (message : OrderCancel) : (encode message).length = 43 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, MifidFields.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderCancel) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancel) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, MifidFields.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderCancel

/-- Order Cancel Response: 32 bytes -/
structure OrderCancelResponse where
  orderId : BitVec 64
  statusOrderStatus : BitVec 8
  reasonOrderRejectionReason : BitVec 16
  execTypeReason : BitVec 8
  clientOrderId : Alpha 20
  deriving DecidableEq, Repr

namespace OrderCancelResponse

def encode (message : OrderCancelResponse) : List UInt8 :=
  encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 1 message.statusOrderStatus
    ++ (encodeUIntLE 2 message.reasonOrderRejectionReason
    ++ (encodeUIntLE 1 message.execTypeReason
    ++ (Alpha.encode message.clientOrderId))))

def decode (bytes : List UInt8) : Option (OrderCancelResponse × List UInt8) := do
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (statusOrderStatus, bytes) ← decodeUIntLE 1 bytes
  let (reasonOrderRejectionReason, bytes) ← decodeUIntLE 2 bytes
  let (execTypeReason, bytes) ← decodeUIntLE 1 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  pure ({ orderId, statusOrderStatus, reasonOrderRejectionReason, execTypeReason, clientOrderId }, bytes)

@[simp] theorem encode_length (message : OrderCancelResponse) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderCancelResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancelResponse) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderCancelResponse

/-- Order Modify: 83 bytes -/
structure OrderModify where
  orderId : BitVec 64
  price : BitVec 64
  triggerPrice : BitVec 64
  quantity : BitVec 64
  displayQty : BitVec 64
  expire : BitVec 64
  mifidFields : MifidFields
  clientOrderId : Alpha 20
  deriving DecidableEq, Repr

namespace OrderModify

def encode (message : OrderModify) : List UInt8 :=
  encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.triggerPrice
    ++ (encodeUIntLE 8 message.quantity
    ++ (encodeUIntLE 8 message.displayQty
    ++ (encodeUIntLE 8 message.expire
    ++ (MifidFields.encode message.mifidFields
    ++ (Alpha.encode message.clientOrderId)))))))

def decode (bytes : List UInt8) : Option (OrderModify × List UInt8) := do
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (triggerPrice, bytes) ← decodeUIntLE 8 bytes
  let (quantity, bytes) ← decodeUIntLE 8 bytes
  let (displayQty, bytes) ← decodeUIntLE 8 bytes
  let (expire, bytes) ← decodeUIntLE 8 bytes
  let (mifidFields, bytes) ← MifidFields.decode bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  pure ({ orderId, price, triggerPrice, quantity, displayQty, expire, mifidFields, clientOrderId }, bytes)

@[simp] theorem encode_length (message : OrderModify) : (encode message).length = 83 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, MifidFields.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderModify) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderModify) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, MifidFields.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderModify

/-- Order Modify Response: 40 bytes -/
structure OrderModifyResponse where
  orderId : BitVec 64
  filled : BitVec 64
  statusOrderStatus : BitVec 8
  priorityFlag : BitVec 8
  reasonOrderRejectionReason : BitVec 16
  clientOrderId : Alpha 20
  deriving DecidableEq, Repr

namespace OrderModifyResponse

def encode (message : OrderModifyResponse) : List UInt8 :=
  encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.filled
    ++ (encodeUIntLE 1 message.statusOrderStatus
    ++ (encodeUIntLE 1 message.priorityFlag
    ++ (encodeUIntLE 2 message.reasonOrderRejectionReason
    ++ (Alpha.encode message.clientOrderId)))))

def decode (bytes : List UInt8) : Option (OrderModifyResponse × List UInt8) := do
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (filled, bytes) ← decodeUIntLE 8 bytes
  let (statusOrderStatus, bytes) ← decodeUIntLE 1 bytes
  let (priorityFlag, bytes) ← decodeUIntLE 1 bytes
  let (reasonOrderRejectionReason, bytes) ← decodeUIntLE 2 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  pure ({ orderId, filled, statusOrderStatus, priorityFlag, reasonOrderRejectionReason, clientOrderId }, bytes)

@[simp] theorem encode_length (message : OrderModifyResponse) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderModifyResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderModifyResponse) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderModifyResponse

/-- Order Mass Cancel: 39 bytes -/
structure OrderMassCancel where
  massCancelRequestType : BitVec 8
  targetPartyRole : BitVec 8
  targetPartyId : BitVec 32
  marketSegmentId : BitVec 32
  instrumentId : BitVec 32
  executingTrader : ExecutingTrader
  clientOrderId : Alpha 20
  deriving DecidableEq, Repr

namespace OrderMassCancel

def encode (message : OrderMassCancel) : List UInt8 :=
  encodeUIntLE 1 message.massCancelRequestType
    ++ (encodeUIntLE 1 message.targetPartyRole
    ++ (encodeUIntLE 4 message.targetPartyId
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (ExecutingTrader.encode message.executingTrader
    ++ (Alpha.encode message.clientOrderId))))))

def decode (bytes : List UInt8) : Option (OrderMassCancel × List UInt8) := do
  let (massCancelRequestType, bytes) ← decodeUIntLE 1 bytes
  let (targetPartyRole, bytes) ← decodeUIntLE 1 bytes
  let (targetPartyId, bytes) ← decodeUIntLE 4 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (executingTrader, bytes) ← ExecutingTrader.decode bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  pure ({ massCancelRequestType, targetPartyRole, targetPartyId, marketSegmentId, instrumentId, executingTrader, clientOrderId }, bytes)

@[simp] theorem encode_length (message : OrderMassCancel) : (encode message).length = 39 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, ExecutingTrader.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderMassCancel) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderMassCancel) (rest : List UInt8) :
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
  rw [List.append_assoc, ExecutingTrader.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderMassCancel

/-- Order Mass Cancel Response: 48 bytes -/
structure OrderMassCancelResponse where
  totalAffectedOrders : BitVec 64
  massCancelRequestType : BitVec 8
  massCancelId : BitVec 64
  targetPartyRole : BitVec 8
  targetPartyId : BitVec 32
  marketSegmentId : BitVec 32
  reasonMassCancelRejectionReason : BitVec 16
  clientOrderId : Alpha 20
  deriving DecidableEq, Repr

namespace OrderMassCancelResponse

def encode (message : OrderMassCancelResponse) : List UInt8 :=
  encodeUIntLE 8 message.totalAffectedOrders
    ++ (encodeUIntLE 1 message.massCancelRequestType
    ++ (encodeUIntLE 8 message.massCancelId
    ++ (encodeUIntLE 1 message.targetPartyRole
    ++ (encodeUIntLE 4 message.targetPartyId
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 2 message.reasonMassCancelRejectionReason
    ++ (Alpha.encode message.clientOrderId)))))))

def decode (bytes : List UInt8) : Option (OrderMassCancelResponse × List UInt8) := do
  let (totalAffectedOrders, bytes) ← decodeUIntLE 8 bytes
  let (massCancelRequestType, bytes) ← decodeUIntLE 1 bytes
  let (massCancelId, bytes) ← decodeUIntLE 8 bytes
  let (targetPartyRole, bytes) ← decodeUIntLE 1 bytes
  let (targetPartyId, bytes) ← decodeUIntLE 4 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (reasonMassCancelRejectionReason, bytes) ← decodeUIntLE 2 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  pure ({ totalAffectedOrders, massCancelRequestType, massCancelId, targetPartyRole, targetPartyId, marketSegmentId, reasonMassCancelRejectionReason, clientOrderId }, bytes)

@[simp] theorem encode_length (message : OrderMassCancelResponse) : (encode message).length = 48 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderMassCancelResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderMassCancelResponse) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderMassCancelResponse

/-- Order Execute: 64 bytes -/
structure OrderExecute where
  instrumentId : BitVec 32
  orderId : BitVec 64
  tradeId : BitVec 32
  price : BitVec 64
  quantity : BitVec 64
  leavesQty : BitVec 64
  liquidityIndicator : BitVec 8
  currency : BitVec 16
  side : BitVec 8
  clientOrderId : Alpha 20
  deriving DecidableEq, Repr

namespace OrderExecute

def encode (message : OrderExecute) : List UInt8 :=
  encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 4 message.tradeId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.quantity
    ++ (encodeUIntLE 8 message.leavesQty
    ++ (encodeUIntLE 1 message.liquidityIndicator
    ++ (encodeUIntLE 2 message.currency
    ++ (encodeUIntLE 1 message.side
    ++ (Alpha.encode message.clientOrderId)))))))))

def decode (bytes : List UInt8) : Option (OrderExecute × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (quantity, bytes) ← decodeUIntLE 8 bytes
  let (leavesQty, bytes) ← decodeUIntLE 8 bytes
  let (liquidityIndicator, bytes) ← decodeUIntLE 1 bytes
  let (currency, bytes) ← decodeUIntLE 2 bytes
  let (side, bytes) ← decodeUIntLE 1 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  pure ({ instrumentId, orderId, tradeId, price, quantity, leavesQty, liquidityIndicator, currency, side, clientOrderId }, bytes)

@[simp] theorem encode_length (message : OrderExecute) : (encode message).length = 64 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderExecute) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderExecute) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderExecute

/-- Bid: 16 bytes -/
structure Bid where
  price : BitVec 64
  quantity : BitVec 64
  deriving DecidableEq, Repr

namespace Bid

def encode (message : Bid) : List UInt8 :=
  encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.quantity)

def decode (bytes : List UInt8) : Option (Bid × List UInt8) := do
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (quantity, bytes) ← decodeUIntLE 8 bytes
  pure ({ price, quantity }, bytes)

@[simp] theorem encode_length (message : Bid) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : Bid) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Bid) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end Bid

/-- Ask: 16 bytes -/
structure Ask where
  price : BitVec 64
  quantity : BitVec 64
  deriving DecidableEq, Repr

namespace Ask

def encode (message : Ask) : List UInt8 :=
  encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.quantity)

def decode (bytes : List UInt8) : Option (Ask × List UInt8) := do
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (quantity, bytes) ← decodeUIntLE 8 bytes
  pure ({ price, quantity }, bytes)

@[simp] theorem encode_length (message : Ask) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : Ask) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Ask) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end Ask

/-- Quote: 36 bytes -/
structure Quote where
  instrumentId : BitVec 32
  bid : Bid
  ask : Ask
  deriving DecidableEq, Repr

namespace Quote

def encode (message : Quote) : List UInt8 :=
  encodeUIntLE 4 message.instrumentId
    ++ (Bid.encode message.bid
    ++ (Ask.encode message.ask))

def decode (bytes : List UInt8) : Option (Quote × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (bid, bytes) ← Bid.decode bytes
  let (ask, bytes) ← Ask.decode bytes
  pure ({ instrumentId, bid, ask }, bytes)

@[simp] theorem encode_length (message : Quote) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Bid.encode_length, Ask.encode_length]

theorem encode_length_pos (message : Quote) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Quote) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Bid.decode_encode, some_bind]
  dsimp only
  rw [Ask.decode_encode, some_bind]
  rfl

end Quote

/-- Items Quotes Array: 36 bytes -/
structure ItemsQuotesArray where
  quote : Quote
  deriving DecidableEq, Repr

namespace ItemsQuotesArray

def encode (message : ItemsQuotesArray) : List UInt8 :=
  Quote.encode message.quote

def decode (bytes : List UInt8) : Option (ItemsQuotesArray × List UInt8) := do
  let (quote, bytes) ← Quote.decode bytes
  pure ({ quote }, bytes)

@[simp] theorem encode_length (message : ItemsQuotesArray) : (encode message).length = 36 := by
  unfold encode
  simp only [Quote.encode_length]

theorem encode_length_pos (message : ItemsQuotesArray) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ItemsQuotesArray) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Quote.decode_encode, some_bind]
  rfl

end ItemsQuotesArray

/-- Quotes: 1081 bytes -/
structure Quotes where
  count : BitVec 8
  itemsQuotesArray : Exact 30 ItemsQuotesArray
  deriving DecidableEq, Repr

namespace Quotes

def encode (message : Quotes) : List UInt8 :=
  encodeUIntLE 1 message.count
    ++ (encodeMany ItemsQuotesArray.encode message.itemsQuotesArray.val)

def decode (bytes : List UInt8) : Option (Quotes × List UInt8) := do
  let (count, bytes) ← decodeUIntLE 1 bytes
  let (itemsQuotesArray_, bytes) ← decodeMany ItemsQuotesArray.decode 30 bytes
  if fits_itemsQuotesArray : itemsQuotesArray_.length = 30 then
    pure ({ count, itemsQuotesArray := ⟨itemsQuotesArray_, fits_itemsQuotesArray⟩ }, bytes)
  else none

@[simp] theorem encode_length (message : Quotes) : (encode message).length = 1081 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeMany_length_const ItemsQuotesArray.encode 36 ItemsQuotesArray.encode_length, message.itemsQuotesArray.length_eq]

theorem encode_length_pos (message : Quotes) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Quotes) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_exact 30 ItemsQuotesArray.encode ItemsQuotesArray.decode ItemsQuotesArray.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.itemsQuotesArray.length_eq]
  rfl

end Quotes

/-- Mass Quote: 1184 bytes -/
structure MassQuote where
  stpId : BitVec 8
  capacity : BitVec 8
  account : Alpha 16
  accountType : BitVec 8
  flags : BitVec 8
  mifidFields : MifidFields
  memo : Alpha 18
  clearingMemberCode : Alpha 20
  clearingMemberClearingIdentifier : BitVec 8
  quotes : Quotes
  feeStructureId : BitVec 8
  interestedParty : Alpha 8
  quoteId : Alpha 20
  deriving DecidableEq, Repr

namespace MassQuote

def encode (message : MassQuote) : List UInt8 :=
  encodeUIntLE 1 message.stpId
    ++ (encodeUIntLE 1 message.capacity
    ++ (Alpha.encode message.account
    ++ (encodeUIntLE 1 message.accountType
    ++ (encodeUIntLE 1 message.flags
    ++ (MifidFields.encode message.mifidFields
    ++ (Alpha.encode message.memo
    ++ (Alpha.encode message.clearingMemberCode
    ++ (encodeUIntLE 1 message.clearingMemberClearingIdentifier
    ++ (Quotes.encode message.quotes
    ++ (encodeUIntLE 1 message.feeStructureId
    ++ (Alpha.encode message.interestedParty
    ++ (Alpha.encode message.quoteId))))))))))))

def decode (bytes : List UInt8) : Option (MassQuote × List UInt8) := do
  let (stpId, bytes) ← decodeUIntLE 1 bytes
  let (capacity, bytes) ← decodeUIntLE 1 bytes
  let (account, bytes) ← Alpha.decode 16 bytes
  let (accountType, bytes) ← decodeUIntLE 1 bytes
  let (flags, bytes) ← decodeUIntLE 1 bytes
  let (mifidFields, bytes) ← MifidFields.decode bytes
  let (memo, bytes) ← Alpha.decode 18 bytes
  let (clearingMemberCode, bytes) ← Alpha.decode 20 bytes
  let (clearingMemberClearingIdentifier, bytes) ← decodeUIntLE 1 bytes
  let (quotes, bytes) ← Quotes.decode bytes
  let (feeStructureId, bytes) ← decodeUIntLE 1 bytes
  let (interestedParty, bytes) ← Alpha.decode 8 bytes
  let (quoteId, bytes) ← Alpha.decode 20 bytes
  pure ({ stpId, capacity, account, accountType, flags, mifidFields, memo, clearingMemberCode, clearingMemberClearingIdentifier, quotes, feeStructureId, interestedParty, quoteId }, bytes)

@[simp] theorem encode_length (message : MassQuote) : (encode message).length = 1184 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, MifidFields.encode_length, Quotes.encode_length]

theorem encode_length_pos (message : MassQuote) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MassQuote) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, MifidFields.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Quotes.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MassQuote

/-- Quote Order Response: 23 bytes -/
structure QuoteOrderResponse where
  instrumentId : BitVec 32
  bidOrderId : BitVec 64
  askOrderId : BitVec 64
  statusOrderStatus : BitVec 8
  reasonOrderRejectionReason : BitVec 16
  deriving DecidableEq, Repr

namespace QuoteOrderResponse

def encode (message : QuoteOrderResponse) : List UInt8 :=
  encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 8 message.bidOrderId
    ++ (encodeUIntLE 8 message.askOrderId
    ++ (encodeUIntLE 1 message.statusOrderStatus
    ++ (encodeUIntLE 2 message.reasonOrderRejectionReason))))

def decode (bytes : List UInt8) : Option (QuoteOrderResponse × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (bidOrderId, bytes) ← decodeUIntLE 8 bytes
  let (askOrderId, bytes) ← decodeUIntLE 8 bytes
  let (statusOrderStatus, bytes) ← decodeUIntLE 1 bytes
  let (reasonOrderRejectionReason, bytes) ← decodeUIntLE 2 bytes
  pure ({ instrumentId, bidOrderId, askOrderId, statusOrderStatus, reasonOrderRejectionReason }, bytes)

@[simp] theorem encode_length (message : QuoteOrderResponse) : (encode message).length = 23 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : QuoteOrderResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteOrderResponse) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end QuoteOrderResponse

/-- Items Quote Order Response Array: 23 bytes -/
structure ItemsQuoteOrderResponseArray where
  quoteOrderResponse : QuoteOrderResponse
  deriving DecidableEq, Repr

namespace ItemsQuoteOrderResponseArray

def encode (message : ItemsQuoteOrderResponseArray) : List UInt8 :=
  QuoteOrderResponse.encode message.quoteOrderResponse

def decode (bytes : List UInt8) : Option (ItemsQuoteOrderResponseArray × List UInt8) := do
  let (quoteOrderResponse, bytes) ← QuoteOrderResponse.decode bytes
  pure ({ quoteOrderResponse }, bytes)

@[simp] theorem encode_length (message : ItemsQuoteOrderResponseArray) : (encode message).length = 23 := by
  unfold encode
  simp only [QuoteOrderResponse.encode_length]

theorem encode_length_pos (message : ItemsQuoteOrderResponseArray) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ItemsQuoteOrderResponseArray) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [QuoteOrderResponse.decode_encode, some_bind]
  rfl

end ItemsQuoteOrderResponseArray

/-- Responses: 691 bytes -/
structure Responses where
  count : BitVec 8
  itemsQuoteOrderResponseArray : Exact 30 ItemsQuoteOrderResponseArray
  deriving DecidableEq, Repr

namespace Responses

def encode (message : Responses) : List UInt8 :=
  encodeUIntLE 1 message.count
    ++ (encodeMany ItemsQuoteOrderResponseArray.encode message.itemsQuoteOrderResponseArray.val)

def decode (bytes : List UInt8) : Option (Responses × List UInt8) := do
  let (count, bytes) ← decodeUIntLE 1 bytes
  let (itemsQuoteOrderResponseArray_, bytes) ← decodeMany ItemsQuoteOrderResponseArray.decode 30 bytes
  if fits_itemsQuoteOrderResponseArray : itemsQuoteOrderResponseArray_.length = 30 then
    pure ({ count, itemsQuoteOrderResponseArray := ⟨itemsQuoteOrderResponseArray_, fits_itemsQuoteOrderResponseArray⟩ }, bytes)
  else none

@[simp] theorem encode_length (message : Responses) : (encode message).length = 691 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeMany_length_const ItemsQuoteOrderResponseArray.encode 23 ItemsQuoteOrderResponseArray.encode_length, message.itemsQuoteOrderResponseArray.length_eq]

theorem encode_length_pos (message : Responses) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Responses) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_exact 30 ItemsQuoteOrderResponseArray.encode ItemsQuoteOrderResponseArray.decode ItemsQuoteOrderResponseArray.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.itemsQuoteOrderResponseArray.length_eq]
  rfl

end Responses

/-- Mass Quote Response: 703 bytes -/
structure MassQuoteResponse where
  massQuoteId : BitVec 64
  responses : Responses
  statusMassQuoteStatus : BitVec 8
  reasonMassQuoteRejectionReason : BitVec 16
  feeStructureId : BitVec 8
  deriving DecidableEq, Repr

namespace MassQuoteResponse

def encode (message : MassQuoteResponse) : List UInt8 :=
  encodeUIntLE 8 message.massQuoteId
    ++ (Responses.encode message.responses
    ++ (encodeUIntLE 1 message.statusMassQuoteStatus
    ++ (encodeUIntLE 2 message.reasonMassQuoteRejectionReason
    ++ (encodeUIntLE 1 message.feeStructureId))))

def decode (bytes : List UInt8) : Option (MassQuoteResponse × List UInt8) := do
  let (massQuoteId, bytes) ← decodeUIntLE 8 bytes
  let (responses, bytes) ← Responses.decode bytes
  let (statusMassQuoteStatus, bytes) ← decodeUIntLE 1 bytes
  let (reasonMassQuoteRejectionReason, bytes) ← decodeUIntLE 2 bytes
  let (feeStructureId, bytes) ← decodeUIntLE 1 bytes
  pure ({ massQuoteId, responses, statusMassQuoteStatus, reasonMassQuoteRejectionReason, feeStructureId }, bytes)

@[simp] theorem encode_length (message : MassQuoteResponse) : (encode message).length = 703 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Responses.encode_length]

theorem encode_length_pos (message : MassQuoteResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MassQuoteResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Responses.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end MassQuoteResponse

/-- Market Maker Command: 5 bytes -/
structure MarketMakerCommand where
  instrumentId : BitVec 32
  action : BitVec 8
  deriving DecidableEq, Repr

namespace MarketMakerCommand

def encode (message : MarketMakerCommand) : List UInt8 :=
  encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 1 message.action)

def decode (bytes : List UInt8) : Option (MarketMakerCommand × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (action, bytes) ← decodeUIntLE 1 bytes
  pure ({ instrumentId, action }, bytes)

@[simp] theorem encode_length (message : MarketMakerCommand) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : MarketMakerCommand) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketMakerCommand) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end MarketMakerCommand

/-- Market Maker Command Response: 7 bytes -/
structure MarketMakerCommandResponse where
  refId : BitVec 32
  resultCommandResult : BitVec 8
  rejectionCode : BitVec 16
  deriving DecidableEq, Repr

namespace MarketMakerCommandResponse

def encode (message : MarketMakerCommandResponse) : List UInt8 :=
  encodeUIntLE 4 message.refId
    ++ (encodeUIntLE 1 message.resultCommandResult
    ++ (encodeUIntLE 2 message.rejectionCode))

def decode (bytes : List UInt8) : Option (MarketMakerCommandResponse × List UInt8) := do
  let (refId, bytes) ← decodeUIntLE 4 bytes
  let (resultCommandResult, bytes) ← decodeUIntLE 1 bytes
  let (rejectionCode, bytes) ← decodeUIntLE 2 bytes
  pure ({ refId, resultCommandResult, rejectionCode }, bytes)

@[simp] theorem encode_length (message : MarketMakerCommandResponse) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : MarketMakerCommandResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketMakerCommandResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end MarketMakerCommandResponse

/-- Request For Execution: 5 bytes -/
structure RequestForExecution where
  instrumentId : BitVec 32
  reasonRequestForExecutionReason : BitVec 8
  deriving DecidableEq, Repr

namespace RequestForExecution

def encode (message : RequestForExecution) : List UInt8 :=
  encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 1 message.reasonRequestForExecutionReason)

def decode (bytes : List UInt8) : Option (RequestForExecution × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (reasonRequestForExecutionReason, bytes) ← decodeUIntLE 1 bytes
  pure ({ instrumentId, reasonRequestForExecutionReason }, bytes)

@[simp] theorem encode_length (message : RequestForExecution) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : RequestForExecution) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RequestForExecution) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end RequestForExecution

/-- Bid Offer Update: 29 bytes -/
structure BidOfferUpdate where
  instrumentId : BitVec 32
  updateType : BitVec 8
  totalBidSize : BitVec 64
  totalOfferSize : BitVec 64
  bidOrders : BitVec 32
  offerOrders : BitVec 32
  deriving DecidableEq, Repr

namespace BidOfferUpdate

def encode (message : BidOfferUpdate) : List UInt8 :=
  encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 1 message.updateType
    ++ (encodeUIntLE 8 message.totalBidSize
    ++ (encodeUIntLE 8 message.totalOfferSize
    ++ (encodeUIntLE 4 message.bidOrders
    ++ (encodeUIntLE 4 message.offerOrders)))))

def decode (bytes : List UInt8) : Option (BidOfferUpdate × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (updateType, bytes) ← decodeUIntLE 1 bytes
  let (totalBidSize, bytes) ← decodeUIntLE 8 bytes
  let (totalOfferSize, bytes) ← decodeUIntLE 8 bytes
  let (bidOrders, bytes) ← decodeUIntLE 4 bytes
  let (offerOrders, bytes) ← decodeUIntLE 4 bytes
  pure ({ instrumentId, updateType, totalBidSize, totalOfferSize, bidOrders, offerOrders }, bytes)

@[simp] theorem encode_length (message : BidOfferUpdate) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : BidOfferUpdate) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BidOfferUpdate) (rest : List UInt8) :
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

end BidOfferUpdate

/-- Tcr Party: 82 bytes -/
structure TcrParty where
  flags : BitVec 8
  mifidFields : MifidFields
  clearingMemberCode : Alpha 20
  clearingMemberClearingIdentifier : BitVec 8
  account : Alpha 16
  accountType : BitVec 8
  orderCapacity : BitVec 8
  feeStructureId : BitVec 8
  interestedParty : Alpha 8
  memo : Alpha 18
  deriving DecidableEq, Repr

namespace TcrParty

def encode (message : TcrParty) : List UInt8 :=
  encodeUIntLE 1 message.flags
    ++ (MifidFields.encode message.mifidFields
    ++ (Alpha.encode message.clearingMemberCode
    ++ (encodeUIntLE 1 message.clearingMemberClearingIdentifier
    ++ (Alpha.encode message.account
    ++ (encodeUIntLE 1 message.accountType
    ++ (encodeUIntLE 1 message.orderCapacity
    ++ (encodeUIntLE 1 message.feeStructureId
    ++ (Alpha.encode message.interestedParty
    ++ (Alpha.encode message.memo)))))))))

def decode (bytes : List UInt8) : Option (TcrParty × List UInt8) := do
  let (flags, bytes) ← decodeUIntLE 1 bytes
  let (mifidFields, bytes) ← MifidFields.decode bytes
  let (clearingMemberCode, bytes) ← Alpha.decode 20 bytes
  let (clearingMemberClearingIdentifier, bytes) ← decodeUIntLE 1 bytes
  let (account, bytes) ← Alpha.decode 16 bytes
  let (accountType, bytes) ← decodeUIntLE 1 bytes
  let (orderCapacity, bytes) ← decodeUIntLE 1 bytes
  let (feeStructureId, bytes) ← decodeUIntLE 1 bytes
  let (interestedParty, bytes) ← Alpha.decode 8 bytes
  let (memo, bytes) ← Alpha.decode 18 bytes
  pure ({ flags, mifidFields, clearingMemberCode, clearingMemberClearingIdentifier, account, accountType, orderCapacity, feeStructureId, interestedParty, memo }, bytes)

@[simp] theorem encode_length (message : TcrParty) : (encode message).length = 82 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, MifidFields.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : TcrParty) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TcrParty) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, MifidFields.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TcrParty

/-- Trade Capture Report Single: 182 bytes -/
structure TradeCaptureReportSingle where
  instrumentId : BitVec 32
  tradeReportId : Alpha 21
  secondaryTradeReportId : BitVec 64
  tradeId : BitVec 32
  tradeReportTransType : BitVec 8
  tradeReportType : BitVec 8
  tradeType : BitVec 8
  algorithmicTradeIndicator : BitVec 8
  execType : BitVec 8
  tradeReportRefId : Alpha 21
  lastQty : BitVec 64
  lastPx : BitVec 64
  settlementDate : BitVec 32
  side : BitVec 8
  counterpartyCode : Alpha 16
  tcrParty : TcrParty
  deriving DecidableEq, Repr

namespace TradeCaptureReportSingle

def encode (message : TradeCaptureReportSingle) : List UInt8 :=
  encodeUIntLE 4 message.instrumentId
    ++ (Alpha.encode message.tradeReportId
    ++ (encodeUIntLE 8 message.secondaryTradeReportId
    ++ (encodeUIntLE 4 message.tradeId
    ++ (encodeUIntLE 1 message.tradeReportTransType
    ++ (encodeUIntLE 1 message.tradeReportType
    ++ (encodeUIntLE 1 message.tradeType
    ++ (encodeUIntLE 1 message.algorithmicTradeIndicator
    ++ (encodeUIntLE 1 message.execType
    ++ (Alpha.encode message.tradeReportRefId
    ++ (encodeUIntLE 8 message.lastQty
    ++ (encodeUIntLE 8 message.lastPx
    ++ (encodeUIntLE 4 message.settlementDate
    ++ (encodeUIntLE 1 message.side
    ++ (Alpha.encode message.counterpartyCode
    ++ (TcrParty.encode message.tcrParty)))))))))))))))

def decode (bytes : List UInt8) : Option (TradeCaptureReportSingle × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (tradeReportId, bytes) ← Alpha.decode 21 bytes
  let (secondaryTradeReportId, bytes) ← decodeUIntLE 8 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (tradeReportTransType, bytes) ← decodeUIntLE 1 bytes
  let (tradeReportType, bytes) ← decodeUIntLE 1 bytes
  let (tradeType, bytes) ← decodeUIntLE 1 bytes
  let (algorithmicTradeIndicator, bytes) ← decodeUIntLE 1 bytes
  let (execType, bytes) ← decodeUIntLE 1 bytes
  let (tradeReportRefId, bytes) ← Alpha.decode 21 bytes
  let (lastQty, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (settlementDate, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← decodeUIntLE 1 bytes
  let (counterpartyCode, bytes) ← Alpha.decode 16 bytes
  let (tcrParty, bytes) ← TcrParty.decode bytes
  pure ({ instrumentId, tradeReportId, secondaryTradeReportId, tradeId, tradeReportTransType, tradeReportType, tradeType, algorithmicTradeIndicator, execType, tradeReportRefId, lastQty, lastPx, settlementDate, side, counterpartyCode, tcrParty }, bytes)

@[simp] theorem encode_length (message : TradeCaptureReportSingle) : (encode message).length = 182 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TcrParty.encode_length]

theorem encode_length_pos (message : TradeCaptureReportSingle) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCaptureReportSingle) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [TcrParty.decode_encode, some_bind]
  rfl

end TradeCaptureReportSingle

/-- Tcr Party Buy: 82 bytes -/
structure TcrPartyBuy where
  flags : BitVec 8
  mifidFields : MifidFields
  clearingMemberCode : Alpha 20
  clearingMemberClearingIdentifier : BitVec 8
  account : Alpha 16
  accountType : BitVec 8
  orderCapacity : BitVec 8
  feeStructureId : BitVec 8
  interestedParty : Alpha 8
  memo : Alpha 18
  deriving DecidableEq, Repr

namespace TcrPartyBuy

def encode (message : TcrPartyBuy) : List UInt8 :=
  encodeUIntLE 1 message.flags
    ++ (MifidFields.encode message.mifidFields
    ++ (Alpha.encode message.clearingMemberCode
    ++ (encodeUIntLE 1 message.clearingMemberClearingIdentifier
    ++ (Alpha.encode message.account
    ++ (encodeUIntLE 1 message.accountType
    ++ (encodeUIntLE 1 message.orderCapacity
    ++ (encodeUIntLE 1 message.feeStructureId
    ++ (Alpha.encode message.interestedParty
    ++ (Alpha.encode message.memo)))))))))

def decode (bytes : List UInt8) : Option (TcrPartyBuy × List UInt8) := do
  let (flags, bytes) ← decodeUIntLE 1 bytes
  let (mifidFields, bytes) ← MifidFields.decode bytes
  let (clearingMemberCode, bytes) ← Alpha.decode 20 bytes
  let (clearingMemberClearingIdentifier, bytes) ← decodeUIntLE 1 bytes
  let (account, bytes) ← Alpha.decode 16 bytes
  let (accountType, bytes) ← decodeUIntLE 1 bytes
  let (orderCapacity, bytes) ← decodeUIntLE 1 bytes
  let (feeStructureId, bytes) ← decodeUIntLE 1 bytes
  let (interestedParty, bytes) ← Alpha.decode 8 bytes
  let (memo, bytes) ← Alpha.decode 18 bytes
  pure ({ flags, mifidFields, clearingMemberCode, clearingMemberClearingIdentifier, account, accountType, orderCapacity, feeStructureId, interestedParty, memo }, bytes)

@[simp] theorem encode_length (message : TcrPartyBuy) : (encode message).length = 82 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, MifidFields.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : TcrPartyBuy) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TcrPartyBuy) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, MifidFields.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TcrPartyBuy

/-- Tcr Party Sell: 82 bytes -/
structure TcrPartySell where
  flags : BitVec 8
  mifidFields : MifidFields
  clearingMemberCode : Alpha 20
  clearingMemberClearingIdentifier : BitVec 8
  account : Alpha 16
  accountType : BitVec 8
  orderCapacity : BitVec 8
  feeStructureId : BitVec 8
  interestedParty : Alpha 8
  memo : Alpha 18
  deriving DecidableEq, Repr

namespace TcrPartySell

def encode (message : TcrPartySell) : List UInt8 :=
  encodeUIntLE 1 message.flags
    ++ (MifidFields.encode message.mifidFields
    ++ (Alpha.encode message.clearingMemberCode
    ++ (encodeUIntLE 1 message.clearingMemberClearingIdentifier
    ++ (Alpha.encode message.account
    ++ (encodeUIntLE 1 message.accountType
    ++ (encodeUIntLE 1 message.orderCapacity
    ++ (encodeUIntLE 1 message.feeStructureId
    ++ (Alpha.encode message.interestedParty
    ++ (Alpha.encode message.memo)))))))))

def decode (bytes : List UInt8) : Option (TcrPartySell × List UInt8) := do
  let (flags, bytes) ← decodeUIntLE 1 bytes
  let (mifidFields, bytes) ← MifidFields.decode bytes
  let (clearingMemberCode, bytes) ← Alpha.decode 20 bytes
  let (clearingMemberClearingIdentifier, bytes) ← decodeUIntLE 1 bytes
  let (account, bytes) ← Alpha.decode 16 bytes
  let (accountType, bytes) ← decodeUIntLE 1 bytes
  let (orderCapacity, bytes) ← decodeUIntLE 1 bytes
  let (feeStructureId, bytes) ← decodeUIntLE 1 bytes
  let (interestedParty, bytes) ← Alpha.decode 8 bytes
  let (memo, bytes) ← Alpha.decode 18 bytes
  pure ({ flags, mifidFields, clearingMemberCode, clearingMemberClearingIdentifier, account, accountType, orderCapacity, feeStructureId, interestedParty, memo }, bytes)

@[simp] theorem encode_length (message : TcrPartySell) : (encode message).length = 82 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, MifidFields.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : TcrPartySell) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TcrPartySell) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, MifidFields.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TcrPartySell

/-- Trade Capture Report Dual: 247 bytes -/
structure TradeCaptureReportDual where
  instrumentId : BitVec 32
  tradeReportId : Alpha 21
  secondaryTradeReportId : BitVec 64
  tradeId : BitVec 32
  tradeReportTransType : BitVec 8
  tradeReportType : BitVec 8
  tradeType : BitVec 8
  algorithmicTradeIndicator : BitVec 8
  execType : BitVec 8
  tradeReportRefId : Alpha 21
  lastQty : BitVec 64
  lastPx : BitVec 64
  settlementDate : BitVec 32
  tcrPartyBuy : TcrPartyBuy
  tcrPartySell : TcrPartySell
  deriving DecidableEq, Repr

namespace TradeCaptureReportDual

def encode (message : TradeCaptureReportDual) : List UInt8 :=
  encodeUIntLE 4 message.instrumentId
    ++ (Alpha.encode message.tradeReportId
    ++ (encodeUIntLE 8 message.secondaryTradeReportId
    ++ (encodeUIntLE 4 message.tradeId
    ++ (encodeUIntLE 1 message.tradeReportTransType
    ++ (encodeUIntLE 1 message.tradeReportType
    ++ (encodeUIntLE 1 message.tradeType
    ++ (encodeUIntLE 1 message.algorithmicTradeIndicator
    ++ (encodeUIntLE 1 message.execType
    ++ (Alpha.encode message.tradeReportRefId
    ++ (encodeUIntLE 8 message.lastQty
    ++ (encodeUIntLE 8 message.lastPx
    ++ (encodeUIntLE 4 message.settlementDate
    ++ (TcrPartyBuy.encode message.tcrPartyBuy
    ++ (TcrPartySell.encode message.tcrPartySell))))))))))))))

def decode (bytes : List UInt8) : Option (TradeCaptureReportDual × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (tradeReportId, bytes) ← Alpha.decode 21 bytes
  let (secondaryTradeReportId, bytes) ← decodeUIntLE 8 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (tradeReportTransType, bytes) ← decodeUIntLE 1 bytes
  let (tradeReportType, bytes) ← decodeUIntLE 1 bytes
  let (tradeType, bytes) ← decodeUIntLE 1 bytes
  let (algorithmicTradeIndicator, bytes) ← decodeUIntLE 1 bytes
  let (execType, bytes) ← decodeUIntLE 1 bytes
  let (tradeReportRefId, bytes) ← Alpha.decode 21 bytes
  let (lastQty, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (settlementDate, bytes) ← decodeUIntLE 4 bytes
  let (tcrPartyBuy, bytes) ← TcrPartyBuy.decode bytes
  let (tcrPartySell, bytes) ← TcrPartySell.decode bytes
  pure ({ instrumentId, tradeReportId, secondaryTradeReportId, tradeId, tradeReportTransType, tradeReportType, tradeType, algorithmicTradeIndicator, execType, tradeReportRefId, lastQty, lastPx, settlementDate, tcrPartyBuy, tcrPartySell }, bytes)

@[simp] theorem encode_length (message : TradeCaptureReportDual) : (encode message).length = 247 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TcrPartyBuy.encode_length, TcrPartySell.encode_length]

theorem encode_length_pos (message : TradeCaptureReportDual) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCaptureReportDual) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TcrPartyBuy.decode_encode, some_bind]
  dsimp only
  rw [TcrPartySell.decode_encode, some_bind]
  rfl

end TradeCaptureReportDual

/-- Trade Capture Report Response: 40 bytes -/
structure TradeCaptureReportResponse where
  instrumentId : BitVec 32
  tradeId : BitVec 32
  tradeReportId : Alpha 21
  secondaryTradeReportId : BitVec 64
  statusTcrStatus : BitVec 8
  reasonTcrRejectionReason : BitVec 16
  deriving DecidableEq, Repr

namespace TradeCaptureReportResponse

def encode (message : TradeCaptureReportResponse) : List UInt8 :=
  encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 4 message.tradeId
    ++ (Alpha.encode message.tradeReportId
    ++ (encodeUIntLE 8 message.secondaryTradeReportId
    ++ (encodeUIntLE 1 message.statusTcrStatus
    ++ (encodeUIntLE 2 message.reasonTcrRejectionReason)))))

def decode (bytes : List UInt8) : Option (TradeCaptureReportResponse × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (tradeReportId, bytes) ← Alpha.decode 21 bytes
  let (secondaryTradeReportId, bytes) ← decodeUIntLE 8 bytes
  let (statusTcrStatus, bytes) ← decodeUIntLE 1 bytes
  let (reasonTcrRejectionReason, bytes) ← decodeUIntLE 2 bytes
  pure ({ instrumentId, tradeId, tradeReportId, secondaryTradeReportId, statusTcrStatus, reasonTcrRejectionReason }, bytes)

@[simp] theorem encode_length (message : TradeCaptureReportResponse) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : TradeCaptureReportResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCaptureReportResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeCaptureReportResponse

/-- Trade Bust: 4 bytes -/
structure TradeBust where
  tradeId : BitVec 32
  deriving DecidableEq, Repr

namespace TradeBust

def encode (message : TradeBust) : List UInt8 :=
  encodeUIntLE 4 message.tradeId

def decode (bytes : List UInt8) : Option (TradeBust × List UInt8) := do
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  pure ({ tradeId }, bytes)

@[simp] theorem encode_length (message : TradeBust) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : TradeBust) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeBust) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeBust

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | login (message : Login) -- 2
  | loginResponse (message : LoginResponse) -- 3
  | connectionClose (message : ConnectionClose) -- 12
  | reject (message : Reject) -- 15
  | test (message : Test) -- 1
  | testEvent (message : TestEvent) -- 255
  | tradingSessionStatus (message : TradingSessionStatus) -- 35
  | orderAdd (message : OrderAdd) -- 4
  | orderAddResponse (message : OrderAddResponse) -- 5
  | orderCancel (message : OrderCancel) -- 6
  | orderCancelResponse (message : OrderCancelResponse) -- 7
  | orderModify (message : OrderModify) -- 8
  | orderModifyResponse (message : OrderModifyResponse) -- 9
  | orderMassCancel (message : OrderMassCancel) -- 29
  | orderMassCancelResponse (message : OrderMassCancelResponse) -- 30
  | orderExecute (message : OrderExecute) -- 10
  | massQuote (message : MassQuote) -- 24
  | massQuoteResponse (message : MassQuoteResponse) -- 25
  | marketMakerCommand (message : MarketMakerCommand) -- 32
  | marketMakerCommandResponse (message : MarketMakerCommandResponse) -- 33
  | requestForExecution (message : RequestForExecution) -- 28
  | bidOfferUpdate (message : BidOfferUpdate) -- 31
  | tradeCaptureReportSingle (message : TradeCaptureReportSingle) -- 18
  | tradeCaptureReportDual (message : TradeCaptureReportDual) -- 19
  | tradeCaptureReportResponse (message : TradeCaptureReportResponse) -- 20
  | tradeBust (message : TradeBust) -- 23
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 16
  | .login _ => 2
  | .loginResponse _ => 3
  | .connectionClose _ => 12
  | .reject _ => 15
  | .test _ => 1
  | .testEvent _ => 255
  | .tradingSessionStatus _ => 35
  | .orderAdd _ => 4
  | .orderAddResponse _ => 5
  | .orderCancel _ => 6
  | .orderCancelResponse _ => 7
  | .orderModify _ => 8
  | .orderModifyResponse _ => 9
  | .orderMassCancel _ => 29
  | .orderMassCancelResponse _ => 30
  | .orderExecute _ => 10
  | .massQuote _ => 24
  | .massQuoteResponse _ => 25
  | .marketMakerCommand _ => 32
  | .marketMakerCommandResponse _ => 33
  | .requestForExecution _ => 28
  | .bidOfferUpdate _ => 31
  | .tradeCaptureReportSingle _ => 18
  | .tradeCaptureReportDual _ => 19
  | .tradeCaptureReportResponse _ => 20
  | .tradeBust _ => 23

def encode : Payload → List UInt8
  | .login message => Login.encode message
  | .loginResponse message => LoginResponse.encode message
  | .connectionClose message => ConnectionClose.encode message
  | .reject message => Reject.encode message
  | .test message => Test.encode message
  | .testEvent message => TestEvent.encode message
  | .tradingSessionStatus message => TradingSessionStatus.encode message
  | .orderAdd message => OrderAdd.encode message
  | .orderAddResponse message => OrderAddResponse.encode message
  | .orderCancel message => OrderCancel.encode message
  | .orderCancelResponse message => OrderCancelResponse.encode message
  | .orderModify message => OrderModify.encode message
  | .orderModifyResponse message => OrderModifyResponse.encode message
  | .orderMassCancel message => OrderMassCancel.encode message
  | .orderMassCancelResponse message => OrderMassCancelResponse.encode message
  | .orderExecute message => OrderExecute.encode message
  | .massQuote message => MassQuote.encode message
  | .massQuoteResponse message => MassQuoteResponse.encode message
  | .marketMakerCommand message => MarketMakerCommand.encode message
  | .marketMakerCommandResponse message => MarketMakerCommandResponse.encode message
  | .requestForExecution message => RequestForExecution.encode message
  | .bidOfferUpdate message => BidOfferUpdate.encode message
  | .tradeCaptureReportSingle message => TradeCaptureReportSingle.encode message
  | .tradeCaptureReportDual message => TradeCaptureReportDual.encode message
  | .tradeCaptureReportResponse message => TradeCaptureReportResponse.encode message
  | .tradeBust message => TradeBust.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 1184 := by
  cases message with
  | login inner =>
    simp only [encode, Login.encode_length]
    omega
  | loginResponse inner =>
    simp only [encode, LoginResponse.encode_length]
    omega
  | connectionClose inner =>
    simp only [encode, ConnectionClose.encode_length]
    omega
  | reject inner =>
    simp only [encode, Reject.encode_length]
    omega
  | test inner =>
    simp only [encode, Test.encode_length]
    omega
  | testEvent inner =>
    simp only [encode, TestEvent.encode_length]
    omega
  | tradingSessionStatus inner =>
    simp only [encode, TradingSessionStatus.encode_length]
    omega
  | orderAdd inner =>
    simp only [encode, OrderAdd.encode_length]
    omega
  | orderAddResponse inner =>
    simp only [encode, OrderAddResponse.encode_length]
    omega
  | orderCancel inner =>
    simp only [encode, OrderCancel.encode_length]
    omega
  | orderCancelResponse inner =>
    simp only [encode, OrderCancelResponse.encode_length]
    omega
  | orderModify inner =>
    simp only [encode, OrderModify.encode_length]
    omega
  | orderModifyResponse inner =>
    simp only [encode, OrderModifyResponse.encode_length]
    omega
  | orderMassCancel inner =>
    simp only [encode, OrderMassCancel.encode_length]
    omega
  | orderMassCancelResponse inner =>
    simp only [encode, OrderMassCancelResponse.encode_length]
    omega
  | orderExecute inner =>
    simp only [encode, OrderExecute.encode_length]
    omega
  | massQuote inner =>
    simp only [encode, MassQuote.encode_length]
    omega
  | massQuoteResponse inner =>
    simp only [encode, MassQuoteResponse.encode_length]
    omega
  | marketMakerCommand inner =>
    simp only [encode, MarketMakerCommand.encode_length]
    omega
  | marketMakerCommandResponse inner =>
    simp only [encode, MarketMakerCommandResponse.encode_length]
    omega
  | requestForExecution inner =>
    simp only [encode, RequestForExecution.encode_length]
    omega
  | bidOfferUpdate inner =>
    simp only [encode, BidOfferUpdate.encode_length]
    omega
  | tradeCaptureReportSingle inner =>
    simp only [encode, TradeCaptureReportSingle.encode_length]
    omega
  | tradeCaptureReportDual inner =>
    simp only [encode, TradeCaptureReportDual.encode_length]
    omega
  | tradeCaptureReportResponse inner =>
    simp only [encode, TradeCaptureReportResponse.encode_length]
    omega
  | tradeBust inner =>
    simp only [encode, TradeBust.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 2 then (Login.decode bytes).map fun (message, rest) => (.login message, rest)
  else if tag = 3 then (LoginResponse.decode bytes).map fun (message, rest) => (.loginResponse message, rest)
  else if tag = 12 then (ConnectionClose.decode bytes).map fun (message, rest) => (.connectionClose message, rest)
  else if tag = 15 then (Reject.decode bytes).map fun (message, rest) => (.reject message, rest)
  else if tag = 1 then (Test.decode bytes).map fun (message, rest) => (.test message, rest)
  else if tag = 255 then (TestEvent.decode bytes).map fun (message, rest) => (.testEvent message, rest)
  else if tag = 35 then (TradingSessionStatus.decode bytes).map fun (message, rest) => (.tradingSessionStatus message, rest)
  else if tag = 4 then (OrderAdd.decode bytes).map fun (message, rest) => (.orderAdd message, rest)
  else if tag = 5 then (OrderAddResponse.decode bytes).map fun (message, rest) => (.orderAddResponse message, rest)
  else if tag = 6 then (OrderCancel.decode bytes).map fun (message, rest) => (.orderCancel message, rest)
  else if tag = 7 then (OrderCancelResponse.decode bytes).map fun (message, rest) => (.orderCancelResponse message, rest)
  else if tag = 8 then (OrderModify.decode bytes).map fun (message, rest) => (.orderModify message, rest)
  else if tag = 9 then (OrderModifyResponse.decode bytes).map fun (message, rest) => (.orderModifyResponse message, rest)
  else if tag = 29 then (OrderMassCancel.decode bytes).map fun (message, rest) => (.orderMassCancel message, rest)
  else if tag = 30 then (OrderMassCancelResponse.decode bytes).map fun (message, rest) => (.orderMassCancelResponse message, rest)
  else if tag = 10 then (OrderExecute.decode bytes).map fun (message, rest) => (.orderExecute message, rest)
  else if tag = 24 then (MassQuote.decode bytes).map fun (message, rest) => (.massQuote message, rest)
  else if tag = 25 then (MassQuoteResponse.decode bytes).map fun (message, rest) => (.massQuoteResponse message, rest)
  else if tag = 32 then (MarketMakerCommand.decode bytes).map fun (message, rest) => (.marketMakerCommand message, rest)
  else if tag = 33 then (MarketMakerCommandResponse.decode bytes).map fun (message, rest) => (.marketMakerCommandResponse message, rest)
  else if tag = 28 then (RequestForExecution.decode bytes).map fun (message, rest) => (.requestForExecution message, rest)
  else if tag = 31 then (BidOfferUpdate.decode bytes).map fun (message, rest) => (.bidOfferUpdate message, rest)
  else if tag = 18 then (TradeCaptureReportSingle.decode bytes).map fun (message, rest) => (.tradeCaptureReportSingle message, rest)
  else if tag = 19 then (TradeCaptureReportDual.decode bytes).map fun (message, rest) => (.tradeCaptureReportDual message, rest)
  else if tag = 20 then (TradeCaptureReportResponse.decode bytes).map fun (message, rest) => (.tradeCaptureReportResponse message, rest)
  else if tag = 23 then (TradeBust.decode bytes).map fun (message, rest) => (.tradeBust message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message -/
structure Message where
  messageLength : BitVec 16
  sequenceNumber : BitVec 32
  timestamp : BitVec 64
  sourceTimestamp : BitVec 64
  payload : Payload
  deriving DecidableEq, Repr

namespace Message

def encode (message : Message) : List UInt8 :=
  encodeUIntLE 2 message.messageLength
    ++ (encodeUIntLE 2 (Payload.tag message.payload)
    ++ (encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.sourceTimestamp
    ++ (Payload.encode message.payload)))))

def decode (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (messageLength, bytes) ← decodeUIntLE 2 bytes
  let (messageType, bytes) ← decodeUIntLE 2 bytes
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (sourceTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (payload, bytes) ← Payload.decode messageType bytes
  pure ({ messageLength, sequenceNumber, timestamp, sourceTimestamp, payload }, bytes)

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Message) : (encode message).length ≤ 1208 := by
  unfold encode
  cases message.payload with
  | login inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Login.encode_length]
    omega
  | loginResponse inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, LoginResponse.encode_length]
    omega
  | connectionClose inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, ConnectionClose.encode_length]
    omega
  | reject inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Reject.encode_length]
    omega
  | test inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Test.encode_length]
    omega
  | testEvent inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, TestEvent.encode_length]
    omega
  | tradingSessionStatus inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, TradingSessionStatus.encode_length]
    omega
  | orderAdd inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OrderAdd.encode_length]
    omega
  | orderAddResponse inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OrderAddResponse.encode_length]
    omega
  | orderCancel inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OrderCancel.encode_length]
    omega
  | orderCancelResponse inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OrderCancelResponse.encode_length]
    omega
  | orderModify inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OrderModify.encode_length]
    omega
  | orderModifyResponse inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OrderModifyResponse.encode_length]
    omega
  | orderMassCancel inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OrderMassCancel.encode_length]
    omega
  | orderMassCancelResponse inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OrderMassCancelResponse.encode_length]
    omega
  | orderExecute inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OrderExecute.encode_length]
    omega
  | massQuote inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, MassQuote.encode_length]
    omega
  | massQuoteResponse inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, MassQuoteResponse.encode_length]
    omega
  | marketMakerCommand inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, MarketMakerCommand.encode_length]
    omega
  | marketMakerCommandResponse inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, MarketMakerCommandResponse.encode_length]
    omega
  | requestForExecution inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, RequestForExecution.encode_length]
    omega
  | bidOfferUpdate inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, BidOfferUpdate.encode_length]
    omega
  | tradeCaptureReportSingle inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, TradeCaptureReportSingle.encode_length]
    omega
  | tradeCaptureReportDual inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, TradeCaptureReportDual.encode_length]
    omega
  | tradeCaptureReportResponse inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, TradeCaptureReportResponse.encode_length]
    omega
  | tradeBust inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, TradeBust.encode_length]
    omega

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
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
  rw [Payload.decode_encode, some_bind]
  rfl

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

end Omi.GpwWseOrderentryWatsV17620
