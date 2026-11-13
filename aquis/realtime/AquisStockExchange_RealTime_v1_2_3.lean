import Wire

/-!
# Aquis Exchange Real Time Market Data Feed v1.2.3

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.

Note: Binary Mmt is a bit field set, proven as its 4 byte integer rather than bit by bit

Note: Market Flags is a bit field set, proven as its 1 byte integer rather than bit by bit

License: MIT No Attribution
-/

namespace Omi.AquisAquisstockexchangeRealtimeAmdV123

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

/-- Order Add Message: 27 bytes -/
structure OrderAddMessage where
  securityId : BitVec 16
  side : BitVec 8
  quantity : BitVec 32
  price : BitVec 64
  orderRef : BitVec 32
  timestamp : BitVec 64
  deriving DecidableEq, Repr

namespace OrderAddMessage

def encode (message : OrderAddMessage) : List UInt8 :=
  encodeUIntLE 2 message.securityId
    ++ (encodeUInt 1 message.side
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.orderRef
    ++ (encodeUIntLE 8 message.timestamp)))))

def decode (bytes : List UInt8) : Option (OrderAddMessage × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 2 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (orderRef, bytes) ← decodeUIntLE 4 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  pure ({ securityId, side, quantity, price, orderRef, timestamp }, bytes)

@[simp] theorem encode_length (message : OrderAddMessage) : (encode message).length = 27 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : OrderAddMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderAddMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderAddMessage

/-- Order Cancel Message: 14 bytes -/
structure OrderCancelMessage where
  securityId : BitVec 16
  orderRef : BitVec 32
  timestamp : BitVec 64
  deriving DecidableEq, Repr

namespace OrderCancelMessage

def encode (message : OrderCancelMessage) : List UInt8 :=
  encodeUIntLE 2 message.securityId
    ++ (encodeUIntLE 4 message.orderRef
    ++ (encodeUIntLE 8 message.timestamp))

def decode (bytes : List UInt8) : Option (OrderCancelMessage × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 2 bytes
  let (orderRef, bytes) ← decodeUIntLE 4 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  pure ({ securityId, orderRef, timestamp }, bytes)

@[simp] theorem encode_length (message : OrderCancelMessage) : (encode message).length = 14 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderCancelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancelMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderCancelMessage

/-- Order Modify Message: 26 bytes -/
structure OrderModifyMessage where
  securityId : BitVec 16
  remainingQuantity : BitVec 32
  price : BitVec 64
  orderRef : BitVec 32
  timestamp : BitVec 64
  deriving DecidableEq, Repr

namespace OrderModifyMessage

def encode (message : OrderModifyMessage) : List UInt8 :=
  encodeUIntLE 2 message.securityId
    ++ (encodeUIntLE 4 message.remainingQuantity
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.orderRef
    ++ (encodeUIntLE 8 message.timestamp))))

def decode (bytes : List UInt8) : Option (OrderModifyMessage × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 2 bytes
  let (remainingQuantity, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (orderRef, bytes) ← decodeUIntLE 4 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  pure ({ securityId, remainingQuantity, price, orderRef, timestamp }, bytes)

@[simp] theorem encode_length (message : OrderModifyMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderModifyMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderModifyMessage) (rest : List UInt8) :
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

end OrderModifyMessage

/-- Quote Add Replace Message: 36 bytes -/
structure QuoteAddReplaceMessage where
  traderId : BitVec 16
  securityId : BitVec 16
  bidQuantity : BitVec 32
  bidPrice : BitVec 64
  offerQuantity : BitVec 32
  offerPrice : BitVec 64
  timestamp : BitVec 64
  deriving DecidableEq, Repr

namespace QuoteAddReplaceMessage

def encode (message : QuoteAddReplaceMessage) : List UInt8 :=
  encodeUIntLE 2 message.traderId
    ++ (encodeUIntLE 2 message.securityId
    ++ (encodeUIntLE 4 message.bidQuantity
    ++ (encodeUIntLE 8 message.bidPrice
    ++ (encodeUIntLE 4 message.offerQuantity
    ++ (encodeUIntLE 8 message.offerPrice
    ++ (encodeUIntLE 8 message.timestamp))))))

def decode (bytes : List UInt8) : Option (QuoteAddReplaceMessage × List UInt8) := do
  let (traderId, bytes) ← decodeUIntLE 2 bytes
  let (securityId, bytes) ← decodeUIntLE 2 bytes
  let (bidQuantity, bytes) ← decodeUIntLE 4 bytes
  let (bidPrice, bytes) ← decodeUIntLE 8 bytes
  let (offerQuantity, bytes) ← decodeUIntLE 4 bytes
  let (offerPrice, bytes) ← decodeUIntLE 8 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  pure ({ traderId, securityId, bidQuantity, bidPrice, offerQuantity, offerPrice, timestamp }, bytes)

@[simp] theorem encode_length (message : QuoteAddReplaceMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : QuoteAddReplaceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteAddReplaceMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end QuoteAddReplaceMessage

/-- Quote Cancel Message: 12 bytes -/
structure QuoteCancelMessage where
  traderId : BitVec 16
  securityId : BitVec 16
  timestamp : BitVec 64
  deriving DecidableEq, Repr

namespace QuoteCancelMessage

def encode (message : QuoteCancelMessage) : List UInt8 :=
  encodeUIntLE 2 message.traderId
    ++ (encodeUIntLE 2 message.securityId
    ++ (encodeUIntLE 8 message.timestamp))

def decode (bytes : List UInt8) : Option (QuoteCancelMessage × List UInt8) := do
  let (traderId, bytes) ← decodeUIntLE 2 bytes
  let (securityId, bytes) ← decodeUIntLE 2 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  pure ({ traderId, securityId, timestamp }, bytes)

@[simp] theorem encode_length (message : QuoteCancelMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : QuoteCancelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteCancelMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end QuoteCancelMessage

/-- Trade Message: 35 bytes -/
structure TradeMessage where
  securityId : BitVec 16
  tradeType : BitVec 8
  tradedQuantity : BitVec 32
  executionPrice : BitVec 64
  orderRef : BitVec 32
  tradeRef : BitVec 32
  timestamp : BitVec 64
  binaryMmt : BitVec 32
  deriving DecidableEq, Repr

namespace TradeMessage

def encode (message : TradeMessage) : List UInt8 :=
  encodeUIntLE 2 message.securityId
    ++ (encodeUInt 1 message.tradeType
    ++ (encodeUIntLE 4 message.tradedQuantity
    ++ (encodeUIntLE 8 message.executionPrice
    ++ (encodeUIntLE 4 message.orderRef
    ++ (encodeUIntLE 4 message.tradeRef
    ++ (encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 4 message.binaryMmt)))))))

def decode (bytes : List UInt8) : Option (TradeMessage × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 2 bytes
  let (tradeType, bytes) ← decodeUInt 1 bytes
  let (tradedQuantity, bytes) ← decodeUIntLE 4 bytes
  let (executionPrice, bytes) ← decodeUIntLE 8 bytes
  let (orderRef, bytes) ← decodeUIntLE 4 bytes
  let (tradeRef, bytes) ← decodeUIntLE 4 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (binaryMmt, bytes) ← decodeUIntLE 4 bytes
  pure ({ securityId, tradeType, tradedQuantity, executionPrice, orderRef, tradeRef, timestamp, binaryMmt }, bytes)

@[simp] theorem encode_length (message : TradeMessage) : (encode message).length = 35 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : TradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeMessage

/-- Trade Report Message: 39 bytes -/
structure TradeReportMessage where
  securityId : BitVec 16
  tradeType : BitVec 8
  tradedQuantity : BitVec 32
  executionPrice : BitVec 64
  tradeRef : BitVec 32
  receivedTimestamp : BitVec 64
  binaryMmt : BitVec 32
  transactTime : BitVec 64
  deriving DecidableEq, Repr

namespace TradeReportMessage

def encode (message : TradeReportMessage) : List UInt8 :=
  encodeUIntLE 2 message.securityId
    ++ (encodeUInt 1 message.tradeType
    ++ (encodeUIntLE 4 message.tradedQuantity
    ++ (encodeUIntLE 8 message.executionPrice
    ++ (encodeUIntLE 4 message.tradeRef
    ++ (encodeUIntLE 8 message.receivedTimestamp
    ++ (encodeUIntLE 4 message.binaryMmt
    ++ (encodeUIntLE 8 message.transactTime)))))))

def decode (bytes : List UInt8) : Option (TradeReportMessage × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 2 bytes
  let (tradeType, bytes) ← decodeUInt 1 bytes
  let (tradedQuantity, bytes) ← decodeUIntLE 4 bytes
  let (executionPrice, bytes) ← decodeUIntLE 8 bytes
  let (tradeRef, bytes) ← decodeUIntLE 4 bytes
  let (receivedTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (binaryMmt, bytes) ← decodeUIntLE 4 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ securityId, tradeType, tradedQuantity, executionPrice, tradeRef, receivedTimestamp, binaryMmt, transactTime }, bytes)

@[simp] theorem encode_length (message : TradeReportMessage) : (encode message).length = 39 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : TradeReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeReportMessage

/-- Trade Report Modify Message: 51 bytes -/
structure TradeReportModifyMessage where
  securityId : BitVec 16
  tradeType : BitVec 8
  tradedQuantity : BitVec 32
  executionPrice : BitVec 64
  tradeRef : BitVec 32
  receivedTimestamp : BitVec 64
  binaryMmt : BitVec 32
  transactTime : BitVec 64
  origTradeRef : BitVec 32
  origTimestamp : BitVec 64
  deriving DecidableEq, Repr

namespace TradeReportModifyMessage

def encode (message : TradeReportModifyMessage) : List UInt8 :=
  encodeUIntLE 2 message.securityId
    ++ (encodeUInt 1 message.tradeType
    ++ (encodeUIntLE 4 message.tradedQuantity
    ++ (encodeUIntLE 8 message.executionPrice
    ++ (encodeUIntLE 4 message.tradeRef
    ++ (encodeUIntLE 8 message.receivedTimestamp
    ++ (encodeUIntLE 4 message.binaryMmt
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 4 message.origTradeRef
    ++ (encodeUIntLE 8 message.origTimestamp)))))))))

def decode (bytes : List UInt8) : Option (TradeReportModifyMessage × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 2 bytes
  let (tradeType, bytes) ← decodeUInt 1 bytes
  let (tradedQuantity, bytes) ← decodeUIntLE 4 bytes
  let (executionPrice, bytes) ← decodeUIntLE 8 bytes
  let (tradeRef, bytes) ← decodeUIntLE 4 bytes
  let (receivedTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (binaryMmt, bytes) ← decodeUIntLE 4 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (origTradeRef, bytes) ← decodeUIntLE 4 bytes
  let (origTimestamp, bytes) ← decodeUIntLE 8 bytes
  pure ({ securityId, tradeType, tradedQuantity, executionPrice, tradeRef, receivedTimestamp, binaryMmt, transactTime, origTradeRef, origTimestamp }, bytes)

@[simp] theorem encode_length (message : TradeReportModifyMessage) : (encode message).length = 51 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : TradeReportModifyMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeReportModifyMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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

end TradeReportModifyMessage

/-- Trade Report Cancel Message: 59 bytes -/
structure TradeReportCancelMessage where
  origSecurityId : BitVec 16
  origTradeType : BitVec 8
  origQuantity : BitVec 32
  origPrice : BitVec 64
  tradeRef : BitVec 32
  receivedTimestamp : BitVec 64
  binaryMmt : BitVec 32
  transactTime : BitVec 64
  origTradeRef : BitVec 32
  origTimestamp : BitVec 64
  origTransactTime : BitVec 64
  deriving DecidableEq, Repr

namespace TradeReportCancelMessage

def encode (message : TradeReportCancelMessage) : List UInt8 :=
  encodeUIntLE 2 message.origSecurityId
    ++ (encodeUInt 1 message.origTradeType
    ++ (encodeUIntLE 4 message.origQuantity
    ++ (encodeUIntLE 8 message.origPrice
    ++ (encodeUIntLE 4 message.tradeRef
    ++ (encodeUIntLE 8 message.receivedTimestamp
    ++ (encodeUIntLE 4 message.binaryMmt
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 4 message.origTradeRef
    ++ (encodeUIntLE 8 message.origTimestamp
    ++ (encodeUIntLE 8 message.origTransactTime))))))))))

def decode (bytes : List UInt8) : Option (TradeReportCancelMessage × List UInt8) := do
  let (origSecurityId, bytes) ← decodeUIntLE 2 bytes
  let (origTradeType, bytes) ← decodeUInt 1 bytes
  let (origQuantity, bytes) ← decodeUIntLE 4 bytes
  let (origPrice, bytes) ← decodeUIntLE 8 bytes
  let (tradeRef, bytes) ← decodeUIntLE 4 bytes
  let (receivedTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (binaryMmt, bytes) ← decodeUIntLE 4 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (origTradeRef, bytes) ← decodeUIntLE 4 bytes
  let (origTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (origTransactTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ origSecurityId, origTradeType, origQuantity, origPrice, tradeRef, receivedTimestamp, binaryMmt, transactTime, origTradeRef, origTimestamp, origTransactTime }, bytes)

@[simp] theorem encode_length (message : TradeReportCancelMessage) : (encode message).length = 59 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : TradeReportCancelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeReportCancelMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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

end TradeReportCancelMessage

/-- Trade Bust Message: 30 bytes -/
structure TradeBustMessage where
  securityId : BitVec 16
  tradedQuantity : BitVec 32
  executionPrice : BitVec 64
  tradeRef : BitVec 32
  timestamp : BitVec 64
  binaryMmt : BitVec 32
  deriving DecidableEq, Repr

namespace TradeBustMessage

def encode (message : TradeBustMessage) : List UInt8 :=
  encodeUIntLE 2 message.securityId
    ++ (encodeUIntLE 4 message.tradedQuantity
    ++ (encodeUIntLE 8 message.executionPrice
    ++ (encodeUIntLE 4 message.tradeRef
    ++ (encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 4 message.binaryMmt)))))

def decode (bytes : List UInt8) : Option (TradeBustMessage × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 2 bytes
  let (tradedQuantity, bytes) ← decodeUIntLE 4 bytes
  let (executionPrice, bytes) ← decodeUIntLE 8 bytes
  let (tradeRef, bytes) ← decodeUIntLE 4 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (binaryMmt, bytes) ← decodeUIntLE 4 bytes
  pure ({ securityId, tradedQuantity, executionPrice, tradeRef, timestamp, binaryMmt }, bytes)

@[simp] theorem encode_length (message : TradeBustMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : TradeBustMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeBustMessage) (rest : List UInt8) :
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

end TradeBustMessage

/-- Security Statistics Message: 19 bytes -/
structure SecurityStatisticsMessage where
  securityId : BitVec 16
  statisticsPrice : BitVec 64
  priceType : BitVec 8
  timestamp : BitVec 64
  deriving DecidableEq, Repr

namespace SecurityStatisticsMessage

def encode (message : SecurityStatisticsMessage) : List UInt8 :=
  encodeUIntLE 2 message.securityId
    ++ (encodeUIntLE 8 message.statisticsPrice
    ++ (encodeUInt 1 message.priceType
    ++ (encodeUIntLE 8 message.timestamp)))

def decode (bytes : List UInt8) : Option (SecurityStatisticsMessage × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 2 bytes
  let (statisticsPrice, bytes) ← decodeUIntLE 8 bytes
  let (priceType, bytes) ← decodeUInt 1 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  pure ({ securityId, statisticsPrice, priceType, timestamp }, bytes)

@[simp] theorem encode_length (message : SecurityStatisticsMessage) : (encode message).length = 19 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : SecurityStatisticsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityStatisticsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SecurityStatisticsMessage

/-- Trader Definition Message: 18 bytes -/
structure TraderDefinitionMessage where
  traderId : BitVec 16
  senderId : Alpha 16
  deriving DecidableEq, Repr

namespace TraderDefinitionMessage

def encode (message : TraderDefinitionMessage) : List UInt8 :=
  encodeUIntLE 2 message.traderId
    ++ (Alpha.encode message.senderId)

def decode (bytes : List UInt8) : Option (TraderDefinitionMessage × List UInt8) := do
  let (traderId, bytes) ← decodeUIntLE 2 bytes
  let (senderId, bytes) ← Alpha.decode 16 bytes
  pure ({ traderId, senderId }, bytes)

@[simp] theorem encode_length (message : TraderDefinitionMessage) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : TraderDefinitionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TraderDefinitionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TraderDefinitionMessage

/-- Tick Table Data Message: 27 bytes -/
structure TickTableDataMessage where
  tickTableId : BitVec 8
  name : Alpha 10
  threshold : BitVec 64
  tickSize : BitVec 64
  deriving DecidableEq, Repr

namespace TickTableDataMessage

def encode (message : TickTableDataMessage) : List UInt8 :=
  encodeUInt 1 message.tickTableId
    ++ (Alpha.encode message.name
    ++ (encodeUIntLE 8 message.threshold
    ++ (encodeUIntLE 8 message.tickSize)))

def decode (bytes : List UInt8) : Option (TickTableDataMessage × List UInt8) := do
  let (tickTableId, bytes) ← decodeUInt 1 bytes
  let (name, bytes) ← Alpha.decode 10 bytes
  let (threshold, bytes) ← decodeUIntLE 8 bytes
  let (tickSize, bytes) ← decodeUIntLE 8 bytes
  pure ({ tickTableId, name, threshold, tickSize }, bytes)

@[simp] theorem encode_length (message : TickTableDataMessage) : (encode message).length = 27 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : TickTableDataMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TickTableDataMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TickTableDataMessage

/-- Security Definition Message: 28 bytes -/
structure SecurityDefinitionMessage where
  securityId : BitVec 16
  umtf : Alpha 6
  isin : Alpha 12
  currency : Alpha 3
  mic : Alpha 4
  tickTableId : BitVec 8
  deriving DecidableEq, Repr

namespace SecurityDefinitionMessage

def encode (message : SecurityDefinitionMessage) : List UInt8 :=
  encodeUIntLE 2 message.securityId
    ++ (Alpha.encode message.umtf
    ++ (Alpha.encode message.isin
    ++ (Alpha.encode message.currency
    ++ (Alpha.encode message.mic
    ++ (encodeUInt 1 message.tickTableId)))))

def decode (bytes : List UInt8) : Option (SecurityDefinitionMessage × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 2 bytes
  let (umtf, bytes) ← Alpha.decode 6 bytes
  let (isin, bytes) ← Alpha.decode 12 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (mic, bytes) ← Alpha.decode 4 bytes
  let (tickTableId, bytes) ← decodeUInt 1 bytes
  pure ({ securityId, umtf, isin, currency, mic, tickTableId }, bytes)

@[simp] theorem encode_length (message : SecurityDefinitionMessage) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SecurityDefinitionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityDefinitionMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SecurityDefinitionMessage

/-- Security Status Message: 12 bytes -/
structure SecurityStatusMessage where
  securityId : BitVec 16
  tradingStatus : BitVec 8
  marketFlags : BitVec 8
  timestamp : BitVec 64
  deriving DecidableEq, Repr

namespace SecurityStatusMessage

def encode (message : SecurityStatusMessage) : List UInt8 :=
  encodeUIntLE 2 message.securityId
    ++ (encodeUInt 1 message.tradingStatus
    ++ (encodeUIntLE 1 message.marketFlags
    ++ (encodeUIntLE 8 message.timestamp)))

def decode (bytes : List UInt8) : Option (SecurityStatusMessage × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 2 bytes
  let (tradingStatus, bytes) ← decodeUInt 1 bytes
  let (marketFlags, bytes) ← decodeUIntLE 1 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  pure ({ securityId, tradingStatus, marketFlags, timestamp }, bytes)

@[simp] theorem encode_length (message : SecurityStatusMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : SecurityStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SecurityStatusMessage

/-- Aod Update Message: 22 bytes -/
structure AodUpdateMessage where
  securityId : BitVec 16
  indicativePrice : BitVec 64
  matchVol : BitVec 32
  timestamp : BitVec 64
  deriving DecidableEq, Repr

namespace AodUpdateMessage

def encode (message : AodUpdateMessage) : List UInt8 :=
  encodeUIntLE 2 message.securityId
    ++ (encodeUIntLE 8 message.indicativePrice
    ++ (encodeUIntLE 4 message.matchVol
    ++ (encodeUIntLE 8 message.timestamp)))

def decode (bytes : List UInt8) : Option (AodUpdateMessage × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 2 bytes
  let (indicativePrice, bytes) ← decodeUIntLE 8 bytes
  let (matchVol, bytes) ← decodeUIntLE 4 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  pure ({ securityId, indicativePrice, matchVol, timestamp }, bytes)

@[simp] theorem encode_length (message : AodUpdateMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : AodUpdateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AodUpdateMessage) (rest : List UInt8) :
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

end AodUpdateMessage

/-- Any Payload, selected by Msg Type -/
inductive Payload where
  | heartbeatMessage (message : HeartbeatMessage) -- 1
  | orderAddMessage (message : OrderAddMessage) -- 2
  | orderCancelMessage (message : OrderCancelMessage) -- 3
  | orderModifyMessage (message : OrderModifyMessage) -- 4
  | quoteAddReplaceMessage (message : QuoteAddReplaceMessage) -- 20
  | quoteCancelMessage (message : QuoteCancelMessage) -- 21
  | tradeMessage (message : TradeMessage) -- 5
  | tradeReportMessage (message : TradeReportMessage) -- 25
  | tradeReportModifyMessage (message : TradeReportModifyMessage) -- 26
  | tradeReportCancelMessage (message : TradeReportCancelMessage) -- 27
  | tradeBustMessage (message : TradeBustMessage) -- 6
  | securityStatisticsMessage (message : SecurityStatisticsMessage) -- 22
  | traderDefinitionMessage (message : TraderDefinitionMessage) -- 23
  | tickTableDataMessage (message : TickTableDataMessage) -- 7
  | securityDefinitionMessage (message : SecurityDefinitionMessage) -- 8
  | securityStatusMessage (message : SecurityStatusMessage) -- 9
  | aodUpdateMessage (message : AodUpdateMessage) -- 17
  deriving DecidableEq, Repr

namespace Payload

/-- The Msg Type each message is sent under -/
def tag : Payload → BitVec 8
  | .heartbeatMessage _ => 1
  | .orderAddMessage _ => 2
  | .orderCancelMessage _ => 3
  | .orderModifyMessage _ => 4
  | .quoteAddReplaceMessage _ => 20
  | .quoteCancelMessage _ => 21
  | .tradeMessage _ => 5
  | .tradeReportMessage _ => 25
  | .tradeReportModifyMessage _ => 26
  | .tradeReportCancelMessage _ => 27
  | .tradeBustMessage _ => 6
  | .securityStatisticsMessage _ => 22
  | .traderDefinitionMessage _ => 23
  | .tickTableDataMessage _ => 7
  | .securityDefinitionMessage _ => 8
  | .securityStatusMessage _ => 9
  | .aodUpdateMessage _ => 17

def encode : Payload → List UInt8
  | .heartbeatMessage message => HeartbeatMessage.encode message
  | .orderAddMessage message => OrderAddMessage.encode message
  | .orderCancelMessage message => OrderCancelMessage.encode message
  | .orderModifyMessage message => OrderModifyMessage.encode message
  | .quoteAddReplaceMessage message => QuoteAddReplaceMessage.encode message
  | .quoteCancelMessage message => QuoteCancelMessage.encode message
  | .tradeMessage message => TradeMessage.encode message
  | .tradeReportMessage message => TradeReportMessage.encode message
  | .tradeReportModifyMessage message => TradeReportModifyMessage.encode message
  | .tradeReportCancelMessage message => TradeReportCancelMessage.encode message
  | .tradeBustMessage message => TradeBustMessage.encode message
  | .securityStatisticsMessage message => SecurityStatisticsMessage.encode message
  | .traderDefinitionMessage message => TraderDefinitionMessage.encode message
  | .tickTableDataMessage message => TickTableDataMessage.encode message
  | .securityDefinitionMessage message => SecurityDefinitionMessage.encode message
  | .securityStatusMessage message => SecurityStatusMessage.encode message
  | .aodUpdateMessage message => AodUpdateMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 59 := by
  cases message with
  | heartbeatMessage inner =>
    simp only [encode, HeartbeatMessage.encode_length]
    omega
  | orderAddMessage inner =>
    simp only [encode, OrderAddMessage.encode_length]
    omega
  | orderCancelMessage inner =>
    simp only [encode, OrderCancelMessage.encode_length]
    omega
  | orderModifyMessage inner =>
    simp only [encode, OrderModifyMessage.encode_length]
    omega
  | quoteAddReplaceMessage inner =>
    simp only [encode, QuoteAddReplaceMessage.encode_length]
    omega
  | quoteCancelMessage inner =>
    simp only [encode, QuoteCancelMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [encode, TradeMessage.encode_length]
    omega
  | tradeReportMessage inner =>
    simp only [encode, TradeReportMessage.encode_length]
    omega
  | tradeReportModifyMessage inner =>
    simp only [encode, TradeReportModifyMessage.encode_length]
    omega
  | tradeReportCancelMessage inner =>
    simp only [encode, TradeReportCancelMessage.encode_length]
    omega
  | tradeBustMessage inner =>
    simp only [encode, TradeBustMessage.encode_length]
    omega
  | securityStatisticsMessage inner =>
    simp only [encode, SecurityStatisticsMessage.encode_length]
    omega
  | traderDefinitionMessage inner =>
    simp only [encode, TraderDefinitionMessage.encode_length]
    omega
  | tickTableDataMessage inner =>
    simp only [encode, TickTableDataMessage.encode_length]
    omega
  | securityDefinitionMessage inner =>
    simp only [encode, SecurityDefinitionMessage.encode_length]
    omega
  | securityStatusMessage inner =>
    simp only [encode, SecurityStatusMessage.encode_length]
    omega
  | aodUpdateMessage inner =>
    simp only [encode, AodUpdateMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 1 then (HeartbeatMessage.decode bytes).map fun (message, rest) => (.heartbeatMessage message, rest)
  else if tag = 2 then (OrderAddMessage.decode bytes).map fun (message, rest) => (.orderAddMessage message, rest)
  else if tag = 3 then (OrderCancelMessage.decode bytes).map fun (message, rest) => (.orderCancelMessage message, rest)
  else if tag = 4 then (OrderModifyMessage.decode bytes).map fun (message, rest) => (.orderModifyMessage message, rest)
  else if tag = 20 then (QuoteAddReplaceMessage.decode bytes).map fun (message, rest) => (.quoteAddReplaceMessage message, rest)
  else if tag = 21 then (QuoteCancelMessage.decode bytes).map fun (message, rest) => (.quoteCancelMessage message, rest)
  else if tag = 5 then (TradeMessage.decode bytes).map fun (message, rest) => (.tradeMessage message, rest)
  else if tag = 25 then (TradeReportMessage.decode bytes).map fun (message, rest) => (.tradeReportMessage message, rest)
  else if tag = 26 then (TradeReportModifyMessage.decode bytes).map fun (message, rest) => (.tradeReportModifyMessage message, rest)
  else if tag = 27 then (TradeReportCancelMessage.decode bytes).map fun (message, rest) => (.tradeReportCancelMessage message, rest)
  else if tag = 6 then (TradeBustMessage.decode bytes).map fun (message, rest) => (.tradeBustMessage message, rest)
  else if tag = 22 then (SecurityStatisticsMessage.decode bytes).map fun (message, rest) => (.securityStatisticsMessage message, rest)
  else if tag = 23 then (TraderDefinitionMessage.decode bytes).map fun (message, rest) => (.traderDefinitionMessage message, rest)
  else if tag = 7 then (TickTableDataMessage.decode bytes).map fun (message, rest) => (.tickTableDataMessage message, rest)
  else if tag = 8 then (SecurityDefinitionMessage.decode bytes).map fun (message, rest) => (.securityDefinitionMessage message, rest)
  else if tag = 9 then (SecurityStatusMessage.decode bytes).map fun (message, rest) => (.securityStatusMessage message, rest)
  else if tag = 17 then (AodUpdateMessage.decode bytes).map fun (message, rest) => (.aodUpdateMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message -/
structure Message where
  seqNo : BitVec 32
  payload : Payload
  deriving DecidableEq, Repr

namespace Message

def encodeBody (message : Message) : List UInt8 :=
  encodeUIntLE 4 message.seqNo
    ++ (Payload.encode message.payload)

def decodeBody (msgType : BitVec 8) (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (seqNo, bytes) ← decodeUIntLE 4 bytes
  let (payload, bytes) ← Payload.decode msgType bytes
  pure ({ seqNo, payload }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (Payload.tag message.payload) (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 2 < 256 ^ 1 := by
  unfold encodeBody
  cases message.payload with
  | heartbeatMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, HeartbeatMessage.encode_length]
    omega
  | orderAddMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, OrderAddMessage.encode_length]
    omega
  | orderCancelMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, OrderCancelMessage.encode_length]
    omega
  | orderModifyMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, OrderModifyMessage.encode_length]
    omega
  | quoteAddReplaceMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, QuoteAddReplaceMessage.encode_length]
    omega
  | quoteCancelMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, QuoteCancelMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, TradeMessage.encode_length]
    omega
  | tradeReportMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, TradeReportMessage.encode_length]
    omega
  | tradeReportModifyMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, TradeReportModifyMessage.encode_length]
    omega
  | tradeReportCancelMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, TradeReportCancelMessage.encode_length]
    omega
  | tradeBustMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, TradeBustMessage.encode_length]
    omega
  | securityStatisticsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, SecurityStatisticsMessage.encode_length]
    omega
  | traderDefinitionMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, TraderDefinitionMessage.encode_length]
    omega
  | tickTableDataMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, TickTableDataMessage.encode_length]
    omega
  | securityDefinitionMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, SecurityDefinitionMessage.encode_length]
    omega
  | securityStatusMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, SecurityStatusMessage.encode_length]
    omega
  | aodUpdateMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, AodUpdateMessage.encode_length]
    omega

/-- Size rule: Msg Length counts the bytes after it plus 2, so it is written from the body and checked on decode; Msg Type is read ahead of it -/
def encode (message : Message) : List UInt8 :=
  encodeUInt 1 (Payload.tag message.payload)
    ++ (encodeFramed 1 2 encodeBody message)

def decode (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (msgType, bytes) ← decodeUInt 1 bytes
  decodeFramed 1 2 (decodeBody msgType) bytes

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  exact decodeFramed_encodeFramed 1 2 encodeBody (decodeBody (Payload.tag message.payload)) message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, encodeFramed_length]
  omega

end Message

/-- Packet -/
structure Packet where
  message : Bounded 1 Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUInt 1 (BitVec.ofNat (8 * 1) message.message.val.length)
    ++ (encodeMany Message.encode message.message.val)

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (messageCount, bytes) ← decodeUInt 1 bytes
  let (message_, bytes) ← decodeMany Message.decode messageCount.toNat bytes
  if fits_message : message_.length < 256 ^ 1 then
    pure ({ message := ⟨message_, fits_message⟩ }, bytes)
  else none

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt]
  rfl

end Packet

end Omi.AquisAquisstockexchangeRealtimeAmdV123
