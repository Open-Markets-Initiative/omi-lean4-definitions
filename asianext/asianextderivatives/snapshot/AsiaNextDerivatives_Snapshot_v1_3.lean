import Wire

/-!
# AsiaNext Market Data Snapshot v1.3

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.

Note: Market Flags is a bit field set, proven as its 1 byte integer rather than bit by bit

Note: Flags is a bit field set, proven as its 2 byte integer rather than bit by bit

Note: Futures Flags is a bit field set, proven as its 2 byte integer rather than bit by bit

Note: Options Flags is a bit field set, proven as its 2 byte integer rather than bit by bit

License: MIT No Attribution
-/

namespace Omi.AsianextAsianextderivativesSnapshotAmdV13

/-- Snapshot Start Message: 16 bytes -/
structure SnapshotStartMessage where
  streamSeqNo : BitVec 32
  securityCount : BitVec 32
  timestamp : BitVec 64
  deriving DecidableEq, Repr

namespace SnapshotStartMessage

def encode (message : SnapshotStartMessage) : List UInt8 :=
  encodeUIntLE 4 message.streamSeqNo
    ++ (encodeUIntLE 4 message.securityCount
    ++ (encodeUIntLE 8 message.timestamp))

def decode (bytes : List UInt8) : Option (SnapshotStartMessage × List UInt8) := do
  let (streamSeqNo, bytes) ← decodeUIntLE 4 bytes
  let (securityCount, bytes) ← decodeUIntLE 4 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  pure ({ streamSeqNo, securityCount, timestamp }, bytes)

@[simp] theorem encode_length (message : SnapshotStartMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : SnapshotStartMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SnapshotStartMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SnapshotStartMessage

/-- Book Status Message: 32 bytes -/
structure BookStatusMessage where
  securityId : BitVec 32
  tradingStatus : BitVec 8
  marketFlags : BitVec 8
  entries : BitVec 16
  closingBuyQty : BitVec 64
  closingSellQty : BitVec 64
  indicativePrice : BitVec 64
  deriving DecidableEq, Repr

namespace BookStatusMessage

def encode (message : BookStatusMessage) : List UInt8 :=
  encodeUIntLE 4 message.securityId
    ++ (encodeUIntLE 1 message.tradingStatus
    ++ (encodeUIntLE 1 message.marketFlags
    ++ (encodeUIntLE 2 message.entries
    ++ (encodeUIntLE 8 message.closingBuyQty
    ++ (encodeUIntLE 8 message.closingSellQty
    ++ (encodeUIntLE 8 message.indicativePrice))))))

def decode (bytes : List UInt8) : Option (BookStatusMessage × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (tradingStatus, bytes) ← decodeUIntLE 1 bytes
  let (marketFlags, bytes) ← decodeUIntLE 1 bytes
  let (entries, bytes) ← decodeUIntLE 2 bytes
  let (closingBuyQty, bytes) ← decodeUIntLE 8 bytes
  let (closingSellQty, bytes) ← decodeUIntLE 8 bytes
  let (indicativePrice, bytes) ← decodeUIntLE 8 bytes
  pure ({ securityId, tradingStatus, marketFlags, entries, closingBuyQty, closingSellQty, indicativePrice }, bytes)

@[simp] theorem encode_length (message : BookStatusMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : BookStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BookStatusMessage) (rest : List UInt8) :
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

end BookStatusMessage

/-- Book Entry Message: 29 bytes -/
structure BookEntryMessage where
  securityId : BitVec 32
  side : BitVec 8
  quantity : BitVec 64
  price : BitVec 64
  orderRef : BitVec 64
  deriving DecidableEq, Repr

namespace BookEntryMessage

def encode (message : BookEntryMessage) : List UInt8 :=
  encodeUIntLE 4 message.securityId
    ++ (encodeUIntLE 1 message.side
    ++ (encodeUIntLE 8 message.quantity
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.orderRef))))

def decode (bytes : List UInt8) : Option (BookEntryMessage × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← decodeUIntLE 1 bytes
  let (quantity, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (orderRef, bytes) ← decodeUIntLE 8 bytes
  pure ({ securityId, side, quantity, price, orderRef }, bytes)

@[simp] theorem encode_length (message : BookEntryMessage) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : BookEntryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BookEntryMessage) (rest : List UInt8) :
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

end BookEntryMessage

/-- Tick Table Data Message: 27 bytes -/
structure TickTableDataMessage where
  tickTableId : BitVec 8
  name : Alpha 10
  threshold : BitVec 64
  tickSize : BitVec 64
  deriving DecidableEq, Repr

namespace TickTableDataMessage

def encode (message : TickTableDataMessage) : List UInt8 :=
  encodeUIntLE 1 message.tickTableId
    ++ (Alpha.encode message.name
    ++ (encodeUIntLE 8 message.threshold
    ++ (encodeUIntLE 8 message.tickSize)))

def decode (bytes : List UInt8) : Option (TickTableDataMessage × List UInt8) := do
  let (tickTableId, bytes) ← decodeUIntLE 1 bytes
  let (name, bytes) ← Alpha.decode 10 bytes
  let (threshold, bytes) ← decodeUIntLE 8 bytes
  let (tickSize, bytes) ← decodeUIntLE 8 bytes
  pure ({ tickTableId, name, threshold, tickSize }, bytes)

@[simp] theorem encode_length (message : TickTableDataMessage) : (encode message).length = 27 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : TickTableDataMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TickTableDataMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TickTableDataMessage

/-- Lot Size Composite: 9 bytes -/
structure LotSizeComposite where
  lotSize : BitVec 64
  lotSizeDecimal : BitVec 8
  deriving DecidableEq, Repr

namespace LotSizeComposite

def encode (message : LotSizeComposite) : List UInt8 :=
  encodeUIntLE 8 message.lotSize
    ++ (encodeUIntLE 1 message.lotSizeDecimal)

def decode (bytes : List UInt8) : Option (LotSizeComposite × List UInt8) := do
  let (lotSize, bytes) ← decodeUIntLE 8 bytes
  let (lotSizeDecimal, bytes) ← decodeUIntLE 1 bytes
  pure ({ lotSize, lotSizeDecimal }, bytes)

@[simp] theorem encode_length (message : LotSizeComposite) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : LotSizeComposite) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LotSizeComposite) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end LotSizeComposite

/-- Security Definition Message: 61 bytes -/
structure SecurityDefinitionMessage where
  securityId : BitVec 32
  umtf : Alpha 6
  isin : Alpha 12
  currency : Alpha 3
  mic : Alpha 4
  tickTableId : BitVec 8
  flags : BitVec 16
  exchangeSymbol : Alpha 20
  lotSizeComposite : LotSizeComposite
  deriving DecidableEq, Repr

namespace SecurityDefinitionMessage

def encode (message : SecurityDefinitionMessage) : List UInt8 :=
  encodeUIntLE 4 message.securityId
    ++ (Alpha.encode message.umtf
    ++ (Alpha.encode message.isin
    ++ (Alpha.encode message.currency
    ++ (Alpha.encode message.mic
    ++ (encodeUIntLE 1 message.tickTableId
    ++ (encodeUIntLE 2 message.flags
    ++ (Alpha.encode message.exchangeSymbol
    ++ (LotSizeComposite.encode message.lotSizeComposite))))))))

def decode (bytes : List UInt8) : Option (SecurityDefinitionMessage × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (umtf, bytes) ← Alpha.decode 6 bytes
  let (isin, bytes) ← Alpha.decode 12 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (mic, bytes) ← Alpha.decode 4 bytes
  let (tickTableId, bytes) ← decodeUIntLE 1 bytes
  let (flags, bytes) ← decodeUIntLE 2 bytes
  let (exchangeSymbol, bytes) ← Alpha.decode 20 bytes
  let (lotSizeComposite, bytes) ← LotSizeComposite.decode bytes
  pure ({ securityId, umtf, isin, currency, mic, tickTableId, flags, exchangeSymbol, lotSizeComposite }, bytes)

@[simp] theorem encode_length (message : SecurityDefinitionMessage) : (encode message).length = 61 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, LotSizeComposite.encode_length]

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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [LotSizeComposite.decode_encode, some_bind]
  rfl

end SecurityDefinitionMessage

/-- Contract Size Composite: 9 bytes -/
structure ContractSizeComposite where
  contractSize : BitVec 64
  contractSizeDecimals : BitVec 8
  deriving DecidableEq, Repr

namespace ContractSizeComposite

def encode (message : ContractSizeComposite) : List UInt8 :=
  encodeUIntLE 8 message.contractSize
    ++ (encodeUIntLE 1 message.contractSizeDecimals)

def decode (bytes : List UInt8) : Option (ContractSizeComposite × List UInt8) := do
  let (contractSize, bytes) ← decodeUIntLE 8 bytes
  let (contractSizeDecimals, bytes) ← decodeUIntLE 1 bytes
  pure ({ contractSize, contractSizeDecimals }, bytes)

@[simp] theorem encode_length (message : ContractSizeComposite) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : ContractSizeComposite) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ContractSizeComposite) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ContractSizeComposite

/-- Security Definition Futures Message: 99 bytes -/
structure SecurityDefinitionFuturesMessage where
  securityId : BitVec 32
  umtf : Alpha 6
  isin : Alpha 12
  currency : Alpha 3
  mic : Alpha 4
  tickTableId : BitVec 8
  futuresFlags : BitVec 16
  exchangeSymbol : Alpha 20
  lotSizeComposite : LotSizeComposite
  maturityDate : BitVec 64
  settlementType : BitVec 8
  contractSizeComposite : ContractSizeComposite
  underlying : Alpha 20
  deriving DecidableEq, Repr

namespace SecurityDefinitionFuturesMessage

def encode (message : SecurityDefinitionFuturesMessage) : List UInt8 :=
  encodeUIntLE 4 message.securityId
    ++ (Alpha.encode message.umtf
    ++ (Alpha.encode message.isin
    ++ (Alpha.encode message.currency
    ++ (Alpha.encode message.mic
    ++ (encodeUIntLE 1 message.tickTableId
    ++ (encodeUIntLE 2 message.futuresFlags
    ++ (Alpha.encode message.exchangeSymbol
    ++ (LotSizeComposite.encode message.lotSizeComposite
    ++ (encodeUIntLE 8 message.maturityDate
    ++ (encodeUIntLE 1 message.settlementType
    ++ (ContractSizeComposite.encode message.contractSizeComposite
    ++ (Alpha.encode message.underlying))))))))))))

def decode (bytes : List UInt8) : Option (SecurityDefinitionFuturesMessage × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (umtf, bytes) ← Alpha.decode 6 bytes
  let (isin, bytes) ← Alpha.decode 12 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (mic, bytes) ← Alpha.decode 4 bytes
  let (tickTableId, bytes) ← decodeUIntLE 1 bytes
  let (futuresFlags, bytes) ← decodeUIntLE 2 bytes
  let (exchangeSymbol, bytes) ← Alpha.decode 20 bytes
  let (lotSizeComposite, bytes) ← LotSizeComposite.decode bytes
  let (maturityDate, bytes) ← decodeUIntLE 8 bytes
  let (settlementType, bytes) ← decodeUIntLE 1 bytes
  let (contractSizeComposite, bytes) ← ContractSizeComposite.decode bytes
  let (underlying, bytes) ← Alpha.decode 20 bytes
  pure ({ securityId, umtf, isin, currency, mic, tickTableId, futuresFlags, exchangeSymbol, lotSizeComposite, maturityDate, settlementType, contractSizeComposite, underlying }, bytes)

@[simp] theorem encode_length (message : SecurityDefinitionFuturesMessage) : (encode message).length = 99 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, LotSizeComposite.encode_length, ContractSizeComposite.encode_length]

theorem encode_length_pos (message : SecurityDefinitionFuturesMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityDefinitionFuturesMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LotSizeComposite.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, ContractSizeComposite.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SecurityDefinitionFuturesMessage

/-- Security Definition Options Message: 109 bytes -/
structure SecurityDefinitionOptionsMessage where
  securityId : BitVec 32
  umtf : Alpha 6
  isin : Alpha 12
  currency : Alpha 3
  mic : Alpha 4
  tickTableId : BitVec 8
  optionsFlags : BitVec 16
  exchangeSymbol : Alpha 20
  lotSizeComposite : LotSizeComposite
  maturityDate : BitVec 64
  settlementType : BitVec 8
  contractSizeComposite : ContractSizeComposite
  underlying : Alpha 20
  optionType : BitVec 8
  exerciseStyle : BitVec 8
  strikePrice : BitVec 64
  deriving DecidableEq, Repr

namespace SecurityDefinitionOptionsMessage

def encode (message : SecurityDefinitionOptionsMessage) : List UInt8 :=
  encodeUIntLE 4 message.securityId
    ++ (Alpha.encode message.umtf
    ++ (Alpha.encode message.isin
    ++ (Alpha.encode message.currency
    ++ (Alpha.encode message.mic
    ++ (encodeUIntLE 1 message.tickTableId
    ++ (encodeUIntLE 2 message.optionsFlags
    ++ (Alpha.encode message.exchangeSymbol
    ++ (LotSizeComposite.encode message.lotSizeComposite
    ++ (encodeUIntLE 8 message.maturityDate
    ++ (encodeUIntLE 1 message.settlementType
    ++ (ContractSizeComposite.encode message.contractSizeComposite
    ++ (Alpha.encode message.underlying
    ++ (encodeUIntLE 1 message.optionType
    ++ (encodeUIntLE 1 message.exerciseStyle
    ++ (encodeUIntLE 8 message.strikePrice)))))))))))))))

def decode (bytes : List UInt8) : Option (SecurityDefinitionOptionsMessage × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (umtf, bytes) ← Alpha.decode 6 bytes
  let (isin, bytes) ← Alpha.decode 12 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (mic, bytes) ← Alpha.decode 4 bytes
  let (tickTableId, bytes) ← decodeUIntLE 1 bytes
  let (optionsFlags, bytes) ← decodeUIntLE 2 bytes
  let (exchangeSymbol, bytes) ← Alpha.decode 20 bytes
  let (lotSizeComposite, bytes) ← LotSizeComposite.decode bytes
  let (maturityDate, bytes) ← decodeUIntLE 8 bytes
  let (settlementType, bytes) ← decodeUIntLE 1 bytes
  let (contractSizeComposite, bytes) ← ContractSizeComposite.decode bytes
  let (underlying, bytes) ← Alpha.decode 20 bytes
  let (optionType, bytes) ← decodeUIntLE 1 bytes
  let (exerciseStyle, bytes) ← decodeUIntLE 1 bytes
  let (strikePrice, bytes) ← decodeUIntLE 8 bytes
  pure ({ securityId, umtf, isin, currency, mic, tickTableId, optionsFlags, exchangeSymbol, lotSizeComposite, maturityDate, settlementType, contractSizeComposite, underlying, optionType, exerciseStyle, strikePrice }, bytes)

@[simp] theorem encode_length (message : SecurityDefinitionOptionsMessage) : (encode message).length = 109 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, LotSizeComposite.encode_length, ContractSizeComposite.encode_length]

theorem encode_length_pos (message : SecurityDefinitionOptionsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityDefinitionOptionsMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LotSizeComposite.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, ContractSizeComposite.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SecurityDefinitionOptionsMessage

/-- Security Status Message: 15 bytes -/
structure SecurityStatusMessage where
  securityId : BitVec 32
  tradingStatus : BitVec 8
  marketFlags : BitVec 8
  timestamp : BitVec 64
  tradingPhase : BitVec 8
  deriving DecidableEq, Repr

namespace SecurityStatusMessage

def encode (message : SecurityStatusMessage) : List UInt8 :=
  encodeUIntLE 4 message.securityId
    ++ (encodeUIntLE 1 message.tradingStatus
    ++ (encodeUIntLE 1 message.marketFlags
    ++ (encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 1 message.tradingPhase))))

def decode (bytes : List UInt8) : Option (SecurityStatusMessage × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (tradingStatus, bytes) ← decodeUIntLE 1 bytes
  let (marketFlags, bytes) ← decodeUIntLE 1 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (tradingPhase, bytes) ← decodeUIntLE 1 bytes
  pure ({ securityId, tradingStatus, marketFlags, timestamp, tradingPhase }, bytes)

@[simp] theorem encode_length (message : SecurityStatusMessage) : (encode message).length = 15 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : SecurityStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityStatusMessage) (rest : List UInt8) :
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

end SecurityStatusMessage

/-- Sequence Number Reset Message: 4 bytes -/
structure SequenceNumberResetMessage where
  nextSeqNo : BitVec 32
  deriving DecidableEq, Repr

namespace SequenceNumberResetMessage

def encode (message : SequenceNumberResetMessage) : List UInt8 :=
  encodeUIntLE 4 message.nextSeqNo

def decode (bytes : List UInt8) : Option (SequenceNumberResetMessage × List UInt8) := do
  let (nextSeqNo, bytes) ← decodeUIntLE 4 bytes
  pure ({ nextSeqNo }, bytes)

@[simp] theorem encode_length (message : SequenceNumberResetMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : SequenceNumberResetMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SequenceNumberResetMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SequenceNumberResetMessage

/-- Any Payload, selected by Msg Type -/
inductive Payload where
  | snapshotStartMessage (message : SnapshotStartMessage) -- 10
  | bookStatusMessage (message : BookStatusMessage) -- 11
  | bookEntryMessage (message : BookEntryMessage) -- 12
  | tickTableDataMessage (message : TickTableDataMessage) -- 7
  | securityDefinitionMessage (message : SecurityDefinitionMessage) -- 8
  | securityDefinitionFuturesMessage (message : SecurityDefinitionFuturesMessage) -- 30
  | securityDefinitionOptionsMessage (message : SecurityDefinitionOptionsMessage) -- 32
  | securityStatusMessage (message : SecurityStatusMessage) -- 9
  | sequenceNumberResetMessage (message : SequenceNumberResetMessage) -- 29
  deriving DecidableEq, Repr

namespace Payload

/-- The Msg Type each message is sent under -/
def tag : Payload → BitVec 8
  | .snapshotStartMessage _ => 10
  | .bookStatusMessage _ => 11
  | .bookEntryMessage _ => 12
  | .tickTableDataMessage _ => 7
  | .securityDefinitionMessage _ => 8
  | .securityDefinitionFuturesMessage _ => 30
  | .securityDefinitionOptionsMessage _ => 32
  | .securityStatusMessage _ => 9
  | .sequenceNumberResetMessage _ => 29

def encode : Payload → List UInt8
  | .snapshotStartMessage message => SnapshotStartMessage.encode message
  | .bookStatusMessage message => BookStatusMessage.encode message
  | .bookEntryMessage message => BookEntryMessage.encode message
  | .tickTableDataMessage message => TickTableDataMessage.encode message
  | .securityDefinitionMessage message => SecurityDefinitionMessage.encode message
  | .securityDefinitionFuturesMessage message => SecurityDefinitionFuturesMessage.encode message
  | .securityDefinitionOptionsMessage message => SecurityDefinitionOptionsMessage.encode message
  | .securityStatusMessage message => SecurityStatusMessage.encode message
  | .sequenceNumberResetMessage message => SequenceNumberResetMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 109 := by
  cases message with
  | snapshotStartMessage inner =>
    simp only [encode, SnapshotStartMessage.encode_length]
    omega
  | bookStatusMessage inner =>
    simp only [encode, BookStatusMessage.encode_length]
    omega
  | bookEntryMessage inner =>
    simp only [encode, BookEntryMessage.encode_length]
    omega
  | tickTableDataMessage inner =>
    simp only [encode, TickTableDataMessage.encode_length]
    omega
  | securityDefinitionMessage inner =>
    simp only [encode, SecurityDefinitionMessage.encode_length]
    omega
  | securityDefinitionFuturesMessage inner =>
    simp only [encode, SecurityDefinitionFuturesMessage.encode_length]
    omega
  | securityDefinitionOptionsMessage inner =>
    simp only [encode, SecurityDefinitionOptionsMessage.encode_length]
    omega
  | securityStatusMessage inner =>
    simp only [encode, SecurityStatusMessage.encode_length]
    omega
  | sequenceNumberResetMessage inner =>
    simp only [encode, SequenceNumberResetMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 10 then (SnapshotStartMessage.decode bytes).map fun (message, rest) => (.snapshotStartMessage message, rest)
  else if tag = 11 then (BookStatusMessage.decode bytes).map fun (message, rest) => (.bookStatusMessage message, rest)
  else if tag = 12 then (BookEntryMessage.decode bytes).map fun (message, rest) => (.bookEntryMessage message, rest)
  else if tag = 7 then (TickTableDataMessage.decode bytes).map fun (message, rest) => (.tickTableDataMessage message, rest)
  else if tag = 8 then (SecurityDefinitionMessage.decode bytes).map fun (message, rest) => (.securityDefinitionMessage message, rest)
  else if tag = 30 then (SecurityDefinitionFuturesMessage.decode bytes).map fun (message, rest) => (.securityDefinitionFuturesMessage message, rest)
  else if tag = 32 then (SecurityDefinitionOptionsMessage.decode bytes).map fun (message, rest) => (.securityDefinitionOptionsMessage message, rest)
  else if tag = 9 then (SecurityStatusMessage.decode bytes).map fun (message, rest) => (.securityStatusMessage message, rest)
  else if tag = 29 then (SequenceNumberResetMessage.decode bytes).map fun (message, rest) => (.sequenceNumberResetMessage message, rest)
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
  | snapshotStartMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, SnapshotStartMessage.encode_length]
    omega
  | bookStatusMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, BookStatusMessage.encode_length]
    omega
  | bookEntryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, BookEntryMessage.encode_length]
    omega
  | tickTableDataMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, TickTableDataMessage.encode_length]
    omega
  | securityDefinitionMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, SecurityDefinitionMessage.encode_length]
    omega
  | securityDefinitionFuturesMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, SecurityDefinitionFuturesMessage.encode_length]
    omega
  | securityDefinitionOptionsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, SecurityDefinitionOptionsMessage.encode_length]
    omega
  | securityStatusMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, SecurityStatusMessage.encode_length]
    omega
  | sequenceNumberResetMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, SequenceNumberResetMessage.encode_length]
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

end Omi.AsianextAsianextderivativesSnapshotAmdV13
