import Wire

/-!
# National Stock Exchange of India Ltd Order Entry v6.6

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NseNsecmOrderentryNnftrimmedV66

/-- Sec Info: 12 bytes -/
structure SecInfo where
  symbol : Alpha 10
  series : Alpha 2
  deriving DecidableEq, Repr

namespace SecInfo

def encode (message : SecInfo) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (Alpha.encode message.series)

def decode (bytes : List UInt8) : Option (SecInfo × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 10 bytes
  let (series, bytes) ← Alpha.decode 2 bytes
  pure ({ symbol, series }, bytes)

@[simp] theorem encode_length (message : SecInfo) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : SecInfo) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecInfo) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SecInfo

/-- Order Entry Request Trimmed Message: 136 bytes -/
structure OrderEntryRequestTrimmedMessage where
  transcode : BitVec 16
  traderId : BitVec 32
  secInfo : SecInfo
  accountNumber : Alpha 10
  bookType : BitVec 16
  buySell : BitVec 16
  disclosedVol : BitVec 32
  volume : BitVec 32
  price : BitVec 32
  goodTillDate : BitVec 32
  stOrderFlags : BitVec 16
  branchId : BitVec 16
  userId : BitVec 32
  brokerId : Alpha 5
  suspended : Alpha 1
  settlor : Alpha 12
  proClient : BitVec 16
  nnfField : Alpha 8
  transactionId : BitVec 32
  pan : Alpha 10
  algoId : BitVec 32
  reserved2 : Alpha 2
  reserved32 : Alpha 32
  deriving DecidableEq, Repr

namespace OrderEntryRequestTrimmedMessage

def encode (message : OrderEntryRequestTrimmedMessage) : List UInt8 :=
  encodeUInt 2 message.transcode
    ++ (encodeUInt 4 message.traderId
    ++ (SecInfo.encode message.secInfo
    ++ (Alpha.encode message.accountNumber
    ++ (encodeUInt 2 message.bookType
    ++ (encodeUInt 2 message.buySell
    ++ (encodeUInt 4 message.disclosedVol
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.goodTillDate
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId
    ++ (encodeUInt 4 message.userId
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.suspended
    ++ (Alpha.encode message.settlor
    ++ (encodeUInt 2 message.proClient
    ++ (Alpha.encode message.nnfField
    ++ (encodeUInt 4 message.transactionId
    ++ (Alpha.encode message.pan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.reserved2
    ++ (Alpha.encode message.reserved32))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (OrderEntryRequestTrimmedMessage × List UInt8) := do
  let (transcode, bytes) ← decodeUInt 2 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (secInfo, bytes) ← SecInfo.decode bytes
  let (accountNumber, bytes) ← Alpha.decode 10 bytes
  let (bookType, bytes) ← decodeUInt 2 bytes
  let (buySell, bytes) ← decodeUInt 2 bytes
  let (disclosedVol, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (goodTillDate, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId, bytes) ← decodeUInt 2 bytes
  let (userId, bytes) ← decodeUInt 4 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (suspended, bytes) ← Alpha.decode 1 bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  let (proClient, bytes) ← decodeUInt 2 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (reserved32, bytes) ← Alpha.decode 32 bytes
  pure ({ transcode, traderId, secInfo, accountNumber, bookType, buySell, disclosedVol, volume, price, goodTillDate, stOrderFlags, branchId, userId, brokerId, suspended, settlor, proClient, nnfField, transactionId, pan, algoId, reserved2, reserved32 }, bytes)

@[simp] theorem encode_length (message : OrderEntryRequestTrimmedMessage) : (encode message).length = 136 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, SecInfo.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderEntryRequestTrimmedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderEntryRequestTrimmedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, SecInfo.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderEntryRequestTrimmedMessage

/-- Order Modify Cancel Request Trimmed Message: 180 bytes -/
structure OrderModifyCancelRequestTrimmedMessage where
  transactionCode : BitVec 16
  logTime : BitVec 32
  userId : BitVec 32
  errorCode : BitVec 16
  timeStamp1LongLong8 : BitVec 64
  timeStamp2 : Alpha 1
  modifiedCancelledBy : Alpha 1
  reasonCode : BitVec 16
  secInfo : SecInfo
  orderNumber : Alpha 8
  accountNumber : Alpha 10
  bookType : BitVec 16
  buySell : BitVec 16
  disclosedVol : BitVec 32
  disclosedVolRemaining : BitVec 32
  totalVolRemaining : BitVec 32
  volume : BitVec 32
  volumeFilledToday : BitVec 32
  price : BitVec 32
  entryDateTime : BitVec 32
  lastModified : BitVec 32
  stOrderFlags : BitVec 16
  branchId : BitVec 16
  secondUserId : BitVec 32
  brokerId : Alpha 5
  suspended : Alpha 1
  settlor : Alpha 12
  proClient : BitVec 16
  settlementType : BitVec 16
  nnfField : Alpha 8
  transactionId : BitVec 32
  pan : Alpha 10
  algoId : BitVec 32
  reserved2 : Alpha 2
  lastActivityReference : BitVec 64
  reserved24 : Alpha 24
  deriving DecidableEq, Repr

namespace OrderModifyCancelRequestTrimmedMessage

def encode (message : OrderModifyCancelRequestTrimmedMessage) : List UInt8 :=
  encodeUInt 2 message.transactionCode
    ++ (encodeUInt 4 message.logTime
    ++ (encodeUInt 4 message.userId
    ++ (encodeUInt 2 message.errorCode
    ++ (encodeUInt 8 message.timeStamp1LongLong8
    ++ (Alpha.encode message.timeStamp2
    ++ (Alpha.encode message.modifiedCancelledBy
    ++ (encodeUInt 2 message.reasonCode
    ++ (SecInfo.encode message.secInfo
    ++ (Alpha.encode message.orderNumber
    ++ (Alpha.encode message.accountNumber
    ++ (encodeUInt 2 message.bookType
    ++ (encodeUInt 2 message.buySell
    ++ (encodeUInt 4 message.disclosedVol
    ++ (encodeUInt 4 message.disclosedVolRemaining
    ++ (encodeUInt 4 message.totalVolRemaining
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 4 message.volumeFilledToday
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.entryDateTime
    ++ (encodeUInt 4 message.lastModified
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId
    ++ (encodeUInt 4 message.secondUserId
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.suspended
    ++ (Alpha.encode message.settlor
    ++ (encodeUInt 2 message.proClient
    ++ (encodeUInt 2 message.settlementType
    ++ (Alpha.encode message.nnfField
    ++ (encodeUInt 4 message.transactionId
    ++ (Alpha.encode message.pan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.reserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved24)))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderModifyCancelRequestTrimmedMessage × List UInt8) := do
  let (transactionCode, bytes) ← decodeUInt 2 bytes
  let (logTime, bytes) ← decodeUInt 4 bytes
  let (userId, bytes) ← decodeUInt 4 bytes
  let (errorCode, bytes) ← decodeUInt 2 bytes
  let (timeStamp1LongLong8, bytes) ← decodeUInt 8 bytes
  let (timeStamp2, bytes) ← Alpha.decode 1 bytes
  let (modifiedCancelledBy, bytes) ← Alpha.decode 1 bytes
  let (reasonCode, bytes) ← decodeUInt 2 bytes
  let (secInfo, bytes) ← SecInfo.decode bytes
  let (orderNumber, bytes) ← Alpha.decode 8 bytes
  let (accountNumber, bytes) ← Alpha.decode 10 bytes
  let (bookType, bytes) ← decodeUInt 2 bytes
  let (buySell, bytes) ← decodeUInt 2 bytes
  let (disclosedVol, bytes) ← decodeUInt 4 bytes
  let (disclosedVolRemaining, bytes) ← decodeUInt 4 bytes
  let (totalVolRemaining, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (entryDateTime, bytes) ← decodeUInt 4 bytes
  let (lastModified, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId, bytes) ← decodeUInt 2 bytes
  let (secondUserId, bytes) ← decodeUInt 4 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (suspended, bytes) ← Alpha.decode 1 bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  let (proClient, bytes) ← decodeUInt 2 bytes
  let (settlementType, bytes) ← decodeUInt 2 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved24, bytes) ← Alpha.decode 24 bytes
  pure ({ transactionCode, logTime, userId, errorCode, timeStamp1LongLong8, timeStamp2, modifiedCancelledBy, reasonCode, secInfo, orderNumber, accountNumber, bookType, buySell, disclosedVol, disclosedVolRemaining, totalVolRemaining, volume, volumeFilledToday, price, entryDateTime, lastModified, stOrderFlags, branchId, secondUserId, brokerId, suspended, settlor, proClient, settlementType, nnfField, transactionId, pan, algoId, reserved2, lastActivityReference, reserved24 }, bytes)

@[simp] theorem encode_length (message : OrderModifyCancelRequestTrimmedMessage) : (encode message).length = 180 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, SecInfo.encode_length]

theorem encode_length_pos (message : OrderModifyCancelRequestTrimmedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OrderModifyCancelRequestTrimmedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, SecInfo.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderModifyCancelRequestTrimmedMessage

/-- Order Modify Cancel Response Trimmed Message: 216 bytes -/
structure OrderModifyCancelResponseTrimmedMessage where
  transactionCode : BitVec 16
  logTime : BitVec 32
  userId : BitVec 32
  errorCode : BitVec 16
  timeStamp1LongLong8 : BitVec 64
  timeStamp2 : Alpha 1
  modifiedCancelledBy : Alpha 1
  reasonCode : BitVec 16
  secInfo : SecInfo
  orderNumber : Alpha 8
  accountNumber : Alpha 10
  bookType : BitVec 16
  buySell : BitVec 16
  disclosedVol : BitVec 32
  disclosedVolRemaining : BitVec 32
  totalVolRemaining : BitVec 32
  volume : BitVec 32
  volumeFilledToday : BitVec 32
  price : BitVec 32
  entryDateTime : BitVec 32
  lastModified : BitVec 32
  stOrderFlags : BitVec 16
  branchId : BitVec 16
  secondUserId : BitVec 32
  brokerId : Alpha 5
  suspended : Alpha 1
  settlor : Alpha 12
  proClient : BitVec 16
  settlementType : BitVec 16
  nnfField : Alpha 8
  transactionId : BitVec 32
  timestamp : BitVec 64
  pan : Alpha 10
  algoId : BitVec 32
  reserved2 : Alpha 2
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  deriving DecidableEq, Repr

namespace OrderModifyCancelResponseTrimmedMessage

def encode (message : OrderModifyCancelResponseTrimmedMessage) : List UInt8 :=
  encodeUInt 2 message.transactionCode
    ++ (encodeUInt 4 message.logTime
    ++ (encodeUInt 4 message.userId
    ++ (encodeUInt 2 message.errorCode
    ++ (encodeUInt 8 message.timeStamp1LongLong8
    ++ (Alpha.encode message.timeStamp2
    ++ (Alpha.encode message.modifiedCancelledBy
    ++ (encodeUInt 2 message.reasonCode
    ++ (SecInfo.encode message.secInfo
    ++ (Alpha.encode message.orderNumber
    ++ (Alpha.encode message.accountNumber
    ++ (encodeUInt 2 message.bookType
    ++ (encodeUInt 2 message.buySell
    ++ (encodeUInt 4 message.disclosedVol
    ++ (encodeUInt 4 message.disclosedVolRemaining
    ++ (encodeUInt 4 message.totalVolRemaining
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 4 message.volumeFilledToday
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.entryDateTime
    ++ (encodeUInt 4 message.lastModified
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId
    ++ (encodeUInt 4 message.secondUserId
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.suspended
    ++ (Alpha.encode message.settlor
    ++ (encodeUInt 2 message.proClient
    ++ (encodeUInt 2 message.settlementType
    ++ (Alpha.encode message.nnfField
    ++ (encodeUInt 4 message.transactionId
    ++ (encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.pan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.reserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderModifyCancelResponseTrimmedMessage × List UInt8) := do
  let (transactionCode, bytes) ← decodeUInt 2 bytes
  let (logTime, bytes) ← decodeUInt 4 bytes
  let (userId, bytes) ← decodeUInt 4 bytes
  let (errorCode, bytes) ← decodeUInt 2 bytes
  let (timeStamp1LongLong8, bytes) ← decodeUInt 8 bytes
  let (timeStamp2, bytes) ← Alpha.decode 1 bytes
  let (modifiedCancelledBy, bytes) ← Alpha.decode 1 bytes
  let (reasonCode, bytes) ← decodeUInt 2 bytes
  let (secInfo, bytes) ← SecInfo.decode bytes
  let (orderNumber, bytes) ← Alpha.decode 8 bytes
  let (accountNumber, bytes) ← Alpha.decode 10 bytes
  let (bookType, bytes) ← decodeUInt 2 bytes
  let (buySell, bytes) ← decodeUInt 2 bytes
  let (disclosedVol, bytes) ← decodeUInt 4 bytes
  let (disclosedVolRemaining, bytes) ← decodeUInt 4 bytes
  let (totalVolRemaining, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (entryDateTime, bytes) ← decodeUInt 4 bytes
  let (lastModified, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId, bytes) ← decodeUInt 2 bytes
  let (secondUserId, bytes) ← decodeUInt 4 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (suspended, bytes) ← Alpha.decode 1 bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  let (proClient, bytes) ← decodeUInt 2 bytes
  let (settlementType, bytes) ← decodeUInt 2 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  pure ({ transactionCode, logTime, userId, errorCode, timeStamp1LongLong8, timeStamp2, modifiedCancelledBy, reasonCode, secInfo, orderNumber, accountNumber, bookType, buySell, disclosedVol, disclosedVolRemaining, totalVolRemaining, volume, volumeFilledToday, price, entryDateTime, lastModified, stOrderFlags, branchId, secondUserId, brokerId, suspended, settlor, proClient, settlementType, nnfField, transactionId, timestamp, pan, algoId, reserved2, lastActivityReference, reserved52 }, bytes)

@[simp] theorem encode_length (message : OrderModifyCancelResponseTrimmedMessage) : (encode message).length = 216 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, SecInfo.encode_length]

theorem encode_length_pos (message : OrderModifyCancelResponseTrimmedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OrderModifyCancelResponseTrimmedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, SecInfo.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderModifyCancelResponseTrimmedMessage

/-- Trade Confirmation Trimmed Message: 192 bytes -/
structure TradeConfirmationTrimmedMessage where
  transactionCode : BitVec 16
  logTime : BitVec 32
  userId : BitVec 32
  timestamp : BitVec 64
  timeStamp1Char8 : Alpha 8
  responseOrderNumber : Alpha 8
  timeStamp2 : Alpha 1
  brokerId : Alpha 5
  traderNum : BitVec 32
  buySell : BitVec 16
  accountNum : Alpha 10
  originalVol : BitVec 32
  disclosedVol : BitVec 32
  remainingVol : BitVec 32
  disclosedVolRemaining : BitVec 32
  price : BitVec 32
  stOrderFlags : BitVec 16
  fillNumber : BitVec 32
  fillQty : BitVec 32
  fillPrice : BitVec 32
  volFilledToday : BitVec 32
  activityType : Alpha 2
  activityTime : BitVec 32
  secInfo : SecInfo
  bookType : BitVec 16
  proClient : BitVec 16
  pan : Alpha 10
  algoId : BitVec 32
  reserved2 : Alpha 2
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  deriving DecidableEq, Repr

namespace TradeConfirmationTrimmedMessage

def encode (message : TradeConfirmationTrimmedMessage) : List UInt8 :=
  encodeUInt 2 message.transactionCode
    ++ (encodeUInt 4 message.logTime
    ++ (encodeUInt 4 message.userId
    ++ (encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.timeStamp1Char8
    ++ (Alpha.encode message.responseOrderNumber
    ++ (Alpha.encode message.timeStamp2
    ++ (Alpha.encode message.brokerId
    ++ (encodeUInt 4 message.traderNum
    ++ (encodeUInt 2 message.buySell
    ++ (Alpha.encode message.accountNum
    ++ (encodeUInt 4 message.originalVol
    ++ (encodeUInt 4 message.disclosedVol
    ++ (encodeUInt 4 message.remainingVol
    ++ (encodeUInt 4 message.disclosedVolRemaining
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 4 message.fillNumber
    ++ (encodeUInt 4 message.fillQty
    ++ (encodeUInt 4 message.fillPrice
    ++ (encodeUInt 4 message.volFilledToday
    ++ (Alpha.encode message.activityType
    ++ (encodeUInt 4 message.activityTime
    ++ (SecInfo.encode message.secInfo
    ++ (encodeUInt 2 message.bookType
    ++ (encodeUInt 2 message.proClient
    ++ (Alpha.encode message.pan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.reserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TradeConfirmationTrimmedMessage × List UInt8) := do
  let (transactionCode, bytes) ← decodeUInt 2 bytes
  let (logTime, bytes) ← decodeUInt 4 bytes
  let (userId, bytes) ← decodeUInt 4 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (timeStamp1Char8, bytes) ← Alpha.decode 8 bytes
  let (responseOrderNumber, bytes) ← Alpha.decode 8 bytes
  let (timeStamp2, bytes) ← Alpha.decode 1 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (traderNum, bytes) ← decodeUInt 4 bytes
  let (buySell, bytes) ← decodeUInt 2 bytes
  let (accountNum, bytes) ← Alpha.decode 10 bytes
  let (originalVol, bytes) ← decodeUInt 4 bytes
  let (disclosedVol, bytes) ← decodeUInt 4 bytes
  let (remainingVol, bytes) ← decodeUInt 4 bytes
  let (disclosedVolRemaining, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (fillNumber, bytes) ← decodeUInt 4 bytes
  let (fillQty, bytes) ← decodeUInt 4 bytes
  let (fillPrice, bytes) ← decodeUInt 4 bytes
  let (volFilledToday, bytes) ← decodeUInt 4 bytes
  let (activityType, bytes) ← Alpha.decode 2 bytes
  let (activityTime, bytes) ← decodeUInt 4 bytes
  let (secInfo, bytes) ← SecInfo.decode bytes
  let (bookType, bytes) ← decodeUInt 2 bytes
  let (proClient, bytes) ← decodeUInt 2 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  pure ({ transactionCode, logTime, userId, timestamp, timeStamp1Char8, responseOrderNumber, timeStamp2, brokerId, traderNum, buySell, accountNum, originalVol, disclosedVol, remainingVol, disclosedVolRemaining, price, stOrderFlags, fillNumber, fillQty, fillPrice, volFilledToday, activityType, activityTime, secInfo, bookType, proClient, pan, algoId, reserved2, lastActivityReference, reserved52 }, bytes)

@[simp] theorem encode_length (message : TradeConfirmationTrimmedMessage) : (encode message).length = 192 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, SecInfo.encode_length]

theorem encode_length_pos (message : TradeConfirmationTrimmedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : TradeConfirmationTrimmedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, SecInfo.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeConfirmationTrimmedMessage

/-- Quick Acknowledgement Message: 22 bytes -/
structure QuickAcknowledgementMessage where
  transactionCode : BitVec 16
  traderId : BitVec 32
  timestamp : BitVec 64
  reference : BitVec 32
  errorCode : BitVec 16
  messageLength : BitVec 16
  deriving DecidableEq, Repr

namespace QuickAcknowledgementMessage

def encode (message : QuickAcknowledgementMessage) : List UInt8 :=
  encodeUInt 2 message.transactionCode
    ++ (encodeUInt 4 message.traderId
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.reference
    ++ (encodeUInt 2 message.errorCode
    ++ (encodeUInt 2 message.messageLength)))))

def decode (bytes : List UInt8) : Option (QuickAcknowledgementMessage × List UInt8) := do
  let (transactionCode, bytes) ← decodeUInt 2 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (reference, bytes) ← decodeUInt 4 bytes
  let (errorCode, bytes) ← decodeUInt 2 bytes
  let (messageLength, bytes) ← decodeUInt 2 bytes
  pure ({ transactionCode, traderId, timestamp, reference, errorCode, messageLength }, bytes)

@[simp] theorem encode_length (message : QuickAcknowledgementMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : QuickAcknowledgementMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuickAcknowledgementMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end QuickAcknowledgementMessage

/-- Any Message Payload, selected by Transaction Code -/
inductive MessagePayload where
  | orderEntryRequestTrimmedMessage (message : OrderEntryRequestTrimmedMessage) -- 20000
  | orderEntryRequestTrimmedMessage20400 (message : OrderEntryRequestTrimmedMessage) -- 20400
  | orderModifyCancelRequestTrimmedMessage (message : OrderModifyCancelRequestTrimmedMessage) -- 20040
  | orderModifyCancelRequestTrimmedMessage20070 (message : OrderModifyCancelRequestTrimmedMessage) -- 20070
  | orderModifyCancelRequestTrimmedMessage20402 (message : OrderModifyCancelRequestTrimmedMessage) -- 20402
  | orderModifyCancelRequestTrimmedMessage20404 (message : OrderModifyCancelRequestTrimmedMessage) -- 20404
  | orderModifyCancelResponseTrimmedMessage (message : OrderModifyCancelResponseTrimmedMessage) -- 20012
  | orderModifyCancelResponseTrimmedMessage20042 (message : OrderModifyCancelResponseTrimmedMessage) -- 20042
  | orderModifyCancelResponseTrimmedMessage20072 (message : OrderModifyCancelResponseTrimmedMessage) -- 20072
  | orderModifyCancelResponseTrimmedMessage20073 (message : OrderModifyCancelResponseTrimmedMessage) -- 20073
  | orderModifyCancelResponseTrimmedMessage20074 (message : OrderModifyCancelResponseTrimmedMessage) -- 20074
  | orderModifyCancelResponseTrimmedMessage20075 (message : OrderModifyCancelResponseTrimmedMessage) -- 20075
  | orderModifyCancelResponseTrimmedMessage20231 (message : OrderModifyCancelResponseTrimmedMessage) -- 20231
  | tradeConfirmationTrimmedMessage (message : TradeConfirmationTrimmedMessage) -- 20222
  | quickAcknowledgementMessage (message : QuickAcknowledgementMessage) -- 20401
  | quickAcknowledgementMessage20403 (message : QuickAcknowledgementMessage) -- 20403
  | quickAcknowledgementMessage20405 (message : QuickAcknowledgementMessage) -- 20405
  deriving DecidableEq, Repr

namespace MessagePayload

/-- The Transaction Code each message is sent under -/
def tag : MessagePayload → BitVec 16
  | .orderEntryRequestTrimmedMessage _ => 20000
  | .orderEntryRequestTrimmedMessage20400 _ => 20400
  | .orderModifyCancelRequestTrimmedMessage _ => 20040
  | .orderModifyCancelRequestTrimmedMessage20070 _ => 20070
  | .orderModifyCancelRequestTrimmedMessage20402 _ => 20402
  | .orderModifyCancelRequestTrimmedMessage20404 _ => 20404
  | .orderModifyCancelResponseTrimmedMessage _ => 20012
  | .orderModifyCancelResponseTrimmedMessage20042 _ => 20042
  | .orderModifyCancelResponseTrimmedMessage20072 _ => 20072
  | .orderModifyCancelResponseTrimmedMessage20073 _ => 20073
  | .orderModifyCancelResponseTrimmedMessage20074 _ => 20074
  | .orderModifyCancelResponseTrimmedMessage20075 _ => 20075
  | .orderModifyCancelResponseTrimmedMessage20231 _ => 20231
  | .tradeConfirmationTrimmedMessage _ => 20222
  | .quickAcknowledgementMessage _ => 20401
  | .quickAcknowledgementMessage20403 _ => 20403
  | .quickAcknowledgementMessage20405 _ => 20405

def encode : MessagePayload → List UInt8
  | .orderEntryRequestTrimmedMessage message => OrderEntryRequestTrimmedMessage.encode message
  | .orderEntryRequestTrimmedMessage20400 message => OrderEntryRequestTrimmedMessage.encode message
  | .orderModifyCancelRequestTrimmedMessage message => OrderModifyCancelRequestTrimmedMessage.encode message
  | .orderModifyCancelRequestTrimmedMessage20070 message => OrderModifyCancelRequestTrimmedMessage.encode message
  | .orderModifyCancelRequestTrimmedMessage20402 message => OrderModifyCancelRequestTrimmedMessage.encode message
  | .orderModifyCancelRequestTrimmedMessage20404 message => OrderModifyCancelRequestTrimmedMessage.encode message
  | .orderModifyCancelResponseTrimmedMessage message => OrderModifyCancelResponseTrimmedMessage.encode message
  | .orderModifyCancelResponseTrimmedMessage20042 message => OrderModifyCancelResponseTrimmedMessage.encode message
  | .orderModifyCancelResponseTrimmedMessage20072 message => OrderModifyCancelResponseTrimmedMessage.encode message
  | .orderModifyCancelResponseTrimmedMessage20073 message => OrderModifyCancelResponseTrimmedMessage.encode message
  | .orderModifyCancelResponseTrimmedMessage20074 message => OrderModifyCancelResponseTrimmedMessage.encode message
  | .orderModifyCancelResponseTrimmedMessage20075 message => OrderModifyCancelResponseTrimmedMessage.encode message
  | .orderModifyCancelResponseTrimmedMessage20231 message => OrderModifyCancelResponseTrimmedMessage.encode message
  | .tradeConfirmationTrimmedMessage message => TradeConfirmationTrimmedMessage.encode message
  | .quickAcknowledgementMessage message => QuickAcknowledgementMessage.encode message
  | .quickAcknowledgementMessage20403 message => QuickAcknowledgementMessage.encode message
  | .quickAcknowledgementMessage20405 message => QuickAcknowledgementMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : MessagePayload) : (encode message).length ≤ 216 := by
  cases message with
  | orderEntryRequestTrimmedMessage inner =>
    simp only [encode, OrderEntryRequestTrimmedMessage.encode_length]
    omega
  | orderEntryRequestTrimmedMessage20400 inner =>
    simp only [encode, OrderEntryRequestTrimmedMessage.encode_length]
    omega
  | orderModifyCancelRequestTrimmedMessage inner =>
    simp only [encode, OrderModifyCancelRequestTrimmedMessage.encode_length]
    omega
  | orderModifyCancelRequestTrimmedMessage20070 inner =>
    simp only [encode, OrderModifyCancelRequestTrimmedMessage.encode_length]
    omega
  | orderModifyCancelRequestTrimmedMessage20402 inner =>
    simp only [encode, OrderModifyCancelRequestTrimmedMessage.encode_length]
    omega
  | orderModifyCancelRequestTrimmedMessage20404 inner =>
    simp only [encode, OrderModifyCancelRequestTrimmedMessage.encode_length]
    omega
  | orderModifyCancelResponseTrimmedMessage inner =>
    simp only [encode, OrderModifyCancelResponseTrimmedMessage.encode_length]
    omega
  | orderModifyCancelResponseTrimmedMessage20042 inner =>
    simp only [encode, OrderModifyCancelResponseTrimmedMessage.encode_length]
    omega
  | orderModifyCancelResponseTrimmedMessage20072 inner =>
    simp only [encode, OrderModifyCancelResponseTrimmedMessage.encode_length]
    omega
  | orderModifyCancelResponseTrimmedMessage20073 inner =>
    simp only [encode, OrderModifyCancelResponseTrimmedMessage.encode_length]
    omega
  | orderModifyCancelResponseTrimmedMessage20074 inner =>
    simp only [encode, OrderModifyCancelResponseTrimmedMessage.encode_length]
    omega
  | orderModifyCancelResponseTrimmedMessage20075 inner =>
    simp only [encode, OrderModifyCancelResponseTrimmedMessage.encode_length]
    omega
  | orderModifyCancelResponseTrimmedMessage20231 inner =>
    simp only [encode, OrderModifyCancelResponseTrimmedMessage.encode_length]
    omega
  | tradeConfirmationTrimmedMessage inner =>
    simp only [encode, TradeConfirmationTrimmedMessage.encode_length]
    omega
  | quickAcknowledgementMessage inner =>
    simp only [encode, QuickAcknowledgementMessage.encode_length]
    omega
  | quickAcknowledgementMessage20403 inner =>
    simp only [encode, QuickAcknowledgementMessage.encode_length]
    omega
  | quickAcknowledgementMessage20405 inner =>
    simp only [encode, QuickAcknowledgementMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (MessagePayload × List UInt8) :=
  if tag = 20000 then (OrderEntryRequestTrimmedMessage.decode bytes).map fun (message, rest) => (.orderEntryRequestTrimmedMessage message, rest)
  else if tag = 20400 then (OrderEntryRequestTrimmedMessage.decode bytes).map fun (message, rest) => (.orderEntryRequestTrimmedMessage20400 message, rest)
  else if tag = 20040 then (OrderModifyCancelRequestTrimmedMessage.decode bytes).map fun (message, rest) => (.orderModifyCancelRequestTrimmedMessage message, rest)
  else if tag = 20070 then (OrderModifyCancelRequestTrimmedMessage.decode bytes).map fun (message, rest) => (.orderModifyCancelRequestTrimmedMessage20070 message, rest)
  else if tag = 20402 then (OrderModifyCancelRequestTrimmedMessage.decode bytes).map fun (message, rest) => (.orderModifyCancelRequestTrimmedMessage20402 message, rest)
  else if tag = 20404 then (OrderModifyCancelRequestTrimmedMessage.decode bytes).map fun (message, rest) => (.orderModifyCancelRequestTrimmedMessage20404 message, rest)
  else if tag = 20012 then (OrderModifyCancelResponseTrimmedMessage.decode bytes).map fun (message, rest) => (.orderModifyCancelResponseTrimmedMessage message, rest)
  else if tag = 20042 then (OrderModifyCancelResponseTrimmedMessage.decode bytes).map fun (message, rest) => (.orderModifyCancelResponseTrimmedMessage20042 message, rest)
  else if tag = 20072 then (OrderModifyCancelResponseTrimmedMessage.decode bytes).map fun (message, rest) => (.orderModifyCancelResponseTrimmedMessage20072 message, rest)
  else if tag = 20073 then (OrderModifyCancelResponseTrimmedMessage.decode bytes).map fun (message, rest) => (.orderModifyCancelResponseTrimmedMessage20073 message, rest)
  else if tag = 20074 then (OrderModifyCancelResponseTrimmedMessage.decode bytes).map fun (message, rest) => (.orderModifyCancelResponseTrimmedMessage20074 message, rest)
  else if tag = 20075 then (OrderModifyCancelResponseTrimmedMessage.decode bytes).map fun (message, rest) => (.orderModifyCancelResponseTrimmedMessage20075 message, rest)
  else if tag = 20231 then (OrderModifyCancelResponseTrimmedMessage.decode bytes).map fun (message, rest) => (.orderModifyCancelResponseTrimmedMessage20231 message, rest)
  else if tag = 20222 then (TradeConfirmationTrimmedMessage.decode bytes).map fun (message, rest) => (.tradeConfirmationTrimmedMessage message, rest)
  else if tag = 20401 then (QuickAcknowledgementMessage.decode bytes).map fun (message, rest) => (.quickAcknowledgementMessage message, rest)
  else if tag = 20403 then (QuickAcknowledgementMessage.decode bytes).map fun (message, rest) => (.quickAcknowledgementMessage20403 message, rest)
  else if tag = 20405 then (QuickAcknowledgementMessage.decode bytes).map fun (message, rest) => (.quickAcknowledgementMessage20405 message, rest)
  else none

@[simp] theorem decode_encode (message : MessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end MessagePayload

/-- Message -/
structure Message where
  messagePayload : MessagePayload
  deriving DecidableEq, Repr

namespace Message

def encode (message : Message) : List UInt8 :=
  encodeUInt 2 (MessagePayload.tag message.messagePayload)
    ++ (MessagePayload.encode message.messagePayload)

def decode (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (transactionCode, bytes) ← decodeUInt 2 bytes
  let (messagePayload, bytes) ← MessagePayload.decode transactionCode bytes
  pure ({ messagePayload }, bytes)

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Message) : (encode message).length ≤ 218 := by
  unfold encode
  cases message.messagePayload with
  | orderEntryRequestTrimmedMessage inner =>
    simp only [MessagePayload.encode, List.length_append, encodeUInt_length, OrderEntryRequestTrimmedMessage.encode_length]
    omega
  | orderEntryRequestTrimmedMessage20400 inner =>
    simp only [MessagePayload.encode, List.length_append, encodeUInt_length, OrderEntryRequestTrimmedMessage.encode_length]
    omega
  | orderModifyCancelRequestTrimmedMessage inner =>
    simp only [MessagePayload.encode, List.length_append, encodeUInt_length, OrderModifyCancelRequestTrimmedMessage.encode_length]
    omega
  | orderModifyCancelRequestTrimmedMessage20070 inner =>
    simp only [MessagePayload.encode, List.length_append, encodeUInt_length, OrderModifyCancelRequestTrimmedMessage.encode_length]
    omega
  | orderModifyCancelRequestTrimmedMessage20402 inner =>
    simp only [MessagePayload.encode, List.length_append, encodeUInt_length, OrderModifyCancelRequestTrimmedMessage.encode_length]
    omega
  | orderModifyCancelRequestTrimmedMessage20404 inner =>
    simp only [MessagePayload.encode, List.length_append, encodeUInt_length, OrderModifyCancelRequestTrimmedMessage.encode_length]
    omega
  | orderModifyCancelResponseTrimmedMessage inner =>
    simp only [MessagePayload.encode, List.length_append, encodeUInt_length, OrderModifyCancelResponseTrimmedMessage.encode_length]
    omega
  | orderModifyCancelResponseTrimmedMessage20042 inner =>
    simp only [MessagePayload.encode, List.length_append, encodeUInt_length, OrderModifyCancelResponseTrimmedMessage.encode_length]
    omega
  | orderModifyCancelResponseTrimmedMessage20072 inner =>
    simp only [MessagePayload.encode, List.length_append, encodeUInt_length, OrderModifyCancelResponseTrimmedMessage.encode_length]
    omega
  | orderModifyCancelResponseTrimmedMessage20073 inner =>
    simp only [MessagePayload.encode, List.length_append, encodeUInt_length, OrderModifyCancelResponseTrimmedMessage.encode_length]
    omega
  | orderModifyCancelResponseTrimmedMessage20074 inner =>
    simp only [MessagePayload.encode, List.length_append, encodeUInt_length, OrderModifyCancelResponseTrimmedMessage.encode_length]
    omega
  | orderModifyCancelResponseTrimmedMessage20075 inner =>
    simp only [MessagePayload.encode, List.length_append, encodeUInt_length, OrderModifyCancelResponseTrimmedMessage.encode_length]
    omega
  | orderModifyCancelResponseTrimmedMessage20231 inner =>
    simp only [MessagePayload.encode, List.length_append, encodeUInt_length, OrderModifyCancelResponseTrimmedMessage.encode_length]
    omega
  | tradeConfirmationTrimmedMessage inner =>
    simp only [MessagePayload.encode, List.length_append, encodeUInt_length, TradeConfirmationTrimmedMessage.encode_length]
    omega
  | quickAcknowledgementMessage inner =>
    simp only [MessagePayload.encode, List.length_append, encodeUInt_length, QuickAcknowledgementMessage.encode_length]
    omega
  | quickAcknowledgementMessage20403 inner =>
    simp only [MessagePayload.encode, List.length_append, encodeUInt_length, QuickAcknowledgementMessage.encode_length]
    omega
  | quickAcknowledgementMessage20405 inner =>
    simp only [MessagePayload.encode, List.length_append, encodeUInt_length, QuickAcknowledgementMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [MessagePayload.decode_encode, some_bind]
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

end Omi.NseNsecmOrderentryNnftrimmedV66
