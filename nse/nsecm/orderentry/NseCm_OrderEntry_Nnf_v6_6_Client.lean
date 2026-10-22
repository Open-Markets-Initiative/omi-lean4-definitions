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

namespace Omi.NseNsecmOrderentryNnfV66Client

/-- Branch Limit: 32 bytes -/
structure BranchLimit where
  branchBuyValueLimit : Alpha 8
  reserved8 : Alpha 8
  branchSellValueLimit : Alpha 8
  secondReserved8 : Alpha 8
  deriving DecidableEq, Repr

namespace BranchLimit

def encode (message : BranchLimit) : List UInt8 :=
  Alpha.encode message.branchBuyValueLimit
    ++ (Alpha.encode message.reserved8
    ++ (Alpha.encode message.branchSellValueLimit
    ++ (Alpha.encode message.secondReserved8)))

def decode (bytes : List UInt8) : Option (BranchLimit × List UInt8) := do
  let (branchBuyValueLimit, bytes) ← Alpha.decode 8 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  let (branchSellValueLimit, bytes) ← Alpha.decode 8 bytes
  let (secondReserved8, bytes) ← Alpha.decode 8 bytes
  pure ({ branchBuyValueLimit, reserved8, branchSellValueLimit, secondReserved8 }, bytes)

@[simp] theorem encode_length (message : BranchLimit) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : BranchLimit) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BranchLimit) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BranchLimit

/-- Branch Order Value Limit Update In Message: 64 bytes -/
structure BranchOrderValueLimitUpdateInMessage where
  brokerId : Alpha 5
  reserved25 : Alpha 25
  branch : BitVec 16
  branchLimit : BranchLimit
  deriving DecidableEq, Repr

namespace BranchOrderValueLimitUpdateInMessage

def encode (message : BranchOrderValueLimitUpdateInMessage) : List UInt8 :=
  Alpha.encode message.brokerId
    ++ (Alpha.encode message.reserved25
    ++ (encodeUInt 2 message.branch
    ++ (BranchLimit.encode message.branchLimit)))

def decode (bytes : List UInt8) : Option (BranchOrderValueLimitUpdateInMessage × List UInt8) := do
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (reserved25, bytes) ← Alpha.decode 25 bytes
  let (branch, bytes) ← decodeUInt 2 bytes
  let (branchLimit, bytes) ← BranchLimit.decode bytes
  pure ({ brokerId, reserved25, branch, branchLimit }, bytes)

@[simp] theorem encode_length (message : BranchOrderValueLimitUpdateInMessage) : (encode message).length = 64 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, BranchLimit.encode_length]

theorem encode_length_pos (message : BranchOrderValueLimitUpdateInMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BranchOrderValueLimitUpdateInMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [BranchLimit.decode_encode, some_bind]
  rfl

end BranchOrderValueLimitUpdateInMessage

/-- Cancel On Logout Status Request Message: 12 bytes -/
structure CancelOnLogoutStatusRequestMessage where
  userId : BitVec 32
  coloUserBit : Alpha 1
  reserved7 : Alpha 7
  deriving DecidableEq, Repr

namespace CancelOnLogoutStatusRequestMessage

def encode (message : CancelOnLogoutStatusRequestMessage) : List UInt8 :=
  encodeUInt 4 message.userId
    ++ (Alpha.encode message.coloUserBit
    ++ (Alpha.encode message.reserved7))

def decode (bytes : List UInt8) : Option (CancelOnLogoutStatusRequestMessage × List UInt8) := do
  let (userId, bytes) ← decodeUInt 4 bytes
  let (coloUserBit, bytes) ← Alpha.decode 1 bytes
  let (reserved7, bytes) ← Alpha.decode 7 bytes
  pure ({ userId, coloUserBit, reserved7 }, bytes)

@[simp] theorem encode_length (message : CancelOnLogoutStatusRequestMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : CancelOnLogoutStatusRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CancelOnLogoutStatusRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end CancelOnLogoutStatusRequestMessage

/-- Message Download Request Message: 8 bytes -/
structure MessageDownloadRequestMessage where
  sequenceNumber : Alpha 8
  deriving DecidableEq, Repr

namespace MessageDownloadRequestMessage

def encode (message : MessageDownloadRequestMessage) : List UInt8 :=
  Alpha.encode message.sequenceNumber

def decode (bytes : List UInt8) : Option (MessageDownloadRequestMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ sequenceNumber }, bytes)

@[simp] theorem encode_length (message : MessageDownloadRequestMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : MessageDownloadRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MessageDownloadRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end MessageDownloadRequestMessage

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

/-- Auction Inquiry Request Message: 16 bytes -/
structure AuctionInquiryRequestMessage where
  secInfo : SecInfo
  auctionNo : BitVec 16
  pageIndicator : Alpha 1
  filler : Alpha 1
  deriving DecidableEq, Repr

namespace AuctionInquiryRequestMessage

def encode (message : AuctionInquiryRequestMessage) : List UInt8 :=
  SecInfo.encode message.secInfo
    ++ (encodeUInt 2 message.auctionNo
    ++ (Alpha.encode message.pageIndicator
    ++ (Alpha.encode message.filler)))

def decode (bytes : List UInt8) : Option (AuctionInquiryRequestMessage × List UInt8) := do
  let (secInfo, bytes) ← SecInfo.decode bytes
  let (auctionNo, bytes) ← decodeUInt 2 bytes
  let (pageIndicator, bytes) ← Alpha.decode 1 bytes
  let (filler, bytes) ← Alpha.decode 1 bytes
  pure ({ secInfo, auctionNo, pageIndicator, filler }, bytes)

@[simp] theorem encode_length (message : AuctionInquiryRequestMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, SecInfo.encode_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : AuctionInquiryRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AuctionInquiryRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, SecInfo.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end AuctionInquiryRequestMessage

/-- Box Sign Off Message: 2 bytes -/
structure BoxSignOffMessage where
  boxId : BitVec 16
  deriving DecidableEq, Repr

namespace BoxSignOffMessage

def encode (message : BoxSignOffMessage) : List UInt8 :=
  encodeUInt 2 message.boxId

def decode (bytes : List UInt8) : Option (BoxSignOffMessage × List UInt8) := do
  let (boxId, bytes) ← decodeUInt 2 bytes
  pure ({ boxId }, bytes)

@[simp] theorem encode_length (message : BoxSignOffMessage) : (encode message).length = 2 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : BoxSignOffMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BoxSignOffMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end BoxSignOffMessage

/-- Box Sign On Request Message: 20 bytes -/
structure BoxSignOnRequestMessage where
  boxId : BitVec 16
  brokerId : Alpha 5
  reserved5 : Alpha 5
  sessionKey : Alpha 8
  deriving DecidableEq, Repr

namespace BoxSignOnRequestMessage

def encode (message : BoxSignOnRequestMessage) : List UInt8 :=
  encodeUInt 2 message.boxId
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.reserved5
    ++ (Alpha.encode message.sessionKey)))

def decode (bytes : List UInt8) : Option (BoxSignOnRequestMessage × List UInt8) := do
  let (boxId, bytes) ← decodeUInt 2 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (reserved5, bytes) ← Alpha.decode 5 bytes
  let (sessionKey, bytes) ← Alpha.decode 8 bytes
  pure ({ boxId, brokerId, reserved5, sessionKey }, bytes)

@[simp] theorem encode_length (message : BoxSignOnRequestMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : BoxSignOnRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BoxSignOnRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BoxSignOnRequestMessage

/-- Gateway Router Request Message: 8 bytes -/
structure GatewayRouterRequestMessage where
  boxId : BitVec 16
  brokerId : Alpha 5
  filler : Alpha 1
  deriving DecidableEq, Repr

namespace GatewayRouterRequestMessage

def encode (message : GatewayRouterRequestMessage) : List UInt8 :=
  encodeUInt 2 message.boxId
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.filler))

def decode (bytes : List UInt8) : Option (GatewayRouterRequestMessage × List UInt8) := do
  let (boxId, bytes) ← decodeUInt 2 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (filler, bytes) ← Alpha.decode 1 bytes
  pure ({ boxId, brokerId, filler }, bytes)

@[simp] theorem encode_length (message : GatewayRouterRequestMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : GatewayRouterRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : GatewayRouterRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end GatewayRouterRequestMessage

/-- Order Entry In Message: 250 bytes -/
structure OrderEntryInMessage where
  participantType : Alpha 1
  reserved1 : Alpha 1
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  modCxlBy : Alpha 1
  filler9 : Alpha 1
  reasonCode : BitVec 16
  reserved4 : Alpha 4
  secInfo : SecInfo
  auctionNumber : BitVec 16
  opBrokerId : Alpha 5
  suspended : Alpha 1
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
  triggerPrice : BitVec 32
  goodTillDate : BitVec 32
  entryDateTime : BitVec 32
  minFillAon : BitVec 32
  lastModified : BitVec 32
  stOrderFlags : BitVec 16
  branchId : BitVec 16
  traderId : BitVec 32
  brokerId : Alpha 5
  oeRemarks : Alpha 25
  settlor : Alpha 12
  proClient : BitVec 16
  settlementType : BitVec 16
  nnfField : Alpha 8
  execTimeStamp : Alpha 8
  secondReserved4 : Alpha 4
  pan : Alpha 10
  algoId : BitVec 32
  reserved2 : Alpha 2
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  deriving DecidableEq, Repr

namespace OrderEntryInMessage

def encode (message : OrderEntryInMessage) : List UInt8 :=
  Alpha.encode message.participantType
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (Alpha.encode message.modCxlBy
    ++ (Alpha.encode message.filler9
    ++ (encodeUInt 2 message.reasonCode
    ++ (Alpha.encode message.reserved4
    ++ (SecInfo.encode message.secInfo
    ++ (encodeUInt 2 message.auctionNumber
    ++ (Alpha.encode message.opBrokerId
    ++ (Alpha.encode message.suspended
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
    ++ (encodeUInt 4 message.triggerPrice
    ++ (encodeUInt 4 message.goodTillDate
    ++ (encodeUInt 4 message.entryDateTime
    ++ (encodeUInt 4 message.minFillAon
    ++ (encodeUInt 4 message.lastModified
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId
    ++ (encodeUInt 4 message.traderId
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.oeRemarks
    ++ (Alpha.encode message.settlor
    ++ (encodeUInt 2 message.proClient
    ++ (encodeUInt 2 message.settlementType
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.execTimeStamp
    ++ (Alpha.encode message.secondReserved4
    ++ (Alpha.encode message.pan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.reserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderEntryInMessage × List UInt8) := do
  let (participantType, bytes) ← Alpha.decode 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (modCxlBy, bytes) ← Alpha.decode 1 bytes
  let (filler9, bytes) ← Alpha.decode 1 bytes
  let (reasonCode, bytes) ← decodeUInt 2 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (secInfo, bytes) ← SecInfo.decode bytes
  let (auctionNumber, bytes) ← decodeUInt 2 bytes
  let (opBrokerId, bytes) ← Alpha.decode 5 bytes
  let (suspended, bytes) ← Alpha.decode 1 bytes
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
  let (triggerPrice, bytes) ← decodeUInt 4 bytes
  let (goodTillDate, bytes) ← decodeUInt 4 bytes
  let (entryDateTime, bytes) ← decodeUInt 4 bytes
  let (minFillAon, bytes) ← decodeUInt 4 bytes
  let (lastModified, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId, bytes) ← decodeUInt 2 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (oeRemarks, bytes) ← Alpha.decode 25 bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  let (proClient, bytes) ← decodeUInt 2 bytes
  let (settlementType, bytes) ← decodeUInt 2 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (execTimeStamp, bytes) ← Alpha.decode 8 bytes
  let (secondReserved4, bytes) ← Alpha.decode 4 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  pure ({ participantType, reserved1, competitorPeriod, solicitorPeriod, modCxlBy, filler9, reasonCode, reserved4, secInfo, auctionNumber, opBrokerId, suspended, orderNumber, accountNumber, bookType, buySell, disclosedVol, disclosedVolRemaining, totalVolRemaining, volume, volumeFilledToday, price, triggerPrice, goodTillDate, entryDateTime, minFillAon, lastModified, stOrderFlags, branchId, traderId, brokerId, oeRemarks, settlor, proClient, settlementType, nnfField, execTimeStamp, secondReserved4, pan, algoId, reserved2, lastActivityReference, reserved52 }, bytes)

@[simp] theorem encode_length (message : OrderEntryInMessage) : (encode message).length = 250 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, SecInfo.encode_length]

theorem encode_length_pos (message : OrderEntryInMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OrderEntryInMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecInfo.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderEntryInMessage

/-- Order Limit Update In Message: 28 bytes -/
structure OrderLimitUpdateInMessage where
  brokerId : Alpha 5
  reserved1 : Alpha 1
  userId : BitVec 32
  orderQtyLimit : Alpha 8
  orderValLimit : Alpha 8
  reserved2 : Alpha 2
  deriving DecidableEq, Repr

namespace OrderLimitUpdateInMessage

def encode (message : OrderLimitUpdateInMessage) : List UInt8 :=
  Alpha.encode message.brokerId
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 4 message.userId
    ++ (Alpha.encode message.orderQtyLimit
    ++ (Alpha.encode message.orderValLimit
    ++ (Alpha.encode message.reserved2)))))

def decode (bytes : List UInt8) : Option (OrderLimitUpdateInMessage × List UInt8) := do
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (userId, bytes) ← decodeUInt 4 bytes
  let (orderQtyLimit, bytes) ← Alpha.decode 8 bytes
  let (orderValLimit, bytes) ← Alpha.decode 8 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  pure ({ brokerId, reserved1, userId, orderQtyLimit, orderValLimit, reserved2 }, bytes)

@[simp] theorem encode_length (message : OrderLimitUpdateInMessage) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : OrderLimitUpdateInMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderLimitUpdateInMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderLimitUpdateInMessage

/-- Password Reset In Message: 18 bytes -/
structure PasswordResetInMessage where
  userId : BitVec 32
  reserved14 : Alpha 14
  deriving DecidableEq, Repr

namespace PasswordResetInMessage

def encode (message : PasswordResetInMessage) : List UInt8 :=
  encodeUInt 4 message.userId
    ++ (Alpha.encode message.reserved14)

def decode (bytes : List UInt8) : Option (PasswordResetInMessage × List UInt8) := do
  let (userId, bytes) ← decodeUInt 4 bytes
  let (reserved14, bytes) ← Alpha.decode 14 bytes
  pure ({ userId, reserved14 }, bytes)

@[simp] theorem encode_length (message : PasswordResetInMessage) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : PasswordResetInMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PasswordResetInMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end PasswordResetInMessage

/-- Sign On Request In Message: 236 bytes -/
structure SignOnRequestInMessage where
  userId : BitVec 32
  reserved8 : Alpha 8
  password : Alpha 8
  secondReserved8 : Alpha 8
  newPassword : Alpha 8
  traderName : Alpha 26
  lastPasswordChangeDateTime : BitVec 32
  brokerId : Alpha 5
  reserved1 : Alpha 1
  branchId : BitVec 16
  versionNumber : BitVec 32
  reserved56 : Alpha 56
  userType : BitVec 16
  sequenceNumber : Alpha 8
  workstationNumber : Alpha 14
  brokerStatus : Alpha 1
  showIndex : Alpha 1
  brokerEligibilityPerMarket : BitVec 16
  brokerName : Alpha 26
  reserved16 : Alpha 16
  secondReserved16 : Alpha 16
  thirdReserved16 : Alpha 16
  deriving DecidableEq, Repr

namespace SignOnRequestInMessage

def encode (message : SignOnRequestInMessage) : List UInt8 :=
  encodeUInt 4 message.userId
    ++ (Alpha.encode message.reserved8
    ++ (Alpha.encode message.password
    ++ (Alpha.encode message.secondReserved8
    ++ (Alpha.encode message.newPassword
    ++ (Alpha.encode message.traderName
    ++ (encodeUInt 4 message.lastPasswordChangeDateTime
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.branchId
    ++ (encodeUInt 4 message.versionNumber
    ++ (Alpha.encode message.reserved56
    ++ (encodeUInt 2 message.userType
    ++ (Alpha.encode message.sequenceNumber
    ++ (Alpha.encode message.workstationNumber
    ++ (Alpha.encode message.brokerStatus
    ++ (Alpha.encode message.showIndex
    ++ (encodeUInt 2 message.brokerEligibilityPerMarket
    ++ (Alpha.encode message.brokerName
    ++ (Alpha.encode message.reserved16
    ++ (Alpha.encode message.secondReserved16
    ++ (Alpha.encode message.thirdReserved16)))))))))))))))))))))

def decode (bytes : List UInt8) : Option (SignOnRequestInMessage × List UInt8) := do
  let (userId, bytes) ← decodeUInt 4 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  let (password, bytes) ← Alpha.decode 8 bytes
  let (secondReserved8, bytes) ← Alpha.decode 8 bytes
  let (newPassword, bytes) ← Alpha.decode 8 bytes
  let (traderName, bytes) ← Alpha.decode 26 bytes
  let (lastPasswordChangeDateTime, bytes) ← decodeUInt 4 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (branchId, bytes) ← decodeUInt 2 bytes
  let (versionNumber, bytes) ← decodeUInt 4 bytes
  let (reserved56, bytes) ← Alpha.decode 56 bytes
  let (userType, bytes) ← decodeUInt 2 bytes
  let (sequenceNumber, bytes) ← Alpha.decode 8 bytes
  let (workstationNumber, bytes) ← Alpha.decode 14 bytes
  let (brokerStatus, bytes) ← Alpha.decode 1 bytes
  let (showIndex, bytes) ← Alpha.decode 1 bytes
  let (brokerEligibilityPerMarket, bytes) ← decodeUInt 2 bytes
  let (brokerName, bytes) ← Alpha.decode 26 bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  let (secondReserved16, bytes) ← Alpha.decode 16 bytes
  let (thirdReserved16, bytes) ← Alpha.decode 16 bytes
  pure ({ userId, reserved8, password, secondReserved8, newPassword, traderName, lastPasswordChangeDateTime, brokerId, reserved1, branchId, versionNumber, reserved56, userType, sequenceNumber, workstationNumber, brokerStatus, showIndex, brokerEligibilityPerMarket, brokerName, reserved16, secondReserved16, thirdReserved16 }, bytes)

@[simp] theorem encode_length (message : SignOnRequestInMessage) : (encode message).length = 236 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : SignOnRequestInMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SignOnRequestInMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SignOnRequestInMessage

/-- Trade Inquiry In Message: 170 bytes -/
structure TradeInquiryInMessage where
  secInfo : SecInfo
  fillNumber : BitVec 32
  fillQty : BitVec 32
  fillPrice : BitVec 32
  marketType : BitVec 16
  newVolume : BitVec 32
  reserved24 : Alpha 24
  buyBrokerId : Alpha 5
  sellBrokerId : Alpha 5
  traderId : BitVec 32
  requestedBy : BitVec 16
  buyAccountNumber : Alpha 10
  sellAccountNumber : Alpha 10
  buyPan : Alpha 10
  sellPan : Alpha 10
  reserved60 : Alpha 60
  deriving DecidableEq, Repr

namespace TradeInquiryInMessage

def encode (message : TradeInquiryInMessage) : List UInt8 :=
  SecInfo.encode message.secInfo
    ++ (encodeUInt 4 message.fillNumber
    ++ (encodeUInt 4 message.fillQty
    ++ (encodeUInt 4 message.fillPrice
    ++ (encodeUInt 2 message.marketType
    ++ (encodeUInt 4 message.newVolume
    ++ (Alpha.encode message.reserved24
    ++ (Alpha.encode message.buyBrokerId
    ++ (Alpha.encode message.sellBrokerId
    ++ (encodeUInt 4 message.traderId
    ++ (encodeUInt 2 message.requestedBy
    ++ (Alpha.encode message.buyAccountNumber
    ++ (Alpha.encode message.sellAccountNumber
    ++ (Alpha.encode message.buyPan
    ++ (Alpha.encode message.sellPan
    ++ (Alpha.encode message.reserved60)))))))))))))))

def decode (bytes : List UInt8) : Option (TradeInquiryInMessage × List UInt8) := do
  let (secInfo, bytes) ← SecInfo.decode bytes
  let (fillNumber, bytes) ← decodeUInt 4 bytes
  let (fillQty, bytes) ← decodeUInt 4 bytes
  let (fillPrice, bytes) ← decodeUInt 4 bytes
  let (marketType, bytes) ← decodeUInt 2 bytes
  let (newVolume, bytes) ← decodeUInt 4 bytes
  let (reserved24, bytes) ← Alpha.decode 24 bytes
  let (buyBrokerId, bytes) ← Alpha.decode 5 bytes
  let (sellBrokerId, bytes) ← Alpha.decode 5 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (requestedBy, bytes) ← decodeUInt 2 bytes
  let (buyAccountNumber, bytes) ← Alpha.decode 10 bytes
  let (sellAccountNumber, bytes) ← Alpha.decode 10 bytes
  let (buyPan, bytes) ← Alpha.decode 10 bytes
  let (sellPan, bytes) ← Alpha.decode 10 bytes
  let (reserved60, bytes) ← Alpha.decode 60 bytes
  pure ({ secInfo, fillNumber, fillQty, fillPrice, marketType, newVolume, reserved24, buyBrokerId, sellBrokerId, traderId, requestedBy, buyAccountNumber, sellAccountNumber, buyPan, sellPan, reserved60 }, bytes)

@[simp] theorem encode_length (message : TradeInquiryInMessage) : (encode message).length = 170 := by
  unfold encode
  simp only [List.length_append, SecInfo.encode_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : TradeInquiryInMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeInquiryInMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, SecInfo.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeInquiryInMessage

/-- Update Local Database Request Message: 22 bytes -/
structure UpdateLocalDatabaseRequestMessage where
  lastUpdateSecurityTime : BitVec 32
  lastUpdateParticipantTime : BitVec 32
  requestForOpenOrders : Alpha 1
  reserved1 : Alpha 1
  normalMarketStatus : BitVec 16
  oddLotMarketStatus : BitVec 16
  spotMarketStatus : BitVec 16
  auctionMarketStatus : BitVec 16
  callAuction1MarketStatus : BitVec 16
  callAuction2MarketStatus : BitVec 16
  deriving DecidableEq, Repr

namespace UpdateLocalDatabaseRequestMessage

def encode (message : UpdateLocalDatabaseRequestMessage) : List UInt8 :=
  encodeUInt 4 message.lastUpdateSecurityTime
    ++ (encodeUInt 4 message.lastUpdateParticipantTime
    ++ (Alpha.encode message.requestForOpenOrders
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.normalMarketStatus
    ++ (encodeUInt 2 message.oddLotMarketStatus
    ++ (encodeUInt 2 message.spotMarketStatus
    ++ (encodeUInt 2 message.auctionMarketStatus
    ++ (encodeUInt 2 message.callAuction1MarketStatus
    ++ (encodeUInt 2 message.callAuction2MarketStatus)))))))))

def decode (bytes : List UInt8) : Option (UpdateLocalDatabaseRequestMessage × List UInt8) := do
  let (lastUpdateSecurityTime, bytes) ← decodeUInt 4 bytes
  let (lastUpdateParticipantTime, bytes) ← decodeUInt 4 bytes
  let (requestForOpenOrders, bytes) ← Alpha.decode 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (normalMarketStatus, bytes) ← decodeUInt 2 bytes
  let (oddLotMarketStatus, bytes) ← decodeUInt 2 bytes
  let (spotMarketStatus, bytes) ← decodeUInt 2 bytes
  let (auctionMarketStatus, bytes) ← decodeUInt 2 bytes
  let (callAuction1MarketStatus, bytes) ← decodeUInt 2 bytes
  let (callAuction2MarketStatus, bytes) ← decodeUInt 2 bytes
  pure ({ lastUpdateSecurityTime, lastUpdateParticipantTime, requestForOpenOrders, reserved1, normalMarketStatus, oddLotMarketStatus, spotMarketStatus, auctionMarketStatus, callAuction1MarketStatus, callAuction2MarketStatus }, bytes)

@[simp] theorem encode_length (message : UpdateLocalDatabaseRequestMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : UpdateLocalDatabaseRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UpdateLocalDatabaseRequestMessage) (rest : List UInt8) :
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

end UpdateLocalDatabaseRequestMessage

/-- Trade Modification Cancellation Status Request Message: 12 bytes -/
structure TradeModificationCancellationStatusRequestMessage where
  userId : BitVec 32
  trdModCxlBit : Alpha 1
  reserved7 : Alpha 7
  deriving DecidableEq, Repr

namespace TradeModificationCancellationStatusRequestMessage

def encode (message : TradeModificationCancellationStatusRequestMessage) : List UInt8 :=
  encodeUInt 4 message.userId
    ++ (Alpha.encode message.trdModCxlBit
    ++ (Alpha.encode message.reserved7))

def decode (bytes : List UInt8) : Option (TradeModificationCancellationStatusRequestMessage × List UInt8) := do
  let (userId, bytes) ← decodeUInt 4 bytes
  let (trdModCxlBit, bytes) ← Alpha.decode 1 bytes
  let (reserved7, bytes) ← Alpha.decode 7 bytes
  pure ({ userId, trdModCxlBit, reserved7 }, bytes)

@[simp] theorem encode_length (message : TradeModificationCancellationStatusRequestMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : TradeModificationCancellationStatusRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeModificationCancellationStatusRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeModificationCancellationStatusRequestMessage

/-- User Unlock Request Message: 28 bytes -/
structure UserUnlockRequestMessage where
  userId : BitVec 32
  reserved24 : Alpha 24
  deriving DecidableEq, Repr

namespace UserUnlockRequestMessage

def encode (message : UserUnlockRequestMessage) : List UInt8 :=
  encodeUInt 4 message.userId
    ++ (Alpha.encode message.reserved24)

def decode (bytes : List UInt8) : Option (UserUnlockRequestMessage × List UInt8) := do
  let (userId, bytes) ← decodeUInt 4 bytes
  let (reserved24, bytes) ← Alpha.decode 24 bytes
  pure ({ userId, reserved24 }, bytes)

@[simp] theorem encode_length (message : UserUnlockRequestMessage) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : UserUnlockRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UserUnlockRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end UserUnlockRequestMessage

/-- User Limits: 64 bytes -/
structure UserLimits where
  reserved16 : Alpha 16
  userOrderBuyValueLimit : Alpha 8
  reserved24 : Alpha 24
  userOrderSellValueLimit : Alpha 8
  reserved8 : Alpha 8
  deriving DecidableEq, Repr

namespace UserLimits

def encode (message : UserLimits) : List UInt8 :=
  Alpha.encode message.reserved16
    ++ (Alpha.encode message.userOrderBuyValueLimit
    ++ (Alpha.encode message.reserved24
    ++ (Alpha.encode message.userOrderSellValueLimit
    ++ (Alpha.encode message.reserved8))))

def decode (bytes : List UInt8) : Option (UserLimits × List UInt8) := do
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  let (userOrderBuyValueLimit, bytes) ← Alpha.decode 8 bytes
  let (reserved24, bytes) ← Alpha.decode 24 bytes
  let (userOrderSellValueLimit, bytes) ← Alpha.decode 8 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  pure ({ reserved16, userOrderBuyValueLimit, reserved24, userOrderSellValueLimit, reserved8 }, bytes)

@[simp] theorem encode_length (message : UserLimits) : (encode message).length = 64 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : UserLimits) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UserLimits) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end UserLimits

/-- User Order Value Limit Update In Message: 102 bytes -/
structure UserOrderValueLimitUpdateInMessage where
  brokerId : Alpha 5
  reserved1 : Alpha 1
  branch : BitVec 16
  reserved26 : Alpha 26
  userId : BitVec 32
  userLimits : UserLimits
  deriving DecidableEq, Repr

namespace UserOrderValueLimitUpdateInMessage

def encode (message : UserOrderValueLimitUpdateInMessage) : List UInt8 :=
  Alpha.encode message.brokerId
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.branch
    ++ (Alpha.encode message.reserved26
    ++ (encodeUInt 4 message.userId
    ++ (UserLimits.encode message.userLimits)))))

def decode (bytes : List UInt8) : Option (UserOrderValueLimitUpdateInMessage × List UInt8) := do
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (branch, bytes) ← decodeUInt 2 bytes
  let (reserved26, bytes) ← Alpha.decode 26 bytes
  let (userId, bytes) ← decodeUInt 4 bytes
  let (userLimits, bytes) ← UserLimits.decode bytes
  pure ({ brokerId, reserved1, branch, reserved26, userId, userLimits }, bytes)

@[simp] theorem encode_length (message : UserOrderValueLimitUpdateInMessage) : (encode message).length = 102 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, UserLimits.encode_length]

theorem encode_length_pos (message : UserOrderValueLimitUpdateInMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UserOrderValueLimitUpdateInMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [UserLimits.decode_encode, some_bind]
  rfl

end UserOrderValueLimitUpdateInMessage

/-- System Information Request Message: 0 bytes -/
structure SystemInformationRequestMessage where
  deriving DecidableEq, Repr

namespace SystemInformationRequestMessage

def encode (_ : SystemInformationRequestMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (SystemInformationRequestMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : SystemInformationRequestMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : SystemInformationRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end SystemInformationRequestMessage

/-- Any Client Message Payload, selected by Transaction Code -/
inductive ClientMessagePayload where
  | branchOrderValueLimitUpdateInMessage (message : BranchOrderValueLimitUpdateInMessage) -- 5716
  | cancelOnLogoutStatusRequestMessage (message : CancelOnLogoutStatusRequestMessage) -- 5790
  | messageDownloadRequestMessage (message : MessageDownloadRequestMessage) -- 7000
  | auctionInquiryRequestMessage (message : AuctionInquiryRequestMessage) -- 18016
  | boxSignOffMessage (message : BoxSignOffMessage) -- 20322
  | boxSignOnRequestMessage (message : BoxSignOnRequestMessage) -- 23000
  | gatewayRouterRequestMessage (message : GatewayRouterRequestMessage) -- 2400
  | orderEntryInMessage (message : OrderEntryInMessage) -- 2000
  | orderEntryInMessage2040 (message : OrderEntryInMessage) -- 2040
  | orderEntryInMessage2062 (message : OrderEntryInMessage) -- 2062
  | orderEntryInMessage2070 (message : OrderEntryInMessage) -- 2070
  | orderLimitUpdateInMessage (message : OrderLimitUpdateInMessage) -- 5721
  | passwordResetInMessage (message : PasswordResetInMessage) -- 5738
  | signOnRequestInMessage (message : SignOnRequestInMessage) -- 2300
  | signOnRequestInMessage5723 (message : SignOnRequestInMessage) -- 5723
  | tradeInquiryInMessage (message : TradeInquiryInMessage) -- 5440
  | tradeInquiryInMessage5445 (message : TradeInquiryInMessage) -- 5445
  | updateLocalDatabaseRequestMessage (message : UpdateLocalDatabaseRequestMessage) -- 7300
  | tradeModificationCancellationStatusRequestMessage (message : TradeModificationCancellationStatusRequestMessage) -- 5792
  | userUnlockRequestMessage (message : UserUnlockRequestMessage) -- 5424
  | userOrderValueLimitUpdateInMessage (message : UserOrderValueLimitUpdateInMessage) -- 5719
  | systemInformationRequestMessage (message : SystemInformationRequestMessage) -- 1600
  deriving DecidableEq, Repr

namespace ClientMessagePayload

/-- The Transaction Code each message is sent under -/
def tag : ClientMessagePayload → BitVec 16
  | .branchOrderValueLimitUpdateInMessage _ => 5716
  | .cancelOnLogoutStatusRequestMessage _ => 5790
  | .messageDownloadRequestMessage _ => 7000
  | .auctionInquiryRequestMessage _ => 18016
  | .boxSignOffMessage _ => 20322
  | .boxSignOnRequestMessage _ => 23000
  | .gatewayRouterRequestMessage _ => 2400
  | .orderEntryInMessage _ => 2000
  | .orderEntryInMessage2040 _ => 2040
  | .orderEntryInMessage2062 _ => 2062
  | .orderEntryInMessage2070 _ => 2070
  | .orderLimitUpdateInMessage _ => 5721
  | .passwordResetInMessage _ => 5738
  | .signOnRequestInMessage _ => 2300
  | .signOnRequestInMessage5723 _ => 5723
  | .tradeInquiryInMessage _ => 5440
  | .tradeInquiryInMessage5445 _ => 5445
  | .updateLocalDatabaseRequestMessage _ => 7300
  | .tradeModificationCancellationStatusRequestMessage _ => 5792
  | .userUnlockRequestMessage _ => 5424
  | .userOrderValueLimitUpdateInMessage _ => 5719
  | .systemInformationRequestMessage _ => 1600

def encode : ClientMessagePayload → List UInt8
  | .branchOrderValueLimitUpdateInMessage message => BranchOrderValueLimitUpdateInMessage.encode message
  | .cancelOnLogoutStatusRequestMessage message => CancelOnLogoutStatusRequestMessage.encode message
  | .messageDownloadRequestMessage message => MessageDownloadRequestMessage.encode message
  | .auctionInquiryRequestMessage message => AuctionInquiryRequestMessage.encode message
  | .boxSignOffMessage message => BoxSignOffMessage.encode message
  | .boxSignOnRequestMessage message => BoxSignOnRequestMessage.encode message
  | .gatewayRouterRequestMessage message => GatewayRouterRequestMessage.encode message
  | .orderEntryInMessage message => OrderEntryInMessage.encode message
  | .orderEntryInMessage2040 message => OrderEntryInMessage.encode message
  | .orderEntryInMessage2062 message => OrderEntryInMessage.encode message
  | .orderEntryInMessage2070 message => OrderEntryInMessage.encode message
  | .orderLimitUpdateInMessage message => OrderLimitUpdateInMessage.encode message
  | .passwordResetInMessage message => PasswordResetInMessage.encode message
  | .signOnRequestInMessage message => SignOnRequestInMessage.encode message
  | .signOnRequestInMessage5723 message => SignOnRequestInMessage.encode message
  | .tradeInquiryInMessage message => TradeInquiryInMessage.encode message
  | .tradeInquiryInMessage5445 message => TradeInquiryInMessage.encode message
  | .updateLocalDatabaseRequestMessage message => UpdateLocalDatabaseRequestMessage.encode message
  | .tradeModificationCancellationStatusRequestMessage message => TradeModificationCancellationStatusRequestMessage.encode message
  | .userUnlockRequestMessage message => UserUnlockRequestMessage.encode message
  | .userOrderValueLimitUpdateInMessage message => UserOrderValueLimitUpdateInMessage.encode message
  | .systemInformationRequestMessage message => SystemInformationRequestMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ClientMessagePayload) : (encode message).length ≤ 250 := by
  cases message with
  | branchOrderValueLimitUpdateInMessage inner =>
    simp only [encode, BranchOrderValueLimitUpdateInMessage.encode_length]
    omega
  | cancelOnLogoutStatusRequestMessage inner =>
    simp only [encode, CancelOnLogoutStatusRequestMessage.encode_length]
    omega
  | messageDownloadRequestMessage inner =>
    simp only [encode, MessageDownloadRequestMessage.encode_length]
    omega
  | auctionInquiryRequestMessage inner =>
    simp only [encode, AuctionInquiryRequestMessage.encode_length]
    omega
  | boxSignOffMessage inner =>
    simp only [encode, BoxSignOffMessage.encode_length]
    omega
  | boxSignOnRequestMessage inner =>
    simp only [encode, BoxSignOnRequestMessage.encode_length]
    omega
  | gatewayRouterRequestMessage inner =>
    simp only [encode, GatewayRouterRequestMessage.encode_length]
    omega
  | orderEntryInMessage inner =>
    simp only [encode, OrderEntryInMessage.encode_length]
    omega
  | orderEntryInMessage2040 inner =>
    simp only [encode, OrderEntryInMessage.encode_length]
    omega
  | orderEntryInMessage2062 inner =>
    simp only [encode, OrderEntryInMessage.encode_length]
    omega
  | orderEntryInMessage2070 inner =>
    simp only [encode, OrderEntryInMessage.encode_length]
    omega
  | orderLimitUpdateInMessage inner =>
    simp only [encode, OrderLimitUpdateInMessage.encode_length]
    omega
  | passwordResetInMessage inner =>
    simp only [encode, PasswordResetInMessage.encode_length]
    omega
  | signOnRequestInMessage inner =>
    simp only [encode, SignOnRequestInMessage.encode_length]
    omega
  | signOnRequestInMessage5723 inner =>
    simp only [encode, SignOnRequestInMessage.encode_length]
    omega
  | tradeInquiryInMessage inner =>
    simp only [encode, TradeInquiryInMessage.encode_length]
    omega
  | tradeInquiryInMessage5445 inner =>
    simp only [encode, TradeInquiryInMessage.encode_length]
    omega
  | updateLocalDatabaseRequestMessage inner =>
    simp only [encode, UpdateLocalDatabaseRequestMessage.encode_length]
    omega
  | tradeModificationCancellationStatusRequestMessage inner =>
    simp only [encode, TradeModificationCancellationStatusRequestMessage.encode_length]
    omega
  | userUnlockRequestMessage inner =>
    simp only [encode, UserUnlockRequestMessage.encode_length]
    omega
  | userOrderValueLimitUpdateInMessage inner =>
    simp only [encode, UserOrderValueLimitUpdateInMessage.encode_length]
    omega
  | systemInformationRequestMessage inner =>
    simp only [encode, SystemInformationRequestMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (ClientMessagePayload × List UInt8) :=
  if tag = 5716 then (BranchOrderValueLimitUpdateInMessage.decode bytes).map fun (message, rest) => (.branchOrderValueLimitUpdateInMessage message, rest)
  else if tag = 5790 then (CancelOnLogoutStatusRequestMessage.decode bytes).map fun (message, rest) => (.cancelOnLogoutStatusRequestMessage message, rest)
  else if tag = 7000 then (MessageDownloadRequestMessage.decode bytes).map fun (message, rest) => (.messageDownloadRequestMessage message, rest)
  else if tag = 18016 then (AuctionInquiryRequestMessage.decode bytes).map fun (message, rest) => (.auctionInquiryRequestMessage message, rest)
  else if tag = 20322 then (BoxSignOffMessage.decode bytes).map fun (message, rest) => (.boxSignOffMessage message, rest)
  else if tag = 23000 then (BoxSignOnRequestMessage.decode bytes).map fun (message, rest) => (.boxSignOnRequestMessage message, rest)
  else if tag = 2400 then (GatewayRouterRequestMessage.decode bytes).map fun (message, rest) => (.gatewayRouterRequestMessage message, rest)
  else if tag = 2000 then (OrderEntryInMessage.decode bytes).map fun (message, rest) => (.orderEntryInMessage message, rest)
  else if tag = 2040 then (OrderEntryInMessage.decode bytes).map fun (message, rest) => (.orderEntryInMessage2040 message, rest)
  else if tag = 2062 then (OrderEntryInMessage.decode bytes).map fun (message, rest) => (.orderEntryInMessage2062 message, rest)
  else if tag = 2070 then (OrderEntryInMessage.decode bytes).map fun (message, rest) => (.orderEntryInMessage2070 message, rest)
  else if tag = 5721 then (OrderLimitUpdateInMessage.decode bytes).map fun (message, rest) => (.orderLimitUpdateInMessage message, rest)
  else if tag = 5738 then (PasswordResetInMessage.decode bytes).map fun (message, rest) => (.passwordResetInMessage message, rest)
  else if tag = 2300 then (SignOnRequestInMessage.decode bytes).map fun (message, rest) => (.signOnRequestInMessage message, rest)
  else if tag = 5723 then (SignOnRequestInMessage.decode bytes).map fun (message, rest) => (.signOnRequestInMessage5723 message, rest)
  else if tag = 5440 then (TradeInquiryInMessage.decode bytes).map fun (message, rest) => (.tradeInquiryInMessage message, rest)
  else if tag = 5445 then (TradeInquiryInMessage.decode bytes).map fun (message, rest) => (.tradeInquiryInMessage5445 message, rest)
  else if tag = 7300 then (UpdateLocalDatabaseRequestMessage.decode bytes).map fun (message, rest) => (.updateLocalDatabaseRequestMessage message, rest)
  else if tag = 5792 then (TradeModificationCancellationStatusRequestMessage.decode bytes).map fun (message, rest) => (.tradeModificationCancellationStatusRequestMessage message, rest)
  else if tag = 5424 then (UserUnlockRequestMessage.decode bytes).map fun (message, rest) => (.userUnlockRequestMessage message, rest)
  else if tag = 5719 then (UserOrderValueLimitUpdateInMessage.decode bytes).map fun (message, rest) => (.userOrderValueLimitUpdateInMessage message, rest)
  else if tag = 1600 then (SystemInformationRequestMessage.decode bytes).map fun (message, rest) => (.systemInformationRequestMessage message, rest)
  else none

@[simp] theorem decode_encode (message : ClientMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ClientMessagePayload

/-- Client Message -/
structure ClientMessage where
  logTime : BitVec 32
  alphaChar : Alpha 2
  traderId : BitVec 32
  errorCode : BitVec 16
  headerTimestamp : BitVec 64
  timeStamp1 : Alpha 8
  timeStamp2 : Alpha 8
  clientMessagePayload : ClientMessagePayload
  deriving DecidableEq, Repr

namespace ClientMessage

def encodeBody (message : ClientMessage) : List UInt8 :=
  ClientMessagePayload.encode message.clientMessagePayload

def decodeBody (transactionCode : BitVec 16) (logTime : BitVec 32) (alphaChar : Alpha 2) (traderId : BitVec 32) (errorCode : BitVec 16) (headerTimestamp : BitVec 64) (timeStamp1 : Alpha 8) (timeStamp2 : Alpha 8) (bytes : List UInt8) : Option (ClientMessage × List UInt8) := do
  let (clientMessagePayload, bytes) ← ClientMessagePayload.decode transactionCode bytes
  pure ({ logTime, alphaChar, traderId, errorCode, headerTimestamp, timeStamp1, timeStamp2, clientMessagePayload }, bytes)

theorem decodeBody_encodeBody (message : ClientMessage) (rest : List UInt8) :
    decodeBody (ClientMessagePayload.tag message.clientMessagePayload) message.logTime message.alphaChar message.traderId message.errorCode message.headerTimestamp message.timeStamp1 message.timeStamp2 (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [ClientMessagePayload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : ClientMessage) : (encodeBody message).length + 40 < 256 ^ 2 := by
  unfold encodeBody
  cases message.clientMessagePayload with
  | branchOrderValueLimitUpdateInMessage inner =>
    simp only [ClientMessagePayload.encode, BranchOrderValueLimitUpdateInMessage.encode_length]
    omega
  | cancelOnLogoutStatusRequestMessage inner =>
    simp only [ClientMessagePayload.encode, CancelOnLogoutStatusRequestMessage.encode_length]
    omega
  | messageDownloadRequestMessage inner =>
    simp only [ClientMessagePayload.encode, MessageDownloadRequestMessage.encode_length]
    omega
  | auctionInquiryRequestMessage inner =>
    simp only [ClientMessagePayload.encode, AuctionInquiryRequestMessage.encode_length]
    omega
  | boxSignOffMessage inner =>
    simp only [ClientMessagePayload.encode, BoxSignOffMessage.encode_length]
    omega
  | boxSignOnRequestMessage inner =>
    simp only [ClientMessagePayload.encode, BoxSignOnRequestMessage.encode_length]
    omega
  | gatewayRouterRequestMessage inner =>
    simp only [ClientMessagePayload.encode, GatewayRouterRequestMessage.encode_length]
    omega
  | orderEntryInMessage inner =>
    simp only [ClientMessagePayload.encode, OrderEntryInMessage.encode_length]
    omega
  | orderEntryInMessage2040 inner =>
    simp only [ClientMessagePayload.encode, OrderEntryInMessage.encode_length]
    omega
  | orderEntryInMessage2062 inner =>
    simp only [ClientMessagePayload.encode, OrderEntryInMessage.encode_length]
    omega
  | orderEntryInMessage2070 inner =>
    simp only [ClientMessagePayload.encode, OrderEntryInMessage.encode_length]
    omega
  | orderLimitUpdateInMessage inner =>
    simp only [ClientMessagePayload.encode, OrderLimitUpdateInMessage.encode_length]
    omega
  | passwordResetInMessage inner =>
    simp only [ClientMessagePayload.encode, PasswordResetInMessage.encode_length]
    omega
  | signOnRequestInMessage inner =>
    simp only [ClientMessagePayload.encode, SignOnRequestInMessage.encode_length]
    omega
  | signOnRequestInMessage5723 inner =>
    simp only [ClientMessagePayload.encode, SignOnRequestInMessage.encode_length]
    omega
  | tradeInquiryInMessage inner =>
    simp only [ClientMessagePayload.encode, TradeInquiryInMessage.encode_length]
    omega
  | tradeInquiryInMessage5445 inner =>
    simp only [ClientMessagePayload.encode, TradeInquiryInMessage.encode_length]
    omega
  | updateLocalDatabaseRequestMessage inner =>
    simp only [ClientMessagePayload.encode, UpdateLocalDatabaseRequestMessage.encode_length]
    omega
  | tradeModificationCancellationStatusRequestMessage inner =>
    simp only [ClientMessagePayload.encode, TradeModificationCancellationStatusRequestMessage.encode_length]
    omega
  | userUnlockRequestMessage inner =>
    simp only [ClientMessagePayload.encode, UserUnlockRequestMessage.encode_length]
    omega
  | userOrderValueLimitUpdateInMessage inner =>
    simp only [ClientMessagePayload.encode, UserOrderValueLimitUpdateInMessage.encode_length]
    omega
  | systemInformationRequestMessage inner =>
    simp only [ClientMessagePayload.encode, SystemInformationRequestMessage.encode_length]
    omega

/-- Size rule: Message Length counts the bytes after it plus 40, so it is written from the body and checked on decode; Transaction Code, Log Time, Alpha Char, Trader Id, Error Code, Header Timestamp, Time Stamp 1, Time Stamp 2 are read ahead of it -/
def encode (message : ClientMessage) : List UInt8 :=
  encodeUInt 2 (ClientMessagePayload.tag message.clientMessagePayload)
    ++ (encodeUInt 4 message.logTime
    ++ (Alpha.encode message.alphaChar
    ++ (encodeUInt 4 message.traderId
    ++ (encodeUInt 2 message.errorCode
    ++ (encodeUInt 8 message.headerTimestamp
    ++ (Alpha.encode message.timeStamp1
    ++ (Alpha.encode message.timeStamp2
    ++ (encodeFramed 2 40 encodeBody message))))))))

def decode (bytes : List UInt8) : Option (ClientMessage × List UInt8) := do
  let (transactionCode, bytes) ← decodeUInt 2 bytes
  let (logTime, bytes) ← decodeUInt 4 bytes
  let (alphaChar, bytes) ← Alpha.decode 2 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (errorCode, bytes) ← decodeUInt 2 bytes
  let (headerTimestamp, bytes) ← decodeUInt 8 bytes
  let (timeStamp1, bytes) ← Alpha.decode 8 bytes
  let (timeStamp2, bytes) ← Alpha.decode 8 bytes
  decodeFramed 2 40 (decodeBody transactionCode logTime alphaChar traderId errorCode headerTimestamp timeStamp1 timeStamp2) bytes

@[simp] theorem decode_encode (message : ClientMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  exact decodeFramed_encodeFramed 2 40 encodeBody (decodeBody (ClientMessagePayload.tag message.clientMessagePayload) message.logTime message.alphaChar message.traderId message.errorCode message.headerTimestamp message.timeStamp1 message.timeStamp2) message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : ClientMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, Alpha.encode_length, List.length_append, ← Nat.add_assoc, encodeFramed_length]
  omega

end ClientMessage

/-- Client Packet -/
structure ClientPacket where
  clientMessage : List ClientMessage
  deriving DecidableEq, Repr

namespace ClientPacket

def encode (message : ClientPacket) : List UInt8 :=
  encodeMany ClientMessage.encode message.clientMessage

def decode (bytes : List UInt8) : Option ClientPacket := do
  let clientMessage ← decodeAll ClientMessage.decode bytes.length bytes
  pure { clientMessage }

theorem decode_encode (message : ClientPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany ClientMessage.encode ClientMessage.decode ClientMessage.decode_encode ClientMessage.encode_length_pos message.clientMessage _ (encodeMany_length_ge ClientMessage.encode ClientMessage.encode_length_pos message.clientMessage), some_bind]
  rfl

end ClientPacket

end Omi.NseNsecmOrderentryNnfV66Client
