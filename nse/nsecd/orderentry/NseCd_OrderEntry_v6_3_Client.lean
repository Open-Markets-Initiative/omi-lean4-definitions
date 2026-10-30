import Wire

/-!
# National Stock Exchange of India Ltd Order Entry v6.3

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NseNsecdOrderentryNnfV63Client

/-- System Information In Message: 4 bytes -/
structure SystemInformationInMessage where
  lastUpdatePortfolioTIme : BitVec 32
  deriving DecidableEq, Repr

namespace SystemInformationInMessage

def encode (message : SystemInformationInMessage) : List UInt8 :=
  encodeUInt 4 message.lastUpdatePortfolioTIme

def decode (bytes : List UInt8) : Option (SystemInformationInMessage × List UInt8) := do
  let (lastUpdatePortfolioTIme, bytes) ← decodeUInt 4 bytes
  pure ({ lastUpdatePortfolioTIme }, bytes)

@[simp] theorem encode_length (message : SystemInformationInMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : SystemInformationInMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemInformationInMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SystemInformationInMessage

/-- Contract Desc: 28 bytes -/
structure ContractDesc where
  instrumentName : Alpha 6
  symbol : Alpha 10
  expiryDate : BitVec 32
  strikePrice : BitVec 32
  optionType : Alpha 2
  caLevel : BitVec 16
  deriving DecidableEq, Repr

namespace ContractDesc

def encode (message : ContractDesc) : List UInt8 :=
  Alpha.encode message.instrumentName
    ++ (Alpha.encode message.symbol
    ++ (encodeUInt 4 message.expiryDate
    ++ (encodeUInt 4 message.strikePrice
    ++ (Alpha.encode message.optionType
    ++ (encodeUInt 2 message.caLevel)))))

def decode (bytes : List UInt8) : Option (ContractDesc × List UInt8) := do
  let (instrumentName, bytes) ← Alpha.decode 6 bytes
  let (symbol, bytes) ← Alpha.decode 10 bytes
  let (expiryDate, bytes) ← decodeUInt 4 bytes
  let (strikePrice, bytes) ← decodeUInt 4 bytes
  let (optionType, bytes) ← Alpha.decode 2 bytes
  let (caLevel, bytes) ← decodeUInt 2 bytes
  pure ({ instrumentName, symbol, expiryDate, strikePrice, optionType, caLevel }, bytes)

@[simp] theorem encode_length (message : ContractDesc) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ContractDesc) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ContractDesc) (rest : List UInt8) :
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ContractDesc

/-- Board Lot In Message: 276 bytes -/
structure BoardLotInMessage where
  participantType : Alpha 1
  reserved1 : Alpha 1
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  modifiedCancelledBy : Alpha 1
  secondReserved1 : Alpha 1
  reasonCode : BitVec 16
  reserved4 : Alpha 4
  tokenNo : BitVec 32
  contractDesc : ContractDesc
  counterPartyBrokerId : Alpha 5
  thirdReserved1 : Alpha 1
  reserved2 : Alpha 2
  closeoutFlag : Alpha 1
  fourthReserved1 : Alpha 1
  orderType : BitVec 16
  orderNumber : Alpha 8
  accountNumber : Alpha 10
  bookTypeShort2 : BitVec 16
  buySellIndicator : BitVec 16
  disclosedVolume : BitVec 32
  disclosedVolumeRemaining : BitVec 32
  totalVolumeRemaining : BitVec 32
  volume : BitVec 32
  volumeFilledToday : BitVec 32
  price : BitVec 32
  triggerPrice : BitVec 32
  goodTillDate : BitVec 32
  entryDateTime : BitVec 32
  minimumFillAonVolume : BitVec 32
  lastModified : BitVec 32
  stOrderFlags : BitVec 16
  branchId : BitVec 16
  traderId : BitVec 32
  brokerId : Alpha 5
  cOrdFiller : Alpha 24
  openClose : Alpha 1
  settlor : Alpha 12
  proClientIndicator : BitVec 16
  settlementPeriod : BitVec 16
  additionalOrderFlags : BitVec 8
  fifthReserved1 : Alpha 1
  reference : Alpha 4
  nnfField : Alpha 8
  mktReplay : BitVec 64
  pan : Alpha 10
  algoId : BitVec 32
  secondReserved2 : Alpha 2
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  deriving DecidableEq, Repr

namespace BoardLotInMessage

def encode (message : BoardLotInMessage) : List UInt8 :=
  Alpha.encode message.participantType
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (Alpha.encode message.modifiedCancelledBy
    ++ (Alpha.encode message.secondReserved1
    ++ (encodeUInt 2 message.reasonCode
    ++ (Alpha.encode message.reserved4
    ++ (encodeUInt 4 message.tokenNo
    ++ (ContractDesc.encode message.contractDesc
    ++ (Alpha.encode message.counterPartyBrokerId
    ++ (Alpha.encode message.thirdReserved1
    ++ (Alpha.encode message.reserved2
    ++ (Alpha.encode message.closeoutFlag
    ++ (Alpha.encode message.fourthReserved1
    ++ (encodeUInt 2 message.orderType
    ++ (Alpha.encode message.orderNumber
    ++ (Alpha.encode message.accountNumber
    ++ (encodeUInt 2 message.bookTypeShort2
    ++ (encodeUInt 2 message.buySellIndicator
    ++ (encodeUInt 4 message.disclosedVolume
    ++ (encodeUInt 4 message.disclosedVolumeRemaining
    ++ (encodeUInt 4 message.totalVolumeRemaining
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 4 message.volumeFilledToday
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.triggerPrice
    ++ (encodeUInt 4 message.goodTillDate
    ++ (encodeUInt 4 message.entryDateTime
    ++ (encodeUInt 4 message.minimumFillAonVolume
    ++ (encodeUInt 4 message.lastModified
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId
    ++ (encodeUInt 4 message.traderId
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.cOrdFiller
    ++ (Alpha.encode message.openClose
    ++ (Alpha.encode message.settlor
    ++ (encodeUInt 2 message.proClientIndicator
    ++ (encodeUInt 2 message.settlementPeriod
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.fifthReserved1
    ++ (Alpha.encode message.reference
    ++ (Alpha.encode message.nnfField
    ++ (encodeUInt 8 message.mktReplay
    ++ (Alpha.encode message.pan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.secondReserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52)))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (BoardLotInMessage × List UInt8) := do
  let (participantType, bytes) ← Alpha.decode 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (modifiedCancelledBy, bytes) ← Alpha.decode 1 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  let (reasonCode, bytes) ← decodeUInt 2 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (tokenNo, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (counterPartyBrokerId, bytes) ← Alpha.decode 5 bytes
  let (thirdReserved1, bytes) ← Alpha.decode 1 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (closeoutFlag, bytes) ← Alpha.decode 1 bytes
  let (fourthReserved1, bytes) ← Alpha.decode 1 bytes
  let (orderType, bytes) ← decodeUInt 2 bytes
  let (orderNumber, bytes) ← Alpha.decode 8 bytes
  let (accountNumber, bytes) ← Alpha.decode 10 bytes
  let (bookTypeShort2, bytes) ← decodeUInt 2 bytes
  let (buySellIndicator, bytes) ← decodeUInt 2 bytes
  let (disclosedVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolumeRemaining, bytes) ← decodeUInt 4 bytes
  let (totalVolumeRemaining, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (triggerPrice, bytes) ← decodeUInt 4 bytes
  let (goodTillDate, bytes) ← decodeUInt 4 bytes
  let (entryDateTime, bytes) ← decodeUInt 4 bytes
  let (minimumFillAonVolume, bytes) ← decodeUInt 4 bytes
  let (lastModified, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId, bytes) ← decodeUInt 2 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (cOrdFiller, bytes) ← Alpha.decode 24 bytes
  let (openClose, bytes) ← Alpha.decode 1 bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  let (proClientIndicator, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (fifthReserved1, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 4 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← decodeUInt 8 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (secondReserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  pure ({ participantType, reserved1, competitorPeriod, solicitorPeriod, modifiedCancelledBy, secondReserved1, reasonCode, reserved4, tokenNo, contractDesc, counterPartyBrokerId, thirdReserved1, reserved2, closeoutFlag, fourthReserved1, orderType, orderNumber, accountNumber, bookTypeShort2, buySellIndicator, disclosedVolume, disclosedVolumeRemaining, totalVolumeRemaining, volume, volumeFilledToday, price, triggerPrice, goodTillDate, entryDateTime, minimumFillAonVolume, lastModified, stOrderFlags, branchId, traderId, brokerId, cOrdFiller, openClose, settlor, proClientIndicator, settlementPeriod, additionalOrderFlags, fifthReserved1, reference, nnfField, mktReplay, pan, algoId, secondReserved2, lastActivityReference, reserved52 }, bytes)

@[simp] theorem encode_length (message : BoardLotInMessage) : (encode message).length = 276 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : BoardLotInMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : BoardLotInMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
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

end BoardLotInMessage

/-- Order Mod In Message: 276 bytes -/
structure OrderModInMessage where
  participantType : Alpha 1
  reserved1 : Alpha 1
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  modifiedCancelledBy : Alpha 1
  secondReserved1 : Alpha 1
  reasonCode : BitVec 16
  reserved4 : Alpha 4
  tokenNo : BitVec 32
  contractDesc : ContractDesc
  counterPartyBrokerId : Alpha 5
  thirdReserved1 : Alpha 1
  reserved2 : Alpha 2
  closeoutFlag : Alpha 1
  fourthReserved1 : Alpha 1
  orderType : BitVec 16
  orderNumber : Alpha 8
  accountNumber : Alpha 10
  bookTypeShort2 : BitVec 16
  buySellIndicator : BitVec 16
  disclosedVolume : BitVec 32
  disclosedVolumeRemaining : BitVec 32
  totalVolumeRemaining : BitVec 32
  volume : BitVec 32
  volumeFilledToday : BitVec 32
  price : BitVec 32
  triggerPrice : BitVec 32
  goodTillDate : BitVec 32
  entryDateTime : BitVec 32
  minimumFillAonVolume : BitVec 32
  lastModified : BitVec 32
  stOrderFlags : BitVec 16
  branchId : BitVec 16
  traderId : BitVec 32
  brokerId : Alpha 5
  cOrdFiller : Alpha 24
  openClose : Alpha 1
  settlor : Alpha 12
  proClientIndicator : BitVec 16
  settlementPeriod : BitVec 16
  additionalOrderFlags : BitVec 8
  fifthReserved1 : Alpha 1
  reference : Alpha 4
  nnfField : Alpha 8
  mktReplay : BitVec 64
  pan : Alpha 10
  algoId : BitVec 32
  secondReserved2 : Alpha 2
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  deriving DecidableEq, Repr

namespace OrderModInMessage

def encode (message : OrderModInMessage) : List UInt8 :=
  Alpha.encode message.participantType
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (Alpha.encode message.modifiedCancelledBy
    ++ (Alpha.encode message.secondReserved1
    ++ (encodeUInt 2 message.reasonCode
    ++ (Alpha.encode message.reserved4
    ++ (encodeUInt 4 message.tokenNo
    ++ (ContractDesc.encode message.contractDesc
    ++ (Alpha.encode message.counterPartyBrokerId
    ++ (Alpha.encode message.thirdReserved1
    ++ (Alpha.encode message.reserved2
    ++ (Alpha.encode message.closeoutFlag
    ++ (Alpha.encode message.fourthReserved1
    ++ (encodeUInt 2 message.orderType
    ++ (Alpha.encode message.orderNumber
    ++ (Alpha.encode message.accountNumber
    ++ (encodeUInt 2 message.bookTypeShort2
    ++ (encodeUInt 2 message.buySellIndicator
    ++ (encodeUInt 4 message.disclosedVolume
    ++ (encodeUInt 4 message.disclosedVolumeRemaining
    ++ (encodeUInt 4 message.totalVolumeRemaining
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 4 message.volumeFilledToday
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.triggerPrice
    ++ (encodeUInt 4 message.goodTillDate
    ++ (encodeUInt 4 message.entryDateTime
    ++ (encodeUInt 4 message.minimumFillAonVolume
    ++ (encodeUInt 4 message.lastModified
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId
    ++ (encodeUInt 4 message.traderId
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.cOrdFiller
    ++ (Alpha.encode message.openClose
    ++ (Alpha.encode message.settlor
    ++ (encodeUInt 2 message.proClientIndicator
    ++ (encodeUInt 2 message.settlementPeriod
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.fifthReserved1
    ++ (Alpha.encode message.reference
    ++ (Alpha.encode message.nnfField
    ++ (encodeUInt 8 message.mktReplay
    ++ (Alpha.encode message.pan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.secondReserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52)))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderModInMessage × List UInt8) := do
  let (participantType, bytes) ← Alpha.decode 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (modifiedCancelledBy, bytes) ← Alpha.decode 1 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  let (reasonCode, bytes) ← decodeUInt 2 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (tokenNo, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (counterPartyBrokerId, bytes) ← Alpha.decode 5 bytes
  let (thirdReserved1, bytes) ← Alpha.decode 1 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (closeoutFlag, bytes) ← Alpha.decode 1 bytes
  let (fourthReserved1, bytes) ← Alpha.decode 1 bytes
  let (orderType, bytes) ← decodeUInt 2 bytes
  let (orderNumber, bytes) ← Alpha.decode 8 bytes
  let (accountNumber, bytes) ← Alpha.decode 10 bytes
  let (bookTypeShort2, bytes) ← decodeUInt 2 bytes
  let (buySellIndicator, bytes) ← decodeUInt 2 bytes
  let (disclosedVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolumeRemaining, bytes) ← decodeUInt 4 bytes
  let (totalVolumeRemaining, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (triggerPrice, bytes) ← decodeUInt 4 bytes
  let (goodTillDate, bytes) ← decodeUInt 4 bytes
  let (entryDateTime, bytes) ← decodeUInt 4 bytes
  let (minimumFillAonVolume, bytes) ← decodeUInt 4 bytes
  let (lastModified, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId, bytes) ← decodeUInt 2 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (cOrdFiller, bytes) ← Alpha.decode 24 bytes
  let (openClose, bytes) ← Alpha.decode 1 bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  let (proClientIndicator, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (fifthReserved1, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 4 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← decodeUInt 8 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (secondReserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  pure ({ participantType, reserved1, competitorPeriod, solicitorPeriod, modifiedCancelledBy, secondReserved1, reasonCode, reserved4, tokenNo, contractDesc, counterPartyBrokerId, thirdReserved1, reserved2, closeoutFlag, fourthReserved1, orderType, orderNumber, accountNumber, bookTypeShort2, buySellIndicator, disclosedVolume, disclosedVolumeRemaining, totalVolumeRemaining, volume, volumeFilledToday, price, triggerPrice, goodTillDate, entryDateTime, minimumFillAonVolume, lastModified, stOrderFlags, branchId, traderId, brokerId, cOrdFiller, openClose, settlor, proClientIndicator, settlementPeriod, additionalOrderFlags, fifthReserved1, reference, nnfField, mktReplay, pan, algoId, secondReserved2, lastActivityReference, reserved52 }, bytes)

@[simp] theorem encode_length (message : OrderModInMessage) : (encode message).length = 276 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : OrderModInMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OrderModInMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
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

end OrderModInMessage

/-- Order Cancel In Message: 276 bytes -/
structure OrderCancelInMessage where
  participantType : Alpha 1
  reserved1 : Alpha 1
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  modifiedCancelledBy : Alpha 1
  secondReserved1 : Alpha 1
  reasonCode : BitVec 16
  reserved4 : Alpha 4
  tokenNo : BitVec 32
  contractDesc : ContractDesc
  counterPartyBrokerId : Alpha 5
  thirdReserved1 : Alpha 1
  reserved2 : Alpha 2
  closeoutFlag : Alpha 1
  fourthReserved1 : Alpha 1
  orderType : BitVec 16
  orderNumber : Alpha 8
  accountNumber : Alpha 10
  bookTypeShort2 : BitVec 16
  buySellIndicator : BitVec 16
  disclosedVolume : BitVec 32
  disclosedVolumeRemaining : BitVec 32
  totalVolumeRemaining : BitVec 32
  volume : BitVec 32
  volumeFilledToday : BitVec 32
  price : BitVec 32
  triggerPrice : BitVec 32
  goodTillDate : BitVec 32
  entryDateTime : BitVec 32
  minimumFillAonVolume : BitVec 32
  lastModified : BitVec 32
  stOrderFlags : BitVec 16
  branchId : BitVec 16
  traderId : BitVec 32
  brokerId : Alpha 5
  cOrdFiller : Alpha 24
  openClose : Alpha 1
  settlor : Alpha 12
  proClientIndicator : BitVec 16
  settlementPeriod : BitVec 16
  additionalOrderFlags : BitVec 8
  fifthReserved1 : Alpha 1
  reference : Alpha 4
  nnfField : Alpha 8
  mktReplay : BitVec 64
  pan : Alpha 10
  algoId : BitVec 32
  secondReserved2 : Alpha 2
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  deriving DecidableEq, Repr

namespace OrderCancelInMessage

def encode (message : OrderCancelInMessage) : List UInt8 :=
  Alpha.encode message.participantType
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (Alpha.encode message.modifiedCancelledBy
    ++ (Alpha.encode message.secondReserved1
    ++ (encodeUInt 2 message.reasonCode
    ++ (Alpha.encode message.reserved4
    ++ (encodeUInt 4 message.tokenNo
    ++ (ContractDesc.encode message.contractDesc
    ++ (Alpha.encode message.counterPartyBrokerId
    ++ (Alpha.encode message.thirdReserved1
    ++ (Alpha.encode message.reserved2
    ++ (Alpha.encode message.closeoutFlag
    ++ (Alpha.encode message.fourthReserved1
    ++ (encodeUInt 2 message.orderType
    ++ (Alpha.encode message.orderNumber
    ++ (Alpha.encode message.accountNumber
    ++ (encodeUInt 2 message.bookTypeShort2
    ++ (encodeUInt 2 message.buySellIndicator
    ++ (encodeUInt 4 message.disclosedVolume
    ++ (encodeUInt 4 message.disclosedVolumeRemaining
    ++ (encodeUInt 4 message.totalVolumeRemaining
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 4 message.volumeFilledToday
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.triggerPrice
    ++ (encodeUInt 4 message.goodTillDate
    ++ (encodeUInt 4 message.entryDateTime
    ++ (encodeUInt 4 message.minimumFillAonVolume
    ++ (encodeUInt 4 message.lastModified
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId
    ++ (encodeUInt 4 message.traderId
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.cOrdFiller
    ++ (Alpha.encode message.openClose
    ++ (Alpha.encode message.settlor
    ++ (encodeUInt 2 message.proClientIndicator
    ++ (encodeUInt 2 message.settlementPeriod
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.fifthReserved1
    ++ (Alpha.encode message.reference
    ++ (Alpha.encode message.nnfField
    ++ (encodeUInt 8 message.mktReplay
    ++ (Alpha.encode message.pan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.secondReserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52)))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderCancelInMessage × List UInt8) := do
  let (participantType, bytes) ← Alpha.decode 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (modifiedCancelledBy, bytes) ← Alpha.decode 1 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  let (reasonCode, bytes) ← decodeUInt 2 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (tokenNo, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (counterPartyBrokerId, bytes) ← Alpha.decode 5 bytes
  let (thirdReserved1, bytes) ← Alpha.decode 1 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (closeoutFlag, bytes) ← Alpha.decode 1 bytes
  let (fourthReserved1, bytes) ← Alpha.decode 1 bytes
  let (orderType, bytes) ← decodeUInt 2 bytes
  let (orderNumber, bytes) ← Alpha.decode 8 bytes
  let (accountNumber, bytes) ← Alpha.decode 10 bytes
  let (bookTypeShort2, bytes) ← decodeUInt 2 bytes
  let (buySellIndicator, bytes) ← decodeUInt 2 bytes
  let (disclosedVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolumeRemaining, bytes) ← decodeUInt 4 bytes
  let (totalVolumeRemaining, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (triggerPrice, bytes) ← decodeUInt 4 bytes
  let (goodTillDate, bytes) ← decodeUInt 4 bytes
  let (entryDateTime, bytes) ← decodeUInt 4 bytes
  let (minimumFillAonVolume, bytes) ← decodeUInt 4 bytes
  let (lastModified, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId, bytes) ← decodeUInt 2 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (cOrdFiller, bytes) ← Alpha.decode 24 bytes
  let (openClose, bytes) ← Alpha.decode 1 bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  let (proClientIndicator, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (fifthReserved1, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 4 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← decodeUInt 8 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (secondReserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  pure ({ participantType, reserved1, competitorPeriod, solicitorPeriod, modifiedCancelledBy, secondReserved1, reasonCode, reserved4, tokenNo, contractDesc, counterPartyBrokerId, thirdReserved1, reserved2, closeoutFlag, fourthReserved1, orderType, orderNumber, accountNumber, bookTypeShort2, buySellIndicator, disclosedVolume, disclosedVolumeRemaining, totalVolumeRemaining, volume, volumeFilledToday, price, triggerPrice, goodTillDate, entryDateTime, minimumFillAonVolume, lastModified, stOrderFlags, branchId, traderId, brokerId, cOrdFiller, openClose, settlor, proClientIndicator, settlementPeriod, additionalOrderFlags, fifthReserved1, reference, nnfField, mktReplay, pan, algoId, secondReserved2, lastActivityReference, reserved52 }, bytes)

@[simp] theorem encode_length (message : OrderCancelInMessage) : (encode message).length = 276 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : OrderCancelInMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OrderCancelInMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
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

end OrderCancelInMessage

/-- Price Mod In Message: 66 bytes -/
structure PriceModInMessage where
  tokenNo : BitVec 32
  traderId : BitVec 32
  orderNumber : Alpha 8
  buySell : BitVec 16
  price : BitVec 32
  volume : BitVec 32
  lastModified : BitVec 32
  reference : Alpha 4
  lastActivityReference : BitVec 64
  reserved24 : Alpha 24
  deriving DecidableEq, Repr

namespace PriceModInMessage

def encode (message : PriceModInMessage) : List UInt8 :=
  encodeUInt 4 message.tokenNo
    ++ (encodeUInt 4 message.traderId
    ++ (Alpha.encode message.orderNumber
    ++ (encodeUInt 2 message.buySell
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 4 message.lastModified
    ++ (Alpha.encode message.reference
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved24)))))))))

def decode (bytes : List UInt8) : Option (PriceModInMessage × List UInt8) := do
  let (tokenNo, bytes) ← decodeUInt 4 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (orderNumber, bytes) ← Alpha.decode 8 bytes
  let (buySell, bytes) ← decodeUInt 2 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (lastModified, bytes) ← decodeUInt 4 bytes
  let (reference, bytes) ← Alpha.decode 4 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved24, bytes) ← Alpha.decode 24 bytes
  pure ({ tokenNo, traderId, orderNumber, buySell, price, volume, lastModified, reference, lastActivityReference, reserved24 }, bytes)

@[simp] theorem encode_length (message : PriceModInMessage) : (encode message).length = 66 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : PriceModInMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PriceModInMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end PriceModInMessage

/-- Ms Spd Leg Info Leg 2: 80 bytes -/
structure MsSpdLegInfoLeg2 where
  token2 : BitVec 32
  contractDesc : ContractDesc
  opBrokerId2 : Alpha 5
  fillerx2 : Alpha 1
  orderType2 : BitVec 16
  buySell2 : BitVec 16
  disclosedVol2 : BitVec 32
  disclosedVolRemaining2 : BitVec 32
  totalVolRemaining2 : BitVec 32
  volume2 : BitVec 32
  volumeFilledToday2 : BitVec 32
  price2 : BitVec 32
  triggerPrice2 : BitVec 32
  minFillAon2 : BitVec 32
  stOrderFlags : BitVec 16
  openClose2 : Alpha 1
  additionalOrderFlags : BitVec 8
  reserved1 : Alpha 1
  fillerY : Alpha 1
  deriving DecidableEq, Repr

namespace MsSpdLegInfoLeg2

def encode (message : MsSpdLegInfoLeg2) : List UInt8 :=
  encodeUInt 4 message.token2
    ++ (ContractDesc.encode message.contractDesc
    ++ (Alpha.encode message.opBrokerId2
    ++ (Alpha.encode message.fillerx2
    ++ (encodeUInt 2 message.orderType2
    ++ (encodeUInt 2 message.buySell2
    ++ (encodeUInt 4 message.disclosedVol2
    ++ (encodeUInt 4 message.disclosedVolRemaining2
    ++ (encodeUInt 4 message.totalVolRemaining2
    ++ (encodeUInt 4 message.volume2
    ++ (encodeUInt 4 message.volumeFilledToday2
    ++ (encodeUInt 4 message.price2
    ++ (encodeUInt 4 message.triggerPrice2
    ++ (encodeUInt 4 message.minFillAon2
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (Alpha.encode message.openClose2
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.reserved1
    ++ (Alpha.encode message.fillerY))))))))))))))))))

def decode (bytes : List UInt8) : Option (MsSpdLegInfoLeg2 × List UInt8) := do
  let (token2, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (opBrokerId2, bytes) ← Alpha.decode 5 bytes
  let (fillerx2, bytes) ← Alpha.decode 1 bytes
  let (orderType2, bytes) ← decodeUInt 2 bytes
  let (buySell2, bytes) ← decodeUInt 2 bytes
  let (disclosedVol2, bytes) ← decodeUInt 4 bytes
  let (disclosedVolRemaining2, bytes) ← decodeUInt 4 bytes
  let (totalVolRemaining2, bytes) ← decodeUInt 4 bytes
  let (volume2, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday2, bytes) ← decodeUInt 4 bytes
  let (price2, bytes) ← decodeUInt 4 bytes
  let (triggerPrice2, bytes) ← decodeUInt 4 bytes
  let (minFillAon2, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (openClose2, bytes) ← Alpha.decode 1 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (fillerY, bytes) ← Alpha.decode 1 bytes
  pure ({ token2, contractDesc, opBrokerId2, fillerx2, orderType2, buySell2, disclosedVol2, disclosedVolRemaining2, totalVolRemaining2, volume2, volumeFilledToday2, price2, triggerPrice2, minFillAon2, stOrderFlags, openClose2, additionalOrderFlags, reserved1, fillerY }, bytes)

@[simp] theorem encode_length (message : MsSpdLegInfoLeg2) : (encode message).length = 80 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, ContractDesc.encode_length, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : MsSpdLegInfoLeg2) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MsSpdLegInfoLeg2) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MsSpdLegInfoLeg2

/-- Ms Spd Leg Info Leg 3: 80 bytes -/
structure MsSpdLegInfoLeg3 where
  token2 : BitVec 32
  contractDesc : ContractDesc
  opBrokerId2 : Alpha 5
  fillerx2 : Alpha 1
  orderType2 : BitVec 16
  buySell2 : BitVec 16
  disclosedVol2 : BitVec 32
  disclosedVolRemaining2 : BitVec 32
  totalVolRemaining2 : BitVec 32
  volume2 : BitVec 32
  volumeFilledToday2 : BitVec 32
  price2 : BitVec 32
  triggerPrice2 : BitVec 32
  minFillAon2 : BitVec 32
  stOrderFlags : BitVec 16
  openClose2 : Alpha 1
  additionalOrderFlags : BitVec 8
  reserved1 : Alpha 1
  fillerY : Alpha 1
  deriving DecidableEq, Repr

namespace MsSpdLegInfoLeg3

def encode (message : MsSpdLegInfoLeg3) : List UInt8 :=
  encodeUInt 4 message.token2
    ++ (ContractDesc.encode message.contractDesc
    ++ (Alpha.encode message.opBrokerId2
    ++ (Alpha.encode message.fillerx2
    ++ (encodeUInt 2 message.orderType2
    ++ (encodeUInt 2 message.buySell2
    ++ (encodeUInt 4 message.disclosedVol2
    ++ (encodeUInt 4 message.disclosedVolRemaining2
    ++ (encodeUInt 4 message.totalVolRemaining2
    ++ (encodeUInt 4 message.volume2
    ++ (encodeUInt 4 message.volumeFilledToday2
    ++ (encodeUInt 4 message.price2
    ++ (encodeUInt 4 message.triggerPrice2
    ++ (encodeUInt 4 message.minFillAon2
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (Alpha.encode message.openClose2
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.reserved1
    ++ (Alpha.encode message.fillerY))))))))))))))))))

def decode (bytes : List UInt8) : Option (MsSpdLegInfoLeg3 × List UInt8) := do
  let (token2, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (opBrokerId2, bytes) ← Alpha.decode 5 bytes
  let (fillerx2, bytes) ← Alpha.decode 1 bytes
  let (orderType2, bytes) ← decodeUInt 2 bytes
  let (buySell2, bytes) ← decodeUInt 2 bytes
  let (disclosedVol2, bytes) ← decodeUInt 4 bytes
  let (disclosedVolRemaining2, bytes) ← decodeUInt 4 bytes
  let (totalVolRemaining2, bytes) ← decodeUInt 4 bytes
  let (volume2, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday2, bytes) ← decodeUInt 4 bytes
  let (price2, bytes) ← decodeUInt 4 bytes
  let (triggerPrice2, bytes) ← decodeUInt 4 bytes
  let (minFillAon2, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (openClose2, bytes) ← Alpha.decode 1 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (fillerY, bytes) ← Alpha.decode 1 bytes
  pure ({ token2, contractDesc, opBrokerId2, fillerx2, orderType2, buySell2, disclosedVol2, disclosedVolRemaining2, totalVolRemaining2, volume2, volumeFilledToday2, price2, triggerPrice2, minFillAon2, stOrderFlags, openClose2, additionalOrderFlags, reserved1, fillerY }, bytes)

@[simp] theorem encode_length (message : MsSpdLegInfoLeg3) : (encode message).length = 80 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, ContractDesc.encode_length, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : MsSpdLegInfoLeg3) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MsSpdLegInfoLeg3) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MsSpdLegInfoLeg3

/-- Sp Board Lot In Message: 440 bytes -/
structure SpBoardLotInMessage where
  participantType1 : Alpha 1
  filler1 : Alpha 1
  competitorPeriod1 : BitVec 16
  solicitorPeriod1 : BitVec 16
  modCxlBy1 : Alpha 1
  filler9 : Alpha 1
  reasonCode1 : BitVec 16
  startAlpha1 : Alpha 2
  endAlpha1 : Alpha 2
  token1 : BitVec 32
  contractDesc : ContractDesc
  opBrokerId1 : Alpha 5
  fillerx1 : Alpha 1
  fillerOptions1 : Alpha 3
  fillery1 : Alpha 1
  orderType1 : BitVec 16
  orderNumber1 : Alpha 8
  accountNumber1 : Alpha 10
  bookType1 : BitVec 16
  buySell1 : BitVec 16
  disclosedVol1 : BitVec 32
  disclosedVolRemaining1 : BitVec 32
  totalVolRemaining1 : BitVec 32
  volume1 : BitVec 32
  volumeFilledToday1 : BitVec 32
  price1 : BitVec 32
  triggerPrice1 : BitVec 32
  goodTillDate1 : BitVec 32
  entryDateTime1 : BitVec 32
  minFillAon1 : BitVec 32
  lastModified1 : BitVec 32
  stOrderFlags : BitVec 16
  branchId1 : BitVec 16
  traderId1 : BitVec 32
  brokerId1 : Alpha 5
  cOrdFiller : Alpha 24
  openClose1 : Alpha 1
  settlor1 : Alpha 12
  proClient1 : BitVec 16
  settlementPeriod1 : BitVec 16
  additionalOrderFlags : BitVec 8
  reserved1 : Alpha 1
  reserved2 : Alpha 2
  filler17 : Alpha 1
  filler18 : Alpha 1
  nnfField : Alpha 8
  mktReplay : BitVec 64
  pan : Alpha 10
  algoId : BitVec 32
  secondReserved2 : Alpha 2
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  priceDiff : BitVec 32
  msSpdLegInfoLeg2 : MsSpdLegInfoLeg2
  msSpdLegInfoLeg3 : MsSpdLegInfoLeg3
  deriving DecidableEq, Repr

namespace SpBoardLotInMessage

def encode (message : SpBoardLotInMessage) : List UInt8 :=
  Alpha.encode message.participantType1
    ++ (Alpha.encode message.filler1
    ++ (encodeUInt 2 message.competitorPeriod1
    ++ (encodeUInt 2 message.solicitorPeriod1
    ++ (Alpha.encode message.modCxlBy1
    ++ (Alpha.encode message.filler9
    ++ (encodeUInt 2 message.reasonCode1
    ++ (Alpha.encode message.startAlpha1
    ++ (Alpha.encode message.endAlpha1
    ++ (encodeUInt 4 message.token1
    ++ (ContractDesc.encode message.contractDesc
    ++ (Alpha.encode message.opBrokerId1
    ++ (Alpha.encode message.fillerx1
    ++ (Alpha.encode message.fillerOptions1
    ++ (Alpha.encode message.fillery1
    ++ (encodeUInt 2 message.orderType1
    ++ (Alpha.encode message.orderNumber1
    ++ (Alpha.encode message.accountNumber1
    ++ (encodeUInt 2 message.bookType1
    ++ (encodeUInt 2 message.buySell1
    ++ (encodeUInt 4 message.disclosedVol1
    ++ (encodeUInt 4 message.disclosedVolRemaining1
    ++ (encodeUInt 4 message.totalVolRemaining1
    ++ (encodeUInt 4 message.volume1
    ++ (encodeUInt 4 message.volumeFilledToday1
    ++ (encodeUInt 4 message.price1
    ++ (encodeUInt 4 message.triggerPrice1
    ++ (encodeUInt 4 message.goodTillDate1
    ++ (encodeUInt 4 message.entryDateTime1
    ++ (encodeUInt 4 message.minFillAon1
    ++ (encodeUInt 4 message.lastModified1
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId1
    ++ (encodeUInt 4 message.traderId1
    ++ (Alpha.encode message.brokerId1
    ++ (Alpha.encode message.cOrdFiller
    ++ (Alpha.encode message.openClose1
    ++ (Alpha.encode message.settlor1
    ++ (encodeUInt 2 message.proClient1
    ++ (encodeUInt 2 message.settlementPeriod1
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.reserved1
    ++ (Alpha.encode message.reserved2
    ++ (Alpha.encode message.filler17
    ++ (Alpha.encode message.filler18
    ++ (Alpha.encode message.nnfField
    ++ (encodeUInt 8 message.mktReplay
    ++ (Alpha.encode message.pan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.secondReserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52
    ++ (encodeUInt 4 message.priceDiff
    ++ (MsSpdLegInfoLeg2.encode message.msSpdLegInfoLeg2
    ++ (MsSpdLegInfoLeg3.encode message.msSpdLegInfoLeg3))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SpBoardLotInMessage × List UInt8) := do
  let (participantType1, bytes) ← Alpha.decode 1 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod1, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod1, bytes) ← decodeUInt 2 bytes
  let (modCxlBy1, bytes) ← Alpha.decode 1 bytes
  let (filler9, bytes) ← Alpha.decode 1 bytes
  let (reasonCode1, bytes) ← decodeUInt 2 bytes
  let (startAlpha1, bytes) ← Alpha.decode 2 bytes
  let (endAlpha1, bytes) ← Alpha.decode 2 bytes
  let (token1, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (opBrokerId1, bytes) ← Alpha.decode 5 bytes
  let (fillerx1, bytes) ← Alpha.decode 1 bytes
  let (fillerOptions1, bytes) ← Alpha.decode 3 bytes
  let (fillery1, bytes) ← Alpha.decode 1 bytes
  let (orderType1, bytes) ← decodeUInt 2 bytes
  let (orderNumber1, bytes) ← Alpha.decode 8 bytes
  let (accountNumber1, bytes) ← Alpha.decode 10 bytes
  let (bookType1, bytes) ← decodeUInt 2 bytes
  let (buySell1, bytes) ← decodeUInt 2 bytes
  let (disclosedVol1, bytes) ← decodeUInt 4 bytes
  let (disclosedVolRemaining1, bytes) ← decodeUInt 4 bytes
  let (totalVolRemaining1, bytes) ← decodeUInt 4 bytes
  let (volume1, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday1, bytes) ← decodeUInt 4 bytes
  let (price1, bytes) ← decodeUInt 4 bytes
  let (triggerPrice1, bytes) ← decodeUInt 4 bytes
  let (goodTillDate1, bytes) ← decodeUInt 4 bytes
  let (entryDateTime1, bytes) ← decodeUInt 4 bytes
  let (minFillAon1, bytes) ← decodeUInt 4 bytes
  let (lastModified1, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId1, bytes) ← decodeUInt 2 bytes
  let (traderId1, bytes) ← decodeUInt 4 bytes
  let (brokerId1, bytes) ← Alpha.decode 5 bytes
  let (cOrdFiller, bytes) ← Alpha.decode 24 bytes
  let (openClose1, bytes) ← Alpha.decode 1 bytes
  let (settlor1, bytes) ← Alpha.decode 12 bytes
  let (proClient1, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod1, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (filler17, bytes) ← Alpha.decode 1 bytes
  let (filler18, bytes) ← Alpha.decode 1 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← decodeUInt 8 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (secondReserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  let (priceDiff, bytes) ← decodeUInt 4 bytes
  let (msSpdLegInfoLeg2, bytes) ← MsSpdLegInfoLeg2.decode bytes
  let (msSpdLegInfoLeg3, bytes) ← MsSpdLegInfoLeg3.decode bytes
  pure ({ participantType1, filler1, competitorPeriod1, solicitorPeriod1, modCxlBy1, filler9, reasonCode1, startAlpha1, endAlpha1, token1, contractDesc, opBrokerId1, fillerx1, fillerOptions1, fillery1, orderType1, orderNumber1, accountNumber1, bookType1, buySell1, disclosedVol1, disclosedVolRemaining1, totalVolRemaining1, volume1, volumeFilledToday1, price1, triggerPrice1, goodTillDate1, entryDateTime1, minFillAon1, lastModified1, stOrderFlags, branchId1, traderId1, brokerId1, cOrdFiller, openClose1, settlor1, proClient1, settlementPeriod1, additionalOrderFlags, reserved1, reserved2, filler17, filler18, nnfField, mktReplay, pan, algoId, secondReserved2, lastActivityReference, reserved52, priceDiff, msSpdLegInfoLeg2, msSpdLegInfoLeg3 }, bytes)

@[simp] theorem encode_length (message : SpBoardLotInMessage) : (encode message).length = 440 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, encodeUIntLE_length, MsSpdLegInfoLeg2.encode_length, MsSpdLegInfoLeg3.encode_length]

theorem encode_length_pos (message : SpBoardLotInMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SpBoardLotInMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MsSpdLegInfoLeg2.decode_encode, some_bind]
  dsimp only
  rw [MsSpdLegInfoLeg3.decode_encode, some_bind]
  rfl

end SpBoardLotInMessage

/-- Twol Board Lot In Message: 440 bytes -/
structure TwolBoardLotInMessage where
  participantType1 : Alpha 1
  filler1 : Alpha 1
  competitorPeriod1 : BitVec 16
  solicitorPeriod1 : BitVec 16
  modCxlBy1 : Alpha 1
  filler9 : Alpha 1
  reasonCode1 : BitVec 16
  startAlpha1 : Alpha 2
  endAlpha1 : Alpha 2
  token1 : BitVec 32
  contractDesc : ContractDesc
  opBrokerId1 : Alpha 5
  fillerx1 : Alpha 1
  fillerOptions1 : Alpha 3
  fillery1 : Alpha 1
  orderType1 : BitVec 16
  orderNumber1 : Alpha 8
  accountNumber1 : Alpha 10
  bookType1 : BitVec 16
  buySell1 : BitVec 16
  disclosedVol1 : BitVec 32
  disclosedVolRemaining1 : BitVec 32
  totalVolRemaining1 : BitVec 32
  volume1 : BitVec 32
  volumeFilledToday1 : BitVec 32
  price1 : BitVec 32
  triggerPrice1 : BitVec 32
  goodTillDate1 : BitVec 32
  entryDateTime1 : BitVec 32
  minFillAon1 : BitVec 32
  lastModified1 : BitVec 32
  stOrderFlags : BitVec 16
  branchId1 : BitVec 16
  traderId1 : BitVec 32
  brokerId1 : Alpha 5
  cOrdFiller : Alpha 24
  openClose1 : Alpha 1
  settlor1 : Alpha 12
  proClient1 : BitVec 16
  settlementPeriod1 : BitVec 16
  additionalOrderFlags : BitVec 8
  reserved1 : Alpha 1
  reserved2 : Alpha 2
  filler17 : Alpha 1
  filler18 : Alpha 1
  nnfField : Alpha 8
  mktReplay : BitVec 64
  pan : Alpha 10
  algoId : BitVec 32
  secondReserved2 : Alpha 2
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  priceDiff : BitVec 32
  msSpdLegInfoLeg2 : MsSpdLegInfoLeg2
  msSpdLegInfoLeg3 : MsSpdLegInfoLeg3
  deriving DecidableEq, Repr

namespace TwolBoardLotInMessage

def encode (message : TwolBoardLotInMessage) : List UInt8 :=
  Alpha.encode message.participantType1
    ++ (Alpha.encode message.filler1
    ++ (encodeUInt 2 message.competitorPeriod1
    ++ (encodeUInt 2 message.solicitorPeriod1
    ++ (Alpha.encode message.modCxlBy1
    ++ (Alpha.encode message.filler9
    ++ (encodeUInt 2 message.reasonCode1
    ++ (Alpha.encode message.startAlpha1
    ++ (Alpha.encode message.endAlpha1
    ++ (encodeUInt 4 message.token1
    ++ (ContractDesc.encode message.contractDesc
    ++ (Alpha.encode message.opBrokerId1
    ++ (Alpha.encode message.fillerx1
    ++ (Alpha.encode message.fillerOptions1
    ++ (Alpha.encode message.fillery1
    ++ (encodeUInt 2 message.orderType1
    ++ (Alpha.encode message.orderNumber1
    ++ (Alpha.encode message.accountNumber1
    ++ (encodeUInt 2 message.bookType1
    ++ (encodeUInt 2 message.buySell1
    ++ (encodeUInt 4 message.disclosedVol1
    ++ (encodeUInt 4 message.disclosedVolRemaining1
    ++ (encodeUInt 4 message.totalVolRemaining1
    ++ (encodeUInt 4 message.volume1
    ++ (encodeUInt 4 message.volumeFilledToday1
    ++ (encodeUInt 4 message.price1
    ++ (encodeUInt 4 message.triggerPrice1
    ++ (encodeUInt 4 message.goodTillDate1
    ++ (encodeUInt 4 message.entryDateTime1
    ++ (encodeUInt 4 message.minFillAon1
    ++ (encodeUInt 4 message.lastModified1
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId1
    ++ (encodeUInt 4 message.traderId1
    ++ (Alpha.encode message.brokerId1
    ++ (Alpha.encode message.cOrdFiller
    ++ (Alpha.encode message.openClose1
    ++ (Alpha.encode message.settlor1
    ++ (encodeUInt 2 message.proClient1
    ++ (encodeUInt 2 message.settlementPeriod1
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.reserved1
    ++ (Alpha.encode message.reserved2
    ++ (Alpha.encode message.filler17
    ++ (Alpha.encode message.filler18
    ++ (Alpha.encode message.nnfField
    ++ (encodeUInt 8 message.mktReplay
    ++ (Alpha.encode message.pan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.secondReserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52
    ++ (encodeUInt 4 message.priceDiff
    ++ (MsSpdLegInfoLeg2.encode message.msSpdLegInfoLeg2
    ++ (MsSpdLegInfoLeg3.encode message.msSpdLegInfoLeg3))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TwolBoardLotInMessage × List UInt8) := do
  let (participantType1, bytes) ← Alpha.decode 1 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod1, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod1, bytes) ← decodeUInt 2 bytes
  let (modCxlBy1, bytes) ← Alpha.decode 1 bytes
  let (filler9, bytes) ← Alpha.decode 1 bytes
  let (reasonCode1, bytes) ← decodeUInt 2 bytes
  let (startAlpha1, bytes) ← Alpha.decode 2 bytes
  let (endAlpha1, bytes) ← Alpha.decode 2 bytes
  let (token1, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (opBrokerId1, bytes) ← Alpha.decode 5 bytes
  let (fillerx1, bytes) ← Alpha.decode 1 bytes
  let (fillerOptions1, bytes) ← Alpha.decode 3 bytes
  let (fillery1, bytes) ← Alpha.decode 1 bytes
  let (orderType1, bytes) ← decodeUInt 2 bytes
  let (orderNumber1, bytes) ← Alpha.decode 8 bytes
  let (accountNumber1, bytes) ← Alpha.decode 10 bytes
  let (bookType1, bytes) ← decodeUInt 2 bytes
  let (buySell1, bytes) ← decodeUInt 2 bytes
  let (disclosedVol1, bytes) ← decodeUInt 4 bytes
  let (disclosedVolRemaining1, bytes) ← decodeUInt 4 bytes
  let (totalVolRemaining1, bytes) ← decodeUInt 4 bytes
  let (volume1, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday1, bytes) ← decodeUInt 4 bytes
  let (price1, bytes) ← decodeUInt 4 bytes
  let (triggerPrice1, bytes) ← decodeUInt 4 bytes
  let (goodTillDate1, bytes) ← decodeUInt 4 bytes
  let (entryDateTime1, bytes) ← decodeUInt 4 bytes
  let (minFillAon1, bytes) ← decodeUInt 4 bytes
  let (lastModified1, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId1, bytes) ← decodeUInt 2 bytes
  let (traderId1, bytes) ← decodeUInt 4 bytes
  let (brokerId1, bytes) ← Alpha.decode 5 bytes
  let (cOrdFiller, bytes) ← Alpha.decode 24 bytes
  let (openClose1, bytes) ← Alpha.decode 1 bytes
  let (settlor1, bytes) ← Alpha.decode 12 bytes
  let (proClient1, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod1, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (filler17, bytes) ← Alpha.decode 1 bytes
  let (filler18, bytes) ← Alpha.decode 1 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← decodeUInt 8 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (secondReserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  let (priceDiff, bytes) ← decodeUInt 4 bytes
  let (msSpdLegInfoLeg2, bytes) ← MsSpdLegInfoLeg2.decode bytes
  let (msSpdLegInfoLeg3, bytes) ← MsSpdLegInfoLeg3.decode bytes
  pure ({ participantType1, filler1, competitorPeriod1, solicitorPeriod1, modCxlBy1, filler9, reasonCode1, startAlpha1, endAlpha1, token1, contractDesc, opBrokerId1, fillerx1, fillerOptions1, fillery1, orderType1, orderNumber1, accountNumber1, bookType1, buySell1, disclosedVol1, disclosedVolRemaining1, totalVolRemaining1, volume1, volumeFilledToday1, price1, triggerPrice1, goodTillDate1, entryDateTime1, minFillAon1, lastModified1, stOrderFlags, branchId1, traderId1, brokerId1, cOrdFiller, openClose1, settlor1, proClient1, settlementPeriod1, additionalOrderFlags, reserved1, reserved2, filler17, filler18, nnfField, mktReplay, pan, algoId, secondReserved2, lastActivityReference, reserved52, priceDiff, msSpdLegInfoLeg2, msSpdLegInfoLeg3 }, bytes)

@[simp] theorem encode_length (message : TwolBoardLotInMessage) : (encode message).length = 440 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, encodeUIntLE_length, MsSpdLegInfoLeg2.encode_length, MsSpdLegInfoLeg3.encode_length]

theorem encode_length_pos (message : TwolBoardLotInMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : TwolBoardLotInMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MsSpdLegInfoLeg2.decode_encode, some_bind]
  dsimp only
  rw [MsSpdLegInfoLeg3.decode_encode, some_bind]
  rfl

end TwolBoardLotInMessage

/-- Thrl Board Lot In Message: 440 bytes -/
structure ThrlBoardLotInMessage where
  participantType1 : Alpha 1
  filler1 : Alpha 1
  competitorPeriod1 : BitVec 16
  solicitorPeriod1 : BitVec 16
  modCxlBy1 : Alpha 1
  filler9 : Alpha 1
  reasonCode1 : BitVec 16
  startAlpha1 : Alpha 2
  endAlpha1 : Alpha 2
  token1 : BitVec 32
  contractDesc : ContractDesc
  opBrokerId1 : Alpha 5
  fillerx1 : Alpha 1
  fillerOptions1 : Alpha 3
  fillery1 : Alpha 1
  orderType1 : BitVec 16
  orderNumber1 : Alpha 8
  accountNumber1 : Alpha 10
  bookType1 : BitVec 16
  buySell1 : BitVec 16
  disclosedVol1 : BitVec 32
  disclosedVolRemaining1 : BitVec 32
  totalVolRemaining1 : BitVec 32
  volume1 : BitVec 32
  volumeFilledToday1 : BitVec 32
  price1 : BitVec 32
  triggerPrice1 : BitVec 32
  goodTillDate1 : BitVec 32
  entryDateTime1 : BitVec 32
  minFillAon1 : BitVec 32
  lastModified1 : BitVec 32
  stOrderFlags : BitVec 16
  branchId1 : BitVec 16
  traderId1 : BitVec 32
  brokerId1 : Alpha 5
  cOrdFiller : Alpha 24
  openClose1 : Alpha 1
  settlor1 : Alpha 12
  proClient1 : BitVec 16
  settlementPeriod1 : BitVec 16
  additionalOrderFlags : BitVec 8
  reserved1 : Alpha 1
  reserved2 : Alpha 2
  filler17 : Alpha 1
  filler18 : Alpha 1
  nnfField : Alpha 8
  mktReplay : BitVec 64
  pan : Alpha 10
  algoId : BitVec 32
  secondReserved2 : Alpha 2
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  priceDiff : BitVec 32
  msSpdLegInfoLeg2 : MsSpdLegInfoLeg2
  msSpdLegInfoLeg3 : MsSpdLegInfoLeg3
  deriving DecidableEq, Repr

namespace ThrlBoardLotInMessage

def encode (message : ThrlBoardLotInMessage) : List UInt8 :=
  Alpha.encode message.participantType1
    ++ (Alpha.encode message.filler1
    ++ (encodeUInt 2 message.competitorPeriod1
    ++ (encodeUInt 2 message.solicitorPeriod1
    ++ (Alpha.encode message.modCxlBy1
    ++ (Alpha.encode message.filler9
    ++ (encodeUInt 2 message.reasonCode1
    ++ (Alpha.encode message.startAlpha1
    ++ (Alpha.encode message.endAlpha1
    ++ (encodeUInt 4 message.token1
    ++ (ContractDesc.encode message.contractDesc
    ++ (Alpha.encode message.opBrokerId1
    ++ (Alpha.encode message.fillerx1
    ++ (Alpha.encode message.fillerOptions1
    ++ (Alpha.encode message.fillery1
    ++ (encodeUInt 2 message.orderType1
    ++ (Alpha.encode message.orderNumber1
    ++ (Alpha.encode message.accountNumber1
    ++ (encodeUInt 2 message.bookType1
    ++ (encodeUInt 2 message.buySell1
    ++ (encodeUInt 4 message.disclosedVol1
    ++ (encodeUInt 4 message.disclosedVolRemaining1
    ++ (encodeUInt 4 message.totalVolRemaining1
    ++ (encodeUInt 4 message.volume1
    ++ (encodeUInt 4 message.volumeFilledToday1
    ++ (encodeUInt 4 message.price1
    ++ (encodeUInt 4 message.triggerPrice1
    ++ (encodeUInt 4 message.goodTillDate1
    ++ (encodeUInt 4 message.entryDateTime1
    ++ (encodeUInt 4 message.minFillAon1
    ++ (encodeUInt 4 message.lastModified1
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId1
    ++ (encodeUInt 4 message.traderId1
    ++ (Alpha.encode message.brokerId1
    ++ (Alpha.encode message.cOrdFiller
    ++ (Alpha.encode message.openClose1
    ++ (Alpha.encode message.settlor1
    ++ (encodeUInt 2 message.proClient1
    ++ (encodeUInt 2 message.settlementPeriod1
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.reserved1
    ++ (Alpha.encode message.reserved2
    ++ (Alpha.encode message.filler17
    ++ (Alpha.encode message.filler18
    ++ (Alpha.encode message.nnfField
    ++ (encodeUInt 8 message.mktReplay
    ++ (Alpha.encode message.pan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.secondReserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52
    ++ (encodeUInt 4 message.priceDiff
    ++ (MsSpdLegInfoLeg2.encode message.msSpdLegInfoLeg2
    ++ (MsSpdLegInfoLeg3.encode message.msSpdLegInfoLeg3))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ThrlBoardLotInMessage × List UInt8) := do
  let (participantType1, bytes) ← Alpha.decode 1 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod1, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod1, bytes) ← decodeUInt 2 bytes
  let (modCxlBy1, bytes) ← Alpha.decode 1 bytes
  let (filler9, bytes) ← Alpha.decode 1 bytes
  let (reasonCode1, bytes) ← decodeUInt 2 bytes
  let (startAlpha1, bytes) ← Alpha.decode 2 bytes
  let (endAlpha1, bytes) ← Alpha.decode 2 bytes
  let (token1, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (opBrokerId1, bytes) ← Alpha.decode 5 bytes
  let (fillerx1, bytes) ← Alpha.decode 1 bytes
  let (fillerOptions1, bytes) ← Alpha.decode 3 bytes
  let (fillery1, bytes) ← Alpha.decode 1 bytes
  let (orderType1, bytes) ← decodeUInt 2 bytes
  let (orderNumber1, bytes) ← Alpha.decode 8 bytes
  let (accountNumber1, bytes) ← Alpha.decode 10 bytes
  let (bookType1, bytes) ← decodeUInt 2 bytes
  let (buySell1, bytes) ← decodeUInt 2 bytes
  let (disclosedVol1, bytes) ← decodeUInt 4 bytes
  let (disclosedVolRemaining1, bytes) ← decodeUInt 4 bytes
  let (totalVolRemaining1, bytes) ← decodeUInt 4 bytes
  let (volume1, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday1, bytes) ← decodeUInt 4 bytes
  let (price1, bytes) ← decodeUInt 4 bytes
  let (triggerPrice1, bytes) ← decodeUInt 4 bytes
  let (goodTillDate1, bytes) ← decodeUInt 4 bytes
  let (entryDateTime1, bytes) ← decodeUInt 4 bytes
  let (minFillAon1, bytes) ← decodeUInt 4 bytes
  let (lastModified1, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId1, bytes) ← decodeUInt 2 bytes
  let (traderId1, bytes) ← decodeUInt 4 bytes
  let (brokerId1, bytes) ← Alpha.decode 5 bytes
  let (cOrdFiller, bytes) ← Alpha.decode 24 bytes
  let (openClose1, bytes) ← Alpha.decode 1 bytes
  let (settlor1, bytes) ← Alpha.decode 12 bytes
  let (proClient1, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod1, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (filler17, bytes) ← Alpha.decode 1 bytes
  let (filler18, bytes) ← Alpha.decode 1 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← decodeUInt 8 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (secondReserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  let (priceDiff, bytes) ← decodeUInt 4 bytes
  let (msSpdLegInfoLeg2, bytes) ← MsSpdLegInfoLeg2.decode bytes
  let (msSpdLegInfoLeg3, bytes) ← MsSpdLegInfoLeg3.decode bytes
  pure ({ participantType1, filler1, competitorPeriod1, solicitorPeriod1, modCxlBy1, filler9, reasonCode1, startAlpha1, endAlpha1, token1, contractDesc, opBrokerId1, fillerx1, fillerOptions1, fillery1, orderType1, orderNumber1, accountNumber1, bookType1, buySell1, disclosedVol1, disclosedVolRemaining1, totalVolRemaining1, volume1, volumeFilledToday1, price1, triggerPrice1, goodTillDate1, entryDateTime1, minFillAon1, lastModified1, stOrderFlags, branchId1, traderId1, brokerId1, cOrdFiller, openClose1, settlor1, proClient1, settlementPeriod1, additionalOrderFlags, reserved1, reserved2, filler17, filler18, nnfField, mktReplay, pan, algoId, secondReserved2, lastActivityReference, reserved52, priceDiff, msSpdLegInfoLeg2, msSpdLegInfoLeg3 }, bytes)

@[simp] theorem encode_length (message : ThrlBoardLotInMessage) : (encode message).length = 440 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, encodeUIntLE_length, MsSpdLegInfoLeg2.encode_length, MsSpdLegInfoLeg3.encode_length]

theorem encode_length_pos (message : ThrlBoardLotInMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ThrlBoardLotInMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MsSpdLegInfoLeg2.decode_encode, some_bind]
  dsimp only
  rw [MsSpdLegInfoLeg3.decode_encode, some_bind]
  rfl

end ThrlBoardLotInMessage

/-- Sp Order Cancel In Message: 440 bytes -/
structure SpOrderCancelInMessage where
  participantType1 : Alpha 1
  filler1 : Alpha 1
  competitorPeriod1 : BitVec 16
  solicitorPeriod1 : BitVec 16
  modCxlBy1 : Alpha 1
  filler9 : Alpha 1
  reasonCode1 : BitVec 16
  startAlpha1 : Alpha 2
  endAlpha1 : Alpha 2
  token1 : BitVec 32
  contractDesc : ContractDesc
  opBrokerId1 : Alpha 5
  fillerx1 : Alpha 1
  fillerOptions1 : Alpha 3
  fillery1 : Alpha 1
  orderType1 : BitVec 16
  orderNumber1 : Alpha 8
  accountNumber1 : Alpha 10
  bookType1 : BitVec 16
  buySell1 : BitVec 16
  disclosedVol1 : BitVec 32
  disclosedVolRemaining1 : BitVec 32
  totalVolRemaining1 : BitVec 32
  volume1 : BitVec 32
  volumeFilledToday1 : BitVec 32
  price1 : BitVec 32
  triggerPrice1 : BitVec 32
  goodTillDate1 : BitVec 32
  entryDateTime1 : BitVec 32
  minFillAon1 : BitVec 32
  lastModified1 : BitVec 32
  stOrderFlags : BitVec 16
  branchId1 : BitVec 16
  traderId1 : BitVec 32
  brokerId1 : Alpha 5
  cOrdFiller : Alpha 24
  openClose1 : Alpha 1
  settlor1 : Alpha 12
  proClient1 : BitVec 16
  settlementPeriod1 : BitVec 16
  additionalOrderFlags : BitVec 8
  reserved1 : Alpha 1
  reserved2 : Alpha 2
  filler17 : Alpha 1
  filler18 : Alpha 1
  nnfField : Alpha 8
  mktReplay : BitVec 64
  pan : Alpha 10
  algoId : BitVec 32
  secondReserved2 : Alpha 2
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  priceDiff : BitVec 32
  msSpdLegInfoLeg2 : MsSpdLegInfoLeg2
  msSpdLegInfoLeg3 : MsSpdLegInfoLeg3
  deriving DecidableEq, Repr

namespace SpOrderCancelInMessage

def encode (message : SpOrderCancelInMessage) : List UInt8 :=
  Alpha.encode message.participantType1
    ++ (Alpha.encode message.filler1
    ++ (encodeUInt 2 message.competitorPeriod1
    ++ (encodeUInt 2 message.solicitorPeriod1
    ++ (Alpha.encode message.modCxlBy1
    ++ (Alpha.encode message.filler9
    ++ (encodeUInt 2 message.reasonCode1
    ++ (Alpha.encode message.startAlpha1
    ++ (Alpha.encode message.endAlpha1
    ++ (encodeUInt 4 message.token1
    ++ (ContractDesc.encode message.contractDesc
    ++ (Alpha.encode message.opBrokerId1
    ++ (Alpha.encode message.fillerx1
    ++ (Alpha.encode message.fillerOptions1
    ++ (Alpha.encode message.fillery1
    ++ (encodeUInt 2 message.orderType1
    ++ (Alpha.encode message.orderNumber1
    ++ (Alpha.encode message.accountNumber1
    ++ (encodeUInt 2 message.bookType1
    ++ (encodeUInt 2 message.buySell1
    ++ (encodeUInt 4 message.disclosedVol1
    ++ (encodeUInt 4 message.disclosedVolRemaining1
    ++ (encodeUInt 4 message.totalVolRemaining1
    ++ (encodeUInt 4 message.volume1
    ++ (encodeUInt 4 message.volumeFilledToday1
    ++ (encodeUInt 4 message.price1
    ++ (encodeUInt 4 message.triggerPrice1
    ++ (encodeUInt 4 message.goodTillDate1
    ++ (encodeUInt 4 message.entryDateTime1
    ++ (encodeUInt 4 message.minFillAon1
    ++ (encodeUInt 4 message.lastModified1
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId1
    ++ (encodeUInt 4 message.traderId1
    ++ (Alpha.encode message.brokerId1
    ++ (Alpha.encode message.cOrdFiller
    ++ (Alpha.encode message.openClose1
    ++ (Alpha.encode message.settlor1
    ++ (encodeUInt 2 message.proClient1
    ++ (encodeUInt 2 message.settlementPeriod1
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.reserved1
    ++ (Alpha.encode message.reserved2
    ++ (Alpha.encode message.filler17
    ++ (Alpha.encode message.filler18
    ++ (Alpha.encode message.nnfField
    ++ (encodeUInt 8 message.mktReplay
    ++ (Alpha.encode message.pan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.secondReserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52
    ++ (encodeUInt 4 message.priceDiff
    ++ (MsSpdLegInfoLeg2.encode message.msSpdLegInfoLeg2
    ++ (MsSpdLegInfoLeg3.encode message.msSpdLegInfoLeg3))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SpOrderCancelInMessage × List UInt8) := do
  let (participantType1, bytes) ← Alpha.decode 1 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod1, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod1, bytes) ← decodeUInt 2 bytes
  let (modCxlBy1, bytes) ← Alpha.decode 1 bytes
  let (filler9, bytes) ← Alpha.decode 1 bytes
  let (reasonCode1, bytes) ← decodeUInt 2 bytes
  let (startAlpha1, bytes) ← Alpha.decode 2 bytes
  let (endAlpha1, bytes) ← Alpha.decode 2 bytes
  let (token1, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (opBrokerId1, bytes) ← Alpha.decode 5 bytes
  let (fillerx1, bytes) ← Alpha.decode 1 bytes
  let (fillerOptions1, bytes) ← Alpha.decode 3 bytes
  let (fillery1, bytes) ← Alpha.decode 1 bytes
  let (orderType1, bytes) ← decodeUInt 2 bytes
  let (orderNumber1, bytes) ← Alpha.decode 8 bytes
  let (accountNumber1, bytes) ← Alpha.decode 10 bytes
  let (bookType1, bytes) ← decodeUInt 2 bytes
  let (buySell1, bytes) ← decodeUInt 2 bytes
  let (disclosedVol1, bytes) ← decodeUInt 4 bytes
  let (disclosedVolRemaining1, bytes) ← decodeUInt 4 bytes
  let (totalVolRemaining1, bytes) ← decodeUInt 4 bytes
  let (volume1, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday1, bytes) ← decodeUInt 4 bytes
  let (price1, bytes) ← decodeUInt 4 bytes
  let (triggerPrice1, bytes) ← decodeUInt 4 bytes
  let (goodTillDate1, bytes) ← decodeUInt 4 bytes
  let (entryDateTime1, bytes) ← decodeUInt 4 bytes
  let (minFillAon1, bytes) ← decodeUInt 4 bytes
  let (lastModified1, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId1, bytes) ← decodeUInt 2 bytes
  let (traderId1, bytes) ← decodeUInt 4 bytes
  let (brokerId1, bytes) ← Alpha.decode 5 bytes
  let (cOrdFiller, bytes) ← Alpha.decode 24 bytes
  let (openClose1, bytes) ← Alpha.decode 1 bytes
  let (settlor1, bytes) ← Alpha.decode 12 bytes
  let (proClient1, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod1, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (filler17, bytes) ← Alpha.decode 1 bytes
  let (filler18, bytes) ← Alpha.decode 1 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← decodeUInt 8 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (secondReserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  let (priceDiff, bytes) ← decodeUInt 4 bytes
  let (msSpdLegInfoLeg2, bytes) ← MsSpdLegInfoLeg2.decode bytes
  let (msSpdLegInfoLeg3, bytes) ← MsSpdLegInfoLeg3.decode bytes
  pure ({ participantType1, filler1, competitorPeriod1, solicitorPeriod1, modCxlBy1, filler9, reasonCode1, startAlpha1, endAlpha1, token1, contractDesc, opBrokerId1, fillerx1, fillerOptions1, fillery1, orderType1, orderNumber1, accountNumber1, bookType1, buySell1, disclosedVol1, disclosedVolRemaining1, totalVolRemaining1, volume1, volumeFilledToday1, price1, triggerPrice1, goodTillDate1, entryDateTime1, minFillAon1, lastModified1, stOrderFlags, branchId1, traderId1, brokerId1, cOrdFiller, openClose1, settlor1, proClient1, settlementPeriod1, additionalOrderFlags, reserved1, reserved2, filler17, filler18, nnfField, mktReplay, pan, algoId, secondReserved2, lastActivityReference, reserved52, priceDiff, msSpdLegInfoLeg2, msSpdLegInfoLeg3 }, bytes)

@[simp] theorem encode_length (message : SpOrderCancelInMessage) : (encode message).length = 440 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, encodeUIntLE_length, MsSpdLegInfoLeg2.encode_length, MsSpdLegInfoLeg3.encode_length]

theorem encode_length_pos (message : SpOrderCancelInMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SpOrderCancelInMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MsSpdLegInfoLeg2.decode_encode, some_bind]
  dsimp only
  rw [MsSpdLegInfoLeg3.decode_encode, some_bind]
  rfl

end SpOrderCancelInMessage

/-- Sp Order Mod In Message: 440 bytes -/
structure SpOrderModInMessage where
  participantType1 : Alpha 1
  filler1 : Alpha 1
  competitorPeriod1 : BitVec 16
  solicitorPeriod1 : BitVec 16
  modCxlBy1 : Alpha 1
  filler9 : Alpha 1
  reasonCode1 : BitVec 16
  startAlpha1 : Alpha 2
  endAlpha1 : Alpha 2
  token1 : BitVec 32
  contractDesc : ContractDesc
  opBrokerId1 : Alpha 5
  fillerx1 : Alpha 1
  fillerOptions1 : Alpha 3
  fillery1 : Alpha 1
  orderType1 : BitVec 16
  orderNumber1 : Alpha 8
  accountNumber1 : Alpha 10
  bookType1 : BitVec 16
  buySell1 : BitVec 16
  disclosedVol1 : BitVec 32
  disclosedVolRemaining1 : BitVec 32
  totalVolRemaining1 : BitVec 32
  volume1 : BitVec 32
  volumeFilledToday1 : BitVec 32
  price1 : BitVec 32
  triggerPrice1 : BitVec 32
  goodTillDate1 : BitVec 32
  entryDateTime1 : BitVec 32
  minFillAon1 : BitVec 32
  lastModified1 : BitVec 32
  stOrderFlags : BitVec 16
  branchId1 : BitVec 16
  traderId1 : BitVec 32
  brokerId1 : Alpha 5
  cOrdFiller : Alpha 24
  openClose1 : Alpha 1
  settlor1 : Alpha 12
  proClient1 : BitVec 16
  settlementPeriod1 : BitVec 16
  additionalOrderFlags : BitVec 8
  reserved1 : Alpha 1
  reserved2 : Alpha 2
  filler17 : Alpha 1
  filler18 : Alpha 1
  nnfField : Alpha 8
  mktReplay : BitVec 64
  pan : Alpha 10
  algoId : BitVec 32
  secondReserved2 : Alpha 2
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  priceDiff : BitVec 32
  msSpdLegInfoLeg2 : MsSpdLegInfoLeg2
  msSpdLegInfoLeg3 : MsSpdLegInfoLeg3
  deriving DecidableEq, Repr

namespace SpOrderModInMessage

def encode (message : SpOrderModInMessage) : List UInt8 :=
  Alpha.encode message.participantType1
    ++ (Alpha.encode message.filler1
    ++ (encodeUInt 2 message.competitorPeriod1
    ++ (encodeUInt 2 message.solicitorPeriod1
    ++ (Alpha.encode message.modCxlBy1
    ++ (Alpha.encode message.filler9
    ++ (encodeUInt 2 message.reasonCode1
    ++ (Alpha.encode message.startAlpha1
    ++ (Alpha.encode message.endAlpha1
    ++ (encodeUInt 4 message.token1
    ++ (ContractDesc.encode message.contractDesc
    ++ (Alpha.encode message.opBrokerId1
    ++ (Alpha.encode message.fillerx1
    ++ (Alpha.encode message.fillerOptions1
    ++ (Alpha.encode message.fillery1
    ++ (encodeUInt 2 message.orderType1
    ++ (Alpha.encode message.orderNumber1
    ++ (Alpha.encode message.accountNumber1
    ++ (encodeUInt 2 message.bookType1
    ++ (encodeUInt 2 message.buySell1
    ++ (encodeUInt 4 message.disclosedVol1
    ++ (encodeUInt 4 message.disclosedVolRemaining1
    ++ (encodeUInt 4 message.totalVolRemaining1
    ++ (encodeUInt 4 message.volume1
    ++ (encodeUInt 4 message.volumeFilledToday1
    ++ (encodeUInt 4 message.price1
    ++ (encodeUInt 4 message.triggerPrice1
    ++ (encodeUInt 4 message.goodTillDate1
    ++ (encodeUInt 4 message.entryDateTime1
    ++ (encodeUInt 4 message.minFillAon1
    ++ (encodeUInt 4 message.lastModified1
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId1
    ++ (encodeUInt 4 message.traderId1
    ++ (Alpha.encode message.brokerId1
    ++ (Alpha.encode message.cOrdFiller
    ++ (Alpha.encode message.openClose1
    ++ (Alpha.encode message.settlor1
    ++ (encodeUInt 2 message.proClient1
    ++ (encodeUInt 2 message.settlementPeriod1
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.reserved1
    ++ (Alpha.encode message.reserved2
    ++ (Alpha.encode message.filler17
    ++ (Alpha.encode message.filler18
    ++ (Alpha.encode message.nnfField
    ++ (encodeUInt 8 message.mktReplay
    ++ (Alpha.encode message.pan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.secondReserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52
    ++ (encodeUInt 4 message.priceDiff
    ++ (MsSpdLegInfoLeg2.encode message.msSpdLegInfoLeg2
    ++ (MsSpdLegInfoLeg3.encode message.msSpdLegInfoLeg3))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SpOrderModInMessage × List UInt8) := do
  let (participantType1, bytes) ← Alpha.decode 1 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod1, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod1, bytes) ← decodeUInt 2 bytes
  let (modCxlBy1, bytes) ← Alpha.decode 1 bytes
  let (filler9, bytes) ← Alpha.decode 1 bytes
  let (reasonCode1, bytes) ← decodeUInt 2 bytes
  let (startAlpha1, bytes) ← Alpha.decode 2 bytes
  let (endAlpha1, bytes) ← Alpha.decode 2 bytes
  let (token1, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (opBrokerId1, bytes) ← Alpha.decode 5 bytes
  let (fillerx1, bytes) ← Alpha.decode 1 bytes
  let (fillerOptions1, bytes) ← Alpha.decode 3 bytes
  let (fillery1, bytes) ← Alpha.decode 1 bytes
  let (orderType1, bytes) ← decodeUInt 2 bytes
  let (orderNumber1, bytes) ← Alpha.decode 8 bytes
  let (accountNumber1, bytes) ← Alpha.decode 10 bytes
  let (bookType1, bytes) ← decodeUInt 2 bytes
  let (buySell1, bytes) ← decodeUInt 2 bytes
  let (disclosedVol1, bytes) ← decodeUInt 4 bytes
  let (disclosedVolRemaining1, bytes) ← decodeUInt 4 bytes
  let (totalVolRemaining1, bytes) ← decodeUInt 4 bytes
  let (volume1, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday1, bytes) ← decodeUInt 4 bytes
  let (price1, bytes) ← decodeUInt 4 bytes
  let (triggerPrice1, bytes) ← decodeUInt 4 bytes
  let (goodTillDate1, bytes) ← decodeUInt 4 bytes
  let (entryDateTime1, bytes) ← decodeUInt 4 bytes
  let (minFillAon1, bytes) ← decodeUInt 4 bytes
  let (lastModified1, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId1, bytes) ← decodeUInt 2 bytes
  let (traderId1, bytes) ← decodeUInt 4 bytes
  let (brokerId1, bytes) ← Alpha.decode 5 bytes
  let (cOrdFiller, bytes) ← Alpha.decode 24 bytes
  let (openClose1, bytes) ← Alpha.decode 1 bytes
  let (settlor1, bytes) ← Alpha.decode 12 bytes
  let (proClient1, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod1, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (filler17, bytes) ← Alpha.decode 1 bytes
  let (filler18, bytes) ← Alpha.decode 1 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← decodeUInt 8 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (secondReserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  let (priceDiff, bytes) ← decodeUInt 4 bytes
  let (msSpdLegInfoLeg2, bytes) ← MsSpdLegInfoLeg2.decode bytes
  let (msSpdLegInfoLeg3, bytes) ← MsSpdLegInfoLeg3.decode bytes
  pure ({ participantType1, filler1, competitorPeriod1, solicitorPeriod1, modCxlBy1, filler9, reasonCode1, startAlpha1, endAlpha1, token1, contractDesc, opBrokerId1, fillerx1, fillerOptions1, fillery1, orderType1, orderNumber1, accountNumber1, bookType1, buySell1, disclosedVol1, disclosedVolRemaining1, totalVolRemaining1, volume1, volumeFilledToday1, price1, triggerPrice1, goodTillDate1, entryDateTime1, minFillAon1, lastModified1, stOrderFlags, branchId1, traderId1, brokerId1, cOrdFiller, openClose1, settlor1, proClient1, settlementPeriod1, additionalOrderFlags, reserved1, reserved2, filler17, filler18, nnfField, mktReplay, pan, algoId, secondReserved2, lastActivityReference, reserved52, priceDiff, msSpdLegInfoLeg2, msSpdLegInfoLeg3 }, bytes)

@[simp] theorem encode_length (message : SpOrderModInMessage) : (encode message).length = 440 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, encodeUIntLE_length, MsSpdLegInfoLeg2.encode_length, MsSpdLegInfoLeg3.encode_length]

theorem encode_length_pos (message : SpOrderModInMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SpOrderModInMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MsSpdLegInfoLeg2.decode_encode, some_bind]
  dsimp only
  rw [MsSpdLegInfoLeg3.decode_encode, some_bind]
  rfl

end SpOrderModInMessage

/-- Trade Cancel In Message: 194 bytes -/
structure TradeCancelInMessage where
  tokenNo : BitVec 32
  contractDesc : ContractDesc
  fillNumber : BitVec 32
  fillQuantity : BitVec 32
  fillPrice : BitVec 32
  mktType : Alpha 1
  buyOpenClose : Alpha 1
  reserved4 : Alpha 4
  buyBrokerId : Alpha 5
  sellBrokerId : Alpha 5
  traderId : BitVec 32
  requestedBy : Alpha 1
  sellOpenClose : Alpha 1
  buyAccountNumber : Alpha 10
  sellAccountNumber : Alpha 10
  reserved24 : Alpha 24
  reserved2 : Alpha 2
  secondReserved2 : Alpha 2
  buyPan : Alpha 10
  sellPan : Alpha 10
  reserved60 : Alpha 60
  deriving DecidableEq, Repr

namespace TradeCancelInMessage

def encode (message : TradeCancelInMessage) : List UInt8 :=
  encodeUInt 4 message.tokenNo
    ++ (ContractDesc.encode message.contractDesc
    ++ (encodeUInt 4 message.fillNumber
    ++ (encodeUInt 4 message.fillQuantity
    ++ (encodeUInt 4 message.fillPrice
    ++ (Alpha.encode message.mktType
    ++ (Alpha.encode message.buyOpenClose
    ++ (Alpha.encode message.reserved4
    ++ (Alpha.encode message.buyBrokerId
    ++ (Alpha.encode message.sellBrokerId
    ++ (encodeUInt 4 message.traderId
    ++ (Alpha.encode message.requestedBy
    ++ (Alpha.encode message.sellOpenClose
    ++ (Alpha.encode message.buyAccountNumber
    ++ (Alpha.encode message.sellAccountNumber
    ++ (Alpha.encode message.reserved24
    ++ (Alpha.encode message.reserved2
    ++ (Alpha.encode message.secondReserved2
    ++ (Alpha.encode message.buyPan
    ++ (Alpha.encode message.sellPan
    ++ (Alpha.encode message.reserved60))))))))))))))))))))

def decode (bytes : List UInt8) : Option (TradeCancelInMessage × List UInt8) := do
  let (tokenNo, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (fillNumber, bytes) ← decodeUInt 4 bytes
  let (fillQuantity, bytes) ← decodeUInt 4 bytes
  let (fillPrice, bytes) ← decodeUInt 4 bytes
  let (mktType, bytes) ← Alpha.decode 1 bytes
  let (buyOpenClose, bytes) ← Alpha.decode 1 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (buyBrokerId, bytes) ← Alpha.decode 5 bytes
  let (sellBrokerId, bytes) ← Alpha.decode 5 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (requestedBy, bytes) ← Alpha.decode 1 bytes
  let (sellOpenClose, bytes) ← Alpha.decode 1 bytes
  let (buyAccountNumber, bytes) ← Alpha.decode 10 bytes
  let (sellAccountNumber, bytes) ← Alpha.decode 10 bytes
  let (reserved24, bytes) ← Alpha.decode 24 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (secondReserved2, bytes) ← Alpha.decode 2 bytes
  let (buyPan, bytes) ← Alpha.decode 10 bytes
  let (sellPan, bytes) ← Alpha.decode 10 bytes
  let (reserved60, bytes) ← Alpha.decode 60 bytes
  pure ({ tokenNo, contractDesc, fillNumber, fillQuantity, fillPrice, mktType, buyOpenClose, reserved4, buyBrokerId, sellBrokerId, traderId, requestedBy, sellOpenClose, buyAccountNumber, sellAccountNumber, reserved24, reserved2, secondReserved2, buyPan, sellPan, reserved60 }, bytes)

@[simp] theorem encode_length (message : TradeCancelInMessage) : (encode message).length = 194 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, ContractDesc.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : TradeCancelInMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCancelInMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeCancelInMessage

/-- Trade Mod In Message: 194 bytes -/
structure TradeModInMessage where
  tokenNo : BitVec 32
  contractDesc : ContractDesc
  fillNumber : BitVec 32
  fillQuantity : BitVec 32
  fillPrice : BitVec 32
  mktType : Alpha 1
  buyOpenClose : Alpha 1
  reserved4 : Alpha 4
  buyBrokerId : Alpha 5
  sellBrokerId : Alpha 5
  traderId : BitVec 32
  requestedBy : Alpha 1
  sellOpenClose : Alpha 1
  buyAccountNumber : Alpha 10
  sellAccountNumber : Alpha 10
  reserved24 : Alpha 24
  reserved2 : Alpha 2
  secondReserved2 : Alpha 2
  buyPan : Alpha 10
  sellPan : Alpha 10
  reserved60 : Alpha 60
  deriving DecidableEq, Repr

namespace TradeModInMessage

def encode (message : TradeModInMessage) : List UInt8 :=
  encodeUInt 4 message.tokenNo
    ++ (ContractDesc.encode message.contractDesc
    ++ (encodeUInt 4 message.fillNumber
    ++ (encodeUInt 4 message.fillQuantity
    ++ (encodeUInt 4 message.fillPrice
    ++ (Alpha.encode message.mktType
    ++ (Alpha.encode message.buyOpenClose
    ++ (Alpha.encode message.reserved4
    ++ (Alpha.encode message.buyBrokerId
    ++ (Alpha.encode message.sellBrokerId
    ++ (encodeUInt 4 message.traderId
    ++ (Alpha.encode message.requestedBy
    ++ (Alpha.encode message.sellOpenClose
    ++ (Alpha.encode message.buyAccountNumber
    ++ (Alpha.encode message.sellAccountNumber
    ++ (Alpha.encode message.reserved24
    ++ (Alpha.encode message.reserved2
    ++ (Alpha.encode message.secondReserved2
    ++ (Alpha.encode message.buyPan
    ++ (Alpha.encode message.sellPan
    ++ (Alpha.encode message.reserved60))))))))))))))))))))

def decode (bytes : List UInt8) : Option (TradeModInMessage × List UInt8) := do
  let (tokenNo, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (fillNumber, bytes) ← decodeUInt 4 bytes
  let (fillQuantity, bytes) ← decodeUInt 4 bytes
  let (fillPrice, bytes) ← decodeUInt 4 bytes
  let (mktType, bytes) ← Alpha.decode 1 bytes
  let (buyOpenClose, bytes) ← Alpha.decode 1 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (buyBrokerId, bytes) ← Alpha.decode 5 bytes
  let (sellBrokerId, bytes) ← Alpha.decode 5 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (requestedBy, bytes) ← Alpha.decode 1 bytes
  let (sellOpenClose, bytes) ← Alpha.decode 1 bytes
  let (buyAccountNumber, bytes) ← Alpha.decode 10 bytes
  let (sellAccountNumber, bytes) ← Alpha.decode 10 bytes
  let (reserved24, bytes) ← Alpha.decode 24 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (secondReserved2, bytes) ← Alpha.decode 2 bytes
  let (buyPan, bytes) ← Alpha.decode 10 bytes
  let (sellPan, bytes) ← Alpha.decode 10 bytes
  let (reserved60, bytes) ← Alpha.decode 60 bytes
  pure ({ tokenNo, contractDesc, fillNumber, fillQuantity, fillPrice, mktType, buyOpenClose, reserved4, buyBrokerId, sellBrokerId, traderId, requestedBy, sellOpenClose, buyAccountNumber, sellAccountNumber, reserved24, reserved2, secondReserved2, buyPan, sellPan, reserved60 }, bytes)

@[simp] theorem encode_length (message : TradeModInMessage) : (encode message).length = 194 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, ContractDesc.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : TradeModInMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeModInMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeModInMessage

/-- Sign On Request In Message: 238 bytes -/
structure SignOnRequestInMessage where
  userId : BitVec 32
  reserved8 : Alpha 8
  password : Alpha 8
  secondReserved8 : Alpha 8
  newPassword : Alpha 8
  traderName : Alpha 26
  lastPasswordChangeDate : BitVec 32
  brokerId : Alpha 5
  reserved1 : Alpha 1
  branchId : BitVec 16
  versionNumber : BitVec 32
  batch2StartTime : BitVec 32
  hostSwitchContext : Alpha 1
  colour : Alpha 50
  secondReserved1 : Alpha 1
  userType : BitVec 16
  sequenceNumber : Alpha 8
  wsClassName : Alpha 14
  brokerStatus : Alpha 1
  showIndex : Alpha 1
  stBrokerEligibilityPerMkt : BitVec 16
  memberType : BitVec 16
  clearingStatus : Alpha 1
  brokerName : Alpha 25
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
    ++ (encodeUInt 4 message.lastPasswordChangeDate
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.branchId
    ++ (encodeUInt 4 message.versionNumber
    ++ (encodeUInt 4 message.batch2StartTime
    ++ (Alpha.encode message.hostSwitchContext
    ++ (Alpha.encode message.colour
    ++ (Alpha.encode message.secondReserved1
    ++ (encodeUInt 2 message.userType
    ++ (Alpha.encode message.sequenceNumber
    ++ (Alpha.encode message.wsClassName
    ++ (Alpha.encode message.brokerStatus
    ++ (Alpha.encode message.showIndex
    ++ (encodeUInt 2 message.stBrokerEligibilityPerMkt
    ++ (encodeUInt 2 message.memberType
    ++ (Alpha.encode message.clearingStatus
    ++ (Alpha.encode message.brokerName
    ++ (Alpha.encode message.reserved16
    ++ (Alpha.encode message.secondReserved16
    ++ (Alpha.encode message.thirdReserved16))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SignOnRequestInMessage × List UInt8) := do
  let (userId, bytes) ← decodeUInt 4 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  let (password, bytes) ← Alpha.decode 8 bytes
  let (secondReserved8, bytes) ← Alpha.decode 8 bytes
  let (newPassword, bytes) ← Alpha.decode 8 bytes
  let (traderName, bytes) ← Alpha.decode 26 bytes
  let (lastPasswordChangeDate, bytes) ← decodeUInt 4 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (branchId, bytes) ← decodeUInt 2 bytes
  let (versionNumber, bytes) ← decodeUInt 4 bytes
  let (batch2StartTime, bytes) ← decodeUInt 4 bytes
  let (hostSwitchContext, bytes) ← Alpha.decode 1 bytes
  let (colour, bytes) ← Alpha.decode 50 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  let (userType, bytes) ← decodeUInt 2 bytes
  let (sequenceNumber, bytes) ← Alpha.decode 8 bytes
  let (wsClassName, bytes) ← Alpha.decode 14 bytes
  let (brokerStatus, bytes) ← Alpha.decode 1 bytes
  let (showIndex, bytes) ← Alpha.decode 1 bytes
  let (stBrokerEligibilityPerMkt, bytes) ← decodeUInt 2 bytes
  let (memberType, bytes) ← decodeUInt 2 bytes
  let (clearingStatus, bytes) ← Alpha.decode 1 bytes
  let (brokerName, bytes) ← Alpha.decode 25 bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  let (secondReserved16, bytes) ← Alpha.decode 16 bytes
  let (thirdReserved16, bytes) ← Alpha.decode 16 bytes
  pure ({ userId, reserved8, password, secondReserved8, newPassword, traderName, lastPasswordChangeDate, brokerId, reserved1, branchId, versionNumber, batch2StartTime, hostSwitchContext, colour, secondReserved1, userType, sequenceNumber, wsClassName, brokerStatus, showIndex, stBrokerEligibilityPerMkt, memberType, clearingStatus, brokerName, reserved16, secondReserved16, thirdReserved16 }, bytes)

@[simp] theorem encode_length (message : SignOnRequestInMessage) : (encode message).length = 238 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : SignOnRequestInMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
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

end SignOnRequestInMessage

/-- Sign Off Trader In Message: 238 bytes -/
structure SignOffTraderInMessage where
  userId : BitVec 32
  reserved8 : Alpha 8
  password : Alpha 8
  secondReserved8 : Alpha 8
  newPassword : Alpha 8
  traderName : Alpha 26
  lastPasswordChangeDate : BitVec 32
  brokerId : Alpha 5
  reserved1 : Alpha 1
  branchId : BitVec 16
  versionNumber : BitVec 32
  batch2StartTime : BitVec 32
  hostSwitchContext : Alpha 1
  colour : Alpha 50
  secondReserved1 : Alpha 1
  userType : BitVec 16
  sequenceNumber : Alpha 8
  wsClassName : Alpha 14
  brokerStatus : Alpha 1
  showIndex : Alpha 1
  stBrokerEligibilityPerMkt : BitVec 16
  memberType : BitVec 16
  clearingStatus : Alpha 1
  brokerName : Alpha 25
  reserved16 : Alpha 16
  secondReserved16 : Alpha 16
  thirdReserved16 : Alpha 16
  deriving DecidableEq, Repr

namespace SignOffTraderInMessage

def encode (message : SignOffTraderInMessage) : List UInt8 :=
  encodeUInt 4 message.userId
    ++ (Alpha.encode message.reserved8
    ++ (Alpha.encode message.password
    ++ (Alpha.encode message.secondReserved8
    ++ (Alpha.encode message.newPassword
    ++ (Alpha.encode message.traderName
    ++ (encodeUInt 4 message.lastPasswordChangeDate
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.branchId
    ++ (encodeUInt 4 message.versionNumber
    ++ (encodeUInt 4 message.batch2StartTime
    ++ (Alpha.encode message.hostSwitchContext
    ++ (Alpha.encode message.colour
    ++ (Alpha.encode message.secondReserved1
    ++ (encodeUInt 2 message.userType
    ++ (Alpha.encode message.sequenceNumber
    ++ (Alpha.encode message.wsClassName
    ++ (Alpha.encode message.brokerStatus
    ++ (Alpha.encode message.showIndex
    ++ (encodeUInt 2 message.stBrokerEligibilityPerMkt
    ++ (encodeUInt 2 message.memberType
    ++ (Alpha.encode message.clearingStatus
    ++ (Alpha.encode message.brokerName
    ++ (Alpha.encode message.reserved16
    ++ (Alpha.encode message.secondReserved16
    ++ (Alpha.encode message.thirdReserved16))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SignOffTraderInMessage × List UInt8) := do
  let (userId, bytes) ← decodeUInt 4 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  let (password, bytes) ← Alpha.decode 8 bytes
  let (secondReserved8, bytes) ← Alpha.decode 8 bytes
  let (newPassword, bytes) ← Alpha.decode 8 bytes
  let (traderName, bytes) ← Alpha.decode 26 bytes
  let (lastPasswordChangeDate, bytes) ← decodeUInt 4 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (branchId, bytes) ← decodeUInt 2 bytes
  let (versionNumber, bytes) ← decodeUInt 4 bytes
  let (batch2StartTime, bytes) ← decodeUInt 4 bytes
  let (hostSwitchContext, bytes) ← Alpha.decode 1 bytes
  let (colour, bytes) ← Alpha.decode 50 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  let (userType, bytes) ← decodeUInt 2 bytes
  let (sequenceNumber, bytes) ← Alpha.decode 8 bytes
  let (wsClassName, bytes) ← Alpha.decode 14 bytes
  let (brokerStatus, bytes) ← Alpha.decode 1 bytes
  let (showIndex, bytes) ← Alpha.decode 1 bytes
  let (stBrokerEligibilityPerMkt, bytes) ← decodeUInt 2 bytes
  let (memberType, bytes) ← decodeUInt 2 bytes
  let (clearingStatus, bytes) ← Alpha.decode 1 bytes
  let (brokerName, bytes) ← Alpha.decode 25 bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  let (secondReserved16, bytes) ← Alpha.decode 16 bytes
  let (thirdReserved16, bytes) ← Alpha.decode 16 bytes
  pure ({ userId, reserved8, password, secondReserved8, newPassword, traderName, lastPasswordChangeDate, brokerId, reserved1, branchId, versionNumber, batch2StartTime, hostSwitchContext, colour, secondReserved1, userType, sequenceNumber, wsClassName, brokerStatus, showIndex, stBrokerEligibilityPerMkt, memberType, clearingStatus, brokerName, reserved16, secondReserved16, thirdReserved16 }, bytes)

@[simp] theorem encode_length (message : SignOffTraderInMessage) : (encode message).length = 238 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : SignOffTraderInMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SignOffTraderInMessage) (rest : List UInt8) :
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

end SignOffTraderInMessage

/-- Gr Request Message: 8 bytes -/
structure GrRequestMessage where
  boxId : BitVec 16
  brokerId : Alpha 5
  filler : Alpha 1
  deriving DecidableEq, Repr

namespace GrRequestMessage

def encode (message : GrRequestMessage) : List UInt8 :=
  encodeUInt 2 message.boxId
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.filler))

def decode (bytes : List UInt8) : Option (GrRequestMessage × List UInt8) := do
  let (boxId, bytes) ← decodeUInt 2 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (filler, bytes) ← Alpha.decode 1 bytes
  pure ({ boxId, brokerId, filler }, bytes)

@[simp] theorem encode_length (message : GrRequestMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : GrRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : GrRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end GrRequestMessage

/-- User Addr Unlock In Message: 74 bytes -/
structure UserAddrUnlockInMessage where
  userId : BitVec 32
  reserved70 : Alpha 70
  deriving DecidableEq, Repr

namespace UserAddrUnlockInMessage

def encode (message : UserAddrUnlockInMessage) : List UInt8 :=
  encodeUInt 4 message.userId
    ++ (Alpha.encode message.reserved70)

def decode (bytes : List UInt8) : Option (UserAddrUnlockInMessage × List UInt8) := do
  let (userId, bytes) ← decodeUInt 4 bytes
  let (reserved70, bytes) ← Alpha.decode 70 bytes
  pure ({ userId, reserved70 }, bytes)

@[simp] theorem encode_length (message : UserAddrUnlockInMessage) : (encode message).length = 74 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : UserAddrUnlockInMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UserAddrUnlockInMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end UserAddrUnlockInMessage

/-- Branch Limits 1: 32 bytes -/
structure BranchLimits1 where
  branchBuyValueLimit : Alpha 8
  branchSellValueLimit : Alpha 8
  reserved16 : Alpha 16
  deriving DecidableEq, Repr

namespace BranchLimits1

def encode (message : BranchLimits1) : List UInt8 :=
  Alpha.encode message.branchBuyValueLimit
    ++ (Alpha.encode message.branchSellValueLimit
    ++ (Alpha.encode message.reserved16))

def decode (bytes : List UInt8) : Option (BranchLimits1 × List UInt8) := do
  let (branchBuyValueLimit, bytes) ← Alpha.decode 8 bytes
  let (branchSellValueLimit, bytes) ← Alpha.decode 8 bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  pure ({ branchBuyValueLimit, branchSellValueLimit, reserved16 }, bytes)

@[simp] theorem encode_length (message : BranchLimits1) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : BranchLimits1) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BranchLimits1) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BranchLimits1

/-- Branch Limits 2: 32 bytes -/
structure BranchLimits2 where
  branchBuyValueLimit : Alpha 8
  branchSellValueLimit : Alpha 8
  reserved16 : Alpha 16
  deriving DecidableEq, Repr

namespace BranchLimits2

def encode (message : BranchLimits2) : List UInt8 :=
  Alpha.encode message.branchBuyValueLimit
    ++ (Alpha.encode message.branchSellValueLimit
    ++ (Alpha.encode message.reserved16))

def decode (bytes : List UInt8) : Option (BranchLimits2 × List UInt8) := do
  let (branchBuyValueLimit, bytes) ← Alpha.decode 8 bytes
  let (branchSellValueLimit, bytes) ← Alpha.decode 8 bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  pure ({ branchBuyValueLimit, branchSellValueLimit, reserved16 }, bytes)

@[simp] theorem encode_length (message : BranchLimits2) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : BranchLimits2) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BranchLimits2) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BranchLimits2

/-- Branch Ord Val Limit Update In Message: 96 bytes -/
structure BranchOrdValLimitUpdateInMessage where
  brokerId : Alpha 5
  reserved25 : Alpha 25
  branchId : BitVec 16
  branchLimits1 : BranchLimits1
  branchLimits2 : BranchLimits2
  deriving DecidableEq, Repr

namespace BranchOrdValLimitUpdateInMessage

def encode (message : BranchOrdValLimitUpdateInMessage) : List UInt8 :=
  Alpha.encode message.brokerId
    ++ (Alpha.encode message.reserved25
    ++ (encodeUInt 2 message.branchId
    ++ (BranchLimits1.encode message.branchLimits1
    ++ (BranchLimits2.encode message.branchLimits2))))

def decode (bytes : List UInt8) : Option (BranchOrdValLimitUpdateInMessage × List UInt8) := do
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (reserved25, bytes) ← Alpha.decode 25 bytes
  let (branchId, bytes) ← decodeUInt 2 bytes
  let (branchLimits1, bytes) ← BranchLimits1.decode bytes
  let (branchLimits2, bytes) ← BranchLimits2.decode bytes
  pure ({ brokerId, reserved25, branchId, branchLimits1, branchLimits2 }, bytes)

@[simp] theorem encode_length (message : BranchOrdValLimitUpdateInMessage) : (encode message).length = 96 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, BranchLimits1.encode_length, BranchLimits2.encode_length]

theorem encode_length_pos (message : BranchOrdValLimitUpdateInMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BranchOrdValLimitUpdateInMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, BranchLimits1.decode_encode, some_bind]
  dsimp only
  rw [BranchLimits2.decode_encode, some_bind]
  rfl

end BranchOrdValLimitUpdateInMessage

/-- User Limits 1: 64 bytes -/
structure UserLimits1 where
  reserved32 : Alpha 32
  userOrderBuyValueLimit : Alpha 8
  userOrderSellValueLimit : Alpha 8
  reserved16 : Alpha 16
  deriving DecidableEq, Repr

namespace UserLimits1

def encode (message : UserLimits1) : List UInt8 :=
  Alpha.encode message.reserved32
    ++ (Alpha.encode message.userOrderBuyValueLimit
    ++ (Alpha.encode message.userOrderSellValueLimit
    ++ (Alpha.encode message.reserved16)))

def decode (bytes : List UInt8) : Option (UserLimits1 × List UInt8) := do
  let (reserved32, bytes) ← Alpha.decode 32 bytes
  let (userOrderBuyValueLimit, bytes) ← Alpha.decode 8 bytes
  let (userOrderSellValueLimit, bytes) ← Alpha.decode 8 bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  pure ({ reserved32, userOrderBuyValueLimit, userOrderSellValueLimit, reserved16 }, bytes)

@[simp] theorem encode_length (message : UserLimits1) : (encode message).length = 64 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : UserLimits1) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UserLimits1) (rest : List UInt8) :
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

end UserLimits1

/-- User Limits 2: 64 bytes -/
structure UserLimits2 where
  reserved32 : Alpha 32
  userOrderBuyValueLimit : Alpha 8
  userOrderSellValueLimit : Alpha 8
  reserved16 : Alpha 16
  deriving DecidableEq, Repr

namespace UserLimits2

def encode (message : UserLimits2) : List UInt8 :=
  Alpha.encode message.reserved32
    ++ (Alpha.encode message.userOrderBuyValueLimit
    ++ (Alpha.encode message.userOrderSellValueLimit
    ++ (Alpha.encode message.reserved16)))

def decode (bytes : List UInt8) : Option (UserLimits2 × List UInt8) := do
  let (reserved32, bytes) ← Alpha.decode 32 bytes
  let (userOrderBuyValueLimit, bytes) ← Alpha.decode 8 bytes
  let (userOrderSellValueLimit, bytes) ← Alpha.decode 8 bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  pure ({ reserved32, userOrderBuyValueLimit, userOrderSellValueLimit, reserved16 }, bytes)

@[simp] theorem encode_length (message : UserLimits2) : (encode message).length = 64 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : UserLimits2) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UserLimits2) (rest : List UInt8) :
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

end UserLimits2

/-- User Ord Val Limit Update In Message: 168 bytes -/
structure UserOrdValLimitUpdateInMessage where
  brokerId : Alpha 5
  reserved1 : Alpha 1
  branchId : BitVec 16
  reserved26 : Alpha 26
  userId : BitVec 32
  reserved2 : Alpha 2
  userLimits1 : UserLimits1
  userLimits2 : UserLimits2
  deriving DecidableEq, Repr

namespace UserOrdValLimitUpdateInMessage

def encode (message : UserOrdValLimitUpdateInMessage) : List UInt8 :=
  Alpha.encode message.brokerId
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.branchId
    ++ (Alpha.encode message.reserved26
    ++ (encodeUInt 4 message.userId
    ++ (Alpha.encode message.reserved2
    ++ (UserLimits1.encode message.userLimits1
    ++ (UserLimits2.encode message.userLimits2)))))))

def decode (bytes : List UInt8) : Option (UserOrdValLimitUpdateInMessage × List UInt8) := do
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (branchId, bytes) ← decodeUInt 2 bytes
  let (reserved26, bytes) ← Alpha.decode 26 bytes
  let (userId, bytes) ← decodeUInt 4 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (userLimits1, bytes) ← UserLimits1.decode bytes
  let (userLimits2, bytes) ← UserLimits2.decode bytes
  pure ({ brokerId, reserved1, branchId, reserved26, userId, reserved2, userLimits1, userLimits2 }, bytes)

@[simp] theorem encode_length (message : UserOrdValLimitUpdateInMessage) : (encode message).length = 168 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, UserLimits1.encode_length, UserLimits2.encode_length]

theorem encode_length_pos (message : UserOrdValLimitUpdateInMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UserOrdValLimitUpdateInMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, UserLimits1.decode_encode, some_bind]
  dsimp only
  rw [UserLimits2.decode_encode, some_bind]
  rfl

end UserOrdValLimitUpdateInMessage

/-- Normal Ord Limit Update In Message: 26 bytes -/
structure NormalOrdLimitUpdateInMessage where
  brokerId : Alpha 5
  reserved1 : Alpha 1
  userId : BitVec 32
  orderQtyLimit : Alpha 8
  orderValLimit : Alpha 8
  deriving DecidableEq, Repr

namespace NormalOrdLimitUpdateInMessage

def encode (message : NormalOrdLimitUpdateInMessage) : List UInt8 :=
  Alpha.encode message.brokerId
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 4 message.userId
    ++ (Alpha.encode message.orderQtyLimit
    ++ (Alpha.encode message.orderValLimit))))

def decode (bytes : List UInt8) : Option (NormalOrdLimitUpdateInMessage × List UInt8) := do
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (userId, bytes) ← decodeUInt 4 bytes
  let (orderQtyLimit, bytes) ← Alpha.decode 8 bytes
  let (orderValLimit, bytes) ← Alpha.decode 8 bytes
  pure ({ brokerId, reserved1, userId, orderQtyLimit, orderValLimit }, bytes)

@[simp] theorem encode_length (message : NormalOrdLimitUpdateInMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : NormalOrdLimitUpdateInMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NormalOrdLimitUpdateInMessage) (rest : List UInt8) :
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

end NormalOrdLimitUpdateInMessage

/-- Spread Ord Limit Update In Message: 26 bytes -/
structure SpreadOrdLimitUpdateInMessage where
  brokerId : Alpha 5
  reserved1 : Alpha 1
  userId : BitVec 32
  orderQtyLimit : Alpha 8
  orderValLimit : Alpha 8
  deriving DecidableEq, Repr

namespace SpreadOrdLimitUpdateInMessage

def encode (message : SpreadOrdLimitUpdateInMessage) : List UInt8 :=
  Alpha.encode message.brokerId
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 4 message.userId
    ++ (Alpha.encode message.orderQtyLimit
    ++ (Alpha.encode message.orderValLimit))))

def decode (bytes : List UInt8) : Option (SpreadOrdLimitUpdateInMessage × List UInt8) := do
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (userId, bytes) ← decodeUInt 4 bytes
  let (orderQtyLimit, bytes) ← Alpha.decode 8 bytes
  let (orderValLimit, bytes) ← Alpha.decode 8 bytes
  pure ({ brokerId, reserved1, userId, orderQtyLimit, orderValLimit }, bytes)

@[simp] theorem encode_length (message : SpreadOrdLimitUpdateInMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SpreadOrdLimitUpdateInMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SpreadOrdLimitUpdateInMessage) (rest : List UInt8) :
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

end SpreadOrdLimitUpdateInMessage

/-- Reset User Password In Message: 18 bytes -/
structure ResetUserPasswordInMessage where
  userId : BitVec 32
  reserved14 : Alpha 14
  deriving DecidableEq, Repr

namespace ResetUserPasswordInMessage

def encode (message : ResetUserPasswordInMessage) : List UInt8 :=
  encodeUInt 4 message.userId
    ++ (Alpha.encode message.reserved14)

def decode (bytes : List UInt8) : Option (ResetUserPasswordInMessage × List UInt8) := do
  let (userId, bytes) ← decodeUInt 4 bytes
  let (reserved14, bytes) ← Alpha.decode 14 bytes
  pure ({ userId, reserved14 }, bytes)

@[simp] theorem encode_length (message : ResetUserPasswordInMessage) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : ResetUserPasswordInMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ResetUserPasswordInMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ResetUserPasswordInMessage

/-- Col User Status Change In Message: 12 bytes -/
structure ColUserStatusChangeInMessage where
  userId : BitVec 32
  colUserBit : Alpha 1
  reserved7 : Alpha 7
  deriving DecidableEq, Repr

namespace ColUserStatusChangeInMessage

def encode (message : ColUserStatusChangeInMessage) : List UInt8 :=
  encodeUInt 4 message.userId
    ++ (Alpha.encode message.colUserBit
    ++ (Alpha.encode message.reserved7))

def decode (bytes : List UInt8) : Option (ColUserStatusChangeInMessage × List UInt8) := do
  let (userId, bytes) ← decodeUInt 4 bytes
  let (colUserBit, bytes) ← Alpha.decode 1 bytes
  let (reserved7, bytes) ← Alpha.decode 7 bytes
  pure ({ userId, colUserBit, reserved7 }, bytes)

@[simp] theorem encode_length (message : ColUserStatusChangeInMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : ColUserStatusChangeInMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ColUserStatusChangeInMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ColUserStatusChangeInMessage

/-- Download Request Message: 8 bytes -/
structure DownloadRequestMessage where
  sequenceNumber : Alpha 8
  deriving DecidableEq, Repr

namespace DownloadRequestMessage

def encode (message : DownloadRequestMessage) : List UInt8 :=
  Alpha.encode message.sequenceNumber

def decode (bytes : List UInt8) : Option (DownloadRequestMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ sequenceNumber }, bytes)

@[simp] theorem encode_length (message : DownloadRequestMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : DownloadRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DownloadRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end DownloadRequestMessage

/-- St Market Status: 8 bytes -/
structure StMarketStatus where
  normal : BitVec 16
  oddlot : BitVec 16
  spot : BitVec 16
  auction : BitVec 16
  deriving DecidableEq, Repr

namespace StMarketStatus

def encode (message : StMarketStatus) : List UInt8 :=
  encodeUInt 2 message.normal
    ++ (encodeUInt 2 message.oddlot
    ++ (encodeUInt 2 message.spot
    ++ (encodeUInt 2 message.auction)))

def decode (bytes : List UInt8) : Option (StMarketStatus × List UInt8) := do
  let (normal, bytes) ← decodeUInt 2 bytes
  let (oddlot, bytes) ← decodeUInt 2 bytes
  let (spot, bytes) ← decodeUInt 2 bytes
  let (auction, bytes) ← decodeUInt 2 bytes
  pure ({ normal, oddlot, spot, auction }, bytes)

@[simp] theorem encode_length (message : StMarketStatus) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : StMarketStatus) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StMarketStatus) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end StMarketStatus

/-- St Ex Market Status: 8 bytes -/
structure StExMarketStatus where
  normal : BitVec 16
  oddlot : BitVec 16
  spot : BitVec 16
  auction : BitVec 16
  deriving DecidableEq, Repr

namespace StExMarketStatus

def encode (message : StExMarketStatus) : List UInt8 :=
  encodeUInt 2 message.normal
    ++ (encodeUInt 2 message.oddlot
    ++ (encodeUInt 2 message.spot
    ++ (encodeUInt 2 message.auction)))

def decode (bytes : List UInt8) : Option (StExMarketStatus × List UInt8) := do
  let (normal, bytes) ← decodeUInt 2 bytes
  let (oddlot, bytes) ← decodeUInt 2 bytes
  let (spot, bytes) ← decodeUInt 2 bytes
  let (auction, bytes) ← decodeUInt 2 bytes
  pure ({ normal, oddlot, spot, auction }, bytes)

@[simp] theorem encode_length (message : StExMarketStatus) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : StExMarketStatus) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StExMarketStatus) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end StExMarketStatus

/-- St Pl Market Status: 8 bytes -/
structure StPlMarketStatus where
  normal : BitVec 16
  oddlot : BitVec 16
  spot : BitVec 16
  auction : BitVec 16
  deriving DecidableEq, Repr

namespace StPlMarketStatus

def encode (message : StPlMarketStatus) : List UInt8 :=
  encodeUInt 2 message.normal
    ++ (encodeUInt 2 message.oddlot
    ++ (encodeUInt 2 message.spot
    ++ (encodeUInt 2 message.auction)))

def decode (bytes : List UInt8) : Option (StPlMarketStatus × List UInt8) := do
  let (normal, bytes) ← decodeUInt 2 bytes
  let (oddlot, bytes) ← decodeUInt 2 bytes
  let (spot, bytes) ← decodeUInt 2 bytes
  let (auction, bytes) ← decodeUInt 2 bytes
  pure ({ normal, oddlot, spot, auction }, bytes)

@[simp] theorem encode_length (message : StPlMarketStatus) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : StPlMarketStatus) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StPlMarketStatus) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end StPlMarketStatus

/-- Update Localdb In Message: 42 bytes -/
structure UpdateLocaldbInMessage where
  lastUpdateSecurityTime : BitVec 32
  lastUpdateParticipantTime : BitVec 32
  lastUpdateInstrumentTime : BitVec 32
  lastUpdateIndexTime : BitVec 32
  requestForOpenOrders : Alpha 1
  reserved1 : Alpha 1
  stMarketStatus : StMarketStatus
  stExMarketStatus : StExMarketStatus
  stPlMarketStatus : StPlMarketStatus
  deriving DecidableEq, Repr

namespace UpdateLocaldbInMessage

def encode (message : UpdateLocaldbInMessage) : List UInt8 :=
  encodeUInt 4 message.lastUpdateSecurityTime
    ++ (encodeUInt 4 message.lastUpdateParticipantTime
    ++ (encodeUInt 4 message.lastUpdateInstrumentTime
    ++ (encodeUInt 4 message.lastUpdateIndexTime
    ++ (Alpha.encode message.requestForOpenOrders
    ++ (Alpha.encode message.reserved1
    ++ (StMarketStatus.encode message.stMarketStatus
    ++ (StExMarketStatus.encode message.stExMarketStatus
    ++ (StPlMarketStatus.encode message.stPlMarketStatus))))))))

def decode (bytes : List UInt8) : Option (UpdateLocaldbInMessage × List UInt8) := do
  let (lastUpdateSecurityTime, bytes) ← decodeUInt 4 bytes
  let (lastUpdateParticipantTime, bytes) ← decodeUInt 4 bytes
  let (lastUpdateInstrumentTime, bytes) ← decodeUInt 4 bytes
  let (lastUpdateIndexTime, bytes) ← decodeUInt 4 bytes
  let (requestForOpenOrders, bytes) ← Alpha.decode 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (stMarketStatus, bytes) ← StMarketStatus.decode bytes
  let (stExMarketStatus, bytes) ← StExMarketStatus.decode bytes
  let (stPlMarketStatus, bytes) ← StPlMarketStatus.decode bytes
  pure ({ lastUpdateSecurityTime, lastUpdateParticipantTime, lastUpdateInstrumentTime, lastUpdateIndexTime, requestForOpenOrders, reserved1, stMarketStatus, stExMarketStatus, stPlMarketStatus }, bytes)

@[simp] theorem encode_length (message : UpdateLocaldbInMessage) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, StMarketStatus.encode_length, StExMarketStatus.encode_length, StPlMarketStatus.encode_length]

theorem encode_length_pos (message : UpdateLocaldbInMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UpdateLocaldbInMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, StMarketStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StExMarketStatus.decode_encode, some_bind]
  dsimp only
  rw [StPlMarketStatus.decode_encode, some_bind]
  rfl

end UpdateLocaldbInMessage

/-- Box Sign On Request In Message: 20 bytes -/
structure BoxSignOnRequestInMessage where
  boxId : BitVec 16
  brokerId : Alpha 5
  reserved5 : Alpha 5
  sessionKey : Alpha 8
  deriving DecidableEq, Repr

namespace BoxSignOnRequestInMessage

def encode (message : BoxSignOnRequestInMessage) : List UInt8 :=
  encodeUInt 2 message.boxId
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.reserved5
    ++ (Alpha.encode message.sessionKey)))

def decode (bytes : List UInt8) : Option (BoxSignOnRequestInMessage × List UInt8) := do
  let (boxId, bytes) ← decodeUInt 2 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (reserved5, bytes) ← Alpha.decode 5 bytes
  let (sessionKey, bytes) ← Alpha.decode 8 bytes
  pure ({ boxId, brokerId, reserved5, sessionKey }, bytes)

@[simp] theorem encode_length (message : BoxSignOnRequestInMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : BoxSignOnRequestInMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BoxSignOnRequestInMessage) (rest : List UInt8) :
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

end BoxSignOnRequestInMessage

/-- Any Client Message Payload, selected by Transaction Code -/
inductive ClientMessagePayload where
  | systemInformationInMessage (message : SystemInformationInMessage) -- 1600
  | boardLotInMessage (message : BoardLotInMessage) -- 2000
  | orderModInMessage (message : OrderModInMessage) -- 2040
  | orderCancelInMessage (message : OrderCancelInMessage) -- 2070
  | priceModInMessage (message : PriceModInMessage) -- 2013
  | spBoardLotInMessage (message : SpBoardLotInMessage) -- 2100
  | twolBoardLotInMessage (message : TwolBoardLotInMessage) -- 2102
  | thrlBoardLotInMessage (message : ThrlBoardLotInMessage) -- 2104
  | spOrderCancelInMessage (message : SpOrderCancelInMessage) -- 2106
  | spOrderModInMessage (message : SpOrderModInMessage) -- 2118
  | tradeCancelInMessage (message : TradeCancelInMessage) -- 5440
  | tradeModInMessage (message : TradeModInMessage) -- 5445
  | signOnRequestInMessage (message : SignOnRequestInMessage) -- 2300
  | signOffTraderInMessage (message : SignOffTraderInMessage) -- 5584
  | grRequestMessage (message : GrRequestMessage) -- 2400
  | userAddrUnlockInMessage (message : UserAddrUnlockInMessage) -- 5427
  | branchOrdValLimitUpdateInMessage (message : BranchOrdValLimitUpdateInMessage) -- 5716
  | userOrdValLimitUpdateInMessage (message : UserOrdValLimitUpdateInMessage) -- 5730
  | normalOrdLimitUpdateInMessage (message : NormalOrdLimitUpdateInMessage) -- 5732
  | spreadOrdLimitUpdateInMessage (message : SpreadOrdLimitUpdateInMessage) -- 5771
  | resetUserPasswordInMessage (message : ResetUserPasswordInMessage) -- 5740
  | colUserStatusChangeInMessage (message : ColUserStatusChangeInMessage) -- 5744
  | downloadRequestMessage (message : DownloadRequestMessage) -- 7000
  | updateLocaldbInMessage (message : UpdateLocaldbInMessage) -- 7300
  | boxSignOnRequestInMessage (message : BoxSignOnRequestInMessage) -- 23000
  deriving DecidableEq, Repr

namespace ClientMessagePayload

/-- The Transaction Code each message is sent under -/
def tag : ClientMessagePayload → BitVec 16
  | .systemInformationInMessage _ => 1600
  | .boardLotInMessage _ => 2000
  | .orderModInMessage _ => 2040
  | .orderCancelInMessage _ => 2070
  | .priceModInMessage _ => 2013
  | .spBoardLotInMessage _ => 2100
  | .twolBoardLotInMessage _ => 2102
  | .thrlBoardLotInMessage _ => 2104
  | .spOrderCancelInMessage _ => 2106
  | .spOrderModInMessage _ => 2118
  | .tradeCancelInMessage _ => 5440
  | .tradeModInMessage _ => 5445
  | .signOnRequestInMessage _ => 2300
  | .signOffTraderInMessage _ => 5584
  | .grRequestMessage _ => 2400
  | .userAddrUnlockInMessage _ => 5427
  | .branchOrdValLimitUpdateInMessage _ => 5716
  | .userOrdValLimitUpdateInMessage _ => 5730
  | .normalOrdLimitUpdateInMessage _ => 5732
  | .spreadOrdLimitUpdateInMessage _ => 5771
  | .resetUserPasswordInMessage _ => 5740
  | .colUserStatusChangeInMessage _ => 5744
  | .downloadRequestMessage _ => 7000
  | .updateLocaldbInMessage _ => 7300
  | .boxSignOnRequestInMessage _ => 23000

def encode : ClientMessagePayload → List UInt8
  | .systemInformationInMessage message => SystemInformationInMessage.encode message
  | .boardLotInMessage message => BoardLotInMessage.encode message
  | .orderModInMessage message => OrderModInMessage.encode message
  | .orderCancelInMessage message => OrderCancelInMessage.encode message
  | .priceModInMessage message => PriceModInMessage.encode message
  | .spBoardLotInMessage message => SpBoardLotInMessage.encode message
  | .twolBoardLotInMessage message => TwolBoardLotInMessage.encode message
  | .thrlBoardLotInMessage message => ThrlBoardLotInMessage.encode message
  | .spOrderCancelInMessage message => SpOrderCancelInMessage.encode message
  | .spOrderModInMessage message => SpOrderModInMessage.encode message
  | .tradeCancelInMessage message => TradeCancelInMessage.encode message
  | .tradeModInMessage message => TradeModInMessage.encode message
  | .signOnRequestInMessage message => SignOnRequestInMessage.encode message
  | .signOffTraderInMessage message => SignOffTraderInMessage.encode message
  | .grRequestMessage message => GrRequestMessage.encode message
  | .userAddrUnlockInMessage message => UserAddrUnlockInMessage.encode message
  | .branchOrdValLimitUpdateInMessage message => BranchOrdValLimitUpdateInMessage.encode message
  | .userOrdValLimitUpdateInMessage message => UserOrdValLimitUpdateInMessage.encode message
  | .normalOrdLimitUpdateInMessage message => NormalOrdLimitUpdateInMessage.encode message
  | .spreadOrdLimitUpdateInMessage message => SpreadOrdLimitUpdateInMessage.encode message
  | .resetUserPasswordInMessage message => ResetUserPasswordInMessage.encode message
  | .colUserStatusChangeInMessage message => ColUserStatusChangeInMessage.encode message
  | .downloadRequestMessage message => DownloadRequestMessage.encode message
  | .updateLocaldbInMessage message => UpdateLocaldbInMessage.encode message
  | .boxSignOnRequestInMessage message => BoxSignOnRequestInMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ClientMessagePayload) : (encode message).length ≤ 440 := by
  cases message with
  | systemInformationInMessage inner =>
    simp only [encode, SystemInformationInMessage.encode_length]
    omega
  | boardLotInMessage inner =>
    simp only [encode, BoardLotInMessage.encode_length]
    omega
  | orderModInMessage inner =>
    simp only [encode, OrderModInMessage.encode_length]
    omega
  | orderCancelInMessage inner =>
    simp only [encode, OrderCancelInMessage.encode_length]
    omega
  | priceModInMessage inner =>
    simp only [encode, PriceModInMessage.encode_length]
    omega
  | spBoardLotInMessage inner =>
    simp only [encode, SpBoardLotInMessage.encode_length]
    omega
  | twolBoardLotInMessage inner =>
    simp only [encode, TwolBoardLotInMessage.encode_length]
    omega
  | thrlBoardLotInMessage inner =>
    simp only [encode, ThrlBoardLotInMessage.encode_length]
    omega
  | spOrderCancelInMessage inner =>
    simp only [encode, SpOrderCancelInMessage.encode_length]
    omega
  | spOrderModInMessage inner =>
    simp only [encode, SpOrderModInMessage.encode_length]
    omega
  | tradeCancelInMessage inner =>
    simp only [encode, TradeCancelInMessage.encode_length]
    omega
  | tradeModInMessage inner =>
    simp only [encode, TradeModInMessage.encode_length]
    omega
  | signOnRequestInMessage inner =>
    simp only [encode, SignOnRequestInMessage.encode_length]
    omega
  | signOffTraderInMessage inner =>
    simp only [encode, SignOffTraderInMessage.encode_length]
    omega
  | grRequestMessage inner =>
    simp only [encode, GrRequestMessage.encode_length]
    omega
  | userAddrUnlockInMessage inner =>
    simp only [encode, UserAddrUnlockInMessage.encode_length]
    omega
  | branchOrdValLimitUpdateInMessage inner =>
    simp only [encode, BranchOrdValLimitUpdateInMessage.encode_length]
    omega
  | userOrdValLimitUpdateInMessage inner =>
    simp only [encode, UserOrdValLimitUpdateInMessage.encode_length]
    omega
  | normalOrdLimitUpdateInMessage inner =>
    simp only [encode, NormalOrdLimitUpdateInMessage.encode_length]
    omega
  | spreadOrdLimitUpdateInMessage inner =>
    simp only [encode, SpreadOrdLimitUpdateInMessage.encode_length]
    omega
  | resetUserPasswordInMessage inner =>
    simp only [encode, ResetUserPasswordInMessage.encode_length]
    omega
  | colUserStatusChangeInMessage inner =>
    simp only [encode, ColUserStatusChangeInMessage.encode_length]
    omega
  | downloadRequestMessage inner =>
    simp only [encode, DownloadRequestMessage.encode_length]
    omega
  | updateLocaldbInMessage inner =>
    simp only [encode, UpdateLocaldbInMessage.encode_length]
    omega
  | boxSignOnRequestInMessage inner =>
    simp only [encode, BoxSignOnRequestInMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (ClientMessagePayload × List UInt8) :=
  if tag = 1600 then (SystemInformationInMessage.decode bytes).map fun (message, rest) => (.systemInformationInMessage message, rest)
  else if tag = 2000 then (BoardLotInMessage.decode bytes).map fun (message, rest) => (.boardLotInMessage message, rest)
  else if tag = 2040 then (OrderModInMessage.decode bytes).map fun (message, rest) => (.orderModInMessage message, rest)
  else if tag = 2070 then (OrderCancelInMessage.decode bytes).map fun (message, rest) => (.orderCancelInMessage message, rest)
  else if tag = 2013 then (PriceModInMessage.decode bytes).map fun (message, rest) => (.priceModInMessage message, rest)
  else if tag = 2100 then (SpBoardLotInMessage.decode bytes).map fun (message, rest) => (.spBoardLotInMessage message, rest)
  else if tag = 2102 then (TwolBoardLotInMessage.decode bytes).map fun (message, rest) => (.twolBoardLotInMessage message, rest)
  else if tag = 2104 then (ThrlBoardLotInMessage.decode bytes).map fun (message, rest) => (.thrlBoardLotInMessage message, rest)
  else if tag = 2106 then (SpOrderCancelInMessage.decode bytes).map fun (message, rest) => (.spOrderCancelInMessage message, rest)
  else if tag = 2118 then (SpOrderModInMessage.decode bytes).map fun (message, rest) => (.spOrderModInMessage message, rest)
  else if tag = 5440 then (TradeCancelInMessage.decode bytes).map fun (message, rest) => (.tradeCancelInMessage message, rest)
  else if tag = 5445 then (TradeModInMessage.decode bytes).map fun (message, rest) => (.tradeModInMessage message, rest)
  else if tag = 2300 then (SignOnRequestInMessage.decode bytes).map fun (message, rest) => (.signOnRequestInMessage message, rest)
  else if tag = 5584 then (SignOffTraderInMessage.decode bytes).map fun (message, rest) => (.signOffTraderInMessage message, rest)
  else if tag = 2400 then (GrRequestMessage.decode bytes).map fun (message, rest) => (.grRequestMessage message, rest)
  else if tag = 5427 then (UserAddrUnlockInMessage.decode bytes).map fun (message, rest) => (.userAddrUnlockInMessage message, rest)
  else if tag = 5716 then (BranchOrdValLimitUpdateInMessage.decode bytes).map fun (message, rest) => (.branchOrdValLimitUpdateInMessage message, rest)
  else if tag = 5730 then (UserOrdValLimitUpdateInMessage.decode bytes).map fun (message, rest) => (.userOrdValLimitUpdateInMessage message, rest)
  else if tag = 5732 then (NormalOrdLimitUpdateInMessage.decode bytes).map fun (message, rest) => (.normalOrdLimitUpdateInMessage message, rest)
  else if tag = 5771 then (SpreadOrdLimitUpdateInMessage.decode bytes).map fun (message, rest) => (.spreadOrdLimitUpdateInMessage message, rest)
  else if tag = 5740 then (ResetUserPasswordInMessage.decode bytes).map fun (message, rest) => (.resetUserPasswordInMessage message, rest)
  else if tag = 5744 then (ColUserStatusChangeInMessage.decode bytes).map fun (message, rest) => (.colUserStatusChangeInMessage message, rest)
  else if tag = 7000 then (DownloadRequestMessage.decode bytes).map fun (message, rest) => (.downloadRequestMessage message, rest)
  else if tag = 7300 then (UpdateLocaldbInMessage.decode bytes).map fun (message, rest) => (.updateLocaldbInMessage message, rest)
  else if tag = 23000 then (BoxSignOnRequestInMessage.decode bytes).map fun (message, rest) => (.boxSignOnRequestInMessage message, rest)
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
  | systemInformationInMessage inner =>
    simp only [ClientMessagePayload.encode, SystemInformationInMessage.encode_length]
    omega
  | boardLotInMessage inner =>
    simp only [ClientMessagePayload.encode, BoardLotInMessage.encode_length]
    omega
  | orderModInMessage inner =>
    simp only [ClientMessagePayload.encode, OrderModInMessage.encode_length]
    omega
  | orderCancelInMessage inner =>
    simp only [ClientMessagePayload.encode, OrderCancelInMessage.encode_length]
    omega
  | priceModInMessage inner =>
    simp only [ClientMessagePayload.encode, PriceModInMessage.encode_length]
    omega
  | spBoardLotInMessage inner =>
    simp only [ClientMessagePayload.encode, SpBoardLotInMessage.encode_length]
    omega
  | twolBoardLotInMessage inner =>
    simp only [ClientMessagePayload.encode, TwolBoardLotInMessage.encode_length]
    omega
  | thrlBoardLotInMessage inner =>
    simp only [ClientMessagePayload.encode, ThrlBoardLotInMessage.encode_length]
    omega
  | spOrderCancelInMessage inner =>
    simp only [ClientMessagePayload.encode, SpOrderCancelInMessage.encode_length]
    omega
  | spOrderModInMessage inner =>
    simp only [ClientMessagePayload.encode, SpOrderModInMessage.encode_length]
    omega
  | tradeCancelInMessage inner =>
    simp only [ClientMessagePayload.encode, TradeCancelInMessage.encode_length]
    omega
  | tradeModInMessage inner =>
    simp only [ClientMessagePayload.encode, TradeModInMessage.encode_length]
    omega
  | signOnRequestInMessage inner =>
    simp only [ClientMessagePayload.encode, SignOnRequestInMessage.encode_length]
    omega
  | signOffTraderInMessage inner =>
    simp only [ClientMessagePayload.encode, SignOffTraderInMessage.encode_length]
    omega
  | grRequestMessage inner =>
    simp only [ClientMessagePayload.encode, GrRequestMessage.encode_length]
    omega
  | userAddrUnlockInMessage inner =>
    simp only [ClientMessagePayload.encode, UserAddrUnlockInMessage.encode_length]
    omega
  | branchOrdValLimitUpdateInMessage inner =>
    simp only [ClientMessagePayload.encode, BranchOrdValLimitUpdateInMessage.encode_length]
    omega
  | userOrdValLimitUpdateInMessage inner =>
    simp only [ClientMessagePayload.encode, UserOrdValLimitUpdateInMessage.encode_length]
    omega
  | normalOrdLimitUpdateInMessage inner =>
    simp only [ClientMessagePayload.encode, NormalOrdLimitUpdateInMessage.encode_length]
    omega
  | spreadOrdLimitUpdateInMessage inner =>
    simp only [ClientMessagePayload.encode, SpreadOrdLimitUpdateInMessage.encode_length]
    omega
  | resetUserPasswordInMessage inner =>
    simp only [ClientMessagePayload.encode, ResetUserPasswordInMessage.encode_length]
    omega
  | colUserStatusChangeInMessage inner =>
    simp only [ClientMessagePayload.encode, ColUserStatusChangeInMessage.encode_length]
    omega
  | downloadRequestMessage inner =>
    simp only [ClientMessagePayload.encode, DownloadRequestMessage.encode_length]
    omega
  | updateLocaldbInMessage inner =>
    simp only [ClientMessagePayload.encode, UpdateLocaldbInMessage.encode_length]
    omega
  | boxSignOnRequestInMessage inner =>
    simp only [ClientMessagePayload.encode, BoxSignOnRequestInMessage.encode_length]
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

end Omi.NseNsecdOrderentryNnfV63Client
