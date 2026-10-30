import Wire

/-!
# National Stock Exchange of India Ltd Drop Copy v1.5

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NseNsecomDropcopyNnfdirectV15Server

/-- Open Close: one byte code -/
def OpenClose.codes : List UInt8 :=
  [0x4F, 0x43]

inductive OpenClose where
  | open_ -- Open
  | close -- Close
  | unlisted (byte : { byte : UInt8 // byte ∉ OpenClose.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OpenClose

def toByte : OpenClose → UInt8
  | .open_ => 0x4F
  | .close => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OpenClose :=
  if byte = 0x4F then .open_
  else .close

def ofByte (byte : UInt8) : OpenClose :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OpenClose) : ofByte value.toByte = value := by
  cases value with
  | open_ => decide
  | close => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OpenClose) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OpenClose × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OpenClose) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OpenClose) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OpenClose) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OpenClose

/-- Sign On Out Message: 238 bytes -/
structure SignOnOutMessage where
  userId : BitVec 32
  reserved8 : Alpha 8
  password : Alpha 8
  secondReserved8 : Alpha 8
  reserved38 : Alpha 38
  brokerId : Alpha 5
  reserved119 : Alpha 119
  reserved16 : Alpha 16
  secondReserved16 : Alpha 16
  thirdReserved16 : Alpha 16
  deriving DecidableEq, Repr

namespace SignOnOutMessage

def encode (message : SignOnOutMessage) : List UInt8 :=
  encodeUInt 4 message.userId
    ++ (Alpha.encode message.reserved8
    ++ (Alpha.encode message.password
    ++ (Alpha.encode message.secondReserved8
    ++ (Alpha.encode message.reserved38
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.reserved119
    ++ (Alpha.encode message.reserved16
    ++ (Alpha.encode message.secondReserved16
    ++ (Alpha.encode message.thirdReserved16)))))))))

def decode (bytes : List UInt8) : Option (SignOnOutMessage × List UInt8) := do
  let (userId, bytes) ← decodeUInt 4 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  let (password, bytes) ← Alpha.decode 8 bytes
  let (secondReserved8, bytes) ← Alpha.decode 8 bytes
  let (reserved38, bytes) ← Alpha.decode 38 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (reserved119, bytes) ← Alpha.decode 119 bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  let (secondReserved16, bytes) ← Alpha.decode 16 bytes
  let (thirdReserved16, bytes) ← Alpha.decode 16 bytes
  pure ({ userId, reserved8, password, secondReserved8, reserved38, brokerId, reserved119, reserved16, secondReserved16, thirdReserved16 }, bytes)

@[simp] theorem encode_length (message : SignOnOutMessage) : (encode message).length = 238 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : SignOnOutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SignOnOutMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SignOnOutMessage

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

/-- Trade Confirmation Message: 256 bytes -/
structure TradeConfirmationMessage where
  responseOrderNumber : Alpha 8
  brokerId : Alpha 5
  reserved1 : Alpha 1
  traderNum : BitVec 32
  accountNum : Alpha 10
  buySell : BitVec 16
  originalVol : BitVec 32
  disclosedVol : BitVec 32
  remainingVol : BitVec 32
  disclosedVolRemaining : BitVec 32
  price : BitVec 32
  stOrderFlags : BitVec 16
  gtd : BitVec 32
  fillNumber : BitVec 32
  fillQty : BitVec 32
  fillPrice : BitVec 32
  volFilledToday : BitVec 32
  activityType : Alpha 2
  activityTime : BitVec 32
  opOrderNumber : Alpha 8
  opBrokerId : Alpha 5
  secondReserved1 : Alpha 1
  token : BitVec 32
  contractDesc : ContractDesc
  openClose : OpenClose
  oldOpenClose : Alpha 1
  bookTypeChar1 : Alpha 1
  thirdReserved1 : Alpha 1
  newVolume : BitVec 32
  oldAccountNumber : Alpha 10
  participant : Alpha 12
  oldParticipant : Alpha 12
  additionalOrderFlags : BitVec 8
  fourthReserved1 : Alpha 1
  giveUpTrade : Alpha 1
  fifthReserved1 : Alpha 1
  pan : Alpha 10
  oldPan : Alpha 10
  algoId : BitVec 32
  reserved2 : Alpha 2
  lastActivityReference : BitVec 64
  nnfField : Alpha 8
  reserved44 : Alpha 44
  deriving DecidableEq, Repr

namespace TradeConfirmationMessage

def encode (message : TradeConfirmationMessage) : List UInt8 :=
  Alpha.encode message.responseOrderNumber
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 4 message.traderNum
    ++ (Alpha.encode message.accountNum
    ++ (encodeUInt 2 message.buySell
    ++ (encodeUInt 4 message.originalVol
    ++ (encodeUInt 4 message.disclosedVol
    ++ (encodeUInt 4 message.remainingVol
    ++ (encodeUInt 4 message.disclosedVolRemaining
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 4 message.gtd
    ++ (encodeUInt 4 message.fillNumber
    ++ (encodeUInt 4 message.fillQty
    ++ (encodeUInt 4 message.fillPrice
    ++ (encodeUInt 4 message.volFilledToday
    ++ (Alpha.encode message.activityType
    ++ (encodeUInt 4 message.activityTime
    ++ (Alpha.encode message.opOrderNumber
    ++ (Alpha.encode message.opBrokerId
    ++ (Alpha.encode message.secondReserved1
    ++ (encodeUInt 4 message.token
    ++ (ContractDesc.encode message.contractDesc
    ++ (OpenClose.encode message.openClose
    ++ (Alpha.encode message.oldOpenClose
    ++ (Alpha.encode message.bookTypeChar1
    ++ (Alpha.encode message.thirdReserved1
    ++ (encodeUInt 4 message.newVolume
    ++ (Alpha.encode message.oldAccountNumber
    ++ (Alpha.encode message.participant
    ++ (Alpha.encode message.oldParticipant
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.fourthReserved1
    ++ (Alpha.encode message.giveUpTrade
    ++ (Alpha.encode message.fifthReserved1
    ++ (Alpha.encode message.pan
    ++ (Alpha.encode message.oldPan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.reserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.reserved44))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TradeConfirmationMessage × List UInt8) := do
  let (responseOrderNumber, bytes) ← Alpha.decode 8 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (traderNum, bytes) ← decodeUInt 4 bytes
  let (accountNum, bytes) ← Alpha.decode 10 bytes
  let (buySell, bytes) ← decodeUInt 2 bytes
  let (originalVol, bytes) ← decodeUInt 4 bytes
  let (disclosedVol, bytes) ← decodeUInt 4 bytes
  let (remainingVol, bytes) ← decodeUInt 4 bytes
  let (disclosedVolRemaining, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (gtd, bytes) ← decodeUInt 4 bytes
  let (fillNumber, bytes) ← decodeUInt 4 bytes
  let (fillQty, bytes) ← decodeUInt 4 bytes
  let (fillPrice, bytes) ← decodeUInt 4 bytes
  let (volFilledToday, bytes) ← decodeUInt 4 bytes
  let (activityType, bytes) ← Alpha.decode 2 bytes
  let (activityTime, bytes) ← decodeUInt 4 bytes
  let (opOrderNumber, bytes) ← Alpha.decode 8 bytes
  let (opBrokerId, bytes) ← Alpha.decode 5 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  let (token, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (openClose, bytes) ← OpenClose.decode bytes
  let (oldOpenClose, bytes) ← Alpha.decode 1 bytes
  let (bookTypeChar1, bytes) ← Alpha.decode 1 bytes
  let (thirdReserved1, bytes) ← Alpha.decode 1 bytes
  let (newVolume, bytes) ← decodeUInt 4 bytes
  let (oldAccountNumber, bytes) ← Alpha.decode 10 bytes
  let (participant, bytes) ← Alpha.decode 12 bytes
  let (oldParticipant, bytes) ← Alpha.decode 12 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (fourthReserved1, bytes) ← Alpha.decode 1 bytes
  let (giveUpTrade, bytes) ← Alpha.decode 1 bytes
  let (fifthReserved1, bytes) ← Alpha.decode 1 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (oldPan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (reserved44, bytes) ← Alpha.decode 44 bytes
  pure ({ responseOrderNumber, brokerId, reserved1, traderNum, accountNum, buySell, originalVol, disclosedVol, remainingVol, disclosedVolRemaining, price, stOrderFlags, gtd, fillNumber, fillQty, fillPrice, volFilledToday, activityType, activityTime, opOrderNumber, opBrokerId, secondReserved1, token, contractDesc, openClose, oldOpenClose, bookTypeChar1, thirdReserved1, newVolume, oldAccountNumber, participant, oldParticipant, additionalOrderFlags, fourthReserved1, giveUpTrade, fifthReserved1, pan, oldPan, algoId, reserved2, lastActivityReference, nnfField, reserved44 }, bytes)

@[simp] theorem encode_length (message : TradeConfirmationMessage) : (encode message).length = 256 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, OpenClose.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : TradeConfirmationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : TradeConfirmationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpenClose.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeConfirmationMessage

/-- Trade Cancel Confirm Message: 256 bytes -/
structure TradeCancelConfirmMessage where
  responseOrderNumber : Alpha 8
  brokerId : Alpha 5
  reserved1 : Alpha 1
  traderNum : BitVec 32
  accountNum : Alpha 10
  buySell : BitVec 16
  originalVol : BitVec 32
  disclosedVol : BitVec 32
  remainingVol : BitVec 32
  disclosedVolRemaining : BitVec 32
  price : BitVec 32
  stOrderFlags : BitVec 16
  gtd : BitVec 32
  fillNumber : BitVec 32
  fillQty : BitVec 32
  fillPrice : BitVec 32
  volFilledToday : BitVec 32
  activityType : Alpha 2
  activityTime : BitVec 32
  opOrderNumber : Alpha 8
  opBrokerId : Alpha 5
  secondReserved1 : Alpha 1
  token : BitVec 32
  contractDesc : ContractDesc
  openClose : OpenClose
  oldOpenClose : Alpha 1
  bookTypeChar1 : Alpha 1
  thirdReserved1 : Alpha 1
  newVolume : BitVec 32
  oldAccountNumber : Alpha 10
  participant : Alpha 12
  oldParticipant : Alpha 12
  additionalOrderFlags : BitVec 8
  fourthReserved1 : Alpha 1
  giveUpTrade : Alpha 1
  fifthReserved1 : Alpha 1
  pan : Alpha 10
  oldPan : Alpha 10
  algoId : BitVec 32
  reserved2 : Alpha 2
  lastActivityReference : BitVec 64
  nnfField : Alpha 8
  reserved44 : Alpha 44
  deriving DecidableEq, Repr

namespace TradeCancelConfirmMessage

def encode (message : TradeCancelConfirmMessage) : List UInt8 :=
  Alpha.encode message.responseOrderNumber
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 4 message.traderNum
    ++ (Alpha.encode message.accountNum
    ++ (encodeUInt 2 message.buySell
    ++ (encodeUInt 4 message.originalVol
    ++ (encodeUInt 4 message.disclosedVol
    ++ (encodeUInt 4 message.remainingVol
    ++ (encodeUInt 4 message.disclosedVolRemaining
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 4 message.gtd
    ++ (encodeUInt 4 message.fillNumber
    ++ (encodeUInt 4 message.fillQty
    ++ (encodeUInt 4 message.fillPrice
    ++ (encodeUInt 4 message.volFilledToday
    ++ (Alpha.encode message.activityType
    ++ (encodeUInt 4 message.activityTime
    ++ (Alpha.encode message.opOrderNumber
    ++ (Alpha.encode message.opBrokerId
    ++ (Alpha.encode message.secondReserved1
    ++ (encodeUInt 4 message.token
    ++ (ContractDesc.encode message.contractDesc
    ++ (OpenClose.encode message.openClose
    ++ (Alpha.encode message.oldOpenClose
    ++ (Alpha.encode message.bookTypeChar1
    ++ (Alpha.encode message.thirdReserved1
    ++ (encodeUInt 4 message.newVolume
    ++ (Alpha.encode message.oldAccountNumber
    ++ (Alpha.encode message.participant
    ++ (Alpha.encode message.oldParticipant
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.fourthReserved1
    ++ (Alpha.encode message.giveUpTrade
    ++ (Alpha.encode message.fifthReserved1
    ++ (Alpha.encode message.pan
    ++ (Alpha.encode message.oldPan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.reserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.reserved44))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TradeCancelConfirmMessage × List UInt8) := do
  let (responseOrderNumber, bytes) ← Alpha.decode 8 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (traderNum, bytes) ← decodeUInt 4 bytes
  let (accountNum, bytes) ← Alpha.decode 10 bytes
  let (buySell, bytes) ← decodeUInt 2 bytes
  let (originalVol, bytes) ← decodeUInt 4 bytes
  let (disclosedVol, bytes) ← decodeUInt 4 bytes
  let (remainingVol, bytes) ← decodeUInt 4 bytes
  let (disclosedVolRemaining, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (gtd, bytes) ← decodeUInt 4 bytes
  let (fillNumber, bytes) ← decodeUInt 4 bytes
  let (fillQty, bytes) ← decodeUInt 4 bytes
  let (fillPrice, bytes) ← decodeUInt 4 bytes
  let (volFilledToday, bytes) ← decodeUInt 4 bytes
  let (activityType, bytes) ← Alpha.decode 2 bytes
  let (activityTime, bytes) ← decodeUInt 4 bytes
  let (opOrderNumber, bytes) ← Alpha.decode 8 bytes
  let (opBrokerId, bytes) ← Alpha.decode 5 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  let (token, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (openClose, bytes) ← OpenClose.decode bytes
  let (oldOpenClose, bytes) ← Alpha.decode 1 bytes
  let (bookTypeChar1, bytes) ← Alpha.decode 1 bytes
  let (thirdReserved1, bytes) ← Alpha.decode 1 bytes
  let (newVolume, bytes) ← decodeUInt 4 bytes
  let (oldAccountNumber, bytes) ← Alpha.decode 10 bytes
  let (participant, bytes) ← Alpha.decode 12 bytes
  let (oldParticipant, bytes) ← Alpha.decode 12 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (fourthReserved1, bytes) ← Alpha.decode 1 bytes
  let (giveUpTrade, bytes) ← Alpha.decode 1 bytes
  let (fifthReserved1, bytes) ← Alpha.decode 1 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (oldPan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (reserved44, bytes) ← Alpha.decode 44 bytes
  pure ({ responseOrderNumber, brokerId, reserved1, traderNum, accountNum, buySell, originalVol, disclosedVol, remainingVol, disclosedVolRemaining, price, stOrderFlags, gtd, fillNumber, fillQty, fillPrice, volFilledToday, activityType, activityTime, opOrderNumber, opBrokerId, secondReserved1, token, contractDesc, openClose, oldOpenClose, bookTypeChar1, thirdReserved1, newVolume, oldAccountNumber, participant, oldParticipant, additionalOrderFlags, fourthReserved1, giveUpTrade, fifthReserved1, pan, oldPan, algoId, reserved2, lastActivityReference, nnfField, reserved44 }, bytes)

@[simp] theorem encode_length (message : TradeCancelConfirmMessage) : (encode message).length = 256 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, OpenClose.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : TradeCancelConfirmMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : TradeCancelConfirmMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpenClose.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeCancelConfirmMessage

/-- Trade Cancel Reject Message: 256 bytes -/
structure TradeCancelRejectMessage where
  responseOrderNumber : Alpha 8
  brokerId : Alpha 5
  reserved1 : Alpha 1
  traderNum : BitVec 32
  accountNum : Alpha 10
  buySell : BitVec 16
  originalVol : BitVec 32
  disclosedVol : BitVec 32
  remainingVol : BitVec 32
  disclosedVolRemaining : BitVec 32
  price : BitVec 32
  stOrderFlags : BitVec 16
  gtd : BitVec 32
  fillNumber : BitVec 32
  fillQty : BitVec 32
  fillPrice : BitVec 32
  volFilledToday : BitVec 32
  activityType : Alpha 2
  activityTime : BitVec 32
  opOrderNumber : Alpha 8
  opBrokerId : Alpha 5
  secondReserved1 : Alpha 1
  token : BitVec 32
  contractDesc : ContractDesc
  openClose : OpenClose
  oldOpenClose : Alpha 1
  bookTypeChar1 : Alpha 1
  thirdReserved1 : Alpha 1
  newVolume : BitVec 32
  oldAccountNumber : Alpha 10
  participant : Alpha 12
  oldParticipant : Alpha 12
  additionalOrderFlags : BitVec 8
  fourthReserved1 : Alpha 1
  giveUpTrade : Alpha 1
  fifthReserved1 : Alpha 1
  pan : Alpha 10
  oldPan : Alpha 10
  algoId : BitVec 32
  reserved2 : Alpha 2
  lastActivityReference : BitVec 64
  nnfField : Alpha 8
  reserved44 : Alpha 44
  deriving DecidableEq, Repr

namespace TradeCancelRejectMessage

def encode (message : TradeCancelRejectMessage) : List UInt8 :=
  Alpha.encode message.responseOrderNumber
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 4 message.traderNum
    ++ (Alpha.encode message.accountNum
    ++ (encodeUInt 2 message.buySell
    ++ (encodeUInt 4 message.originalVol
    ++ (encodeUInt 4 message.disclosedVol
    ++ (encodeUInt 4 message.remainingVol
    ++ (encodeUInt 4 message.disclosedVolRemaining
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 4 message.gtd
    ++ (encodeUInt 4 message.fillNumber
    ++ (encodeUInt 4 message.fillQty
    ++ (encodeUInt 4 message.fillPrice
    ++ (encodeUInt 4 message.volFilledToday
    ++ (Alpha.encode message.activityType
    ++ (encodeUInt 4 message.activityTime
    ++ (Alpha.encode message.opOrderNumber
    ++ (Alpha.encode message.opBrokerId
    ++ (Alpha.encode message.secondReserved1
    ++ (encodeUInt 4 message.token
    ++ (ContractDesc.encode message.contractDesc
    ++ (OpenClose.encode message.openClose
    ++ (Alpha.encode message.oldOpenClose
    ++ (Alpha.encode message.bookTypeChar1
    ++ (Alpha.encode message.thirdReserved1
    ++ (encodeUInt 4 message.newVolume
    ++ (Alpha.encode message.oldAccountNumber
    ++ (Alpha.encode message.participant
    ++ (Alpha.encode message.oldParticipant
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.fourthReserved1
    ++ (Alpha.encode message.giveUpTrade
    ++ (Alpha.encode message.fifthReserved1
    ++ (Alpha.encode message.pan
    ++ (Alpha.encode message.oldPan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.reserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.reserved44))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TradeCancelRejectMessage × List UInt8) := do
  let (responseOrderNumber, bytes) ← Alpha.decode 8 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (traderNum, bytes) ← decodeUInt 4 bytes
  let (accountNum, bytes) ← Alpha.decode 10 bytes
  let (buySell, bytes) ← decodeUInt 2 bytes
  let (originalVol, bytes) ← decodeUInt 4 bytes
  let (disclosedVol, bytes) ← decodeUInt 4 bytes
  let (remainingVol, bytes) ← decodeUInt 4 bytes
  let (disclosedVolRemaining, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (gtd, bytes) ← decodeUInt 4 bytes
  let (fillNumber, bytes) ← decodeUInt 4 bytes
  let (fillQty, bytes) ← decodeUInt 4 bytes
  let (fillPrice, bytes) ← decodeUInt 4 bytes
  let (volFilledToday, bytes) ← decodeUInt 4 bytes
  let (activityType, bytes) ← Alpha.decode 2 bytes
  let (activityTime, bytes) ← decodeUInt 4 bytes
  let (opOrderNumber, bytes) ← Alpha.decode 8 bytes
  let (opBrokerId, bytes) ← Alpha.decode 5 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  let (token, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (openClose, bytes) ← OpenClose.decode bytes
  let (oldOpenClose, bytes) ← Alpha.decode 1 bytes
  let (bookTypeChar1, bytes) ← Alpha.decode 1 bytes
  let (thirdReserved1, bytes) ← Alpha.decode 1 bytes
  let (newVolume, bytes) ← decodeUInt 4 bytes
  let (oldAccountNumber, bytes) ← Alpha.decode 10 bytes
  let (participant, bytes) ← Alpha.decode 12 bytes
  let (oldParticipant, bytes) ← Alpha.decode 12 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (fourthReserved1, bytes) ← Alpha.decode 1 bytes
  let (giveUpTrade, bytes) ← Alpha.decode 1 bytes
  let (fifthReserved1, bytes) ← Alpha.decode 1 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (oldPan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (reserved44, bytes) ← Alpha.decode 44 bytes
  pure ({ responseOrderNumber, brokerId, reserved1, traderNum, accountNum, buySell, originalVol, disclosedVol, remainingVol, disclosedVolRemaining, price, stOrderFlags, gtd, fillNumber, fillQty, fillPrice, volFilledToday, activityType, activityTime, opOrderNumber, opBrokerId, secondReserved1, token, contractDesc, openClose, oldOpenClose, bookTypeChar1, thirdReserved1, newVolume, oldAccountNumber, participant, oldParticipant, additionalOrderFlags, fourthReserved1, giveUpTrade, fifthReserved1, pan, oldPan, algoId, reserved2, lastActivityReference, nnfField, reserved44 }, bytes)

@[simp] theorem encode_length (message : TradeCancelRejectMessage) : (encode message).length = 256 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, OpenClose.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : TradeCancelRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : TradeCancelRejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpenClose.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeCancelRejectMessage

/-- Trade Modify Confirm Message: 256 bytes -/
structure TradeModifyConfirmMessage where
  responseOrderNumber : Alpha 8
  brokerId : Alpha 5
  reserved1 : Alpha 1
  traderNum : BitVec 32
  accountNum : Alpha 10
  buySell : BitVec 16
  originalVol : BitVec 32
  disclosedVol : BitVec 32
  remainingVol : BitVec 32
  disclosedVolRemaining : BitVec 32
  price : BitVec 32
  stOrderFlags : BitVec 16
  gtd : BitVec 32
  fillNumber : BitVec 32
  fillQty : BitVec 32
  fillPrice : BitVec 32
  volFilledToday : BitVec 32
  activityType : Alpha 2
  activityTime : BitVec 32
  opOrderNumber : Alpha 8
  opBrokerId : Alpha 5
  secondReserved1 : Alpha 1
  token : BitVec 32
  contractDesc : ContractDesc
  openClose : OpenClose
  oldOpenClose : Alpha 1
  bookTypeChar1 : Alpha 1
  thirdReserved1 : Alpha 1
  newVolume : BitVec 32
  oldAccountNumber : Alpha 10
  participant : Alpha 12
  oldParticipant : Alpha 12
  additionalOrderFlags : BitVec 8
  fourthReserved1 : Alpha 1
  giveUpTrade : Alpha 1
  fifthReserved1 : Alpha 1
  pan : Alpha 10
  oldPan : Alpha 10
  algoId : BitVec 32
  reserved2 : Alpha 2
  lastActivityReference : BitVec 64
  nnfField : Alpha 8
  reserved44 : Alpha 44
  deriving DecidableEq, Repr

namespace TradeModifyConfirmMessage

def encode (message : TradeModifyConfirmMessage) : List UInt8 :=
  Alpha.encode message.responseOrderNumber
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 4 message.traderNum
    ++ (Alpha.encode message.accountNum
    ++ (encodeUInt 2 message.buySell
    ++ (encodeUInt 4 message.originalVol
    ++ (encodeUInt 4 message.disclosedVol
    ++ (encodeUInt 4 message.remainingVol
    ++ (encodeUInt 4 message.disclosedVolRemaining
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 4 message.gtd
    ++ (encodeUInt 4 message.fillNumber
    ++ (encodeUInt 4 message.fillQty
    ++ (encodeUInt 4 message.fillPrice
    ++ (encodeUInt 4 message.volFilledToday
    ++ (Alpha.encode message.activityType
    ++ (encodeUInt 4 message.activityTime
    ++ (Alpha.encode message.opOrderNumber
    ++ (Alpha.encode message.opBrokerId
    ++ (Alpha.encode message.secondReserved1
    ++ (encodeUInt 4 message.token
    ++ (ContractDesc.encode message.contractDesc
    ++ (OpenClose.encode message.openClose
    ++ (Alpha.encode message.oldOpenClose
    ++ (Alpha.encode message.bookTypeChar1
    ++ (Alpha.encode message.thirdReserved1
    ++ (encodeUInt 4 message.newVolume
    ++ (Alpha.encode message.oldAccountNumber
    ++ (Alpha.encode message.participant
    ++ (Alpha.encode message.oldParticipant
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.fourthReserved1
    ++ (Alpha.encode message.giveUpTrade
    ++ (Alpha.encode message.fifthReserved1
    ++ (Alpha.encode message.pan
    ++ (Alpha.encode message.oldPan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.reserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.reserved44))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TradeModifyConfirmMessage × List UInt8) := do
  let (responseOrderNumber, bytes) ← Alpha.decode 8 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (traderNum, bytes) ← decodeUInt 4 bytes
  let (accountNum, bytes) ← Alpha.decode 10 bytes
  let (buySell, bytes) ← decodeUInt 2 bytes
  let (originalVol, bytes) ← decodeUInt 4 bytes
  let (disclosedVol, bytes) ← decodeUInt 4 bytes
  let (remainingVol, bytes) ← decodeUInt 4 bytes
  let (disclosedVolRemaining, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (gtd, bytes) ← decodeUInt 4 bytes
  let (fillNumber, bytes) ← decodeUInt 4 bytes
  let (fillQty, bytes) ← decodeUInt 4 bytes
  let (fillPrice, bytes) ← decodeUInt 4 bytes
  let (volFilledToday, bytes) ← decodeUInt 4 bytes
  let (activityType, bytes) ← Alpha.decode 2 bytes
  let (activityTime, bytes) ← decodeUInt 4 bytes
  let (opOrderNumber, bytes) ← Alpha.decode 8 bytes
  let (opBrokerId, bytes) ← Alpha.decode 5 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  let (token, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (openClose, bytes) ← OpenClose.decode bytes
  let (oldOpenClose, bytes) ← Alpha.decode 1 bytes
  let (bookTypeChar1, bytes) ← Alpha.decode 1 bytes
  let (thirdReserved1, bytes) ← Alpha.decode 1 bytes
  let (newVolume, bytes) ← decodeUInt 4 bytes
  let (oldAccountNumber, bytes) ← Alpha.decode 10 bytes
  let (participant, bytes) ← Alpha.decode 12 bytes
  let (oldParticipant, bytes) ← Alpha.decode 12 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (fourthReserved1, bytes) ← Alpha.decode 1 bytes
  let (giveUpTrade, bytes) ← Alpha.decode 1 bytes
  let (fifthReserved1, bytes) ← Alpha.decode 1 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (oldPan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (reserved44, bytes) ← Alpha.decode 44 bytes
  pure ({ responseOrderNumber, brokerId, reserved1, traderNum, accountNum, buySell, originalVol, disclosedVol, remainingVol, disclosedVolRemaining, price, stOrderFlags, gtd, fillNumber, fillQty, fillPrice, volFilledToday, activityType, activityTime, opOrderNumber, opBrokerId, secondReserved1, token, contractDesc, openClose, oldOpenClose, bookTypeChar1, thirdReserved1, newVolume, oldAccountNumber, participant, oldParticipant, additionalOrderFlags, fourthReserved1, giveUpTrade, fifthReserved1, pan, oldPan, algoId, reserved2, lastActivityReference, nnfField, reserved44 }, bytes)

@[simp] theorem encode_length (message : TradeModifyConfirmMessage) : (encode message).length = 256 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, OpenClose.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : TradeModifyConfirmMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : TradeModifyConfirmMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpenClose.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeModifyConfirmMessage

/-- Trade Modify Reject Message: 256 bytes -/
structure TradeModifyRejectMessage where
  responseOrderNumber : Alpha 8
  brokerId : Alpha 5
  reserved1 : Alpha 1
  traderNum : BitVec 32
  accountNum : Alpha 10
  buySell : BitVec 16
  originalVol : BitVec 32
  disclosedVol : BitVec 32
  remainingVol : BitVec 32
  disclosedVolRemaining : BitVec 32
  price : BitVec 32
  stOrderFlags : BitVec 16
  gtd : BitVec 32
  fillNumber : BitVec 32
  fillQty : BitVec 32
  fillPrice : BitVec 32
  volFilledToday : BitVec 32
  activityType : Alpha 2
  activityTime : BitVec 32
  opOrderNumber : Alpha 8
  opBrokerId : Alpha 5
  secondReserved1 : Alpha 1
  token : BitVec 32
  contractDesc : ContractDesc
  openClose : OpenClose
  oldOpenClose : Alpha 1
  bookTypeChar1 : Alpha 1
  thirdReserved1 : Alpha 1
  newVolume : BitVec 32
  oldAccountNumber : Alpha 10
  participant : Alpha 12
  oldParticipant : Alpha 12
  additionalOrderFlags : BitVec 8
  fourthReserved1 : Alpha 1
  giveUpTrade : Alpha 1
  fifthReserved1 : Alpha 1
  pan : Alpha 10
  oldPan : Alpha 10
  algoId : BitVec 32
  reserved2 : Alpha 2
  lastActivityReference : BitVec 64
  nnfField : Alpha 8
  reserved44 : Alpha 44
  deriving DecidableEq, Repr

namespace TradeModifyRejectMessage

def encode (message : TradeModifyRejectMessage) : List UInt8 :=
  Alpha.encode message.responseOrderNumber
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 4 message.traderNum
    ++ (Alpha.encode message.accountNum
    ++ (encodeUInt 2 message.buySell
    ++ (encodeUInt 4 message.originalVol
    ++ (encodeUInt 4 message.disclosedVol
    ++ (encodeUInt 4 message.remainingVol
    ++ (encodeUInt 4 message.disclosedVolRemaining
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 4 message.gtd
    ++ (encodeUInt 4 message.fillNumber
    ++ (encodeUInt 4 message.fillQty
    ++ (encodeUInt 4 message.fillPrice
    ++ (encodeUInt 4 message.volFilledToday
    ++ (Alpha.encode message.activityType
    ++ (encodeUInt 4 message.activityTime
    ++ (Alpha.encode message.opOrderNumber
    ++ (Alpha.encode message.opBrokerId
    ++ (Alpha.encode message.secondReserved1
    ++ (encodeUInt 4 message.token
    ++ (ContractDesc.encode message.contractDesc
    ++ (OpenClose.encode message.openClose
    ++ (Alpha.encode message.oldOpenClose
    ++ (Alpha.encode message.bookTypeChar1
    ++ (Alpha.encode message.thirdReserved1
    ++ (encodeUInt 4 message.newVolume
    ++ (Alpha.encode message.oldAccountNumber
    ++ (Alpha.encode message.participant
    ++ (Alpha.encode message.oldParticipant
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.fourthReserved1
    ++ (Alpha.encode message.giveUpTrade
    ++ (Alpha.encode message.fifthReserved1
    ++ (Alpha.encode message.pan
    ++ (Alpha.encode message.oldPan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.reserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.reserved44))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TradeModifyRejectMessage × List UInt8) := do
  let (responseOrderNumber, bytes) ← Alpha.decode 8 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (traderNum, bytes) ← decodeUInt 4 bytes
  let (accountNum, bytes) ← Alpha.decode 10 bytes
  let (buySell, bytes) ← decodeUInt 2 bytes
  let (originalVol, bytes) ← decodeUInt 4 bytes
  let (disclosedVol, bytes) ← decodeUInt 4 bytes
  let (remainingVol, bytes) ← decodeUInt 4 bytes
  let (disclosedVolRemaining, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (gtd, bytes) ← decodeUInt 4 bytes
  let (fillNumber, bytes) ← decodeUInt 4 bytes
  let (fillQty, bytes) ← decodeUInt 4 bytes
  let (fillPrice, bytes) ← decodeUInt 4 bytes
  let (volFilledToday, bytes) ← decodeUInt 4 bytes
  let (activityType, bytes) ← Alpha.decode 2 bytes
  let (activityTime, bytes) ← decodeUInt 4 bytes
  let (opOrderNumber, bytes) ← Alpha.decode 8 bytes
  let (opBrokerId, bytes) ← Alpha.decode 5 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  let (token, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (openClose, bytes) ← OpenClose.decode bytes
  let (oldOpenClose, bytes) ← Alpha.decode 1 bytes
  let (bookTypeChar1, bytes) ← Alpha.decode 1 bytes
  let (thirdReserved1, bytes) ← Alpha.decode 1 bytes
  let (newVolume, bytes) ← decodeUInt 4 bytes
  let (oldAccountNumber, bytes) ← Alpha.decode 10 bytes
  let (participant, bytes) ← Alpha.decode 12 bytes
  let (oldParticipant, bytes) ← Alpha.decode 12 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (fourthReserved1, bytes) ← Alpha.decode 1 bytes
  let (giveUpTrade, bytes) ← Alpha.decode 1 bytes
  let (fifthReserved1, bytes) ← Alpha.decode 1 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (oldPan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (reserved44, bytes) ← Alpha.decode 44 bytes
  pure ({ responseOrderNumber, brokerId, reserved1, traderNum, accountNum, buySell, originalVol, disclosedVol, remainingVol, disclosedVolRemaining, price, stOrderFlags, gtd, fillNumber, fillQty, fillPrice, volFilledToday, activityType, activityTime, opOrderNumber, opBrokerId, secondReserved1, token, contractDesc, openClose, oldOpenClose, bookTypeChar1, thirdReserved1, newVolume, oldAccountNumber, participant, oldParticipant, additionalOrderFlags, fourthReserved1, giveUpTrade, fifthReserved1, pan, oldPan, algoId, reserved2, lastActivityReference, nnfField, reserved44 }, bytes)

@[simp] theorem encode_length (message : TradeModifyRejectMessage) : (encode message).length = 256 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, OpenClose.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : TradeModifyRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : TradeModifyRejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpenClose.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeModifyRejectMessage

/-- Giveup App Confirm Tm Message: 82 bytes -/
structure GiveupAppConfirmTmMessage where
  reasonCode : BitVec 16
  orderNumber : Alpha 8
  fillNumber : BitVec 32
  instrumentName : Alpha 6
  symbol : Alpha 10
  expiryDate : BitVec 32
  strikePrice : BitVec 32
  optionType : Alpha 2
  caLevel : BitVec 16
  fillVolume : BitVec 32
  fillPrice : BitVec 32
  brokerId : Alpha 5
  filler : Alpha 1
  buySell : BitVec 16
  bookTypeShort2 : BitVec 16
  lastModifiedDateTime : BitVec 32
  initiatedByControl : Alpha 1
  openClose : OpenClose
  reserved1 : Alpha 1
  participant : Alpha 12
  giveupFlag : Alpha 1
  deleted : Alpha 1
  secondReserved1 : Alpha 1
  deriving DecidableEq, Repr

namespace GiveupAppConfirmTmMessage

def encode (message : GiveupAppConfirmTmMessage) : List UInt8 :=
  encodeUInt 2 message.reasonCode
    ++ (Alpha.encode message.orderNumber
    ++ (encodeUInt 4 message.fillNumber
    ++ (Alpha.encode message.instrumentName
    ++ (Alpha.encode message.symbol
    ++ (encodeUInt 4 message.expiryDate
    ++ (encodeUInt 4 message.strikePrice
    ++ (Alpha.encode message.optionType
    ++ (encodeUInt 2 message.caLevel
    ++ (encodeUInt 4 message.fillVolume
    ++ (encodeUInt 4 message.fillPrice
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.filler
    ++ (encodeUInt 2 message.buySell
    ++ (encodeUInt 2 message.bookTypeShort2
    ++ (encodeUInt 4 message.lastModifiedDateTime
    ++ (Alpha.encode message.initiatedByControl
    ++ (OpenClose.encode message.openClose
    ++ (Alpha.encode message.reserved1
    ++ (Alpha.encode message.participant
    ++ (Alpha.encode message.giveupFlag
    ++ (Alpha.encode message.deleted
    ++ (Alpha.encode message.secondReserved1))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (GiveupAppConfirmTmMessage × List UInt8) := do
  let (reasonCode, bytes) ← decodeUInt 2 bytes
  let (orderNumber, bytes) ← Alpha.decode 8 bytes
  let (fillNumber, bytes) ← decodeUInt 4 bytes
  let (instrumentName, bytes) ← Alpha.decode 6 bytes
  let (symbol, bytes) ← Alpha.decode 10 bytes
  let (expiryDate, bytes) ← decodeUInt 4 bytes
  let (strikePrice, bytes) ← decodeUInt 4 bytes
  let (optionType, bytes) ← Alpha.decode 2 bytes
  let (caLevel, bytes) ← decodeUInt 2 bytes
  let (fillVolume, bytes) ← decodeUInt 4 bytes
  let (fillPrice, bytes) ← decodeUInt 4 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (filler, bytes) ← Alpha.decode 1 bytes
  let (buySell, bytes) ← decodeUInt 2 bytes
  let (bookTypeShort2, bytes) ← decodeUInt 2 bytes
  let (lastModifiedDateTime, bytes) ← decodeUInt 4 bytes
  let (initiatedByControl, bytes) ← Alpha.decode 1 bytes
  let (openClose, bytes) ← OpenClose.decode bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (participant, bytes) ← Alpha.decode 12 bytes
  let (giveupFlag, bytes) ← Alpha.decode 1 bytes
  let (deleted, bytes) ← Alpha.decode 1 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  pure ({ reasonCode, orderNumber, fillNumber, instrumentName, symbol, expiryDate, strikePrice, optionType, caLevel, fillVolume, fillPrice, brokerId, filler, buySell, bookTypeShort2, lastModifiedDateTime, initiatedByControl, openClose, reserved1, participant, giveupFlag, deleted, secondReserved1 }, bytes)

@[simp] theorem encode_length (message : GiveupAppConfirmTmMessage) : (encode message).length = 82 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, OpenClose.encode_length]

theorem encode_length_pos (message : GiveupAppConfirmTmMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : GiveupAppConfirmTmMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpenClose.decode_encode, some_bind]
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

end GiveupAppConfirmTmMessage

/-- Giveup Rej Confirm Tm Message: 82 bytes -/
structure GiveupRejConfirmTmMessage where
  reasonCode : BitVec 16
  orderNumber : Alpha 8
  fillNumber : BitVec 32
  instrumentName : Alpha 6
  symbol : Alpha 10
  expiryDate : BitVec 32
  strikePrice : BitVec 32
  optionType : Alpha 2
  caLevel : BitVec 16
  fillVolume : BitVec 32
  fillPrice : BitVec 32
  brokerId : Alpha 5
  filler : Alpha 1
  buySell : BitVec 16
  bookTypeShort2 : BitVec 16
  lastModifiedDateTime : BitVec 32
  initiatedByControl : Alpha 1
  openClose : OpenClose
  reserved1 : Alpha 1
  participant : Alpha 12
  giveupFlag : Alpha 1
  deleted : Alpha 1
  secondReserved1 : Alpha 1
  deriving DecidableEq, Repr

namespace GiveupRejConfirmTmMessage

def encode (message : GiveupRejConfirmTmMessage) : List UInt8 :=
  encodeUInt 2 message.reasonCode
    ++ (Alpha.encode message.orderNumber
    ++ (encodeUInt 4 message.fillNumber
    ++ (Alpha.encode message.instrumentName
    ++ (Alpha.encode message.symbol
    ++ (encodeUInt 4 message.expiryDate
    ++ (encodeUInt 4 message.strikePrice
    ++ (Alpha.encode message.optionType
    ++ (encodeUInt 2 message.caLevel
    ++ (encodeUInt 4 message.fillVolume
    ++ (encodeUInt 4 message.fillPrice
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.filler
    ++ (encodeUInt 2 message.buySell
    ++ (encodeUInt 2 message.bookTypeShort2
    ++ (encodeUInt 4 message.lastModifiedDateTime
    ++ (Alpha.encode message.initiatedByControl
    ++ (OpenClose.encode message.openClose
    ++ (Alpha.encode message.reserved1
    ++ (Alpha.encode message.participant
    ++ (Alpha.encode message.giveupFlag
    ++ (Alpha.encode message.deleted
    ++ (Alpha.encode message.secondReserved1))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (GiveupRejConfirmTmMessage × List UInt8) := do
  let (reasonCode, bytes) ← decodeUInt 2 bytes
  let (orderNumber, bytes) ← Alpha.decode 8 bytes
  let (fillNumber, bytes) ← decodeUInt 4 bytes
  let (instrumentName, bytes) ← Alpha.decode 6 bytes
  let (symbol, bytes) ← Alpha.decode 10 bytes
  let (expiryDate, bytes) ← decodeUInt 4 bytes
  let (strikePrice, bytes) ← decodeUInt 4 bytes
  let (optionType, bytes) ← Alpha.decode 2 bytes
  let (caLevel, bytes) ← decodeUInt 2 bytes
  let (fillVolume, bytes) ← decodeUInt 4 bytes
  let (fillPrice, bytes) ← decodeUInt 4 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (filler, bytes) ← Alpha.decode 1 bytes
  let (buySell, bytes) ← decodeUInt 2 bytes
  let (bookTypeShort2, bytes) ← decodeUInt 2 bytes
  let (lastModifiedDateTime, bytes) ← decodeUInt 4 bytes
  let (initiatedByControl, bytes) ← Alpha.decode 1 bytes
  let (openClose, bytes) ← OpenClose.decode bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (participant, bytes) ← Alpha.decode 12 bytes
  let (giveupFlag, bytes) ← Alpha.decode 1 bytes
  let (deleted, bytes) ← Alpha.decode 1 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  pure ({ reasonCode, orderNumber, fillNumber, instrumentName, symbol, expiryDate, strikePrice, optionType, caLevel, fillVolume, fillPrice, brokerId, filler, buySell, bookTypeShort2, lastModifiedDateTime, initiatedByControl, openClose, reserved1, participant, giveupFlag, deleted, secondReserved1 }, bytes)

@[simp] theorem encode_length (message : GiveupRejConfirmTmMessage) : (encode message).length = 82 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, OpenClose.encode_length]

theorem encode_length_pos (message : GiveupRejConfirmTmMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : GiveupRejConfirmTmMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpenClose.decode_encode, some_bind]
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

end GiveupRejConfirmTmMessage

/-- Any Server Message Payload, selected by Transaction Code -/
inductive ServerMessagePayload where
  | signOnOutMessage (message : SignOnOutMessage) -- 2301
  | tradeConfirmationMessage (message : TradeConfirmationMessage) -- 2222
  | tradeCancelConfirmMessage (message : TradeCancelConfirmMessage) -- 2282
  | tradeCancelRejectMessage (message : TradeCancelRejectMessage) -- 2286
  | tradeModifyConfirmMessage (message : TradeModifyConfirmMessage) -- 2287
  | tradeModifyRejectMessage (message : TradeModifyRejectMessage) -- 2288
  | giveupAppConfirmTmMessage (message : GiveupAppConfirmTmMessage) -- 4506
  | giveupRejConfirmTmMessage (message : GiveupRejConfirmTmMessage) -- 4507
  deriving DecidableEq, Repr

namespace ServerMessagePayload

/-- The Transaction Code each message is sent under -/
def tag : ServerMessagePayload → BitVec 16
  | .signOnOutMessage _ => 2301
  | .tradeConfirmationMessage _ => 2222
  | .tradeCancelConfirmMessage _ => 2282
  | .tradeCancelRejectMessage _ => 2286
  | .tradeModifyConfirmMessage _ => 2287
  | .tradeModifyRejectMessage _ => 2288
  | .giveupAppConfirmTmMessage _ => 4506
  | .giveupRejConfirmTmMessage _ => 4507

def encode : ServerMessagePayload → List UInt8
  | .signOnOutMessage message => SignOnOutMessage.encode message
  | .tradeConfirmationMessage message => TradeConfirmationMessage.encode message
  | .tradeCancelConfirmMessage message => TradeCancelConfirmMessage.encode message
  | .tradeCancelRejectMessage message => TradeCancelRejectMessage.encode message
  | .tradeModifyConfirmMessage message => TradeModifyConfirmMessage.encode message
  | .tradeModifyRejectMessage message => TradeModifyRejectMessage.encode message
  | .giveupAppConfirmTmMessage message => GiveupAppConfirmTmMessage.encode message
  | .giveupRejConfirmTmMessage message => GiveupRejConfirmTmMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ServerMessagePayload) : (encode message).length ≤ 256 := by
  cases message with
  | signOnOutMessage inner =>
    simp only [encode, SignOnOutMessage.encode_length]
    omega
  | tradeConfirmationMessage inner =>
    simp only [encode, TradeConfirmationMessage.encode_length]
    omega
  | tradeCancelConfirmMessage inner =>
    simp only [encode, TradeCancelConfirmMessage.encode_length]
    omega
  | tradeCancelRejectMessage inner =>
    simp only [encode, TradeCancelRejectMessage.encode_length]
    omega
  | tradeModifyConfirmMessage inner =>
    simp only [encode, TradeModifyConfirmMessage.encode_length]
    omega
  | tradeModifyRejectMessage inner =>
    simp only [encode, TradeModifyRejectMessage.encode_length]
    omega
  | giveupAppConfirmTmMessage inner =>
    simp only [encode, GiveupAppConfirmTmMessage.encode_length]
    omega
  | giveupRejConfirmTmMessage inner =>
    simp only [encode, GiveupRejConfirmTmMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (ServerMessagePayload × List UInt8) :=
  if tag = 2301 then (SignOnOutMessage.decode bytes).map fun (message, rest) => (.signOnOutMessage message, rest)
  else if tag = 2222 then (TradeConfirmationMessage.decode bytes).map fun (message, rest) => (.tradeConfirmationMessage message, rest)
  else if tag = 2282 then (TradeCancelConfirmMessage.decode bytes).map fun (message, rest) => (.tradeCancelConfirmMessage message, rest)
  else if tag = 2286 then (TradeCancelRejectMessage.decode bytes).map fun (message, rest) => (.tradeCancelRejectMessage message, rest)
  else if tag = 2287 then (TradeModifyConfirmMessage.decode bytes).map fun (message, rest) => (.tradeModifyConfirmMessage message, rest)
  else if tag = 2288 then (TradeModifyRejectMessage.decode bytes).map fun (message, rest) => (.tradeModifyRejectMessage message, rest)
  else if tag = 4506 then (GiveupAppConfirmTmMessage.decode bytes).map fun (message, rest) => (.giveupAppConfirmTmMessage message, rest)
  else if tag = 4507 then (GiveupRejConfirmTmMessage.decode bytes).map fun (message, rest) => (.giveupRejConfirmTmMessage message, rest)
  else none

@[simp] theorem decode_encode (message : ServerMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ServerMessagePayload

/-- Server Direct Packet -/
structure ServerDirectPacket where
  packetSequenceNumber : BitVec 32
  checksum : Alpha 16
  logTime : BitVec 32
  alphaChar : Alpha 2
  traderId : BitVec 32
  errorCode : BitVec 16
  headerTimestamp : BitVec 64
  timeStamp1 : Alpha 8
  timeStamp2 : Alpha 8
  messageLength : BitVec 16
  serverMessagePayload : ServerMessagePayload
  deriving DecidableEq, Repr

namespace ServerDirectPacket

def encodeBody (message : ServerDirectPacket) : List UInt8 :=
  encodeUInt 4 message.packetSequenceNumber
    ++ (Alpha.encode message.checksum
    ++ (encodeUInt 2 (ServerMessagePayload.tag message.serverMessagePayload)
    ++ (encodeUInt 4 message.logTime
    ++ (Alpha.encode message.alphaChar
    ++ (encodeUInt 4 message.traderId
    ++ (encodeUInt 2 message.errorCode
    ++ (encodeUInt 8 message.headerTimestamp
    ++ (Alpha.encode message.timeStamp1
    ++ (Alpha.encode message.timeStamp2
    ++ (encodeUInt 2 message.messageLength
    ++ (ServerMessagePayload.encode message.serverMessagePayload)))))))))))

def decodeBody (bytes : List UInt8) : Option (ServerDirectPacket × List UInt8) := do
  let (packetSequenceNumber, bytes) ← decodeUInt 4 bytes
  let (checksum, bytes) ← Alpha.decode 16 bytes
  let (transactionCode, bytes) ← decodeUInt 2 bytes
  let (logTime, bytes) ← decodeUInt 4 bytes
  let (alphaChar, bytes) ← Alpha.decode 2 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (errorCode, bytes) ← decodeUInt 2 bytes
  let (headerTimestamp, bytes) ← decodeUInt 8 bytes
  let (timeStamp1, bytes) ← Alpha.decode 8 bytes
  let (timeStamp2, bytes) ← Alpha.decode 8 bytes
  let (messageLength, bytes) ← decodeUInt 2 bytes
  let (serverMessagePayload, bytes) ← ServerMessagePayload.decode transactionCode bytes
  pure ({ packetSequenceNumber, checksum, logTime, alphaChar, traderId, errorCode, headerTimestamp, timeStamp1, timeStamp2, messageLength, serverMessagePayload }, bytes)

theorem decodeBody_encodeBody (message : ServerDirectPacket) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
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
  rw [ServerMessagePayload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : ServerDirectPacket) : (encodeBody message).length + 2 < 256 ^ 2 := by
  unfold encodeBody
  cases message.serverMessagePayload with
  | signOnOutMessage inner =>
    simp only [ServerMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, SignOnOutMessage.encode_length]
    omega
  | tradeConfirmationMessage inner =>
    simp only [ServerMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, TradeConfirmationMessage.encode_length]
    omega
  | tradeCancelConfirmMessage inner =>
    simp only [ServerMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, TradeCancelConfirmMessage.encode_length]
    omega
  | tradeCancelRejectMessage inner =>
    simp only [ServerMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, TradeCancelRejectMessage.encode_length]
    omega
  | tradeModifyConfirmMessage inner =>
    simp only [ServerMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, TradeModifyConfirmMessage.encode_length]
    omega
  | tradeModifyRejectMessage inner =>
    simp only [ServerMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, TradeModifyRejectMessage.encode_length]
    omega
  | giveupAppConfirmTmMessage inner =>
    simp only [ServerMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, GiveupAppConfirmTmMessage.encode_length]
    omega
  | giveupRejConfirmTmMessage inner =>
    simp only [ServerMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, GiveupRejConfirmTmMessage.encode_length]
    omega

/-- Size rule: Packet Length counts the bytes after it plus 2, so it is written from the body and checked on decode -/
def encode : ServerDirectPacket → List UInt8 :=
  encodeFramed 2 2 encodeBody

def decode : List UInt8 → Option (ServerDirectPacket × List UInt8) :=
  decodeFramed 2 2 decodeBody

@[simp] theorem decode_encode (message : ServerDirectPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 2 2 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : ServerDirectPacket) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end ServerDirectPacket

/-- Server Packet -/
structure ServerPacket where
  serverDirectPacket : List ServerDirectPacket
  deriving DecidableEq, Repr

namespace ServerPacket

def encode (message : ServerPacket) : List UInt8 :=
  encodeMany ServerDirectPacket.encode message.serverDirectPacket

def decode (bytes : List UInt8) : Option ServerPacket := do
  let serverDirectPacket ← decodeAll ServerDirectPacket.decode bytes.length bytes
  pure { serverDirectPacket }

theorem decode_encode (message : ServerPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany ServerDirectPacket.encode ServerDirectPacket.decode ServerDirectPacket.decode_encode ServerDirectPacket.encode_length_pos message.serverDirectPacket _ (encodeMany_length_ge ServerDirectPacket.encode ServerDirectPacket.encode_length_pos message.serverDirectPacket), some_bind]
  rfl

end ServerPacket

end Omi.NseNsecomDropcopyNnfdirectV15Server
