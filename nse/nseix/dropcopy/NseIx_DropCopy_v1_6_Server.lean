import Wire

/-!
# National Stock Exchange of India Ltd Drop Copy v1.6

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.

Note: St Order Flags is a bit field set, proven as its 2 byte integer rather than bit by bit

Note: Additional Order Flags is a bit field set, proven as its 1 byte integer rather than bit by bit

License: MIT No Attribution
-/

namespace Omi.NseNseixDropcopyNnfdirectV16Server

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

/-- Initiated By Control: one byte code -/
def InitiatedByControl.codes : List UInt8 :=
  [0x59, 0x4E]

inductive InitiatedByControl where
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ InitiatedByControl.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InitiatedByControl

def toByte : InitiatedByControl → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : InitiatedByControl :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : InitiatedByControl :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InitiatedByControl) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : InitiatedByControl) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (InitiatedByControl × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : InitiatedByControl) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : InitiatedByControl) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : InitiatedByControl) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end InitiatedByControl

/-- Modified Cancelled By: one byte code -/
def ModifiedCancelledBy.codes : List UInt8 :=
  [0x54, 0x42, 0x4D]

inductive ModifiedCancelledBy where
  | trader -- Trader
  | branchManager -- Branch Manager
  | corporateManager -- Corporate Manager
  | unlisted (byte : { byte : UInt8 // byte ∉ ModifiedCancelledBy.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ModifiedCancelledBy

def toByte : ModifiedCancelledBy → UInt8
  | .trader => 0x54
  | .branchManager => 0x42
  | .corporateManager => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ModifiedCancelledBy :=
  if byte = 0x54 then .trader
  else if byte = 0x42 then .branchManager
  else .corporateManager

def ofByte (byte : UInt8) : ModifiedCancelledBy :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ModifiedCancelledBy) : ofByte value.toByte = value := by
  cases value with
  | trader => decide
  | branchManager => decide
  | corporateManager => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ModifiedCancelledBy) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ModifiedCancelledBy × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ModifiedCancelledBy) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ModifiedCancelledBy) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ModifiedCancelledBy) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ModifiedCancelledBy

/-- Open Close 1: one byte code -/
def OpenClose1.codes : List UInt8 :=
  [0x4F, 0x43]

inductive OpenClose1 where
  | open_ -- Open
  | close -- Close
  | unlisted (byte : { byte : UInt8 // byte ∉ OpenClose1.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OpenClose1

def toByte : OpenClose1 → UInt8
  | .open_ => 0x4F
  | .close => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OpenClose1 :=
  if byte = 0x4F then .open_
  else .close

def ofByte (byte : UInt8) : OpenClose1 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OpenClose1) : ofByte value.toByte = value := by
  cases value with
  | open_ => decide
  | close => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OpenClose1) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OpenClose1 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OpenClose1) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OpenClose1) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OpenClose1) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OpenClose1

/-- Open Close 2: one byte code -/
def OpenClose2.codes : List UInt8 :=
  [0x4F, 0x43]

inductive OpenClose2 where
  | open_ -- Open
  | close -- Close
  | unlisted (byte : { byte : UInt8 // byte ∉ OpenClose2.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OpenClose2

def toByte : OpenClose2 → UInt8
  | .open_ => 0x4F
  | .close => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OpenClose2 :=
  if byte = 0x4F then .open_
  else .close

def ofByte (byte : UInt8) : OpenClose2 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OpenClose2) : ofByte value.toByte = value := by
  cases value with
  | open_ => decide
  | close => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OpenClose2) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OpenClose2 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OpenClose2) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OpenClose2) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OpenClose2) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OpenClose2

/-- Sign On Out Message: 174 bytes -/
structure SignOnOutMessage where
  userId : BitVec 32
  password : Alpha 8
  reserved8 : Alpha 8
  reserved30 : Alpha 30
  brokerId : Alpha 5
  reserved119 : Alpha 119
  deriving DecidableEq, Repr

namespace SignOnOutMessage

def encode (message : SignOnOutMessage) : List UInt8 :=
  encodeUInt 4 message.userId
    ++ (Alpha.encode message.password
    ++ (Alpha.encode message.reserved8
    ++ (Alpha.encode message.reserved30
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.reserved119)))))

def decode (bytes : List UInt8) : Option (SignOnOutMessage × List UInt8) := do
  let (userId, bytes) ← decodeUInt 4 bytes
  let (password, bytes) ← Alpha.decode 8 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  let (reserved30, bytes) ← Alpha.decode 30 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (reserved119, bytes) ← Alpha.decode 119 bytes
  pure ({ userId, password, reserved8, reserved30, brokerId, reserved119 }, bytes)

@[simp] theorem encode_length (message : SignOnOutMessage) : (encode message).length = 174 := by
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
  tradeBookType : Alpha 1
  thirdReserved1 : Alpha 1
  newVolume : BitVec 32
  oldAccountNumber : Alpha 10
  participant : Alpha 12
  oldParticipant : Alpha 12
  additionalOrderFlags : BitVec 8
  fourthReserved1 : Alpha 1
  giveUpTrade : Alpha 1
  fifthReserved1 : Alpha 1
  reserved10 : Alpha 10
  echoBack : Alpha 16
  reserved60 : Alpha 60
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
    ++ (Alpha.encode message.tradeBookType
    ++ (Alpha.encode message.thirdReserved1
    ++ (encodeUInt 4 message.newVolume
    ++ (Alpha.encode message.oldAccountNumber
    ++ (Alpha.encode message.participant
    ++ (Alpha.encode message.oldParticipant
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.fourthReserved1
    ++ (Alpha.encode message.giveUpTrade
    ++ (Alpha.encode message.fifthReserved1
    ++ (Alpha.encode message.reserved10
    ++ (Alpha.encode message.echoBack
    ++ (Alpha.encode message.reserved60))))))))))))))))))))))))))))))))))))))

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
  let (tradeBookType, bytes) ← Alpha.decode 1 bytes
  let (thirdReserved1, bytes) ← Alpha.decode 1 bytes
  let (newVolume, bytes) ← decodeUInt 4 bytes
  let (oldAccountNumber, bytes) ← Alpha.decode 10 bytes
  let (participant, bytes) ← Alpha.decode 12 bytes
  let (oldParticipant, bytes) ← Alpha.decode 12 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (fourthReserved1, bytes) ← Alpha.decode 1 bytes
  let (giveUpTrade, bytes) ← Alpha.decode 1 bytes
  let (fifthReserved1, bytes) ← Alpha.decode 1 bytes
  let (reserved10, bytes) ← Alpha.decode 10 bytes
  let (echoBack, bytes) ← Alpha.decode 16 bytes
  let (reserved60, bytes) ← Alpha.decode 60 bytes
  pure ({ responseOrderNumber, brokerId, reserved1, traderNum, accountNum, buySell, originalVol, disclosedVol, remainingVol, disclosedVolRemaining, price, stOrderFlags, gtd, fillNumber, fillQty, fillPrice, volFilledToday, activityType, activityTime, opOrderNumber, opBrokerId, secondReserved1, token, contractDesc, openClose, oldOpenClose, tradeBookType, thirdReserved1, newVolume, oldAccountNumber, participant, oldParticipant, additionalOrderFlags, fourthReserved1, giveUpTrade, fifthReserved1, reserved10, echoBack, reserved60 }, bytes)

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
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeConfirmationMessage

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
  tradeBookType : Alpha 1
  thirdReserved1 : Alpha 1
  newVolume : BitVec 32
  oldAccountNumber : Alpha 10
  participant : Alpha 12
  oldParticipant : Alpha 12
  additionalOrderFlags : BitVec 8
  fourthReserved1 : Alpha 1
  giveUpTrade : Alpha 1
  fifthReserved1 : Alpha 1
  reserved10 : Alpha 10
  echoBack : Alpha 16
  reserved60 : Alpha 60
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
    ++ (Alpha.encode message.tradeBookType
    ++ (Alpha.encode message.thirdReserved1
    ++ (encodeUInt 4 message.newVolume
    ++ (Alpha.encode message.oldAccountNumber
    ++ (Alpha.encode message.participant
    ++ (Alpha.encode message.oldParticipant
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.fourthReserved1
    ++ (Alpha.encode message.giveUpTrade
    ++ (Alpha.encode message.fifthReserved1
    ++ (Alpha.encode message.reserved10
    ++ (Alpha.encode message.echoBack
    ++ (Alpha.encode message.reserved60))))))))))))))))))))))))))))))))))))))

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
  let (tradeBookType, bytes) ← Alpha.decode 1 bytes
  let (thirdReserved1, bytes) ← Alpha.decode 1 bytes
  let (newVolume, bytes) ← decodeUInt 4 bytes
  let (oldAccountNumber, bytes) ← Alpha.decode 10 bytes
  let (participant, bytes) ← Alpha.decode 12 bytes
  let (oldParticipant, bytes) ← Alpha.decode 12 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (fourthReserved1, bytes) ← Alpha.decode 1 bytes
  let (giveUpTrade, bytes) ← Alpha.decode 1 bytes
  let (fifthReserved1, bytes) ← Alpha.decode 1 bytes
  let (reserved10, bytes) ← Alpha.decode 10 bytes
  let (echoBack, bytes) ← Alpha.decode 16 bytes
  let (reserved60, bytes) ← Alpha.decode 60 bytes
  pure ({ responseOrderNumber, brokerId, reserved1, traderNum, accountNum, buySell, originalVol, disclosedVol, remainingVol, disclosedVolRemaining, price, stOrderFlags, gtd, fillNumber, fillQty, fillPrice, volFilledToday, activityType, activityTime, opOrderNumber, opBrokerId, secondReserved1, token, contractDesc, openClose, oldOpenClose, tradeBookType, thirdReserved1, newVolume, oldAccountNumber, participant, oldParticipant, additionalOrderFlags, fourthReserved1, giveUpTrade, fifthReserved1, reserved10, echoBack, reserved60 }, bytes)

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
  tradeBookType : Alpha 1
  thirdReserved1 : Alpha 1
  newVolume : BitVec 32
  oldAccountNumber : Alpha 10
  participant : Alpha 12
  oldParticipant : Alpha 12
  additionalOrderFlags : BitVec 8
  fourthReserved1 : Alpha 1
  giveUpTrade : Alpha 1
  fifthReserved1 : Alpha 1
  reserved10 : Alpha 10
  echoBack : Alpha 16
  reserved60 : Alpha 60
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
    ++ (Alpha.encode message.tradeBookType
    ++ (Alpha.encode message.thirdReserved1
    ++ (encodeUInt 4 message.newVolume
    ++ (Alpha.encode message.oldAccountNumber
    ++ (Alpha.encode message.participant
    ++ (Alpha.encode message.oldParticipant
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.fourthReserved1
    ++ (Alpha.encode message.giveUpTrade
    ++ (Alpha.encode message.fifthReserved1
    ++ (Alpha.encode message.reserved10
    ++ (Alpha.encode message.echoBack
    ++ (Alpha.encode message.reserved60))))))))))))))))))))))))))))))))))))))

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
  let (tradeBookType, bytes) ← Alpha.decode 1 bytes
  let (thirdReserved1, bytes) ← Alpha.decode 1 bytes
  let (newVolume, bytes) ← decodeUInt 4 bytes
  let (oldAccountNumber, bytes) ← Alpha.decode 10 bytes
  let (participant, bytes) ← Alpha.decode 12 bytes
  let (oldParticipant, bytes) ← Alpha.decode 12 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (fourthReserved1, bytes) ← Alpha.decode 1 bytes
  let (giveUpTrade, bytes) ← Alpha.decode 1 bytes
  let (fifthReserved1, bytes) ← Alpha.decode 1 bytes
  let (reserved10, bytes) ← Alpha.decode 10 bytes
  let (echoBack, bytes) ← Alpha.decode 16 bytes
  let (reserved60, bytes) ← Alpha.decode 60 bytes
  pure ({ responseOrderNumber, brokerId, reserved1, traderNum, accountNum, buySell, originalVol, disclosedVol, remainingVol, disclosedVolRemaining, price, stOrderFlags, gtd, fillNumber, fillQty, fillPrice, volFilledToday, activityType, activityTime, opOrderNumber, opBrokerId, secondReserved1, token, contractDesc, openClose, oldOpenClose, tradeBookType, thirdReserved1, newVolume, oldAccountNumber, participant, oldParticipant, additionalOrderFlags, fourthReserved1, giveUpTrade, fifthReserved1, reserved10, echoBack, reserved60 }, bytes)

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
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeModifyRejectMessage

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
  tradeBookType : Alpha 1
  thirdReserved1 : Alpha 1
  newVolume : BitVec 32
  oldAccountNumber : Alpha 10
  participant : Alpha 12
  oldParticipant : Alpha 12
  additionalOrderFlags : BitVec 8
  fourthReserved1 : Alpha 1
  giveUpTrade : Alpha 1
  fifthReserved1 : Alpha 1
  reserved10 : Alpha 10
  echoBack : Alpha 16
  reserved60 : Alpha 60
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
    ++ (Alpha.encode message.tradeBookType
    ++ (Alpha.encode message.thirdReserved1
    ++ (encodeUInt 4 message.newVolume
    ++ (Alpha.encode message.oldAccountNumber
    ++ (Alpha.encode message.participant
    ++ (Alpha.encode message.oldParticipant
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.fourthReserved1
    ++ (Alpha.encode message.giveUpTrade
    ++ (Alpha.encode message.fifthReserved1
    ++ (Alpha.encode message.reserved10
    ++ (Alpha.encode message.echoBack
    ++ (Alpha.encode message.reserved60))))))))))))))))))))))))))))))))))))))

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
  let (tradeBookType, bytes) ← Alpha.decode 1 bytes
  let (thirdReserved1, bytes) ← Alpha.decode 1 bytes
  let (newVolume, bytes) ← decodeUInt 4 bytes
  let (oldAccountNumber, bytes) ← Alpha.decode 10 bytes
  let (participant, bytes) ← Alpha.decode 12 bytes
  let (oldParticipant, bytes) ← Alpha.decode 12 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (fourthReserved1, bytes) ← Alpha.decode 1 bytes
  let (giveUpTrade, bytes) ← Alpha.decode 1 bytes
  let (fifthReserved1, bytes) ← Alpha.decode 1 bytes
  let (reserved10, bytes) ← Alpha.decode 10 bytes
  let (echoBack, bytes) ← Alpha.decode 16 bytes
  let (reserved60, bytes) ← Alpha.decode 60 bytes
  pure ({ responseOrderNumber, brokerId, reserved1, traderNum, accountNum, buySell, originalVol, disclosedVol, remainingVol, disclosedVolRemaining, price, stOrderFlags, gtd, fillNumber, fillQty, fillPrice, volFilledToday, activityType, activityTime, opOrderNumber, opBrokerId, secondReserved1, token, contractDesc, openClose, oldOpenClose, tradeBookType, thirdReserved1, newVolume, oldAccountNumber, participant, oldParticipant, additionalOrderFlags, fourthReserved1, giveUpTrade, fifthReserved1, reserved10, echoBack, reserved60 }, bytes)

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
  tradeBookType : Alpha 1
  thirdReserved1 : Alpha 1
  newVolume : BitVec 32
  oldAccountNumber : Alpha 10
  participant : Alpha 12
  oldParticipant : Alpha 12
  additionalOrderFlags : BitVec 8
  fourthReserved1 : Alpha 1
  giveUpTrade : Alpha 1
  fifthReserved1 : Alpha 1
  reserved10 : Alpha 10
  echoBack : Alpha 16
  reserved60 : Alpha 60
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
    ++ (Alpha.encode message.tradeBookType
    ++ (Alpha.encode message.thirdReserved1
    ++ (encodeUInt 4 message.newVolume
    ++ (Alpha.encode message.oldAccountNumber
    ++ (Alpha.encode message.participant
    ++ (Alpha.encode message.oldParticipant
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.fourthReserved1
    ++ (Alpha.encode message.giveUpTrade
    ++ (Alpha.encode message.fifthReserved1
    ++ (Alpha.encode message.reserved10
    ++ (Alpha.encode message.echoBack
    ++ (Alpha.encode message.reserved60))))))))))))))))))))))))))))))))))))))

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
  let (tradeBookType, bytes) ← Alpha.decode 1 bytes
  let (thirdReserved1, bytes) ← Alpha.decode 1 bytes
  let (newVolume, bytes) ← decodeUInt 4 bytes
  let (oldAccountNumber, bytes) ← Alpha.decode 10 bytes
  let (participant, bytes) ← Alpha.decode 12 bytes
  let (oldParticipant, bytes) ← Alpha.decode 12 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (fourthReserved1, bytes) ← Alpha.decode 1 bytes
  let (giveUpTrade, bytes) ← Alpha.decode 1 bytes
  let (fifthReserved1, bytes) ← Alpha.decode 1 bytes
  let (reserved10, bytes) ← Alpha.decode 10 bytes
  let (echoBack, bytes) ← Alpha.decode 16 bytes
  let (reserved60, bytes) ← Alpha.decode 60 bytes
  pure ({ responseOrderNumber, brokerId, reserved1, traderNum, accountNum, buySell, originalVol, disclosedVol, remainingVol, disclosedVolRemaining, price, stOrderFlags, gtd, fillNumber, fillQty, fillPrice, volFilledToday, activityType, activityTime, opOrderNumber, opBrokerId, secondReserved1, token, contractDesc, openClose, oldOpenClose, tradeBookType, thirdReserved1, newVolume, oldAccountNumber, participant, oldParticipant, additionalOrderFlags, fourthReserved1, giveUpTrade, fifthReserved1, reserved10, echoBack, reserved60 }, bytes)

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
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeCancelRejectMessage

/-- Nlt Trade Confirmation Message: 256 bytes -/
structure NltTradeConfirmationMessage where
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
  tradeBookType : Alpha 1
  thirdReserved1 : Alpha 1
  newVolume : BitVec 32
  oldAccountNumber : Alpha 10
  participant : Alpha 12
  oldParticipant : Alpha 12
  additionalOrderFlags : BitVec 8
  fourthReserved1 : Alpha 1
  giveUpTrade : Alpha 1
  fifthReserved1 : Alpha 1
  reserved10 : Alpha 10
  echoBack : Alpha 16
  reserved60 : Alpha 60
  deriving DecidableEq, Repr

namespace NltTradeConfirmationMessage

def encode (message : NltTradeConfirmationMessage) : List UInt8 :=
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
    ++ (Alpha.encode message.tradeBookType
    ++ (Alpha.encode message.thirdReserved1
    ++ (encodeUInt 4 message.newVolume
    ++ (Alpha.encode message.oldAccountNumber
    ++ (Alpha.encode message.participant
    ++ (Alpha.encode message.oldParticipant
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.fourthReserved1
    ++ (Alpha.encode message.giveUpTrade
    ++ (Alpha.encode message.fifthReserved1
    ++ (Alpha.encode message.reserved10
    ++ (Alpha.encode message.echoBack
    ++ (Alpha.encode message.reserved60))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (NltTradeConfirmationMessage × List UInt8) := do
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
  let (tradeBookType, bytes) ← Alpha.decode 1 bytes
  let (thirdReserved1, bytes) ← Alpha.decode 1 bytes
  let (newVolume, bytes) ← decodeUInt 4 bytes
  let (oldAccountNumber, bytes) ← Alpha.decode 10 bytes
  let (participant, bytes) ← Alpha.decode 12 bytes
  let (oldParticipant, bytes) ← Alpha.decode 12 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (fourthReserved1, bytes) ← Alpha.decode 1 bytes
  let (giveUpTrade, bytes) ← Alpha.decode 1 bytes
  let (fifthReserved1, bytes) ← Alpha.decode 1 bytes
  let (reserved10, bytes) ← Alpha.decode 10 bytes
  let (echoBack, bytes) ← Alpha.decode 16 bytes
  let (reserved60, bytes) ← Alpha.decode 60 bytes
  pure ({ responseOrderNumber, brokerId, reserved1, traderNum, accountNum, buySell, originalVol, disclosedVol, remainingVol, disclosedVolRemaining, price, stOrderFlags, gtd, fillNumber, fillQty, fillPrice, volFilledToday, activityType, activityTime, opOrderNumber, opBrokerId, secondReserved1, token, contractDesc, openClose, oldOpenClose, tradeBookType, thirdReserved1, newVolume, oldAccountNumber, participant, oldParticipant, additionalOrderFlags, fourthReserved1, giveUpTrade, fifthReserved1, reserved10, echoBack, reserved60 }, bytes)

@[simp] theorem encode_length (message : NltTradeConfirmationMessage) : (encode message).length = 256 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, OpenClose.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : NltTradeConfirmationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : NltTradeConfirmationMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end NltTradeConfirmationMessage

/-- Nlt Trd Mod Confirmation Message: 256 bytes -/
structure NltTrdModConfirmationMessage where
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
  tradeBookType : Alpha 1
  thirdReserved1 : Alpha 1
  newVolume : BitVec 32
  oldAccountNumber : Alpha 10
  participant : Alpha 12
  oldParticipant : Alpha 12
  additionalOrderFlags : BitVec 8
  fourthReserved1 : Alpha 1
  giveUpTrade : Alpha 1
  fifthReserved1 : Alpha 1
  reserved10 : Alpha 10
  echoBack : Alpha 16
  reserved60 : Alpha 60
  deriving DecidableEq, Repr

namespace NltTrdModConfirmationMessage

def encode (message : NltTrdModConfirmationMessage) : List UInt8 :=
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
    ++ (Alpha.encode message.tradeBookType
    ++ (Alpha.encode message.thirdReserved1
    ++ (encodeUInt 4 message.newVolume
    ++ (Alpha.encode message.oldAccountNumber
    ++ (Alpha.encode message.participant
    ++ (Alpha.encode message.oldParticipant
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.fourthReserved1
    ++ (Alpha.encode message.giveUpTrade
    ++ (Alpha.encode message.fifthReserved1
    ++ (Alpha.encode message.reserved10
    ++ (Alpha.encode message.echoBack
    ++ (Alpha.encode message.reserved60))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (NltTrdModConfirmationMessage × List UInt8) := do
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
  let (tradeBookType, bytes) ← Alpha.decode 1 bytes
  let (thirdReserved1, bytes) ← Alpha.decode 1 bytes
  let (newVolume, bytes) ← decodeUInt 4 bytes
  let (oldAccountNumber, bytes) ← Alpha.decode 10 bytes
  let (participant, bytes) ← Alpha.decode 12 bytes
  let (oldParticipant, bytes) ← Alpha.decode 12 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (fourthReserved1, bytes) ← Alpha.decode 1 bytes
  let (giveUpTrade, bytes) ← Alpha.decode 1 bytes
  let (fifthReserved1, bytes) ← Alpha.decode 1 bytes
  let (reserved10, bytes) ← Alpha.decode 10 bytes
  let (echoBack, bytes) ← Alpha.decode 16 bytes
  let (reserved60, bytes) ← Alpha.decode 60 bytes
  pure ({ responseOrderNumber, brokerId, reserved1, traderNum, accountNum, buySell, originalVol, disclosedVol, remainingVol, disclosedVolRemaining, price, stOrderFlags, gtd, fillNumber, fillQty, fillPrice, volFilledToday, activityType, activityTime, opOrderNumber, opBrokerId, secondReserved1, token, contractDesc, openClose, oldOpenClose, tradeBookType, thirdReserved1, newVolume, oldAccountNumber, participant, oldParticipant, additionalOrderFlags, fourthReserved1, giveUpTrade, fifthReserved1, reserved10, echoBack, reserved60 }, bytes)

@[simp] theorem encode_length (message : NltTrdModConfirmationMessage) : (encode message).length = 256 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, OpenClose.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : NltTrdModConfirmationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : NltTrdModConfirmationMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end NltTrdModConfirmationMessage

/-- Nlt Trd Mod Reject Message: 256 bytes -/
structure NltTrdModRejectMessage where
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
  tradeBookType : Alpha 1
  thirdReserved1 : Alpha 1
  newVolume : BitVec 32
  oldAccountNumber : Alpha 10
  participant : Alpha 12
  oldParticipant : Alpha 12
  additionalOrderFlags : BitVec 8
  fourthReserved1 : Alpha 1
  giveUpTrade : Alpha 1
  fifthReserved1 : Alpha 1
  reserved10 : Alpha 10
  echoBack : Alpha 16
  reserved60 : Alpha 60
  deriving DecidableEq, Repr

namespace NltTrdModRejectMessage

def encode (message : NltTrdModRejectMessage) : List UInt8 :=
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
    ++ (Alpha.encode message.tradeBookType
    ++ (Alpha.encode message.thirdReserved1
    ++ (encodeUInt 4 message.newVolume
    ++ (Alpha.encode message.oldAccountNumber
    ++ (Alpha.encode message.participant
    ++ (Alpha.encode message.oldParticipant
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.fourthReserved1
    ++ (Alpha.encode message.giveUpTrade
    ++ (Alpha.encode message.fifthReserved1
    ++ (Alpha.encode message.reserved10
    ++ (Alpha.encode message.echoBack
    ++ (Alpha.encode message.reserved60))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (NltTrdModRejectMessage × List UInt8) := do
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
  let (tradeBookType, bytes) ← Alpha.decode 1 bytes
  let (thirdReserved1, bytes) ← Alpha.decode 1 bytes
  let (newVolume, bytes) ← decodeUInt 4 bytes
  let (oldAccountNumber, bytes) ← Alpha.decode 10 bytes
  let (participant, bytes) ← Alpha.decode 12 bytes
  let (oldParticipant, bytes) ← Alpha.decode 12 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (fourthReserved1, bytes) ← Alpha.decode 1 bytes
  let (giveUpTrade, bytes) ← Alpha.decode 1 bytes
  let (fifthReserved1, bytes) ← Alpha.decode 1 bytes
  let (reserved10, bytes) ← Alpha.decode 10 bytes
  let (echoBack, bytes) ← Alpha.decode 16 bytes
  let (reserved60, bytes) ← Alpha.decode 60 bytes
  pure ({ responseOrderNumber, brokerId, reserved1, traderNum, accountNum, buySell, originalVol, disclosedVol, remainingVol, disclosedVolRemaining, price, stOrderFlags, gtd, fillNumber, fillQty, fillPrice, volFilledToday, activityType, activityTime, opOrderNumber, opBrokerId, secondReserved1, token, contractDesc, openClose, oldOpenClose, tradeBookType, thirdReserved1, newVolume, oldAccountNumber, participant, oldParticipant, additionalOrderFlags, fourthReserved1, giveUpTrade, fifthReserved1, reserved10, echoBack, reserved60 }, bytes)

@[simp] theorem encode_length (message : NltTrdModRejectMessage) : (encode message).length = 256 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, OpenClose.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : NltTrdModRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : NltTrdModRejectMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end NltTrdModRejectMessage

/-- Nlt Trd Cxl Confirmation Message: 256 bytes -/
structure NltTrdCxlConfirmationMessage where
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
  tradeBookType : Alpha 1
  thirdReserved1 : Alpha 1
  newVolume : BitVec 32
  oldAccountNumber : Alpha 10
  participant : Alpha 12
  oldParticipant : Alpha 12
  additionalOrderFlags : BitVec 8
  fourthReserved1 : Alpha 1
  giveUpTrade : Alpha 1
  fifthReserved1 : Alpha 1
  reserved10 : Alpha 10
  echoBack : Alpha 16
  reserved60 : Alpha 60
  deriving DecidableEq, Repr

namespace NltTrdCxlConfirmationMessage

def encode (message : NltTrdCxlConfirmationMessage) : List UInt8 :=
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
    ++ (Alpha.encode message.tradeBookType
    ++ (Alpha.encode message.thirdReserved1
    ++ (encodeUInt 4 message.newVolume
    ++ (Alpha.encode message.oldAccountNumber
    ++ (Alpha.encode message.participant
    ++ (Alpha.encode message.oldParticipant
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.fourthReserved1
    ++ (Alpha.encode message.giveUpTrade
    ++ (Alpha.encode message.fifthReserved1
    ++ (Alpha.encode message.reserved10
    ++ (Alpha.encode message.echoBack
    ++ (Alpha.encode message.reserved60))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (NltTrdCxlConfirmationMessage × List UInt8) := do
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
  let (tradeBookType, bytes) ← Alpha.decode 1 bytes
  let (thirdReserved1, bytes) ← Alpha.decode 1 bytes
  let (newVolume, bytes) ← decodeUInt 4 bytes
  let (oldAccountNumber, bytes) ← Alpha.decode 10 bytes
  let (participant, bytes) ← Alpha.decode 12 bytes
  let (oldParticipant, bytes) ← Alpha.decode 12 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (fourthReserved1, bytes) ← Alpha.decode 1 bytes
  let (giveUpTrade, bytes) ← Alpha.decode 1 bytes
  let (fifthReserved1, bytes) ← Alpha.decode 1 bytes
  let (reserved10, bytes) ← Alpha.decode 10 bytes
  let (echoBack, bytes) ← Alpha.decode 16 bytes
  let (reserved60, bytes) ← Alpha.decode 60 bytes
  pure ({ responseOrderNumber, brokerId, reserved1, traderNum, accountNum, buySell, originalVol, disclosedVol, remainingVol, disclosedVolRemaining, price, stOrderFlags, gtd, fillNumber, fillQty, fillPrice, volFilledToday, activityType, activityTime, opOrderNumber, opBrokerId, secondReserved1, token, contractDesc, openClose, oldOpenClose, tradeBookType, thirdReserved1, newVolume, oldAccountNumber, participant, oldParticipant, additionalOrderFlags, fourthReserved1, giveUpTrade, fifthReserved1, reserved10, echoBack, reserved60 }, bytes)

@[simp] theorem encode_length (message : NltTrdCxlConfirmationMessage) : (encode message).length = 256 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, OpenClose.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : NltTrdCxlConfirmationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : NltTrdCxlConfirmationMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end NltTrdCxlConfirmationMessage

/-- Nlt Trd Cxl Reject Message: 256 bytes -/
structure NltTrdCxlRejectMessage where
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
  tradeBookType : Alpha 1
  thirdReserved1 : Alpha 1
  newVolume : BitVec 32
  oldAccountNumber : Alpha 10
  participant : Alpha 12
  oldParticipant : Alpha 12
  additionalOrderFlags : BitVec 8
  fourthReserved1 : Alpha 1
  giveUpTrade : Alpha 1
  fifthReserved1 : Alpha 1
  reserved10 : Alpha 10
  echoBack : Alpha 16
  reserved60 : Alpha 60
  deriving DecidableEq, Repr

namespace NltTrdCxlRejectMessage

def encode (message : NltTrdCxlRejectMessage) : List UInt8 :=
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
    ++ (Alpha.encode message.tradeBookType
    ++ (Alpha.encode message.thirdReserved1
    ++ (encodeUInt 4 message.newVolume
    ++ (Alpha.encode message.oldAccountNumber
    ++ (Alpha.encode message.participant
    ++ (Alpha.encode message.oldParticipant
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.fourthReserved1
    ++ (Alpha.encode message.giveUpTrade
    ++ (Alpha.encode message.fifthReserved1
    ++ (Alpha.encode message.reserved10
    ++ (Alpha.encode message.echoBack
    ++ (Alpha.encode message.reserved60))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (NltTrdCxlRejectMessage × List UInt8) := do
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
  let (tradeBookType, bytes) ← Alpha.decode 1 bytes
  let (thirdReserved1, bytes) ← Alpha.decode 1 bytes
  let (newVolume, bytes) ← decodeUInt 4 bytes
  let (oldAccountNumber, bytes) ← Alpha.decode 10 bytes
  let (participant, bytes) ← Alpha.decode 12 bytes
  let (oldParticipant, bytes) ← Alpha.decode 12 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (fourthReserved1, bytes) ← Alpha.decode 1 bytes
  let (giveUpTrade, bytes) ← Alpha.decode 1 bytes
  let (fifthReserved1, bytes) ← Alpha.decode 1 bytes
  let (reserved10, bytes) ← Alpha.decode 10 bytes
  let (echoBack, bytes) ← Alpha.decode 16 bytes
  let (reserved60, bytes) ← Alpha.decode 60 bytes
  pure ({ responseOrderNumber, brokerId, reserved1, traderNum, accountNum, buySell, originalVol, disclosedVol, remainingVol, disclosedVolRemaining, price, stOrderFlags, gtd, fillNumber, fillQty, fillPrice, volFilledToday, activityType, activityTime, opOrderNumber, opBrokerId, secondReserved1, token, contractDesc, openClose, oldOpenClose, tradeBookType, thirdReserved1, newVolume, oldAccountNumber, participant, oldParticipant, additionalOrderFlags, fourthReserved1, giveUpTrade, fifthReserved1, reserved10, echoBack, reserved60 }, bytes)

@[simp] theorem encode_length (message : NltTrdCxlRejectMessage) : (encode message).length = 256 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, OpenClose.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : NltTrdCxlRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : NltTrdCxlRejectMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end NltTrdCxlRejectMessage

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
  bookType : BitVec 16
  lastModifiedDateTime : BitVec 32
  initiatedByControl : InitiatedByControl
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
    ++ (encodeUInt 2 message.bookType
    ++ (encodeUInt 4 message.lastModifiedDateTime
    ++ (InitiatedByControl.encode message.initiatedByControl
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
  let (bookType, bytes) ← decodeUInt 2 bytes
  let (lastModifiedDateTime, bytes) ← decodeUInt 4 bytes
  let (initiatedByControl, bytes) ← InitiatedByControl.decode bytes
  let (openClose, bytes) ← OpenClose.decode bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (participant, bytes) ← Alpha.decode 12 bytes
  let (giveupFlag, bytes) ← Alpha.decode 1 bytes
  let (deleted, bytes) ← Alpha.decode 1 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  pure ({ reasonCode, orderNumber, fillNumber, instrumentName, symbol, expiryDate, strikePrice, optionType, caLevel, fillVolume, fillPrice, brokerId, filler, buySell, bookType, lastModifiedDateTime, initiatedByControl, openClose, reserved1, participant, giveupFlag, deleted, secondReserved1 }, bytes)

@[simp] theorem encode_length (message : GiveupAppConfirmTmMessage) : (encode message).length = 82 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, InitiatedByControl.encode_length, OpenClose.encode_length]

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
  rw [List.append_assoc, InitiatedByControl.decode_encode, some_bind]
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
  bookType : BitVec 16
  lastModifiedDateTime : BitVec 32
  initiatedByControl : InitiatedByControl
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
    ++ (encodeUInt 2 message.bookType
    ++ (encodeUInt 4 message.lastModifiedDateTime
    ++ (InitiatedByControl.encode message.initiatedByControl
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
  let (bookType, bytes) ← decodeUInt 2 bytes
  let (lastModifiedDateTime, bytes) ← decodeUInt 4 bytes
  let (initiatedByControl, bytes) ← InitiatedByControl.decode bytes
  let (openClose, bytes) ← OpenClose.decode bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (participant, bytes) ← Alpha.decode 12 bytes
  let (giveupFlag, bytes) ← Alpha.decode 1 bytes
  let (deleted, bytes) ← Alpha.decode 1 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  pure ({ reasonCode, orderNumber, fillNumber, instrumentName, symbol, expiryDate, strikePrice, optionType, caLevel, fillVolume, fillPrice, brokerId, filler, buySell, bookType, lastModifiedDateTime, initiatedByControl, openClose, reserved1, participant, giveupFlag, deleted, secondReserved1 }, bytes)

@[simp] theorem encode_length (message : GiveupRejConfirmTmMessage) : (encode message).length = 82 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, InitiatedByControl.encode_length, OpenClose.encode_length]

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
  rw [List.append_assoc, InitiatedByControl.decode_encode, some_bind]
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

/-- Board Lot Out Message: 276 bytes -/
structure BoardLotOutMessage where
  participantType : Alpha 1
  reserved1 : Alpha 1
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  modifiedCancelledBy : ModifiedCancelledBy
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
  bookType : BitVec 16
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
  openClose : OpenClose
  settlor : Alpha 12
  proClientIndicator : BitVec 16
  settlementPeriod : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag : Alpha 1
  reference : Alpha 4
  nnfField : Alpha 8
  mktReplay : Alpha 8
  echoBack : Alpha 16
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  deriving DecidableEq, Repr

namespace BoardLotOutMessage

def encode (message : BoardLotOutMessage) : List UInt8 :=
  Alpha.encode message.participantType
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (ModifiedCancelledBy.encode message.modifiedCancelledBy
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
    ++ (encodeUInt 2 message.bookType
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
    ++ (OpenClose.encode message.openClose
    ++ (Alpha.encode message.settlor
    ++ (encodeUInt 2 message.proClientIndicator
    ++ (encodeUInt 2 message.settlementPeriod
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag
    ++ (Alpha.encode message.reference
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.mktReplay
    ++ (Alpha.encode message.echoBack
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52)))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (BoardLotOutMessage × List UInt8) := do
  let (participantType, bytes) ← Alpha.decode 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (modifiedCancelledBy, bytes) ← ModifiedCancelledBy.decode bytes
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
  let (bookType, bytes) ← decodeUInt 2 bytes
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
  let (openClose, bytes) ← OpenClose.decode bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  let (proClientIndicator, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 4 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← Alpha.decode 8 bytes
  let (echoBack, bytes) ← Alpha.decode 16 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  pure ({ participantType, reserved1, competitorPeriod, solicitorPeriod, modifiedCancelledBy, secondReserved1, reasonCode, reserved4, tokenNo, contractDesc, counterPartyBrokerId, thirdReserved1, reserved2, closeoutFlag, fourthReserved1, orderType, orderNumber, accountNumber, bookType, buySellIndicator, disclosedVolume, disclosedVolumeRemaining, totalVolumeRemaining, volume, volumeFilledToday, price, triggerPrice, goodTillDate, entryDateTime, minimumFillAonVolume, lastModified, stOrderFlags, branchId, traderId, brokerId, cOrdFiller, openClose, settlor, proClientIndicator, settlementPeriod, additionalOrderFlags, giveupFlag, reference, nnfField, mktReplay, echoBack, lastActivityReference, reserved52 }, bytes)

@[simp] theorem encode_length (message : BoardLotOutMessage) : (encode message).length = 276 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ModifiedCancelledBy.encode_length, ContractDesc.encode_length, OpenClose.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : BoardLotOutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : BoardLotOutMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, ModifiedCancelledBy.decode_encode, some_bind]
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
  rw [List.append_assoc, OpenClose.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end BoardLotOutMessage

/-- Order Mod Out Message: 276 bytes -/
structure OrderModOutMessage where
  participantType : Alpha 1
  reserved1 : Alpha 1
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  modifiedCancelledBy : ModifiedCancelledBy
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
  bookType : BitVec 16
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
  openClose : OpenClose
  settlor : Alpha 12
  proClientIndicator : BitVec 16
  settlementPeriod : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag : Alpha 1
  reference : Alpha 4
  nnfField : Alpha 8
  mktReplay : Alpha 8
  echoBack : Alpha 16
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  deriving DecidableEq, Repr

namespace OrderModOutMessage

def encode (message : OrderModOutMessage) : List UInt8 :=
  Alpha.encode message.participantType
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (ModifiedCancelledBy.encode message.modifiedCancelledBy
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
    ++ (encodeUInt 2 message.bookType
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
    ++ (OpenClose.encode message.openClose
    ++ (Alpha.encode message.settlor
    ++ (encodeUInt 2 message.proClientIndicator
    ++ (encodeUInt 2 message.settlementPeriod
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag
    ++ (Alpha.encode message.reference
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.mktReplay
    ++ (Alpha.encode message.echoBack
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52)))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderModOutMessage × List UInt8) := do
  let (participantType, bytes) ← Alpha.decode 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (modifiedCancelledBy, bytes) ← ModifiedCancelledBy.decode bytes
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
  let (bookType, bytes) ← decodeUInt 2 bytes
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
  let (openClose, bytes) ← OpenClose.decode bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  let (proClientIndicator, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 4 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← Alpha.decode 8 bytes
  let (echoBack, bytes) ← Alpha.decode 16 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  pure ({ participantType, reserved1, competitorPeriod, solicitorPeriod, modifiedCancelledBy, secondReserved1, reasonCode, reserved4, tokenNo, contractDesc, counterPartyBrokerId, thirdReserved1, reserved2, closeoutFlag, fourthReserved1, orderType, orderNumber, accountNumber, bookType, buySellIndicator, disclosedVolume, disclosedVolumeRemaining, totalVolumeRemaining, volume, volumeFilledToday, price, triggerPrice, goodTillDate, entryDateTime, minimumFillAonVolume, lastModified, stOrderFlags, branchId, traderId, brokerId, cOrdFiller, openClose, settlor, proClientIndicator, settlementPeriod, additionalOrderFlags, giveupFlag, reference, nnfField, mktReplay, echoBack, lastActivityReference, reserved52 }, bytes)

@[simp] theorem encode_length (message : OrderModOutMessage) : (encode message).length = 276 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ModifiedCancelledBy.encode_length, ContractDesc.encode_length, OpenClose.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : OrderModOutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OrderModOutMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, ModifiedCancelledBy.decode_encode, some_bind]
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
  rw [List.append_assoc, OpenClose.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderModOutMessage

/-- Order Mod Reject Message: 276 bytes -/
structure OrderModRejectMessage where
  participantType : Alpha 1
  reserved1 : Alpha 1
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  modifiedCancelledBy : ModifiedCancelledBy
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
  bookType : BitVec 16
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
  openClose : OpenClose
  settlor : Alpha 12
  proClientIndicator : BitVec 16
  settlementPeriod : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag : Alpha 1
  reference : Alpha 4
  nnfField : Alpha 8
  mktReplay : Alpha 8
  echoBack : Alpha 16
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  deriving DecidableEq, Repr

namespace OrderModRejectMessage

def encode (message : OrderModRejectMessage) : List UInt8 :=
  Alpha.encode message.participantType
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (ModifiedCancelledBy.encode message.modifiedCancelledBy
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
    ++ (encodeUInt 2 message.bookType
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
    ++ (OpenClose.encode message.openClose
    ++ (Alpha.encode message.settlor
    ++ (encodeUInt 2 message.proClientIndicator
    ++ (encodeUInt 2 message.settlementPeriod
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag
    ++ (Alpha.encode message.reference
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.mktReplay
    ++ (Alpha.encode message.echoBack
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52)))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderModRejectMessage × List UInt8) := do
  let (participantType, bytes) ← Alpha.decode 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (modifiedCancelledBy, bytes) ← ModifiedCancelledBy.decode bytes
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
  let (bookType, bytes) ← decodeUInt 2 bytes
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
  let (openClose, bytes) ← OpenClose.decode bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  let (proClientIndicator, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 4 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← Alpha.decode 8 bytes
  let (echoBack, bytes) ← Alpha.decode 16 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  pure ({ participantType, reserved1, competitorPeriod, solicitorPeriod, modifiedCancelledBy, secondReserved1, reasonCode, reserved4, tokenNo, contractDesc, counterPartyBrokerId, thirdReserved1, reserved2, closeoutFlag, fourthReserved1, orderType, orderNumber, accountNumber, bookType, buySellIndicator, disclosedVolume, disclosedVolumeRemaining, totalVolumeRemaining, volume, volumeFilledToday, price, triggerPrice, goodTillDate, entryDateTime, minimumFillAonVolume, lastModified, stOrderFlags, branchId, traderId, brokerId, cOrdFiller, openClose, settlor, proClientIndicator, settlementPeriod, additionalOrderFlags, giveupFlag, reference, nnfField, mktReplay, echoBack, lastActivityReference, reserved52 }, bytes)

@[simp] theorem encode_length (message : OrderModRejectMessage) : (encode message).length = 276 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ModifiedCancelledBy.encode_length, ContractDesc.encode_length, OpenClose.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : OrderModRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OrderModRejectMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, ModifiedCancelledBy.decode_encode, some_bind]
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
  rw [List.append_assoc, OpenClose.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderModRejectMessage

/-- Order Cancel Out Message: 276 bytes -/
structure OrderCancelOutMessage where
  participantType : Alpha 1
  reserved1 : Alpha 1
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  modifiedCancelledBy : ModifiedCancelledBy
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
  bookType : BitVec 16
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
  openClose : OpenClose
  settlor : Alpha 12
  proClientIndicator : BitVec 16
  settlementPeriod : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag : Alpha 1
  reference : Alpha 4
  nnfField : Alpha 8
  mktReplay : Alpha 8
  echoBack : Alpha 16
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  deriving DecidableEq, Repr

namespace OrderCancelOutMessage

def encode (message : OrderCancelOutMessage) : List UInt8 :=
  Alpha.encode message.participantType
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (ModifiedCancelledBy.encode message.modifiedCancelledBy
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
    ++ (encodeUInt 2 message.bookType
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
    ++ (OpenClose.encode message.openClose
    ++ (Alpha.encode message.settlor
    ++ (encodeUInt 2 message.proClientIndicator
    ++ (encodeUInt 2 message.settlementPeriod
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag
    ++ (Alpha.encode message.reference
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.mktReplay
    ++ (Alpha.encode message.echoBack
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52)))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderCancelOutMessage × List UInt8) := do
  let (participantType, bytes) ← Alpha.decode 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (modifiedCancelledBy, bytes) ← ModifiedCancelledBy.decode bytes
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
  let (bookType, bytes) ← decodeUInt 2 bytes
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
  let (openClose, bytes) ← OpenClose.decode bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  let (proClientIndicator, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 4 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← Alpha.decode 8 bytes
  let (echoBack, bytes) ← Alpha.decode 16 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  pure ({ participantType, reserved1, competitorPeriod, solicitorPeriod, modifiedCancelledBy, secondReserved1, reasonCode, reserved4, tokenNo, contractDesc, counterPartyBrokerId, thirdReserved1, reserved2, closeoutFlag, fourthReserved1, orderType, orderNumber, accountNumber, bookType, buySellIndicator, disclosedVolume, disclosedVolumeRemaining, totalVolumeRemaining, volume, volumeFilledToday, price, triggerPrice, goodTillDate, entryDateTime, minimumFillAonVolume, lastModified, stOrderFlags, branchId, traderId, brokerId, cOrdFiller, openClose, settlor, proClientIndicator, settlementPeriod, additionalOrderFlags, giveupFlag, reference, nnfField, mktReplay, echoBack, lastActivityReference, reserved52 }, bytes)

@[simp] theorem encode_length (message : OrderCancelOutMessage) : (encode message).length = 276 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ModifiedCancelledBy.encode_length, ContractDesc.encode_length, OpenClose.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : OrderCancelOutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OrderCancelOutMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, ModifiedCancelledBy.decode_encode, some_bind]
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
  rw [List.append_assoc, OpenClose.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderCancelOutMessage

/-- Order Cancel Reject Message: 276 bytes -/
structure OrderCancelRejectMessage where
  participantType : Alpha 1
  reserved1 : Alpha 1
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  modifiedCancelledBy : ModifiedCancelledBy
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
  bookType : BitVec 16
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
  openClose : OpenClose
  settlor : Alpha 12
  proClientIndicator : BitVec 16
  settlementPeriod : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag : Alpha 1
  reference : Alpha 4
  nnfField : Alpha 8
  mktReplay : Alpha 8
  echoBack : Alpha 16
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  deriving DecidableEq, Repr

namespace OrderCancelRejectMessage

def encode (message : OrderCancelRejectMessage) : List UInt8 :=
  Alpha.encode message.participantType
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (ModifiedCancelledBy.encode message.modifiedCancelledBy
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
    ++ (encodeUInt 2 message.bookType
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
    ++ (OpenClose.encode message.openClose
    ++ (Alpha.encode message.settlor
    ++ (encodeUInt 2 message.proClientIndicator
    ++ (encodeUInt 2 message.settlementPeriod
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag
    ++ (Alpha.encode message.reference
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.mktReplay
    ++ (Alpha.encode message.echoBack
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52)))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderCancelRejectMessage × List UInt8) := do
  let (participantType, bytes) ← Alpha.decode 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (modifiedCancelledBy, bytes) ← ModifiedCancelledBy.decode bytes
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
  let (bookType, bytes) ← decodeUInt 2 bytes
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
  let (openClose, bytes) ← OpenClose.decode bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  let (proClientIndicator, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 4 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← Alpha.decode 8 bytes
  let (echoBack, bytes) ← Alpha.decode 16 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  pure ({ participantType, reserved1, competitorPeriod, solicitorPeriod, modifiedCancelledBy, secondReserved1, reasonCode, reserved4, tokenNo, contractDesc, counterPartyBrokerId, thirdReserved1, reserved2, closeoutFlag, fourthReserved1, orderType, orderNumber, accountNumber, bookType, buySellIndicator, disclosedVolume, disclosedVolumeRemaining, totalVolumeRemaining, volume, volumeFilledToday, price, triggerPrice, goodTillDate, entryDateTime, minimumFillAonVolume, lastModified, stOrderFlags, branchId, traderId, brokerId, cOrdFiller, openClose, settlor, proClientIndicator, settlementPeriod, additionalOrderFlags, giveupFlag, reference, nnfField, mktReplay, echoBack, lastActivityReference, reserved52 }, bytes)

@[simp] theorem encode_length (message : OrderCancelRejectMessage) : (encode message).length = 276 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ModifiedCancelledBy.encode_length, ContractDesc.encode_length, OpenClose.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : OrderCancelRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OrderCancelRejectMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, ModifiedCancelledBy.decode_encode, some_bind]
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
  rw [List.append_assoc, OpenClose.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderCancelRejectMessage

/-- Order Confirmation Message: 276 bytes -/
structure OrderConfirmationMessage where
  participantType : Alpha 1
  reserved1 : Alpha 1
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  modifiedCancelledBy : ModifiedCancelledBy
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
  bookType : BitVec 16
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
  openClose : OpenClose
  settlor : Alpha 12
  proClientIndicator : BitVec 16
  settlementPeriod : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag : Alpha 1
  reference : Alpha 4
  nnfField : Alpha 8
  mktReplay : Alpha 8
  echoBack : Alpha 16
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  deriving DecidableEq, Repr

namespace OrderConfirmationMessage

def encode (message : OrderConfirmationMessage) : List UInt8 :=
  Alpha.encode message.participantType
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (ModifiedCancelledBy.encode message.modifiedCancelledBy
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
    ++ (encodeUInt 2 message.bookType
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
    ++ (OpenClose.encode message.openClose
    ++ (Alpha.encode message.settlor
    ++ (encodeUInt 2 message.proClientIndicator
    ++ (encodeUInt 2 message.settlementPeriod
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag
    ++ (Alpha.encode message.reference
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.mktReplay
    ++ (Alpha.encode message.echoBack
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52)))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderConfirmationMessage × List UInt8) := do
  let (participantType, bytes) ← Alpha.decode 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (modifiedCancelledBy, bytes) ← ModifiedCancelledBy.decode bytes
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
  let (bookType, bytes) ← decodeUInt 2 bytes
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
  let (openClose, bytes) ← OpenClose.decode bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  let (proClientIndicator, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 4 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← Alpha.decode 8 bytes
  let (echoBack, bytes) ← Alpha.decode 16 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  pure ({ participantType, reserved1, competitorPeriod, solicitorPeriod, modifiedCancelledBy, secondReserved1, reasonCode, reserved4, tokenNo, contractDesc, counterPartyBrokerId, thirdReserved1, reserved2, closeoutFlag, fourthReserved1, orderType, orderNumber, accountNumber, bookType, buySellIndicator, disclosedVolume, disclosedVolumeRemaining, totalVolumeRemaining, volume, volumeFilledToday, price, triggerPrice, goodTillDate, entryDateTime, minimumFillAonVolume, lastModified, stOrderFlags, branchId, traderId, brokerId, cOrdFiller, openClose, settlor, proClientIndicator, settlementPeriod, additionalOrderFlags, giveupFlag, reference, nnfField, mktReplay, echoBack, lastActivityReference, reserved52 }, bytes)

@[simp] theorem encode_length (message : OrderConfirmationMessage) : (encode message).length = 276 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ModifiedCancelledBy.encode_length, ContractDesc.encode_length, OpenClose.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : OrderConfirmationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OrderConfirmationMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, ModifiedCancelledBy.decode_encode, some_bind]
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
  rw [List.append_assoc, OpenClose.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderConfirmationMessage

/-- Order Mod Confirmation Message: 276 bytes -/
structure OrderModConfirmationMessage where
  participantType : Alpha 1
  reserved1 : Alpha 1
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  modifiedCancelledBy : ModifiedCancelledBy
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
  bookType : BitVec 16
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
  openClose : OpenClose
  settlor : Alpha 12
  proClientIndicator : BitVec 16
  settlementPeriod : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag : Alpha 1
  reference : Alpha 4
  nnfField : Alpha 8
  mktReplay : Alpha 8
  echoBack : Alpha 16
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  deriving DecidableEq, Repr

namespace OrderModConfirmationMessage

def encode (message : OrderModConfirmationMessage) : List UInt8 :=
  Alpha.encode message.participantType
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (ModifiedCancelledBy.encode message.modifiedCancelledBy
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
    ++ (encodeUInt 2 message.bookType
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
    ++ (OpenClose.encode message.openClose
    ++ (Alpha.encode message.settlor
    ++ (encodeUInt 2 message.proClientIndicator
    ++ (encodeUInt 2 message.settlementPeriod
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag
    ++ (Alpha.encode message.reference
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.mktReplay
    ++ (Alpha.encode message.echoBack
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52)))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderModConfirmationMessage × List UInt8) := do
  let (participantType, bytes) ← Alpha.decode 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (modifiedCancelledBy, bytes) ← ModifiedCancelledBy.decode bytes
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
  let (bookType, bytes) ← decodeUInt 2 bytes
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
  let (openClose, bytes) ← OpenClose.decode bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  let (proClientIndicator, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 4 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← Alpha.decode 8 bytes
  let (echoBack, bytes) ← Alpha.decode 16 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  pure ({ participantType, reserved1, competitorPeriod, solicitorPeriod, modifiedCancelledBy, secondReserved1, reasonCode, reserved4, tokenNo, contractDesc, counterPartyBrokerId, thirdReserved1, reserved2, closeoutFlag, fourthReserved1, orderType, orderNumber, accountNumber, bookType, buySellIndicator, disclosedVolume, disclosedVolumeRemaining, totalVolumeRemaining, volume, volumeFilledToday, price, triggerPrice, goodTillDate, entryDateTime, minimumFillAonVolume, lastModified, stOrderFlags, branchId, traderId, brokerId, cOrdFiller, openClose, settlor, proClientIndicator, settlementPeriod, additionalOrderFlags, giveupFlag, reference, nnfField, mktReplay, echoBack, lastActivityReference, reserved52 }, bytes)

@[simp] theorem encode_length (message : OrderModConfirmationMessage) : (encode message).length = 276 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ModifiedCancelledBy.encode_length, ContractDesc.encode_length, OpenClose.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : OrderModConfirmationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OrderModConfirmationMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, ModifiedCancelledBy.decode_encode, some_bind]
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
  rw [List.append_assoc, OpenClose.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderModConfirmationMessage

/-- Order Cancel Confirmation Message: 276 bytes -/
structure OrderCancelConfirmationMessage where
  participantType : Alpha 1
  reserved1 : Alpha 1
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  modifiedCancelledBy : ModifiedCancelledBy
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
  bookType : BitVec 16
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
  openClose : OpenClose
  settlor : Alpha 12
  proClientIndicator : BitVec 16
  settlementPeriod : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag : Alpha 1
  reference : Alpha 4
  nnfField : Alpha 8
  mktReplay : Alpha 8
  echoBack : Alpha 16
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  deriving DecidableEq, Repr

namespace OrderCancelConfirmationMessage

def encode (message : OrderCancelConfirmationMessage) : List UInt8 :=
  Alpha.encode message.participantType
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (ModifiedCancelledBy.encode message.modifiedCancelledBy
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
    ++ (encodeUInt 2 message.bookType
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
    ++ (OpenClose.encode message.openClose
    ++ (Alpha.encode message.settlor
    ++ (encodeUInt 2 message.proClientIndicator
    ++ (encodeUInt 2 message.settlementPeriod
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag
    ++ (Alpha.encode message.reference
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.mktReplay
    ++ (Alpha.encode message.echoBack
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52)))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderCancelConfirmationMessage × List UInt8) := do
  let (participantType, bytes) ← Alpha.decode 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (modifiedCancelledBy, bytes) ← ModifiedCancelledBy.decode bytes
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
  let (bookType, bytes) ← decodeUInt 2 bytes
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
  let (openClose, bytes) ← OpenClose.decode bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  let (proClientIndicator, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 4 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← Alpha.decode 8 bytes
  let (echoBack, bytes) ← Alpha.decode 16 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  pure ({ participantType, reserved1, competitorPeriod, solicitorPeriod, modifiedCancelledBy, secondReserved1, reasonCode, reserved4, tokenNo, contractDesc, counterPartyBrokerId, thirdReserved1, reserved2, closeoutFlag, fourthReserved1, orderType, orderNumber, accountNumber, bookType, buySellIndicator, disclosedVolume, disclosedVolumeRemaining, totalVolumeRemaining, volume, volumeFilledToday, price, triggerPrice, goodTillDate, entryDateTime, minimumFillAonVolume, lastModified, stOrderFlags, branchId, traderId, brokerId, cOrdFiller, openClose, settlor, proClientIndicator, settlementPeriod, additionalOrderFlags, giveupFlag, reference, nnfField, mktReplay, echoBack, lastActivityReference, reserved52 }, bytes)

@[simp] theorem encode_length (message : OrderCancelConfirmationMessage) : (encode message).length = 276 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ModifiedCancelledBy.encode_length, ContractDesc.encode_length, OpenClose.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : OrderCancelConfirmationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OrderCancelConfirmationMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, ModifiedCancelledBy.decode_encode, some_bind]
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
  rw [List.append_assoc, OpenClose.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderCancelConfirmationMessage

/-- Freeze To Control Message: 276 bytes -/
structure FreezeToControlMessage where
  participantType : Alpha 1
  reserved1 : Alpha 1
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  modifiedCancelledBy : ModifiedCancelledBy
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
  bookType : BitVec 16
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
  openClose : OpenClose
  settlor : Alpha 12
  proClientIndicator : BitVec 16
  settlementPeriod : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag : Alpha 1
  reference : Alpha 4
  nnfField : Alpha 8
  mktReplay : Alpha 8
  echoBack : Alpha 16
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  deriving DecidableEq, Repr

namespace FreezeToControlMessage

def encode (message : FreezeToControlMessage) : List UInt8 :=
  Alpha.encode message.participantType
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (ModifiedCancelledBy.encode message.modifiedCancelledBy
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
    ++ (encodeUInt 2 message.bookType
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
    ++ (OpenClose.encode message.openClose
    ++ (Alpha.encode message.settlor
    ++ (encodeUInt 2 message.proClientIndicator
    ++ (encodeUInt 2 message.settlementPeriod
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag
    ++ (Alpha.encode message.reference
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.mktReplay
    ++ (Alpha.encode message.echoBack
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52)))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (FreezeToControlMessage × List UInt8) := do
  let (participantType, bytes) ← Alpha.decode 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (modifiedCancelledBy, bytes) ← ModifiedCancelledBy.decode bytes
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
  let (bookType, bytes) ← decodeUInt 2 bytes
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
  let (openClose, bytes) ← OpenClose.decode bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  let (proClientIndicator, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 4 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← Alpha.decode 8 bytes
  let (echoBack, bytes) ← Alpha.decode 16 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  pure ({ participantType, reserved1, competitorPeriod, solicitorPeriod, modifiedCancelledBy, secondReserved1, reasonCode, reserved4, tokenNo, contractDesc, counterPartyBrokerId, thirdReserved1, reserved2, closeoutFlag, fourthReserved1, orderType, orderNumber, accountNumber, bookType, buySellIndicator, disclosedVolume, disclosedVolumeRemaining, totalVolumeRemaining, volume, volumeFilledToday, price, triggerPrice, goodTillDate, entryDateTime, minimumFillAonVolume, lastModified, stOrderFlags, branchId, traderId, brokerId, cOrdFiller, openClose, settlor, proClientIndicator, settlementPeriod, additionalOrderFlags, giveupFlag, reference, nnfField, mktReplay, echoBack, lastActivityReference, reserved52 }, bytes)

@[simp] theorem encode_length (message : FreezeToControlMessage) : (encode message).length = 276 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ModifiedCancelledBy.encode_length, ContractDesc.encode_length, OpenClose.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : FreezeToControlMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : FreezeToControlMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, ModifiedCancelledBy.decode_encode, some_bind]
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
  rw [List.append_assoc, OpenClose.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end FreezeToControlMessage

/-- Order Error Message: 276 bytes -/
structure OrderErrorMessage where
  participantType : Alpha 1
  reserved1 : Alpha 1
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  modifiedCancelledBy : ModifiedCancelledBy
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
  bookType : BitVec 16
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
  openClose : OpenClose
  settlor : Alpha 12
  proClientIndicator : BitVec 16
  settlementPeriod : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag : Alpha 1
  reference : Alpha 4
  nnfField : Alpha 8
  mktReplay : Alpha 8
  echoBack : Alpha 16
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  deriving DecidableEq, Repr

namespace OrderErrorMessage

def encode (message : OrderErrorMessage) : List UInt8 :=
  Alpha.encode message.participantType
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (ModifiedCancelledBy.encode message.modifiedCancelledBy
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
    ++ (encodeUInt 2 message.bookType
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
    ++ (OpenClose.encode message.openClose
    ++ (Alpha.encode message.settlor
    ++ (encodeUInt 2 message.proClientIndicator
    ++ (encodeUInt 2 message.settlementPeriod
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag
    ++ (Alpha.encode message.reference
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.mktReplay
    ++ (Alpha.encode message.echoBack
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52)))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderErrorMessage × List UInt8) := do
  let (participantType, bytes) ← Alpha.decode 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (modifiedCancelledBy, bytes) ← ModifiedCancelledBy.decode bytes
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
  let (bookType, bytes) ← decodeUInt 2 bytes
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
  let (openClose, bytes) ← OpenClose.decode bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  let (proClientIndicator, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 4 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← Alpha.decode 8 bytes
  let (echoBack, bytes) ← Alpha.decode 16 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  pure ({ participantType, reserved1, competitorPeriod, solicitorPeriod, modifiedCancelledBy, secondReserved1, reasonCode, reserved4, tokenNo, contractDesc, counterPartyBrokerId, thirdReserved1, reserved2, closeoutFlag, fourthReserved1, orderType, orderNumber, accountNumber, bookType, buySellIndicator, disclosedVolume, disclosedVolumeRemaining, totalVolumeRemaining, volume, volumeFilledToday, price, triggerPrice, goodTillDate, entryDateTime, minimumFillAonVolume, lastModified, stOrderFlags, branchId, traderId, brokerId, cOrdFiller, openClose, settlor, proClientIndicator, settlementPeriod, additionalOrderFlags, giveupFlag, reference, nnfField, mktReplay, echoBack, lastActivityReference, reserved52 }, bytes)

@[simp] theorem encode_length (message : OrderErrorMessage) : (encode message).length = 276 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ModifiedCancelledBy.encode_length, ContractDesc.encode_length, OpenClose.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : OrderErrorMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OrderErrorMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, ModifiedCancelledBy.decode_encode, some_bind]
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
  rw [List.append_assoc, OpenClose.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderErrorMessage

/-- Batch Order Cancel Message: 276 bytes -/
structure BatchOrderCancelMessage where
  participantType : Alpha 1
  reserved1 : Alpha 1
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  modifiedCancelledBy : ModifiedCancelledBy
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
  bookType : BitVec 16
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
  openClose : OpenClose
  settlor : Alpha 12
  proClientIndicator : BitVec 16
  settlementPeriod : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag : Alpha 1
  reference : Alpha 4
  nnfField : Alpha 8
  mktReplay : Alpha 8
  echoBack : Alpha 16
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  deriving DecidableEq, Repr

namespace BatchOrderCancelMessage

def encode (message : BatchOrderCancelMessage) : List UInt8 :=
  Alpha.encode message.participantType
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (ModifiedCancelledBy.encode message.modifiedCancelledBy
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
    ++ (encodeUInt 2 message.bookType
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
    ++ (OpenClose.encode message.openClose
    ++ (Alpha.encode message.settlor
    ++ (encodeUInt 2 message.proClientIndicator
    ++ (encodeUInt 2 message.settlementPeriod
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag
    ++ (Alpha.encode message.reference
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.mktReplay
    ++ (Alpha.encode message.echoBack
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52)))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (BatchOrderCancelMessage × List UInt8) := do
  let (participantType, bytes) ← Alpha.decode 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (modifiedCancelledBy, bytes) ← ModifiedCancelledBy.decode bytes
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
  let (bookType, bytes) ← decodeUInt 2 bytes
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
  let (openClose, bytes) ← OpenClose.decode bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  let (proClientIndicator, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 4 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← Alpha.decode 8 bytes
  let (echoBack, bytes) ← Alpha.decode 16 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  pure ({ participantType, reserved1, competitorPeriod, solicitorPeriod, modifiedCancelledBy, secondReserved1, reasonCode, reserved4, tokenNo, contractDesc, counterPartyBrokerId, thirdReserved1, reserved2, closeoutFlag, fourthReserved1, orderType, orderNumber, accountNumber, bookType, buySellIndicator, disclosedVolume, disclosedVolumeRemaining, totalVolumeRemaining, volume, volumeFilledToday, price, triggerPrice, goodTillDate, entryDateTime, minimumFillAonVolume, lastModified, stOrderFlags, branchId, traderId, brokerId, cOrdFiller, openClose, settlor, proClientIndicator, settlementPeriod, additionalOrderFlags, giveupFlag, reference, nnfField, mktReplay, echoBack, lastActivityReference, reserved52 }, bytes)

@[simp] theorem encode_length (message : BatchOrderCancelMessage) : (encode message).length = 276 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ModifiedCancelledBy.encode_length, ContractDesc.encode_length, OpenClose.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : BatchOrderCancelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : BatchOrderCancelMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, ModifiedCancelledBy.decode_encode, some_bind]
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
  rw [List.append_assoc, OpenClose.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end BatchOrderCancelMessage

/-- Net Order Error Message: 276 bytes -/
structure NetOrderErrorMessage where
  participantType : Alpha 1
  reserved1 : Alpha 1
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  modifiedCancelledBy : ModifiedCancelledBy
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
  bookType : BitVec 16
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
  openClose : OpenClose
  settlor : Alpha 12
  proClientIndicator : BitVec 16
  settlementPeriod : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag : Alpha 1
  reference : Alpha 4
  nnfField : Alpha 8
  mktReplay : Alpha 8
  echoBack : Alpha 16
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  deriving DecidableEq, Repr

namespace NetOrderErrorMessage

def encode (message : NetOrderErrorMessage) : List UInt8 :=
  Alpha.encode message.participantType
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (ModifiedCancelledBy.encode message.modifiedCancelledBy
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
    ++ (encodeUInt 2 message.bookType
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
    ++ (OpenClose.encode message.openClose
    ++ (Alpha.encode message.settlor
    ++ (encodeUInt 2 message.proClientIndicator
    ++ (encodeUInt 2 message.settlementPeriod
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag
    ++ (Alpha.encode message.reference
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.mktReplay
    ++ (Alpha.encode message.echoBack
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52)))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (NetOrderErrorMessage × List UInt8) := do
  let (participantType, bytes) ← Alpha.decode 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (modifiedCancelledBy, bytes) ← ModifiedCancelledBy.decode bytes
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
  let (bookType, bytes) ← decodeUInt 2 bytes
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
  let (openClose, bytes) ← OpenClose.decode bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  let (proClientIndicator, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 4 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← Alpha.decode 8 bytes
  let (echoBack, bytes) ← Alpha.decode 16 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  pure ({ participantType, reserved1, competitorPeriod, solicitorPeriod, modifiedCancelledBy, secondReserved1, reasonCode, reserved4, tokenNo, contractDesc, counterPartyBrokerId, thirdReserved1, reserved2, closeoutFlag, fourthReserved1, orderType, orderNumber, accountNumber, bookType, buySellIndicator, disclosedVolume, disclosedVolumeRemaining, totalVolumeRemaining, volume, volumeFilledToday, price, triggerPrice, goodTillDate, entryDateTime, minimumFillAonVolume, lastModified, stOrderFlags, branchId, traderId, brokerId, cOrdFiller, openClose, settlor, proClientIndicator, settlementPeriod, additionalOrderFlags, giveupFlag, reference, nnfField, mktReplay, echoBack, lastActivityReference, reserved52 }, bytes)

@[simp] theorem encode_length (message : NetOrderErrorMessage) : (encode message).length = 276 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ModifiedCancelledBy.encode_length, ContractDesc.encode_length, OpenClose.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : NetOrderErrorMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : NetOrderErrorMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, ModifiedCancelledBy.decode_encode, some_bind]
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
  rw [List.append_assoc, OpenClose.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end NetOrderErrorMessage

/-- Nlt Confirmation Message: 276 bytes -/
structure NltConfirmationMessage where
  participantType : Alpha 1
  reserved1 : Alpha 1
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  modifiedCancelledBy : ModifiedCancelledBy
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
  bookType : BitVec 16
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
  openClose : OpenClose
  settlor : Alpha 12
  proClientIndicator : BitVec 16
  settlementPeriod : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag : Alpha 1
  reference : Alpha 4
  nnfField : Alpha 8
  mktReplay : Alpha 8
  echoBack : Alpha 16
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  deriving DecidableEq, Repr

namespace NltConfirmationMessage

def encode (message : NltConfirmationMessage) : List UInt8 :=
  Alpha.encode message.participantType
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (ModifiedCancelledBy.encode message.modifiedCancelledBy
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
    ++ (encodeUInt 2 message.bookType
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
    ++ (OpenClose.encode message.openClose
    ++ (Alpha.encode message.settlor
    ++ (encodeUInt 2 message.proClientIndicator
    ++ (encodeUInt 2 message.settlementPeriod
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag
    ++ (Alpha.encode message.reference
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.mktReplay
    ++ (Alpha.encode message.echoBack
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52)))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (NltConfirmationMessage × List UInt8) := do
  let (participantType, bytes) ← Alpha.decode 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (modifiedCancelledBy, bytes) ← ModifiedCancelledBy.decode bytes
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
  let (bookType, bytes) ← decodeUInt 2 bytes
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
  let (openClose, bytes) ← OpenClose.decode bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  let (proClientIndicator, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 4 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← Alpha.decode 8 bytes
  let (echoBack, bytes) ← Alpha.decode 16 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  pure ({ participantType, reserved1, competitorPeriod, solicitorPeriod, modifiedCancelledBy, secondReserved1, reasonCode, reserved4, tokenNo, contractDesc, counterPartyBrokerId, thirdReserved1, reserved2, closeoutFlag, fourthReserved1, orderType, orderNumber, accountNumber, bookType, buySellIndicator, disclosedVolume, disclosedVolumeRemaining, totalVolumeRemaining, volume, volumeFilledToday, price, triggerPrice, goodTillDate, entryDateTime, minimumFillAonVolume, lastModified, stOrderFlags, branchId, traderId, brokerId, cOrdFiller, openClose, settlor, proClientIndicator, settlementPeriod, additionalOrderFlags, giveupFlag, reference, nnfField, mktReplay, echoBack, lastActivityReference, reserved52 }, bytes)

@[simp] theorem encode_length (message : NltConfirmationMessage) : (encode message).length = 276 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ModifiedCancelledBy.encode_length, ContractDesc.encode_length, OpenClose.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : NltConfirmationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : NltConfirmationMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, ModifiedCancelledBy.decode_encode, some_bind]
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
  rw [List.append_assoc, OpenClose.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end NltConfirmationMessage

/-- Nlt Mod Confirmation Message: 276 bytes -/
structure NltModConfirmationMessage where
  participantType : Alpha 1
  reserved1 : Alpha 1
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  modifiedCancelledBy : ModifiedCancelledBy
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
  bookType : BitVec 16
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
  openClose : OpenClose
  settlor : Alpha 12
  proClientIndicator : BitVec 16
  settlementPeriod : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag : Alpha 1
  reference : Alpha 4
  nnfField : Alpha 8
  mktReplay : Alpha 8
  echoBack : Alpha 16
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  deriving DecidableEq, Repr

namespace NltModConfirmationMessage

def encode (message : NltModConfirmationMessage) : List UInt8 :=
  Alpha.encode message.participantType
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (ModifiedCancelledBy.encode message.modifiedCancelledBy
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
    ++ (encodeUInt 2 message.bookType
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
    ++ (OpenClose.encode message.openClose
    ++ (Alpha.encode message.settlor
    ++ (encodeUInt 2 message.proClientIndicator
    ++ (encodeUInt 2 message.settlementPeriod
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag
    ++ (Alpha.encode message.reference
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.mktReplay
    ++ (Alpha.encode message.echoBack
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52)))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (NltModConfirmationMessage × List UInt8) := do
  let (participantType, bytes) ← Alpha.decode 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (modifiedCancelledBy, bytes) ← ModifiedCancelledBy.decode bytes
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
  let (bookType, bytes) ← decodeUInt 2 bytes
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
  let (openClose, bytes) ← OpenClose.decode bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  let (proClientIndicator, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 4 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← Alpha.decode 8 bytes
  let (echoBack, bytes) ← Alpha.decode 16 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  pure ({ participantType, reserved1, competitorPeriod, solicitorPeriod, modifiedCancelledBy, secondReserved1, reasonCode, reserved4, tokenNo, contractDesc, counterPartyBrokerId, thirdReserved1, reserved2, closeoutFlag, fourthReserved1, orderType, orderNumber, accountNumber, bookType, buySellIndicator, disclosedVolume, disclosedVolumeRemaining, totalVolumeRemaining, volume, volumeFilledToday, price, triggerPrice, goodTillDate, entryDateTime, minimumFillAonVolume, lastModified, stOrderFlags, branchId, traderId, brokerId, cOrdFiller, openClose, settlor, proClientIndicator, settlementPeriod, additionalOrderFlags, giveupFlag, reference, nnfField, mktReplay, echoBack, lastActivityReference, reserved52 }, bytes)

@[simp] theorem encode_length (message : NltModConfirmationMessage) : (encode message).length = 276 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ModifiedCancelledBy.encode_length, ContractDesc.encode_length, OpenClose.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : NltModConfirmationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : NltModConfirmationMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, ModifiedCancelledBy.decode_encode, some_bind]
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
  rw [List.append_assoc, OpenClose.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end NltModConfirmationMessage

/-- Nlt Cxl Confirmation Message: 276 bytes -/
structure NltCxlConfirmationMessage where
  participantType : Alpha 1
  reserved1 : Alpha 1
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  modifiedCancelledBy : ModifiedCancelledBy
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
  bookType : BitVec 16
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
  openClose : OpenClose
  settlor : Alpha 12
  proClientIndicator : BitVec 16
  settlementPeriod : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag : Alpha 1
  reference : Alpha 4
  nnfField : Alpha 8
  mktReplay : Alpha 8
  echoBack : Alpha 16
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  deriving DecidableEq, Repr

namespace NltCxlConfirmationMessage

def encode (message : NltCxlConfirmationMessage) : List UInt8 :=
  Alpha.encode message.participantType
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (ModifiedCancelledBy.encode message.modifiedCancelledBy
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
    ++ (encodeUInt 2 message.bookType
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
    ++ (OpenClose.encode message.openClose
    ++ (Alpha.encode message.settlor
    ++ (encodeUInt 2 message.proClientIndicator
    ++ (encodeUInt 2 message.settlementPeriod
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag
    ++ (Alpha.encode message.reference
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.mktReplay
    ++ (Alpha.encode message.echoBack
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52)))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (NltCxlConfirmationMessage × List UInt8) := do
  let (participantType, bytes) ← Alpha.decode 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (modifiedCancelledBy, bytes) ← ModifiedCancelledBy.decode bytes
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
  let (bookType, bytes) ← decodeUInt 2 bytes
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
  let (openClose, bytes) ← OpenClose.decode bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  let (proClientIndicator, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 4 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← Alpha.decode 8 bytes
  let (echoBack, bytes) ← Alpha.decode 16 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  pure ({ participantType, reserved1, competitorPeriod, solicitorPeriod, modifiedCancelledBy, secondReserved1, reasonCode, reserved4, tokenNo, contractDesc, counterPartyBrokerId, thirdReserved1, reserved2, closeoutFlag, fourthReserved1, orderType, orderNumber, accountNumber, bookType, buySellIndicator, disclosedVolume, disclosedVolumeRemaining, totalVolumeRemaining, volume, volumeFilledToday, price, triggerPrice, goodTillDate, entryDateTime, minimumFillAonVolume, lastModified, stOrderFlags, branchId, traderId, brokerId, cOrdFiller, openClose, settlor, proClientIndicator, settlementPeriod, additionalOrderFlags, giveupFlag, reference, nnfField, mktReplay, echoBack, lastActivityReference, reserved52 }, bytes)

@[simp] theorem encode_length (message : NltCxlConfirmationMessage) : (encode message).length = 276 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ModifiedCancelledBy.encode_length, ContractDesc.encode_length, OpenClose.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : NltCxlConfirmationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : NltCxlConfirmationMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, ModifiedCancelledBy.decode_encode, some_bind]
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
  rw [List.append_assoc, OpenClose.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end NltCxlConfirmationMessage

/-- Nlt Mod Reject Message: 276 bytes -/
structure NltModRejectMessage where
  participantType : Alpha 1
  reserved1 : Alpha 1
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  modifiedCancelledBy : ModifiedCancelledBy
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
  bookType : BitVec 16
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
  openClose : OpenClose
  settlor : Alpha 12
  proClientIndicator : BitVec 16
  settlementPeriod : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag : Alpha 1
  reference : Alpha 4
  nnfField : Alpha 8
  mktReplay : Alpha 8
  echoBack : Alpha 16
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  deriving DecidableEq, Repr

namespace NltModRejectMessage

def encode (message : NltModRejectMessage) : List UInt8 :=
  Alpha.encode message.participantType
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (ModifiedCancelledBy.encode message.modifiedCancelledBy
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
    ++ (encodeUInt 2 message.bookType
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
    ++ (OpenClose.encode message.openClose
    ++ (Alpha.encode message.settlor
    ++ (encodeUInt 2 message.proClientIndicator
    ++ (encodeUInt 2 message.settlementPeriod
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag
    ++ (Alpha.encode message.reference
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.mktReplay
    ++ (Alpha.encode message.echoBack
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52)))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (NltModRejectMessage × List UInt8) := do
  let (participantType, bytes) ← Alpha.decode 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (modifiedCancelledBy, bytes) ← ModifiedCancelledBy.decode bytes
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
  let (bookType, bytes) ← decodeUInt 2 bytes
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
  let (openClose, bytes) ← OpenClose.decode bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  let (proClientIndicator, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 4 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← Alpha.decode 8 bytes
  let (echoBack, bytes) ← Alpha.decode 16 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  pure ({ participantType, reserved1, competitorPeriod, solicitorPeriod, modifiedCancelledBy, secondReserved1, reasonCode, reserved4, tokenNo, contractDesc, counterPartyBrokerId, thirdReserved1, reserved2, closeoutFlag, fourthReserved1, orderType, orderNumber, accountNumber, bookType, buySellIndicator, disclosedVolume, disclosedVolumeRemaining, totalVolumeRemaining, volume, volumeFilledToday, price, triggerPrice, goodTillDate, entryDateTime, minimumFillAonVolume, lastModified, stOrderFlags, branchId, traderId, brokerId, cOrdFiller, openClose, settlor, proClientIndicator, settlementPeriod, additionalOrderFlags, giveupFlag, reference, nnfField, mktReplay, echoBack, lastActivityReference, reserved52 }, bytes)

@[simp] theorem encode_length (message : NltModRejectMessage) : (encode message).length = 276 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ModifiedCancelledBy.encode_length, ContractDesc.encode_length, OpenClose.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : NltModRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : NltModRejectMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, ModifiedCancelledBy.decode_encode, some_bind]
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
  rw [List.append_assoc, OpenClose.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end NltModRejectMessage

/-- Nlt Cxl Reject Message: 276 bytes -/
structure NltCxlRejectMessage where
  participantType : Alpha 1
  reserved1 : Alpha 1
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  modifiedCancelledBy : ModifiedCancelledBy
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
  bookType : BitVec 16
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
  openClose : OpenClose
  settlor : Alpha 12
  proClientIndicator : BitVec 16
  settlementPeriod : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag : Alpha 1
  reference : Alpha 4
  nnfField : Alpha 8
  mktReplay : Alpha 8
  echoBack : Alpha 16
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  deriving DecidableEq, Repr

namespace NltCxlRejectMessage

def encode (message : NltCxlRejectMessage) : List UInt8 :=
  Alpha.encode message.participantType
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (ModifiedCancelledBy.encode message.modifiedCancelledBy
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
    ++ (encodeUInt 2 message.bookType
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
    ++ (OpenClose.encode message.openClose
    ++ (Alpha.encode message.settlor
    ++ (encodeUInt 2 message.proClientIndicator
    ++ (encodeUInt 2 message.settlementPeriod
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag
    ++ (Alpha.encode message.reference
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.mktReplay
    ++ (Alpha.encode message.echoBack
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52)))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (NltCxlRejectMessage × List UInt8) := do
  let (participantType, bytes) ← Alpha.decode 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (modifiedCancelledBy, bytes) ← ModifiedCancelledBy.decode bytes
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
  let (bookType, bytes) ← decodeUInt 2 bytes
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
  let (openClose, bytes) ← OpenClose.decode bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  let (proClientIndicator, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 4 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← Alpha.decode 8 bytes
  let (echoBack, bytes) ← Alpha.decode 16 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  pure ({ participantType, reserved1, competitorPeriod, solicitorPeriod, modifiedCancelledBy, secondReserved1, reasonCode, reserved4, tokenNo, contractDesc, counterPartyBrokerId, thirdReserved1, reserved2, closeoutFlag, fourthReserved1, orderType, orderNumber, accountNumber, bookType, buySellIndicator, disclosedVolume, disclosedVolumeRemaining, totalVolumeRemaining, volume, volumeFilledToday, price, triggerPrice, goodTillDate, entryDateTime, minimumFillAonVolume, lastModified, stOrderFlags, branchId, traderId, brokerId, cOrdFiller, openClose, settlor, proClientIndicator, settlementPeriod, additionalOrderFlags, giveupFlag, reference, nnfField, mktReplay, echoBack, lastActivityReference, reserved52 }, bytes)

@[simp] theorem encode_length (message : NltCxlRejectMessage) : (encode message).length = 276 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ModifiedCancelledBy.encode_length, ContractDesc.encode_length, OpenClose.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : NltCxlRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : NltCxlRejectMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, ModifiedCancelledBy.decode_encode, some_bind]
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
  rw [List.append_assoc, OpenClose.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end NltCxlRejectMessage

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
  openClose2 : OpenClose2
  additionalOrderFlags : BitVec 8
  giveupFlag2 : Alpha 1
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
    ++ (OpenClose2.encode message.openClose2
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag2
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
  let (openClose2, bytes) ← OpenClose2.decode bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag2, bytes) ← Alpha.decode 1 bytes
  let (fillerY, bytes) ← Alpha.decode 1 bytes
  pure ({ token2, contractDesc, opBrokerId2, fillerx2, orderType2, buySell2, disclosedVol2, disclosedVolRemaining2, totalVolRemaining2, volume2, volumeFilledToday2, price2, triggerPrice2, minFillAon2, stOrderFlags, openClose2, additionalOrderFlags, giveupFlag2, fillerY }, bytes)

@[simp] theorem encode_length (message : MsSpdLegInfoLeg2) : (encode message).length = 80 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, ContractDesc.encode_length, Alpha.encode_length, OpenClose2.encode_length, encodeUIntLE_length]

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
  rw [List.append_assoc, OpenClose2.decode_encode, some_bind]
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
  openClose2 : OpenClose2
  additionalOrderFlags : BitVec 8
  giveupFlag2 : Alpha 1
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
    ++ (OpenClose2.encode message.openClose2
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag2
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
  let (openClose2, bytes) ← OpenClose2.decode bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag2, bytes) ← Alpha.decode 1 bytes
  let (fillerY, bytes) ← Alpha.decode 1 bytes
  pure ({ token2, contractDesc, opBrokerId2, fillerx2, orderType2, buySell2, disclosedVol2, disclosedVolRemaining2, totalVolRemaining2, volume2, volumeFilledToday2, price2, triggerPrice2, minFillAon2, stOrderFlags, openClose2, additionalOrderFlags, giveupFlag2, fillerY }, bytes)

@[simp] theorem encode_length (message : MsSpdLegInfoLeg3) : (encode message).length = 80 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, ContractDesc.encode_length, Alpha.encode_length, OpenClose2.encode_length, encodeUIntLE_length]

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
  rw [List.append_assoc, OpenClose2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MsSpdLegInfoLeg3

/-- Spread Order Confirmation Message: 440 bytes -/
structure SpreadOrderConfirmationMessage where
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
  openClose1 : OpenClose1
  settlor1 : Alpha 12
  proClient1 : BitVec 16
  settlementPeriod1 : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag1 : Alpha 1
  filler1To16 : Alpha 2
  filler17 : Alpha 1
  filler18 : Alpha 1
  nnfField : Alpha 8
  spreadEntryTime : Alpha 8
  echoBack : Alpha 16
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  priceDiff : BitVec 32
  msSpdLegInfoLeg2 : MsSpdLegInfoLeg2
  msSpdLegInfoLeg3 : MsSpdLegInfoLeg3
  deriving DecidableEq, Repr

namespace SpreadOrderConfirmationMessage

def encode (message : SpreadOrderConfirmationMessage) : List UInt8 :=
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
    ++ (OpenClose1.encode message.openClose1
    ++ (Alpha.encode message.settlor1
    ++ (encodeUInt 2 message.proClient1
    ++ (encodeUInt 2 message.settlementPeriod1
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag1
    ++ (Alpha.encode message.filler1To16
    ++ (Alpha.encode message.filler17
    ++ (Alpha.encode message.filler18
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.spreadEntryTime
    ++ (Alpha.encode message.echoBack
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52
    ++ (encodeUInt 4 message.priceDiff
    ++ (MsSpdLegInfoLeg2.encode message.msSpdLegInfoLeg2
    ++ (MsSpdLegInfoLeg3.encode message.msSpdLegInfoLeg3))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SpreadOrderConfirmationMessage × List UInt8) := do
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
  let (openClose1, bytes) ← OpenClose1.decode bytes
  let (settlor1, bytes) ← Alpha.decode 12 bytes
  let (proClient1, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod1, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag1, bytes) ← Alpha.decode 1 bytes
  let (filler1To16, bytes) ← Alpha.decode 2 bytes
  let (filler17, bytes) ← Alpha.decode 1 bytes
  let (filler18, bytes) ← Alpha.decode 1 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (spreadEntryTime, bytes) ← Alpha.decode 8 bytes
  let (echoBack, bytes) ← Alpha.decode 16 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  let (priceDiff, bytes) ← decodeUInt 4 bytes
  let (msSpdLegInfoLeg2, bytes) ← MsSpdLegInfoLeg2.decode bytes
  let (msSpdLegInfoLeg3, bytes) ← MsSpdLegInfoLeg3.decode bytes
  pure ({ participantType1, filler1, competitorPeriod1, solicitorPeriod1, modCxlBy1, filler9, reasonCode1, startAlpha1, endAlpha1, token1, contractDesc, opBrokerId1, fillerx1, fillerOptions1, fillery1, orderType1, orderNumber1, accountNumber1, bookType1, buySell1, disclosedVol1, disclosedVolRemaining1, totalVolRemaining1, volume1, volumeFilledToday1, price1, triggerPrice1, goodTillDate1, entryDateTime1, minFillAon1, lastModified1, stOrderFlags, branchId1, traderId1, brokerId1, cOrdFiller, openClose1, settlor1, proClient1, settlementPeriod1, additionalOrderFlags, giveupFlag1, filler1To16, filler17, filler18, nnfField, spreadEntryTime, echoBack, lastActivityReference, reserved52, priceDiff, msSpdLegInfoLeg2, msSpdLegInfoLeg3 }, bytes)

@[simp] theorem encode_length (message : SpreadOrderConfirmationMessage) : (encode message).length = 440 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, OpenClose1.encode_length, encodeUIntLE_length, MsSpdLegInfoLeg2.encode_length, MsSpdLegInfoLeg3.encode_length]

theorem encode_length_pos (message : SpreadOrderConfirmationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SpreadOrderConfirmationMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, OpenClose1.decode_encode, some_bind]
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
  rw [List.append_assoc, MsSpdLegInfoLeg2.decode_encode, some_bind]
  dsimp only
  rw [MsSpdLegInfoLeg3.decode_encode, some_bind]
  rfl

end SpreadOrderConfirmationMessage

/-- Sp Order Error Message: 440 bytes -/
structure SpOrderErrorMessage where
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
  openClose1 : OpenClose1
  settlor1 : Alpha 12
  proClient1 : BitVec 16
  settlementPeriod1 : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag1 : Alpha 1
  filler1To16 : Alpha 2
  filler17 : Alpha 1
  filler18 : Alpha 1
  nnfField : Alpha 8
  spreadEntryTime : Alpha 8
  echoBack : Alpha 16
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  priceDiff : BitVec 32
  msSpdLegInfoLeg2 : MsSpdLegInfoLeg2
  msSpdLegInfoLeg3 : MsSpdLegInfoLeg3
  deriving DecidableEq, Repr

namespace SpOrderErrorMessage

def encode (message : SpOrderErrorMessage) : List UInt8 :=
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
    ++ (OpenClose1.encode message.openClose1
    ++ (Alpha.encode message.settlor1
    ++ (encodeUInt 2 message.proClient1
    ++ (encodeUInt 2 message.settlementPeriod1
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag1
    ++ (Alpha.encode message.filler1To16
    ++ (Alpha.encode message.filler17
    ++ (Alpha.encode message.filler18
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.spreadEntryTime
    ++ (Alpha.encode message.echoBack
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52
    ++ (encodeUInt 4 message.priceDiff
    ++ (MsSpdLegInfoLeg2.encode message.msSpdLegInfoLeg2
    ++ (MsSpdLegInfoLeg3.encode message.msSpdLegInfoLeg3))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SpOrderErrorMessage × List UInt8) := do
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
  let (openClose1, bytes) ← OpenClose1.decode bytes
  let (settlor1, bytes) ← Alpha.decode 12 bytes
  let (proClient1, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod1, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag1, bytes) ← Alpha.decode 1 bytes
  let (filler1To16, bytes) ← Alpha.decode 2 bytes
  let (filler17, bytes) ← Alpha.decode 1 bytes
  let (filler18, bytes) ← Alpha.decode 1 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (spreadEntryTime, bytes) ← Alpha.decode 8 bytes
  let (echoBack, bytes) ← Alpha.decode 16 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  let (priceDiff, bytes) ← decodeUInt 4 bytes
  let (msSpdLegInfoLeg2, bytes) ← MsSpdLegInfoLeg2.decode bytes
  let (msSpdLegInfoLeg3, bytes) ← MsSpdLegInfoLeg3.decode bytes
  pure ({ participantType1, filler1, competitorPeriod1, solicitorPeriod1, modCxlBy1, filler9, reasonCode1, startAlpha1, endAlpha1, token1, contractDesc, opBrokerId1, fillerx1, fillerOptions1, fillery1, orderType1, orderNumber1, accountNumber1, bookType1, buySell1, disclosedVol1, disclosedVolRemaining1, totalVolRemaining1, volume1, volumeFilledToday1, price1, triggerPrice1, goodTillDate1, entryDateTime1, minFillAon1, lastModified1, stOrderFlags, branchId1, traderId1, brokerId1, cOrdFiller, openClose1, settlor1, proClient1, settlementPeriod1, additionalOrderFlags, giveupFlag1, filler1To16, filler17, filler18, nnfField, spreadEntryTime, echoBack, lastActivityReference, reserved52, priceDiff, msSpdLegInfoLeg2, msSpdLegInfoLeg3 }, bytes)

@[simp] theorem encode_length (message : SpOrderErrorMessage) : (encode message).length = 440 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, OpenClose1.encode_length, encodeUIntLE_length, MsSpdLegInfoLeg2.encode_length, MsSpdLegInfoLeg3.encode_length]

theorem encode_length_pos (message : SpOrderErrorMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SpOrderErrorMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, OpenClose1.decode_encode, some_bind]
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
  rw [List.append_assoc, MsSpdLegInfoLeg2.decode_encode, some_bind]
  dsimp only
  rw [MsSpdLegInfoLeg3.decode_encode, some_bind]
  rfl

end SpOrderErrorMessage

/-- Sp Net Order Error Message: 440 bytes -/
structure SpNetOrderErrorMessage where
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
  openClose1 : OpenClose1
  settlor1 : Alpha 12
  proClient1 : BitVec 16
  settlementPeriod1 : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag1 : Alpha 1
  filler1To16 : Alpha 2
  filler17 : Alpha 1
  filler18 : Alpha 1
  nnfField : Alpha 8
  spreadEntryTime : Alpha 8
  echoBack : Alpha 16
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  priceDiff : BitVec 32
  msSpdLegInfoLeg2 : MsSpdLegInfoLeg2
  msSpdLegInfoLeg3 : MsSpdLegInfoLeg3
  deriving DecidableEq, Repr

namespace SpNetOrderErrorMessage

def encode (message : SpNetOrderErrorMessage) : List UInt8 :=
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
    ++ (OpenClose1.encode message.openClose1
    ++ (Alpha.encode message.settlor1
    ++ (encodeUInt 2 message.proClient1
    ++ (encodeUInt 2 message.settlementPeriod1
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag1
    ++ (Alpha.encode message.filler1To16
    ++ (Alpha.encode message.filler17
    ++ (Alpha.encode message.filler18
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.spreadEntryTime
    ++ (Alpha.encode message.echoBack
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52
    ++ (encodeUInt 4 message.priceDiff
    ++ (MsSpdLegInfoLeg2.encode message.msSpdLegInfoLeg2
    ++ (MsSpdLegInfoLeg3.encode message.msSpdLegInfoLeg3))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SpNetOrderErrorMessage × List UInt8) := do
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
  let (openClose1, bytes) ← OpenClose1.decode bytes
  let (settlor1, bytes) ← Alpha.decode 12 bytes
  let (proClient1, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod1, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag1, bytes) ← Alpha.decode 1 bytes
  let (filler1To16, bytes) ← Alpha.decode 2 bytes
  let (filler17, bytes) ← Alpha.decode 1 bytes
  let (filler18, bytes) ← Alpha.decode 1 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (spreadEntryTime, bytes) ← Alpha.decode 8 bytes
  let (echoBack, bytes) ← Alpha.decode 16 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  let (priceDiff, bytes) ← decodeUInt 4 bytes
  let (msSpdLegInfoLeg2, bytes) ← MsSpdLegInfoLeg2.decode bytes
  let (msSpdLegInfoLeg3, bytes) ← MsSpdLegInfoLeg3.decode bytes
  pure ({ participantType1, filler1, competitorPeriod1, solicitorPeriod1, modCxlBy1, filler9, reasonCode1, startAlpha1, endAlpha1, token1, contractDesc, opBrokerId1, fillerx1, fillerOptions1, fillery1, orderType1, orderNumber1, accountNumber1, bookType1, buySell1, disclosedVol1, disclosedVolRemaining1, totalVolRemaining1, volume1, volumeFilledToday1, price1, triggerPrice1, goodTillDate1, entryDateTime1, minFillAon1, lastModified1, stOrderFlags, branchId1, traderId1, brokerId1, cOrdFiller, openClose1, settlor1, proClient1, settlementPeriod1, additionalOrderFlags, giveupFlag1, filler1To16, filler17, filler18, nnfField, spreadEntryTime, echoBack, lastActivityReference, reserved52, priceDiff, msSpdLegInfoLeg2, msSpdLegInfoLeg3 }, bytes)

@[simp] theorem encode_length (message : SpNetOrderErrorMessage) : (encode message).length = 440 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, OpenClose1.encode_length, encodeUIntLE_length, MsSpdLegInfoLeg2.encode_length, MsSpdLegInfoLeg3.encode_length]

theorem encode_length_pos (message : SpNetOrderErrorMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SpNetOrderErrorMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, OpenClose1.decode_encode, some_bind]
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
  rw [List.append_assoc, MsSpdLegInfoLeg2.decode_encode, some_bind]
  dsimp only
  rw [MsSpdLegInfoLeg3.decode_encode, some_bind]
  rfl

end SpNetOrderErrorMessage

/-- Spread Cxl Confirmation Message: 440 bytes -/
structure SpreadCxlConfirmationMessage where
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
  openClose1 : OpenClose1
  settlor1 : Alpha 12
  proClient1 : BitVec 16
  settlementPeriod1 : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag1 : Alpha 1
  filler1To16 : Alpha 2
  filler17 : Alpha 1
  filler18 : Alpha 1
  nnfField : Alpha 8
  spreadEntryTime : Alpha 8
  echoBack : Alpha 16
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  priceDiff : BitVec 32
  msSpdLegInfoLeg2 : MsSpdLegInfoLeg2
  msSpdLegInfoLeg3 : MsSpdLegInfoLeg3
  deriving DecidableEq, Repr

namespace SpreadCxlConfirmationMessage

def encode (message : SpreadCxlConfirmationMessage) : List UInt8 :=
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
    ++ (OpenClose1.encode message.openClose1
    ++ (Alpha.encode message.settlor1
    ++ (encodeUInt 2 message.proClient1
    ++ (encodeUInt 2 message.settlementPeriod1
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag1
    ++ (Alpha.encode message.filler1To16
    ++ (Alpha.encode message.filler17
    ++ (Alpha.encode message.filler18
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.spreadEntryTime
    ++ (Alpha.encode message.echoBack
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52
    ++ (encodeUInt 4 message.priceDiff
    ++ (MsSpdLegInfoLeg2.encode message.msSpdLegInfoLeg2
    ++ (MsSpdLegInfoLeg3.encode message.msSpdLegInfoLeg3))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SpreadCxlConfirmationMessage × List UInt8) := do
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
  let (openClose1, bytes) ← OpenClose1.decode bytes
  let (settlor1, bytes) ← Alpha.decode 12 bytes
  let (proClient1, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod1, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag1, bytes) ← Alpha.decode 1 bytes
  let (filler1To16, bytes) ← Alpha.decode 2 bytes
  let (filler17, bytes) ← Alpha.decode 1 bytes
  let (filler18, bytes) ← Alpha.decode 1 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (spreadEntryTime, bytes) ← Alpha.decode 8 bytes
  let (echoBack, bytes) ← Alpha.decode 16 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  let (priceDiff, bytes) ← decodeUInt 4 bytes
  let (msSpdLegInfoLeg2, bytes) ← MsSpdLegInfoLeg2.decode bytes
  let (msSpdLegInfoLeg3, bytes) ← MsSpdLegInfoLeg3.decode bytes
  pure ({ participantType1, filler1, competitorPeriod1, solicitorPeriod1, modCxlBy1, filler9, reasonCode1, startAlpha1, endAlpha1, token1, contractDesc, opBrokerId1, fillerx1, fillerOptions1, fillery1, orderType1, orderNumber1, accountNumber1, bookType1, buySell1, disclosedVol1, disclosedVolRemaining1, totalVolRemaining1, volume1, volumeFilledToday1, price1, triggerPrice1, goodTillDate1, entryDateTime1, minFillAon1, lastModified1, stOrderFlags, branchId1, traderId1, brokerId1, cOrdFiller, openClose1, settlor1, proClient1, settlementPeriod1, additionalOrderFlags, giveupFlag1, filler1To16, filler17, filler18, nnfField, spreadEntryTime, echoBack, lastActivityReference, reserved52, priceDiff, msSpdLegInfoLeg2, msSpdLegInfoLeg3 }, bytes)

@[simp] theorem encode_length (message : SpreadCxlConfirmationMessage) : (encode message).length = 440 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, OpenClose1.encode_length, encodeUIntLE_length, MsSpdLegInfoLeg2.encode_length, MsSpdLegInfoLeg3.encode_length]

theorem encode_length_pos (message : SpreadCxlConfirmationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SpreadCxlConfirmationMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, OpenClose1.decode_encode, some_bind]
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
  rw [List.append_assoc, MsSpdLegInfoLeg2.decode_encode, some_bind]
  dsimp only
  rw [MsSpdLegInfoLeg3.decode_encode, some_bind]
  rfl

end SpreadCxlConfirmationMessage

/-- Spread Mod Confirmation Message: 440 bytes -/
structure SpreadModConfirmationMessage where
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
  openClose1 : OpenClose1
  settlor1 : Alpha 12
  proClient1 : BitVec 16
  settlementPeriod1 : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag1 : Alpha 1
  filler1To16 : Alpha 2
  filler17 : Alpha 1
  filler18 : Alpha 1
  nnfField : Alpha 8
  spreadEntryTime : Alpha 8
  echoBack : Alpha 16
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  priceDiff : BitVec 32
  msSpdLegInfoLeg2 : MsSpdLegInfoLeg2
  msSpdLegInfoLeg3 : MsSpdLegInfoLeg3
  deriving DecidableEq, Repr

namespace SpreadModConfirmationMessage

def encode (message : SpreadModConfirmationMessage) : List UInt8 :=
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
    ++ (OpenClose1.encode message.openClose1
    ++ (Alpha.encode message.settlor1
    ++ (encodeUInt 2 message.proClient1
    ++ (encodeUInt 2 message.settlementPeriod1
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag1
    ++ (Alpha.encode message.filler1To16
    ++ (Alpha.encode message.filler17
    ++ (Alpha.encode message.filler18
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.spreadEntryTime
    ++ (Alpha.encode message.echoBack
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52
    ++ (encodeUInt 4 message.priceDiff
    ++ (MsSpdLegInfoLeg2.encode message.msSpdLegInfoLeg2
    ++ (MsSpdLegInfoLeg3.encode message.msSpdLegInfoLeg3))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SpreadModConfirmationMessage × List UInt8) := do
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
  let (openClose1, bytes) ← OpenClose1.decode bytes
  let (settlor1, bytes) ← Alpha.decode 12 bytes
  let (proClient1, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod1, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag1, bytes) ← Alpha.decode 1 bytes
  let (filler1To16, bytes) ← Alpha.decode 2 bytes
  let (filler17, bytes) ← Alpha.decode 1 bytes
  let (filler18, bytes) ← Alpha.decode 1 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (spreadEntryTime, bytes) ← Alpha.decode 8 bytes
  let (echoBack, bytes) ← Alpha.decode 16 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  let (priceDiff, bytes) ← decodeUInt 4 bytes
  let (msSpdLegInfoLeg2, bytes) ← MsSpdLegInfoLeg2.decode bytes
  let (msSpdLegInfoLeg3, bytes) ← MsSpdLegInfoLeg3.decode bytes
  pure ({ participantType1, filler1, competitorPeriod1, solicitorPeriod1, modCxlBy1, filler9, reasonCode1, startAlpha1, endAlpha1, token1, contractDesc, opBrokerId1, fillerx1, fillerOptions1, fillery1, orderType1, orderNumber1, accountNumber1, bookType1, buySell1, disclosedVol1, disclosedVolRemaining1, totalVolRemaining1, volume1, volumeFilledToday1, price1, triggerPrice1, goodTillDate1, entryDateTime1, minFillAon1, lastModified1, stOrderFlags, branchId1, traderId1, brokerId1, cOrdFiller, openClose1, settlor1, proClient1, settlementPeriod1, additionalOrderFlags, giveupFlag1, filler1To16, filler17, filler18, nnfField, spreadEntryTime, echoBack, lastActivityReference, reserved52, priceDiff, msSpdLegInfoLeg2, msSpdLegInfoLeg3 }, bytes)

@[simp] theorem encode_length (message : SpreadModConfirmationMessage) : (encode message).length = 440 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, OpenClose1.encode_length, encodeUIntLE_length, MsSpdLegInfoLeg2.encode_length, MsSpdLegInfoLeg3.encode_length]

theorem encode_length_pos (message : SpreadModConfirmationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SpreadModConfirmationMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, OpenClose1.decode_encode, some_bind]
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
  rw [List.append_assoc, MsSpdLegInfoLeg2.decode_encode, some_bind]
  dsimp only
  rw [MsSpdLegInfoLeg3.decode_encode, some_bind]
  rfl

end SpreadModConfirmationMessage

/-- Spread Mod Reject Message: 440 bytes -/
structure SpreadModRejectMessage where
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
  openClose1 : OpenClose1
  settlor1 : Alpha 12
  proClient1 : BitVec 16
  settlementPeriod1 : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag1 : Alpha 1
  filler1To16 : Alpha 2
  filler17 : Alpha 1
  filler18 : Alpha 1
  nnfField : Alpha 8
  spreadEntryTime : Alpha 8
  echoBack : Alpha 16
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  priceDiff : BitVec 32
  msSpdLegInfoLeg2 : MsSpdLegInfoLeg2
  msSpdLegInfoLeg3 : MsSpdLegInfoLeg3
  deriving DecidableEq, Repr

namespace SpreadModRejectMessage

def encode (message : SpreadModRejectMessage) : List UInt8 :=
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
    ++ (OpenClose1.encode message.openClose1
    ++ (Alpha.encode message.settlor1
    ++ (encodeUInt 2 message.proClient1
    ++ (encodeUInt 2 message.settlementPeriod1
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag1
    ++ (Alpha.encode message.filler1To16
    ++ (Alpha.encode message.filler17
    ++ (Alpha.encode message.filler18
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.spreadEntryTime
    ++ (Alpha.encode message.echoBack
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52
    ++ (encodeUInt 4 message.priceDiff
    ++ (MsSpdLegInfoLeg2.encode message.msSpdLegInfoLeg2
    ++ (MsSpdLegInfoLeg3.encode message.msSpdLegInfoLeg3))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SpreadModRejectMessage × List UInt8) := do
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
  let (openClose1, bytes) ← OpenClose1.decode bytes
  let (settlor1, bytes) ← Alpha.decode 12 bytes
  let (proClient1, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod1, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag1, bytes) ← Alpha.decode 1 bytes
  let (filler1To16, bytes) ← Alpha.decode 2 bytes
  let (filler17, bytes) ← Alpha.decode 1 bytes
  let (filler18, bytes) ← Alpha.decode 1 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (spreadEntryTime, bytes) ← Alpha.decode 8 bytes
  let (echoBack, bytes) ← Alpha.decode 16 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  let (priceDiff, bytes) ← decodeUInt 4 bytes
  let (msSpdLegInfoLeg2, bytes) ← MsSpdLegInfoLeg2.decode bytes
  let (msSpdLegInfoLeg3, bytes) ← MsSpdLegInfoLeg3.decode bytes
  pure ({ participantType1, filler1, competitorPeriod1, solicitorPeriod1, modCxlBy1, filler9, reasonCode1, startAlpha1, endAlpha1, token1, contractDesc, opBrokerId1, fillerx1, fillerOptions1, fillery1, orderType1, orderNumber1, accountNumber1, bookType1, buySell1, disclosedVol1, disclosedVolRemaining1, totalVolRemaining1, volume1, volumeFilledToday1, price1, triggerPrice1, goodTillDate1, entryDateTime1, minFillAon1, lastModified1, stOrderFlags, branchId1, traderId1, brokerId1, cOrdFiller, openClose1, settlor1, proClient1, settlementPeriod1, additionalOrderFlags, giveupFlag1, filler1To16, filler17, filler18, nnfField, spreadEntryTime, echoBack, lastActivityReference, reserved52, priceDiff, msSpdLegInfoLeg2, msSpdLegInfoLeg3 }, bytes)

@[simp] theorem encode_length (message : SpreadModRejectMessage) : (encode message).length = 440 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, OpenClose1.encode_length, encodeUIntLE_length, MsSpdLegInfoLeg2.encode_length, MsSpdLegInfoLeg3.encode_length]

theorem encode_length_pos (message : SpreadModRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SpreadModRejectMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, OpenClose1.decode_encode, some_bind]
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
  rw [List.append_assoc, MsSpdLegInfoLeg2.decode_encode, some_bind]
  dsimp only
  rw [MsSpdLegInfoLeg3.decode_encode, some_bind]
  rfl

end SpreadModRejectMessage

/-- Spread Cxl Reject Message: 440 bytes -/
structure SpreadCxlRejectMessage where
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
  openClose1 : OpenClose1
  settlor1 : Alpha 12
  proClient1 : BitVec 16
  settlementPeriod1 : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag1 : Alpha 1
  filler1To16 : Alpha 2
  filler17 : Alpha 1
  filler18 : Alpha 1
  nnfField : Alpha 8
  spreadEntryTime : Alpha 8
  echoBack : Alpha 16
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  priceDiff : BitVec 32
  msSpdLegInfoLeg2 : MsSpdLegInfoLeg2
  msSpdLegInfoLeg3 : MsSpdLegInfoLeg3
  deriving DecidableEq, Repr

namespace SpreadCxlRejectMessage

def encode (message : SpreadCxlRejectMessage) : List UInt8 :=
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
    ++ (OpenClose1.encode message.openClose1
    ++ (Alpha.encode message.settlor1
    ++ (encodeUInt 2 message.proClient1
    ++ (encodeUInt 2 message.settlementPeriod1
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag1
    ++ (Alpha.encode message.filler1To16
    ++ (Alpha.encode message.filler17
    ++ (Alpha.encode message.filler18
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.spreadEntryTime
    ++ (Alpha.encode message.echoBack
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52
    ++ (encodeUInt 4 message.priceDiff
    ++ (MsSpdLegInfoLeg2.encode message.msSpdLegInfoLeg2
    ++ (MsSpdLegInfoLeg3.encode message.msSpdLegInfoLeg3))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SpreadCxlRejectMessage × List UInt8) := do
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
  let (openClose1, bytes) ← OpenClose1.decode bytes
  let (settlor1, bytes) ← Alpha.decode 12 bytes
  let (proClient1, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod1, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag1, bytes) ← Alpha.decode 1 bytes
  let (filler1To16, bytes) ← Alpha.decode 2 bytes
  let (filler17, bytes) ← Alpha.decode 1 bytes
  let (filler18, bytes) ← Alpha.decode 1 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (spreadEntryTime, bytes) ← Alpha.decode 8 bytes
  let (echoBack, bytes) ← Alpha.decode 16 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  let (priceDiff, bytes) ← decodeUInt 4 bytes
  let (msSpdLegInfoLeg2, bytes) ← MsSpdLegInfoLeg2.decode bytes
  let (msSpdLegInfoLeg3, bytes) ← MsSpdLegInfoLeg3.decode bytes
  pure ({ participantType1, filler1, competitorPeriod1, solicitorPeriod1, modCxlBy1, filler9, reasonCode1, startAlpha1, endAlpha1, token1, contractDesc, opBrokerId1, fillerx1, fillerOptions1, fillery1, orderType1, orderNumber1, accountNumber1, bookType1, buySell1, disclosedVol1, disclosedVolRemaining1, totalVolRemaining1, volume1, volumeFilledToday1, price1, triggerPrice1, goodTillDate1, entryDateTime1, minFillAon1, lastModified1, stOrderFlags, branchId1, traderId1, brokerId1, cOrdFiller, openClose1, settlor1, proClient1, settlementPeriod1, additionalOrderFlags, giveupFlag1, filler1To16, filler17, filler18, nnfField, spreadEntryTime, echoBack, lastActivityReference, reserved52, priceDiff, msSpdLegInfoLeg2, msSpdLegInfoLeg3 }, bytes)

@[simp] theorem encode_length (message : SpreadCxlRejectMessage) : (encode message).length = 440 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, OpenClose1.encode_length, encodeUIntLE_length, MsSpdLegInfoLeg2.encode_length, MsSpdLegInfoLeg3.encode_length]

theorem encode_length_pos (message : SpreadCxlRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SpreadCxlRejectMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, OpenClose1.decode_encode, some_bind]
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
  rw [List.append_assoc, MsSpdLegInfoLeg2.decode_encode, some_bind]
  dsimp only
  rw [MsSpdLegInfoLeg3.decode_encode, some_bind]
  rfl

end SpreadCxlRejectMessage

/-- Batch Spread Order Cancel Message: 440 bytes -/
structure BatchSpreadOrderCancelMessage where
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
  openClose1 : OpenClose1
  settlor1 : Alpha 12
  proClient1 : BitVec 16
  settlementPeriod1 : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag1 : Alpha 1
  filler1To16 : Alpha 2
  filler17 : Alpha 1
  filler18 : Alpha 1
  nnfField : Alpha 8
  spreadEntryTime : Alpha 8
  echoBack : Alpha 16
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  priceDiff : BitVec 32
  msSpdLegInfoLeg2 : MsSpdLegInfoLeg2
  msSpdLegInfoLeg3 : MsSpdLegInfoLeg3
  deriving DecidableEq, Repr

namespace BatchSpreadOrderCancelMessage

def encode (message : BatchSpreadOrderCancelMessage) : List UInt8 :=
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
    ++ (OpenClose1.encode message.openClose1
    ++ (Alpha.encode message.settlor1
    ++ (encodeUInt 2 message.proClient1
    ++ (encodeUInt 2 message.settlementPeriod1
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag1
    ++ (Alpha.encode message.filler1To16
    ++ (Alpha.encode message.filler17
    ++ (Alpha.encode message.filler18
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.spreadEntryTime
    ++ (Alpha.encode message.echoBack
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52
    ++ (encodeUInt 4 message.priceDiff
    ++ (MsSpdLegInfoLeg2.encode message.msSpdLegInfoLeg2
    ++ (MsSpdLegInfoLeg3.encode message.msSpdLegInfoLeg3))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (BatchSpreadOrderCancelMessage × List UInt8) := do
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
  let (openClose1, bytes) ← OpenClose1.decode bytes
  let (settlor1, bytes) ← Alpha.decode 12 bytes
  let (proClient1, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod1, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag1, bytes) ← Alpha.decode 1 bytes
  let (filler1To16, bytes) ← Alpha.decode 2 bytes
  let (filler17, bytes) ← Alpha.decode 1 bytes
  let (filler18, bytes) ← Alpha.decode 1 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (spreadEntryTime, bytes) ← Alpha.decode 8 bytes
  let (echoBack, bytes) ← Alpha.decode 16 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  let (priceDiff, bytes) ← decodeUInt 4 bytes
  let (msSpdLegInfoLeg2, bytes) ← MsSpdLegInfoLeg2.decode bytes
  let (msSpdLegInfoLeg3, bytes) ← MsSpdLegInfoLeg3.decode bytes
  pure ({ participantType1, filler1, competitorPeriod1, solicitorPeriod1, modCxlBy1, filler9, reasonCode1, startAlpha1, endAlpha1, token1, contractDesc, opBrokerId1, fillerx1, fillerOptions1, fillery1, orderType1, orderNumber1, accountNumber1, bookType1, buySell1, disclosedVol1, disclosedVolRemaining1, totalVolRemaining1, volume1, volumeFilledToday1, price1, triggerPrice1, goodTillDate1, entryDateTime1, minFillAon1, lastModified1, stOrderFlags, branchId1, traderId1, brokerId1, cOrdFiller, openClose1, settlor1, proClient1, settlementPeriod1, additionalOrderFlags, giveupFlag1, filler1To16, filler17, filler18, nnfField, spreadEntryTime, echoBack, lastActivityReference, reserved52, priceDiff, msSpdLegInfoLeg2, msSpdLegInfoLeg3 }, bytes)

@[simp] theorem encode_length (message : BatchSpreadOrderCancelMessage) : (encode message).length = 440 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, OpenClose1.encode_length, encodeUIntLE_length, MsSpdLegInfoLeg2.encode_length, MsSpdLegInfoLeg3.encode_length]

theorem encode_length_pos (message : BatchSpreadOrderCancelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : BatchSpreadOrderCancelMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, OpenClose1.decode_encode, some_bind]
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
  rw [List.append_assoc, MsSpdLegInfoLeg2.decode_encode, some_bind]
  dsimp only
  rw [MsSpdLegInfoLeg3.decode_encode, some_bind]
  rfl

end BatchSpreadOrderCancelMessage

/-- Twol Order Confirmation Message: 440 bytes -/
structure TwolOrderConfirmationMessage where
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
  openClose1 : OpenClose1
  settlor1 : Alpha 12
  proClient1 : BitVec 16
  settlementPeriod1 : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag1 : Alpha 1
  filler1To16 : Alpha 2
  filler17 : Alpha 1
  filler18 : Alpha 1
  nnfField : Alpha 8
  spreadEntryTime : Alpha 8
  echoBack : Alpha 16
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  priceDiff : BitVec 32
  msSpdLegInfoLeg2 : MsSpdLegInfoLeg2
  msSpdLegInfoLeg3 : MsSpdLegInfoLeg3
  deriving DecidableEq, Repr

namespace TwolOrderConfirmationMessage

def encode (message : TwolOrderConfirmationMessage) : List UInt8 :=
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
    ++ (OpenClose1.encode message.openClose1
    ++ (Alpha.encode message.settlor1
    ++ (encodeUInt 2 message.proClient1
    ++ (encodeUInt 2 message.settlementPeriod1
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag1
    ++ (Alpha.encode message.filler1To16
    ++ (Alpha.encode message.filler17
    ++ (Alpha.encode message.filler18
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.spreadEntryTime
    ++ (Alpha.encode message.echoBack
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52
    ++ (encodeUInt 4 message.priceDiff
    ++ (MsSpdLegInfoLeg2.encode message.msSpdLegInfoLeg2
    ++ (MsSpdLegInfoLeg3.encode message.msSpdLegInfoLeg3))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TwolOrderConfirmationMessage × List UInt8) := do
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
  let (openClose1, bytes) ← OpenClose1.decode bytes
  let (settlor1, bytes) ← Alpha.decode 12 bytes
  let (proClient1, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod1, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag1, bytes) ← Alpha.decode 1 bytes
  let (filler1To16, bytes) ← Alpha.decode 2 bytes
  let (filler17, bytes) ← Alpha.decode 1 bytes
  let (filler18, bytes) ← Alpha.decode 1 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (spreadEntryTime, bytes) ← Alpha.decode 8 bytes
  let (echoBack, bytes) ← Alpha.decode 16 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  let (priceDiff, bytes) ← decodeUInt 4 bytes
  let (msSpdLegInfoLeg2, bytes) ← MsSpdLegInfoLeg2.decode bytes
  let (msSpdLegInfoLeg3, bytes) ← MsSpdLegInfoLeg3.decode bytes
  pure ({ participantType1, filler1, competitorPeriod1, solicitorPeriod1, modCxlBy1, filler9, reasonCode1, startAlpha1, endAlpha1, token1, contractDesc, opBrokerId1, fillerx1, fillerOptions1, fillery1, orderType1, orderNumber1, accountNumber1, bookType1, buySell1, disclosedVol1, disclosedVolRemaining1, totalVolRemaining1, volume1, volumeFilledToday1, price1, triggerPrice1, goodTillDate1, entryDateTime1, minFillAon1, lastModified1, stOrderFlags, branchId1, traderId1, brokerId1, cOrdFiller, openClose1, settlor1, proClient1, settlementPeriod1, additionalOrderFlags, giveupFlag1, filler1To16, filler17, filler18, nnfField, spreadEntryTime, echoBack, lastActivityReference, reserved52, priceDiff, msSpdLegInfoLeg2, msSpdLegInfoLeg3 }, bytes)

@[simp] theorem encode_length (message : TwolOrderConfirmationMessage) : (encode message).length = 440 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, OpenClose1.encode_length, encodeUIntLE_length, MsSpdLegInfoLeg2.encode_length, MsSpdLegInfoLeg3.encode_length]

theorem encode_length_pos (message : TwolOrderConfirmationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : TwolOrderConfirmationMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, OpenClose1.decode_encode, some_bind]
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
  rw [List.append_assoc, MsSpdLegInfoLeg2.decode_encode, some_bind]
  dsimp only
  rw [MsSpdLegInfoLeg3.decode_encode, some_bind]
  rfl

end TwolOrderConfirmationMessage

/-- Thrl Order Confirmation Message: 440 bytes -/
structure ThrlOrderConfirmationMessage where
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
  openClose1 : OpenClose1
  settlor1 : Alpha 12
  proClient1 : BitVec 16
  settlementPeriod1 : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag1 : Alpha 1
  filler1To16 : Alpha 2
  filler17 : Alpha 1
  filler18 : Alpha 1
  nnfField : Alpha 8
  spreadEntryTime : Alpha 8
  echoBack : Alpha 16
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  priceDiff : BitVec 32
  msSpdLegInfoLeg2 : MsSpdLegInfoLeg2
  msSpdLegInfoLeg3 : MsSpdLegInfoLeg3
  deriving DecidableEq, Repr

namespace ThrlOrderConfirmationMessage

def encode (message : ThrlOrderConfirmationMessage) : List UInt8 :=
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
    ++ (OpenClose1.encode message.openClose1
    ++ (Alpha.encode message.settlor1
    ++ (encodeUInt 2 message.proClient1
    ++ (encodeUInt 2 message.settlementPeriod1
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag1
    ++ (Alpha.encode message.filler1To16
    ++ (Alpha.encode message.filler17
    ++ (Alpha.encode message.filler18
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.spreadEntryTime
    ++ (Alpha.encode message.echoBack
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52
    ++ (encodeUInt 4 message.priceDiff
    ++ (MsSpdLegInfoLeg2.encode message.msSpdLegInfoLeg2
    ++ (MsSpdLegInfoLeg3.encode message.msSpdLegInfoLeg3))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ThrlOrderConfirmationMessage × List UInt8) := do
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
  let (openClose1, bytes) ← OpenClose1.decode bytes
  let (settlor1, bytes) ← Alpha.decode 12 bytes
  let (proClient1, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod1, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag1, bytes) ← Alpha.decode 1 bytes
  let (filler1To16, bytes) ← Alpha.decode 2 bytes
  let (filler17, bytes) ← Alpha.decode 1 bytes
  let (filler18, bytes) ← Alpha.decode 1 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (spreadEntryTime, bytes) ← Alpha.decode 8 bytes
  let (echoBack, bytes) ← Alpha.decode 16 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  let (priceDiff, bytes) ← decodeUInt 4 bytes
  let (msSpdLegInfoLeg2, bytes) ← MsSpdLegInfoLeg2.decode bytes
  let (msSpdLegInfoLeg3, bytes) ← MsSpdLegInfoLeg3.decode bytes
  pure ({ participantType1, filler1, competitorPeriod1, solicitorPeriod1, modCxlBy1, filler9, reasonCode1, startAlpha1, endAlpha1, token1, contractDesc, opBrokerId1, fillerx1, fillerOptions1, fillery1, orderType1, orderNumber1, accountNumber1, bookType1, buySell1, disclosedVol1, disclosedVolRemaining1, totalVolRemaining1, volume1, volumeFilledToday1, price1, triggerPrice1, goodTillDate1, entryDateTime1, minFillAon1, lastModified1, stOrderFlags, branchId1, traderId1, brokerId1, cOrdFiller, openClose1, settlor1, proClient1, settlementPeriod1, additionalOrderFlags, giveupFlag1, filler1To16, filler17, filler18, nnfField, spreadEntryTime, echoBack, lastActivityReference, reserved52, priceDiff, msSpdLegInfoLeg2, msSpdLegInfoLeg3 }, bytes)

@[simp] theorem encode_length (message : ThrlOrderConfirmationMessage) : (encode message).length = 440 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, OpenClose1.encode_length, encodeUIntLE_length, MsSpdLegInfoLeg2.encode_length, MsSpdLegInfoLeg3.encode_length]

theorem encode_length_pos (message : ThrlOrderConfirmationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ThrlOrderConfirmationMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, OpenClose1.decode_encode, some_bind]
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
  rw [List.append_assoc, MsSpdLegInfoLeg2.decode_encode, some_bind]
  dsimp only
  rw [MsSpdLegInfoLeg3.decode_encode, some_bind]
  rfl

end ThrlOrderConfirmationMessage

/-- Twol Order Error Message: 440 bytes -/
structure TwolOrderErrorMessage where
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
  openClose1 : OpenClose1
  settlor1 : Alpha 12
  proClient1 : BitVec 16
  settlementPeriod1 : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag1 : Alpha 1
  filler1To16 : Alpha 2
  filler17 : Alpha 1
  filler18 : Alpha 1
  nnfField : Alpha 8
  spreadEntryTime : Alpha 8
  echoBack : Alpha 16
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  priceDiff : BitVec 32
  msSpdLegInfoLeg2 : MsSpdLegInfoLeg2
  msSpdLegInfoLeg3 : MsSpdLegInfoLeg3
  deriving DecidableEq, Repr

namespace TwolOrderErrorMessage

def encode (message : TwolOrderErrorMessage) : List UInt8 :=
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
    ++ (OpenClose1.encode message.openClose1
    ++ (Alpha.encode message.settlor1
    ++ (encodeUInt 2 message.proClient1
    ++ (encodeUInt 2 message.settlementPeriod1
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag1
    ++ (Alpha.encode message.filler1To16
    ++ (Alpha.encode message.filler17
    ++ (Alpha.encode message.filler18
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.spreadEntryTime
    ++ (Alpha.encode message.echoBack
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52
    ++ (encodeUInt 4 message.priceDiff
    ++ (MsSpdLegInfoLeg2.encode message.msSpdLegInfoLeg2
    ++ (MsSpdLegInfoLeg3.encode message.msSpdLegInfoLeg3))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TwolOrderErrorMessage × List UInt8) := do
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
  let (openClose1, bytes) ← OpenClose1.decode bytes
  let (settlor1, bytes) ← Alpha.decode 12 bytes
  let (proClient1, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod1, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag1, bytes) ← Alpha.decode 1 bytes
  let (filler1To16, bytes) ← Alpha.decode 2 bytes
  let (filler17, bytes) ← Alpha.decode 1 bytes
  let (filler18, bytes) ← Alpha.decode 1 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (spreadEntryTime, bytes) ← Alpha.decode 8 bytes
  let (echoBack, bytes) ← Alpha.decode 16 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  let (priceDiff, bytes) ← decodeUInt 4 bytes
  let (msSpdLegInfoLeg2, bytes) ← MsSpdLegInfoLeg2.decode bytes
  let (msSpdLegInfoLeg3, bytes) ← MsSpdLegInfoLeg3.decode bytes
  pure ({ participantType1, filler1, competitorPeriod1, solicitorPeriod1, modCxlBy1, filler9, reasonCode1, startAlpha1, endAlpha1, token1, contractDesc, opBrokerId1, fillerx1, fillerOptions1, fillery1, orderType1, orderNumber1, accountNumber1, bookType1, buySell1, disclosedVol1, disclosedVolRemaining1, totalVolRemaining1, volume1, volumeFilledToday1, price1, triggerPrice1, goodTillDate1, entryDateTime1, minFillAon1, lastModified1, stOrderFlags, branchId1, traderId1, brokerId1, cOrdFiller, openClose1, settlor1, proClient1, settlementPeriod1, additionalOrderFlags, giveupFlag1, filler1To16, filler17, filler18, nnfField, spreadEntryTime, echoBack, lastActivityReference, reserved52, priceDiff, msSpdLegInfoLeg2, msSpdLegInfoLeg3 }, bytes)

@[simp] theorem encode_length (message : TwolOrderErrorMessage) : (encode message).length = 440 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, OpenClose1.encode_length, encodeUIntLE_length, MsSpdLegInfoLeg2.encode_length, MsSpdLegInfoLeg3.encode_length]

theorem encode_length_pos (message : TwolOrderErrorMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : TwolOrderErrorMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, OpenClose1.decode_encode, some_bind]
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
  rw [List.append_assoc, MsSpdLegInfoLeg2.decode_encode, some_bind]
  dsimp only
  rw [MsSpdLegInfoLeg3.decode_encode, some_bind]
  rfl

end TwolOrderErrorMessage

/-- Thrl Order Error Message: 440 bytes -/
structure ThrlOrderErrorMessage where
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
  openClose1 : OpenClose1
  settlor1 : Alpha 12
  proClient1 : BitVec 16
  settlementPeriod1 : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag1 : Alpha 1
  filler1To16 : Alpha 2
  filler17 : Alpha 1
  filler18 : Alpha 1
  nnfField : Alpha 8
  spreadEntryTime : Alpha 8
  echoBack : Alpha 16
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  priceDiff : BitVec 32
  msSpdLegInfoLeg2 : MsSpdLegInfoLeg2
  msSpdLegInfoLeg3 : MsSpdLegInfoLeg3
  deriving DecidableEq, Repr

namespace ThrlOrderErrorMessage

def encode (message : ThrlOrderErrorMessage) : List UInt8 :=
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
    ++ (OpenClose1.encode message.openClose1
    ++ (Alpha.encode message.settlor1
    ++ (encodeUInt 2 message.proClient1
    ++ (encodeUInt 2 message.settlementPeriod1
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag1
    ++ (Alpha.encode message.filler1To16
    ++ (Alpha.encode message.filler17
    ++ (Alpha.encode message.filler18
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.spreadEntryTime
    ++ (Alpha.encode message.echoBack
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52
    ++ (encodeUInt 4 message.priceDiff
    ++ (MsSpdLegInfoLeg2.encode message.msSpdLegInfoLeg2
    ++ (MsSpdLegInfoLeg3.encode message.msSpdLegInfoLeg3))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ThrlOrderErrorMessage × List UInt8) := do
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
  let (openClose1, bytes) ← OpenClose1.decode bytes
  let (settlor1, bytes) ← Alpha.decode 12 bytes
  let (proClient1, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod1, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag1, bytes) ← Alpha.decode 1 bytes
  let (filler1To16, bytes) ← Alpha.decode 2 bytes
  let (filler17, bytes) ← Alpha.decode 1 bytes
  let (filler18, bytes) ← Alpha.decode 1 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (spreadEntryTime, bytes) ← Alpha.decode 8 bytes
  let (echoBack, bytes) ← Alpha.decode 16 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  let (priceDiff, bytes) ← decodeUInt 4 bytes
  let (msSpdLegInfoLeg2, bytes) ← MsSpdLegInfoLeg2.decode bytes
  let (msSpdLegInfoLeg3, bytes) ← MsSpdLegInfoLeg3.decode bytes
  pure ({ participantType1, filler1, competitorPeriod1, solicitorPeriod1, modCxlBy1, filler9, reasonCode1, startAlpha1, endAlpha1, token1, contractDesc, opBrokerId1, fillerx1, fillerOptions1, fillery1, orderType1, orderNumber1, accountNumber1, bookType1, buySell1, disclosedVol1, disclosedVolRemaining1, totalVolRemaining1, volume1, volumeFilledToday1, price1, triggerPrice1, goodTillDate1, entryDateTime1, minFillAon1, lastModified1, stOrderFlags, branchId1, traderId1, brokerId1, cOrdFiller, openClose1, settlor1, proClient1, settlementPeriod1, additionalOrderFlags, giveupFlag1, filler1To16, filler17, filler18, nnfField, spreadEntryTime, echoBack, lastActivityReference, reserved52, priceDiff, msSpdLegInfoLeg2, msSpdLegInfoLeg3 }, bytes)

@[simp] theorem encode_length (message : ThrlOrderErrorMessage) : (encode message).length = 440 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, OpenClose1.encode_length, encodeUIntLE_length, MsSpdLegInfoLeg2.encode_length, MsSpdLegInfoLeg3.encode_length]

theorem encode_length_pos (message : ThrlOrderErrorMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ThrlOrderErrorMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, OpenClose1.decode_encode, some_bind]
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
  rw [List.append_assoc, MsSpdLegInfoLeg2.decode_encode, some_bind]
  dsimp only
  rw [MsSpdLegInfoLeg3.decode_encode, some_bind]
  rfl

end ThrlOrderErrorMessage

/-- Twol Net Order Error Message: 440 bytes -/
structure TwolNetOrderErrorMessage where
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
  openClose1 : OpenClose1
  settlor1 : Alpha 12
  proClient1 : BitVec 16
  settlementPeriod1 : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag1 : Alpha 1
  filler1To16 : Alpha 2
  filler17 : Alpha 1
  filler18 : Alpha 1
  nnfField : Alpha 8
  spreadEntryTime : Alpha 8
  echoBack : Alpha 16
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  priceDiff : BitVec 32
  msSpdLegInfoLeg2 : MsSpdLegInfoLeg2
  msSpdLegInfoLeg3 : MsSpdLegInfoLeg3
  deriving DecidableEq, Repr

namespace TwolNetOrderErrorMessage

def encode (message : TwolNetOrderErrorMessage) : List UInt8 :=
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
    ++ (OpenClose1.encode message.openClose1
    ++ (Alpha.encode message.settlor1
    ++ (encodeUInt 2 message.proClient1
    ++ (encodeUInt 2 message.settlementPeriod1
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag1
    ++ (Alpha.encode message.filler1To16
    ++ (Alpha.encode message.filler17
    ++ (Alpha.encode message.filler18
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.spreadEntryTime
    ++ (Alpha.encode message.echoBack
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52
    ++ (encodeUInt 4 message.priceDiff
    ++ (MsSpdLegInfoLeg2.encode message.msSpdLegInfoLeg2
    ++ (MsSpdLegInfoLeg3.encode message.msSpdLegInfoLeg3))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TwolNetOrderErrorMessage × List UInt8) := do
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
  let (openClose1, bytes) ← OpenClose1.decode bytes
  let (settlor1, bytes) ← Alpha.decode 12 bytes
  let (proClient1, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod1, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag1, bytes) ← Alpha.decode 1 bytes
  let (filler1To16, bytes) ← Alpha.decode 2 bytes
  let (filler17, bytes) ← Alpha.decode 1 bytes
  let (filler18, bytes) ← Alpha.decode 1 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (spreadEntryTime, bytes) ← Alpha.decode 8 bytes
  let (echoBack, bytes) ← Alpha.decode 16 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  let (priceDiff, bytes) ← decodeUInt 4 bytes
  let (msSpdLegInfoLeg2, bytes) ← MsSpdLegInfoLeg2.decode bytes
  let (msSpdLegInfoLeg3, bytes) ← MsSpdLegInfoLeg3.decode bytes
  pure ({ participantType1, filler1, competitorPeriod1, solicitorPeriod1, modCxlBy1, filler9, reasonCode1, startAlpha1, endAlpha1, token1, contractDesc, opBrokerId1, fillerx1, fillerOptions1, fillery1, orderType1, orderNumber1, accountNumber1, bookType1, buySell1, disclosedVol1, disclosedVolRemaining1, totalVolRemaining1, volume1, volumeFilledToday1, price1, triggerPrice1, goodTillDate1, entryDateTime1, minFillAon1, lastModified1, stOrderFlags, branchId1, traderId1, brokerId1, cOrdFiller, openClose1, settlor1, proClient1, settlementPeriod1, additionalOrderFlags, giveupFlag1, filler1To16, filler17, filler18, nnfField, spreadEntryTime, echoBack, lastActivityReference, reserved52, priceDiff, msSpdLegInfoLeg2, msSpdLegInfoLeg3 }, bytes)

@[simp] theorem encode_length (message : TwolNetOrderErrorMessage) : (encode message).length = 440 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, OpenClose1.encode_length, encodeUIntLE_length, MsSpdLegInfoLeg2.encode_length, MsSpdLegInfoLeg3.encode_length]

theorem encode_length_pos (message : TwolNetOrderErrorMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : TwolNetOrderErrorMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, OpenClose1.decode_encode, some_bind]
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
  rw [List.append_assoc, MsSpdLegInfoLeg2.decode_encode, some_bind]
  dsimp only
  rw [MsSpdLegInfoLeg3.decode_encode, some_bind]
  rfl

end TwolNetOrderErrorMessage

/-- Thrl Net Order Error Message: 440 bytes -/
structure ThrlNetOrderErrorMessage where
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
  openClose1 : OpenClose1
  settlor1 : Alpha 12
  proClient1 : BitVec 16
  settlementPeriod1 : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag1 : Alpha 1
  filler1To16 : Alpha 2
  filler17 : Alpha 1
  filler18 : Alpha 1
  nnfField : Alpha 8
  spreadEntryTime : Alpha 8
  echoBack : Alpha 16
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  priceDiff : BitVec 32
  msSpdLegInfoLeg2 : MsSpdLegInfoLeg2
  msSpdLegInfoLeg3 : MsSpdLegInfoLeg3
  deriving DecidableEq, Repr

namespace ThrlNetOrderErrorMessage

def encode (message : ThrlNetOrderErrorMessage) : List UInt8 :=
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
    ++ (OpenClose1.encode message.openClose1
    ++ (Alpha.encode message.settlor1
    ++ (encodeUInt 2 message.proClient1
    ++ (encodeUInt 2 message.settlementPeriod1
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag1
    ++ (Alpha.encode message.filler1To16
    ++ (Alpha.encode message.filler17
    ++ (Alpha.encode message.filler18
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.spreadEntryTime
    ++ (Alpha.encode message.echoBack
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52
    ++ (encodeUInt 4 message.priceDiff
    ++ (MsSpdLegInfoLeg2.encode message.msSpdLegInfoLeg2
    ++ (MsSpdLegInfoLeg3.encode message.msSpdLegInfoLeg3))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ThrlNetOrderErrorMessage × List UInt8) := do
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
  let (openClose1, bytes) ← OpenClose1.decode bytes
  let (settlor1, bytes) ← Alpha.decode 12 bytes
  let (proClient1, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod1, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag1, bytes) ← Alpha.decode 1 bytes
  let (filler1To16, bytes) ← Alpha.decode 2 bytes
  let (filler17, bytes) ← Alpha.decode 1 bytes
  let (filler18, bytes) ← Alpha.decode 1 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (spreadEntryTime, bytes) ← Alpha.decode 8 bytes
  let (echoBack, bytes) ← Alpha.decode 16 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  let (priceDiff, bytes) ← decodeUInt 4 bytes
  let (msSpdLegInfoLeg2, bytes) ← MsSpdLegInfoLeg2.decode bytes
  let (msSpdLegInfoLeg3, bytes) ← MsSpdLegInfoLeg3.decode bytes
  pure ({ participantType1, filler1, competitorPeriod1, solicitorPeriod1, modCxlBy1, filler9, reasonCode1, startAlpha1, endAlpha1, token1, contractDesc, opBrokerId1, fillerx1, fillerOptions1, fillery1, orderType1, orderNumber1, accountNumber1, bookType1, buySell1, disclosedVol1, disclosedVolRemaining1, totalVolRemaining1, volume1, volumeFilledToday1, price1, triggerPrice1, goodTillDate1, entryDateTime1, minFillAon1, lastModified1, stOrderFlags, branchId1, traderId1, brokerId1, cOrdFiller, openClose1, settlor1, proClient1, settlementPeriod1, additionalOrderFlags, giveupFlag1, filler1To16, filler17, filler18, nnfField, spreadEntryTime, echoBack, lastActivityReference, reserved52, priceDiff, msSpdLegInfoLeg2, msSpdLegInfoLeg3 }, bytes)

@[simp] theorem encode_length (message : ThrlNetOrderErrorMessage) : (encode message).length = 440 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, OpenClose1.encode_length, encodeUIntLE_length, MsSpdLegInfoLeg2.encode_length, MsSpdLegInfoLeg3.encode_length]

theorem encode_length_pos (message : ThrlNetOrderErrorMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ThrlNetOrderErrorMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, OpenClose1.decode_encode, some_bind]
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
  rw [List.append_assoc, MsSpdLegInfoLeg2.decode_encode, some_bind]
  dsimp only
  rw [MsSpdLegInfoLeg3.decode_encode, some_bind]
  rfl

end ThrlNetOrderErrorMessage

/-- Twol Order Cxl Confirmation Message: 440 bytes -/
structure TwolOrderCxlConfirmationMessage where
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
  openClose1 : OpenClose1
  settlor1 : Alpha 12
  proClient1 : BitVec 16
  settlementPeriod1 : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag1 : Alpha 1
  filler1To16 : Alpha 2
  filler17 : Alpha 1
  filler18 : Alpha 1
  nnfField : Alpha 8
  spreadEntryTime : Alpha 8
  echoBack : Alpha 16
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  priceDiff : BitVec 32
  msSpdLegInfoLeg2 : MsSpdLegInfoLeg2
  msSpdLegInfoLeg3 : MsSpdLegInfoLeg3
  deriving DecidableEq, Repr

namespace TwolOrderCxlConfirmationMessage

def encode (message : TwolOrderCxlConfirmationMessage) : List UInt8 :=
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
    ++ (OpenClose1.encode message.openClose1
    ++ (Alpha.encode message.settlor1
    ++ (encodeUInt 2 message.proClient1
    ++ (encodeUInt 2 message.settlementPeriod1
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag1
    ++ (Alpha.encode message.filler1To16
    ++ (Alpha.encode message.filler17
    ++ (Alpha.encode message.filler18
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.spreadEntryTime
    ++ (Alpha.encode message.echoBack
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52
    ++ (encodeUInt 4 message.priceDiff
    ++ (MsSpdLegInfoLeg2.encode message.msSpdLegInfoLeg2
    ++ (MsSpdLegInfoLeg3.encode message.msSpdLegInfoLeg3))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TwolOrderCxlConfirmationMessage × List UInt8) := do
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
  let (openClose1, bytes) ← OpenClose1.decode bytes
  let (settlor1, bytes) ← Alpha.decode 12 bytes
  let (proClient1, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod1, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag1, bytes) ← Alpha.decode 1 bytes
  let (filler1To16, bytes) ← Alpha.decode 2 bytes
  let (filler17, bytes) ← Alpha.decode 1 bytes
  let (filler18, bytes) ← Alpha.decode 1 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (spreadEntryTime, bytes) ← Alpha.decode 8 bytes
  let (echoBack, bytes) ← Alpha.decode 16 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  let (priceDiff, bytes) ← decodeUInt 4 bytes
  let (msSpdLegInfoLeg2, bytes) ← MsSpdLegInfoLeg2.decode bytes
  let (msSpdLegInfoLeg3, bytes) ← MsSpdLegInfoLeg3.decode bytes
  pure ({ participantType1, filler1, competitorPeriod1, solicitorPeriod1, modCxlBy1, filler9, reasonCode1, startAlpha1, endAlpha1, token1, contractDesc, opBrokerId1, fillerx1, fillerOptions1, fillery1, orderType1, orderNumber1, accountNumber1, bookType1, buySell1, disclosedVol1, disclosedVolRemaining1, totalVolRemaining1, volume1, volumeFilledToday1, price1, triggerPrice1, goodTillDate1, entryDateTime1, minFillAon1, lastModified1, stOrderFlags, branchId1, traderId1, brokerId1, cOrdFiller, openClose1, settlor1, proClient1, settlementPeriod1, additionalOrderFlags, giveupFlag1, filler1To16, filler17, filler18, nnfField, spreadEntryTime, echoBack, lastActivityReference, reserved52, priceDiff, msSpdLegInfoLeg2, msSpdLegInfoLeg3 }, bytes)

@[simp] theorem encode_length (message : TwolOrderCxlConfirmationMessage) : (encode message).length = 440 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, OpenClose1.encode_length, encodeUIntLE_length, MsSpdLegInfoLeg2.encode_length, MsSpdLegInfoLeg3.encode_length]

theorem encode_length_pos (message : TwolOrderCxlConfirmationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : TwolOrderCxlConfirmationMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, OpenClose1.decode_encode, some_bind]
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
  rw [List.append_assoc, MsSpdLegInfoLeg2.decode_encode, some_bind]
  dsimp only
  rw [MsSpdLegInfoLeg3.decode_encode, some_bind]
  rfl

end TwolOrderCxlConfirmationMessage

/-- Thrl Order Cxl Confirmation Message: 440 bytes -/
structure ThrlOrderCxlConfirmationMessage where
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
  openClose1 : OpenClose1
  settlor1 : Alpha 12
  proClient1 : BitVec 16
  settlementPeriod1 : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag1 : Alpha 1
  filler1To16 : Alpha 2
  filler17 : Alpha 1
  filler18 : Alpha 1
  nnfField : Alpha 8
  spreadEntryTime : Alpha 8
  echoBack : Alpha 16
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  priceDiff : BitVec 32
  msSpdLegInfoLeg2 : MsSpdLegInfoLeg2
  msSpdLegInfoLeg3 : MsSpdLegInfoLeg3
  deriving DecidableEq, Repr

namespace ThrlOrderCxlConfirmationMessage

def encode (message : ThrlOrderCxlConfirmationMessage) : List UInt8 :=
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
    ++ (OpenClose1.encode message.openClose1
    ++ (Alpha.encode message.settlor1
    ++ (encodeUInt 2 message.proClient1
    ++ (encodeUInt 2 message.settlementPeriod1
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag1
    ++ (Alpha.encode message.filler1To16
    ++ (Alpha.encode message.filler17
    ++ (Alpha.encode message.filler18
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.spreadEntryTime
    ++ (Alpha.encode message.echoBack
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52
    ++ (encodeUInt 4 message.priceDiff
    ++ (MsSpdLegInfoLeg2.encode message.msSpdLegInfoLeg2
    ++ (MsSpdLegInfoLeg3.encode message.msSpdLegInfoLeg3))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ThrlOrderCxlConfirmationMessage × List UInt8) := do
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
  let (openClose1, bytes) ← OpenClose1.decode bytes
  let (settlor1, bytes) ← Alpha.decode 12 bytes
  let (proClient1, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod1, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag1, bytes) ← Alpha.decode 1 bytes
  let (filler1To16, bytes) ← Alpha.decode 2 bytes
  let (filler17, bytes) ← Alpha.decode 1 bytes
  let (filler18, bytes) ← Alpha.decode 1 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (spreadEntryTime, bytes) ← Alpha.decode 8 bytes
  let (echoBack, bytes) ← Alpha.decode 16 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  let (priceDiff, bytes) ← decodeUInt 4 bytes
  let (msSpdLegInfoLeg2, bytes) ← MsSpdLegInfoLeg2.decode bytes
  let (msSpdLegInfoLeg3, bytes) ← MsSpdLegInfoLeg3.decode bytes
  pure ({ participantType1, filler1, competitorPeriod1, solicitorPeriod1, modCxlBy1, filler9, reasonCode1, startAlpha1, endAlpha1, token1, contractDesc, opBrokerId1, fillerx1, fillerOptions1, fillery1, orderType1, orderNumber1, accountNumber1, bookType1, buySell1, disclosedVol1, disclosedVolRemaining1, totalVolRemaining1, volume1, volumeFilledToday1, price1, triggerPrice1, goodTillDate1, entryDateTime1, minFillAon1, lastModified1, stOrderFlags, branchId1, traderId1, brokerId1, cOrdFiller, openClose1, settlor1, proClient1, settlementPeriod1, additionalOrderFlags, giveupFlag1, filler1To16, filler17, filler18, nnfField, spreadEntryTime, echoBack, lastActivityReference, reserved52, priceDiff, msSpdLegInfoLeg2, msSpdLegInfoLeg3 }, bytes)

@[simp] theorem encode_length (message : ThrlOrderCxlConfirmationMessage) : (encode message).length = 440 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, OpenClose1.encode_length, encodeUIntLE_length, MsSpdLegInfoLeg2.encode_length, MsSpdLegInfoLeg3.encode_length]

theorem encode_length_pos (message : ThrlOrderCxlConfirmationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ThrlOrderCxlConfirmationMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, OpenClose1.decode_encode, some_bind]
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
  rw [List.append_assoc, MsSpdLegInfoLeg2.decode_encode, some_bind]
  dsimp only
  rw [MsSpdLegInfoLeg3.decode_encode, some_bind]
  rfl

end ThrlOrderCxlConfirmationMessage

/-- Any Server Message Payload, selected by Transaction Code -/
inductive ServerMessagePayload where
  | signOnOutMessage (message : SignOnOutMessage) -- 2301
  | tradeConfirmationMessage (message : TradeConfirmationMessage) -- 2222
  | tradeModifyConfirmMessage (message : TradeModifyConfirmMessage) -- 2287
  | tradeModifyRejectMessage (message : TradeModifyRejectMessage) -- 2288
  | tradeCancelConfirmMessage (message : TradeCancelConfirmMessage) -- 2282
  | tradeCancelRejectMessage (message : TradeCancelRejectMessage) -- 2286
  | nltTradeConfirmationMessage (message : NltTradeConfirmationMessage) -- 2090
  | nltTrdModConfirmationMessage (message : NltTrdModConfirmationMessage) -- 5449
  | nltTrdModRejectMessage (message : NltTrdModRejectMessage) -- 5450
  | nltTrdCxlConfirmationMessage (message : NltTrdCxlConfirmationMessage) -- 5452
  | nltTrdCxlRejectMessage (message : NltTrdCxlRejectMessage) -- 5453
  | giveupAppConfirmTmMessage (message : GiveupAppConfirmTmMessage) -- 4506
  | giveupRejConfirmTmMessage (message : GiveupRejConfirmTmMessage) -- 4507
  | boardLotOutMessage (message : BoardLotOutMessage) -- 2001
  | orderModOutMessage (message : OrderModOutMessage) -- 2041
  | orderModRejectMessage (message : OrderModRejectMessage) -- 2042
  | orderCancelOutMessage (message : OrderCancelOutMessage) -- 2071
  | orderCancelRejectMessage (message : OrderCancelRejectMessage) -- 2072
  | orderConfirmationMessage (message : OrderConfirmationMessage) -- 2073
  | orderModConfirmationMessage (message : OrderModConfirmationMessage) -- 2074
  | orderCancelConfirmationMessage (message : OrderCancelConfirmationMessage) -- 2075
  | freezeToControlMessage (message : FreezeToControlMessage) -- 2170
  | orderErrorMessage (message : OrderErrorMessage) -- 2231
  | batchOrderCancelMessage (message : BatchOrderCancelMessage) -- 9002
  | netOrderErrorMessage (message : NetOrderErrorMessage) -- 27100
  | nltConfirmationMessage (message : NltConfirmationMessage) -- 2083
  | nltModConfirmationMessage (message : NltModConfirmationMessage) -- 2085
  | nltCxlConfirmationMessage (message : NltCxlConfirmationMessage) -- 2087
  | nltModRejectMessage (message : NltModRejectMessage) -- 2088
  | nltCxlRejectMessage (message : NltCxlRejectMessage) -- 2089
  | spreadOrderConfirmationMessage (message : SpreadOrderConfirmationMessage) -- 2124
  | spOrderErrorMessage (message : SpOrderErrorMessage) -- 2154
  | spNetOrderErrorMessage (message : SpNetOrderErrorMessage) -- 27102
  | spreadCxlConfirmationMessage (message : SpreadCxlConfirmationMessage) -- 2130
  | spreadModConfirmationMessage (message : SpreadModConfirmationMessage) -- 2136
  | spreadModRejectMessage (message : SpreadModRejectMessage) -- 2133
  | spreadCxlRejectMessage (message : SpreadCxlRejectMessage) -- 2127
  | batchSpreadOrderCancelMessage (message : BatchSpreadOrderCancelMessage) -- 9004
  | twolOrderConfirmationMessage (message : TwolOrderConfirmationMessage) -- 2125
  | thrlOrderConfirmationMessage (message : ThrlOrderConfirmationMessage) -- 2126
  | twolOrderErrorMessage (message : TwolOrderErrorMessage) -- 2155
  | thrlOrderErrorMessage (message : ThrlOrderErrorMessage) -- 2156
  | twolNetOrderErrorMessage (message : TwolNetOrderErrorMessage) -- 27103
  | thrlNetOrderErrorMessage (message : ThrlNetOrderErrorMessage) -- 27104
  | twolOrderCxlConfirmationMessage (message : TwolOrderCxlConfirmationMessage) -- 2131
  | thrlOrderCxlConfirmationMessage (message : ThrlOrderCxlConfirmationMessage) -- 2132
  deriving DecidableEq, Repr

namespace ServerMessagePayload

/-- The Transaction Code each message is sent under -/
def tag : ServerMessagePayload → BitVec 16
  | .signOnOutMessage _ => 2301
  | .tradeConfirmationMessage _ => 2222
  | .tradeModifyConfirmMessage _ => 2287
  | .tradeModifyRejectMessage _ => 2288
  | .tradeCancelConfirmMessage _ => 2282
  | .tradeCancelRejectMessage _ => 2286
  | .nltTradeConfirmationMessage _ => 2090
  | .nltTrdModConfirmationMessage _ => 5449
  | .nltTrdModRejectMessage _ => 5450
  | .nltTrdCxlConfirmationMessage _ => 5452
  | .nltTrdCxlRejectMessage _ => 5453
  | .giveupAppConfirmTmMessage _ => 4506
  | .giveupRejConfirmTmMessage _ => 4507
  | .boardLotOutMessage _ => 2001
  | .orderModOutMessage _ => 2041
  | .orderModRejectMessage _ => 2042
  | .orderCancelOutMessage _ => 2071
  | .orderCancelRejectMessage _ => 2072
  | .orderConfirmationMessage _ => 2073
  | .orderModConfirmationMessage _ => 2074
  | .orderCancelConfirmationMessage _ => 2075
  | .freezeToControlMessage _ => 2170
  | .orderErrorMessage _ => 2231
  | .batchOrderCancelMessage _ => 9002
  | .netOrderErrorMessage _ => 27100
  | .nltConfirmationMessage _ => 2083
  | .nltModConfirmationMessage _ => 2085
  | .nltCxlConfirmationMessage _ => 2087
  | .nltModRejectMessage _ => 2088
  | .nltCxlRejectMessage _ => 2089
  | .spreadOrderConfirmationMessage _ => 2124
  | .spOrderErrorMessage _ => 2154
  | .spNetOrderErrorMessage _ => 27102
  | .spreadCxlConfirmationMessage _ => 2130
  | .spreadModConfirmationMessage _ => 2136
  | .spreadModRejectMessage _ => 2133
  | .spreadCxlRejectMessage _ => 2127
  | .batchSpreadOrderCancelMessage _ => 9004
  | .twolOrderConfirmationMessage _ => 2125
  | .thrlOrderConfirmationMessage _ => 2126
  | .twolOrderErrorMessage _ => 2155
  | .thrlOrderErrorMessage _ => 2156
  | .twolNetOrderErrorMessage _ => 27103
  | .thrlNetOrderErrorMessage _ => 27104
  | .twolOrderCxlConfirmationMessage _ => 2131
  | .thrlOrderCxlConfirmationMessage _ => 2132

def encode : ServerMessagePayload → List UInt8
  | .signOnOutMessage message => SignOnOutMessage.encode message
  | .tradeConfirmationMessage message => TradeConfirmationMessage.encode message
  | .tradeModifyConfirmMessage message => TradeModifyConfirmMessage.encode message
  | .tradeModifyRejectMessage message => TradeModifyRejectMessage.encode message
  | .tradeCancelConfirmMessage message => TradeCancelConfirmMessage.encode message
  | .tradeCancelRejectMessage message => TradeCancelRejectMessage.encode message
  | .nltTradeConfirmationMessage message => NltTradeConfirmationMessage.encode message
  | .nltTrdModConfirmationMessage message => NltTrdModConfirmationMessage.encode message
  | .nltTrdModRejectMessage message => NltTrdModRejectMessage.encode message
  | .nltTrdCxlConfirmationMessage message => NltTrdCxlConfirmationMessage.encode message
  | .nltTrdCxlRejectMessage message => NltTrdCxlRejectMessage.encode message
  | .giveupAppConfirmTmMessage message => GiveupAppConfirmTmMessage.encode message
  | .giveupRejConfirmTmMessage message => GiveupRejConfirmTmMessage.encode message
  | .boardLotOutMessage message => BoardLotOutMessage.encode message
  | .orderModOutMessage message => OrderModOutMessage.encode message
  | .orderModRejectMessage message => OrderModRejectMessage.encode message
  | .orderCancelOutMessage message => OrderCancelOutMessage.encode message
  | .orderCancelRejectMessage message => OrderCancelRejectMessage.encode message
  | .orderConfirmationMessage message => OrderConfirmationMessage.encode message
  | .orderModConfirmationMessage message => OrderModConfirmationMessage.encode message
  | .orderCancelConfirmationMessage message => OrderCancelConfirmationMessage.encode message
  | .freezeToControlMessage message => FreezeToControlMessage.encode message
  | .orderErrorMessage message => OrderErrorMessage.encode message
  | .batchOrderCancelMessage message => BatchOrderCancelMessage.encode message
  | .netOrderErrorMessage message => NetOrderErrorMessage.encode message
  | .nltConfirmationMessage message => NltConfirmationMessage.encode message
  | .nltModConfirmationMessage message => NltModConfirmationMessage.encode message
  | .nltCxlConfirmationMessage message => NltCxlConfirmationMessage.encode message
  | .nltModRejectMessage message => NltModRejectMessage.encode message
  | .nltCxlRejectMessage message => NltCxlRejectMessage.encode message
  | .spreadOrderConfirmationMessage message => SpreadOrderConfirmationMessage.encode message
  | .spOrderErrorMessage message => SpOrderErrorMessage.encode message
  | .spNetOrderErrorMessage message => SpNetOrderErrorMessage.encode message
  | .spreadCxlConfirmationMessage message => SpreadCxlConfirmationMessage.encode message
  | .spreadModConfirmationMessage message => SpreadModConfirmationMessage.encode message
  | .spreadModRejectMessage message => SpreadModRejectMessage.encode message
  | .spreadCxlRejectMessage message => SpreadCxlRejectMessage.encode message
  | .batchSpreadOrderCancelMessage message => BatchSpreadOrderCancelMessage.encode message
  | .twolOrderConfirmationMessage message => TwolOrderConfirmationMessage.encode message
  | .thrlOrderConfirmationMessage message => ThrlOrderConfirmationMessage.encode message
  | .twolOrderErrorMessage message => TwolOrderErrorMessage.encode message
  | .thrlOrderErrorMessage message => ThrlOrderErrorMessage.encode message
  | .twolNetOrderErrorMessage message => TwolNetOrderErrorMessage.encode message
  | .thrlNetOrderErrorMessage message => ThrlNetOrderErrorMessage.encode message
  | .twolOrderCxlConfirmationMessage message => TwolOrderCxlConfirmationMessage.encode message
  | .thrlOrderCxlConfirmationMessage message => ThrlOrderCxlConfirmationMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ServerMessagePayload) : (encode message).length ≤ 440 := by
  cases message with
  | signOnOutMessage inner =>
    simp only [encode, SignOnOutMessage.encode_length]
    omega
  | tradeConfirmationMessage inner =>
    simp only [encode, TradeConfirmationMessage.encode_length]
    omega
  | tradeModifyConfirmMessage inner =>
    simp only [encode, TradeModifyConfirmMessage.encode_length]
    omega
  | tradeModifyRejectMessage inner =>
    simp only [encode, TradeModifyRejectMessage.encode_length]
    omega
  | tradeCancelConfirmMessage inner =>
    simp only [encode, TradeCancelConfirmMessage.encode_length]
    omega
  | tradeCancelRejectMessage inner =>
    simp only [encode, TradeCancelRejectMessage.encode_length]
    omega
  | nltTradeConfirmationMessage inner =>
    simp only [encode, NltTradeConfirmationMessage.encode_length]
    omega
  | nltTrdModConfirmationMessage inner =>
    simp only [encode, NltTrdModConfirmationMessage.encode_length]
    omega
  | nltTrdModRejectMessage inner =>
    simp only [encode, NltTrdModRejectMessage.encode_length]
    omega
  | nltTrdCxlConfirmationMessage inner =>
    simp only [encode, NltTrdCxlConfirmationMessage.encode_length]
    omega
  | nltTrdCxlRejectMessage inner =>
    simp only [encode, NltTrdCxlRejectMessage.encode_length]
    omega
  | giveupAppConfirmTmMessage inner =>
    simp only [encode, GiveupAppConfirmTmMessage.encode_length]
    omega
  | giveupRejConfirmTmMessage inner =>
    simp only [encode, GiveupRejConfirmTmMessage.encode_length]
    omega
  | boardLotOutMessage inner =>
    simp only [encode, BoardLotOutMessage.encode_length]
    omega
  | orderModOutMessage inner =>
    simp only [encode, OrderModOutMessage.encode_length]
    omega
  | orderModRejectMessage inner =>
    simp only [encode, OrderModRejectMessage.encode_length]
    omega
  | orderCancelOutMessage inner =>
    simp only [encode, OrderCancelOutMessage.encode_length]
    omega
  | orderCancelRejectMessage inner =>
    simp only [encode, OrderCancelRejectMessage.encode_length]
    omega
  | orderConfirmationMessage inner =>
    simp only [encode, OrderConfirmationMessage.encode_length]
    omega
  | orderModConfirmationMessage inner =>
    simp only [encode, OrderModConfirmationMessage.encode_length]
    omega
  | orderCancelConfirmationMessage inner =>
    simp only [encode, OrderCancelConfirmationMessage.encode_length]
    omega
  | freezeToControlMessage inner =>
    simp only [encode, FreezeToControlMessage.encode_length]
    omega
  | orderErrorMessage inner =>
    simp only [encode, OrderErrorMessage.encode_length]
    omega
  | batchOrderCancelMessage inner =>
    simp only [encode, BatchOrderCancelMessage.encode_length]
    omega
  | netOrderErrorMessage inner =>
    simp only [encode, NetOrderErrorMessage.encode_length]
    omega
  | nltConfirmationMessage inner =>
    simp only [encode, NltConfirmationMessage.encode_length]
    omega
  | nltModConfirmationMessage inner =>
    simp only [encode, NltModConfirmationMessage.encode_length]
    omega
  | nltCxlConfirmationMessage inner =>
    simp only [encode, NltCxlConfirmationMessage.encode_length]
    omega
  | nltModRejectMessage inner =>
    simp only [encode, NltModRejectMessage.encode_length]
    omega
  | nltCxlRejectMessage inner =>
    simp only [encode, NltCxlRejectMessage.encode_length]
    omega
  | spreadOrderConfirmationMessage inner =>
    simp only [encode, SpreadOrderConfirmationMessage.encode_length]
    omega
  | spOrderErrorMessage inner =>
    simp only [encode, SpOrderErrorMessage.encode_length]
    omega
  | spNetOrderErrorMessage inner =>
    simp only [encode, SpNetOrderErrorMessage.encode_length]
    omega
  | spreadCxlConfirmationMessage inner =>
    simp only [encode, SpreadCxlConfirmationMessage.encode_length]
    omega
  | spreadModConfirmationMessage inner =>
    simp only [encode, SpreadModConfirmationMessage.encode_length]
    omega
  | spreadModRejectMessage inner =>
    simp only [encode, SpreadModRejectMessage.encode_length]
    omega
  | spreadCxlRejectMessage inner =>
    simp only [encode, SpreadCxlRejectMessage.encode_length]
    omega
  | batchSpreadOrderCancelMessage inner =>
    simp only [encode, BatchSpreadOrderCancelMessage.encode_length]
    omega
  | twolOrderConfirmationMessage inner =>
    simp only [encode, TwolOrderConfirmationMessage.encode_length]
    omega
  | thrlOrderConfirmationMessage inner =>
    simp only [encode, ThrlOrderConfirmationMessage.encode_length]
    omega
  | twolOrderErrorMessage inner =>
    simp only [encode, TwolOrderErrorMessage.encode_length]
    omega
  | thrlOrderErrorMessage inner =>
    simp only [encode, ThrlOrderErrorMessage.encode_length]
    omega
  | twolNetOrderErrorMessage inner =>
    simp only [encode, TwolNetOrderErrorMessage.encode_length]
    omega
  | thrlNetOrderErrorMessage inner =>
    simp only [encode, ThrlNetOrderErrorMessage.encode_length]
    omega
  | twolOrderCxlConfirmationMessage inner =>
    simp only [encode, TwolOrderCxlConfirmationMessage.encode_length]
    omega
  | thrlOrderCxlConfirmationMessage inner =>
    simp only [encode, ThrlOrderCxlConfirmationMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (ServerMessagePayload × List UInt8) :=
  if tag = 2301 then (SignOnOutMessage.decode bytes).map fun (message, rest) => (.signOnOutMessage message, rest)
  else if tag = 2222 then (TradeConfirmationMessage.decode bytes).map fun (message, rest) => (.tradeConfirmationMessage message, rest)
  else if tag = 2287 then (TradeModifyConfirmMessage.decode bytes).map fun (message, rest) => (.tradeModifyConfirmMessage message, rest)
  else if tag = 2288 then (TradeModifyRejectMessage.decode bytes).map fun (message, rest) => (.tradeModifyRejectMessage message, rest)
  else if tag = 2282 then (TradeCancelConfirmMessage.decode bytes).map fun (message, rest) => (.tradeCancelConfirmMessage message, rest)
  else if tag = 2286 then (TradeCancelRejectMessage.decode bytes).map fun (message, rest) => (.tradeCancelRejectMessage message, rest)
  else if tag = 2090 then (NltTradeConfirmationMessage.decode bytes).map fun (message, rest) => (.nltTradeConfirmationMessage message, rest)
  else if tag = 5449 then (NltTrdModConfirmationMessage.decode bytes).map fun (message, rest) => (.nltTrdModConfirmationMessage message, rest)
  else if tag = 5450 then (NltTrdModRejectMessage.decode bytes).map fun (message, rest) => (.nltTrdModRejectMessage message, rest)
  else if tag = 5452 then (NltTrdCxlConfirmationMessage.decode bytes).map fun (message, rest) => (.nltTrdCxlConfirmationMessage message, rest)
  else if tag = 5453 then (NltTrdCxlRejectMessage.decode bytes).map fun (message, rest) => (.nltTrdCxlRejectMessage message, rest)
  else if tag = 4506 then (GiveupAppConfirmTmMessage.decode bytes).map fun (message, rest) => (.giveupAppConfirmTmMessage message, rest)
  else if tag = 4507 then (GiveupRejConfirmTmMessage.decode bytes).map fun (message, rest) => (.giveupRejConfirmTmMessage message, rest)
  else if tag = 2001 then (BoardLotOutMessage.decode bytes).map fun (message, rest) => (.boardLotOutMessage message, rest)
  else if tag = 2041 then (OrderModOutMessage.decode bytes).map fun (message, rest) => (.orderModOutMessage message, rest)
  else if tag = 2042 then (OrderModRejectMessage.decode bytes).map fun (message, rest) => (.orderModRejectMessage message, rest)
  else if tag = 2071 then (OrderCancelOutMessage.decode bytes).map fun (message, rest) => (.orderCancelOutMessage message, rest)
  else if tag = 2072 then (OrderCancelRejectMessage.decode bytes).map fun (message, rest) => (.orderCancelRejectMessage message, rest)
  else if tag = 2073 then (OrderConfirmationMessage.decode bytes).map fun (message, rest) => (.orderConfirmationMessage message, rest)
  else if tag = 2074 then (OrderModConfirmationMessage.decode bytes).map fun (message, rest) => (.orderModConfirmationMessage message, rest)
  else if tag = 2075 then (OrderCancelConfirmationMessage.decode bytes).map fun (message, rest) => (.orderCancelConfirmationMessage message, rest)
  else if tag = 2170 then (FreezeToControlMessage.decode bytes).map fun (message, rest) => (.freezeToControlMessage message, rest)
  else if tag = 2231 then (OrderErrorMessage.decode bytes).map fun (message, rest) => (.orderErrorMessage message, rest)
  else if tag = 9002 then (BatchOrderCancelMessage.decode bytes).map fun (message, rest) => (.batchOrderCancelMessage message, rest)
  else if tag = 27100 then (NetOrderErrorMessage.decode bytes).map fun (message, rest) => (.netOrderErrorMessage message, rest)
  else if tag = 2083 then (NltConfirmationMessage.decode bytes).map fun (message, rest) => (.nltConfirmationMessage message, rest)
  else if tag = 2085 then (NltModConfirmationMessage.decode bytes).map fun (message, rest) => (.nltModConfirmationMessage message, rest)
  else if tag = 2087 then (NltCxlConfirmationMessage.decode bytes).map fun (message, rest) => (.nltCxlConfirmationMessage message, rest)
  else if tag = 2088 then (NltModRejectMessage.decode bytes).map fun (message, rest) => (.nltModRejectMessage message, rest)
  else if tag = 2089 then (NltCxlRejectMessage.decode bytes).map fun (message, rest) => (.nltCxlRejectMessage message, rest)
  else if tag = 2124 then (SpreadOrderConfirmationMessage.decode bytes).map fun (message, rest) => (.spreadOrderConfirmationMessage message, rest)
  else if tag = 2154 then (SpOrderErrorMessage.decode bytes).map fun (message, rest) => (.spOrderErrorMessage message, rest)
  else if tag = 27102 then (SpNetOrderErrorMessage.decode bytes).map fun (message, rest) => (.spNetOrderErrorMessage message, rest)
  else if tag = 2130 then (SpreadCxlConfirmationMessage.decode bytes).map fun (message, rest) => (.spreadCxlConfirmationMessage message, rest)
  else if tag = 2136 then (SpreadModConfirmationMessage.decode bytes).map fun (message, rest) => (.spreadModConfirmationMessage message, rest)
  else if tag = 2133 then (SpreadModRejectMessage.decode bytes).map fun (message, rest) => (.spreadModRejectMessage message, rest)
  else if tag = 2127 then (SpreadCxlRejectMessage.decode bytes).map fun (message, rest) => (.spreadCxlRejectMessage message, rest)
  else if tag = 9004 then (BatchSpreadOrderCancelMessage.decode bytes).map fun (message, rest) => (.batchSpreadOrderCancelMessage message, rest)
  else if tag = 2125 then (TwolOrderConfirmationMessage.decode bytes).map fun (message, rest) => (.twolOrderConfirmationMessage message, rest)
  else if tag = 2126 then (ThrlOrderConfirmationMessage.decode bytes).map fun (message, rest) => (.thrlOrderConfirmationMessage message, rest)
  else if tag = 2155 then (TwolOrderErrorMessage.decode bytes).map fun (message, rest) => (.twolOrderErrorMessage message, rest)
  else if tag = 2156 then (ThrlOrderErrorMessage.decode bytes).map fun (message, rest) => (.thrlOrderErrorMessage message, rest)
  else if tag = 27103 then (TwolNetOrderErrorMessage.decode bytes).map fun (message, rest) => (.twolNetOrderErrorMessage message, rest)
  else if tag = 27104 then (ThrlNetOrderErrorMessage.decode bytes).map fun (message, rest) => (.thrlNetOrderErrorMessage message, rest)
  else if tag = 2131 then (TwolOrderCxlConfirmationMessage.decode bytes).map fun (message, rest) => (.twolOrderCxlConfirmationMessage message, rest)
  else if tag = 2132 then (ThrlOrderCxlConfirmationMessage.decode bytes).map fun (message, rest) => (.thrlOrderCxlConfirmationMessage message, rest)
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
  | tradeModifyConfirmMessage inner =>
    simp only [ServerMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, TradeModifyConfirmMessage.encode_length]
    omega
  | tradeModifyRejectMessage inner =>
    simp only [ServerMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, TradeModifyRejectMessage.encode_length]
    omega
  | tradeCancelConfirmMessage inner =>
    simp only [ServerMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, TradeCancelConfirmMessage.encode_length]
    omega
  | tradeCancelRejectMessage inner =>
    simp only [ServerMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, TradeCancelRejectMessage.encode_length]
    omega
  | nltTradeConfirmationMessage inner =>
    simp only [ServerMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, NltTradeConfirmationMessage.encode_length]
    omega
  | nltTrdModConfirmationMessage inner =>
    simp only [ServerMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, NltTrdModConfirmationMessage.encode_length]
    omega
  | nltTrdModRejectMessage inner =>
    simp only [ServerMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, NltTrdModRejectMessage.encode_length]
    omega
  | nltTrdCxlConfirmationMessage inner =>
    simp only [ServerMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, NltTrdCxlConfirmationMessage.encode_length]
    omega
  | nltTrdCxlRejectMessage inner =>
    simp only [ServerMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, NltTrdCxlRejectMessage.encode_length]
    omega
  | giveupAppConfirmTmMessage inner =>
    simp only [ServerMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, GiveupAppConfirmTmMessage.encode_length]
    omega
  | giveupRejConfirmTmMessage inner =>
    simp only [ServerMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, GiveupRejConfirmTmMessage.encode_length]
    omega
  | boardLotOutMessage inner =>
    simp only [ServerMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, BoardLotOutMessage.encode_length]
    omega
  | orderModOutMessage inner =>
    simp only [ServerMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OrderModOutMessage.encode_length]
    omega
  | orderModRejectMessage inner =>
    simp only [ServerMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OrderModRejectMessage.encode_length]
    omega
  | orderCancelOutMessage inner =>
    simp only [ServerMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OrderCancelOutMessage.encode_length]
    omega
  | orderCancelRejectMessage inner =>
    simp only [ServerMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OrderCancelRejectMessage.encode_length]
    omega
  | orderConfirmationMessage inner =>
    simp only [ServerMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OrderConfirmationMessage.encode_length]
    omega
  | orderModConfirmationMessage inner =>
    simp only [ServerMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OrderModConfirmationMessage.encode_length]
    omega
  | orderCancelConfirmationMessage inner =>
    simp only [ServerMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OrderCancelConfirmationMessage.encode_length]
    omega
  | freezeToControlMessage inner =>
    simp only [ServerMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FreezeToControlMessage.encode_length]
    omega
  | orderErrorMessage inner =>
    simp only [ServerMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OrderErrorMessage.encode_length]
    omega
  | batchOrderCancelMessage inner =>
    simp only [ServerMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, BatchOrderCancelMessage.encode_length]
    omega
  | netOrderErrorMessage inner =>
    simp only [ServerMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, NetOrderErrorMessage.encode_length]
    omega
  | nltConfirmationMessage inner =>
    simp only [ServerMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, NltConfirmationMessage.encode_length]
    omega
  | nltModConfirmationMessage inner =>
    simp only [ServerMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, NltModConfirmationMessage.encode_length]
    omega
  | nltCxlConfirmationMessage inner =>
    simp only [ServerMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, NltCxlConfirmationMessage.encode_length]
    omega
  | nltModRejectMessage inner =>
    simp only [ServerMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, NltModRejectMessage.encode_length]
    omega
  | nltCxlRejectMessage inner =>
    simp only [ServerMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, NltCxlRejectMessage.encode_length]
    omega
  | spreadOrderConfirmationMessage inner =>
    simp only [ServerMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, SpreadOrderConfirmationMessage.encode_length]
    omega
  | spOrderErrorMessage inner =>
    simp only [ServerMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, SpOrderErrorMessage.encode_length]
    omega
  | spNetOrderErrorMessage inner =>
    simp only [ServerMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, SpNetOrderErrorMessage.encode_length]
    omega
  | spreadCxlConfirmationMessage inner =>
    simp only [ServerMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, SpreadCxlConfirmationMessage.encode_length]
    omega
  | spreadModConfirmationMessage inner =>
    simp only [ServerMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, SpreadModConfirmationMessage.encode_length]
    omega
  | spreadModRejectMessage inner =>
    simp only [ServerMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, SpreadModRejectMessage.encode_length]
    omega
  | spreadCxlRejectMessage inner =>
    simp only [ServerMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, SpreadCxlRejectMessage.encode_length]
    omega
  | batchSpreadOrderCancelMessage inner =>
    simp only [ServerMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, BatchSpreadOrderCancelMessage.encode_length]
    omega
  | twolOrderConfirmationMessage inner =>
    simp only [ServerMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, TwolOrderConfirmationMessage.encode_length]
    omega
  | thrlOrderConfirmationMessage inner =>
    simp only [ServerMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, ThrlOrderConfirmationMessage.encode_length]
    omega
  | twolOrderErrorMessage inner =>
    simp only [ServerMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, TwolOrderErrorMessage.encode_length]
    omega
  | thrlOrderErrorMessage inner =>
    simp only [ServerMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, ThrlOrderErrorMessage.encode_length]
    omega
  | twolNetOrderErrorMessage inner =>
    simp only [ServerMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, TwolNetOrderErrorMessage.encode_length]
    omega
  | thrlNetOrderErrorMessage inner =>
    simp only [ServerMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, ThrlNetOrderErrorMessage.encode_length]
    omega
  | twolOrderCxlConfirmationMessage inner =>
    simp only [ServerMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, TwolOrderCxlConfirmationMessage.encode_length]
    omega
  | thrlOrderCxlConfirmationMessage inner =>
    simp only [ServerMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, ThrlOrderCxlConfirmationMessage.encode_length]
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

end Omi.NseNseixDropcopyNnfdirectV16Server
