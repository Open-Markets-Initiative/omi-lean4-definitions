import Wire

/-!
# National Stock Exchange of India Ltd Order Entry v1.12

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.

Note: St Order Flags is a bit field set, proven as its 2 byte integer rather than bit by bit

Note: Additional Order Flags is a bit field set, proven as its 1 byte integer rather than bit by bit

Note: Order Modify Cancel Trimmed Message is selected by more than one code: each is a constructor
of its own over the one record, so the code read is the code written back

Note: Order Response Trimmed Message is selected by more than one code: each is a constructor of its
own over the one record, so the code read is the code written back

License: MIT No Attribution
-/

namespace Omi.NseNseixOrderentryNnftrimmedV112

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

/-- Modified Cancelled By: one byte code -/
def ModifiedCancelledBy.codes : List UInt8 :=
  [0x54, 0x42, 0x4D, 0x43]

inductive ModifiedCancelledBy where
  | trader -- Trader
  | branchManager -- Branch Manager
  | corporateManager -- Corporate Manager
  | exchange -- Exchange
  | unlisted (byte : { byte : UInt8 // byte ∉ ModifiedCancelledBy.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ModifiedCancelledBy

def toByte : ModifiedCancelledBy → UInt8
  | .trader => 0x54
  | .branchManager => 0x42
  | .corporateManager => 0x4D
  | .exchange => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ModifiedCancelledBy :=
  if byte = 0x54 then .trader
  else if byte = 0x42 then .branchManager
  else if byte = 0x4D then .corporateManager
  else .exchange

def ofByte (byte : UInt8) : ModifiedCancelledBy :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ModifiedCancelledBy) : ofByte value.toByte = value := by
  cases value with
  | trader => decide
  | branchManager => decide
  | corporateManager => decide
  | exchange => decide
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

/-- Contract Desc Tr: 26 bytes -/
structure ContractDescTr where
  instrumentName : Alpha 6
  symbol : Alpha 10
  expiryDate : BitVec 32
  strikePrice : BitVec 32
  optionType : Alpha 2
  deriving DecidableEq, Repr

namespace ContractDescTr

def encode (message : ContractDescTr) : List UInt8 :=
  Alpha.encode message.instrumentName
    ++ (Alpha.encode message.symbol
    ++ (encodeUInt 4 message.expiryDate
    ++ (encodeUInt 4 message.strikePrice
    ++ (Alpha.encode message.optionType))))

def decode (bytes : List UInt8) : Option (ContractDescTr × List UInt8) := do
  let (instrumentName, bytes) ← Alpha.decode 6 bytes
  let (symbol, bytes) ← Alpha.decode 10 bytes
  let (expiryDate, bytes) ← decodeUInt 4 bytes
  let (strikePrice, bytes) ← decodeUInt 4 bytes
  let (optionType, bytes) ← Alpha.decode 2 bytes
  pure ({ instrumentName, symbol, expiryDate, strikePrice, optionType }, bytes)

@[simp] theorem encode_length (message : ContractDescTr) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ContractDescTr) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ContractDescTr) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end ContractDescTr

/-- Board Lot In Trimmed Message: 156 bytes -/
structure BoardLotInTrimmedMessage where
  userId : BitVec 32
  reasonCode : BitVec 16
  tokenNo : BitVec 32
  contractDescTr : ContractDescTr
  accountNumber : Alpha 10
  bookType : BitVec 16
  buySellIndicator : BitVec 16
  disclosedVolume : BitVec 32
  volume : BitVec 32
  price : BitVec 32
  goodTillDate : BitVec 32
  stOrderFlags : BitVec 16
  branchId : BitVec 16
  traderId : BitVec 32
  brokerId : Alpha 5
  openClose : OpenClose
  settlor : Alpha 12
  proClientIndicator : BitVec 16
  additionalOrderFlags : BitVec 8
  reserved1 : Alpha 1
  filler4 : Alpha 4
  nnfField : Alpha 8
  echoBack : Alpha 16
  lastActivityReference : BitVec 64
  reserved24 : Alpha 24
  deriving DecidableEq, Repr

namespace BoardLotInTrimmedMessage

def encode (message : BoardLotInTrimmedMessage) : List UInt8 :=
  encodeUInt 4 message.userId
    ++ (encodeUInt 2 message.reasonCode
    ++ (encodeUInt 4 message.tokenNo
    ++ (ContractDescTr.encode message.contractDescTr
    ++ (Alpha.encode message.accountNumber
    ++ (encodeUInt 2 message.bookType
    ++ (encodeUInt 2 message.buySellIndicator
    ++ (encodeUInt 4 message.disclosedVolume
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.goodTillDate
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId
    ++ (encodeUInt 4 message.traderId
    ++ (Alpha.encode message.brokerId
    ++ (OpenClose.encode message.openClose
    ++ (Alpha.encode message.settlor
    ++ (encodeUInt 2 message.proClientIndicator
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.reserved1
    ++ (Alpha.encode message.filler4
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.echoBack
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved24))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (BoardLotInTrimmedMessage × List UInt8) := do
  let (userId, bytes) ← decodeUInt 4 bytes
  let (reasonCode, bytes) ← decodeUInt 2 bytes
  let (tokenNo, bytes) ← decodeUInt 4 bytes
  let (contractDescTr, bytes) ← ContractDescTr.decode bytes
  let (accountNumber, bytes) ← Alpha.decode 10 bytes
  let (bookType, bytes) ← decodeUInt 2 bytes
  let (buySellIndicator, bytes) ← decodeUInt 2 bytes
  let (disclosedVolume, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (goodTillDate, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId, bytes) ← decodeUInt 2 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (openClose, bytes) ← OpenClose.decode bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  let (proClientIndicator, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (filler4, bytes) ← Alpha.decode 4 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (echoBack, bytes) ← Alpha.decode 16 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved24, bytes) ← Alpha.decode 24 bytes
  pure ({ userId, reasonCode, tokenNo, contractDescTr, accountNumber, bookType, buySellIndicator, disclosedVolume, volume, price, goodTillDate, stOrderFlags, branchId, traderId, brokerId, openClose, settlor, proClientIndicator, additionalOrderFlags, reserved1, filler4, nnfField, echoBack, lastActivityReference, reserved24 }, bytes)

@[simp] theorem encode_length (message : BoardLotInTrimmedMessage) : (encode message).length = 156 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, ContractDescTr.encode_length, Alpha.encode_length, OpenClose.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : BoardLotInTrimmedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : BoardLotInTrimmedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDescTr.decode_encode, some_bind]
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
  rw [List.append_assoc, OpenClose.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BoardLotInTrimmedMessage

/-- Order Modify Cancel Trimmed Message: 184 bytes -/
structure OrderModifyCancelTrimmedMessage where
  userId : BitVec 32
  modifiedCancelledBy : ModifiedCancelledBy
  filler1 : Alpha 1
  tokenNo : BitVec 32
  contractDescTr : ContractDescTr
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
  goodTillDate : BitVec 32
  entryDateTime : BitVec 32
  lastModified : BitVec 32
  stOrderFlags : BitVec 16
  branchId : BitVec 16
  traderId : BitVec 32
  brokerId : Alpha 5
  openClose : OpenClose
  settlor : Alpha 12
  proClientIndicator : BitVec 16
  additionalOrderFlags : BitVec 8
  secondFiller1 : Alpha 1
  filler4 : Alpha 4
  nnfField : Alpha 8
  echoBack : Alpha 16
  lastActivityReference : BitVec 64
  reserved24 : Alpha 24
  deriving DecidableEq, Repr

namespace OrderModifyCancelTrimmedMessage

def encode (message : OrderModifyCancelTrimmedMessage) : List UInt8 :=
  encodeUInt 4 message.userId
    ++ (ModifiedCancelledBy.encode message.modifiedCancelledBy
    ++ (Alpha.encode message.filler1
    ++ (encodeUInt 4 message.tokenNo
    ++ (ContractDescTr.encode message.contractDescTr
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
    ++ (encodeUInt 4 message.goodTillDate
    ++ (encodeUInt 4 message.entryDateTime
    ++ (encodeUInt 4 message.lastModified
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId
    ++ (encodeUInt 4 message.traderId
    ++ (Alpha.encode message.brokerId
    ++ (OpenClose.encode message.openClose
    ++ (Alpha.encode message.settlor
    ++ (encodeUInt 2 message.proClientIndicator
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.secondFiller1
    ++ (Alpha.encode message.filler4
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.echoBack
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved24)))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderModifyCancelTrimmedMessage × List UInt8) := do
  let (userId, bytes) ← decodeUInt 4 bytes
  let (modifiedCancelledBy, bytes) ← ModifiedCancelledBy.decode bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (tokenNo, bytes) ← decodeUInt 4 bytes
  let (contractDescTr, bytes) ← ContractDescTr.decode bytes
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
  let (goodTillDate, bytes) ← decodeUInt 4 bytes
  let (entryDateTime, bytes) ← decodeUInt 4 bytes
  let (lastModified, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId, bytes) ← decodeUInt 2 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (openClose, bytes) ← OpenClose.decode bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  let (proClientIndicator, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (secondFiller1, bytes) ← Alpha.decode 1 bytes
  let (filler4, bytes) ← Alpha.decode 4 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (echoBack, bytes) ← Alpha.decode 16 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved24, bytes) ← Alpha.decode 24 bytes
  pure ({ userId, modifiedCancelledBy, filler1, tokenNo, contractDescTr, orderNumber, accountNumber, bookType, buySellIndicator, disclosedVolume, disclosedVolumeRemaining, totalVolumeRemaining, volume, volumeFilledToday, price, goodTillDate, entryDateTime, lastModified, stOrderFlags, branchId, traderId, brokerId, openClose, settlor, proClientIndicator, additionalOrderFlags, secondFiller1, filler4, nnfField, echoBack, lastActivityReference, reserved24 }, bytes)

@[simp] theorem encode_length (message : OrderModifyCancelTrimmedMessage) : (encode message).length = 184 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, ModifiedCancelledBy.encode_length, Alpha.encode_length, ContractDescTr.encode_length, OpenClose.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : OrderModifyCancelTrimmedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OrderModifyCancelTrimmedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ModifiedCancelledBy.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDescTr.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpenClose.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderModifyCancelTrimmedMessage

/-- Order Response Trimmed Message: 238 bytes -/
structure OrderResponseTrimmedMessage where
  logTime : BitVec 32
  userId : BitVec 32
  errorCode : BitVec 16
  timeStamp1 : Alpha 8
  timestamp2Char : Alpha 1
  modifiedCancelledBy : ModifiedCancelledBy
  reasonCode : BitVec 16
  tokenNo : BitVec 32
  contractDescTr : ContractDescTr
  closeoutFlag : Alpha 1
  reserved1 : Alpha 1
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
  goodTillDate : BitVec 32
  entryDateTime : BitVec 32
  lastModified : BitVec 32
  stOrderFlags : BitVec 16
  branchId : BitVec 16
  traderId : BitVec 32
  brokerId : Alpha 5
  openClose : OpenClose
  settlor : Alpha 12
  proClientIndicator : BitVec 16
  additionalOrderFlags : BitVec 8
  secondReserved1 : Alpha 1
  filler4 : Alpha 4
  nnfField : Alpha 8
  reserved8 : Alpha 8
  echoBack : Alpha 16
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  deriving DecidableEq, Repr

namespace OrderResponseTrimmedMessage

def encode (message : OrderResponseTrimmedMessage) : List UInt8 :=
  encodeUInt 4 message.logTime
    ++ (encodeUInt 4 message.userId
    ++ (encodeUInt 2 message.errorCode
    ++ (Alpha.encode message.timeStamp1
    ++ (Alpha.encode message.timestamp2Char
    ++ (ModifiedCancelledBy.encode message.modifiedCancelledBy
    ++ (encodeUInt 2 message.reasonCode
    ++ (encodeUInt 4 message.tokenNo
    ++ (ContractDescTr.encode message.contractDescTr
    ++ (Alpha.encode message.closeoutFlag
    ++ (Alpha.encode message.reserved1
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
    ++ (encodeUInt 4 message.goodTillDate
    ++ (encodeUInt 4 message.entryDateTime
    ++ (encodeUInt 4 message.lastModified
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId
    ++ (encodeUInt 4 message.traderId
    ++ (Alpha.encode message.brokerId
    ++ (OpenClose.encode message.openClose
    ++ (Alpha.encode message.settlor
    ++ (encodeUInt 2 message.proClientIndicator
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.secondReserved1
    ++ (Alpha.encode message.filler4
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.reserved8
    ++ (Alpha.encode message.echoBack
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderResponseTrimmedMessage × List UInt8) := do
  let (logTime, bytes) ← decodeUInt 4 bytes
  let (userId, bytes) ← decodeUInt 4 bytes
  let (errorCode, bytes) ← decodeUInt 2 bytes
  let (timeStamp1, bytes) ← Alpha.decode 8 bytes
  let (timestamp2Char, bytes) ← Alpha.decode 1 bytes
  let (modifiedCancelledBy, bytes) ← ModifiedCancelledBy.decode bytes
  let (reasonCode, bytes) ← decodeUInt 2 bytes
  let (tokenNo, bytes) ← decodeUInt 4 bytes
  let (contractDescTr, bytes) ← ContractDescTr.decode bytes
  let (closeoutFlag, bytes) ← Alpha.decode 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
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
  let (goodTillDate, bytes) ← decodeUInt 4 bytes
  let (entryDateTime, bytes) ← decodeUInt 4 bytes
  let (lastModified, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId, bytes) ← decodeUInt 2 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (openClose, bytes) ← OpenClose.decode bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  let (proClientIndicator, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  let (filler4, bytes) ← Alpha.decode 4 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  let (echoBack, bytes) ← Alpha.decode 16 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  pure ({ logTime, userId, errorCode, timeStamp1, timestamp2Char, modifiedCancelledBy, reasonCode, tokenNo, contractDescTr, closeoutFlag, reserved1, orderNumber, accountNumber, bookType, buySellIndicator, disclosedVolume, disclosedVolumeRemaining, totalVolumeRemaining, volume, volumeFilledToday, price, goodTillDate, entryDateTime, lastModified, stOrderFlags, branchId, traderId, brokerId, openClose, settlor, proClientIndicator, additionalOrderFlags, secondReserved1, filler4, nnfField, reserved8, echoBack, lastActivityReference, reserved52 }, bytes)

@[simp] theorem encode_length (message : OrderResponseTrimmedMessage) : (encode message).length = 238 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, ModifiedCancelledBy.encode_length, ContractDescTr.encode_length, OpenClose.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : OrderResponseTrimmedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OrderResponseTrimmedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, ModifiedCancelledBy.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDescTr.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpenClose.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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

end OrderResponseTrimmedMessage

/-- Trade Confirmation Trimmed Message: 228 bytes -/
structure TradeConfirmationTrimmedMessage where
  logTime : BitVec 32
  traderId : BitVec 32
  timeStamp : Alpha 8
  timeStamp1 : Alpha 8
  timestamp2Double : Alpha 8
  responseOrderNumber : Alpha 8
  brokerId : Alpha 5
  reserved1 : Alpha 1
  accountNumber : Alpha 10
  buySellIndicator : BitVec 16
  originalVolume : BitVec 32
  disclosedVolume : BitVec 32
  remainingVolume : BitVec 32
  disclosedVolumeRemaining : BitVec 32
  price : BitVec 32
  stOrderFlags : BitVec 16
  goodTillDate : BitVec 32
  fillNumber : BitVec 32
  fillQuantity : BitVec 32
  fillPrice : BitVec 32
  volumeFilledToday : BitVec 32
  activityType : Alpha 2
  activityTime : BitVec 32
  token : BitVec 32
  contractDescTr : ContractDescTr
  openClose : OpenClose
  tradeBookType : Alpha 1
  participant : Alpha 12
  additionalOrderFlags : BitVec 8
  secondReserved1 : Alpha 1
  echoBack : Alpha 16
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  deriving DecidableEq, Repr

namespace TradeConfirmationTrimmedMessage

def encode (message : TradeConfirmationTrimmedMessage) : List UInt8 :=
  encodeUInt 4 message.logTime
    ++ (encodeUInt 4 message.traderId
    ++ (Alpha.encode message.timeStamp
    ++ (Alpha.encode message.timeStamp1
    ++ (Alpha.encode message.timestamp2Double
    ++ (Alpha.encode message.responseOrderNumber
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.reserved1
    ++ (Alpha.encode message.accountNumber
    ++ (encodeUInt 2 message.buySellIndicator
    ++ (encodeUInt 4 message.originalVolume
    ++ (encodeUInt 4 message.disclosedVolume
    ++ (encodeUInt 4 message.remainingVolume
    ++ (encodeUInt 4 message.disclosedVolumeRemaining
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 4 message.goodTillDate
    ++ (encodeUInt 4 message.fillNumber
    ++ (encodeUInt 4 message.fillQuantity
    ++ (encodeUInt 4 message.fillPrice
    ++ (encodeUInt 4 message.volumeFilledToday
    ++ (Alpha.encode message.activityType
    ++ (encodeUInt 4 message.activityTime
    ++ (encodeUInt 4 message.token
    ++ (ContractDescTr.encode message.contractDescTr
    ++ (OpenClose.encode message.openClose
    ++ (Alpha.encode message.tradeBookType
    ++ (Alpha.encode message.participant
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.secondReserved1
    ++ (Alpha.encode message.echoBack
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TradeConfirmationTrimmedMessage × List UInt8) := do
  let (logTime, bytes) ← decodeUInt 4 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (timeStamp, bytes) ← Alpha.decode 8 bytes
  let (timeStamp1, bytes) ← Alpha.decode 8 bytes
  let (timestamp2Double, bytes) ← Alpha.decode 8 bytes
  let (responseOrderNumber, bytes) ← Alpha.decode 8 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (accountNumber, bytes) ← Alpha.decode 10 bytes
  let (buySellIndicator, bytes) ← decodeUInt 2 bytes
  let (originalVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolume, bytes) ← decodeUInt 4 bytes
  let (remainingVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolumeRemaining, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (goodTillDate, bytes) ← decodeUInt 4 bytes
  let (fillNumber, bytes) ← decodeUInt 4 bytes
  let (fillQuantity, bytes) ← decodeUInt 4 bytes
  let (fillPrice, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday, bytes) ← decodeUInt 4 bytes
  let (activityType, bytes) ← Alpha.decode 2 bytes
  let (activityTime, bytes) ← decodeUInt 4 bytes
  let (token, bytes) ← decodeUInt 4 bytes
  let (contractDescTr, bytes) ← ContractDescTr.decode bytes
  let (openClose, bytes) ← OpenClose.decode bytes
  let (tradeBookType, bytes) ← Alpha.decode 1 bytes
  let (participant, bytes) ← Alpha.decode 12 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  let (echoBack, bytes) ← Alpha.decode 16 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  pure ({ logTime, traderId, timeStamp, timeStamp1, timestamp2Double, responseOrderNumber, brokerId, reserved1, accountNumber, buySellIndicator, originalVolume, disclosedVolume, remainingVolume, disclosedVolumeRemaining, price, stOrderFlags, goodTillDate, fillNumber, fillQuantity, fillPrice, volumeFilledToday, activityType, activityTime, token, contractDescTr, openClose, tradeBookType, participant, additionalOrderFlags, secondReserved1, echoBack, lastActivityReference, reserved52 }, bytes)

@[simp] theorem encode_length (message : TradeConfirmationTrimmedMessage) : (encode message).length = 228 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, ContractDescTr.encode_length, OpenClose.encode_length, encodeUIntLE_length]

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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDescTr.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpenClose.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeConfirmationTrimmedMessage

/-- Any Message Payload, selected by Transaction Code -/
inductive MessagePayload where
  | boardLotInTrimmedMessage (message : BoardLotInTrimmedMessage) -- 20000
  | orderModifyCancelTrimmedMessage (message : OrderModifyCancelTrimmedMessage) -- 20040
  | orderModifyCancelTrimmedMessage20060 (message : OrderModifyCancelTrimmedMessage) -- 20060
  | orderModifyCancelTrimmedMessage20070 (message : OrderModifyCancelTrimmedMessage) -- 20070
  | orderResponseTrimmedMessage (message : OrderResponseTrimmedMessage) -- 20012
  | orderResponseTrimmedMessage20042 (message : OrderResponseTrimmedMessage) -- 20042
  | orderResponseTrimmedMessage20072 (message : OrderResponseTrimmedMessage) -- 20072
  | orderResponseTrimmedMessage20073 (message : OrderResponseTrimmedMessage) -- 20073
  | orderResponseTrimmedMessage20074 (message : OrderResponseTrimmedMessage) -- 20074
  | orderResponseTrimmedMessage20075 (message : OrderResponseTrimmedMessage) -- 20075
  | orderResponseTrimmedMessage20231 (message : OrderResponseTrimmedMessage) -- 20231
  | tradeConfirmationTrimmedMessage (message : TradeConfirmationTrimmedMessage) -- 20222
  deriving DecidableEq, Repr

namespace MessagePayload

/-- The Transaction Code each message is sent under -/
def tag : MessagePayload → BitVec 16
  | .boardLotInTrimmedMessage _ => 20000
  | .orderModifyCancelTrimmedMessage _ => 20040
  | .orderModifyCancelTrimmedMessage20060 _ => 20060
  | .orderModifyCancelTrimmedMessage20070 _ => 20070
  | .orderResponseTrimmedMessage _ => 20012
  | .orderResponseTrimmedMessage20042 _ => 20042
  | .orderResponseTrimmedMessage20072 _ => 20072
  | .orderResponseTrimmedMessage20073 _ => 20073
  | .orderResponseTrimmedMessage20074 _ => 20074
  | .orderResponseTrimmedMessage20075 _ => 20075
  | .orderResponseTrimmedMessage20231 _ => 20231
  | .tradeConfirmationTrimmedMessage _ => 20222

def encode : MessagePayload → List UInt8
  | .boardLotInTrimmedMessage message => BoardLotInTrimmedMessage.encode message
  | .orderModifyCancelTrimmedMessage message => OrderModifyCancelTrimmedMessage.encode message
  | .orderModifyCancelTrimmedMessage20060 message => OrderModifyCancelTrimmedMessage.encode message
  | .orderModifyCancelTrimmedMessage20070 message => OrderModifyCancelTrimmedMessage.encode message
  | .orderResponseTrimmedMessage message => OrderResponseTrimmedMessage.encode message
  | .orderResponseTrimmedMessage20042 message => OrderResponseTrimmedMessage.encode message
  | .orderResponseTrimmedMessage20072 message => OrderResponseTrimmedMessage.encode message
  | .orderResponseTrimmedMessage20073 message => OrderResponseTrimmedMessage.encode message
  | .orderResponseTrimmedMessage20074 message => OrderResponseTrimmedMessage.encode message
  | .orderResponseTrimmedMessage20075 message => OrderResponseTrimmedMessage.encode message
  | .orderResponseTrimmedMessage20231 message => OrderResponseTrimmedMessage.encode message
  | .tradeConfirmationTrimmedMessage message => TradeConfirmationTrimmedMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : MessagePayload) : (encode message).length ≤ 238 := by
  cases message with
  | boardLotInTrimmedMessage inner =>
    simp only [encode, BoardLotInTrimmedMessage.encode_length]
    omega
  | orderModifyCancelTrimmedMessage inner =>
    simp only [encode, OrderModifyCancelTrimmedMessage.encode_length]
    omega
  | orderModifyCancelTrimmedMessage20060 inner =>
    simp only [encode, OrderModifyCancelTrimmedMessage.encode_length]
    omega
  | orderModifyCancelTrimmedMessage20070 inner =>
    simp only [encode, OrderModifyCancelTrimmedMessage.encode_length]
    omega
  | orderResponseTrimmedMessage inner =>
    simp only [encode, OrderResponseTrimmedMessage.encode_length]
    omega
  | orderResponseTrimmedMessage20042 inner =>
    simp only [encode, OrderResponseTrimmedMessage.encode_length]
    omega
  | orderResponseTrimmedMessage20072 inner =>
    simp only [encode, OrderResponseTrimmedMessage.encode_length]
    omega
  | orderResponseTrimmedMessage20073 inner =>
    simp only [encode, OrderResponseTrimmedMessage.encode_length]
    omega
  | orderResponseTrimmedMessage20074 inner =>
    simp only [encode, OrderResponseTrimmedMessage.encode_length]
    omega
  | orderResponseTrimmedMessage20075 inner =>
    simp only [encode, OrderResponseTrimmedMessage.encode_length]
    omega
  | orderResponseTrimmedMessage20231 inner =>
    simp only [encode, OrderResponseTrimmedMessage.encode_length]
    omega
  | tradeConfirmationTrimmedMessage inner =>
    simp only [encode, TradeConfirmationTrimmedMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (MessagePayload × List UInt8) :=
  if tag = 20000 then (BoardLotInTrimmedMessage.decode bytes).map fun (message, rest) => (.boardLotInTrimmedMessage message, rest)
  else if tag = 20040 then (OrderModifyCancelTrimmedMessage.decode bytes).map fun (message, rest) => (.orderModifyCancelTrimmedMessage message, rest)
  else if tag = 20060 then (OrderModifyCancelTrimmedMessage.decode bytes).map fun (message, rest) => (.orderModifyCancelTrimmedMessage20060 message, rest)
  else if tag = 20070 then (OrderModifyCancelTrimmedMessage.decode bytes).map fun (message, rest) => (.orderModifyCancelTrimmedMessage20070 message, rest)
  else if tag = 20012 then (OrderResponseTrimmedMessage.decode bytes).map fun (message, rest) => (.orderResponseTrimmedMessage message, rest)
  else if tag = 20042 then (OrderResponseTrimmedMessage.decode bytes).map fun (message, rest) => (.orderResponseTrimmedMessage20042 message, rest)
  else if tag = 20072 then (OrderResponseTrimmedMessage.decode bytes).map fun (message, rest) => (.orderResponseTrimmedMessage20072 message, rest)
  else if tag = 20073 then (OrderResponseTrimmedMessage.decode bytes).map fun (message, rest) => (.orderResponseTrimmedMessage20073 message, rest)
  else if tag = 20074 then (OrderResponseTrimmedMessage.decode bytes).map fun (message, rest) => (.orderResponseTrimmedMessage20074 message, rest)
  else if tag = 20075 then (OrderResponseTrimmedMessage.decode bytes).map fun (message, rest) => (.orderResponseTrimmedMessage20075 message, rest)
  else if tag = 20231 then (OrderResponseTrimmedMessage.decode bytes).map fun (message, rest) => (.orderResponseTrimmedMessage20231 message, rest)
  else if tag = 20222 then (TradeConfirmationTrimmedMessage.decode bytes).map fun (message, rest) => (.tradeConfirmationTrimmedMessage message, rest)
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
theorem encode_length_le (message : Message) : (encode message).length ≤ 240 := by
  unfold encode
  cases message.messagePayload with
  | boardLotInTrimmedMessage inner =>
    simp only [MessagePayload.encode, List.length_append, encodeUInt_length, BoardLotInTrimmedMessage.encode_length]
    omega
  | orderModifyCancelTrimmedMessage inner =>
    simp only [MessagePayload.encode, List.length_append, encodeUInt_length, OrderModifyCancelTrimmedMessage.encode_length]
    omega
  | orderModifyCancelTrimmedMessage20060 inner =>
    simp only [MessagePayload.encode, List.length_append, encodeUInt_length, OrderModifyCancelTrimmedMessage.encode_length]
    omega
  | orderModifyCancelTrimmedMessage20070 inner =>
    simp only [MessagePayload.encode, List.length_append, encodeUInt_length, OrderModifyCancelTrimmedMessage.encode_length]
    omega
  | orderResponseTrimmedMessage inner =>
    simp only [MessagePayload.encode, List.length_append, encodeUInt_length, OrderResponseTrimmedMessage.encode_length]
    omega
  | orderResponseTrimmedMessage20042 inner =>
    simp only [MessagePayload.encode, List.length_append, encodeUInt_length, OrderResponseTrimmedMessage.encode_length]
    omega
  | orderResponseTrimmedMessage20072 inner =>
    simp only [MessagePayload.encode, List.length_append, encodeUInt_length, OrderResponseTrimmedMessage.encode_length]
    omega
  | orderResponseTrimmedMessage20073 inner =>
    simp only [MessagePayload.encode, List.length_append, encodeUInt_length, OrderResponseTrimmedMessage.encode_length]
    omega
  | orderResponseTrimmedMessage20074 inner =>
    simp only [MessagePayload.encode, List.length_append, encodeUInt_length, OrderResponseTrimmedMessage.encode_length]
    omega
  | orderResponseTrimmedMessage20075 inner =>
    simp only [MessagePayload.encode, List.length_append, encodeUInt_length, OrderResponseTrimmedMessage.encode_length]
    omega
  | orderResponseTrimmedMessage20231 inner =>
    simp only [MessagePayload.encode, List.length_append, encodeUInt_length, OrderResponseTrimmedMessage.encode_length]
    omega
  | tradeConfirmationTrimmedMessage inner =>
    simp only [MessagePayload.encode, List.length_append, encodeUInt_length, TradeConfirmationTrimmedMessage.encode_length]
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

end Omi.NseNseixOrderentryNnftrimmedV112
