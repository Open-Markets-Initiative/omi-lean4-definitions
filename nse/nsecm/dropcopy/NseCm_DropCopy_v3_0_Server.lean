import Wire

/-!
# National Stock Exchange of India Ltd Drop Copy v3.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NseNsecmDropcopyNnfdcV30Server

/-- Environment Type: one byte code -/
def EnvironmentType.codes : List UInt8 :=
  [0x31, 0x32, 0x33]

inductive EnvironmentType where
  | productionEnvironment -- Production Environment
  | prodParallelMockEnvironment -- Prod Parallel Mock Environment
  | testingEnvironment -- Testing Environment
  | unlisted (byte : { byte : UInt8 // byte ∉ EnvironmentType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EnvironmentType

def toByte : EnvironmentType → UInt8
  | .productionEnvironment => 0x31
  | .prodParallelMockEnvironment => 0x32
  | .testingEnvironment => 0x33
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EnvironmentType :=
  if byte = 0x31 then .productionEnvironment
  else if byte = 0x32 then .prodParallelMockEnvironment
  else .testingEnvironment

def ofByte (byte : UInt8) : EnvironmentType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EnvironmentType) : ofByte value.toByte = value := by
  cases value with
  | productionEnvironment => decide
  | prodParallelMockEnvironment => decide
  | testingEnvironment => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : EnvironmentType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (EnvironmentType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : EnvironmentType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : EnvironmentType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : EnvironmentType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end EnvironmentType

/-- Compression Indicator: one byte code -/
def CompressionIndicator.codes : List UInt8 :=
  [0x30, 0x31]

inductive CompressionIndicator where
  | noCompressionDone -- No Compression Done
  | dataIsCompressed -- Data Is Compressed
  | unlisted (byte : { byte : UInt8 // byte ∉ CompressionIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CompressionIndicator

def toByte : CompressionIndicator → UInt8
  | .noCompressionDone => 0x30
  | .dataIsCompressed => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CompressionIndicator :=
  if byte = 0x30 then .noCompressionDone
  else .dataIsCompressed

def ofByte (byte : UInt8) : CompressionIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CompressionIndicator) : ofByte value.toByte = value := by
  cases value with
  | noCompressionDone => decide
  | dataIsCompressed => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CompressionIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CompressionIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CompressionIndicator) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CompressionIndicator) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CompressionIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CompressionIndicator

/-- Participant Type: one byte code -/
def ParticipantType.codes : List UInt8 :=
  [0x49, 0x43, 0x53]

inductive ParticipantType where
  | initiator -- Initiator
  | competitorOrder -- Competitor Order
  | solicitorOrder -- Solicitor Order
  | unlisted (byte : { byte : UInt8 // byte ∉ ParticipantType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ParticipantType

def toByte : ParticipantType → UInt8
  | .initiator => 0x49
  | .competitorOrder => 0x43
  | .solicitorOrder => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ParticipantType :=
  if byte = 0x49 then .initiator
  else if byte = 0x43 then .competitorOrder
  else .solicitorOrder

def ofByte (byte : UInt8) : ParticipantType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ParticipantType) : ofByte value.toByte = value := by
  cases value with
  | initiator => decide
  | competitorOrder => decide
  | solicitorOrder => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ParticipantType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ParticipantType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ParticipantType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ParticipantType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ParticipantType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ParticipantType

/-- Settlement Type: one byte code -/
def SettlementType.codes : List UInt8 :=
  [0x30, 0x31, 0x32]

inductive SettlementType where
  | t0Settlement -- T 0 Settlement
  | t1Settlement -- T 1 Settlement
  | t2Settlement -- T 2 Settlement
  | unlisted (byte : { byte : UInt8 // byte ∉ SettlementType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SettlementType

def toByte : SettlementType → UInt8
  | .t0Settlement => 0x30
  | .t1Settlement => 0x31
  | .t2Settlement => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SettlementType :=
  if byte = 0x30 then .t0Settlement
  else if byte = 0x31 then .t1Settlement
  else .t2Settlement

def ofByte (byte : UInt8) : SettlementType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SettlementType) : ofByte value.toByte = value := by
  cases value with
  | t0Settlement => decide
  | t1Settlement => decide
  | t2Settlement => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SettlementType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SettlementType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SettlementType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SettlementType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SettlementType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SettlementType

/-- Ip Details Partition Wise: 26 bytes -/
structure IpDetailsPartitionWise where
  ipAddress : Alpha 16
  port : BitVec 32
  partitionId : Alpha 6
  deriving DecidableEq, Repr

namespace IpDetailsPartitionWise

def encode (message : IpDetailsPartitionWise) : List UInt8 :=
  Alpha.encode message.ipAddress
    ++ (encodeUInt 4 message.port
    ++ (Alpha.encode message.partitionId))

def decode (bytes : List UInt8) : Option (IpDetailsPartitionWise × List UInt8) := do
  let (ipAddress, bytes) ← Alpha.decode 16 bytes
  let (port, bytes) ← decodeUInt 4 bytes
  let (partitionId, bytes) ← Alpha.decode 6 bytes
  pure ({ ipAddress, port, partitionId }, bytes)

@[simp] theorem encode_length (message : IpDetailsPartitionWise) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : IpDetailsPartitionWise) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IpDetailsPartitionWise) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end IpDetailsPartitionWise

/-- Gr Response Message: 86 bytes -/
structure GrResponseMessage where
  messageIndicator : BitVec 16
  partitionCount : BitVec 16
  ipDetailsPartitionWise : IpDetailsPartitionWise
  sessionKey : Alpha 8
  cryptographicKey : Alpha 32
  cryptographicIv : Alpha 16
  deriving DecidableEq, Repr

namespace GrResponseMessage

def encode (message : GrResponseMessage) : List UInt8 :=
  encodeUInt 2 message.messageIndicator
    ++ (encodeUInt 2 message.partitionCount
    ++ (IpDetailsPartitionWise.encode message.ipDetailsPartitionWise
    ++ (Alpha.encode message.sessionKey
    ++ (Alpha.encode message.cryptographicKey
    ++ (Alpha.encode message.cryptographicIv)))))

def decode (bytes : List UInt8) : Option (GrResponseMessage × List UInt8) := do
  let (messageIndicator, bytes) ← decodeUInt 2 bytes
  let (partitionCount, bytes) ← decodeUInt 2 bytes
  let (ipDetailsPartitionWise, bytes) ← IpDetailsPartitionWise.decode bytes
  let (sessionKey, bytes) ← Alpha.decode 8 bytes
  let (cryptographicKey, bytes) ← Alpha.decode 32 bytes
  let (cryptographicIv, bytes) ← Alpha.decode 16 bytes
  pure ({ messageIndicator, partitionCount, ipDetailsPartitionWise, sessionKey, cryptographicKey, cryptographicIv }, bytes)

@[simp] theorem encode_length (message : GrResponseMessage) : (encode message).length = 86 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, IpDetailsPartitionWise.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : GrResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : GrResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, IpDetailsPartitionWise.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end GrResponseMessage

/-- Gr Secure User Registration Response Message: 0 bytes -/
structure GrSecureUserRegistrationResponseMessage where
  deriving DecidableEq, Repr

namespace GrSecureUserRegistrationResponseMessage

def encode (_ : GrSecureUserRegistrationResponseMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (GrSecureUserRegistrationResponseMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : GrSecureUserRegistrationResponseMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : GrSecureUserRegistrationResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end GrSecureUserRegistrationResponseMessage

/-- Dc Signon Out Message: 12 bytes -/
structure DcSignonOutMessage where
  userId : BitVec 32
  partitionId : Alpha 6
  concurrentLoginId : BitVec 16
  deriving DecidableEq, Repr

namespace DcSignonOutMessage

def encode (message : DcSignonOutMessage) : List UInt8 :=
  encodeUInt 4 message.userId
    ++ (Alpha.encode message.partitionId
    ++ (encodeUInt 2 message.concurrentLoginId))

def decode (bytes : List UInt8) : Option (DcSignonOutMessage × List UInt8) := do
  let (userId, bytes) ← decodeUInt 4 bytes
  let (partitionId, bytes) ← Alpha.decode 6 bytes
  let (concurrentLoginId, bytes) ← decodeUInt 2 bytes
  pure ({ userId, partitionId, concurrentLoginId }, bytes)

@[simp] theorem encode_length (message : DcSignonOutMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : DcSignonOutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DcSignonOutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end DcSignonOutMessage

/-- Dc Error Response Trade Message: 128 bytes -/
structure DcErrorResponseTradeMessage where
  errorMessage : Alpha 128
  deriving DecidableEq, Repr

namespace DcErrorResponseTradeMessage

def encode (message : DcErrorResponseTradeMessage) : List UInt8 :=
  Alpha.encode message.errorMessage

def decode (bytes : List UInt8) : Option (DcErrorResponseTradeMessage × List UInt8) := do
  let (errorMessage, bytes) ← Alpha.decode 128 bytes
  pure ({ errorMessage }, bytes)

@[simp] theorem encode_length (message : DcErrorResponseTradeMessage) : (encode message).length = 128 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : DcErrorResponseTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DcErrorResponseTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end DcErrorResponseTradeMessage

/-- Dc Error Response Order Message: 128 bytes -/
structure DcErrorResponseOrderMessage where
  errorMessage : Alpha 128
  deriving DecidableEq, Repr

namespace DcErrorResponseOrderMessage

def encode (message : DcErrorResponseOrderMessage) : List UInt8 :=
  Alpha.encode message.errorMessage

def decode (bytes : List UInt8) : Option (DcErrorResponseOrderMessage × List UInt8) := do
  let (errorMessage, bytes) ← Alpha.decode 128 bytes
  pure ({ errorMessage }, bytes)

@[simp] theorem encode_length (message : DcErrorResponseOrderMessage) : (encode message).length = 128 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : DcErrorResponseOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DcErrorResponseOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end DcErrorResponseOrderMessage

/-- Trade Confirmation Message: 116 bytes -/
structure TradeConfirmationMessage where
  orderNumber : Alpha 8
  traderNumber : BitVec 32
  buySell : BitVec 16
  originalVolume : BitVec 32
  disclosedVolume : BitVec 32
  remainingVolume : BitVec 32
  disclosedVolRemaining : BitVec 32
  price : BitVec 32
  stOrderFlags : BitVec 16
  fillNumber : BitVec 32
  fillQty : BitVec 32
  fillPrice : BitVec 32
  token : BitVec 32
  bookType : BitVec 16
  proClientShort2 : BitVec 16
  algoId : BitVec 32
  activityTimeInNanos : BitVec 64
  nnfField : Alpha 8
  segmentShort2 : BitVec 16
  brokerId : Alpha 5
  filler : Alpha 1
  pan : Alpha 10
  accountNumber : Alpha 10
  settlor : Alpha 12
  deriving DecidableEq, Repr

namespace TradeConfirmationMessage

def encode (message : TradeConfirmationMessage) : List UInt8 :=
  Alpha.encode message.orderNumber
    ++ (encodeUInt 4 message.traderNumber
    ++ (encodeUInt 2 message.buySell
    ++ (encodeUInt 4 message.originalVolume
    ++ (encodeUInt 4 message.disclosedVolume
    ++ (encodeUInt 4 message.remainingVolume
    ++ (encodeUInt 4 message.disclosedVolRemaining
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 4 message.fillNumber
    ++ (encodeUInt 4 message.fillQty
    ++ (encodeUInt 4 message.fillPrice
    ++ (encodeUInt 4 message.token
    ++ (encodeUInt 2 message.bookType
    ++ (encodeUInt 2 message.proClientShort2
    ++ (encodeUInt 4 message.algoId
    ++ (encodeUInt 8 message.activityTimeInNanos
    ++ (Alpha.encode message.nnfField
    ++ (encodeUInt 2 message.segmentShort2
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.filler
    ++ (Alpha.encode message.pan
    ++ (Alpha.encode message.accountNumber
    ++ (Alpha.encode message.settlor)))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (TradeConfirmationMessage × List UInt8) := do
  let (orderNumber, bytes) ← Alpha.decode 8 bytes
  let (traderNumber, bytes) ← decodeUInt 4 bytes
  let (buySell, bytes) ← decodeUInt 2 bytes
  let (originalVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolume, bytes) ← decodeUInt 4 bytes
  let (remainingVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolRemaining, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (fillNumber, bytes) ← decodeUInt 4 bytes
  let (fillQty, bytes) ← decodeUInt 4 bytes
  let (fillPrice, bytes) ← decodeUInt 4 bytes
  let (token, bytes) ← decodeUInt 4 bytes
  let (bookType, bytes) ← decodeUInt 2 bytes
  let (proClientShort2, bytes) ← decodeUInt 2 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (activityTimeInNanos, bytes) ← decodeUInt 8 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (segmentShort2, bytes) ← decodeUInt 2 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (filler, bytes) ← Alpha.decode 1 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (accountNumber, bytes) ← Alpha.decode 10 bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  pure ({ orderNumber, traderNumber, buySell, originalVolume, disclosedVolume, remainingVolume, disclosedVolRemaining, price, stOrderFlags, fillNumber, fillQty, fillPrice, token, bookType, proClientShort2, algoId, activityTimeInNanos, nnfField, segmentShort2, brokerId, filler, pan, accountNumber, settlor }, bytes)

@[simp] theorem encode_length (message : TradeConfirmationMessage) : (encode message).length = 116 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : TradeConfirmationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeConfirmationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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

end TradeConfirmationMessage

/-- Trade Cancel Confirm Message: 116 bytes -/
structure TradeCancelConfirmMessage where
  orderNumber : Alpha 8
  traderNumber : BitVec 32
  buySell : BitVec 16
  originalVolume : BitVec 32
  disclosedVolume : BitVec 32
  remainingVolume : BitVec 32
  disclosedVolRemaining : BitVec 32
  price : BitVec 32
  stOrderFlags : BitVec 16
  fillNumber : BitVec 32
  fillQty : BitVec 32
  fillPrice : BitVec 32
  token : BitVec 32
  bookType : BitVec 16
  proClientShort2 : BitVec 16
  algoId : BitVec 32
  activityTimeInNanos : BitVec 64
  nnfField : Alpha 8
  segmentShort2 : BitVec 16
  brokerId : Alpha 5
  filler : Alpha 1
  pan : Alpha 10
  accountNumber : Alpha 10
  settlor : Alpha 12
  deriving DecidableEq, Repr

namespace TradeCancelConfirmMessage

def encode (message : TradeCancelConfirmMessage) : List UInt8 :=
  Alpha.encode message.orderNumber
    ++ (encodeUInt 4 message.traderNumber
    ++ (encodeUInt 2 message.buySell
    ++ (encodeUInt 4 message.originalVolume
    ++ (encodeUInt 4 message.disclosedVolume
    ++ (encodeUInt 4 message.remainingVolume
    ++ (encodeUInt 4 message.disclosedVolRemaining
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 4 message.fillNumber
    ++ (encodeUInt 4 message.fillQty
    ++ (encodeUInt 4 message.fillPrice
    ++ (encodeUInt 4 message.token
    ++ (encodeUInt 2 message.bookType
    ++ (encodeUInt 2 message.proClientShort2
    ++ (encodeUInt 4 message.algoId
    ++ (encodeUInt 8 message.activityTimeInNanos
    ++ (Alpha.encode message.nnfField
    ++ (encodeUInt 2 message.segmentShort2
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.filler
    ++ (Alpha.encode message.pan
    ++ (Alpha.encode message.accountNumber
    ++ (Alpha.encode message.settlor)))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (TradeCancelConfirmMessage × List UInt8) := do
  let (orderNumber, bytes) ← Alpha.decode 8 bytes
  let (traderNumber, bytes) ← decodeUInt 4 bytes
  let (buySell, bytes) ← decodeUInt 2 bytes
  let (originalVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolume, bytes) ← decodeUInt 4 bytes
  let (remainingVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolRemaining, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (fillNumber, bytes) ← decodeUInt 4 bytes
  let (fillQty, bytes) ← decodeUInt 4 bytes
  let (fillPrice, bytes) ← decodeUInt 4 bytes
  let (token, bytes) ← decodeUInt 4 bytes
  let (bookType, bytes) ← decodeUInt 2 bytes
  let (proClientShort2, bytes) ← decodeUInt 2 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (activityTimeInNanos, bytes) ← decodeUInt 8 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (segmentShort2, bytes) ← decodeUInt 2 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (filler, bytes) ← Alpha.decode 1 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (accountNumber, bytes) ← Alpha.decode 10 bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  pure ({ orderNumber, traderNumber, buySell, originalVolume, disclosedVolume, remainingVolume, disclosedVolRemaining, price, stOrderFlags, fillNumber, fillQty, fillPrice, token, bookType, proClientShort2, algoId, activityTimeInNanos, nnfField, segmentShort2, brokerId, filler, pan, accountNumber, settlor }, bytes)

@[simp] theorem encode_length (message : TradeCancelConfirmMessage) : (encode message).length = 116 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : TradeCancelConfirmMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCancelConfirmMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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

end TradeCancelConfirmMessage

/-- Trade Cancel Reject Message: 116 bytes -/
structure TradeCancelRejectMessage where
  orderNumber : Alpha 8
  traderNumber : BitVec 32
  buySell : BitVec 16
  originalVolume : BitVec 32
  disclosedVolume : BitVec 32
  remainingVolume : BitVec 32
  disclosedVolRemaining : BitVec 32
  price : BitVec 32
  stOrderFlags : BitVec 16
  fillNumber : BitVec 32
  fillQty : BitVec 32
  fillPrice : BitVec 32
  token : BitVec 32
  bookType : BitVec 16
  proClientShort2 : BitVec 16
  algoId : BitVec 32
  activityTimeInNanos : BitVec 64
  nnfField : Alpha 8
  segmentShort2 : BitVec 16
  brokerId : Alpha 5
  filler : Alpha 1
  pan : Alpha 10
  accountNumber : Alpha 10
  settlor : Alpha 12
  deriving DecidableEq, Repr

namespace TradeCancelRejectMessage

def encode (message : TradeCancelRejectMessage) : List UInt8 :=
  Alpha.encode message.orderNumber
    ++ (encodeUInt 4 message.traderNumber
    ++ (encodeUInt 2 message.buySell
    ++ (encodeUInt 4 message.originalVolume
    ++ (encodeUInt 4 message.disclosedVolume
    ++ (encodeUInt 4 message.remainingVolume
    ++ (encodeUInt 4 message.disclosedVolRemaining
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 4 message.fillNumber
    ++ (encodeUInt 4 message.fillQty
    ++ (encodeUInt 4 message.fillPrice
    ++ (encodeUInt 4 message.token
    ++ (encodeUInt 2 message.bookType
    ++ (encodeUInt 2 message.proClientShort2
    ++ (encodeUInt 4 message.algoId
    ++ (encodeUInt 8 message.activityTimeInNanos
    ++ (Alpha.encode message.nnfField
    ++ (encodeUInt 2 message.segmentShort2
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.filler
    ++ (Alpha.encode message.pan
    ++ (Alpha.encode message.accountNumber
    ++ (Alpha.encode message.settlor)))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (TradeCancelRejectMessage × List UInt8) := do
  let (orderNumber, bytes) ← Alpha.decode 8 bytes
  let (traderNumber, bytes) ← decodeUInt 4 bytes
  let (buySell, bytes) ← decodeUInt 2 bytes
  let (originalVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolume, bytes) ← decodeUInt 4 bytes
  let (remainingVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolRemaining, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (fillNumber, bytes) ← decodeUInt 4 bytes
  let (fillQty, bytes) ← decodeUInt 4 bytes
  let (fillPrice, bytes) ← decodeUInt 4 bytes
  let (token, bytes) ← decodeUInt 4 bytes
  let (bookType, bytes) ← decodeUInt 2 bytes
  let (proClientShort2, bytes) ← decodeUInt 2 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (activityTimeInNanos, bytes) ← decodeUInt 8 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (segmentShort2, bytes) ← decodeUInt 2 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (filler, bytes) ← Alpha.decode 1 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (accountNumber, bytes) ← Alpha.decode 10 bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  pure ({ orderNumber, traderNumber, buySell, originalVolume, disclosedVolume, remainingVolume, disclosedVolRemaining, price, stOrderFlags, fillNumber, fillQty, fillPrice, token, bookType, proClientShort2, algoId, activityTimeInNanos, nnfField, segmentShort2, brokerId, filler, pan, accountNumber, settlor }, bytes)

@[simp] theorem encode_length (message : TradeCancelRejectMessage) : (encode message).length = 116 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : TradeCancelRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCancelRejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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

end TradeCancelRejectMessage

/-- Trade Modify Confirm Message: 116 bytes -/
structure TradeModifyConfirmMessage where
  orderNumber : Alpha 8
  traderNumber : BitVec 32
  buySell : BitVec 16
  originalVolume : BitVec 32
  disclosedVolume : BitVec 32
  remainingVolume : BitVec 32
  disclosedVolRemaining : BitVec 32
  price : BitVec 32
  stOrderFlags : BitVec 16
  fillNumber : BitVec 32
  fillQty : BitVec 32
  fillPrice : BitVec 32
  token : BitVec 32
  bookType : BitVec 16
  proClientShort2 : BitVec 16
  algoId : BitVec 32
  activityTimeInNanos : BitVec 64
  nnfField : Alpha 8
  segmentShort2 : BitVec 16
  brokerId : Alpha 5
  filler : Alpha 1
  pan : Alpha 10
  accountNumber : Alpha 10
  settlor : Alpha 12
  deriving DecidableEq, Repr

namespace TradeModifyConfirmMessage

def encode (message : TradeModifyConfirmMessage) : List UInt8 :=
  Alpha.encode message.orderNumber
    ++ (encodeUInt 4 message.traderNumber
    ++ (encodeUInt 2 message.buySell
    ++ (encodeUInt 4 message.originalVolume
    ++ (encodeUInt 4 message.disclosedVolume
    ++ (encodeUInt 4 message.remainingVolume
    ++ (encodeUInt 4 message.disclosedVolRemaining
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 4 message.fillNumber
    ++ (encodeUInt 4 message.fillQty
    ++ (encodeUInt 4 message.fillPrice
    ++ (encodeUInt 4 message.token
    ++ (encodeUInt 2 message.bookType
    ++ (encodeUInt 2 message.proClientShort2
    ++ (encodeUInt 4 message.algoId
    ++ (encodeUInt 8 message.activityTimeInNanos
    ++ (Alpha.encode message.nnfField
    ++ (encodeUInt 2 message.segmentShort2
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.filler
    ++ (Alpha.encode message.pan
    ++ (Alpha.encode message.accountNumber
    ++ (Alpha.encode message.settlor)))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (TradeModifyConfirmMessage × List UInt8) := do
  let (orderNumber, bytes) ← Alpha.decode 8 bytes
  let (traderNumber, bytes) ← decodeUInt 4 bytes
  let (buySell, bytes) ← decodeUInt 2 bytes
  let (originalVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolume, bytes) ← decodeUInt 4 bytes
  let (remainingVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolRemaining, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (fillNumber, bytes) ← decodeUInt 4 bytes
  let (fillQty, bytes) ← decodeUInt 4 bytes
  let (fillPrice, bytes) ← decodeUInt 4 bytes
  let (token, bytes) ← decodeUInt 4 bytes
  let (bookType, bytes) ← decodeUInt 2 bytes
  let (proClientShort2, bytes) ← decodeUInt 2 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (activityTimeInNanos, bytes) ← decodeUInt 8 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (segmentShort2, bytes) ← decodeUInt 2 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (filler, bytes) ← Alpha.decode 1 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (accountNumber, bytes) ← Alpha.decode 10 bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  pure ({ orderNumber, traderNumber, buySell, originalVolume, disclosedVolume, remainingVolume, disclosedVolRemaining, price, stOrderFlags, fillNumber, fillQty, fillPrice, token, bookType, proClientShort2, algoId, activityTimeInNanos, nnfField, segmentShort2, brokerId, filler, pan, accountNumber, settlor }, bytes)

@[simp] theorem encode_length (message : TradeModifyConfirmMessage) : (encode message).length = 116 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : TradeModifyConfirmMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeModifyConfirmMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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

end TradeModifyConfirmMessage

/-- Price Confirmation Message: 112 bytes -/
structure PriceConfirmationMessage where
  reasonCode : BitVec 16
  token : BitVec 32
  orderNumber : Alpha 8
  bookType : BitVec 16
  buySell : BitVec 16
  disclosedVolume : BitVec 32
  disclosedVolRemaining : BitVec 32
  totalVolRemaining : BitVec 32
  volume : BitVec 32
  price : BitVec 32
  triggerPrice : BitVec 32
  stOrderFlags : BitVec 16
  traderId : BitVec 32
  nnfField : Alpha 8
  algoId : BitVec 32
  activityTimeInNanos : BitVec 64
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  auctionNumber : BitVec 16
  suspended : Alpha 1
  filler : Alpha 1
  pan : Alpha 10
  segmentChar1 : Alpha 1
  participantType : ParticipantType
  accountNumber : Alpha 10
  proClientChar1 : Alpha 1
  settlementType : SettlementType
  settlor : Alpha 12
  deriving DecidableEq, Repr

namespace PriceConfirmationMessage

def encode (message : PriceConfirmationMessage) : List UInt8 :=
  encodeUInt 2 message.reasonCode
    ++ (encodeUInt 4 message.token
    ++ (Alpha.encode message.orderNumber
    ++ (encodeUInt 2 message.bookType
    ++ (encodeUInt 2 message.buySell
    ++ (encodeUInt 4 message.disclosedVolume
    ++ (encodeUInt 4 message.disclosedVolRemaining
    ++ (encodeUInt 4 message.totalVolRemaining
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.triggerPrice
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 4 message.traderId
    ++ (Alpha.encode message.nnfField
    ++ (encodeUInt 4 message.algoId
    ++ (encodeUInt 8 message.activityTimeInNanos
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (encodeUInt 2 message.auctionNumber
    ++ (Alpha.encode message.suspended
    ++ (Alpha.encode message.filler
    ++ (Alpha.encode message.pan
    ++ (Alpha.encode message.segmentChar1
    ++ (ParticipantType.encode message.participantType
    ++ (Alpha.encode message.accountNumber
    ++ (Alpha.encode message.proClientChar1
    ++ (SettlementType.encode message.settlementType
    ++ (Alpha.encode message.settlor)))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (PriceConfirmationMessage × List UInt8) := do
  let (reasonCode, bytes) ← decodeUInt 2 bytes
  let (token, bytes) ← decodeUInt 4 bytes
  let (orderNumber, bytes) ← Alpha.decode 8 bytes
  let (bookType, bytes) ← decodeUInt 2 bytes
  let (buySell, bytes) ← decodeUInt 2 bytes
  let (disclosedVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolRemaining, bytes) ← decodeUInt 4 bytes
  let (totalVolRemaining, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (triggerPrice, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (activityTimeInNanos, bytes) ← decodeUInt 8 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (auctionNumber, bytes) ← decodeUInt 2 bytes
  let (suspended, bytes) ← Alpha.decode 1 bytes
  let (filler, bytes) ← Alpha.decode 1 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (segmentChar1, bytes) ← Alpha.decode 1 bytes
  let (participantType, bytes) ← ParticipantType.decode bytes
  let (accountNumber, bytes) ← Alpha.decode 10 bytes
  let (proClientChar1, bytes) ← Alpha.decode 1 bytes
  let (settlementType, bytes) ← SettlementType.decode bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  pure ({ reasonCode, token, orderNumber, bookType, buySell, disclosedVolume, disclosedVolRemaining, totalVolRemaining, volume, price, triggerPrice, stOrderFlags, traderId, nnfField, algoId, activityTimeInNanos, competitorPeriod, solicitorPeriod, auctionNumber, suspended, filler, pan, segmentChar1, participantType, accountNumber, proClientChar1, settlementType, settlor }, bytes)

@[simp] theorem encode_length (message : PriceConfirmationMessage) : (encode message).length = 112 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, ParticipantType.encode_length, SettlementType.encode_length]

theorem encode_length_pos (message : PriceConfirmationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : PriceConfirmationMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, ParticipantType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SettlementType.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end PriceConfirmationMessage

/-- Order Mod Reject Message: 112 bytes -/
structure OrderModRejectMessage where
  reasonCode : BitVec 16
  token : BitVec 32
  orderNumber : Alpha 8
  bookType : BitVec 16
  buySell : BitVec 16
  disclosedVolume : BitVec 32
  disclosedVolRemaining : BitVec 32
  totalVolRemaining : BitVec 32
  volume : BitVec 32
  price : BitVec 32
  triggerPrice : BitVec 32
  stOrderFlags : BitVec 16
  traderId : BitVec 32
  nnfField : Alpha 8
  algoId : BitVec 32
  activityTimeInNanos : BitVec 64
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  auctionNumber : BitVec 16
  suspended : Alpha 1
  filler : Alpha 1
  pan : Alpha 10
  segmentChar1 : Alpha 1
  participantType : ParticipantType
  accountNumber : Alpha 10
  proClientChar1 : Alpha 1
  settlementType : SettlementType
  settlor : Alpha 12
  deriving DecidableEq, Repr

namespace OrderModRejectMessage

def encode (message : OrderModRejectMessage) : List UInt8 :=
  encodeUInt 2 message.reasonCode
    ++ (encodeUInt 4 message.token
    ++ (Alpha.encode message.orderNumber
    ++ (encodeUInt 2 message.bookType
    ++ (encodeUInt 2 message.buySell
    ++ (encodeUInt 4 message.disclosedVolume
    ++ (encodeUInt 4 message.disclosedVolRemaining
    ++ (encodeUInt 4 message.totalVolRemaining
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.triggerPrice
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 4 message.traderId
    ++ (Alpha.encode message.nnfField
    ++ (encodeUInt 4 message.algoId
    ++ (encodeUInt 8 message.activityTimeInNanos
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (encodeUInt 2 message.auctionNumber
    ++ (Alpha.encode message.suspended
    ++ (Alpha.encode message.filler
    ++ (Alpha.encode message.pan
    ++ (Alpha.encode message.segmentChar1
    ++ (ParticipantType.encode message.participantType
    ++ (Alpha.encode message.accountNumber
    ++ (Alpha.encode message.proClientChar1
    ++ (SettlementType.encode message.settlementType
    ++ (Alpha.encode message.settlor)))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderModRejectMessage × List UInt8) := do
  let (reasonCode, bytes) ← decodeUInt 2 bytes
  let (token, bytes) ← decodeUInt 4 bytes
  let (orderNumber, bytes) ← Alpha.decode 8 bytes
  let (bookType, bytes) ← decodeUInt 2 bytes
  let (buySell, bytes) ← decodeUInt 2 bytes
  let (disclosedVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolRemaining, bytes) ← decodeUInt 4 bytes
  let (totalVolRemaining, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (triggerPrice, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (activityTimeInNanos, bytes) ← decodeUInt 8 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (auctionNumber, bytes) ← decodeUInt 2 bytes
  let (suspended, bytes) ← Alpha.decode 1 bytes
  let (filler, bytes) ← Alpha.decode 1 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (segmentChar1, bytes) ← Alpha.decode 1 bytes
  let (participantType, bytes) ← ParticipantType.decode bytes
  let (accountNumber, bytes) ← Alpha.decode 10 bytes
  let (proClientChar1, bytes) ← Alpha.decode 1 bytes
  let (settlementType, bytes) ← SettlementType.decode bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  pure ({ reasonCode, token, orderNumber, bookType, buySell, disclosedVolume, disclosedVolRemaining, totalVolRemaining, volume, price, triggerPrice, stOrderFlags, traderId, nnfField, algoId, activityTimeInNanos, competitorPeriod, solicitorPeriod, auctionNumber, suspended, filler, pan, segmentChar1, participantType, accountNumber, proClientChar1, settlementType, settlor }, bytes)

@[simp] theorem encode_length (message : OrderModRejectMessage) : (encode message).length = 112 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, ParticipantType.encode_length, SettlementType.encode_length]

theorem encode_length_pos (message : OrderModRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OrderModRejectMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, ParticipantType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SettlementType.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderModRejectMessage

/-- Order Cancel Reject Message: 112 bytes -/
structure OrderCancelRejectMessage where
  reasonCode : BitVec 16
  token : BitVec 32
  orderNumber : Alpha 8
  bookType : BitVec 16
  buySell : BitVec 16
  disclosedVolume : BitVec 32
  disclosedVolRemaining : BitVec 32
  totalVolRemaining : BitVec 32
  volume : BitVec 32
  price : BitVec 32
  triggerPrice : BitVec 32
  stOrderFlags : BitVec 16
  traderId : BitVec 32
  nnfField : Alpha 8
  algoId : BitVec 32
  activityTimeInNanos : BitVec 64
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  auctionNumber : BitVec 16
  suspended : Alpha 1
  filler : Alpha 1
  pan : Alpha 10
  segmentChar1 : Alpha 1
  participantType : ParticipantType
  accountNumber : Alpha 10
  proClientChar1 : Alpha 1
  settlementType : SettlementType
  settlor : Alpha 12
  deriving DecidableEq, Repr

namespace OrderCancelRejectMessage

def encode (message : OrderCancelRejectMessage) : List UInt8 :=
  encodeUInt 2 message.reasonCode
    ++ (encodeUInt 4 message.token
    ++ (Alpha.encode message.orderNumber
    ++ (encodeUInt 2 message.bookType
    ++ (encodeUInt 2 message.buySell
    ++ (encodeUInt 4 message.disclosedVolume
    ++ (encodeUInt 4 message.disclosedVolRemaining
    ++ (encodeUInt 4 message.totalVolRemaining
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.triggerPrice
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 4 message.traderId
    ++ (Alpha.encode message.nnfField
    ++ (encodeUInt 4 message.algoId
    ++ (encodeUInt 8 message.activityTimeInNanos
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (encodeUInt 2 message.auctionNumber
    ++ (Alpha.encode message.suspended
    ++ (Alpha.encode message.filler
    ++ (Alpha.encode message.pan
    ++ (Alpha.encode message.segmentChar1
    ++ (ParticipantType.encode message.participantType
    ++ (Alpha.encode message.accountNumber
    ++ (Alpha.encode message.proClientChar1
    ++ (SettlementType.encode message.settlementType
    ++ (Alpha.encode message.settlor)))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderCancelRejectMessage × List UInt8) := do
  let (reasonCode, bytes) ← decodeUInt 2 bytes
  let (token, bytes) ← decodeUInt 4 bytes
  let (orderNumber, bytes) ← Alpha.decode 8 bytes
  let (bookType, bytes) ← decodeUInt 2 bytes
  let (buySell, bytes) ← decodeUInt 2 bytes
  let (disclosedVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolRemaining, bytes) ← decodeUInt 4 bytes
  let (totalVolRemaining, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (triggerPrice, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (activityTimeInNanos, bytes) ← decodeUInt 8 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (auctionNumber, bytes) ← decodeUInt 2 bytes
  let (suspended, bytes) ← Alpha.decode 1 bytes
  let (filler, bytes) ← Alpha.decode 1 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (segmentChar1, bytes) ← Alpha.decode 1 bytes
  let (participantType, bytes) ← ParticipantType.decode bytes
  let (accountNumber, bytes) ← Alpha.decode 10 bytes
  let (proClientChar1, bytes) ← Alpha.decode 1 bytes
  let (settlementType, bytes) ← SettlementType.decode bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  pure ({ reasonCode, token, orderNumber, bookType, buySell, disclosedVolume, disclosedVolRemaining, totalVolRemaining, volume, price, triggerPrice, stOrderFlags, traderId, nnfField, algoId, activityTimeInNanos, competitorPeriod, solicitorPeriod, auctionNumber, suspended, filler, pan, segmentChar1, participantType, accountNumber, proClientChar1, settlementType, settlor }, bytes)

@[simp] theorem encode_length (message : OrderCancelRejectMessage) : (encode message).length = 112 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, ParticipantType.encode_length, SettlementType.encode_length]

theorem encode_length_pos (message : OrderCancelRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OrderCancelRejectMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, ParticipantType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SettlementType.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderCancelRejectMessage

/-- Order Confirmation Message: 112 bytes -/
structure OrderConfirmationMessage where
  reasonCode : BitVec 16
  token : BitVec 32
  orderNumber : Alpha 8
  bookType : BitVec 16
  buySell : BitVec 16
  disclosedVolume : BitVec 32
  disclosedVolRemaining : BitVec 32
  totalVolRemaining : BitVec 32
  volume : BitVec 32
  price : BitVec 32
  triggerPrice : BitVec 32
  stOrderFlags : BitVec 16
  traderId : BitVec 32
  nnfField : Alpha 8
  algoId : BitVec 32
  activityTimeInNanos : BitVec 64
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  auctionNumber : BitVec 16
  suspended : Alpha 1
  filler : Alpha 1
  pan : Alpha 10
  segmentChar1 : Alpha 1
  participantType : ParticipantType
  accountNumber : Alpha 10
  proClientChar1 : Alpha 1
  settlementType : SettlementType
  settlor : Alpha 12
  deriving DecidableEq, Repr

namespace OrderConfirmationMessage

def encode (message : OrderConfirmationMessage) : List UInt8 :=
  encodeUInt 2 message.reasonCode
    ++ (encodeUInt 4 message.token
    ++ (Alpha.encode message.orderNumber
    ++ (encodeUInt 2 message.bookType
    ++ (encodeUInt 2 message.buySell
    ++ (encodeUInt 4 message.disclosedVolume
    ++ (encodeUInt 4 message.disclosedVolRemaining
    ++ (encodeUInt 4 message.totalVolRemaining
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.triggerPrice
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 4 message.traderId
    ++ (Alpha.encode message.nnfField
    ++ (encodeUInt 4 message.algoId
    ++ (encodeUInt 8 message.activityTimeInNanos
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (encodeUInt 2 message.auctionNumber
    ++ (Alpha.encode message.suspended
    ++ (Alpha.encode message.filler
    ++ (Alpha.encode message.pan
    ++ (Alpha.encode message.segmentChar1
    ++ (ParticipantType.encode message.participantType
    ++ (Alpha.encode message.accountNumber
    ++ (Alpha.encode message.proClientChar1
    ++ (SettlementType.encode message.settlementType
    ++ (Alpha.encode message.settlor)))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderConfirmationMessage × List UInt8) := do
  let (reasonCode, bytes) ← decodeUInt 2 bytes
  let (token, bytes) ← decodeUInt 4 bytes
  let (orderNumber, bytes) ← Alpha.decode 8 bytes
  let (bookType, bytes) ← decodeUInt 2 bytes
  let (buySell, bytes) ← decodeUInt 2 bytes
  let (disclosedVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolRemaining, bytes) ← decodeUInt 4 bytes
  let (totalVolRemaining, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (triggerPrice, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (activityTimeInNanos, bytes) ← decodeUInt 8 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (auctionNumber, bytes) ← decodeUInt 2 bytes
  let (suspended, bytes) ← Alpha.decode 1 bytes
  let (filler, bytes) ← Alpha.decode 1 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (segmentChar1, bytes) ← Alpha.decode 1 bytes
  let (participantType, bytes) ← ParticipantType.decode bytes
  let (accountNumber, bytes) ← Alpha.decode 10 bytes
  let (proClientChar1, bytes) ← Alpha.decode 1 bytes
  let (settlementType, bytes) ← SettlementType.decode bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  pure ({ reasonCode, token, orderNumber, bookType, buySell, disclosedVolume, disclosedVolRemaining, totalVolRemaining, volume, price, triggerPrice, stOrderFlags, traderId, nnfField, algoId, activityTimeInNanos, competitorPeriod, solicitorPeriod, auctionNumber, suspended, filler, pan, segmentChar1, participantType, accountNumber, proClientChar1, settlementType, settlor }, bytes)

@[simp] theorem encode_length (message : OrderConfirmationMessage) : (encode message).length = 112 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, ParticipantType.encode_length, SettlementType.encode_length]

theorem encode_length_pos (message : OrderConfirmationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OrderConfirmationMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, ParticipantType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SettlementType.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderConfirmationMessage

/-- Order Mod Confirmation Message: 112 bytes -/
structure OrderModConfirmationMessage where
  reasonCode : BitVec 16
  token : BitVec 32
  orderNumber : Alpha 8
  bookType : BitVec 16
  buySell : BitVec 16
  disclosedVolume : BitVec 32
  disclosedVolRemaining : BitVec 32
  totalVolRemaining : BitVec 32
  volume : BitVec 32
  price : BitVec 32
  triggerPrice : BitVec 32
  stOrderFlags : BitVec 16
  traderId : BitVec 32
  nnfField : Alpha 8
  algoId : BitVec 32
  activityTimeInNanos : BitVec 64
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  auctionNumber : BitVec 16
  suspended : Alpha 1
  filler : Alpha 1
  pan : Alpha 10
  segmentChar1 : Alpha 1
  participantType : ParticipantType
  accountNumber : Alpha 10
  proClientChar1 : Alpha 1
  settlementType : SettlementType
  settlor : Alpha 12
  deriving DecidableEq, Repr

namespace OrderModConfirmationMessage

def encode (message : OrderModConfirmationMessage) : List UInt8 :=
  encodeUInt 2 message.reasonCode
    ++ (encodeUInt 4 message.token
    ++ (Alpha.encode message.orderNumber
    ++ (encodeUInt 2 message.bookType
    ++ (encodeUInt 2 message.buySell
    ++ (encodeUInt 4 message.disclosedVolume
    ++ (encodeUInt 4 message.disclosedVolRemaining
    ++ (encodeUInt 4 message.totalVolRemaining
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.triggerPrice
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 4 message.traderId
    ++ (Alpha.encode message.nnfField
    ++ (encodeUInt 4 message.algoId
    ++ (encodeUInt 8 message.activityTimeInNanos
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (encodeUInt 2 message.auctionNumber
    ++ (Alpha.encode message.suspended
    ++ (Alpha.encode message.filler
    ++ (Alpha.encode message.pan
    ++ (Alpha.encode message.segmentChar1
    ++ (ParticipantType.encode message.participantType
    ++ (Alpha.encode message.accountNumber
    ++ (Alpha.encode message.proClientChar1
    ++ (SettlementType.encode message.settlementType
    ++ (Alpha.encode message.settlor)))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderModConfirmationMessage × List UInt8) := do
  let (reasonCode, bytes) ← decodeUInt 2 bytes
  let (token, bytes) ← decodeUInt 4 bytes
  let (orderNumber, bytes) ← Alpha.decode 8 bytes
  let (bookType, bytes) ← decodeUInt 2 bytes
  let (buySell, bytes) ← decodeUInt 2 bytes
  let (disclosedVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolRemaining, bytes) ← decodeUInt 4 bytes
  let (totalVolRemaining, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (triggerPrice, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (activityTimeInNanos, bytes) ← decodeUInt 8 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (auctionNumber, bytes) ← decodeUInt 2 bytes
  let (suspended, bytes) ← Alpha.decode 1 bytes
  let (filler, bytes) ← Alpha.decode 1 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (segmentChar1, bytes) ← Alpha.decode 1 bytes
  let (participantType, bytes) ← ParticipantType.decode bytes
  let (accountNumber, bytes) ← Alpha.decode 10 bytes
  let (proClientChar1, bytes) ← Alpha.decode 1 bytes
  let (settlementType, bytes) ← SettlementType.decode bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  pure ({ reasonCode, token, orderNumber, bookType, buySell, disclosedVolume, disclosedVolRemaining, totalVolRemaining, volume, price, triggerPrice, stOrderFlags, traderId, nnfField, algoId, activityTimeInNanos, competitorPeriod, solicitorPeriod, auctionNumber, suspended, filler, pan, segmentChar1, participantType, accountNumber, proClientChar1, settlementType, settlor }, bytes)

@[simp] theorem encode_length (message : OrderModConfirmationMessage) : (encode message).length = 112 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, ParticipantType.encode_length, SettlementType.encode_length]

theorem encode_length_pos (message : OrderModConfirmationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OrderModConfirmationMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, ParticipantType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SettlementType.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderModConfirmationMessage

/-- Order Cancel Confirmation Message: 112 bytes -/
structure OrderCancelConfirmationMessage where
  reasonCode : BitVec 16
  token : BitVec 32
  orderNumber : Alpha 8
  bookType : BitVec 16
  buySell : BitVec 16
  disclosedVolume : BitVec 32
  disclosedVolRemaining : BitVec 32
  totalVolRemaining : BitVec 32
  volume : BitVec 32
  price : BitVec 32
  triggerPrice : BitVec 32
  stOrderFlags : BitVec 16
  traderId : BitVec 32
  nnfField : Alpha 8
  algoId : BitVec 32
  activityTimeInNanos : BitVec 64
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  auctionNumber : BitVec 16
  suspended : Alpha 1
  filler : Alpha 1
  pan : Alpha 10
  segmentChar1 : Alpha 1
  participantType : ParticipantType
  accountNumber : Alpha 10
  proClientChar1 : Alpha 1
  settlementType : SettlementType
  settlor : Alpha 12
  deriving DecidableEq, Repr

namespace OrderCancelConfirmationMessage

def encode (message : OrderCancelConfirmationMessage) : List UInt8 :=
  encodeUInt 2 message.reasonCode
    ++ (encodeUInt 4 message.token
    ++ (Alpha.encode message.orderNumber
    ++ (encodeUInt 2 message.bookType
    ++ (encodeUInt 2 message.buySell
    ++ (encodeUInt 4 message.disclosedVolume
    ++ (encodeUInt 4 message.disclosedVolRemaining
    ++ (encodeUInt 4 message.totalVolRemaining
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.triggerPrice
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 4 message.traderId
    ++ (Alpha.encode message.nnfField
    ++ (encodeUInt 4 message.algoId
    ++ (encodeUInt 8 message.activityTimeInNanos
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (encodeUInt 2 message.auctionNumber
    ++ (Alpha.encode message.suspended
    ++ (Alpha.encode message.filler
    ++ (Alpha.encode message.pan
    ++ (Alpha.encode message.segmentChar1
    ++ (ParticipantType.encode message.participantType
    ++ (Alpha.encode message.accountNumber
    ++ (Alpha.encode message.proClientChar1
    ++ (SettlementType.encode message.settlementType
    ++ (Alpha.encode message.settlor)))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderCancelConfirmationMessage × List UInt8) := do
  let (reasonCode, bytes) ← decodeUInt 2 bytes
  let (token, bytes) ← decodeUInt 4 bytes
  let (orderNumber, bytes) ← Alpha.decode 8 bytes
  let (bookType, bytes) ← decodeUInt 2 bytes
  let (buySell, bytes) ← decodeUInt 2 bytes
  let (disclosedVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolRemaining, bytes) ← decodeUInt 4 bytes
  let (totalVolRemaining, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (triggerPrice, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (activityTimeInNanos, bytes) ← decodeUInt 8 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (auctionNumber, bytes) ← decodeUInt 2 bytes
  let (suspended, bytes) ← Alpha.decode 1 bytes
  let (filler, bytes) ← Alpha.decode 1 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (segmentChar1, bytes) ← Alpha.decode 1 bytes
  let (participantType, bytes) ← ParticipantType.decode bytes
  let (accountNumber, bytes) ← Alpha.decode 10 bytes
  let (proClientChar1, bytes) ← Alpha.decode 1 bytes
  let (settlementType, bytes) ← SettlementType.decode bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  pure ({ reasonCode, token, orderNumber, bookType, buySell, disclosedVolume, disclosedVolRemaining, totalVolRemaining, volume, price, triggerPrice, stOrderFlags, traderId, nnfField, algoId, activityTimeInNanos, competitorPeriod, solicitorPeriod, auctionNumber, suspended, filler, pan, segmentChar1, participantType, accountNumber, proClientChar1, settlementType, settlor }, bytes)

@[simp] theorem encode_length (message : OrderCancelConfirmationMessage) : (encode message).length = 112 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, ParticipantType.encode_length, SettlementType.encode_length]

theorem encode_length_pos (message : OrderCancelConfirmationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OrderCancelConfirmationMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, ParticipantType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SettlementType.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderCancelConfirmationMessage

/-- Freeze To Control Message: 112 bytes -/
structure FreezeToControlMessage where
  reasonCode : BitVec 16
  token : BitVec 32
  orderNumber : Alpha 8
  bookType : BitVec 16
  buySell : BitVec 16
  disclosedVolume : BitVec 32
  disclosedVolRemaining : BitVec 32
  totalVolRemaining : BitVec 32
  volume : BitVec 32
  price : BitVec 32
  triggerPrice : BitVec 32
  stOrderFlags : BitVec 16
  traderId : BitVec 32
  nnfField : Alpha 8
  algoId : BitVec 32
  activityTimeInNanos : BitVec 64
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  auctionNumber : BitVec 16
  suspended : Alpha 1
  filler : Alpha 1
  pan : Alpha 10
  segmentChar1 : Alpha 1
  participantType : ParticipantType
  accountNumber : Alpha 10
  proClientChar1 : Alpha 1
  settlementType : SettlementType
  settlor : Alpha 12
  deriving DecidableEq, Repr

namespace FreezeToControlMessage

def encode (message : FreezeToControlMessage) : List UInt8 :=
  encodeUInt 2 message.reasonCode
    ++ (encodeUInt 4 message.token
    ++ (Alpha.encode message.orderNumber
    ++ (encodeUInt 2 message.bookType
    ++ (encodeUInt 2 message.buySell
    ++ (encodeUInt 4 message.disclosedVolume
    ++ (encodeUInt 4 message.disclosedVolRemaining
    ++ (encodeUInt 4 message.totalVolRemaining
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.triggerPrice
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 4 message.traderId
    ++ (Alpha.encode message.nnfField
    ++ (encodeUInt 4 message.algoId
    ++ (encodeUInt 8 message.activityTimeInNanos
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (encodeUInt 2 message.auctionNumber
    ++ (Alpha.encode message.suspended
    ++ (Alpha.encode message.filler
    ++ (Alpha.encode message.pan
    ++ (Alpha.encode message.segmentChar1
    ++ (ParticipantType.encode message.participantType
    ++ (Alpha.encode message.accountNumber
    ++ (Alpha.encode message.proClientChar1
    ++ (SettlementType.encode message.settlementType
    ++ (Alpha.encode message.settlor)))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (FreezeToControlMessage × List UInt8) := do
  let (reasonCode, bytes) ← decodeUInt 2 bytes
  let (token, bytes) ← decodeUInt 4 bytes
  let (orderNumber, bytes) ← Alpha.decode 8 bytes
  let (bookType, bytes) ← decodeUInt 2 bytes
  let (buySell, bytes) ← decodeUInt 2 bytes
  let (disclosedVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolRemaining, bytes) ← decodeUInt 4 bytes
  let (totalVolRemaining, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (triggerPrice, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (activityTimeInNanos, bytes) ← decodeUInt 8 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (auctionNumber, bytes) ← decodeUInt 2 bytes
  let (suspended, bytes) ← Alpha.decode 1 bytes
  let (filler, bytes) ← Alpha.decode 1 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (segmentChar1, bytes) ← Alpha.decode 1 bytes
  let (participantType, bytes) ← ParticipantType.decode bytes
  let (accountNumber, bytes) ← Alpha.decode 10 bytes
  let (proClientChar1, bytes) ← Alpha.decode 1 bytes
  let (settlementType, bytes) ← SettlementType.decode bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  pure ({ reasonCode, token, orderNumber, bookType, buySell, disclosedVolume, disclosedVolRemaining, totalVolRemaining, volume, price, triggerPrice, stOrderFlags, traderId, nnfField, algoId, activityTimeInNanos, competitorPeriod, solicitorPeriod, auctionNumber, suspended, filler, pan, segmentChar1, participantType, accountNumber, proClientChar1, settlementType, settlor }, bytes)

@[simp] theorem encode_length (message : FreezeToControlMessage) : (encode message).length = 112 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, ParticipantType.encode_length, SettlementType.encode_length]

theorem encode_length_pos (message : FreezeToControlMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : FreezeToControlMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, ParticipantType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SettlementType.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FreezeToControlMessage

/-- On Stop Notification Message: 112 bytes -/
structure OnStopNotificationMessage where
  reasonCode : BitVec 16
  token : BitVec 32
  orderNumber : Alpha 8
  bookType : BitVec 16
  buySell : BitVec 16
  disclosedVolume : BitVec 32
  disclosedVolRemaining : BitVec 32
  totalVolRemaining : BitVec 32
  volume : BitVec 32
  price : BitVec 32
  triggerPrice : BitVec 32
  stOrderFlags : BitVec 16
  traderId : BitVec 32
  nnfField : Alpha 8
  algoId : BitVec 32
  activityTimeInNanos : BitVec 64
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  auctionNumber : BitVec 16
  suspended : Alpha 1
  filler : Alpha 1
  pan : Alpha 10
  segmentChar1 : Alpha 1
  participantType : ParticipantType
  accountNumber : Alpha 10
  proClientChar1 : Alpha 1
  settlementType : SettlementType
  settlor : Alpha 12
  deriving DecidableEq, Repr

namespace OnStopNotificationMessage

def encode (message : OnStopNotificationMessage) : List UInt8 :=
  encodeUInt 2 message.reasonCode
    ++ (encodeUInt 4 message.token
    ++ (Alpha.encode message.orderNumber
    ++ (encodeUInt 2 message.bookType
    ++ (encodeUInt 2 message.buySell
    ++ (encodeUInt 4 message.disclosedVolume
    ++ (encodeUInt 4 message.disclosedVolRemaining
    ++ (encodeUInt 4 message.totalVolRemaining
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.triggerPrice
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 4 message.traderId
    ++ (Alpha.encode message.nnfField
    ++ (encodeUInt 4 message.algoId
    ++ (encodeUInt 8 message.activityTimeInNanos
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (encodeUInt 2 message.auctionNumber
    ++ (Alpha.encode message.suspended
    ++ (Alpha.encode message.filler
    ++ (Alpha.encode message.pan
    ++ (Alpha.encode message.segmentChar1
    ++ (ParticipantType.encode message.participantType
    ++ (Alpha.encode message.accountNumber
    ++ (Alpha.encode message.proClientChar1
    ++ (SettlementType.encode message.settlementType
    ++ (Alpha.encode message.settlor)))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OnStopNotificationMessage × List UInt8) := do
  let (reasonCode, bytes) ← decodeUInt 2 bytes
  let (token, bytes) ← decodeUInt 4 bytes
  let (orderNumber, bytes) ← Alpha.decode 8 bytes
  let (bookType, bytes) ← decodeUInt 2 bytes
  let (buySell, bytes) ← decodeUInt 2 bytes
  let (disclosedVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolRemaining, bytes) ← decodeUInt 4 bytes
  let (totalVolRemaining, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (triggerPrice, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (activityTimeInNanos, bytes) ← decodeUInt 8 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (auctionNumber, bytes) ← decodeUInt 2 bytes
  let (suspended, bytes) ← Alpha.decode 1 bytes
  let (filler, bytes) ← Alpha.decode 1 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (segmentChar1, bytes) ← Alpha.decode 1 bytes
  let (participantType, bytes) ← ParticipantType.decode bytes
  let (accountNumber, bytes) ← Alpha.decode 10 bytes
  let (proClientChar1, bytes) ← Alpha.decode 1 bytes
  let (settlementType, bytes) ← SettlementType.decode bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  pure ({ reasonCode, token, orderNumber, bookType, buySell, disclosedVolume, disclosedVolRemaining, totalVolRemaining, volume, price, triggerPrice, stOrderFlags, traderId, nnfField, algoId, activityTimeInNanos, competitorPeriod, solicitorPeriod, auctionNumber, suspended, filler, pan, segmentChar1, participantType, accountNumber, proClientChar1, settlementType, settlor }, bytes)

@[simp] theorem encode_length (message : OnStopNotificationMessage) : (encode message).length = 112 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, ParticipantType.encode_length, SettlementType.encode_length]

theorem encode_length_pos (message : OnStopNotificationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OnStopNotificationMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, ParticipantType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SettlementType.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OnStopNotificationMessage

/-- Order Error Message: 112 bytes -/
structure OrderErrorMessage where
  reasonCode : BitVec 16
  token : BitVec 32
  orderNumber : Alpha 8
  bookType : BitVec 16
  buySell : BitVec 16
  disclosedVolume : BitVec 32
  disclosedVolRemaining : BitVec 32
  totalVolRemaining : BitVec 32
  volume : BitVec 32
  price : BitVec 32
  triggerPrice : BitVec 32
  stOrderFlags : BitVec 16
  traderId : BitVec 32
  nnfField : Alpha 8
  algoId : BitVec 32
  activityTimeInNanos : BitVec 64
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  auctionNumber : BitVec 16
  suspended : Alpha 1
  filler : Alpha 1
  pan : Alpha 10
  segmentChar1 : Alpha 1
  participantType : ParticipantType
  accountNumber : Alpha 10
  proClientChar1 : Alpha 1
  settlementType : SettlementType
  settlor : Alpha 12
  deriving DecidableEq, Repr

namespace OrderErrorMessage

def encode (message : OrderErrorMessage) : List UInt8 :=
  encodeUInt 2 message.reasonCode
    ++ (encodeUInt 4 message.token
    ++ (Alpha.encode message.orderNumber
    ++ (encodeUInt 2 message.bookType
    ++ (encodeUInt 2 message.buySell
    ++ (encodeUInt 4 message.disclosedVolume
    ++ (encodeUInt 4 message.disclosedVolRemaining
    ++ (encodeUInt 4 message.totalVolRemaining
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.triggerPrice
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 4 message.traderId
    ++ (Alpha.encode message.nnfField
    ++ (encodeUInt 4 message.algoId
    ++ (encodeUInt 8 message.activityTimeInNanos
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (encodeUInt 2 message.auctionNumber
    ++ (Alpha.encode message.suspended
    ++ (Alpha.encode message.filler
    ++ (Alpha.encode message.pan
    ++ (Alpha.encode message.segmentChar1
    ++ (ParticipantType.encode message.participantType
    ++ (Alpha.encode message.accountNumber
    ++ (Alpha.encode message.proClientChar1
    ++ (SettlementType.encode message.settlementType
    ++ (Alpha.encode message.settlor)))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderErrorMessage × List UInt8) := do
  let (reasonCode, bytes) ← decodeUInt 2 bytes
  let (token, bytes) ← decodeUInt 4 bytes
  let (orderNumber, bytes) ← Alpha.decode 8 bytes
  let (bookType, bytes) ← decodeUInt 2 bytes
  let (buySell, bytes) ← decodeUInt 2 bytes
  let (disclosedVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolRemaining, bytes) ← decodeUInt 4 bytes
  let (totalVolRemaining, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (triggerPrice, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (activityTimeInNanos, bytes) ← decodeUInt 8 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (auctionNumber, bytes) ← decodeUInt 2 bytes
  let (suspended, bytes) ← Alpha.decode 1 bytes
  let (filler, bytes) ← Alpha.decode 1 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (segmentChar1, bytes) ← Alpha.decode 1 bytes
  let (participantType, bytes) ← ParticipantType.decode bytes
  let (accountNumber, bytes) ← Alpha.decode 10 bytes
  let (proClientChar1, bytes) ← Alpha.decode 1 bytes
  let (settlementType, bytes) ← SettlementType.decode bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  pure ({ reasonCode, token, orderNumber, bookType, buySell, disclosedVolume, disclosedVolRemaining, totalVolRemaining, volume, price, triggerPrice, stOrderFlags, traderId, nnfField, algoId, activityTimeInNanos, competitorPeriod, solicitorPeriod, auctionNumber, suspended, filler, pan, segmentChar1, participantType, accountNumber, proClientChar1, settlementType, settlor }, bytes)

@[simp] theorem encode_length (message : OrderErrorMessage) : (encode message).length = 112 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, ParticipantType.encode_length, SettlementType.encode_length]

theorem encode_length_pos (message : OrderErrorMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OrderErrorMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, ParticipantType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SettlementType.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderErrorMessage

/-- Batch Order Cancel Message: 112 bytes -/
structure BatchOrderCancelMessage where
  reasonCode : BitVec 16
  token : BitVec 32
  orderNumber : Alpha 8
  bookType : BitVec 16
  buySell : BitVec 16
  disclosedVolume : BitVec 32
  disclosedVolRemaining : BitVec 32
  totalVolRemaining : BitVec 32
  volume : BitVec 32
  price : BitVec 32
  triggerPrice : BitVec 32
  stOrderFlags : BitVec 16
  traderId : BitVec 32
  nnfField : Alpha 8
  algoId : BitVec 32
  activityTimeInNanos : BitVec 64
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  auctionNumber : BitVec 16
  suspended : Alpha 1
  filler : Alpha 1
  pan : Alpha 10
  segmentChar1 : Alpha 1
  participantType : ParticipantType
  accountNumber : Alpha 10
  proClientChar1 : Alpha 1
  settlementType : SettlementType
  settlor : Alpha 12
  deriving DecidableEq, Repr

namespace BatchOrderCancelMessage

def encode (message : BatchOrderCancelMessage) : List UInt8 :=
  encodeUInt 2 message.reasonCode
    ++ (encodeUInt 4 message.token
    ++ (Alpha.encode message.orderNumber
    ++ (encodeUInt 2 message.bookType
    ++ (encodeUInt 2 message.buySell
    ++ (encodeUInt 4 message.disclosedVolume
    ++ (encodeUInt 4 message.disclosedVolRemaining
    ++ (encodeUInt 4 message.totalVolRemaining
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.triggerPrice
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 4 message.traderId
    ++ (Alpha.encode message.nnfField
    ++ (encodeUInt 4 message.algoId
    ++ (encodeUInt 8 message.activityTimeInNanos
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (encodeUInt 2 message.auctionNumber
    ++ (Alpha.encode message.suspended
    ++ (Alpha.encode message.filler
    ++ (Alpha.encode message.pan
    ++ (Alpha.encode message.segmentChar1
    ++ (ParticipantType.encode message.participantType
    ++ (Alpha.encode message.accountNumber
    ++ (Alpha.encode message.proClientChar1
    ++ (SettlementType.encode message.settlementType
    ++ (Alpha.encode message.settlor)))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (BatchOrderCancelMessage × List UInt8) := do
  let (reasonCode, bytes) ← decodeUInt 2 bytes
  let (token, bytes) ← decodeUInt 4 bytes
  let (orderNumber, bytes) ← Alpha.decode 8 bytes
  let (bookType, bytes) ← decodeUInt 2 bytes
  let (buySell, bytes) ← decodeUInt 2 bytes
  let (disclosedVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolRemaining, bytes) ← decodeUInt 4 bytes
  let (totalVolRemaining, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (triggerPrice, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (activityTimeInNanos, bytes) ← decodeUInt 8 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (auctionNumber, bytes) ← decodeUInt 2 bytes
  let (suspended, bytes) ← Alpha.decode 1 bytes
  let (filler, bytes) ← Alpha.decode 1 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (segmentChar1, bytes) ← Alpha.decode 1 bytes
  let (participantType, bytes) ← ParticipantType.decode bytes
  let (accountNumber, bytes) ← Alpha.decode 10 bytes
  let (proClientChar1, bytes) ← Alpha.decode 1 bytes
  let (settlementType, bytes) ← SettlementType.decode bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  pure ({ reasonCode, token, orderNumber, bookType, buySell, disclosedVolume, disclosedVolRemaining, totalVolRemaining, volume, price, triggerPrice, stOrderFlags, traderId, nnfField, algoId, activityTimeInNanos, competitorPeriod, solicitorPeriod, auctionNumber, suspended, filler, pan, segmentChar1, participantType, accountNumber, proClientChar1, settlementType, settlor }, bytes)

@[simp] theorem encode_length (message : BatchOrderCancelMessage) : (encode message).length = 112 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, ParticipantType.encode_length, SettlementType.encode_length]

theorem encode_length_pos (message : BatchOrderCancelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : BatchOrderCancelMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, ParticipantType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SettlementType.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BatchOrderCancelMessage

/-- Any Server Message Payload, selected by Transaction Code -/
inductive ServerMessagePayload where
  | grResponseMessage (message : GrResponseMessage) -- 2401
  | grSecureUserRegistrationResponseMessage (message : GrSecureUserRegistrationResponseMessage) -- 23009
  | dcSignonOutMessage (message : DcSignonOutMessage) -- 2501
  | dcErrorResponseTradeMessage (message : DcErrorResponseTradeMessage) -- 8006
  | dcErrorResponseOrderMessage (message : DcErrorResponseOrderMessage) -- 9006
  | tradeConfirmationMessage (message : TradeConfirmationMessage) -- 2222
  | tradeCancelConfirmMessage (message : TradeCancelConfirmMessage) -- 2282
  | tradeCancelRejectMessage (message : TradeCancelRejectMessage) -- 2286
  | tradeModifyConfirmMessage (message : TradeModifyConfirmMessage) -- 2287
  | priceConfirmationMessage (message : PriceConfirmationMessage) -- 2012
  | orderModRejectMessage (message : OrderModRejectMessage) -- 2042
  | orderCancelRejectMessage (message : OrderCancelRejectMessage) -- 2072
  | orderConfirmationMessage (message : OrderConfirmationMessage) -- 2073
  | orderModConfirmationMessage (message : OrderModConfirmationMessage) -- 2074
  | orderCancelConfirmationMessage (message : OrderCancelConfirmationMessage) -- 2075
  | freezeToControlMessage (message : FreezeToControlMessage) -- 2170
  | onStopNotificationMessage (message : OnStopNotificationMessage) -- 2212
  | orderErrorMessage (message : OrderErrorMessage) -- 2231
  | batchOrderCancelMessage (message : BatchOrderCancelMessage) -- 9002
  deriving DecidableEq, Repr

namespace ServerMessagePayload

/-- The Transaction Code each message is sent under -/
def tag : ServerMessagePayload → BitVec 16
  | .grResponseMessage _ => 2401
  | .grSecureUserRegistrationResponseMessage _ => 23009
  | .dcSignonOutMessage _ => 2501
  | .dcErrorResponseTradeMessage _ => 8006
  | .dcErrorResponseOrderMessage _ => 9006
  | .tradeConfirmationMessage _ => 2222
  | .tradeCancelConfirmMessage _ => 2282
  | .tradeCancelRejectMessage _ => 2286
  | .tradeModifyConfirmMessage _ => 2287
  | .priceConfirmationMessage _ => 2012
  | .orderModRejectMessage _ => 2042
  | .orderCancelRejectMessage _ => 2072
  | .orderConfirmationMessage _ => 2073
  | .orderModConfirmationMessage _ => 2074
  | .orderCancelConfirmationMessage _ => 2075
  | .freezeToControlMessage _ => 2170
  | .onStopNotificationMessage _ => 2212
  | .orderErrorMessage _ => 2231
  | .batchOrderCancelMessage _ => 9002

def encode : ServerMessagePayload → List UInt8
  | .grResponseMessage message => GrResponseMessage.encode message
  | .grSecureUserRegistrationResponseMessage message => GrSecureUserRegistrationResponseMessage.encode message
  | .dcSignonOutMessage message => DcSignonOutMessage.encode message
  | .dcErrorResponseTradeMessage message => DcErrorResponseTradeMessage.encode message
  | .dcErrorResponseOrderMessage message => DcErrorResponseOrderMessage.encode message
  | .tradeConfirmationMessage message => TradeConfirmationMessage.encode message
  | .tradeCancelConfirmMessage message => TradeCancelConfirmMessage.encode message
  | .tradeCancelRejectMessage message => TradeCancelRejectMessage.encode message
  | .tradeModifyConfirmMessage message => TradeModifyConfirmMessage.encode message
  | .priceConfirmationMessage message => PriceConfirmationMessage.encode message
  | .orderModRejectMessage message => OrderModRejectMessage.encode message
  | .orderCancelRejectMessage message => OrderCancelRejectMessage.encode message
  | .orderConfirmationMessage message => OrderConfirmationMessage.encode message
  | .orderModConfirmationMessage message => OrderModConfirmationMessage.encode message
  | .orderCancelConfirmationMessage message => OrderCancelConfirmationMessage.encode message
  | .freezeToControlMessage message => FreezeToControlMessage.encode message
  | .onStopNotificationMessage message => OnStopNotificationMessage.encode message
  | .orderErrorMessage message => OrderErrorMessage.encode message
  | .batchOrderCancelMessage message => BatchOrderCancelMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ServerMessagePayload) : (encode message).length ≤ 128 := by
  cases message with
  | grResponseMessage inner =>
    simp only [encode, GrResponseMessage.encode_length]
    omega
  | grSecureUserRegistrationResponseMessage inner =>
    simp only [encode, GrSecureUserRegistrationResponseMessage.encode_length]
    omega
  | dcSignonOutMessage inner =>
    simp only [encode, DcSignonOutMessage.encode_length]
    omega
  | dcErrorResponseTradeMessage inner =>
    simp only [encode, DcErrorResponseTradeMessage.encode_length]
    omega
  | dcErrorResponseOrderMessage inner =>
    simp only [encode, DcErrorResponseOrderMessage.encode_length]
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
  | priceConfirmationMessage inner =>
    simp only [encode, PriceConfirmationMessage.encode_length]
    omega
  | orderModRejectMessage inner =>
    simp only [encode, OrderModRejectMessage.encode_length]
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
  | onStopNotificationMessage inner =>
    simp only [encode, OnStopNotificationMessage.encode_length]
    omega
  | orderErrorMessage inner =>
    simp only [encode, OrderErrorMessage.encode_length]
    omega
  | batchOrderCancelMessage inner =>
    simp only [encode, BatchOrderCancelMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (ServerMessagePayload × List UInt8) :=
  if tag = 2401 then (GrResponseMessage.decode bytes).map fun (message, rest) => (.grResponseMessage message, rest)
  else if tag = 23009 then (GrSecureUserRegistrationResponseMessage.decode bytes).map fun (message, rest) => (.grSecureUserRegistrationResponseMessage message, rest)
  else if tag = 2501 then (DcSignonOutMessage.decode bytes).map fun (message, rest) => (.dcSignonOutMessage message, rest)
  else if tag = 8006 then (DcErrorResponseTradeMessage.decode bytes).map fun (message, rest) => (.dcErrorResponseTradeMessage message, rest)
  else if tag = 9006 then (DcErrorResponseOrderMessage.decode bytes).map fun (message, rest) => (.dcErrorResponseOrderMessage message, rest)
  else if tag = 2222 then (TradeConfirmationMessage.decode bytes).map fun (message, rest) => (.tradeConfirmationMessage message, rest)
  else if tag = 2282 then (TradeCancelConfirmMessage.decode bytes).map fun (message, rest) => (.tradeCancelConfirmMessage message, rest)
  else if tag = 2286 then (TradeCancelRejectMessage.decode bytes).map fun (message, rest) => (.tradeCancelRejectMessage message, rest)
  else if tag = 2287 then (TradeModifyConfirmMessage.decode bytes).map fun (message, rest) => (.tradeModifyConfirmMessage message, rest)
  else if tag = 2012 then (PriceConfirmationMessage.decode bytes).map fun (message, rest) => (.priceConfirmationMessage message, rest)
  else if tag = 2042 then (OrderModRejectMessage.decode bytes).map fun (message, rest) => (.orderModRejectMessage message, rest)
  else if tag = 2072 then (OrderCancelRejectMessage.decode bytes).map fun (message, rest) => (.orderCancelRejectMessage message, rest)
  else if tag = 2073 then (OrderConfirmationMessage.decode bytes).map fun (message, rest) => (.orderConfirmationMessage message, rest)
  else if tag = 2074 then (OrderModConfirmationMessage.decode bytes).map fun (message, rest) => (.orderModConfirmationMessage message, rest)
  else if tag = 2075 then (OrderCancelConfirmationMessage.decode bytes).map fun (message, rest) => (.orderCancelConfirmationMessage message, rest)
  else if tag = 2170 then (FreezeToControlMessage.decode bytes).map fun (message, rest) => (.freezeToControlMessage message, rest)
  else if tag = 2212 then (OnStopNotificationMessage.decode bytes).map fun (message, rest) => (.onStopNotificationMessage message, rest)
  else if tag = 2231 then (OrderErrorMessage.decode bytes).map fun (message, rest) => (.orderErrorMessage message, rest)
  else if tag = 9002 then (BatchOrderCancelMessage.decode bytes).map fun (message, rest) => (.batchOrderCancelMessage message, rest)
  else none

@[simp] theorem decode_encode (message : ServerMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ServerMessagePayload

/-- Server Message -/
structure ServerMessage where
  errorCode : BitVec 16
  sequenceNumber : BitVec 64
  serverMessagePayload : ServerMessagePayload
  deriving DecidableEq, Repr

namespace ServerMessage

def encodeBody (message : ServerMessage) : List UInt8 :=
  ServerMessagePayload.encode message.serverMessagePayload

def decodeBody (transactionCode : BitVec 16) (errorCode : BitVec 16) (sequenceNumber : BitVec 64) (bytes : List UInt8) : Option (ServerMessage × List UInt8) := do
  let (serverMessagePayload, bytes) ← ServerMessagePayload.decode transactionCode bytes
  pure ({ errorCode, sequenceNumber, serverMessagePayload }, bytes)

theorem decodeBody_encodeBody (message : ServerMessage) (rest : List UInt8) :
    decodeBody (ServerMessagePayload.tag message.serverMessagePayload) message.errorCode message.sequenceNumber (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [ServerMessagePayload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : ServerMessage) : (encodeBody message).length + 14 < 256 ^ 2 := by
  unfold encodeBody
  cases message.serverMessagePayload with
  | grResponseMessage inner =>
    simp only [ServerMessagePayload.encode, GrResponseMessage.encode_length]
    omega
  | grSecureUserRegistrationResponseMessage inner =>
    simp only [ServerMessagePayload.encode, GrSecureUserRegistrationResponseMessage.encode_length]
    omega
  | dcSignonOutMessage inner =>
    simp only [ServerMessagePayload.encode, DcSignonOutMessage.encode_length]
    omega
  | dcErrorResponseTradeMessage inner =>
    simp only [ServerMessagePayload.encode, DcErrorResponseTradeMessage.encode_length]
    omega
  | dcErrorResponseOrderMessage inner =>
    simp only [ServerMessagePayload.encode, DcErrorResponseOrderMessage.encode_length]
    omega
  | tradeConfirmationMessage inner =>
    simp only [ServerMessagePayload.encode, TradeConfirmationMessage.encode_length]
    omega
  | tradeCancelConfirmMessage inner =>
    simp only [ServerMessagePayload.encode, TradeCancelConfirmMessage.encode_length]
    omega
  | tradeCancelRejectMessage inner =>
    simp only [ServerMessagePayload.encode, TradeCancelRejectMessage.encode_length]
    omega
  | tradeModifyConfirmMessage inner =>
    simp only [ServerMessagePayload.encode, TradeModifyConfirmMessage.encode_length]
    omega
  | priceConfirmationMessage inner =>
    simp only [ServerMessagePayload.encode, PriceConfirmationMessage.encode_length]
    omega
  | orderModRejectMessage inner =>
    simp only [ServerMessagePayload.encode, OrderModRejectMessage.encode_length]
    omega
  | orderCancelRejectMessage inner =>
    simp only [ServerMessagePayload.encode, OrderCancelRejectMessage.encode_length]
    omega
  | orderConfirmationMessage inner =>
    simp only [ServerMessagePayload.encode, OrderConfirmationMessage.encode_length]
    omega
  | orderModConfirmationMessage inner =>
    simp only [ServerMessagePayload.encode, OrderModConfirmationMessage.encode_length]
    omega
  | orderCancelConfirmationMessage inner =>
    simp only [ServerMessagePayload.encode, OrderCancelConfirmationMessage.encode_length]
    omega
  | freezeToControlMessage inner =>
    simp only [ServerMessagePayload.encode, FreezeToControlMessage.encode_length]
    omega
  | onStopNotificationMessage inner =>
    simp only [ServerMessagePayload.encode, OnStopNotificationMessage.encode_length]
    omega
  | orderErrorMessage inner =>
    simp only [ServerMessagePayload.encode, OrderErrorMessage.encode_length]
    omega
  | batchOrderCancelMessage inner =>
    simp only [ServerMessagePayload.encode, BatchOrderCancelMessage.encode_length]
    omega

/-- Size rule: Message Length counts the bytes after it plus 14, so it is written from the body and checked on decode; Transaction Code, Error Code, Sequence Number are read ahead of it -/
def encode (message : ServerMessage) : List UInt8 :=
  encodeUInt 2 (ServerMessagePayload.tag message.serverMessagePayload)
    ++ (encodeUInt 2 message.errorCode
    ++ (encodeUInt 8 message.sequenceNumber
    ++ (encodeFramed 2 14 encodeBody message)))

def decode (bytes : List UInt8) : Option (ServerMessage × List UInt8) := do
  let (transactionCode, bytes) ← decodeUInt 2 bytes
  let (errorCode, bytes) ← decodeUInt 2 bytes
  let (sequenceNumber, bytes) ← decodeUInt 8 bytes
  decodeFramed 2 14 (decodeBody transactionCode errorCode sequenceNumber) bytes

@[simp] theorem decode_encode (message : ServerMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  exact decodeFramed_encodeFramed 2 14 encodeBody (decodeBody (ServerMessagePayload.tag message.serverMessagePayload) message.errorCode message.sequenceNumber) message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : ServerMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc, encodeFramed_length]
  omega

end ServerMessage

/-- Message Buffer -/
structure MessageBuffer where
  serverMessage : List ServerMessage
  deriving DecidableEq, Repr

namespace MessageBuffer

def encode (message : MessageBuffer) : List UInt8 :=
  encodeMany ServerMessage.encode message.serverMessage

def decode (bytes : List UInt8) : Option MessageBuffer := do
  let serverMessage ← decodeAll ServerMessage.decode bytes.length bytes
  pure { serverMessage }

theorem decode_encode (message : MessageBuffer) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany ServerMessage.encode ServerMessage.decode ServerMessage.decode_encode ServerMessage.encode_length_pos message.serverMessage _ (encodeMany_length_ge ServerMessage.encode ServerMessage.encode_length_pos message.serverMessage), some_bind]
  rfl

end MessageBuffer

/-- Message Buffer -/
structure MessageBufferLz4 where
  payload : Capped 65511
  deriving DecidableEq, Repr

namespace MessageBufferLz4

def encode (message : MessageBufferLz4) : List UInt8 :=
  message.payload.val

def decode (bytes : List UInt8) : Option MessageBufferLz4 := do
  let payload_ := bytes
  if fits_payload : payload_.length ≤ 65511 then
    pure { payload := ⟨payload_, fits_payload⟩ }
  else none

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MessageBufferLz4) : (encode message).length ≤ 65511 := by
  have bound_payload := message.payload.length_le
  unfold encode
  omega

theorem decode_encode (message : MessageBufferLz4) : decode (encode message) = some message := by
  unfold decode encode
  rw [dite_eq_left message.payload.length_le]
  rfl

end MessageBufferLz4

/-- The Message Buffer, as bytes when Compression Indicator says it was LZ4 transformed and as it lies when it says it was not -/
inductive MessageBufferBody where
  | lz4 (tag : { v : CompressionIndicator // v = CompressionIndicator.dataIsCompressed }) (message : MessageBufferLz4) -- tag = CompressionIndicator.dataIsCompressed
  | plain (tag : { v : CompressionIndicator // ¬ (v = CompressionIndicator.dataIsCompressed) }) (message : MessageBuffer) -- every other value
  deriving DecidableEq, Repr

namespace MessageBufferBody

/-- The Compression Indicator each body is read by -/
def tag : MessageBufferBody → CompressionIndicator
  | .lz4 tag _ => tag.val
  | .plain tag _ => tag.val

def encode : MessageBufferBody → List UInt8
  | .lz4 _ message => MessageBufferLz4.encode message
  | .plain _ message => MessageBuffer.encode message

/-- Decoded from the whole of what holds it: a body that reads to its end takes it all, any other must leave nothing -/
def decode (tag : CompressionIndicator) (bytes : List UInt8) : Option MessageBufferBody :=
  if h : tag = CompressionIndicator.dataIsCompressed then (MessageBufferLz4.decode bytes).map fun message => .lz4 ⟨tag, h⟩ message
  else (MessageBuffer.decode bytes).map fun message => .plain ⟨tag, h⟩ message

theorem decode_encode (message : MessageBufferBody) :
    decode (tag message) (encode message) = some message := by
  cases message with
  | lz4 t m =>
    obtain ⟨v, h⟩ := t
    simp only [tag, encode, decode, h, reduceDIte, MessageBufferLz4.decode_encode, Option.map_some]
  | plain t m =>
    obtain ⟨v, h⟩ := t
    simp only [tag, encode, decode, h, reduceDIte, MessageBuffer.decode_encode, Option.map_some]

end MessageBufferBody

/-- Server Drop Copy Packet: the body, which the record carries with the proof it fits its frame -/
structure ServerDropCopyPacketBody where
  packetSequenceNumber : BitVec 32
  checksum : Alpha 16
  environmentType : EnvironmentType
  messageBuffer : MessageBufferBody
  deriving DecidableEq, Repr

namespace ServerDropCopyPacketBody

def encodeBody (message : ServerDropCopyPacketBody) : List UInt8 :=
  encodeUInt 4 message.packetSequenceNumber
    ++ (Alpha.encode message.checksum
    ++ (EnvironmentType.encode message.environmentType
    ++ (CompressionIndicator.encode (MessageBufferBody.tag message.messageBuffer)
    ++ (MessageBufferBody.encode message.messageBuffer))))

def decodeBody (bytes : List UInt8) : Option ServerDropCopyPacketBody := do
  let (packetSequenceNumber, bytes) ← decodeUInt 4 bytes
  let (checksum, bytes) ← Alpha.decode 16 bytes
  let (environmentType, bytes) ← EnvironmentType.decode bytes
  let (compressionIndicator, bytes) ← CompressionIndicator.decode bytes
  let messageBuffer ← MessageBufferBody.decode compressionIndicator bytes
  pure { packetSequenceNumber, checksum, environmentType, messageBuffer }

theorem decodeBody_encodeBody (message : ServerDropCopyPacketBody) : decodeBody (encodeBody message) = some message := by
  unfold decodeBody encodeBody
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [EnvironmentType.decode_encode, some_bind]
  dsimp only
  rw [CompressionIndicator.decode_encode, some_bind]
  dsimp only
  rw [MessageBufferBody.decode_encode, some_bind]
  rfl

end ServerDropCopyPacketBody

/-- Server Drop Copy Packet: the body with the proof its encoding fits Packet Length, whose 2 bytes no bound of the fields fits -/
abbrev ServerDropCopyPacket := Fitting ServerDropCopyPacketBody.encodeBody 2 65536

namespace ServerDropCopyPacket

def encode (message : ServerDropCopyPacket) : List UInt8 :=
  encodeFramed 2 2 ServerDropCopyPacketBody.encodeBody message.val

def decode : List UInt8 → Option (ServerDropCopyPacket × List UInt8) :=
  decodeFittingAll 2 2 ServerDropCopyPacketBody.encodeBody ServerDropCopyPacketBody.decodeBody

@[simp] theorem decode_encode (message : ServerDropCopyPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFittingAll_encodeFramed 2 2 ServerDropCopyPacketBody.encodeBody ServerDropCopyPacketBody.decodeBody message (ServerDropCopyPacketBody.decodeBody_encodeBody message.val) rest

theorem encode_length_pos (message : ServerDropCopyPacket) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

/-- The most bytes an encoding can take: what the prefix can count, by the fit the message carries -/
theorem encode_length_le (message : ServerDropCopyPacket) : (encode message).length ≤ 65535 := by
  have fits := message.fits
  unfold encode
  rw [encodeFramed_length]
  omega

end ServerDropCopyPacket

/-- Server Packet -/
structure ServerPacket where
  serverDropCopyPacket : List ServerDropCopyPacket
  deriving DecidableEq, Repr

namespace ServerPacket

def encode (message : ServerPacket) : List UInt8 :=
  encodeMany ServerDropCopyPacket.encode message.serverDropCopyPacket

def decode (bytes : List UInt8) : Option ServerPacket := do
  let serverDropCopyPacket ← decodeAll ServerDropCopyPacket.decode bytes.length bytes
  pure { serverDropCopyPacket }

theorem decode_encode (message : ServerPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany ServerDropCopyPacket.encode ServerDropCopyPacket.decode ServerDropCopyPacket.decode_encode ServerDropCopyPacket.encode_length_pos message.serverDropCopyPacket _ (encodeMany_length_ge ServerDropCopyPacket.encode ServerDropCopyPacket.encode_length_pos message.serverDropCopyPacket), some_bind]
  rfl

end ServerPacket

end Omi.NseNsecmDropcopyNnfdcV30Server
