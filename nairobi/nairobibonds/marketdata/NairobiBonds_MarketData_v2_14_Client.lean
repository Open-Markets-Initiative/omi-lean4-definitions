import Wire

/-!
# Nairobi Securities Exchange Nairobi Bonds Market Data v2.14

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.

Note: Request Data Retrieval Message is selected by more than one code: each is a constructor of its
own over the one record, so the code read is the code written back

Note: Client Message is not framed: its size rule is not the length plus a constant the frame proof
covers

License: MIT No Attribution
-/

namespace Omi.NairobiNairobibondsMarketdataMitsV214Client

/-- User Name: 16 bytes -/
structure UserName where
  userNameLengthByte : BitVec 8
  userNameCharacters : Alpha 15
  deriving DecidableEq, Repr

namespace UserName

def encode (message : UserName) : List UInt8 :=
  encodeUInt 1 message.userNameLengthByte
    ++ (Alpha.encode message.userNameCharacters)

def decode (bytes : List UInt8) : Option (UserName × List UInt8) := do
  let (userNameLengthByte, bytes) ← decodeUInt 1 bytes
  let (userNameCharacters, bytes) ← Alpha.decode 15 bytes
  pure ({ userNameLengthByte, userNameCharacters }, bytes)

@[simp] theorem encode_length (message : UserName) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : UserName) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UserName) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end UserName

/-- Time: 4 bytes -/
structure Time where
  hours : BitVec 8
  minutes : BitVec 8
  seconds : BitVec 8
  unused1 : Alpha 1
  deriving DecidableEq, Repr

namespace Time

def encode (message : Time) : List UInt8 :=
  encodeUInt 1 message.hours
    ++ (encodeUInt 1 message.minutes
    ++ (encodeUInt 1 message.seconds
    ++ (Alpha.encode message.unused1)))

def decode (bytes : List UInt8) : Option (Time × List UInt8) := do
  let (hours, bytes) ← decodeUInt 1 bytes
  let (minutes, bytes) ← decodeUInt 1 bytes
  let (seconds, bytes) ← decodeUInt 1 bytes
  let (unused1, bytes) ← Alpha.decode 1 bytes
  pure ({ hours, minutes, seconds, unused1 }, bytes)

@[simp] theorem encode_length (message : Time) : (encode message).length = 4 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : Time) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Time) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end Time

/-- Log In Message: 624 bytes -/
structure LogInMessage where
  encryptedPassword : Alpha 312
  newPassword : Alpha 312
  deriving DecidableEq, Repr

namespace LogInMessage

def encode (message : LogInMessage) : List UInt8 :=
  Alpha.encode message.encryptedPassword
    ++ (Alpha.encode message.newPassword)

def decode (bytes : List UInt8) : Option (LogInMessage × List UInt8) := do
  let (encryptedPassword, bytes) ← Alpha.decode 312 bytes
  let (newPassword, bytes) ← Alpha.decode 312 bytes
  pure ({ encryptedPassword, newPassword }, bytes)

@[simp] theorem encode_length (message : LogInMessage) : (encode message).length = 624 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : LogInMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogInMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LogInMessage

/-- Re Request Message: 12 bytes -/
structure ReRequestMessage where
  fromSequence : BitVec 32
  toSequence : BitVec 32
  marketShardNumberI4 : BitVec 32
  deriving DecidableEq, Repr

namespace ReRequestMessage

def encode (message : ReRequestMessage) : List UInt8 :=
  encodeUIntLE 4 message.fromSequence
    ++ (encodeUIntLE 4 message.toSequence
    ++ (encodeUIntLE 4 message.marketShardNumberI4))

def decode (bytes : List UInt8) : Option (ReRequestMessage × List UInt8) := do
  let (fromSequence, bytes) ← decodeUIntLE 4 bytes
  let (toSequence, bytes) ← decodeUIntLE 4 bytes
  let (marketShardNumberI4, bytes) ← decodeUIntLE 4 bytes
  pure ({ fromSequence, toSequence, marketShardNumberI4 }, bytes)

@[simp] theorem encode_length (message : ReRequestMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : ReRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ReRequestMessage

/-- Log Out Message: 0 bytes -/
structure LogOutMessage where
  deriving DecidableEq, Repr

namespace LogOutMessage

def encode (_ : LogOutMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (LogOutMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : LogOutMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : LogOutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end LogOutMessage

/-- Download Date: 12 bytes -/
structure DownloadDate where
  year : BitVec 32
  month : BitVec 32
  day : BitVec 32
  deriving DecidableEq, Repr

namespace DownloadDate

def encode (message : DownloadDate) : List UInt8 :=
  encodeUIntLE 4 message.year
    ++ (encodeUIntLE 4 message.month
    ++ (encodeUIntLE 4 message.day))

def decode (bytes : List UInt8) : Option (DownloadDate × List UInt8) := do
  let (year, bytes) ← decodeUIntLE 4 bytes
  let (month, bytes) ← decodeUIntLE 4 bytes
  let (day, bytes) ← decodeUIntLE 4 bytes
  pure ({ year, month, day }, bytes)

@[simp] theorem encode_length (message : DownloadDate) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : DownloadDate) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DownloadDate) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end DownloadDate

/-- Request Data Retrieval Message: 24 bytes -/
structure RequestDataRetrievalMessage where
  dataType : BitVec 8
  unused1 : Alpha 1
  lastPieceOfChunk : BitVec 8
  reRequest : BitVec 8
  action : BitVec 32
  specificRecord : BitVec 32
  downloadDate : DownloadDate
  deriving DecidableEq, Repr

namespace RequestDataRetrievalMessage

def encode (message : RequestDataRetrievalMessage) : List UInt8 :=
  encodeUInt 1 message.dataType
    ++ (Alpha.encode message.unused1
    ++ (encodeUInt 1 message.lastPieceOfChunk
    ++ (encodeUInt 1 message.reRequest
    ++ (encodeUIntLE 4 message.action
    ++ (encodeUIntLE 4 message.specificRecord
    ++ (DownloadDate.encode message.downloadDate))))))

def decode (bytes : List UInt8) : Option (RequestDataRetrievalMessage × List UInt8) := do
  let (dataType, bytes) ← decodeUInt 1 bytes
  let (unused1, bytes) ← Alpha.decode 1 bytes
  let (lastPieceOfChunk, bytes) ← decodeUInt 1 bytes
  let (reRequest, bytes) ← decodeUInt 1 bytes
  let (action, bytes) ← decodeUIntLE 4 bytes
  let (specificRecord, bytes) ← decodeUIntLE 4 bytes
  let (downloadDate, bytes) ← DownloadDate.decode bytes
  pure ({ dataType, unused1, lastPieceOfChunk, reRequest, action, specificRecord, downloadDate }, bytes)

@[simp] theorem encode_length (message : RequestDataRetrievalMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, encodeUIntLE_length, DownloadDate.encode_length]

theorem encode_length_pos (message : RequestDataRetrievalMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RequestDataRetrievalMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [DownloadDate.decode_encode, some_bind]
  rfl

end RequestDataRetrievalMessage

/-- Date: 12 bytes -/
structure Date where
  year : BitVec 32
  month : BitVec 32
  day : BitVec 32
  deriving DecidableEq, Repr

namespace Date

def encode (message : Date) : List UInt8 :=
  encodeUIntLE 4 message.year
    ++ (encodeUIntLE 4 message.month
    ++ (encodeUIntLE 4 message.day))

def decode (bytes : List UInt8) : Option (Date × List UInt8) := do
  let (year, bytes) ← decodeUIntLE 4 bytes
  let (month, bytes) ← decodeUIntLE 4 bytes
  let (day, bytes) ← decodeUIntLE 4 bytes
  pure ({ year, month, day }, bytes)

@[simp] theorem encode_length (message : Date) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : Date) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Date) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end Date

/-- Instrument Name P 5: 5 bytes -/
structure InstrumentNameP5 where
  instrumentNameP5LengthByte : BitVec 8
  instrumentNameP5Characters : Alpha 4
  deriving DecidableEq, Repr

namespace InstrumentNameP5

def encode (message : InstrumentNameP5) : List UInt8 :=
  encodeUInt 1 message.instrumentNameP5LengthByte
    ++ (Alpha.encode message.instrumentNameP5Characters)

def decode (bytes : List UInt8) : Option (InstrumentNameP5 × List UInt8) := do
  let (instrumentNameP5LengthByte, bytes) ← decodeUInt 1 bytes
  let (instrumentNameP5Characters, bytes) ← Alpha.decode 4 bytes
  pure ({ instrumentNameP5LengthByte, instrumentNameP5Characters }, bytes)

@[simp] theorem encode_length (message : InstrumentNameP5) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : InstrumentNameP5) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentNameP5) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end InstrumentNameP5

/-- Secondary Date: 12 bytes -/
structure SecondaryDate where
  year : BitVec 32
  month : BitVec 32
  day : BitVec 32
  deriving DecidableEq, Repr

namespace SecondaryDate

def encode (message : SecondaryDate) : List UInt8 :=
  encodeUIntLE 4 message.year
    ++ (encodeUIntLE 4 message.month
    ++ (encodeUIntLE 4 message.day))

def decode (bytes : List UInt8) : Option (SecondaryDate × List UInt8) := do
  let (year, bytes) ← decodeUIntLE 4 bytes
  let (month, bytes) ← decodeUIntLE 4 bytes
  let (day, bytes) ← decodeUIntLE 4 bytes
  pure ({ year, month, day }, bytes)

@[simp] theorem encode_length (message : SecondaryDate) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : SecondaryDate) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecondaryDate) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SecondaryDate

/-- Secondary Instrument Name P 5: 5 bytes -/
structure SecondaryInstrumentNameP5 where
  secondaryInstrumentNameP5LengthByte : BitVec 8
  secondaryInstrumentNameP5Characters : Alpha 4
  deriving DecidableEq, Repr

namespace SecondaryInstrumentNameP5

def encode (message : SecondaryInstrumentNameP5) : List UInt8 :=
  encodeUInt 1 message.secondaryInstrumentNameP5LengthByte
    ++ (Alpha.encode message.secondaryInstrumentNameP5Characters)

def decode (bytes : List UInt8) : Option (SecondaryInstrumentNameP5 × List UInt8) := do
  let (secondaryInstrumentNameP5LengthByte, bytes) ← decodeUInt 1 bytes
  let (secondaryInstrumentNameP5Characters, bytes) ← Alpha.decode 4 bytes
  pure ({ secondaryInstrumentNameP5LengthByte, secondaryInstrumentNameP5Characters }, bytes)

@[simp] theorem encode_length (message : SecondaryInstrumentNameP5) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : SecondaryInstrumentNameP5) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecondaryInstrumentNameP5) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SecondaryInstrumentNameP5

/-- Contract: 48 bytes -/
structure Contract where
  identifierPrefixI4 : BitVec 32
  date : Date
  instrumentNameP5 : InstrumentNameP5
  strike : Alpha 8
  callPutC1 : Alpha 1
  secondaryDate : SecondaryDate
  secondaryInstrumentNameP5 : SecondaryInstrumentNameP5
  isDeltaOption : BitVec 8
  deriving DecidableEq, Repr

namespace Contract

def encode (message : Contract) : List UInt8 :=
  encodeUIntLE 4 message.identifierPrefixI4
    ++ (Date.encode message.date
    ++ (InstrumentNameP5.encode message.instrumentNameP5
    ++ (Alpha.encode message.strike
    ++ (Alpha.encode message.callPutC1
    ++ (SecondaryDate.encode message.secondaryDate
    ++ (SecondaryInstrumentNameP5.encode message.secondaryInstrumentNameP5
    ++ (encodeUInt 1 message.isDeltaOption)))))))

def decode (bytes : List UInt8) : Option (Contract × List UInt8) := do
  let (identifierPrefixI4, bytes) ← decodeUIntLE 4 bytes
  let (date, bytes) ← Date.decode bytes
  let (instrumentNameP5, bytes) ← InstrumentNameP5.decode bytes
  let (strike, bytes) ← Alpha.decode 8 bytes
  let (callPutC1, bytes) ← Alpha.decode 1 bytes
  let (secondaryDate, bytes) ← SecondaryDate.decode bytes
  let (secondaryInstrumentNameP5, bytes) ← SecondaryInstrumentNameP5.decode bytes
  let (isDeltaOption, bytes) ← decodeUInt 1 bytes
  pure ({ identifierPrefixI4, date, instrumentNameP5, strike, callPutC1, secondaryDate, secondaryInstrumentNameP5, isDeltaOption }, bytes)

@[simp] theorem encode_length (message : Contract) : (encode message).length = 48 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Date.encode_length, InstrumentNameP5.encode_length, Alpha.encode_length, SecondaryDate.encode_length, SecondaryInstrumentNameP5.encode_length, encodeUInt_length]

theorem encode_length_pos (message : Contract) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Contract) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Date.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentNameP5.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecondaryDate.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecondaryInstrumentNameP5.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end Contract

/-- Contracts To Unsubscribe: 48 bytes -/
structure ContractsToUnsubscribe where
  contract : Contract
  deriving DecidableEq, Repr

namespace ContractsToUnsubscribe

def encode (message : ContractsToUnsubscribe) : List UInt8 :=
  Contract.encode message.contract

def decode (bytes : List UInt8) : Option (ContractsToUnsubscribe × List UInt8) := do
  let (contract, bytes) ← Contract.decode bytes
  pure ({ contract }, bytes)

@[simp] theorem encode_length (message : ContractsToUnsubscribe) : (encode message).length = 48 := by
  unfold encode
  simp only [Contract.encode_length]

theorem encode_length_pos (message : ContractsToUnsubscribe) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ContractsToUnsubscribe) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Contract.decode_encode, some_bind]
  rfl

end ContractsToUnsubscribe

/-- Unsubscribe Contract Message: 1922 bytes -/
structure UnsubscribeContractMessage where
  quantityI2 : BitVec 16
  contractsToUnsubscribe : Exact 40 ContractsToUnsubscribe
  deriving DecidableEq, Repr

namespace UnsubscribeContractMessage

def encode (message : UnsubscribeContractMessage) : List UInt8 :=
  encodeUIntLE 2 message.quantityI2
    ++ (encodeMany ContractsToUnsubscribe.encode message.contractsToUnsubscribe.val)

def decode (bytes : List UInt8) : Option (UnsubscribeContractMessage × List UInt8) := do
  let (quantityI2, bytes) ← decodeUIntLE 2 bytes
  let (contractsToUnsubscribe_, bytes) ← decodeMany ContractsToUnsubscribe.decode 40 bytes
  if fits_contractsToUnsubscribe : contractsToUnsubscribe_.length = 40 then
    pure ({ quantityI2, contractsToUnsubscribe := ⟨contractsToUnsubscribe_, fits_contractsToUnsubscribe⟩ }, bytes)
  else none

@[simp] theorem encode_length (message : UnsubscribeContractMessage) : (encode message).length = 1922 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeMany_length_const ContractsToUnsubscribe.encode 48 ContractsToUnsubscribe.encode_length, message.contractsToUnsubscribe.length_eq]

theorem encode_length_pos (message : UnsubscribeContractMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UnsubscribeContractMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_exact 40 ContractsToUnsubscribe.encode ContractsToUnsubscribe.decode ContractsToUnsubscribe.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.contractsToUnsubscribe.length_eq]
  rfl

end UnsubscribeContractMessage

/-- Contract Name: 48 bytes -/
structure ContractName where
  identifierPrefixI4 : BitVec 32
  date : Date
  instrumentNameP5 : InstrumentNameP5
  strike : Alpha 8
  callPutC1 : Alpha 1
  secondaryDate : SecondaryDate
  secondaryInstrumentNameP5 : SecondaryInstrumentNameP5
  isDeltaOption : BitVec 8
  deriving DecidableEq, Repr

namespace ContractName

def encode (message : ContractName) : List UInt8 :=
  encodeUIntLE 4 message.identifierPrefixI4
    ++ (Date.encode message.date
    ++ (InstrumentNameP5.encode message.instrumentNameP5
    ++ (Alpha.encode message.strike
    ++ (Alpha.encode message.callPutC1
    ++ (SecondaryDate.encode message.secondaryDate
    ++ (SecondaryInstrumentNameP5.encode message.secondaryInstrumentNameP5
    ++ (encodeUInt 1 message.isDeltaOption)))))))

def decode (bytes : List UInt8) : Option (ContractName × List UInt8) := do
  let (identifierPrefixI4, bytes) ← decodeUIntLE 4 bytes
  let (date, bytes) ← Date.decode bytes
  let (instrumentNameP5, bytes) ← InstrumentNameP5.decode bytes
  let (strike, bytes) ← Alpha.decode 8 bytes
  let (callPutC1, bytes) ← Alpha.decode 1 bytes
  let (secondaryDate, bytes) ← SecondaryDate.decode bytes
  let (secondaryInstrumentNameP5, bytes) ← SecondaryInstrumentNameP5.decode bytes
  let (isDeltaOption, bytes) ← decodeUInt 1 bytes
  pure ({ identifierPrefixI4, date, instrumentNameP5, strike, callPutC1, secondaryDate, secondaryInstrumentNameP5, isDeltaOption }, bytes)

@[simp] theorem encode_length (message : ContractName) : (encode message).length = 48 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Date.encode_length, InstrumentNameP5.encode_length, Alpha.encode_length, SecondaryDate.encode_length, SecondaryInstrumentNameP5.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ContractName) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ContractName) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Date.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentNameP5.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecondaryDate.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecondaryInstrumentNameP5.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ContractName

/-- Request Daily Trend Message: 48 bytes -/
structure RequestDailyTrendMessage where
  contractName : ContractName
  deriving DecidableEq, Repr

namespace RequestDailyTrendMessage

def encode (message : RequestDailyTrendMessage) : List UInt8 :=
  ContractName.encode message.contractName

def decode (bytes : List UInt8) : Option (RequestDailyTrendMessage × List UInt8) := do
  let (contractName, bytes) ← ContractName.decode bytes
  pure ({ contractName }, bytes)

@[simp] theorem encode_length (message : RequestDailyTrendMessage) : (encode message).length = 48 := by
  unfold encode
  simp only [ContractName.encode_length]

theorem encode_length_pos (message : RequestDailyTrendMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RequestDailyTrendMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [ContractName.decode_encode, some_bind]
  rfl

end RequestDailyTrendMessage

/-- Option Contract Subscription Message: 48 bytes -/
structure OptionContractSubscriptionMessage where
  contractName : ContractName
  deriving DecidableEq, Repr

namespace OptionContractSubscriptionMessage

def encode (message : OptionContractSubscriptionMessage) : List UInt8 :=
  ContractName.encode message.contractName

def decode (bytes : List UInt8) : Option (OptionContractSubscriptionMessage × List UInt8) := do
  let (contractName, bytes) ← ContractName.decode bytes
  pure ({ contractName }, bytes)

@[simp] theorem encode_length (message : OptionContractSubscriptionMessage) : (encode message).length = 48 := by
  unfold encode
  simp only [ContractName.encode_length]

theorem encode_length_pos (message : OptionContractSubscriptionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionContractSubscriptionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [ContractName.decode_encode, some_bind]
  rfl

end OptionContractSubscriptionMessage

/-- Heart Beats Message: 0 bytes -/
structure HeartBeatsMessage where
  deriving DecidableEq, Repr

namespace HeartBeatsMessage

def encode (_ : HeartBeatsMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (HeartBeatsMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : HeartBeatsMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : HeartBeatsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end HeartBeatsMessage

/-- Subscribing To Indices Service Message: 1 bytes -/
structure SubscribingToIndicesServiceMessage where
  subscribe : BitVec 8
  deriving DecidableEq, Repr

namespace SubscribingToIndicesServiceMessage

def encode (message : SubscribingToIndicesServiceMessage) : List UInt8 :=
  encodeUInt 1 message.subscribe

def decode (bytes : List UInt8) : Option (SubscribingToIndicesServiceMessage × List UInt8) := do
  let (subscribe, bytes) ← decodeUInt 1 bytes
  pure ({ subscribe }, bytes)

@[simp] theorem encode_length (message : SubscribingToIndicesServiceMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : SubscribingToIndicesServiceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SubscribingToIndicesServiceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SubscribingToIndicesServiceMessage

/-- Contracts Requested For Display: 48 bytes -/
structure ContractsRequestedForDisplay where
  contract : Contract
  deriving DecidableEq, Repr

namespace ContractsRequestedForDisplay

def encode (message : ContractsRequestedForDisplay) : List UInt8 :=
  Contract.encode message.contract

def decode (bytes : List UInt8) : Option (ContractsRequestedForDisplay × List UInt8) := do
  let (contract, bytes) ← Contract.decode bytes
  pure ({ contract }, bytes)

@[simp] theorem encode_length (message : ContractsRequestedForDisplay) : (encode message).length = 48 := by
  unfold encode
  simp only [Contract.encode_length]

theorem encode_length_pos (message : ContractsRequestedForDisplay) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ContractsRequestedForDisplay) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Contract.decode_encode, some_bind]
  rfl

end ContractsRequestedForDisplay

/-- Future Contract Subscription Message: 1922 bytes -/
structure FutureContractSubscriptionMessage where
  quantityI2 : BitVec 16
  contractsRequestedForDisplay : Exact 40 ContractsRequestedForDisplay
  deriving DecidableEq, Repr

namespace FutureContractSubscriptionMessage

def encode (message : FutureContractSubscriptionMessage) : List UInt8 :=
  encodeUIntLE 2 message.quantityI2
    ++ (encodeMany ContractsRequestedForDisplay.encode message.contractsRequestedForDisplay.val)

def decode (bytes : List UInt8) : Option (FutureContractSubscriptionMessage × List UInt8) := do
  let (quantityI2, bytes) ← decodeUIntLE 2 bytes
  let (contractsRequestedForDisplay_, bytes) ← decodeMany ContractsRequestedForDisplay.decode 40 bytes
  if fits_contractsRequestedForDisplay : contractsRequestedForDisplay_.length = 40 then
    pure ({ quantityI2, contractsRequestedForDisplay := ⟨contractsRequestedForDisplay_, fits_contractsRequestedForDisplay⟩ }, bytes)
  else none

@[simp] theorem encode_length (message : FutureContractSubscriptionMessage) : (encode message).length = 1922 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeMany_length_const ContractsRequestedForDisplay.encode 48 ContractsRequestedForDisplay.encode_length, message.contractsRequestedForDisplay.length_eq]

theorem encode_length_pos (message : FutureContractSubscriptionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FutureContractSubscriptionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_exact 40 ContractsRequestedForDisplay.encode ContractsRequestedForDisplay.decode ContractsRequestedForDisplay.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.contractsRequestedForDisplay.length_eq]
  rfl

end FutureContractSubscriptionMessage

/-- Option Statistics Request Message: 48 bytes -/
structure OptionStatisticsRequestMessage where
  contractName : ContractName
  deriving DecidableEq, Repr

namespace OptionStatisticsRequestMessage

def encode (message : OptionStatisticsRequestMessage) : List UInt8 :=
  ContractName.encode message.contractName

def decode (bytes : List UInt8) : Option (OptionStatisticsRequestMessage × List UInt8) := do
  let (contractName, bytes) ← ContractName.decode bytes
  pure ({ contractName }, bytes)

@[simp] theorem encode_length (message : OptionStatisticsRequestMessage) : (encode message).length = 48 := by
  unfold encode
  simp only [ContractName.encode_length]

theorem encode_length_pos (message : OptionStatisticsRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionStatisticsRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [ContractName.decode_encode, some_bind]
  rfl

end OptionStatisticsRequestMessage

/-- Any Client Message Payload, selected by Client Message Type -/
inductive ClientMessagePayload where
  | logInMessage (message : LogInMessage) -- 0
  | reRequestMessage (message : ReRequestMessage) -- 3
  | logOutMessage (message : LogOutMessage) -- 4
  | requestDataRetrievalMessage (message : RequestDataRetrievalMessage) -- 36
  | requestDataRetrievalMessage37 (message : RequestDataRetrievalMessage) -- 37
  | unsubscribeContractMessage (message : UnsubscribeContractMessage) -- 42
  | requestDailyTrendMessage (message : RequestDailyTrendMessage) -- 61
  | optionContractSubscriptionMessage (message : OptionContractSubscriptionMessage) -- 67
  | heartBeatsMessage (message : HeartBeatsMessage) -- 84
  | subscribingToIndicesServiceMessage (message : SubscribingToIndicesServiceMessage) -- 98
  | futureContractSubscriptionMessage (message : FutureContractSubscriptionMessage) -- 99
  | optionStatisticsRequestMessage (message : OptionStatisticsRequestMessage) -- 135
  deriving DecidableEq, Repr

namespace ClientMessagePayload

/-- The Client Message Type each message is sent under -/
def tag : ClientMessagePayload → BitVec 8
  | .logInMessage _ => 0
  | .reRequestMessage _ => 3
  | .logOutMessage _ => 4
  | .requestDataRetrievalMessage _ => 36
  | .requestDataRetrievalMessage37 _ => 37
  | .unsubscribeContractMessage _ => 42
  | .requestDailyTrendMessage _ => 61
  | .optionContractSubscriptionMessage _ => 67
  | .heartBeatsMessage _ => 84
  | .subscribingToIndicesServiceMessage _ => 98
  | .futureContractSubscriptionMessage _ => 99
  | .optionStatisticsRequestMessage _ => 135

def encode : ClientMessagePayload → List UInt8
  | .logInMessage message => LogInMessage.encode message
  | .reRequestMessage message => ReRequestMessage.encode message
  | .logOutMessage message => LogOutMessage.encode message
  | .requestDataRetrievalMessage message => RequestDataRetrievalMessage.encode message
  | .requestDataRetrievalMessage37 message => RequestDataRetrievalMessage.encode message
  | .unsubscribeContractMessage message => UnsubscribeContractMessage.encode message
  | .requestDailyTrendMessage message => RequestDailyTrendMessage.encode message
  | .optionContractSubscriptionMessage message => OptionContractSubscriptionMessage.encode message
  | .heartBeatsMessage message => HeartBeatsMessage.encode message
  | .subscribingToIndicesServiceMessage message => SubscribingToIndicesServiceMessage.encode message
  | .futureContractSubscriptionMessage message => FutureContractSubscriptionMessage.encode message
  | .optionStatisticsRequestMessage message => OptionStatisticsRequestMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ClientMessagePayload) : (encode message).length ≤ 1922 := by
  cases message with
  | logInMessage inner =>
    simp only [encode, LogInMessage.encode_length]
    omega
  | reRequestMessage inner =>
    simp only [encode, ReRequestMessage.encode_length]
    omega
  | logOutMessage inner =>
    simp only [encode, LogOutMessage.encode_length]
    omega
  | requestDataRetrievalMessage inner =>
    simp only [encode, RequestDataRetrievalMessage.encode_length]
    omega
  | requestDataRetrievalMessage37 inner =>
    simp only [encode, RequestDataRetrievalMessage.encode_length]
    omega
  | unsubscribeContractMessage inner =>
    simp only [encode, UnsubscribeContractMessage.encode_length]
    omega
  | requestDailyTrendMessage inner =>
    simp only [encode, RequestDailyTrendMessage.encode_length]
    omega
  | optionContractSubscriptionMessage inner =>
    simp only [encode, OptionContractSubscriptionMessage.encode_length]
    omega
  | heartBeatsMessage inner =>
    simp only [encode, HeartBeatsMessage.encode_length]
    omega
  | subscribingToIndicesServiceMessage inner =>
    simp only [encode, SubscribingToIndicesServiceMessage.encode_length]
    omega
  | futureContractSubscriptionMessage inner =>
    simp only [encode, FutureContractSubscriptionMessage.encode_length]
    omega
  | optionStatisticsRequestMessage inner =>
    simp only [encode, OptionStatisticsRequestMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (ClientMessagePayload × List UInt8) :=
  if tag = 0 then (LogInMessage.decode bytes).map fun (message, rest) => (.logInMessage message, rest)
  else if tag = 3 then (ReRequestMessage.decode bytes).map fun (message, rest) => (.reRequestMessage message, rest)
  else if tag = 4 then (LogOutMessage.decode bytes).map fun (message, rest) => (.logOutMessage message, rest)
  else if tag = 36 then (RequestDataRetrievalMessage.decode bytes).map fun (message, rest) => (.requestDataRetrievalMessage message, rest)
  else if tag = 37 then (RequestDataRetrievalMessage.decode bytes).map fun (message, rest) => (.requestDataRetrievalMessage37 message, rest)
  else if tag = 42 then (UnsubscribeContractMessage.decode bytes).map fun (message, rest) => (.unsubscribeContractMessage message, rest)
  else if tag = 61 then (RequestDailyTrendMessage.decode bytes).map fun (message, rest) => (.requestDailyTrendMessage message, rest)
  else if tag = 67 then (OptionContractSubscriptionMessage.decode bytes).map fun (message, rest) => (.optionContractSubscriptionMessage message, rest)
  else if tag = 84 then (HeartBeatsMessage.decode bytes).map fun (message, rest) => (.heartBeatsMessage message, rest)
  else if tag = 98 then (SubscribingToIndicesServiceMessage.decode bytes).map fun (message, rest) => (.subscribingToIndicesServiceMessage message, rest)
  else if tag = 99 then (FutureContractSubscriptionMessage.decode bytes).map fun (message, rest) => (.futureContractSubscriptionMessage message, rest)
  else if tag = 135 then (OptionStatisticsRequestMessage.decode bytes).map fun (message, rest) => (.optionStatisticsRequestMessage message, rest)
  else none

@[simp] theorem decode_encode (message : ClientMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ClientMessagePayload

/-- Client Message -/
structure ClientMessage where
  startByte : BitVec 8
  messageLength : BitVec 16
  lengthCheck : BitVec 8
  sequenceNumber : BitVec 32
  userName : UserName
  userNumber : BitVec 32
  time : Time
  clientMessagePayload : ClientMessagePayload
  deriving DecidableEq, Repr

namespace ClientMessage

def encode (message : ClientMessage) : List UInt8 :=
  encodeUInt 1 message.startByte
    ++ (encodeUIntLE 2 message.messageLength
    ++ (encodeUInt 1 message.lengthCheck
    ++ (encodeUIntLE 4 message.sequenceNumber
    ++ (UserName.encode message.userName
    ++ (encodeUIntLE 4 message.userNumber
    ++ (Time.encode message.time
    ++ (encodeUInt 1 (ClientMessagePayload.tag message.clientMessagePayload)
    ++ (ClientMessagePayload.encode message.clientMessagePayload))))))))

def decode (bytes : List UInt8) : Option (ClientMessage × List UInt8) := do
  let (startByte, bytes) ← decodeUInt 1 bytes
  let (messageLength, bytes) ← decodeUIntLE 2 bytes
  let (lengthCheck, bytes) ← decodeUInt 1 bytes
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (userName, bytes) ← UserName.decode bytes
  let (userNumber, bytes) ← decodeUIntLE 4 bytes
  let (time, bytes) ← Time.decode bytes
  let (clientMessageType, bytes) ← decodeUInt 1 bytes
  let (clientMessagePayload, bytes) ← ClientMessagePayload.decode clientMessageType bytes
  pure ({ startByte, messageLength, lengthCheck, sequenceNumber, userName, userNumber, time, clientMessagePayload }, bytes)

theorem encode_length_pos (message : ClientMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ClientMessage) : (encode message).length ≤ 1955 := by
  unfold encode
  cases message.clientMessagePayload with
  | logInMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, UserName.encode_length, Time.encode_length, LogInMessage.encode_length]
    omega
  | reRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, UserName.encode_length, Time.encode_length, ReRequestMessage.encode_length]
    omega
  | logOutMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, UserName.encode_length, Time.encode_length, LogOutMessage.encode_length]
    omega
  | requestDataRetrievalMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, UserName.encode_length, Time.encode_length, RequestDataRetrievalMessage.encode_length]
    omega
  | requestDataRetrievalMessage37 inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, UserName.encode_length, Time.encode_length, RequestDataRetrievalMessage.encode_length]
    omega
  | unsubscribeContractMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, UserName.encode_length, Time.encode_length, UnsubscribeContractMessage.encode_length]
    omega
  | requestDailyTrendMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, UserName.encode_length, Time.encode_length, RequestDailyTrendMessage.encode_length]
    omega
  | optionContractSubscriptionMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, UserName.encode_length, Time.encode_length, OptionContractSubscriptionMessage.encode_length]
    omega
  | heartBeatsMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, UserName.encode_length, Time.encode_length, HeartBeatsMessage.encode_length]
    omega
  | subscribingToIndicesServiceMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, UserName.encode_length, Time.encode_length, SubscribingToIndicesServiceMessage.encode_length]
    omega
  | futureContractSubscriptionMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, UserName.encode_length, Time.encode_length, FutureContractSubscriptionMessage.encode_length]
    omega
  | optionStatisticsRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, UserName.encode_length, Time.encode_length, OptionStatisticsRequestMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : ClientMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, UserName.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Time.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ClientMessagePayload.decode_encode, some_bind]
  rfl

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

end Omi.NairobiNairobibondsMarketdataMitsV214Client
