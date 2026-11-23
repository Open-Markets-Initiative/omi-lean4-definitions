import Wire

/-!
# National Stock Exchange of India Ltd Order Entry v2.7

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.

Note: Broker Eligibility Per Market is a bit field set, proven as its 2 byte integer rather than bit
by bit

Note: St Order Flags is a bit field set, proven as its 2 byte integer rather than bit by bit

Note: Client Packet Body is keyed on Transaction Code, which Client Registration Packet holds 16
bytes in, behind what frames it: those 2 bytes are read where they lie without taking them, 23008
reading Client Registration Packet and any other Client Session Packet, each carrying the proof of
what its encoding holds there

Note: Client Direct Packet's Packet Length is written from its body but not checked on decode, since
the body has no bound the prefix must fit; the body is read by its content

License: MIT No Attribution
-/

namespace Omi.NseNseslbmOrderentryNnfdirectV27Client

/-- Broker Status: one byte code -/
def BrokerStatus.codes : List UInt8 :=
  [0x20, 0x53, 0x41, 0x44, 0x43]

inductive BrokerStatus where
  | blank -- Blank
  | suspended -- Suspended
  | active -- Active
  | deactivated -- Deactivated
  | closeout -- Closeout
  | unlisted (byte : { byte : UInt8 // byte ∉ BrokerStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BrokerStatus

def toByte : BrokerStatus → UInt8
  | .blank => 0x20
  | .suspended => 0x53
  | .active => 0x41
  | .deactivated => 0x44
  | .closeout => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BrokerStatus :=
  if byte = 0x20 then .blank
  else if byte = 0x53 then .suspended
  else if byte = 0x41 then .active
  else if byte = 0x44 then .deactivated
  else .closeout

def ofByte (byte : UInt8) : BrokerStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BrokerStatus) : ofByte value.toByte = value := by
  cases value with
  | blank => decide
  | suspended => decide
  | active => decide
  | deactivated => decide
  | closeout => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BrokerStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BrokerStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BrokerStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : BrokerStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : BrokerStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BrokerStatus

/-- Request For Open Orders: one byte code -/
def RequestForOpenOrders.codes : List UInt8 :=
  [0x47, 0x4E]

inductive RequestForOpenOrders where
  | downloadGtcAndGtdOrders -- Download Gtc And Gtd Orders
  | noOpenOrders -- No Open Orders
  | unlisted (byte : { byte : UInt8 // byte ∉ RequestForOpenOrders.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RequestForOpenOrders

def toByte : RequestForOpenOrders → UInt8
  | .downloadGtcAndGtdOrders => 0x47
  | .noOpenOrders => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RequestForOpenOrders :=
  if byte = 0x47 then .downloadGtcAndGtdOrders
  else .noOpenOrders

def ofByte (byte : UInt8) : RequestForOpenOrders :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RequestForOpenOrders) : ofByte value.toByte = value := by
  cases value with
  | downloadGtcAndGtdOrders => decide
  | noOpenOrders => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RequestForOpenOrders) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RequestForOpenOrders × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RequestForOpenOrders) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : RequestForOpenOrders) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : RequestForOpenOrders) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RequestForOpenOrders

/-- Participant Type: one byte code -/
def ParticipantType.codes : List UInt8 :=
  [0x43, 0x53, 0x49]

inductive ParticipantType where
  | competitor -- Competitor
  | solicitor -- Solicitor
  | initiator -- Initiator
  | unlisted (byte : { byte : UInt8 // byte ∉ ParticipantType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ParticipantType

def toByte : ParticipantType → UInt8
  | .competitor => 0x43
  | .solicitor => 0x53
  | .initiator => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ParticipantType :=
  if byte = 0x43 then .competitor
  else if byte = 0x53 then .solicitor
  else .initiator

def ofByte (byte : UInt8) : ParticipantType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ParticipantType) : ofByte value.toByte = value := by
  cases value with
  | competitor => decide
  | solicitor => decide
  | initiator => decide
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

/-- Mod Cxl By: one byte code -/
def ModCxlBy.codes : List UInt8 :=
  [0x54, 0x42, 0x4D, 0x43]

inductive ModCxlBy where
  | trader -- Trader
  | branchManager -- Branch Manager
  | corporateManager -- Corporate Manager
  | control -- Control
  | unlisted (byte : { byte : UInt8 // byte ∉ ModCxlBy.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ModCxlBy

def toByte : ModCxlBy → UInt8
  | .trader => 0x54
  | .branchManager => 0x42
  | .corporateManager => 0x4D
  | .control => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ModCxlBy :=
  if byte = 0x54 then .trader
  else if byte = 0x42 then .branchManager
  else if byte = 0x4D then .corporateManager
  else .control

def ofByte (byte : UInt8) : ModCxlBy :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ModCxlBy) : ofByte value.toByte = value := by
  cases value with
  | trader => decide
  | branchManager => decide
  | corporateManager => decide
  | control => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ModCxlBy) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ModCxlBy × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ModCxlBy) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ModCxlBy) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ModCxlBy) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ModCxlBy

/-- Logon Request Message: 172 bytes -/
structure LogonRequestMessage where
  userId : BitVec 32
  password : Alpha 8
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
  brokerStatus : BrokerStatus
  showIndex : Alpha 1
  brokerEligibilityPerMarket : BitVec 16
  logonRequestBrokerName : Alpha 26
  deriving DecidableEq, Repr

namespace LogonRequestMessage

def encode (message : LogonRequestMessage) : List UInt8 :=
  encodeUInt 4 message.userId
    ++ (Alpha.encode message.password
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
    ++ (BrokerStatus.encode message.brokerStatus
    ++ (Alpha.encode message.showIndex
    ++ (encodeUInt 2 message.brokerEligibilityPerMarket
    ++ (Alpha.encode message.logonRequestBrokerName))))))))))))))))

def decode (bytes : List UInt8) : Option (LogonRequestMessage × List UInt8) := do
  let (userId, bytes) ← decodeUInt 4 bytes
  let (password, bytes) ← Alpha.decode 8 bytes
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
  let (brokerStatus, bytes) ← BrokerStatus.decode bytes
  let (showIndex, bytes) ← Alpha.decode 1 bytes
  let (brokerEligibilityPerMarket, bytes) ← decodeUInt 2 bytes
  let (logonRequestBrokerName, bytes) ← Alpha.decode 26 bytes
  pure ({ userId, password, newPassword, traderName, lastPasswordChangeDateTime, brokerId, reserved1, branchId, versionNumber, reserved56, userType, sequenceNumber, workstationNumber, brokerStatus, showIndex, brokerEligibilityPerMarket, logonRequestBrokerName }, bytes)

@[simp] theorem encode_length (message : LogonRequestMessage) : (encode message).length = 172 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, BrokerStatus.encode_length]

theorem encode_length_pos (message : LogonRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogonRequestMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, BrokerStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LogonRequestMessage

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

/-- Update Local Database Request Message: 18 bytes -/
structure UpdateLocalDatabaseRequestMessage where
  lastUpdateSecurityTime : BitVec 32
  lastUpdateParticipantTime : BitVec 32
  requestForOpenOrders : RequestForOpenOrders
  reserved1 : Alpha 1
  normalMarketStatus : BitVec 16
  oddLotMarketStatus : BitVec 16
  spotMarketStatus : BitVec 16
  auctionMarketStatus : BitVec 16
  deriving DecidableEq, Repr

namespace UpdateLocalDatabaseRequestMessage

def encode (message : UpdateLocalDatabaseRequestMessage) : List UInt8 :=
  encodeUInt 4 message.lastUpdateSecurityTime
    ++ (encodeUInt 4 message.lastUpdateParticipantTime
    ++ (RequestForOpenOrders.encode message.requestForOpenOrders
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.normalMarketStatus
    ++ (encodeUInt 2 message.oddLotMarketStatus
    ++ (encodeUInt 2 message.spotMarketStatus
    ++ (encodeUInt 2 message.auctionMarketStatus)))))))

def decode (bytes : List UInt8) : Option (UpdateLocalDatabaseRequestMessage × List UInt8) := do
  let (lastUpdateSecurityTime, bytes) ← decodeUInt 4 bytes
  let (lastUpdateParticipantTime, bytes) ← decodeUInt 4 bytes
  let (requestForOpenOrders, bytes) ← RequestForOpenOrders.decode bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (normalMarketStatus, bytes) ← decodeUInt 2 bytes
  let (oddLotMarketStatus, bytes) ← decodeUInt 2 bytes
  let (spotMarketStatus, bytes) ← decodeUInt 2 bytes
  let (auctionMarketStatus, bytes) ← decodeUInt 2 bytes
  pure ({ lastUpdateSecurityTime, lastUpdateParticipantTime, requestForOpenOrders, reserved1, normalMarketStatus, oddLotMarketStatus, spotMarketStatus, auctionMarketStatus }, bytes)

@[simp] theorem encode_length (message : UpdateLocalDatabaseRequestMessage) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, RequestForOpenOrders.encode_length, Alpha.encode_length]

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
  rw [List.append_assoc, RequestForOpenOrders.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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

/-- Logoff Request Message: 0 bytes -/
structure LogoffRequestMessage where
  deriving DecidableEq, Repr

namespace LogoffRequestMessage

def encode (_ : LogoffRequestMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (LogoffRequestMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : LogoffRequestMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : LogoffRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end LogoffRequestMessage

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

/-- Order Entry Request Message: 174 bytes -/
structure OrderEntryRequestMessage where
  participantType : ParticipantType
  reserved1 : Alpha 1
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  modCxlBy : ModCxlBy
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
  reverseLegSettlDate : BitVec 32
  entryDateTime : BitVec 32
  minFillAon : BitVec 32
  lastModified : BitVec 32
  stOrderFlags : BitVec 16
  branchId : BitVec 16
  traderId : BitVec 32
  brokerId : Alpha 5
  oeRemarks : Alpha 21
  transactionId : BitVec 32
  settlor : Alpha 12
  proClient : BitVec 16
  settlementPeriod : BitVec 16
  nnfField : Alpha 8
  execTimeStamp : Alpha 8
  reserved2 : Alpha 2
  orderType : Alpha 2
  deriving DecidableEq, Repr

namespace OrderEntryRequestMessage

def encode (message : OrderEntryRequestMessage) : List UInt8 :=
  ParticipantType.encode message.participantType
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (ModCxlBy.encode message.modCxlBy
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
    ++ (encodeUInt 4 message.reverseLegSettlDate
    ++ (encodeUInt 4 message.entryDateTime
    ++ (encodeUInt 4 message.minFillAon
    ++ (encodeUInt 4 message.lastModified
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId
    ++ (encodeUInt 4 message.traderId
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.oeRemarks
    ++ (encodeUInt 4 message.transactionId
    ++ (Alpha.encode message.settlor
    ++ (encodeUInt 2 message.proClient
    ++ (encodeUInt 2 message.settlementPeriod
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.execTimeStamp
    ++ (Alpha.encode message.reserved2
    ++ (Alpha.encode message.orderType)))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderEntryRequestMessage × List UInt8) := do
  let (participantType, bytes) ← ParticipantType.decode bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (modCxlBy, bytes) ← ModCxlBy.decode bytes
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
  let (reverseLegSettlDate, bytes) ← decodeUInt 4 bytes
  let (entryDateTime, bytes) ← decodeUInt 4 bytes
  let (minFillAon, bytes) ← decodeUInt 4 bytes
  let (lastModified, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId, bytes) ← decodeUInt 2 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (oeRemarks, bytes) ← Alpha.decode 21 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  let (proClient, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod, bytes) ← decodeUInt 2 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (execTimeStamp, bytes) ← Alpha.decode 8 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (orderType, bytes) ← Alpha.decode 2 bytes
  pure ({ participantType, reserved1, competitorPeriod, solicitorPeriod, modCxlBy, filler9, reasonCode, reserved4, secInfo, auctionNumber, opBrokerId, suspended, orderNumber, accountNumber, bookType, buySell, disclosedVol, disclosedVolRemaining, totalVolRemaining, volume, volumeFilledToday, price, triggerPrice, reverseLegSettlDate, entryDateTime, minFillAon, lastModified, stOrderFlags, branchId, traderId, brokerId, oeRemarks, transactionId, settlor, proClient, settlementPeriod, nnfField, execTimeStamp, reserved2, orderType }, bytes)

@[simp] theorem encode_length (message : OrderEntryRequestMessage) : (encode message).length = 174 := by
  unfold encode
  simp only [List.length_append, ParticipantType.encode_length, Alpha.encode_length, encodeUInt_length, ModCxlBy.encode_length, SecInfo.encode_length]

theorem encode_length_pos (message : OrderEntryRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OrderEntryRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ModCxlBy.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderEntryRequestMessage

/-- Order Modification Request Message: 174 bytes -/
structure OrderModificationRequestMessage where
  participantType : ParticipantType
  reserved1 : Alpha 1
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  modCxlBy : ModCxlBy
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
  reverseLegSettlDate : BitVec 32
  entryDateTime : BitVec 32
  minFillAon : BitVec 32
  lastModified : BitVec 32
  stOrderFlags : BitVec 16
  branchId : BitVec 16
  traderId : BitVec 32
  brokerId : Alpha 5
  oeRemarks : Alpha 21
  transactionId : BitVec 32
  settlor : Alpha 12
  proClient : BitVec 16
  settlementPeriod : BitVec 16
  nnfField : Alpha 8
  execTimeStamp : Alpha 8
  reserved2 : Alpha 2
  orderType : Alpha 2
  deriving DecidableEq, Repr

namespace OrderModificationRequestMessage

def encode (message : OrderModificationRequestMessage) : List UInt8 :=
  ParticipantType.encode message.participantType
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (ModCxlBy.encode message.modCxlBy
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
    ++ (encodeUInt 4 message.reverseLegSettlDate
    ++ (encodeUInt 4 message.entryDateTime
    ++ (encodeUInt 4 message.minFillAon
    ++ (encodeUInt 4 message.lastModified
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId
    ++ (encodeUInt 4 message.traderId
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.oeRemarks
    ++ (encodeUInt 4 message.transactionId
    ++ (Alpha.encode message.settlor
    ++ (encodeUInt 2 message.proClient
    ++ (encodeUInt 2 message.settlementPeriod
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.execTimeStamp
    ++ (Alpha.encode message.reserved2
    ++ (Alpha.encode message.orderType)))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderModificationRequestMessage × List UInt8) := do
  let (participantType, bytes) ← ParticipantType.decode bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (modCxlBy, bytes) ← ModCxlBy.decode bytes
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
  let (reverseLegSettlDate, bytes) ← decodeUInt 4 bytes
  let (entryDateTime, bytes) ← decodeUInt 4 bytes
  let (minFillAon, bytes) ← decodeUInt 4 bytes
  let (lastModified, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId, bytes) ← decodeUInt 2 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (oeRemarks, bytes) ← Alpha.decode 21 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  let (proClient, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod, bytes) ← decodeUInt 2 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (execTimeStamp, bytes) ← Alpha.decode 8 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (orderType, bytes) ← Alpha.decode 2 bytes
  pure ({ participantType, reserved1, competitorPeriod, solicitorPeriod, modCxlBy, filler9, reasonCode, reserved4, secInfo, auctionNumber, opBrokerId, suspended, orderNumber, accountNumber, bookType, buySell, disclosedVol, disclosedVolRemaining, totalVolRemaining, volume, volumeFilledToday, price, triggerPrice, reverseLegSettlDate, entryDateTime, minFillAon, lastModified, stOrderFlags, branchId, traderId, brokerId, oeRemarks, transactionId, settlor, proClient, settlementPeriod, nnfField, execTimeStamp, reserved2, orderType }, bytes)

@[simp] theorem encode_length (message : OrderModificationRequestMessage) : (encode message).length = 174 := by
  unfold encode
  simp only [List.length_append, ParticipantType.encode_length, Alpha.encode_length, encodeUInt_length, ModCxlBy.encode_length, SecInfo.encode_length]

theorem encode_length_pos (message : OrderModificationRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OrderModificationRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ModCxlBy.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderModificationRequestMessage

/-- Order Cancellation Request Message: 174 bytes -/
structure OrderCancellationRequestMessage where
  participantType : ParticipantType
  reserved1 : Alpha 1
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  modCxlBy : ModCxlBy
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
  reverseLegSettlDate : BitVec 32
  entryDateTime : BitVec 32
  minFillAon : BitVec 32
  lastModified : BitVec 32
  stOrderFlags : BitVec 16
  branchId : BitVec 16
  traderId : BitVec 32
  brokerId : Alpha 5
  oeRemarks : Alpha 21
  transactionId : BitVec 32
  settlor : Alpha 12
  proClient : BitVec 16
  settlementPeriod : BitVec 16
  nnfField : Alpha 8
  execTimeStamp : Alpha 8
  reserved2 : Alpha 2
  orderType : Alpha 2
  deriving DecidableEq, Repr

namespace OrderCancellationRequestMessage

def encode (message : OrderCancellationRequestMessage) : List UInt8 :=
  ParticipantType.encode message.participantType
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (ModCxlBy.encode message.modCxlBy
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
    ++ (encodeUInt 4 message.reverseLegSettlDate
    ++ (encodeUInt 4 message.entryDateTime
    ++ (encodeUInt 4 message.minFillAon
    ++ (encodeUInt 4 message.lastModified
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId
    ++ (encodeUInt 4 message.traderId
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.oeRemarks
    ++ (encodeUInt 4 message.transactionId
    ++ (Alpha.encode message.settlor
    ++ (encodeUInt 2 message.proClient
    ++ (encodeUInt 2 message.settlementPeriod
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.execTimeStamp
    ++ (Alpha.encode message.reserved2
    ++ (Alpha.encode message.orderType)))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderCancellationRequestMessage × List UInt8) := do
  let (participantType, bytes) ← ParticipantType.decode bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (modCxlBy, bytes) ← ModCxlBy.decode bytes
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
  let (reverseLegSettlDate, bytes) ← decodeUInt 4 bytes
  let (entryDateTime, bytes) ← decodeUInt 4 bytes
  let (minFillAon, bytes) ← decodeUInt 4 bytes
  let (lastModified, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId, bytes) ← decodeUInt 2 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (oeRemarks, bytes) ← Alpha.decode 21 bytes
  let (transactionId, bytes) ← decodeUInt 4 bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  let (proClient, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod, bytes) ← decodeUInt 2 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (execTimeStamp, bytes) ← Alpha.decode 8 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (orderType, bytes) ← Alpha.decode 2 bytes
  pure ({ participantType, reserved1, competitorPeriod, solicitorPeriod, modCxlBy, filler9, reasonCode, reserved4, secInfo, auctionNumber, opBrokerId, suspended, orderNumber, accountNumber, bookType, buySell, disclosedVol, disclosedVolRemaining, totalVolRemaining, volume, volumeFilledToday, price, triggerPrice, reverseLegSettlDate, entryDateTime, minFillAon, lastModified, stOrderFlags, branchId, traderId, brokerId, oeRemarks, transactionId, settlor, proClient, settlementPeriod, nnfField, execTimeStamp, reserved2, orderType }, bytes)

@[simp] theorem encode_length (message : OrderCancellationRequestMessage) : (encode message).length = 174 := by
  unfold encode
  simp only [List.length_append, ParticipantType.encode_length, Alpha.encode_length, encodeUInt_length, ModCxlBy.encode_length, SecInfo.encode_length]

theorem encode_length_pos (message : OrderCancellationRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OrderCancellationRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, ParticipantType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ModCxlBy.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderCancellationRequestMessage

/-- Trade Cancellation Request Message: 74 bytes -/
structure TradeCancellationRequestMessage where
  secInfo : SecInfo
  reverseLegSettlDate : BitVec 32
  lFillNumber : BitVec 32
  lFillQty : BitVec 32
  lFillPrice : BitVec 32
  iMktType : BitVec 16
  lNewVolume : BitVec 32
  buyParticipantId : Alpha 12
  sellParticipantId : Alpha 12
  buyBrokerId : Alpha 5
  sellBrokerId : Alpha 5
  traderId : BitVec 32
  requestedBy : BitVec 16
  deriving DecidableEq, Repr

namespace TradeCancellationRequestMessage

def encode (message : TradeCancellationRequestMessage) : List UInt8 :=
  SecInfo.encode message.secInfo
    ++ (encodeUInt 4 message.reverseLegSettlDate
    ++ (encodeUInt 4 message.lFillNumber
    ++ (encodeUInt 4 message.lFillQty
    ++ (encodeUInt 4 message.lFillPrice
    ++ (encodeUInt 2 message.iMktType
    ++ (encodeUInt 4 message.lNewVolume
    ++ (Alpha.encode message.buyParticipantId
    ++ (Alpha.encode message.sellParticipantId
    ++ (Alpha.encode message.buyBrokerId
    ++ (Alpha.encode message.sellBrokerId
    ++ (encodeUInt 4 message.traderId
    ++ (encodeUInt 2 message.requestedBy))))))))))))

def decode (bytes : List UInt8) : Option (TradeCancellationRequestMessage × List UInt8) := do
  let (secInfo, bytes) ← SecInfo.decode bytes
  let (reverseLegSettlDate, bytes) ← decodeUInt 4 bytes
  let (lFillNumber, bytes) ← decodeUInt 4 bytes
  let (lFillQty, bytes) ← decodeUInt 4 bytes
  let (lFillPrice, bytes) ← decodeUInt 4 bytes
  let (iMktType, bytes) ← decodeUInt 2 bytes
  let (lNewVolume, bytes) ← decodeUInt 4 bytes
  let (buyParticipantId, bytes) ← Alpha.decode 12 bytes
  let (sellParticipantId, bytes) ← Alpha.decode 12 bytes
  let (buyBrokerId, bytes) ← Alpha.decode 5 bytes
  let (sellBrokerId, bytes) ← Alpha.decode 5 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (requestedBy, bytes) ← decodeUInt 2 bytes
  pure ({ secInfo, reverseLegSettlDate, lFillNumber, lFillQty, lFillPrice, iMktType, lNewVolume, buyParticipantId, sellParticipantId, buyBrokerId, sellBrokerId, traderId, requestedBy }, bytes)

@[simp] theorem encode_length (message : TradeCancellationRequestMessage) : (encode message).length = 74 := by
  unfold encode
  simp only [List.length_append, SecInfo.encode_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : TradeCancellationRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCancellationRequestMessage) (rest : List UInt8) :
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TradeCancellationRequestMessage

/-- Trade Modification Request Message: 74 bytes -/
structure TradeModificationRequestMessage where
  secInfo : SecInfo
  reverseLegSettlDate : BitVec 32
  lFillNumber : BitVec 32
  lFillQty : BitVec 32
  lFillPrice : BitVec 32
  iMktType : BitVec 16
  lNewVolume : BitVec 32
  buyParticipantId : Alpha 12
  sellParticipantId : Alpha 12
  buyBrokerId : Alpha 5
  sellBrokerId : Alpha 5
  traderId : BitVec 32
  requestedBy : BitVec 16
  deriving DecidableEq, Repr

namespace TradeModificationRequestMessage

def encode (message : TradeModificationRequestMessage) : List UInt8 :=
  SecInfo.encode message.secInfo
    ++ (encodeUInt 4 message.reverseLegSettlDate
    ++ (encodeUInt 4 message.lFillNumber
    ++ (encodeUInt 4 message.lFillQty
    ++ (encodeUInt 4 message.lFillPrice
    ++ (encodeUInt 2 message.iMktType
    ++ (encodeUInt 4 message.lNewVolume
    ++ (Alpha.encode message.buyParticipantId
    ++ (Alpha.encode message.sellParticipantId
    ++ (Alpha.encode message.buyBrokerId
    ++ (Alpha.encode message.sellBrokerId
    ++ (encodeUInt 4 message.traderId
    ++ (encodeUInt 2 message.requestedBy))))))))))))

def decode (bytes : List UInt8) : Option (TradeModificationRequestMessage × List UInt8) := do
  let (secInfo, bytes) ← SecInfo.decode bytes
  let (reverseLegSettlDate, bytes) ← decodeUInt 4 bytes
  let (lFillNumber, bytes) ← decodeUInt 4 bytes
  let (lFillQty, bytes) ← decodeUInt 4 bytes
  let (lFillPrice, bytes) ← decodeUInt 4 bytes
  let (iMktType, bytes) ← decodeUInt 2 bytes
  let (lNewVolume, bytes) ← decodeUInt 4 bytes
  let (buyParticipantId, bytes) ← Alpha.decode 12 bytes
  let (sellParticipantId, bytes) ← Alpha.decode 12 bytes
  let (buyBrokerId, bytes) ← Alpha.decode 5 bytes
  let (sellBrokerId, bytes) ← Alpha.decode 5 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (requestedBy, bytes) ← decodeUInt 2 bytes
  pure ({ secInfo, reverseLegSettlDate, lFillNumber, lFillQty, lFillPrice, iMktType, lNewVolume, buyParticipantId, sellParticipantId, buyBrokerId, sellBrokerId, traderId, requestedBy }, bytes)

@[simp] theorem encode_length (message : TradeModificationRequestMessage) : (encode message).length = 74 := by
  unfold encode
  simp only [List.length_append, SecInfo.encode_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : TradeModificationRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeModificationRequestMessage) (rest : List UInt8) :
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TradeModificationRequestMessage

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

/-- Secure Box Registration Request Message: 2 bytes -/
structure SecureBoxRegistrationRequestMessage where
  boxId : BitVec 16
  deriving DecidableEq, Repr

namespace SecureBoxRegistrationRequestMessage

def encode (message : SecureBoxRegistrationRequestMessage) : List UInt8 :=
  encodeUInt 2 message.boxId

def decode (bytes : List UInt8) : Option (SecureBoxRegistrationRequestMessage × List UInt8) := do
  let (boxId, bytes) ← decodeUInt 2 bytes
  pure ({ boxId }, bytes)

@[simp] theorem encode_length (message : SecureBoxRegistrationRequestMessage) : (encode message).length = 2 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : SecureBoxRegistrationRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecureBoxRegistrationRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SecureBoxRegistrationRequestMessage

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

/-- Any Client Message Payload, selected by Transaction Code -/
inductive ClientMessagePayload where
  | logonRequestMessage (message : LogonRequestMessage) -- 2300
  | systemInformationRequestMessage (message : SystemInformationRequestMessage) -- 1600
  | updateLocalDatabaseRequestMessage (message : UpdateLocalDatabaseRequestMessage) -- 7300
  | messageDownloadRequestMessage (message : MessageDownloadRequestMessage) -- 7000
  | logoffRequestMessage (message : LogoffRequestMessage) -- 2320
  | orderEntryRequestMessage (message : OrderEntryRequestMessage) -- 2000
  | orderModificationRequestMessage (message : OrderModificationRequestMessage) -- 2040
  | orderCancellationRequestMessage (message : OrderCancellationRequestMessage) -- 2070
  | tradeCancellationRequestMessage (message : TradeCancellationRequestMessage) -- 5440
  | tradeModificationRequestMessage (message : TradeModificationRequestMessage) -- 5445
  | gatewayRouterRequestMessage (message : GatewayRouterRequestMessage) -- 2400
  | secureBoxRegistrationRequestMessage (message : SecureBoxRegistrationRequestMessage) -- 23008
  | boxSignOnRequestMessage (message : BoxSignOnRequestMessage) -- 23000
  | heartbeatMessage (message : HeartbeatMessage) -- 23506
  deriving DecidableEq, Repr

namespace ClientMessagePayload

/-- The Transaction Code each message is sent under -/
def tag : ClientMessagePayload → BitVec 16
  | .logonRequestMessage _ => 2300
  | .systemInformationRequestMessage _ => 1600
  | .updateLocalDatabaseRequestMessage _ => 7300
  | .messageDownloadRequestMessage _ => 7000
  | .logoffRequestMessage _ => 2320
  | .orderEntryRequestMessage _ => 2000
  | .orderModificationRequestMessage _ => 2040
  | .orderCancellationRequestMessage _ => 2070
  | .tradeCancellationRequestMessage _ => 5440
  | .tradeModificationRequestMessage _ => 5445
  | .gatewayRouterRequestMessage _ => 2400
  | .secureBoxRegistrationRequestMessage _ => 23008
  | .boxSignOnRequestMessage _ => 23000
  | .heartbeatMessage _ => 23506

def encode : ClientMessagePayload → List UInt8
  | .logonRequestMessage message => LogonRequestMessage.encode message
  | .systemInformationRequestMessage message => SystemInformationRequestMessage.encode message
  | .updateLocalDatabaseRequestMessage message => UpdateLocalDatabaseRequestMessage.encode message
  | .messageDownloadRequestMessage message => MessageDownloadRequestMessage.encode message
  | .logoffRequestMessage message => LogoffRequestMessage.encode message
  | .orderEntryRequestMessage message => OrderEntryRequestMessage.encode message
  | .orderModificationRequestMessage message => OrderModificationRequestMessage.encode message
  | .orderCancellationRequestMessage message => OrderCancellationRequestMessage.encode message
  | .tradeCancellationRequestMessage message => TradeCancellationRequestMessage.encode message
  | .tradeModificationRequestMessage message => TradeModificationRequestMessage.encode message
  | .gatewayRouterRequestMessage message => GatewayRouterRequestMessage.encode message
  | .secureBoxRegistrationRequestMessage message => SecureBoxRegistrationRequestMessage.encode message
  | .boxSignOnRequestMessage message => BoxSignOnRequestMessage.encode message
  | .heartbeatMessage message => HeartbeatMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ClientMessagePayload) : (encode message).length ≤ 174 := by
  cases message with
  | logonRequestMessage inner =>
    simp only [encode, LogonRequestMessage.encode_length]
    omega
  | systemInformationRequestMessage inner =>
    simp only [encode, SystemInformationRequestMessage.encode_length]
    omega
  | updateLocalDatabaseRequestMessage inner =>
    simp only [encode, UpdateLocalDatabaseRequestMessage.encode_length]
    omega
  | messageDownloadRequestMessage inner =>
    simp only [encode, MessageDownloadRequestMessage.encode_length]
    omega
  | logoffRequestMessage inner =>
    simp only [encode, LogoffRequestMessage.encode_length]
    omega
  | orderEntryRequestMessage inner =>
    simp only [encode, OrderEntryRequestMessage.encode_length]
    omega
  | orderModificationRequestMessage inner =>
    simp only [encode, OrderModificationRequestMessage.encode_length]
    omega
  | orderCancellationRequestMessage inner =>
    simp only [encode, OrderCancellationRequestMessage.encode_length]
    omega
  | tradeCancellationRequestMessage inner =>
    simp only [encode, TradeCancellationRequestMessage.encode_length]
    omega
  | tradeModificationRequestMessage inner =>
    simp only [encode, TradeModificationRequestMessage.encode_length]
    omega
  | gatewayRouterRequestMessage inner =>
    simp only [encode, GatewayRouterRequestMessage.encode_length]
    omega
  | secureBoxRegistrationRequestMessage inner =>
    simp only [encode, SecureBoxRegistrationRequestMessage.encode_length]
    omega
  | boxSignOnRequestMessage inner =>
    simp only [encode, BoxSignOnRequestMessage.encode_length]
    omega
  | heartbeatMessage inner =>
    simp only [encode, HeartbeatMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (ClientMessagePayload × List UInt8) :=
  if tag = 2300 then (LogonRequestMessage.decode bytes).map fun (message, rest) => (.logonRequestMessage message, rest)
  else if tag = 1600 then (SystemInformationRequestMessage.decode bytes).map fun (message, rest) => (.systemInformationRequestMessage message, rest)
  else if tag = 7300 then (UpdateLocalDatabaseRequestMessage.decode bytes).map fun (message, rest) => (.updateLocalDatabaseRequestMessage message, rest)
  else if tag = 7000 then (MessageDownloadRequestMessage.decode bytes).map fun (message, rest) => (.messageDownloadRequestMessage message, rest)
  else if tag = 2320 then (LogoffRequestMessage.decode bytes).map fun (message, rest) => (.logoffRequestMessage message, rest)
  else if tag = 2000 then (OrderEntryRequestMessage.decode bytes).map fun (message, rest) => (.orderEntryRequestMessage message, rest)
  else if tag = 2040 then (OrderModificationRequestMessage.decode bytes).map fun (message, rest) => (.orderModificationRequestMessage message, rest)
  else if tag = 2070 then (OrderCancellationRequestMessage.decode bytes).map fun (message, rest) => (.orderCancellationRequestMessage message, rest)
  else if tag = 5440 then (TradeCancellationRequestMessage.decode bytes).map fun (message, rest) => (.tradeCancellationRequestMessage message, rest)
  else if tag = 5445 then (TradeModificationRequestMessage.decode bytes).map fun (message, rest) => (.tradeModificationRequestMessage message, rest)
  else if tag = 2400 then (GatewayRouterRequestMessage.decode bytes).map fun (message, rest) => (.gatewayRouterRequestMessage message, rest)
  else if tag = 23008 then (SecureBoxRegistrationRequestMessage.decode bytes).map fun (message, rest) => (.secureBoxRegistrationRequestMessage message, rest)
  else if tag = 23000 then (BoxSignOnRequestMessage.decode bytes).map fun (message, rest) => (.boxSignOnRequestMessage message, rest)
  else if tag = 23506 then (HeartbeatMessage.decode bytes).map fun (message, rest) => (.heartbeatMessage message, rest)
  else none

@[simp] theorem decode_encode (message : ClientMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ClientMessagePayload

/-- Client Registration Packet -/
structure ClientRegistrationPacket where
  registrationChecksum : Alpha 16
  logTime : BitVec 32
  alphaChar : Alpha 2
  traderId : BitVec 32
  errorCode : BitVec 16
  headerTimestamp : BitVec 64
  timeStamp1 : Alpha 8
  timeStamp2 : Alpha 8
  messageLength : BitVec 16
  clientMessagePayload : ClientMessagePayload
  deriving DecidableEq, Repr

namespace ClientRegistrationPacket

def encode (message : ClientRegistrationPacket) : List UInt8 :=
  Alpha.encode message.registrationChecksum
    ++ (encodeUInt 2 (ClientMessagePayload.tag message.clientMessagePayload)
    ++ (encodeUInt 4 message.logTime
    ++ (Alpha.encode message.alphaChar
    ++ (encodeUInt 4 message.traderId
    ++ (encodeUInt 2 message.errorCode
    ++ (encodeUInt 8 message.headerTimestamp
    ++ (Alpha.encode message.timeStamp1
    ++ (Alpha.encode message.timeStamp2
    ++ (encodeUInt 2 message.messageLength
    ++ (ClientMessagePayload.encode message.clientMessagePayload))))))))))

def decode (bytes : List UInt8) : Option (ClientRegistrationPacket × List UInt8) := do
  let (registrationChecksum, bytes) ← Alpha.decode 16 bytes
  let (transactionCode, bytes) ← decodeUInt 2 bytes
  let (logTime, bytes) ← decodeUInt 4 bytes
  let (alphaChar, bytes) ← Alpha.decode 2 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (errorCode, bytes) ← decodeUInt 2 bytes
  let (headerTimestamp, bytes) ← decodeUInt 8 bytes
  let (timeStamp1, bytes) ← Alpha.decode 8 bytes
  let (timeStamp2, bytes) ← Alpha.decode 8 bytes
  let (messageLength, bytes) ← decodeUInt 2 bytes
  let (clientMessagePayload, bytes) ← ClientMessagePayload.decode transactionCode bytes
  pure ({ registrationChecksum, logTime, alphaChar, traderId, errorCode, headerTimestamp, timeStamp1, timeStamp2, messageLength, clientMessagePayload }, bytes)

theorem encode_length_pos (message : ClientRegistrationPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ClientRegistrationPacket) : (encode message).length ≤ 230 := by
  unfold encode
  cases message.clientMessagePayload with
  | logonRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, LogonRequestMessage.encode_length]
    omega
  | systemInformationRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, SystemInformationRequestMessage.encode_length]
    omega
  | updateLocalDatabaseRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, UpdateLocalDatabaseRequestMessage.encode_length]
    omega
  | messageDownloadRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, MessageDownloadRequestMessage.encode_length]
    omega
  | logoffRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, LogoffRequestMessage.encode_length]
    omega
  | orderEntryRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, OrderEntryRequestMessage.encode_length]
    omega
  | orderModificationRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, OrderModificationRequestMessage.encode_length]
    omega
  | orderCancellationRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, OrderCancellationRequestMessage.encode_length]
    omega
  | tradeCancellationRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, TradeCancellationRequestMessage.encode_length]
    omega
  | tradeModificationRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, TradeModificationRequestMessage.encode_length]
    omega
  | gatewayRouterRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, GatewayRouterRequestMessage.encode_length]
    omega
  | secureBoxRegistrationRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, SecureBoxRegistrationRequestMessage.encode_length]
    omega
  | boxSignOnRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, BoxSignOnRequestMessage.encode_length]
    omega
  | heartbeatMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, HeartbeatMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : ClientRegistrationPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [ClientMessagePayload.decode_encode, some_bind]
  rfl

end ClientRegistrationPacket

/-- Client Message Data -/
structure ClientMessageData where
  logTime : BitVec 32
  alphaChar : Alpha 2
  traderId : BitVec 32
  errorCode : BitVec 16
  headerTimestamp : BitVec 64
  timeStamp1 : Alpha 8
  timeStamp2 : Alpha 8
  messageLength : BitVec 16
  clientMessagePayload : ClientMessagePayload
  deriving DecidableEq, Repr

namespace ClientMessageData

def encode (message : ClientMessageData) : List UInt8 :=
  encodeUInt 2 (ClientMessagePayload.tag message.clientMessagePayload)
    ++ (encodeUInt 4 message.logTime
    ++ (Alpha.encode message.alphaChar
    ++ (encodeUInt 4 message.traderId
    ++ (encodeUInt 2 message.errorCode
    ++ (encodeUInt 8 message.headerTimestamp
    ++ (Alpha.encode message.timeStamp1
    ++ (Alpha.encode message.timeStamp2
    ++ (encodeUInt 2 message.messageLength
    ++ (ClientMessagePayload.encode message.clientMessagePayload)))))))))

def decode (bytes : List UInt8) : Option (ClientMessageData × List UInt8) := do
  let (transactionCode, bytes) ← decodeUInt 2 bytes
  let (logTime, bytes) ← decodeUInt 4 bytes
  let (alphaChar, bytes) ← Alpha.decode 2 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (errorCode, bytes) ← decodeUInt 2 bytes
  let (headerTimestamp, bytes) ← decodeUInt 8 bytes
  let (timeStamp1, bytes) ← Alpha.decode 8 bytes
  let (timeStamp2, bytes) ← Alpha.decode 8 bytes
  let (messageLength, bytes) ← decodeUInt 2 bytes
  let (clientMessagePayload, bytes) ← ClientMessagePayload.decode transactionCode bytes
  pure ({ logTime, alphaChar, traderId, errorCode, headerTimestamp, timeStamp1, timeStamp2, messageLength, clientMessagePayload }, bytes)

theorem encode_length_pos (message : ClientMessageData) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ClientMessageData) : (encode message).length ≤ 214 := by
  unfold encode
  cases message.clientMessagePayload with
  | logonRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, LogonRequestMessage.encode_length]
    omega
  | systemInformationRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, SystemInformationRequestMessage.encode_length]
    omega
  | updateLocalDatabaseRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, UpdateLocalDatabaseRequestMessage.encode_length]
    omega
  | messageDownloadRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, MessageDownloadRequestMessage.encode_length]
    omega
  | logoffRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, LogoffRequestMessage.encode_length]
    omega
  | orderEntryRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OrderEntryRequestMessage.encode_length]
    omega
  | orderModificationRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OrderModificationRequestMessage.encode_length]
    omega
  | orderCancellationRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OrderCancellationRequestMessage.encode_length]
    omega
  | tradeCancellationRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, TradeCancellationRequestMessage.encode_length]
    omega
  | tradeModificationRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, TradeModificationRequestMessage.encode_length]
    omega
  | gatewayRouterRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, GatewayRouterRequestMessage.encode_length]
    omega
  | secureBoxRegistrationRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, SecureBoxRegistrationRequestMessage.encode_length]
    omega
  | boxSignOnRequestMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, BoxSignOnRequestMessage.encode_length]
    omega
  | heartbeatMessage inner =>
    simp only [ClientMessagePayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, HeartbeatMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : ClientMessageData) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ClientMessagePayload.decode_encode, some_bind]
  rfl

end ClientMessageData

/-- Client Session Packet -/
structure ClientSessionPacket where
  checksum : Alpha 16
  clientMessageData : ClientMessageData
  deriving DecidableEq, Repr

namespace ClientSessionPacket

def encode (message : ClientSessionPacket) : List UInt8 :=
  Alpha.encode message.checksum
    ++ (ClientMessageData.encode message.clientMessageData)

def decode (bytes : List UInt8) : Option (ClientSessionPacket × List UInt8) := do
  let (checksum, bytes) ← Alpha.decode 16 bytes
  let (clientMessageData, bytes) ← ClientMessageData.decode bytes
  pure ({ checksum, clientMessageData }, bytes)

theorem encode_length_pos (message : ClientSessionPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

@[simp] theorem decode_encode (message : ClientSessionPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [ClientMessageData.decode_encode, some_bind]
  rfl

end ClientSessionPacket

/-- Client Direct Packet -/
structure ClientDirectPacket where
  packetSequenceNumber : BitVec 32
  clientPacketBody : Peeked (ClientRegistrationPacket) (ClientSessionPacket) ClientRegistrationPacket.encode ClientSessionPacket.encode 16 [89, 224]
  deriving DecidableEq, Repr

namespace ClientDirectPacket

def encodeBody (message : ClientDirectPacket) : List UInt8 :=
  encodeUInt 4 message.packetSequenceNumber
    ++ (encodePeek ClientRegistrationPacket.encode ClientSessionPacket.encode message.clientPacketBody)

def decodeBody (bytes : List UInt8) : Option (ClientDirectPacket × List UInt8) := do
  let (packetSequenceNumber, bytes) ← decodeUInt 4 bytes
  let (clientPacketBody, bytes) ← decodePeek 16 [89, 224] (decodeKeyed ClientRegistrationPacket.encode ClientRegistrationPacket.decode 16 [89, 224]) (decodeUnkeyed ClientSessionPacket.encode ClientSessionPacket.decode 16 [89, 224]) bytes
  pure ({ packetSequenceNumber, clientPacketBody }, bytes)

theorem decodeBody_encodeBody (message : ClientDirectPacket) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodePeek_encodePeek ClientRegistrationPacket.encode ClientRegistrationPacket.decode ClientSessionPacket.encode ClientSessionPacket.decode 16 [89, 224] ClientRegistrationPacket.decode_encode ClientSessionPacket.decode_encode, some_bind]
  rfl

/-- Size rule: Packet Length counts the bytes after it plus 2, so it is written from the body; the body has no bound the prefix must fit, so it is read by its content and the prefix is not checked -/
def encode (message : ClientDirectPacket) : List UInt8 :=
  encodeUInt 2 (BitVec.ofNat (8 * 2) ((encodeBody message).length + 2)) ++ encodeBody message

def decode (bytes : List UInt8) : Option (ClientDirectPacket × List UInt8) := do
  let (_, bytes) ← decodeUInt 2 bytes
  decodeBody bytes

@[simp] theorem decode_encode (message : ClientDirectPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  exact decodeBody_encodeBody message rest

theorem encode_length_pos (message : ClientDirectPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]
  omega

end ClientDirectPacket

/-- Client Packet -/
structure ClientPacket where
  clientDirectPacket : List ClientDirectPacket
  deriving DecidableEq, Repr

namespace ClientPacket

def encode (message : ClientPacket) : List UInt8 :=
  encodeMany ClientDirectPacket.encode message.clientDirectPacket

def decode (bytes : List UInt8) : Option ClientPacket := do
  let clientDirectPacket ← decodeAll ClientDirectPacket.decode bytes.length bytes
  pure { clientDirectPacket }

theorem decode_encode (message : ClientPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany ClientDirectPacket.encode ClientDirectPacket.decode ClientDirectPacket.decode_encode ClientDirectPacket.encode_length_pos message.clientDirectPacket _ (encodeMany_length_ge ClientDirectPacket.encode ClientDirectPacket.encode_length_pos message.clientDirectPacket), some_bind]
  rfl

end ClientPacket

end Omi.NseNseslbmOrderentryNnfdirectV27Client
