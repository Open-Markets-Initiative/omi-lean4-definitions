import Wire

/-!
# Beijing Stock Exchange Bjse Tcp Market Data v1.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.

License: MIT No Attribution
-/

namespace Omi.BjseBjsesecuritiesTcpmarketdataBjsebinaryV11

/-- Side: one byte code -/
def Side.codes : List UInt8 :=
  [0x31, 0x32, 0x47, 0x46]

inductive Side where
  | buy -- Buy
  | sell -- Sell
  | borrow -- Borrow
  | lend -- Lend
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .buy => 0x31
  | .sell => 0x32
  | .borrow => 0x47
  | .lend => 0x46
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x31 then .buy
  else if byte = 0x32 then .sell
  else if byte = 0x47 then .borrow
  else .lend

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | borrow => decide
  | lend => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Side) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Side × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Side) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Side) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Side) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Side

/-- Ord Type: one byte code -/
def OrdType.codes : List UInt8 :=
  [0x31, 0x32, 0x55]

inductive OrdType where
  | market -- Market
  | limit -- Limit
  | bestOwnSide -- Best Own Side
  | unlisted (byte : { byte : UInt8 // byte ∉ OrdType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrdType

def toByte : OrdType → UInt8
  | .market => 0x31
  | .limit => 0x32
  | .bestOwnSide => 0x55
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrdType :=
  if byte = 0x31 then .market
  else if byte = 0x32 then .limit
  else .bestOwnSide

def ofByte (byte : UInt8) : OrdType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrdType) : ofByte value.toByte = value := by
  cases value with
  | market => decide
  | limit => decide
  | bestOwnSide => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrdType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrdType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrdType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OrdType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OrdType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrdType

/-- Settl Type: one byte code -/
def SettlType.codes : List UInt8 :=
  [0x31, 0x32]

inductive SettlType where
  | gross -- Gross
  | multilateralNet -- Multilateral Net
  | unlisted (byte : { byte : UInt8 // byte ∉ SettlType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SettlType

def toByte : SettlType → UInt8
  | .gross => 0x31
  | .multilateralNet => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SettlType :=
  if byte = 0x31 then .gross
  else .multilateralNet

def ofByte (byte : UInt8) : SettlType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SettlType) : ofByte value.toByte = value := by
  cases value with
  | gross => decide
  | multilateralNet => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SettlType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SettlType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SettlType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SettlType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SettlType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SettlType

/-- Settl Period: one byte code -/
def SettlPeriod.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33]

inductive SettlPeriod where
  | tPlus0 -- T Plus 0
  | tPlus1 -- T Plus 1
  | tPlus2 -- T Plus 2
  | tPlus3 -- T Plus 3
  | unlisted (byte : { byte : UInt8 // byte ∉ SettlPeriod.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SettlPeriod

def toByte : SettlPeriod → UInt8
  | .tPlus0 => 0x30
  | .tPlus1 => 0x31
  | .tPlus2 => 0x32
  | .tPlus3 => 0x33
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SettlPeriod :=
  if byte = 0x30 then .tPlus0
  else if byte = 0x31 then .tPlus1
  else if byte = 0x32 then .tPlus2
  else .tPlus3

def ofByte (byte : UInt8) : SettlPeriod :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SettlPeriod) : ofByte value.toByte = value := by
  cases value with
  | tPlus0 => decide
  | tPlus1 => decide
  | tPlus2 => decide
  | tPlus3 => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SettlPeriod) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SettlPeriod × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SettlPeriod) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SettlPeriod) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SettlPeriod) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SettlPeriod

/-- Exec Type: one byte code -/
def ExecType.codes : List UInt8 :=
  [0x34, 0x46]

inductive ExecType where
  | cancelled -- Cancelled
  | trade -- Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ ExecType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExecType

def toByte : ExecType → UInt8
  | .cancelled => 0x34
  | .trade => 0x46
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExecType :=
  if byte = 0x34 then .cancelled
  else .trade

def ofByte (byte : UInt8) : ExecType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExecType) : ofByte value.toByte = value := by
  cases value with
  | cancelled => decide
  | trade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ExecType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ExecType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ExecType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ExecType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ExecType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ExecType

/-- Logon Message: 92 bytes -/
structure LogonMessage where
  senderCompId : Alpha 20
  targetCompId : Alpha 20
  heartBtInt : BitVec 32
  password : Alpha 16
  defaultApplVerId : Alpha 32
  deriving DecidableEq, Repr

namespace LogonMessage

def encode (message : LogonMessage) : List UInt8 :=
  Alpha.encode message.senderCompId
    ++ (Alpha.encode message.targetCompId
    ++ (encodeUInt 4 message.heartBtInt
    ++ (Alpha.encode message.password
    ++ (Alpha.encode message.defaultApplVerId))))

def decode (bytes : List UInt8) : Option (LogonMessage × List UInt8) := do
  let (senderCompId, bytes) ← Alpha.decode 20 bytes
  let (targetCompId, bytes) ← Alpha.decode 20 bytes
  let (heartBtInt, bytes) ← decodeUInt 4 bytes
  let (password, bytes) ← Alpha.decode 16 bytes
  let (defaultApplVerId, bytes) ← Alpha.decode 32 bytes
  pure ({ senderCompId, targetCompId, heartBtInt, password, defaultApplVerId }, bytes)

@[simp] theorem encode_length (message : LogonMessage) : (encode message).length = 92 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : LogonMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogonMessage) (rest : List UInt8) :
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

end LogonMessage

/-- Logout Message: 204 bytes -/
structure LogoutMessage where
  sessionStatus : BitVec 32
  text : Alpha 200
  deriving DecidableEq, Repr

namespace LogoutMessage

def encode (message : LogoutMessage) : List UInt8 :=
  encodeUInt 4 message.sessionStatus
    ++ (Alpha.encode message.text)

def decode (bytes : List UInt8) : Option (LogoutMessage × List UInt8) := do
  let (sessionStatus, bytes) ← decodeUInt 4 bytes
  let (text, bytes) ← Alpha.decode 200 bytes
  pure ({ sessionStatus, text }, bytes)

@[simp] theorem encode_length (message : LogoutMessage) : (encode message).length = 204 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : LogoutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogoutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LogoutMessage

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

/-- Channel Heartbeat Message: 20 bytes -/
structure ChannelHeartbeatMessage where
  channelNo : BitVec 16
  applLastSeqNum : BitVec 64
  endOfChannel : BitVec 16
  origTime : BitVec 64
  deriving DecidableEq, Repr

namespace ChannelHeartbeatMessage

def encode (message : ChannelHeartbeatMessage) : List UInt8 :=
  encodeUInt 2 message.channelNo
    ++ (encodeUInt 8 message.applLastSeqNum
    ++ (encodeUInt 2 message.endOfChannel
    ++ (encodeUInt 8 message.origTime)))

def decode (bytes : List UInt8) : Option (ChannelHeartbeatMessage × List UInt8) := do
  let (channelNo, bytes) ← decodeUInt 2 bytes
  let (applLastSeqNum, bytes) ← decodeUInt 8 bytes
  let (endOfChannel, bytes) ← decodeUInt 2 bytes
  let (origTime, bytes) ← decodeUInt 8 bytes
  pure ({ channelNo, applLastSeqNum, endOfChannel, origTime }, bytes)

@[simp] theorem encode_length (message : ChannelHeartbeatMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : ChannelHeartbeatMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ChannelHeartbeatMessage) (rest : List UInt8) :
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

end ChannelHeartbeatMessage

/-- Retransmission Message: 52 bytes -/
structure RetransmissionMessage where
  resendType : BitVec 8
  channelNo : BitVec 16
  applBegSeqNum : BitVec 64
  applEndSeqNum : BitVec 64
  newsId : Alpha 16
  resendStatus : BitVec 8
  rejectText : Alpha 16
  deriving DecidableEq, Repr

namespace RetransmissionMessage

def encode (message : RetransmissionMessage) : List UInt8 :=
  encodeUInt 1 message.resendType
    ++ (encodeUInt 2 message.channelNo
    ++ (encodeUInt 8 message.applBegSeqNum
    ++ (encodeUInt 8 message.applEndSeqNum
    ++ (Alpha.encode message.newsId
    ++ (encodeUInt 1 message.resendStatus
    ++ (Alpha.encode message.rejectText))))))

def decode (bytes : List UInt8) : Option (RetransmissionMessage × List UInt8) := do
  let (resendType, bytes) ← decodeUInt 1 bytes
  let (channelNo, bytes) ← decodeUInt 2 bytes
  let (applBegSeqNum, bytes) ← decodeUInt 8 bytes
  let (applEndSeqNum, bytes) ← decodeUInt 8 bytes
  let (newsId, bytes) ← Alpha.decode 16 bytes
  let (resendStatus, bytes) ← decodeUInt 1 bytes
  let (rejectText, bytes) ← Alpha.decode 16 bytes
  pure ({ resendType, channelNo, applBegSeqNum, applEndSeqNum, newsId, resendStatus, rejectText }, bytes)

@[simp] theorem encode_length (message : RetransmissionMessage) : (encode message).length = 52 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : RetransmissionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RetransmissionMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end RetransmissionMessage

/-- Md Stream I Ds: 15 bytes -/
structure MdStreamIDs where
  mdStreamId : Alpha 3
  stockNum : BitVec 32
  tradingPhaseCode : Alpha 8
  deriving DecidableEq, Repr

namespace MdStreamIDs

def encode (message : MdStreamIDs) : List UInt8 :=
  Alpha.encode message.mdStreamId
    ++ (encodeUInt 4 message.stockNum
    ++ (Alpha.encode message.tradingPhaseCode))

def decode (bytes : List UInt8) : Option (MdStreamIDs × List UInt8) := do
  let (mdStreamId, bytes) ← Alpha.decode 3 bytes
  let (stockNum, bytes) ← decodeUInt 4 bytes
  let (tradingPhaseCode, bytes) ← Alpha.decode 8 bytes
  pure ({ mdStreamId, stockNum, tradingPhaseCode }, bytes)

@[simp] theorem encode_length (message : MdStreamIDs) : (encode message).length = 15 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : MdStreamIDs) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MdStreamIDs) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MdStreamIDs

/-- Snapshot Channel Statistics Message -/
structure SnapshotChannelStatisticsMessage where
  origTime : BitVec 64
  channelNo : BitVec 16
  mdStreamIDs : Bounded 4 MdStreamIDs
  deriving DecidableEq, Repr

namespace SnapshotChannelStatisticsMessage

def encode (message : SnapshotChannelStatisticsMessage) : List UInt8 :=
  encodeUInt 8 message.origTime
    ++ (encodeUInt 2 message.channelNo
    ++ (encodeUInt 4 (BitVec.ofNat (8 * 4) message.mdStreamIDs.val.length)
    ++ (encodeMany MdStreamIDs.encode message.mdStreamIDs.val)))

def decode (bytes : List UInt8) : Option (SnapshotChannelStatisticsMessage × List UInt8) := do
  let (origTime, bytes) ← decodeUInt 8 bytes
  let (channelNo, bytes) ← decodeUInt 2 bytes
  let (noMdStreamId, bytes) ← decodeUInt 4 bytes
  let (mdStreamIDs_, bytes) ← decodeMany MdStreamIDs.decode noMdStreamId.toNat bytes
  if fits_mdStreamIDs : mdStreamIDs_.length < 256 ^ 4 then
    pure ({ origTime, channelNo, mdStreamIDs := ⟨mdStreamIDs_, fits_mdStreamIDs⟩ }, bytes)
  else none

theorem encode_length_pos (message : SnapshotChannelStatisticsMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SnapshotChannelStatisticsMessage) : (encode message).length ≤ 64424509439 := by
  have bound_mdStreamIDs := message.mdStreamIDs.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const MdStreamIDs.encode 15 MdStreamIDs.encode_length]
  omega

@[simp] theorem decode_encode (message : SnapshotChannelStatisticsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 4 MdStreamIDs.encode MdStreamIDs.decode MdStreamIDs.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.mdStreamIDs.length_lt]
  rfl

end SnapshotChannelStatisticsMessage

/-- Business Reject Message: 74 bytes -/
structure BusinessRejectMessage where
  refSeqNum : BitVec 64
  refMsgType : BitVec 32
  businessRejectRefId : Alpha 10
  businessRejectReason : BitVec 16
  businessRejectText : Alpha 50
  deriving DecidableEq, Repr

namespace BusinessRejectMessage

def encode (message : BusinessRejectMessage) : List UInt8 :=
  encodeUInt 8 message.refSeqNum
    ++ (encodeUInt 4 message.refMsgType
    ++ (Alpha.encode message.businessRejectRefId
    ++ (encodeUInt 2 message.businessRejectReason
    ++ (Alpha.encode message.businessRejectText))))

def decode (bytes : List UInt8) : Option (BusinessRejectMessage × List UInt8) := do
  let (refSeqNum, bytes) ← decodeUInt 8 bytes
  let (refMsgType, bytes) ← decodeUInt 4 bytes
  let (businessRejectRefId, bytes) ← Alpha.decode 10 bytes
  let (businessRejectReason, bytes) ← decodeUInt 2 bytes
  let (businessRejectText, bytes) ← Alpha.decode 50 bytes
  pure ({ refSeqNum, refMsgType, businessRejectRefId, businessRejectReason, businessRejectText }, bytes)

@[simp] theorem encode_length (message : BusinessRejectMessage) : (encode message).length = 74 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : BusinessRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BusinessRejectMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end BusinessRejectMessage

/-- Switch: 4 bytes -/
structure Switch where
  securitySwitchType : BitVec 16
  securitySwitchStatus : BitVec 16
  deriving DecidableEq, Repr

namespace Switch

def encode (message : Switch) : List UInt8 :=
  encodeUInt 2 message.securitySwitchType
    ++ (encodeUInt 2 message.securitySwitchStatus)

def decode (bytes : List UInt8) : Option (Switch × List UInt8) := do
  let (securitySwitchType, bytes) ← decodeUInt 2 bytes
  let (securitySwitchStatus, bytes) ← decodeUInt 2 bytes
  pure ({ securitySwitchType, securitySwitchStatus }, bytes)

@[simp] theorem encode_length (message : Switch) : (encode message).length = 4 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : Switch) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Switch) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end Switch

/-- Security Real Time Status Message -/
structure SecurityRealTimeStatusMessage where
  origTime : BitVec 64
  channelNo : BitVec 16
  securityId : Alpha 8
  securityIdSource : Alpha 4
  securitySymbol : Alpha 40
  switch : Bounded 4 Switch
  deriving DecidableEq, Repr

namespace SecurityRealTimeStatusMessage

def encode (message : SecurityRealTimeStatusMessage) : List UInt8 :=
  encodeUInt 8 message.origTime
    ++ (encodeUInt 2 message.channelNo
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (Alpha.encode message.securitySymbol
    ++ (encodeUInt 4 (BitVec.ofNat (8 * 4) message.switch.val.length)
    ++ (encodeMany Switch.encode message.switch.val))))))

def decode (bytes : List UInt8) : Option (SecurityRealTimeStatusMessage × List UInt8) := do
  let (origTime, bytes) ← decodeUInt 8 bytes
  let (channelNo, bytes) ← decodeUInt 2 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (securitySymbol, bytes) ← Alpha.decode 40 bytes
  let (noSwitch, bytes) ← decodeUInt 4 bytes
  let (switch_, bytes) ← decodeMany Switch.decode noSwitch.toNat bytes
  if fits_switch : switch_.length < 256 ^ 4 then
    pure ({ origTime, channelNo, securityId, securityIdSource, securitySymbol, switch := ⟨switch_, fits_switch⟩ }, bytes)
  else none

theorem encode_length_pos (message : SecurityRealTimeStatusMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SecurityRealTimeStatusMessage) : (encode message).length ≤ 17179869246 := by
  have bound_switch := message.switch.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, encodeMany_length_const Switch.encode 4 Switch.encode_length]
  omega

@[simp] theorem decode_encode (message : SecurityRealTimeStatusMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 4 Switch.encode Switch.decode Switch.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.switch.length_lt]
  rfl

end SecurityRealTimeStatusMessage

/-- Announcement Message -/
structure AnnouncementMessage where
  origTime : BitVec 64
  channelNo : BitVec 16
  newsId : Alpha 16
  headline : Alpha 128
  newsType : BitVec 8
  rawDataFormat : Alpha 8
  rawData : Bounded 4 UInt8
  deriving DecidableEq, Repr

namespace AnnouncementMessage

def encode (message : AnnouncementMessage) : List UInt8 :=
  encodeUInt 8 message.origTime
    ++ (encodeUInt 2 message.channelNo
    ++ (Alpha.encode message.newsId
    ++ (Alpha.encode message.headline
    ++ (encodeUInt 1 message.newsType
    ++ (Alpha.encode message.rawDataFormat
    ++ (encodeUInt 4 (BitVec.ofNat (8 * 4) message.rawData.val.length)
    ++ (encodeMany Byte.encode message.rawData.val)))))))

def decode (bytes : List UInt8) : Option (AnnouncementMessage × List UInt8) := do
  let (origTime, bytes) ← decodeUInt 8 bytes
  let (channelNo, bytes) ← decodeUInt 2 bytes
  let (newsId, bytes) ← Alpha.decode 16 bytes
  let (headline, bytes) ← Alpha.decode 128 bytes
  let (newsType, bytes) ← decodeUInt 1 bytes
  let (rawDataFormat, bytes) ← Alpha.decode 8 bytes
  let (rawDataLength, bytes) ← decodeUInt 4 bytes
  let (rawData_, bytes) ← decodeMany Byte.decode rawDataLength.toNat bytes
  if fits_rawData : rawData_.length < 256 ^ 4 then
    pure ({ origTime, channelNo, newsId, headline, newsType, rawDataFormat, rawData := ⟨rawData_, fits_rawData⟩ }, bytes)
  else none

theorem encode_length_pos (message : AnnouncementMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : AnnouncementMessage) : (encode message).length ≤ 4294967462 := by
  have bound_rawData := message.rawData.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

@[simp] theorem decode_encode (message : AnnouncementMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 4 Byte.encode Byte.decode Byte.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.rawData.length_lt]
  rfl

end AnnouncementMessage

/-- Orders: 8 bytes -/
structure Orders where
  orderQty : BitVec 64
  deriving DecidableEq, Repr

namespace Orders

def encode (message : Orders) : List UInt8 :=
  encodeUInt 8 message.orderQty

def decode (bytes : List UInt8) : Option (Orders × List UInt8) := do
  let (orderQty, bytes) ← decodeUInt 8 bytes
  pure ({ orderQty }, bytes)

@[simp] theorem encode_length (message : Orders) : (encode message).length = 8 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : Orders) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Orders) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end Orders

/-- Md Entries -/
structure MdEntries where
  mdEntryType : Alpha 2
  mdEntryPx : BitVec 64
  mdEntrySize : BitVec 64
  mdPriceLevel : BitVec 16
  numberOfOrders : BitVec 64
  orders : Bounded 4 Orders
  deriving DecidableEq, Repr

namespace MdEntries

def encode (message : MdEntries) : List UInt8 :=
  Alpha.encode message.mdEntryType
    ++ (encodeUInt 8 message.mdEntryPx
    ++ (encodeUInt 8 message.mdEntrySize
    ++ (encodeUInt 2 message.mdPriceLevel
    ++ (encodeUInt 8 message.numberOfOrders
    ++ (encodeUInt 4 (BitVec.ofNat (8 * 4) message.orders.val.length)
    ++ (encodeMany Orders.encode message.orders.val))))))

def decode (bytes : List UInt8) : Option (MdEntries × List UInt8) := do
  let (mdEntryType, bytes) ← Alpha.decode 2 bytes
  let (mdEntryPx, bytes) ← decodeUInt 8 bytes
  let (mdEntrySize, bytes) ← decodeUInt 8 bytes
  let (mdPriceLevel, bytes) ← decodeUInt 2 bytes
  let (numberOfOrders, bytes) ← decodeUInt 8 bytes
  let (noOrders, bytes) ← decodeUInt 4 bytes
  let (orders_, bytes) ← decodeMany Orders.decode noOrders.toNat bytes
  if fits_orders : orders_.length < 256 ^ 4 then
    pure ({ mdEntryType, mdEntryPx, mdEntrySize, mdPriceLevel, numberOfOrders, orders := ⟨orders_, fits_orders⟩ }, bytes)
  else none

theorem encode_length_pos (message : MdEntries) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MdEntries) : (encode message).length ≤ 34359738392 := by
  have bound_orders := message.orders.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, encodeMany_length_const Orders.encode 8 Orders.encode_length]
  omega

@[simp] theorem decode_encode (message : MdEntries) (rest : List UInt8) :
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
  rw [decodeMany_bounded 4 Orders.encode Orders.decode Orders.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.orders.length_lt]
  rfl

end MdEntries

/-- Sub Trading Phase Codes: 9 bytes -/
structure SubTradingPhaseCodes where
  subTradingPhaseCode : Alpha 8
  tradingType : BitVec 8
  deriving DecidableEq, Repr

namespace SubTradingPhaseCodes

def encode (message : SubTradingPhaseCodes) : List UInt8 :=
  Alpha.encode message.subTradingPhaseCode
    ++ (encodeUInt 1 message.tradingType)

def decode (bytes : List UInt8) : Option (SubTradingPhaseCodes × List UInt8) := do
  let (subTradingPhaseCode, bytes) ← Alpha.decode 8 bytes
  let (tradingType, bytes) ← decodeUInt 1 bytes
  pure ({ subTradingPhaseCode, tradingType }, bytes)

@[simp] theorem encode_length (message : SubTradingPhaseCodes) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SubTradingPhaseCodes) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SubTradingPhaseCodes) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SubTradingPhaseCodes

/-- Bond Spot Trading Snapshot Message -/
structure BondSpotTradingSnapshotMessage where
  origTime : BitVec 64
  channelNo : BitVec 16
  mdStreamId : Alpha 3
  securityId : Alpha 8
  securityIdSource : Alpha 4
  tradingPhaseCode : Alpha 8
  preClosePx : BitVec 64
  numTrades : BitVec 64
  totalVolumeTrade : BitVec 64
  totalValueTrade : BitVec 64
  mdEntries : Bounded 4 MdEntries
  subTradingPhaseCodes : Bounded 4 SubTradingPhaseCodes
  auctionVolumeTrade : BitVec 64
  auctionValueTrade : BitVec 64
  tradeTime : BitVec 64
  deriving DecidableEq, Repr

namespace BondSpotTradingSnapshotMessage

def encode (message : BondSpotTradingSnapshotMessage) : List UInt8 :=
  encodeUInt 8 message.origTime
    ++ (encodeUInt 2 message.channelNo
    ++ (Alpha.encode message.mdStreamId
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (Alpha.encode message.tradingPhaseCode
    ++ (encodeUInt 8 message.preClosePx
    ++ (encodeUInt 8 message.numTrades
    ++ (encodeUInt 8 message.totalVolumeTrade
    ++ (encodeUInt 8 message.totalValueTrade
    ++ (encodeUInt 4 (BitVec.ofNat (8 * 4) message.mdEntries.val.length)
    ++ (encodeMany MdEntries.encode message.mdEntries.val
    ++ (encodeUInt 4 (BitVec.ofNat (8 * 4) message.subTradingPhaseCodes.val.length)
    ++ (encodeMany SubTradingPhaseCodes.encode message.subTradingPhaseCodes.val
    ++ (encodeUInt 8 message.auctionVolumeTrade
    ++ (encodeUInt 8 message.auctionValueTrade
    ++ (encodeUInt 8 message.tradeTime))))))))))))))))

def decode (bytes : List UInt8) : Option (BondSpotTradingSnapshotMessage × List UInt8) := do
  let (origTime, bytes) ← decodeUInt 8 bytes
  let (channelNo, bytes) ← decodeUInt 2 bytes
  let (mdStreamId, bytes) ← Alpha.decode 3 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (tradingPhaseCode, bytes) ← Alpha.decode 8 bytes
  let (preClosePx, bytes) ← decodeUInt 8 bytes
  let (numTrades, bytes) ← decodeUInt 8 bytes
  let (totalVolumeTrade, bytes) ← decodeUInt 8 bytes
  let (totalValueTrade, bytes) ← decodeUInt 8 bytes
  let (noMdEntries, bytes) ← decodeUInt 4 bytes
  let (mdEntries_, bytes) ← decodeMany MdEntries.decode noMdEntries.toNat bytes
  let (noSubTradingPhaseCodes, bytes) ← decodeUInt 4 bytes
  let (subTradingPhaseCodes_, bytes) ← decodeMany SubTradingPhaseCodes.decode noSubTradingPhaseCodes.toNat bytes
  let (auctionVolumeTrade, bytes) ← decodeUInt 8 bytes
  let (auctionValueTrade, bytes) ← decodeUInt 8 bytes
  let (tradeTime, bytes) ← decodeUInt 8 bytes
  if fits_mdEntries : mdEntries_.length < 256 ^ 4 then
    if fits_subTradingPhaseCodes : subTradingPhaseCodes_.length < 256 ^ 4 then
      pure ({ origTime, channelNo, mdStreamId, securityId, securityIdSource, tradingPhaseCode, preClosePx, numTrades, totalVolumeTrade, totalValueTrade, mdEntries := ⟨mdEntries_, fits_mdEntries⟩, subTradingPhaseCodes := ⟨subTradingPhaseCodes_, fits_subTradingPhaseCodes⟩, auctionVolumeTrade, auctionValueTrade, tradeTime }, bytes)
    else none
  else none

theorem encode_length_pos (message : BondSpotTradingSnapshotMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : BondSpotTradingSnapshotMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeMany_bounded 4 MdEntries.encode MdEntries.decode MdEntries.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeMany_bounded 4 SubTradingPhaseCodes.encode SubTradingPhaseCodes.decode SubTradingPhaseCodes.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [dite_eq_left message.mdEntries.length_lt, dite_eq_left message.subTradingPhaseCodes.length_lt]
  rfl

end BondSpotTradingSnapshotMessage

/-- Auction Trading Snapshot Message -/
structure AuctionTradingSnapshotMessage where
  origTime : BitVec 64
  channelNo : BitVec 16
  mdStreamId : Alpha 3
  securityId : Alpha 8
  securityIdSource : Alpha 4
  tradingPhaseCode : Alpha 8
  preClosePx : BitVec 64
  numTrades : BitVec 64
  totalVolumeTrade : BitVec 64
  totalValueTrade : BitVec 64
  mdEntries : Bounded 4 MdEntries
  deriving DecidableEq, Repr

namespace AuctionTradingSnapshotMessage

def encode (message : AuctionTradingSnapshotMessage) : List UInt8 :=
  encodeUInt 8 message.origTime
    ++ (encodeUInt 2 message.channelNo
    ++ (Alpha.encode message.mdStreamId
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (Alpha.encode message.tradingPhaseCode
    ++ (encodeUInt 8 message.preClosePx
    ++ (encodeUInt 8 message.numTrades
    ++ (encodeUInt 8 message.totalVolumeTrade
    ++ (encodeUInt 8 message.totalValueTrade
    ++ (encodeUInt 4 (BitVec.ofNat (8 * 4) message.mdEntries.val.length)
    ++ (encodeMany MdEntries.encode message.mdEntries.val)))))))))))

def decode (bytes : List UInt8) : Option (AuctionTradingSnapshotMessage × List UInt8) := do
  let (origTime, bytes) ← decodeUInt 8 bytes
  let (channelNo, bytes) ← decodeUInt 2 bytes
  let (mdStreamId, bytes) ← Alpha.decode 3 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (tradingPhaseCode, bytes) ← Alpha.decode 8 bytes
  let (preClosePx, bytes) ← decodeUInt 8 bytes
  let (numTrades, bytes) ← decodeUInt 8 bytes
  let (totalVolumeTrade, bytes) ← decodeUInt 8 bytes
  let (totalValueTrade, bytes) ← decodeUInt 8 bytes
  let (noMdEntries, bytes) ← decodeUInt 4 bytes
  let (mdEntries_, bytes) ← decodeMany MdEntries.decode noMdEntries.toNat bytes
  if fits_mdEntries : mdEntries_.length < 256 ^ 4 then
    pure ({ origTime, channelNo, mdStreamId, securityId, securityIdSource, tradingPhaseCode, preClosePx, numTrades, totalVolumeTrade, totalValueTrade, mdEntries := ⟨mdEntries_, fits_mdEntries⟩ }, bytes)
  else none

theorem encode_length_pos (message : AuctionTradingSnapshotMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : AuctionTradingSnapshotMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 4 MdEntries.encode MdEntries.decode MdEntries.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.mdEntries.length_lt]
  rfl

end AuctionTradingSnapshotMessage

/-- Index Md Entries: 10 bytes -/
structure IndexMdEntries where
  mdEntryType : Alpha 2
  mdEntryPx : BitVec 64
  deriving DecidableEq, Repr

namespace IndexMdEntries

def encode (message : IndexMdEntries) : List UInt8 :=
  Alpha.encode message.mdEntryType
    ++ (encodeUInt 8 message.mdEntryPx)

def decode (bytes : List UInt8) : Option (IndexMdEntries × List UInt8) := do
  let (mdEntryType, bytes) ← Alpha.decode 2 bytes
  let (mdEntryPx, bytes) ← decodeUInt 8 bytes
  pure ({ mdEntryType, mdEntryPx }, bytes)

@[simp] theorem encode_length (message : IndexMdEntries) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : IndexMdEntries) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IndexMdEntries) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end IndexMdEntries

/-- Index Snapshot Message -/
structure IndexSnapshotMessage where
  origTime : BitVec 64
  channelNo : BitVec 16
  mdStreamId : Alpha 3
  securityId : Alpha 8
  securityIdSource : Alpha 4
  tradingPhaseCode : Alpha 8
  preClosePx : BitVec 64
  numTrades : BitVec 64
  totalVolumeTrade : BitVec 64
  totalValueTrade : BitVec 64
  indexMdEntries : Bounded 4 IndexMdEntries
  deriving DecidableEq, Repr

namespace IndexSnapshotMessage

def encode (message : IndexSnapshotMessage) : List UInt8 :=
  encodeUInt 8 message.origTime
    ++ (encodeUInt 2 message.channelNo
    ++ (Alpha.encode message.mdStreamId
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (Alpha.encode message.tradingPhaseCode
    ++ (encodeUInt 8 message.preClosePx
    ++ (encodeUInt 8 message.numTrades
    ++ (encodeUInt 8 message.totalVolumeTrade
    ++ (encodeUInt 8 message.totalValueTrade
    ++ (encodeUInt 4 (BitVec.ofNat (8 * 4) message.indexMdEntries.val.length)
    ++ (encodeMany IndexMdEntries.encode message.indexMdEntries.val)))))))))))

def decode (bytes : List UInt8) : Option (IndexSnapshotMessage × List UInt8) := do
  let (origTime, bytes) ← decodeUInt 8 bytes
  let (channelNo, bytes) ← decodeUInt 2 bytes
  let (mdStreamId, bytes) ← Alpha.decode 3 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (tradingPhaseCode, bytes) ← Alpha.decode 8 bytes
  let (preClosePx, bytes) ← decodeUInt 8 bytes
  let (numTrades, bytes) ← decodeUInt 8 bytes
  let (totalVolumeTrade, bytes) ← decodeUInt 8 bytes
  let (totalValueTrade, bytes) ← decodeUInt 8 bytes
  let (noMdEntries, bytes) ← decodeUInt 4 bytes
  let (indexMdEntries_, bytes) ← decodeMany IndexMdEntries.decode noMdEntries.toNat bytes
  if fits_indexMdEntries : indexMdEntries_.length < 256 ^ 4 then
    pure ({ origTime, channelNo, mdStreamId, securityId, securityIdSource, tradingPhaseCode, preClosePx, numTrades, totalVolumeTrade, totalValueTrade, indexMdEntries := ⟨indexMdEntries_, fits_indexMdEntries⟩ }, bytes)
  else none

theorem encode_length_pos (message : IndexSnapshotMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : IndexSnapshotMessage) : (encode message).length ≤ 42949673019 := by
  have bound_indexMdEntries := message.indexMdEntries.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, encodeMany_length_const IndexMdEntries.encode 10 IndexMdEntries.encode_length]
  omega

@[simp] theorem decode_encode (message : IndexSnapshotMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 4 IndexMdEntries.encode IndexMdEntries.decode IndexMdEntries.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.indexMdEntries.length_lt]
  rfl

end IndexSnapshotMessage

/-- Bond Spot Matching Large Order Tick Message: 53 bytes -/
structure BondSpotMatchingLargeOrderTickMessage where
  channelNo : BitVec 16
  applSeqNum : BitVec 64
  mdStreamId : Alpha 3
  securityId : Alpha 8
  securityIdSource : Alpha 4
  price : BitVec 64
  orderQty : BitVec 64
  side : Side
  transactTime : BitVec 64
  ordType : OrdType
  settlType : SettlType
  settlPeriod : SettlPeriod
  deriving DecidableEq, Repr

namespace BondSpotMatchingLargeOrderTickMessage

def encode (message : BondSpotMatchingLargeOrderTickMessage) : List UInt8 :=
  encodeUInt 2 message.channelNo
    ++ (encodeUInt 8 message.applSeqNum
    ++ (Alpha.encode message.mdStreamId
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 8 message.price
    ++ (encodeUInt 8 message.orderQty
    ++ (Side.encode message.side
    ++ (encodeUInt 8 message.transactTime
    ++ (OrdType.encode message.ordType
    ++ (SettlType.encode message.settlType
    ++ (SettlPeriod.encode message.settlPeriod)))))))))))

def decode (bytes : List UInt8) : Option (BondSpotMatchingLargeOrderTickMessage × List UInt8) := do
  let (channelNo, bytes) ← decodeUInt 2 bytes
  let (applSeqNum, bytes) ← decodeUInt 8 bytes
  let (mdStreamId, bytes) ← Alpha.decode 3 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (orderQty, bytes) ← decodeUInt 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  let (ordType, bytes) ← OrdType.decode bytes
  let (settlType, bytes) ← SettlType.decode bytes
  let (settlPeriod, bytes) ← SettlPeriod.decode bytes
  pure ({ channelNo, applSeqNum, mdStreamId, securityId, securityIdSource, price, orderQty, side, transactTime, ordType, settlType, settlPeriod }, bytes)

@[simp] theorem encode_length (message : BondSpotMatchingLargeOrderTickMessage) : (encode message).length = 53 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, Side.encode_length, OrdType.encode_length, SettlType.encode_length, SettlPeriod.encode_length]

theorem encode_length_pos (message : BondSpotMatchingLargeOrderTickMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BondSpotMatchingLargeOrderTickMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OrdType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SettlType.decode_encode, some_bind]
  dsimp only
  rw [SettlPeriod.decode_encode, some_bind]
  rfl

end BondSpotMatchingLargeOrderTickMessage

/-- Agreement Trading Order Tick Message: 54 bytes -/
structure AgreementTradingOrderTickMessage where
  channelNo : BitVec 16
  applSeqNum : BitVec 64
  mdStreamId : Alpha 3
  securityId : Alpha 8
  securityIdSource : Alpha 4
  price : BitVec 64
  orderQty : BitVec 64
  side : Side
  transactTime : BitVec 64
  confirmId : BitVec 32
  deriving DecidableEq, Repr

namespace AgreementTradingOrderTickMessage

def encode (message : AgreementTradingOrderTickMessage) : List UInt8 :=
  encodeUInt 2 message.channelNo
    ++ (encodeUInt 8 message.applSeqNum
    ++ (Alpha.encode message.mdStreamId
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 8 message.price
    ++ (encodeUInt 8 message.orderQty
    ++ (Side.encode message.side
    ++ (encodeUInt 8 message.transactTime
    ++ (encodeUInt 4 message.confirmId)))))))))

def decode (bytes : List UInt8) : Option (AgreementTradingOrderTickMessage × List UInt8) := do
  let (channelNo, bytes) ← decodeUInt 2 bytes
  let (applSeqNum, bytes) ← decodeUInt 8 bytes
  let (mdStreamId, bytes) ← Alpha.decode 3 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (orderQty, bytes) ← decodeUInt 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  let (confirmId, bytes) ← decodeUInt 4 bytes
  pure ({ channelNo, applSeqNum, mdStreamId, securityId, securityIdSource, price, orderQty, side, transactTime, confirmId }, bytes)

@[simp] theorem encode_length (message : AgreementTradingOrderTickMessage) : (encode message).length = 54 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, Side.encode_length]

theorem encode_length_pos (message : AgreementTradingOrderTickMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AgreementTradingOrderTickMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AgreementTradingOrderTickMessage

/-- Securities Lending Order Tick Message: 53 bytes -/
structure SecuritiesLendingOrderTickMessage where
  channelNo : BitVec 16
  applSeqNum : BitVec 64
  mdStreamId : Alpha 3
  securityId : Alpha 8
  securityIdSource : Alpha 4
  price : BitVec 64
  orderQty : BitVec 64
  side : Side
  transactTime : BitVec 64
  expirationDays : BitVec 16
  expirationType : BitVec 8
  deriving DecidableEq, Repr

namespace SecuritiesLendingOrderTickMessage

def encode (message : SecuritiesLendingOrderTickMessage) : List UInt8 :=
  encodeUInt 2 message.channelNo
    ++ (encodeUInt 8 message.applSeqNum
    ++ (Alpha.encode message.mdStreamId
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 8 message.price
    ++ (encodeUInt 8 message.orderQty
    ++ (Side.encode message.side
    ++ (encodeUInt 8 message.transactTime
    ++ (encodeUInt 2 message.expirationDays
    ++ (encodeUInt 1 message.expirationType))))))))))

def decode (bytes : List UInt8) : Option (SecuritiesLendingOrderTickMessage × List UInt8) := do
  let (channelNo, bytes) ← decodeUInt 2 bytes
  let (applSeqNum, bytes) ← decodeUInt 8 bytes
  let (mdStreamId, bytes) ← Alpha.decode 3 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (orderQty, bytes) ← decodeUInt 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  let (expirationDays, bytes) ← decodeUInt 2 bytes
  let (expirationType, bytes) ← decodeUInt 1 bytes
  pure ({ channelNo, applSeqNum, mdStreamId, securityId, securityIdSource, price, orderQty, side, transactTime, expirationDays, expirationType }, bytes)

@[simp] theorem encode_length (message : SecuritiesLendingOrderTickMessage) : (encode message).length = 53 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, Side.encode_length]

theorem encode_length_pos (message : SecuritiesLendingOrderTickMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecuritiesLendingOrderTickMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SecuritiesLendingOrderTickMessage

/-- Bond Spot Matching Large Trade Tick Message: 76 bytes -/
structure BondSpotMatchingLargeTradeTickMessage where
  channelNo : BitVec 16
  applSeqNum : BitVec 64
  mdStreamId : Alpha 3
  securityId : Alpha 8
  securityIdSource : Alpha 4
  bidApplSeqNum : BitVec 64
  askApplSeqNum : BitVec 64
  tradePrice : BitVec 64
  tradeQty : BitVec 64
  tradeMoney : BitVec 64
  execType : ExecType
  transactTime : BitVec 64
  settlPeriod : SettlPeriod
  settlType : SettlType
  deriving DecidableEq, Repr

namespace BondSpotMatchingLargeTradeTickMessage

def encode (message : BondSpotMatchingLargeTradeTickMessage) : List UInt8 :=
  encodeUInt 2 message.channelNo
    ++ (encodeUInt 8 message.applSeqNum
    ++ (Alpha.encode message.mdStreamId
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 8 message.bidApplSeqNum
    ++ (encodeUInt 8 message.askApplSeqNum
    ++ (encodeUInt 8 message.tradePrice
    ++ (encodeUInt 8 message.tradeQty
    ++ (encodeUInt 8 message.tradeMoney
    ++ (ExecType.encode message.execType
    ++ (encodeUInt 8 message.transactTime
    ++ (SettlPeriod.encode message.settlPeriod
    ++ (SettlType.encode message.settlType)))))))))))))

def decode (bytes : List UInt8) : Option (BondSpotMatchingLargeTradeTickMessage × List UInt8) := do
  let (channelNo, bytes) ← decodeUInt 2 bytes
  let (applSeqNum, bytes) ← decodeUInt 8 bytes
  let (mdStreamId, bytes) ← Alpha.decode 3 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (bidApplSeqNum, bytes) ← decodeUInt 8 bytes
  let (askApplSeqNum, bytes) ← decodeUInt 8 bytes
  let (tradePrice, bytes) ← decodeUInt 8 bytes
  let (tradeQty, bytes) ← decodeUInt 8 bytes
  let (tradeMoney, bytes) ← decodeUInt 8 bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  let (settlPeriod, bytes) ← SettlPeriod.decode bytes
  let (settlType, bytes) ← SettlType.decode bytes
  pure ({ channelNo, applSeqNum, mdStreamId, securityId, securityIdSource, bidApplSeqNum, askApplSeqNum, tradePrice, tradeQty, tradeMoney, execType, transactTime, settlPeriod, settlType }, bytes)

@[simp] theorem encode_length (message : BondSpotMatchingLargeTradeTickMessage) : (encode message).length = 76 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, ExecType.encode_length, SettlPeriod.encode_length, SettlType.encode_length]

theorem encode_length_pos (message : BondSpotMatchingLargeTradeTickMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BondSpotMatchingLargeTradeTickMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, SettlPeriod.decode_encode, some_bind]
  dsimp only
  rw [SettlType.decode_encode, some_bind]
  rfl

end BondSpotMatchingLargeTradeTickMessage

/-- Bond Spot Negotiated Trade Tick Message: 76 bytes -/
structure BondSpotNegotiatedTradeTickMessage where
  channelNo : BitVec 16
  applSeqNum : BitVec 64
  mdStreamId : Alpha 3
  securityId : Alpha 8
  securityIdSource : Alpha 4
  bidApplSeqNum : BitVec 64
  askApplSeqNum : BitVec 64
  tradePrice : BitVec 64
  tradeQty : BitVec 64
  tradeMoney : BitVec 64
  execType : ExecType
  transactTime : BitVec 64
  settlPeriod : SettlPeriod
  settlType : SettlType
  deriving DecidableEq, Repr

namespace BondSpotNegotiatedTradeTickMessage

def encode (message : BondSpotNegotiatedTradeTickMessage) : List UInt8 :=
  encodeUInt 2 message.channelNo
    ++ (encodeUInt 8 message.applSeqNum
    ++ (Alpha.encode message.mdStreamId
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 8 message.bidApplSeqNum
    ++ (encodeUInt 8 message.askApplSeqNum
    ++ (encodeUInt 8 message.tradePrice
    ++ (encodeUInt 8 message.tradeQty
    ++ (encodeUInt 8 message.tradeMoney
    ++ (ExecType.encode message.execType
    ++ (encodeUInt 8 message.transactTime
    ++ (SettlPeriod.encode message.settlPeriod
    ++ (SettlType.encode message.settlType)))))))))))))

def decode (bytes : List UInt8) : Option (BondSpotNegotiatedTradeTickMessage × List UInt8) := do
  let (channelNo, bytes) ← decodeUInt 2 bytes
  let (applSeqNum, bytes) ← decodeUInt 8 bytes
  let (mdStreamId, bytes) ← Alpha.decode 3 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (bidApplSeqNum, bytes) ← decodeUInt 8 bytes
  let (askApplSeqNum, bytes) ← decodeUInt 8 bytes
  let (tradePrice, bytes) ← decodeUInt 8 bytes
  let (tradeQty, bytes) ← decodeUInt 8 bytes
  let (tradeMoney, bytes) ← decodeUInt 8 bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  let (settlPeriod, bytes) ← SettlPeriod.decode bytes
  let (settlType, bytes) ← SettlType.decode bytes
  pure ({ channelNo, applSeqNum, mdStreamId, securityId, securityIdSource, bidApplSeqNum, askApplSeqNum, tradePrice, tradeQty, tradeMoney, execType, transactTime, settlPeriod, settlType }, bytes)

@[simp] theorem encode_length (message : BondSpotNegotiatedTradeTickMessage) : (encode message).length = 76 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, ExecType.encode_length, SettlPeriod.encode_length, SettlType.encode_length]

theorem encode_length_pos (message : BondSpotNegotiatedTradeTickMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BondSpotNegotiatedTradeTickMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, SettlPeriod.decode_encode, some_bind]
  dsimp only
  rw [SettlType.decode_encode, some_bind]
  rfl

end BondSpotNegotiatedTradeTickMessage

/-- Securities Lending Trade Tick Message: 74 bytes -/
structure SecuritiesLendingTradeTickMessage where
  channelNo : BitVec 16
  applSeqNum : BitVec 64
  mdStreamId : Alpha 3
  securityId : Alpha 8
  securityIdSource : Alpha 4
  bidApplSeqNum : BitVec 64
  askApplSeqNum : BitVec 64
  tradePrice : BitVec 64
  tradeQty : BitVec 64
  tradeMoney : BitVec 64
  execType : ExecType
  transactTime : BitVec 64
  deriving DecidableEq, Repr

namespace SecuritiesLendingTradeTickMessage

def encode (message : SecuritiesLendingTradeTickMessage) : List UInt8 :=
  encodeUInt 2 message.channelNo
    ++ (encodeUInt 8 message.applSeqNum
    ++ (Alpha.encode message.mdStreamId
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.securityIdSource
    ++ (encodeUInt 8 message.bidApplSeqNum
    ++ (encodeUInt 8 message.askApplSeqNum
    ++ (encodeUInt 8 message.tradePrice
    ++ (encodeUInt 8 message.tradeQty
    ++ (encodeUInt 8 message.tradeMoney
    ++ (ExecType.encode message.execType
    ++ (encodeUInt 8 message.transactTime)))))))))))

def decode (bytes : List UInt8) : Option (SecuritiesLendingTradeTickMessage × List UInt8) := do
  let (channelNo, bytes) ← decodeUInt 2 bytes
  let (applSeqNum, bytes) ← decodeUInt 8 bytes
  let (mdStreamId, bytes) ← Alpha.decode 3 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (securityIdSource, bytes) ← Alpha.decode 4 bytes
  let (bidApplSeqNum, bytes) ← decodeUInt 8 bytes
  let (askApplSeqNum, bytes) ← decodeUInt 8 bytes
  let (tradePrice, bytes) ← decodeUInt 8 bytes
  let (tradeQty, bytes) ← decodeUInt 8 bytes
  let (tradeMoney, bytes) ← decodeUInt 8 bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  pure ({ channelNo, applSeqNum, mdStreamId, securityId, securityIdSource, bidApplSeqNum, askApplSeqNum, tradePrice, tradeQty, tradeMoney, execType, transactTime }, bytes)

@[simp] theorem encode_length (message : SecuritiesLendingTradeTickMessage) : (encode message).length = 74 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, ExecType.encode_length]

theorem encode_length_pos (message : SecuritiesLendingTradeTickMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecuritiesLendingTradeTickMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SecuritiesLendingTradeTickMessage

/-- Any Payload, selected by Msg Type -/
inductive Payload where
  | logonMessage (message : LogonMessage) -- 1
  | logoutMessage (message : LogoutMessage) -- 2
  | heartbeatMessage (message : HeartbeatMessage) -- 3
  | channelHeartbeatMessage (message : ChannelHeartbeatMessage) -- 301000
  | retransmissionMessage (message : RetransmissionMessage) -- 302000
  | snapshotChannelStatisticsMessage (message : SnapshotChannelStatisticsMessage) -- 303000
  | businessRejectMessage (message : BusinessRejectMessage) -- 8
  | securityRealTimeStatusMessage (message : SecurityRealTimeStatusMessage) -- 304000
  | announcementMessage (message : AnnouncementMessage) -- 305000
  | bondSpotTradingSnapshotMessage (message : BondSpotTradingSnapshotMessage) -- 306001
  | auctionTradingSnapshotMessage (message : AuctionTradingSnapshotMessage) -- 306002
  | indexSnapshotMessage (message : IndexSnapshotMessage) -- 306003
  | bondSpotMatchingLargeOrderTickMessage (message : BondSpotMatchingLargeOrderTickMessage) -- 307011
  | agreementTradingOrderTickMessage (message : AgreementTradingOrderTickMessage) -- 307021
  | securitiesLendingOrderTickMessage (message : SecuritiesLendingOrderTickMessage) -- 307023
  | bondSpotMatchingLargeTradeTickMessage (message : BondSpotMatchingLargeTradeTickMessage) -- 308011
  | bondSpotNegotiatedTradeTickMessage (message : BondSpotNegotiatedTradeTickMessage) -- 308012
  | securitiesLendingTradeTickMessage (message : SecuritiesLendingTradeTickMessage) -- 308023
  deriving DecidableEq, Repr

namespace Payload

/-- The Msg Type each message is sent under -/
def tag : Payload → BitVec 32
  | .logonMessage _ => 1
  | .logoutMessage _ => 2
  | .heartbeatMessage _ => 3
  | .channelHeartbeatMessage _ => 301000
  | .retransmissionMessage _ => 302000
  | .snapshotChannelStatisticsMessage _ => 303000
  | .businessRejectMessage _ => 8
  | .securityRealTimeStatusMessage _ => 304000
  | .announcementMessage _ => 305000
  | .bondSpotTradingSnapshotMessage _ => 306001
  | .auctionTradingSnapshotMessage _ => 306002
  | .indexSnapshotMessage _ => 306003
  | .bondSpotMatchingLargeOrderTickMessage _ => 307011
  | .agreementTradingOrderTickMessage _ => 307021
  | .securitiesLendingOrderTickMessage _ => 307023
  | .bondSpotMatchingLargeTradeTickMessage _ => 308011
  | .bondSpotNegotiatedTradeTickMessage _ => 308012
  | .securitiesLendingTradeTickMessage _ => 308023

def encode : Payload → List UInt8
  | .logonMessage message => LogonMessage.encode message
  | .logoutMessage message => LogoutMessage.encode message
  | .heartbeatMessage message => HeartbeatMessage.encode message
  | .channelHeartbeatMessage message => ChannelHeartbeatMessage.encode message
  | .retransmissionMessage message => RetransmissionMessage.encode message
  | .snapshotChannelStatisticsMessage message => SnapshotChannelStatisticsMessage.encode message
  | .businessRejectMessage message => BusinessRejectMessage.encode message
  | .securityRealTimeStatusMessage message => SecurityRealTimeStatusMessage.encode message
  | .announcementMessage message => AnnouncementMessage.encode message
  | .bondSpotTradingSnapshotMessage message => BondSpotTradingSnapshotMessage.encode message
  | .auctionTradingSnapshotMessage message => AuctionTradingSnapshotMessage.encode message
  | .indexSnapshotMessage message => IndexSnapshotMessage.encode message
  | .bondSpotMatchingLargeOrderTickMessage message => BondSpotMatchingLargeOrderTickMessage.encode message
  | .agreementTradingOrderTickMessage message => AgreementTradingOrderTickMessage.encode message
  | .securitiesLendingOrderTickMessage message => SecuritiesLendingOrderTickMessage.encode message
  | .bondSpotMatchingLargeTradeTickMessage message => BondSpotMatchingLargeTradeTickMessage.encode message
  | .bondSpotNegotiatedTradeTickMessage message => BondSpotNegotiatedTradeTickMessage.encode message
  | .securitiesLendingTradeTickMessage message => SecuritiesLendingTradeTickMessage.encode message

def decode (tag : BitVec 32) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 1 then (LogonMessage.decode bytes).map fun (message, rest) => (.logonMessage message, rest)
  else if tag = 2 then (LogoutMessage.decode bytes).map fun (message, rest) => (.logoutMessage message, rest)
  else if tag = 3 then (HeartbeatMessage.decode bytes).map fun (message, rest) => (.heartbeatMessage message, rest)
  else if tag = 301000 then (ChannelHeartbeatMessage.decode bytes).map fun (message, rest) => (.channelHeartbeatMessage message, rest)
  else if tag = 302000 then (RetransmissionMessage.decode bytes).map fun (message, rest) => (.retransmissionMessage message, rest)
  else if tag = 303000 then (SnapshotChannelStatisticsMessage.decode bytes).map fun (message, rest) => (.snapshotChannelStatisticsMessage message, rest)
  else if tag = 8 then (BusinessRejectMessage.decode bytes).map fun (message, rest) => (.businessRejectMessage message, rest)
  else if tag = 304000 then (SecurityRealTimeStatusMessage.decode bytes).map fun (message, rest) => (.securityRealTimeStatusMessage message, rest)
  else if tag = 305000 then (AnnouncementMessage.decode bytes).map fun (message, rest) => (.announcementMessage message, rest)
  else if tag = 306001 then (BondSpotTradingSnapshotMessage.decode bytes).map fun (message, rest) => (.bondSpotTradingSnapshotMessage message, rest)
  else if tag = 306002 then (AuctionTradingSnapshotMessage.decode bytes).map fun (message, rest) => (.auctionTradingSnapshotMessage message, rest)
  else if tag = 306003 then (IndexSnapshotMessage.decode bytes).map fun (message, rest) => (.indexSnapshotMessage message, rest)
  else if tag = 307011 then (BondSpotMatchingLargeOrderTickMessage.decode bytes).map fun (message, rest) => (.bondSpotMatchingLargeOrderTickMessage message, rest)
  else if tag = 307021 then (AgreementTradingOrderTickMessage.decode bytes).map fun (message, rest) => (.agreementTradingOrderTickMessage message, rest)
  else if tag = 307023 then (SecuritiesLendingOrderTickMessage.decode bytes).map fun (message, rest) => (.securitiesLendingOrderTickMessage message, rest)
  else if tag = 308011 then (BondSpotMatchingLargeTradeTickMessage.decode bytes).map fun (message, rest) => (.bondSpotMatchingLargeTradeTickMessage message, rest)
  else if tag = 308012 then (BondSpotNegotiatedTradeTickMessage.decode bytes).map fun (message, rest) => (.bondSpotNegotiatedTradeTickMessage message, rest)
  else if tag = 308023 then (SecuritiesLendingTradeTickMessage.decode bytes).map fun (message, rest) => (.securitiesLendingTradeTickMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message Tail: 4 bytes -/
structure MessageTail where
  checksum : BitVec 32
  deriving DecidableEq, Repr

namespace MessageTail

def encode (message : MessageTail) : List UInt8 :=
  encodeUInt 4 message.checksum

def decode (bytes : List UInt8) : Option (MessageTail × List UInt8) := do
  let (checksum, bytes) ← decodeUInt 4 bytes
  pure ({ checksum }, bytes)

@[simp] theorem encode_length (message : MessageTail) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : MessageTail) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MessageTail) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MessageTail

/-- Message -/
structure Message where
  bodyLength : BitVec 32
  payload : Payload
  messageTail : MessageTail
  deriving DecidableEq, Repr

namespace Message

def encode (message : Message) : List UInt8 :=
  encodeUInt 4 (Payload.tag message.payload)
    ++ (encodeUInt 4 message.bodyLength
    ++ (Payload.encode message.payload
    ++ (MessageTail.encode message.messageTail)))

def decode (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (msgType, bytes) ← decodeUInt 4 bytes
  let (bodyLength, bytes) ← decodeUInt 4 bytes
  let (payload, bytes) ← Payload.decode msgType bytes
  let (messageTail, bytes) ← MessageTail.decode bytes
  pure ({ bodyLength, payload, messageTail }, bytes)

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Payload.decode_encode, some_bind]
  dsimp only
  rw [MessageTail.decode_encode, some_bind]
  rfl

end Message

end Omi.BjseBjsesecuritiesTcpmarketdataBjsebinaryV11
