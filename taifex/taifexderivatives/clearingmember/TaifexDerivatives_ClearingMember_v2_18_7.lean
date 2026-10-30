import Wire

/-!
# Taiwan Futures Exchange Clearing Member Order And Execution Report v2.18.7

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.TaifexTaifexderivativesClearingmemberTmpV2187

/-- Exec Type: one byte code -/
def ExecType.codes : List UInt8 :=
  [0x30, 0x34, 0x35, 0x36, 0x46, 0x49, 0x4D, 0x6D]

inductive ExecType where
  | new -- New
  | cancel -- Cancel
  | decrease -- Decrease
  | newAndExecutionReport -- New And Execution Report
  | executionReport -- Execution Report
  | query -- Query
  | modifyPriceReplyingToTheModifyingLine -- Modify Price Replying To The Modifying Line
  | modifyPriceReplyingToTheOriginalLine -- Modify Price Replying To The Original Line
  | unlisted (byte : { byte : UInt8 // byte ∉ ExecType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExecType

def toByte : ExecType → UInt8
  | .new => 0x30
  | .cancel => 0x34
  | .decrease => 0x35
  | .newAndExecutionReport => 0x36
  | .executionReport => 0x46
  | .query => 0x49
  | .modifyPriceReplyingToTheModifyingLine => 0x4D
  | .modifyPriceReplyingToTheOriginalLine => 0x6D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExecType :=
  if byte = 0x30 then .new
  else if byte = 0x34 then .cancel
  else if byte = 0x35 then .decrease
  else if byte = 0x36 then .newAndExecutionReport
  else if byte = 0x46 then .executionReport
  else if byte = 0x49 then .query
  else if byte = 0x4D then .modifyPriceReplyingToTheModifyingLine
  else .modifyPriceReplyingToTheOriginalLine

def ofByte (byte : UInt8) : ExecType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExecType) : ofByte value.toByte = value := by
  cases value with
  | new => decide
  | cancel => decide
  | decrease => decide
  | newAndExecutionReport => decide
  | executionReport => decide
  | query => decide
  | modifyPriceReplyingToTheModifyingLine => decide
  | modifyPriceReplyingToTheOriginalLine => decide
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

/-- Position Effect: one byte code -/
def PositionEffect.codes : List UInt8 :=
  [0x4F, 0x43, 0x44, 0x41, 0x37, 0x39]

inductive PositionEffect where
  | open_ -- Open
  | close -- Close
  | daytrade -- Daytrade
  | openAndSpecifiedPositionOffsets -- Open And Specified Position Offsets
  | offsetByFcm -- Offset By Fcm
  | marketMakerQuote -- Market Maker Quote
  | unlisted (byte : { byte : UInt8 // byte ∉ PositionEffect.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PositionEffect

def toByte : PositionEffect → UInt8
  | .open_ => 0x4F
  | .close => 0x43
  | .daytrade => 0x44
  | .openAndSpecifiedPositionOffsets => 0x41
  | .offsetByFcm => 0x37
  | .marketMakerQuote => 0x39
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PositionEffect :=
  if byte = 0x4F then .open_
  else if byte = 0x43 then .close
  else if byte = 0x44 then .daytrade
  else if byte = 0x41 then .openAndSpecifiedPositionOffsets
  else if byte = 0x37 then .offsetByFcm
  else .marketMakerQuote

def ofByte (byte : UInt8) : PositionEffect :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PositionEffect) : ofByte value.toByte = value := by
  cases value with
  | open_ => decide
  | close => decide
  | daytrade => decide
  | openAndSpecifiedPositionOffsets => decide
  | offsetByFcm => decide
  | marketMakerQuote => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PositionEffect) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PositionEffect × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PositionEffect) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : PositionEffect) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : PositionEffect) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PositionEffect

/-- Header Time: 6 bytes -/
structure HeaderTime where
  headerEpochS : BitVec 32
  headerMs : BitVec 16
  deriving DecidableEq, Repr

namespace HeaderTime

def encode (message : HeaderTime) : List UInt8 :=
  encodeUInt 4 message.headerEpochS
    ++ (encodeUInt 2 message.headerMs)

def decode (bytes : List UInt8) : Option (HeaderTime × List UInt8) := do
  let (headerEpochS, bytes) ← decodeUInt 4 bytes
  let (headerMs, bytes) ← decodeUInt 2 bytes
  pure ({ headerEpochS, headerMs }, bytes)

@[simp] theorem encode_length (message : HeaderTime) : (encode message).length = 6 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : HeaderTime) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : HeaderTime) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end HeaderTime

/-- Wake Up Call Message: 5 bytes -/
structure WakeUpCallMessage where
  statusCodeUint81 : BitVec 8
  startInBoundNum : BitVec 32
  deriving DecidableEq, Repr

namespace WakeUpCallMessage

def encode (message : WakeUpCallMessage) : List UInt8 :=
  encodeUInt 1 message.statusCodeUint81
    ++ (encodeUInt 4 message.startInBoundNum)

def decode (bytes : List UInt8) : Option (WakeUpCallMessage × List UInt8) := do
  let (statusCodeUint81, bytes) ← decodeUInt 1 bytes
  let (startInBoundNum, bytes) ← decodeUInt 4 bytes
  pure ({ statusCodeUint81, startInBoundNum }, bytes)

@[simp] theorem encode_length (message : WakeUpCallMessage) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : WakeUpCallMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : WakeUpCallMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end WakeUpCallMessage

/-- Wake Up Call Confirmed Message: 1 bytes -/
structure WakeUpCallConfirmedMessage where
  version : BitVec 8
  deriving DecidableEq, Repr

namespace WakeUpCallConfirmedMessage

def encode (message : WakeUpCallConfirmedMessage) : List UInt8 :=
  encodeUInt 1 message.version

def decode (bytes : List UInt8) : Option (WakeUpCallConfirmedMessage × List UInt8) := do
  let (version, bytes) ← decodeUInt 1 bytes
  pure ({ version }, bytes)

@[simp] theorem encode_length (message : WakeUpCallConfirmedMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : WakeUpCallConfirmedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : WakeUpCallConfirmedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end WakeUpCallConfirmedMessage

/-- Logon Notice Message: 9 bytes -/
structure LogonNoticeMessage where
  statusCodeUint81 : BitVec 8
  appendNo : BitVec 16
  endOutBoundNum : BitVec 32
  systemType : BitVec 8
  encryptMethod : BitVec 8
  deriving DecidableEq, Repr

namespace LogonNoticeMessage

def encode (message : LogonNoticeMessage) : List UInt8 :=
  encodeUInt 1 message.statusCodeUint81
    ++ (encodeUInt 2 message.appendNo
    ++ (encodeUInt 4 message.endOutBoundNum
    ++ (encodeUInt 1 message.systemType
    ++ (encodeUInt 1 message.encryptMethod))))

def decode (bytes : List UInt8) : Option (LogonNoticeMessage × List UInt8) := do
  let (statusCodeUint81, bytes) ← decodeUInt 1 bytes
  let (appendNo, bytes) ← decodeUInt 2 bytes
  let (endOutBoundNum, bytes) ← decodeUInt 4 bytes
  let (systemType, bytes) ← decodeUInt 1 bytes
  let (encryptMethod, bytes) ← decodeUInt 1 bytes
  pure ({ statusCodeUint81, appendNo, endOutBoundNum, systemType, encryptMethod }, bytes)

@[simp] theorem encode_length (message : LogonNoticeMessage) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : LogonNoticeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogonNoticeMessage) (rest : List UInt8) :
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end LogonNoticeMessage

/-- Sub Hdr: 6 bytes -/
structure SubHdr where
  msgTypeExt : BitVec 8
  preserve : BitVec 8
  msgTimeNs : BitVec 32
  deriving DecidableEq, Repr

namespace SubHdr

def encode (message : SubHdr) : List UInt8 :=
  encodeUInt 1 message.msgTypeExt
    ++ (encodeUInt 1 message.preserve
    ++ (encodeUInt 4 message.msgTimeNs))

def decode (bytes : List UInt8) : Option (SubHdr × List UInt8) := do
  let (msgTypeExt, bytes) ← decodeUInt 1 bytes
  let (preserve, bytes) ← decodeUInt 1 bytes
  let (msgTimeNs, bytes) ← decodeUInt 4 bytes
  pure ({ msgTypeExt, preserve, msgTimeNs }, bytes)

@[simp] theorem encode_length (message : SubHdr) : (encode message).length = 6 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : SubHdr) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SubHdr) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SubHdr

/-- Final Sequential Number Notification For Group Message: 21 bytes -/
structure FinalSequentialNumberNotificationForGroupMessage where
  subHdr : SubHdr
  statusCodeUint162 : BitVec 16
  partId : BitVec 8
  endOutBoundNum : BitVec 32
  reserved8 : Alpha 8
  deriving DecidableEq, Repr

namespace FinalSequentialNumberNotificationForGroupMessage

def encode (message : FinalSequentialNumberNotificationForGroupMessage) : List UInt8 :=
  SubHdr.encode message.subHdr
    ++ (encodeUInt 2 message.statusCodeUint162
    ++ (encodeUInt 1 message.partId
    ++ (encodeUInt 4 message.endOutBoundNum
    ++ (Alpha.encode message.reserved8))))

def decode (bytes : List UInt8) : Option (FinalSequentialNumberNotificationForGroupMessage × List UInt8) := do
  let (subHdr, bytes) ← SubHdr.decode bytes
  let (statusCodeUint162, bytes) ← decodeUInt 2 bytes
  let (partId, bytes) ← decodeUInt 1 bytes
  let (endOutBoundNum, bytes) ← decodeUInt 4 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  pure ({ subHdr, statusCodeUint162, partId, endOutBoundNum, reserved8 }, bytes)

@[simp] theorem encode_length (message : FinalSequentialNumberNotificationForGroupMessage) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, SubHdr.encode_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : FinalSequentialNumberNotificationForGroupMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FinalSequentialNumberNotificationForGroupMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, SubHdr.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FinalSequentialNumberNotificationForGroupMessage

/-- Request Logon Message: 15 bytes -/
structure RequestLogonMessage where
  statusCodeUint81 : BitVec 8
  appendNo : BitVec 16
  fcmId : BitVec 16
  sessionId : BitVec 16
  systemType : BitVec 8
  apCode : BitVec 8
  keyValue : BitVec 8
  requestStartSeq : BitVec 32
  cancelOrderSec : BitVec 8
  deriving DecidableEq, Repr

namespace RequestLogonMessage

def encode (message : RequestLogonMessage) : List UInt8 :=
  encodeUInt 1 message.statusCodeUint81
    ++ (encodeUInt 2 message.appendNo
    ++ (encodeUInt 2 message.fcmId
    ++ (encodeUInt 2 message.sessionId
    ++ (encodeUInt 1 message.systemType
    ++ (encodeUInt 1 message.apCode
    ++ (encodeUInt 1 message.keyValue
    ++ (encodeUInt 4 message.requestStartSeq
    ++ (encodeUInt 1 message.cancelOrderSec))))))))

def decode (bytes : List UInt8) : Option (RequestLogonMessage × List UInt8) := do
  let (statusCodeUint81, bytes) ← decodeUInt 1 bytes
  let (appendNo, bytes) ← decodeUInt 2 bytes
  let (fcmId, bytes) ← decodeUInt 2 bytes
  let (sessionId, bytes) ← decodeUInt 2 bytes
  let (systemType, bytes) ← decodeUInt 1 bytes
  let (apCode, bytes) ← decodeUInt 1 bytes
  let (keyValue, bytes) ← decodeUInt 1 bytes
  let (requestStartSeq, bytes) ← decodeUInt 4 bytes
  let (cancelOrderSec, bytes) ← decodeUInt 1 bytes
  pure ({ statusCodeUint81, appendNo, fcmId, sessionId, systemType, apCode, keyValue, requestStartSeq, cancelOrderSec }, bytes)

@[simp] theorem encode_length (message : RequestLogonMessage) : (encode message).length = 15 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : RequestLogonMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RequestLogonMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end RequestLogonMessage

/-- Activate Application System Message: 4 bytes -/
structure ActivateApplicationSystemMessage where
  statusCodeUint81 : BitVec 8
  heartBtInt : BitVec 8
  maxFlowCtrlCnt : BitVec 16
  deriving DecidableEq, Repr

namespace ActivateApplicationSystemMessage

def encode (message : ActivateApplicationSystemMessage) : List UInt8 :=
  encodeUInt 1 message.statusCodeUint81
    ++ (encodeUInt 1 message.heartBtInt
    ++ (encodeUInt 2 message.maxFlowCtrlCnt))

def decode (bytes : List UInt8) : Option (ActivateApplicationSystemMessage × List UInt8) := do
  let (statusCodeUint81, bytes) ← decodeUInt 1 bytes
  let (heartBtInt, bytes) ← decodeUInt 1 bytes
  let (maxFlowCtrlCnt, bytes) ← decodeUInt 2 bytes
  pure ({ statusCodeUint81, heartBtInt, maxFlowCtrlCnt }, bytes)

@[simp] theorem encode_length (message : ActivateApplicationSystemMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : ActivateApplicationSystemMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ActivateApplicationSystemMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ActivateApplicationSystemMessage

/-- Activate Application System Confirmed Message: 1 bytes -/
structure ActivateApplicationSystemConfirmedMessage where
  statusCodeUint81 : BitVec 8
  deriving DecidableEq, Repr

namespace ActivateApplicationSystemConfirmedMessage

def encode (message : ActivateApplicationSystemConfirmedMessage) : List UInt8 :=
  encodeUInt 1 message.statusCodeUint81

def decode (bytes : List UInt8) : Option (ActivateApplicationSystemConfirmedMessage × List UInt8) := do
  let (statusCodeUint81, bytes) ← decodeUInt 1 bytes
  pure ({ statusCodeUint81 }, bytes)

@[simp] theorem encode_length (message : ActivateApplicationSystemConfirmedMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : ActivateApplicationSystemConfirmedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ActivateApplicationSystemConfirmedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ActivateApplicationSystemConfirmedMessage

/-- Logout Message: 0 bytes -/
structure LogoutMessage where
  deriving DecidableEq, Repr

namespace LogoutMessage

def encode (_ : LogoutMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (LogoutMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : LogoutMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : LogoutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end LogoutMessage

/-- Logout Confirmed Message: 1 bytes -/
structure LogoutConfirmedMessage where
  statusCodeUint81 : BitVec 8
  deriving DecidableEq, Repr

namespace LogoutConfirmedMessage

def encode (message : LogoutConfirmedMessage) : List UInt8 :=
  encodeUInt 1 message.statusCodeUint81

def decode (bytes : List UInt8) : Option (LogoutConfirmedMessage × List UInt8) := do
  let (statusCodeUint81, bytes) ← decodeUInt 1 bytes
  pure ({ statusCodeUint81 }, bytes)

@[simp] theorem encode_length (message : LogoutConfirmedMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : LogoutConfirmedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogoutConfirmedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end LogoutConfirmedMessage

/-- Confirm Connection Message: 1 bytes -/
structure ConfirmConnectionMessage where
  statusCodeUint81 : BitVec 8
  deriving DecidableEq, Repr

namespace ConfirmConnectionMessage

def encode (message : ConfirmConnectionMessage) : List UInt8 :=
  encodeUInt 1 message.statusCodeUint81

def decode (bytes : List UInt8) : Option (ConfirmConnectionMessage × List UInt8) := do
  let (statusCodeUint81, bytes) ← decodeUInt 1 bytes
  pure ({ statusCodeUint81 }, bytes)

@[simp] theorem encode_length (message : ConfirmConnectionMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : ConfirmConnectionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ConfirmConnectionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ConfirmConnectionMessage

/-- Connection Confirmed Message: 1 bytes -/
structure ConnectionConfirmedMessage where
  statusCodeUint81 : BitVec 8
  deriving DecidableEq, Repr

namespace ConnectionConfirmedMessage

def encode (message : ConnectionConfirmedMessage) : List UInt8 :=
  encodeUInt 1 message.statusCodeUint81

def decode (bytes : List UInt8) : Option (ConnectionConfirmedMessage × List UInt8) := do
  let (statusCodeUint81, bytes) ← decodeUInt 1 bytes
  pure ({ statusCodeUint81 }, bytes)

@[simp] theorem encode_length (message : ConnectionConfirmedMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : ConnectionConfirmedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ConnectionConfirmedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ConnectionConfirmedMessage

/-- Symbol Num: 19 bytes -/
structure SymbolNum where
  pseq1 : BitVec 16
  pseq2 : BitVec 16
  legSideUint822 : BitVec 8
  combOp : BitVec 8
  reserved13 : Alpha 13
  deriving DecidableEq, Repr

namespace SymbolNum

def encode (message : SymbolNum) : List UInt8 :=
  encodeUInt 2 message.pseq1
    ++ (encodeUInt 2 message.pseq2
    ++ (encodeUInt 1 message.legSideUint822
    ++ (encodeUInt 1 message.combOp
    ++ (Alpha.encode message.reserved13))))

def decode (bytes : List UInt8) : Option (SymbolNum × List UInt8) := do
  let (pseq1, bytes) ← decodeUInt 2 bytes
  let (pseq2, bytes) ← decodeUInt 2 bytes
  let (legSideUint822, bytes) ← decodeUInt 1 bytes
  let (combOp, bytes) ← decodeUInt 1 bytes
  let (reserved13, bytes) ← Alpha.decode 13 bytes
  pure ({ pseq1, pseq2, legSideUint822, combOp, reserved13 }, bytes)

@[simp] theorem encode_length (message : SymbolNum) : (encode message).length = 19 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : SymbolNum) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SymbolNum) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end SymbolNum

/-- Symbol Text: 20 bytes -/
structure SymbolText where
  symbolChar2020 : Alpha 20
  deriving DecidableEq, Repr

namespace SymbolText

def encode (message : SymbolText) : List UInt8 :=
  Alpha.encode message.symbolChar2020

def decode (bytes : List UInt8) : Option (SymbolText × List UInt8) := do
  let (symbolChar2020, bytes) ← Alpha.decode 20 bytes
  pure ({ symbolChar2020 }, bytes)

@[simp] theorem encode_length (message : SymbolText) : (encode message).length = 20 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : SymbolText) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SymbolText) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end SymbolText

/-- Any Sym Symbol X, selected by Symbol Type -/
inductive SymSymbolX where
  | symbolNum (message : SymbolNum) -- 1
  | symbolText (message : SymbolText) -- 2
  deriving DecidableEq, Repr

namespace SymSymbolX

/-- The Symbol Type each message is sent under -/
def tag : SymSymbolX → BitVec 8
  | .symbolNum _ => 1
  | .symbolText _ => 2

def encode : SymSymbolX → List UInt8
  | .symbolNum message => SymbolNum.encode message
  | .symbolText message => SymbolText.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : SymSymbolX) : (encode message).length ≤ 20 := by
  cases message with
  | symbolNum inner =>
    simp only [encode, SymbolNum.encode_length]
    omega
  | symbolText inner =>
    simp only [encode, SymbolText.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (SymSymbolX × List UInt8) :=
  if tag = 1 then (SymbolNum.decode bytes).map fun (message, rest) => (.symbolNum message, rest)
  else if tag = 2 then (SymbolText.decode bytes).map fun (message, rest) => (.symbolText message, rest)
  else none

@[simp] theorem decode_encode (message : SymSymbolX) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end SymSymbolX

/-- Org Trans Time Msg Time: 6 bytes -/
structure OrgTransTimeMsgTime where
  epochSInt324 : BitVec 32
  ms : BitVec 16
  deriving DecidableEq, Repr

namespace OrgTransTimeMsgTime

def encode (message : OrgTransTimeMsgTime) : List UInt8 :=
  encodeUInt 4 message.epochSInt324
    ++ (encodeUInt 2 message.ms)

def decode (bytes : List UInt8) : Option (OrgTransTimeMsgTime × List UInt8) := do
  let (epochSInt324, bytes) ← decodeUInt 4 bytes
  let (ms, bytes) ← decodeUInt 2 bytes
  pure ({ epochSInt324, ms }, bytes)

@[simp] theorem encode_length (message : OrgTransTimeMsgTime) : (encode message).length = 6 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : OrgTransTimeMsgTime) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrgTransTimeMsgTime) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrgTransTimeMsgTime

/-- Transact Time Msg Time: 6 bytes -/
structure TransactTimeMsgTime where
  epochSInt324 : BitVec 32
  ms : BitVec 16
  deriving DecidableEq, Repr

namespace TransactTimeMsgTime

def encode (message : TransactTimeMsgTime) : List UInt8 :=
  encodeUInt 4 message.epochSInt324
    ++ (encodeUInt 2 message.ms)

def decode (bytes : List UInt8) : Option (TransactTimeMsgTime × List UInt8) := do
  let (epochSInt324, bytes) ← decodeUInt 4 bytes
  let (ms, bytes) ← decodeUInt 2 bytes
  pure ({ epochSInt324, ms }, bytes)

@[simp] theorem encode_length (message : TransactTimeMsgTime) : (encode message).length = 6 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : TransactTimeMsgTime) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TransactTimeMsgTime) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TransactTimeMsgTime

/-- Order Status Report Message -/
structure OrderStatusReportMessage where
  statusCodeUint81 : BitVec 8
  execType : ExecType
  cmId : BitVec 16
  fcmId : BitVec 16
  orderNo : Alpha 5
  ordId : BitVec 32
  userDefine : Alpha 8
  symSymbolX : SymSymbolX
  price : BitVec 32
  qty : BitVec 16
  investorAcno : BitVec 32
  investorFlag : Alpha 1
  side : BitVec 8
  ordType : BitVec 8
  timeInForce : BitVec 8
  positionEffect : PositionEffect
  lastPx : BitVec 32
  lastQty : BitVec 16
  pxSubtotal : BitVec 64
  cumQty : BitVec 16
  leavesQty : BitVec 16
  beforeQty : BitVec 16
  legSideUint822 : BitVec 8
  legPx : BitVec 32
  legQtyUint1624 : BitVec 16
  orgTransTimeMsgTime : OrgTransTimeMsgTime
  transactTimeMsgTime : TransactTimeMsgTime
  targetId : BitVec 8
  uniqId : BitVec 32
  rptSeq : BitVec 32
  protocolType : BitVec 8
  deriving DecidableEq, Repr

namespace OrderStatusReportMessage

def encode (message : OrderStatusReportMessage) : List UInt8 :=
  encodeUInt 1 message.statusCodeUint81
    ++ (ExecType.encode message.execType
    ++ (encodeUInt 2 message.cmId
    ++ (encodeUInt 2 message.fcmId
    ++ (Alpha.encode message.orderNo
    ++ (encodeUInt 4 message.ordId
    ++ (Alpha.encode message.userDefine
    ++ (encodeUInt 1 (SymSymbolX.tag message.symSymbolX)
    ++ (SymSymbolX.encode message.symSymbolX
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 2 message.qty
    ++ (encodeUInt 4 message.investorAcno
    ++ (Alpha.encode message.investorFlag
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.ordType
    ++ (encodeUInt 1 message.timeInForce
    ++ (PositionEffect.encode message.positionEffect
    ++ (encodeUInt 4 message.lastPx
    ++ (encodeUInt 2 message.lastQty
    ++ (encodeUInt 8 message.pxSubtotal
    ++ (encodeUInt 2 message.cumQty
    ++ (encodeUInt 2 message.leavesQty
    ++ (encodeUInt 2 message.beforeQty
    ++ (encodeUInt 1 message.legSideUint822
    ++ (encodeUInt 4 message.legPx
    ++ (encodeUInt 2 message.legQtyUint1624
    ++ (OrgTransTimeMsgTime.encode message.orgTransTimeMsgTime
    ++ (TransactTimeMsgTime.encode message.transactTimeMsgTime
    ++ (encodeUInt 1 message.targetId
    ++ (encodeUInt 4 message.uniqId
    ++ (encodeUInt 4 message.rptSeq
    ++ (encodeUInt 1 message.protocolType)))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderStatusReportMessage × List UInt8) := do
  let (statusCodeUint81, bytes) ← decodeUInt 1 bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (cmId, bytes) ← decodeUInt 2 bytes
  let (fcmId, bytes) ← decodeUInt 2 bytes
  let (orderNo, bytes) ← Alpha.decode 5 bytes
  let (ordId, bytes) ← decodeUInt 4 bytes
  let (userDefine, bytes) ← Alpha.decode 8 bytes
  let (symbolType, bytes) ← decodeUInt 1 bytes
  let (symSymbolX, bytes) ← SymSymbolX.decode symbolType bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (qty, bytes) ← decodeUInt 2 bytes
  let (investorAcno, bytes) ← decodeUInt 4 bytes
  let (investorFlag, bytes) ← Alpha.decode 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (ordType, bytes) ← decodeUInt 1 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (positionEffect, bytes) ← PositionEffect.decode bytes
  let (lastPx, bytes) ← decodeUInt 4 bytes
  let (lastQty, bytes) ← decodeUInt 2 bytes
  let (pxSubtotal, bytes) ← decodeUInt 8 bytes
  let (cumQty, bytes) ← decodeUInt 2 bytes
  let (leavesQty, bytes) ← decodeUInt 2 bytes
  let (beforeQty, bytes) ← decodeUInt 2 bytes
  let (legSideUint822, bytes) ← decodeUInt 1 bytes
  let (legPx, bytes) ← decodeUInt 4 bytes
  let (legQtyUint1624, bytes) ← decodeUInt 2 bytes
  let (orgTransTimeMsgTime, bytes) ← OrgTransTimeMsgTime.decode bytes
  let (transactTimeMsgTime, bytes) ← TransactTimeMsgTime.decode bytes
  let (targetId, bytes) ← decodeUInt 1 bytes
  let (uniqId, bytes) ← decodeUInt 4 bytes
  let (rptSeq, bytes) ← decodeUInt 4 bytes
  let (protocolType, bytes) ← decodeUInt 1 bytes
  pure ({ statusCodeUint81, execType, cmId, fcmId, orderNo, ordId, userDefine, symSymbolX, price, qty, investorAcno, investorFlag, side, ordType, timeInForce, positionEffect, lastPx, lastQty, pxSubtotal, cumQty, leavesQty, beforeQty, legSideUint822, legPx, legQtyUint1624, orgTransTimeMsgTime, transactTimeMsgTime, targetId, uniqId, rptSeq, protocolType }, bytes)

theorem encode_length_pos (message : OrderStatusReportMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrderStatusReportMessage) : (encode message).length ≤ 108 := by
  unfold encode
  cases message.symSymbolX with
  | symbolNum inner =>
    simp only [SymSymbolX.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ExecType.encode_length, Alpha.encode_length, PositionEffect.encode_length, OrgTransTimeMsgTime.encode_length, TransactTimeMsgTime.encode_length, SymbolNum.encode_length]
    omega
  | symbolText inner =>
    simp only [SymSymbolX.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ExecType.encode_length, Alpha.encode_length, PositionEffect.encode_length, OrgTransTimeMsgTime.encode_length, TransactTimeMsgTime.encode_length, SymbolText.encode_length]
    omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OrderStatusReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
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
  rw [List.append_assoc, SymSymbolX.decode_encode, some_bind]
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
  rw [List.append_assoc, PositionEffect.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OrgTransTimeMsgTime.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TransactTimeMsgTime.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderStatusReportMessage

/-- Long Symbol Num: 39 bytes -/
structure LongSymbolNum where
  pseq1 : BitVec 16
  pseq2 : BitVec 16
  legSideUint822 : BitVec 8
  combOp : BitVec 8
  reserved33 : Alpha 33
  deriving DecidableEq, Repr

namespace LongSymbolNum

def encode (message : LongSymbolNum) : List UInt8 :=
  encodeUInt 2 message.pseq1
    ++ (encodeUInt 2 message.pseq2
    ++ (encodeUInt 1 message.legSideUint822
    ++ (encodeUInt 1 message.combOp
    ++ (Alpha.encode message.reserved33))))

def decode (bytes : List UInt8) : Option (LongSymbolNum × List UInt8) := do
  let (pseq1, bytes) ← decodeUInt 2 bytes
  let (pseq2, bytes) ← decodeUInt 2 bytes
  let (legSideUint822, bytes) ← decodeUInt 1 bytes
  let (combOp, bytes) ← decodeUInt 1 bytes
  let (reserved33, bytes) ← Alpha.decode 33 bytes
  pure ({ pseq1, pseq2, legSideUint822, combOp, reserved33 }, bytes)

@[simp] theorem encode_length (message : LongSymbolNum) : (encode message).length = 39 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : LongSymbolNum) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LongSymbolNum) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end LongSymbolNum

/-- Long Symbol Text: 40 bytes -/
structure LongSymbolText where
  symbolChar4040 : Alpha 40
  deriving DecidableEq, Repr

namespace LongSymbolText

def encode (message : LongSymbolText) : List UInt8 :=
  Alpha.encode message.symbolChar4040

def decode (bytes : List UInt8) : Option (LongSymbolText × List UInt8) := do
  let (symbolChar4040, bytes) ← Alpha.decode 40 bytes
  pure ({ symbolChar4040 }, bytes)

@[simp] theorem encode_length (message : LongSymbolText) : (encode message).length = 40 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : LongSymbolText) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LongSymbolText) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end LongSymbolText

/-- Any Sym Long Symbol X, selected by Symbol Type -/
inductive SymLongSymbolX where
  | longSymbolNum (message : LongSymbolNum) -- 3
  | longSymbolText (message : LongSymbolText) -- 4
  deriving DecidableEq, Repr

namespace SymLongSymbolX

/-- The Symbol Type each message is sent under -/
def tag : SymLongSymbolX → BitVec 8
  | .longSymbolNum _ => 3
  | .longSymbolText _ => 4

def encode : SymLongSymbolX → List UInt8
  | .longSymbolNum message => LongSymbolNum.encode message
  | .longSymbolText message => LongSymbolText.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : SymLongSymbolX) : (encode message).length ≤ 40 := by
  cases message with
  | longSymbolNum inner =>
    simp only [encode, LongSymbolNum.encode_length]
    omega
  | longSymbolText inner =>
    simp only [encode, LongSymbolText.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (SymLongSymbolX × List UInt8) :=
  if tag = 3 then (LongSymbolNum.decode bytes).map fun (message, rest) => (.longSymbolNum message, rest)
  else if tag = 4 then (LongSymbolText.decode bytes).map fun (message, rest) => (.longSymbolText message, rest)
  else none

@[simp] theorem decode_encode (message : SymLongSymbolX) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end SymLongSymbolX

/-- Order Status Report Long Format Message -/
structure OrderStatusReportLongFormatMessage where
  statusCodeUint81 : BitVec 8
  execType : ExecType
  cmId : BitVec 16
  fcmId : BitVec 16
  orderNo : Alpha 5
  ordId : BitVec 32
  userDefine : Alpha 8
  symLongSymbolX : SymLongSymbolX
  price : BitVec 32
  qty : BitVec 16
  investorAcno : BitVec 32
  investorFlag : Alpha 1
  side : BitVec 8
  ordType : BitVec 8
  timeInForce : BitVec 8
  positionEffect : PositionEffect
  lastPx : BitVec 32
  lastQty : BitVec 16
  pxSubtotal : BitVec 64
  cumQty : BitVec 16
  leavesQty : BitVec 16
  beforeQty : BitVec 16
  legSideUint822 : BitVec 8
  legPx : BitVec 32
  legQtyUint1624 : BitVec 16
  orgTransTimeMsgTime : OrgTransTimeMsgTime
  transactTimeMsgTime : TransactTimeMsgTime
  targetId : BitVec 8
  uniqId : BitVec 32
  rptSeq : BitVec 32
  protocolType : BitVec 8
  deriving DecidableEq, Repr

namespace OrderStatusReportLongFormatMessage

def encode (message : OrderStatusReportLongFormatMessage) : List UInt8 :=
  encodeUInt 1 message.statusCodeUint81
    ++ (ExecType.encode message.execType
    ++ (encodeUInt 2 message.cmId
    ++ (encodeUInt 2 message.fcmId
    ++ (Alpha.encode message.orderNo
    ++ (encodeUInt 4 message.ordId
    ++ (Alpha.encode message.userDefine
    ++ (encodeUInt 1 (SymLongSymbolX.tag message.symLongSymbolX)
    ++ (SymLongSymbolX.encode message.symLongSymbolX
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 2 message.qty
    ++ (encodeUInt 4 message.investorAcno
    ++ (Alpha.encode message.investorFlag
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.ordType
    ++ (encodeUInt 1 message.timeInForce
    ++ (PositionEffect.encode message.positionEffect
    ++ (encodeUInt 4 message.lastPx
    ++ (encodeUInt 2 message.lastQty
    ++ (encodeUInt 8 message.pxSubtotal
    ++ (encodeUInt 2 message.cumQty
    ++ (encodeUInt 2 message.leavesQty
    ++ (encodeUInt 2 message.beforeQty
    ++ (encodeUInt 1 message.legSideUint822
    ++ (encodeUInt 4 message.legPx
    ++ (encodeUInt 2 message.legQtyUint1624
    ++ (OrgTransTimeMsgTime.encode message.orgTransTimeMsgTime
    ++ (TransactTimeMsgTime.encode message.transactTimeMsgTime
    ++ (encodeUInt 1 message.targetId
    ++ (encodeUInt 4 message.uniqId
    ++ (encodeUInt 4 message.rptSeq
    ++ (encodeUInt 1 message.protocolType)))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderStatusReportLongFormatMessage × List UInt8) := do
  let (statusCodeUint81, bytes) ← decodeUInt 1 bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (cmId, bytes) ← decodeUInt 2 bytes
  let (fcmId, bytes) ← decodeUInt 2 bytes
  let (orderNo, bytes) ← Alpha.decode 5 bytes
  let (ordId, bytes) ← decodeUInt 4 bytes
  let (userDefine, bytes) ← Alpha.decode 8 bytes
  let (symbolType, bytes) ← decodeUInt 1 bytes
  let (symLongSymbolX, bytes) ← SymLongSymbolX.decode symbolType bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (qty, bytes) ← decodeUInt 2 bytes
  let (investorAcno, bytes) ← decodeUInt 4 bytes
  let (investorFlag, bytes) ← Alpha.decode 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (ordType, bytes) ← decodeUInt 1 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (positionEffect, bytes) ← PositionEffect.decode bytes
  let (lastPx, bytes) ← decodeUInt 4 bytes
  let (lastQty, bytes) ← decodeUInt 2 bytes
  let (pxSubtotal, bytes) ← decodeUInt 8 bytes
  let (cumQty, bytes) ← decodeUInt 2 bytes
  let (leavesQty, bytes) ← decodeUInt 2 bytes
  let (beforeQty, bytes) ← decodeUInt 2 bytes
  let (legSideUint822, bytes) ← decodeUInt 1 bytes
  let (legPx, bytes) ← decodeUInt 4 bytes
  let (legQtyUint1624, bytes) ← decodeUInt 2 bytes
  let (orgTransTimeMsgTime, bytes) ← OrgTransTimeMsgTime.decode bytes
  let (transactTimeMsgTime, bytes) ← TransactTimeMsgTime.decode bytes
  let (targetId, bytes) ← decodeUInt 1 bytes
  let (uniqId, bytes) ← decodeUInt 4 bytes
  let (rptSeq, bytes) ← decodeUInt 4 bytes
  let (protocolType, bytes) ← decodeUInt 1 bytes
  pure ({ statusCodeUint81, execType, cmId, fcmId, orderNo, ordId, userDefine, symLongSymbolX, price, qty, investorAcno, investorFlag, side, ordType, timeInForce, positionEffect, lastPx, lastQty, pxSubtotal, cumQty, leavesQty, beforeQty, legSideUint822, legPx, legQtyUint1624, orgTransTimeMsgTime, transactTimeMsgTime, targetId, uniqId, rptSeq, protocolType }, bytes)

theorem encode_length_pos (message : OrderStatusReportLongFormatMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrderStatusReportLongFormatMessage) : (encode message).length ≤ 128 := by
  unfold encode
  cases message.symLongSymbolX with
  | longSymbolNum inner =>
    simp only [SymLongSymbolX.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ExecType.encode_length, Alpha.encode_length, PositionEffect.encode_length, OrgTransTimeMsgTime.encode_length, TransactTimeMsgTime.encode_length, LongSymbolNum.encode_length]
    omega
  | longSymbolText inner =>
    simp only [SymLongSymbolX.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ExecType.encode_length, Alpha.encode_length, PositionEffect.encode_length, OrgTransTimeMsgTime.encode_length, TransactTimeMsgTime.encode_length, LongSymbolText.encode_length]
    omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OrderStatusReportLongFormatMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
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
  rw [List.append_assoc, SymLongSymbolX.decode_encode, some_bind]
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
  rw [List.append_assoc, PositionEffect.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OrgTransTimeMsgTime.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TransactTimeMsgTime.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderStatusReportLongFormatMessage

/-- Execution Report Including Head Office And Branch Offices Message -/
structure ExecutionReportIncludingHeadOfficeAndBranchOfficesMessage where
  statusCodeUint81 : BitVec 8
  execType : ExecType
  cmId : BitVec 16
  fcmId : BitVec 16
  orderNo : Alpha 5
  ordId : BitVec 32
  userDefine : Alpha 8
  symSymbolX : SymSymbolX
  price : BitVec 32
  qty : BitVec 16
  investorAcno : BitVec 32
  investorFlag : Alpha 1
  side : BitVec 8
  ordType : BitVec 8
  timeInForce : BitVec 8
  positionEffect : PositionEffect
  lastPx : BitVec 32
  lastQty : BitVec 16
  pxSubtotal : BitVec 64
  cumQty : BitVec 16
  leavesQty : BitVec 16
  beforeQty : BitVec 16
  legSideUint822 : BitVec 8
  legPx : BitVec 32
  legQtyUint1624 : BitVec 16
  orgTransTimeMsgTime : OrgTransTimeMsgTime
  transactTimeMsgTime : TransactTimeMsgTime
  targetId : BitVec 8
  uniqId : BitVec 32
  rptSeq : BitVec 32
  protocolType : BitVec 8
  rptSessionId : BitVec 16
  deriving DecidableEq, Repr

namespace ExecutionReportIncludingHeadOfficeAndBranchOfficesMessage

def encode (message : ExecutionReportIncludingHeadOfficeAndBranchOfficesMessage) : List UInt8 :=
  encodeUInt 1 message.statusCodeUint81
    ++ (ExecType.encode message.execType
    ++ (encodeUInt 2 message.cmId
    ++ (encodeUInt 2 message.fcmId
    ++ (Alpha.encode message.orderNo
    ++ (encodeUInt 4 message.ordId
    ++ (Alpha.encode message.userDefine
    ++ (encodeUInt 1 (SymSymbolX.tag message.symSymbolX)
    ++ (SymSymbolX.encode message.symSymbolX
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 2 message.qty
    ++ (encodeUInt 4 message.investorAcno
    ++ (Alpha.encode message.investorFlag
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.ordType
    ++ (encodeUInt 1 message.timeInForce
    ++ (PositionEffect.encode message.positionEffect
    ++ (encodeUInt 4 message.lastPx
    ++ (encodeUInt 2 message.lastQty
    ++ (encodeUInt 8 message.pxSubtotal
    ++ (encodeUInt 2 message.cumQty
    ++ (encodeUInt 2 message.leavesQty
    ++ (encodeUInt 2 message.beforeQty
    ++ (encodeUInt 1 message.legSideUint822
    ++ (encodeUInt 4 message.legPx
    ++ (encodeUInt 2 message.legQtyUint1624
    ++ (OrgTransTimeMsgTime.encode message.orgTransTimeMsgTime
    ++ (TransactTimeMsgTime.encode message.transactTimeMsgTime
    ++ (encodeUInt 1 message.targetId
    ++ (encodeUInt 4 message.uniqId
    ++ (encodeUInt 4 message.rptSeq
    ++ (encodeUInt 1 message.protocolType
    ++ (encodeUInt 2 message.rptSessionId))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ExecutionReportIncludingHeadOfficeAndBranchOfficesMessage × List UInt8) := do
  let (statusCodeUint81, bytes) ← decodeUInt 1 bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (cmId, bytes) ← decodeUInt 2 bytes
  let (fcmId, bytes) ← decodeUInt 2 bytes
  let (orderNo, bytes) ← Alpha.decode 5 bytes
  let (ordId, bytes) ← decodeUInt 4 bytes
  let (userDefine, bytes) ← Alpha.decode 8 bytes
  let (symbolType, bytes) ← decodeUInt 1 bytes
  let (symSymbolX, bytes) ← SymSymbolX.decode symbolType bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (qty, bytes) ← decodeUInt 2 bytes
  let (investorAcno, bytes) ← decodeUInt 4 bytes
  let (investorFlag, bytes) ← Alpha.decode 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (ordType, bytes) ← decodeUInt 1 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (positionEffect, bytes) ← PositionEffect.decode bytes
  let (lastPx, bytes) ← decodeUInt 4 bytes
  let (lastQty, bytes) ← decodeUInt 2 bytes
  let (pxSubtotal, bytes) ← decodeUInt 8 bytes
  let (cumQty, bytes) ← decodeUInt 2 bytes
  let (leavesQty, bytes) ← decodeUInt 2 bytes
  let (beforeQty, bytes) ← decodeUInt 2 bytes
  let (legSideUint822, bytes) ← decodeUInt 1 bytes
  let (legPx, bytes) ← decodeUInt 4 bytes
  let (legQtyUint1624, bytes) ← decodeUInt 2 bytes
  let (orgTransTimeMsgTime, bytes) ← OrgTransTimeMsgTime.decode bytes
  let (transactTimeMsgTime, bytes) ← TransactTimeMsgTime.decode bytes
  let (targetId, bytes) ← decodeUInt 1 bytes
  let (uniqId, bytes) ← decodeUInt 4 bytes
  let (rptSeq, bytes) ← decodeUInt 4 bytes
  let (protocolType, bytes) ← decodeUInt 1 bytes
  let (rptSessionId, bytes) ← decodeUInt 2 bytes
  pure ({ statusCodeUint81, execType, cmId, fcmId, orderNo, ordId, userDefine, symSymbolX, price, qty, investorAcno, investorFlag, side, ordType, timeInForce, positionEffect, lastPx, lastQty, pxSubtotal, cumQty, leavesQty, beforeQty, legSideUint822, legPx, legQtyUint1624, orgTransTimeMsgTime, transactTimeMsgTime, targetId, uniqId, rptSeq, protocolType, rptSessionId }, bytes)

theorem encode_length_pos (message : ExecutionReportIncludingHeadOfficeAndBranchOfficesMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ExecutionReportIncludingHeadOfficeAndBranchOfficesMessage) : (encode message).length ≤ 110 := by
  unfold encode
  cases message.symSymbolX with
  | symbolNum inner =>
    simp only [SymSymbolX.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ExecType.encode_length, Alpha.encode_length, PositionEffect.encode_length, OrgTransTimeMsgTime.encode_length, TransactTimeMsgTime.encode_length, SymbolNum.encode_length]
    omega
  | symbolText inner =>
    simp only [SymSymbolX.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ExecType.encode_length, Alpha.encode_length, PositionEffect.encode_length, OrgTransTimeMsgTime.encode_length, TransactTimeMsgTime.encode_length, SymbolText.encode_length]
    omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ExecutionReportIncludingHeadOfficeAndBranchOfficesMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
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
  rw [List.append_assoc, SymSymbolX.decode_encode, some_bind]
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
  rw [List.append_assoc, PositionEffect.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OrgTransTimeMsgTime.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TransactTimeMsgTime.decode_encode, some_bind]
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

end ExecutionReportIncludingHeadOfficeAndBranchOfficesMessage

/-- Symbol Num X: 4 bytes -/
structure SymbolNumX where
  pseq : BitVec 32
  deriving DecidableEq, Repr

namespace SymbolNumX

def encode (message : SymbolNumX) : List UInt8 :=
  encodeUInt 4 message.pseq

def decode (bytes : List UInt8) : Option (SymbolNumX × List UInt8) := do
  let (pseq, bytes) ← decodeUInt 4 bytes
  pure ({ pseq }, bytes)

@[simp] theorem encode_length (message : SymbolNumX) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : SymbolNumX) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SymbolNumX) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SymbolNumX

/-- Symbol Txt X: 20 bytes -/
structure SymbolTxtX where
  prodId : Alpha 20
  deriving DecidableEq, Repr

namespace SymbolTxtX

def encode (message : SymbolTxtX) : List UInt8 :=
  Alpha.encode message.prodId

def decode (bytes : List UInt8) : Option (SymbolTxtX × List UInt8) := do
  let (prodId, bytes) ← Alpha.decode 20 bytes
  pure ({ prodId }, bytes)

@[simp] theorem encode_length (message : SymbolTxtX) : (encode message).length = 20 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : SymbolTxtX) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SymbolTxtX) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end SymbolTxtX

/-- Leg Sym Symbol Num X: 4 bytes -/
structure LegSymSymbolNumX where
  pseq : BitVec 32
  deriving DecidableEq, Repr

namespace LegSymSymbolNumX

def encode (message : LegSymSymbolNumX) : List UInt8 :=
  encodeUInt 4 message.pseq

def decode (bytes : List UInt8) : Option (LegSymSymbolNumX × List UInt8) := do
  let (pseq, bytes) ← decodeUInt 4 bytes
  pure ({ pseq }, bytes)

@[simp] theorem encode_length (message : LegSymSymbolNumX) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : LegSymSymbolNumX) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LegSymSymbolNumX) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end LegSymSymbolNumX

/-- Leg Entry Num: 7 bytes -/
structure LegEntryNum where
  legSymSymbolNumX : LegSymSymbolNumX
  legSideUint81 : BitVec 8
  legQtyUint162 : BitVec 16
  deriving DecidableEq, Repr

namespace LegEntryNum

def encode (message : LegEntryNum) : List UInt8 :=
  LegSymSymbolNumX.encode message.legSymSymbolNumX
    ++ (encodeUInt 1 message.legSideUint81
    ++ (encodeUInt 2 message.legQtyUint162))

def decode (bytes : List UInt8) : Option (LegEntryNum × List UInt8) := do
  let (legSymSymbolNumX, bytes) ← LegSymSymbolNumX.decode bytes
  let (legSideUint81, bytes) ← decodeUInt 1 bytes
  let (legQtyUint162, bytes) ← decodeUInt 2 bytes
  pure ({ legSymSymbolNumX, legSideUint81, legQtyUint162 }, bytes)

@[simp] theorem encode_length (message : LegEntryNum) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, LegSymSymbolNumX.encode_length, encodeUInt_length]

theorem encode_length_pos (message : LegEntryNum) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LegEntryNum) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LegSymSymbolNumX.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end LegEntryNum

/-- Multi Leg Num -/
structure MultiLegNum where
  combOp : BitVec 8
  legEntryNum : Bounded 1 LegEntryNum
  deriving DecidableEq, Repr

namespace MultiLegNum

def encode (message : MultiLegNum) : List UInt8 :=
  encodeUInt 1 (BitVec.ofNat (8 * 1) message.legEntryNum.val.length)
    ++ (encodeUInt 1 message.combOp
    ++ (encodeMany LegEntryNum.encode message.legEntryNum.val))

def decode (bytes : List UInt8) : Option (MultiLegNum × List UInt8) := do
  let (noLeg, bytes) ← decodeUInt 1 bytes
  let (combOp, bytes) ← decodeUInt 1 bytes
  let (legEntryNum_, bytes) ← decodeMany LegEntryNum.decode noLeg.toNat bytes
  if fits_legEntryNum : legEntryNum_.length < 256 ^ 1 then
    pure ({ combOp, legEntryNum := ⟨legEntryNum_, fits_legEntryNum⟩ }, bytes)
  else none

theorem encode_length_pos (message : MultiLegNum) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MultiLegNum) : (encode message).length ≤ 1787 := by
  have bound_legEntryNum := message.legEntryNum.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const LegEntryNum.encode 7 LegEntryNum.encode_length]
  omega

@[simp] theorem decode_encode (message : MultiLegNum) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 LegEntryNum.encode LegEntryNum.decode LegEntryNum.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.legEntryNum.length_lt]
  rfl

end MultiLegNum

/-- Leg Sym Symbol Txt X: 20 bytes -/
structure LegSymSymbolTxtX where
  prodId : Alpha 20
  deriving DecidableEq, Repr

namespace LegSymSymbolTxtX

def encode (message : LegSymSymbolTxtX) : List UInt8 :=
  Alpha.encode message.prodId

def decode (bytes : List UInt8) : Option (LegSymSymbolTxtX × List UInt8) := do
  let (prodId, bytes) ← Alpha.decode 20 bytes
  pure ({ prodId }, bytes)

@[simp] theorem encode_length (message : LegSymSymbolTxtX) : (encode message).length = 20 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : LegSymSymbolTxtX) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LegSymSymbolTxtX) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end LegSymSymbolTxtX

/-- Leg Entry Txt: 23 bytes -/
structure LegEntryTxt where
  legSymSymbolTxtX : LegSymSymbolTxtX
  legSideUint81 : BitVec 8
  legQtyUint162 : BitVec 16
  deriving DecidableEq, Repr

namespace LegEntryTxt

def encode (message : LegEntryTxt) : List UInt8 :=
  LegSymSymbolTxtX.encode message.legSymSymbolTxtX
    ++ (encodeUInt 1 message.legSideUint81
    ++ (encodeUInt 2 message.legQtyUint162))

def decode (bytes : List UInt8) : Option (LegEntryTxt × List UInt8) := do
  let (legSymSymbolTxtX, bytes) ← LegSymSymbolTxtX.decode bytes
  let (legSideUint81, bytes) ← decodeUInt 1 bytes
  let (legQtyUint162, bytes) ← decodeUInt 2 bytes
  pure ({ legSymSymbolTxtX, legSideUint81, legQtyUint162 }, bytes)

@[simp] theorem encode_length (message : LegEntryTxt) : (encode message).length = 23 := by
  unfold encode
  simp only [List.length_append, LegSymSymbolTxtX.encode_length, encodeUInt_length]

theorem encode_length_pos (message : LegEntryTxt) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LegEntryTxt) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LegSymSymbolTxtX.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end LegEntryTxt

/-- Multi Leg Txt -/
structure MultiLegTxt where
  combOp : BitVec 8
  legEntryTxt : Bounded 1 LegEntryTxt
  deriving DecidableEq, Repr

namespace MultiLegTxt

def encode (message : MultiLegTxt) : List UInt8 :=
  encodeUInt 1 (BitVec.ofNat (8 * 1) message.legEntryTxt.val.length)
    ++ (encodeUInt 1 message.combOp
    ++ (encodeMany LegEntryTxt.encode message.legEntryTxt.val))

def decode (bytes : List UInt8) : Option (MultiLegTxt × List UInt8) := do
  let (noLeg, bytes) ← decodeUInt 1 bytes
  let (combOp, bytes) ← decodeUInt 1 bytes
  let (legEntryTxt_, bytes) ← decodeMany LegEntryTxt.decode noLeg.toNat bytes
  if fits_legEntryTxt : legEntryTxt_.length < 256 ^ 1 then
    pure ({ combOp, legEntryTxt := ⟨legEntryTxt_, fits_legEntryTxt⟩ }, bytes)
  else none

theorem encode_length_pos (message : MultiLegTxt) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MultiLegTxt) : (encode message).length ≤ 5867 := by
  have bound_legEntryTxt := message.legEntryTxt.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const LegEntryTxt.encode 23 LegEntryTxt.encode_length]
  omega

@[simp] theorem decode_encode (message : MultiLegTxt) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 LegEntryTxt.encode LegEntryTxt.decode LegEntryTxt.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.legEntryTxt.length_lt]
  rfl

end MultiLegTxt

/-- Any Sym Flex Product X, selected by Msg Type Ext -/
inductive SymFlexProductX where
  | symbolNumX (message : SymbolNumX) -- 1
  | symbolTxtX (message : SymbolTxtX) -- 2
  | multiLegNum (message : MultiLegNum) -- 3
  | multiLegTxt (message : MultiLegTxt) -- 4
  deriving DecidableEq, Repr

namespace SymFlexProductX

/-- The Msg Type Ext each message is sent under -/
def tag : SymFlexProductX → BitVec 8
  | .symbolNumX _ => 1
  | .symbolTxtX _ => 2
  | .multiLegNum _ => 3
  | .multiLegTxt _ => 4

def encode : SymFlexProductX → List UInt8
  | .symbolNumX message => SymbolNumX.encode message
  | .symbolTxtX message => SymbolTxtX.encode message
  | .multiLegNum message => MultiLegNum.encode message
  | .multiLegTxt message => MultiLegTxt.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : SymFlexProductX) : (encode message).length ≤ 5867 := by
  cases message with
  | symbolNumX inner =>
    simp only [encode, SymbolNumX.encode_length]
    omega
  | symbolTxtX inner =>
    simp only [encode, SymbolTxtX.encode_length]
    omega
  | multiLegNum inner =>
    have bound_inner := MultiLegNum.encode_length_le inner
    simp only [encode]
    omega
  | multiLegTxt inner =>
    have bound_inner := MultiLegTxt.encode_length_le inner
    simp only [encode]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (SymFlexProductX × List UInt8) :=
  if tag = 1 then (SymbolNumX.decode bytes).map fun (message, rest) => (.symbolNumX message, rest)
  else if tag = 2 then (SymbolTxtX.decode bytes).map fun (message, rest) => (.symbolTxtX message, rest)
  else if tag = 3 then (MultiLegNum.decode bytes).map fun (message, rest) => (.multiLegNum message, rest)
  else if tag = 4 then (MultiLegTxt.decode bytes).map fun (message, rest) => (.multiLegTxt message, rest)
  else none

@[simp] theorem decode_encode (message : SymFlexProductX) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end SymFlexProductX

/-- Org Trans Time Msg Time X: 8 bytes -/
structure OrgTransTimeMsgTimeX where
  epochSUint324 : BitVec 32
  nanosecond : BitVec 32
  deriving DecidableEq, Repr

namespace OrgTransTimeMsgTimeX

def encode (message : OrgTransTimeMsgTimeX) : List UInt8 :=
  encodeUInt 4 message.epochSUint324
    ++ (encodeUInt 4 message.nanosecond)

def decode (bytes : List UInt8) : Option (OrgTransTimeMsgTimeX × List UInt8) := do
  let (epochSUint324, bytes) ← decodeUInt 4 bytes
  let (nanosecond, bytes) ← decodeUInt 4 bytes
  pure ({ epochSUint324, nanosecond }, bytes)

@[simp] theorem encode_length (message : OrgTransTimeMsgTimeX) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : OrgTransTimeMsgTimeX) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrgTransTimeMsgTimeX) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrgTransTimeMsgTimeX

/-- Transact Time Msg Time X: 8 bytes -/
structure TransactTimeMsgTimeX where
  epochSUint324 : BitVec 32
  nanosecond : BitVec 32
  deriving DecidableEq, Repr

namespace TransactTimeMsgTimeX

def encode (message : TransactTimeMsgTimeX) : List UInt8 :=
  encodeUInt 4 message.epochSUint324
    ++ (encodeUInt 4 message.nanosecond)

def decode (bytes : List UInt8) : Option (TransactTimeMsgTimeX × List UInt8) := do
  let (epochSUint324, bytes) ← decodeUInt 4 bytes
  let (nanosecond, bytes) ← decodeUInt 4 bytes
  pure ({ epochSUint324, nanosecond }, bytes)

@[simp] theorem encode_length (message : TransactTimeMsgTimeX) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : TransactTimeMsgTimeX) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TransactTimeMsgTimeX) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TransactTimeMsgTimeX

/-- Flex Order Status Report Message -/
structure FlexOrderStatusReportMessage where
  preserve : BitVec 8
  msgTimeNs : BitVec 32
  partId : BitVec 8
  noLeg : BitVec 8
  statusCodeUint162 : BitVec 16
  execType : ExecType
  cmId : BitVec 16
  fcmId : BitVec 16
  orderNo : Alpha 5
  ordId : BitVec 32
  userDefine : Alpha 8
  symFlexProductX : SymFlexProductX
  price : BitVec 32
  qty : BitVec 16
  investorAcno : BitVec 32
  investorFlag : Alpha 1
  side : BitVec 8
  ordType : BitVec 8
  timeInForce : BitVec 8
  positionEffect : PositionEffect
  lastPx : BitVec 32
  lastQty : BitVec 16
  pxSubtotal : BitVec 64
  cumQty : BitVec 16
  leavesQty : BitVec 16
  beforeQty : BitVec 16
  orgTransTimeMsgTimeX : OrgTransTimeMsgTimeX
  transactTimeMsgTimeX : TransactTimeMsgTimeX
  targetId : BitVec 8
  uniqId : BitVec 32
  rptSeq : BitVec 32
  rptSessionId : BitVec 16
  rptSessionSeq : BitVec 32
  reserved12 : Alpha 12
  deriving DecidableEq, Repr

namespace FlexOrderStatusReportMessage

def encode (message : FlexOrderStatusReportMessage) : List UInt8 :=
  encodeUInt 1 (SymFlexProductX.tag message.symFlexProductX)
    ++ (encodeUInt 1 message.preserve
    ++ (encodeUInt 4 message.msgTimeNs
    ++ (encodeUInt 1 message.partId
    ++ (encodeUInt 1 message.noLeg
    ++ (encodeUInt 2 message.statusCodeUint162
    ++ (ExecType.encode message.execType
    ++ (encodeUInt 2 message.cmId
    ++ (encodeUInt 2 message.fcmId
    ++ (Alpha.encode message.orderNo
    ++ (encodeUInt 4 message.ordId
    ++ (Alpha.encode message.userDefine
    ++ (SymFlexProductX.encode message.symFlexProductX
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 2 message.qty
    ++ (encodeUInt 4 message.investorAcno
    ++ (Alpha.encode message.investorFlag
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.ordType
    ++ (encodeUInt 1 message.timeInForce
    ++ (PositionEffect.encode message.positionEffect
    ++ (encodeUInt 4 message.lastPx
    ++ (encodeUInt 2 message.lastQty
    ++ (encodeUInt 8 message.pxSubtotal
    ++ (encodeUInt 2 message.cumQty
    ++ (encodeUInt 2 message.leavesQty
    ++ (encodeUInt 2 message.beforeQty
    ++ (OrgTransTimeMsgTimeX.encode message.orgTransTimeMsgTimeX
    ++ (TransactTimeMsgTimeX.encode message.transactTimeMsgTimeX
    ++ (encodeUInt 1 message.targetId
    ++ (encodeUInt 4 message.uniqId
    ++ (encodeUInt 4 message.rptSeq
    ++ (encodeUInt 2 message.rptSessionId
    ++ (encodeUInt 4 message.rptSessionSeq
    ++ (Alpha.encode message.reserved12))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (FlexOrderStatusReportMessage × List UInt8) := do
  let (msgTypeExt, bytes) ← decodeUInt 1 bytes
  let (preserve, bytes) ← decodeUInt 1 bytes
  let (msgTimeNs, bytes) ← decodeUInt 4 bytes
  let (partId, bytes) ← decodeUInt 1 bytes
  let (noLeg, bytes) ← decodeUInt 1 bytes
  let (statusCodeUint162, bytes) ← decodeUInt 2 bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (cmId, bytes) ← decodeUInt 2 bytes
  let (fcmId, bytes) ← decodeUInt 2 bytes
  let (orderNo, bytes) ← Alpha.decode 5 bytes
  let (ordId, bytes) ← decodeUInt 4 bytes
  let (userDefine, bytes) ← Alpha.decode 8 bytes
  let (symFlexProductX, bytes) ← SymFlexProductX.decode msgTypeExt bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (qty, bytes) ← decodeUInt 2 bytes
  let (investorAcno, bytes) ← decodeUInt 4 bytes
  let (investorFlag, bytes) ← Alpha.decode 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (ordType, bytes) ← decodeUInt 1 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (positionEffect, bytes) ← PositionEffect.decode bytes
  let (lastPx, bytes) ← decodeUInt 4 bytes
  let (lastQty, bytes) ← decodeUInt 2 bytes
  let (pxSubtotal, bytes) ← decodeUInt 8 bytes
  let (cumQty, bytes) ← decodeUInt 2 bytes
  let (leavesQty, bytes) ← decodeUInt 2 bytes
  let (beforeQty, bytes) ← decodeUInt 2 bytes
  let (orgTransTimeMsgTimeX, bytes) ← OrgTransTimeMsgTimeX.decode bytes
  let (transactTimeMsgTimeX, bytes) ← TransactTimeMsgTimeX.decode bytes
  let (targetId, bytes) ← decodeUInt 1 bytes
  let (uniqId, bytes) ← decodeUInt 4 bytes
  let (rptSeq, bytes) ← decodeUInt 4 bytes
  let (rptSessionId, bytes) ← decodeUInt 2 bytes
  let (rptSessionSeq, bytes) ← decodeUInt 4 bytes
  let (reserved12, bytes) ← Alpha.decode 12 bytes
  pure ({ preserve, msgTimeNs, partId, noLeg, statusCodeUint162, execType, cmId, fcmId, orderNo, ordId, userDefine, symFlexProductX, price, qty, investorAcno, investorFlag, side, ordType, timeInForce, positionEffect, lastPx, lastQty, pxSubtotal, cumQty, leavesQty, beforeQty, orgTransTimeMsgTimeX, transactTimeMsgTimeX, targetId, uniqId, rptSeq, rptSessionId, rptSessionSeq, reserved12 }, bytes)

theorem encode_length_pos (message : FlexOrderStatusReportMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : FlexOrderStatusReportMessage) : (encode message).length ≤ 5977 := by
  unfold encode
  cases message.symFlexProductX with
  | symbolNumX inner =>
    simp only [SymFlexProductX.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ExecType.encode_length, Alpha.encode_length, PositionEffect.encode_length, OrgTransTimeMsgTimeX.encode_length, TransactTimeMsgTimeX.encode_length, SymbolNumX.encode_length]
    omega
  | symbolTxtX inner =>
    simp only [SymFlexProductX.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ExecType.encode_length, Alpha.encode_length, PositionEffect.encode_length, OrgTransTimeMsgTimeX.encode_length, TransactTimeMsgTimeX.encode_length, SymbolTxtX.encode_length]
    omega
  | multiLegNum inner =>
    have bound_inner := MultiLegNum.encode_length_le inner
    simp only [SymFlexProductX.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ExecType.encode_length, Alpha.encode_length, PositionEffect.encode_length, OrgTransTimeMsgTimeX.encode_length, TransactTimeMsgTimeX.encode_length]
    omega
  | multiLegTxt inner =>
    have bound_inner := MultiLegTxt.encode_length_le inner
    simp only [SymFlexProductX.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ExecType.encode_length, Alpha.encode_length, PositionEffect.encode_length, OrgTransTimeMsgTimeX.encode_length, TransactTimeMsgTimeX.encode_length]
    omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : FlexOrderStatusReportMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
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
  rw [List.append_assoc, SymFlexProductX.decode_encode, some_bind]
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
  rw [List.append_assoc, PositionEffect.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OrgTransTimeMsgTimeX.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TransactTimeMsgTimeX.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FlexOrderStatusReportMessage

/-- Clearing Member Initiate Operation Message: 7 bytes -/
structure ClearingMemberInitiateOperationMessage where
  memberId : BitVec 16
  targetId : BitVec 8
  reqCmSeq : BitVec 32
  deriving DecidableEq, Repr

namespace ClearingMemberInitiateOperationMessage

def encode (message : ClearingMemberInitiateOperationMessage) : List UInt8 :=
  encodeUInt 2 message.memberId
    ++ (encodeUInt 1 message.targetId
    ++ (encodeUInt 4 message.reqCmSeq))

def decode (bytes : List UInt8) : Option (ClearingMemberInitiateOperationMessage × List UInt8) := do
  let (memberId, bytes) ← decodeUInt 2 bytes
  let (targetId, bytes) ← decodeUInt 1 bytes
  let (reqCmSeq, bytes) ← decodeUInt 4 bytes
  pure ({ memberId, targetId, reqCmSeq }, bytes)

@[simp] theorem encode_length (message : ClearingMemberInitiateOperationMessage) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : ClearingMemberInitiateOperationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ClearingMemberInitiateOperationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ClearingMemberInitiateOperationMessage

/-- Clearing Member Initiate Operation Confirmed Message: 8 bytes -/
structure ClearingMemberInitiateOperationConfirmedMessage where
  statusCodeUint81 : BitVec 8
  memberId : BitVec 16
  targetId : BitVec 8
  reqCmSeq : BitVec 32
  deriving DecidableEq, Repr

namespace ClearingMemberInitiateOperationConfirmedMessage

def encode (message : ClearingMemberInitiateOperationConfirmedMessage) : List UInt8 :=
  encodeUInt 1 message.statusCodeUint81
    ++ (encodeUInt 2 message.memberId
    ++ (encodeUInt 1 message.targetId
    ++ (encodeUInt 4 message.reqCmSeq)))

def decode (bytes : List UInt8) : Option (ClearingMemberInitiateOperationConfirmedMessage × List UInt8) := do
  let (statusCodeUint81, bytes) ← decodeUInt 1 bytes
  let (memberId, bytes) ← decodeUInt 2 bytes
  let (targetId, bytes) ← decodeUInt 1 bytes
  let (reqCmSeq, bytes) ← decodeUInt 4 bytes
  pure ({ statusCodeUint81, memberId, targetId, reqCmSeq }, bytes)

@[simp] theorem encode_length (message : ClearingMemberInitiateOperationConfirmedMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : ClearingMemberInitiateOperationConfirmedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ClearingMemberInitiateOperationConfirmedMessage) (rest : List UInt8) :
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

end ClearingMemberInitiateOperationConfirmedMessage

/-- Flex Clearing Member Initiate Operation Message: 14 bytes -/
structure FlexClearingMemberInitiateOperationMessage where
  subHdr : SubHdr
  partId : BitVec 8
  memberId : BitVec 16
  targetId : BitVec 8
  reqCmSeq : BitVec 32
  deriving DecidableEq, Repr

namespace FlexClearingMemberInitiateOperationMessage

def encode (message : FlexClearingMemberInitiateOperationMessage) : List UInt8 :=
  SubHdr.encode message.subHdr
    ++ (encodeUInt 1 message.partId
    ++ (encodeUInt 2 message.memberId
    ++ (encodeUInt 1 message.targetId
    ++ (encodeUInt 4 message.reqCmSeq))))

def decode (bytes : List UInt8) : Option (FlexClearingMemberInitiateOperationMessage × List UInt8) := do
  let (subHdr, bytes) ← SubHdr.decode bytes
  let (partId, bytes) ← decodeUInt 1 bytes
  let (memberId, bytes) ← decodeUInt 2 bytes
  let (targetId, bytes) ← decodeUInt 1 bytes
  let (reqCmSeq, bytes) ← decodeUInt 4 bytes
  pure ({ subHdr, partId, memberId, targetId, reqCmSeq }, bytes)

@[simp] theorem encode_length (message : FlexClearingMemberInitiateOperationMessage) : (encode message).length = 14 := by
  unfold encode
  simp only [List.length_append, SubHdr.encode_length, encodeUInt_length]

theorem encode_length_pos (message : FlexClearingMemberInitiateOperationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FlexClearingMemberInitiateOperationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, SubHdr.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end FlexClearingMemberInitiateOperationMessage

/-- Flex Clearing Member Initiate Operation Confirmed Message: 32 bytes -/
structure FlexClearingMemberInitiateOperationConfirmedMessage where
  subHdr : SubHdr
  partId : BitVec 8
  statusCodeUint162 : BitVec 16
  memberId : BitVec 16
  targetId : BitVec 8
  reqCmSeq : BitVec 32
  reserved16 : Alpha 16
  deriving DecidableEq, Repr

namespace FlexClearingMemberInitiateOperationConfirmedMessage

def encode (message : FlexClearingMemberInitiateOperationConfirmedMessage) : List UInt8 :=
  SubHdr.encode message.subHdr
    ++ (encodeUInt 1 message.partId
    ++ (encodeUInt 2 message.statusCodeUint162
    ++ (encodeUInt 2 message.memberId
    ++ (encodeUInt 1 message.targetId
    ++ (encodeUInt 4 message.reqCmSeq
    ++ (Alpha.encode message.reserved16))))))

def decode (bytes : List UInt8) : Option (FlexClearingMemberInitiateOperationConfirmedMessage × List UInt8) := do
  let (subHdr, bytes) ← SubHdr.decode bytes
  let (partId, bytes) ← decodeUInt 1 bytes
  let (statusCodeUint162, bytes) ← decodeUInt 2 bytes
  let (memberId, bytes) ← decodeUInt 2 bytes
  let (targetId, bytes) ← decodeUInt 1 bytes
  let (reqCmSeq, bytes) ← decodeUInt 4 bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  pure ({ subHdr, partId, statusCodeUint162, memberId, targetId, reqCmSeq, reserved16 }, bytes)

@[simp] theorem encode_length (message : FlexClearingMemberInitiateOperationConfirmedMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, SubHdr.encode_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : FlexClearingMemberInitiateOperationConfirmedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FlexClearingMemberInitiateOperationConfirmedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, SubHdr.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FlexClearingMemberInitiateOperationConfirmedMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | wakeUpCallMessage (message : WakeUpCallMessage) -- 10
  | wakeUpCallConfirmedMessage (message : WakeUpCallConfirmedMessage) -- 20
  | logonNoticeMessage (message : LogonNoticeMessage) -- 30
  | finalSequentialNumberNotificationForGroupMessage (message : FinalSequentialNumberNotificationForGroupMessage) -- 230
  | requestLogonMessage (message : RequestLogonMessage) -- 40
  | activateApplicationSystemMessage (message : ActivateApplicationSystemMessage) -- 50
  | activateApplicationSystemConfirmedMessage (message : ActivateApplicationSystemConfirmedMessage) -- 60
  | logoutMessage (message : LogoutMessage) -- 70
  | logoutConfirmedMessage (message : LogoutConfirmedMessage) -- 80
  | confirmConnectionMessage (message : ConfirmConnectionMessage) -- 104
  | connectionConfirmedMessage (message : ConnectionConfirmedMessage) -- 105
  | orderStatusReportMessage (message : OrderStatusReportMessage) -- 102
  | orderStatusReportLongFormatMessage (message : OrderStatusReportLongFormatMessage) -- 132
  | executionReportIncludingHeadOfficeAndBranchOfficesMessage (message : ExecutionReportIncludingHeadOfficeAndBranchOfficesMessage) -- 106
  | flexOrderStatusReportMessage (message : FlexOrderStatusReportMessage) -- 202
  | clearingMemberInitiateOperationMessage (message : ClearingMemberInitiateOperationMessage) -- 115
  | clearingMemberInitiateOperationConfirmedMessage (message : ClearingMemberInitiateOperationConfirmedMessage) -- 116
  | flexClearingMemberInitiateOperationMessage (message : FlexClearingMemberInitiateOperationMessage) -- 215
  | flexClearingMemberInitiateOperationConfirmedMessage (message : FlexClearingMemberInitiateOperationConfirmedMessage) -- 216
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .wakeUpCallMessage _ => 10
  | .wakeUpCallConfirmedMessage _ => 20
  | .logonNoticeMessage _ => 30
  | .finalSequentialNumberNotificationForGroupMessage _ => 230
  | .requestLogonMessage _ => 40
  | .activateApplicationSystemMessage _ => 50
  | .activateApplicationSystemConfirmedMessage _ => 60
  | .logoutMessage _ => 70
  | .logoutConfirmedMessage _ => 80
  | .confirmConnectionMessage _ => 104
  | .connectionConfirmedMessage _ => 105
  | .orderStatusReportMessage _ => 102
  | .orderStatusReportLongFormatMessage _ => 132
  | .executionReportIncludingHeadOfficeAndBranchOfficesMessage _ => 106
  | .flexOrderStatusReportMessage _ => 202
  | .clearingMemberInitiateOperationMessage _ => 115
  | .clearingMemberInitiateOperationConfirmedMessage _ => 116
  | .flexClearingMemberInitiateOperationMessage _ => 215
  | .flexClearingMemberInitiateOperationConfirmedMessage _ => 216

def encode : Payload → List UInt8
  | .wakeUpCallMessage message => WakeUpCallMessage.encode message
  | .wakeUpCallConfirmedMessage message => WakeUpCallConfirmedMessage.encode message
  | .logonNoticeMessage message => LogonNoticeMessage.encode message
  | .finalSequentialNumberNotificationForGroupMessage message => FinalSequentialNumberNotificationForGroupMessage.encode message
  | .requestLogonMessage message => RequestLogonMessage.encode message
  | .activateApplicationSystemMessage message => ActivateApplicationSystemMessage.encode message
  | .activateApplicationSystemConfirmedMessage message => ActivateApplicationSystemConfirmedMessage.encode message
  | .logoutMessage message => LogoutMessage.encode message
  | .logoutConfirmedMessage message => LogoutConfirmedMessage.encode message
  | .confirmConnectionMessage message => ConfirmConnectionMessage.encode message
  | .connectionConfirmedMessage message => ConnectionConfirmedMessage.encode message
  | .orderStatusReportMessage message => OrderStatusReportMessage.encode message
  | .orderStatusReportLongFormatMessage message => OrderStatusReportLongFormatMessage.encode message
  | .executionReportIncludingHeadOfficeAndBranchOfficesMessage message => ExecutionReportIncludingHeadOfficeAndBranchOfficesMessage.encode message
  | .flexOrderStatusReportMessage message => FlexOrderStatusReportMessage.encode message
  | .clearingMemberInitiateOperationMessage message => ClearingMemberInitiateOperationMessage.encode message
  | .clearingMemberInitiateOperationConfirmedMessage message => ClearingMemberInitiateOperationConfirmedMessage.encode message
  | .flexClearingMemberInitiateOperationMessage message => FlexClearingMemberInitiateOperationMessage.encode message
  | .flexClearingMemberInitiateOperationConfirmedMessage message => FlexClearingMemberInitiateOperationConfirmedMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 5977 := by
  cases message with
  | wakeUpCallMessage inner =>
    simp only [encode, WakeUpCallMessage.encode_length]
    omega
  | wakeUpCallConfirmedMessage inner =>
    simp only [encode, WakeUpCallConfirmedMessage.encode_length]
    omega
  | logonNoticeMessage inner =>
    simp only [encode, LogonNoticeMessage.encode_length]
    omega
  | finalSequentialNumberNotificationForGroupMessage inner =>
    simp only [encode, FinalSequentialNumberNotificationForGroupMessage.encode_length]
    omega
  | requestLogonMessage inner =>
    simp only [encode, RequestLogonMessage.encode_length]
    omega
  | activateApplicationSystemMessage inner =>
    simp only [encode, ActivateApplicationSystemMessage.encode_length]
    omega
  | activateApplicationSystemConfirmedMessage inner =>
    simp only [encode, ActivateApplicationSystemConfirmedMessage.encode_length]
    omega
  | logoutMessage inner =>
    simp only [encode, LogoutMessage.encode_length]
    omega
  | logoutConfirmedMessage inner =>
    simp only [encode, LogoutConfirmedMessage.encode_length]
    omega
  | confirmConnectionMessage inner =>
    simp only [encode, ConfirmConnectionMessage.encode_length]
    omega
  | connectionConfirmedMessage inner =>
    simp only [encode, ConnectionConfirmedMessage.encode_length]
    omega
  | orderStatusReportMessage inner =>
    have bound_inner := OrderStatusReportMessage.encode_length_le inner
    simp only [encode]
    omega
  | orderStatusReportLongFormatMessage inner =>
    have bound_inner := OrderStatusReportLongFormatMessage.encode_length_le inner
    simp only [encode]
    omega
  | executionReportIncludingHeadOfficeAndBranchOfficesMessage inner =>
    have bound_inner := ExecutionReportIncludingHeadOfficeAndBranchOfficesMessage.encode_length_le inner
    simp only [encode]
    omega
  | flexOrderStatusReportMessage inner =>
    have bound_inner := FlexOrderStatusReportMessage.encode_length_le inner
    simp only [encode]
    omega
  | clearingMemberInitiateOperationMessage inner =>
    simp only [encode, ClearingMemberInitiateOperationMessage.encode_length]
    omega
  | clearingMemberInitiateOperationConfirmedMessage inner =>
    simp only [encode, ClearingMemberInitiateOperationConfirmedMessage.encode_length]
    omega
  | flexClearingMemberInitiateOperationMessage inner =>
    simp only [encode, FlexClearingMemberInitiateOperationMessage.encode_length]
    omega
  | flexClearingMemberInitiateOperationConfirmedMessage inner =>
    simp only [encode, FlexClearingMemberInitiateOperationConfirmedMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 10 then (WakeUpCallMessage.decode bytes).map fun (message, rest) => (.wakeUpCallMessage message, rest)
  else if tag = 20 then (WakeUpCallConfirmedMessage.decode bytes).map fun (message, rest) => (.wakeUpCallConfirmedMessage message, rest)
  else if tag = 30 then (LogonNoticeMessage.decode bytes).map fun (message, rest) => (.logonNoticeMessage message, rest)
  else if tag = 230 then (FinalSequentialNumberNotificationForGroupMessage.decode bytes).map fun (message, rest) => (.finalSequentialNumberNotificationForGroupMessage message, rest)
  else if tag = 40 then (RequestLogonMessage.decode bytes).map fun (message, rest) => (.requestLogonMessage message, rest)
  else if tag = 50 then (ActivateApplicationSystemMessage.decode bytes).map fun (message, rest) => (.activateApplicationSystemMessage message, rest)
  else if tag = 60 then (ActivateApplicationSystemConfirmedMessage.decode bytes).map fun (message, rest) => (.activateApplicationSystemConfirmedMessage message, rest)
  else if tag = 70 then (LogoutMessage.decode bytes).map fun (message, rest) => (.logoutMessage message, rest)
  else if tag = 80 then (LogoutConfirmedMessage.decode bytes).map fun (message, rest) => (.logoutConfirmedMessage message, rest)
  else if tag = 104 then (ConfirmConnectionMessage.decode bytes).map fun (message, rest) => (.confirmConnectionMessage message, rest)
  else if tag = 105 then (ConnectionConfirmedMessage.decode bytes).map fun (message, rest) => (.connectionConfirmedMessage message, rest)
  else if tag = 102 then (OrderStatusReportMessage.decode bytes).map fun (message, rest) => (.orderStatusReportMessage message, rest)
  else if tag = 132 then (OrderStatusReportLongFormatMessage.decode bytes).map fun (message, rest) => (.orderStatusReportLongFormatMessage message, rest)
  else if tag = 106 then (ExecutionReportIncludingHeadOfficeAndBranchOfficesMessage.decode bytes).map fun (message, rest) => (.executionReportIncludingHeadOfficeAndBranchOfficesMessage message, rest)
  else if tag = 202 then (FlexOrderStatusReportMessage.decode bytes).map fun (message, rest) => (.flexOrderStatusReportMessage message, rest)
  else if tag = 115 then (ClearingMemberInitiateOperationMessage.decode bytes).map fun (message, rest) => (.clearingMemberInitiateOperationMessage message, rest)
  else if tag = 116 then (ClearingMemberInitiateOperationConfirmedMessage.decode bytes).map fun (message, rest) => (.clearingMemberInitiateOperationConfirmedMessage message, rest)
  else if tag = 215 then (FlexClearingMemberInitiateOperationMessage.decode bytes).map fun (message, rest) => (.flexClearingMemberInitiateOperationMessage message, rest)
  else if tag = 216 then (FlexClearingMemberInitiateOperationConfirmedMessage.decode bytes).map fun (message, rest) => (.flexClearingMemberInitiateOperationConfirmedMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message Tail: 1 bytes -/
structure MessageTail where
  checkSum : BitVec 8
  deriving DecidableEq, Repr

namespace MessageTail

def encode (message : MessageTail) : List UInt8 :=
  encodeUInt 1 message.checkSum

def decode (bytes : List UInt8) : Option (MessageTail × List UInt8) := do
  let (checkSum, bytes) ← decodeUInt 1 bytes
  pure ({ checkSum }, bytes)

@[simp] theorem encode_length (message : MessageTail) : (encode message).length = 1 := by
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

/-- Tmp Message -/
structure TmpMessage where
  msgLength : BitVec 16
  msgSeqNum : BitVec 32
  headerTime : HeaderTime
  fcmId : BitVec 16
  sessionId : BitVec 16
  payload : Payload
  messageTail : MessageTail
  deriving DecidableEq, Repr

namespace TmpMessage

def encode (message : TmpMessage) : List UInt8 :=
  encodeUInt 2 message.msgLength
    ++ (encodeUInt 4 message.msgSeqNum
    ++ (HeaderTime.encode message.headerTime
    ++ (encodeUInt 1 (Payload.tag message.payload)
    ++ (encodeUInt 2 message.fcmId
    ++ (encodeUInt 2 message.sessionId
    ++ (Payload.encode message.payload
    ++ (MessageTail.encode message.messageTail)))))))

def decode (bytes : List UInt8) : Option (TmpMessage × List UInt8) := do
  let (msgLength, bytes) ← decodeUInt 2 bytes
  let (msgSeqNum, bytes) ← decodeUInt 4 bytes
  let (headerTime, bytes) ← HeaderTime.decode bytes
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (fcmId, bytes) ← decodeUInt 2 bytes
  let (sessionId, bytes) ← decodeUInt 2 bytes
  let (payload, bytes) ← Payload.decode messageType bytes
  let (messageTail, bytes) ← MessageTail.decode bytes
  pure ({ msgLength, msgSeqNum, headerTime, fcmId, sessionId, payload, messageTail }, bytes)

theorem encode_length_pos (message : TmpMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TmpMessage) : (encode message).length ≤ 5995 := by
  unfold encode
  cases message.payload with
  | wakeUpCallMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, HeaderTime.encode_length, MessageTail.encode_length, WakeUpCallMessage.encode_length]
    omega
  | wakeUpCallConfirmedMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, HeaderTime.encode_length, MessageTail.encode_length, WakeUpCallConfirmedMessage.encode_length]
    omega
  | logonNoticeMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, HeaderTime.encode_length, MessageTail.encode_length, LogonNoticeMessage.encode_length]
    omega
  | finalSequentialNumberNotificationForGroupMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, HeaderTime.encode_length, MessageTail.encode_length, FinalSequentialNumberNotificationForGroupMessage.encode_length]
    omega
  | requestLogonMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, HeaderTime.encode_length, MessageTail.encode_length, RequestLogonMessage.encode_length]
    omega
  | activateApplicationSystemMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, HeaderTime.encode_length, MessageTail.encode_length, ActivateApplicationSystemMessage.encode_length]
    omega
  | activateApplicationSystemConfirmedMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, HeaderTime.encode_length, MessageTail.encode_length, ActivateApplicationSystemConfirmedMessage.encode_length]
    omega
  | logoutMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, HeaderTime.encode_length, MessageTail.encode_length, LogoutMessage.encode_length]
    omega
  | logoutConfirmedMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, HeaderTime.encode_length, MessageTail.encode_length, LogoutConfirmedMessage.encode_length]
    omega
  | confirmConnectionMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, HeaderTime.encode_length, MessageTail.encode_length, ConfirmConnectionMessage.encode_length]
    omega
  | connectionConfirmedMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, HeaderTime.encode_length, MessageTail.encode_length, ConnectionConfirmedMessage.encode_length]
    omega
  | orderStatusReportMessage inner =>
    have bound_inner := OrderStatusReportMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, HeaderTime.encode_length, MessageTail.encode_length]
    omega
  | orderStatusReportLongFormatMessage inner =>
    have bound_inner := OrderStatusReportLongFormatMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, HeaderTime.encode_length, MessageTail.encode_length]
    omega
  | executionReportIncludingHeadOfficeAndBranchOfficesMessage inner =>
    have bound_inner := ExecutionReportIncludingHeadOfficeAndBranchOfficesMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, HeaderTime.encode_length, MessageTail.encode_length]
    omega
  | flexOrderStatusReportMessage inner =>
    have bound_inner := FlexOrderStatusReportMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, HeaderTime.encode_length, MessageTail.encode_length]
    omega
  | clearingMemberInitiateOperationMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, HeaderTime.encode_length, MessageTail.encode_length, ClearingMemberInitiateOperationMessage.encode_length]
    omega
  | clearingMemberInitiateOperationConfirmedMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, HeaderTime.encode_length, MessageTail.encode_length, ClearingMemberInitiateOperationConfirmedMessage.encode_length]
    omega
  | flexClearingMemberInitiateOperationMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, HeaderTime.encode_length, MessageTail.encode_length, FlexClearingMemberInitiateOperationMessage.encode_length]
    omega
  | flexClearingMemberInitiateOperationConfirmedMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, HeaderTime.encode_length, MessageTail.encode_length, FlexClearingMemberInitiateOperationConfirmedMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : TmpMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, HeaderTime.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Payload.decode_encode, some_bind]
  dsimp only
  rw [MessageTail.decode_encode, some_bind]
  rfl

end TmpMessage

end Omi.TaifexTaifexderivativesClearingmemberTmpV2187
