import Wire

/-!
# Taiwan Futures Exchange Order Entry v2.18.7

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.TaifexTaifexderivativesOrderentryTmpV2187

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

/-- Order Source: one byte code -/
def OrderSource.codes : List UInt8 :=
  [0x44, 0x41, 0x4D, 0x57, 0x50, 0x56, 0x47]

inductive OrderSource where
  | leasedLineOrVpnOrClosedPrivateNetwork -- Leased Line Or Vpn Or Closed Private Network
  | applicationProgramInterface -- Application Program Interface
  | mobileDevice -- Mobile Device
  | webSite -- Web Site
  | personalComputer -- Personal Computer
  | voice -- Voice
  | inWritingOrByTelephoneOrTelegram -- In Writing Or By Telephone Or Telegram
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderSource.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderSource

def toByte : OrderSource → UInt8
  | .leasedLineOrVpnOrClosedPrivateNetwork => 0x44
  | .applicationProgramInterface => 0x41
  | .mobileDevice => 0x4D
  | .webSite => 0x57
  | .personalComputer => 0x50
  | .voice => 0x56
  | .inWritingOrByTelephoneOrTelegram => 0x47
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderSource :=
  if byte = 0x44 then .leasedLineOrVpnOrClosedPrivateNetwork
  else if byte = 0x41 then .applicationProgramInterface
  else if byte = 0x4D then .mobileDevice
  else if byte = 0x57 then .webSite
  else if byte = 0x50 then .personalComputer
  else if byte = 0x56 then .voice
  else .inWritingOrByTelephoneOrTelegram

def ofByte (byte : UInt8) : OrderSource :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderSource) : ofByte value.toByte = value := by
  cases value with
  | leasedLineOrVpnOrClosedPrivateNetwork => decide
  | applicationProgramInterface => decide
  | mobileDevice => decide
  | webSite => decide
  | personalComputer => decide
  | voice => decide
  | inWritingOrByTelephoneOrTelegram => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderSource) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderSource × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderSource) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OrderSource) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OrderSource) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderSource

/-- Security Request Type: one byte code -/
def SecurityRequestType.codes : List UInt8 :=
  [0x31, 0x33]

inductive SecurityRequestType where
  | request -- Request
  | query -- Query
  | unlisted (byte : { byte : UInt8 // byte ∉ SecurityRequestType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SecurityRequestType

def toByte : SecurityRequestType → UInt8
  | .request => 0x31
  | .query => 0x33
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SecurityRequestType :=
  if byte = 0x31 then .request
  else .query

def ofByte (byte : UInt8) : SecurityRequestType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SecurityRequestType) : ofByte value.toByte = value := by
  cases value with
  | request => decide
  | query => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SecurityRequestType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SecurityRequestType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SecurityRequestType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SecurityRequestType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SecurityRequestType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SecurityRequestType

/-- Type: one byte code -/
def Type_.codes : List UInt8 :=
  [0x46, 0x4F]

inductive Type_ where
  | futures -- Futures
  | options -- Options
  | unlisted (byte : { byte : UInt8 // byte ∉ Type_.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Type_

def toByte : Type_ → UInt8
  | .futures => 0x46
  | .options => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Type_ :=
  if byte = 0x46 then .futures
  else .options

def ofByte (byte : UInt8) : Type_ :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Type_) : ofByte value.toByte = value := by
  cases value with
  | futures => decide
  | options => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Type_) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Type_ × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Type_) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Type_) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Type_) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Type_

/-- Application Type: one byte code -/
def ApplicationType.codes : List UInt8 :=
  [0x31, 0x32, 0x33]

inductive ApplicationType where
  | tradersDelegatedApplication -- Traders Delegated Application
  | proprietaryTradersSelfApplication -- Proprietary Traders Self Application
  | fcmsSelfApplication -- Fcms Self Application
  | unlisted (byte : { byte : UInt8 // byte ∉ ApplicationType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ApplicationType

def toByte : ApplicationType → UInt8
  | .tradersDelegatedApplication => 0x31
  | .proprietaryTradersSelfApplication => 0x32
  | .fcmsSelfApplication => 0x33
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ApplicationType :=
  if byte = 0x31 then .tradersDelegatedApplication
  else if byte = 0x32 then .proprietaryTradersSelfApplication
  else .fcmsSelfApplication

def ofByte (byte : UInt8) : ApplicationType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ApplicationType) : ofByte value.toByte = value := by
  cases value with
  | tradersDelegatedApplication => decide
  | proprietaryTradersSelfApplication => decide
  | fcmsSelfApplication => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ApplicationType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ApplicationType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ApplicationType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ApplicationType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ApplicationType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ApplicationType

/-- Expiry Type: one byte code -/
def ExpiryType.codes : List UInt8 :=
  [0x58]

inductive ExpiryType where
  | flexibleEuropeanStyleExerciseCashSettlement -- Flexible European Style Exercise Cash Settlement
  | unlisted (byte : { byte : UInt8 // byte ∉ ExpiryType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExpiryType

def toByte : ExpiryType → UInt8
  | .flexibleEuropeanStyleExerciseCashSettlement => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : ExpiryType :=
  .flexibleEuropeanStyleExerciseCashSettlement

def ofByte (byte : UInt8) : ExpiryType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExpiryType) : ofByte value.toByte = value := by
  cases value with
  | flexibleEuropeanStyleExerciseCashSettlement => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ExpiryType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ExpiryType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ExpiryType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ExpiryType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ExpiryType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ExpiryType

/-- Call Put Code: one byte code -/
def CallPutCode.codes : List UInt8 :=
  [0x43, 0x50]

inductive CallPutCode where
  | call -- Call
  | put -- Put
  | unlisted (byte : { byte : UInt8 // byte ∉ CallPutCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CallPutCode

def toByte : CallPutCode → UInt8
  | .call => 0x43
  | .put => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CallPutCode :=
  if byte = 0x43 then .call
  else .put

def ofByte (byte : UInt8) : CallPutCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CallPutCode) : ofByte value.toByte = value := by
  cases value with
  | call => decide
  | put => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CallPutCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CallPutCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CallPutCode) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CallPutCode) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CallPutCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CallPutCode

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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : WakeUpCallMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : WakeUpCallConfirmedMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LogonNoticeMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : FinalSequentialNumberNotificationForGroupMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : RequestLogonMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end RequestLogonMessage

/-- Resend Report Message -/
structure ResendReportMessage where
  statusCodeUint81 : BitVec 8
  isEof : BitVec 8
  fileSize : BitVec 32
  dataUint8HdrMsgLength156 : List UInt8
  deriving DecidableEq, Repr

namespace ResendReportMessage

def encode (message : ResendReportMessage) : List UInt8 :=
  encodeUInt 1 message.statusCodeUint81
    ++ (encodeUInt 1 message.isEof
    ++ (encodeUInt 4 message.fileSize
    ++ (encodeMany Byte.encode message.dataUint8HdrMsgLength156)))

def decode (bytes : List UInt8) : Option ResendReportMessage := do
  let (statusCodeUint81, bytes) ← decodeUInt 1 bytes
  let (isEof, bytes) ← decodeUInt 1 bytes
  let (fileSize, bytes) ← decodeUInt 4 bytes
  let dataUint8HdrMsgLength156 ← decodeAll Byte.decode bytes.length bytes
  pure { statusCodeUint81, isEof, fileSize, dataUint8HdrMsgLength156 }

theorem encode_length_pos (message : ResendReportMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

theorem decode_encode (message : ResendReportMessage) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeAll_encodeMany Byte.encode Byte.decode Byte.decode_encode Byte.encode_length_pos message.dataUint8HdrMsgLength156 _ (encodeMany_length_ge Byte.encode Byte.encode_length_pos message.dataUint8HdrMsgLength156), some_bind]
  rfl

end ResendReportMessage

/-- Resend Report Confirmed Message: 1 bytes -/
structure ResendReportConfirmedMessage where
  statusCodeUint81 : BitVec 8
  deriving DecidableEq, Repr

namespace ResendReportConfirmedMessage

def encode (message : ResendReportConfirmedMessage) : List UInt8 :=
  encodeUInt 1 message.statusCodeUint81

def decode (bytes : List UInt8) : Option (ResendReportConfirmedMessage × List UInt8) := do
  let (statusCodeUint81, bytes) ← decodeUInt 1 bytes
  pure ({ statusCodeUint81 }, bytes)

@[simp] theorem encode_length (message : ResendReportConfirmedMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : ResendReportConfirmedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ResendReportConfirmedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ResendReportConfirmedMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ResendReportConfirmedMessage

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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ActivateApplicationSystemMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ActivateApplicationSystemConfirmedMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LogoutMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LogoutConfirmedMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ConfirmConnectionMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ConnectionConfirmedMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ConnectionConfirmedMessage

/-- Trade Session Status Request Message: 5 bytes -/
structure TradeSessionStatusRequestMessage where
  statusCodeUint81 : BitVec 8
  tradeReqId : BitVec 16
  flowGroupNo : BitVec 8
  subscriptionRequestType : BitVec 8
  deriving DecidableEq, Repr

namespace TradeSessionStatusRequestMessage

def encode (message : TradeSessionStatusRequestMessage) : List UInt8 :=
  encodeUInt 1 message.statusCodeUint81
    ++ (encodeUInt 2 message.tradeReqId
    ++ (encodeUInt 1 message.flowGroupNo
    ++ (encodeUInt 1 message.subscriptionRequestType)))

def decode (bytes : List UInt8) : Option (TradeSessionStatusRequestMessage × List UInt8) := do
  let (statusCodeUint81, bytes) ← decodeUInt 1 bytes
  let (tradeReqId, bytes) ← decodeUInt 2 bytes
  let (flowGroupNo, bytes) ← decodeUInt 1 bytes
  let (subscriptionRequestType, bytes) ← decodeUInt 1 bytes
  pure ({ statusCodeUint81, tradeReqId, flowGroupNo, subscriptionRequestType }, bytes)

@[simp] theorem encode_length (message : TradeSessionStatusRequestMessage) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : TradeSessionStatusRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeSessionStatusRequestMessage) (rest : List UInt8) :
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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : TradeSessionStatusRequestMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end TradeSessionStatusRequestMessage

/-- Trade Session Status Report Message: 5 bytes -/
structure TradeSessionStatusReportMessage where
  statusCodeUint81 : BitVec 8
  tradeReqId : BitVec 16
  flowGroupNo : BitVec 8
  tradeStatus : BitVec 8
  deriving DecidableEq, Repr

namespace TradeSessionStatusReportMessage

def encode (message : TradeSessionStatusReportMessage) : List UInt8 :=
  encodeUInt 1 message.statusCodeUint81
    ++ (encodeUInt 2 message.tradeReqId
    ++ (encodeUInt 1 message.flowGroupNo
    ++ (encodeUInt 1 message.tradeStatus)))

def decode (bytes : List UInt8) : Option (TradeSessionStatusReportMessage × List UInt8) := do
  let (statusCodeUint81, bytes) ← decodeUInt 1 bytes
  let (tradeReqId, bytes) ← decodeUInt 2 bytes
  let (flowGroupNo, bytes) ← decodeUInt 1 bytes
  let (tradeStatus, bytes) ← decodeUInt 1 bytes
  pure ({ statusCodeUint81, tradeReqId, flowGroupNo, tradeStatus }, bytes)

@[simp] theorem encode_length (message : TradeSessionStatusReportMessage) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : TradeSessionStatusReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeSessionStatusReportMessage) (rest : List UInt8) :
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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : TradeSessionStatusReportMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end TradeSessionStatusReportMessage

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

/-- Order Input Message -/
structure OrderInputMessage where
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
  orderSource : OrderSource
  infoSource : Alpha 3
  deriving DecidableEq, Repr

namespace OrderInputMessage

def encode (message : OrderInputMessage) : List UInt8 :=
  ExecType.encode message.execType
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
    ++ (OrderSource.encode message.orderSource
    ++ (Alpha.encode message.infoSource)))))))))))))))))

def decode (bytes : List UInt8) : Option (OrderInputMessage × List UInt8) := do
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
  let (orderSource, bytes) ← OrderSource.decode bytes
  let (infoSource, bytes) ← Alpha.decode 3 bytes
  pure ({ execType, cmId, fcmId, orderNo, ordId, userDefine, symSymbolX, price, qty, investorAcno, investorFlag, side, ordType, timeInForce, positionEffect, orderSource, infoSource }, bytes)

theorem encode_length_pos (message : OrderInputMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [ExecType.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrderInputMessage) : (encode message).length ≤ 62 := by
  unfold encode
  cases message.symSymbolX with
  | symbolNum inner =>
    simp only [SymSymbolX.encode, List.length_append, ← Nat.add_assoc, ExecType.encode_length, encodeUInt_length, Alpha.encode_length, PositionEffect.encode_length, OrderSource.encode_length, SymbolNum.encode_length]
    omega
  | symbolText inner =>
    simp only [SymSymbolX.encode, List.length_append, ← Nat.add_assoc, ExecType.encode_length, encodeUInt_length, Alpha.encode_length, PositionEffect.encode_length, OrderSource.encode_length, SymbolText.encode_length]
    omega

@[simp] theorem decode_encode (message : OrderInputMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, OrderSource.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : OrderInputMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end OrderInputMessage

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

/-- Order Input Long Format Message -/
structure OrderInputLongFormatMessage where
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
  orderSource : OrderSource
  infoSource : Alpha 3
  deriving DecidableEq, Repr

namespace OrderInputLongFormatMessage

def encode (message : OrderInputLongFormatMessage) : List UInt8 :=
  ExecType.encode message.execType
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
    ++ (OrderSource.encode message.orderSource
    ++ (Alpha.encode message.infoSource)))))))))))))))))

def decode (bytes : List UInt8) : Option (OrderInputLongFormatMessage × List UInt8) := do
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
  let (orderSource, bytes) ← OrderSource.decode bytes
  let (infoSource, bytes) ← Alpha.decode 3 bytes
  pure ({ execType, cmId, fcmId, orderNo, ordId, userDefine, symLongSymbolX, price, qty, investorAcno, investorFlag, side, ordType, timeInForce, positionEffect, orderSource, infoSource }, bytes)

theorem encode_length_pos (message : OrderInputLongFormatMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [ExecType.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrderInputLongFormatMessage) : (encode message).length ≤ 82 := by
  unfold encode
  cases message.symLongSymbolX with
  | longSymbolNum inner =>
    simp only [SymLongSymbolX.encode, List.length_append, ← Nat.add_assoc, ExecType.encode_length, encodeUInt_length, Alpha.encode_length, PositionEffect.encode_length, OrderSource.encode_length, LongSymbolNum.encode_length]
    omega
  | longSymbolText inner =>
    simp only [SymLongSymbolX.encode, List.length_append, ← Nat.add_assoc, ExecType.encode_length, encodeUInt_length, Alpha.encode_length, PositionEffect.encode_length, OrderSource.encode_length, LongSymbolText.encode_length]
    omega

@[simp] theorem decode_encode (message : OrderInputLongFormatMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, OrderSource.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : OrderInputLongFormatMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end OrderInputLongFormatMessage

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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : OrderStatusReportMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end OrderStatusReportMessage

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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : OrderStatusReportLongFormatMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end OrderStatusReportLongFormatMessage

/-- Error Report Message: 26 bytes -/
structure ErrorReportMessage where
  statusCodeUint81 : BitVec 8
  execType : ExecType
  fcmId : BitVec 16
  orderNo : Alpha 5
  ordId : BitVec 32
  userDefine : Alpha 8
  rptSeq : BitVec 32
  side : BitVec 8
  deriving DecidableEq, Repr

namespace ErrorReportMessage

def encode (message : ErrorReportMessage) : List UInt8 :=
  encodeUInt 1 message.statusCodeUint81
    ++ (ExecType.encode message.execType
    ++ (encodeUInt 2 message.fcmId
    ++ (Alpha.encode message.orderNo
    ++ (encodeUInt 4 message.ordId
    ++ (Alpha.encode message.userDefine
    ++ (encodeUInt 4 message.rptSeq
    ++ (encodeUInt 1 message.side)))))))

def decode (bytes : List UInt8) : Option (ErrorReportMessage × List UInt8) := do
  let (statusCodeUint81, bytes) ← decodeUInt 1 bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (fcmId, bytes) ← decodeUInt 2 bytes
  let (orderNo, bytes) ← Alpha.decode 5 bytes
  let (ordId, bytes) ← decodeUInt 4 bytes
  let (userDefine, bytes) ← Alpha.decode 8 bytes
  let (rptSeq, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  pure ({ statusCodeUint81, execType, fcmId, orderNo, ordId, userDefine, rptSeq, side }, bytes)

@[simp] theorem encode_length (message : ErrorReportMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, ExecType.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : ErrorReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ErrorReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ErrorReportMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ErrorReportMessage

/-- Price Inquiry Input Message -/
structure PriceInquiryInputMessage where
  orderNo : Alpha 5
  ordId : BitVec 32
  fcmId : BitVec 16
  symSymbolX : SymSymbolX
  orderSource : OrderSource
  infoSource : Alpha 3
  deriving DecidableEq, Repr

namespace PriceInquiryInputMessage

def encode (message : PriceInquiryInputMessage) : List UInt8 :=
  Alpha.encode message.orderNo
    ++ (encodeUInt 4 message.ordId
    ++ (encodeUInt 2 message.fcmId
    ++ (encodeUInt 1 (SymSymbolX.tag message.symSymbolX)
    ++ (SymSymbolX.encode message.symSymbolX
    ++ (OrderSource.encode message.orderSource
    ++ (Alpha.encode message.infoSource))))))

def decode (bytes : List UInt8) : Option (PriceInquiryInputMessage × List UInt8) := do
  let (orderNo, bytes) ← Alpha.decode 5 bytes
  let (ordId, bytes) ← decodeUInt 4 bytes
  let (fcmId, bytes) ← decodeUInt 2 bytes
  let (symbolType, bytes) ← decodeUInt 1 bytes
  let (symSymbolX, bytes) ← SymSymbolX.decode symbolType bytes
  let (orderSource, bytes) ← OrderSource.decode bytes
  let (infoSource, bytes) ← Alpha.decode 3 bytes
  pure ({ orderNo, ordId, fcmId, symSymbolX, orderSource, infoSource }, bytes)

theorem encode_length_pos (message : PriceInquiryInputMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : PriceInquiryInputMessage) : (encode message).length ≤ 36 := by
  unfold encode
  cases message.symSymbolX with
  | symbolNum inner =>
    simp only [SymSymbolX.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, OrderSource.encode_length, SymbolNum.encode_length]
    omega
  | symbolText inner =>
    simp only [SymSymbolX.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, OrderSource.encode_length, SymbolText.encode_length]
    omega

@[simp] theorem decode_encode (message : PriceInquiryInputMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, SymSymbolX.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderSource.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : PriceInquiryInputMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end PriceInquiryInputMessage

/-- Price Inquiry Input Long Format Message -/
structure PriceInquiryInputLongFormatMessage where
  orderNo : Alpha 5
  ordId : BitVec 32
  fcmId : BitVec 16
  symLongSymbolX : SymLongSymbolX
  orderSource : OrderSource
  infoSource : Alpha 3
  deriving DecidableEq, Repr

namespace PriceInquiryInputLongFormatMessage

def encode (message : PriceInquiryInputLongFormatMessage) : List UInt8 :=
  Alpha.encode message.orderNo
    ++ (encodeUInt 4 message.ordId
    ++ (encodeUInt 2 message.fcmId
    ++ (encodeUInt 1 (SymLongSymbolX.tag message.symLongSymbolX)
    ++ (SymLongSymbolX.encode message.symLongSymbolX
    ++ (OrderSource.encode message.orderSource
    ++ (Alpha.encode message.infoSource))))))

def decode (bytes : List UInt8) : Option (PriceInquiryInputLongFormatMessage × List UInt8) := do
  let (orderNo, bytes) ← Alpha.decode 5 bytes
  let (ordId, bytes) ← decodeUInt 4 bytes
  let (fcmId, bytes) ← decodeUInt 2 bytes
  let (symbolType, bytes) ← decodeUInt 1 bytes
  let (symLongSymbolX, bytes) ← SymLongSymbolX.decode symbolType bytes
  let (orderSource, bytes) ← OrderSource.decode bytes
  let (infoSource, bytes) ← Alpha.decode 3 bytes
  pure ({ orderNo, ordId, fcmId, symLongSymbolX, orderSource, infoSource }, bytes)

theorem encode_length_pos (message : PriceInquiryInputLongFormatMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : PriceInquiryInputLongFormatMessage) : (encode message).length ≤ 56 := by
  unfold encode
  cases message.symLongSymbolX with
  | longSymbolNum inner =>
    simp only [SymLongSymbolX.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, OrderSource.encode_length, LongSymbolNum.encode_length]
    omega
  | longSymbolText inner =>
    simp only [SymLongSymbolX.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, OrderSource.encode_length, LongSymbolText.encode_length]
    omega

@[simp] theorem decode_encode (message : PriceInquiryInputLongFormatMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, SymLongSymbolX.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderSource.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : PriceInquiryInputLongFormatMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end PriceInquiryInputLongFormatMessage

/-- Price Inquiry Reply Message -/
structure PriceInquiryReplyMessage where
  statusCodeUint81 : BitVec 8
  orderNo : Alpha 5
  ordId : BitVec 32
  fcmId : BitVec 16
  symSymbolX : SymSymbolX
  deriving DecidableEq, Repr

namespace PriceInquiryReplyMessage

def encode (message : PriceInquiryReplyMessage) : List UInt8 :=
  encodeUInt 1 message.statusCodeUint81
    ++ (Alpha.encode message.orderNo
    ++ (encodeUInt 4 message.ordId
    ++ (encodeUInt 2 message.fcmId
    ++ (encodeUInt 1 (SymSymbolX.tag message.symSymbolX)
    ++ (SymSymbolX.encode message.symSymbolX)))))

def decode (bytes : List UInt8) : Option (PriceInquiryReplyMessage × List UInt8) := do
  let (statusCodeUint81, bytes) ← decodeUInt 1 bytes
  let (orderNo, bytes) ← Alpha.decode 5 bytes
  let (ordId, bytes) ← decodeUInt 4 bytes
  let (fcmId, bytes) ← decodeUInt 2 bytes
  let (symbolType, bytes) ← decodeUInt 1 bytes
  let (symSymbolX, bytes) ← SymSymbolX.decode symbolType bytes
  pure ({ statusCodeUint81, orderNo, ordId, fcmId, symSymbolX }, bytes)

theorem encode_length_pos (message : PriceInquiryReplyMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : PriceInquiryReplyMessage) : (encode message).length ≤ 33 := by
  unfold encode
  cases message.symSymbolX with
  | symbolNum inner =>
    simp only [SymSymbolX.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, SymbolNum.encode_length]
    omega
  | symbolText inner =>
    simp only [SymSymbolX.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, SymbolText.encode_length]
    omega

@[simp] theorem decode_encode (message : PriceInquiryReplyMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [SymSymbolX.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : PriceInquiryReplyMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end PriceInquiryReplyMessage

/-- Price Inquiry Reply Long Format Message -/
structure PriceInquiryReplyLongFormatMessage where
  statusCodeUint81 : BitVec 8
  orderNo : Alpha 5
  ordId : BitVec 32
  fcmId : BitVec 16
  symLongSymbolX : SymLongSymbolX
  deriving DecidableEq, Repr

namespace PriceInquiryReplyLongFormatMessage

def encode (message : PriceInquiryReplyLongFormatMessage) : List UInt8 :=
  encodeUInt 1 message.statusCodeUint81
    ++ (Alpha.encode message.orderNo
    ++ (encodeUInt 4 message.ordId
    ++ (encodeUInt 2 message.fcmId
    ++ (encodeUInt 1 (SymLongSymbolX.tag message.symLongSymbolX)
    ++ (SymLongSymbolX.encode message.symLongSymbolX)))))

def decode (bytes : List UInt8) : Option (PriceInquiryReplyLongFormatMessage × List UInt8) := do
  let (statusCodeUint81, bytes) ← decodeUInt 1 bytes
  let (orderNo, bytes) ← Alpha.decode 5 bytes
  let (ordId, bytes) ← decodeUInt 4 bytes
  let (fcmId, bytes) ← decodeUInt 2 bytes
  let (symbolType, bytes) ← decodeUInt 1 bytes
  let (symLongSymbolX, bytes) ← SymLongSymbolX.decode symbolType bytes
  pure ({ statusCodeUint81, orderNo, ordId, fcmId, symLongSymbolX }, bytes)

theorem encode_length_pos (message : PriceInquiryReplyLongFormatMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : PriceInquiryReplyLongFormatMessage) : (encode message).length ≤ 53 := by
  unfold encode
  cases message.symLongSymbolX with
  | longSymbolNum inner =>
    simp only [SymLongSymbolX.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, LongSymbolNum.encode_length]
    omega
  | longSymbolText inner =>
    simp only [SymLongSymbolX.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, LongSymbolText.encode_length]
    omega

@[simp] theorem decode_encode (message : PriceInquiryReplyLongFormatMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [SymLongSymbolX.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : PriceInquiryReplyLongFormatMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end PriceInquiryReplyLongFormatMessage

/-- Quote Input Message -/
structure QuoteInputMessage where
  execType : ExecType
  cmId : BitVec 16
  fcmId : BitVec 16
  orderNo : Alpha 5
  ordId : BitVec 32
  userDefine : Alpha 8
  symSymbolX : SymSymbolX
  bidPx : BitVec 32
  offerPx : BitVec 32
  bidSize : BitVec 16
  offerSize : BitVec 16
  investorAcno : BitVec 32
  investorFlag : Alpha 1
  timeInForce : BitVec 8
  positionEffect : PositionEffect
  orderSource : OrderSource
  infoSource : Alpha 3
  deriving DecidableEq, Repr

namespace QuoteInputMessage

def encode (message : QuoteInputMessage) : List UInt8 :=
  ExecType.encode message.execType
    ++ (encodeUInt 2 message.cmId
    ++ (encodeUInt 2 message.fcmId
    ++ (Alpha.encode message.orderNo
    ++ (encodeUInt 4 message.ordId
    ++ (Alpha.encode message.userDefine
    ++ (encodeUInt 1 (SymSymbolX.tag message.symSymbolX)
    ++ (SymSymbolX.encode message.symSymbolX
    ++ (encodeUInt 4 message.bidPx
    ++ (encodeUInt 4 message.offerPx
    ++ (encodeUInt 2 message.bidSize
    ++ (encodeUInt 2 message.offerSize
    ++ (encodeUInt 4 message.investorAcno
    ++ (Alpha.encode message.investorFlag
    ++ (encodeUInt 1 message.timeInForce
    ++ (PositionEffect.encode message.positionEffect
    ++ (OrderSource.encode message.orderSource
    ++ (Alpha.encode message.infoSource)))))))))))))))))

def decode (bytes : List UInt8) : Option (QuoteInputMessage × List UInt8) := do
  let (execType, bytes) ← ExecType.decode bytes
  let (cmId, bytes) ← decodeUInt 2 bytes
  let (fcmId, bytes) ← decodeUInt 2 bytes
  let (orderNo, bytes) ← Alpha.decode 5 bytes
  let (ordId, bytes) ← decodeUInt 4 bytes
  let (userDefine, bytes) ← Alpha.decode 8 bytes
  let (symbolType, bytes) ← decodeUInt 1 bytes
  let (symSymbolX, bytes) ← SymSymbolX.decode symbolType bytes
  let (bidPx, bytes) ← decodeUInt 4 bytes
  let (offerPx, bytes) ← decodeUInt 4 bytes
  let (bidSize, bytes) ← decodeUInt 2 bytes
  let (offerSize, bytes) ← decodeUInt 2 bytes
  let (investorAcno, bytes) ← decodeUInt 4 bytes
  let (investorFlag, bytes) ← Alpha.decode 1 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (positionEffect, bytes) ← PositionEffect.decode bytes
  let (orderSource, bytes) ← OrderSource.decode bytes
  let (infoSource, bytes) ← Alpha.decode 3 bytes
  pure ({ execType, cmId, fcmId, orderNo, ordId, userDefine, symSymbolX, bidPx, offerPx, bidSize, offerSize, investorAcno, investorFlag, timeInForce, positionEffect, orderSource, infoSource }, bytes)

theorem encode_length_pos (message : QuoteInputMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [ExecType.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : QuoteInputMessage) : (encode message).length ≤ 66 := by
  unfold encode
  cases message.symSymbolX with
  | symbolNum inner =>
    simp only [SymSymbolX.encode, List.length_append, ← Nat.add_assoc, ExecType.encode_length, encodeUInt_length, Alpha.encode_length, PositionEffect.encode_length, OrderSource.encode_length, SymbolNum.encode_length]
    omega
  | symbolText inner =>
    simp only [SymSymbolX.encode, List.length_append, ← Nat.add_assoc, ExecType.encode_length, encodeUInt_length, Alpha.encode_length, PositionEffect.encode_length, OrderSource.encode_length, SymbolText.encode_length]
    omega

@[simp] theorem decode_encode (message : QuoteInputMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, PositionEffect.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderSource.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : QuoteInputMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end QuoteInputMessage

/-- Quote Input Long Format Message -/
structure QuoteInputLongFormatMessage where
  execType : ExecType
  cmId : BitVec 16
  fcmId : BitVec 16
  orderNo : Alpha 5
  ordId : BitVec 32
  userDefine : Alpha 8
  symLongSymbolX : SymLongSymbolX
  bidPx : BitVec 32
  offerPx : BitVec 32
  bidSize : BitVec 16
  offerSize : BitVec 16
  investorAcno : BitVec 32
  investorFlag : Alpha 1
  timeInForce : BitVec 8
  positionEffect : PositionEffect
  orderSource : OrderSource
  infoSource : Alpha 3
  deriving DecidableEq, Repr

namespace QuoteInputLongFormatMessage

def encode (message : QuoteInputLongFormatMessage) : List UInt8 :=
  ExecType.encode message.execType
    ++ (encodeUInt 2 message.cmId
    ++ (encodeUInt 2 message.fcmId
    ++ (Alpha.encode message.orderNo
    ++ (encodeUInt 4 message.ordId
    ++ (Alpha.encode message.userDefine
    ++ (encodeUInt 1 (SymLongSymbolX.tag message.symLongSymbolX)
    ++ (SymLongSymbolX.encode message.symLongSymbolX
    ++ (encodeUInt 4 message.bidPx
    ++ (encodeUInt 4 message.offerPx
    ++ (encodeUInt 2 message.bidSize
    ++ (encodeUInt 2 message.offerSize
    ++ (encodeUInt 4 message.investorAcno
    ++ (Alpha.encode message.investorFlag
    ++ (encodeUInt 1 message.timeInForce
    ++ (PositionEffect.encode message.positionEffect
    ++ (OrderSource.encode message.orderSource
    ++ (Alpha.encode message.infoSource)))))))))))))))))

def decode (bytes : List UInt8) : Option (QuoteInputLongFormatMessage × List UInt8) := do
  let (execType, bytes) ← ExecType.decode bytes
  let (cmId, bytes) ← decodeUInt 2 bytes
  let (fcmId, bytes) ← decodeUInt 2 bytes
  let (orderNo, bytes) ← Alpha.decode 5 bytes
  let (ordId, bytes) ← decodeUInt 4 bytes
  let (userDefine, bytes) ← Alpha.decode 8 bytes
  let (symbolType, bytes) ← decodeUInt 1 bytes
  let (symLongSymbolX, bytes) ← SymLongSymbolX.decode symbolType bytes
  let (bidPx, bytes) ← decodeUInt 4 bytes
  let (offerPx, bytes) ← decodeUInt 4 bytes
  let (bidSize, bytes) ← decodeUInt 2 bytes
  let (offerSize, bytes) ← decodeUInt 2 bytes
  let (investorAcno, bytes) ← decodeUInt 4 bytes
  let (investorFlag, bytes) ← Alpha.decode 1 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (positionEffect, bytes) ← PositionEffect.decode bytes
  let (orderSource, bytes) ← OrderSource.decode bytes
  let (infoSource, bytes) ← Alpha.decode 3 bytes
  pure ({ execType, cmId, fcmId, orderNo, ordId, userDefine, symLongSymbolX, bidPx, offerPx, bidSize, offerSize, investorAcno, investorFlag, timeInForce, positionEffect, orderSource, infoSource }, bytes)

theorem encode_length_pos (message : QuoteInputLongFormatMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [ExecType.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : QuoteInputLongFormatMessage) : (encode message).length ≤ 86 := by
  unfold encode
  cases message.symLongSymbolX with
  | longSymbolNum inner =>
    simp only [SymLongSymbolX.encode, List.length_append, ← Nat.add_assoc, ExecType.encode_length, encodeUInt_length, Alpha.encode_length, PositionEffect.encode_length, OrderSource.encode_length, LongSymbolNum.encode_length]
    omega
  | longSymbolText inner =>
    simp only [SymLongSymbolX.encode, List.length_append, ← Nat.add_assoc, ExecType.encode_length, encodeUInt_length, Alpha.encode_length, PositionEffect.encode_length, OrderSource.encode_length, LongSymbolText.encode_length]
    omega

@[simp] theorem decode_encode (message : QuoteInputLongFormatMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, PositionEffect.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderSource.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : QuoteInputLongFormatMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end QuoteInputLongFormatMessage

/-- Condensed Version Order Status Report Message: 52 bytes -/
structure CondensedVersionOrderStatusReportMessage where
  statusCodeUint81 : BitVec 8
  execType : ExecType
  fcmId : BitVec 16
  orderNo : Alpha 5
  ordId : BitVec 32
  userDefine : Alpha 8
  side : BitVec 8
  positionEffect : PositionEffect
  leavesQty : BitVec 16
  beforeQty : BitVec 16
  legPx : BitVec 32
  legQtyUint1624 : BitVec 16
  transactTimeMsgTime : TransactTimeMsgTime
  uniqId : BitVec 32
  rptSeq : BitVec 32
  protocolType : BitVec 8
  price : BitVec 32
  deriving DecidableEq, Repr

namespace CondensedVersionOrderStatusReportMessage

def encode (message : CondensedVersionOrderStatusReportMessage) : List UInt8 :=
  encodeUInt 1 message.statusCodeUint81
    ++ (ExecType.encode message.execType
    ++ (encodeUInt 2 message.fcmId
    ++ (Alpha.encode message.orderNo
    ++ (encodeUInt 4 message.ordId
    ++ (Alpha.encode message.userDefine
    ++ (encodeUInt 1 message.side
    ++ (PositionEffect.encode message.positionEffect
    ++ (encodeUInt 2 message.leavesQty
    ++ (encodeUInt 2 message.beforeQty
    ++ (encodeUInt 4 message.legPx
    ++ (encodeUInt 2 message.legQtyUint1624
    ++ (TransactTimeMsgTime.encode message.transactTimeMsgTime
    ++ (encodeUInt 4 message.uniqId
    ++ (encodeUInt 4 message.rptSeq
    ++ (encodeUInt 1 message.protocolType
    ++ (encodeUInt 4 message.price))))))))))))))))

def decode (bytes : List UInt8) : Option (CondensedVersionOrderStatusReportMessage × List UInt8) := do
  let (statusCodeUint81, bytes) ← decodeUInt 1 bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (fcmId, bytes) ← decodeUInt 2 bytes
  let (orderNo, bytes) ← Alpha.decode 5 bytes
  let (ordId, bytes) ← decodeUInt 4 bytes
  let (userDefine, bytes) ← Alpha.decode 8 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (positionEffect, bytes) ← PositionEffect.decode bytes
  let (leavesQty, bytes) ← decodeUInt 2 bytes
  let (beforeQty, bytes) ← decodeUInt 2 bytes
  let (legPx, bytes) ← decodeUInt 4 bytes
  let (legQtyUint1624, bytes) ← decodeUInt 2 bytes
  let (transactTimeMsgTime, bytes) ← TransactTimeMsgTime.decode bytes
  let (uniqId, bytes) ← decodeUInt 4 bytes
  let (rptSeq, bytes) ← decodeUInt 4 bytes
  let (protocolType, bytes) ← decodeUInt 1 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  pure ({ statusCodeUint81, execType, fcmId, orderNo, ordId, userDefine, side, positionEffect, leavesQty, beforeQty, legPx, legQtyUint1624, transactTimeMsgTime, uniqId, rptSeq, protocolType, price }, bytes)

@[simp] theorem encode_length (message : CondensedVersionOrderStatusReportMessage) : (encode message).length = 52 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, ExecType.encode_length, Alpha.encode_length, PositionEffect.encode_length, TransactTimeMsgTime.encode_length]

theorem encode_length_pos (message : CondensedVersionOrderStatusReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CondensedVersionOrderStatusReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : CondensedVersionOrderStatusReportMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end CondensedVersionOrderStatusReportMessage

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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ExecutionReportIncludingHeadOfficeAndBranchOfficesMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ExecutionReportIncludingHeadOfficeAndBranchOfficesMessage

/-- Bulletin Request Message -/
structure BulletinRequestMessage where
  fcmReqId : BitVec 32
  bulletinReqId : BitVec 32
  systemType : BitVec 8
  dataCharHdrMsgLength159 : List UInt8
  deriving DecidableEq, Repr

namespace BulletinRequestMessage

def encode (message : BulletinRequestMessage) : List UInt8 :=
  encodeUInt 4 message.fcmReqId
    ++ (encodeUInt 4 message.bulletinReqId
    ++ (encodeUInt 1 message.systemType
    ++ (encodeMany Byte.encode message.dataCharHdrMsgLength159)))

def decode (bytes : List UInt8) : Option BulletinRequestMessage := do
  let (fcmReqId, bytes) ← decodeUInt 4 bytes
  let (bulletinReqId, bytes) ← decodeUInt 4 bytes
  let (systemType, bytes) ← decodeUInt 1 bytes
  let dataCharHdrMsgLength159 ← decodeAll Byte.decode bytes.length bytes
  pure { fcmReqId, bulletinReqId, systemType, dataCharHdrMsgLength159 }

theorem encode_length_pos (message : BulletinRequestMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

theorem decode_encode (message : BulletinRequestMessage) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeAll_encodeMany Byte.encode Byte.decode Byte.decode_encode Byte.encode_length_pos message.dataCharHdrMsgLength159 _ (encodeMany_length_ge Byte.encode Byte.encode_length_pos message.dataCharHdrMsgLength159), some_bind]
  rfl

end BulletinRequestMessage

/-- Bulletin Time Msg Time: 6 bytes -/
structure BulletinTimeMsgTime where
  epochSInt324 : BitVec 32
  ms : BitVec 16
  deriving DecidableEq, Repr

namespace BulletinTimeMsgTime

def encode (message : BulletinTimeMsgTime) : List UInt8 :=
  encodeUInt 4 message.epochSInt324
    ++ (encodeUInt 2 message.ms)

def decode (bytes : List UInt8) : Option (BulletinTimeMsgTime × List UInt8) := do
  let (epochSInt324, bytes) ← decodeUInt 4 bytes
  let (ms, bytes) ← decodeUInt 2 bytes
  pure ({ epochSInt324, ms }, bytes)

@[simp] theorem encode_length (message : BulletinTimeMsgTime) : (encode message).length = 6 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : BulletinTimeMsgTime) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BulletinTimeMsgTime) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end BulletinTimeMsgTime

/-- Bulletin Report Message -/
structure BulletinReportMessage where
  statusCodeUint81 : BitVec 8
  fcmReqId : BitVec 32
  bulletinSeq : BitVec 32
  bulletinTimeMsgTime : BulletinTimeMsgTime
  systemType : BitVec 8
  dataCharHdrMsgLength1516 : List UInt8
  deriving DecidableEq, Repr

namespace BulletinReportMessage

def encode (message : BulletinReportMessage) : List UInt8 :=
  encodeUInt 1 message.statusCodeUint81
    ++ (encodeUInt 4 message.fcmReqId
    ++ (encodeUInt 4 message.bulletinSeq
    ++ (BulletinTimeMsgTime.encode message.bulletinTimeMsgTime
    ++ (encodeUInt 1 message.systemType
    ++ (encodeMany Byte.encode message.dataCharHdrMsgLength1516)))))

def decode (bytes : List UInt8) : Option BulletinReportMessage := do
  let (statusCodeUint81, bytes) ← decodeUInt 1 bytes
  let (fcmReqId, bytes) ← decodeUInt 4 bytes
  let (bulletinSeq, bytes) ← decodeUInt 4 bytes
  let (bulletinTimeMsgTime, bytes) ← BulletinTimeMsgTime.decode bytes
  let (systemType, bytes) ← decodeUInt 1 bytes
  let dataCharHdrMsgLength1516 ← decodeAll Byte.decode bytes.length bytes
  pure { statusCodeUint81, fcmReqId, bulletinSeq, bulletinTimeMsgTime, systemType, dataCharHdrMsgLength1516 }

theorem encode_length_pos (message : BulletinReportMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

theorem decode_encode (message : BulletinReportMessage) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [BulletinTimeMsgTime.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeAll_encodeMany Byte.encode Byte.decode Byte.decode_encode Byte.encode_length_pos message.dataCharHdrMsgLength1516 _ (encodeMany_length_ge Byte.encode Byte.encode_length_pos message.dataCharHdrMsgLength1516), some_bind]
  rfl

end BulletinReportMessage

/-- System Setting Message -/
structure SystemSettingMessage where
  dataCharHdrMsgLength15 : List UInt8
  deriving DecidableEq, Repr

namespace SystemSettingMessage

def encode (message : SystemSettingMessage) : List UInt8 :=
  encodeMany Byte.encode message.dataCharHdrMsgLength15

def decode (bytes : List UInt8) : Option SystemSettingMessage := do
  let dataCharHdrMsgLength15 ← decodeAll Byte.decode bytes.length bytes
  pure { dataCharHdrMsgLength15 }

theorem decode_encode (message : SystemSettingMessage) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany Byte.encode Byte.decode Byte.decode_encode Byte.encode_length_pos message.dataCharHdrMsgLength15 _ (encodeMany_length_ge Byte.encode Byte.encode_length_pos message.dataCharHdrMsgLength15), some_bind]
  rfl

end SystemSettingMessage

/-- System Notification Message -/
structure SystemNotificationMessage where
  statusCodeUint81 : BitVec 8
  dataCharHdrMsgLength151 : List UInt8
  deriving DecidableEq, Repr

namespace SystemNotificationMessage

def encode (message : SystemNotificationMessage) : List UInt8 :=
  encodeUInt 1 message.statusCodeUint81
    ++ (encodeMany Byte.encode message.dataCharHdrMsgLength151)

def decode (bytes : List UInt8) : Option SystemNotificationMessage := do
  let (statusCodeUint81, bytes) ← decodeUInt 1 bytes
  let dataCharHdrMsgLength151 ← decodeAll Byte.decode bytes.length bytes
  pure { statusCodeUint81, dataCharHdrMsgLength151 }

theorem encode_length_pos (message : SystemNotificationMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

theorem decode_encode (message : SystemNotificationMessage) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeAll_encodeMany Byte.encode Byte.decode Byte.decode_encode Byte.encode_length_pos message.dataCharHdrMsgLength151 _ (encodeMany_length_ge Byte.encode Byte.encode_length_pos message.dataCharHdrMsgLength151), some_bind]
  rfl

end SystemNotificationMessage

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

/-- Flex Order Input Single Message -/
structure FlexOrderInputSingleMessage where
  preserve : BitVec 8
  msgTimeNs : BitVec 32
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
  reserved12 : Alpha 12
  deriving DecidableEq, Repr

namespace FlexOrderInputSingleMessage

def encode (message : FlexOrderInputSingleMessage) : List UInt8 :=
  encodeUInt 1 (SymFlexProductX.tag message.symFlexProductX)
    ++ (encodeUInt 1 message.preserve
    ++ (encodeUInt 4 message.msgTimeNs
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
    ++ (Alpha.encode message.reserved12))))))))))))))))))

def decode (bytes : List UInt8) : Option (FlexOrderInputSingleMessage × List UInt8) := do
  let (msgTypeExt, bytes) ← decodeUInt 1 bytes
  let (preserve, bytes) ← decodeUInt 1 bytes
  let (msgTimeNs, bytes) ← decodeUInt 4 bytes
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
  let (reserved12, bytes) ← Alpha.decode 12 bytes
  pure ({ preserve, msgTimeNs, execType, cmId, fcmId, orderNo, ordId, userDefine, symFlexProductX, price, qty, investorAcno, investorFlag, side, ordType, timeInForce, positionEffect, reserved12 }, bytes)

theorem encode_length_pos (message : FlexOrderInputSingleMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : FlexOrderInputSingleMessage) : (encode message).length ≤ 5922 := by
  unfold encode
  cases message.symFlexProductX with
  | symbolNumX inner =>
    simp only [SymFlexProductX.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ExecType.encode_length, Alpha.encode_length, PositionEffect.encode_length, SymbolNumX.encode_length]
    omega
  | symbolTxtX inner =>
    simp only [SymFlexProductX.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ExecType.encode_length, Alpha.encode_length, PositionEffect.encode_length, SymbolTxtX.encode_length]
    omega
  | multiLegNum inner =>
    have bound_inner := MultiLegNum.encode_length_le inner
    simp only [SymFlexProductX.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ExecType.encode_length, Alpha.encode_length, PositionEffect.encode_length]
    omega
  | multiLegTxt inner =>
    have bound_inner := MultiLegTxt.encode_length_le inner
    simp only [SymFlexProductX.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ExecType.encode_length, Alpha.encode_length, PositionEffect.encode_length]
    omega

@[simp] theorem decode_encode (message : FlexOrderInputSingleMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : FlexOrderInputSingleMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end FlexOrderInputSingleMessage

/-- Flex Price Inquiry Input Message -/
structure FlexPriceInquiryInputMessage where
  preserve : BitVec 8
  msgTimeNs : BitVec 32
  orderNo : Alpha 5
  ordId : BitVec 32
  fcmId : BitVec 16
  symFlexProductX : SymFlexProductX
  reserved8 : Alpha 8
  deriving DecidableEq, Repr

namespace FlexPriceInquiryInputMessage

def encode (message : FlexPriceInquiryInputMessage) : List UInt8 :=
  encodeUInt 1 (SymFlexProductX.tag message.symFlexProductX)
    ++ (encodeUInt 1 message.preserve
    ++ (encodeUInt 4 message.msgTimeNs
    ++ (Alpha.encode message.orderNo
    ++ (encodeUInt 4 message.ordId
    ++ (encodeUInt 2 message.fcmId
    ++ (SymFlexProductX.encode message.symFlexProductX
    ++ (Alpha.encode message.reserved8)))))))

def decode (bytes : List UInt8) : Option (FlexPriceInquiryInputMessage × List UInt8) := do
  let (msgTypeExt, bytes) ← decodeUInt 1 bytes
  let (preserve, bytes) ← decodeUInt 1 bytes
  let (msgTimeNs, bytes) ← decodeUInt 4 bytes
  let (orderNo, bytes) ← Alpha.decode 5 bytes
  let (ordId, bytes) ← decodeUInt 4 bytes
  let (fcmId, bytes) ← decodeUInt 2 bytes
  let (symFlexProductX, bytes) ← SymFlexProductX.decode msgTypeExt bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  pure ({ preserve, msgTimeNs, orderNo, ordId, fcmId, symFlexProductX, reserved8 }, bytes)

theorem encode_length_pos (message : FlexPriceInquiryInputMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : FlexPriceInquiryInputMessage) : (encode message).length ≤ 5892 := by
  unfold encode
  cases message.symFlexProductX with
  | symbolNumX inner =>
    simp only [SymFlexProductX.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, SymbolNumX.encode_length]
    omega
  | symbolTxtX inner =>
    simp only [SymFlexProductX.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, SymbolTxtX.encode_length]
    omega
  | multiLegNum inner =>
    have bound_inner := MultiLegNum.encode_length_le inner
    simp only [SymFlexProductX.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
    omega
  | multiLegTxt inner =>
    have bound_inner := MultiLegTxt.encode_length_le inner
    simp only [SymFlexProductX.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
    omega

@[simp] theorem decode_encode (message : FlexPriceInquiryInputMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, SymFlexProductX.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : FlexPriceInquiryInputMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end FlexPriceInquiryInputMessage

/-- Flex Quote Input Message -/
structure FlexQuoteInputMessage where
  preserve : BitVec 8
  msgTimeNs : BitVec 32
  execType : ExecType
  cmId : BitVec 16
  fcmId : BitVec 16
  orderNo : Alpha 5
  ordId : BitVec 32
  userDefine : Alpha 8
  symFlexProductX : SymFlexProductX
  bidPx : BitVec 32
  offerPx : BitVec 32
  bidSize : BitVec 16
  offerSize : BitVec 16
  investorAcno : BitVec 32
  investorFlag : Alpha 1
  timeInForce : BitVec 8
  positionEffect : PositionEffect
  reserved12 : Alpha 12
  deriving DecidableEq, Repr

namespace FlexQuoteInputMessage

def encode (message : FlexQuoteInputMessage) : List UInt8 :=
  encodeUInt 1 (SymFlexProductX.tag message.symFlexProductX)
    ++ (encodeUInt 1 message.preserve
    ++ (encodeUInt 4 message.msgTimeNs
    ++ (ExecType.encode message.execType
    ++ (encodeUInt 2 message.cmId
    ++ (encodeUInt 2 message.fcmId
    ++ (Alpha.encode message.orderNo
    ++ (encodeUInt 4 message.ordId
    ++ (Alpha.encode message.userDefine
    ++ (SymFlexProductX.encode message.symFlexProductX
    ++ (encodeUInt 4 message.bidPx
    ++ (encodeUInt 4 message.offerPx
    ++ (encodeUInt 2 message.bidSize
    ++ (encodeUInt 2 message.offerSize
    ++ (encodeUInt 4 message.investorAcno
    ++ (Alpha.encode message.investorFlag
    ++ (encodeUInt 1 message.timeInForce
    ++ (PositionEffect.encode message.positionEffect
    ++ (Alpha.encode message.reserved12))))))))))))))))))

def decode (bytes : List UInt8) : Option (FlexQuoteInputMessage × List UInt8) := do
  let (msgTypeExt, bytes) ← decodeUInt 1 bytes
  let (preserve, bytes) ← decodeUInt 1 bytes
  let (msgTimeNs, bytes) ← decodeUInt 4 bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (cmId, bytes) ← decodeUInt 2 bytes
  let (fcmId, bytes) ← decodeUInt 2 bytes
  let (orderNo, bytes) ← Alpha.decode 5 bytes
  let (ordId, bytes) ← decodeUInt 4 bytes
  let (userDefine, bytes) ← Alpha.decode 8 bytes
  let (symFlexProductX, bytes) ← SymFlexProductX.decode msgTypeExt bytes
  let (bidPx, bytes) ← decodeUInt 4 bytes
  let (offerPx, bytes) ← decodeUInt 4 bytes
  let (bidSize, bytes) ← decodeUInt 2 bytes
  let (offerSize, bytes) ← decodeUInt 2 bytes
  let (investorAcno, bytes) ← decodeUInt 4 bytes
  let (investorFlag, bytes) ← Alpha.decode 1 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (positionEffect, bytes) ← PositionEffect.decode bytes
  let (reserved12, bytes) ← Alpha.decode 12 bytes
  pure ({ preserve, msgTimeNs, execType, cmId, fcmId, orderNo, ordId, userDefine, symFlexProductX, bidPx, offerPx, bidSize, offerSize, investorAcno, investorFlag, timeInForce, positionEffect, reserved12 }, bytes)

theorem encode_length_pos (message : FlexQuoteInputMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : FlexQuoteInputMessage) : (encode message).length ≤ 5926 := by
  unfold encode
  cases message.symFlexProductX with
  | symbolNumX inner =>
    simp only [SymFlexProductX.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ExecType.encode_length, Alpha.encode_length, PositionEffect.encode_length, SymbolNumX.encode_length]
    omega
  | symbolTxtX inner =>
    simp only [SymFlexProductX.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ExecType.encode_length, Alpha.encode_length, PositionEffect.encode_length, SymbolTxtX.encode_length]
    omega
  | multiLegNum inner =>
    have bound_inner := MultiLegNum.encode_length_le inner
    simp only [SymFlexProductX.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ExecType.encode_length, Alpha.encode_length, PositionEffect.encode_length]
    omega
  | multiLegTxt inner =>
    have bound_inner := MultiLegTxt.encode_length_le inner
    simp only [SymFlexProductX.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ExecType.encode_length, Alpha.encode_length, PositionEffect.encode_length]
    omega

@[simp] theorem decode_encode (message : FlexQuoteInputMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, PositionEffect.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : FlexQuoteInputMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end FlexQuoteInputMessage

/-- Request For Supplementary Flex Group Report Message: 11 bytes -/
structure RequestForSupplementaryFlexGroupReportMessage where
  subHdr : SubHdr
  partId : BitVec 8
  requestStartSeq : BitVec 32
  deriving DecidableEq, Repr

namespace RequestForSupplementaryFlexGroupReportMessage

def encode (message : RequestForSupplementaryFlexGroupReportMessage) : List UInt8 :=
  SubHdr.encode message.subHdr
    ++ (encodeUInt 1 message.partId
    ++ (encodeUInt 4 message.requestStartSeq))

def decode (bytes : List UInt8) : Option (RequestForSupplementaryFlexGroupReportMessage × List UInt8) := do
  let (subHdr, bytes) ← SubHdr.decode bytes
  let (partId, bytes) ← decodeUInt 1 bytes
  let (requestStartSeq, bytes) ← decodeUInt 4 bytes
  pure ({ subHdr, partId, requestStartSeq }, bytes)

@[simp] theorem encode_length (message : RequestForSupplementaryFlexGroupReportMessage) : (encode message).length = 11 := by
  unfold encode
  simp only [List.length_append, SubHdr.encode_length, encodeUInt_length]

theorem encode_length_pos (message : RequestForSupplementaryFlexGroupReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RequestForSupplementaryFlexGroupReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, SubHdr.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : RequestForSupplementaryFlexGroupReportMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end RequestForSupplementaryFlexGroupReportMessage

/-- Temporary Suspension Of Supplementary Flex Group Report Message: 7 bytes -/
structure TemporarySuspensionOfSupplementaryFlexGroupReportMessage where
  subHdr : SubHdr
  partId : BitVec 8
  deriving DecidableEq, Repr

namespace TemporarySuspensionOfSupplementaryFlexGroupReportMessage

def encode (message : TemporarySuspensionOfSupplementaryFlexGroupReportMessage) : List UInt8 :=
  SubHdr.encode message.subHdr
    ++ (encodeUInt 1 message.partId)

def decode (bytes : List UInt8) : Option (TemporarySuspensionOfSupplementaryFlexGroupReportMessage × List UInt8) := do
  let (subHdr, bytes) ← SubHdr.decode bytes
  let (partId, bytes) ← decodeUInt 1 bytes
  pure ({ subHdr, partId }, bytes)

@[simp] theorem encode_length (message : TemporarySuspensionOfSupplementaryFlexGroupReportMessage) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, SubHdr.encode_length, encodeUInt_length]

theorem encode_length_pos (message : TemporarySuspensionOfSupplementaryFlexGroupReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TemporarySuspensionOfSupplementaryFlexGroupReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, SubHdr.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : TemporarySuspensionOfSupplementaryFlexGroupReportMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end TemporarySuspensionOfSupplementaryFlexGroupReportMessage

/-- Flex Product Definition Request Message: 56 bytes -/
structure FlexProductDefinitionRequestMessage where
  subHdr : SubHdr
  securityRequestType : SecurityRequestType
  securityReqId : BitVec 32
  type : Type_
  fcmId : BitVec 16
  investorAcno : BitVec 32
  applicationType : ApplicationType
  rootSymbol : Alpha 3
  expiryType : ExpiryType
  contractDate : Alpha 8
  strikePrice : BitVec 32
  callPutCode : CallPutCode
  reserved20 : Alpha 20
  deriving DecidableEq, Repr

namespace FlexProductDefinitionRequestMessage

def encode (message : FlexProductDefinitionRequestMessage) : List UInt8 :=
  SubHdr.encode message.subHdr
    ++ (SecurityRequestType.encode message.securityRequestType
    ++ (encodeUInt 4 message.securityReqId
    ++ (Type_.encode message.type
    ++ (encodeUInt 2 message.fcmId
    ++ (encodeUInt 4 message.investorAcno
    ++ (ApplicationType.encode message.applicationType
    ++ (Alpha.encode message.rootSymbol
    ++ (ExpiryType.encode message.expiryType
    ++ (Alpha.encode message.contractDate
    ++ (encodeUInt 4 message.strikePrice
    ++ (CallPutCode.encode message.callPutCode
    ++ (Alpha.encode message.reserved20))))))))))))

def decode (bytes : List UInt8) : Option (FlexProductDefinitionRequestMessage × List UInt8) := do
  let (subHdr, bytes) ← SubHdr.decode bytes
  let (securityRequestType, bytes) ← SecurityRequestType.decode bytes
  let (securityReqId, bytes) ← decodeUInt 4 bytes
  let (type, bytes) ← Type_.decode bytes
  let (fcmId, bytes) ← decodeUInt 2 bytes
  let (investorAcno, bytes) ← decodeUInt 4 bytes
  let (applicationType, bytes) ← ApplicationType.decode bytes
  let (rootSymbol, bytes) ← Alpha.decode 3 bytes
  let (expiryType, bytes) ← ExpiryType.decode bytes
  let (contractDate, bytes) ← Alpha.decode 8 bytes
  let (strikePrice, bytes) ← decodeUInt 4 bytes
  let (callPutCode, bytes) ← CallPutCode.decode bytes
  let (reserved20, bytes) ← Alpha.decode 20 bytes
  pure ({ subHdr, securityRequestType, securityReqId, type, fcmId, investorAcno, applicationType, rootSymbol, expiryType, contractDate, strikePrice, callPutCode, reserved20 }, bytes)

@[simp] theorem encode_length (message : FlexProductDefinitionRequestMessage) : (encode message).length = 56 := by
  unfold encode
  simp only [List.length_append, SubHdr.encode_length, SecurityRequestType.encode_length, encodeUInt_length, Type_.encode_length, ApplicationType.encode_length, Alpha.encode_length, ExpiryType.encode_length, CallPutCode.encode_length]

theorem encode_length_pos (message : FlexProductDefinitionRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FlexProductDefinitionRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, SubHdr.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityRequestType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Type_.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ApplicationType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExpiryType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, CallPutCode.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : FlexProductDefinitionRequestMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end FlexProductDefinitionRequestMessage

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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : FlexOrderStatusReportMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end FlexOrderStatusReportMessage

/-- Flex Error Report Message: 47 bytes -/
structure FlexErrorReportMessage where
  subHdr : SubHdr
  partId : BitVec 8
  oriMessageType : BitVec 8
  statusCodeUint162 : BitVec 16
  execType : ExecType
  fcmId : BitVec 16
  orderNo : Alpha 5
  ordId : BitVec 32
  userDefine : Alpha 8
  rptSeq : BitVec 32
  side : BitVec 8
  reserved12 : Alpha 12
  deriving DecidableEq, Repr

namespace FlexErrorReportMessage

def encode (message : FlexErrorReportMessage) : List UInt8 :=
  SubHdr.encode message.subHdr
    ++ (encodeUInt 1 message.partId
    ++ (encodeUInt 1 message.oriMessageType
    ++ (encodeUInt 2 message.statusCodeUint162
    ++ (ExecType.encode message.execType
    ++ (encodeUInt 2 message.fcmId
    ++ (Alpha.encode message.orderNo
    ++ (encodeUInt 4 message.ordId
    ++ (Alpha.encode message.userDefine
    ++ (encodeUInt 4 message.rptSeq
    ++ (encodeUInt 1 message.side
    ++ (Alpha.encode message.reserved12)))))))))))

def decode (bytes : List UInt8) : Option (FlexErrorReportMessage × List UInt8) := do
  let (subHdr, bytes) ← SubHdr.decode bytes
  let (partId, bytes) ← decodeUInt 1 bytes
  let (oriMessageType, bytes) ← decodeUInt 1 bytes
  let (statusCodeUint162, bytes) ← decodeUInt 2 bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (fcmId, bytes) ← decodeUInt 2 bytes
  let (orderNo, bytes) ← Alpha.decode 5 bytes
  let (ordId, bytes) ← decodeUInt 4 bytes
  let (userDefine, bytes) ← Alpha.decode 8 bytes
  let (rptSeq, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (reserved12, bytes) ← Alpha.decode 12 bytes
  pure ({ subHdr, partId, oriMessageType, statusCodeUint162, execType, fcmId, orderNo, ordId, userDefine, rptSeq, side, reserved12 }, bytes)

@[simp] theorem encode_length (message : FlexErrorReportMessage) : (encode message).length = 47 := by
  unfold encode
  simp only [List.length_append, SubHdr.encode_length, encodeUInt_length, ExecType.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : FlexErrorReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FlexErrorReportMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : FlexErrorReportMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end FlexErrorReportMessage

/-- Flex Price Inquiry Reply Message -/
structure FlexPriceInquiryReplyMessage where
  preserve : BitVec 8
  msgTimeNs : BitVec 32
  partId : BitVec 8
  statusCodeUint162 : BitVec 16
  orderNo : Alpha 5
  ordId : BitVec 32
  fcmId : BitVec 16
  symFlexProductX : SymFlexProductX
  reserved8 : Alpha 8
  deriving DecidableEq, Repr

namespace FlexPriceInquiryReplyMessage

def encode (message : FlexPriceInquiryReplyMessage) : List UInt8 :=
  encodeUInt 1 (SymFlexProductX.tag message.symFlexProductX)
    ++ (encodeUInt 1 message.preserve
    ++ (encodeUInt 4 message.msgTimeNs
    ++ (encodeUInt 1 message.partId
    ++ (encodeUInt 2 message.statusCodeUint162
    ++ (Alpha.encode message.orderNo
    ++ (encodeUInt 4 message.ordId
    ++ (encodeUInt 2 message.fcmId
    ++ (SymFlexProductX.encode message.symFlexProductX
    ++ (Alpha.encode message.reserved8)))))))))

def decode (bytes : List UInt8) : Option (FlexPriceInquiryReplyMessage × List UInt8) := do
  let (msgTypeExt, bytes) ← decodeUInt 1 bytes
  let (preserve, bytes) ← decodeUInt 1 bytes
  let (msgTimeNs, bytes) ← decodeUInt 4 bytes
  let (partId, bytes) ← decodeUInt 1 bytes
  let (statusCodeUint162, bytes) ← decodeUInt 2 bytes
  let (orderNo, bytes) ← Alpha.decode 5 bytes
  let (ordId, bytes) ← decodeUInt 4 bytes
  let (fcmId, bytes) ← decodeUInt 2 bytes
  let (symFlexProductX, bytes) ← SymFlexProductX.decode msgTypeExt bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  pure ({ preserve, msgTimeNs, partId, statusCodeUint162, orderNo, ordId, fcmId, symFlexProductX, reserved8 }, bytes)

theorem encode_length_pos (message : FlexPriceInquiryReplyMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : FlexPriceInquiryReplyMessage) : (encode message).length ≤ 5895 := by
  unfold encode
  cases message.symFlexProductX with
  | symbolNumX inner =>
    simp only [SymFlexProductX.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, SymbolNumX.encode_length]
    omega
  | symbolTxtX inner =>
    simp only [SymFlexProductX.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, SymbolTxtX.encode_length]
    omega
  | multiLegNum inner =>
    have bound_inner := MultiLegNum.encode_length_le inner
    simp only [SymFlexProductX.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
    omega
  | multiLegTxt inner =>
    have bound_inner := MultiLegTxt.encode_length_le inner
    simp only [SymFlexProductX.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
    omega

@[simp] theorem decode_encode (message : FlexPriceInquiryReplyMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, SymFlexProductX.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : FlexPriceInquiryReplyMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end FlexPriceInquiryReplyMessage

/-- Send Flex Group Report Resend Message -/
structure SendFlexGroupReportResendMessage where
  subHdr : SubHdr
  statusCodeUint162 : BitVec 16
  partId : BitVec 8
  isEof : BitVec 8
  fileSize : BitVec 32
  dataUint8HdrMsgLength1514 : List UInt8
  deriving DecidableEq, Repr

namespace SendFlexGroupReportResendMessage

def encode (message : SendFlexGroupReportResendMessage) : List UInt8 :=
  SubHdr.encode message.subHdr
    ++ (encodeUInt 2 message.statusCodeUint162
    ++ (encodeUInt 1 message.partId
    ++ (encodeUInt 1 message.isEof
    ++ (encodeUInt 4 message.fileSize
    ++ (encodeMany Byte.encode message.dataUint8HdrMsgLength1514)))))

def decode (bytes : List UInt8) : Option SendFlexGroupReportResendMessage := do
  let (subHdr, bytes) ← SubHdr.decode bytes
  let (statusCodeUint162, bytes) ← decodeUInt 2 bytes
  let (partId, bytes) ← decodeUInt 1 bytes
  let (isEof, bytes) ← decodeUInt 1 bytes
  let (fileSize, bytes) ← decodeUInt 4 bytes
  let dataUint8HdrMsgLength1514 ← decodeAll Byte.decode bytes.length bytes
  pure { subHdr, statusCodeUint162, partId, isEof, fileSize, dataUint8HdrMsgLength1514 }

theorem encode_length_pos (message : SendFlexGroupReportResendMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [SubHdr.encode_length, List.length_append, ← Nat.add_assoc]
  omega

theorem decode_encode (message : SendFlexGroupReportResendMessage) : decode (encode message) = some message := by
  unfold decode encode
  rw [SubHdr.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeAll_encodeMany Byte.encode Byte.decode Byte.decode_encode Byte.encode_length_pos message.dataUint8HdrMsgLength1514 _ (encodeMany_length_ge Byte.encode Byte.encode_length_pos message.dataUint8HdrMsgLength1514), some_bind]
  rfl

end SendFlexGroupReportResendMessage

/-- Flex Product Definition Message: 13 bytes -/
structure FlexProductDefinitionMessage where
  subHdr : SubHdr
  securityRequestType : SecurityRequestType
  securityReqId : BitVec 32
  statusCodeUint162 : BitVec 16
  deriving DecidableEq, Repr

namespace FlexProductDefinitionMessage

def encode (message : FlexProductDefinitionMessage) : List UInt8 :=
  SubHdr.encode message.subHdr
    ++ (SecurityRequestType.encode message.securityRequestType
    ++ (encodeUInt 4 message.securityReqId
    ++ (encodeUInt 2 message.statusCodeUint162)))

def decode (bytes : List UInt8) : Option (FlexProductDefinitionMessage × List UInt8) := do
  let (subHdr, bytes) ← SubHdr.decode bytes
  let (securityRequestType, bytes) ← SecurityRequestType.decode bytes
  let (securityReqId, bytes) ← decodeUInt 4 bytes
  let (statusCodeUint162, bytes) ← decodeUInt 2 bytes
  pure ({ subHdr, securityRequestType, securityReqId, statusCodeUint162 }, bytes)

@[simp] theorem encode_length (message : FlexProductDefinitionMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, SubHdr.encode_length, SecurityRequestType.encode_length, encodeUInt_length]

theorem encode_length_pos (message : FlexProductDefinitionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FlexProductDefinitionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, SubHdr.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityRequestType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : FlexProductDefinitionMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end FlexProductDefinitionMessage

/-- Flex Bulletin Request Message -/
structure FlexBulletinRequestMessage where
  subHdr : SubHdr
  fcmReqId : BitVec 32
  bulletinReqId : BitVec 32
  systemType : BitVec 8
  dataCharHdrMsgLength1515 : List UInt8
  deriving DecidableEq, Repr

namespace FlexBulletinRequestMessage

def encode (message : FlexBulletinRequestMessage) : List UInt8 :=
  SubHdr.encode message.subHdr
    ++ (encodeUInt 4 message.fcmReqId
    ++ (encodeUInt 4 message.bulletinReqId
    ++ (encodeUInt 1 message.systemType
    ++ (encodeMany Byte.encode message.dataCharHdrMsgLength1515))))

def decode (bytes : List UInt8) : Option FlexBulletinRequestMessage := do
  let (subHdr, bytes) ← SubHdr.decode bytes
  let (fcmReqId, bytes) ← decodeUInt 4 bytes
  let (bulletinReqId, bytes) ← decodeUInt 4 bytes
  let (systemType, bytes) ← decodeUInt 1 bytes
  let dataCharHdrMsgLength1515 ← decodeAll Byte.decode bytes.length bytes
  pure { subHdr, fcmReqId, bulletinReqId, systemType, dataCharHdrMsgLength1515 }

theorem encode_length_pos (message : FlexBulletinRequestMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [SubHdr.encode_length, List.length_append, ← Nat.add_assoc]
  omega

theorem decode_encode (message : FlexBulletinRequestMessage) : decode (encode message) = some message := by
  unfold decode encode
  rw [SubHdr.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeAll_encodeMany Byte.encode Byte.decode Byte.decode_encode Byte.encode_length_pos message.dataCharHdrMsgLength1515 _ (encodeMany_length_ge Byte.encode Byte.encode_length_pos message.dataCharHdrMsgLength1515), some_bind]
  rfl

end FlexBulletinRequestMessage

/-- Bulletin Time Msg Time X: 8 bytes -/
structure BulletinTimeMsgTimeX where
  epochSUint324 : BitVec 32
  nanosecond : BitVec 32
  deriving DecidableEq, Repr

namespace BulletinTimeMsgTimeX

def encode (message : BulletinTimeMsgTimeX) : List UInt8 :=
  encodeUInt 4 message.epochSUint324
    ++ (encodeUInt 4 message.nanosecond)

def decode (bytes : List UInt8) : Option (BulletinTimeMsgTimeX × List UInt8) := do
  let (epochSUint324, bytes) ← decodeUInt 4 bytes
  let (nanosecond, bytes) ← decodeUInt 4 bytes
  pure ({ epochSUint324, nanosecond }, bytes)

@[simp] theorem encode_length (message : BulletinTimeMsgTimeX) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : BulletinTimeMsgTimeX) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BulletinTimeMsgTimeX) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end BulletinTimeMsgTimeX

/-- Flex Bulletin Report Message -/
structure FlexBulletinReportMessage where
  subHdr : SubHdr
  statusCodeUint162 : BitVec 16
  fcmReqId : BitVec 32
  bulletinSeq : BitVec 32
  bulletinTimeMsgTimeX : BulletinTimeMsgTimeX
  systemType : BitVec 8
  dataCharHdrMsgLength1525 : List UInt8
  deriving DecidableEq, Repr

namespace FlexBulletinReportMessage

def encode (message : FlexBulletinReportMessage) : List UInt8 :=
  SubHdr.encode message.subHdr
    ++ (encodeUInt 2 message.statusCodeUint162
    ++ (encodeUInt 4 message.fcmReqId
    ++ (encodeUInt 4 message.bulletinSeq
    ++ (BulletinTimeMsgTimeX.encode message.bulletinTimeMsgTimeX
    ++ (encodeUInt 1 message.systemType
    ++ (encodeMany Byte.encode message.dataCharHdrMsgLength1525))))))

def decode (bytes : List UInt8) : Option FlexBulletinReportMessage := do
  let (subHdr, bytes) ← SubHdr.decode bytes
  let (statusCodeUint162, bytes) ← decodeUInt 2 bytes
  let (fcmReqId, bytes) ← decodeUInt 4 bytes
  let (bulletinSeq, bytes) ← decodeUInt 4 bytes
  let (bulletinTimeMsgTimeX, bytes) ← BulletinTimeMsgTimeX.decode bytes
  let (systemType, bytes) ← decodeUInt 1 bytes
  let dataCharHdrMsgLength1525 ← decodeAll Byte.decode bytes.length bytes
  pure { subHdr, statusCodeUint162, fcmReqId, bulletinSeq, bulletinTimeMsgTimeX, systemType, dataCharHdrMsgLength1525 }

theorem encode_length_pos (message : FlexBulletinReportMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [SubHdr.encode_length, List.length_append, ← Nat.add_assoc]
  omega

theorem decode_encode (message : FlexBulletinReportMessage) : decode (encode message) = some message := by
  unfold decode encode
  rw [SubHdr.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [BulletinTimeMsgTimeX.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeAll_encodeMany Byte.encode Byte.decode Byte.decode_encode Byte.encode_length_pos message.dataCharHdrMsgLength1525 _ (encodeMany_length_ge Byte.encode Byte.encode_length_pos message.dataCharHdrMsgLength1525), some_bind]
  rfl

end FlexBulletinReportMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | wakeUpCallMessage (message : WakeUpCallMessage) -- 10
  | wakeUpCallConfirmedMessage (message : WakeUpCallConfirmedMessage) -- 20
  | logonNoticeMessage (message : LogonNoticeMessage) -- 30
  | finalSequentialNumberNotificationForGroupMessage (message : FinalSequentialNumberNotificationForGroupMessage) -- 230
  | requestLogonMessage (message : RequestLogonMessage) -- 40
  | resendReportMessage (message : ResendReportMessage) -- 41
  | resendReportConfirmedMessage (message : ResendReportConfirmedMessage) -- 42
  | activateApplicationSystemMessage (message : ActivateApplicationSystemMessage) -- 50
  | activateApplicationSystemConfirmedMessage (message : ActivateApplicationSystemConfirmedMessage) -- 60
  | logoutMessage (message : LogoutMessage) -- 70
  | logoutConfirmedMessage (message : LogoutConfirmedMessage) -- 80
  | confirmConnectionMessage (message : ConfirmConnectionMessage) -- 104
  | connectionConfirmedMessage (message : ConnectionConfirmedMessage) -- 105
  | tradeSessionStatusRequestMessage (message : TradeSessionStatusRequestMessage) -- 111
  | tradeSessionStatusReportMessage (message : TradeSessionStatusReportMessage) -- 112
  | orderInputMessage (message : OrderInputMessage) -- 101
  | orderInputLongFormatMessage (message : OrderInputLongFormatMessage) -- 131
  | orderStatusReportMessage (message : OrderStatusReportMessage) -- 102
  | orderStatusReportLongFormatMessage (message : OrderStatusReportLongFormatMessage) -- 132
  | errorReportMessage (message : ErrorReportMessage) -- 103
  | priceInquiryInputMessage (message : PriceInquiryInputMessage) -- 107
  | priceInquiryInputLongFormatMessage (message : PriceInquiryInputLongFormatMessage) -- 137
  | priceInquiryReplyMessage (message : PriceInquiryReplyMessage) -- 108
  | priceInquiryReplyLongFormatMessage (message : PriceInquiryReplyLongFormatMessage) -- 138
  | quoteInputMessage (message : QuoteInputMessage) -- 109
  | quoteInputLongFormatMessage (message : QuoteInputLongFormatMessage) -- 139
  | condensedVersionOrderStatusReportMessage (message : CondensedVersionOrderStatusReportMessage) -- 122
  | executionReportIncludingHeadOfficeAndBranchOfficesMessage (message : ExecutionReportIncludingHeadOfficeAndBranchOfficesMessage) -- 106
  | bulletinRequestMessage (message : BulletinRequestMessage) -- 113
  | bulletinReportMessage (message : BulletinReportMessage) -- 114
  | systemSettingMessage (message : SystemSettingMessage) -- 117
  | systemNotificationMessage (message : SystemNotificationMessage) -- 118
  | flexOrderInputSingleMessage (message : FlexOrderInputSingleMessage) -- 201
  | flexPriceInquiryInputMessage (message : FlexPriceInquiryInputMessage) -- 207
  | flexQuoteInputMessage (message : FlexQuoteInputMessage) -- 209
  | requestForSupplementaryFlexGroupReportMessage (message : RequestForSupplementaryFlexGroupReportMessage) -- 240
  | temporarySuspensionOfSupplementaryFlexGroupReportMessage (message : TemporarySuspensionOfSupplementaryFlexGroupReportMessage) -- 242
  | flexProductDefinitionRequestMessage (message : FlexProductDefinitionRequestMessage) -- 219
  | flexOrderStatusReportMessage (message : FlexOrderStatusReportMessage) -- 202
  | flexErrorReportMessage (message : FlexErrorReportMessage) -- 203
  | flexPriceInquiryReplyMessage (message : FlexPriceInquiryReplyMessage) -- 208
  | sendFlexGroupReportResendMessage (message : SendFlexGroupReportResendMessage) -- 241
  | flexProductDefinitionMessage (message : FlexProductDefinitionMessage) -- 220
  | flexBulletinRequestMessage (message : FlexBulletinRequestMessage) -- 213
  | flexBulletinReportMessage (message : FlexBulletinReportMessage) -- 214
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .wakeUpCallMessage _ => 10
  | .wakeUpCallConfirmedMessage _ => 20
  | .logonNoticeMessage _ => 30
  | .finalSequentialNumberNotificationForGroupMessage _ => 230
  | .requestLogonMessage _ => 40
  | .resendReportMessage _ => 41
  | .resendReportConfirmedMessage _ => 42
  | .activateApplicationSystemMessage _ => 50
  | .activateApplicationSystemConfirmedMessage _ => 60
  | .logoutMessage _ => 70
  | .logoutConfirmedMessage _ => 80
  | .confirmConnectionMessage _ => 104
  | .connectionConfirmedMessage _ => 105
  | .tradeSessionStatusRequestMessage _ => 111
  | .tradeSessionStatusReportMessage _ => 112
  | .orderInputMessage _ => 101
  | .orderInputLongFormatMessage _ => 131
  | .orderStatusReportMessage _ => 102
  | .orderStatusReportLongFormatMessage _ => 132
  | .errorReportMessage _ => 103
  | .priceInquiryInputMessage _ => 107
  | .priceInquiryInputLongFormatMessage _ => 137
  | .priceInquiryReplyMessage _ => 108
  | .priceInquiryReplyLongFormatMessage _ => 138
  | .quoteInputMessage _ => 109
  | .quoteInputLongFormatMessage _ => 139
  | .condensedVersionOrderStatusReportMessage _ => 122
  | .executionReportIncludingHeadOfficeAndBranchOfficesMessage _ => 106
  | .bulletinRequestMessage _ => 113
  | .bulletinReportMessage _ => 114
  | .systemSettingMessage _ => 117
  | .systemNotificationMessage _ => 118
  | .flexOrderInputSingleMessage _ => 201
  | .flexPriceInquiryInputMessage _ => 207
  | .flexQuoteInputMessage _ => 209
  | .requestForSupplementaryFlexGroupReportMessage _ => 240
  | .temporarySuspensionOfSupplementaryFlexGroupReportMessage _ => 242
  | .flexProductDefinitionRequestMessage _ => 219
  | .flexOrderStatusReportMessage _ => 202
  | .flexErrorReportMessage _ => 203
  | .flexPriceInquiryReplyMessage _ => 208
  | .sendFlexGroupReportResendMessage _ => 241
  | .flexProductDefinitionMessage _ => 220
  | .flexBulletinRequestMessage _ => 213
  | .flexBulletinReportMessage _ => 214

def encode : Payload → List UInt8
  | .wakeUpCallMessage message => WakeUpCallMessage.encode message
  | .wakeUpCallConfirmedMessage message => WakeUpCallConfirmedMessage.encode message
  | .logonNoticeMessage message => LogonNoticeMessage.encode message
  | .finalSequentialNumberNotificationForGroupMessage message => FinalSequentialNumberNotificationForGroupMessage.encode message
  | .requestLogonMessage message => RequestLogonMessage.encode message
  | .resendReportMessage message => ResendReportMessage.encode message
  | .resendReportConfirmedMessage message => ResendReportConfirmedMessage.encode message
  | .activateApplicationSystemMessage message => ActivateApplicationSystemMessage.encode message
  | .activateApplicationSystemConfirmedMessage message => ActivateApplicationSystemConfirmedMessage.encode message
  | .logoutMessage message => LogoutMessage.encode message
  | .logoutConfirmedMessage message => LogoutConfirmedMessage.encode message
  | .confirmConnectionMessage message => ConfirmConnectionMessage.encode message
  | .connectionConfirmedMessage message => ConnectionConfirmedMessage.encode message
  | .tradeSessionStatusRequestMessage message => TradeSessionStatusRequestMessage.encode message
  | .tradeSessionStatusReportMessage message => TradeSessionStatusReportMessage.encode message
  | .orderInputMessage message => OrderInputMessage.encode message
  | .orderInputLongFormatMessage message => OrderInputLongFormatMessage.encode message
  | .orderStatusReportMessage message => OrderStatusReportMessage.encode message
  | .orderStatusReportLongFormatMessage message => OrderStatusReportLongFormatMessage.encode message
  | .errorReportMessage message => ErrorReportMessage.encode message
  | .priceInquiryInputMessage message => PriceInquiryInputMessage.encode message
  | .priceInquiryInputLongFormatMessage message => PriceInquiryInputLongFormatMessage.encode message
  | .priceInquiryReplyMessage message => PriceInquiryReplyMessage.encode message
  | .priceInquiryReplyLongFormatMessage message => PriceInquiryReplyLongFormatMessage.encode message
  | .quoteInputMessage message => QuoteInputMessage.encode message
  | .quoteInputLongFormatMessage message => QuoteInputLongFormatMessage.encode message
  | .condensedVersionOrderStatusReportMessage message => CondensedVersionOrderStatusReportMessage.encode message
  | .executionReportIncludingHeadOfficeAndBranchOfficesMessage message => ExecutionReportIncludingHeadOfficeAndBranchOfficesMessage.encode message
  | .bulletinRequestMessage message => BulletinRequestMessage.encode message
  | .bulletinReportMessage message => BulletinReportMessage.encode message
  | .systemSettingMessage message => SystemSettingMessage.encode message
  | .systemNotificationMessage message => SystemNotificationMessage.encode message
  | .flexOrderInputSingleMessage message => FlexOrderInputSingleMessage.encode message
  | .flexPriceInquiryInputMessage message => FlexPriceInquiryInputMessage.encode message
  | .flexQuoteInputMessage message => FlexQuoteInputMessage.encode message
  | .requestForSupplementaryFlexGroupReportMessage message => RequestForSupplementaryFlexGroupReportMessage.encode message
  | .temporarySuspensionOfSupplementaryFlexGroupReportMessage message => TemporarySuspensionOfSupplementaryFlexGroupReportMessage.encode message
  | .flexProductDefinitionRequestMessage message => FlexProductDefinitionRequestMessage.encode message
  | .flexOrderStatusReportMessage message => FlexOrderStatusReportMessage.encode message
  | .flexErrorReportMessage message => FlexErrorReportMessage.encode message
  | .flexPriceInquiryReplyMessage message => FlexPriceInquiryReplyMessage.encode message
  | .sendFlexGroupReportResendMessage message => SendFlexGroupReportResendMessage.encode message
  | .flexProductDefinitionMessage message => FlexProductDefinitionMessage.encode message
  | .flexBulletinRequestMessage message => FlexBulletinRequestMessage.encode message
  | .flexBulletinReportMessage message => FlexBulletinReportMessage.encode message

/-- Decoded from the whole of the frame: a message that reads to its end takes it all, any other must leave nothing -/
def decode (tag : BitVec 8) (bytes : List UInt8) : Option Payload :=
  if tag = 10 then (WakeUpCallMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.wakeUpCallMessage message) else none
  else if tag = 20 then (WakeUpCallConfirmedMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.wakeUpCallConfirmedMessage message) else none
  else if tag = 30 then (LogonNoticeMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.logonNoticeMessage message) else none
  else if tag = 230 then (FinalSequentialNumberNotificationForGroupMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.finalSequentialNumberNotificationForGroupMessage message) else none
  else if tag = 40 then (RequestLogonMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.requestLogonMessage message) else none
  else if tag = 41 then (ResendReportMessage.decode bytes).map fun message => .resendReportMessage message
  else if tag = 42 then (ResendReportConfirmedMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.resendReportConfirmedMessage message) else none
  else if tag = 50 then (ActivateApplicationSystemMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.activateApplicationSystemMessage message) else none
  else if tag = 60 then (ActivateApplicationSystemConfirmedMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.activateApplicationSystemConfirmedMessage message) else none
  else if tag = 70 then (LogoutMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.logoutMessage message) else none
  else if tag = 80 then (LogoutConfirmedMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.logoutConfirmedMessage message) else none
  else if tag = 104 then (ConfirmConnectionMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.confirmConnectionMessage message) else none
  else if tag = 105 then (ConnectionConfirmedMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.connectionConfirmedMessage message) else none
  else if tag = 111 then (TradeSessionStatusRequestMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tradeSessionStatusRequestMessage message) else none
  else if tag = 112 then (TradeSessionStatusReportMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tradeSessionStatusReportMessage message) else none
  else if tag = 101 then (OrderInputMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderInputMessage message) else none
  else if tag = 131 then (OrderInputLongFormatMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderInputLongFormatMessage message) else none
  else if tag = 102 then (OrderStatusReportMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderStatusReportMessage message) else none
  else if tag = 132 then (OrderStatusReportLongFormatMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderStatusReportLongFormatMessage message) else none
  else if tag = 103 then (ErrorReportMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.errorReportMessage message) else none
  else if tag = 107 then (PriceInquiryInputMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.priceInquiryInputMessage message) else none
  else if tag = 137 then (PriceInquiryInputLongFormatMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.priceInquiryInputLongFormatMessage message) else none
  else if tag = 108 then (PriceInquiryReplyMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.priceInquiryReplyMessage message) else none
  else if tag = 138 then (PriceInquiryReplyLongFormatMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.priceInquiryReplyLongFormatMessage message) else none
  else if tag = 109 then (QuoteInputMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.quoteInputMessage message) else none
  else if tag = 139 then (QuoteInputLongFormatMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.quoteInputLongFormatMessage message) else none
  else if tag = 122 then (CondensedVersionOrderStatusReportMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.condensedVersionOrderStatusReportMessage message) else none
  else if tag = 106 then (ExecutionReportIncludingHeadOfficeAndBranchOfficesMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.executionReportIncludingHeadOfficeAndBranchOfficesMessage message) else none
  else if tag = 113 then (BulletinRequestMessage.decode bytes).map fun message => .bulletinRequestMessage message
  else if tag = 114 then (BulletinReportMessage.decode bytes).map fun message => .bulletinReportMessage message
  else if tag = 117 then (SystemSettingMessage.decode bytes).map fun message => .systemSettingMessage message
  else if tag = 118 then (SystemNotificationMessage.decode bytes).map fun message => .systemNotificationMessage message
  else if tag = 201 then (FlexOrderInputSingleMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.flexOrderInputSingleMessage message) else none
  else if tag = 207 then (FlexPriceInquiryInputMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.flexPriceInquiryInputMessage message) else none
  else if tag = 209 then (FlexQuoteInputMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.flexQuoteInputMessage message) else none
  else if tag = 240 then (RequestForSupplementaryFlexGroupReportMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.requestForSupplementaryFlexGroupReportMessage message) else none
  else if tag = 242 then (TemporarySuspensionOfSupplementaryFlexGroupReportMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.temporarySuspensionOfSupplementaryFlexGroupReportMessage message) else none
  else if tag = 219 then (FlexProductDefinitionRequestMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.flexProductDefinitionRequestMessage message) else none
  else if tag = 202 then (FlexOrderStatusReportMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.flexOrderStatusReportMessage message) else none
  else if tag = 203 then (FlexErrorReportMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.flexErrorReportMessage message) else none
  else if tag = 208 then (FlexPriceInquiryReplyMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.flexPriceInquiryReplyMessage message) else none
  else if tag = 241 then (SendFlexGroupReportResendMessage.decode bytes).map fun message => .sendFlexGroupReportResendMessage message
  else if tag = 220 then (FlexProductDefinitionMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.flexProductDefinitionMessage message) else none
  else if tag = 213 then (FlexBulletinRequestMessage.decode bytes).map fun message => .flexBulletinRequestMessage message
  else if tag = 214 then (FlexBulletinReportMessage.decode bytes).map fun message => .flexBulletinReportMessage message
  else none

theorem decode_encode (message : Payload) :
    decode (tag message) (encode message) = some message := by
  cases message with
  | wakeUpCallMessage message => simp [decode, encode, tag, WakeUpCallMessage.decode_encode_nil]
  | wakeUpCallConfirmedMessage message => simp [decode, encode, tag, WakeUpCallConfirmedMessage.decode_encode_nil]
  | logonNoticeMessage message => simp [decode, encode, tag, LogonNoticeMessage.decode_encode_nil]
  | finalSequentialNumberNotificationForGroupMessage message => simp [decode, encode, tag, FinalSequentialNumberNotificationForGroupMessage.decode_encode_nil]
  | requestLogonMessage message => simp [decode, encode, tag, RequestLogonMessage.decode_encode_nil]
  | resendReportMessage message => simp [decode, encode, tag, ResendReportMessage.decode_encode]
  | resendReportConfirmedMessage message => simp [decode, encode, tag, ResendReportConfirmedMessage.decode_encode_nil]
  | activateApplicationSystemMessage message => simp [decode, encode, tag, ActivateApplicationSystemMessage.decode_encode_nil]
  | activateApplicationSystemConfirmedMessage message => simp [decode, encode, tag, ActivateApplicationSystemConfirmedMessage.decode_encode_nil]
  | logoutMessage message => simp [decode, encode, tag, LogoutMessage.decode_encode_nil]
  | logoutConfirmedMessage message => simp [decode, encode, tag, LogoutConfirmedMessage.decode_encode_nil]
  | confirmConnectionMessage message => simp [decode, encode, tag, ConfirmConnectionMessage.decode_encode_nil]
  | connectionConfirmedMessage message => simp [decode, encode, tag, ConnectionConfirmedMessage.decode_encode_nil]
  | tradeSessionStatusRequestMessage message => simp [decode, encode, tag, TradeSessionStatusRequestMessage.decode_encode_nil]
  | tradeSessionStatusReportMessage message => simp [decode, encode, tag, TradeSessionStatusReportMessage.decode_encode_nil]
  | orderInputMessage message => simp [decode, encode, tag, OrderInputMessage.decode_encode_nil]
  | orderInputLongFormatMessage message => simp [decode, encode, tag, OrderInputLongFormatMessage.decode_encode_nil]
  | orderStatusReportMessage message => simp [decode, encode, tag, OrderStatusReportMessage.decode_encode_nil]
  | orderStatusReportLongFormatMessage message => simp [decode, encode, tag, OrderStatusReportLongFormatMessage.decode_encode_nil]
  | errorReportMessage message => simp [decode, encode, tag, ErrorReportMessage.decode_encode_nil]
  | priceInquiryInputMessage message => simp [decode, encode, tag, PriceInquiryInputMessage.decode_encode_nil]
  | priceInquiryInputLongFormatMessage message => simp [decode, encode, tag, PriceInquiryInputLongFormatMessage.decode_encode_nil]
  | priceInquiryReplyMessage message => simp [decode, encode, tag, PriceInquiryReplyMessage.decode_encode_nil]
  | priceInquiryReplyLongFormatMessage message => simp [decode, encode, tag, PriceInquiryReplyLongFormatMessage.decode_encode_nil]
  | quoteInputMessage message => simp [decode, encode, tag, QuoteInputMessage.decode_encode_nil]
  | quoteInputLongFormatMessage message => simp [decode, encode, tag, QuoteInputLongFormatMessage.decode_encode_nil]
  | condensedVersionOrderStatusReportMessage message => simp [decode, encode, tag, CondensedVersionOrderStatusReportMessage.decode_encode_nil]
  | executionReportIncludingHeadOfficeAndBranchOfficesMessage message => simp [decode, encode, tag, ExecutionReportIncludingHeadOfficeAndBranchOfficesMessage.decode_encode_nil]
  | bulletinRequestMessage message => simp [decode, encode, tag, BulletinRequestMessage.decode_encode]
  | bulletinReportMessage message => simp [decode, encode, tag, BulletinReportMessage.decode_encode]
  | systemSettingMessage message => simp [decode, encode, tag, SystemSettingMessage.decode_encode]
  | systemNotificationMessage message => simp [decode, encode, tag, SystemNotificationMessage.decode_encode]
  | flexOrderInputSingleMessage message => simp [decode, encode, tag, FlexOrderInputSingleMessage.decode_encode_nil]
  | flexPriceInquiryInputMessage message => simp [decode, encode, tag, FlexPriceInquiryInputMessage.decode_encode_nil]
  | flexQuoteInputMessage message => simp [decode, encode, tag, FlexQuoteInputMessage.decode_encode_nil]
  | requestForSupplementaryFlexGroupReportMessage message => simp [decode, encode, tag, RequestForSupplementaryFlexGroupReportMessage.decode_encode_nil]
  | temporarySuspensionOfSupplementaryFlexGroupReportMessage message => simp [decode, encode, tag, TemporarySuspensionOfSupplementaryFlexGroupReportMessage.decode_encode_nil]
  | flexProductDefinitionRequestMessage message => simp [decode, encode, tag, FlexProductDefinitionRequestMessage.decode_encode_nil]
  | flexOrderStatusReportMessage message => simp [decode, encode, tag, FlexOrderStatusReportMessage.decode_encode_nil]
  | flexErrorReportMessage message => simp [decode, encode, tag, FlexErrorReportMessage.decode_encode_nil]
  | flexPriceInquiryReplyMessage message => simp [decode, encode, tag, FlexPriceInquiryReplyMessage.decode_encode_nil]
  | sendFlexGroupReportResendMessage message => simp [decode, encode, tag, SendFlexGroupReportResendMessage.decode_encode]
  | flexProductDefinitionMessage message => simp [decode, encode, tag, FlexProductDefinitionMessage.decode_encode_nil]
  | flexBulletinRequestMessage message => simp [decode, encode, tag, FlexBulletinRequestMessage.decode_encode]
  | flexBulletinReportMessage message => simp [decode, encode, tag, FlexBulletinReportMessage.decode_encode]

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

def decode (bytes : List UInt8) : Option TmpMessage := do
  let (msgLength, bytes) ← decodeUInt 2 bytes
  let (msgSeqNum, bytes) ← decodeUInt 4 bytes
  let (headerTime, bytes) ← HeaderTime.decode bytes
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (fcmId, bytes) ← decodeUInt 2 bytes
  let (sessionId, bytes) ← decodeUInt 2 bytes
  let (bytes, trailing) ← splitTrailer 1 bytes
  let payload ← Payload.decode messageType bytes
  let bytes := trailing
  let (messageTail, _) ← MessageTail.decode bytes
  pure { msgLength, msgSeqNum, headerTime, fcmId, sessionId, payload, messageTail }

theorem encode_length_pos (message : TmpMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

theorem decode_encode (message : TmpMessage) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [HeaderTime.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  have trailing_length : (MessageTail.encode message.messageTail).length = 1 := by
    simp [MessageTail.encode_length]
  rw [splitTrailer_append 1 _ _ trailing_length, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rw [MessageTail.decode_encode, some_bind]
  rfl

end TmpMessage

end Omi.TaifexTaifexderivativesOrderentryTmpV2187
