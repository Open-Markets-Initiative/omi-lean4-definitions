import Wire

/-!
# Singapore Exchange Reference Data v0.8, Exchange messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.SgxTitandtReferencedataFixV08Exchange

structure Header where
  senderCompID : Terminated 1  -- tag 49
  targetCompID : Terminated 1  -- tag 56
  senderSubID : Option (Terminated 1)  -- tag 50
  msgSeqNum : Terminated 1  -- tag 34
  sendingTime : Terminated 1  -- tag 52
  possDupFlag : Option (Terminated 1)  -- tag 43
  possResend : Option (Terminated 1)  -- tag 97
  origSendingTime : Option (Terminated 1)  -- tag 122

def Header.parts (record : Header) : List Part :=
  [Part.required [52, 57] record.senderCompID,
   Part.required [53, 54] record.targetCompID,
   Part.optional [53, 48] record.senderSubID,
   Part.required [51, 52] record.msgSeqNum,
   Part.required [53, 50] record.sendingTime,
   Part.optional [52, 51] record.possDupFlag,
   Part.optional [57, 55] record.possResend,
   Part.optional [49, 50, 50] record.origSendingTime]

def Header.tags : List (List (List UInt8)) :=
  [[[52, 57]], [[53, 54]], [[53, 48]], [[51, 52]], [[53, 50]], [[52, 51]], [[57, 55]], [[49, 50, 50]]]

theorem Header.shape (record : Header) : record.parts.map Part.tags = Header.tags := rfl

def Header.decode (tokens : List Token) : Option Header := do
  let senderCompID ← readRequired [52, 57] tokens
  let targetCompID ← readRequired [53, 54] tokens
  let senderSubID ← readOptional [53, 48] tokens
  let msgSeqNum ← readRequired [51, 52] tokens
  let sendingTime ← readRequired [53, 50] tokens
  let possDupFlag ← readOptional [52, 51] tokens
  let possResend ← readOptional [57, 55] tokens
  let origSendingTime ← readOptional [49, 50, 50] tokens
  pure { senderCompID, targetCompID, senderSubID, msgSeqNum, sendingTime, possDupFlag, possResend, origSendingTime }

theorem Header.decode_agrees (record : Header) (tokens : List Token)
    (agrees : ∀ tags ∈ Header.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Header.decode tokens = some record := by
  have distinct : Header.tags.flatten.Nodup := by decide +kernel
  have senderCompID := readRequired_part [52, 57] record.senderCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have targetCompID := readRequired_part [53, 54] record.targetCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have senderSubID := readOptional_part [53, 48] record.senderSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have msgSeqNum := readRequired_part [51, 52] record.msgSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have sendingTime := readRequired_part [53, 50] record.sendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have possDupFlag := readOptional_part [52, 51] record.possDupFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have possResend := readOptional_part [57, 55] record.possResend tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have origSendingTime := readOptional_part [49, 50, 50] record.origSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  simp only [Header.decode, senderCompID, targetCompID, senderSubID, msgSeqNum, sendingTime, possDupFlag, possResend, origSendingTime, some_bind] <;> rfl

structure Logon where
  encryptMethod : Terminated 1  -- tag 98
  heartBtInt : Terminated 1  -- tag 108
  resetSeqNumFlag : Option (Terminated 1)  -- tag 141
  username : Terminated 1  -- tag 553
  password : Terminated 1  -- tag 554
  newPassword : Option (Terminated 1)  -- tag 925
  defaultApplVerID : Terminated 1  -- tag 1137
  sessionStatus : Option (Terminated 1)  -- tag 1409
  daysToPwdExpiry : Option (Terminated 1)  -- tag 20002

def Logon.parts (record : Logon) : List Part :=
  [Part.required [57, 56] record.encryptMethod,
   Part.required [49, 48, 56] record.heartBtInt,
   Part.optional [49, 52, 49] record.resetSeqNumFlag,
   Part.required [53, 53, 51] record.username,
   Part.required [53, 53, 52] record.password,
   Part.optional [57, 50, 53] record.newPassword,
   Part.required [49, 49, 51, 55] record.defaultApplVerID,
   Part.optional [49, 52, 48, 57] record.sessionStatus,
   Part.optional [50, 48, 48, 48, 50] record.daysToPwdExpiry]

def Logon.tags : List (List (List UInt8)) :=
  [[[57, 56]], [[49, 48, 56]], [[49, 52, 49]], [[53, 53, 51]], [[53, 53, 52]], [[57, 50, 53]], [[49, 49, 51, 55]], [[49, 52, 48, 57]], [[50, 48, 48, 48, 50]]]

theorem Logon.shape (record : Logon) : record.parts.map Part.tags = Logon.tags := rfl

def Logon.decode (tokens : List Token) : Option Logon := do
  let encryptMethod ← readRequired [57, 56] tokens
  let heartBtInt ← readRequired [49, 48, 56] tokens
  let resetSeqNumFlag ← readOptional [49, 52, 49] tokens
  let username ← readRequired [53, 53, 51] tokens
  let password ← readRequired [53, 53, 52] tokens
  let newPassword ← readOptional [57, 50, 53] tokens
  let defaultApplVerID ← readRequired [49, 49, 51, 55] tokens
  let sessionStatus ← readOptional [49, 52, 48, 57] tokens
  let daysToPwdExpiry ← readOptional [50, 48, 48, 48, 50] tokens
  pure { encryptMethod, heartBtInt, resetSeqNumFlag, username, password, newPassword, defaultApplVerID, sessionStatus, daysToPwdExpiry }

theorem Logon.decode_agrees (record : Logon) (tokens : List Token)
    (agrees : ∀ tags ∈ Logon.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Logon.decode tokens = some record := by
  have distinct : Logon.tags.flatten.Nodup := by decide +kernel
  have encryptMethod := readRequired_part [57, 56] record.encryptMethod tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have heartBtInt := readRequired_part [49, 48, 56] record.heartBtInt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have resetSeqNumFlag := readOptional_part [49, 52, 49] record.resetSeqNumFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have username := readRequired_part [53, 53, 51] record.username tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have password := readRequired_part [53, 53, 52] record.password tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have newPassword := readOptional_part [57, 50, 53] record.newPassword tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have defaultApplVerID := readRequired_part [49, 49, 51, 55] record.defaultApplVerID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have sessionStatus := readOptional_part [49, 52, 48, 57] record.sessionStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have daysToPwdExpiry := readOptional_part [50, 48, 48, 48, 50] record.daysToPwdExpiry tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  simp only [Logon.decode, encryptMethod, heartBtInt, resetSeqNumFlag, username, password, newPassword, defaultApplVerID, sessionStatus, daysToPwdExpiry, some_bind] <;> rfl

structure Logout where
  sessionStatus : Option (Terminated 1)  -- tag 1409
  text : Option (Terminated 1)  -- tag 58

def Logout.parts (record : Logout) : List Part :=
  [Part.optional [49, 52, 48, 57] record.sessionStatus,
   Part.optional [53, 56] record.text]

def Logout.tags : List (List (List UInt8)) :=
  [[[49, 52, 48, 57]], [[53, 56]]]

theorem Logout.shape (record : Logout) : record.parts.map Part.tags = Logout.tags := rfl

def Logout.decode (tokens : List Token) : Option Logout := do
  let sessionStatus ← readOptional [49, 52, 48, 57] tokens
  let text ← readOptional [53, 56] tokens
  pure { sessionStatus, text }

theorem Logout.decode_agrees (record : Logout) (tokens : List Token)
    (agrees : ∀ tags ∈ Logout.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Logout.decode tokens = some record := by
  have distinct : Logout.tags.flatten.Nodup := by decide +kernel
  have sessionStatus := readOptional_part [49, 52, 48, 57] record.sessionStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [Logout.decode, sessionStatus, text, some_bind] <;> rfl

structure SequenceReset where
  gapFillFlag : Option (Terminated 1)  -- tag 123
  newSeqNo : Terminated 1  -- tag 36

def SequenceReset.parts (record : SequenceReset) : List Part :=
  [Part.optional [49, 50, 51] record.gapFillFlag,
   Part.required [51, 54] record.newSeqNo]

def SequenceReset.tags : List (List (List UInt8)) :=
  [[[49, 50, 51]], [[51, 54]]]

theorem SequenceReset.shape (record : SequenceReset) : record.parts.map Part.tags = SequenceReset.tags := rfl

def SequenceReset.decode (tokens : List Token) : Option SequenceReset := do
  let gapFillFlag ← readOptional [49, 50, 51] tokens
  let newSeqNo ← readRequired [51, 54] tokens
  pure { gapFillFlag, newSeqNo }

theorem SequenceReset.decode_agrees (record : SequenceReset) (tokens : List Token)
    (agrees : ∀ tags ∈ SequenceReset.tags, select tags tokens = select tags (encodeParts record.parts)) :
    SequenceReset.decode tokens = some record := by
  have distinct : SequenceReset.tags.flatten.Nodup := by decide +kernel
  have gapFillFlag := readOptional_part [49, 50, 51] record.gapFillFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have newSeqNo := readRequired_part [51, 54] record.newSeqNo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [SequenceReset.decode, gapFillFlag, newSeqNo, some_bind] <;> rfl

structure ResendRequest where
  beginSeqNo : Terminated 1  -- tag 7
  endSeqNo : Terminated 1  -- tag 16

def ResendRequest.parts (record : ResendRequest) : List Part :=
  [Part.required [55] record.beginSeqNo,
   Part.required [49, 54] record.endSeqNo]

def ResendRequest.tags : List (List (List UInt8)) :=
  [[[55]], [[49, 54]]]

theorem ResendRequest.shape (record : ResendRequest) : record.parts.map Part.tags = ResendRequest.tags := rfl

def ResendRequest.decode (tokens : List Token) : Option ResendRequest := do
  let beginSeqNo ← readRequired [55] tokens
  let endSeqNo ← readRequired [49, 54] tokens
  pure { beginSeqNo, endSeqNo }

theorem ResendRequest.decode_agrees (record : ResendRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ ResendRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ResendRequest.decode tokens = some record := by
  have distinct : ResendRequest.tags.flatten.Nodup := by decide +kernel
  have beginSeqNo := readRequired_part [55] record.beginSeqNo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have endSeqNo := readRequired_part [49, 54] record.endSeqNo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [ResendRequest.decode, beginSeqNo, endSeqNo, some_bind] <;> rfl

structure Heartbeat where
  testReqID : Option (Terminated 1)  -- tag 112

def Heartbeat.parts (record : Heartbeat) : List Part :=
  [Part.optional [49, 49, 50] record.testReqID]

def Heartbeat.tags : List (List (List UInt8)) :=
  [[[49, 49, 50]]]

theorem Heartbeat.shape (record : Heartbeat) : record.parts.map Part.tags = Heartbeat.tags := rfl

def Heartbeat.decode (tokens : List Token) : Option Heartbeat := do
  let testReqID ← readOptional [49, 49, 50] tokens
  pure { testReqID }

theorem Heartbeat.decode_agrees (record : Heartbeat) (tokens : List Token)
    (agrees : ∀ tags ∈ Heartbeat.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Heartbeat.decode tokens = some record := by
  have distinct : Heartbeat.tags.flatten.Nodup := by decide +kernel
  have testReqID := readOptional_part [49, 49, 50] record.testReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [Heartbeat.decode, testReqID, some_bind] <;> rfl

structure TestRequest where
  testReqID : Terminated 1  -- tag 112

def TestRequest.parts (record : TestRequest) : List Part :=
  [Part.required [49, 49, 50] record.testReqID]

def TestRequest.tags : List (List (List UInt8)) :=
  [[[49, 49, 50]]]

theorem TestRequest.shape (record : TestRequest) : record.parts.map Part.tags = TestRequest.tags := rfl

def TestRequest.decode (tokens : List Token) : Option TestRequest := do
  let testReqID ← readRequired [49, 49, 50] tokens
  pure { testReqID }

theorem TestRequest.decode_agrees (record : TestRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ TestRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TestRequest.decode tokens = some record := by
  have distinct : TestRequest.tags.flatten.Nodup := by decide +kernel
  have testReqID := readRequired_part [49, 49, 50] record.testReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [TestRequest.decode, testReqID, some_bind] <;> rfl

structure Reject where
  refSeqNum : Terminated 1  -- tag 45
  refTagID : Option (Terminated 1)  -- tag 371
  refMsgType : Option (Terminated 1)  -- tag 372
  sessionRejectReason : Option (Terminated 1)  -- tag 373
  text : Option (Terminated 1)  -- tag 58

def Reject.parts (record : Reject) : List Part :=
  [Part.required [52, 53] record.refSeqNum,
   Part.optional [51, 55, 49] record.refTagID,
   Part.optional [51, 55, 50] record.refMsgType,
   Part.optional [51, 55, 51] record.sessionRejectReason,
   Part.optional [53, 56] record.text]

def Reject.tags : List (List (List UInt8)) :=
  [[[52, 53]], [[51, 55, 49]], [[51, 55, 50]], [[51, 55, 51]], [[53, 56]]]

theorem Reject.shape (record : Reject) : record.parts.map Part.tags = Reject.tags := rfl

def Reject.decode (tokens : List Token) : Option Reject := do
  let refSeqNum ← readRequired [52, 53] tokens
  let refTagID ← readOptional [51, 55, 49] tokens
  let refMsgType ← readOptional [51, 55, 50] tokens
  let sessionRejectReason ← readOptional [51, 55, 51] tokens
  let text ← readOptional [53, 56] tokens
  pure { refSeqNum, refTagID, refMsgType, sessionRejectReason, text }

theorem Reject.decode_agrees (record : Reject) (tokens : List Token)
    (agrees : ∀ tags ∈ Reject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Reject.decode tokens = some record := by
  have distinct : Reject.tags.flatten.Nodup := by decide +kernel
  have refSeqNum := readRequired_part [52, 53] record.refSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have refTagID := readOptional_part [51, 55, 49] record.refTagID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have refMsgType := readOptional_part [51, 55, 50] record.refMsgType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have sessionRejectReason := readOptional_part [51, 55, 51] record.sessionRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [Reject.decode, refSeqNum, refTagID, refMsgType, sessionRejectReason, text, some_bind] <;> rfl

structure NoApplIDs where
  refApplID : Terminated 1  -- tag 1355
  applBegSeqNum : Option (Terminated 1)  -- tag 1182
  applEndSeqNum : Option (Terminated 1)  -- tag 1183

def NoApplIDs.parts (record : NoApplIDs) : List Part :=
  [Part.required [49, 51, 53, 53] record.refApplID,
   Part.optional [49, 49, 56, 50] record.applBegSeqNum,
   Part.optional [49, 49, 56, 51] record.applEndSeqNum]

def NoApplIDs.tags : List (List (List UInt8)) :=
  [[[49, 51, 53, 53]], [[49, 49, 56, 50]], [[49, 49, 56, 51]]]

theorem NoApplIDs.shape (record : NoApplIDs) : record.parts.map Part.tags = NoApplIDs.tags := rfl

def NoApplIDs.decode (tokens : List Token) : Option NoApplIDs := do
  let refApplID ← readRequired [49, 51, 53, 53] tokens
  let applBegSeqNum ← readOptional [49, 49, 56, 50] tokens
  let applEndSeqNum ← readOptional [49, 49, 56, 51] tokens
  pure { refApplID, applBegSeqNum, applEndSeqNum }

theorem NoApplIDs.decode_agrees (record : NoApplIDs) (tokens : List Token)
    (agrees : ∀ tags ∈ NoApplIDs.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoApplIDs.decode tokens = some record := by
  have distinct : NoApplIDs.tags.flatten.Nodup := by decide +kernel
  have refApplID := readRequired_part [49, 51, 53, 53] record.refApplID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have applBegSeqNum := readOptional_part [49, 49, 56, 50] record.applBegSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have applEndSeqNum := readOptional_part [49, 49, 56, 51] record.applEndSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [NoApplIDs.decode, refApplID, applBegSeqNum, applEndSeqNum, some_bind] <;> rfl

def NoApplIDs.members : List (List UInt8) := NoApplIDs.tags.flatten

def NoApplIDs.encode (entry : NoApplIDs) : List Token := encodeParts entry.parts

theorem NoApplIDs.decode_encode (entry : NoApplIDs) : NoApplIDs.decode entry.encode = some entry :=
  NoApplIDs.decode_agrees entry _ (fun _ _ => rfl)

theorem NoApplIDs.within (entry : NoApplIDs) : ∀ token ∈ entry.encode, token.tag ∈ NoApplIDs.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoApplIDs.shape] at this

theorem NoApplIDs.led (entry : NoApplIDs) : Lead [49, 51, 53, 53] entry.encode :=
  lead_parts [49, 51, 53, 53] entry.refApplID _ NoApplIDs.tags.tail rfl (by decide +kernel)

structure ApplicationMessageRequestAck where
  applResponseID : Terminated 1  -- tag 1353
  applReqID : Option (Terminated 1)  -- tag 1346
  applReqType : Option (Terminated 1)  -- tag 1347
  applResponseType : Option (Terminated 1)  -- tag 1348
  noApplIDs : List NoApplIDs  -- tag 1351
  applResponseError : Option (Terminated 1)  -- tag 1354
  text : Option (Terminated 1)  -- tag 58

def ApplicationMessageRequestAck.parts (record : ApplicationMessageRequestAck) : List Part :=
  [Part.required [49, 51, 53, 51] record.applResponseID,
   Part.optional [49, 51, 52, 54] record.applReqID,
   Part.optional [49, 51, 52, 55] record.applReqType,
   Part.optional [49, 51, 52, 56] record.applResponseType,
   Part.group [49, 51, 53, 49] NoApplIDs.members NoApplIDs.encode NoApplIDs.within record.noApplIDs,
   Part.optional [49, 51, 53, 52] record.applResponseError,
   Part.optional [53, 56] record.text]

def ApplicationMessageRequestAck.tags : List (List (List UInt8)) :=
  [[[49, 51, 53, 51]], [[49, 51, 52, 54]], [[49, 51, 52, 55]], [[49, 51, 52, 56]], [49, 51, 53, 49] :: NoApplIDs.members, [[49, 51, 53, 52]], [[53, 56]]]

theorem ApplicationMessageRequestAck.shape (record : ApplicationMessageRequestAck) : record.parts.map Part.tags = ApplicationMessageRequestAck.tags := rfl

def ApplicationMessageRequestAck.decode (tokens : List Token) : Option ApplicationMessageRequestAck := do
  let applResponseID ← readRequired [49, 51, 53, 51] tokens
  let applReqID ← readOptional [49, 51, 52, 54] tokens
  let applReqType ← readOptional [49, 51, 52, 55] tokens
  let applResponseType ← readOptional [49, 51, 52, 56] tokens
  let noApplIDs ← readGroup [49, 51, 53, 49] [49, 51, 53, 53] NoApplIDs.members NoApplIDs.decode tokens
  let applResponseError ← readOptional [49, 51, 53, 52] tokens
  let text ← readOptional [53, 56] tokens
  pure { applResponseID, applReqID, applReqType, applResponseType, noApplIDs, applResponseError, text }

theorem ApplicationMessageRequestAck.decode_agrees (record : ApplicationMessageRequestAck) (tokens : List Token)
    (agrees : ∀ tags ∈ ApplicationMessageRequestAck.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ApplicationMessageRequestAck.decode tokens = some record := by
  have distinct : ApplicationMessageRequestAck.tags.flatten.Nodup := by decide +kernel
  have applResponseID := readRequired_part [49, 51, 53, 51] record.applResponseID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have applReqID := readOptional_part [49, 51, 52, 54] record.applReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have applReqType := readOptional_part [49, 51, 52, 55] record.applReqType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have applResponseType := readOptional_part [49, 51, 52, 56] record.applResponseType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have noApplIDs := readGroup_part [49, 51, 53, 49] [49, 51, 53, 53] NoApplIDs.members NoApplIDs.encode NoApplIDs.within NoApplIDs.decode NoApplIDs.decode_encode NoApplIDs.led record.noApplIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have applResponseError := readOptional_part [49, 51, 53, 52] record.applResponseError tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  simp only [ApplicationMessageRequestAck.decode, applResponseID, applReqID, applReqType, applResponseType, noApplIDs, applResponseError, text, some_bind] <;> rfl

structure NoUnderlyings where
  underlyingSymbol : Terminated 1  -- tag 311
  underlyingCurrency : Option (Terminated 1)  -- tag 318

def NoUnderlyings.parts (record : NoUnderlyings) : List Part :=
  [Part.required [51, 49, 49] record.underlyingSymbol,
   Part.optional [51, 49, 56] record.underlyingCurrency]

def NoUnderlyings.tags : List (List (List UInt8)) :=
  [[[51, 49, 49]], [[51, 49, 56]]]

theorem NoUnderlyings.shape (record : NoUnderlyings) : record.parts.map Part.tags = NoUnderlyings.tags := rfl

def NoUnderlyings.decode (tokens : List Token) : Option NoUnderlyings := do
  let underlyingSymbol ← readRequired [51, 49, 49] tokens
  let underlyingCurrency ← readOptional [51, 49, 56] tokens
  pure { underlyingSymbol, underlyingCurrency }

theorem NoUnderlyings.decode_agrees (record : NoUnderlyings) (tokens : List Token)
    (agrees : ∀ tags ∈ NoUnderlyings.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoUnderlyings.decode tokens = some record := by
  have distinct : NoUnderlyings.tags.flatten.Nodup := by decide +kernel
  have underlyingSymbol := readRequired_part [51, 49, 49] record.underlyingSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have underlyingCurrency := readOptional_part [51, 49, 56] record.underlyingCurrency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [NoUnderlyings.decode, underlyingSymbol, underlyingCurrency, some_bind] <;> rfl

def NoUnderlyings.members : List (List UInt8) := NoUnderlyings.tags.flatten

def NoUnderlyings.encode (entry : NoUnderlyings) : List Token := encodeParts entry.parts

theorem NoUnderlyings.decode_encode (entry : NoUnderlyings) : NoUnderlyings.decode entry.encode = some entry :=
  NoUnderlyings.decode_agrees entry _ (fun _ _ => rfl)

theorem NoUnderlyings.within (entry : NoUnderlyings) : ∀ token ∈ entry.encode, token.tag ∈ NoUnderlyings.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoUnderlyings.shape] at this

theorem NoUnderlyings.led (entry : NoUnderlyings) : Lead [51, 49, 49] entry.encode :=
  lead_parts [51, 49, 49] entry.underlyingSymbol _ NoUnderlyings.tags.tail rfl (by decide +kernel)

structure SecurityDefinition where
  applID : Option (Terminated 1)  -- tag 1180
  applSeqNum : Option (Terminated 1)  -- tag 1181
  applLastSeqNum : Option (Terminated 1)  -- tag 1350
  applResendFlag : Option (Terminated 1)  -- tag 1352
  symbol : Option (Terminated 1)  -- tag 55
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22
  securityType : Option (Terminated 1)  -- tag 167
  securitySubType : Option (Terminated 1)  -- tag 762
  maturityDate : Option (Terminated 1)  -- tag 541
  issueDate : Option (Terminated 1)  -- tag 225
  contractMultiplier : Option (Terminated 1)  -- tag 231
  securityDesc : Option (Terminated 1)  -- tag 107
  maturityMonthYear : Option (Terminated 1)  -- tag 200
  putOrCall : Option (Terminated 1)  -- tag 201
  marketID : Option (Terminated 1)  -- tag 1301
  marketSegmentID : Option (Terminated 1)  -- tag 1310
  noUnderlyings : List NoUnderlyings  -- tag 711

def SecurityDefinition.parts (record : SecurityDefinition) : List Part :=
  [Part.optional [49, 49, 56, 48] record.applID,
   Part.optional [49, 49, 56, 49] record.applSeqNum,
   Part.optional [49, 51, 53, 48] record.applLastSeqNum,
   Part.optional [49, 51, 53, 50] record.applResendFlag,
   Part.optional [53, 53] record.symbol,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource,
   Part.optional [49, 54, 55] record.securityType,
   Part.optional [55, 54, 50] record.securitySubType,
   Part.optional [53, 52, 49] record.maturityDate,
   Part.optional [50, 50, 53] record.issueDate,
   Part.optional [50, 51, 49] record.contractMultiplier,
   Part.optional [49, 48, 55] record.securityDesc,
   Part.optional [50, 48, 48] record.maturityMonthYear,
   Part.optional [50, 48, 49] record.putOrCall,
   Part.optional [49, 51, 48, 49] record.marketID,
   Part.optional [49, 51, 49, 48] record.marketSegmentID,
   Part.group [55, 49, 49] NoUnderlyings.members NoUnderlyings.encode NoUnderlyings.within record.noUnderlyings]

def SecurityDefinition.tags : List (List (List UInt8)) :=
  [[[49, 49, 56, 48]], [[49, 49, 56, 49]], [[49, 51, 53, 48]], [[49, 51, 53, 50]], [[53, 53]], [[52, 56]], [[50, 50]], [[49, 54, 55]], [[55, 54, 50]], [[53, 52, 49]], [[50, 50, 53]], [[50, 51, 49]], [[49, 48, 55]], [[50, 48, 48]], [[50, 48, 49]], [[49, 51, 48, 49]], [[49, 51, 49, 48]], [55, 49, 49] :: NoUnderlyings.members]

theorem SecurityDefinition.shape (record : SecurityDefinition) : record.parts.map Part.tags = SecurityDefinition.tags := rfl

def SecurityDefinition.decode (tokens : List Token) : Option SecurityDefinition := do
  let applID ← readOptional [49, 49, 56, 48] tokens
  let applSeqNum ← readOptional [49, 49, 56, 49] tokens
  let applLastSeqNum ← readOptional [49, 51, 53, 48] tokens
  let applResendFlag ← readOptional [49, 51, 53, 50] tokens
  let symbol ← readOptional [53, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let securityType ← readOptional [49, 54, 55] tokens
  let securitySubType ← readOptional [55, 54, 50] tokens
  let maturityDate ← readOptional [53, 52, 49] tokens
  let issueDate ← readOptional [50, 50, 53] tokens
  let contractMultiplier ← readOptional [50, 51, 49] tokens
  let securityDesc ← readOptional [49, 48, 55] tokens
  let maturityMonthYear ← readOptional [50, 48, 48] tokens
  let putOrCall ← readOptional [50, 48, 49] tokens
  let marketID ← readOptional [49, 51, 48, 49] tokens
  let marketSegmentID ← readOptional [49, 51, 49, 48] tokens
  let noUnderlyings ← readGroup [55, 49, 49] [51, 49, 49] NoUnderlyings.members NoUnderlyings.decode tokens
  pure { applID, applSeqNum, applLastSeqNum, applResendFlag, symbol, securityID, securityIDSource, securityType, securitySubType, maturityDate, issueDate, contractMultiplier, securityDesc, maturityMonthYear, putOrCall, marketID, marketSegmentID, noUnderlyings }

theorem SecurityDefinition.decode_agrees (record : SecurityDefinition) (tokens : List Token)
    (agrees : ∀ tags ∈ SecurityDefinition.tags, select tags tokens = select tags (encodeParts record.parts)) :
    SecurityDefinition.decode tokens = some record := by
  have distinct : SecurityDefinition.tags.flatten.Nodup := by decide +kernel
  have applID := readOptional_part [49, 49, 56, 48] record.applID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have applSeqNum := readOptional_part [49, 49, 56, 49] record.applSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have applLastSeqNum := readOptional_part [49, 51, 53, 48] record.applLastSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have applResendFlag := readOptional_part [49, 51, 53, 50] record.applResendFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have securityType := readOptional_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have securitySubType := readOptional_part [55, 54, 50] record.securitySubType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have maturityDate := readOptional_part [53, 52, 49] record.maturityDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have issueDate := readOptional_part [50, 50, 53] record.issueDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have contractMultiplier := readOptional_part [50, 51, 49] record.contractMultiplier tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have securityDesc := readOptional_part [49, 48, 55] record.securityDesc tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have maturityMonthYear := readOptional_part [50, 48, 48] record.maturityMonthYear tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have putOrCall := readOptional_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have marketID := readOptional_part [49, 51, 48, 49] record.marketID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have marketSegmentID := readOptional_part [49, 51, 49, 48] record.marketSegmentID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have noUnderlyings := readGroup_part [55, 49, 49] [51, 49, 49] NoUnderlyings.members NoUnderlyings.encode NoUnderlyings.within NoUnderlyings.decode NoUnderlyings.decode_encode NoUnderlyings.led record.noUnderlyings tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  simp only [SecurityDefinition.decode, applID, applSeqNum, applLastSeqNum, applResendFlag, symbol, securityID, securityIDSource, securityType, securitySubType, maturityDate, issueDate, contractMultiplier, securityDesc, maturityMonthYear, putOrCall, marketID, marketSegmentID, noUnderlyings, some_bind] <;> rfl

structure SecurityDefinitionUpdateReport where
  applID : Option (Terminated 1)  -- tag 1180
  applSeqNum : Option (Terminated 1)  -- tag 1181
  applLastSeqNum : Option (Terminated 1)  -- tag 1350
  applResendFlag : Option (Terminated 1)  -- tag 1352
  securityUpdateAction : Terminated 1  -- tag 980
  symbol : Option (Terminated 1)  -- tag 55
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22
  securityType : Option (Terminated 1)  -- tag 167
  contractMultiplier : Option (Terminated 1)  -- tag 231
  securityDesc : Option (Terminated 1)  -- tag 107
  maturityMonthYear : Option (Terminated 1)  -- tag 200
  putOrCall : Option (Terminated 1)  -- tag 201
  noUnderlyings : List NoUnderlyings  -- tag 711

def SecurityDefinitionUpdateReport.parts (record : SecurityDefinitionUpdateReport) : List Part :=
  [Part.optional [49, 49, 56, 48] record.applID,
   Part.optional [49, 49, 56, 49] record.applSeqNum,
   Part.optional [49, 51, 53, 48] record.applLastSeqNum,
   Part.optional [49, 51, 53, 50] record.applResendFlag,
   Part.required [57, 56, 48] record.securityUpdateAction,
   Part.optional [53, 53] record.symbol,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource,
   Part.optional [49, 54, 55] record.securityType,
   Part.optional [50, 51, 49] record.contractMultiplier,
   Part.optional [49, 48, 55] record.securityDesc,
   Part.optional [50, 48, 48] record.maturityMonthYear,
   Part.optional [50, 48, 49] record.putOrCall,
   Part.group [55, 49, 49] NoUnderlyings.members NoUnderlyings.encode NoUnderlyings.within record.noUnderlyings]

def SecurityDefinitionUpdateReport.tags : List (List (List UInt8)) :=
  [[[49, 49, 56, 48]], [[49, 49, 56, 49]], [[49, 51, 53, 48]], [[49, 51, 53, 50]], [[57, 56, 48]], [[53, 53]], [[52, 56]], [[50, 50]], [[49, 54, 55]], [[50, 51, 49]], [[49, 48, 55]], [[50, 48, 48]], [[50, 48, 49]], [55, 49, 49] :: NoUnderlyings.members]

theorem SecurityDefinitionUpdateReport.shape (record : SecurityDefinitionUpdateReport) : record.parts.map Part.tags = SecurityDefinitionUpdateReport.tags := rfl

def SecurityDefinitionUpdateReport.decode (tokens : List Token) : Option SecurityDefinitionUpdateReport := do
  let applID ← readOptional [49, 49, 56, 48] tokens
  let applSeqNum ← readOptional [49, 49, 56, 49] tokens
  let applLastSeqNum ← readOptional [49, 51, 53, 48] tokens
  let applResendFlag ← readOptional [49, 51, 53, 50] tokens
  let securityUpdateAction ← readRequired [57, 56, 48] tokens
  let symbol ← readOptional [53, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let securityType ← readOptional [49, 54, 55] tokens
  let contractMultiplier ← readOptional [50, 51, 49] tokens
  let securityDesc ← readOptional [49, 48, 55] tokens
  let maturityMonthYear ← readOptional [50, 48, 48] tokens
  let putOrCall ← readOptional [50, 48, 49] tokens
  let noUnderlyings ← readGroup [55, 49, 49] [51, 49, 49] NoUnderlyings.members NoUnderlyings.decode tokens
  pure { applID, applSeqNum, applLastSeqNum, applResendFlag, securityUpdateAction, symbol, securityID, securityIDSource, securityType, contractMultiplier, securityDesc, maturityMonthYear, putOrCall, noUnderlyings }

theorem SecurityDefinitionUpdateReport.decode_agrees (record : SecurityDefinitionUpdateReport) (tokens : List Token)
    (agrees : ∀ tags ∈ SecurityDefinitionUpdateReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    SecurityDefinitionUpdateReport.decode tokens = some record := by
  have distinct : SecurityDefinitionUpdateReport.tags.flatten.Nodup := by decide +kernel
  have applID := readOptional_part [49, 49, 56, 48] record.applID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have applSeqNum := readOptional_part [49, 49, 56, 49] record.applSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have applLastSeqNum := readOptional_part [49, 51, 53, 48] record.applLastSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have applResendFlag := readOptional_part [49, 51, 53, 50] record.applResendFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have securityUpdateAction := readRequired_part [57, 56, 48] record.securityUpdateAction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have securityType := readOptional_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have contractMultiplier := readOptional_part [50, 51, 49] record.contractMultiplier tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have securityDesc := readOptional_part [49, 48, 55] record.securityDesc tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have maturityMonthYear := readOptional_part [50, 48, 48] record.maturityMonthYear tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have putOrCall := readOptional_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have noUnderlyings := readGroup_part [55, 49, 49] [51, 49, 49] NoUnderlyings.members NoUnderlyings.encode NoUnderlyings.within NoUnderlyings.decode NoUnderlyings.decode_encode NoUnderlyings.led record.noUnderlyings tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  simp only [SecurityDefinitionUpdateReport.decode, applID, applSeqNum, applLastSeqNum, applResendFlag, securityUpdateAction, symbol, securityID, securityIDSource, securityType, contractMultiplier, securityDesc, maturityMonthYear, putOrCall, noUnderlyings, some_bind] <;> rfl

structure MarketDefinition where
  applID : Option (Terminated 1)  -- tag 1180
  applSeqNum : Option (Terminated 1)  -- tag 1181
  applLastSeqNum : Option (Terminated 1)  -- tag 1350
  applResendFlag : Option (Terminated 1)  -- tag 1352
  marketReportID : Terminated 1  -- tag 1394
  marketID : Terminated 1  -- tag 1301
  marketSegmentID : Option (Terminated 1)  -- tag 1310
  marketSegmentDesc : Option (Terminated 1)  -- tag 1396

def MarketDefinition.parts (record : MarketDefinition) : List Part :=
  [Part.optional [49, 49, 56, 48] record.applID,
   Part.optional [49, 49, 56, 49] record.applSeqNum,
   Part.optional [49, 51, 53, 48] record.applLastSeqNum,
   Part.optional [49, 51, 53, 50] record.applResendFlag,
   Part.required [49, 51, 57, 52] record.marketReportID,
   Part.required [49, 51, 48, 49] record.marketID,
   Part.optional [49, 51, 49, 48] record.marketSegmentID,
   Part.optional [49, 51, 57, 54] record.marketSegmentDesc]

def MarketDefinition.tags : List (List (List UInt8)) :=
  [[[49, 49, 56, 48]], [[49, 49, 56, 49]], [[49, 51, 53, 48]], [[49, 51, 53, 50]], [[49, 51, 57, 52]], [[49, 51, 48, 49]], [[49, 51, 49, 48]], [[49, 51, 57, 54]]]

theorem MarketDefinition.shape (record : MarketDefinition) : record.parts.map Part.tags = MarketDefinition.tags := rfl

def MarketDefinition.decode (tokens : List Token) : Option MarketDefinition := do
  let applID ← readOptional [49, 49, 56, 48] tokens
  let applSeqNum ← readOptional [49, 49, 56, 49] tokens
  let applLastSeqNum ← readOptional [49, 51, 53, 48] tokens
  let applResendFlag ← readOptional [49, 51, 53, 50] tokens
  let marketReportID ← readRequired [49, 51, 57, 52] tokens
  let marketID ← readRequired [49, 51, 48, 49] tokens
  let marketSegmentID ← readOptional [49, 51, 49, 48] tokens
  let marketSegmentDesc ← readOptional [49, 51, 57, 54] tokens
  pure { applID, applSeqNum, applLastSeqNum, applResendFlag, marketReportID, marketID, marketSegmentID, marketSegmentDesc }

theorem MarketDefinition.decode_agrees (record : MarketDefinition) (tokens : List Token)
    (agrees : ∀ tags ∈ MarketDefinition.tags, select tags tokens = select tags (encodeParts record.parts)) :
    MarketDefinition.decode tokens = some record := by
  have distinct : MarketDefinition.tags.flatten.Nodup := by decide +kernel
  have applID := readOptional_part [49, 49, 56, 48] record.applID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have applSeqNum := readOptional_part [49, 49, 56, 49] record.applSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have applLastSeqNum := readOptional_part [49, 51, 53, 48] record.applLastSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have applResendFlag := readOptional_part [49, 51, 53, 50] record.applResendFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have marketReportID := readRequired_part [49, 51, 57, 52] record.marketReportID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have marketID := readRequired_part [49, 51, 48, 49] record.marketID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have marketSegmentID := readOptional_part [49, 51, 49, 48] record.marketSegmentID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have marketSegmentDesc := readOptional_part [49, 51, 57, 54] record.marketSegmentDesc tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  simp only [MarketDefinition.decode, applID, applSeqNum, applLastSeqNum, applResendFlag, marketReportID, marketID, marketSegmentID, marketSegmentDesc, some_bind] <;> rfl

structure NoOrdTypeRules where
  ordType : Terminated 1  -- tag 40

def NoOrdTypeRules.parts (record : NoOrdTypeRules) : List Part :=
  [Part.required [52, 48] record.ordType]

def NoOrdTypeRules.tags : List (List (List UInt8)) :=
  [[[52, 48]]]

theorem NoOrdTypeRules.shape (record : NoOrdTypeRules) : record.parts.map Part.tags = NoOrdTypeRules.tags := rfl

def NoOrdTypeRules.decode (tokens : List Token) : Option NoOrdTypeRules := do
  let ordType ← readRequired [52, 48] tokens
  pure { ordType }

theorem NoOrdTypeRules.decode_agrees (record : NoOrdTypeRules) (tokens : List Token)
    (agrees : ∀ tags ∈ NoOrdTypeRules.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoOrdTypeRules.decode tokens = some record := by
  have distinct : NoOrdTypeRules.tags.flatten.Nodup := by decide +kernel
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [NoOrdTypeRules.decode, ordType, some_bind] <;> rfl

def NoOrdTypeRules.members : List (List UInt8) := NoOrdTypeRules.tags.flatten

def NoOrdTypeRules.encode (entry : NoOrdTypeRules) : List Token := encodeParts entry.parts

theorem NoOrdTypeRules.decode_encode (entry : NoOrdTypeRules) : NoOrdTypeRules.decode entry.encode = some entry :=
  NoOrdTypeRules.decode_agrees entry _ (fun _ _ => rfl)

theorem NoOrdTypeRules.within (entry : NoOrdTypeRules) : ∀ token ∈ entry.encode, token.tag ∈ NoOrdTypeRules.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoOrdTypeRules.shape] at this

theorem NoOrdTypeRules.led (entry : NoOrdTypeRules) : Lead [52, 48] entry.encode :=
  lead_parts [52, 48] entry.ordType _ NoOrdTypeRules.tags.tail rfl (by decide +kernel)

structure NoTimeInForceRules where
  timeInForce : Terminated 1  -- tag 59

def NoTimeInForceRules.parts (record : NoTimeInForceRules) : List Part :=
  [Part.required [53, 57] record.timeInForce]

def NoTimeInForceRules.tags : List (List (List UInt8)) :=
  [[[53, 57]]]

theorem NoTimeInForceRules.shape (record : NoTimeInForceRules) : record.parts.map Part.tags = NoTimeInForceRules.tags := rfl

def NoTimeInForceRules.decode (tokens : List Token) : Option NoTimeInForceRules := do
  let timeInForce ← readRequired [53, 57] tokens
  pure { timeInForce }

theorem NoTimeInForceRules.decode_agrees (record : NoTimeInForceRules) (tokens : List Token)
    (agrees : ∀ tags ∈ NoTimeInForceRules.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoTimeInForceRules.decode tokens = some record := by
  have distinct : NoTimeInForceRules.tags.flatten.Nodup := by decide +kernel
  have timeInForce := readRequired_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [NoTimeInForceRules.decode, timeInForce, some_bind] <;> rfl

def NoTimeInForceRules.members : List (List UInt8) := NoTimeInForceRules.tags.flatten

def NoTimeInForceRules.encode (entry : NoTimeInForceRules) : List Token := encodeParts entry.parts

theorem NoTimeInForceRules.decode_encode (entry : NoTimeInForceRules) : NoTimeInForceRules.decode entry.encode = some entry :=
  NoTimeInForceRules.decode_agrees entry _ (fun _ _ => rfl)

theorem NoTimeInForceRules.within (entry : NoTimeInForceRules) : ∀ token ∈ entry.encode, token.tag ∈ NoTimeInForceRules.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoTimeInForceRules.shape] at this

theorem NoTimeInForceRules.led (entry : NoTimeInForceRules) : Lead [53, 57] entry.encode :=
  lead_parts [53, 57] entry.timeInForce _ NoTimeInForceRules.tags.tail rfl (by decide +kernel)

structure NoMatchRules where
  matchAlgorithm : Terminated 1  -- tag 1142
  matchType : Option (Terminated 1)  -- tag 574
  exSessionStateNumber : Option (Terminated 1)  -- tag 28032

def NoMatchRules.parts (record : NoMatchRules) : List Part :=
  [Part.required [49, 49, 52, 50] record.matchAlgorithm,
   Part.optional [53, 55, 52] record.matchType,
   Part.optional [50, 56, 48, 51, 50] record.exSessionStateNumber]

def NoMatchRules.tags : List (List (List UInt8)) :=
  [[[49, 49, 52, 50]], [[53, 55, 52]], [[50, 56, 48, 51, 50]]]

theorem NoMatchRules.shape (record : NoMatchRules) : record.parts.map Part.tags = NoMatchRules.tags := rfl

def NoMatchRules.decode (tokens : List Token) : Option NoMatchRules := do
  let matchAlgorithm ← readRequired [49, 49, 52, 50] tokens
  let matchType ← readOptional [53, 55, 52] tokens
  let exSessionStateNumber ← readOptional [50, 56, 48, 51, 50] tokens
  pure { matchAlgorithm, matchType, exSessionStateNumber }

theorem NoMatchRules.decode_agrees (record : NoMatchRules) (tokens : List Token)
    (agrees : ∀ tags ∈ NoMatchRules.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoMatchRules.decode tokens = some record := by
  have distinct : NoMatchRules.tags.flatten.Nodup := by decide +kernel
  have matchAlgorithm := readRequired_part [49, 49, 52, 50] record.matchAlgorithm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have matchType := readOptional_part [53, 55, 52] record.matchType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have exSessionStateNumber := readOptional_part [50, 56, 48, 51, 50] record.exSessionStateNumber tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [NoMatchRules.decode, matchAlgorithm, matchType, exSessionStateNumber, some_bind] <;> rfl

def NoMatchRules.members : List (List UInt8) := NoMatchRules.tags.flatten

def NoMatchRules.encode (entry : NoMatchRules) : List Token := encodeParts entry.parts

theorem NoMatchRules.decode_encode (entry : NoMatchRules) : NoMatchRules.decode entry.encode = some entry :=
  NoMatchRules.decode_agrees entry _ (fun _ _ => rfl)

theorem NoMatchRules.within (entry : NoMatchRules) : ∀ token ∈ entry.encode, token.tag ∈ NoMatchRules.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoMatchRules.shape] at this

theorem NoMatchRules.led (entry : NoMatchRules) : Lead [49, 49, 52, 50] entry.encode :=
  lead_parts [49, 49, 52, 50] entry.matchAlgorithm _ NoMatchRules.tags.tail rfl (by decide +kernel)

structure NoTradingSessions where
  tradingSessionID : Terminated 1  -- tag 336
  tradingSessionDesc : Option (Terminated 1)  -- tag 1326
  tradSesStatus : Option (Terminated 1)  -- tag 340
  noOrdTypeRules : List NoOrdTypeRules  -- tag 1237
  noTimeInForceRules : List NoTimeInForceRules  -- tag 1239
  noMatchRules : List NoMatchRules  -- tag 1235

def NoTradingSessions.parts (record : NoTradingSessions) : List Part :=
  [Part.required [51, 51, 54] record.tradingSessionID,
   Part.optional [49, 51, 50, 54] record.tradingSessionDesc,
   Part.optional [51, 52, 48] record.tradSesStatus,
   Part.group [49, 50, 51, 55] NoOrdTypeRules.members NoOrdTypeRules.encode NoOrdTypeRules.within record.noOrdTypeRules,
   Part.group [49, 50, 51, 57] NoTimeInForceRules.members NoTimeInForceRules.encode NoTimeInForceRules.within record.noTimeInForceRules,
   Part.group [49, 50, 51, 53] NoMatchRules.members NoMatchRules.encode NoMatchRules.within record.noMatchRules]

def NoTradingSessions.tags : List (List (List UInt8)) :=
  [[[51, 51, 54]], [[49, 51, 50, 54]], [[51, 52, 48]], [49, 50, 51, 55] :: NoOrdTypeRules.members, [49, 50, 51, 57] :: NoTimeInForceRules.members, [49, 50, 51, 53] :: NoMatchRules.members]

theorem NoTradingSessions.shape (record : NoTradingSessions) : record.parts.map Part.tags = NoTradingSessions.tags := rfl

def NoTradingSessions.decode (tokens : List Token) : Option NoTradingSessions := do
  let tradingSessionID ← readRequired [51, 51, 54] tokens
  let tradingSessionDesc ← readOptional [49, 51, 50, 54] tokens
  let tradSesStatus ← readOptional [51, 52, 48] tokens
  let noOrdTypeRules ← readGroup [49, 50, 51, 55] [52, 48] NoOrdTypeRules.members NoOrdTypeRules.decode tokens
  let noTimeInForceRules ← readGroup [49, 50, 51, 57] [53, 57] NoTimeInForceRules.members NoTimeInForceRules.decode tokens
  let noMatchRules ← readGroup [49, 50, 51, 53] [49, 49, 52, 50] NoMatchRules.members NoMatchRules.decode tokens
  pure { tradingSessionID, tradingSessionDesc, tradSesStatus, noOrdTypeRules, noTimeInForceRules, noMatchRules }

theorem NoTradingSessions.decode_agrees (record : NoTradingSessions) (tokens : List Token)
    (agrees : ∀ tags ∈ NoTradingSessions.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoTradingSessions.decode tokens = some record := by
  have distinct : NoTradingSessions.tags.flatten.Nodup := by decide +kernel
  have tradingSessionID := readRequired_part [51, 51, 54] record.tradingSessionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have tradingSessionDesc := readOptional_part [49, 51, 50, 54] record.tradingSessionDesc tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have tradSesStatus := readOptional_part [51, 52, 48] record.tradSesStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have noOrdTypeRules := readGroup_part [49, 50, 51, 55] [52, 48] NoOrdTypeRules.members NoOrdTypeRules.encode NoOrdTypeRules.within NoOrdTypeRules.decode NoOrdTypeRules.decode_encode NoOrdTypeRules.led record.noOrdTypeRules tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have noTimeInForceRules := readGroup_part [49, 50, 51, 57] [53, 57] NoTimeInForceRules.members NoTimeInForceRules.encode NoTimeInForceRules.within NoTimeInForceRules.decode NoTimeInForceRules.decode_encode NoTimeInForceRules.led record.noTimeInForceRules tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have noMatchRules := readGroup_part [49, 50, 51, 53] [49, 49, 52, 50] NoMatchRules.members NoMatchRules.encode NoMatchRules.within NoMatchRules.decode NoMatchRules.decode_encode NoMatchRules.led record.noMatchRules tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  simp only [NoTradingSessions.decode, tradingSessionID, tradingSessionDesc, tradSesStatus, noOrdTypeRules, noTimeInForceRules, noMatchRules, some_bind] <;> rfl

def NoTradingSessions.members : List (List UInt8) := NoTradingSessions.tags.flatten

def NoTradingSessions.encode (entry : NoTradingSessions) : List Token := encodeParts entry.parts

theorem NoTradingSessions.decode_encode (entry : NoTradingSessions) : NoTradingSessions.decode entry.encode = some entry :=
  NoTradingSessions.decode_agrees entry _ (fun _ _ => rfl)

theorem NoTradingSessions.within (entry : NoTradingSessions) : ∀ token ∈ entry.encode, token.tag ∈ NoTradingSessions.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoTradingSessions.shape] at this

theorem NoTradingSessions.led (entry : NoTradingSessions) : Lead [51, 51, 54] entry.encode :=
  lead_parts [51, 51, 54] entry.tradingSessionID _ NoTradingSessions.tags.tail rfl (by decide +kernel)

structure TradingSessionList where
  applID : Option (Terminated 1)  -- tag 1180
  applSeqNum : Option (Terminated 1)  -- tag 1181
  applLastSeqNum : Option (Terminated 1)  -- tag 1350
  applResendFlag : Option (Terminated 1)  -- tag 1352
  noTradingSessions : List NoTradingSessions  -- tag 386

def TradingSessionList.parts (record : TradingSessionList) : List Part :=
  [Part.optional [49, 49, 56, 48] record.applID,
   Part.optional [49, 49, 56, 49] record.applSeqNum,
   Part.optional [49, 51, 53, 48] record.applLastSeqNum,
   Part.optional [49, 51, 53, 50] record.applResendFlag,
   Part.group [51, 56, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within record.noTradingSessions]

def TradingSessionList.tags : List (List (List UInt8)) :=
  [[[49, 49, 56, 48]], [[49, 49, 56, 49]], [[49, 51, 53, 48]], [[49, 51, 53, 50]], [51, 56, 54] :: NoTradingSessions.members]

theorem TradingSessionList.shape (record : TradingSessionList) : record.parts.map Part.tags = TradingSessionList.tags := rfl

def TradingSessionList.decode (tokens : List Token) : Option TradingSessionList := do
  let applID ← readOptional [49, 49, 56, 48] tokens
  let applSeqNum ← readOptional [49, 49, 56, 49] tokens
  let applLastSeqNum ← readOptional [49, 51, 53, 48] tokens
  let applResendFlag ← readOptional [49, 51, 53, 50] tokens
  let noTradingSessions ← readGroup [51, 56, 54] [51, 51, 54] NoTradingSessions.members NoTradingSessions.decode tokens
  pure { applID, applSeqNum, applLastSeqNum, applResendFlag, noTradingSessions }

theorem TradingSessionList.decode_agrees (record : TradingSessionList) (tokens : List Token)
    (agrees : ∀ tags ∈ TradingSessionList.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TradingSessionList.decode tokens = some record := by
  have distinct : TradingSessionList.tags.flatten.Nodup := by decide +kernel
  have applID := readOptional_part [49, 49, 56, 48] record.applID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have applSeqNum := readOptional_part [49, 49, 56, 49] record.applSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have applLastSeqNum := readOptional_part [49, 51, 53, 48] record.applLastSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have applResendFlag := readOptional_part [49, 51, 53, 50] record.applResendFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have noTradingSessions := readGroup_part [51, 56, 54] [51, 51, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within NoTradingSessions.decode NoTradingSessions.decode_encode NoTradingSessions.led record.noTradingSessions tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [TradingSessionList.decode, applID, applSeqNum, applLastSeqNum, applResendFlag, noTradingSessions, some_bind] <;> rfl

inductive Message where
  | logon (header : Header) (r0 : Logon)
  | logout (header : Header) (r0 : Logout)
  | sequenceReset (header : Header) (r0 : SequenceReset)
  | resendRequest (header : Header) (r0 : ResendRequest)
  | heartbeat (header : Header) (r0 : Heartbeat)
  | testRequest (header : Header) (r0 : TestRequest)
  | reject (header : Header) (r0 : Reject)
  | applicationMessageRequestAck (header : Header) (r0 : ApplicationMessageRequestAck)
  | securityDefinition (header : Header) (r0 : SecurityDefinition)
  | securityDefinitionUpdateReport (header : Header) (r0 : SecurityDefinitionUpdateReport)
  | marketDefinition (header : Header) (r0 : MarketDefinition)
  | tradingSessionList (header : Header) (r0 : TradingSessionList)

def Message.tokens : Message → List Token
  | .logon header r0 => ⟨[51, 53], ⟨[65], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logout header r0 => ⟨[51, 53], ⟨[53], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .sequenceReset header r0 => ⟨[51, 53], ⟨[52], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .resendRequest header r0 => ⟨[51, 53], ⟨[50], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .heartbeat header r0 => ⟨[51, 53], ⟨[48], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .testRequest header r0 => ⟨[51, 53], ⟨[49], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .reject header r0 => ⟨[51, 53], ⟨[51], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .applicationMessageRequestAck header r0 => ⟨[51, 53], ⟨[66, 88], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .securityDefinition header r0 => ⟨[51, 53], ⟨[100], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .securityDefinitionUpdateReport header r0 => ⟨[51, 53], ⟨[66, 80], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .marketDefinition header r0 => ⟨[51, 53], ⟨[66, 85], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .tradingSessionList header r0 => ⟨[51, 53], ⟨[66, 74], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)

def Message.decode : List Token → Option Message
  | [] => none
  | token :: rest =>
    if token.tag = [51, 53] then
      if token.value.val = [65] then
        if known (Header.tags ++ Logon.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Logon.decode rest
          pure (.logon header r0)
        else none
      else if token.value.val = [53] then
        if known (Header.tags ++ Logout.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Logout.decode rest
          pure (.logout header r0)
        else none
      else if token.value.val = [52] then
        if known (Header.tags ++ SequenceReset.tags) rest then do
          let header ← Header.decode rest
          let r0 ← SequenceReset.decode rest
          pure (.sequenceReset header r0)
        else none
      else if token.value.val = [50] then
        if known (Header.tags ++ ResendRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← ResendRequest.decode rest
          pure (.resendRequest header r0)
        else none
      else if token.value.val = [48] then
        if known (Header.tags ++ Heartbeat.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Heartbeat.decode rest
          pure (.heartbeat header r0)
        else none
      else if token.value.val = [49] then
        if known (Header.tags ++ TestRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← TestRequest.decode rest
          pure (.testRequest header r0)
        else none
      else if token.value.val = [51] then
        if known (Header.tags ++ Reject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Reject.decode rest
          pure (.reject header r0)
        else none
      else if token.value.val = [66, 88] then
        if known (Header.tags ++ ApplicationMessageRequestAck.tags) rest then do
          let header ← Header.decode rest
          let r0 ← ApplicationMessageRequestAck.decode rest
          pure (.applicationMessageRequestAck header r0)
        else none
      else if token.value.val = [100] then
        if known (Header.tags ++ SecurityDefinition.tags) rest then do
          let header ← Header.decode rest
          let r0 ← SecurityDefinition.decode rest
          pure (.securityDefinition header r0)
        else none
      else if token.value.val = [66, 80] then
        if known (Header.tags ++ SecurityDefinitionUpdateReport.tags) rest then do
          let header ← Header.decode rest
          let r0 ← SecurityDefinitionUpdateReport.decode rest
          pure (.securityDefinitionUpdateReport header r0)
        else none
      else if token.value.val = [66, 85] then
        if known (Header.tags ++ MarketDefinition.tags) rest then do
          let header ← Header.decode rest
          let r0 ← MarketDefinition.decode rest
          pure (.marketDefinition header r0)
        else none
      else if token.value.val = [66, 74] then
        if known (Header.tags ++ TradingSessionList.tags) rest then do
          let header ← Header.decode rest
          let r0 ← TradingSessionList.decode rest
          pure (.tradingSessionList header r0)
        else none
      else none
    else none

theorem Message.decode_logon (header : Header) (r0 : Logon) :
    Message.decode (Message.tokens (.logon header r0)) = some (.logon header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (Logon.tags) rfl rfl (by decide +kernel))
  have c1 := Logon.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (Logon.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ Logon.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, some_bind] <;> rfl

theorem Message.decode_logout (header : Header) (r0 : Logout) :
    Message.decode (Message.tokens (.logout header r0)) = some (.logout header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (Logout.tags) rfl rfl (by decide +kernel))
  have c1 := Logout.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (Logout.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ Logout.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_sequenceReset (header : Header) (r0 : SequenceReset) :
    Message.decode (Message.tokens (.sequenceReset header r0)) = some (.sequenceReset header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (SequenceReset.tags) rfl rfl (by decide +kernel))
  have c1 := SequenceReset.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (SequenceReset.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ SequenceReset.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_resendRequest (header : Header) (r0 : ResendRequest) :
    Message.decode (Message.tokens (.resendRequest header r0)) = some (.resendRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (ResendRequest.tags) rfl rfl (by decide +kernel))
  have c1 := ResendRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (ResendRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ ResendRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_heartbeat (header : Header) (r0 : Heartbeat) :
    Message.decode (Message.tokens (.heartbeat header r0)) = some (.heartbeat header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (Heartbeat.tags) rfl rfl (by decide +kernel))
  have c1 := Heartbeat.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (Heartbeat.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ Heartbeat.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_testRequest (header : Header) (r0 : TestRequest) :
    Message.decode (Message.tokens (.testRequest header r0)) = some (.testRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (TestRequest.tags) rfl rfl (by decide +kernel))
  have c1 := TestRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (TestRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ TestRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_reject (header : Header) (r0 : Reject) :
    Message.decode (Message.tokens (.reject header r0)) = some (.reject header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (Reject.tags) rfl rfl (by decide +kernel))
  have c1 := Reject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (Reject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ Reject.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_applicationMessageRequestAck (header : Header) (r0 : ApplicationMessageRequestAck) :
    Message.decode (Message.tokens (.applicationMessageRequestAck header r0)) = some (.applicationMessageRequestAck header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (ApplicationMessageRequestAck.tags) rfl rfl (by decide +kernel))
  have c1 := ApplicationMessageRequestAck.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (ApplicationMessageRequestAck.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ ApplicationMessageRequestAck.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_securityDefinition (header : Header) (r0 : SecurityDefinition) :
    Message.decode (Message.tokens (.securityDefinition header r0)) = some (.securityDefinition header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (SecurityDefinition.tags) rfl rfl (by decide +kernel))
  have c1 := SecurityDefinition.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (SecurityDefinition.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ SecurityDefinition.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_securityDefinitionUpdateReport (header : Header) (r0 : SecurityDefinitionUpdateReport) :
    Message.decode (Message.tokens (.securityDefinitionUpdateReport header r0)) = some (.securityDefinitionUpdateReport header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (SecurityDefinitionUpdateReport.tags) rfl rfl (by decide +kernel))
  have c1 := SecurityDefinitionUpdateReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (SecurityDefinitionUpdateReport.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ SecurityDefinitionUpdateReport.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_marketDefinition (header : Header) (r0 : MarketDefinition) :
    Message.decode (Message.tokens (.marketDefinition header r0)) = some (.marketDefinition header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (MarketDefinition.tags) rfl rfl (by decide +kernel))
  have c1 := MarketDefinition.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (MarketDefinition.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ MarketDefinition.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tradingSessionList (header : Header) (r0 : TradingSessionList) :
    Message.decode (Message.tokens (.tradingSessionList header r0)) = some (.tradingSessionList header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (TradingSessionList.tags) rfl rfl (by decide +kernel))
  have c1 := TradingSessionList.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (TradingSessionList.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ TradingSessionList.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | logon header r0 => exact Message.decode_logon header r0
  | logout header r0 => exact Message.decode_logout header r0
  | sequenceReset header r0 => exact Message.decode_sequenceReset header r0
  | resendRequest header r0 => exact Message.decode_resendRequest header r0
  | heartbeat header r0 => exact Message.decode_heartbeat header r0
  | testRequest header r0 => exact Message.decode_testRequest header r0
  | reject header r0 => exact Message.decode_reject header r0
  | applicationMessageRequestAck header r0 => exact Message.decode_applicationMessageRequestAck header r0
  | securityDefinition header r0 => exact Message.decode_securityDefinition header r0
  | securityDefinitionUpdateReport header r0 => exact Message.decode_securityDefinitionUpdateReport header r0
  | marketDefinition header r0 => exact Message.decode_marketDefinition header r0
  | tradingSessionList header r0 => exact Message.decode_tradingSessionList header r0

def Message.encode (message : Message) : List UInt8 := encodeTokens message.tokens

def Message.decodeBytes (bytes : List UInt8) : Option Message := do
  let tokens ← decodeTokens bytes.length bytes
  Message.decode tokens

theorem Message.decodeBytes_logon (header : Header) (r0 : Logon) :
    Message.decodeBytes (Message.encode (.logon header r0)) = some (.logon header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[65], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ Logon.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_logon header r0

theorem Message.decodeBytes_logout (header : Header) (r0 : Logout) :
    Message.decodeBytes (Message.encode (.logout header r0)) = some (.logout header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[53], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ Logout.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_logout header r0

theorem Message.decodeBytes_sequenceReset (header : Header) (r0 : SequenceReset) :
    Message.decodeBytes (Message.encode (.sequenceReset header r0)) = some (.sequenceReset header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[52], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ SequenceReset.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_sequenceReset header r0

theorem Message.decodeBytes_resendRequest (header : Header) (r0 : ResendRequest) :
    Message.decodeBytes (Message.encode (.resendRequest header r0)) = some (.resendRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[50], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ ResendRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_resendRequest header r0

theorem Message.decodeBytes_heartbeat (header : Header) (r0 : Heartbeat) :
    Message.decodeBytes (Message.encode (.heartbeat header r0)) = some (.heartbeat header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[48], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ Heartbeat.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_heartbeat header r0

theorem Message.decodeBytes_testRequest (header : Header) (r0 : TestRequest) :
    Message.decodeBytes (Message.encode (.testRequest header r0)) = some (.testRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[49], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ TestRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_testRequest header r0

theorem Message.decodeBytes_reject (header : Header) (r0 : Reject) :
    Message.decodeBytes (Message.encode (.reject header r0)) = some (.reject header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[51], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ Reject.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_reject header r0

theorem Message.decodeBytes_applicationMessageRequestAck (header : Header) (r0 : ApplicationMessageRequestAck) :
    Message.decodeBytes (Message.encode (.applicationMessageRequestAck header r0)) = some (.applicationMessageRequestAck header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[66, 88], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ ApplicationMessageRequestAck.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_applicationMessageRequestAck header r0

theorem Message.decodeBytes_securityDefinition (header : Header) (r0 : SecurityDefinition) :
    Message.decodeBytes (Message.encode (.securityDefinition header r0)) = some (.securityDefinition header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[100], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ SecurityDefinition.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_securityDefinition header r0

theorem Message.decodeBytes_securityDefinitionUpdateReport (header : Header) (r0 : SecurityDefinitionUpdateReport) :
    Message.decodeBytes (Message.encode (.securityDefinitionUpdateReport header r0)) = some (.securityDefinitionUpdateReport header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[66, 80], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ SecurityDefinitionUpdateReport.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_securityDefinitionUpdateReport header r0

theorem Message.decodeBytes_marketDefinition (header : Header) (r0 : MarketDefinition) :
    Message.decodeBytes (Message.encode (.marketDefinition header r0)) = some (.marketDefinition header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[66, 85], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ MarketDefinition.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_marketDefinition header r0

theorem Message.decodeBytes_tradingSessionList (header : Header) (r0 : TradingSessionList) :
    Message.decodeBytes (Message.encode (.tradingSessionList header r0)) = some (.tradingSessionList header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[66, 74], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ TradingSessionList.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_tradingSessionList header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | logon header r0 => exact Message.decodeBytes_logon header r0
  | logout header r0 => exact Message.decodeBytes_logout header r0
  | sequenceReset header r0 => exact Message.decodeBytes_sequenceReset header r0
  | resendRequest header r0 => exact Message.decodeBytes_resendRequest header r0
  | heartbeat header r0 => exact Message.decodeBytes_heartbeat header r0
  | testRequest header r0 => exact Message.decodeBytes_testRequest header r0
  | reject header r0 => exact Message.decodeBytes_reject header r0
  | applicationMessageRequestAck header r0 => exact Message.decodeBytes_applicationMessageRequestAck header r0
  | securityDefinition header r0 => exact Message.decodeBytes_securityDefinition header r0
  | securityDefinitionUpdateReport header r0 => exact Message.decodeBytes_securityDefinitionUpdateReport header r0
  | marketDefinition header r0 => exact Message.decodeBytes_marketDefinition header r0
  | tradingSessionList header r0 => exact Message.decodeBytes_tradingSessionList header r0

/-- BeginString as the venue fixes it: FIXT.1.1 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 84, 46, 49, 46, 49, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.SgxTitandtReferencedataFixV08Exchange
