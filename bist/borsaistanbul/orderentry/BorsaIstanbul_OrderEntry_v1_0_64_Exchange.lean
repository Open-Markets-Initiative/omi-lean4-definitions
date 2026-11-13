import Wire

/-!
# Borsa İstanbul A.Ş.  v1.0.64, Exchange messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.BistBorsaistanbulOrderentryFixV1064Exchange

structure Header where
  senderCompID : Terminated 1  -- tag 49
  targetCompID : Terminated 1  -- tag 56
  msgSeqNum : Terminated 1  -- tag 34
  sendingTime : Terminated 1  -- tag 52
  possDupFlag : Terminated 1  -- tag 43
  possResend : Terminated 1  -- tag 97
  origSendingTime : Terminated 1  -- tag 122

def Header.parts (record : Header) : List Part :=
  [Part.required [52, 57] record.senderCompID,
   Part.required [53, 54] record.targetCompID,
   Part.required [51, 52] record.msgSeqNum,
   Part.required [53, 50] record.sendingTime,
   Part.required [52, 51] record.possDupFlag,
   Part.required [57, 55] record.possResend,
   Part.required [49, 50, 50] record.origSendingTime]

def Header.tags : List (List (List UInt8)) :=
  [[[52, 57]], [[53, 54]], [[51, 52]], [[53, 50]], [[52, 51]], [[57, 55]], [[49, 50, 50]]]

theorem Header.shape (record : Header) : record.parts.map Part.tags = Header.tags := rfl

def Header.decode (tokens : List Token) : Option Header := do
  let senderCompID ← readRequired [52, 57] tokens
  let targetCompID ← readRequired [53, 54] tokens
  let msgSeqNum ← readRequired [51, 52] tokens
  let sendingTime ← readRequired [53, 50] tokens
  let possDupFlag ← readRequired [52, 51] tokens
  let possResend ← readRequired [57, 55] tokens
  let origSendingTime ← readRequired [49, 50, 50] tokens
  pure { senderCompID, targetCompID, msgSeqNum, sendingTime, possDupFlag, possResend, origSendingTime }

theorem Header.decode_agrees (record : Header) (tokens : List Token)
    (agrees : ∀ tags ∈ Header.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Header.decode tokens = some record := by
  have distinct : Header.tags.flatten.Nodup := by decide +kernel
  have senderCompID := readRequired_part [52, 57] record.senderCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have targetCompID := readRequired_part [53, 54] record.targetCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have msgSeqNum := readRequired_part [51, 52] record.msgSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have sendingTime := readRequired_part [53, 50] record.sendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have possDupFlag := readRequired_part [52, 51] record.possDupFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have possResend := readRequired_part [57, 55] record.possResend tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have origSendingTime := readRequired_part [49, 50, 50] record.origSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  simp only [Header.decode, senderCompID, targetCompID, msgSeqNum, sendingTime, possDupFlag, possResend, origSendingTime, some_bind] <;> rfl

structure Logon where
  encryptMethod : Terminated 1  -- tag 98
  resetSeqNumFlag : Option (Terminated 1)  -- tag 141
  heartBtInt : Terminated 1  -- tag 108
  username : Terminated 1  -- tag 553
  password : Terminated 1  -- tag 554
  newPassword : Option (Terminated 1)  -- tag 925
  defaultApplVerID : Terminated 1  -- tag 1137
  sessionStatus : Terminated 1  -- tag 1409
  daysToPwdExpiry : Option (Terminated 1)  -- tag 20002

def Logon.parts (record : Logon) : List Part :=
  [Part.required [57, 56] record.encryptMethod,
   Part.optional [49, 52, 49] record.resetSeqNumFlag,
   Part.required [49, 48, 56] record.heartBtInt,
   Part.required [53, 53, 51] record.username,
   Part.required [53, 53, 52] record.password,
   Part.optional [57, 50, 53] record.newPassword,
   Part.required [49, 49, 51, 55] record.defaultApplVerID,
   Part.required [49, 52, 48, 57] record.sessionStatus,
   Part.optional [50, 48, 48, 48, 50] record.daysToPwdExpiry]

def Logon.tags : List (List (List UInt8)) :=
  [[[57, 56]], [[49, 52, 49]], [[49, 48, 56]], [[53, 53, 51]], [[53, 53, 52]], [[57, 50, 53]], [[49, 49, 51, 55]], [[49, 52, 48, 57]], [[50, 48, 48, 48, 50]]]

theorem Logon.shape (record : Logon) : record.parts.map Part.tags = Logon.tags := rfl

def Logon.decode (tokens : List Token) : Option Logon := do
  let encryptMethod ← readRequired [57, 56] tokens
  let resetSeqNumFlag ← readOptional [49, 52, 49] tokens
  let heartBtInt ← readRequired [49, 48, 56] tokens
  let username ← readRequired [53, 53, 51] tokens
  let password ← readRequired [53, 53, 52] tokens
  let newPassword ← readOptional [57, 50, 53] tokens
  let defaultApplVerID ← readRequired [49, 49, 51, 55] tokens
  let sessionStatus ← readRequired [49, 52, 48, 57] tokens
  let daysToPwdExpiry ← readOptional [50, 48, 48, 48, 50] tokens
  pure { encryptMethod, resetSeqNumFlag, heartBtInt, username, password, newPassword, defaultApplVerID, sessionStatus, daysToPwdExpiry }

theorem Logon.decode_agrees (record : Logon) (tokens : List Token)
    (agrees : ∀ tags ∈ Logon.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Logon.decode tokens = some record := by
  have distinct : Logon.tags.flatten.Nodup := by decide +kernel
  have encryptMethod := readRequired_part [57, 56] record.encryptMethod tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have resetSeqNumFlag := readOptional_part [49, 52, 49] record.resetSeqNumFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have heartBtInt := readRequired_part [49, 48, 56] record.heartBtInt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have username := readRequired_part [53, 53, 51] record.username tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have password := readRequired_part [53, 53, 52] record.password tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have newPassword := readOptional_part [57, 50, 53] record.newPassword tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have defaultApplVerID := readRequired_part [49, 49, 51, 55] record.defaultApplVerID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have sessionStatus := readRequired_part [49, 52, 48, 57] record.sessionStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have daysToPwdExpiry := readOptional_part [50, 48, 48, 48, 50] record.daysToPwdExpiry tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  simp only [Logon.decode, encryptMethod, resetSeqNumFlag, heartBtInt, username, password, newPassword, defaultApplVerID, sessionStatus, daysToPwdExpiry, some_bind] <;> rfl

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
  beginSeqNo : Terminated 1  -- tag 7
  endSeqNo : Terminated 1  -- tag 16

def SequenceReset.parts (record : SequenceReset) : List Part :=
  [Part.optional [49, 50, 51] record.gapFillFlag,
   Part.required [51, 54] record.newSeqNo,
   Part.required [55] record.beginSeqNo,
   Part.required [49, 54] record.endSeqNo]

def SequenceReset.tags : List (List (List UInt8)) :=
  [[[49, 50, 51]], [[51, 54]], [[55]], [[49, 54]]]

theorem SequenceReset.shape (record : SequenceReset) : record.parts.map Part.tags = SequenceReset.tags := rfl

def SequenceReset.decode (tokens : List Token) : Option SequenceReset := do
  let gapFillFlag ← readOptional [49, 50, 51] tokens
  let newSeqNo ← readRequired [51, 54] tokens
  let beginSeqNo ← readRequired [55] tokens
  let endSeqNo ← readRequired [49, 54] tokens
  pure { gapFillFlag, newSeqNo, beginSeqNo, endSeqNo }

theorem SequenceReset.decode_agrees (record : SequenceReset) (tokens : List Token)
    (agrees : ∀ tags ∈ SequenceReset.tags, select tags tokens = select tags (encodeParts record.parts)) :
    SequenceReset.decode tokens = some record := by
  have distinct : SequenceReset.tags.flatten.Nodup := by decide +kernel
  have gapFillFlag := readOptional_part [49, 50, 51] record.gapFillFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have newSeqNo := readRequired_part [51, 54] record.newSeqNo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have beginSeqNo := readRequired_part [55] record.beginSeqNo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have endSeqNo := readRequired_part [49, 54] record.endSeqNo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [SequenceReset.decode, gapFillFlag, newSeqNo, beginSeqNo, endSeqNo, some_bind] <;> rfl

structure Reject where
  refSeqNum : Terminated 1  -- tag 45
  refTagID : Option (Terminated 1)  -- tag 371
  refMsgType : Option (Terminated 1)  -- tag 372
  sessionRejectReason : Terminated 1  -- tag 373
  text : Option (Terminated 1)  -- tag 58

def Reject.parts (record : Reject) : List Part :=
  [Part.required [52, 53] record.refSeqNum,
   Part.optional [51, 55, 49] record.refTagID,
   Part.optional [51, 55, 50] record.refMsgType,
   Part.required [51, 55, 51] record.sessionRejectReason,
   Part.optional [53, 56] record.text]

def Reject.tags : List (List (List UInt8)) :=
  [[[52, 53]], [[51, 55, 49]], [[51, 55, 50]], [[51, 55, 51]], [[53, 56]]]

theorem Reject.shape (record : Reject) : record.parts.map Part.tags = Reject.tags := rfl

def Reject.decode (tokens : List Token) : Option Reject := do
  let refSeqNum ← readRequired [52, 53] tokens
  let refTagID ← readOptional [51, 55, 49] tokens
  let refMsgType ← readOptional [51, 55, 50] tokens
  let sessionRejectReason ← readRequired [51, 55, 51] tokens
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
  have sessionRejectReason := readRequired_part [51, 55, 51] record.sessionRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [Reject.decode, refSeqNum, refTagID, refMsgType, sessionRejectReason, text, some_bind] <;> rfl

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

structure UserResponse where
  userRequestID : Terminated 1  -- tag 923
  username : Terminated 1  -- tag 553
  userRequestType : Terminated 1  -- tag 924
  userStatus : Terminated 1  -- tag 926
  userStatusText : Option (Terminated 1)  -- tag 927

def UserResponse.parts (record : UserResponse) : List Part :=
  [Part.required [57, 50, 51] record.userRequestID,
   Part.required [53, 53, 51] record.username,
   Part.required [57, 50, 52] record.userRequestType,
   Part.required [57, 50, 54] record.userStatus,
   Part.optional [57, 50, 55] record.userStatusText]

def UserResponse.tags : List (List (List UInt8)) :=
  [[[57, 50, 51]], [[53, 53, 51]], [[57, 50, 52]], [[57, 50, 54]], [[57, 50, 55]]]

theorem UserResponse.shape (record : UserResponse) : record.parts.map Part.tags = UserResponse.tags := rfl

def UserResponse.decode (tokens : List Token) : Option UserResponse := do
  let userRequestID ← readRequired [57, 50, 51] tokens
  let username ← readRequired [53, 53, 51] tokens
  let userRequestType ← readRequired [57, 50, 52] tokens
  let userStatus ← readRequired [57, 50, 54] tokens
  let userStatusText ← readOptional [57, 50, 55] tokens
  pure { userRequestID, username, userRequestType, userStatus, userStatusText }

theorem UserResponse.decode_agrees (record : UserResponse) (tokens : List Token)
    (agrees : ∀ tags ∈ UserResponse.tags, select tags tokens = select tags (encodeParts record.parts)) :
    UserResponse.decode tokens = some record := by
  have distinct : UserResponse.tags.flatten.Nodup := by decide +kernel
  have userRequestID := readRequired_part [57, 50, 51] record.userRequestID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have username := readRequired_part [53, 53, 51] record.username tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have userRequestType := readRequired_part [57, 50, 52] record.userRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have userStatus := readRequired_part [57, 50, 54] record.userStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have userStatusText := readOptional_part [57, 50, 55] record.userStatusText tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [UserResponse.decode, userRequestID, username, userRequestType, userStatus, userStatusText, some_bind] <;> rfl

structure NoUsernames where
  username : Terminated 1  -- tag 553

def NoUsernames.parts (record : NoUsernames) : List Part :=
  [Part.required [53, 53, 51] record.username]

def NoUsernames.tags : List (List (List UInt8)) :=
  [[[53, 53, 51]]]

theorem NoUsernames.shape (record : NoUsernames) : record.parts.map Part.tags = NoUsernames.tags := rfl

def NoUsernames.decode (tokens : List Token) : Option NoUsernames := do
  let username ← readRequired [53, 53, 51] tokens
  pure { username }

theorem NoUsernames.decode_agrees (record : NoUsernames) (tokens : List Token)
    (agrees : ∀ tags ∈ NoUsernames.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoUsernames.decode tokens = some record := by
  have distinct : NoUsernames.tags.flatten.Nodup := by decide +kernel
  have username := readRequired_part [53, 53, 51] record.username tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [NoUsernames.decode, username, some_bind] <;> rfl

def NoUsernames.members : List (List UInt8) := NoUsernames.tags.flatten

def NoUsernames.encode (entry : NoUsernames) : List Token := encodeParts entry.parts

theorem NoUsernames.decode_encode (entry : NoUsernames) : NoUsernames.decode entry.encode = some entry :=
  NoUsernames.decode_agrees entry _ (fun _ _ => rfl)

theorem NoUsernames.within (entry : NoUsernames) : ∀ token ∈ entry.encode, token.tag ∈ NoUsernames.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoUsernames.shape] at this

theorem NoUsernames.led (entry : NoUsernames) : Lead [53, 53, 51] entry.encode :=
  lead_parts [53, 53, 51] entry.username _ NoUsernames.tags.tail rfl (by decide +kernel)

structure NoPartyIDs where
  partyID : Terminated 1  -- tag 448
  partyIDSource : Terminated 1  -- tag 447
  partyRole : Terminated 1  -- tag 452
  noPartySubIDs : Option (Terminated 1)  -- tag 802
  partySubID : Terminated 1  -- tag 523
  partySubIDType : Terminated 1  -- tag 803

def NoPartyIDs.parts (record : NoPartyIDs) : List Part :=
  [Part.required [52, 52, 56] record.partyID,
   Part.required [52, 52, 55] record.partyIDSource,
   Part.required [52, 53, 50] record.partyRole,
   Part.optional [56, 48, 50] record.noPartySubIDs,
   Part.required [53, 50, 51] record.partySubID,
   Part.required [56, 48, 51] record.partySubIDType]

def NoPartyIDs.tags : List (List (List UInt8)) :=
  [[[52, 52, 56]], [[52, 52, 55]], [[52, 53, 50]], [[56, 48, 50]], [[53, 50, 51]], [[56, 48, 51]]]

theorem NoPartyIDs.shape (record : NoPartyIDs) : record.parts.map Part.tags = NoPartyIDs.tags := rfl

def NoPartyIDs.decode (tokens : List Token) : Option NoPartyIDs := do
  let partyID ← readRequired [52, 52, 56] tokens
  let partyIDSource ← readRequired [52, 52, 55] tokens
  let partyRole ← readRequired [52, 53, 50] tokens
  let noPartySubIDs ← readOptional [56, 48, 50] tokens
  let partySubID ← readRequired [53, 50, 51] tokens
  let partySubIDType ← readRequired [56, 48, 51] tokens
  pure { partyID, partyIDSource, partyRole, noPartySubIDs, partySubID, partySubIDType }

theorem NoPartyIDs.decode_agrees (record : NoPartyIDs) (tokens : List Token)
    (agrees : ∀ tags ∈ NoPartyIDs.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoPartyIDs.decode tokens = some record := by
  have distinct : NoPartyIDs.tags.flatten.Nodup := by decide +kernel
  have partyID := readRequired_part [52, 52, 56] record.partyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have partyIDSource := readRequired_part [52, 52, 55] record.partyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have partyRole := readRequired_part [52, 53, 50] record.partyRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have noPartySubIDs := readOptional_part [56, 48, 50] record.noPartySubIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have partySubID := readRequired_part [53, 50, 51] record.partySubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have partySubIDType := readRequired_part [56, 48, 51] record.partySubIDType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  simp only [NoPartyIDs.decode, partyID, partyIDSource, partyRole, noPartySubIDs, partySubID, partySubIDType, some_bind] <;> rfl

def NoPartyIDs.members : List (List UInt8) := NoPartyIDs.tags.flatten

def NoPartyIDs.encode (entry : NoPartyIDs) : List Token := encodeParts entry.parts

theorem NoPartyIDs.decode_encode (entry : NoPartyIDs) : NoPartyIDs.decode entry.encode = some entry :=
  NoPartyIDs.decode_agrees entry _ (fun _ _ => rfl)

theorem NoPartyIDs.within (entry : NoPartyIDs) : ∀ token ∈ entry.encode, token.tag ∈ NoPartyIDs.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoPartyIDs.shape] at this

theorem NoPartyIDs.led (entry : NoPartyIDs) : Lead [52, 52, 56] entry.encode :=
  lead_parts [52, 52, 56] entry.partyID _ NoPartyIDs.tags.tail rfl (by decide +kernel)

structure UserNotification where
  noUsernames : List NoUsernames  -- tag 809
  userStatus : Terminated 1  -- tag 926
  noPartyIDs : List NoPartyIDs  -- tag 453

def UserNotification.parts (record : UserNotification) : List Part :=
  [Part.group [56, 48, 57] NoUsernames.members NoUsernames.encode NoUsernames.within record.noUsernames,
   Part.required [57, 50, 54] record.userStatus,
   Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs]

def UserNotification.tags : List (List (List UInt8)) :=
  [[56, 48, 57] :: NoUsernames.members, [[57, 50, 54]], [52, 53, 51] :: NoPartyIDs.members]

theorem UserNotification.shape (record : UserNotification) : record.parts.map Part.tags = UserNotification.tags := rfl

def UserNotification.decode (tokens : List Token) : Option UserNotification := do
  let noUsernames ← readGroup [56, 48, 57] [53, 53, 51] NoUsernames.members NoUsernames.decode tokens
  let userStatus ← readRequired [57, 50, 54] tokens
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  pure { noUsernames, userStatus, noPartyIDs }

theorem UserNotification.decode_agrees (record : UserNotification) (tokens : List Token)
    (agrees : ∀ tags ∈ UserNotification.tags, select tags tokens = select tags (encodeParts record.parts)) :
    UserNotification.decode tokens = some record := by
  have distinct : UserNotification.tags.flatten.Nodup := by decide +kernel
  have noUsernames := readGroup_part [56, 48, 57] [53, 53, 51] NoUsernames.members NoUsernames.encode NoUsernames.within NoUsernames.decode NoUsernames.decode_encode NoUsernames.led record.noUsernames tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have userStatus := readRequired_part [57, 50, 54] record.userStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [UserNotification.decode, noUsernames, userStatus, noPartyIDs, some_bind] <;> rfl

structure OrderCancelReject where
  orderID : Terminated 1  -- tag 37
  clOrdID : Terminated 1  -- tag 11
  origClOrdID : Terminated 1  -- tag 41
  ordStatus : Terminated 1  -- tag 39
  transactTime : Terminated 1  -- tag 60
  cxlRejResponseTo : Terminated 1  -- tag 434
  cxlRejReason : Option (Terminated 1)  -- tag 102
  text : Option (Terminated 1)  -- tag 58

def OrderCancelReject.parts (record : OrderCancelReject) : List Part :=
  [Part.required [51, 55] record.orderID,
   Part.required [49, 49] record.clOrdID,
   Part.required [52, 49] record.origClOrdID,
   Part.required [51, 57] record.ordStatus,
   Part.required [54, 48] record.transactTime,
   Part.required [52, 51, 52] record.cxlRejResponseTo,
   Part.optional [49, 48, 50] record.cxlRejReason,
   Part.optional [53, 56] record.text]

def OrderCancelReject.tags : List (List (List UInt8)) :=
  [[[51, 55]], [[49, 49]], [[52, 49]], [[51, 57]], [[54, 48]], [[52, 51, 52]], [[49, 48, 50]], [[53, 56]]]

theorem OrderCancelReject.shape (record : OrderCancelReject) : record.parts.map Part.tags = OrderCancelReject.tags := rfl

def OrderCancelReject.decode (tokens : List Token) : Option OrderCancelReject := do
  let orderID ← readRequired [51, 55] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let transactTime ← readRequired [54, 48] tokens
  let cxlRejResponseTo ← readRequired [52, 51, 52] tokens
  let cxlRejReason ← readOptional [49, 48, 50] tokens
  let text ← readOptional [53, 56] tokens
  pure { orderID, clOrdID, origClOrdID, ordStatus, transactTime, cxlRejResponseTo, cxlRejReason, text }

theorem OrderCancelReject.decode_agrees (record : OrderCancelReject) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelReject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelReject.decode tokens = some record := by
  have distinct : OrderCancelReject.tags.flatten.Nodup := by decide +kernel
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have cxlRejResponseTo := readRequired_part [52, 51, 52] record.cxlRejResponseTo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have cxlRejReason := readOptional_part [49, 48, 50] record.cxlRejReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  simp only [OrderCancelReject.decode, orderID, clOrdID, origClOrdID, ordStatus, transactTime, cxlRejResponseTo, cxlRejReason, text, some_bind] <;> rfl

structure ExecutionReport where
  orderID : Terminated 1  -- tag 37
  clOrdID : Terminated 1  -- tag 11
  execID : Terminated 1  -- tag 17
  ordStatus : Terminated 1  -- tag 39
  instrumentSymbol : Terminated 1  -- tag 55
  leavesQty : Terminated 1  -- tag 151
  cumQty : Terminated 1  -- tag 14
  avgPx : Terminated 1  -- tag 6
  transactTime : Terminated 1  -- tag 60

def ExecutionReport.parts (record : ExecutionReport) : List Part :=
  [Part.required [51, 55] record.orderID,
   Part.required [49, 49] record.clOrdID,
   Part.required [49, 55] record.execID,
   Part.required [51, 57] record.ordStatus,
   Part.required [53, 53] record.instrumentSymbol,
   Part.required [49, 53, 49] record.leavesQty,
   Part.required [49, 52] record.cumQty,
   Part.required [54] record.avgPx,
   Part.required [54, 48] record.transactTime]

def ExecutionReport.tags : List (List (List UInt8)) :=
  [[[51, 55]], [[49, 49]], [[49, 55]], [[51, 57]], [[53, 53]], [[49, 53, 49]], [[49, 52]], [[54]], [[54, 48]]]

theorem ExecutionReport.shape (record : ExecutionReport) : record.parts.map Part.tags = ExecutionReport.tags := rfl

def ExecutionReport.decode (tokens : List Token) : Option ExecutionReport := do
  let orderID ← readRequired [51, 55] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let execID ← readRequired [49, 55] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let instrumentSymbol ← readRequired [53, 53] tokens
  let leavesQty ← readRequired [49, 53, 49] tokens
  let cumQty ← readRequired [49, 52] tokens
  let avgPx ← readRequired [54] tokens
  let transactTime ← readRequired [54, 48] tokens
  pure { orderID, clOrdID, execID, ordStatus, instrumentSymbol, leavesQty, cumQty, avgPx, transactTime }

theorem ExecutionReport.decode_agrees (record : ExecutionReport) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReport.decode tokens = some record := by
  have distinct : ExecutionReport.tags.flatten.Nodup := by decide +kernel
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have execID := readRequired_part [49, 55] record.execID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have instrumentSymbol := readRequired_part [53, 53] record.instrumentSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have leavesQty := readRequired_part [49, 53, 49] record.leavesQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have cumQty := readRequired_part [49, 52] record.cumQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have avgPx := readRequired_part [54] record.avgPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  simp only [ExecutionReport.decode, orderID, clOrdID, execID, ordStatus, instrumentSymbol, leavesQty, cumQty, avgPx, transactTime, some_bind] <;> rfl

structure ExecutionReportNew where
  noPartyIDs : List NoPartyIDs  -- tag 453
  account : Option (Terminated 1)  -- tag 1
  orderCapacity : Option (Terminated 1)  -- tag 528
  instrumentSecurityID : Terminated 1  -- tag 48
  instrumentSecurityIDSource : Terminated 1  -- tag 22
  side : Terminated 1  -- tag 54
  orderQtyDataOrderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  underlyingColPx : Option (Terminated 1)  -- tag 21101
  triggeringInstructionTriggerType : Option (Terminated 1)  -- tag 1100
  triggeringInstructionTriggerAction : Option (Terminated 1)  -- tag 1101
  triggeringInstructionTriggerPrice : Option (Terminated 1)  -- tag 1102
  triggeringInstructionTriggerSymbol : Option (Terminated 1)  -- tag 1103
  tradingSessionID : Option (Terminated 1)  -- tag 336
  timeInForce : Terminated 1  -- tag 59
  expireDate : Option (Terminated 1)  -- tag 432
  execInst : Option (Terminated 1)  -- tag 18
  allocID : Option (Terminated 1)  -- tag 70
  copyMsgIndicator : Option (Terminated 1)  -- tag 797
  matchIncrement : Option (Terminated 1)  -- tag 1089
  pegPriceType : Option (Terminated 1)  -- tag 1094
  maxFloor : Option (Terminated 1)  -- tag 111
  settlCurrAmt : Option (Terminated 1)  -- tag 119
  optionPremiumAmt : Option (Terminated 1)  -- tag 20015
  openCloseIndicator : Option (Terminated 1)  -- tag 20199
  sMPLevel : Option (Terminated 1)  -- tag 21114
  sMPMethod : Option (Terminated 1)  -- tag 21115
  sMPID : Option (Terminated 1)  -- tag 21116

def ExecutionReportNew.parts (record : ExecutionReportNew) : List Part :=
  [Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.optional [49] record.account,
   Part.optional [53, 50, 56] record.orderCapacity,
   Part.required [52, 56] record.instrumentSecurityID,
   Part.required [50, 50] record.instrumentSecurityIDSource,
   Part.required [53, 52] record.side,
   Part.required [51, 56] record.orderQtyDataOrderQty,
   Part.required [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.optional [50, 49, 49, 48, 49] record.underlyingColPx,
   Part.optional [49, 49, 48, 48] record.triggeringInstructionTriggerType,
   Part.optional [49, 49, 48, 49] record.triggeringInstructionTriggerAction,
   Part.optional [49, 49, 48, 50] record.triggeringInstructionTriggerPrice,
   Part.optional [49, 49, 48, 51] record.triggeringInstructionTriggerSymbol,
   Part.optional [51, 51, 54] record.tradingSessionID,
   Part.required [53, 57] record.timeInForce,
   Part.optional [52, 51, 50] record.expireDate,
   Part.optional [49, 56] record.execInst,
   Part.optional [55, 48] record.allocID,
   Part.optional [55, 57, 55] record.copyMsgIndicator,
   Part.optional [49, 48, 56, 57] record.matchIncrement,
   Part.optional [49, 48, 57, 52] record.pegPriceType,
   Part.optional [49, 49, 49] record.maxFloor,
   Part.optional [49, 49, 57] record.settlCurrAmt,
   Part.optional [50, 48, 48, 49, 53] record.optionPremiumAmt,
   Part.optional [50, 48, 49, 57, 57] record.openCloseIndicator,
   Part.optional [50, 49, 49, 49, 52] record.sMPLevel,
   Part.optional [50, 49, 49, 49, 53] record.sMPMethod,
   Part.optional [50, 49, 49, 49, 54] record.sMPID]

def ExecutionReportNew.tags : List (List (List UInt8)) :=
  [[52, 53, 51] :: NoPartyIDs.members, [[49]], [[53, 50, 56]], [[52, 56]], [[50, 50]], [[53, 52]], [[51, 56]], [[52, 48]], [[52, 52]], [[50, 49, 49, 48, 49]], [[49, 49, 48, 48]], [[49, 49, 48, 49]], [[49, 49, 48, 50]], [[49, 49, 48, 51]], [[51, 51, 54]], [[53, 57]], [[52, 51, 50]], [[49, 56]], [[55, 48]], [[55, 57, 55]], [[49, 48, 56, 57]], [[49, 48, 57, 52]], [[49, 49, 49]], [[49, 49, 57]], [[50, 48, 48, 49, 53]], [[50, 48, 49, 57, 57]], [[50, 49, 49, 49, 52]], [[50, 49, 49, 49, 53]], [[50, 49, 49, 49, 54]]]

theorem ExecutionReportNew.shape (record : ExecutionReportNew) : record.parts.map Part.tags = ExecutionReportNew.tags := rfl

def ExecutionReportNew.decode (tokens : List Token) : Option ExecutionReportNew := do
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let account ← readOptional [49] tokens
  let orderCapacity ← readOptional [53, 50, 56] tokens
  let instrumentSecurityID ← readRequired [52, 56] tokens
  let instrumentSecurityIDSource ← readRequired [50, 50] tokens
  let side ← readRequired [53, 52] tokens
  let orderQtyDataOrderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let underlyingColPx ← readOptional [50, 49, 49, 48, 49] tokens
  let triggeringInstructionTriggerType ← readOptional [49, 49, 48, 48] tokens
  let triggeringInstructionTriggerAction ← readOptional [49, 49, 48, 49] tokens
  let triggeringInstructionTriggerPrice ← readOptional [49, 49, 48, 50] tokens
  let triggeringInstructionTriggerSymbol ← readOptional [49, 49, 48, 51] tokens
  let tradingSessionID ← readOptional [51, 51, 54] tokens
  let timeInForce ← readRequired [53, 57] tokens
  let expireDate ← readOptional [52, 51, 50] tokens
  let execInst ← readOptional [49, 56] tokens
  let allocID ← readOptional [55, 48] tokens
  let copyMsgIndicator ← readOptional [55, 57, 55] tokens
  let matchIncrement ← readOptional [49, 48, 56, 57] tokens
  let pegPriceType ← readOptional [49, 48, 57, 52] tokens
  let maxFloor ← readOptional [49, 49, 49] tokens
  let settlCurrAmt ← readOptional [49, 49, 57] tokens
  let optionPremiumAmt ← readOptional [50, 48, 48, 49, 53] tokens
  let openCloseIndicator ← readOptional [50, 48, 49, 57, 57] tokens
  let sMPLevel ← readOptional [50, 49, 49, 49, 52] tokens
  let sMPMethod ← readOptional [50, 49, 49, 49, 53] tokens
  let sMPID ← readOptional [50, 49, 49, 49, 54] tokens
  pure { noPartyIDs, account, orderCapacity, instrumentSecurityID, instrumentSecurityIDSource, side, orderQtyDataOrderQty, ordType, price, underlyingColPx, triggeringInstructionTriggerType, triggeringInstructionTriggerAction, triggeringInstructionTriggerPrice, triggeringInstructionTriggerSymbol, tradingSessionID, timeInForce, expireDate, execInst, allocID, copyMsgIndicator, matchIncrement, pegPriceType, maxFloor, settlCurrAmt, optionPremiumAmt, openCloseIndicator, sMPLevel, sMPMethod, sMPID }

theorem ExecutionReportNew.decode_agrees (record : ExecutionReportNew) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportNew.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportNew.decode tokens = some record := by
  have distinct : ExecutionReportNew.tags.flatten.Nodup := by decide +kernel
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have orderCapacity := readOptional_part [53, 50, 56] record.orderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have instrumentSecurityID := readRequired_part [52, 56] record.instrumentSecurityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have instrumentSecurityIDSource := readRequired_part [50, 50] record.instrumentSecurityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have orderQtyDataOrderQty := readRequired_part [51, 56] record.orderQtyDataOrderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have underlyingColPx := readOptional_part [50, 49, 49, 48, 49] record.underlyingColPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have triggeringInstructionTriggerType := readOptional_part [49, 49, 48, 48] record.triggeringInstructionTriggerType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have triggeringInstructionTriggerAction := readOptional_part [49, 49, 48, 49] record.triggeringInstructionTriggerAction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have triggeringInstructionTriggerPrice := readOptional_part [49, 49, 48, 50] record.triggeringInstructionTriggerPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have triggeringInstructionTriggerSymbol := readOptional_part [49, 49, 48, 51] record.triggeringInstructionTriggerSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have tradingSessionID := readOptional_part [51, 51, 54] record.tradingSessionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have timeInForce := readRequired_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have expireDate := readOptional_part [52, 51, 50] record.expireDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have allocID := readOptional_part [55, 48] record.allocID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have copyMsgIndicator := readOptional_part [55, 57, 55] record.copyMsgIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have matchIncrement := readOptional_part [49, 48, 56, 57] record.matchIncrement tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have pegPriceType := readOptional_part [49, 48, 57, 52] record.pegPriceType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have maxFloor := readOptional_part [49, 49, 49] record.maxFloor tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have settlCurrAmt := readOptional_part [49, 49, 57] record.settlCurrAmt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have optionPremiumAmt := readOptional_part [50, 48, 48, 49, 53] record.optionPremiumAmt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have openCloseIndicator := readOptional_part [50, 48, 49, 57, 57] record.openCloseIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have sMPLevel := readOptional_part [50, 49, 49, 49, 52] record.sMPLevel tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have sMPMethod := readOptional_part [50, 49, 49, 49, 53] record.sMPMethod tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have sMPID := readOptional_part [50, 49, 49, 49, 54] record.sMPID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  simp only [ExecutionReportNew.decode, noPartyIDs, account, orderCapacity, instrumentSecurityID, instrumentSecurityIDSource, side, orderQtyDataOrderQty, ordType, price, underlyingColPx, triggeringInstructionTriggerType, triggeringInstructionTriggerAction, triggeringInstructionTriggerPrice, triggeringInstructionTriggerSymbol, tradingSessionID, timeInForce, expireDate, execInst, allocID, copyMsgIndicator, matchIncrement, pegPriceType, maxFloor, settlCurrAmt, optionPremiumAmt, openCloseIndicator, sMPLevel, sMPMethod, sMPID, some_bind] <;> rfl

structure ExecutionReportCanceled where
  noPartyIDs : List NoPartyIDs  -- tag 453
  account : Option (Terminated 1)  -- tag 1
  orderCapacity : Option (Terminated 1)  -- tag 528
  instrumentSecurityID : Terminated 1  -- tag 48
  instrumentSecurityIDSource : Terminated 1  -- tag 22
  side : Terminated 1  -- tag 54
  orderQtyDataOrderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  underlyingColPx : Option (Terminated 1)  -- tag 21101
  timeInForce : Terminated 1  -- tag 59
  allocID : Option (Terminated 1)  -- tag 70
  tradingSessionID : Option (Terminated 1)  -- tag 336
  openCloseIndicator : Option (Terminated 1)  -- tag 20199
  copyMsgIndicator : Option (Terminated 1)  -- tag 797
  expireDate : Option (Terminated 1)  -- tag 432
  origClOrdID : Option (Terminated 1)  -- tag 41
  settlCurrAmt : Option (Terminated 1)  -- tag 119
  optionPremiumAmt : Option (Terminated 1)  -- tag 20015
  text : Option (Terminated 1)  -- tag 58
  execRestatementReason : Terminated 1  -- tag 378

def ExecutionReportCanceled.parts (record : ExecutionReportCanceled) : List Part :=
  [Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.optional [49] record.account,
   Part.optional [53, 50, 56] record.orderCapacity,
   Part.required [52, 56] record.instrumentSecurityID,
   Part.required [50, 50] record.instrumentSecurityIDSource,
   Part.required [53, 52] record.side,
   Part.required [51, 56] record.orderQtyDataOrderQty,
   Part.required [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.optional [50, 49, 49, 48, 49] record.underlyingColPx,
   Part.required [53, 57] record.timeInForce,
   Part.optional [55, 48] record.allocID,
   Part.optional [51, 51, 54] record.tradingSessionID,
   Part.optional [50, 48, 49, 57, 57] record.openCloseIndicator,
   Part.optional [55, 57, 55] record.copyMsgIndicator,
   Part.optional [52, 51, 50] record.expireDate,
   Part.optional [52, 49] record.origClOrdID,
   Part.optional [49, 49, 57] record.settlCurrAmt,
   Part.optional [50, 48, 48, 49, 53] record.optionPremiumAmt,
   Part.optional [53, 56] record.text,
   Part.required [51, 55, 56] record.execRestatementReason]

def ExecutionReportCanceled.tags : List (List (List UInt8)) :=
  [[52, 53, 51] :: NoPartyIDs.members, [[49]], [[53, 50, 56]], [[52, 56]], [[50, 50]], [[53, 52]], [[51, 56]], [[52, 48]], [[52, 52]], [[50, 49, 49, 48, 49]], [[53, 57]], [[55, 48]], [[51, 51, 54]], [[50, 48, 49, 57, 57]], [[55, 57, 55]], [[52, 51, 50]], [[52, 49]], [[49, 49, 57]], [[50, 48, 48, 49, 53]], [[53, 56]], [[51, 55, 56]]]

theorem ExecutionReportCanceled.shape (record : ExecutionReportCanceled) : record.parts.map Part.tags = ExecutionReportCanceled.tags := rfl

def ExecutionReportCanceled.decode (tokens : List Token) : Option ExecutionReportCanceled := do
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let account ← readOptional [49] tokens
  let orderCapacity ← readOptional [53, 50, 56] tokens
  let instrumentSecurityID ← readRequired [52, 56] tokens
  let instrumentSecurityIDSource ← readRequired [50, 50] tokens
  let side ← readRequired [53, 52] tokens
  let orderQtyDataOrderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let underlyingColPx ← readOptional [50, 49, 49, 48, 49] tokens
  let timeInForce ← readRequired [53, 57] tokens
  let allocID ← readOptional [55, 48] tokens
  let tradingSessionID ← readOptional [51, 51, 54] tokens
  let openCloseIndicator ← readOptional [50, 48, 49, 57, 57] tokens
  let copyMsgIndicator ← readOptional [55, 57, 55] tokens
  let expireDate ← readOptional [52, 51, 50] tokens
  let origClOrdID ← readOptional [52, 49] tokens
  let settlCurrAmt ← readOptional [49, 49, 57] tokens
  let optionPremiumAmt ← readOptional [50, 48, 48, 49, 53] tokens
  let text ← readOptional [53, 56] tokens
  let execRestatementReason ← readRequired [51, 55, 56] tokens
  pure { noPartyIDs, account, orderCapacity, instrumentSecurityID, instrumentSecurityIDSource, side, orderQtyDataOrderQty, ordType, price, underlyingColPx, timeInForce, allocID, tradingSessionID, openCloseIndicator, copyMsgIndicator, expireDate, origClOrdID, settlCurrAmt, optionPremiumAmt, text, execRestatementReason }

theorem ExecutionReportCanceled.decode_agrees (record : ExecutionReportCanceled) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportCanceled.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportCanceled.decode tokens = some record := by
  have distinct : ExecutionReportCanceled.tags.flatten.Nodup := by decide +kernel
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have orderCapacity := readOptional_part [53, 50, 56] record.orderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have instrumentSecurityID := readRequired_part [52, 56] record.instrumentSecurityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have instrumentSecurityIDSource := readRequired_part [50, 50] record.instrumentSecurityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have orderQtyDataOrderQty := readRequired_part [51, 56] record.orderQtyDataOrderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have underlyingColPx := readOptional_part [50, 49, 49, 48, 49] record.underlyingColPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have timeInForce := readRequired_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have allocID := readOptional_part [55, 48] record.allocID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have tradingSessionID := readOptional_part [51, 51, 54] record.tradingSessionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have openCloseIndicator := readOptional_part [50, 48, 49, 57, 57] record.openCloseIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have copyMsgIndicator := readOptional_part [55, 57, 55] record.copyMsgIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have expireDate := readOptional_part [52, 51, 50] record.expireDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have settlCurrAmt := readOptional_part [49, 49, 57] record.settlCurrAmt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have optionPremiumAmt := readOptional_part [50, 48, 48, 49, 53] record.optionPremiumAmt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have execRestatementReason := readRequired_part [51, 55, 56] record.execRestatementReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  simp only [ExecutionReportCanceled.decode, noPartyIDs, account, orderCapacity, instrumentSecurityID, instrumentSecurityIDSource, side, orderQtyDataOrderQty, ordType, price, underlyingColPx, timeInForce, allocID, tradingSessionID, openCloseIndicator, copyMsgIndicator, expireDate, origClOrdID, settlCurrAmt, optionPremiumAmt, text, execRestatementReason, some_bind] <;> rfl

structure ExecutionReportRejected where
  ordRejReason : Terminated 1  -- tag 103
  text : Option (Terminated 1)  -- tag 58
  origClOrdID : Option (Terminated 1)  -- tag 41
  noPartyIDs : List NoPartyIDs  -- tag 453
  account : Option (Terminated 1)  -- tag 1
  orderCapacity : Option (Terminated 1)  -- tag 528
  instrumentSecurityID : Terminated 1  -- tag 48
  instrumentSecurityIDSource : Terminated 1  -- tag 22
  side : Terminated 1  -- tag 54
  orderQtyDataOrderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  underlyingColPx : Option (Terminated 1)  -- tag 21101
  triggeringInstructionTriggerType : Option (Terminated 1)  -- tag 1100
  triggeringInstructionTriggerAction : Option (Terminated 1)  -- tag 1101
  triggeringInstructionTriggerPrice : Option (Terminated 1)  -- tag 1102
  triggeringInstructionTriggerSymbol : Option (Terminated 1)  -- tag 1103
  tradingSessionID : Option (Terminated 1)  -- tag 336
  timeInForce : Terminated 1  -- tag 59
  expireDate : Option (Terminated 1)  -- tag 432
  execInst : Option (Terminated 1)  -- tag 18
  allocID : Option (Terminated 1)  -- tag 70
  copyMsgIndicator : Option (Terminated 1)  -- tag 797
  matchIncrement : Option (Terminated 1)  -- tag 1089
  maxFloor : Option (Terminated 1)  -- tag 111
  settlCurrAmt : Option (Terminated 1)  -- tag 119
  optionPremiumAmt : Option (Terminated 1)  -- tag 20015
  openCloseIndicator : Option (Terminated 1)  -- tag 20199
  sMPLevel : Option (Terminated 1)  -- tag 21114
  sMPMethod : Option (Terminated 1)  -- tag 21115
  sMPID : Option (Terminated 1)  -- tag 21116

def ExecutionReportRejected.parts (record : ExecutionReportRejected) : List Part :=
  [Part.required [49, 48, 51] record.ordRejReason,
   Part.optional [53, 56] record.text,
   Part.optional [52, 49] record.origClOrdID,
   Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.optional [49] record.account,
   Part.optional [53, 50, 56] record.orderCapacity,
   Part.required [52, 56] record.instrumentSecurityID,
   Part.required [50, 50] record.instrumentSecurityIDSource,
   Part.required [53, 52] record.side,
   Part.required [51, 56] record.orderQtyDataOrderQty,
   Part.required [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.optional [50, 49, 49, 48, 49] record.underlyingColPx,
   Part.optional [49, 49, 48, 48] record.triggeringInstructionTriggerType,
   Part.optional [49, 49, 48, 49] record.triggeringInstructionTriggerAction,
   Part.optional [49, 49, 48, 50] record.triggeringInstructionTriggerPrice,
   Part.optional [49, 49, 48, 51] record.triggeringInstructionTriggerSymbol,
   Part.optional [51, 51, 54] record.tradingSessionID,
   Part.required [53, 57] record.timeInForce,
   Part.optional [52, 51, 50] record.expireDate,
   Part.optional [49, 56] record.execInst,
   Part.optional [55, 48] record.allocID,
   Part.optional [55, 57, 55] record.copyMsgIndicator,
   Part.optional [49, 48, 56, 57] record.matchIncrement,
   Part.optional [49, 49, 49] record.maxFloor,
   Part.optional [49, 49, 57] record.settlCurrAmt,
   Part.optional [50, 48, 48, 49, 53] record.optionPremiumAmt,
   Part.optional [50, 48, 49, 57, 57] record.openCloseIndicator,
   Part.optional [50, 49, 49, 49, 52] record.sMPLevel,
   Part.optional [50, 49, 49, 49, 53] record.sMPMethod,
   Part.optional [50, 49, 49, 49, 54] record.sMPID]

def ExecutionReportRejected.tags : List (List (List UInt8)) :=
  [[[49, 48, 51]], [[53, 56]], [[52, 49]], [52, 53, 51] :: NoPartyIDs.members, [[49]], [[53, 50, 56]], [[52, 56]], [[50, 50]], [[53, 52]], [[51, 56]], [[52, 48]], [[52, 52]], [[50, 49, 49, 48, 49]], [[49, 49, 48, 48]], [[49, 49, 48, 49]], [[49, 49, 48, 50]], [[49, 49, 48, 51]], [[51, 51, 54]], [[53, 57]], [[52, 51, 50]], [[49, 56]], [[55, 48]], [[55, 57, 55]], [[49, 48, 56, 57]], [[49, 49, 49]], [[49, 49, 57]], [[50, 48, 48, 49, 53]], [[50, 48, 49, 57, 57]], [[50, 49, 49, 49, 52]], [[50, 49, 49, 49, 53]], [[50, 49, 49, 49, 54]]]

theorem ExecutionReportRejected.shape (record : ExecutionReportRejected) : record.parts.map Part.tags = ExecutionReportRejected.tags := rfl

def ExecutionReportRejected.decode (tokens : List Token) : Option ExecutionReportRejected := do
  let ordRejReason ← readRequired [49, 48, 51] tokens
  let text ← readOptional [53, 56] tokens
  let origClOrdID ← readOptional [52, 49] tokens
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let account ← readOptional [49] tokens
  let orderCapacity ← readOptional [53, 50, 56] tokens
  let instrumentSecurityID ← readRequired [52, 56] tokens
  let instrumentSecurityIDSource ← readRequired [50, 50] tokens
  let side ← readRequired [53, 52] tokens
  let orderQtyDataOrderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let underlyingColPx ← readOptional [50, 49, 49, 48, 49] tokens
  let triggeringInstructionTriggerType ← readOptional [49, 49, 48, 48] tokens
  let triggeringInstructionTriggerAction ← readOptional [49, 49, 48, 49] tokens
  let triggeringInstructionTriggerPrice ← readOptional [49, 49, 48, 50] tokens
  let triggeringInstructionTriggerSymbol ← readOptional [49, 49, 48, 51] tokens
  let tradingSessionID ← readOptional [51, 51, 54] tokens
  let timeInForce ← readRequired [53, 57] tokens
  let expireDate ← readOptional [52, 51, 50] tokens
  let execInst ← readOptional [49, 56] tokens
  let allocID ← readOptional [55, 48] tokens
  let copyMsgIndicator ← readOptional [55, 57, 55] tokens
  let matchIncrement ← readOptional [49, 48, 56, 57] tokens
  let maxFloor ← readOptional [49, 49, 49] tokens
  let settlCurrAmt ← readOptional [49, 49, 57] tokens
  let optionPremiumAmt ← readOptional [50, 48, 48, 49, 53] tokens
  let openCloseIndicator ← readOptional [50, 48, 49, 57, 57] tokens
  let sMPLevel ← readOptional [50, 49, 49, 49, 52] tokens
  let sMPMethod ← readOptional [50, 49, 49, 49, 53] tokens
  let sMPID ← readOptional [50, 49, 49, 49, 54] tokens
  pure { ordRejReason, text, origClOrdID, noPartyIDs, account, orderCapacity, instrumentSecurityID, instrumentSecurityIDSource, side, orderQtyDataOrderQty, ordType, price, underlyingColPx, triggeringInstructionTriggerType, triggeringInstructionTriggerAction, triggeringInstructionTriggerPrice, triggeringInstructionTriggerSymbol, tradingSessionID, timeInForce, expireDate, execInst, allocID, copyMsgIndicator, matchIncrement, maxFloor, settlCurrAmt, optionPremiumAmt, openCloseIndicator, sMPLevel, sMPMethod, sMPID }

theorem ExecutionReportRejected.decode_agrees (record : ExecutionReportRejected) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportRejected.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportRejected.decode tokens = some record := by
  have distinct : ExecutionReportRejected.tags.flatten.Nodup := by decide +kernel
  have ordRejReason := readRequired_part [49, 48, 51] record.ordRejReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have orderCapacity := readOptional_part [53, 50, 56] record.orderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have instrumentSecurityID := readRequired_part [52, 56] record.instrumentSecurityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have instrumentSecurityIDSource := readRequired_part [50, 50] record.instrumentSecurityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have orderQtyDataOrderQty := readRequired_part [51, 56] record.orderQtyDataOrderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have underlyingColPx := readOptional_part [50, 49, 49, 48, 49] record.underlyingColPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have triggeringInstructionTriggerType := readOptional_part [49, 49, 48, 48] record.triggeringInstructionTriggerType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have triggeringInstructionTriggerAction := readOptional_part [49, 49, 48, 49] record.triggeringInstructionTriggerAction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have triggeringInstructionTriggerPrice := readOptional_part [49, 49, 48, 50] record.triggeringInstructionTriggerPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have triggeringInstructionTriggerSymbol := readOptional_part [49, 49, 48, 51] record.triggeringInstructionTriggerSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have tradingSessionID := readOptional_part [51, 51, 54] record.tradingSessionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have timeInForce := readRequired_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have expireDate := readOptional_part [52, 51, 50] record.expireDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have allocID := readOptional_part [55, 48] record.allocID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have copyMsgIndicator := readOptional_part [55, 57, 55] record.copyMsgIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have matchIncrement := readOptional_part [49, 48, 56, 57] record.matchIncrement tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have maxFloor := readOptional_part [49, 49, 49] record.maxFloor tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have settlCurrAmt := readOptional_part [49, 49, 57] record.settlCurrAmt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have optionPremiumAmt := readOptional_part [50, 48, 48, 49, 53] record.optionPremiumAmt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have openCloseIndicator := readOptional_part [50, 48, 49, 57, 57] record.openCloseIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have sMPLevel := readOptional_part [50, 49, 49, 49, 52] record.sMPLevel tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have sMPMethod := readOptional_part [50, 49, 49, 49, 53] record.sMPMethod tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have sMPID := readOptional_part [50, 49, 49, 49, 54] record.sMPID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  simp only [ExecutionReportRejected.decode, ordRejReason, text, origClOrdID, noPartyIDs, account, orderCapacity, instrumentSecurityID, instrumentSecurityIDSource, side, orderQtyDataOrderQty, ordType, price, underlyingColPx, triggeringInstructionTriggerType, triggeringInstructionTriggerAction, triggeringInstructionTriggerPrice, triggeringInstructionTriggerSymbol, tradingSessionID, timeInForce, expireDate, execInst, allocID, copyMsgIndicator, matchIncrement, maxFloor, settlCurrAmt, optionPremiumAmt, openCloseIndicator, sMPLevel, sMPMethod, sMPID, some_bind] <;> rfl

structure ExecutionReportRestated where
  noPartyIDs : List NoPartyIDs  -- tag 453
  account : Option (Terminated 1)  -- tag 1
  orderCapacity : Option (Terminated 1)  -- tag 528
  instrumentSecurityID : Terminated 1  -- tag 48
  instrumentSecurityIDSource : Terminated 1  -- tag 22
  side : Terminated 1  -- tag 54
  orderQtyDataOrderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  underlyingColPx : Option (Terminated 1)  -- tag 21101
  triggeringInstructionTriggerType : Option (Terminated 1)  -- tag 1100
  triggeringInstructionTriggerAction : Option (Terminated 1)  -- tag 1101
  triggeringInstructionTriggerPrice : Option (Terminated 1)  -- tag 1102
  triggeringInstructionTriggerSymbol : Option (Terminated 1)  -- tag 1103
  tradingSessionID : Option (Terminated 1)  -- tag 336
  timeInForce : Terminated 1  -- tag 59
  expireDate : Option (Terminated 1)  -- tag 432
  execInst : Option (Terminated 1)  -- tag 18
  execRestatementReason : Terminated 1  -- tag 378
  allocID : Option (Terminated 1)  -- tag 70
  settlCurrAmt : Option (Terminated 1)  -- tag 119
  optionPremiumAmt : Option (Terminated 1)  -- tag 20015
  copyMsgIndicator : Option (Terminated 1)  -- tag 797
  matchIncrement : Option (Terminated 1)  -- tag 1089
  maxFloor : Option (Terminated 1)  -- tag 111
  openCloseIndicator : Option (Terminated 1)  -- tag 20199
  sMPLevel : Option (Terminated 1)  -- tag 21114
  sMPMethod : Option (Terminated 1)  -- tag 21115
  sMPID : Option (Terminated 1)  -- tag 21116
  trdMatchID : Terminated 1  -- tag 880
  lastQty : Terminated 1  -- tag 32
  lastPx : Terminated 1  -- tag 31
  lastUnderlyingPx : Option (Terminated 1)  -- tag 21100

def ExecutionReportRestated.parts (record : ExecutionReportRestated) : List Part :=
  [Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.optional [49] record.account,
   Part.optional [53, 50, 56] record.orderCapacity,
   Part.required [52, 56] record.instrumentSecurityID,
   Part.required [50, 50] record.instrumentSecurityIDSource,
   Part.required [53, 52] record.side,
   Part.required [51, 56] record.orderQtyDataOrderQty,
   Part.required [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.optional [50, 49, 49, 48, 49] record.underlyingColPx,
   Part.optional [49, 49, 48, 48] record.triggeringInstructionTriggerType,
   Part.optional [49, 49, 48, 49] record.triggeringInstructionTriggerAction,
   Part.optional [49, 49, 48, 50] record.triggeringInstructionTriggerPrice,
   Part.optional [49, 49, 48, 51] record.triggeringInstructionTriggerSymbol,
   Part.optional [51, 51, 54] record.tradingSessionID,
   Part.required [53, 57] record.timeInForce,
   Part.optional [52, 51, 50] record.expireDate,
   Part.optional [49, 56] record.execInst,
   Part.required [51, 55, 56] record.execRestatementReason,
   Part.optional [55, 48] record.allocID,
   Part.optional [49, 49, 57] record.settlCurrAmt,
   Part.optional [50, 48, 48, 49, 53] record.optionPremiumAmt,
   Part.optional [55, 57, 55] record.copyMsgIndicator,
   Part.optional [49, 48, 56, 57] record.matchIncrement,
   Part.optional [49, 49, 49] record.maxFloor,
   Part.optional [50, 48, 49, 57, 57] record.openCloseIndicator,
   Part.optional [50, 49, 49, 49, 52] record.sMPLevel,
   Part.optional [50, 49, 49, 49, 53] record.sMPMethod,
   Part.optional [50, 49, 49, 49, 54] record.sMPID,
   Part.required [56, 56, 48] record.trdMatchID,
   Part.required [51, 50] record.lastQty,
   Part.required [51, 49] record.lastPx,
   Part.optional [50, 49, 49, 48, 48] record.lastUnderlyingPx]

def ExecutionReportRestated.tags : List (List (List UInt8)) :=
  [[52, 53, 51] :: NoPartyIDs.members, [[49]], [[53, 50, 56]], [[52, 56]], [[50, 50]], [[53, 52]], [[51, 56]], [[52, 48]], [[52, 52]], [[50, 49, 49, 48, 49]], [[49, 49, 48, 48]], [[49, 49, 48, 49]], [[49, 49, 48, 50]], [[49, 49, 48, 51]], [[51, 51, 54]], [[53, 57]], [[52, 51, 50]], [[49, 56]], [[51, 55, 56]], [[55, 48]], [[49, 49, 57]], [[50, 48, 48, 49, 53]], [[55, 57, 55]], [[49, 48, 56, 57]], [[49, 49, 49]], [[50, 48, 49, 57, 57]], [[50, 49, 49, 49, 52]], [[50, 49, 49, 49, 53]], [[50, 49, 49, 49, 54]], [[56, 56, 48]], [[51, 50]], [[51, 49]], [[50, 49, 49, 48, 48]]]

theorem ExecutionReportRestated.shape (record : ExecutionReportRestated) : record.parts.map Part.tags = ExecutionReportRestated.tags := rfl

def ExecutionReportRestated.decode (tokens : List Token) : Option ExecutionReportRestated := do
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let account ← readOptional [49] tokens
  let orderCapacity ← readOptional [53, 50, 56] tokens
  let instrumentSecurityID ← readRequired [52, 56] tokens
  let instrumentSecurityIDSource ← readRequired [50, 50] tokens
  let side ← readRequired [53, 52] tokens
  let orderQtyDataOrderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let underlyingColPx ← readOptional [50, 49, 49, 48, 49] tokens
  let triggeringInstructionTriggerType ← readOptional [49, 49, 48, 48] tokens
  let triggeringInstructionTriggerAction ← readOptional [49, 49, 48, 49] tokens
  let triggeringInstructionTriggerPrice ← readOptional [49, 49, 48, 50] tokens
  let triggeringInstructionTriggerSymbol ← readOptional [49, 49, 48, 51] tokens
  let tradingSessionID ← readOptional [51, 51, 54] tokens
  let timeInForce ← readRequired [53, 57] tokens
  let expireDate ← readOptional [52, 51, 50] tokens
  let execInst ← readOptional [49, 56] tokens
  let execRestatementReason ← readRequired [51, 55, 56] tokens
  let allocID ← readOptional [55, 48] tokens
  let settlCurrAmt ← readOptional [49, 49, 57] tokens
  let optionPremiumAmt ← readOptional [50, 48, 48, 49, 53] tokens
  let copyMsgIndicator ← readOptional [55, 57, 55] tokens
  let matchIncrement ← readOptional [49, 48, 56, 57] tokens
  let maxFloor ← readOptional [49, 49, 49] tokens
  let openCloseIndicator ← readOptional [50, 48, 49, 57, 57] tokens
  let sMPLevel ← readOptional [50, 49, 49, 49, 52] tokens
  let sMPMethod ← readOptional [50, 49, 49, 49, 53] tokens
  let sMPID ← readOptional [50, 49, 49, 49, 54] tokens
  let trdMatchID ← readRequired [56, 56, 48] tokens
  let lastQty ← readRequired [51, 50] tokens
  let lastPx ← readRequired [51, 49] tokens
  let lastUnderlyingPx ← readOptional [50, 49, 49, 48, 48] tokens
  pure { noPartyIDs, account, orderCapacity, instrumentSecurityID, instrumentSecurityIDSource, side, orderQtyDataOrderQty, ordType, price, underlyingColPx, triggeringInstructionTriggerType, triggeringInstructionTriggerAction, triggeringInstructionTriggerPrice, triggeringInstructionTriggerSymbol, tradingSessionID, timeInForce, expireDate, execInst, execRestatementReason, allocID, settlCurrAmt, optionPremiumAmt, copyMsgIndicator, matchIncrement, maxFloor, openCloseIndicator, sMPLevel, sMPMethod, sMPID, trdMatchID, lastQty, lastPx, lastUnderlyingPx }

theorem ExecutionReportRestated.decode_agrees (record : ExecutionReportRestated) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportRestated.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportRestated.decode tokens = some record := by
  have distinct : ExecutionReportRestated.tags.flatten.Nodup := by decide +kernel
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have orderCapacity := readOptional_part [53, 50, 56] record.orderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have instrumentSecurityID := readRequired_part [52, 56] record.instrumentSecurityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have instrumentSecurityIDSource := readRequired_part [50, 50] record.instrumentSecurityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have orderQtyDataOrderQty := readRequired_part [51, 56] record.orderQtyDataOrderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have underlyingColPx := readOptional_part [50, 49, 49, 48, 49] record.underlyingColPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have triggeringInstructionTriggerType := readOptional_part [49, 49, 48, 48] record.triggeringInstructionTriggerType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have triggeringInstructionTriggerAction := readOptional_part [49, 49, 48, 49] record.triggeringInstructionTriggerAction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have triggeringInstructionTriggerPrice := readOptional_part [49, 49, 48, 50] record.triggeringInstructionTriggerPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have triggeringInstructionTriggerSymbol := readOptional_part [49, 49, 48, 51] record.triggeringInstructionTriggerSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have tradingSessionID := readOptional_part [51, 51, 54] record.tradingSessionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have timeInForce := readRequired_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have expireDate := readOptional_part [52, 51, 50] record.expireDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have execRestatementReason := readRequired_part [51, 55, 56] record.execRestatementReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have allocID := readOptional_part [55, 48] record.allocID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have settlCurrAmt := readOptional_part [49, 49, 57] record.settlCurrAmt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have optionPremiumAmt := readOptional_part [50, 48, 48, 49, 53] record.optionPremiumAmt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have copyMsgIndicator := readOptional_part [55, 57, 55] record.copyMsgIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have matchIncrement := readOptional_part [49, 48, 56, 57] record.matchIncrement tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have maxFloor := readOptional_part [49, 49, 49] record.maxFloor tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have openCloseIndicator := readOptional_part [50, 48, 49, 57, 57] record.openCloseIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have sMPLevel := readOptional_part [50, 49, 49, 49, 52] record.sMPLevel tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have sMPMethod := readOptional_part [50, 49, 49, 49, 53] record.sMPMethod tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have sMPID := readOptional_part [50, 49, 49, 49, 54] record.sMPID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have trdMatchID := readRequired_part [56, 56, 48] record.trdMatchID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have lastQty := readRequired_part [51, 50] record.lastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have lastPx := readRequired_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have lastUnderlyingPx := readOptional_part [50, 49, 49, 48, 48] record.lastUnderlyingPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  simp only [ExecutionReportRestated.decode, noPartyIDs, account, orderCapacity, instrumentSecurityID, instrumentSecurityIDSource, side, orderQtyDataOrderQty, ordType, price, underlyingColPx, triggeringInstructionTriggerType, triggeringInstructionTriggerAction, triggeringInstructionTriggerPrice, triggeringInstructionTriggerSymbol, tradingSessionID, timeInForce, expireDate, execInst, execRestatementReason, allocID, settlCurrAmt, optionPremiumAmt, copyMsgIndicator, matchIncrement, maxFloor, openCloseIndicator, sMPLevel, sMPMethod, sMPID, trdMatchID, lastQty, lastPx, lastUnderlyingPx, some_bind] <;> rfl

structure ExecutionReportSuspended where
  noPartyIDs : List NoPartyIDs  -- tag 453
  account : Option (Terminated 1)  -- tag 1
  orderCapacity : Option (Terminated 1)  -- tag 528
  instrumentSecurityID : Terminated 1  -- tag 48
  instrumentSecurityIDSource : Terminated 1  -- tag 22
  orderQtyDataOrderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  underlyingColPx : Option (Terminated 1)  -- tag 21101
  triggeringInstructionTriggerType : Option (Terminated 1)  -- tag 1100
  triggeringInstructionTriggerAction : Option (Terminated 1)  -- tag 1101
  triggeringInstructionTriggerPrice : Option (Terminated 1)  -- tag 1102
  triggeringInstructionTriggerSymbol : Option (Terminated 1)  -- tag 1103
  tradingSessionID : Option (Terminated 1)  -- tag 336
  timeInForce : Terminated 1  -- tag 59
  expireDate : Option (Terminated 1)  -- tag 432
  execInst : Option (Terminated 1)  -- tag 18
  allocID : Option (Terminated 1)  -- tag 70
  copyMsgIndicator : Option (Terminated 1)  -- tag 797
  maxFloor : Option (Terminated 1)  -- tag 111
  matchIncrement : Option (Terminated 1)  -- tag 1089
  openCloseIndicator : Option (Terminated 1)  -- tag 20199
  sMPLevel : Option (Terminated 1)  -- tag 21114
  sMPMethod : Option (Terminated 1)  -- tag 21115
  sMPID : Option (Terminated 1)  -- tag 21116

def ExecutionReportSuspended.parts (record : ExecutionReportSuspended) : List Part :=
  [Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.optional [49] record.account,
   Part.optional [53, 50, 56] record.orderCapacity,
   Part.required [52, 56] record.instrumentSecurityID,
   Part.required [50, 50] record.instrumentSecurityIDSource,
   Part.required [51, 56] record.orderQtyDataOrderQty,
   Part.required [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.optional [50, 49, 49, 48, 49] record.underlyingColPx,
   Part.optional [49, 49, 48, 48] record.triggeringInstructionTriggerType,
   Part.optional [49, 49, 48, 49] record.triggeringInstructionTriggerAction,
   Part.optional [49, 49, 48, 50] record.triggeringInstructionTriggerPrice,
   Part.optional [49, 49, 48, 51] record.triggeringInstructionTriggerSymbol,
   Part.optional [51, 51, 54] record.tradingSessionID,
   Part.required [53, 57] record.timeInForce,
   Part.optional [52, 51, 50] record.expireDate,
   Part.optional [49, 56] record.execInst,
   Part.optional [55, 48] record.allocID,
   Part.optional [55, 57, 55] record.copyMsgIndicator,
   Part.optional [49, 49, 49] record.maxFloor,
   Part.optional [49, 48, 56, 57] record.matchIncrement,
   Part.optional [50, 48, 49, 57, 57] record.openCloseIndicator,
   Part.optional [50, 49, 49, 49, 52] record.sMPLevel,
   Part.optional [50, 49, 49, 49, 53] record.sMPMethod,
   Part.optional [50, 49, 49, 49, 54] record.sMPID]

def ExecutionReportSuspended.tags : List (List (List UInt8)) :=
  [[52, 53, 51] :: NoPartyIDs.members, [[49]], [[53, 50, 56]], [[52, 56]], [[50, 50]], [[51, 56]], [[52, 48]], [[52, 52]], [[50, 49, 49, 48, 49]], [[49, 49, 48, 48]], [[49, 49, 48, 49]], [[49, 49, 48, 50]], [[49, 49, 48, 51]], [[51, 51, 54]], [[53, 57]], [[52, 51, 50]], [[49, 56]], [[55, 48]], [[55, 57, 55]], [[49, 49, 49]], [[49, 48, 56, 57]], [[50, 48, 49, 57, 57]], [[50, 49, 49, 49, 52]], [[50, 49, 49, 49, 53]], [[50, 49, 49, 49, 54]]]

theorem ExecutionReportSuspended.shape (record : ExecutionReportSuspended) : record.parts.map Part.tags = ExecutionReportSuspended.tags := rfl

def ExecutionReportSuspended.decode (tokens : List Token) : Option ExecutionReportSuspended := do
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let account ← readOptional [49] tokens
  let orderCapacity ← readOptional [53, 50, 56] tokens
  let instrumentSecurityID ← readRequired [52, 56] tokens
  let instrumentSecurityIDSource ← readRequired [50, 50] tokens
  let orderQtyDataOrderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let underlyingColPx ← readOptional [50, 49, 49, 48, 49] tokens
  let triggeringInstructionTriggerType ← readOptional [49, 49, 48, 48] tokens
  let triggeringInstructionTriggerAction ← readOptional [49, 49, 48, 49] tokens
  let triggeringInstructionTriggerPrice ← readOptional [49, 49, 48, 50] tokens
  let triggeringInstructionTriggerSymbol ← readOptional [49, 49, 48, 51] tokens
  let tradingSessionID ← readOptional [51, 51, 54] tokens
  let timeInForce ← readRequired [53, 57] tokens
  let expireDate ← readOptional [52, 51, 50] tokens
  let execInst ← readOptional [49, 56] tokens
  let allocID ← readOptional [55, 48] tokens
  let copyMsgIndicator ← readOptional [55, 57, 55] tokens
  let maxFloor ← readOptional [49, 49, 49] tokens
  let matchIncrement ← readOptional [49, 48, 56, 57] tokens
  let openCloseIndicator ← readOptional [50, 48, 49, 57, 57] tokens
  let sMPLevel ← readOptional [50, 49, 49, 49, 52] tokens
  let sMPMethod ← readOptional [50, 49, 49, 49, 53] tokens
  let sMPID ← readOptional [50, 49, 49, 49, 54] tokens
  pure { noPartyIDs, account, orderCapacity, instrumentSecurityID, instrumentSecurityIDSource, orderQtyDataOrderQty, ordType, price, underlyingColPx, triggeringInstructionTriggerType, triggeringInstructionTriggerAction, triggeringInstructionTriggerPrice, triggeringInstructionTriggerSymbol, tradingSessionID, timeInForce, expireDate, execInst, allocID, copyMsgIndicator, maxFloor, matchIncrement, openCloseIndicator, sMPLevel, sMPMethod, sMPID }

theorem ExecutionReportSuspended.decode_agrees (record : ExecutionReportSuspended) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportSuspended.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportSuspended.decode tokens = some record := by
  have distinct : ExecutionReportSuspended.tags.flatten.Nodup := by decide +kernel
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have orderCapacity := readOptional_part [53, 50, 56] record.orderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have instrumentSecurityID := readRequired_part [52, 56] record.instrumentSecurityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have instrumentSecurityIDSource := readRequired_part [50, 50] record.instrumentSecurityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have orderQtyDataOrderQty := readRequired_part [51, 56] record.orderQtyDataOrderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have underlyingColPx := readOptional_part [50, 49, 49, 48, 49] record.underlyingColPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have triggeringInstructionTriggerType := readOptional_part [49, 49, 48, 48] record.triggeringInstructionTriggerType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have triggeringInstructionTriggerAction := readOptional_part [49, 49, 48, 49] record.triggeringInstructionTriggerAction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have triggeringInstructionTriggerPrice := readOptional_part [49, 49, 48, 50] record.triggeringInstructionTriggerPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have triggeringInstructionTriggerSymbol := readOptional_part [49, 49, 48, 51] record.triggeringInstructionTriggerSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have tradingSessionID := readOptional_part [51, 51, 54] record.tradingSessionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have timeInForce := readRequired_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have expireDate := readOptional_part [52, 51, 50] record.expireDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have allocID := readOptional_part [55, 48] record.allocID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have copyMsgIndicator := readOptional_part [55, 57, 55] record.copyMsgIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have maxFloor := readOptional_part [49, 49, 49] record.maxFloor tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have matchIncrement := readOptional_part [49, 48, 56, 57] record.matchIncrement tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have openCloseIndicator := readOptional_part [50, 48, 49, 57, 57] record.openCloseIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have sMPLevel := readOptional_part [50, 49, 49, 49, 52] record.sMPLevel tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have sMPMethod := readOptional_part [50, 49, 49, 49, 53] record.sMPMethod tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have sMPID := readOptional_part [50, 49, 49, 49, 54] record.sMPID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  simp only [ExecutionReportSuspended.decode, noPartyIDs, account, orderCapacity, instrumentSecurityID, instrumentSecurityIDSource, orderQtyDataOrderQty, ordType, price, underlyingColPx, triggeringInstructionTriggerType, triggeringInstructionTriggerAction, triggeringInstructionTriggerPrice, triggeringInstructionTriggerSymbol, tradingSessionID, timeInForce, expireDate, execInst, allocID, copyMsgIndicator, maxFloor, matchIncrement, openCloseIndicator, sMPLevel, sMPMethod, sMPID, some_bind] <;> rfl

structure ExecutionReportExpired where
  noPartyIDs : List NoPartyIDs  -- tag 453
  account : Option (Terminated 1)  -- tag 1
  orderCapacity : Option (Terminated 1)  -- tag 528
  instrumentSecurityID : Terminated 1  -- tag 48
  instrumentSecurityIDSource : Terminated 1  -- tag 22
  side : Terminated 1  -- tag 54
  orderQtyDataOrderQty : Option (Terminated 1)  -- tag 38
  ordType : Terminated 1  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  underlyingColPx : Option (Terminated 1)  -- tag 21101
  timeInForce : Terminated 1  -- tag 59
  execInst : Option (Terminated 1)  -- tag 18
  allocID : Option (Terminated 1)  -- tag 70
  copyMsgIndicator : Option (Terminated 1)  -- tag 797
  maxFloor : Option (Terminated 1)  -- tag 111
  matchIncrement : Option (Terminated 1)  -- tag 1089
  openCloseIndicator : Option (Terminated 1)  -- tag 20199

def ExecutionReportExpired.parts (record : ExecutionReportExpired) : List Part :=
  [Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.optional [49] record.account,
   Part.optional [53, 50, 56] record.orderCapacity,
   Part.required [52, 56] record.instrumentSecurityID,
   Part.required [50, 50] record.instrumentSecurityIDSource,
   Part.required [53, 52] record.side,
   Part.optional [51, 56] record.orderQtyDataOrderQty,
   Part.required [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.optional [50, 49, 49, 48, 49] record.underlyingColPx,
   Part.required [53, 57] record.timeInForce,
   Part.optional [49, 56] record.execInst,
   Part.optional [55, 48] record.allocID,
   Part.optional [55, 57, 55] record.copyMsgIndicator,
   Part.optional [49, 49, 49] record.maxFloor,
   Part.optional [49, 48, 56, 57] record.matchIncrement,
   Part.optional [50, 48, 49, 57, 57] record.openCloseIndicator]

def ExecutionReportExpired.tags : List (List (List UInt8)) :=
  [[52, 53, 51] :: NoPartyIDs.members, [[49]], [[53, 50, 56]], [[52, 56]], [[50, 50]], [[53, 52]], [[51, 56]], [[52, 48]], [[52, 52]], [[50, 49, 49, 48, 49]], [[53, 57]], [[49, 56]], [[55, 48]], [[55, 57, 55]], [[49, 49, 49]], [[49, 48, 56, 57]], [[50, 48, 49, 57, 57]]]

theorem ExecutionReportExpired.shape (record : ExecutionReportExpired) : record.parts.map Part.tags = ExecutionReportExpired.tags := rfl

def ExecutionReportExpired.decode (tokens : List Token) : Option ExecutionReportExpired := do
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let account ← readOptional [49] tokens
  let orderCapacity ← readOptional [53, 50, 56] tokens
  let instrumentSecurityID ← readRequired [52, 56] tokens
  let instrumentSecurityIDSource ← readRequired [50, 50] tokens
  let side ← readRequired [53, 52] tokens
  let orderQtyDataOrderQty ← readOptional [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let underlyingColPx ← readOptional [50, 49, 49, 48, 49] tokens
  let timeInForce ← readRequired [53, 57] tokens
  let execInst ← readOptional [49, 56] tokens
  let allocID ← readOptional [55, 48] tokens
  let copyMsgIndicator ← readOptional [55, 57, 55] tokens
  let maxFloor ← readOptional [49, 49, 49] tokens
  let matchIncrement ← readOptional [49, 48, 56, 57] tokens
  let openCloseIndicator ← readOptional [50, 48, 49, 57, 57] tokens
  pure { noPartyIDs, account, orderCapacity, instrumentSecurityID, instrumentSecurityIDSource, side, orderQtyDataOrderQty, ordType, price, underlyingColPx, timeInForce, execInst, allocID, copyMsgIndicator, maxFloor, matchIncrement, openCloseIndicator }

theorem ExecutionReportExpired.decode_agrees (record : ExecutionReportExpired) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportExpired.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportExpired.decode tokens = some record := by
  have distinct : ExecutionReportExpired.tags.flatten.Nodup := by decide +kernel
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have orderCapacity := readOptional_part [53, 50, 56] record.orderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have instrumentSecurityID := readRequired_part [52, 56] record.instrumentSecurityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have instrumentSecurityIDSource := readRequired_part [50, 50] record.instrumentSecurityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have orderQtyDataOrderQty := readOptional_part [51, 56] record.orderQtyDataOrderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have underlyingColPx := readOptional_part [50, 49, 49, 48, 49] record.underlyingColPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have timeInForce := readRequired_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have allocID := readOptional_part [55, 48] record.allocID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have copyMsgIndicator := readOptional_part [55, 57, 55] record.copyMsgIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have maxFloor := readOptional_part [49, 49, 49] record.maxFloor tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have matchIncrement := readOptional_part [49, 48, 56, 57] record.matchIncrement tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have openCloseIndicator := readOptional_part [50, 48, 49, 57, 57] record.openCloseIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  simp only [ExecutionReportExpired.decode, noPartyIDs, account, orderCapacity, instrumentSecurityID, instrumentSecurityIDSource, side, orderQtyDataOrderQty, ordType, price, underlyingColPx, timeInForce, execInst, allocID, copyMsgIndicator, maxFloor, matchIncrement, openCloseIndicator, some_bind] <;> rfl

structure NoLegs where
  legSymbol : Terminated 1  -- tag 600
  legSecurityID : Terminated 1  -- tag 602
  legSecurityIDSource : Terminated 1  -- tag 603
  legLastPx : Terminated 1  -- tag 637
  legLastQty : Terminated 1  -- tag 1418
  legTrdMatchID : Terminated 1  -- tag 20200
  legSide : Terminated 1  -- tag 624
  legRatioQty : Terminated 1  -- tag 623

def NoLegs.parts (record : NoLegs) : List Part :=
  [Part.required [54, 48, 48] record.legSymbol,
   Part.required [54, 48, 50] record.legSecurityID,
   Part.required [54, 48, 51] record.legSecurityIDSource,
   Part.required [54, 51, 55] record.legLastPx,
   Part.required [49, 52, 49, 56] record.legLastQty,
   Part.required [50, 48, 50, 48, 48] record.legTrdMatchID,
   Part.required [54, 50, 52] record.legSide,
   Part.required [54, 50, 51] record.legRatioQty]

def NoLegs.tags : List (List (List UInt8)) :=
  [[[54, 48, 48]], [[54, 48, 50]], [[54, 48, 51]], [[54, 51, 55]], [[49, 52, 49, 56]], [[50, 48, 50, 48, 48]], [[54, 50, 52]], [[54, 50, 51]]]

theorem NoLegs.shape (record : NoLegs) : record.parts.map Part.tags = NoLegs.tags := rfl

def NoLegs.decode (tokens : List Token) : Option NoLegs := do
  let legSymbol ← readRequired [54, 48, 48] tokens
  let legSecurityID ← readRequired [54, 48, 50] tokens
  let legSecurityIDSource ← readRequired [54, 48, 51] tokens
  let legLastPx ← readRequired [54, 51, 55] tokens
  let legLastQty ← readRequired [49, 52, 49, 56] tokens
  let legTrdMatchID ← readRequired [50, 48, 50, 48, 48] tokens
  let legSide ← readRequired [54, 50, 52] tokens
  let legRatioQty ← readRequired [54, 50, 51] tokens
  pure { legSymbol, legSecurityID, legSecurityIDSource, legLastPx, legLastQty, legTrdMatchID, legSide, legRatioQty }

theorem NoLegs.decode_agrees (record : NoLegs) (tokens : List Token)
    (agrees : ∀ tags ∈ NoLegs.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoLegs.decode tokens = some record := by
  have distinct : NoLegs.tags.flatten.Nodup := by decide +kernel
  have legSymbol := readRequired_part [54, 48, 48] record.legSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have legSecurityID := readRequired_part [54, 48, 50] record.legSecurityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have legSecurityIDSource := readRequired_part [54, 48, 51] record.legSecurityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have legLastPx := readRequired_part [54, 51, 55] record.legLastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have legLastQty := readRequired_part [49, 52, 49, 56] record.legLastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have legTrdMatchID := readRequired_part [50, 48, 50, 48, 48] record.legTrdMatchID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have legSide := readRequired_part [54, 50, 52] record.legSide tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have legRatioQty := readRequired_part [54, 50, 51] record.legRatioQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  simp only [NoLegs.decode, legSymbol, legSecurityID, legSecurityIDSource, legLastPx, legLastQty, legTrdMatchID, legSide, legRatioQty, some_bind] <;> rfl

def NoLegs.members : List (List UInt8) := NoLegs.tags.flatten

def NoLegs.encode (entry : NoLegs) : List Token := encodeParts entry.parts

theorem NoLegs.decode_encode (entry : NoLegs) : NoLegs.decode entry.encode = some entry :=
  NoLegs.decode_agrees entry _ (fun _ _ => rfl)

theorem NoLegs.within (entry : NoLegs) : ∀ token ∈ entry.encode, token.tag ∈ NoLegs.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoLegs.shape] at this

theorem NoLegs.led (entry : NoLegs) : Lead [54, 48, 48] entry.encode :=
  lead_parts [54, 48, 48] entry.legSymbol _ NoLegs.tags.tail rfl (by decide +kernel)

structure ExecutionReportTrade where
  noPartyIDs : List NoPartyIDs  -- tag 453
  trdMatchID : Terminated 1  -- tag 880
  comboMatchID : Terminated 1  -- tag 20034
  account : Option (Terminated 1)  -- tag 1
  instrumentSecurityID : Terminated 1  -- tag 48
  instrumentSecurityIDSource : Terminated 1  -- tag 22
  side : Terminated 1  -- tag 54
  ordType : Terminated 1  -- tag 40
  price : Terminated 1  -- tag 44
  timeInForce : Terminated 1  -- tag 59
  tradingSessionID : Option (Terminated 1)  -- tag 336
  lastQty : Option (Terminated 1)  -- tag 32
  lastPx : Option (Terminated 1)  -- tag 31
  multiLegReportingType : Terminated 1  -- tag 442
  noLegs : List NoLegs  -- tag 555
  lastFragment : Option (Terminated 1)  -- tag 893
  allocID : Option (Terminated 1)  -- tag 70
  copyMsgIndicator : Option (Terminated 1)  -- tag 797
  openCloseIndicator : Option (Terminated 1)  -- tag 20199

def ExecutionReportTrade.parts (record : ExecutionReportTrade) : List Part :=
  [Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.required [56, 56, 48] record.trdMatchID,
   Part.required [50, 48, 48, 51, 52] record.comboMatchID,
   Part.optional [49] record.account,
   Part.required [52, 56] record.instrumentSecurityID,
   Part.required [50, 50] record.instrumentSecurityIDSource,
   Part.required [53, 52] record.side,
   Part.required [52, 48] record.ordType,
   Part.required [52, 52] record.price,
   Part.required [53, 57] record.timeInForce,
   Part.optional [51, 51, 54] record.tradingSessionID,
   Part.optional [51, 50] record.lastQty,
   Part.optional [51, 49] record.lastPx,
   Part.required [52, 52, 50] record.multiLegReportingType,
   Part.group [53, 53, 53] NoLegs.members NoLegs.encode NoLegs.within record.noLegs,
   Part.optional [56, 57, 51] record.lastFragment,
   Part.optional [55, 48] record.allocID,
   Part.optional [55, 57, 55] record.copyMsgIndicator,
   Part.optional [50, 48, 49, 57, 57] record.openCloseIndicator]

def ExecutionReportTrade.tags : List (List (List UInt8)) :=
  [[52, 53, 51] :: NoPartyIDs.members, [[56, 56, 48]], [[50, 48, 48, 51, 52]], [[49]], [[52, 56]], [[50, 50]], [[53, 52]], [[52, 48]], [[52, 52]], [[53, 57]], [[51, 51, 54]], [[51, 50]], [[51, 49]], [[52, 52, 50]], [53, 53, 53] :: NoLegs.members, [[56, 57, 51]], [[55, 48]], [[55, 57, 55]], [[50, 48, 49, 57, 57]]]

theorem ExecutionReportTrade.shape (record : ExecutionReportTrade) : record.parts.map Part.tags = ExecutionReportTrade.tags := rfl

def ExecutionReportTrade.decode (tokens : List Token) : Option ExecutionReportTrade := do
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let trdMatchID ← readRequired [56, 56, 48] tokens
  let comboMatchID ← readRequired [50, 48, 48, 51, 52] tokens
  let account ← readOptional [49] tokens
  let instrumentSecurityID ← readRequired [52, 56] tokens
  let instrumentSecurityIDSource ← readRequired [50, 50] tokens
  let side ← readRequired [53, 52] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readRequired [52, 52] tokens
  let timeInForce ← readRequired [53, 57] tokens
  let tradingSessionID ← readOptional [51, 51, 54] tokens
  let lastQty ← readOptional [51, 50] tokens
  let lastPx ← readOptional [51, 49] tokens
  let multiLegReportingType ← readRequired [52, 52, 50] tokens
  let noLegs ← readGroup [53, 53, 53] [54, 48, 48] NoLegs.members NoLegs.decode tokens
  let lastFragment ← readOptional [56, 57, 51] tokens
  let allocID ← readOptional [55, 48] tokens
  let copyMsgIndicator ← readOptional [55, 57, 55] tokens
  let openCloseIndicator ← readOptional [50, 48, 49, 57, 57] tokens
  pure { noPartyIDs, trdMatchID, comboMatchID, account, instrumentSecurityID, instrumentSecurityIDSource, side, ordType, price, timeInForce, tradingSessionID, lastQty, lastPx, multiLegReportingType, noLegs, lastFragment, allocID, copyMsgIndicator, openCloseIndicator }

theorem ExecutionReportTrade.decode_agrees (record : ExecutionReportTrade) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportTrade.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportTrade.decode tokens = some record := by
  have distinct : ExecutionReportTrade.tags.flatten.Nodup := by decide +kernel
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have trdMatchID := readRequired_part [56, 56, 48] record.trdMatchID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have comboMatchID := readRequired_part [50, 48, 48, 51, 52] record.comboMatchID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have instrumentSecurityID := readRequired_part [52, 56] record.instrumentSecurityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have instrumentSecurityIDSource := readRequired_part [50, 50] record.instrumentSecurityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have price := readRequired_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have timeInForce := readRequired_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have tradingSessionID := readOptional_part [51, 51, 54] record.tradingSessionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have lastQty := readOptional_part [51, 50] record.lastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have lastPx := readOptional_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have multiLegReportingType := readRequired_part [52, 52, 50] record.multiLegReportingType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have noLegs := readGroup_part [53, 53, 53] [54, 48, 48] NoLegs.members NoLegs.encode NoLegs.within NoLegs.decode NoLegs.decode_encode NoLegs.led record.noLegs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have lastFragment := readOptional_part [56, 57, 51] record.lastFragment tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have allocID := readOptional_part [55, 48] record.allocID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have copyMsgIndicator := readOptional_part [55, 57, 55] record.copyMsgIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have openCloseIndicator := readOptional_part [50, 48, 49, 57, 57] record.openCloseIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  simp only [ExecutionReportTrade.decode, noPartyIDs, trdMatchID, comboMatchID, account, instrumentSecurityID, instrumentSecurityIDSource, side, ordType, price, timeInForce, tradingSessionID, lastQty, lastPx, multiLegReportingType, noLegs, lastFragment, allocID, copyMsgIndicator, openCloseIndicator, some_bind] <;> rfl

structure BusinessMessageReject where
  refSeqNum : Option (Terminated 1)  -- tag 45
  refMsgType : Terminated 1  -- tag 372
  businessRejectReason : Terminated 1  -- tag 380
  text : Option (Terminated 1)  -- tag 58

def BusinessMessageReject.parts (record : BusinessMessageReject) : List Part :=
  [Part.optional [52, 53] record.refSeqNum,
   Part.required [51, 55, 50] record.refMsgType,
   Part.required [51, 56, 48] record.businessRejectReason,
   Part.optional [53, 56] record.text]

def BusinessMessageReject.tags : List (List (List UInt8)) :=
  [[[52, 53]], [[51, 55, 50]], [[51, 56, 48]], [[53, 56]]]

theorem BusinessMessageReject.shape (record : BusinessMessageReject) : record.parts.map Part.tags = BusinessMessageReject.tags := rfl

def BusinessMessageReject.decode (tokens : List Token) : Option BusinessMessageReject := do
  let refSeqNum ← readOptional [52, 53] tokens
  let refMsgType ← readRequired [51, 55, 50] tokens
  let businessRejectReason ← readRequired [51, 56, 48] tokens
  let text ← readOptional [53, 56] tokens
  pure { refSeqNum, refMsgType, businessRejectReason, text }

theorem BusinessMessageReject.decode_agrees (record : BusinessMessageReject) (tokens : List Token)
    (agrees : ∀ tags ∈ BusinessMessageReject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    BusinessMessageReject.decode tokens = some record := by
  have distinct : BusinessMessageReject.tags.flatten.Nodup := by decide +kernel
  have refSeqNum := readOptional_part [52, 53] record.refSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have refMsgType := readRequired_part [51, 55, 50] record.refMsgType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have businessRejectReason := readRequired_part [51, 56, 48] record.businessRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [BusinessMessageReject.decode, refSeqNum, refMsgType, businessRejectReason, text, some_bind] <;> rfl

structure NoAssetAttributes where
  assetAttributeType : Terminated 1  -- tag 2305
  assetAttributeValue : Option (Terminated 1)  -- tag 2306

def NoAssetAttributes.parts (record : NoAssetAttributes) : List Part :=
  [Part.required [50, 51, 48, 53] record.assetAttributeType,
   Part.optional [50, 51, 48, 54] record.assetAttributeValue]

def NoAssetAttributes.tags : List (List (List UInt8)) :=
  [[[50, 51, 48, 53]], [[50, 51, 48, 54]]]

theorem NoAssetAttributes.shape (record : NoAssetAttributes) : record.parts.map Part.tags = NoAssetAttributes.tags := rfl

def NoAssetAttributes.decode (tokens : List Token) : Option NoAssetAttributes := do
  let assetAttributeType ← readRequired [50, 51, 48, 53] tokens
  let assetAttributeValue ← readOptional [50, 51, 48, 54] tokens
  pure { assetAttributeType, assetAttributeValue }

theorem NoAssetAttributes.decode_agrees (record : NoAssetAttributes) (tokens : List Token)
    (agrees : ∀ tags ∈ NoAssetAttributes.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoAssetAttributes.decode tokens = some record := by
  have distinct : NoAssetAttributes.tags.flatten.Nodup := by decide +kernel
  have assetAttributeType := readRequired_part [50, 51, 48, 53] record.assetAttributeType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have assetAttributeValue := readOptional_part [50, 51, 48, 54] record.assetAttributeValue tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [NoAssetAttributes.decode, assetAttributeType, assetAttributeValue, some_bind] <;> rfl

def NoAssetAttributes.members : List (List UInt8) := NoAssetAttributes.tags.flatten

def NoAssetAttributes.encode (entry : NoAssetAttributes) : List Token := encodeParts entry.parts

theorem NoAssetAttributes.decode_encode (entry : NoAssetAttributes) : NoAssetAttributes.decode entry.encode = some entry :=
  NoAssetAttributes.decode_agrees entry _ (fun _ _ => rfl)

theorem NoAssetAttributes.within (entry : NoAssetAttributes) : ∀ token ∈ entry.encode, token.tag ∈ NoAssetAttributes.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoAssetAttributes.shape] at this

theorem NoAssetAttributes.led (entry : NoAssetAttributes) : Lead [50, 51, 48, 53] entry.encode :=
  lead_parts [50, 51, 48, 53] entry.assetAttributeType _ NoAssetAttributes.tags.tail rfl (by decide +kernel)

structure SecurityDefinition where
  securityReqID : Terminated 1  -- tag 320
  securityResponseType : Terminated 1  -- tag 323
  instrumentSymbol : Terminated 1  -- tag 55
  instrumentSecurityID : Terminated 1  -- tag 48
  instrumentSecurityIDSource : Terminated 1  -- tag 22
  deferredPublicationTime : Option (Terminated 1)  -- tag 20013
  assetType : Option (Terminated 1)  -- tag 1940
  assetClass : Option (Terminated 1)  -- tag 1938
  assetSubClass : Option (Terminated 1)  -- tag 1939
  unitOfMeasure : Option (Terminated 1)  -- tag 996
  finenessNotation : Option (Terminated 1)  -- tag 21061
  metalWeightConversionFactor : Option (Terminated 1)  -- tag 21062
  fineness : Option (Terminated 1)  -- tag 21060
  unitOfMeasureQuantity : Option (Terminated 1)  -- tag 1147
  noAssetAttributes : List NoAssetAttributes  -- tag 2304
  text : Terminated 1  -- tag 58

def SecurityDefinition.parts (record : SecurityDefinition) : List Part :=
  [Part.required [51, 50, 48] record.securityReqID,
   Part.required [51, 50, 51] record.securityResponseType,
   Part.required [53, 53] record.instrumentSymbol,
   Part.required [52, 56] record.instrumentSecurityID,
   Part.required [50, 50] record.instrumentSecurityIDSource,
   Part.optional [50, 48, 48, 49, 51] record.deferredPublicationTime,
   Part.optional [49, 57, 52, 48] record.assetType,
   Part.optional [49, 57, 51, 56] record.assetClass,
   Part.optional [49, 57, 51, 57] record.assetSubClass,
   Part.optional [57, 57, 54] record.unitOfMeasure,
   Part.optional [50, 49, 48, 54, 49] record.finenessNotation,
   Part.optional [50, 49, 48, 54, 50] record.metalWeightConversionFactor,
   Part.optional [50, 49, 48, 54, 48] record.fineness,
   Part.optional [49, 49, 52, 55] record.unitOfMeasureQuantity,
   Part.group [50, 51, 48, 52] NoAssetAttributes.members NoAssetAttributes.encode NoAssetAttributes.within record.noAssetAttributes,
   Part.required [53, 56] record.text]

def SecurityDefinition.tags : List (List (List UInt8)) :=
  [[[51, 50, 48]], [[51, 50, 51]], [[53, 53]], [[52, 56]], [[50, 50]], [[50, 48, 48, 49, 51]], [[49, 57, 52, 48]], [[49, 57, 51, 56]], [[49, 57, 51, 57]], [[57, 57, 54]], [[50, 49, 48, 54, 49]], [[50, 49, 48, 54, 50]], [[50, 49, 48, 54, 48]], [[49, 49, 52, 55]], [50, 51, 48, 52] :: NoAssetAttributes.members, [[53, 56]]]

theorem SecurityDefinition.shape (record : SecurityDefinition) : record.parts.map Part.tags = SecurityDefinition.tags := rfl

def SecurityDefinition.decode (tokens : List Token) : Option SecurityDefinition := do
  let securityReqID ← readRequired [51, 50, 48] tokens
  let securityResponseType ← readRequired [51, 50, 51] tokens
  let instrumentSymbol ← readRequired [53, 53] tokens
  let instrumentSecurityID ← readRequired [52, 56] tokens
  let instrumentSecurityIDSource ← readRequired [50, 50] tokens
  let deferredPublicationTime ← readOptional [50, 48, 48, 49, 51] tokens
  let assetType ← readOptional [49, 57, 52, 48] tokens
  let assetClass ← readOptional [49, 57, 51, 56] tokens
  let assetSubClass ← readOptional [49, 57, 51, 57] tokens
  let unitOfMeasure ← readOptional [57, 57, 54] tokens
  let finenessNotation ← readOptional [50, 49, 48, 54, 49] tokens
  let metalWeightConversionFactor ← readOptional [50, 49, 48, 54, 50] tokens
  let fineness ← readOptional [50, 49, 48, 54, 48] tokens
  let unitOfMeasureQuantity ← readOptional [49, 49, 52, 55] tokens
  let noAssetAttributes ← readGroup [50, 51, 48, 52] [50, 51, 48, 53] NoAssetAttributes.members NoAssetAttributes.decode tokens
  let text ← readRequired [53, 56] tokens
  pure { securityReqID, securityResponseType, instrumentSymbol, instrumentSecurityID, instrumentSecurityIDSource, deferredPublicationTime, assetType, assetClass, assetSubClass, unitOfMeasure, finenessNotation, metalWeightConversionFactor, fineness, unitOfMeasureQuantity, noAssetAttributes, text }

theorem SecurityDefinition.decode_agrees (record : SecurityDefinition) (tokens : List Token)
    (agrees : ∀ tags ∈ SecurityDefinition.tags, select tags tokens = select tags (encodeParts record.parts)) :
    SecurityDefinition.decode tokens = some record := by
  have distinct : SecurityDefinition.tags.flatten.Nodup := by decide +kernel
  have securityReqID := readRequired_part [51, 50, 48] record.securityReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityResponseType := readRequired_part [51, 50, 51] record.securityResponseType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have instrumentSymbol := readRequired_part [53, 53] record.instrumentSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have instrumentSecurityID := readRequired_part [52, 56] record.instrumentSecurityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have instrumentSecurityIDSource := readRequired_part [50, 50] record.instrumentSecurityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have deferredPublicationTime := readOptional_part [50, 48, 48, 49, 51] record.deferredPublicationTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have assetType := readOptional_part [49, 57, 52, 48] record.assetType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have assetClass := readOptional_part [49, 57, 51, 56] record.assetClass tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have assetSubClass := readOptional_part [49, 57, 51, 57] record.assetSubClass tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have unitOfMeasure := readOptional_part [57, 57, 54] record.unitOfMeasure tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have finenessNotation := readOptional_part [50, 49, 48, 54, 49] record.finenessNotation tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have metalWeightConversionFactor := readOptional_part [50, 49, 48, 54, 50] record.metalWeightConversionFactor tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have fineness := readOptional_part [50, 49, 48, 54, 48] record.fineness tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have unitOfMeasureQuantity := readOptional_part [49, 49, 52, 55] record.unitOfMeasureQuantity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have noAssetAttributes := readGroup_part [50, 51, 48, 52] [50, 51, 48, 53] NoAssetAttributes.members NoAssetAttributes.encode NoAssetAttributes.within NoAssetAttributes.decode NoAssetAttributes.decode_encode NoAssetAttributes.led record.noAssetAttributes tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have text := readRequired_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  simp only [SecurityDefinition.decode, securityReqID, securityResponseType, instrumentSymbol, instrumentSecurityID, instrumentSecurityIDSource, deferredPublicationTime, assetType, assetClass, assetSubClass, unitOfMeasure, finenessNotation, metalWeightConversionFactor, fineness, unitOfMeasureQuantity, noAssetAttributes, text, some_bind] <;> rfl

structure NoSecurityAltID where
  securityAltID : Terminated 1  -- tag 455
  securityAltIDSource : Terminated 1  -- tag 456

def NoSecurityAltID.parts (record : NoSecurityAltID) : List Part :=
  [Part.required [52, 53, 53] record.securityAltID,
   Part.required [52, 53, 54] record.securityAltIDSource]

def NoSecurityAltID.tags : List (List (List UInt8)) :=
  [[[52, 53, 53]], [[52, 53, 54]]]

theorem NoSecurityAltID.shape (record : NoSecurityAltID) : record.parts.map Part.tags = NoSecurityAltID.tags := rfl

def NoSecurityAltID.decode (tokens : List Token) : Option NoSecurityAltID := do
  let securityAltID ← readRequired [52, 53, 53] tokens
  let securityAltIDSource ← readRequired [52, 53, 54] tokens
  pure { securityAltID, securityAltIDSource }

theorem NoSecurityAltID.decode_agrees (record : NoSecurityAltID) (tokens : List Token)
    (agrees : ∀ tags ∈ NoSecurityAltID.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoSecurityAltID.decode tokens = some record := by
  have distinct : NoSecurityAltID.tags.flatten.Nodup := by decide +kernel
  have securityAltID := readRequired_part [52, 53, 53] record.securityAltID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityAltIDSource := readRequired_part [52, 53, 54] record.securityAltIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [NoSecurityAltID.decode, securityAltID, securityAltIDSource, some_bind] <;> rfl

def NoSecurityAltID.members : List (List UInt8) := NoSecurityAltID.tags.flatten

def NoSecurityAltID.encode (entry : NoSecurityAltID) : List Token := encodeParts entry.parts

theorem NoSecurityAltID.decode_encode (entry : NoSecurityAltID) : NoSecurityAltID.decode entry.encode = some entry :=
  NoSecurityAltID.decode_agrees entry _ (fun _ _ => rfl)

theorem NoSecurityAltID.within (entry : NoSecurityAltID) : ∀ token ∈ entry.encode, token.tag ∈ NoSecurityAltID.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoSecurityAltID.shape] at this

theorem NoSecurityAltID.led (entry : NoSecurityAltID) : Lead [52, 53, 53] entry.encode :=
  lead_parts [52, 53, 53] entry.securityAltID _ NoSecurityAltID.tags.tail rfl (by decide +kernel)

structure SecurityDefinitionUpdateReport where
  securityReqID : Terminated 1  -- tag 320
  securityUpdateAction : Terminated 1  -- tag 980
  instrumentSymbol : Terminated 1  -- tag 55
  instrumentSecurityID : Terminated 1  -- tag 48
  instrumentSecurityIDSource : Terminated 1  -- tag 22
  noSecurityAltID : List NoSecurityAltID  -- tag 454
  noLegs : List NoLegs  -- tag 555
  assetType : Option (Terminated 1)  -- tag 1940
  assetClass : Option (Terminated 1)  -- tag 1938
  assetSubClass : Option (Terminated 1)  -- tag 1939
  unitOfMeasure : Option (Terminated 1)  -- tag 996
  finenessNotation : Option (Terminated 1)  -- tag 21061
  metalWeightConversionFactor : Option (Terminated 1)  -- tag 21062
  fineness : Option (Terminated 1)  -- tag 21060
  unitOfMeasureQuantity : Option (Terminated 1)  -- tag 1147
  noAssetAttributes : List NoAssetAttributes  -- tag 2304

def SecurityDefinitionUpdateReport.parts (record : SecurityDefinitionUpdateReport) : List Part :=
  [Part.required [51, 50, 48] record.securityReqID,
   Part.required [57, 56, 48] record.securityUpdateAction,
   Part.required [53, 53] record.instrumentSymbol,
   Part.required [52, 56] record.instrumentSecurityID,
   Part.required [50, 50] record.instrumentSecurityIDSource,
   Part.group [52, 53, 52] NoSecurityAltID.members NoSecurityAltID.encode NoSecurityAltID.within record.noSecurityAltID,
   Part.group [53, 53, 53] NoLegs.members NoLegs.encode NoLegs.within record.noLegs,
   Part.optional [49, 57, 52, 48] record.assetType,
   Part.optional [49, 57, 51, 56] record.assetClass,
   Part.optional [49, 57, 51, 57] record.assetSubClass,
   Part.optional [57, 57, 54] record.unitOfMeasure,
   Part.optional [50, 49, 48, 54, 49] record.finenessNotation,
   Part.optional [50, 49, 48, 54, 50] record.metalWeightConversionFactor,
   Part.optional [50, 49, 48, 54, 48] record.fineness,
   Part.optional [49, 49, 52, 55] record.unitOfMeasureQuantity,
   Part.group [50, 51, 48, 52] NoAssetAttributes.members NoAssetAttributes.encode NoAssetAttributes.within record.noAssetAttributes]

def SecurityDefinitionUpdateReport.tags : List (List (List UInt8)) :=
  [[[51, 50, 48]], [[57, 56, 48]], [[53, 53]], [[52, 56]], [[50, 50]], [52, 53, 52] :: NoSecurityAltID.members, [53, 53, 53] :: NoLegs.members, [[49, 57, 52, 48]], [[49, 57, 51, 56]], [[49, 57, 51, 57]], [[57, 57, 54]], [[50, 49, 48, 54, 49]], [[50, 49, 48, 54, 50]], [[50, 49, 48, 54, 48]], [[49, 49, 52, 55]], [50, 51, 48, 52] :: NoAssetAttributes.members]

theorem SecurityDefinitionUpdateReport.shape (record : SecurityDefinitionUpdateReport) : record.parts.map Part.tags = SecurityDefinitionUpdateReport.tags := rfl

def SecurityDefinitionUpdateReport.decode (tokens : List Token) : Option SecurityDefinitionUpdateReport := do
  let securityReqID ← readRequired [51, 50, 48] tokens
  let securityUpdateAction ← readRequired [57, 56, 48] tokens
  let instrumentSymbol ← readRequired [53, 53] tokens
  let instrumentSecurityID ← readRequired [52, 56] tokens
  let instrumentSecurityIDSource ← readRequired [50, 50] tokens
  let noSecurityAltID ← readGroup [52, 53, 52] [52, 53, 53] NoSecurityAltID.members NoSecurityAltID.decode tokens
  let noLegs ← readGroup [53, 53, 53] [54, 48, 48] NoLegs.members NoLegs.decode tokens
  let assetType ← readOptional [49, 57, 52, 48] tokens
  let assetClass ← readOptional [49, 57, 51, 56] tokens
  let assetSubClass ← readOptional [49, 57, 51, 57] tokens
  let unitOfMeasure ← readOptional [57, 57, 54] tokens
  let finenessNotation ← readOptional [50, 49, 48, 54, 49] tokens
  let metalWeightConversionFactor ← readOptional [50, 49, 48, 54, 50] tokens
  let fineness ← readOptional [50, 49, 48, 54, 48] tokens
  let unitOfMeasureQuantity ← readOptional [49, 49, 52, 55] tokens
  let noAssetAttributes ← readGroup [50, 51, 48, 52] [50, 51, 48, 53] NoAssetAttributes.members NoAssetAttributes.decode tokens
  pure { securityReqID, securityUpdateAction, instrumentSymbol, instrumentSecurityID, instrumentSecurityIDSource, noSecurityAltID, noLegs, assetType, assetClass, assetSubClass, unitOfMeasure, finenessNotation, metalWeightConversionFactor, fineness, unitOfMeasureQuantity, noAssetAttributes }

theorem SecurityDefinitionUpdateReport.decode_agrees (record : SecurityDefinitionUpdateReport) (tokens : List Token)
    (agrees : ∀ tags ∈ SecurityDefinitionUpdateReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    SecurityDefinitionUpdateReport.decode tokens = some record := by
  have distinct : SecurityDefinitionUpdateReport.tags.flatten.Nodup := by decide +kernel
  have securityReqID := readRequired_part [51, 50, 48] record.securityReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityUpdateAction := readRequired_part [57, 56, 48] record.securityUpdateAction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have instrumentSymbol := readRequired_part [53, 53] record.instrumentSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have instrumentSecurityID := readRequired_part [52, 56] record.instrumentSecurityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have instrumentSecurityIDSource := readRequired_part [50, 50] record.instrumentSecurityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have noSecurityAltID := readGroup_part [52, 53, 52] [52, 53, 53] NoSecurityAltID.members NoSecurityAltID.encode NoSecurityAltID.within NoSecurityAltID.decode NoSecurityAltID.decode_encode NoSecurityAltID.led record.noSecurityAltID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have noLegs := readGroup_part [53, 53, 53] [54, 48, 48] NoLegs.members NoLegs.encode NoLegs.within NoLegs.decode NoLegs.decode_encode NoLegs.led record.noLegs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have assetType := readOptional_part [49, 57, 52, 48] record.assetType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have assetClass := readOptional_part [49, 57, 51, 56] record.assetClass tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have assetSubClass := readOptional_part [49, 57, 51, 57] record.assetSubClass tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have unitOfMeasure := readOptional_part [57, 57, 54] record.unitOfMeasure tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have finenessNotation := readOptional_part [50, 49, 48, 54, 49] record.finenessNotation tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have metalWeightConversionFactor := readOptional_part [50, 49, 48, 54, 50] record.metalWeightConversionFactor tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have fineness := readOptional_part [50, 49, 48, 54, 48] record.fineness tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have unitOfMeasureQuantity := readOptional_part [49, 49, 52, 55] record.unitOfMeasureQuantity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have noAssetAttributes := readGroup_part [50, 51, 48, 52] [50, 51, 48, 53] NoAssetAttributes.members NoAssetAttributes.encode NoAssetAttributes.within NoAssetAttributes.decode NoAssetAttributes.decode_encode NoAssetAttributes.led record.noAssetAttributes tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  simp only [SecurityDefinitionUpdateReport.decode, securityReqID, securityUpdateAction, instrumentSymbol, instrumentSecurityID, instrumentSecurityIDSource, noSecurityAltID, noLegs, assetType, assetClass, assetSubClass, unitOfMeasure, finenessNotation, metalWeightConversionFactor, fineness, unitOfMeasureQuantity, noAssetAttributes, some_bind] <;> rfl

structure NoQuoteEntriesAck where
  quoteEntryID : Terminated 1  -- tag 299
  quoteEntryRejectReason : Option (Terminated 1)  -- tag 368

def NoQuoteEntriesAck.parts (record : NoQuoteEntriesAck) : List Part :=
  [Part.required [50, 57, 57] record.quoteEntryID,
   Part.optional [51, 54, 56] record.quoteEntryRejectReason]

def NoQuoteEntriesAck.tags : List (List (List UInt8)) :=
  [[[50, 57, 57]], [[51, 54, 56]]]

theorem NoQuoteEntriesAck.shape (record : NoQuoteEntriesAck) : record.parts.map Part.tags = NoQuoteEntriesAck.tags := rfl

def NoQuoteEntriesAck.decode (tokens : List Token) : Option NoQuoteEntriesAck := do
  let quoteEntryID ← readRequired [50, 57, 57] tokens
  let quoteEntryRejectReason ← readOptional [51, 54, 56] tokens
  pure { quoteEntryID, quoteEntryRejectReason }

theorem NoQuoteEntriesAck.decode_agrees (record : NoQuoteEntriesAck) (tokens : List Token)
    (agrees : ∀ tags ∈ NoQuoteEntriesAck.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoQuoteEntriesAck.decode tokens = some record := by
  have distinct : NoQuoteEntriesAck.tags.flatten.Nodup := by decide +kernel
  have quoteEntryID := readRequired_part [50, 57, 57] record.quoteEntryID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have quoteEntryRejectReason := readOptional_part [51, 54, 56] record.quoteEntryRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [NoQuoteEntriesAck.decode, quoteEntryID, quoteEntryRejectReason, some_bind] <;> rfl

def NoQuoteEntriesAck.members : List (List UInt8) := NoQuoteEntriesAck.tags.flatten

def NoQuoteEntriesAck.encode (entry : NoQuoteEntriesAck) : List Token := encodeParts entry.parts

theorem NoQuoteEntriesAck.decode_encode (entry : NoQuoteEntriesAck) : NoQuoteEntriesAck.decode entry.encode = some entry :=
  NoQuoteEntriesAck.decode_agrees entry _ (fun _ _ => rfl)

theorem NoQuoteEntriesAck.within (entry : NoQuoteEntriesAck) : ∀ token ∈ entry.encode, token.tag ∈ NoQuoteEntriesAck.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoQuoteEntriesAck.shape] at this

theorem NoQuoteEntriesAck.led (entry : NoQuoteEntriesAck) : Lead [50, 57, 57] entry.encode :=
  lead_parts [50, 57, 57] entry.quoteEntryID _ NoQuoteEntriesAck.tags.tail rfl (by decide +kernel)

structure NoQuoteSetsAck where
  quoteSetID : Terminated 1  -- tag 302
  noQuoteEntriesAck : List NoQuoteEntriesAck  -- tag 295

def NoQuoteSetsAck.parts (record : NoQuoteSetsAck) : List Part :=
  [Part.required [51, 48, 50] record.quoteSetID,
   Part.group [50, 57, 53] NoQuoteEntriesAck.members NoQuoteEntriesAck.encode NoQuoteEntriesAck.within record.noQuoteEntriesAck]

def NoQuoteSetsAck.tags : List (List (List UInt8)) :=
  [[[51, 48, 50]], [50, 57, 53] :: NoQuoteEntriesAck.members]

theorem NoQuoteSetsAck.shape (record : NoQuoteSetsAck) : record.parts.map Part.tags = NoQuoteSetsAck.tags := rfl

def NoQuoteSetsAck.decode (tokens : List Token) : Option NoQuoteSetsAck := do
  let quoteSetID ← readRequired [51, 48, 50] tokens
  let noQuoteEntriesAck ← readGroup [50, 57, 53] [50, 57, 57] NoQuoteEntriesAck.members NoQuoteEntriesAck.decode tokens
  pure { quoteSetID, noQuoteEntriesAck }

theorem NoQuoteSetsAck.decode_agrees (record : NoQuoteSetsAck) (tokens : List Token)
    (agrees : ∀ tags ∈ NoQuoteSetsAck.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoQuoteSetsAck.decode tokens = some record := by
  have distinct : NoQuoteSetsAck.tags.flatten.Nodup := by decide +kernel
  have quoteSetID := readRequired_part [51, 48, 50] record.quoteSetID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have noQuoteEntriesAck := readGroup_part [50, 57, 53] [50, 57, 57] NoQuoteEntriesAck.members NoQuoteEntriesAck.encode NoQuoteEntriesAck.within NoQuoteEntriesAck.decode NoQuoteEntriesAck.decode_encode NoQuoteEntriesAck.led record.noQuoteEntriesAck tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [NoQuoteSetsAck.decode, quoteSetID, noQuoteEntriesAck, some_bind] <;> rfl

def NoQuoteSetsAck.members : List (List UInt8) := NoQuoteSetsAck.tags.flatten

def NoQuoteSetsAck.encode (entry : NoQuoteSetsAck) : List Token := encodeParts entry.parts

theorem NoQuoteSetsAck.decode_encode (entry : NoQuoteSetsAck) : NoQuoteSetsAck.decode entry.encode = some entry :=
  NoQuoteSetsAck.decode_agrees entry _ (fun _ _ => rfl)

theorem NoQuoteSetsAck.within (entry : NoQuoteSetsAck) : ∀ token ∈ entry.encode, token.tag ∈ NoQuoteSetsAck.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoQuoteSetsAck.shape] at this

theorem NoQuoteSetsAck.led (entry : NoQuoteSetsAck) : Lead [51, 48, 50] entry.encode :=
  lead_parts [51, 48, 50] entry.quoteSetID _ NoQuoteSetsAck.tags.tail rfl (by decide +kernel)

structure MassQuoteAcknowledgement where
  quoteID : Option (Terminated 1)  -- tag 117
  quoteStatus : Terminated 1  -- tag 297
  quoteResponseLevel : Terminated 1  -- tag 301
  quoteType : Terminated 1  -- tag 537
  noPartyIDs : List NoPartyIDs  -- tag 453
  noQuoteSetsAck : List NoQuoteSetsAck  -- tag 296
  text : Option (Terminated 1)  -- tag 58
  quoteRejectReason : Option (Terminated 1)  -- tag 300

def MassQuoteAcknowledgement.parts (record : MassQuoteAcknowledgement) : List Part :=
  [Part.optional [49, 49, 55] record.quoteID,
   Part.required [50, 57, 55] record.quoteStatus,
   Part.required [51, 48, 49] record.quoteResponseLevel,
   Part.required [53, 51, 55] record.quoteType,
   Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.group [50, 57, 54] NoQuoteSetsAck.members NoQuoteSetsAck.encode NoQuoteSetsAck.within record.noQuoteSetsAck,
   Part.optional [53, 56] record.text,
   Part.optional [51, 48, 48] record.quoteRejectReason]

def MassQuoteAcknowledgement.tags : List (List (List UInt8)) :=
  [[[49, 49, 55]], [[50, 57, 55]], [[51, 48, 49]], [[53, 51, 55]], [52, 53, 51] :: NoPartyIDs.members, [50, 57, 54] :: NoQuoteSetsAck.members, [[53, 56]], [[51, 48, 48]]]

theorem MassQuoteAcknowledgement.shape (record : MassQuoteAcknowledgement) : record.parts.map Part.tags = MassQuoteAcknowledgement.tags := rfl

def MassQuoteAcknowledgement.decode (tokens : List Token) : Option MassQuoteAcknowledgement := do
  let quoteID ← readOptional [49, 49, 55] tokens
  let quoteStatus ← readRequired [50, 57, 55] tokens
  let quoteResponseLevel ← readRequired [51, 48, 49] tokens
  let quoteType ← readRequired [53, 51, 55] tokens
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let noQuoteSetsAck ← readGroup [50, 57, 54] [51, 48, 50] NoQuoteSetsAck.members NoQuoteSetsAck.decode tokens
  let text ← readOptional [53, 56] tokens
  let quoteRejectReason ← readOptional [51, 48, 48] tokens
  pure { quoteID, quoteStatus, quoteResponseLevel, quoteType, noPartyIDs, noQuoteSetsAck, text, quoteRejectReason }

theorem MassQuoteAcknowledgement.decode_agrees (record : MassQuoteAcknowledgement) (tokens : List Token)
    (agrees : ∀ tags ∈ MassQuoteAcknowledgement.tags, select tags tokens = select tags (encodeParts record.parts)) :
    MassQuoteAcknowledgement.decode tokens = some record := by
  have distinct : MassQuoteAcknowledgement.tags.flatten.Nodup := by decide +kernel
  have quoteID := readOptional_part [49, 49, 55] record.quoteID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have quoteStatus := readRequired_part [50, 57, 55] record.quoteStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have quoteResponseLevel := readRequired_part [51, 48, 49] record.quoteResponseLevel tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have quoteType := readRequired_part [53, 51, 55] record.quoteType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have noQuoteSetsAck := readGroup_part [50, 57, 54] [51, 48, 50] NoQuoteSetsAck.members NoQuoteSetsAck.encode NoQuoteSetsAck.within NoQuoteSetsAck.decode NoQuoteSetsAck.decode_encode NoQuoteSetsAck.led record.noQuoteSetsAck tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have quoteRejectReason := readOptional_part [51, 48, 48] record.quoteRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  simp only [MassQuoteAcknowledgement.decode, quoteID, quoteStatus, quoteResponseLevel, quoteType, noPartyIDs, noQuoteSetsAck, text, quoteRejectReason, some_bind] <;> rfl

structure NoRelatedSym where
  instrumentSymbol : Terminated 1  -- tag 55
  instrumentSecurityID : Option (Terminated 1)  -- tag 48
  instrumentSecurityIDSource : Option (Terminated 1)  -- tag 22
  side : Option (Terminated 1)  -- tag 54
  minQty : Option (Terminated 1)  -- tag 110

def NoRelatedSym.parts (record : NoRelatedSym) : List Part :=
  [Part.required [53, 53] record.instrumentSymbol,
   Part.optional [52, 56] record.instrumentSecurityID,
   Part.optional [50, 50] record.instrumentSecurityIDSource,
   Part.optional [53, 52] record.side,
   Part.optional [49, 49, 48] record.minQty]

def NoRelatedSym.tags : List (List (List UInt8)) :=
  [[[53, 53]], [[52, 56]], [[50, 50]], [[53, 52]], [[49, 49, 48]]]

theorem NoRelatedSym.shape (record : NoRelatedSym) : record.parts.map Part.tags = NoRelatedSym.tags := rfl

def NoRelatedSym.decode (tokens : List Token) : Option NoRelatedSym := do
  let instrumentSymbol ← readRequired [53, 53] tokens
  let instrumentSecurityID ← readOptional [52, 56] tokens
  let instrumentSecurityIDSource ← readOptional [50, 50] tokens
  let side ← readOptional [53, 52] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  pure { instrumentSymbol, instrumentSecurityID, instrumentSecurityIDSource, side, minQty }

theorem NoRelatedSym.decode_agrees (record : NoRelatedSym) (tokens : List Token)
    (agrees : ∀ tags ∈ NoRelatedSym.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoRelatedSym.decode tokens = some record := by
  have distinct : NoRelatedSym.tags.flatten.Nodup := by decide +kernel
  have instrumentSymbol := readRequired_part [53, 53] record.instrumentSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have instrumentSecurityID := readOptional_part [52, 56] record.instrumentSecurityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have instrumentSecurityIDSource := readOptional_part [50, 50] record.instrumentSecurityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [NoRelatedSym.decode, instrumentSymbol, instrumentSecurityID, instrumentSecurityIDSource, side, minQty, some_bind] <;> rfl

def NoRelatedSym.members : List (List UInt8) := NoRelatedSym.tags.flatten

def NoRelatedSym.encode (entry : NoRelatedSym) : List Token := encodeParts entry.parts

theorem NoRelatedSym.decode_encode (entry : NoRelatedSym) : NoRelatedSym.decode entry.encode = some entry :=
  NoRelatedSym.decode_agrees entry _ (fun _ _ => rfl)

theorem NoRelatedSym.within (entry : NoRelatedSym) : ∀ token ∈ entry.encode, token.tag ∈ NoRelatedSym.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoRelatedSym.shape] at this

theorem NoRelatedSym.led (entry : NoRelatedSym) : Lead [53, 53] entry.encode :=
  lead_parts [53, 53] entry.instrumentSymbol _ NoRelatedSym.tags.tail rfl (by decide +kernel)

structure NoRootPartyIDs where
  rootPartyID : Terminated 1  -- tag 1117
  rootPartyIDSource : Terminated 1  -- tag 1118
  rootPartyRole : Terminated 1  -- tag 1119

def NoRootPartyIDs.parts (record : NoRootPartyIDs) : List Part :=
  [Part.required [49, 49, 49, 55] record.rootPartyID,
   Part.required [49, 49, 49, 56] record.rootPartyIDSource,
   Part.required [49, 49, 49, 57] record.rootPartyRole]

def NoRootPartyIDs.tags : List (List (List UInt8)) :=
  [[[49, 49, 49, 55]], [[49, 49, 49, 56]], [[49, 49, 49, 57]]]

theorem NoRootPartyIDs.shape (record : NoRootPartyIDs) : record.parts.map Part.tags = NoRootPartyIDs.tags := rfl

def NoRootPartyIDs.decode (tokens : List Token) : Option NoRootPartyIDs := do
  let rootPartyID ← readRequired [49, 49, 49, 55] tokens
  let rootPartyIDSource ← readRequired [49, 49, 49, 56] tokens
  let rootPartyRole ← readRequired [49, 49, 49, 57] tokens
  pure { rootPartyID, rootPartyIDSource, rootPartyRole }

theorem NoRootPartyIDs.decode_agrees (record : NoRootPartyIDs) (tokens : List Token)
    (agrees : ∀ tags ∈ NoRootPartyIDs.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoRootPartyIDs.decode tokens = some record := by
  have distinct : NoRootPartyIDs.tags.flatten.Nodup := by decide +kernel
  have rootPartyID := readRequired_part [49, 49, 49, 55] record.rootPartyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have rootPartyIDSource := readRequired_part [49, 49, 49, 56] record.rootPartyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have rootPartyRole := readRequired_part [49, 49, 49, 57] record.rootPartyRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [NoRootPartyIDs.decode, rootPartyID, rootPartyIDSource, rootPartyRole, some_bind] <;> rfl

def NoRootPartyIDs.members : List (List UInt8) := NoRootPartyIDs.tags.flatten

def NoRootPartyIDs.encode (entry : NoRootPartyIDs) : List Token := encodeParts entry.parts

theorem NoRootPartyIDs.decode_encode (entry : NoRootPartyIDs) : NoRootPartyIDs.decode entry.encode = some entry :=
  NoRootPartyIDs.decode_agrees entry _ (fun _ _ => rfl)

theorem NoRootPartyIDs.within (entry : NoRootPartyIDs) : ∀ token ∈ entry.encode, token.tag ∈ NoRootPartyIDs.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoRootPartyIDs.shape] at this

theorem NoRootPartyIDs.led (entry : NoRootPartyIDs) : Lead [49, 49, 49, 55] entry.encode :=
  lead_parts [49, 49, 49, 55] entry.rootPartyID _ NoRootPartyIDs.tags.tail rfl (by decide +kernel)

structure QuoteRequest where
  quoteReqID : Terminated 1  -- tag 131
  noRelatedSym : List NoRelatedSym  -- tag 146
  noRootPartyIDs : List NoRootPartyIDs  -- tag 1116

def QuoteRequest.parts (record : QuoteRequest) : List Part :=
  [Part.required [49, 51, 49] record.quoteReqID,
   Part.group [49, 52, 54] NoRelatedSym.members NoRelatedSym.encode NoRelatedSym.within record.noRelatedSym,
   Part.group [49, 49, 49, 54] NoRootPartyIDs.members NoRootPartyIDs.encode NoRootPartyIDs.within record.noRootPartyIDs]

def QuoteRequest.tags : List (List (List UInt8)) :=
  [[[49, 51, 49]], [49, 52, 54] :: NoRelatedSym.members, [49, 49, 49, 54] :: NoRootPartyIDs.members]

theorem QuoteRequest.shape (record : QuoteRequest) : record.parts.map Part.tags = QuoteRequest.tags := rfl

def QuoteRequest.decode (tokens : List Token) : Option QuoteRequest := do
  let quoteReqID ← readRequired [49, 51, 49] tokens
  let noRelatedSym ← readGroup [49, 52, 54] [53, 53] NoRelatedSym.members NoRelatedSym.decode tokens
  let noRootPartyIDs ← readGroup [49, 49, 49, 54] [49, 49, 49, 55] NoRootPartyIDs.members NoRootPartyIDs.decode tokens
  pure { quoteReqID, noRelatedSym, noRootPartyIDs }

theorem QuoteRequest.decode_agrees (record : QuoteRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ QuoteRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    QuoteRequest.decode tokens = some record := by
  have distinct : QuoteRequest.tags.flatten.Nodup := by decide +kernel
  have quoteReqID := readRequired_part [49, 51, 49] record.quoteReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have noRelatedSym := readGroup_part [49, 52, 54] [53, 53] NoRelatedSym.members NoRelatedSym.encode NoRelatedSym.within NoRelatedSym.decode NoRelatedSym.decode_encode NoRelatedSym.led record.noRelatedSym tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have noRootPartyIDs := readGroup_part [49, 49, 49, 54] [49, 49, 49, 55] NoRootPartyIDs.members NoRootPartyIDs.encode NoRootPartyIDs.within NoRootPartyIDs.decode NoRootPartyIDs.decode_encode NoRootPartyIDs.led record.noRootPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [QuoteRequest.decode, quoteReqID, noRelatedSym, noRootPartyIDs, some_bind] <;> rfl

structure QuoteRequestReject where
  quoteReqID : Terminated 1  -- tag 131
  quoteRequstRejectReason : Terminated 1  -- tag 658
  noRelatedSym : List NoRelatedSym  -- tag 146
  text : Option (Terminated 1)  -- tag 58

def QuoteRequestReject.parts (record : QuoteRequestReject) : List Part :=
  [Part.required [49, 51, 49] record.quoteReqID,
   Part.required [54, 53, 56] record.quoteRequstRejectReason,
   Part.group [49, 52, 54] NoRelatedSym.members NoRelatedSym.encode NoRelatedSym.within record.noRelatedSym,
   Part.optional [53, 56] record.text]

def QuoteRequestReject.tags : List (List (List UInt8)) :=
  [[[49, 51, 49]], [[54, 53, 56]], [49, 52, 54] :: NoRelatedSym.members, [[53, 56]]]

theorem QuoteRequestReject.shape (record : QuoteRequestReject) : record.parts.map Part.tags = QuoteRequestReject.tags := rfl

def QuoteRequestReject.decode (tokens : List Token) : Option QuoteRequestReject := do
  let quoteReqID ← readRequired [49, 51, 49] tokens
  let quoteRequstRejectReason ← readRequired [54, 53, 56] tokens
  let noRelatedSym ← readGroup [49, 52, 54] [53, 53] NoRelatedSym.members NoRelatedSym.decode tokens
  let text ← readOptional [53, 56] tokens
  pure { quoteReqID, quoteRequstRejectReason, noRelatedSym, text }

theorem QuoteRequestReject.decode_agrees (record : QuoteRequestReject) (tokens : List Token)
    (agrees : ∀ tags ∈ QuoteRequestReject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    QuoteRequestReject.decode tokens = some record := by
  have distinct : QuoteRequestReject.tags.flatten.Nodup := by decide +kernel
  have quoteReqID := readRequired_part [49, 51, 49] record.quoteReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have quoteRequstRejectReason := readRequired_part [54, 53, 56] record.quoteRequstRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have noRelatedSym := readGroup_part [49, 52, 54] [53, 53] NoRelatedSym.members NoRelatedSym.encode NoRelatedSym.within NoRelatedSym.decode NoRelatedSym.decode_encode NoRelatedSym.led record.noRelatedSym tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [QuoteRequestReject.decode, quoteReqID, quoteRequstRejectReason, noRelatedSym, text, some_bind] <;> rfl

structure TradeCaptureReport where
  tradeReportID : Terminated 1  -- tag 571
  tradeReportTransType : Terminated 1  -- tag 487
  instrumentSymbol : Option (Terminated 1)  -- tag 55
  instrumentSecurityID : Option (Terminated 1)  -- tag 48
  transactTime : Terminated 1  -- tag 60

def TradeCaptureReport.parts (record : TradeCaptureReport) : List Part :=
  [Part.required [53, 55, 49] record.tradeReportID,
   Part.required [52, 56, 55] record.tradeReportTransType,
   Part.optional [53, 53] record.instrumentSymbol,
   Part.optional [52, 56] record.instrumentSecurityID,
   Part.required [54, 48] record.transactTime]

def TradeCaptureReport.tags : List (List (List UInt8)) :=
  [[[53, 55, 49]], [[52, 56, 55]], [[53, 53]], [[52, 56]], [[54, 48]]]

theorem TradeCaptureReport.shape (record : TradeCaptureReport) : record.parts.map Part.tags = TradeCaptureReport.tags := rfl

def TradeCaptureReport.decode (tokens : List Token) : Option TradeCaptureReport := do
  let tradeReportID ← readRequired [53, 55, 49] tokens
  let tradeReportTransType ← readRequired [52, 56, 55] tokens
  let instrumentSymbol ← readOptional [53, 53] tokens
  let instrumentSecurityID ← readOptional [52, 56] tokens
  let transactTime ← readRequired [54, 48] tokens
  pure { tradeReportID, tradeReportTransType, instrumentSymbol, instrumentSecurityID, transactTime }

theorem TradeCaptureReport.decode_agrees (record : TradeCaptureReport) (tokens : List Token)
    (agrees : ∀ tags ∈ TradeCaptureReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TradeCaptureReport.decode tokens = some record := by
  have distinct : TradeCaptureReport.tags.flatten.Nodup := by decide +kernel
  have tradeReportID := readRequired_part [53, 55, 49] record.tradeReportID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have tradeReportTransType := readRequired_part [52, 56, 55] record.tradeReportTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have instrumentSymbol := readOptional_part [53, 53] record.instrumentSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have instrumentSecurityID := readOptional_part [52, 56] record.instrumentSecurityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [TradeCaptureReport.decode, tradeReportID, tradeReportTransType, instrumentSymbol, instrumentSecurityID, transactTime, some_bind] <;> rfl

structure NoSides where
  side : Terminated 1  -- tag 54
  orderID : Terminated 1  -- tag 37
  noPartyIDs : Terminated 1  -- tag 453
  partyID : Terminated 1  -- tag 448
  partyIDSource : Terminated 1  -- tag 447
  partyRole : Terminated 1  -- tag 452
  account : Option (Terminated 1)  -- tag 1
  orderCapacity : Option (Terminated 1)  -- tag 528
  allocID : Option (Terminated 1)  -- tag 70
  transBkdTime : Option (Terminated 1)  -- tag 483
  openCloseIndicator : Option (Terminated 1)  -- tag 20199

def NoSides.parts (record : NoSides) : List Part :=
  [Part.required [53, 52] record.side,
   Part.required [51, 55] record.orderID,
   Part.required [52, 53, 51] record.noPartyIDs,
   Part.required [52, 52, 56] record.partyID,
   Part.required [52, 52, 55] record.partyIDSource,
   Part.required [52, 53, 50] record.partyRole,
   Part.optional [49] record.account,
   Part.optional [53, 50, 56] record.orderCapacity,
   Part.optional [55, 48] record.allocID,
   Part.optional [52, 56, 51] record.transBkdTime,
   Part.optional [50, 48, 49, 57, 57] record.openCloseIndicator]

def NoSides.tags : List (List (List UInt8)) :=
  [[[53, 52]], [[51, 55]], [[52, 53, 51]], [[52, 52, 56]], [[52, 52, 55]], [[52, 53, 50]], [[49]], [[53, 50, 56]], [[55, 48]], [[52, 56, 51]], [[50, 48, 49, 57, 57]]]

theorem NoSides.shape (record : NoSides) : record.parts.map Part.tags = NoSides.tags := rfl

def NoSides.decode (tokens : List Token) : Option NoSides := do
  let side ← readRequired [53, 52] tokens
  let orderID ← readRequired [51, 55] tokens
  let noPartyIDs ← readRequired [52, 53, 51] tokens
  let partyID ← readRequired [52, 52, 56] tokens
  let partyIDSource ← readRequired [52, 52, 55] tokens
  let partyRole ← readRequired [52, 53, 50] tokens
  let account ← readOptional [49] tokens
  let orderCapacity ← readOptional [53, 50, 56] tokens
  let allocID ← readOptional [55, 48] tokens
  let transBkdTime ← readOptional [52, 56, 51] tokens
  let openCloseIndicator ← readOptional [50, 48, 49, 57, 57] tokens
  pure { side, orderID, noPartyIDs, partyID, partyIDSource, partyRole, account, orderCapacity, allocID, transBkdTime, openCloseIndicator }

theorem NoSides.decode_agrees (record : NoSides) (tokens : List Token)
    (agrees : ∀ tags ∈ NoSides.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoSides.decode tokens = some record := by
  have distinct : NoSides.tags.flatten.Nodup := by decide +kernel
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have noPartyIDs := readRequired_part [52, 53, 51] record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have partyID := readRequired_part [52, 52, 56] record.partyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have partyIDSource := readRequired_part [52, 52, 55] record.partyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have partyRole := readRequired_part [52, 53, 50] record.partyRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have orderCapacity := readOptional_part [53, 50, 56] record.orderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have allocID := readOptional_part [55, 48] record.allocID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have transBkdTime := readOptional_part [52, 56, 51] record.transBkdTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have openCloseIndicator := readOptional_part [50, 48, 49, 57, 57] record.openCloseIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  simp only [NoSides.decode, side, orderID, noPartyIDs, partyID, partyIDSource, partyRole, account, orderCapacity, allocID, transBkdTime, openCloseIndicator, some_bind] <;> rfl

def NoSides.members : List (List UInt8) := NoSides.tags.flatten

def NoSides.encode (entry : NoSides) : List Token := encodeParts entry.parts

theorem NoSides.decode_encode (entry : NoSides) : NoSides.decode entry.encode = some entry :=
  NoSides.decode_agrees entry _ (fun _ _ => rfl)

theorem NoSides.within (entry : NoSides) : ∀ token ∈ entry.encode, token.tag ∈ NoSides.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoSides.shape] at this

theorem NoSides.led (entry : NoSides) : Lead [53, 52] entry.encode :=
  lead_parts [53, 52] entry.side _ NoSides.tags.tail rfl (by decide +kernel)

structure TrdMatchID where
  orderReference : Terminated 1  -- tag 20009
  positionEffect : Option (Terminated 1)  -- tag 77

def TrdMatchID.parts (record : TrdMatchID) : List Part :=
  [Part.required [50, 48, 48, 48, 57] record.orderReference,
   Part.optional [55, 55] record.positionEffect]

def TrdMatchID.tags : List (List (List UInt8)) :=
  [[[50, 48, 48, 48, 57]], [[55, 55]]]

theorem TrdMatchID.shape (record : TrdMatchID) : record.parts.map Part.tags = TrdMatchID.tags := rfl

def TrdMatchID.decode (tokens : List Token) : Option TrdMatchID := do
  let orderReference ← readRequired [50, 48, 48, 48, 57] tokens
  let positionEffect ← readOptional [55, 55] tokens
  pure { orderReference, positionEffect }

theorem TrdMatchID.decode_agrees (record : TrdMatchID) (tokens : List Token)
    (agrees : ∀ tags ∈ TrdMatchID.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TrdMatchID.decode tokens = some record := by
  have distinct : TrdMatchID.tags.flatten.Nodup := by decide +kernel
  have orderReference := readRequired_part [50, 48, 48, 48, 57] record.orderReference tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have positionEffect := readOptional_part [55, 55] record.positionEffect tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [TrdMatchID.decode, orderReference, positionEffect, some_bind] <;> rfl

def TrdMatchID.members : List (List UInt8) := TrdMatchID.tags.flatten

def TrdMatchID.encode (entry : TrdMatchID) : List Token := encodeParts entry.parts

theorem TrdMatchID.decode_encode (entry : TrdMatchID) : TrdMatchID.decode entry.encode = some entry :=
  TrdMatchID.decode_agrees entry _ (fun _ _ => rfl)

theorem TrdMatchID.within (entry : TrdMatchID) : ∀ token ∈ entry.encode, token.tag ∈ TrdMatchID.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [TrdMatchID.shape] at this

theorem TrdMatchID.led (entry : TrdMatchID) : Lead [50, 48, 48, 48, 57] entry.encode :=
  lead_parts [50, 48, 48, 48, 57] entry.orderReference _ TrdMatchID.tags.tail rfl (by decide +kernel)

structure SecondaryTradeReportRefID where
  tradeAllocIndicator : Terminated 1  -- tag 826
  noAllocs : Terminated 1  -- tag 78
  allocAccount : Terminated 1  -- tag 79
  noNested2PartyIDs : Terminated 1  -- tag 756
  nested2PartyID : Option (Terminated 1)  -- tag 757
  nested2PartyIDSource : Option (Terminated 1)  -- tag 758
  nested2PartyRole : Option (Terminated 1)  -- tag 759
  individualAllocID : Option (Terminated 1)  -- tag 467

def SecondaryTradeReportRefID.parts (record : SecondaryTradeReportRefID) : List Part :=
  [Part.required [56, 50, 54] record.tradeAllocIndicator,
   Part.required [55, 56] record.noAllocs,
   Part.required [55, 57] record.allocAccount,
   Part.required [55, 53, 54] record.noNested2PartyIDs,
   Part.optional [55, 53, 55] record.nested2PartyID,
   Part.optional [55, 53, 56] record.nested2PartyIDSource,
   Part.optional [55, 53, 57] record.nested2PartyRole,
   Part.optional [52, 54, 55] record.individualAllocID]

def SecondaryTradeReportRefID.tags : List (List (List UInt8)) :=
  [[[56, 50, 54]], [[55, 56]], [[55, 57]], [[55, 53, 54]], [[55, 53, 55]], [[55, 53, 56]], [[55, 53, 57]], [[52, 54, 55]]]

theorem SecondaryTradeReportRefID.shape (record : SecondaryTradeReportRefID) : record.parts.map Part.tags = SecondaryTradeReportRefID.tags := rfl

def SecondaryTradeReportRefID.decode (tokens : List Token) : Option SecondaryTradeReportRefID := do
  let tradeAllocIndicator ← readRequired [56, 50, 54] tokens
  let noAllocs ← readRequired [55, 56] tokens
  let allocAccount ← readRequired [55, 57] tokens
  let noNested2PartyIDs ← readRequired [55, 53, 54] tokens
  let nested2PartyID ← readOptional [55, 53, 55] tokens
  let nested2PartyIDSource ← readOptional [55, 53, 56] tokens
  let nested2PartyRole ← readOptional [55, 53, 57] tokens
  let individualAllocID ← readOptional [52, 54, 55] tokens
  pure { tradeAllocIndicator, noAllocs, allocAccount, noNested2PartyIDs, nested2PartyID, nested2PartyIDSource, nested2PartyRole, individualAllocID }

theorem SecondaryTradeReportRefID.decode_agrees (record : SecondaryTradeReportRefID) (tokens : List Token)
    (agrees : ∀ tags ∈ SecondaryTradeReportRefID.tags, select tags tokens = select tags (encodeParts record.parts)) :
    SecondaryTradeReportRefID.decode tokens = some record := by
  have distinct : SecondaryTradeReportRefID.tags.flatten.Nodup := by decide +kernel
  have tradeAllocIndicator := readRequired_part [56, 50, 54] record.tradeAllocIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have noAllocs := readRequired_part [55, 56] record.noAllocs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have allocAccount := readRequired_part [55, 57] record.allocAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have noNested2PartyIDs := readRequired_part [55, 53, 54] record.noNested2PartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have nested2PartyID := readOptional_part [55, 53, 55] record.nested2PartyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have nested2PartyIDSource := readOptional_part [55, 53, 56] record.nested2PartyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have nested2PartyRole := readOptional_part [55, 53, 57] record.nested2PartyRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have individualAllocID := readOptional_part [52, 54, 55] record.individualAllocID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  simp only [SecondaryTradeReportRefID.decode, tradeAllocIndicator, noAllocs, allocAccount, noNested2PartyIDs, nested2PartyID, nested2PartyIDSource, nested2PartyRole, individualAllocID, some_bind] <;> rfl

def SecondaryTradeReportRefID.members : List (List UInt8) := SecondaryTradeReportRefID.tags.flatten

def SecondaryTradeReportRefID.encode (entry : SecondaryTradeReportRefID) : List Token := encodeParts entry.parts

theorem SecondaryTradeReportRefID.decode_encode (entry : SecondaryTradeReportRefID) : SecondaryTradeReportRefID.decode entry.encode = some entry :=
  SecondaryTradeReportRefID.decode_agrees entry _ (fun _ _ => rfl)

theorem SecondaryTradeReportRefID.within (entry : SecondaryTradeReportRefID) : ∀ token ∈ entry.encode, token.tag ∈ SecondaryTradeReportRefID.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [SecondaryTradeReportRefID.shape] at this

theorem SecondaryTradeReportRefID.led (entry : SecondaryTradeReportRefID) : Lead [56, 50, 54] entry.encode :=
  lead_parts [56, 50, 54] entry.tradeAllocIndicator _ SecondaryTradeReportRefID.tags.tail rfl (by decide +kernel)

structure NoCollateralAmounts where
  currentCollateralAmount : Terminated 1  -- tag 1704

def NoCollateralAmounts.parts (record : NoCollateralAmounts) : List Part :=
  [Part.required [49, 55, 48, 52] record.currentCollateralAmount]

def NoCollateralAmounts.tags : List (List (List UInt8)) :=
  [[[49, 55, 48, 52]]]

theorem NoCollateralAmounts.shape (record : NoCollateralAmounts) : record.parts.map Part.tags = NoCollateralAmounts.tags := rfl

def NoCollateralAmounts.decode (tokens : List Token) : Option NoCollateralAmounts := do
  let currentCollateralAmount ← readRequired [49, 55, 48, 52] tokens
  pure { currentCollateralAmount }

theorem NoCollateralAmounts.decode_agrees (record : NoCollateralAmounts) (tokens : List Token)
    (agrees : ∀ tags ∈ NoCollateralAmounts.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoCollateralAmounts.decode tokens = some record := by
  have distinct : NoCollateralAmounts.tags.flatten.Nodup := by decide +kernel
  have currentCollateralAmount := readRequired_part [49, 55, 48, 52] record.currentCollateralAmount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [NoCollateralAmounts.decode, currentCollateralAmount, some_bind] <;> rfl

def NoCollateralAmounts.members : List (List UInt8) := NoCollateralAmounts.tags.flatten

def NoCollateralAmounts.encode (entry : NoCollateralAmounts) : List Token := encodeParts entry.parts

theorem NoCollateralAmounts.decode_encode (entry : NoCollateralAmounts) : NoCollateralAmounts.decode entry.encode = some entry :=
  NoCollateralAmounts.decode_agrees entry _ (fun _ _ => rfl)

theorem NoCollateralAmounts.within (entry : NoCollateralAmounts) : ∀ token ∈ entry.encode, token.tag ∈ NoCollateralAmounts.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoCollateralAmounts.shape] at this

theorem NoCollateralAmounts.led (entry : NoCollateralAmounts) : Lead [49, 55, 48, 52] entry.encode :=
  lead_parts [49, 55, 48, 52] entry.currentCollateralAmount _ NoCollateralAmounts.tags.tail rfl (by decide +kernel)

structure TradeCaptureReportSubmit where
  trdType : Terminated 1  -- tag 828
  previouslyReported : Terminated 1  -- tag 570
  noRootPartyIDs : List NoRootPartyIDs  -- tag 1116
  instrumentSecurityIDSource : Option (Terminated 1)  -- tag 22
  lastQty : Terminated 1  -- tag 32
  lastPx : Terminated 1  -- tag 31
  lastUnderlyingPx : Option (Terminated 1)  -- tag 21100
  tradeDate : Terminated 1  -- tag 75
  settlDate : Option (Terminated 1)  -- tag 64
  noSides : List NoSides  -- tag 552
  tradeID : Terminated 1  -- tag 1003
  tradeReportRefID : Terminated 1  -- tag 572
  secondaryTradeReportID : Terminated 1  -- tag 818
  matchStatus : Terminated 1  -- tag 573
  trdMatchID : List TrdMatchID  -- tag 880
  clearingBusinessDate : Option (Terminated 1)  -- tag 715
  dealNumber : Option (Terminated 1)  -- tag 21102
  tradeReportState : Terminated 1  -- tag 21103
  tradeReportSubState : Terminated 1  -- tag 21104
  tradeReportInstrType : Option (Terminated 1)  -- tag 21105
  traderReportReason : Option (Terminated 1)  -- tag 21106
  authorizationState : Option (Terminated 1)  -- tag 21107
  affimationState : Option (Terminated 1)  -- tag 21108
  deliveryUnit : Option (Terminated 1)  -- tag 21109
  origClearingBusinessDate : Option (Terminated 1)  -- tag 21110
  secondaryTradeReportRefID : List SecondaryTradeReportRefID  -- tag 881
  secondaryTradeID : Option (Terminated 1)  -- tag 1040
  origTradeID : Option (Terminated 1)  -- tag 1126
  origSecondaryTradeID : Option (Terminated 1)  -- tag 1127
  trdSubType : Terminated 1  -- tag 829
  settlementPrice : Option (Terminated 1)  -- tag 730
  withHoldingTax : Option (Terminated 1)  -- tag 20017
  repoInterestAmt : Option (Terminated 1)  -- tag 20018
  noCollateralAmounts : List NoCollateralAmounts  -- tag 1703
  correspondingPrice : Option (Terminated 1)  -- tag 20007
  consideration : Option (Terminated 1)  -- tag 20008
  comboMatchID : Option (Terminated 1)  -- tag 20034
  orderQtyDataOrderQty : Option (Terminated 1)  -- tag 38
  grossTradeAmt : Option (Terminated 1)  -- tag 381
  optionPremiumAmt : Option (Terminated 1)  -- tag 20015
  secondaryTrdType : Option (Terminated 1)  -- tag 855
  secondaryAllocID : Option (Terminated 1)  -- tag 793
  copyMsgIndicator : Option (Terminated 1)  -- tag 797

def TradeCaptureReportSubmit.parts (record : TradeCaptureReportSubmit) : List Part :=
  [Part.required [56, 50, 56] record.trdType,
   Part.required [53, 55, 48] record.previouslyReported,
   Part.group [49, 49, 49, 54] NoRootPartyIDs.members NoRootPartyIDs.encode NoRootPartyIDs.within record.noRootPartyIDs,
   Part.optional [50, 50] record.instrumentSecurityIDSource,
   Part.required [51, 50] record.lastQty,
   Part.required [51, 49] record.lastPx,
   Part.optional [50, 49, 49, 48, 48] record.lastUnderlyingPx,
   Part.required [55, 53] record.tradeDate,
   Part.optional [54, 52] record.settlDate,
   Part.group [53, 53, 50] NoSides.members NoSides.encode NoSides.within record.noSides,
   Part.required [49, 48, 48, 51] record.tradeID,
   Part.required [53, 55, 50] record.tradeReportRefID,
   Part.required [56, 49, 56] record.secondaryTradeReportID,
   Part.required [53, 55, 51] record.matchStatus,
   Part.group [56, 56, 48] TrdMatchID.members TrdMatchID.encode TrdMatchID.within record.trdMatchID,
   Part.optional [55, 49, 53] record.clearingBusinessDate,
   Part.optional [50, 49, 49, 48, 50] record.dealNumber,
   Part.required [50, 49, 49, 48, 51] record.tradeReportState,
   Part.required [50, 49, 49, 48, 52] record.tradeReportSubState,
   Part.optional [50, 49, 49, 48, 53] record.tradeReportInstrType,
   Part.optional [50, 49, 49, 48, 54] record.traderReportReason,
   Part.optional [50, 49, 49, 48, 55] record.authorizationState,
   Part.optional [50, 49, 49, 48, 56] record.affimationState,
   Part.optional [50, 49, 49, 48, 57] record.deliveryUnit,
   Part.optional [50, 49, 49, 49, 48] record.origClearingBusinessDate,
   Part.group [56, 56, 49] SecondaryTradeReportRefID.members SecondaryTradeReportRefID.encode SecondaryTradeReportRefID.within record.secondaryTradeReportRefID,
   Part.optional [49, 48, 52, 48] record.secondaryTradeID,
   Part.optional [49, 49, 50, 54] record.origTradeID,
   Part.optional [49, 49, 50, 55] record.origSecondaryTradeID,
   Part.required [56, 50, 57] record.trdSubType,
   Part.optional [55, 51, 48] record.settlementPrice,
   Part.optional [50, 48, 48, 49, 55] record.withHoldingTax,
   Part.optional [50, 48, 48, 49, 56] record.repoInterestAmt,
   Part.group [49, 55, 48, 51] NoCollateralAmounts.members NoCollateralAmounts.encode NoCollateralAmounts.within record.noCollateralAmounts,
   Part.optional [50, 48, 48, 48, 55] record.correspondingPrice,
   Part.optional [50, 48, 48, 48, 56] record.consideration,
   Part.optional [50, 48, 48, 51, 52] record.comboMatchID,
   Part.optional [51, 56] record.orderQtyDataOrderQty,
   Part.optional [51, 56, 49] record.grossTradeAmt,
   Part.optional [50, 48, 48, 49, 53] record.optionPremiumAmt,
   Part.optional [56, 53, 53] record.secondaryTrdType,
   Part.optional [55, 57, 51] record.secondaryAllocID,
   Part.optional [55, 57, 55] record.copyMsgIndicator]

def TradeCaptureReportSubmit.tags : List (List (List UInt8)) :=
  [[[56, 50, 56]], [[53, 55, 48]], [49, 49, 49, 54] :: NoRootPartyIDs.members, [[50, 50]], [[51, 50]], [[51, 49]], [[50, 49, 49, 48, 48]], [[55, 53]], [[54, 52]], [53, 53, 50] :: NoSides.members, [[49, 48, 48, 51]], [[53, 55, 50]], [[56, 49, 56]], [[53, 55, 51]], [56, 56, 48] :: TrdMatchID.members, [[55, 49, 53]], [[50, 49, 49, 48, 50]], [[50, 49, 49, 48, 51]], [[50, 49, 49, 48, 52]], [[50, 49, 49, 48, 53]], [[50, 49, 49, 48, 54]], [[50, 49, 49, 48, 55]], [[50, 49, 49, 48, 56]], [[50, 49, 49, 48, 57]], [[50, 49, 49, 49, 48]], [56, 56, 49] :: SecondaryTradeReportRefID.members, [[49, 48, 52, 48]], [[49, 49, 50, 54]], [[49, 49, 50, 55]], [[56, 50, 57]], [[55, 51, 48]], [[50, 48, 48, 49, 55]], [[50, 48, 48, 49, 56]], [49, 55, 48, 51] :: NoCollateralAmounts.members, [[50, 48, 48, 48, 55]], [[50, 48, 48, 48, 56]], [[50, 48, 48, 51, 52]], [[51, 56]], [[51, 56, 49]], [[50, 48, 48, 49, 53]], [[56, 53, 53]], [[55, 57, 51]], [[55, 57, 55]]]

theorem TradeCaptureReportSubmit.shape (record : TradeCaptureReportSubmit) : record.parts.map Part.tags = TradeCaptureReportSubmit.tags := rfl

def TradeCaptureReportSubmit.decode (tokens : List Token) : Option TradeCaptureReportSubmit := do
  let trdType ← readRequired [56, 50, 56] tokens
  let previouslyReported ← readRequired [53, 55, 48] tokens
  let noRootPartyIDs ← readGroup [49, 49, 49, 54] [49, 49, 49, 55] NoRootPartyIDs.members NoRootPartyIDs.decode tokens
  let instrumentSecurityIDSource ← readOptional [50, 50] tokens
  let lastQty ← readRequired [51, 50] tokens
  let lastPx ← readRequired [51, 49] tokens
  let lastUnderlyingPx ← readOptional [50, 49, 49, 48, 48] tokens
  let tradeDate ← readRequired [55, 53] tokens
  let settlDate ← readOptional [54, 52] tokens
  let noSides ← readGroup [53, 53, 50] [53, 52] NoSides.members NoSides.decode tokens
  let tradeID ← readRequired [49, 48, 48, 51] tokens
  let tradeReportRefID ← readRequired [53, 55, 50] tokens
  let secondaryTradeReportID ← readRequired [56, 49, 56] tokens
  let matchStatus ← readRequired [53, 55, 51] tokens
  let trdMatchID ← readGroup [56, 56, 48] [50, 48, 48, 48, 57] TrdMatchID.members TrdMatchID.decode tokens
  let clearingBusinessDate ← readOptional [55, 49, 53] tokens
  let dealNumber ← readOptional [50, 49, 49, 48, 50] tokens
  let tradeReportState ← readRequired [50, 49, 49, 48, 51] tokens
  let tradeReportSubState ← readRequired [50, 49, 49, 48, 52] tokens
  let tradeReportInstrType ← readOptional [50, 49, 49, 48, 53] tokens
  let traderReportReason ← readOptional [50, 49, 49, 48, 54] tokens
  let authorizationState ← readOptional [50, 49, 49, 48, 55] tokens
  let affimationState ← readOptional [50, 49, 49, 48, 56] tokens
  let deliveryUnit ← readOptional [50, 49, 49, 48, 57] tokens
  let origClearingBusinessDate ← readOptional [50, 49, 49, 49, 48] tokens
  let secondaryTradeReportRefID ← readGroup [56, 56, 49] [56, 50, 54] SecondaryTradeReportRefID.members SecondaryTradeReportRefID.decode tokens
  let secondaryTradeID ← readOptional [49, 48, 52, 48] tokens
  let origTradeID ← readOptional [49, 49, 50, 54] tokens
  let origSecondaryTradeID ← readOptional [49, 49, 50, 55] tokens
  let trdSubType ← readRequired [56, 50, 57] tokens
  let settlementPrice ← readOptional [55, 51, 48] tokens
  let withHoldingTax ← readOptional [50, 48, 48, 49, 55] tokens
  let repoInterestAmt ← readOptional [50, 48, 48, 49, 56] tokens
  let noCollateralAmounts ← readGroup [49, 55, 48, 51] [49, 55, 48, 52] NoCollateralAmounts.members NoCollateralAmounts.decode tokens
  let correspondingPrice ← readOptional [50, 48, 48, 48, 55] tokens
  let consideration ← readOptional [50, 48, 48, 48, 56] tokens
  let comboMatchID ← readOptional [50, 48, 48, 51, 52] tokens
  let orderQtyDataOrderQty ← readOptional [51, 56] tokens
  let grossTradeAmt ← readOptional [51, 56, 49] tokens
  let optionPremiumAmt ← readOptional [50, 48, 48, 49, 53] tokens
  let secondaryTrdType ← readOptional [56, 53, 53] tokens
  let secondaryAllocID ← readOptional [55, 57, 51] tokens
  let copyMsgIndicator ← readOptional [55, 57, 55] tokens
  pure { trdType, previouslyReported, noRootPartyIDs, instrumentSecurityIDSource, lastQty, lastPx, lastUnderlyingPx, tradeDate, settlDate, noSides, tradeID, tradeReportRefID, secondaryTradeReportID, matchStatus, trdMatchID, clearingBusinessDate, dealNumber, tradeReportState, tradeReportSubState, tradeReportInstrType, traderReportReason, authorizationState, affimationState, deliveryUnit, origClearingBusinessDate, secondaryTradeReportRefID, secondaryTradeID, origTradeID, origSecondaryTradeID, trdSubType, settlementPrice, withHoldingTax, repoInterestAmt, noCollateralAmounts, correspondingPrice, consideration, comboMatchID, orderQtyDataOrderQty, grossTradeAmt, optionPremiumAmt, secondaryTrdType, secondaryAllocID, copyMsgIndicator }

theorem TradeCaptureReportSubmit.decode_agrees (record : TradeCaptureReportSubmit) (tokens : List Token)
    (agrees : ∀ tags ∈ TradeCaptureReportSubmit.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TradeCaptureReportSubmit.decode tokens = some record := by
  have distinct : TradeCaptureReportSubmit.tags.flatten.Nodup := by decide +kernel
  have trdType := readRequired_part [56, 50, 56] record.trdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have previouslyReported := readRequired_part [53, 55, 48] record.previouslyReported tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have noRootPartyIDs := readGroup_part [49, 49, 49, 54] [49, 49, 49, 55] NoRootPartyIDs.members NoRootPartyIDs.encode NoRootPartyIDs.within NoRootPartyIDs.decode NoRootPartyIDs.decode_encode NoRootPartyIDs.led record.noRootPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have instrumentSecurityIDSource := readOptional_part [50, 50] record.instrumentSecurityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have lastQty := readRequired_part [51, 50] record.lastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have lastPx := readRequired_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have lastUnderlyingPx := readOptional_part [50, 49, 49, 48, 48] record.lastUnderlyingPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have tradeDate := readRequired_part [55, 53] record.tradeDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have settlDate := readOptional_part [54, 52] record.settlDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have noSides := readGroup_part [53, 53, 50] [53, 52] NoSides.members NoSides.encode NoSides.within NoSides.decode NoSides.decode_encode NoSides.led record.noSides tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have tradeID := readRequired_part [49, 48, 48, 51] record.tradeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have tradeReportRefID := readRequired_part [53, 55, 50] record.tradeReportRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have secondaryTradeReportID := readRequired_part [56, 49, 56] record.secondaryTradeReportID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have matchStatus := readRequired_part [53, 55, 51] record.matchStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have trdMatchID := readGroup_part [56, 56, 48] [50, 48, 48, 48, 57] TrdMatchID.members TrdMatchID.encode TrdMatchID.within TrdMatchID.decode TrdMatchID.decode_encode TrdMatchID.led record.trdMatchID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have clearingBusinessDate := readOptional_part [55, 49, 53] record.clearingBusinessDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have dealNumber := readOptional_part [50, 49, 49, 48, 50] record.dealNumber tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have tradeReportState := readRequired_part [50, 49, 49, 48, 51] record.tradeReportState tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have tradeReportSubState := readRequired_part [50, 49, 49, 48, 52] record.tradeReportSubState tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have tradeReportInstrType := readOptional_part [50, 49, 49, 48, 53] record.tradeReportInstrType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have traderReportReason := readOptional_part [50, 49, 49, 48, 54] record.traderReportReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have authorizationState := readOptional_part [50, 49, 49, 48, 55] record.authorizationState tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have affimationState := readOptional_part [50, 49, 49, 48, 56] record.affimationState tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have deliveryUnit := readOptional_part [50, 49, 49, 48, 57] record.deliveryUnit tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have origClearingBusinessDate := readOptional_part [50, 49, 49, 49, 48] record.origClearingBusinessDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have secondaryTradeReportRefID := readGroup_part [56, 56, 49] [56, 50, 54] SecondaryTradeReportRefID.members SecondaryTradeReportRefID.encode SecondaryTradeReportRefID.within SecondaryTradeReportRefID.decode SecondaryTradeReportRefID.decode_encode SecondaryTradeReportRefID.led record.secondaryTradeReportRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have secondaryTradeID := readOptional_part [49, 48, 52, 48] record.secondaryTradeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have origTradeID := readOptional_part [49, 49, 50, 54] record.origTradeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have origSecondaryTradeID := readOptional_part [49, 49, 50, 55] record.origSecondaryTradeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have trdSubType := readRequired_part [56, 50, 57] record.trdSubType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have settlementPrice := readOptional_part [55, 51, 48] record.settlementPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have withHoldingTax := readOptional_part [50, 48, 48, 49, 55] record.withHoldingTax tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have repoInterestAmt := readOptional_part [50, 48, 48, 49, 56] record.repoInterestAmt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have noCollateralAmounts := readGroup_part [49, 55, 48, 51] [49, 55, 48, 52] NoCollateralAmounts.members NoCollateralAmounts.encode NoCollateralAmounts.within NoCollateralAmounts.decode NoCollateralAmounts.decode_encode NoCollateralAmounts.led record.noCollateralAmounts tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have correspondingPrice := readOptional_part [50, 48, 48, 48, 55] record.correspondingPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have consideration := readOptional_part [50, 48, 48, 48, 56] record.consideration tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have comboMatchID := readOptional_part [50, 48, 48, 51, 52] record.comboMatchID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have orderQtyDataOrderQty := readOptional_part [51, 56] record.orderQtyDataOrderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have grossTradeAmt := readOptional_part [51, 56, 49] record.grossTradeAmt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  have optionPremiumAmt := readOptional_part [50, 48, 48, 49, 53] record.optionPremiumAmt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 39 (by decide +kernel)))
  have secondaryTrdType := readOptional_part [56, 53, 53] record.secondaryTrdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 40 (by decide +kernel)))
  have secondaryAllocID := readOptional_part [55, 57, 51] record.secondaryAllocID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 41 (by decide +kernel)))
  have copyMsgIndicator := readOptional_part [55, 57, 55] record.copyMsgIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 42 (by decide +kernel)))
  simp only [TradeCaptureReportSubmit.decode, trdType, previouslyReported, noRootPartyIDs, instrumentSecurityIDSource, lastQty, lastPx, lastUnderlyingPx, tradeDate, settlDate, noSides, tradeID, tradeReportRefID, secondaryTradeReportID, matchStatus, trdMatchID, clearingBusinessDate, dealNumber, tradeReportState, tradeReportSubState, tradeReportInstrType, traderReportReason, authorizationState, affimationState, deliveryUnit, origClearingBusinessDate, secondaryTradeReportRefID, secondaryTradeID, origTradeID, origSecondaryTradeID, trdSubType, settlementPrice, withHoldingTax, repoInterestAmt, noCollateralAmounts, correspondingPrice, consideration, comboMatchID, orderQtyDataOrderQty, grossTradeAmt, optionPremiumAmt, secondaryTrdType, secondaryAllocID, copyMsgIndicator, some_bind] <;> rfl

structure TradeCaptureReportAlleged where
  trdType : Terminated 1  -- tag 828
  matchStatus : Terminated 1  -- tag 573
  previouslyReported : Terminated 1  -- tag 570
  instrumentSecurityIDSource : Terminated 1  -- tag 22
  lastQty : Terminated 1  -- tag 32
  lastPx : Terminated 1  -- tag 31
  lastUnderlyingPx : Option (Terminated 1)  -- tag 21100
  tradeDate : Terminated 1  -- tag 75
  settlDate : Option (Terminated 1)  -- tag 64
  noSides : List NoSides  -- tag 552
  copyMsgIndicator : Option (Terminated 1)  -- tag 797
  tradeReportRefID : Option (Terminated 1)  -- tag 572

def TradeCaptureReportAlleged.parts (record : TradeCaptureReportAlleged) : List Part :=
  [Part.required [56, 50, 56] record.trdType,
   Part.required [53, 55, 51] record.matchStatus,
   Part.required [53, 55, 48] record.previouslyReported,
   Part.required [50, 50] record.instrumentSecurityIDSource,
   Part.required [51, 50] record.lastQty,
   Part.required [51, 49] record.lastPx,
   Part.optional [50, 49, 49, 48, 48] record.lastUnderlyingPx,
   Part.required [55, 53] record.tradeDate,
   Part.optional [54, 52] record.settlDate,
   Part.group [53, 53, 50] NoSides.members NoSides.encode NoSides.within record.noSides,
   Part.optional [55, 57, 55] record.copyMsgIndicator,
   Part.optional [53, 55, 50] record.tradeReportRefID]

def TradeCaptureReportAlleged.tags : List (List (List UInt8)) :=
  [[[56, 50, 56]], [[53, 55, 51]], [[53, 55, 48]], [[50, 50]], [[51, 50]], [[51, 49]], [[50, 49, 49, 48, 48]], [[55, 53]], [[54, 52]], [53, 53, 50] :: NoSides.members, [[55, 57, 55]], [[53, 55, 50]]]

theorem TradeCaptureReportAlleged.shape (record : TradeCaptureReportAlleged) : record.parts.map Part.tags = TradeCaptureReportAlleged.tags := rfl

def TradeCaptureReportAlleged.decode (tokens : List Token) : Option TradeCaptureReportAlleged := do
  let trdType ← readRequired [56, 50, 56] tokens
  let matchStatus ← readRequired [53, 55, 51] tokens
  let previouslyReported ← readRequired [53, 55, 48] tokens
  let instrumentSecurityIDSource ← readRequired [50, 50] tokens
  let lastQty ← readRequired [51, 50] tokens
  let lastPx ← readRequired [51, 49] tokens
  let lastUnderlyingPx ← readOptional [50, 49, 49, 48, 48] tokens
  let tradeDate ← readRequired [55, 53] tokens
  let settlDate ← readOptional [54, 52] tokens
  let noSides ← readGroup [53, 53, 50] [53, 52] NoSides.members NoSides.decode tokens
  let copyMsgIndicator ← readOptional [55, 57, 55] tokens
  let tradeReportRefID ← readOptional [53, 55, 50] tokens
  pure { trdType, matchStatus, previouslyReported, instrumentSecurityIDSource, lastQty, lastPx, lastUnderlyingPx, tradeDate, settlDate, noSides, copyMsgIndicator, tradeReportRefID }

theorem TradeCaptureReportAlleged.decode_agrees (record : TradeCaptureReportAlleged) (tokens : List Token)
    (agrees : ∀ tags ∈ TradeCaptureReportAlleged.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TradeCaptureReportAlleged.decode tokens = some record := by
  have distinct : TradeCaptureReportAlleged.tags.flatten.Nodup := by decide +kernel
  have trdType := readRequired_part [56, 50, 56] record.trdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have matchStatus := readRequired_part [53, 55, 51] record.matchStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have previouslyReported := readRequired_part [53, 55, 48] record.previouslyReported tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have instrumentSecurityIDSource := readRequired_part [50, 50] record.instrumentSecurityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have lastQty := readRequired_part [51, 50] record.lastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have lastPx := readRequired_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have lastUnderlyingPx := readOptional_part [50, 49, 49, 48, 48] record.lastUnderlyingPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have tradeDate := readRequired_part [55, 53] record.tradeDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have settlDate := readOptional_part [54, 52] record.settlDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have noSides := readGroup_part [53, 53, 50] [53, 52] NoSides.members NoSides.encode NoSides.within NoSides.decode NoSides.decode_encode NoSides.led record.noSides tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have copyMsgIndicator := readOptional_part [55, 57, 55] record.copyMsgIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have tradeReportRefID := readOptional_part [53, 55, 50] record.tradeReportRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  simp only [TradeCaptureReportAlleged.decode, trdType, matchStatus, previouslyReported, instrumentSecurityIDSource, lastQty, lastPx, lastUnderlyingPx, tradeDate, settlDate, noSides, copyMsgIndicator, tradeReportRefID, some_bind] <;> rfl

structure TradeCaptureReportTradeCancelRequest where
  tradeID : Terminated 1  -- tag 1003
  instrumentSecurityIDSource : Option (Terminated 1)  -- tag 22
  clearingBusinessDate : Terminated 1  -- tag 715
  dealNumber : Terminated 1  -- tag 21102
  tradeCancelRequestReason : Option (Terminated 1)  -- tag 21112

def TradeCaptureReportTradeCancelRequest.parts (record : TradeCaptureReportTradeCancelRequest) : List Part :=
  [Part.required [49, 48, 48, 51] record.tradeID,
   Part.optional [50, 50] record.instrumentSecurityIDSource,
   Part.required [55, 49, 53] record.clearingBusinessDate,
   Part.required [50, 49, 49, 48, 50] record.dealNumber,
   Part.optional [50, 49, 49, 49, 50] record.tradeCancelRequestReason]

def TradeCaptureReportTradeCancelRequest.tags : List (List (List UInt8)) :=
  [[[49, 48, 48, 51]], [[50, 50]], [[55, 49, 53]], [[50, 49, 49, 48, 50]], [[50, 49, 49, 49, 50]]]

theorem TradeCaptureReportTradeCancelRequest.shape (record : TradeCaptureReportTradeCancelRequest) : record.parts.map Part.tags = TradeCaptureReportTradeCancelRequest.tags := rfl

def TradeCaptureReportTradeCancelRequest.decode (tokens : List Token) : Option TradeCaptureReportTradeCancelRequest := do
  let tradeID ← readRequired [49, 48, 48, 51] tokens
  let instrumentSecurityIDSource ← readOptional [50, 50] tokens
  let clearingBusinessDate ← readRequired [55, 49, 53] tokens
  let dealNumber ← readRequired [50, 49, 49, 48, 50] tokens
  let tradeCancelRequestReason ← readOptional [50, 49, 49, 49, 50] tokens
  pure { tradeID, instrumentSecurityIDSource, clearingBusinessDate, dealNumber, tradeCancelRequestReason }

theorem TradeCaptureReportTradeCancelRequest.decode_agrees (record : TradeCaptureReportTradeCancelRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ TradeCaptureReportTradeCancelRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TradeCaptureReportTradeCancelRequest.decode tokens = some record := by
  have distinct : TradeCaptureReportTradeCancelRequest.tags.flatten.Nodup := by decide +kernel
  have tradeID := readRequired_part [49, 48, 48, 51] record.tradeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have instrumentSecurityIDSource := readOptional_part [50, 50] record.instrumentSecurityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have clearingBusinessDate := readRequired_part [55, 49, 53] record.clearingBusinessDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have dealNumber := readRequired_part [50, 49, 49, 48, 50] record.dealNumber tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have tradeCancelRequestReason := readOptional_part [50, 49, 49, 49, 50] record.tradeCancelRequestReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [TradeCaptureReportTradeCancelRequest.decode, tradeID, instrumentSecurityIDSource, clearingBusinessDate, dealNumber, tradeCancelRequestReason, some_bind] <;> rfl

structure TradeCaptureReportAck where
  tradeReportID : Terminated 1  -- tag 571
  tradeRptStatus : Terminated 1  -- tag 939
  instrumentSymbol : Terminated 1  -- tag 55

def TradeCaptureReportAck.parts (record : TradeCaptureReportAck) : List Part :=
  [Part.required [53, 55, 49] record.tradeReportID,
   Part.required [57, 51, 57] record.tradeRptStatus,
   Part.required [53, 53] record.instrumentSymbol]

def TradeCaptureReportAck.tags : List (List (List UInt8)) :=
  [[[53, 55, 49]], [[57, 51, 57]], [[53, 53]]]

theorem TradeCaptureReportAck.shape (record : TradeCaptureReportAck) : record.parts.map Part.tags = TradeCaptureReportAck.tags := rfl

def TradeCaptureReportAck.decode (tokens : List Token) : Option TradeCaptureReportAck := do
  let tradeReportID ← readRequired [53, 55, 49] tokens
  let tradeRptStatus ← readRequired [57, 51, 57] tokens
  let instrumentSymbol ← readRequired [53, 53] tokens
  pure { tradeReportID, tradeRptStatus, instrumentSymbol }

theorem TradeCaptureReportAck.decode_agrees (record : TradeCaptureReportAck) (tokens : List Token)
    (agrees : ∀ tags ∈ TradeCaptureReportAck.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TradeCaptureReportAck.decode tokens = some record := by
  have distinct : TradeCaptureReportAck.tags.flatten.Nodup := by decide +kernel
  have tradeReportID := readRequired_part [53, 55, 49] record.tradeReportID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have tradeRptStatus := readRequired_part [57, 51, 57] record.tradeRptStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have instrumentSymbol := readRequired_part [53, 53] record.instrumentSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [TradeCaptureReportAck.decode, tradeReportID, tradeRptStatus, instrumentSymbol, some_bind] <;> rfl

structure TradeCaptureReportAckNew where
  secondaryTradeReportID : Option (Terminated 1)  -- tag 818
  instrumentSecurityID : Terminated 1  -- tag 48
  instrumentSecurityIDSource : Terminated 1  -- tag 22
  allocID : Option (Terminated 1)  -- tag 70
  account : Option (Terminated 1)  -- tag 1
  orderCapacity : Option (Terminated 1)  -- tag 528
  noRootPartyIDs : List NoRootPartyIDs  -- tag 1116
  copyMsgIndicator : Option (Terminated 1)  -- tag 797

def TradeCaptureReportAckNew.parts (record : TradeCaptureReportAckNew) : List Part :=
  [Part.optional [56, 49, 56] record.secondaryTradeReportID,
   Part.required [52, 56] record.instrumentSecurityID,
   Part.required [50, 50] record.instrumentSecurityIDSource,
   Part.optional [55, 48] record.allocID,
   Part.optional [49] record.account,
   Part.optional [53, 50, 56] record.orderCapacity,
   Part.group [49, 49, 49, 54] NoRootPartyIDs.members NoRootPartyIDs.encode NoRootPartyIDs.within record.noRootPartyIDs,
   Part.optional [55, 57, 55] record.copyMsgIndicator]

def TradeCaptureReportAckNew.tags : List (List (List UInt8)) :=
  [[[56, 49, 56]], [[52, 56]], [[50, 50]], [[55, 48]], [[49]], [[53, 50, 56]], [49, 49, 49, 54] :: NoRootPartyIDs.members, [[55, 57, 55]]]

theorem TradeCaptureReportAckNew.shape (record : TradeCaptureReportAckNew) : record.parts.map Part.tags = TradeCaptureReportAckNew.tags := rfl

def TradeCaptureReportAckNew.decode (tokens : List Token) : Option TradeCaptureReportAckNew := do
  let secondaryTradeReportID ← readOptional [56, 49, 56] tokens
  let instrumentSecurityID ← readRequired [52, 56] tokens
  let instrumentSecurityIDSource ← readRequired [50, 50] tokens
  let allocID ← readOptional [55, 48] tokens
  let account ← readOptional [49] tokens
  let orderCapacity ← readOptional [53, 50, 56] tokens
  let noRootPartyIDs ← readGroup [49, 49, 49, 54] [49, 49, 49, 55] NoRootPartyIDs.members NoRootPartyIDs.decode tokens
  let copyMsgIndicator ← readOptional [55, 57, 55] tokens
  pure { secondaryTradeReportID, instrumentSecurityID, instrumentSecurityIDSource, allocID, account, orderCapacity, noRootPartyIDs, copyMsgIndicator }

theorem TradeCaptureReportAckNew.decode_agrees (record : TradeCaptureReportAckNew) (tokens : List Token)
    (agrees : ∀ tags ∈ TradeCaptureReportAckNew.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TradeCaptureReportAckNew.decode tokens = some record := by
  have distinct : TradeCaptureReportAckNew.tags.flatten.Nodup := by decide +kernel
  have secondaryTradeReportID := readOptional_part [56, 49, 56] record.secondaryTradeReportID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have instrumentSecurityID := readRequired_part [52, 56] record.instrumentSecurityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have instrumentSecurityIDSource := readRequired_part [50, 50] record.instrumentSecurityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have allocID := readOptional_part [55, 48] record.allocID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have orderCapacity := readOptional_part [53, 50, 56] record.orderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have noRootPartyIDs := readGroup_part [49, 49, 49, 54] [49, 49, 49, 55] NoRootPartyIDs.members NoRootPartyIDs.encode NoRootPartyIDs.within NoRootPartyIDs.decode NoRootPartyIDs.decode_encode NoRootPartyIDs.led record.noRootPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have copyMsgIndicator := readOptional_part [55, 57, 55] record.copyMsgIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  simp only [TradeCaptureReportAckNew.decode, secondaryTradeReportID, instrumentSecurityID, instrumentSecurityIDSource, allocID, account, orderCapacity, noRootPartyIDs, copyMsgIndicator, some_bind] <;> rfl

structure TradeCaptureReportAckRejected where
  tradeReportRejectReason : Terminated 1  -- tag 751
  text : Option (Terminated 1)  -- tag 58
  tradeReportTransType : Terminated 1  -- tag 487

def TradeCaptureReportAckRejected.parts (record : TradeCaptureReportAckRejected) : List Part :=
  [Part.required [55, 53, 49] record.tradeReportRejectReason,
   Part.optional [53, 56] record.text,
   Part.required [52, 56, 55] record.tradeReportTransType]

def TradeCaptureReportAckRejected.tags : List (List (List UInt8)) :=
  [[[55, 53, 49]], [[53, 56]], [[52, 56, 55]]]

theorem TradeCaptureReportAckRejected.shape (record : TradeCaptureReportAckRejected) : record.parts.map Part.tags = TradeCaptureReportAckRejected.tags := rfl

def TradeCaptureReportAckRejected.decode (tokens : List Token) : Option TradeCaptureReportAckRejected := do
  let tradeReportRejectReason ← readRequired [55, 53, 49] tokens
  let text ← readOptional [53, 56] tokens
  let tradeReportTransType ← readRequired [52, 56, 55] tokens
  pure { tradeReportRejectReason, text, tradeReportTransType }

theorem TradeCaptureReportAckRejected.decode_agrees (record : TradeCaptureReportAckRejected) (tokens : List Token)
    (agrees : ∀ tags ∈ TradeCaptureReportAckRejected.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TradeCaptureReportAckRejected.decode tokens = some record := by
  have distinct : TradeCaptureReportAckRejected.tags.flatten.Nodup := by decide +kernel
  have tradeReportRejectReason := readRequired_part [55, 53, 49] record.tradeReportRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have tradeReportTransType := readRequired_part [52, 56, 55] record.tradeReportTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [TradeCaptureReportAckRejected.decode, tradeReportRejectReason, text, tradeReportTransType, some_bind] <;> rfl

structure TradeCaptureReportAckCanceled where
  tradeReportTransType : Terminated 1  -- tag 487
  secondaryTradeReportID : Terminated 1  -- tag 818
  instrumentSecurityID : Terminated 1  -- tag 48
  instrumentSecurityIDSource : Terminated 1  -- tag 22
  allocID : Option (Terminated 1)  -- tag 70
  account : Option (Terminated 1)  -- tag 1
  orderCapacity : Option (Terminated 1)  -- tag 528
  copyMsgIndicator : Option (Terminated 1)  -- tag 797

def TradeCaptureReportAckCanceled.parts (record : TradeCaptureReportAckCanceled) : List Part :=
  [Part.required [52, 56, 55] record.tradeReportTransType,
   Part.required [56, 49, 56] record.secondaryTradeReportID,
   Part.required [52, 56] record.instrumentSecurityID,
   Part.required [50, 50] record.instrumentSecurityIDSource,
   Part.optional [55, 48] record.allocID,
   Part.optional [49] record.account,
   Part.optional [53, 50, 56] record.orderCapacity,
   Part.optional [55, 57, 55] record.copyMsgIndicator]

def TradeCaptureReportAckCanceled.tags : List (List (List UInt8)) :=
  [[[52, 56, 55]], [[56, 49, 56]], [[52, 56]], [[50, 50]], [[55, 48]], [[49]], [[53, 50, 56]], [[55, 57, 55]]]

theorem TradeCaptureReportAckCanceled.shape (record : TradeCaptureReportAckCanceled) : record.parts.map Part.tags = TradeCaptureReportAckCanceled.tags := rfl

def TradeCaptureReportAckCanceled.decode (tokens : List Token) : Option TradeCaptureReportAckCanceled := do
  let tradeReportTransType ← readRequired [52, 56, 55] tokens
  let secondaryTradeReportID ← readRequired [56, 49, 56] tokens
  let instrumentSecurityID ← readRequired [52, 56] tokens
  let instrumentSecurityIDSource ← readRequired [50, 50] tokens
  let allocID ← readOptional [55, 48] tokens
  let account ← readOptional [49] tokens
  let orderCapacity ← readOptional [53, 50, 56] tokens
  let copyMsgIndicator ← readOptional [55, 57, 55] tokens
  pure { tradeReportTransType, secondaryTradeReportID, instrumentSecurityID, instrumentSecurityIDSource, allocID, account, orderCapacity, copyMsgIndicator }

theorem TradeCaptureReportAckCanceled.decode_agrees (record : TradeCaptureReportAckCanceled) (tokens : List Token)
    (agrees : ∀ tags ∈ TradeCaptureReportAckCanceled.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TradeCaptureReportAckCanceled.decode tokens = some record := by
  have distinct : TradeCaptureReportAckCanceled.tags.flatten.Nodup := by decide +kernel
  have tradeReportTransType := readRequired_part [52, 56, 55] record.tradeReportTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have secondaryTradeReportID := readRequired_part [56, 49, 56] record.secondaryTradeReportID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have instrumentSecurityID := readRequired_part [52, 56] record.instrumentSecurityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have instrumentSecurityIDSource := readRequired_part [50, 50] record.instrumentSecurityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have allocID := readOptional_part [55, 48] record.allocID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have orderCapacity := readOptional_part [53, 50, 56] record.orderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have copyMsgIndicator := readOptional_part [55, 57, 55] record.copyMsgIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  simp only [TradeCaptureReportAckCanceled.decode, tradeReportTransType, secondaryTradeReportID, instrumentSecurityID, instrumentSecurityIDSource, allocID, account, orderCapacity, copyMsgIndicator, some_bind] <;> rfl

structure TradeCaptureReportAckTradeCorrect where
  tradeReportTransType : Terminated 1  -- tag 487
  tradeID : Terminated 1  -- tag 1003
  instrumentSecurityID : Terminated 1  -- tag 48
  instrumentSecurityIDSource : Terminated 1  -- tag 22
  copyMsgIndicator : Option (Terminated 1)  -- tag 797

def TradeCaptureReportAckTradeCorrect.parts (record : TradeCaptureReportAckTradeCorrect) : List Part :=
  [Part.required [52, 56, 55] record.tradeReportTransType,
   Part.required [49, 48, 48, 51] record.tradeID,
   Part.required [52, 56] record.instrumentSecurityID,
   Part.required [50, 50] record.instrumentSecurityIDSource,
   Part.optional [55, 57, 55] record.copyMsgIndicator]

def TradeCaptureReportAckTradeCorrect.tags : List (List (List UInt8)) :=
  [[[52, 56, 55]], [[49, 48, 48, 51]], [[52, 56]], [[50, 50]], [[55, 57, 55]]]

theorem TradeCaptureReportAckTradeCorrect.shape (record : TradeCaptureReportAckTradeCorrect) : record.parts.map Part.tags = TradeCaptureReportAckTradeCorrect.tags := rfl

def TradeCaptureReportAckTradeCorrect.decode (tokens : List Token) : Option TradeCaptureReportAckTradeCorrect := do
  let tradeReportTransType ← readRequired [52, 56, 55] tokens
  let tradeID ← readRequired [49, 48, 48, 51] tokens
  let instrumentSecurityID ← readRequired [52, 56] tokens
  let instrumentSecurityIDSource ← readRequired [50, 50] tokens
  let copyMsgIndicator ← readOptional [55, 57, 55] tokens
  pure { tradeReportTransType, tradeID, instrumentSecurityID, instrumentSecurityIDSource, copyMsgIndicator }

theorem TradeCaptureReportAckTradeCorrect.decode_agrees (record : TradeCaptureReportAckTradeCorrect) (tokens : List Token)
    (agrees : ∀ tags ∈ TradeCaptureReportAckTradeCorrect.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TradeCaptureReportAckTradeCorrect.decode tokens = some record := by
  have distinct : TradeCaptureReportAckTradeCorrect.tags.flatten.Nodup := by decide +kernel
  have tradeReportTransType := readRequired_part [52, 56, 55] record.tradeReportTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have tradeID := readRequired_part [49, 48, 48, 51] record.tradeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have instrumentSecurityID := readRequired_part [52, 56] record.instrumentSecurityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have instrumentSecurityIDSource := readRequired_part [50, 50] record.instrumentSecurityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have copyMsgIndicator := readOptional_part [55, 57, 55] record.copyMsgIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [TradeCaptureReportAckTradeCorrect.decode, tradeReportTransType, tradeID, instrumentSecurityID, instrumentSecurityIDSource, copyMsgIndicator, some_bind] <;> rfl

structure AllocationInstructionAck where
  allocReportID : Terminated 1  -- tag 755
  allocID : Terminated 1  -- tag 70
  allocTransType : Terminated 1  -- tag 71
  allocStatus : Terminated 1  -- tag 87
  allocRejCode : Terminated 1  -- tag 88
  text : Option (Terminated 1)  -- tag 58

def AllocationInstructionAck.parts (record : AllocationInstructionAck) : List Part :=
  [Part.required [55, 53, 53] record.allocReportID,
   Part.required [55, 48] record.allocID,
   Part.required [55, 49] record.allocTransType,
   Part.required [56, 55] record.allocStatus,
   Part.required [56, 56] record.allocRejCode,
   Part.optional [53, 56] record.text]

def AllocationInstructionAck.tags : List (List (List UInt8)) :=
  [[[55, 53, 53]], [[55, 48]], [[55, 49]], [[56, 55]], [[56, 56]], [[53, 56]]]

theorem AllocationInstructionAck.shape (record : AllocationInstructionAck) : record.parts.map Part.tags = AllocationInstructionAck.tags := rfl

def AllocationInstructionAck.decode (tokens : List Token) : Option AllocationInstructionAck := do
  let allocReportID ← readRequired [55, 53, 53] tokens
  let allocID ← readRequired [55, 48] tokens
  let allocTransType ← readRequired [55, 49] tokens
  let allocStatus ← readRequired [56, 55] tokens
  let allocRejCode ← readRequired [56, 56] tokens
  let text ← readOptional [53, 56] tokens
  pure { allocReportID, allocID, allocTransType, allocStatus, allocRejCode, text }

theorem AllocationInstructionAck.decode_agrees (record : AllocationInstructionAck) (tokens : List Token)
    (agrees : ∀ tags ∈ AllocationInstructionAck.tags, select tags tokens = select tags (encodeParts record.parts)) :
    AllocationInstructionAck.decode tokens = some record := by
  have distinct : AllocationInstructionAck.tags.flatten.Nodup := by decide +kernel
  have allocReportID := readRequired_part [55, 53, 53] record.allocReportID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have allocID := readRequired_part [55, 48] record.allocID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have allocTransType := readRequired_part [55, 49] record.allocTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have allocStatus := readRequired_part [56, 55] record.allocStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have allocRejCode := readRequired_part [56, 56] record.allocRejCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  simp only [AllocationInstructionAck.decode, allocReportID, allocID, allocTransType, allocStatus, allocRejCode, text, some_bind] <;> rfl

structure NoExecs where
  lastQty : Terminated 1  -- tag 32
  lastPx : Option (Terminated 1)  -- tag 31
  tradeID : Terminated 1  -- tag 1003

def NoExecs.parts (record : NoExecs) : List Part :=
  [Part.required [51, 50] record.lastQty,
   Part.optional [51, 49] record.lastPx,
   Part.required [49, 48, 48, 51] record.tradeID]

def NoExecs.tags : List (List (List UInt8)) :=
  [[[51, 50]], [[51, 49]], [[49, 48, 48, 51]]]

theorem NoExecs.shape (record : NoExecs) : record.parts.map Part.tags = NoExecs.tags := rfl

def NoExecs.decode (tokens : List Token) : Option NoExecs := do
  let lastQty ← readRequired [51, 50] tokens
  let lastPx ← readOptional [51, 49] tokens
  let tradeID ← readRequired [49, 48, 48, 51] tokens
  pure { lastQty, lastPx, tradeID }

theorem NoExecs.decode_agrees (record : NoExecs) (tokens : List Token)
    (agrees : ∀ tags ∈ NoExecs.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoExecs.decode tokens = some record := by
  have distinct : NoExecs.tags.flatten.Nodup := by decide +kernel
  have lastQty := readRequired_part [51, 50] record.lastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have lastPx := readOptional_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have tradeID := readRequired_part [49, 48, 48, 51] record.tradeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [NoExecs.decode, lastQty, lastPx, tradeID, some_bind] <;> rfl

def NoExecs.members : List (List UInt8) := NoExecs.tags.flatten

def NoExecs.encode (entry : NoExecs) : List Token := encodeParts entry.parts

theorem NoExecs.decode_encode (entry : NoExecs) : NoExecs.decode entry.encode = some entry :=
  NoExecs.decode_agrees entry _ (fun _ _ => rfl)

theorem NoExecs.within (entry : NoExecs) : ∀ token ∈ entry.encode, token.tag ∈ NoExecs.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoExecs.shape] at this

theorem NoExecs.led (entry : NoExecs) : Lead [51, 50] entry.encode :=
  lead_parts [51, 50] entry.lastQty _ NoExecs.tags.tail rfl (by decide +kernel)

structure NoAllocs where
  allocAccount : Terminated 1  -- tag 79
  allocQty : Terminated 1  -- tag 80
  noNestedPartyIDs : Terminated 1  -- tag 539
  nestedPartyID : Terminated 1  -- tag 524
  nestedPartyIDSource : Terminated 1  -- tag 525
  nestedPartyRole : Terminated 1  -- tag 538
  commission : Option (Terminated 1)  -- tag 12
  commType : Option (Terminated 1)  -- tag 13
  externalTradeFeeType : Option (Terminated 1)  -- tag 20014

def NoAllocs.parts (record : NoAllocs) : List Part :=
  [Part.required [55, 57] record.allocAccount,
   Part.required [56, 48] record.allocQty,
   Part.required [53, 51, 57] record.noNestedPartyIDs,
   Part.required [53, 50, 52] record.nestedPartyID,
   Part.required [53, 50, 53] record.nestedPartyIDSource,
   Part.required [53, 51, 56] record.nestedPartyRole,
   Part.optional [49, 50] record.commission,
   Part.optional [49, 51] record.commType,
   Part.optional [50, 48, 48, 49, 52] record.externalTradeFeeType]

def NoAllocs.tags : List (List (List UInt8)) :=
  [[[55, 57]], [[56, 48]], [[53, 51, 57]], [[53, 50, 52]], [[53, 50, 53]], [[53, 51, 56]], [[49, 50]], [[49, 51]], [[50, 48, 48, 49, 52]]]

theorem NoAllocs.shape (record : NoAllocs) : record.parts.map Part.tags = NoAllocs.tags := rfl

def NoAllocs.decode (tokens : List Token) : Option NoAllocs := do
  let allocAccount ← readRequired [55, 57] tokens
  let allocQty ← readRequired [56, 48] tokens
  let noNestedPartyIDs ← readRequired [53, 51, 57] tokens
  let nestedPartyID ← readRequired [53, 50, 52] tokens
  let nestedPartyIDSource ← readRequired [53, 50, 53] tokens
  let nestedPartyRole ← readRequired [53, 51, 56] tokens
  let commission ← readOptional [49, 50] tokens
  let commType ← readOptional [49, 51] tokens
  let externalTradeFeeType ← readOptional [50, 48, 48, 49, 52] tokens
  pure { allocAccount, allocQty, noNestedPartyIDs, nestedPartyID, nestedPartyIDSource, nestedPartyRole, commission, commType, externalTradeFeeType }

theorem NoAllocs.decode_agrees (record : NoAllocs) (tokens : List Token)
    (agrees : ∀ tags ∈ NoAllocs.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoAllocs.decode tokens = some record := by
  have distinct : NoAllocs.tags.flatten.Nodup := by decide +kernel
  have allocAccount := readRequired_part [55, 57] record.allocAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have allocQty := readRequired_part [56, 48] record.allocQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have noNestedPartyIDs := readRequired_part [53, 51, 57] record.noNestedPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have nestedPartyID := readRequired_part [53, 50, 52] record.nestedPartyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have nestedPartyIDSource := readRequired_part [53, 50, 53] record.nestedPartyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have nestedPartyRole := readRequired_part [53, 51, 56] record.nestedPartyRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have commission := readOptional_part [49, 50] record.commission tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have commType := readOptional_part [49, 51] record.commType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have externalTradeFeeType := readOptional_part [50, 48, 48, 49, 52] record.externalTradeFeeType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  simp only [NoAllocs.decode, allocAccount, allocQty, noNestedPartyIDs, nestedPartyID, nestedPartyIDSource, nestedPartyRole, commission, commType, externalTradeFeeType, some_bind] <;> rfl

def NoAllocs.members : List (List UInt8) := NoAllocs.tags.flatten

def NoAllocs.encode (entry : NoAllocs) : List Token := encodeParts entry.parts

theorem NoAllocs.decode_encode (entry : NoAllocs) : NoAllocs.decode entry.encode = some entry :=
  NoAllocs.decode_agrees entry _ (fun _ _ => rfl)

theorem NoAllocs.within (entry : NoAllocs) : ∀ token ∈ entry.encode, token.tag ∈ NoAllocs.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoAllocs.shape] at this

theorem NoAllocs.led (entry : NoAllocs) : Lead [55, 57] entry.encode :=
  lead_parts [55, 57] entry.allocAccount _ NoAllocs.tags.tail rfl (by decide +kernel)

structure AllocationReport where
  allocReportID : Option (Terminated 1)  -- tag 755
  allocID : Option (Terminated 1)  -- tag 70
  secondaryAllocID : Terminated 1  -- tag 793
  allocTransType : Terminated 1  -- tag 71
  allocReportType : Terminated 1  -- tag 794
  allocStatus : Terminated 1  -- tag 87
  clearingBusinessDate : Option (Terminated 1)  -- tag 715
  side : Terminated 1  -- tag 54
  noExecs : List NoExecs  -- tag 124
  instrumentSymbol : Option (Terminated 1)  -- tag 55
  instrumentSecurityID : Option (Terminated 1)  -- tag 48
  instrumentSecurityIDSource : Option (Terminated 1)  -- tag 22
  quantity : Terminated 1  -- tag 53
  lastMkt : Option (Terminated 1)  -- tag 30
  avgPx : Terminated 1  -- tag 6
  noPartyIDs : List NoPartyIDs  -- tag 453
  tradeDate : Terminated 1  -- tag 75
  transactTime : Option (Terminated 1)  -- tag 60
  noAllocs : List NoAllocs  -- tag 78
  text : Option (Terminated 1)  -- tag 58
  secondaryTradeID : Option (Terminated 1)  -- tag 1040
  origSecondaryTradeID : Option (Terminated 1)  -- tag 1127
  secondaryTrdType : Option (Terminated 1)  -- tag 855

def AllocationReport.parts (record : AllocationReport) : List Part :=
  [Part.optional [55, 53, 53] record.allocReportID,
   Part.optional [55, 48] record.allocID,
   Part.required [55, 57, 51] record.secondaryAllocID,
   Part.required [55, 49] record.allocTransType,
   Part.required [55, 57, 52] record.allocReportType,
   Part.required [56, 55] record.allocStatus,
   Part.optional [55, 49, 53] record.clearingBusinessDate,
   Part.required [53, 52] record.side,
   Part.group [49, 50, 52] NoExecs.members NoExecs.encode NoExecs.within record.noExecs,
   Part.optional [53, 53] record.instrumentSymbol,
   Part.optional [52, 56] record.instrumentSecurityID,
   Part.optional [50, 50] record.instrumentSecurityIDSource,
   Part.required [53, 51] record.quantity,
   Part.optional [51, 48] record.lastMkt,
   Part.required [54] record.avgPx,
   Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.required [55, 53] record.tradeDate,
   Part.optional [54, 48] record.transactTime,
   Part.group [55, 56] NoAllocs.members NoAllocs.encode NoAllocs.within record.noAllocs,
   Part.optional [53, 56] record.text,
   Part.optional [49, 48, 52, 48] record.secondaryTradeID,
   Part.optional [49, 49, 50, 55] record.origSecondaryTradeID,
   Part.optional [56, 53, 53] record.secondaryTrdType]

def AllocationReport.tags : List (List (List UInt8)) :=
  [[[55, 53, 53]], [[55, 48]], [[55, 57, 51]], [[55, 49]], [[55, 57, 52]], [[56, 55]], [[55, 49, 53]], [[53, 52]], [49, 50, 52] :: NoExecs.members, [[53, 53]], [[52, 56]], [[50, 50]], [[53, 51]], [[51, 48]], [[54]], [52, 53, 51] :: NoPartyIDs.members, [[55, 53]], [[54, 48]], [55, 56] :: NoAllocs.members, [[53, 56]], [[49, 48, 52, 48]], [[49, 49, 50, 55]], [[56, 53, 53]]]

theorem AllocationReport.shape (record : AllocationReport) : record.parts.map Part.tags = AllocationReport.tags := rfl

def AllocationReport.decode (tokens : List Token) : Option AllocationReport := do
  let allocReportID ← readOptional [55, 53, 53] tokens
  let allocID ← readOptional [55, 48] tokens
  let secondaryAllocID ← readRequired [55, 57, 51] tokens
  let allocTransType ← readRequired [55, 49] tokens
  let allocReportType ← readRequired [55, 57, 52] tokens
  let allocStatus ← readRequired [56, 55] tokens
  let clearingBusinessDate ← readOptional [55, 49, 53] tokens
  let side ← readRequired [53, 52] tokens
  let noExecs ← readGroup [49, 50, 52] [51, 50] NoExecs.members NoExecs.decode tokens
  let instrumentSymbol ← readOptional [53, 53] tokens
  let instrumentSecurityID ← readOptional [52, 56] tokens
  let instrumentSecurityIDSource ← readOptional [50, 50] tokens
  let quantity ← readRequired [53, 51] tokens
  let lastMkt ← readOptional [51, 48] tokens
  let avgPx ← readRequired [54] tokens
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let tradeDate ← readRequired [55, 53] tokens
  let transactTime ← readOptional [54, 48] tokens
  let noAllocs ← readGroup [55, 56] [55, 57] NoAllocs.members NoAllocs.decode tokens
  let text ← readOptional [53, 56] tokens
  let secondaryTradeID ← readOptional [49, 48, 52, 48] tokens
  let origSecondaryTradeID ← readOptional [49, 49, 50, 55] tokens
  let secondaryTrdType ← readOptional [56, 53, 53] tokens
  pure { allocReportID, allocID, secondaryAllocID, allocTransType, allocReportType, allocStatus, clearingBusinessDate, side, noExecs, instrumentSymbol, instrumentSecurityID, instrumentSecurityIDSource, quantity, lastMkt, avgPx, noPartyIDs, tradeDate, transactTime, noAllocs, text, secondaryTradeID, origSecondaryTradeID, secondaryTrdType }

theorem AllocationReport.decode_agrees (record : AllocationReport) (tokens : List Token)
    (agrees : ∀ tags ∈ AllocationReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    AllocationReport.decode tokens = some record := by
  have distinct : AllocationReport.tags.flatten.Nodup := by decide +kernel
  have allocReportID := readOptional_part [55, 53, 53] record.allocReportID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have allocID := readOptional_part [55, 48] record.allocID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have secondaryAllocID := readRequired_part [55, 57, 51] record.secondaryAllocID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have allocTransType := readRequired_part [55, 49] record.allocTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have allocReportType := readRequired_part [55, 57, 52] record.allocReportType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have allocStatus := readRequired_part [56, 55] record.allocStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have clearingBusinessDate := readOptional_part [55, 49, 53] record.clearingBusinessDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have noExecs := readGroup_part [49, 50, 52] [51, 50] NoExecs.members NoExecs.encode NoExecs.within NoExecs.decode NoExecs.decode_encode NoExecs.led record.noExecs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have instrumentSymbol := readOptional_part [53, 53] record.instrumentSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have instrumentSecurityID := readOptional_part [52, 56] record.instrumentSecurityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have instrumentSecurityIDSource := readOptional_part [50, 50] record.instrumentSecurityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have quantity := readRequired_part [53, 51] record.quantity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have lastMkt := readOptional_part [51, 48] record.lastMkt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have avgPx := readRequired_part [54] record.avgPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have tradeDate := readRequired_part [55, 53] record.tradeDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have noAllocs := readGroup_part [55, 56] [55, 57] NoAllocs.members NoAllocs.encode NoAllocs.within NoAllocs.decode NoAllocs.decode_encode NoAllocs.led record.noAllocs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have secondaryTradeID := readOptional_part [49, 48, 52, 48] record.secondaryTradeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have origSecondaryTradeID := readOptional_part [49, 49, 50, 55] record.origSecondaryTradeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have secondaryTrdType := readOptional_part [56, 53, 53] record.secondaryTrdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  simp only [AllocationReport.decode, allocReportID, allocID, secondaryAllocID, allocTransType, allocReportType, allocStatus, clearingBusinessDate, side, noExecs, instrumentSymbol, instrumentSecurityID, instrumentSecurityIDSource, quantity, lastMkt, avgPx, noPartyIDs, tradeDate, transactTime, noAllocs, text, secondaryTradeID, origSecondaryTradeID, secondaryTrdType, some_bind] <;> rfl

inductive Message where
  | logon (header : Header) (r0 : Logon)
  | logout (header : Header) (r0 : Logout)
  | sequenceReset (header : Header) (r0 : SequenceReset)
  | reject (header : Header) (r0 : Reject)
  | heartbeat (header : Header) (r0 : Heartbeat)
  | testRequest (header : Header) (r0 : TestRequest)
  | userResponse (header : Header) (r0 : UserResponse)
  | userNotification (header : Header) (r0 : UserNotification)
  | orderCancelReject (header : Header) (r0 : OrderCancelReject)
  | executionReportNew (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportNew)
  | executionReportCanceled (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCanceled)
  | executionReportRejected (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportRejected)
  | executionReportRestated (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportRestated)
  | executionReportSuspended (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportSuspended)
  | executionReportExpired (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportExpired)
  | executionReportTrade (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportTrade)
  | businessMessageReject (header : Header) (r0 : BusinessMessageReject)
  | securityDefinition (header : Header) (r0 : SecurityDefinition)
  | securityDefinitionUpdateReport (header : Header) (r0 : SecurityDefinitionUpdateReport)
  | massQuoteAcknowledgement (header : Header) (r0 : MassQuoteAcknowledgement)
  | quoteRequest (header : Header) (r0 : QuoteRequest)
  | quoteRequestReject (header : Header) (r0 : QuoteRequestReject)
  | tradeCaptureReportSubmit (header : Header) (r0 : TradeCaptureReport) (r1 : TradeCaptureReportSubmit)
  | tradeCaptureReportAlleged (header : Header) (r0 : TradeCaptureReport) (r1 : TradeCaptureReportAlleged)
  | tradeCaptureReportTradeCancelRequest (header : Header) (r0 : TradeCaptureReport) (r1 : TradeCaptureReportTradeCancelRequest)
  | tradeCaptureReportAckNew (header : Header) (r0 : TradeCaptureReportAck) (r1 : TradeCaptureReportAckNew)
  | tradeCaptureReportAckRejected (header : Header) (r0 : TradeCaptureReportAck) (r1 : TradeCaptureReportAckRejected)
  | tradeCaptureReportAckCanceled (header : Header) (r0 : TradeCaptureReportAck) (r1 : TradeCaptureReportAckCanceled)
  | tradeCaptureReportAckTradeCorrect (header : Header) (r0 : TradeCaptureReportAck) (r1 : TradeCaptureReportAckTradeCorrect)
  | allocationInstructionAck (header : Header) (r0 : AllocationInstructionAck)
  | allocationReport (header : Header) (r0 : AllocationReport)

def Message.tokens : Message → List Token
  | .logon header r0 => ⟨[51, 53], ⟨[65], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logout header r0 => ⟨[51, 53], ⟨[53], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .sequenceReset header r0 => ⟨[51, 53], ⟨[52], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .reject header r0 => ⟨[51, 53], ⟨[51], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .heartbeat header r0 => ⟨[51, 53], ⟨[48], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .testRequest header r0 => ⟨[51, 53], ⟨[49], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .userResponse header r0 => ⟨[51, 53], ⟨[66, 70], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .userNotification header r0 => ⟨[51, 53], ⟨[67, 66], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelReject header r0 => ⟨[51, 53], ⟨[57], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .executionReportNew header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts)
  | .executionReportCanceled header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r1.parts)
  | .executionReportRejected header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r1.parts)
  | .executionReportRestated header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[68], by decide⟩] ++ r1.parts)
  | .executionReportSuspended header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[57], by decide⟩] ++ r1.parts)
  | .executionReportExpired header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[67], by decide⟩] ++ r1.parts)
  | .executionReportTrade header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[70], by decide⟩] ++ r1.parts)
  | .businessMessageReject header r0 => ⟨[51, 53], ⟨[106], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .securityDefinition header r0 => ⟨[51, 53], ⟨[100], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .securityDefinitionUpdateReport header r0 => ⟨[51, 53], ⟨[66, 80], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .massQuoteAcknowledgement header r0 => ⟨[51, 53], ⟨[98], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .quoteRequest header r0 => ⟨[51, 53], ⟨[82], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .quoteRequestReject header r0 => ⟨[51, 53], ⟨[65, 71], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .tradeCaptureReportSubmit header r0 r1 => ⟨[51, 53], ⟨[65, 69], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [56, 53, 54] ⟨[48], by decide⟩] ++ r1.parts)
  | .tradeCaptureReportAlleged header r0 r1 => ⟨[51, 53], ⟨[65, 69], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [56, 53, 54] ⟨[49], by decide⟩] ++ r1.parts)
  | .tradeCaptureReportTradeCancelRequest header r0 r1 => ⟨[51, 53], ⟨[65, 69], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [56, 53, 54] ⟨[56], by decide⟩] ++ r1.parts)
  | .tradeCaptureReportAckNew header r0 r1 => ⟨[51, 53], ⟨[65, 82], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts)
  | .tradeCaptureReportAckRejected header r0 r1 => ⟨[51, 53], ⟨[65, 82], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r1.parts)
  | .tradeCaptureReportAckCanceled header r0 r1 => ⟨[51, 53], ⟨[65, 82], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r1.parts)
  | .tradeCaptureReportAckTradeCorrect header r0 r1 => ⟨[51, 53], ⟨[65, 82], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[71], by decide⟩] ++ r1.parts)
  | .allocationInstructionAck header r0 => ⟨[51, 53], ⟨[65, 84], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .allocationReport header r0 => ⟨[51, 53], ⟨[65, 83], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)

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
      else if token.value.val = [51] then
        if known (Header.tags ++ Reject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Reject.decode rest
          pure (.reject header r0)
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
      else if token.value.val = [66, 70] then
        if known (Header.tags ++ UserResponse.tags) rest then do
          let header ← Header.decode rest
          let r0 ← UserResponse.decode rest
          pure (.userResponse header r0)
        else none
      else if token.value.val = [67, 66] then
        if known (Header.tags ++ UserNotification.tags) rest then do
          let header ← Header.decode rest
          let r0 ← UserNotification.decode rest
          pure (.userNotification header r0)
        else none
      else if token.value.val = [57] then
        if known (Header.tags ++ OrderCancelReject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderCancelReject.decode rest
          pure (.orderCancelReject header r0)
        else none
      else if token.value.val = [56] then
        match readRequired [49, 53, 48] rest with
        | none => none
        | some key =>
          if key.val = [48] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportNew.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportNew.decode rest
              pure (.executionReportNew header r0 r1)
            else none
          else if key.val = [52] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCanceled.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportCanceled.decode rest
              pure (.executionReportCanceled header r0 r1)
            else none
          else if key.val = [56] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRejected.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportRejected.decode rest
              pure (.executionReportRejected header r0 r1)
            else none
          else if key.val = [68] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRestated.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportRestated.decode rest
              pure (.executionReportRestated header r0 r1)
            else none
          else if key.val = [57] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportSuspended.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportSuspended.decode rest
              pure (.executionReportSuspended header r0 r1)
            else none
          else if key.val = [67] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportExpired.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportExpired.decode rest
              pure (.executionReportExpired header r0 r1)
            else none
          else if key.val = [70] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportTrade.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportTrade.decode rest
              pure (.executionReportTrade header r0 r1)
            else none
          else none
      else if token.value.val = [106] then
        if known (Header.tags ++ BusinessMessageReject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← BusinessMessageReject.decode rest
          pure (.businessMessageReject header r0)
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
      else if token.value.val = [98] then
        if known (Header.tags ++ MassQuoteAcknowledgement.tags) rest then do
          let header ← Header.decode rest
          let r0 ← MassQuoteAcknowledgement.decode rest
          pure (.massQuoteAcknowledgement header r0)
        else none
      else if token.value.val = [82] then
        if known (Header.tags ++ QuoteRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← QuoteRequest.decode rest
          pure (.quoteRequest header r0)
        else none
      else if token.value.val = [65, 71] then
        if known (Header.tags ++ QuoteRequestReject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← QuoteRequestReject.decode rest
          pure (.quoteRequestReject header r0)
        else none
      else if token.value.val = [65, 69] then
        match readRequired [56, 53, 54] rest with
        | none => none
        | some key =>
          if key.val = [48] then
            if known (Header.tags ++ TradeCaptureReport.tags ++ [[[56, 53, 54]]] ++ TradeCaptureReportSubmit.tags) rest then do
              let header ← Header.decode rest
              let r0 ← TradeCaptureReport.decode rest
              let r1 ← TradeCaptureReportSubmit.decode rest
              pure (.tradeCaptureReportSubmit header r0 r1)
            else none
          else if key.val = [49] then
            if known (Header.tags ++ TradeCaptureReport.tags ++ [[[56, 53, 54]]] ++ TradeCaptureReportAlleged.tags) rest then do
              let header ← Header.decode rest
              let r0 ← TradeCaptureReport.decode rest
              let r1 ← TradeCaptureReportAlleged.decode rest
              pure (.tradeCaptureReportAlleged header r0 r1)
            else none
          else if key.val = [56] then
            if known (Header.tags ++ TradeCaptureReport.tags ++ [[[56, 53, 54]]] ++ TradeCaptureReportTradeCancelRequest.tags) rest then do
              let header ← Header.decode rest
              let r0 ← TradeCaptureReport.decode rest
              let r1 ← TradeCaptureReportTradeCancelRequest.decode rest
              pure (.tradeCaptureReportTradeCancelRequest header r0 r1)
            else none
          else none
      else if token.value.val = [65, 82] then
        match readRequired [49, 53, 48] rest with
        | none => none
        | some key =>
          if key.val = [48] then
            if known (Header.tags ++ TradeCaptureReportAck.tags ++ [[[49, 53, 48]]] ++ TradeCaptureReportAckNew.tags) rest then do
              let header ← Header.decode rest
              let r0 ← TradeCaptureReportAck.decode rest
              let r1 ← TradeCaptureReportAckNew.decode rest
              pure (.tradeCaptureReportAckNew header r0 r1)
            else none
          else if key.val = [56] then
            if known (Header.tags ++ TradeCaptureReportAck.tags ++ [[[49, 53, 48]]] ++ TradeCaptureReportAckRejected.tags) rest then do
              let header ← Header.decode rest
              let r0 ← TradeCaptureReportAck.decode rest
              let r1 ← TradeCaptureReportAckRejected.decode rest
              pure (.tradeCaptureReportAckRejected header r0 r1)
            else none
          else if key.val = [52] then
            if known (Header.tags ++ TradeCaptureReportAck.tags ++ [[[49, 53, 48]]] ++ TradeCaptureReportAckCanceled.tags) rest then do
              let header ← Header.decode rest
              let r0 ← TradeCaptureReportAck.decode rest
              let r1 ← TradeCaptureReportAckCanceled.decode rest
              pure (.tradeCaptureReportAckCanceled header r0 r1)
            else none
          else if key.val = [71] then
            if known (Header.tags ++ TradeCaptureReportAck.tags ++ [[[49, 53, 48]]] ++ TradeCaptureReportAckTradeCorrect.tags) rest then do
              let header ← Header.decode rest
              let r0 ← TradeCaptureReportAck.decode rest
              let r1 ← TradeCaptureReportAckTradeCorrect.decode rest
              pure (.tradeCaptureReportAckTradeCorrect header r0 r1)
            else none
          else none
      else if token.value.val = [65, 84] then
        if known (Header.tags ++ AllocationInstructionAck.tags) rest then do
          let header ← Header.decode rest
          let r0 ← AllocationInstructionAck.decode rest
          pure (.allocationInstructionAck header r0)
        else none
      else if token.value.val = [65, 83] then
        if known (Header.tags ++ AllocationReport.tags) rest then do
          let header ← Header.decode rest
          let r0 ← AllocationReport.decode rest
          pure (.allocationReport header r0)
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

theorem Message.decode_reject (header : Header) (r0 : Reject) :
    Message.decode (Message.tokens (.reject header r0)) = some (.reject header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (Reject.tags) rfl rfl (by decide +kernel))
  have c1 := Reject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (Reject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ Reject.tags) rfl
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

theorem Message.decode_userResponse (header : Header) (r0 : UserResponse) :
    Message.decode (Message.tokens (.userResponse header r0)) = some (.userResponse header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (UserResponse.tags) rfl rfl (by decide +kernel))
  have c1 := UserResponse.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (UserResponse.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ UserResponse.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_userNotification (header : Header) (r0 : UserNotification) :
    Message.decode (Message.tokens (.userNotification header r0)) = some (.userNotification header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (UserNotification.tags) rfl rfl (by decide +kernel))
  have c1 := UserNotification.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (UserNotification.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ UserNotification.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_orderCancelReject (header : Header) (r0 : OrderCancelReject) :
    Message.decode (Message.tokens (.orderCancelReject header r0)) = some (.orderCancelReject header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelReject.tags) rfl rfl (by decide +kernel))
  have c1 := OrderCancelReject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelReject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderCancelReject.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportNew (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportNew) :
    Message.decode (Message.tokens (.executionReportNew header r0 r1)) = some (.executionReportNew header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportNew.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportNew.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[48], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[48], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportNew.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportNew.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportNew.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportNew.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportCanceled (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCanceled) :
    Message.decode (Message.tokens (.executionReportCanceled header r0 r1)) = some (.executionReportCanceled header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCanceled.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportCanceled.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[52], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[52], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportCanceled.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportCanceled.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportCanceled.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCanceled.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportRejected (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportRejected) :
    Message.decode (Message.tokens (.executionReportRejected header r0 r1)) = some (.executionReportRejected header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRejected.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportRejected.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[56], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[56], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportRejected.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportRejected.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportRejected.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRejected.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportRestated (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportRestated) :
    Message.decode (Message.tokens (.executionReportRestated header r0 r1)) = some (.executionReportRestated header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[68], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRestated.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[68], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportRestated.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[68], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[68], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportRestated.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportRestated.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[68], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportRestated.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[68], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRestated.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportSuspended (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportSuspended) :
    Message.decode (Message.tokens (.executionReportSuspended header r0 r1)) = some (.executionReportSuspended header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[57], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportSuspended.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[57], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportSuspended.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[57], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[57], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportSuspended.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportSuspended.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[57], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportSuspended.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[57], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportSuspended.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportExpired (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportExpired) :
    Message.decode (Message.tokens (.executionReportExpired header r0 r1)) = some (.executionReportExpired header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[67], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportExpired.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[67], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportExpired.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[67], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[67], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportExpired.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportExpired.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[67], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportExpired.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[67], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportExpired.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportTrade (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportTrade) :
    Message.decode (Message.tokens (.executionReportTrade header r0 r1)) = some (.executionReportTrade header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[70], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportTrade.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[70], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportTrade.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[70], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[70], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportTrade.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportTrade.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[70], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportTrade.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[70], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportTrade.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_businessMessageReject (header : Header) (r0 : BusinessMessageReject) :
    Message.decode (Message.tokens (.businessMessageReject header r0)) = some (.businessMessageReject header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (BusinessMessageReject.tags) rfl rfl (by decide +kernel))
  have c1 := BusinessMessageReject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (BusinessMessageReject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ BusinessMessageReject.tags) rfl
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

theorem Message.decode_massQuoteAcknowledgement (header : Header) (r0 : MassQuoteAcknowledgement) :
    Message.decode (Message.tokens (.massQuoteAcknowledgement header r0)) = some (.massQuoteAcknowledgement header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (MassQuoteAcknowledgement.tags) rfl rfl (by decide +kernel))
  have c1 := MassQuoteAcknowledgement.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (MassQuoteAcknowledgement.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ MassQuoteAcknowledgement.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_quoteRequest (header : Header) (r0 : QuoteRequest) :
    Message.decode (Message.tokens (.quoteRequest header r0)) = some (.quoteRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (QuoteRequest.tags) rfl rfl (by decide +kernel))
  have c1 := QuoteRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (QuoteRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ QuoteRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_quoteRequestReject (header : Header) (r0 : QuoteRequestReject) :
    Message.decode (Message.tokens (.quoteRequestReject header r0)) = some (.quoteRequestReject header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (QuoteRequestReject.tags) rfl rfl (by decide +kernel))
  have c1 := QuoteRequestReject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (QuoteRequestReject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ QuoteRequestReject.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tradeCaptureReportSubmit (header : Header) (r0 : TradeCaptureReport) (r1 : TradeCaptureReportSubmit) :
    Message.decode (Message.tokens (.tradeCaptureReportSubmit header r0 r1)) = some (.tradeCaptureReportSubmit header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [56, 53, 54] ⟨[48], by decide⟩] ++ r1.parts) ([]) (Header.tags) (TradeCaptureReport.tags ++ [[[56, 53, 54]]] ++ TradeCaptureReportSubmit.tags) rfl rfl (by decide +kernel))
  have c1 := TradeCaptureReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [56, 53, 54] ⟨[48], by decide⟩] ++ r1.parts) (Header.tags) (TradeCaptureReport.tags) ([[[56, 53, 54]]] ++ TradeCaptureReportSubmit.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [56, 53, 54] ⟨[48], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [56, 53, 54] ⟨[48], by decide⟩]) (r1.parts) (Header.tags ++ TradeCaptureReport.tags) ([[[56, 53, 54]]]) (TradeCaptureReportSubmit.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := TradeCaptureReportSubmit.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [56, 53, 54] ⟨[48], by decide⟩]) (r1.parts) ([]) (Header.tags ++ TradeCaptureReport.tags ++ [[[56, 53, 54]]]) (TradeCaptureReportSubmit.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [56, 53, 54] ⟨[48], by decide⟩] ++ r1.parts) (Header.tags ++ TradeCaptureReport.tags ++ [[[56, 53, 54]]] ++ TradeCaptureReportSubmit.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tradeCaptureReportAlleged (header : Header) (r0 : TradeCaptureReport) (r1 : TradeCaptureReportAlleged) :
    Message.decode (Message.tokens (.tradeCaptureReportAlleged header r0 r1)) = some (.tradeCaptureReportAlleged header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [56, 53, 54] ⟨[49], by decide⟩] ++ r1.parts) ([]) (Header.tags) (TradeCaptureReport.tags ++ [[[56, 53, 54]]] ++ TradeCaptureReportAlleged.tags) rfl rfl (by decide +kernel))
  have c1 := TradeCaptureReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [56, 53, 54] ⟨[49], by decide⟩] ++ r1.parts) (Header.tags) (TradeCaptureReport.tags) ([[[56, 53, 54]]] ++ TradeCaptureReportAlleged.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [56, 53, 54] ⟨[49], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [56, 53, 54] ⟨[49], by decide⟩]) (r1.parts) (Header.tags ++ TradeCaptureReport.tags) ([[[56, 53, 54]]]) (TradeCaptureReportAlleged.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := TradeCaptureReportAlleged.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [56, 53, 54] ⟨[49], by decide⟩]) (r1.parts) ([]) (Header.tags ++ TradeCaptureReport.tags ++ [[[56, 53, 54]]]) (TradeCaptureReportAlleged.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [56, 53, 54] ⟨[49], by decide⟩] ++ r1.parts) (Header.tags ++ TradeCaptureReport.tags ++ [[[56, 53, 54]]] ++ TradeCaptureReportAlleged.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tradeCaptureReportTradeCancelRequest (header : Header) (r0 : TradeCaptureReport) (r1 : TradeCaptureReportTradeCancelRequest) :
    Message.decode (Message.tokens (.tradeCaptureReportTradeCancelRequest header r0 r1)) = some (.tradeCaptureReportTradeCancelRequest header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [56, 53, 54] ⟨[56], by decide⟩] ++ r1.parts) ([]) (Header.tags) (TradeCaptureReport.tags ++ [[[56, 53, 54]]] ++ TradeCaptureReportTradeCancelRequest.tags) rfl rfl (by decide +kernel))
  have c1 := TradeCaptureReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [56, 53, 54] ⟨[56], by decide⟩] ++ r1.parts) (Header.tags) (TradeCaptureReport.tags) ([[[56, 53, 54]]] ++ TradeCaptureReportTradeCancelRequest.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [56, 53, 54] ⟨[56], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [56, 53, 54] ⟨[56], by decide⟩]) (r1.parts) (Header.tags ++ TradeCaptureReport.tags) ([[[56, 53, 54]]]) (TradeCaptureReportTradeCancelRequest.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := TradeCaptureReportTradeCancelRequest.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [56, 53, 54] ⟨[56], by decide⟩]) (r1.parts) ([]) (Header.tags ++ TradeCaptureReport.tags ++ [[[56, 53, 54]]]) (TradeCaptureReportTradeCancelRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [56, 53, 54] ⟨[56], by decide⟩] ++ r1.parts) (Header.tags ++ TradeCaptureReport.tags ++ [[[56, 53, 54]]] ++ TradeCaptureReportTradeCancelRequest.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tradeCaptureReportAckNew (header : Header) (r0 : TradeCaptureReportAck) (r1 : TradeCaptureReportAckNew) :
    Message.decode (Message.tokens (.tradeCaptureReportAckNew header r0 r1)) = some (.tradeCaptureReportAckNew header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts) ([]) (Header.tags) (TradeCaptureReportAck.tags ++ [[[49, 53, 48]]] ++ TradeCaptureReportAckNew.tags) rfl rfl (by decide +kernel))
  have c1 := TradeCaptureReportAck.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts) (Header.tags) (TradeCaptureReportAck.tags) ([[[49, 53, 48]]] ++ TradeCaptureReportAckNew.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[48], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[48], by decide⟩]) (r1.parts) (Header.tags ++ TradeCaptureReportAck.tags) ([[[49, 53, 48]]]) (TradeCaptureReportAckNew.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := TradeCaptureReportAckNew.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩]) (r1.parts) ([]) (Header.tags ++ TradeCaptureReportAck.tags ++ [[[49, 53, 48]]]) (TradeCaptureReportAckNew.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts) (Header.tags ++ TradeCaptureReportAck.tags ++ [[[49, 53, 48]]] ++ TradeCaptureReportAckNew.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tradeCaptureReportAckRejected (header : Header) (r0 : TradeCaptureReportAck) (r1 : TradeCaptureReportAckRejected) :
    Message.decode (Message.tokens (.tradeCaptureReportAckRejected header r0 r1)) = some (.tradeCaptureReportAckRejected header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r1.parts) ([]) (Header.tags) (TradeCaptureReportAck.tags ++ [[[49, 53, 48]]] ++ TradeCaptureReportAckRejected.tags) rfl rfl (by decide +kernel))
  have c1 := TradeCaptureReportAck.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r1.parts) (Header.tags) (TradeCaptureReportAck.tags) ([[[49, 53, 48]]] ++ TradeCaptureReportAckRejected.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[56], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[56], by decide⟩]) (r1.parts) (Header.tags ++ TradeCaptureReportAck.tags) ([[[49, 53, 48]]]) (TradeCaptureReportAckRejected.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := TradeCaptureReportAckRejected.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩]) (r1.parts) ([]) (Header.tags ++ TradeCaptureReportAck.tags ++ [[[49, 53, 48]]]) (TradeCaptureReportAckRejected.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r1.parts) (Header.tags ++ TradeCaptureReportAck.tags ++ [[[49, 53, 48]]] ++ TradeCaptureReportAckRejected.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tradeCaptureReportAckCanceled (header : Header) (r0 : TradeCaptureReportAck) (r1 : TradeCaptureReportAckCanceled) :
    Message.decode (Message.tokens (.tradeCaptureReportAckCanceled header r0 r1)) = some (.tradeCaptureReportAckCanceled header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r1.parts) ([]) (Header.tags) (TradeCaptureReportAck.tags ++ [[[49, 53, 48]]] ++ TradeCaptureReportAckCanceled.tags) rfl rfl (by decide +kernel))
  have c1 := TradeCaptureReportAck.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r1.parts) (Header.tags) (TradeCaptureReportAck.tags) ([[[49, 53, 48]]] ++ TradeCaptureReportAckCanceled.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[52], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[52], by decide⟩]) (r1.parts) (Header.tags ++ TradeCaptureReportAck.tags) ([[[49, 53, 48]]]) (TradeCaptureReportAckCanceled.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := TradeCaptureReportAckCanceled.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩]) (r1.parts) ([]) (Header.tags ++ TradeCaptureReportAck.tags ++ [[[49, 53, 48]]]) (TradeCaptureReportAckCanceled.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r1.parts) (Header.tags ++ TradeCaptureReportAck.tags ++ [[[49, 53, 48]]] ++ TradeCaptureReportAckCanceled.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tradeCaptureReportAckTradeCorrect (header : Header) (r0 : TradeCaptureReportAck) (r1 : TradeCaptureReportAckTradeCorrect) :
    Message.decode (Message.tokens (.tradeCaptureReportAckTradeCorrect header r0 r1)) = some (.tradeCaptureReportAckTradeCorrect header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[71], by decide⟩] ++ r1.parts) ([]) (Header.tags) (TradeCaptureReportAck.tags ++ [[[49, 53, 48]]] ++ TradeCaptureReportAckTradeCorrect.tags) rfl rfl (by decide +kernel))
  have c1 := TradeCaptureReportAck.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[71], by decide⟩] ++ r1.parts) (Header.tags) (TradeCaptureReportAck.tags) ([[[49, 53, 48]]] ++ TradeCaptureReportAckTradeCorrect.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[71], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[71], by decide⟩]) (r1.parts) (Header.tags ++ TradeCaptureReportAck.tags) ([[[49, 53, 48]]]) (TradeCaptureReportAckTradeCorrect.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := TradeCaptureReportAckTradeCorrect.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[71], by decide⟩]) (r1.parts) ([]) (Header.tags ++ TradeCaptureReportAck.tags ++ [[[49, 53, 48]]]) (TradeCaptureReportAckTradeCorrect.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[71], by decide⟩] ++ r1.parts) (Header.tags ++ TradeCaptureReportAck.tags ++ [[[49, 53, 48]]] ++ TradeCaptureReportAckTradeCorrect.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_allocationInstructionAck (header : Header) (r0 : AllocationInstructionAck) :
    Message.decode (Message.tokens (.allocationInstructionAck header r0)) = some (.allocationInstructionAck header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (AllocationInstructionAck.tags) rfl rfl (by decide +kernel))
  have c1 := AllocationInstructionAck.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (AllocationInstructionAck.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ AllocationInstructionAck.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_allocationReport (header : Header) (r0 : AllocationReport) :
    Message.decode (Message.tokens (.allocationReport header r0)) = some (.allocationReport header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (AllocationReport.tags) rfl rfl (by decide +kernel))
  have c1 := AllocationReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (AllocationReport.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ AllocationReport.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | logon header r0 => exact Message.decode_logon header r0
  | logout header r0 => exact Message.decode_logout header r0
  | sequenceReset header r0 => exact Message.decode_sequenceReset header r0
  | reject header r0 => exact Message.decode_reject header r0
  | heartbeat header r0 => exact Message.decode_heartbeat header r0
  | testRequest header r0 => exact Message.decode_testRequest header r0
  | userResponse header r0 => exact Message.decode_userResponse header r0
  | userNotification header r0 => exact Message.decode_userNotification header r0
  | orderCancelReject header r0 => exact Message.decode_orderCancelReject header r0
  | executionReportNew header r0 r1 => exact Message.decode_executionReportNew header r0 r1
  | executionReportCanceled header r0 r1 => exact Message.decode_executionReportCanceled header r0 r1
  | executionReportRejected header r0 r1 => exact Message.decode_executionReportRejected header r0 r1
  | executionReportRestated header r0 r1 => exact Message.decode_executionReportRestated header r0 r1
  | executionReportSuspended header r0 r1 => exact Message.decode_executionReportSuspended header r0 r1
  | executionReportExpired header r0 r1 => exact Message.decode_executionReportExpired header r0 r1
  | executionReportTrade header r0 r1 => exact Message.decode_executionReportTrade header r0 r1
  | businessMessageReject header r0 => exact Message.decode_businessMessageReject header r0
  | securityDefinition header r0 => exact Message.decode_securityDefinition header r0
  | securityDefinitionUpdateReport header r0 => exact Message.decode_securityDefinitionUpdateReport header r0
  | massQuoteAcknowledgement header r0 => exact Message.decode_massQuoteAcknowledgement header r0
  | quoteRequest header r0 => exact Message.decode_quoteRequest header r0
  | quoteRequestReject header r0 => exact Message.decode_quoteRequestReject header r0
  | tradeCaptureReportSubmit header r0 r1 => exact Message.decode_tradeCaptureReportSubmit header r0 r1
  | tradeCaptureReportAlleged header r0 r1 => exact Message.decode_tradeCaptureReportAlleged header r0 r1
  | tradeCaptureReportTradeCancelRequest header r0 r1 => exact Message.decode_tradeCaptureReportTradeCancelRequest header r0 r1
  | tradeCaptureReportAckNew header r0 r1 => exact Message.decode_tradeCaptureReportAckNew header r0 r1
  | tradeCaptureReportAckRejected header r0 r1 => exact Message.decode_tradeCaptureReportAckRejected header r0 r1
  | tradeCaptureReportAckCanceled header r0 r1 => exact Message.decode_tradeCaptureReportAckCanceled header r0 r1
  | tradeCaptureReportAckTradeCorrect header r0 r1 => exact Message.decode_tradeCaptureReportAckTradeCorrect header r0 r1
  | allocationInstructionAck header r0 => exact Message.decode_allocationInstructionAck header r0
  | allocationReport header r0 => exact Message.decode_allocationReport header r0

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

theorem Message.decodeBytes_reject (header : Header) (r0 : Reject) :
    Message.decodeBytes (Message.encode (.reject header r0)) = some (.reject header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[51], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ Reject.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_reject header r0

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

theorem Message.decodeBytes_userResponse (header : Header) (r0 : UserResponse) :
    Message.decodeBytes (Message.encode (.userResponse header r0)) = some (.userResponse header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[66, 70], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ UserResponse.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_userResponse header r0

theorem Message.decodeBytes_userNotification (header : Header) (r0 : UserNotification) :
    Message.decodeBytes (Message.encode (.userNotification header r0)) = some (.userNotification header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[67, 66], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ UserNotification.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_userNotification header r0

theorem Message.decodeBytes_orderCancelReject (header : Header) (r0 : OrderCancelReject) :
    Message.decodeBytes (Message.encode (.orderCancelReject header r0)) = some (.orderCancelReject header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[57], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ OrderCancelReject.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderCancelReject header r0

theorem Message.decodeBytes_executionReportNew (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportNew) :
    Message.decodeBytes (Message.encode (.executionReportNew header r0 r1)) = some (.executionReportNew header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportNew.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportNew header r0 r1

theorem Message.decodeBytes_executionReportCanceled (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCanceled) :
    Message.decodeBytes (Message.encode (.executionReportCanceled header r0 r1)) = some (.executionReportCanceled header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCanceled.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportCanceled header r0 r1

theorem Message.decodeBytes_executionReportRejected (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportRejected) :
    Message.decodeBytes (Message.encode (.executionReportRejected header r0 r1)) = some (.executionReportRejected header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRejected.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportRejected header r0 r1

theorem Message.decodeBytes_executionReportRestated (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportRestated) :
    Message.decodeBytes (Message.encode (.executionReportRestated header r0 r1)) = some (.executionReportRestated header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[68], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRestated.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportRestated header r0 r1

theorem Message.decodeBytes_executionReportSuspended (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportSuspended) :
    Message.decodeBytes (Message.encode (.executionReportSuspended header r0 r1)) = some (.executionReportSuspended header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[57], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportSuspended.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportSuspended header r0 r1

theorem Message.decodeBytes_executionReportExpired (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportExpired) :
    Message.decodeBytes (Message.encode (.executionReportExpired header r0 r1)) = some (.executionReportExpired header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[67], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportExpired.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportExpired header r0 r1

theorem Message.decodeBytes_executionReportTrade (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportTrade) :
    Message.decodeBytes (Message.encode (.executionReportTrade header r0 r1)) = some (.executionReportTrade header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[70], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportTrade.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportTrade header r0 r1

theorem Message.decodeBytes_businessMessageReject (header : Header) (r0 : BusinessMessageReject) :
    Message.decodeBytes (Message.encode (.businessMessageReject header r0)) = some (.businessMessageReject header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[106], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ BusinessMessageReject.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_businessMessageReject header r0

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

theorem Message.decodeBytes_massQuoteAcknowledgement (header : Header) (r0 : MassQuoteAcknowledgement) :
    Message.decodeBytes (Message.encode (.massQuoteAcknowledgement header r0)) = some (.massQuoteAcknowledgement header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[98], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ MassQuoteAcknowledgement.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_massQuoteAcknowledgement header r0

theorem Message.decodeBytes_quoteRequest (header : Header) (r0 : QuoteRequest) :
    Message.decodeBytes (Message.encode (.quoteRequest header r0)) = some (.quoteRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[82], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ QuoteRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_quoteRequest header r0

theorem Message.decodeBytes_quoteRequestReject (header : Header) (r0 : QuoteRequestReject) :
    Message.decodeBytes (Message.encode (.quoteRequestReject header r0)) = some (.quoteRequestReject header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[65, 71], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ QuoteRequestReject.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_quoteRequestReject header r0

theorem Message.decodeBytes_tradeCaptureReportSubmit (header : Header) (r0 : TradeCaptureReport) (r1 : TradeCaptureReportSubmit) :
    Message.decodeBytes (Message.encode (.tradeCaptureReportSubmit header r0 r1)) = some (.tradeCaptureReportSubmit header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[65, 69], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [56, 53, 54] ⟨[48], by decide⟩] ++ r1.parts) (Header.tags ++ TradeCaptureReport.tags ++ [[[56, 53, 54]]] ++ TradeCaptureReportSubmit.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_tradeCaptureReportSubmit header r0 r1

theorem Message.decodeBytes_tradeCaptureReportAlleged (header : Header) (r0 : TradeCaptureReport) (r1 : TradeCaptureReportAlleged) :
    Message.decodeBytes (Message.encode (.tradeCaptureReportAlleged header r0 r1)) = some (.tradeCaptureReportAlleged header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[65, 69], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [56, 53, 54] ⟨[49], by decide⟩] ++ r1.parts) (Header.tags ++ TradeCaptureReport.tags ++ [[[56, 53, 54]]] ++ TradeCaptureReportAlleged.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_tradeCaptureReportAlleged header r0 r1

theorem Message.decodeBytes_tradeCaptureReportTradeCancelRequest (header : Header) (r0 : TradeCaptureReport) (r1 : TradeCaptureReportTradeCancelRequest) :
    Message.decodeBytes (Message.encode (.tradeCaptureReportTradeCancelRequest header r0 r1)) = some (.tradeCaptureReportTradeCancelRequest header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[65, 69], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [56, 53, 54] ⟨[56], by decide⟩] ++ r1.parts) (Header.tags ++ TradeCaptureReport.tags ++ [[[56, 53, 54]]] ++ TradeCaptureReportTradeCancelRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_tradeCaptureReportTradeCancelRequest header r0 r1

theorem Message.decodeBytes_tradeCaptureReportAckNew (header : Header) (r0 : TradeCaptureReportAck) (r1 : TradeCaptureReportAckNew) :
    Message.decodeBytes (Message.encode (.tradeCaptureReportAckNew header r0 r1)) = some (.tradeCaptureReportAckNew header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[65, 82], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts) (Header.tags ++ TradeCaptureReportAck.tags ++ [[[49, 53, 48]]] ++ TradeCaptureReportAckNew.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_tradeCaptureReportAckNew header r0 r1

theorem Message.decodeBytes_tradeCaptureReportAckRejected (header : Header) (r0 : TradeCaptureReportAck) (r1 : TradeCaptureReportAckRejected) :
    Message.decodeBytes (Message.encode (.tradeCaptureReportAckRejected header r0 r1)) = some (.tradeCaptureReportAckRejected header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[65, 82], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r1.parts) (Header.tags ++ TradeCaptureReportAck.tags ++ [[[49, 53, 48]]] ++ TradeCaptureReportAckRejected.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_tradeCaptureReportAckRejected header r0 r1

theorem Message.decodeBytes_tradeCaptureReportAckCanceled (header : Header) (r0 : TradeCaptureReportAck) (r1 : TradeCaptureReportAckCanceled) :
    Message.decodeBytes (Message.encode (.tradeCaptureReportAckCanceled header r0 r1)) = some (.tradeCaptureReportAckCanceled header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[65, 82], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r1.parts) (Header.tags ++ TradeCaptureReportAck.tags ++ [[[49, 53, 48]]] ++ TradeCaptureReportAckCanceled.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_tradeCaptureReportAckCanceled header r0 r1

theorem Message.decodeBytes_tradeCaptureReportAckTradeCorrect (header : Header) (r0 : TradeCaptureReportAck) (r1 : TradeCaptureReportAckTradeCorrect) :
    Message.decodeBytes (Message.encode (.tradeCaptureReportAckTradeCorrect header r0 r1)) = some (.tradeCaptureReportAckTradeCorrect header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[65, 82], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[71], by decide⟩] ++ r1.parts) (Header.tags ++ TradeCaptureReportAck.tags ++ [[[49, 53, 48]]] ++ TradeCaptureReportAckTradeCorrect.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_tradeCaptureReportAckTradeCorrect header r0 r1

theorem Message.decodeBytes_allocationInstructionAck (header : Header) (r0 : AllocationInstructionAck) :
    Message.decodeBytes (Message.encode (.allocationInstructionAck header r0)) = some (.allocationInstructionAck header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[65, 84], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ AllocationInstructionAck.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_allocationInstructionAck header r0

theorem Message.decodeBytes_allocationReport (header : Header) (r0 : AllocationReport) :
    Message.decodeBytes (Message.encode (.allocationReport header r0)) = some (.allocationReport header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[65, 83], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ AllocationReport.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_allocationReport header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | logon header r0 => exact Message.decodeBytes_logon header r0
  | logout header r0 => exact Message.decodeBytes_logout header r0
  | sequenceReset header r0 => exact Message.decodeBytes_sequenceReset header r0
  | reject header r0 => exact Message.decodeBytes_reject header r0
  | heartbeat header r0 => exact Message.decodeBytes_heartbeat header r0
  | testRequest header r0 => exact Message.decodeBytes_testRequest header r0
  | userResponse header r0 => exact Message.decodeBytes_userResponse header r0
  | userNotification header r0 => exact Message.decodeBytes_userNotification header r0
  | orderCancelReject header r0 => exact Message.decodeBytes_orderCancelReject header r0
  | executionReportNew header r0 r1 => exact Message.decodeBytes_executionReportNew header r0 r1
  | executionReportCanceled header r0 r1 => exact Message.decodeBytes_executionReportCanceled header r0 r1
  | executionReportRejected header r0 r1 => exact Message.decodeBytes_executionReportRejected header r0 r1
  | executionReportRestated header r0 r1 => exact Message.decodeBytes_executionReportRestated header r0 r1
  | executionReportSuspended header r0 r1 => exact Message.decodeBytes_executionReportSuspended header r0 r1
  | executionReportExpired header r0 r1 => exact Message.decodeBytes_executionReportExpired header r0 r1
  | executionReportTrade header r0 r1 => exact Message.decodeBytes_executionReportTrade header r0 r1
  | businessMessageReject header r0 => exact Message.decodeBytes_businessMessageReject header r0
  | securityDefinition header r0 => exact Message.decodeBytes_securityDefinition header r0
  | securityDefinitionUpdateReport header r0 => exact Message.decodeBytes_securityDefinitionUpdateReport header r0
  | massQuoteAcknowledgement header r0 => exact Message.decodeBytes_massQuoteAcknowledgement header r0
  | quoteRequest header r0 => exact Message.decodeBytes_quoteRequest header r0
  | quoteRequestReject header r0 => exact Message.decodeBytes_quoteRequestReject header r0
  | tradeCaptureReportSubmit header r0 r1 => exact Message.decodeBytes_tradeCaptureReportSubmit header r0 r1
  | tradeCaptureReportAlleged header r0 r1 => exact Message.decodeBytes_tradeCaptureReportAlleged header r0 r1
  | tradeCaptureReportTradeCancelRequest header r0 r1 => exact Message.decodeBytes_tradeCaptureReportTradeCancelRequest header r0 r1
  | tradeCaptureReportAckNew header r0 r1 => exact Message.decodeBytes_tradeCaptureReportAckNew header r0 r1
  | tradeCaptureReportAckRejected header r0 r1 => exact Message.decodeBytes_tradeCaptureReportAckRejected header r0 r1
  | tradeCaptureReportAckCanceled header r0 r1 => exact Message.decodeBytes_tradeCaptureReportAckCanceled header r0 r1
  | tradeCaptureReportAckTradeCorrect header r0 r1 => exact Message.decodeBytes_tradeCaptureReportAckTradeCorrect header r0 r1
  | allocationInstructionAck header r0 => exact Message.decodeBytes_allocationInstructionAck header r0
  | allocationReport header r0 => exact Message.decodeBytes_allocationReport header r0

/-- BeginString as the venue fixes it: FIXT.1.1 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 84, 46, 49, 46, 49, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.BistBorsaistanbulOrderentryFixV1064Exchange
