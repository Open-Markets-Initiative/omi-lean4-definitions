import Wire

/-!
# Singapore Exchange Order Entry v1.5.5, Client messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.SgxTitanotcOrderentryFixV155Client

structure Header where
  senderCompID : Terminated 1  -- tag 49
  targetCompID : Terminated 1  -- tag 56
  targetSubID : Option (Terminated 1)  -- tag 57
  msgSeqNum : Terminated 1  -- tag 34
  sendingTime : Terminated 1  -- tag 52
  senderSubID : Option (Terminated 1)  -- tag 50
  possDupFlag : Option (Terminated 1)  -- tag 43
  possResend : Option (Terminated 1)  -- tag 97
  origSendingTime : Option (Terminated 1)  -- tag 122

def Header.parts (record : Header) : List Part :=
  [Part.required [52, 57] record.senderCompID,
   Part.required [53, 54] record.targetCompID,
   Part.optional [53, 55] record.targetSubID,
   Part.required [51, 52] record.msgSeqNum,
   Part.required [53, 50] record.sendingTime,
   Part.optional [53, 48] record.senderSubID,
   Part.optional [52, 51] record.possDupFlag,
   Part.optional [57, 55] record.possResend,
   Part.optional [49, 50, 50] record.origSendingTime]

def Header.tags : List (List (List UInt8)) :=
  [[[52, 57]], [[53, 54]], [[53, 55]], [[51, 52]], [[53, 50]], [[53, 48]], [[52, 51]], [[57, 55]], [[49, 50, 50]]]

theorem Header.shape (record : Header) : record.parts.map Part.tags = Header.tags := rfl

def Header.decode (tokens : List Token) : Option Header := do
  let senderCompID ← readRequired [52, 57] tokens
  let targetCompID ← readRequired [53, 54] tokens
  let targetSubID ← readOptional [53, 55] tokens
  let msgSeqNum ← readRequired [51, 52] tokens
  let sendingTime ← readRequired [53, 50] tokens
  let senderSubID ← readOptional [53, 48] tokens
  let possDupFlag ← readOptional [52, 51] tokens
  let possResend ← readOptional [57, 55] tokens
  let origSendingTime ← readOptional [49, 50, 50] tokens
  pure { senderCompID, targetCompID, targetSubID, msgSeqNum, sendingTime, senderSubID, possDupFlag, possResend, origSendingTime }

theorem Header.decode_agrees (record : Header) (tokens : List Token)
    (agrees : ∀ tags ∈ Header.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Header.decode tokens = some record := by
  have distinct : Header.tags.flatten.Nodup := by decide +kernel
  have senderCompID := readRequired_part [52, 57] record.senderCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have targetCompID := readRequired_part [53, 54] record.targetCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have targetSubID := readOptional_part [53, 55] record.targetSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have msgSeqNum := readRequired_part [51, 52] record.msgSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have sendingTime := readRequired_part [53, 50] record.sendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have senderSubID := readOptional_part [53, 48] record.senderSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have possDupFlag := readOptional_part [52, 51] record.possDupFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have possResend := readOptional_part [57, 55] record.possResend tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have origSendingTime := readOptional_part [49, 50, 50] record.origSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  simp only [Header.decode, senderCompID, targetCompID, targetSubID, msgSeqNum, sendingTime, senderSubID, possDupFlag, possResend, origSendingTime, some_bind] <;> rfl

structure Logon where
  username : Terminated 1  -- tag 553
  password : Terminated 1  -- tag 554
  newPassword : Option (Terminated 1)  -- tag 925
  encryptMethod : Terminated 1  -- tag 98
  heartBtInt : Terminated 1  -- tag 108
  defaultApplVerID : Terminated 1  -- tag 1137
  sessionStatus : Option (Terminated 1)  -- tag 1409
  text : Option (Terminated 1)  -- tag 58

def Logon.parts (record : Logon) : List Part :=
  [Part.required [53, 53, 51] record.username,
   Part.required [53, 53, 52] record.password,
   Part.optional [57, 50, 53] record.newPassword,
   Part.required [57, 56] record.encryptMethod,
   Part.required [49, 48, 56] record.heartBtInt,
   Part.required [49, 49, 51, 55] record.defaultApplVerID,
   Part.optional [49, 52, 48, 57] record.sessionStatus,
   Part.optional [53, 56] record.text]

def Logon.tags : List (List (List UInt8)) :=
  [[[53, 53, 51]], [[53, 53, 52]], [[57, 50, 53]], [[57, 56]], [[49, 48, 56]], [[49, 49, 51, 55]], [[49, 52, 48, 57]], [[53, 56]]]

theorem Logon.shape (record : Logon) : record.parts.map Part.tags = Logon.tags := rfl

def Logon.decode (tokens : List Token) : Option Logon := do
  let username ← readRequired [53, 53, 51] tokens
  let password ← readRequired [53, 53, 52] tokens
  let newPassword ← readOptional [57, 50, 53] tokens
  let encryptMethod ← readRequired [57, 56] tokens
  let heartBtInt ← readRequired [49, 48, 56] tokens
  let defaultApplVerID ← readRequired [49, 49, 51, 55] tokens
  let sessionStatus ← readOptional [49, 52, 48, 57] tokens
  let text ← readOptional [53, 56] tokens
  pure { username, password, newPassword, encryptMethod, heartBtInt, defaultApplVerID, sessionStatus, text }

theorem Logon.decode_agrees (record : Logon) (tokens : List Token)
    (agrees : ∀ tags ∈ Logon.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Logon.decode tokens = some record := by
  have distinct : Logon.tags.flatten.Nodup := by decide +kernel
  have username := readRequired_part [53, 53, 51] record.username tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have password := readRequired_part [53, 53, 52] record.password tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have newPassword := readOptional_part [57, 50, 53] record.newPassword tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have encryptMethod := readRequired_part [57, 56] record.encryptMethod tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have heartBtInt := readRequired_part [49, 48, 56] record.heartBtInt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have defaultApplVerID := readRequired_part [49, 49, 51, 55] record.defaultApplVerID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have sessionStatus := readOptional_part [49, 52, 48, 57] record.sessionStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  simp only [Logon.decode, username, password, newPassword, encryptMethod, heartBtInt, defaultApplVerID, sessionStatus, text, some_bind] <;> rfl

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

structure NoPartySubIDs where
  partySubID : Terminated 1  -- tag 523
  partySubIDType : Option (Terminated 1)  -- tag 803

def NoPartySubIDs.parts (record : NoPartySubIDs) : List Part :=
  [Part.required [53, 50, 51] record.partySubID,
   Part.optional [56, 48, 51] record.partySubIDType]

def NoPartySubIDs.tags : List (List (List UInt8)) :=
  [[[53, 50, 51]], [[56, 48, 51]]]

theorem NoPartySubIDs.shape (record : NoPartySubIDs) : record.parts.map Part.tags = NoPartySubIDs.tags := rfl

def NoPartySubIDs.decode (tokens : List Token) : Option NoPartySubIDs := do
  let partySubID ← readRequired [53, 50, 51] tokens
  let partySubIDType ← readOptional [56, 48, 51] tokens
  pure { partySubID, partySubIDType }

theorem NoPartySubIDs.decode_agrees (record : NoPartySubIDs) (tokens : List Token)
    (agrees : ∀ tags ∈ NoPartySubIDs.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoPartySubIDs.decode tokens = some record := by
  have distinct : NoPartySubIDs.tags.flatten.Nodup := by decide +kernel
  have partySubID := readRequired_part [53, 50, 51] record.partySubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have partySubIDType := readOptional_part [56, 48, 51] record.partySubIDType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [NoPartySubIDs.decode, partySubID, partySubIDType, some_bind] <;> rfl

def NoPartySubIDs.members : List (List UInt8) := NoPartySubIDs.tags.flatten

def NoPartySubIDs.encode (entry : NoPartySubIDs) : List Token := encodeParts entry.parts

theorem NoPartySubIDs.decode_encode (entry : NoPartySubIDs) : NoPartySubIDs.decode entry.encode = some entry :=
  NoPartySubIDs.decode_agrees entry _ (fun _ _ => rfl)

theorem NoPartySubIDs.within (entry : NoPartySubIDs) : ∀ token ∈ entry.encode, token.tag ∈ NoPartySubIDs.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoPartySubIDs.shape] at this

theorem NoPartySubIDs.led (entry : NoPartySubIDs) : Lead [53, 50, 51] entry.encode :=
  lead_parts [53, 50, 51] entry.partySubID _ NoPartySubIDs.tags.tail rfl (by decide +kernel)

structure NoPartyIDs where
  partyID : Terminated 1  -- tag 448
  partyIDSource : Option (Terminated 1)  -- tag 447
  partyRole : Terminated 1  -- tag 452
  noPartySubIDs : List NoPartySubIDs  -- tag 802

def NoPartyIDs.parts (record : NoPartyIDs) : List Part :=
  [Part.required [52, 52, 56] record.partyID,
   Part.optional [52, 52, 55] record.partyIDSource,
   Part.required [52, 53, 50] record.partyRole,
   Part.group [56, 48, 50] NoPartySubIDs.members NoPartySubIDs.encode NoPartySubIDs.within record.noPartySubIDs]

def NoPartyIDs.tags : List (List (List UInt8)) :=
  [[[52, 52, 56]], [[52, 52, 55]], [[52, 53, 50]], [56, 48, 50] :: NoPartySubIDs.members]

theorem NoPartyIDs.shape (record : NoPartyIDs) : record.parts.map Part.tags = NoPartyIDs.tags := rfl

def NoPartyIDs.decode (tokens : List Token) : Option NoPartyIDs := do
  let partyID ← readRequired [52, 52, 56] tokens
  let partyIDSource ← readOptional [52, 52, 55] tokens
  let partyRole ← readRequired [52, 53, 50] tokens
  let noPartySubIDs ← readGroup [56, 48, 50] [53, 50, 51] NoPartySubIDs.members NoPartySubIDs.decode tokens
  pure { partyID, partyIDSource, partyRole, noPartySubIDs }

theorem NoPartyIDs.decode_agrees (record : NoPartyIDs) (tokens : List Token)
    (agrees : ∀ tags ∈ NoPartyIDs.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoPartyIDs.decode tokens = some record := by
  have distinct : NoPartyIDs.tags.flatten.Nodup := by decide +kernel
  have partyID := readRequired_part [52, 52, 56] record.partyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have partyIDSource := readOptional_part [52, 52, 55] record.partyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have partyRole := readRequired_part [52, 53, 50] record.partyRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have noPartySubIDs := readGroup_part [56, 48, 50] [53, 50, 51] NoPartySubIDs.members NoPartySubIDs.encode NoPartySubIDs.within NoPartySubIDs.decode NoPartySubIDs.decode_encode NoPartySubIDs.led record.noPartySubIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [NoPartyIDs.decode, partyID, partyIDSource, partyRole, noPartySubIDs, some_bind] <;> rfl

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

structure NoTargetPartySubIDs where
  targetPartySubID : Terminated 1  -- tag 2434
  targetPartySubIDType : Option (Terminated 1)  -- tag 2435

def NoTargetPartySubIDs.parts (record : NoTargetPartySubIDs) : List Part :=
  [Part.required [50, 52, 51, 52] record.targetPartySubID,
   Part.optional [50, 52, 51, 53] record.targetPartySubIDType]

def NoTargetPartySubIDs.tags : List (List (List UInt8)) :=
  [[[50, 52, 51, 52]], [[50, 52, 51, 53]]]

theorem NoTargetPartySubIDs.shape (record : NoTargetPartySubIDs) : record.parts.map Part.tags = NoTargetPartySubIDs.tags := rfl

def NoTargetPartySubIDs.decode (tokens : List Token) : Option NoTargetPartySubIDs := do
  let targetPartySubID ← readRequired [50, 52, 51, 52] tokens
  let targetPartySubIDType ← readOptional [50, 52, 51, 53] tokens
  pure { targetPartySubID, targetPartySubIDType }

theorem NoTargetPartySubIDs.decode_agrees (record : NoTargetPartySubIDs) (tokens : List Token)
    (agrees : ∀ tags ∈ NoTargetPartySubIDs.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoTargetPartySubIDs.decode tokens = some record := by
  have distinct : NoTargetPartySubIDs.tags.flatten.Nodup := by decide +kernel
  have targetPartySubID := readRequired_part [50, 52, 51, 52] record.targetPartySubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have targetPartySubIDType := readOptional_part [50, 52, 51, 53] record.targetPartySubIDType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [NoTargetPartySubIDs.decode, targetPartySubID, targetPartySubIDType, some_bind] <;> rfl

def NoTargetPartySubIDs.members : List (List UInt8) := NoTargetPartySubIDs.tags.flatten

def NoTargetPartySubIDs.encode (entry : NoTargetPartySubIDs) : List Token := encodeParts entry.parts

theorem NoTargetPartySubIDs.decode_encode (entry : NoTargetPartySubIDs) : NoTargetPartySubIDs.decode entry.encode = some entry :=
  NoTargetPartySubIDs.decode_agrees entry _ (fun _ _ => rfl)

theorem NoTargetPartySubIDs.within (entry : NoTargetPartySubIDs) : ∀ token ∈ entry.encode, token.tag ∈ NoTargetPartySubIDs.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoTargetPartySubIDs.shape] at this

theorem NoTargetPartySubIDs.led (entry : NoTargetPartySubIDs) : Lead [50, 52, 51, 52] entry.encode :=
  lead_parts [50, 52, 51, 52] entry.targetPartySubID _ NoTargetPartySubIDs.tags.tail rfl (by decide +kernel)

structure NoTargetPartyIDs where
  targetPartyID : Terminated 1  -- tag 1462
  targetPartyIDSource : Option (Terminated 1)  -- tag 1463
  targetPartyRole : Option (Terminated 1)  -- tag 1464
  noTargetPartySubIDs : List NoTargetPartySubIDs  -- tag 2433

def NoTargetPartyIDs.parts (record : NoTargetPartyIDs) : List Part :=
  [Part.required [49, 52, 54, 50] record.targetPartyID,
   Part.optional [49, 52, 54, 51] record.targetPartyIDSource,
   Part.optional [49, 52, 54, 52] record.targetPartyRole,
   Part.group [50, 52, 51, 51] NoTargetPartySubIDs.members NoTargetPartySubIDs.encode NoTargetPartySubIDs.within record.noTargetPartySubIDs]

def NoTargetPartyIDs.tags : List (List (List UInt8)) :=
  [[[49, 52, 54, 50]], [[49, 52, 54, 51]], [[49, 52, 54, 52]], [50, 52, 51, 51] :: NoTargetPartySubIDs.members]

theorem NoTargetPartyIDs.shape (record : NoTargetPartyIDs) : record.parts.map Part.tags = NoTargetPartyIDs.tags := rfl

def NoTargetPartyIDs.decode (tokens : List Token) : Option NoTargetPartyIDs := do
  let targetPartyID ← readRequired [49, 52, 54, 50] tokens
  let targetPartyIDSource ← readOptional [49, 52, 54, 51] tokens
  let targetPartyRole ← readOptional [49, 52, 54, 52] tokens
  let noTargetPartySubIDs ← readGroup [50, 52, 51, 51] [50, 52, 51, 52] NoTargetPartySubIDs.members NoTargetPartySubIDs.decode tokens
  pure { targetPartyID, targetPartyIDSource, targetPartyRole, noTargetPartySubIDs }

theorem NoTargetPartyIDs.decode_agrees (record : NoTargetPartyIDs) (tokens : List Token)
    (agrees : ∀ tags ∈ NoTargetPartyIDs.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoTargetPartyIDs.decode tokens = some record := by
  have distinct : NoTargetPartyIDs.tags.flatten.Nodup := by decide +kernel
  have targetPartyID := readRequired_part [49, 52, 54, 50] record.targetPartyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have targetPartyIDSource := readOptional_part [49, 52, 54, 51] record.targetPartyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have targetPartyRole := readOptional_part [49, 52, 54, 52] record.targetPartyRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have noTargetPartySubIDs := readGroup_part [50, 52, 51, 51] [50, 52, 51, 52] NoTargetPartySubIDs.members NoTargetPartySubIDs.encode NoTargetPartySubIDs.within NoTargetPartySubIDs.decode NoTargetPartySubIDs.decode_encode NoTargetPartySubIDs.led record.noTargetPartySubIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [NoTargetPartyIDs.decode, targetPartyID, targetPartyIDSource, targetPartyRole, noTargetPartySubIDs, some_bind] <;> rfl

def NoTargetPartyIDs.members : List (List UInt8) := NoTargetPartyIDs.tags.flatten

def NoTargetPartyIDs.encode (entry : NoTargetPartyIDs) : List Token := encodeParts entry.parts

theorem NoTargetPartyIDs.decode_encode (entry : NoTargetPartyIDs) : NoTargetPartyIDs.decode entry.encode = some entry :=
  NoTargetPartyIDs.decode_agrees entry _ (fun _ _ => rfl)

theorem NoTargetPartyIDs.within (entry : NoTargetPartyIDs) : ∀ token ∈ entry.encode, token.tag ∈ NoTargetPartyIDs.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoTargetPartyIDs.shape] at this

theorem NoTargetPartyIDs.led (entry : NoTargetPartyIDs) : Lead [49, 52, 54, 50] entry.encode :=
  lead_parts [49, 52, 54, 50] entry.targetPartyID _ NoTargetPartyIDs.tags.tail rfl (by decide +kernel)

structure NoValueChecks where
  valueCheckType : Terminated 1  -- tag 1869
  valueCheckAction : Option (Terminated 1)  -- tag 1870

def NoValueChecks.parts (record : NoValueChecks) : List Part :=
  [Part.required [49, 56, 54, 57] record.valueCheckType,
   Part.optional [49, 56, 55, 48] record.valueCheckAction]

def NoValueChecks.tags : List (List (List UInt8)) :=
  [[[49, 56, 54, 57]], [[49, 56, 55, 48]]]

theorem NoValueChecks.shape (record : NoValueChecks) : record.parts.map Part.tags = NoValueChecks.tags := rfl

def NoValueChecks.decode (tokens : List Token) : Option NoValueChecks := do
  let valueCheckType ← readRequired [49, 56, 54, 57] tokens
  let valueCheckAction ← readOptional [49, 56, 55, 48] tokens
  pure { valueCheckType, valueCheckAction }

theorem NoValueChecks.decode_agrees (record : NoValueChecks) (tokens : List Token)
    (agrees : ∀ tags ∈ NoValueChecks.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoValueChecks.decode tokens = some record := by
  have distinct : NoValueChecks.tags.flatten.Nodup := by decide +kernel
  have valueCheckType := readRequired_part [49, 56, 54, 57] record.valueCheckType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have valueCheckAction := readOptional_part [49, 56, 55, 48] record.valueCheckAction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [NoValueChecks.decode, valueCheckType, valueCheckAction, some_bind] <;> rfl

def NoValueChecks.members : List (List UInt8) := NoValueChecks.tags.flatten

def NoValueChecks.encode (entry : NoValueChecks) : List Token := encodeParts entry.parts

theorem NoValueChecks.decode_encode (entry : NoValueChecks) : NoValueChecks.decode entry.encode = some entry :=
  NoValueChecks.decode_agrees entry _ (fun _ _ => rfl)

theorem NoValueChecks.within (entry : NoValueChecks) : ∀ token ∈ entry.encode, token.tag ∈ NoValueChecks.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoValueChecks.shape] at this

theorem NoValueChecks.led (entry : NoValueChecks) : Lead [49, 56, 54, 57] entry.encode :=
  lead_parts [49, 56, 54, 57] entry.valueCheckType _ NoValueChecks.tags.tail rfl (by decide +kernel)

structure NewOrderSingle where
  clOrdID : Terminated 1  -- tag 11
  noPartyIDs : List NoPartyIDs  -- tag 453
  noTargetPartyIDs : List NoTargetPartyIDs  -- tag 1461
  account : Option (Terminated 1)  -- tag 1
  execInst : Option (Terminated 1)  -- tag 18
  noValueChecks : List NoValueChecks  -- tag 1868
  symbol : Terminated 1  -- tag 55
  side : Terminated 1  -- tag 54
  transactTime : Terminated 1  -- tag 60
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  timeInForce : Option (Terminated 1)  -- tag 59
  exposureDuration : Option (Terminated 1)  -- tag 1629
  refOrderID : Option (Terminated 1)  -- tag 1080
  refOrderIDSource : Option (Terminated 1)  -- tag 1081

def NewOrderSingle.parts (record : NewOrderSingle) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.group [49, 52, 54, 49] NoTargetPartyIDs.members NoTargetPartyIDs.encode NoTargetPartyIDs.within record.noTargetPartyIDs,
   Part.optional [49] record.account,
   Part.optional [49, 56] record.execInst,
   Part.group [49, 56, 54, 56] NoValueChecks.members NoValueChecks.encode NoValueChecks.within record.noValueChecks,
   Part.required [53, 53] record.symbol,
   Part.required [53, 52] record.side,
   Part.required [54, 48] record.transactTime,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.optional [53, 57] record.timeInForce,
   Part.optional [49, 54, 50, 57] record.exposureDuration,
   Part.optional [49, 48, 56, 48] record.refOrderID,
   Part.optional [49, 48, 56, 49] record.refOrderIDSource]

def NewOrderSingle.tags : List (List (List UInt8)) :=
  [[[49, 49]], [52, 53, 51] :: NoPartyIDs.members, [49, 52, 54, 49] :: NoTargetPartyIDs.members, [[49]], [[49, 56]], [49, 56, 54, 56] :: NoValueChecks.members, [[53, 53]], [[53, 52]], [[54, 48]], [[51, 56]], [[52, 48]], [[52, 52]], [[53, 57]], [[49, 54, 50, 57]], [[49, 48, 56, 48]], [[49, 48, 56, 49]]]

theorem NewOrderSingle.shape (record : NewOrderSingle) : record.parts.map Part.tags = NewOrderSingle.tags := rfl

def NewOrderSingle.decode (tokens : List Token) : Option NewOrderSingle := do
  let clOrdID ← readRequired [49, 49] tokens
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let noTargetPartyIDs ← readGroup [49, 52, 54, 49] [49, 52, 54, 50] NoTargetPartyIDs.members NoTargetPartyIDs.decode tokens
  let account ← readOptional [49] tokens
  let execInst ← readOptional [49, 56] tokens
  let noValueChecks ← readGroup [49, 56, 54, 56] [49, 56, 54, 57] NoValueChecks.members NoValueChecks.decode tokens
  let symbol ← readRequired [53, 53] tokens
  let side ← readRequired [53, 52] tokens
  let transactTime ← readRequired [54, 48] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let exposureDuration ← readOptional [49, 54, 50, 57] tokens
  let refOrderID ← readOptional [49, 48, 56, 48] tokens
  let refOrderIDSource ← readOptional [49, 48, 56, 49] tokens
  pure { clOrdID, noPartyIDs, noTargetPartyIDs, account, execInst, noValueChecks, symbol, side, transactTime, orderQty, ordType, price, timeInForce, exposureDuration, refOrderID, refOrderIDSource }

theorem NewOrderSingle.decode_agrees (record : NewOrderSingle) (tokens : List Token)
    (agrees : ∀ tags ∈ NewOrderSingle.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NewOrderSingle.decode tokens = some record := by
  have distinct : NewOrderSingle.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have noTargetPartyIDs := readGroup_part [49, 52, 54, 49] [49, 52, 54, 50] NoTargetPartyIDs.members NoTargetPartyIDs.encode NoTargetPartyIDs.within NoTargetPartyIDs.decode NoTargetPartyIDs.decode_encode NoTargetPartyIDs.led record.noTargetPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have noValueChecks := readGroup_part [49, 56, 54, 56] [49, 56, 54, 57] NoValueChecks.members NoValueChecks.encode NoValueChecks.within NoValueChecks.decode NoValueChecks.decode_encode NoValueChecks.led record.noValueChecks tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have exposureDuration := readOptional_part [49, 54, 50, 57] record.exposureDuration tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have refOrderID := readOptional_part [49, 48, 56, 48] record.refOrderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have refOrderIDSource := readOptional_part [49, 48, 56, 49] record.refOrderIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  simp only [NewOrderSingle.decode, clOrdID, noPartyIDs, noTargetPartyIDs, account, execInst, noValueChecks, symbol, side, transactTime, orderQty, ordType, price, timeInForce, exposureDuration, refOrderID, refOrderIDSource, some_bind] <;> rfl

structure NoMatchInst where
  matchAttribTagID : Terminated 1  -- tag 1626
  matchAttribValue : Option (Terminated 1)  -- tag 1627

def NoMatchInst.parts (record : NoMatchInst) : List Part :=
  [Part.required [49, 54, 50, 54] record.matchAttribTagID,
   Part.optional [49, 54, 50, 55] record.matchAttribValue]

def NoMatchInst.tags : List (List (List UInt8)) :=
  [[[49, 54, 50, 54]], [[49, 54, 50, 55]]]

theorem NoMatchInst.shape (record : NoMatchInst) : record.parts.map Part.tags = NoMatchInst.tags := rfl

def NoMatchInst.decode (tokens : List Token) : Option NoMatchInst := do
  let matchAttribTagID ← readRequired [49, 54, 50, 54] tokens
  let matchAttribValue ← readOptional [49, 54, 50, 55] tokens
  pure { matchAttribTagID, matchAttribValue }

theorem NoMatchInst.decode_agrees (record : NoMatchInst) (tokens : List Token)
    (agrees : ∀ tags ∈ NoMatchInst.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoMatchInst.decode tokens = some record := by
  have distinct : NoMatchInst.tags.flatten.Nodup := by decide +kernel
  have matchAttribTagID := readRequired_part [49, 54, 50, 54] record.matchAttribTagID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have matchAttribValue := readOptional_part [49, 54, 50, 55] record.matchAttribValue tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [NoMatchInst.decode, matchAttribTagID, matchAttribValue, some_bind] <;> rfl

def NoMatchInst.members : List (List UInt8) := NoMatchInst.tags.flatten

def NoMatchInst.encode (entry : NoMatchInst) : List Token := encodeParts entry.parts

theorem NoMatchInst.decode_encode (entry : NoMatchInst) : NoMatchInst.decode entry.encode = some entry :=
  NoMatchInst.decode_agrees entry _ (fun _ _ => rfl)

theorem NoMatchInst.within (entry : NoMatchInst) : ∀ token ∈ entry.encode, token.tag ∈ NoMatchInst.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoMatchInst.shape] at this

theorem NoMatchInst.led (entry : NoMatchInst) : Lead [49, 54, 50, 54] entry.encode :=
  lead_parts [49, 54, 50, 54] entry.matchAttribTagID _ NoMatchInst.tags.tail rfl (by decide +kernel)

structure OrderCancelReplaceRequest where
  orderID : Option (Terminated 1)  -- tag 37
  noTargetPartyIDs : List NoTargetPartyIDs  -- tag 1461
  origClOrdID : Terminated 1  -- tag 41
  clOrdID : Terminated 1  -- tag 11
  execInst : Option (Terminated 1)  -- tag 18
  symbol : Terminated 1  -- tag 55
  side : Terminated 1  -- tag 54
  transactTime : Terminated 1  -- tag 60
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  noMatchInst : List NoMatchInst  -- tag 1625
  text : Option (Terminated 1)  -- tag 58

def OrderCancelReplaceRequest.parts (record : OrderCancelReplaceRequest) : List Part :=
  [Part.optional [51, 55] record.orderID,
   Part.group [49, 52, 54, 49] NoTargetPartyIDs.members NoTargetPartyIDs.encode NoTargetPartyIDs.within record.noTargetPartyIDs,
   Part.required [52, 49] record.origClOrdID,
   Part.required [49, 49] record.clOrdID,
   Part.optional [49, 56] record.execInst,
   Part.required [53, 53] record.symbol,
   Part.required [53, 52] record.side,
   Part.required [54, 48] record.transactTime,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.group [49, 54, 50, 53] NoMatchInst.members NoMatchInst.encode NoMatchInst.within record.noMatchInst,
   Part.optional [53, 56] record.text]

def OrderCancelReplaceRequest.tags : List (List (List UInt8)) :=
  [[[51, 55]], [49, 52, 54, 49] :: NoTargetPartyIDs.members, [[52, 49]], [[49, 49]], [[49, 56]], [[53, 53]], [[53, 52]], [[54, 48]], [[51, 56]], [[52, 48]], [[52, 52]], [49, 54, 50, 53] :: NoMatchInst.members, [[53, 56]]]

theorem OrderCancelReplaceRequest.shape (record : OrderCancelReplaceRequest) : record.parts.map Part.tags = OrderCancelReplaceRequest.tags := rfl

def OrderCancelReplaceRequest.decode (tokens : List Token) : Option OrderCancelReplaceRequest := do
  let orderID ← readOptional [51, 55] tokens
  let noTargetPartyIDs ← readGroup [49, 52, 54, 49] [49, 52, 54, 50] NoTargetPartyIDs.members NoTargetPartyIDs.decode tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let execInst ← readOptional [49, 56] tokens
  let symbol ← readRequired [53, 53] tokens
  let side ← readRequired [53, 52] tokens
  let transactTime ← readRequired [54, 48] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let noMatchInst ← readGroup [49, 54, 50, 53] [49, 54, 50, 54] NoMatchInst.members NoMatchInst.decode tokens
  let text ← readOptional [53, 56] tokens
  pure { orderID, noTargetPartyIDs, origClOrdID, clOrdID, execInst, symbol, side, transactTime, orderQty, ordType, price, noMatchInst, text }

theorem OrderCancelReplaceRequest.decode_agrees (record : OrderCancelReplaceRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelReplaceRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelReplaceRequest.decode tokens = some record := by
  have distinct : OrderCancelReplaceRequest.tags.flatten.Nodup := by decide +kernel
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have noTargetPartyIDs := readGroup_part [49, 52, 54, 49] [49, 52, 54, 50] NoTargetPartyIDs.members NoTargetPartyIDs.encode NoTargetPartyIDs.within NoTargetPartyIDs.decode NoTargetPartyIDs.decode_encode NoTargetPartyIDs.led record.noTargetPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have noMatchInst := readGroup_part [49, 54, 50, 53] [49, 54, 50, 54] NoMatchInst.members NoMatchInst.encode NoMatchInst.within NoMatchInst.decode NoMatchInst.decode_encode NoMatchInst.led record.noMatchInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  simp only [OrderCancelReplaceRequest.decode, orderID, noTargetPartyIDs, origClOrdID, clOrdID, execInst, symbol, side, transactTime, orderQty, ordType, price, noMatchInst, text, some_bind] <;> rfl

structure OrderCancelRequest where
  orderID : Option (Terminated 1)  -- tag 37
  clOrdID : Terminated 1  -- tag 11
  symbol : Terminated 1  -- tag 55
  side : Terminated 1  -- tag 54
  transactTime : Terminated 1  -- tag 60
  orderQty : Option (Terminated 1)  -- tag 38

def OrderCancelRequest.parts (record : OrderCancelRequest) : List Part :=
  [Part.optional [51, 55] record.orderID,
   Part.required [49, 49] record.clOrdID,
   Part.required [53, 53] record.symbol,
   Part.required [53, 52] record.side,
   Part.required [54, 48] record.transactTime,
   Part.optional [51, 56] record.orderQty]

def OrderCancelRequest.tags : List (List (List UInt8)) :=
  [[[51, 55]], [[49, 49]], [[53, 53]], [[53, 52]], [[54, 48]], [[51, 56]]]

theorem OrderCancelRequest.shape (record : OrderCancelRequest) : record.parts.map Part.tags = OrderCancelRequest.tags := rfl

def OrderCancelRequest.decode (tokens : List Token) : Option OrderCancelRequest := do
  let orderID ← readOptional [51, 55] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let symbol ← readRequired [53, 53] tokens
  let side ← readRequired [53, 52] tokens
  let transactTime ← readRequired [54, 48] tokens
  let orderQty ← readOptional [51, 56] tokens
  pure { orderID, clOrdID, symbol, side, transactTime, orderQty }

theorem OrderCancelRequest.decode_agrees (record : OrderCancelRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelRequest.decode tokens = some record := by
  have distinct : OrderCancelRequest.tags.flatten.Nodup := by decide +kernel
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have orderQty := readOptional_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  simp only [OrderCancelRequest.decode, orderID, clOrdID, symbol, side, transactTime, orderQty, some_bind] <;> rfl

structure OrderMassCancelRequest where
  clOrdID : Terminated 1  -- tag 11
  massCancelRequestType : Terminated 1  -- tag 530
  transactTime : Terminated 1  -- tag 60

def OrderMassCancelRequest.parts (record : OrderMassCancelRequest) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.required [53, 51, 48] record.massCancelRequestType,
   Part.required [54, 48] record.transactTime]

def OrderMassCancelRequest.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[53, 51, 48]], [[54, 48]]]

theorem OrderMassCancelRequest.shape (record : OrderMassCancelRequest) : record.parts.map Part.tags = OrderMassCancelRequest.tags := rfl

def OrderMassCancelRequest.decode (tokens : List Token) : Option OrderMassCancelRequest := do
  let clOrdID ← readRequired [49, 49] tokens
  let massCancelRequestType ← readRequired [53, 51, 48] tokens
  let transactTime ← readRequired [54, 48] tokens
  pure { clOrdID, massCancelRequestType, transactTime }

theorem OrderMassCancelRequest.decode_agrees (record : OrderMassCancelRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderMassCancelRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderMassCancelRequest.decode tokens = some record := by
  have distinct : OrderMassCancelRequest.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have massCancelRequestType := readRequired_part [53, 51, 48] record.massCancelRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [OrderMassCancelRequest.decode, clOrdID, massCancelRequestType, transactTime, some_bind] <;> rfl

structure OrderStatusRequest where
  orderID : Option (Terminated 1)  -- tag 37
  ordStatusReqID : Terminated 1  -- tag 790
  symbol : Option (Terminated 1)  -- tag 55
  side : Option (Terminated 1)  -- tag 54

def OrderStatusRequest.parts (record : OrderStatusRequest) : List Part :=
  [Part.optional [51, 55] record.orderID,
   Part.required [55, 57, 48] record.ordStatusReqID,
   Part.optional [53, 53] record.symbol,
   Part.optional [53, 52] record.side]

def OrderStatusRequest.tags : List (List (List UInt8)) :=
  [[[51, 55]], [[55, 57, 48]], [[53, 53]], [[53, 52]]]

theorem OrderStatusRequest.shape (record : OrderStatusRequest) : record.parts.map Part.tags = OrderStatusRequest.tags := rfl

def OrderStatusRequest.decode (tokens : List Token) : Option OrderStatusRequest := do
  let orderID ← readOptional [51, 55] tokens
  let ordStatusReqID ← readRequired [55, 57, 48] tokens
  let symbol ← readOptional [53, 53] tokens
  let side ← readOptional [53, 52] tokens
  pure { orderID, ordStatusReqID, symbol, side }

theorem OrderStatusRequest.decode_agrees (record : OrderStatusRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderStatusRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderStatusRequest.decode tokens = some record := by
  have distinct : OrderStatusRequest.tags.flatten.Nodup := by decide +kernel
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have ordStatusReqID := readRequired_part [55, 57, 48] record.ordStatusReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [OrderStatusRequest.decode, orderID, ordStatusReqID, symbol, side, some_bind] <;> rfl

structure SecurityListRequest where
  securityReqID : Terminated 1  -- tag 320
  securityListRequestType : Terminated 1  -- tag 559

def SecurityListRequest.parts (record : SecurityListRequest) : List Part :=
  [Part.required [51, 50, 48] record.securityReqID,
   Part.required [53, 53, 57] record.securityListRequestType]

def SecurityListRequest.tags : List (List (List UInt8)) :=
  [[[51, 50, 48]], [[53, 53, 57]]]

theorem SecurityListRequest.shape (record : SecurityListRequest) : record.parts.map Part.tags = SecurityListRequest.tags := rfl

def SecurityListRequest.decode (tokens : List Token) : Option SecurityListRequest := do
  let securityReqID ← readRequired [51, 50, 48] tokens
  let securityListRequestType ← readRequired [53, 53, 57] tokens
  pure { securityReqID, securityListRequestType }

theorem SecurityListRequest.decode_agrees (record : SecurityListRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ SecurityListRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    SecurityListRequest.decode tokens = some record := by
  have distinct : SecurityListRequest.tags.flatten.Nodup := by decide +kernel
  have securityReqID := readRequired_part [51, 50, 48] record.securityReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityListRequestType := readRequired_part [53, 53, 57] record.securityListRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [SecurityListRequest.decode, securityReqID, securityListRequestType, some_bind] <;> rfl

structure NoLegs where
  legSymbol : Terminated 1  -- tag 600
  legSecurityID : Option (Terminated 1)  -- tag 602
  legSecurityIDSource : Option (Terminated 1)  -- tag 603
  legSecurityType : Option (Terminated 1)  -- tag 609
  legMaturityMonthYear : Option (Terminated 1)  -- tag 610
  legStrikePrice : Option (Terminated 1)  -- tag 612
  legRatioQty : Option (Terminated 1)  -- tag 623
  legPutOrCall : Option (Terminated 1)  -- tag 1358
  legExerciseStyle : Option (Terminated 1)  -- tag 1420
  legLastPx : Option (Terminated 1)  -- tag 637
  legReportID : Option (Terminated 1)  -- tag 990
  legLastQty : Option (Terminated 1)  -- tag 1418

def NoLegs.parts (record : NoLegs) : List Part :=
  [Part.required [54, 48, 48] record.legSymbol,
   Part.optional [54, 48, 50] record.legSecurityID,
   Part.optional [54, 48, 51] record.legSecurityIDSource,
   Part.optional [54, 48, 57] record.legSecurityType,
   Part.optional [54, 49, 48] record.legMaturityMonthYear,
   Part.optional [54, 49, 50] record.legStrikePrice,
   Part.optional [54, 50, 51] record.legRatioQty,
   Part.optional [49, 51, 53, 56] record.legPutOrCall,
   Part.optional [49, 52, 50, 48] record.legExerciseStyle,
   Part.optional [54, 51, 55] record.legLastPx,
   Part.optional [57, 57, 48] record.legReportID,
   Part.optional [49, 52, 49, 56] record.legLastQty]

def NoLegs.tags : List (List (List UInt8)) :=
  [[[54, 48, 48]], [[54, 48, 50]], [[54, 48, 51]], [[54, 48, 57]], [[54, 49, 48]], [[54, 49, 50]], [[54, 50, 51]], [[49, 51, 53, 56]], [[49, 52, 50, 48]], [[54, 51, 55]], [[57, 57, 48]], [[49, 52, 49, 56]]]

theorem NoLegs.shape (record : NoLegs) : record.parts.map Part.tags = NoLegs.tags := rfl

def NoLegs.decode (tokens : List Token) : Option NoLegs := do
  let legSymbol ← readRequired [54, 48, 48] tokens
  let legSecurityID ← readOptional [54, 48, 50] tokens
  let legSecurityIDSource ← readOptional [54, 48, 51] tokens
  let legSecurityType ← readOptional [54, 48, 57] tokens
  let legMaturityMonthYear ← readOptional [54, 49, 48] tokens
  let legStrikePrice ← readOptional [54, 49, 50] tokens
  let legRatioQty ← readOptional [54, 50, 51] tokens
  let legPutOrCall ← readOptional [49, 51, 53, 56] tokens
  let legExerciseStyle ← readOptional [49, 52, 50, 48] tokens
  let legLastPx ← readOptional [54, 51, 55] tokens
  let legReportID ← readOptional [57, 57, 48] tokens
  let legLastQty ← readOptional [49, 52, 49, 56] tokens
  pure { legSymbol, legSecurityID, legSecurityIDSource, legSecurityType, legMaturityMonthYear, legStrikePrice, legRatioQty, legPutOrCall, legExerciseStyle, legLastPx, legReportID, legLastQty }

theorem NoLegs.decode_agrees (record : NoLegs) (tokens : List Token)
    (agrees : ∀ tags ∈ NoLegs.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoLegs.decode tokens = some record := by
  have distinct : NoLegs.tags.flatten.Nodup := by decide +kernel
  have legSymbol := readRequired_part [54, 48, 48] record.legSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have legSecurityID := readOptional_part [54, 48, 50] record.legSecurityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have legSecurityIDSource := readOptional_part [54, 48, 51] record.legSecurityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have legSecurityType := readOptional_part [54, 48, 57] record.legSecurityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have legMaturityMonthYear := readOptional_part [54, 49, 48] record.legMaturityMonthYear tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have legStrikePrice := readOptional_part [54, 49, 50] record.legStrikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have legRatioQty := readOptional_part [54, 50, 51] record.legRatioQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have legPutOrCall := readOptional_part [49, 51, 53, 56] record.legPutOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have legExerciseStyle := readOptional_part [49, 52, 50, 48] record.legExerciseStyle tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have legLastPx := readOptional_part [54, 51, 55] record.legLastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have legReportID := readOptional_part [57, 57, 48] record.legReportID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have legLastQty := readOptional_part [49, 52, 49, 56] record.legLastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  simp only [NoLegs.decode, legSymbol, legSecurityID, legSecurityIDSource, legSecurityType, legMaturityMonthYear, legStrikePrice, legRatioQty, legPutOrCall, legExerciseStyle, legLastPx, legReportID, legLastQty, some_bind] <;> rfl

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

structure SecurityDefinitionRequest where
  securityReqID : Terminated 1  -- tag 320
  securityRequestType : Terminated 1  -- tag 321
  symbol : Option (Terminated 1)  -- tag 55
  securityType : Option (Terminated 1)  -- tag 167
  noLegs : List NoLegs  -- tag 555

def SecurityDefinitionRequest.parts (record : SecurityDefinitionRequest) : List Part :=
  [Part.required [51, 50, 48] record.securityReqID,
   Part.required [51, 50, 49] record.securityRequestType,
   Part.optional [53, 53] record.symbol,
   Part.optional [49, 54, 55] record.securityType,
   Part.group [53, 53, 53] NoLegs.members NoLegs.encode NoLegs.within record.noLegs]

def SecurityDefinitionRequest.tags : List (List (List UInt8)) :=
  [[[51, 50, 48]], [[51, 50, 49]], [[53, 53]], [[49, 54, 55]], [53, 53, 53] :: NoLegs.members]

theorem SecurityDefinitionRequest.shape (record : SecurityDefinitionRequest) : record.parts.map Part.tags = SecurityDefinitionRequest.tags := rfl

def SecurityDefinitionRequest.decode (tokens : List Token) : Option SecurityDefinitionRequest := do
  let securityReqID ← readRequired [51, 50, 48] tokens
  let securityRequestType ← readRequired [51, 50, 49] tokens
  let symbol ← readOptional [53, 53] tokens
  let securityType ← readOptional [49, 54, 55] tokens
  let noLegs ← readGroup [53, 53, 53] [54, 48, 48] NoLegs.members NoLegs.decode tokens
  pure { securityReqID, securityRequestType, symbol, securityType, noLegs }

theorem SecurityDefinitionRequest.decode_agrees (record : SecurityDefinitionRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ SecurityDefinitionRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    SecurityDefinitionRequest.decode tokens = some record := by
  have distinct : SecurityDefinitionRequest.tags.flatten.Nodup := by decide +kernel
  have securityReqID := readRequired_part [51, 50, 48] record.securityReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityRequestType := readRequired_part [51, 50, 49] record.securityRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have securityType := readOptional_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have noLegs := readGroup_part [53, 53, 53] [54, 48, 48] NoLegs.members NoLegs.encode NoLegs.within NoLegs.decode NoLegs.decode_encode NoLegs.led record.noLegs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [SecurityDefinitionRequest.decode, securityReqID, securityRequestType, symbol, securityType, noLegs, some_bind] <;> rfl

structure NoSides where
  side : Terminated 1  -- tag 54
  noPartyIDs : List NoPartyIDs  -- tag 453
  account : Option (Terminated 1)  -- tag 1
  text : Option (Terminated 1)  -- tag 58
  sideTradeReportID : Option (Terminated 1)  -- tag 1005
  aggressorIndicator : Option (Terminated 1)  -- tag 1057
  exchangeSpecialInstructions : Option (Terminated 1)  -- tag 1139
  tradingSessionID : Option (Terminated 1)  -- tag 336
  tradingSessionSubID : Option (Terminated 1)  -- tag 625
  tradeID : Option (Terminated 1)  -- tag 1003

def NoSides.parts (record : NoSides) : List Part :=
  [Part.required [53, 52] record.side,
   Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.optional [49] record.account,
   Part.optional [53, 56] record.text,
   Part.optional [49, 48, 48, 53] record.sideTradeReportID,
   Part.optional [49, 48, 53, 55] record.aggressorIndicator,
   Part.optional [49, 49, 51, 57] record.exchangeSpecialInstructions,
   Part.optional [51, 51, 54] record.tradingSessionID,
   Part.optional [54, 50, 53] record.tradingSessionSubID,
   Part.optional [49, 48, 48, 51] record.tradeID]

def NoSides.tags : List (List (List UInt8)) :=
  [[[53, 52]], [52, 53, 51] :: NoPartyIDs.members, [[49]], [[53, 56]], [[49, 48, 48, 53]], [[49, 48, 53, 55]], [[49, 49, 51, 57]], [[51, 51, 54]], [[54, 50, 53]], [[49, 48, 48, 51]]]

theorem NoSides.shape (record : NoSides) : record.parts.map Part.tags = NoSides.tags := rfl

def NoSides.decode (tokens : List Token) : Option NoSides := do
  let side ← readRequired [53, 52] tokens
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let account ← readOptional [49] tokens
  let text ← readOptional [53, 56] tokens
  let sideTradeReportID ← readOptional [49, 48, 48, 53] tokens
  let aggressorIndicator ← readOptional [49, 48, 53, 55] tokens
  let exchangeSpecialInstructions ← readOptional [49, 49, 51, 57] tokens
  let tradingSessionID ← readOptional [51, 51, 54] tokens
  let tradingSessionSubID ← readOptional [54, 50, 53] tokens
  let tradeID ← readOptional [49, 48, 48, 51] tokens
  pure { side, noPartyIDs, account, text, sideTradeReportID, aggressorIndicator, exchangeSpecialInstructions, tradingSessionID, tradingSessionSubID, tradeID }

theorem NoSides.decode_agrees (record : NoSides) (tokens : List Token)
    (agrees : ∀ tags ∈ NoSides.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoSides.decode tokens = some record := by
  have distinct : NoSides.tags.flatten.Nodup := by decide +kernel
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have sideTradeReportID := readOptional_part [49, 48, 48, 53] record.sideTradeReportID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have aggressorIndicator := readOptional_part [49, 48, 53, 55] record.aggressorIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have exchangeSpecialInstructions := readOptional_part [49, 49, 51, 57] record.exchangeSpecialInstructions tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have tradingSessionID := readOptional_part [51, 51, 54] record.tradingSessionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have tradingSessionSubID := readOptional_part [54, 50, 53] record.tradingSessionSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have tradeID := readOptional_part [49, 48, 48, 51] record.tradeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  simp only [NoSides.decode, side, noPartyIDs, account, text, sideTradeReportID, aggressorIndicator, exchangeSpecialInstructions, tradingSessionID, tradingSessionSubID, tradeID, some_bind] <;> rfl

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

structure TradeCaptureReport where
  tradeReportID : Terminated 1  -- tag 571
  execType : Option (Terminated 1)  -- tag 150
  tradeReportTransType : Option (Terminated 1)  -- tag 487
  tradeReportType : Option (Terminated 1)  -- tag 856
  trdType : Option (Terminated 1)  -- tag 828
  priceType : Option (Terminated 1)  -- tag 423
  symbol : Terminated 1  -- tag 55
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22
  securityType : Option (Terminated 1)  -- tag 167
  maturityMonthYear : Option (Terminated 1)  -- tag 200
  lastQty : Terminated 1  -- tag 32
  lastPx : Terminated 1  -- tag 31
  qtyType : Option (Terminated 1)  -- tag 854
  tradeDate : Option (Terminated 1)  -- tag 75
  clearingBusinessDate : Option (Terminated 1)  -- tag 715
  multiLegReportingType : Option (Terminated 1)  -- tag 442
  noLegs : List NoLegs  -- tag 555
  transactTime : Terminated 1  -- tag 60
  noSides : List NoSides  -- tag 552
  currency : Option (Terminated 1)  -- tag 15

def TradeCaptureReport.parts (record : TradeCaptureReport) : List Part :=
  [Part.required [53, 55, 49] record.tradeReportID,
   Part.optional [49, 53, 48] record.execType,
   Part.optional [52, 56, 55] record.tradeReportTransType,
   Part.optional [56, 53, 54] record.tradeReportType,
   Part.optional [56, 50, 56] record.trdType,
   Part.optional [52, 50, 51] record.priceType,
   Part.required [53, 53] record.symbol,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource,
   Part.optional [49, 54, 55] record.securityType,
   Part.optional [50, 48, 48] record.maturityMonthYear,
   Part.required [51, 50] record.lastQty,
   Part.required [51, 49] record.lastPx,
   Part.optional [56, 53, 52] record.qtyType,
   Part.optional [55, 53] record.tradeDate,
   Part.optional [55, 49, 53] record.clearingBusinessDate,
   Part.optional [52, 52, 50] record.multiLegReportingType,
   Part.group [53, 53, 53] NoLegs.members NoLegs.encode NoLegs.within record.noLegs,
   Part.required [54, 48] record.transactTime,
   Part.group [53, 53, 50] NoSides.members NoSides.encode NoSides.within record.noSides,
   Part.optional [49, 53] record.currency]

def TradeCaptureReport.tags : List (List (List UInt8)) :=
  [[[53, 55, 49]], [[49, 53, 48]], [[52, 56, 55]], [[56, 53, 54]], [[56, 50, 56]], [[52, 50, 51]], [[53, 53]], [[52, 56]], [[50, 50]], [[49, 54, 55]], [[50, 48, 48]], [[51, 50]], [[51, 49]], [[56, 53, 52]], [[55, 53]], [[55, 49, 53]], [[52, 52, 50]], [53, 53, 53] :: NoLegs.members, [[54, 48]], [53, 53, 50] :: NoSides.members, [[49, 53]]]

theorem TradeCaptureReport.shape (record : TradeCaptureReport) : record.parts.map Part.tags = TradeCaptureReport.tags := rfl

def TradeCaptureReport.decode (tokens : List Token) : Option TradeCaptureReport := do
  let tradeReportID ← readRequired [53, 55, 49] tokens
  let execType ← readOptional [49, 53, 48] tokens
  let tradeReportTransType ← readOptional [52, 56, 55] tokens
  let tradeReportType ← readOptional [56, 53, 54] tokens
  let trdType ← readOptional [56, 50, 56] tokens
  let priceType ← readOptional [52, 50, 51] tokens
  let symbol ← readRequired [53, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let securityType ← readOptional [49, 54, 55] tokens
  let maturityMonthYear ← readOptional [50, 48, 48] tokens
  let lastQty ← readRequired [51, 50] tokens
  let lastPx ← readRequired [51, 49] tokens
  let qtyType ← readOptional [56, 53, 52] tokens
  let tradeDate ← readOptional [55, 53] tokens
  let clearingBusinessDate ← readOptional [55, 49, 53] tokens
  let multiLegReportingType ← readOptional [52, 52, 50] tokens
  let noLegs ← readGroup [53, 53, 53] [54, 48, 48] NoLegs.members NoLegs.decode tokens
  let transactTime ← readRequired [54, 48] tokens
  let noSides ← readGroup [53, 53, 50] [53, 52] NoSides.members NoSides.decode tokens
  let currency ← readOptional [49, 53] tokens
  pure { tradeReportID, execType, tradeReportTransType, tradeReportType, trdType, priceType, symbol, securityID, securityIDSource, securityType, maturityMonthYear, lastQty, lastPx, qtyType, tradeDate, clearingBusinessDate, multiLegReportingType, noLegs, transactTime, noSides, currency }

theorem TradeCaptureReport.decode_agrees (record : TradeCaptureReport) (tokens : List Token)
    (agrees : ∀ tags ∈ TradeCaptureReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TradeCaptureReport.decode tokens = some record := by
  have distinct : TradeCaptureReport.tags.flatten.Nodup := by decide +kernel
  have tradeReportID := readRequired_part [53, 55, 49] record.tradeReportID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have execType := readOptional_part [49, 53, 48] record.execType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have tradeReportTransType := readOptional_part [52, 56, 55] record.tradeReportTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have tradeReportType := readOptional_part [56, 53, 54] record.tradeReportType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have trdType := readOptional_part [56, 50, 56] record.trdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have priceType := readOptional_part [52, 50, 51] record.priceType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have securityType := readOptional_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have maturityMonthYear := readOptional_part [50, 48, 48] record.maturityMonthYear tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have lastQty := readRequired_part [51, 50] record.lastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have lastPx := readRequired_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have qtyType := readOptional_part [56, 53, 52] record.qtyType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have tradeDate := readOptional_part [55, 53] record.tradeDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have clearingBusinessDate := readOptional_part [55, 49, 53] record.clearingBusinessDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have multiLegReportingType := readOptional_part [52, 52, 50] record.multiLegReportingType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have noLegs := readGroup_part [53, 53, 53] [54, 48, 48] NoLegs.members NoLegs.encode NoLegs.within NoLegs.decode NoLegs.decode_encode NoLegs.led record.noLegs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have noSides := readGroup_part [53, 53, 50] [53, 52] NoSides.members NoSides.encode NoSides.within NoSides.decode NoSides.decode_encode NoSides.led record.noSides tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have currency := readOptional_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  simp only [TradeCaptureReport.decode, tradeReportID, execType, tradeReportTransType, tradeReportType, trdType, priceType, symbol, securityID, securityIDSource, securityType, maturityMonthYear, lastQty, lastPx, qtyType, tradeDate, clearingBusinessDate, multiLegReportingType, noLegs, transactTime, noSides, currency, some_bind] <;> rfl

structure TradeCaptureReportRequest where
  tradeRequestID : Terminated 1  -- tag 568
  tradeRequestType : Terminated 1  -- tag 569
  subscriptionRequestType : Option (Terminated 1)  -- tag 263
  tradeID : Option (Terminated 1)  -- tag 1003

def TradeCaptureReportRequest.parts (record : TradeCaptureReportRequest) : List Part :=
  [Part.required [53, 54, 56] record.tradeRequestID,
   Part.required [53, 54, 57] record.tradeRequestType,
   Part.optional [50, 54, 51] record.subscriptionRequestType,
   Part.optional [49, 48, 48, 51] record.tradeID]

def TradeCaptureReportRequest.tags : List (List (List UInt8)) :=
  [[[53, 54, 56]], [[53, 54, 57]], [[50, 54, 51]], [[49, 48, 48, 51]]]

theorem TradeCaptureReportRequest.shape (record : TradeCaptureReportRequest) : record.parts.map Part.tags = TradeCaptureReportRequest.tags := rfl

def TradeCaptureReportRequest.decode (tokens : List Token) : Option TradeCaptureReportRequest := do
  let tradeRequestID ← readRequired [53, 54, 56] tokens
  let tradeRequestType ← readRequired [53, 54, 57] tokens
  let subscriptionRequestType ← readOptional [50, 54, 51] tokens
  let tradeID ← readOptional [49, 48, 48, 51] tokens
  pure { tradeRequestID, tradeRequestType, subscriptionRequestType, tradeID }

theorem TradeCaptureReportRequest.decode_agrees (record : TradeCaptureReportRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ TradeCaptureReportRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TradeCaptureReportRequest.decode tokens = some record := by
  have distinct : TradeCaptureReportRequest.tags.flatten.Nodup := by decide +kernel
  have tradeRequestID := readRequired_part [53, 54, 56] record.tradeRequestID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have tradeRequestType := readRequired_part [53, 54, 57] record.tradeRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have subscriptionRequestType := readOptional_part [50, 54, 51] record.subscriptionRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have tradeID := readOptional_part [49, 48, 48, 51] record.tradeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [TradeCaptureReportRequest.decode, tradeRequestID, tradeRequestType, subscriptionRequestType, tradeID, some_bind] <;> rfl

structure PartyDetailsListRequest where
  partyDetailsListRequestID : Terminated 1  -- tag 1505
  partyListResponseType : Option (Terminated 1)  -- tag 1507

def PartyDetailsListRequest.parts (record : PartyDetailsListRequest) : List Part :=
  [Part.required [49, 53, 48, 53] record.partyDetailsListRequestID,
   Part.optional [49, 53, 48, 55] record.partyListResponseType]

def PartyDetailsListRequest.tags : List (List (List UInt8)) :=
  [[[49, 53, 48, 53]], [[49, 53, 48, 55]]]

theorem PartyDetailsListRequest.shape (record : PartyDetailsListRequest) : record.parts.map Part.tags = PartyDetailsListRequest.tags := rfl

def PartyDetailsListRequest.decode (tokens : List Token) : Option PartyDetailsListRequest := do
  let partyDetailsListRequestID ← readRequired [49, 53, 48, 53] tokens
  let partyListResponseType ← readOptional [49, 53, 48, 55] tokens
  pure { partyDetailsListRequestID, partyListResponseType }

theorem PartyDetailsListRequest.decode_agrees (record : PartyDetailsListRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ PartyDetailsListRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    PartyDetailsListRequest.decode tokens = some record := by
  have distinct : PartyDetailsListRequest.tags.flatten.Nodup := by decide +kernel
  have partyDetailsListRequestID := readRequired_part [49, 53, 48, 53] record.partyDetailsListRequestID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have partyListResponseType := readOptional_part [49, 53, 48, 55] record.partyListResponseType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [PartyDetailsListRequest.decode, partyDetailsListRequestID, partyListResponseType, some_bind] <;> rfl

structure NoMDEntryTypes where
  mDEntryType : Terminated 1  -- tag 269

def NoMDEntryTypes.parts (record : NoMDEntryTypes) : List Part :=
  [Part.required [50, 54, 57] record.mDEntryType]

def NoMDEntryTypes.tags : List (List (List UInt8)) :=
  [[[50, 54, 57]]]

theorem NoMDEntryTypes.shape (record : NoMDEntryTypes) : record.parts.map Part.tags = NoMDEntryTypes.tags := rfl

def NoMDEntryTypes.decode (tokens : List Token) : Option NoMDEntryTypes := do
  let mDEntryType ← readRequired [50, 54, 57] tokens
  pure { mDEntryType }

theorem NoMDEntryTypes.decode_agrees (record : NoMDEntryTypes) (tokens : List Token)
    (agrees : ∀ tags ∈ NoMDEntryTypes.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoMDEntryTypes.decode tokens = some record := by
  have distinct : NoMDEntryTypes.tags.flatten.Nodup := by decide +kernel
  have mDEntryType := readRequired_part [50, 54, 57] record.mDEntryType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [NoMDEntryTypes.decode, mDEntryType, some_bind] <;> rfl

def NoMDEntryTypes.members : List (List UInt8) := NoMDEntryTypes.tags.flatten

def NoMDEntryTypes.encode (entry : NoMDEntryTypes) : List Token := encodeParts entry.parts

theorem NoMDEntryTypes.decode_encode (entry : NoMDEntryTypes) : NoMDEntryTypes.decode entry.encode = some entry :=
  NoMDEntryTypes.decode_agrees entry _ (fun _ _ => rfl)

theorem NoMDEntryTypes.within (entry : NoMDEntryTypes) : ∀ token ∈ entry.encode, token.tag ∈ NoMDEntryTypes.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoMDEntryTypes.shape] at this

theorem NoMDEntryTypes.led (entry : NoMDEntryTypes) : Lead [50, 54, 57] entry.encode :=
  lead_parts [50, 54, 57] entry.mDEntryType _ NoMDEntryTypes.tags.tail rfl (by decide +kernel)

structure NoRelatedSym where
  symbol : Terminated 1  -- tag 55
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22

def NoRelatedSym.parts (record : NoRelatedSym) : List Part :=
  [Part.required [53, 53] record.symbol,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource]

def NoRelatedSym.tags : List (List (List UInt8)) :=
  [[[53, 53]], [[52, 56]], [[50, 50]]]

theorem NoRelatedSym.shape (record : NoRelatedSym) : record.parts.map Part.tags = NoRelatedSym.tags := rfl

def NoRelatedSym.decode (tokens : List Token) : Option NoRelatedSym := do
  let symbol ← readRequired [53, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  pure { symbol, securityID, securityIDSource }

theorem NoRelatedSym.decode_agrees (record : NoRelatedSym) (tokens : List Token)
    (agrees : ∀ tags ∈ NoRelatedSym.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoRelatedSym.decode tokens = some record := by
  have distinct : NoRelatedSym.tags.flatten.Nodup := by decide +kernel
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [NoRelatedSym.decode, symbol, securityID, securityIDSource, some_bind] <;> rfl

def NoRelatedSym.members : List (List UInt8) := NoRelatedSym.tags.flatten

def NoRelatedSym.encode (entry : NoRelatedSym) : List Token := encodeParts entry.parts

theorem NoRelatedSym.decode_encode (entry : NoRelatedSym) : NoRelatedSym.decode entry.encode = some entry :=
  NoRelatedSym.decode_agrees entry _ (fun _ _ => rfl)

theorem NoRelatedSym.within (entry : NoRelatedSym) : ∀ token ∈ entry.encode, token.tag ∈ NoRelatedSym.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoRelatedSym.shape] at this

theorem NoRelatedSym.led (entry : NoRelatedSym) : Lead [53, 53] entry.encode :=
  lead_parts [53, 53] entry.symbol _ NoRelatedSym.tags.tail rfl (by decide +kernel)

structure MarketDataRequest where
  mDReqID : Terminated 1  -- tag 262
  subscriptionRequestType : Terminated 1  -- tag 263
  marketDepth : Terminated 1  -- tag 264
  noMDEntryTypes : List NoMDEntryTypes  -- tag 267
  noRelatedSym : List NoRelatedSym  -- tag 146

def MarketDataRequest.parts (record : MarketDataRequest) : List Part :=
  [Part.required [50, 54, 50] record.mDReqID,
   Part.required [50, 54, 51] record.subscriptionRequestType,
   Part.required [50, 54, 52] record.marketDepth,
   Part.group [50, 54, 55] NoMDEntryTypes.members NoMDEntryTypes.encode NoMDEntryTypes.within record.noMDEntryTypes,
   Part.group [49, 52, 54] NoRelatedSym.members NoRelatedSym.encode NoRelatedSym.within record.noRelatedSym]

def MarketDataRequest.tags : List (List (List UInt8)) :=
  [[[50, 54, 50]], [[50, 54, 51]], [[50, 54, 52]], [50, 54, 55] :: NoMDEntryTypes.members, [49, 52, 54] :: NoRelatedSym.members]

theorem MarketDataRequest.shape (record : MarketDataRequest) : record.parts.map Part.tags = MarketDataRequest.tags := rfl

def MarketDataRequest.decode (tokens : List Token) : Option MarketDataRequest := do
  let mDReqID ← readRequired [50, 54, 50] tokens
  let subscriptionRequestType ← readRequired [50, 54, 51] tokens
  let marketDepth ← readRequired [50, 54, 52] tokens
  let noMDEntryTypes ← readGroup [50, 54, 55] [50, 54, 57] NoMDEntryTypes.members NoMDEntryTypes.decode tokens
  let noRelatedSym ← readGroup [49, 52, 54] [53, 53] NoRelatedSym.members NoRelatedSym.decode tokens
  pure { mDReqID, subscriptionRequestType, marketDepth, noMDEntryTypes, noRelatedSym }

theorem MarketDataRequest.decode_agrees (record : MarketDataRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ MarketDataRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    MarketDataRequest.decode tokens = some record := by
  have distinct : MarketDataRequest.tags.flatten.Nodup := by decide +kernel
  have mDReqID := readRequired_part [50, 54, 50] record.mDReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have subscriptionRequestType := readRequired_part [50, 54, 51] record.subscriptionRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have marketDepth := readRequired_part [50, 54, 52] record.marketDepth tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have noMDEntryTypes := readGroup_part [50, 54, 55] [50, 54, 57] NoMDEntryTypes.members NoMDEntryTypes.encode NoMDEntryTypes.within NoMDEntryTypes.decode NoMDEntryTypes.decode_encode NoMDEntryTypes.led record.noMDEntryTypes tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have noRelatedSym := readGroup_part [49, 52, 54] [53, 53] NoRelatedSym.members NoRelatedSym.encode NoRelatedSym.within NoRelatedSym.decode NoRelatedSym.decode_encode NoRelatedSym.led record.noRelatedSym tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [MarketDataRequest.decode, mDReqID, subscriptionRequestType, marketDepth, noMDEntryTypes, noRelatedSym, some_bind] <;> rfl

inductive Message where
  | logon (header : Header) (r0 : Logon)
  | logout (header : Header) (r0 : Logout)
  | heartbeat (header : Header) (r0 : Heartbeat)
  | testRequest (header : Header) (r0 : TestRequest)
  | reject (header : Header) (r0 : Reject)
  | newOrderSingle (header : Header) (r0 : NewOrderSingle)
  | orderCancelReplaceRequest (header : Header) (r0 : OrderCancelReplaceRequest)
  | orderCancelRequest (header : Header) (r0 : OrderCancelRequest)
  | orderMassCancelRequest (header : Header) (r0 : OrderMassCancelRequest)
  | orderStatusRequest (header : Header) (r0 : OrderStatusRequest)
  | securityListRequest (header : Header) (r0 : SecurityListRequest)
  | securityDefinitionRequest (header : Header) (r0 : SecurityDefinitionRequest)
  | tradeCaptureReport (header : Header) (r0 : TradeCaptureReport)
  | tradeCaptureReportRequest (header : Header) (r0 : TradeCaptureReportRequest)
  | partyDetailsListRequest (header : Header) (r0 : PartyDetailsListRequest)
  | marketDataRequest (header : Header) (r0 : MarketDataRequest)

def Message.tokens : Message → List Token
  | .logon header r0 => ⟨[51, 53], ⟨[65], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logout header r0 => ⟨[51, 53], ⟨[53], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .heartbeat header r0 => ⟨[51, 53], ⟨[48], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .testRequest header r0 => ⟨[51, 53], ⟨[49], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .reject header r0 => ⟨[51, 53], ⟨[51], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .newOrderSingle header r0 => ⟨[51, 53], ⟨[68], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelReplaceRequest header r0 => ⟨[51, 53], ⟨[71], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelRequest header r0 => ⟨[51, 53], ⟨[70], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderMassCancelRequest header r0 => ⟨[51, 53], ⟨[113], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderStatusRequest header r0 => ⟨[51, 53], ⟨[72], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .securityListRequest header r0 => ⟨[51, 53], ⟨[120], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .securityDefinitionRequest header r0 => ⟨[51, 53], ⟨[99], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .tradeCaptureReport header r0 => ⟨[51, 53], ⟨[65, 69], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .tradeCaptureReportRequest header r0 => ⟨[51, 53], ⟨[65, 68], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .partyDetailsListRequest header r0 => ⟨[51, 53], ⟨[67, 70], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .marketDataRequest header r0 => ⟨[51, 53], ⟨[86], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)

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
      else if token.value.val = [68] then
        if known (Header.tags ++ NewOrderSingle.tags) rest then do
          let header ← Header.decode rest
          let r0 ← NewOrderSingle.decode rest
          pure (.newOrderSingle header r0)
        else none
      else if token.value.val = [71] then
        if known (Header.tags ++ OrderCancelReplaceRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderCancelReplaceRequest.decode rest
          pure (.orderCancelReplaceRequest header r0)
        else none
      else if token.value.val = [70] then
        if known (Header.tags ++ OrderCancelRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderCancelRequest.decode rest
          pure (.orderCancelRequest header r0)
        else none
      else if token.value.val = [113] then
        if known (Header.tags ++ OrderMassCancelRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderMassCancelRequest.decode rest
          pure (.orderMassCancelRequest header r0)
        else none
      else if token.value.val = [72] then
        if known (Header.tags ++ OrderStatusRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderStatusRequest.decode rest
          pure (.orderStatusRequest header r0)
        else none
      else if token.value.val = [120] then
        if known (Header.tags ++ SecurityListRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← SecurityListRequest.decode rest
          pure (.securityListRequest header r0)
        else none
      else if token.value.val = [99] then
        if known (Header.tags ++ SecurityDefinitionRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← SecurityDefinitionRequest.decode rest
          pure (.securityDefinitionRequest header r0)
        else none
      else if token.value.val = [65, 69] then
        if known (Header.tags ++ TradeCaptureReport.tags) rest then do
          let header ← Header.decode rest
          let r0 ← TradeCaptureReport.decode rest
          pure (.tradeCaptureReport header r0)
        else none
      else if token.value.val = [65, 68] then
        if known (Header.tags ++ TradeCaptureReportRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← TradeCaptureReportRequest.decode rest
          pure (.tradeCaptureReportRequest header r0)
        else none
      else if token.value.val = [67, 70] then
        if known (Header.tags ++ PartyDetailsListRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← PartyDetailsListRequest.decode rest
          pure (.partyDetailsListRequest header r0)
        else none
      else if token.value.val = [86] then
        if known (Header.tags ++ MarketDataRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← MarketDataRequest.decode rest
          pure (.marketDataRequest header r0)
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

theorem Message.decode_newOrderSingle (header : Header) (r0 : NewOrderSingle) :
    Message.decode (Message.tokens (.newOrderSingle header r0)) = some (.newOrderSingle header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (NewOrderSingle.tags) rfl rfl (by decide +kernel))
  have c1 := NewOrderSingle.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (NewOrderSingle.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ NewOrderSingle.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_orderCancelReplaceRequest (header : Header) (r0 : OrderCancelReplaceRequest) :
    Message.decode (Message.tokens (.orderCancelReplaceRequest header r0)) = some (.orderCancelReplaceRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelReplaceRequest.tags) rfl rfl (by decide +kernel))
  have c1 := OrderCancelReplaceRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelReplaceRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderCancelReplaceRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_orderCancelRequest (header : Header) (r0 : OrderCancelRequest) :
    Message.decode (Message.tokens (.orderCancelRequest header r0)) = some (.orderCancelRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelRequest.tags) rfl rfl (by decide +kernel))
  have c1 := OrderCancelRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderCancelRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_orderMassCancelRequest (header : Header) (r0 : OrderMassCancelRequest) :
    Message.decode (Message.tokens (.orderMassCancelRequest header r0)) = some (.orderMassCancelRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderMassCancelRequest.tags) rfl rfl (by decide +kernel))
  have c1 := OrderMassCancelRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderMassCancelRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderMassCancelRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_orderStatusRequest (header : Header) (r0 : OrderStatusRequest) :
    Message.decode (Message.tokens (.orderStatusRequest header r0)) = some (.orderStatusRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderStatusRequest.tags) rfl rfl (by decide +kernel))
  have c1 := OrderStatusRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderStatusRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderStatusRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_securityListRequest (header : Header) (r0 : SecurityListRequest) :
    Message.decode (Message.tokens (.securityListRequest header r0)) = some (.securityListRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (SecurityListRequest.tags) rfl rfl (by decide +kernel))
  have c1 := SecurityListRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (SecurityListRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ SecurityListRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_securityDefinitionRequest (header : Header) (r0 : SecurityDefinitionRequest) :
    Message.decode (Message.tokens (.securityDefinitionRequest header r0)) = some (.securityDefinitionRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (SecurityDefinitionRequest.tags) rfl rfl (by decide +kernel))
  have c1 := SecurityDefinitionRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (SecurityDefinitionRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ SecurityDefinitionRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tradeCaptureReport (header : Header) (r0 : TradeCaptureReport) :
    Message.decode (Message.tokens (.tradeCaptureReport header r0)) = some (.tradeCaptureReport header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (TradeCaptureReport.tags) rfl rfl (by decide +kernel))
  have c1 := TradeCaptureReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (TradeCaptureReport.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ TradeCaptureReport.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tradeCaptureReportRequest (header : Header) (r0 : TradeCaptureReportRequest) :
    Message.decode (Message.tokens (.tradeCaptureReportRequest header r0)) = some (.tradeCaptureReportRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (TradeCaptureReportRequest.tags) rfl rfl (by decide +kernel))
  have c1 := TradeCaptureReportRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (TradeCaptureReportRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ TradeCaptureReportRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_partyDetailsListRequest (header : Header) (r0 : PartyDetailsListRequest) :
    Message.decode (Message.tokens (.partyDetailsListRequest header r0)) = some (.partyDetailsListRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (PartyDetailsListRequest.tags) rfl rfl (by decide +kernel))
  have c1 := PartyDetailsListRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (PartyDetailsListRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ PartyDetailsListRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_marketDataRequest (header : Header) (r0 : MarketDataRequest) :
    Message.decode (Message.tokens (.marketDataRequest header r0)) = some (.marketDataRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (MarketDataRequest.tags) rfl rfl (by decide +kernel))
  have c1 := MarketDataRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (MarketDataRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ MarketDataRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | logon header r0 => exact Message.decode_logon header r0
  | logout header r0 => exact Message.decode_logout header r0
  | heartbeat header r0 => exact Message.decode_heartbeat header r0
  | testRequest header r0 => exact Message.decode_testRequest header r0
  | reject header r0 => exact Message.decode_reject header r0
  | newOrderSingle header r0 => exact Message.decode_newOrderSingle header r0
  | orderCancelReplaceRequest header r0 => exact Message.decode_orderCancelReplaceRequest header r0
  | orderCancelRequest header r0 => exact Message.decode_orderCancelRequest header r0
  | orderMassCancelRequest header r0 => exact Message.decode_orderMassCancelRequest header r0
  | orderStatusRequest header r0 => exact Message.decode_orderStatusRequest header r0
  | securityListRequest header r0 => exact Message.decode_securityListRequest header r0
  | securityDefinitionRequest header r0 => exact Message.decode_securityDefinitionRequest header r0
  | tradeCaptureReport header r0 => exact Message.decode_tradeCaptureReport header r0
  | tradeCaptureReportRequest header r0 => exact Message.decode_tradeCaptureReportRequest header r0
  | partyDetailsListRequest header r0 => exact Message.decode_partyDetailsListRequest header r0
  | marketDataRequest header r0 => exact Message.decode_marketDataRequest header r0

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

theorem Message.decodeBytes_newOrderSingle (header : Header) (r0 : NewOrderSingle) :
    Message.decodeBytes (Message.encode (.newOrderSingle header r0)) = some (.newOrderSingle header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[68], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ NewOrderSingle.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_newOrderSingle header r0

theorem Message.decodeBytes_orderCancelReplaceRequest (header : Header) (r0 : OrderCancelReplaceRequest) :
    Message.decodeBytes (Message.encode (.orderCancelReplaceRequest header r0)) = some (.orderCancelReplaceRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[71], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ OrderCancelReplaceRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderCancelReplaceRequest header r0

theorem Message.decodeBytes_orderCancelRequest (header : Header) (r0 : OrderCancelRequest) :
    Message.decodeBytes (Message.encode (.orderCancelRequest header r0)) = some (.orderCancelRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[70], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ OrderCancelRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderCancelRequest header r0

theorem Message.decodeBytes_orderMassCancelRequest (header : Header) (r0 : OrderMassCancelRequest) :
    Message.decodeBytes (Message.encode (.orderMassCancelRequest header r0)) = some (.orderMassCancelRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[113], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ OrderMassCancelRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderMassCancelRequest header r0

theorem Message.decodeBytes_orderStatusRequest (header : Header) (r0 : OrderStatusRequest) :
    Message.decodeBytes (Message.encode (.orderStatusRequest header r0)) = some (.orderStatusRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[72], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ OrderStatusRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderStatusRequest header r0

theorem Message.decodeBytes_securityListRequest (header : Header) (r0 : SecurityListRequest) :
    Message.decodeBytes (Message.encode (.securityListRequest header r0)) = some (.securityListRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[120], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ SecurityListRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_securityListRequest header r0

theorem Message.decodeBytes_securityDefinitionRequest (header : Header) (r0 : SecurityDefinitionRequest) :
    Message.decodeBytes (Message.encode (.securityDefinitionRequest header r0)) = some (.securityDefinitionRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[99], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ SecurityDefinitionRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_securityDefinitionRequest header r0

theorem Message.decodeBytes_tradeCaptureReport (header : Header) (r0 : TradeCaptureReport) :
    Message.decodeBytes (Message.encode (.tradeCaptureReport header r0)) = some (.tradeCaptureReport header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[65, 69], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ TradeCaptureReport.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_tradeCaptureReport header r0

theorem Message.decodeBytes_tradeCaptureReportRequest (header : Header) (r0 : TradeCaptureReportRequest) :
    Message.decodeBytes (Message.encode (.tradeCaptureReportRequest header r0)) = some (.tradeCaptureReportRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[65, 68], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ TradeCaptureReportRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_tradeCaptureReportRequest header r0

theorem Message.decodeBytes_partyDetailsListRequest (header : Header) (r0 : PartyDetailsListRequest) :
    Message.decodeBytes (Message.encode (.partyDetailsListRequest header r0)) = some (.partyDetailsListRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[67, 70], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ PartyDetailsListRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_partyDetailsListRequest header r0

theorem Message.decodeBytes_marketDataRequest (header : Header) (r0 : MarketDataRequest) :
    Message.decodeBytes (Message.encode (.marketDataRequest header r0)) = some (.marketDataRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[86], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ MarketDataRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_marketDataRequest header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | logon header r0 => exact Message.decodeBytes_logon header r0
  | logout header r0 => exact Message.decodeBytes_logout header r0
  | heartbeat header r0 => exact Message.decodeBytes_heartbeat header r0
  | testRequest header r0 => exact Message.decodeBytes_testRequest header r0
  | reject header r0 => exact Message.decodeBytes_reject header r0
  | newOrderSingle header r0 => exact Message.decodeBytes_newOrderSingle header r0
  | orderCancelReplaceRequest header r0 => exact Message.decodeBytes_orderCancelReplaceRequest header r0
  | orderCancelRequest header r0 => exact Message.decodeBytes_orderCancelRequest header r0
  | orderMassCancelRequest header r0 => exact Message.decodeBytes_orderMassCancelRequest header r0
  | orderStatusRequest header r0 => exact Message.decodeBytes_orderStatusRequest header r0
  | securityListRequest header r0 => exact Message.decodeBytes_securityListRequest header r0
  | securityDefinitionRequest header r0 => exact Message.decodeBytes_securityDefinitionRequest header r0
  | tradeCaptureReport header r0 => exact Message.decodeBytes_tradeCaptureReport header r0
  | tradeCaptureReportRequest header r0 => exact Message.decodeBytes_tradeCaptureReportRequest header r0
  | partyDetailsListRequest header r0 => exact Message.decodeBytes_partyDetailsListRequest header r0
  | marketDataRequest header r0 => exact Message.decodeBytes_marketDataRequest header r0

/-- BeginString as the venue fixes it: FIXT.1.1 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 84, 46, 49, 46, 49, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.SgxTitanotcOrderentryFixV155Client
