import Wire

/-!
# London Stock Exchange  v19.0, Client messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.LsegMillenniumPosttradeFixV190Client

structure Header where
  senderCompID : Terminated 1  -- tag 49
  targetCompID : Terminated 1  -- tag 56
  msgSeqNum : Terminated 1  -- tag 34
  possDupFlag : Option (Terminated 1)  -- tag 43
  possResend : Option (Terminated 1)  -- tag 97
  sendingTime : Option (Terminated 1)  -- tag 52
  onBehalfOfCompID : Option (Terminated 1)  -- tag 115
  deliverToCompID : Option (Terminated 1)  -- tag 128
  origSendingTime : Option (Terminated 1)  -- tag 122
  applVerID : Option (Terminated 1)  -- tag 1128

def Header.parts (record : Header) : List Part :=
  [Part.required [52, 57] record.senderCompID,
   Part.required [53, 54] record.targetCompID,
   Part.required [51, 52] record.msgSeqNum,
   Part.optional [52, 51] record.possDupFlag,
   Part.optional [57, 55] record.possResend,
   Part.optional [53, 50] record.sendingTime,
   Part.optional [49, 49, 53] record.onBehalfOfCompID,
   Part.optional [49, 50, 56] record.deliverToCompID,
   Part.optional [49, 50, 50] record.origSendingTime,
   Part.optional [49, 49, 50, 56] record.applVerID]

def Header.tags : List (List (List UInt8)) :=
  [[[52, 57]], [[53, 54]], [[51, 52]], [[52, 51]], [[57, 55]], [[53, 50]], [[49, 49, 53]], [[49, 50, 56]], [[49, 50, 50]], [[49, 49, 50, 56]]]

theorem Header.shape (record : Header) : record.parts.map Part.tags = Header.tags := rfl

def Header.decode (tokens : List Token) : Option Header := do
  let senderCompID ← readRequired [52, 57] tokens
  let targetCompID ← readRequired [53, 54] tokens
  let msgSeqNum ← readRequired [51, 52] tokens
  let possDupFlag ← readOptional [52, 51] tokens
  let possResend ← readOptional [57, 55] tokens
  let sendingTime ← readOptional [53, 50] tokens
  let onBehalfOfCompID ← readOptional [49, 49, 53] tokens
  let deliverToCompID ← readOptional [49, 50, 56] tokens
  let origSendingTime ← readOptional [49, 50, 50] tokens
  let applVerID ← readOptional [49, 49, 50, 56] tokens
  pure { senderCompID, targetCompID, msgSeqNum, possDupFlag, possResend, sendingTime, onBehalfOfCompID, deliverToCompID, origSendingTime, applVerID }

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
  have possDupFlag := readOptional_part [52, 51] record.possDupFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have possResend := readOptional_part [57, 55] record.possResend tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have sendingTime := readOptional_part [53, 50] record.sendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have onBehalfOfCompID := readOptional_part [49, 49, 53] record.onBehalfOfCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have deliverToCompID := readOptional_part [49, 50, 56] record.deliverToCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have origSendingTime := readOptional_part [49, 50, 50] record.origSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have applVerID := readOptional_part [49, 49, 50, 56] record.applVerID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  simp only [Header.decode, senderCompID, targetCompID, msgSeqNum, possDupFlag, possResend, sendingTime, onBehalfOfCompID, deliverToCompID, origSendingTime, applVerID, some_bind] <;> rfl

structure Logon where
  encryptMethod : Terminated 1  -- tag 98
  heartBtInt : Terminated 1  -- tag 108
  resetSeqNumFlag : Option (Terminated 1)  -- tag 141
  password : Option (Terminated 1)  -- tag 554
  newPassword : Option (Terminated 1)  -- tag 925
  sessionStatus : Option (Terminated 1)  -- tag 1409
  defaultApplVerID : Terminated 1  -- tag 1137

def Logon.parts (record : Logon) : List Part :=
  [Part.required [57, 56] record.encryptMethod,
   Part.required [49, 48, 56] record.heartBtInt,
   Part.optional [49, 52, 49] record.resetSeqNumFlag,
   Part.optional [53, 53, 52] record.password,
   Part.optional [57, 50, 53] record.newPassword,
   Part.optional [49, 52, 48, 57] record.sessionStatus,
   Part.required [49, 49, 51, 55] record.defaultApplVerID]

def Logon.tags : List (List (List UInt8)) :=
  [[[57, 56]], [[49, 48, 56]], [[49, 52, 49]], [[53, 53, 52]], [[57, 50, 53]], [[49, 52, 48, 57]], [[49, 49, 51, 55]]]

theorem Logon.shape (record : Logon) : record.parts.map Part.tags = Logon.tags := rfl

def Logon.decode (tokens : List Token) : Option Logon := do
  let encryptMethod ← readRequired [57, 56] tokens
  let heartBtInt ← readRequired [49, 48, 56] tokens
  let resetSeqNumFlag ← readOptional [49, 52, 49] tokens
  let password ← readOptional [53, 53, 52] tokens
  let newPassword ← readOptional [57, 50, 53] tokens
  let sessionStatus ← readOptional [49, 52, 48, 57] tokens
  let defaultApplVerID ← readRequired [49, 49, 51, 55] tokens
  pure { encryptMethod, heartBtInt, resetSeqNumFlag, password, newPassword, sessionStatus, defaultApplVerID }

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
  have password := readOptional_part [53, 53, 52] record.password tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have newPassword := readOptional_part [57, 50, 53] record.newPassword tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have sessionStatus := readOptional_part [49, 52, 48, 57] record.sessionStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have defaultApplVerID := readRequired_part [49, 49, 51, 55] record.defaultApplVerID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  simp only [Logon.decode, encryptMethod, heartBtInt, resetSeqNumFlag, password, newPassword, sessionStatus, defaultApplVerID, some_bind] <;> rfl

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

structure SequenceReset where
  newSeqNo : Terminated 1  -- tag 36
  gapFillFlag : Option (Terminated 1)  -- tag 123

def SequenceReset.parts (record : SequenceReset) : List Part :=
  [Part.required [51, 54] record.newSeqNo,
   Part.optional [49, 50, 51] record.gapFillFlag]

def SequenceReset.tags : List (List (List UInt8)) :=
  [[[51, 54]], [[49, 50, 51]]]

theorem SequenceReset.shape (record : SequenceReset) : record.parts.map Part.tags = SequenceReset.tags := rfl

def SequenceReset.decode (tokens : List Token) : Option SequenceReset := do
  let newSeqNo ← readRequired [51, 54] tokens
  let gapFillFlag ← readOptional [49, 50, 51] tokens
  pure { newSeqNo, gapFillFlag }

theorem SequenceReset.decode_agrees (record : SequenceReset) (tokens : List Token)
    (agrees : ∀ tags ∈ SequenceReset.tags, select tags tokens = select tags (encodeParts record.parts)) :
    SequenceReset.decode tokens = some record := by
  have distinct : SequenceReset.tags.flatten.Nodup := by decide +kernel
  have newSeqNo := readRequired_part [51, 54] record.newSeqNo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have gapFillFlag := readOptional_part [49, 50, 51] record.gapFillFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [SequenceReset.decode, newSeqNo, gapFillFlag, some_bind] <;> rfl

structure NoSecurityAltID where
  securityAltID : Terminated 1  -- tag 455
  securityAltIDSource : Option (Terminated 1)  -- tag 456

def NoSecurityAltID.parts (record : NoSecurityAltID) : List Part :=
  [Part.required [52, 53, 53] record.securityAltID,
   Part.optional [52, 53, 54] record.securityAltIDSource]

def NoSecurityAltID.tags : List (List (List UInt8)) :=
  [[[52, 53, 53]], [[52, 53, 54]]]

theorem NoSecurityAltID.shape (record : NoSecurityAltID) : record.parts.map Part.tags = NoSecurityAltID.tags := rfl

def NoSecurityAltID.decode (tokens : List Token) : Option NoSecurityAltID := do
  let securityAltID ← readRequired [52, 53, 53] tokens
  let securityAltIDSource ← readOptional [52, 53, 54] tokens
  pure { securityAltID, securityAltIDSource }

theorem NoSecurityAltID.decode_agrees (record : NoSecurityAltID) (tokens : List Token)
    (agrees : ∀ tags ∈ NoSecurityAltID.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoSecurityAltID.decode tokens = some record := by
  have distinct : NoSecurityAltID.tags.flatten.Nodup := by decide +kernel
  have securityAltID := readRequired_part [52, 53, 53] record.securityAltID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityAltIDSource := readOptional_part [52, 53, 54] record.securityAltIDSource tokens
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

structure NoPartyIDs where
  partyID : Terminated 1  -- tag 448
  partyIDSource : Option (Terminated 1)  -- tag 447
  partyRole : Option (Terminated 1)  -- tag 452
  partyRoleQualifier : Option (Terminated 1)  -- tag 2376

def NoPartyIDs.parts (record : NoPartyIDs) : List Part :=
  [Part.required [52, 52, 56] record.partyID,
   Part.optional [52, 52, 55] record.partyIDSource,
   Part.optional [52, 53, 50] record.partyRole,
   Part.optional [50, 51, 55, 54] record.partyRoleQualifier]

def NoPartyIDs.tags : List (List (List UInt8)) :=
  [[[52, 52, 56]], [[52, 52, 55]], [[52, 53, 50]], [[50, 51, 55, 54]]]

theorem NoPartyIDs.shape (record : NoPartyIDs) : record.parts.map Part.tags = NoPartyIDs.tags := rfl

def NoPartyIDs.decode (tokens : List Token) : Option NoPartyIDs := do
  let partyID ← readRequired [52, 52, 56] tokens
  let partyIDSource ← readOptional [52, 52, 55] tokens
  let partyRole ← readOptional [52, 53, 50] tokens
  let partyRoleQualifier ← readOptional [50, 51, 55, 54] tokens
  pure { partyID, partyIDSource, partyRole, partyRoleQualifier }

theorem NoPartyIDs.decode_agrees (record : NoPartyIDs) (tokens : List Token)
    (agrees : ∀ tags ∈ NoPartyIDs.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoPartyIDs.decode tokens = some record := by
  have distinct : NoPartyIDs.tags.flatten.Nodup := by decide +kernel
  have partyID := readRequired_part [52, 52, 56] record.partyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have partyIDSource := readOptional_part [52, 52, 55] record.partyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have partyRole := readOptional_part [52, 53, 50] record.partyRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have partyRoleQualifier := readOptional_part [50, 51, 55, 54] record.partyRoleQualifier tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [NoPartyIDs.decode, partyID, partyIDSource, partyRole, partyRoleQualifier, some_bind] <;> rfl

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

structure NoOrderAttributes where
  orderAttributeType : Terminated 1  -- tag 2594
  orderAttributeValue : Option (Terminated 1)  -- tag 2595

def NoOrderAttributes.parts (record : NoOrderAttributes) : List Part :=
  [Part.required [50, 53, 57, 52] record.orderAttributeType,
   Part.optional [50, 53, 57, 53] record.orderAttributeValue]

def NoOrderAttributes.tags : List (List (List UInt8)) :=
  [[[50, 53, 57, 52]], [[50, 53, 57, 53]]]

theorem NoOrderAttributes.shape (record : NoOrderAttributes) : record.parts.map Part.tags = NoOrderAttributes.tags := rfl

def NoOrderAttributes.decode (tokens : List Token) : Option NoOrderAttributes := do
  let orderAttributeType ← readRequired [50, 53, 57, 52] tokens
  let orderAttributeValue ← readOptional [50, 53, 57, 53] tokens
  pure { orderAttributeType, orderAttributeValue }

theorem NoOrderAttributes.decode_agrees (record : NoOrderAttributes) (tokens : List Token)
    (agrees : ∀ tags ∈ NoOrderAttributes.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoOrderAttributes.decode tokens = some record := by
  have distinct : NoOrderAttributes.tags.flatten.Nodup := by decide +kernel
  have orderAttributeType := readRequired_part [50, 53, 57, 52] record.orderAttributeType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have orderAttributeValue := readOptional_part [50, 53, 57, 53] record.orderAttributeValue tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [NoOrderAttributes.decode, orderAttributeType, orderAttributeValue, some_bind] <;> rfl

def NoOrderAttributes.members : List (List UInt8) := NoOrderAttributes.tags.flatten

def NoOrderAttributes.encode (entry : NoOrderAttributes) : List Token := encodeParts entry.parts

theorem NoOrderAttributes.decode_encode (entry : NoOrderAttributes) : NoOrderAttributes.decode entry.encode = some entry :=
  NoOrderAttributes.decode_agrees entry _ (fun _ _ => rfl)

theorem NoOrderAttributes.within (entry : NoOrderAttributes) : ∀ token ∈ entry.encode, token.tag ∈ NoOrderAttributes.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoOrderAttributes.shape] at this

theorem NoOrderAttributes.led (entry : NoOrderAttributes) : Lead [50, 53, 57, 52] entry.encode :=
  lead_parts [50, 53, 57, 52] entry.orderAttributeType _ NoOrderAttributes.tags.tail rfl (by decide +kernel)

structure NoSides where
  side : Terminated 1  -- tag 54
  sideExecID : Option (Terminated 1)  -- tag 1427
  noPartyIDs : List NoPartyIDs  -- tag 453
  tradingSessionSubID : Option (Terminated 1)  -- tag 625
  orderCategory : Terminated 1  -- tag 1115
  sideLiquidityInd : Option (Terminated 1)  -- tag 1444
  orderID : Option (Terminated 1)  -- tag 37
  clOrdID : Option (Terminated 1)  -- tag 11
  orderCapacity : Terminated 1  -- tag 528
  account : Option (Terminated 1)  -- tag 1
  accountType : Terminated 1  -- tag 581
  algorithmicTradeIndicator : Option (Terminated 1)  -- tag 2667
  orderOrigination : Option (Terminated 1)  -- tag 1724
  noOrderAttributes : List NoOrderAttributes  -- tag 2593

def NoSides.parts (record : NoSides) : List Part :=
  [Part.required [53, 52] record.side,
   Part.optional [49, 52, 50, 55] record.sideExecID,
   Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.optional [54, 50, 53] record.tradingSessionSubID,
   Part.required [49, 49, 49, 53] record.orderCategory,
   Part.optional [49, 52, 52, 52] record.sideLiquidityInd,
   Part.optional [51, 55] record.orderID,
   Part.optional [49, 49] record.clOrdID,
   Part.required [53, 50, 56] record.orderCapacity,
   Part.optional [49] record.account,
   Part.required [53, 56, 49] record.accountType,
   Part.optional [50, 54, 54, 55] record.algorithmicTradeIndicator,
   Part.optional [49, 55, 50, 52] record.orderOrigination,
   Part.group [50, 53, 57, 51] NoOrderAttributes.members NoOrderAttributes.encode NoOrderAttributes.within record.noOrderAttributes]

def NoSides.tags : List (List (List UInt8)) :=
  [[[53, 52]], [[49, 52, 50, 55]], [52, 53, 51] :: NoPartyIDs.members, [[54, 50, 53]], [[49, 49, 49, 53]], [[49, 52, 52, 52]], [[51, 55]], [[49, 49]], [[53, 50, 56]], [[49]], [[53, 56, 49]], [[50, 54, 54, 55]], [[49, 55, 50, 52]], [50, 53, 57, 51] :: NoOrderAttributes.members]

theorem NoSides.shape (record : NoSides) : record.parts.map Part.tags = NoSides.tags := rfl

def NoSides.decode (tokens : List Token) : Option NoSides := do
  let side ← readRequired [53, 52] tokens
  let sideExecID ← readOptional [49, 52, 50, 55] tokens
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let tradingSessionSubID ← readOptional [54, 50, 53] tokens
  let orderCategory ← readRequired [49, 49, 49, 53] tokens
  let sideLiquidityInd ← readOptional [49, 52, 52, 52] tokens
  let orderID ← readOptional [51, 55] tokens
  let clOrdID ← readOptional [49, 49] tokens
  let orderCapacity ← readRequired [53, 50, 56] tokens
  let account ← readOptional [49] tokens
  let accountType ← readRequired [53, 56, 49] tokens
  let algorithmicTradeIndicator ← readOptional [50, 54, 54, 55] tokens
  let orderOrigination ← readOptional [49, 55, 50, 52] tokens
  let noOrderAttributes ← readGroup [50, 53, 57, 51] [50, 53, 57, 52] NoOrderAttributes.members NoOrderAttributes.decode tokens
  pure { side, sideExecID, noPartyIDs, tradingSessionSubID, orderCategory, sideLiquidityInd, orderID, clOrdID, orderCapacity, account, accountType, algorithmicTradeIndicator, orderOrigination, noOrderAttributes }

theorem NoSides.decode_agrees (record : NoSides) (tokens : List Token)
    (agrees : ∀ tags ∈ NoSides.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoSides.decode tokens = some record := by
  have distinct : NoSides.tags.flatten.Nodup := by decide +kernel
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have sideExecID := readOptional_part [49, 52, 50, 55] record.sideExecID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have tradingSessionSubID := readOptional_part [54, 50, 53] record.tradingSessionSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have orderCategory := readRequired_part [49, 49, 49, 53] record.orderCategory tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have sideLiquidityInd := readOptional_part [49, 52, 52, 52] record.sideLiquidityInd tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have clOrdID := readOptional_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have orderCapacity := readRequired_part [53, 50, 56] record.orderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have accountType := readRequired_part [53, 56, 49] record.accountType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have algorithmicTradeIndicator := readOptional_part [50, 54, 54, 55] record.algorithmicTradeIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have orderOrigination := readOptional_part [49, 55, 50, 52] record.orderOrigination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have noOrderAttributes := readGroup_part [50, 53, 57, 51] [50, 53, 57, 52] NoOrderAttributes.members NoOrderAttributes.encode NoOrderAttributes.within NoOrderAttributes.decode NoOrderAttributes.decode_encode NoOrderAttributes.led record.noOrderAttributes tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  simp only [NoSides.decode, side, sideExecID, noPartyIDs, tradingSessionSubID, orderCategory, sideLiquidityInd, orderID, clOrdID, orderCapacity, account, accountType, algorithmicTradeIndicator, orderOrigination, noOrderAttributes, some_bind] <;> rfl

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

structure NoTrdRegPublications where
  trdRegPublicationType : Terminated 1  -- tag 2669
  trdRegPublicationReason : Option (Terminated 1)  -- tag 2670

def NoTrdRegPublications.parts (record : NoTrdRegPublications) : List Part :=
  [Part.required [50, 54, 54, 57] record.trdRegPublicationType,
   Part.optional [50, 54, 55, 48] record.trdRegPublicationReason]

def NoTrdRegPublications.tags : List (List (List UInt8)) :=
  [[[50, 54, 54, 57]], [[50, 54, 55, 48]]]

theorem NoTrdRegPublications.shape (record : NoTrdRegPublications) : record.parts.map Part.tags = NoTrdRegPublications.tags := rfl

def NoTrdRegPublications.decode (tokens : List Token) : Option NoTrdRegPublications := do
  let trdRegPublicationType ← readRequired [50, 54, 54, 57] tokens
  let trdRegPublicationReason ← readOptional [50, 54, 55, 48] tokens
  pure { trdRegPublicationType, trdRegPublicationReason }

theorem NoTrdRegPublications.decode_agrees (record : NoTrdRegPublications) (tokens : List Token)
    (agrees : ∀ tags ∈ NoTrdRegPublications.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoTrdRegPublications.decode tokens = some record := by
  have distinct : NoTrdRegPublications.tags.flatten.Nodup := by decide +kernel
  have trdRegPublicationType := readRequired_part [50, 54, 54, 57] record.trdRegPublicationType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have trdRegPublicationReason := readOptional_part [50, 54, 55, 48] record.trdRegPublicationReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [NoTrdRegPublications.decode, trdRegPublicationType, trdRegPublicationReason, some_bind] <;> rfl

def NoTrdRegPublications.members : List (List UInt8) := NoTrdRegPublications.tags.flatten

def NoTrdRegPublications.encode (entry : NoTrdRegPublications) : List Token := encodeParts entry.parts

theorem NoTrdRegPublications.decode_encode (entry : NoTrdRegPublications) : NoTrdRegPublications.decode entry.encode = some entry :=
  NoTrdRegPublications.decode_agrees entry _ (fun _ _ => rfl)

theorem NoTrdRegPublications.within (entry : NoTrdRegPublications) : ∀ token ∈ entry.encode, token.tag ∈ NoTrdRegPublications.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoTrdRegPublications.shape] at this

theorem NoTrdRegPublications.led (entry : NoTrdRegPublications) : Lead [50, 54, 54, 57] entry.encode :=
  lead_parts [50, 54, 54, 57] entry.trdRegPublicationType _ NoTrdRegPublications.tags.tail rfl (by decide +kernel)

structure TradeCaptureReport where
  applID : Terminated 1  -- tag 1180
  applSeqNum : Terminated 1  -- tag 1181
  applLastSeqNum : Option (Terminated 1)  -- tag 1350
  applResendFlag : Option (Terminated 1)  -- tag 1352
  tradeRequestID : Option (Terminated 1)  -- tag 568
  lastRptRequested : Option (Terminated 1)  -- tag 912
  tradeReportID : Terminated 1  -- tag 571
  tradeID : Terminated 1  -- tag 1003
  tradeLinkID : Terminated 1  -- tag 820
  firmTradeID : Option (Terminated 1)  -- tag 1041
  tradeReportRefID : Option (Terminated 1)  -- tag 572
  tradeHandlingInstr : Terminated 1  -- tag 1123
  tradeReportType : Terminated 1  -- tag 856
  execType : Terminated 1  -- tag 150
  clearingType : Terminated 1  -- tag 20110
  novatedIndicator : Terminated 1  -- tag 20111
  tradeReportTransType : Terminated 1  -- tag 487
  matchStatus : Terminated 1  -- tag 573
  origTradeHandlingInstr : Option (Terminated 1)  -- tag 1124
  trdType : Terminated 1  -- tag 828
  trdSubType : Option (Terminated 1)  -- tag 829
  transactTime : Terminated 1  -- tag 60
  lastQty : Terminated 1  -- tag 32
  lastPx : Terminated 1  -- tag 31
  settlDate : Option (Terminated 1)  -- tag 64
  matchType : Terminated 1  -- tag 574
  securityID : Terminated 1  -- tag 48
  securityIDSource : Terminated 1  -- tag 22
  noSecurityAltID : List NoSecurityAltID  -- tag 454
  noSides : List NoSides  -- tag 552
  marketID : Option (Terminated 1)  -- tag 1301
  noTrdRegPublications : List NoTrdRegPublications  -- tag 2668
  origTradeDate : Option (Terminated 1)  -- tag 1125
  contraOrderBook : Option (Terminated 1)  -- tag 33007
  decimalTVTIC : Terminated 1  -- tag 27020
  productComplex : Option (Terminated 1)  -- tag 1227

def TradeCaptureReport.parts (record : TradeCaptureReport) : List Part :=
  [Part.required [49, 49, 56, 48] record.applID,
   Part.required [49, 49, 56, 49] record.applSeqNum,
   Part.optional [49, 51, 53, 48] record.applLastSeqNum,
   Part.optional [49, 51, 53, 50] record.applResendFlag,
   Part.optional [53, 54, 56] record.tradeRequestID,
   Part.optional [57, 49, 50] record.lastRptRequested,
   Part.required [53, 55, 49] record.tradeReportID,
   Part.required [49, 48, 48, 51] record.tradeID,
   Part.required [56, 50, 48] record.tradeLinkID,
   Part.optional [49, 48, 52, 49] record.firmTradeID,
   Part.optional [53, 55, 50] record.tradeReportRefID,
   Part.required [49, 49, 50, 51] record.tradeHandlingInstr,
   Part.required [56, 53, 54] record.tradeReportType,
   Part.required [49, 53, 48] record.execType,
   Part.required [50, 48, 49, 49, 48] record.clearingType,
   Part.required [50, 48, 49, 49, 49] record.novatedIndicator,
   Part.required [52, 56, 55] record.tradeReportTransType,
   Part.required [53, 55, 51] record.matchStatus,
   Part.optional [49, 49, 50, 52] record.origTradeHandlingInstr,
   Part.required [56, 50, 56] record.trdType,
   Part.optional [56, 50, 57] record.trdSubType,
   Part.required [54, 48] record.transactTime,
   Part.required [51, 50] record.lastQty,
   Part.required [51, 49] record.lastPx,
   Part.optional [54, 52] record.settlDate,
   Part.required [53, 55, 52] record.matchType,
   Part.required [52, 56] record.securityID,
   Part.required [50, 50] record.securityIDSource,
   Part.group [52, 53, 52] NoSecurityAltID.members NoSecurityAltID.encode NoSecurityAltID.within record.noSecurityAltID,
   Part.group [53, 53, 50] NoSides.members NoSides.encode NoSides.within record.noSides,
   Part.optional [49, 51, 48, 49] record.marketID,
   Part.group [50, 54, 54, 56] NoTrdRegPublications.members NoTrdRegPublications.encode NoTrdRegPublications.within record.noTrdRegPublications,
   Part.optional [49, 49, 50, 53] record.origTradeDate,
   Part.optional [51, 51, 48, 48, 55] record.contraOrderBook,
   Part.required [50, 55, 48, 50, 48] record.decimalTVTIC,
   Part.optional [49, 50, 50, 55] record.productComplex]

def TradeCaptureReport.tags : List (List (List UInt8)) :=
  [[[49, 49, 56, 48]], [[49, 49, 56, 49]], [[49, 51, 53, 48]], [[49, 51, 53, 50]], [[53, 54, 56]], [[57, 49, 50]], [[53, 55, 49]], [[49, 48, 48, 51]], [[56, 50, 48]], [[49, 48, 52, 49]], [[53, 55, 50]], [[49, 49, 50, 51]], [[56, 53, 54]], [[49, 53, 48]], [[50, 48, 49, 49, 48]], [[50, 48, 49, 49, 49]], [[52, 56, 55]], [[53, 55, 51]], [[49, 49, 50, 52]], [[56, 50, 56]], [[56, 50, 57]], [[54, 48]], [[51, 50]], [[51, 49]], [[54, 52]], [[53, 55, 52]], [[52, 56]], [[50, 50]], [52, 53, 52] :: NoSecurityAltID.members, [53, 53, 50] :: NoSides.members, [[49, 51, 48, 49]], [50, 54, 54, 56] :: NoTrdRegPublications.members, [[49, 49, 50, 53]], [[51, 51, 48, 48, 55]], [[50, 55, 48, 50, 48]], [[49, 50, 50, 55]]]

theorem TradeCaptureReport.shape (record : TradeCaptureReport) : record.parts.map Part.tags = TradeCaptureReport.tags := rfl

def TradeCaptureReport.decode (tokens : List Token) : Option TradeCaptureReport := do
  let applID ← readRequired [49, 49, 56, 48] tokens
  let applSeqNum ← readRequired [49, 49, 56, 49] tokens
  let applLastSeqNum ← readOptional [49, 51, 53, 48] tokens
  let applResendFlag ← readOptional [49, 51, 53, 50] tokens
  let tradeRequestID ← readOptional [53, 54, 56] tokens
  let lastRptRequested ← readOptional [57, 49, 50] tokens
  let tradeReportID ← readRequired [53, 55, 49] tokens
  let tradeID ← readRequired [49, 48, 48, 51] tokens
  let tradeLinkID ← readRequired [56, 50, 48] tokens
  let firmTradeID ← readOptional [49, 48, 52, 49] tokens
  let tradeReportRefID ← readOptional [53, 55, 50] tokens
  let tradeHandlingInstr ← readRequired [49, 49, 50, 51] tokens
  let tradeReportType ← readRequired [56, 53, 54] tokens
  let execType ← readRequired [49, 53, 48] tokens
  let clearingType ← readRequired [50, 48, 49, 49, 48] tokens
  let novatedIndicator ← readRequired [50, 48, 49, 49, 49] tokens
  let tradeReportTransType ← readRequired [52, 56, 55] tokens
  let matchStatus ← readRequired [53, 55, 51] tokens
  let origTradeHandlingInstr ← readOptional [49, 49, 50, 52] tokens
  let trdType ← readRequired [56, 50, 56] tokens
  let trdSubType ← readOptional [56, 50, 57] tokens
  let transactTime ← readRequired [54, 48] tokens
  let lastQty ← readRequired [51, 50] tokens
  let lastPx ← readRequired [51, 49] tokens
  let settlDate ← readOptional [54, 52] tokens
  let matchType ← readRequired [53, 55, 52] tokens
  let securityID ← readRequired [52, 56] tokens
  let securityIDSource ← readRequired [50, 50] tokens
  let noSecurityAltID ← readGroup [52, 53, 52] [52, 53, 53] NoSecurityAltID.members NoSecurityAltID.decode tokens
  let noSides ← readGroup [53, 53, 50] [53, 52] NoSides.members NoSides.decode tokens
  let marketID ← readOptional [49, 51, 48, 49] tokens
  let noTrdRegPublications ← readGroup [50, 54, 54, 56] [50, 54, 54, 57] NoTrdRegPublications.members NoTrdRegPublications.decode tokens
  let origTradeDate ← readOptional [49, 49, 50, 53] tokens
  let contraOrderBook ← readOptional [51, 51, 48, 48, 55] tokens
  let decimalTVTIC ← readRequired [50, 55, 48, 50, 48] tokens
  let productComplex ← readOptional [49, 50, 50, 55] tokens
  pure { applID, applSeqNum, applLastSeqNum, applResendFlag, tradeRequestID, lastRptRequested, tradeReportID, tradeID, tradeLinkID, firmTradeID, tradeReportRefID, tradeHandlingInstr, tradeReportType, execType, clearingType, novatedIndicator, tradeReportTransType, matchStatus, origTradeHandlingInstr, trdType, trdSubType, transactTime, lastQty, lastPx, settlDate, matchType, securityID, securityIDSource, noSecurityAltID, noSides, marketID, noTrdRegPublications, origTradeDate, contraOrderBook, decimalTVTIC, productComplex }

theorem TradeCaptureReport.decode_agrees (record : TradeCaptureReport) (tokens : List Token)
    (agrees : ∀ tags ∈ TradeCaptureReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TradeCaptureReport.decode tokens = some record := by
  have distinct : TradeCaptureReport.tags.flatten.Nodup := by decide +kernel
  have applID := readRequired_part [49, 49, 56, 48] record.applID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have applSeqNum := readRequired_part [49, 49, 56, 49] record.applSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have applLastSeqNum := readOptional_part [49, 51, 53, 48] record.applLastSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have applResendFlag := readOptional_part [49, 51, 53, 50] record.applResendFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have tradeRequestID := readOptional_part [53, 54, 56] record.tradeRequestID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have lastRptRequested := readOptional_part [57, 49, 50] record.lastRptRequested tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have tradeReportID := readRequired_part [53, 55, 49] record.tradeReportID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have tradeID := readRequired_part [49, 48, 48, 51] record.tradeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have tradeLinkID := readRequired_part [56, 50, 48] record.tradeLinkID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have firmTradeID := readOptional_part [49, 48, 52, 49] record.firmTradeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have tradeReportRefID := readOptional_part [53, 55, 50] record.tradeReportRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have tradeHandlingInstr := readRequired_part [49, 49, 50, 51] record.tradeHandlingInstr tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have tradeReportType := readRequired_part [56, 53, 54] record.tradeReportType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have execType := readRequired_part [49, 53, 48] record.execType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have clearingType := readRequired_part [50, 48, 49, 49, 48] record.clearingType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have novatedIndicator := readRequired_part [50, 48, 49, 49, 49] record.novatedIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have tradeReportTransType := readRequired_part [52, 56, 55] record.tradeReportTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have matchStatus := readRequired_part [53, 55, 51] record.matchStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have origTradeHandlingInstr := readOptional_part [49, 49, 50, 52] record.origTradeHandlingInstr tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have trdType := readRequired_part [56, 50, 56] record.trdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have trdSubType := readOptional_part [56, 50, 57] record.trdSubType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have lastQty := readRequired_part [51, 50] record.lastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have lastPx := readRequired_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have settlDate := readOptional_part [54, 52] record.settlDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have matchType := readRequired_part [53, 55, 52] record.matchType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have securityID := readRequired_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have securityIDSource := readRequired_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have noSecurityAltID := readGroup_part [52, 53, 52] [52, 53, 53] NoSecurityAltID.members NoSecurityAltID.encode NoSecurityAltID.within NoSecurityAltID.decode NoSecurityAltID.decode_encode NoSecurityAltID.led record.noSecurityAltID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have noSides := readGroup_part [53, 53, 50] [53, 52] NoSides.members NoSides.encode NoSides.within NoSides.decode NoSides.decode_encode NoSides.led record.noSides tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have marketID := readOptional_part [49, 51, 48, 49] record.marketID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have noTrdRegPublications := readGroup_part [50, 54, 54, 56] [50, 54, 54, 57] NoTrdRegPublications.members NoTrdRegPublications.encode NoTrdRegPublications.within NoTrdRegPublications.decode NoTrdRegPublications.decode_encode NoTrdRegPublications.led record.noTrdRegPublications tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have origTradeDate := readOptional_part [49, 49, 50, 53] record.origTradeDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have contraOrderBook := readOptional_part [51, 51, 48, 48, 55] record.contraOrderBook tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have decimalTVTIC := readRequired_part [50, 55, 48, 50, 48] record.decimalTVTIC tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have productComplex := readOptional_part [49, 50, 50, 55] record.productComplex tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  simp only [TradeCaptureReport.decode, applID, applSeqNum, applLastSeqNum, applResendFlag, tradeRequestID, lastRptRequested, tradeReportID, tradeID, tradeLinkID, firmTradeID, tradeReportRefID, tradeHandlingInstr, tradeReportType, execType, clearingType, novatedIndicator, tradeReportTransType, matchStatus, origTradeHandlingInstr, trdType, trdSubType, transactTime, lastQty, lastPx, settlDate, matchType, securityID, securityIDSource, noSecurityAltID, noSides, marketID, noTrdRegPublications, origTradeDate, contraOrderBook, decimalTVTIC, productComplex, some_bind] <;> rfl

structure TradeCaptureReportRequest where
  tradeRequestID : Terminated 1  -- tag 568
  tradeRequestType : Terminated 1  -- tag 569
  execType : Option (Terminated 1)  -- tag 150
  trdType : Option (Terminated 1)  -- tag 828
  trdSubType : Option (Terminated 1)  -- tag 829
  securityID : Option (Terminated 1)  -- tag 48
  noSecurityAltID : List NoSecurityAltID  -- tag 454
  side : Option (Terminated 1)  -- tag 54
  matchType : Option (Terminated 1)  -- tag 574
  clOrdID : Option (Terminated 1)  -- tag 11
  orderID : Option (Terminated 1)  -- tag 37
  noPartyIDs : List NoPartyIDs  -- tag 453
  securityIDSource : Option (Terminated 1)  -- tag 22
  account : Option (Terminated 1)  -- tag 1

def TradeCaptureReportRequest.parts (record : TradeCaptureReportRequest) : List Part :=
  [Part.required [53, 54, 56] record.tradeRequestID,
   Part.required [53, 54, 57] record.tradeRequestType,
   Part.optional [49, 53, 48] record.execType,
   Part.optional [56, 50, 56] record.trdType,
   Part.optional [56, 50, 57] record.trdSubType,
   Part.optional [52, 56] record.securityID,
   Part.group [52, 53, 52] NoSecurityAltID.members NoSecurityAltID.encode NoSecurityAltID.within record.noSecurityAltID,
   Part.optional [53, 52] record.side,
   Part.optional [53, 55, 52] record.matchType,
   Part.optional [49, 49] record.clOrdID,
   Part.optional [51, 55] record.orderID,
   Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.optional [50, 50] record.securityIDSource,
   Part.optional [49] record.account]

def TradeCaptureReportRequest.tags : List (List (List UInt8)) :=
  [[[53, 54, 56]], [[53, 54, 57]], [[49, 53, 48]], [[56, 50, 56]], [[56, 50, 57]], [[52, 56]], [52, 53, 52] :: NoSecurityAltID.members, [[53, 52]], [[53, 55, 52]], [[49, 49]], [[51, 55]], [52, 53, 51] :: NoPartyIDs.members, [[50, 50]], [[49]]]

theorem TradeCaptureReportRequest.shape (record : TradeCaptureReportRequest) : record.parts.map Part.tags = TradeCaptureReportRequest.tags := rfl

def TradeCaptureReportRequest.decode (tokens : List Token) : Option TradeCaptureReportRequest := do
  let tradeRequestID ← readRequired [53, 54, 56] tokens
  let tradeRequestType ← readRequired [53, 54, 57] tokens
  let execType ← readOptional [49, 53, 48] tokens
  let trdType ← readOptional [56, 50, 56] tokens
  let trdSubType ← readOptional [56, 50, 57] tokens
  let securityID ← readOptional [52, 56] tokens
  let noSecurityAltID ← readGroup [52, 53, 52] [52, 53, 53] NoSecurityAltID.members NoSecurityAltID.decode tokens
  let side ← readOptional [53, 52] tokens
  let matchType ← readOptional [53, 55, 52] tokens
  let clOrdID ← readOptional [49, 49] tokens
  let orderID ← readOptional [51, 55] tokens
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let account ← readOptional [49] tokens
  pure { tradeRequestID, tradeRequestType, execType, trdType, trdSubType, securityID, noSecurityAltID, side, matchType, clOrdID, orderID, noPartyIDs, securityIDSource, account }

theorem TradeCaptureReportRequest.decode_agrees (record : TradeCaptureReportRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ TradeCaptureReportRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TradeCaptureReportRequest.decode tokens = some record := by
  have distinct : TradeCaptureReportRequest.tags.flatten.Nodup := by decide +kernel
  have tradeRequestID := readRequired_part [53, 54, 56] record.tradeRequestID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have tradeRequestType := readRequired_part [53, 54, 57] record.tradeRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have execType := readOptional_part [49, 53, 48] record.execType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have trdType := readOptional_part [56, 50, 56] record.trdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have trdSubType := readOptional_part [56, 50, 57] record.trdSubType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have noSecurityAltID := readGroup_part [52, 53, 52] [52, 53, 53] NoSecurityAltID.members NoSecurityAltID.encode NoSecurityAltID.within NoSecurityAltID.decode NoSecurityAltID.decode_encode NoSecurityAltID.led record.noSecurityAltID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have matchType := readOptional_part [53, 55, 52] record.matchType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have clOrdID := readOptional_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  simp only [TradeCaptureReportRequest.decode, tradeRequestID, tradeRequestType, execType, trdType, trdSubType, securityID, noSecurityAltID, side, matchType, clOrdID, orderID, noPartyIDs, securityIDSource, account, some_bind] <;> rfl

structure NoApplIDs where
  refApplID : Terminated 1  -- tag 1355
  applBegSeqNum : Option (Terminated 1)  -- tag 1182
  applEndSeqNum : Option (Terminated 1)  -- tag 1183
  refApplLastSeqNum : Option (Terminated 1)  -- tag 1357
  applResponseError : Option (Terminated 1)  -- tag 1354

def NoApplIDs.parts (record : NoApplIDs) : List Part :=
  [Part.required [49, 51, 53, 53] record.refApplID,
   Part.optional [49, 49, 56, 50] record.applBegSeqNum,
   Part.optional [49, 49, 56, 51] record.applEndSeqNum,
   Part.optional [49, 51, 53, 55] record.refApplLastSeqNum,
   Part.optional [49, 51, 53, 52] record.applResponseError]

def NoApplIDs.tags : List (List (List UInt8)) :=
  [[[49, 51, 53, 53]], [[49, 49, 56, 50]], [[49, 49, 56, 51]], [[49, 51, 53, 55]], [[49, 51, 53, 52]]]

theorem NoApplIDs.shape (record : NoApplIDs) : record.parts.map Part.tags = NoApplIDs.tags := rfl

def NoApplIDs.decode (tokens : List Token) : Option NoApplIDs := do
  let refApplID ← readRequired [49, 51, 53, 53] tokens
  let applBegSeqNum ← readOptional [49, 49, 56, 50] tokens
  let applEndSeqNum ← readOptional [49, 49, 56, 51] tokens
  let refApplLastSeqNum ← readOptional [49, 51, 53, 55] tokens
  let applResponseError ← readOptional [49, 51, 53, 52] tokens
  pure { refApplID, applBegSeqNum, applEndSeqNum, refApplLastSeqNum, applResponseError }

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
  have refApplLastSeqNum := readOptional_part [49, 51, 53, 55] record.refApplLastSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have applResponseError := readOptional_part [49, 51, 53, 52] record.applResponseError tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [NoApplIDs.decode, refApplID, applBegSeqNum, applEndSeqNum, refApplLastSeqNum, applResponseError, some_bind] <;> rfl

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

structure ApplicationMessageRequest where
  applReqID : Terminated 1  -- tag 1346
  applReqType : Terminated 1  -- tag 1347
  noApplIDs : List NoApplIDs  -- tag 1351

def ApplicationMessageRequest.parts (record : ApplicationMessageRequest) : List Part :=
  [Part.required [49, 51, 52, 54] record.applReqID,
   Part.required [49, 51, 52, 55] record.applReqType,
   Part.group [49, 51, 53, 49] NoApplIDs.members NoApplIDs.encode NoApplIDs.within record.noApplIDs]

def ApplicationMessageRequest.tags : List (List (List UInt8)) :=
  [[[49, 51, 52, 54]], [[49, 51, 52, 55]], [49, 51, 53, 49] :: NoApplIDs.members]

theorem ApplicationMessageRequest.shape (record : ApplicationMessageRequest) : record.parts.map Part.tags = ApplicationMessageRequest.tags := rfl

def ApplicationMessageRequest.decode (tokens : List Token) : Option ApplicationMessageRequest := do
  let applReqID ← readRequired [49, 51, 52, 54] tokens
  let applReqType ← readRequired [49, 51, 52, 55] tokens
  let noApplIDs ← readGroup [49, 51, 53, 49] [49, 51, 53, 53] NoApplIDs.members NoApplIDs.decode tokens
  pure { applReqID, applReqType, noApplIDs }

theorem ApplicationMessageRequest.decode_agrees (record : ApplicationMessageRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ ApplicationMessageRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ApplicationMessageRequest.decode tokens = some record := by
  have distinct : ApplicationMessageRequest.tags.flatten.Nodup := by decide +kernel
  have applReqID := readRequired_part [49, 51, 52, 54] record.applReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have applReqType := readRequired_part [49, 51, 52, 55] record.applReqType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have noApplIDs := readGroup_part [49, 51, 53, 49] [49, 51, 53, 53] NoApplIDs.members NoApplIDs.encode NoApplIDs.within NoApplIDs.decode NoApplIDs.decode_encode NoApplIDs.led record.noApplIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [ApplicationMessageRequest.decode, applReqID, applReqType, noApplIDs, some_bind] <;> rfl

inductive Message where
  | logon (header : Header) (r0 : Logon)
  | logout (header : Header) (r0 : Logout)
  | heartbeat (header : Header) (r0 : Heartbeat)
  | testRequest (header : Header) (r0 : TestRequest)
  | resendRequest (header : Header) (r0 : ResendRequest)
  | reject (header : Header) (r0 : Reject)
  | sequenceReset (header : Header) (r0 : SequenceReset)
  | tradeCaptureReport (header : Header) (r0 : TradeCaptureReport)
  | tradeCaptureReportRequest (header : Header) (r0 : TradeCaptureReportRequest)
  | applicationMessageRequest (header : Header) (r0 : ApplicationMessageRequest)

def Message.tokens : Message → List Token
  | .logon header r0 => ⟨[51, 53], ⟨[65], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logout header r0 => ⟨[51, 53], ⟨[53], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .heartbeat header r0 => ⟨[51, 53], ⟨[48], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .testRequest header r0 => ⟨[51, 53], ⟨[49], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .resendRequest header r0 => ⟨[51, 53], ⟨[50], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .reject header r0 => ⟨[51, 53], ⟨[51], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .sequenceReset header r0 => ⟨[51, 53], ⟨[52], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .tradeCaptureReport header r0 => ⟨[51, 53], ⟨[65, 69], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .tradeCaptureReportRequest header r0 => ⟨[51, 53], ⟨[65, 68], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .applicationMessageRequest header r0 => ⟨[51, 53], ⟨[66, 87], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)

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
      else if token.value.val = [50] then
        if known (Header.tags ++ ResendRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← ResendRequest.decode rest
          pure (.resendRequest header r0)
        else none
      else if token.value.val = [51] then
        if known (Header.tags ++ Reject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Reject.decode rest
          pure (.reject header r0)
        else none
      else if token.value.val = [52] then
        if known (Header.tags ++ SequenceReset.tags) rest then do
          let header ← Header.decode rest
          let r0 ← SequenceReset.decode rest
          pure (.sequenceReset header r0)
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
      else if token.value.val = [66, 87] then
        if known (Header.tags ++ ApplicationMessageRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← ApplicationMessageRequest.decode rest
          pure (.applicationMessageRequest header r0)
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

theorem Message.decode_resendRequest (header : Header) (r0 : ResendRequest) :
    Message.decode (Message.tokens (.resendRequest header r0)) = some (.resendRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (ResendRequest.tags) rfl rfl (by decide +kernel))
  have c1 := ResendRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (ResendRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ ResendRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_reject (header : Header) (r0 : Reject) :
    Message.decode (Message.tokens (.reject header r0)) = some (.reject header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (Reject.tags) rfl rfl (by decide +kernel))
  have c1 := Reject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (Reject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ Reject.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_sequenceReset (header : Header) (r0 : SequenceReset) :
    Message.decode (Message.tokens (.sequenceReset header r0)) = some (.sequenceReset header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (SequenceReset.tags) rfl rfl (by decide +kernel))
  have c1 := SequenceReset.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (SequenceReset.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ SequenceReset.tags) rfl
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

theorem Message.decode_applicationMessageRequest (header : Header) (r0 : ApplicationMessageRequest) :
    Message.decode (Message.tokens (.applicationMessageRequest header r0)) = some (.applicationMessageRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (ApplicationMessageRequest.tags) rfl rfl (by decide +kernel))
  have c1 := ApplicationMessageRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (ApplicationMessageRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ ApplicationMessageRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | logon header r0 => exact Message.decode_logon header r0
  | logout header r0 => exact Message.decode_logout header r0
  | heartbeat header r0 => exact Message.decode_heartbeat header r0
  | testRequest header r0 => exact Message.decode_testRequest header r0
  | resendRequest header r0 => exact Message.decode_resendRequest header r0
  | reject header r0 => exact Message.decode_reject header r0
  | sequenceReset header r0 => exact Message.decode_sequenceReset header r0
  | tradeCaptureReport header r0 => exact Message.decode_tradeCaptureReport header r0
  | tradeCaptureReportRequest header r0 => exact Message.decode_tradeCaptureReportRequest header r0
  | applicationMessageRequest header r0 => exact Message.decode_applicationMessageRequest header r0

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

theorem Message.decodeBytes_resendRequest (header : Header) (r0 : ResendRequest) :
    Message.decodeBytes (Message.encode (.resendRequest header r0)) = some (.resendRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[50], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ ResendRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_resendRequest header r0

theorem Message.decodeBytes_reject (header : Header) (r0 : Reject) :
    Message.decodeBytes (Message.encode (.reject header r0)) = some (.reject header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[51], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ Reject.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_reject header r0

theorem Message.decodeBytes_sequenceReset (header : Header) (r0 : SequenceReset) :
    Message.decodeBytes (Message.encode (.sequenceReset header r0)) = some (.sequenceReset header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[52], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ SequenceReset.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_sequenceReset header r0

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

theorem Message.decodeBytes_applicationMessageRequest (header : Header) (r0 : ApplicationMessageRequest) :
    Message.decodeBytes (Message.encode (.applicationMessageRequest header r0)) = some (.applicationMessageRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[66, 87], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ ApplicationMessageRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_applicationMessageRequest header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | logon header r0 => exact Message.decodeBytes_logon header r0
  | logout header r0 => exact Message.decodeBytes_logout header r0
  | heartbeat header r0 => exact Message.decodeBytes_heartbeat header r0
  | testRequest header r0 => exact Message.decodeBytes_testRequest header r0
  | resendRequest header r0 => exact Message.decodeBytes_resendRequest header r0
  | reject header r0 => exact Message.decodeBytes_reject header r0
  | sequenceReset header r0 => exact Message.decodeBytes_sequenceReset header r0
  | tradeCaptureReport header r0 => exact Message.decodeBytes_tradeCaptureReport header r0
  | tradeCaptureReportRequest header r0 => exact Message.decodeBytes_tradeCaptureReportRequest header r0
  | applicationMessageRequest header r0 => exact Message.decodeBytes_applicationMessageRequest header r0

/-- BeginString as the venue fixes it: FIXT.1.1 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 84, 46, 49, 46, 49, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.LsegMillenniumPosttradeFixV190Client
