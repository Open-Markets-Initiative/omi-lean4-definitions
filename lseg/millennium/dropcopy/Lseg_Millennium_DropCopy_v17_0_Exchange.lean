import Wire

/-!
# London Stock Exchange  v17.0, Exchange messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.LsegMillenniumDropcopyFixV170Exchange

structure Header where
  senderCompID : Terminated 1  -- tag 49
  targetCompID : Terminated 1  -- tag 56
  onBehalfOfCompID : Option (Terminated 1)  -- tag 115
  msgSeqNum : Terminated 1  -- tag 34
  possDupFlag : Option (Terminated 1)  -- tag 43
  possResend : Option (Terminated 1)  -- tag 97
  sendingTime : Option (Terminated 1)  -- tag 52
  origSendingTime : Option (Terminated 1)  -- tag 122
  applVerID : Option (Terminated 1)  -- tag 1128
  deliverToCompID : Option (Terminated 1)  -- tag 128

def Header.parts (record : Header) : List Part :=
  [Part.required [52, 57] record.senderCompID,
   Part.required [53, 54] record.targetCompID,
   Part.optional [49, 49, 53] record.onBehalfOfCompID,
   Part.required [51, 52] record.msgSeqNum,
   Part.optional [52, 51] record.possDupFlag,
   Part.optional [57, 55] record.possResend,
   Part.optional [53, 50] record.sendingTime,
   Part.optional [49, 50, 50] record.origSendingTime,
   Part.optional [49, 49, 50, 56] record.applVerID,
   Part.optional [49, 50, 56] record.deliverToCompID]

def Header.tags : List (List (List UInt8)) :=
  [[[52, 57]], [[53, 54]], [[49, 49, 53]], [[51, 52]], [[52, 51]], [[57, 55]], [[53, 50]], [[49, 50, 50]], [[49, 49, 50, 56]], [[49, 50, 56]]]

theorem Header.shape (record : Header) : record.parts.map Part.tags = Header.tags := rfl

def Header.decode (tokens : List Token) : Option Header := do
  let senderCompID ← readRequired [52, 57] tokens
  let targetCompID ← readRequired [53, 54] tokens
  let onBehalfOfCompID ← readOptional [49, 49, 53] tokens
  let msgSeqNum ← readRequired [51, 52] tokens
  let possDupFlag ← readOptional [52, 51] tokens
  let possResend ← readOptional [57, 55] tokens
  let sendingTime ← readOptional [53, 50] tokens
  let origSendingTime ← readOptional [49, 50, 50] tokens
  let applVerID ← readOptional [49, 49, 50, 56] tokens
  let deliverToCompID ← readOptional [49, 50, 56] tokens
  pure { senderCompID, targetCompID, onBehalfOfCompID, msgSeqNum, possDupFlag, possResend, sendingTime, origSendingTime, applVerID, deliverToCompID }

theorem Header.decode_agrees (record : Header) (tokens : List Token)
    (agrees : ∀ tags ∈ Header.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Header.decode tokens = some record := by
  have distinct : Header.tags.flatten.Nodup := by decide +kernel
  have senderCompID := readRequired_part [52, 57] record.senderCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have targetCompID := readRequired_part [53, 54] record.targetCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have onBehalfOfCompID := readOptional_part [49, 49, 53] record.onBehalfOfCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have msgSeqNum := readRequired_part [51, 52] record.msgSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have possDupFlag := readOptional_part [52, 51] record.possDupFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have possResend := readOptional_part [57, 55] record.possResend tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have sendingTime := readOptional_part [53, 50] record.sendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have origSendingTime := readOptional_part [49, 50, 50] record.origSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have applVerID := readOptional_part [49, 49, 50, 56] record.applVerID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have deliverToCompID := readOptional_part [49, 50, 56] record.deliverToCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  simp only [Header.decode, senderCompID, targetCompID, onBehalfOfCompID, msgSeqNum, possDupFlag, possResend, sendingTime, origSendingTime, applVerID, deliverToCompID, some_bind] <;> rfl

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
  refMsgType : Option (Terminated 1)  -- tag 372
  refTagID : Option (Terminated 1)  -- tag 371
  sessionRejectReason : Option (Terminated 1)  -- tag 373
  text : Option (Terminated 1)  -- tag 58

def Reject.parts (record : Reject) : List Part :=
  [Part.required [52, 53] record.refSeqNum,
   Part.optional [51, 55, 50] record.refMsgType,
   Part.optional [51, 55, 49] record.refTagID,
   Part.optional [51, 55, 51] record.sessionRejectReason,
   Part.optional [53, 56] record.text]

def Reject.tags : List (List (List UInt8)) :=
  [[[52, 53]], [[51, 55, 50]], [[51, 55, 49]], [[51, 55, 51]], [[53, 56]]]

theorem Reject.shape (record : Reject) : record.parts.map Part.tags = Reject.tags := rfl

def Reject.decode (tokens : List Token) : Option Reject := do
  let refSeqNum ← readRequired [52, 53] tokens
  let refMsgType ← readOptional [51, 55, 50] tokens
  let refTagID ← readOptional [51, 55, 49] tokens
  let sessionRejectReason ← readOptional [51, 55, 51] tokens
  let text ← readOptional [53, 56] tokens
  pure { refSeqNum, refMsgType, refTagID, sessionRejectReason, text }

theorem Reject.decode_agrees (record : Reject) (tokens : List Token)
    (agrees : ∀ tags ∈ Reject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Reject.decode tokens = some record := by
  have distinct : Reject.tags.flatten.Nodup := by decide +kernel
  have refSeqNum := readRequired_part [52, 53] record.refSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have refMsgType := readOptional_part [51, 55, 50] record.refMsgType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have refTagID := readOptional_part [51, 55, 49] record.refTagID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have sessionRejectReason := readOptional_part [51, 55, 51] record.sessionRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [Reject.decode, refSeqNum, refMsgType, refTagID, sessionRejectReason, text, some_bind] <;> rfl

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

structure NoPartyIDs where
  partyID : Terminated 1  -- tag 448
  partyIDSource : Terminated 1  -- tag 447
  partyRole : Terminated 1  -- tag 452
  partyRoleQualifier : Option (Terminated 1)  -- tag 2376

def NoPartyIDs.parts (record : NoPartyIDs) : List Part :=
  [Part.required [52, 52, 56] record.partyID,
   Part.required [52, 52, 55] record.partyIDSource,
   Part.required [52, 53, 50] record.partyRole,
   Part.optional [50, 51, 55, 54] record.partyRoleQualifier]

def NoPartyIDs.tags : List (List (List UInt8)) :=
  [[[52, 52, 56]], [[52, 52, 55]], [[52, 53, 50]], [[50, 51, 55, 54]]]

theorem NoPartyIDs.shape (record : NoPartyIDs) : record.parts.map Part.tags = NoPartyIDs.tags := rfl

def NoPartyIDs.decode (tokens : List Token) : Option NoPartyIDs := do
  let partyID ← readRequired [52, 52, 56] tokens
  let partyIDSource ← readRequired [52, 52, 55] tokens
  let partyRole ← readRequired [52, 53, 50] tokens
  let partyRoleQualifier ← readOptional [50, 51, 55, 54] tokens
  pure { partyID, partyIDSource, partyRole, partyRoleQualifier }

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

structure ExecutionReport where
  execID : Terminated 1  -- tag 17
  clOrdID : Option (Terminated 1)  -- tag 11
  origClOrdID : Option (Terminated 1)  -- tag 41
  orderID : Option (Terminated 1)  -- tag 37
  massStatusReqID : Option (Terminated 1)  -- tag 584
  rFQID : Option (Terminated 1)  -- tag 30006
  quoteRespType : Option (Terminated 1)  -- tag 694
  noTrdRegPublications : List NoTrdRegPublications  -- tag 2668
  noOrderAttributes : List NoOrderAttributes  -- tag 2593
  orderOrigination : Option (Terminated 1)  -- tag 1724
  lastRptRequested : Option (Terminated 1)  -- tag 912
  execType : Terminated 1  -- tag 150
  execRefID : Option (Terminated 1)  -- tag 19
  execRestatementReason : Option (Terminated 1)  -- tag 378
  ordStatus : Terminated 1  -- tag 39
  ordRejReason : Option (Terminated 1)  -- tag 103
  tradingSessionID : Option (Terminated 1)  -- tag 336
  text : Option (Terminated 1)  -- tag 58
  lastQty : Option (Terminated 1)  -- tag 32
  lastPx : Option (Terminated 1)  -- tag 31
  leavesQty : Option (Terminated 1)  -- tag 151
  cumQty : Option (Terminated 1)  -- tag 14
  securityID : Terminated 1  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22
  noPartyIDs : List NoPartyIDs  -- tag 453
  account : Option (Terminated 1)  -- tag 1
  ordType : Terminated 1  -- tag 40
  timeInForce : Option (Terminated 1)  -- tag 59
  expireTime : Option (Terminated 1)  -- tag 126
  expireDate : Option (Terminated 1)  -- tag 432
  side : Option (Terminated 1)  -- tag 54
  orderQty : Option (Terminated 1)  -- tag 38
  displayQty : Option (Terminated 1)  -- tag 1138
  displayMethod : Option (Terminated 1)  -- tag 1084
  price : Option (Terminated 1)  -- tag 44
  stopPx : Option (Terminated 1)  -- tag 99
  preTradeAnonymity : Option (Terminated 1)  -- tag 1091
  mDEntryID : Option (Terminated 1)  -- tag 278
  accountType : Option (Terminated 1)  -- tag 581
  orderCapacity : Option (Terminated 1)  -- tag 528
  transactTime : Option (Terminated 1)  -- tag 60
  secondaryClOrdID : Option (Terminated 1)  -- tag 526
  clOrdLinkID : Option (Terminated 1)  -- tag 583
  tradeLiquidityIndicator : Option (Terminated 1)  -- tag 9730
  tradeMatchID : Option (Terminated 1)  -- tag 880
  typeOfTrade : Option (Terminated 1)  -- tag 20000
  passiveOnlyOrder : Option (Terminated 1)  -- tag 27010
  minQty : Option (Terminated 1)  -- tag 110
  lastLiquidityInd : Option (Terminated 1)  -- tag 851
  contraOrderBook : Option (Terminated 1)  -- tag 33007
  groupID : Option (Terminated 1)  -- tag 27017
  avgPx : Option (Terminated 1)  -- tag 6
  lastMkt : Option (Terminated 1)  -- tag 30
  offset : Option (Terminated 1)  -- tag 27018
  decimalTVTIC : Option (Terminated 1)  -- tag 27020
  trdType : Option (Terminated 1)  -- tag 828
  peggedExecInst : Option (Terminated 1)  -- tag 27021
  ownerType : Option (Terminated 1)  -- tag 522

def ExecutionReport.parts (record : ExecutionReport) : List Part :=
  [Part.required [49, 55] record.execID,
   Part.optional [49, 49] record.clOrdID,
   Part.optional [52, 49] record.origClOrdID,
   Part.optional [51, 55] record.orderID,
   Part.optional [53, 56, 52] record.massStatusReqID,
   Part.optional [51, 48, 48, 48, 54] record.rFQID,
   Part.optional [54, 57, 52] record.quoteRespType,
   Part.group [50, 54, 54, 56] NoTrdRegPublications.members NoTrdRegPublications.encode NoTrdRegPublications.within record.noTrdRegPublications,
   Part.group [50, 53, 57, 51] NoOrderAttributes.members NoOrderAttributes.encode NoOrderAttributes.within record.noOrderAttributes,
   Part.optional [49, 55, 50, 52] record.orderOrigination,
   Part.optional [57, 49, 50] record.lastRptRequested,
   Part.required [49, 53, 48] record.execType,
   Part.optional [49, 57] record.execRefID,
   Part.optional [51, 55, 56] record.execRestatementReason,
   Part.required [51, 57] record.ordStatus,
   Part.optional [49, 48, 51] record.ordRejReason,
   Part.optional [51, 51, 54] record.tradingSessionID,
   Part.optional [53, 56] record.text,
   Part.optional [51, 50] record.lastQty,
   Part.optional [51, 49] record.lastPx,
   Part.optional [49, 53, 49] record.leavesQty,
   Part.optional [49, 52] record.cumQty,
   Part.required [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource,
   Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.optional [49] record.account,
   Part.required [52, 48] record.ordType,
   Part.optional [53, 57] record.timeInForce,
   Part.optional [49, 50, 54] record.expireTime,
   Part.optional [52, 51, 50] record.expireDate,
   Part.optional [53, 52] record.side,
   Part.optional [51, 56] record.orderQty,
   Part.optional [49, 49, 51, 56] record.displayQty,
   Part.optional [49, 48, 56, 52] record.displayMethod,
   Part.optional [52, 52] record.price,
   Part.optional [57, 57] record.stopPx,
   Part.optional [49, 48, 57, 49] record.preTradeAnonymity,
   Part.optional [50, 55, 56] record.mDEntryID,
   Part.optional [53, 56, 49] record.accountType,
   Part.optional [53, 50, 56] record.orderCapacity,
   Part.optional [54, 48] record.transactTime,
   Part.optional [53, 50, 54] record.secondaryClOrdID,
   Part.optional [53, 56, 51] record.clOrdLinkID,
   Part.optional [57, 55, 51, 48] record.tradeLiquidityIndicator,
   Part.optional [56, 56, 48] record.tradeMatchID,
   Part.optional [50, 48, 48, 48, 48] record.typeOfTrade,
   Part.optional [50, 55, 48, 49, 48] record.passiveOnlyOrder,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [56, 53, 49] record.lastLiquidityInd,
   Part.optional [51, 51, 48, 48, 55] record.contraOrderBook,
   Part.optional [50, 55, 48, 49, 55] record.groupID,
   Part.optional [54] record.avgPx,
   Part.optional [51, 48] record.lastMkt,
   Part.optional [50, 55, 48, 49, 56] record.offset,
   Part.optional [50, 55, 48, 50, 48] record.decimalTVTIC,
   Part.optional [56, 50, 56] record.trdType,
   Part.optional [50, 55, 48, 50, 49] record.peggedExecInst,
   Part.optional [53, 50, 50] record.ownerType]

def ExecutionReport.tags : List (List (List UInt8)) :=
  [[[49, 55]], [[49, 49]], [[52, 49]], [[51, 55]], [[53, 56, 52]], [[51, 48, 48, 48, 54]], [[54, 57, 52]], [50, 54, 54, 56] :: NoTrdRegPublications.members, [50, 53, 57, 51] :: NoOrderAttributes.members, [[49, 55, 50, 52]], [[57, 49, 50]], [[49, 53, 48]], [[49, 57]], [[51, 55, 56]], [[51, 57]], [[49, 48, 51]], [[51, 51, 54]], [[53, 56]], [[51, 50]], [[51, 49]], [[49, 53, 49]], [[49, 52]], [[52, 56]], [[50, 50]], [52, 53, 51] :: NoPartyIDs.members, [[49]], [[52, 48]], [[53, 57]], [[49, 50, 54]], [[52, 51, 50]], [[53, 52]], [[51, 56]], [[49, 49, 51, 56]], [[49, 48, 56, 52]], [[52, 52]], [[57, 57]], [[49, 48, 57, 49]], [[50, 55, 56]], [[53, 56, 49]], [[53, 50, 56]], [[54, 48]], [[53, 50, 54]], [[53, 56, 51]], [[57, 55, 51, 48]], [[56, 56, 48]], [[50, 48, 48, 48, 48]], [[50, 55, 48, 49, 48]], [[49, 49, 48]], [[56, 53, 49]], [[51, 51, 48, 48, 55]], [[50, 55, 48, 49, 55]], [[54]], [[51, 48]], [[50, 55, 48, 49, 56]], [[50, 55, 48, 50, 48]], [[56, 50, 56]], [[50, 55, 48, 50, 49]], [[53, 50, 50]]]

theorem ExecutionReport.shape (record : ExecutionReport) : record.parts.map Part.tags = ExecutionReport.tags := rfl

def ExecutionReport.decode (tokens : List Token) : Option ExecutionReport := do
  let execID ← readRequired [49, 55] tokens
  let clOrdID ← readOptional [49, 49] tokens
  let origClOrdID ← readOptional [52, 49] tokens
  let orderID ← readOptional [51, 55] tokens
  let massStatusReqID ← readOptional [53, 56, 52] tokens
  let rFQID ← readOptional [51, 48, 48, 48, 54] tokens
  let quoteRespType ← readOptional [54, 57, 52] tokens
  let noTrdRegPublications ← readGroup [50, 54, 54, 56] [50, 54, 54, 57] NoTrdRegPublications.members NoTrdRegPublications.decode tokens
  let noOrderAttributes ← readGroup [50, 53, 57, 51] [50, 53, 57, 52] NoOrderAttributes.members NoOrderAttributes.decode tokens
  let orderOrigination ← readOptional [49, 55, 50, 52] tokens
  let lastRptRequested ← readOptional [57, 49, 50] tokens
  let execType ← readRequired [49, 53, 48] tokens
  let execRefID ← readOptional [49, 57] tokens
  let execRestatementReason ← readOptional [51, 55, 56] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let ordRejReason ← readOptional [49, 48, 51] tokens
  let tradingSessionID ← readOptional [51, 51, 54] tokens
  let text ← readOptional [53, 56] tokens
  let lastQty ← readOptional [51, 50] tokens
  let lastPx ← readOptional [51, 49] tokens
  let leavesQty ← readOptional [49, 53, 49] tokens
  let cumQty ← readOptional [49, 52] tokens
  let securityID ← readRequired [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let account ← readOptional [49] tokens
  let ordType ← readRequired [52, 48] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let expireTime ← readOptional [49, 50, 54] tokens
  let expireDate ← readOptional [52, 51, 50] tokens
  let side ← readOptional [53, 52] tokens
  let orderQty ← readOptional [51, 56] tokens
  let displayQty ← readOptional [49, 49, 51, 56] tokens
  let displayMethod ← readOptional [49, 48, 56, 52] tokens
  let price ← readOptional [52, 52] tokens
  let stopPx ← readOptional [57, 57] tokens
  let preTradeAnonymity ← readOptional [49, 48, 57, 49] tokens
  let mDEntryID ← readOptional [50, 55, 56] tokens
  let accountType ← readOptional [53, 56, 49] tokens
  let orderCapacity ← readOptional [53, 50, 56] tokens
  let transactTime ← readOptional [54, 48] tokens
  let secondaryClOrdID ← readOptional [53, 50, 54] tokens
  let clOrdLinkID ← readOptional [53, 56, 51] tokens
  let tradeLiquidityIndicator ← readOptional [57, 55, 51, 48] tokens
  let tradeMatchID ← readOptional [56, 56, 48] tokens
  let typeOfTrade ← readOptional [50, 48, 48, 48, 48] tokens
  let passiveOnlyOrder ← readOptional [50, 55, 48, 49, 48] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let lastLiquidityInd ← readOptional [56, 53, 49] tokens
  let contraOrderBook ← readOptional [51, 51, 48, 48, 55] tokens
  let groupID ← readOptional [50, 55, 48, 49, 55] tokens
  let avgPx ← readOptional [54] tokens
  let lastMkt ← readOptional [51, 48] tokens
  let offset ← readOptional [50, 55, 48, 49, 56] tokens
  let decimalTVTIC ← readOptional [50, 55, 48, 50, 48] tokens
  let trdType ← readOptional [56, 50, 56] tokens
  let peggedExecInst ← readOptional [50, 55, 48, 50, 49] tokens
  let ownerType ← readOptional [53, 50, 50] tokens
  pure { execID, clOrdID, origClOrdID, orderID, massStatusReqID, rFQID, quoteRespType, noTrdRegPublications, noOrderAttributes, orderOrigination, lastRptRequested, execType, execRefID, execRestatementReason, ordStatus, ordRejReason, tradingSessionID, text, lastQty, lastPx, leavesQty, cumQty, securityID, securityIDSource, noPartyIDs, account, ordType, timeInForce, expireTime, expireDate, side, orderQty, displayQty, displayMethod, price, stopPx, preTradeAnonymity, mDEntryID, accountType, orderCapacity, transactTime, secondaryClOrdID, clOrdLinkID, tradeLiquidityIndicator, tradeMatchID, typeOfTrade, passiveOnlyOrder, minQty, lastLiquidityInd, contraOrderBook, groupID, avgPx, lastMkt, offset, decimalTVTIC, trdType, peggedExecInst, ownerType }

theorem ExecutionReport.decode_agrees (record : ExecutionReport) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReport.decode tokens = some record := by
  have distinct : ExecutionReport.tags.flatten.Nodup := by decide +kernel
  have execID := readRequired_part [49, 55] record.execID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readOptional_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have massStatusReqID := readOptional_part [53, 56, 52] record.massStatusReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have rFQID := readOptional_part [51, 48, 48, 48, 54] record.rFQID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have quoteRespType := readOptional_part [54, 57, 52] record.quoteRespType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have noTrdRegPublications := readGroup_part [50, 54, 54, 56] [50, 54, 54, 57] NoTrdRegPublications.members NoTrdRegPublications.encode NoTrdRegPublications.within NoTrdRegPublications.decode NoTrdRegPublications.decode_encode NoTrdRegPublications.led record.noTrdRegPublications tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have noOrderAttributes := readGroup_part [50, 53, 57, 51] [50, 53, 57, 52] NoOrderAttributes.members NoOrderAttributes.encode NoOrderAttributes.within NoOrderAttributes.decode NoOrderAttributes.decode_encode NoOrderAttributes.led record.noOrderAttributes tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have orderOrigination := readOptional_part [49, 55, 50, 52] record.orderOrigination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have lastRptRequested := readOptional_part [57, 49, 50] record.lastRptRequested tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have execType := readRequired_part [49, 53, 48] record.execType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have execRefID := readOptional_part [49, 57] record.execRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have execRestatementReason := readOptional_part [51, 55, 56] record.execRestatementReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have ordRejReason := readOptional_part [49, 48, 51] record.ordRejReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have tradingSessionID := readOptional_part [51, 51, 54] record.tradingSessionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have lastQty := readOptional_part [51, 50] record.lastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have lastPx := readOptional_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have leavesQty := readOptional_part [49, 53, 49] record.leavesQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have cumQty := readOptional_part [49, 52] record.cumQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have securityID := readRequired_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have expireTime := readOptional_part [49, 50, 54] record.expireTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have expireDate := readOptional_part [52, 51, 50] record.expireDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have orderQty := readOptional_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have displayQty := readOptional_part [49, 49, 51, 56] record.displayQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have displayMethod := readOptional_part [49, 48, 56, 52] record.displayMethod tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have stopPx := readOptional_part [57, 57] record.stopPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have preTradeAnonymity := readOptional_part [49, 48, 57, 49] record.preTradeAnonymity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have mDEntryID := readOptional_part [50, 55, 56] record.mDEntryID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have accountType := readOptional_part [53, 56, 49] record.accountType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  have orderCapacity := readOptional_part [53, 50, 56] record.orderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 39 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 40 (by decide +kernel)))
  have secondaryClOrdID := readOptional_part [53, 50, 54] record.secondaryClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 41 (by decide +kernel)))
  have clOrdLinkID := readOptional_part [53, 56, 51] record.clOrdLinkID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 42 (by decide +kernel)))
  have tradeLiquidityIndicator := readOptional_part [57, 55, 51, 48] record.tradeLiquidityIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 43 (by decide +kernel)))
  have tradeMatchID := readOptional_part [56, 56, 48] record.tradeMatchID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 44 (by decide +kernel)))
  have typeOfTrade := readOptional_part [50, 48, 48, 48, 48] record.typeOfTrade tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 45 (by decide +kernel)))
  have passiveOnlyOrder := readOptional_part [50, 55, 48, 49, 48] record.passiveOnlyOrder tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 46 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 47 (by decide +kernel)))
  have lastLiquidityInd := readOptional_part [56, 53, 49] record.lastLiquidityInd tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 48 (by decide +kernel)))
  have contraOrderBook := readOptional_part [51, 51, 48, 48, 55] record.contraOrderBook tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 49 (by decide +kernel)))
  have groupID := readOptional_part [50, 55, 48, 49, 55] record.groupID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 50 (by decide +kernel)))
  have avgPx := readOptional_part [54] record.avgPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 51 (by decide +kernel)))
  have lastMkt := readOptional_part [51, 48] record.lastMkt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 52 (by decide +kernel)))
  have offset := readOptional_part [50, 55, 48, 49, 56] record.offset tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 53 (by decide +kernel)))
  have decimalTVTIC := readOptional_part [50, 55, 48, 50, 48] record.decimalTVTIC tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 54 (by decide +kernel)))
  have trdType := readOptional_part [56, 50, 56] record.trdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 55 (by decide +kernel)))
  have peggedExecInst := readOptional_part [50, 55, 48, 50, 49] record.peggedExecInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 56 (by decide +kernel)))
  have ownerType := readOptional_part [53, 50, 50] record.ownerType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 57 (by decide +kernel)))
  simp only [ExecutionReport.decode, execID, clOrdID, origClOrdID, orderID, massStatusReqID, rFQID, quoteRespType, noTrdRegPublications, noOrderAttributes, orderOrigination, lastRptRequested, execType, execRefID, execRestatementReason, ordStatus, ordRejReason, tradingSessionID, text, lastQty, lastPx, leavesQty, cumQty, securityID, securityIDSource, noPartyIDs, account, ordType, timeInForce, expireTime, expireDate, side, orderQty, displayQty, displayMethod, price, stopPx, preTradeAnonymity, mDEntryID, accountType, orderCapacity, transactTime, secondaryClOrdID, clOrdLinkID, tradeLiquidityIndicator, tradeMatchID, typeOfTrade, passiveOnlyOrder, minQty, lastLiquidityInd, contraOrderBook, groupID, avgPx, lastMkt, offset, decimalTVTIC, trdType, peggedExecInst, ownerType, some_bind] <;> rfl

structure UserResponse where
  userRequestID : Terminated 1  -- tag 923
  username : Terminated 1  -- tag 553
  userStatus : Terminated 1  -- tag 926
  userStatusText : Option (Terminated 1)  -- tag 927

def UserResponse.parts (record : UserResponse) : List Part :=
  [Part.required [57, 50, 51] record.userRequestID,
   Part.required [53, 53, 51] record.username,
   Part.required [57, 50, 54] record.userStatus,
   Part.optional [57, 50, 55] record.userStatusText]

def UserResponse.tags : List (List (List UInt8)) :=
  [[[57, 50, 51]], [[53, 53, 51]], [[57, 50, 54]], [[57, 50, 55]]]

theorem UserResponse.shape (record : UserResponse) : record.parts.map Part.tags = UserResponse.tags := rfl

def UserResponse.decode (tokens : List Token) : Option UserResponse := do
  let userRequestID ← readRequired [57, 50, 51] tokens
  let username ← readRequired [53, 53, 51] tokens
  let userStatus ← readRequired [57, 50, 54] tokens
  let userStatusText ← readOptional [57, 50, 55] tokens
  pure { userRequestID, username, userStatus, userStatusText }

theorem UserResponse.decode_agrees (record : UserResponse) (tokens : List Token)
    (agrees : ∀ tags ∈ UserResponse.tags, select tags tokens = select tags (encodeParts record.parts)) :
    UserResponse.decode tokens = some record := by
  have distinct : UserResponse.tags.flatten.Nodup := by decide +kernel
  have userRequestID := readRequired_part [57, 50, 51] record.userRequestID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have username := readRequired_part [53, 53, 51] record.username tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have userStatus := readRequired_part [57, 50, 54] record.userStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have userStatusText := readOptional_part [57, 50, 55] record.userStatusText tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [UserResponse.decode, userRequestID, username, userStatus, userStatusText, some_bind] <;> rfl

structure NoLinesOfText where
  text : Terminated 1  -- tag 58

def NoLinesOfText.parts (record : NoLinesOfText) : List Part :=
  [Part.required [53, 56] record.text]

def NoLinesOfText.tags : List (List (List UInt8)) :=
  [[[53, 56]]]

theorem NoLinesOfText.shape (record : NoLinesOfText) : record.parts.map Part.tags = NoLinesOfText.tags := rfl

def NoLinesOfText.decode (tokens : List Token) : Option NoLinesOfText := do
  let text ← readRequired [53, 56] tokens
  pure { text }

theorem NoLinesOfText.decode_agrees (record : NoLinesOfText) (tokens : List Token)
    (agrees : ∀ tags ∈ NoLinesOfText.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoLinesOfText.decode tokens = some record := by
  have distinct : NoLinesOfText.tags.flatten.Nodup := by decide +kernel
  have text := readRequired_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [NoLinesOfText.decode, text, some_bind] <;> rfl

def NoLinesOfText.members : List (List UInt8) := NoLinesOfText.tags.flatten

def NoLinesOfText.encode (entry : NoLinesOfText) : List Token := encodeParts entry.parts

theorem NoLinesOfText.decode_encode (entry : NoLinesOfText) : NoLinesOfText.decode entry.encode = some entry :=
  NoLinesOfText.decode_agrees entry _ (fun _ _ => rfl)

theorem NoLinesOfText.within (entry : NoLinesOfText) : ∀ token ∈ entry.encode, token.tag ∈ NoLinesOfText.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoLinesOfText.shape] at this

theorem NoLinesOfText.led (entry : NoLinesOfText) : Lead [53, 56] entry.encode :=
  lead_parts [53, 56] entry.text _ NoLinesOfText.tags.tail rfl (by decide +kernel)

structure NoRelatedSym where
  securityID : Terminated 1  -- tag 48
  securityIDSource : Terminated 1  -- tag 22

def NoRelatedSym.parts (record : NoRelatedSym) : List Part :=
  [Part.required [52, 56] record.securityID,
   Part.required [50, 50] record.securityIDSource]

def NoRelatedSym.tags : List (List (List UInt8)) :=
  [[[52, 56]], [[50, 50]]]

theorem NoRelatedSym.shape (record : NoRelatedSym) : record.parts.map Part.tags = NoRelatedSym.tags := rfl

def NoRelatedSym.decode (tokens : List Token) : Option NoRelatedSym := do
  let securityID ← readRequired [52, 56] tokens
  let securityIDSource ← readRequired [50, 50] tokens
  pure { securityID, securityIDSource }

theorem NoRelatedSym.decode_agrees (record : NoRelatedSym) (tokens : List Token)
    (agrees : ∀ tags ∈ NoRelatedSym.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoRelatedSym.decode tokens = some record := by
  have distinct : NoRelatedSym.tags.flatten.Nodup := by decide +kernel
  have securityID := readRequired_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityIDSource := readRequired_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [NoRelatedSym.decode, securityID, securityIDSource, some_bind] <;> rfl

def NoRelatedSym.members : List (List UInt8) := NoRelatedSym.tags.flatten

def NoRelatedSym.encode (entry : NoRelatedSym) : List Token := encodeParts entry.parts

theorem NoRelatedSym.decode_encode (entry : NoRelatedSym) : NoRelatedSym.decode entry.encode = some entry :=
  NoRelatedSym.decode_agrees entry _ (fun _ _ => rfl)

theorem NoRelatedSym.within (entry : NoRelatedSym) : ∀ token ∈ entry.encode, token.tag ∈ NoRelatedSym.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoRelatedSym.shape] at this

theorem NoRelatedSym.led (entry : NoRelatedSym) : Lead [52, 56] entry.encode :=
  lead_parts [52, 56] entry.securityID _ NoRelatedSym.tags.tail rfl (by decide +kernel)

structure NoRoutingIDs where
  routingType : Terminated 1  -- tag 216
  routingID : Terminated 1  -- tag 217

def NoRoutingIDs.parts (record : NoRoutingIDs) : List Part :=
  [Part.required [50, 49, 54] record.routingType,
   Part.required [50, 49, 55] record.routingID]

def NoRoutingIDs.tags : List (List (List UInt8)) :=
  [[[50, 49, 54]], [[50, 49, 55]]]

theorem NoRoutingIDs.shape (record : NoRoutingIDs) : record.parts.map Part.tags = NoRoutingIDs.tags := rfl

def NoRoutingIDs.decode (tokens : List Token) : Option NoRoutingIDs := do
  let routingType ← readRequired [50, 49, 54] tokens
  let routingID ← readRequired [50, 49, 55] tokens
  pure { routingType, routingID }

theorem NoRoutingIDs.decode_agrees (record : NoRoutingIDs) (tokens : List Token)
    (agrees : ∀ tags ∈ NoRoutingIDs.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoRoutingIDs.decode tokens = some record := by
  have distinct : NoRoutingIDs.tags.flatten.Nodup := by decide +kernel
  have routingType := readRequired_part [50, 49, 54] record.routingType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have routingID := readRequired_part [50, 49, 55] record.routingID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [NoRoutingIDs.decode, routingType, routingID, some_bind] <;> rfl

def NoRoutingIDs.members : List (List UInt8) := NoRoutingIDs.tags.flatten

def NoRoutingIDs.encode (entry : NoRoutingIDs) : List Token := encodeParts entry.parts

theorem NoRoutingIDs.decode_encode (entry : NoRoutingIDs) : NoRoutingIDs.decode entry.encode = some entry :=
  NoRoutingIDs.decode_agrees entry _ (fun _ _ => rfl)

theorem NoRoutingIDs.within (entry : NoRoutingIDs) : ∀ token ∈ entry.encode, token.tag ∈ NoRoutingIDs.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoRoutingIDs.shape] at this

theorem NoRoutingIDs.led (entry : NoRoutingIDs) : Lead [50, 49, 54] entry.encode :=
  lead_parts [50, 49, 54] entry.routingType _ NoRoutingIDs.tags.tail rfl (by decide +kernel)

structure News where
  applID : Terminated 1  -- tag 1180
  origTime : Terminated 1  -- tag 42
  urgency : Terminated 1  -- tag 61
  headline : Terminated 1  -- tag 148
  noLinesOfText : List NoLinesOfText  -- tag 33
  noRelatedSym : List NoRelatedSym  -- tag 146
  noRoutingIDs : List NoRoutingIDs  -- tag 215

def News.parts (record : News) : List Part :=
  [Part.required [49, 49, 56, 48] record.applID,
   Part.required [52, 50] record.origTime,
   Part.required [54, 49] record.urgency,
   Part.required [49, 52, 56] record.headline,
   Part.group [51, 51] NoLinesOfText.members NoLinesOfText.encode NoLinesOfText.within record.noLinesOfText,
   Part.group [49, 52, 54] NoRelatedSym.members NoRelatedSym.encode NoRelatedSym.within record.noRelatedSym,
   Part.group [50, 49, 53] NoRoutingIDs.members NoRoutingIDs.encode NoRoutingIDs.within record.noRoutingIDs]

def News.tags : List (List (List UInt8)) :=
  [[[49, 49, 56, 48]], [[52, 50]], [[54, 49]], [[49, 52, 56]], [51, 51] :: NoLinesOfText.members, [49, 52, 54] :: NoRelatedSym.members, [50, 49, 53] :: NoRoutingIDs.members]

theorem News.shape (record : News) : record.parts.map Part.tags = News.tags := rfl

def News.decode (tokens : List Token) : Option News := do
  let applID ← readRequired [49, 49, 56, 48] tokens
  let origTime ← readRequired [52, 50] tokens
  let urgency ← readRequired [54, 49] tokens
  let headline ← readRequired [49, 52, 56] tokens
  let noLinesOfText ← readGroup [51, 51] [53, 56] NoLinesOfText.members NoLinesOfText.decode tokens
  let noRelatedSym ← readGroup [49, 52, 54] [52, 56] NoRelatedSym.members NoRelatedSym.decode tokens
  let noRoutingIDs ← readGroup [50, 49, 53] [50, 49, 54] NoRoutingIDs.members NoRoutingIDs.decode tokens
  pure { applID, origTime, urgency, headline, noLinesOfText, noRelatedSym, noRoutingIDs }

theorem News.decode_agrees (record : News) (tokens : List Token)
    (agrees : ∀ tags ∈ News.tags, select tags tokens = select tags (encodeParts record.parts)) :
    News.decode tokens = some record := by
  have distinct : News.tags.flatten.Nodup := by decide +kernel
  have applID := readRequired_part [49, 49, 56, 48] record.applID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have origTime := readRequired_part [52, 50] record.origTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have urgency := readRequired_part [54, 49] record.urgency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have headline := readRequired_part [49, 52, 56] record.headline tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have noLinesOfText := readGroup_part [51, 51] [53, 56] NoLinesOfText.members NoLinesOfText.encode NoLinesOfText.within NoLinesOfText.decode NoLinesOfText.decode_encode NoLinesOfText.led record.noLinesOfText tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have noRelatedSym := readGroup_part [49, 52, 54] [52, 56] NoRelatedSym.members NoRelatedSym.encode NoRelatedSym.within NoRelatedSym.decode NoRelatedSym.decode_encode NoRelatedSym.led record.noRelatedSym tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have noRoutingIDs := readGroup_part [50, 49, 53] [50, 49, 54] NoRoutingIDs.members NoRoutingIDs.encode NoRoutingIDs.within NoRoutingIDs.decode NoRoutingIDs.decode_encode NoRoutingIDs.led record.noRoutingIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  simp only [News.decode, applID, origTime, urgency, headline, noLinesOfText, noRelatedSym, noRoutingIDs, some_bind] <;> rfl

structure BusinessMessageReject where
  businessRejectRefID : Option (Terminated 1)  -- tag 379
  refSeqNum : Terminated 1  -- tag 45
  refMsgType : Terminated 1  -- tag 372
  refTagID : Option (Terminated 1)  -- tag 371
  businessRejectReason : Terminated 1  -- tag 380
  text : Option (Terminated 1)  -- tag 58

def BusinessMessageReject.parts (record : BusinessMessageReject) : List Part :=
  [Part.optional [51, 55, 57] record.businessRejectRefID,
   Part.required [52, 53] record.refSeqNum,
   Part.required [51, 55, 50] record.refMsgType,
   Part.optional [51, 55, 49] record.refTagID,
   Part.required [51, 56, 48] record.businessRejectReason,
   Part.optional [53, 56] record.text]

def BusinessMessageReject.tags : List (List (List UInt8)) :=
  [[[51, 55, 57]], [[52, 53]], [[51, 55, 50]], [[51, 55, 49]], [[51, 56, 48]], [[53, 56]]]

theorem BusinessMessageReject.shape (record : BusinessMessageReject) : record.parts.map Part.tags = BusinessMessageReject.tags := rfl

def BusinessMessageReject.decode (tokens : List Token) : Option BusinessMessageReject := do
  let businessRejectRefID ← readOptional [51, 55, 57] tokens
  let refSeqNum ← readRequired [52, 53] tokens
  let refMsgType ← readRequired [51, 55, 50] tokens
  let refTagID ← readOptional [51, 55, 49] tokens
  let businessRejectReason ← readRequired [51, 56, 48] tokens
  let text ← readOptional [53, 56] tokens
  pure { businessRejectRefID, refSeqNum, refMsgType, refTagID, businessRejectReason, text }

theorem BusinessMessageReject.decode_agrees (record : BusinessMessageReject) (tokens : List Token)
    (agrees : ∀ tags ∈ BusinessMessageReject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    BusinessMessageReject.decode tokens = some record := by
  have distinct : BusinessMessageReject.tags.flatten.Nodup := by decide +kernel
  have businessRejectRefID := readOptional_part [51, 55, 57] record.businessRejectRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have refSeqNum := readRequired_part [52, 53] record.refSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have refMsgType := readRequired_part [51, 55, 50] record.refMsgType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have refTagID := readOptional_part [51, 55, 49] record.refTagID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have businessRejectReason := readRequired_part [51, 56, 48] record.businessRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  simp only [BusinessMessageReject.decode, businessRejectRefID, refSeqNum, refMsgType, refTagID, businessRejectReason, text, some_bind] <;> rfl

inductive Message where
  | logon (header : Header) (r0 : Logon)
  | logout (header : Header) (r0 : Logout)
  | heartbeat (header : Header) (r0 : Heartbeat)
  | testRequest (header : Header) (r0 : TestRequest)
  | resendRequest (header : Header) (r0 : ResendRequest)
  | reject (header : Header) (r0 : Reject)
  | sequenceReset (header : Header) (r0 : SequenceReset)
  | executionReport (header : Header) (r0 : ExecutionReport)
  | userResponse (header : Header) (r0 : UserResponse)
  | news (header : Header) (r0 : News)
  | businessMessageReject (header : Header) (r0 : BusinessMessageReject)

def Message.tokens : Message → List Token
  | .logon header r0 => ⟨[51, 53], ⟨[65], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logout header r0 => ⟨[51, 53], ⟨[53], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .heartbeat header r0 => ⟨[51, 53], ⟨[48], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .testRequest header r0 => ⟨[51, 53], ⟨[49], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .resendRequest header r0 => ⟨[51, 53], ⟨[50], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .reject header r0 => ⟨[51, 53], ⟨[51], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .sequenceReset header r0 => ⟨[51, 53], ⟨[52], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .executionReport header r0 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .userResponse header r0 => ⟨[51, 53], ⟨[66, 70], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .news header r0 => ⟨[51, 53], ⟨[66], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .businessMessageReject header r0 => ⟨[51, 53], ⟨[106], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)

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
      else if token.value.val = [56] then
        if known (Header.tags ++ ExecutionReport.tags) rest then do
          let header ← Header.decode rest
          let r0 ← ExecutionReport.decode rest
          pure (.executionReport header r0)
        else none
      else if token.value.val = [66, 70] then
        if known (Header.tags ++ UserResponse.tags) rest then do
          let header ← Header.decode rest
          let r0 ← UserResponse.decode rest
          pure (.userResponse header r0)
        else none
      else if token.value.val = [66] then
        if known (Header.tags ++ News.tags) rest then do
          let header ← Header.decode rest
          let r0 ← News.decode rest
          pure (.news header r0)
        else none
      else if token.value.val = [106] then
        if known (Header.tags ++ BusinessMessageReject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← BusinessMessageReject.decode rest
          pure (.businessMessageReject header r0)
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

theorem Message.decode_executionReport (header : Header) (r0 : ExecutionReport) :
    Message.decode (Message.tokens (.executionReport header r0)) = some (.executionReport header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (ExecutionReport.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (ExecutionReport.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ ExecutionReport.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_userResponse (header : Header) (r0 : UserResponse) :
    Message.decode (Message.tokens (.userResponse header r0)) = some (.userResponse header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (UserResponse.tags) rfl rfl (by decide +kernel))
  have c1 := UserResponse.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (UserResponse.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ UserResponse.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_news (header : Header) (r0 : News) :
    Message.decode (Message.tokens (.news header r0)) = some (.news header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (News.tags) rfl rfl (by decide +kernel))
  have c1 := News.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (News.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ News.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_businessMessageReject (header : Header) (r0 : BusinessMessageReject) :
    Message.decode (Message.tokens (.businessMessageReject header r0)) = some (.businessMessageReject header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (BusinessMessageReject.tags) rfl rfl (by decide +kernel))
  have c1 := BusinessMessageReject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (BusinessMessageReject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ BusinessMessageReject.tags) rfl
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
  | executionReport header r0 => exact Message.decode_executionReport header r0
  | userResponse header r0 => exact Message.decode_userResponse header r0
  | news header r0 => exact Message.decode_news header r0
  | businessMessageReject header r0 => exact Message.decode_businessMessageReject header r0

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

theorem Message.decodeBytes_executionReport (header : Header) (r0 : ExecutionReport) :
    Message.decodeBytes (Message.encode (.executionReport header r0)) = some (.executionReport header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ ExecutionReport.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReport header r0

theorem Message.decodeBytes_userResponse (header : Header) (r0 : UserResponse) :
    Message.decodeBytes (Message.encode (.userResponse header r0)) = some (.userResponse header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[66, 70], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ UserResponse.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_userResponse header r0

theorem Message.decodeBytes_news (header : Header) (r0 : News) :
    Message.decodeBytes (Message.encode (.news header r0)) = some (.news header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[66], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ News.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_news header r0

theorem Message.decodeBytes_businessMessageReject (header : Header) (r0 : BusinessMessageReject) :
    Message.decodeBytes (Message.encode (.businessMessageReject header r0)) = some (.businessMessageReject header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[106], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ BusinessMessageReject.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_businessMessageReject header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | logon header r0 => exact Message.decodeBytes_logon header r0
  | logout header r0 => exact Message.decodeBytes_logout header r0
  | heartbeat header r0 => exact Message.decodeBytes_heartbeat header r0
  | testRequest header r0 => exact Message.decodeBytes_testRequest header r0
  | resendRequest header r0 => exact Message.decodeBytes_resendRequest header r0
  | reject header r0 => exact Message.decodeBytes_reject header r0
  | sequenceReset header r0 => exact Message.decodeBytes_sequenceReset header r0
  | executionReport header r0 => exact Message.decodeBytes_executionReport header r0
  | userResponse header r0 => exact Message.decodeBytes_userResponse header r0
  | news header r0 => exact Message.decodeBytes_news header r0
  | businessMessageReject header r0 => exact Message.decodeBytes_businessMessageReject header r0

/-- BeginString as the venue fixes it: FIXT.1.1 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 84, 46, 49, 46, 49, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.LsegMillenniumDropcopyFixV170Exchange
