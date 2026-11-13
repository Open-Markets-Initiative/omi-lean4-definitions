import Wire

/-!
# London Stock Exchange  v21.1, Exchange messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.LsegMillenniumTradingFixV211Exchange

structure Header where
  senderCompID : Terminated 1  -- tag 49
  targetCompID : Terminated 1  -- tag 56
  msgSeqNum : Terminated 1  -- tag 34
  possDupFlag : Option (Terminated 1)  -- tag 43
  possResend : Option (Terminated 1)  -- tag 97
  sendingTime : Option (Terminated 1)  -- tag 52
  origSendingTime : Option (Terminated 1)  -- tag 122
  applVerID : Option (Terminated 1)  -- tag 1128
  onBehalfOfCompID : Option (Terminated 1)  -- tag 115
  deliverToCompID : Option (Terminated 1)  -- tag 128

def Header.parts (record : Header) : List Part :=
  [Part.required [52, 57] record.senderCompID,
   Part.required [53, 54] record.targetCompID,
   Part.required [51, 52] record.msgSeqNum,
   Part.optional [52, 51] record.possDupFlag,
   Part.optional [57, 55] record.possResend,
   Part.optional [53, 50] record.sendingTime,
   Part.optional [49, 50, 50] record.origSendingTime,
   Part.optional [49, 49, 50, 56] record.applVerID,
   Part.optional [49, 49, 53] record.onBehalfOfCompID,
   Part.optional [49, 50, 56] record.deliverToCompID]

def Header.tags : List (List (List UInt8)) :=
  [[[52, 57]], [[53, 54]], [[51, 52]], [[52, 51]], [[57, 55]], [[53, 50]], [[49, 50, 50]], [[49, 49, 50, 56]], [[49, 49, 53]], [[49, 50, 56]]]

theorem Header.shape (record : Header) : record.parts.map Part.tags = Header.tags := rfl

def Header.decode (tokens : List Token) : Option Header := do
  let senderCompID ← readRequired [52, 57] tokens
  let targetCompID ← readRequired [53, 54] tokens
  let msgSeqNum ← readRequired [51, 52] tokens
  let possDupFlag ← readOptional [52, 51] tokens
  let possResend ← readOptional [57, 55] tokens
  let sendingTime ← readOptional [53, 50] tokens
  let origSendingTime ← readOptional [49, 50, 50] tokens
  let applVerID ← readOptional [49, 49, 50, 56] tokens
  let onBehalfOfCompID ← readOptional [49, 49, 53] tokens
  let deliverToCompID ← readOptional [49, 50, 56] tokens
  pure { senderCompID, targetCompID, msgSeqNum, possDupFlag, possResend, sendingTime, origSendingTime, applVerID, onBehalfOfCompID, deliverToCompID }

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
  have origSendingTime := readOptional_part [49, 50, 50] record.origSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have applVerID := readOptional_part [49, 49, 50, 56] record.applVerID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have onBehalfOfCompID := readOptional_part [49, 49, 53] record.onBehalfOfCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have deliverToCompID := readOptional_part [49, 50, 56] record.deliverToCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  simp only [Header.decode, senderCompID, targetCompID, msgSeqNum, possDupFlag, possResend, sendingTime, origSendingTime, applVerID, onBehalfOfCompID, deliverToCompID, some_bind] <;> rfl

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

structure ExecutionReport where
  execID : Terminated 1  -- tag 17
  clOrdID : Terminated 1  -- tag 11
  origClOrdID : Option (Terminated 1)  -- tag 41
  orderID : Terminated 1  -- tag 37
  rFQID : Option (Terminated 1)  -- tag 30006
  execType : Terminated 1  -- tag 150
  execRefID : Option (Terminated 1)  -- tag 19
  execRestatementReason : Option (Terminated 1)  -- tag 378
  ordStatus : Terminated 1  -- tag 39
  ordRejReason : Option (Terminated 1)  -- tag 103
  text : Option (Terminated 1)  -- tag 58
  lastQty : Option (Terminated 1)  -- tag 32
  lastPx : Option (Terminated 1)  -- tag 31
  leavesQty : Terminated 1  -- tag 151
  cumQty : Terminated 1  -- tag 14
  securityID : Terminated 1  -- tag 48
  securityIDSource : Terminated 1  -- tag 22
  account : Option (Terminated 1)  -- tag 1
  noPartyIDs : List NoPartyIDs  -- tag 453
  ordType : Terminated 1  -- tag 40
  preTradeAnonymity : Option (Terminated 1)  -- tag 1091
  timeInForce : Option (Terminated 1)  -- tag 59
  expireTime : Option (Terminated 1)  -- tag 126
  expireDate : Option (Terminated 1)  -- tag 432
  side : Terminated 1  -- tag 54
  orderQty : Terminated 1  -- tag 38
  displayQty : Option (Terminated 1)  -- tag 1138
  displayMethod : Option (Terminated 1)  -- tag 1084
  price : Option (Terminated 1)  -- tag 44
  stopPx : Option (Terminated 1)  -- tag 99
  accountType : Terminated 1  -- tag 581
  orderCapacity : Terminated 1  -- tag 528
  transactTime : Terminated 1  -- tag 60
  secondaryClOrdID : Option (Terminated 1)  -- tag 526
  clOrdLinkID : Option (Terminated 1)  -- tag 583
  tradeLiquidityIndicator : Option (Terminated 1)  -- tag 9730
  tradingSessionID : Option (Terminated 1)  -- tag 336
  tradeMatchID : Option (Terminated 1)  -- tag 880
  typeOfTrade : Option (Terminated 1)  -- tag 20000
  passiveOnlyOrder : Option (Terminated 1)  -- tag 27010
  mDEntryID : Terminated 1  -- tag 278
  avgPx : Option (Terminated 1)  -- tag 6
  minQty : Option (Terminated 1)  -- tag 110
  lastLiquidityInd : Option (Terminated 1)  -- tag 851
  noTrdRegPublications : List NoTrdRegPublications  -- tag 2668
  noOrderAttributes : List NoOrderAttributes  -- tag 2593
  orderOrigination : Option (Terminated 1)  -- tag 1724
  groupID : Terminated 1  -- tag 27017
  contraOrderBook : Option (Terminated 1)  -- tag 33007
  lastMkt : Option (Terminated 1)  -- tag 30
  offset : Option (Terminated 1)  -- tag 27018
  decimalTVTIC : Option (Terminated 1)  -- tag 27020
  trdType : Option (Terminated 1)  -- tag 828
  peggedExecInst : Option (Terminated 1)  -- tag 27021
  ownerType : Option (Terminated 1)  -- tag 522

def ExecutionReport.parts (record : ExecutionReport) : List Part :=
  [Part.required [49, 55] record.execID,
   Part.required [49, 49] record.clOrdID,
   Part.optional [52, 49] record.origClOrdID,
   Part.required [51, 55] record.orderID,
   Part.optional [51, 48, 48, 48, 54] record.rFQID,
   Part.required [49, 53, 48] record.execType,
   Part.optional [49, 57] record.execRefID,
   Part.optional [51, 55, 56] record.execRestatementReason,
   Part.required [51, 57] record.ordStatus,
   Part.optional [49, 48, 51] record.ordRejReason,
   Part.optional [53, 56] record.text,
   Part.optional [51, 50] record.lastQty,
   Part.optional [51, 49] record.lastPx,
   Part.required [49, 53, 49] record.leavesQty,
   Part.required [49, 52] record.cumQty,
   Part.required [52, 56] record.securityID,
   Part.required [50, 50] record.securityIDSource,
   Part.optional [49] record.account,
   Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.required [52, 48] record.ordType,
   Part.optional [49, 48, 57, 49] record.preTradeAnonymity,
   Part.optional [53, 57] record.timeInForce,
   Part.optional [49, 50, 54] record.expireTime,
   Part.optional [52, 51, 50] record.expireDate,
   Part.required [53, 52] record.side,
   Part.required [51, 56] record.orderQty,
   Part.optional [49, 49, 51, 56] record.displayQty,
   Part.optional [49, 48, 56, 52] record.displayMethod,
   Part.optional [52, 52] record.price,
   Part.optional [57, 57] record.stopPx,
   Part.required [53, 56, 49] record.accountType,
   Part.required [53, 50, 56] record.orderCapacity,
   Part.required [54, 48] record.transactTime,
   Part.optional [53, 50, 54] record.secondaryClOrdID,
   Part.optional [53, 56, 51] record.clOrdLinkID,
   Part.optional [57, 55, 51, 48] record.tradeLiquidityIndicator,
   Part.optional [51, 51, 54] record.tradingSessionID,
   Part.optional [56, 56, 48] record.tradeMatchID,
   Part.optional [50, 48, 48, 48, 48] record.typeOfTrade,
   Part.optional [50, 55, 48, 49, 48] record.passiveOnlyOrder,
   Part.required [50, 55, 56] record.mDEntryID,
   Part.optional [54] record.avgPx,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [56, 53, 49] record.lastLiquidityInd,
   Part.group [50, 54, 54, 56] NoTrdRegPublications.members NoTrdRegPublications.encode NoTrdRegPublications.within record.noTrdRegPublications,
   Part.group [50, 53, 57, 51] NoOrderAttributes.members NoOrderAttributes.encode NoOrderAttributes.within record.noOrderAttributes,
   Part.optional [49, 55, 50, 52] record.orderOrigination,
   Part.required [50, 55, 48, 49, 55] record.groupID,
   Part.optional [51, 51, 48, 48, 55] record.contraOrderBook,
   Part.optional [51, 48] record.lastMkt,
   Part.optional [50, 55, 48, 49, 56] record.offset,
   Part.optional [50, 55, 48, 50, 48] record.decimalTVTIC,
   Part.optional [56, 50, 56] record.trdType,
   Part.optional [50, 55, 48, 50, 49] record.peggedExecInst,
   Part.optional [53, 50, 50] record.ownerType]

def ExecutionReport.tags : List (List (List UInt8)) :=
  [[[49, 55]], [[49, 49]], [[52, 49]], [[51, 55]], [[51, 48, 48, 48, 54]], [[49, 53, 48]], [[49, 57]], [[51, 55, 56]], [[51, 57]], [[49, 48, 51]], [[53, 56]], [[51, 50]], [[51, 49]], [[49, 53, 49]], [[49, 52]], [[52, 56]], [[50, 50]], [[49]], [52, 53, 51] :: NoPartyIDs.members, [[52, 48]], [[49, 48, 57, 49]], [[53, 57]], [[49, 50, 54]], [[52, 51, 50]], [[53, 52]], [[51, 56]], [[49, 49, 51, 56]], [[49, 48, 56, 52]], [[52, 52]], [[57, 57]], [[53, 56, 49]], [[53, 50, 56]], [[54, 48]], [[53, 50, 54]], [[53, 56, 51]], [[57, 55, 51, 48]], [[51, 51, 54]], [[56, 56, 48]], [[50, 48, 48, 48, 48]], [[50, 55, 48, 49, 48]], [[50, 55, 56]], [[54]], [[49, 49, 48]], [[56, 53, 49]], [50, 54, 54, 56] :: NoTrdRegPublications.members, [50, 53, 57, 51] :: NoOrderAttributes.members, [[49, 55, 50, 52]], [[50, 55, 48, 49, 55]], [[51, 51, 48, 48, 55]], [[51, 48]], [[50, 55, 48, 49, 56]], [[50, 55, 48, 50, 48]], [[56, 50, 56]], [[50, 55, 48, 50, 49]], [[53, 50, 50]]]

theorem ExecutionReport.shape (record : ExecutionReport) : record.parts.map Part.tags = ExecutionReport.tags := rfl

def ExecutionReport.decode (tokens : List Token) : Option ExecutionReport := do
  let execID ← readRequired [49, 55] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let origClOrdID ← readOptional [52, 49] tokens
  let orderID ← readRequired [51, 55] tokens
  let rFQID ← readOptional [51, 48, 48, 48, 54] tokens
  let execType ← readRequired [49, 53, 48] tokens
  let execRefID ← readOptional [49, 57] tokens
  let execRestatementReason ← readOptional [51, 55, 56] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let ordRejReason ← readOptional [49, 48, 51] tokens
  let text ← readOptional [53, 56] tokens
  let lastQty ← readOptional [51, 50] tokens
  let lastPx ← readOptional [51, 49] tokens
  let leavesQty ← readRequired [49, 53, 49] tokens
  let cumQty ← readRequired [49, 52] tokens
  let securityID ← readRequired [52, 56] tokens
  let securityIDSource ← readRequired [50, 50] tokens
  let account ← readOptional [49] tokens
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let ordType ← readRequired [52, 48] tokens
  let preTradeAnonymity ← readOptional [49, 48, 57, 49] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let expireTime ← readOptional [49, 50, 54] tokens
  let expireDate ← readOptional [52, 51, 50] tokens
  let side ← readRequired [53, 52] tokens
  let orderQty ← readRequired [51, 56] tokens
  let displayQty ← readOptional [49, 49, 51, 56] tokens
  let displayMethod ← readOptional [49, 48, 56, 52] tokens
  let price ← readOptional [52, 52] tokens
  let stopPx ← readOptional [57, 57] tokens
  let accountType ← readRequired [53, 56, 49] tokens
  let orderCapacity ← readRequired [53, 50, 56] tokens
  let transactTime ← readRequired [54, 48] tokens
  let secondaryClOrdID ← readOptional [53, 50, 54] tokens
  let clOrdLinkID ← readOptional [53, 56, 51] tokens
  let tradeLiquidityIndicator ← readOptional [57, 55, 51, 48] tokens
  let tradingSessionID ← readOptional [51, 51, 54] tokens
  let tradeMatchID ← readOptional [56, 56, 48] tokens
  let typeOfTrade ← readOptional [50, 48, 48, 48, 48] tokens
  let passiveOnlyOrder ← readOptional [50, 55, 48, 49, 48] tokens
  let mDEntryID ← readRequired [50, 55, 56] tokens
  let avgPx ← readOptional [54] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let lastLiquidityInd ← readOptional [56, 53, 49] tokens
  let noTrdRegPublications ← readGroup [50, 54, 54, 56] [50, 54, 54, 57] NoTrdRegPublications.members NoTrdRegPublications.decode tokens
  let noOrderAttributes ← readGroup [50, 53, 57, 51] [50, 53, 57, 52] NoOrderAttributes.members NoOrderAttributes.decode tokens
  let orderOrigination ← readOptional [49, 55, 50, 52] tokens
  let groupID ← readRequired [50, 55, 48, 49, 55] tokens
  let contraOrderBook ← readOptional [51, 51, 48, 48, 55] tokens
  let lastMkt ← readOptional [51, 48] tokens
  let offset ← readOptional [50, 55, 48, 49, 56] tokens
  let decimalTVTIC ← readOptional [50, 55, 48, 50, 48] tokens
  let trdType ← readOptional [56, 50, 56] tokens
  let peggedExecInst ← readOptional [50, 55, 48, 50, 49] tokens
  let ownerType ← readOptional [53, 50, 50] tokens
  pure { execID, clOrdID, origClOrdID, orderID, rFQID, execType, execRefID, execRestatementReason, ordStatus, ordRejReason, text, lastQty, lastPx, leavesQty, cumQty, securityID, securityIDSource, account, noPartyIDs, ordType, preTradeAnonymity, timeInForce, expireTime, expireDate, side, orderQty, displayQty, displayMethod, price, stopPx, accountType, orderCapacity, transactTime, secondaryClOrdID, clOrdLinkID, tradeLiquidityIndicator, tradingSessionID, tradeMatchID, typeOfTrade, passiveOnlyOrder, mDEntryID, avgPx, minQty, lastLiquidityInd, noTrdRegPublications, noOrderAttributes, orderOrigination, groupID, contraOrderBook, lastMkt, offset, decimalTVTIC, trdType, peggedExecInst, ownerType }

theorem ExecutionReport.decode_agrees (record : ExecutionReport) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReport.decode tokens = some record := by
  have distinct : ExecutionReport.tags.flatten.Nodup := by decide +kernel
  have execID := readRequired_part [49, 55] record.execID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have rFQID := readOptional_part [51, 48, 48, 48, 54] record.rFQID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have execType := readRequired_part [49, 53, 48] record.execType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have execRefID := readOptional_part [49, 57] record.execRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have execRestatementReason := readOptional_part [51, 55, 56] record.execRestatementReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have ordRejReason := readOptional_part [49, 48, 51] record.ordRejReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have lastQty := readOptional_part [51, 50] record.lastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have lastPx := readOptional_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have leavesQty := readRequired_part [49, 53, 49] record.leavesQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have cumQty := readRequired_part [49, 52] record.cumQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have securityID := readRequired_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have securityIDSource := readRequired_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have preTradeAnonymity := readOptional_part [49, 48, 57, 49] record.preTradeAnonymity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have expireTime := readOptional_part [49, 50, 54] record.expireTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have expireDate := readOptional_part [52, 51, 50] record.expireDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have displayQty := readOptional_part [49, 49, 51, 56] record.displayQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have displayMethod := readOptional_part [49, 48, 56, 52] record.displayMethod tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have stopPx := readOptional_part [57, 57] record.stopPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have accountType := readRequired_part [53, 56, 49] record.accountType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have orderCapacity := readRequired_part [53, 50, 56] record.orderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have secondaryClOrdID := readOptional_part [53, 50, 54] record.secondaryClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have clOrdLinkID := readOptional_part [53, 56, 51] record.clOrdLinkID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have tradeLiquidityIndicator := readOptional_part [57, 55, 51, 48] record.tradeLiquidityIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have tradingSessionID := readOptional_part [51, 51, 54] record.tradingSessionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have tradeMatchID := readOptional_part [56, 56, 48] record.tradeMatchID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have typeOfTrade := readOptional_part [50, 48, 48, 48, 48] record.typeOfTrade tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  have passiveOnlyOrder := readOptional_part [50, 55, 48, 49, 48] record.passiveOnlyOrder tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 39 (by decide +kernel)))
  have mDEntryID := readRequired_part [50, 55, 56] record.mDEntryID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 40 (by decide +kernel)))
  have avgPx := readOptional_part [54] record.avgPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 41 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 42 (by decide +kernel)))
  have lastLiquidityInd := readOptional_part [56, 53, 49] record.lastLiquidityInd tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 43 (by decide +kernel)))
  have noTrdRegPublications := readGroup_part [50, 54, 54, 56] [50, 54, 54, 57] NoTrdRegPublications.members NoTrdRegPublications.encode NoTrdRegPublications.within NoTrdRegPublications.decode NoTrdRegPublications.decode_encode NoTrdRegPublications.led record.noTrdRegPublications tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 44 (by decide +kernel)))
  have noOrderAttributes := readGroup_part [50, 53, 57, 51] [50, 53, 57, 52] NoOrderAttributes.members NoOrderAttributes.encode NoOrderAttributes.within NoOrderAttributes.decode NoOrderAttributes.decode_encode NoOrderAttributes.led record.noOrderAttributes tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 45 (by decide +kernel)))
  have orderOrigination := readOptional_part [49, 55, 50, 52] record.orderOrigination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 46 (by decide +kernel)))
  have groupID := readRequired_part [50, 55, 48, 49, 55] record.groupID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 47 (by decide +kernel)))
  have contraOrderBook := readOptional_part [51, 51, 48, 48, 55] record.contraOrderBook tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 48 (by decide +kernel)))
  have lastMkt := readOptional_part [51, 48] record.lastMkt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 49 (by decide +kernel)))
  have offset := readOptional_part [50, 55, 48, 49, 56] record.offset tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 50 (by decide +kernel)))
  have decimalTVTIC := readOptional_part [50, 55, 48, 50, 48] record.decimalTVTIC tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 51 (by decide +kernel)))
  have trdType := readOptional_part [56, 50, 56] record.trdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 52 (by decide +kernel)))
  have peggedExecInst := readOptional_part [50, 55, 48, 50, 49] record.peggedExecInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 53 (by decide +kernel)))
  have ownerType := readOptional_part [53, 50, 50] record.ownerType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 54 (by decide +kernel)))
  simp only [ExecutionReport.decode, execID, clOrdID, origClOrdID, orderID, rFQID, execType, execRefID, execRestatementReason, ordStatus, ordRejReason, text, lastQty, lastPx, leavesQty, cumQty, securityID, securityIDSource, account, noPartyIDs, ordType, preTradeAnonymity, timeInForce, expireTime, expireDate, side, orderQty, displayQty, displayMethod, price, stopPx, accountType, orderCapacity, transactTime, secondaryClOrdID, clOrdLinkID, tradeLiquidityIndicator, tradingSessionID, tradeMatchID, typeOfTrade, passiveOnlyOrder, mDEntryID, avgPx, minQty, lastLiquidityInd, noTrdRegPublications, noOrderAttributes, orderOrigination, groupID, contraOrderBook, lastMkt, offset, decimalTVTIC, trdType, peggedExecInst, ownerType, some_bind] <;> rfl

structure OrderCancelReject where
  clOrdID : Terminated 1  -- tag 11
  origClOrdID : Option (Terminated 1)  -- tag 41
  orderID : Terminated 1  -- tag 37
  ordStatus : Terminated 1  -- tag 39
  cxlRejResponseTo : Terminated 1  -- tag 434
  cxlRejReason : Terminated 1  -- tag 102
  text : Option (Terminated 1)  -- tag 58

def OrderCancelReject.parts (record : OrderCancelReject) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.optional [52, 49] record.origClOrdID,
   Part.required [51, 55] record.orderID,
   Part.required [51, 57] record.ordStatus,
   Part.required [52, 51, 52] record.cxlRejResponseTo,
   Part.required [49, 48, 50] record.cxlRejReason,
   Part.optional [53, 56] record.text]

def OrderCancelReject.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[52, 49]], [[51, 55]], [[51, 57]], [[52, 51, 52]], [[49, 48, 50]], [[53, 56]]]

theorem OrderCancelReject.shape (record : OrderCancelReject) : record.parts.map Part.tags = OrderCancelReject.tags := rfl

def OrderCancelReject.decode (tokens : List Token) : Option OrderCancelReject := do
  let clOrdID ← readRequired [49, 49] tokens
  let origClOrdID ← readOptional [52, 49] tokens
  let orderID ← readRequired [51, 55] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let cxlRejResponseTo ← readRequired [52, 51, 52] tokens
  let cxlRejReason ← readRequired [49, 48, 50] tokens
  let text ← readOptional [53, 56] tokens
  pure { clOrdID, origClOrdID, orderID, ordStatus, cxlRejResponseTo, cxlRejReason, text }

theorem OrderCancelReject.decode_agrees (record : OrderCancelReject) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelReject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelReject.decode tokens = some record := by
  have distinct : OrderCancelReject.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have cxlRejResponseTo := readRequired_part [52, 51, 52] record.cxlRejResponseTo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have cxlRejReason := readRequired_part [49, 48, 50] record.cxlRejReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  simp only [OrderCancelReject.decode, clOrdID, origClOrdID, orderID, ordStatus, cxlRejResponseTo, cxlRejReason, text, some_bind] <;> rfl

structure OrderMassCancelReport where
  massActionReportID : Terminated 1  -- tag 1369
  clOrdID : Terminated 1  -- tag 11
  massCancelRequestType : Terminated 1  -- tag 530
  massCancelResponse : Terminated 1  -- tag 531
  massCancelRejectReason : Option (Terminated 1)  -- tag 532
  applID : Terminated 1  -- tag 1180

def OrderMassCancelReport.parts (record : OrderMassCancelReport) : List Part :=
  [Part.required [49, 51, 54, 57] record.massActionReportID,
   Part.required [49, 49] record.clOrdID,
   Part.required [53, 51, 48] record.massCancelRequestType,
   Part.required [53, 51, 49] record.massCancelResponse,
   Part.optional [53, 51, 50] record.massCancelRejectReason,
   Part.required [49, 49, 56, 48] record.applID]

def OrderMassCancelReport.tags : List (List (List UInt8)) :=
  [[[49, 51, 54, 57]], [[49, 49]], [[53, 51, 48]], [[53, 51, 49]], [[53, 51, 50]], [[49, 49, 56, 48]]]

theorem OrderMassCancelReport.shape (record : OrderMassCancelReport) : record.parts.map Part.tags = OrderMassCancelReport.tags := rfl

def OrderMassCancelReport.decode (tokens : List Token) : Option OrderMassCancelReport := do
  let massActionReportID ← readRequired [49, 51, 54, 57] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let massCancelRequestType ← readRequired [53, 51, 48] tokens
  let massCancelResponse ← readRequired [53, 51, 49] tokens
  let massCancelRejectReason ← readOptional [53, 51, 50] tokens
  let applID ← readRequired [49, 49, 56, 48] tokens
  pure { massActionReportID, clOrdID, massCancelRequestType, massCancelResponse, massCancelRejectReason, applID }

theorem OrderMassCancelReport.decode_agrees (record : OrderMassCancelReport) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderMassCancelReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderMassCancelReport.decode tokens = some record := by
  have distinct : OrderMassCancelReport.tags.flatten.Nodup := by decide +kernel
  have massActionReportID := readRequired_part [49, 51, 54, 57] record.massActionReportID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have massCancelRequestType := readRequired_part [53, 51, 48] record.massCancelRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have massCancelResponse := readRequired_part [53, 51, 49] record.massCancelResponse tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have massCancelRejectReason := readOptional_part [53, 51, 50] record.massCancelRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have applID := readRequired_part [49, 49, 56, 48] record.applID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  simp only [OrderMassCancelReport.decode, massActionReportID, clOrdID, massCancelRequestType, massCancelResponse, massCancelRejectReason, applID, some_bind] <;> rfl

structure Quote where
  quoteMsgID : Terminated 1  -- tag 1166
  quoteID : Terminated 1  -- tag 117
  rFQID : Option (Terminated 1)  -- tag 30006
  bidID : Option (Terminated 1)  -- tag 30007
  offerID : Option (Terminated 1)  -- tag 30008
  privateQuote : Option (Terminated 1)  -- tag 1171
  quoteType : Option (Terminated 1)  -- tag 537
  securityID : Terminated 1  -- tag 48
  securityIDSource : Terminated 1  -- tag 22
  noPartyIDs : List NoPartyIDs  -- tag 453
  bidPx : Option (Terminated 1)  -- tag 132
  bidSize : Option (Terminated 1)  -- tag 134
  offerPx : Option (Terminated 1)  -- tag 133
  offerSize : Option (Terminated 1)  -- tag 135
  accountType : Terminated 1  -- tag 581
  orderCapacity : Option (Terminated 1)  -- tag 528
  noOrderAttributes : List NoOrderAttributes  -- tag 2593
  orderOrigination : Option (Terminated 1)  -- tag 1724
  peggedExecInst : Option (Terminated 1)  -- tag 27021

def Quote.parts (record : Quote) : List Part :=
  [Part.required [49, 49, 54, 54] record.quoteMsgID,
   Part.required [49, 49, 55] record.quoteID,
   Part.optional [51, 48, 48, 48, 54] record.rFQID,
   Part.optional [51, 48, 48, 48, 55] record.bidID,
   Part.optional [51, 48, 48, 48, 56] record.offerID,
   Part.optional [49, 49, 55, 49] record.privateQuote,
   Part.optional [53, 51, 55] record.quoteType,
   Part.required [52, 56] record.securityID,
   Part.required [50, 50] record.securityIDSource,
   Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.optional [49, 51, 50] record.bidPx,
   Part.optional [49, 51, 52] record.bidSize,
   Part.optional [49, 51, 51] record.offerPx,
   Part.optional [49, 51, 53] record.offerSize,
   Part.required [53, 56, 49] record.accountType,
   Part.optional [53, 50, 56] record.orderCapacity,
   Part.group [50, 53, 57, 51] NoOrderAttributes.members NoOrderAttributes.encode NoOrderAttributes.within record.noOrderAttributes,
   Part.optional [49, 55, 50, 52] record.orderOrigination,
   Part.optional [50, 55, 48, 50, 49] record.peggedExecInst]

def Quote.tags : List (List (List UInt8)) :=
  [[[49, 49, 54, 54]], [[49, 49, 55]], [[51, 48, 48, 48, 54]], [[51, 48, 48, 48, 55]], [[51, 48, 48, 48, 56]], [[49, 49, 55, 49]], [[53, 51, 55]], [[52, 56]], [[50, 50]], [52, 53, 51] :: NoPartyIDs.members, [[49, 51, 50]], [[49, 51, 52]], [[49, 51, 51]], [[49, 51, 53]], [[53, 56, 49]], [[53, 50, 56]], [50, 53, 57, 51] :: NoOrderAttributes.members, [[49, 55, 50, 52]], [[50, 55, 48, 50, 49]]]

theorem Quote.shape (record : Quote) : record.parts.map Part.tags = Quote.tags := rfl

def Quote.decode (tokens : List Token) : Option Quote := do
  let quoteMsgID ← readRequired [49, 49, 54, 54] tokens
  let quoteID ← readRequired [49, 49, 55] tokens
  let rFQID ← readOptional [51, 48, 48, 48, 54] tokens
  let bidID ← readOptional [51, 48, 48, 48, 55] tokens
  let offerID ← readOptional [51, 48, 48, 48, 56] tokens
  let privateQuote ← readOptional [49, 49, 55, 49] tokens
  let quoteType ← readOptional [53, 51, 55] tokens
  let securityID ← readRequired [52, 56] tokens
  let securityIDSource ← readRequired [50, 50] tokens
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let bidPx ← readOptional [49, 51, 50] tokens
  let bidSize ← readOptional [49, 51, 52] tokens
  let offerPx ← readOptional [49, 51, 51] tokens
  let offerSize ← readOptional [49, 51, 53] tokens
  let accountType ← readRequired [53, 56, 49] tokens
  let orderCapacity ← readOptional [53, 50, 56] tokens
  let noOrderAttributes ← readGroup [50, 53, 57, 51] [50, 53, 57, 52] NoOrderAttributes.members NoOrderAttributes.decode tokens
  let orderOrigination ← readOptional [49, 55, 50, 52] tokens
  let peggedExecInst ← readOptional [50, 55, 48, 50, 49] tokens
  pure { quoteMsgID, quoteID, rFQID, bidID, offerID, privateQuote, quoteType, securityID, securityIDSource, noPartyIDs, bidPx, bidSize, offerPx, offerSize, accountType, orderCapacity, noOrderAttributes, orderOrigination, peggedExecInst }

theorem Quote.decode_agrees (record : Quote) (tokens : List Token)
    (agrees : ∀ tags ∈ Quote.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Quote.decode tokens = some record := by
  have distinct : Quote.tags.flatten.Nodup := by decide +kernel
  have quoteMsgID := readRequired_part [49, 49, 54, 54] record.quoteMsgID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have quoteID := readRequired_part [49, 49, 55] record.quoteID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have rFQID := readOptional_part [51, 48, 48, 48, 54] record.rFQID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have bidID := readOptional_part [51, 48, 48, 48, 55] record.bidID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have offerID := readOptional_part [51, 48, 48, 48, 56] record.offerID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have privateQuote := readOptional_part [49, 49, 55, 49] record.privateQuote tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have quoteType := readOptional_part [53, 51, 55] record.quoteType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have securityID := readRequired_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have securityIDSource := readRequired_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have bidPx := readOptional_part [49, 51, 50] record.bidPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have bidSize := readOptional_part [49, 51, 52] record.bidSize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have offerPx := readOptional_part [49, 51, 51] record.offerPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have offerSize := readOptional_part [49, 51, 53] record.offerSize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have accountType := readRequired_part [53, 56, 49] record.accountType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have orderCapacity := readOptional_part [53, 50, 56] record.orderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have noOrderAttributes := readGroup_part [50, 53, 57, 51] [50, 53, 57, 52] NoOrderAttributes.members NoOrderAttributes.encode NoOrderAttributes.within NoOrderAttributes.decode NoOrderAttributes.decode_encode NoOrderAttributes.led record.noOrderAttributes tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have orderOrigination := readOptional_part [49, 55, 50, 52] record.orderOrigination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have peggedExecInst := readOptional_part [50, 55, 48, 50, 49] record.peggedExecInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  simp only [Quote.decode, quoteMsgID, quoteID, rFQID, bidID, offerID, privateQuote, quoteType, securityID, securityIDSource, noPartyIDs, bidPx, bidSize, offerPx, offerSize, accountType, orderCapacity, noOrderAttributes, orderOrigination, peggedExecInst, some_bind] <;> rfl

structure QuoteStatusReport where
  quoteMsgID : Terminated 1  -- tag 1166
  quoteReqID : Option (Terminated 1)  -- tag 131
  rFQID : Option (Terminated 1)  -- tag 30006
  bidID : Option (Terminated 1)  -- tag 30007
  offerID : Option (Terminated 1)  -- tag 30008
  quoteCancelType : Option (Terminated 1)  -- tag 298
  noPartyIDs : List NoPartyIDs  -- tag 453
  quoteType : Option (Terminated 1)  -- tag 537
  quoteStatus : Terminated 1  -- tag 297
  quoteRejectReason : Option (Terminated 1)  -- tag 300
  text : Option (Terminated 1)  -- tag 58
  expireTime : Option (Terminated 1)  -- tag 126
  noOrderAttributes : List NoOrderAttributes  -- tag 2593
  orderOrigination : Option (Terminated 1)  -- tag 1724

def QuoteStatusReport.parts (record : QuoteStatusReport) : List Part :=
  [Part.required [49, 49, 54, 54] record.quoteMsgID,
   Part.optional [49, 51, 49] record.quoteReqID,
   Part.optional [51, 48, 48, 48, 54] record.rFQID,
   Part.optional [51, 48, 48, 48, 55] record.bidID,
   Part.optional [51, 48, 48, 48, 56] record.offerID,
   Part.optional [50, 57, 56] record.quoteCancelType,
   Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.optional [53, 51, 55] record.quoteType,
   Part.required [50, 57, 55] record.quoteStatus,
   Part.optional [51, 48, 48] record.quoteRejectReason,
   Part.optional [53, 56] record.text,
   Part.optional [49, 50, 54] record.expireTime,
   Part.group [50, 53, 57, 51] NoOrderAttributes.members NoOrderAttributes.encode NoOrderAttributes.within record.noOrderAttributes,
   Part.optional [49, 55, 50, 52] record.orderOrigination]

def QuoteStatusReport.tags : List (List (List UInt8)) :=
  [[[49, 49, 54, 54]], [[49, 51, 49]], [[51, 48, 48, 48, 54]], [[51, 48, 48, 48, 55]], [[51, 48, 48, 48, 56]], [[50, 57, 56]], [52, 53, 51] :: NoPartyIDs.members, [[53, 51, 55]], [[50, 57, 55]], [[51, 48, 48]], [[53, 56]], [[49, 50, 54]], [50, 53, 57, 51] :: NoOrderAttributes.members, [[49, 55, 50, 52]]]

theorem QuoteStatusReport.shape (record : QuoteStatusReport) : record.parts.map Part.tags = QuoteStatusReport.tags := rfl

def QuoteStatusReport.decode (tokens : List Token) : Option QuoteStatusReport := do
  let quoteMsgID ← readRequired [49, 49, 54, 54] tokens
  let quoteReqID ← readOptional [49, 51, 49] tokens
  let rFQID ← readOptional [51, 48, 48, 48, 54] tokens
  let bidID ← readOptional [51, 48, 48, 48, 55] tokens
  let offerID ← readOptional [51, 48, 48, 48, 56] tokens
  let quoteCancelType ← readOptional [50, 57, 56] tokens
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let quoteType ← readOptional [53, 51, 55] tokens
  let quoteStatus ← readRequired [50, 57, 55] tokens
  let quoteRejectReason ← readOptional [51, 48, 48] tokens
  let text ← readOptional [53, 56] tokens
  let expireTime ← readOptional [49, 50, 54] tokens
  let noOrderAttributes ← readGroup [50, 53, 57, 51] [50, 53, 57, 52] NoOrderAttributes.members NoOrderAttributes.decode tokens
  let orderOrigination ← readOptional [49, 55, 50, 52] tokens
  pure { quoteMsgID, quoteReqID, rFQID, bidID, offerID, quoteCancelType, noPartyIDs, quoteType, quoteStatus, quoteRejectReason, text, expireTime, noOrderAttributes, orderOrigination }

theorem QuoteStatusReport.decode_agrees (record : QuoteStatusReport) (tokens : List Token)
    (agrees : ∀ tags ∈ QuoteStatusReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    QuoteStatusReport.decode tokens = some record := by
  have distinct : QuoteStatusReport.tags.flatten.Nodup := by decide +kernel
  have quoteMsgID := readRequired_part [49, 49, 54, 54] record.quoteMsgID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have quoteReqID := readOptional_part [49, 51, 49] record.quoteReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have rFQID := readOptional_part [51, 48, 48, 48, 54] record.rFQID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have bidID := readOptional_part [51, 48, 48, 48, 55] record.bidID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have offerID := readOptional_part [51, 48, 48, 48, 56] record.offerID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have quoteCancelType := readOptional_part [50, 57, 56] record.quoteCancelType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have quoteType := readOptional_part [53, 51, 55] record.quoteType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have quoteStatus := readRequired_part [50, 57, 55] record.quoteStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have quoteRejectReason := readOptional_part [51, 48, 48] record.quoteRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have expireTime := readOptional_part [49, 50, 54] record.expireTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have noOrderAttributes := readGroup_part [50, 53, 57, 51] [50, 53, 57, 52] NoOrderAttributes.members NoOrderAttributes.encode NoOrderAttributes.within NoOrderAttributes.decode NoOrderAttributes.decode_encode NoOrderAttributes.led record.noOrderAttributes tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have orderOrigination := readOptional_part [49, 55, 50, 52] record.orderOrigination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  simp only [QuoteStatusReport.decode, quoteMsgID, quoteReqID, rFQID, bidID, offerID, quoteCancelType, noPartyIDs, quoteType, quoteStatus, quoteRejectReason, text, expireTime, noOrderAttributes, orderOrigination, some_bind] <;> rfl

structure NoQuoteEntries where
  quoteEntryID : Terminated 1  -- tag 299
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22
  quoteEntryStatus : Option (Terminated 1)  -- tag 1167
  quoteEntryRejectReason : Option (Terminated 1)  -- tag 368

def NoQuoteEntries.parts (record : NoQuoteEntries) : List Part :=
  [Part.required [50, 57, 57] record.quoteEntryID,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource,
   Part.optional [49, 49, 54, 55] record.quoteEntryStatus,
   Part.optional [51, 54, 56] record.quoteEntryRejectReason]

def NoQuoteEntries.tags : List (List (List UInt8)) :=
  [[[50, 57, 57]], [[52, 56]], [[50, 50]], [[49, 49, 54, 55]], [[51, 54, 56]]]

theorem NoQuoteEntries.shape (record : NoQuoteEntries) : record.parts.map Part.tags = NoQuoteEntries.tags := rfl

def NoQuoteEntries.decode (tokens : List Token) : Option NoQuoteEntries := do
  let quoteEntryID ← readRequired [50, 57, 57] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let quoteEntryStatus ← readOptional [49, 49, 54, 55] tokens
  let quoteEntryRejectReason ← readOptional [51, 54, 56] tokens
  pure { quoteEntryID, securityID, securityIDSource, quoteEntryStatus, quoteEntryRejectReason }

theorem NoQuoteEntries.decode_agrees (record : NoQuoteEntries) (tokens : List Token)
    (agrees : ∀ tags ∈ NoQuoteEntries.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoQuoteEntries.decode tokens = some record := by
  have distinct : NoQuoteEntries.tags.flatten.Nodup := by decide +kernel
  have quoteEntryID := readRequired_part [50, 57, 57] record.quoteEntryID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have quoteEntryStatus := readOptional_part [49, 49, 54, 55] record.quoteEntryStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have quoteEntryRejectReason := readOptional_part [51, 54, 56] record.quoteEntryRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [NoQuoteEntries.decode, quoteEntryID, securityID, securityIDSource, quoteEntryStatus, quoteEntryRejectReason, some_bind] <;> rfl

def NoQuoteEntries.members : List (List UInt8) := NoQuoteEntries.tags.flatten

def NoQuoteEntries.encode (entry : NoQuoteEntries) : List Token := encodeParts entry.parts

theorem NoQuoteEntries.decode_encode (entry : NoQuoteEntries) : NoQuoteEntries.decode entry.encode = some entry :=
  NoQuoteEntries.decode_agrees entry _ (fun _ _ => rfl)

theorem NoQuoteEntries.within (entry : NoQuoteEntries) : ∀ token ∈ entry.encode, token.tag ∈ NoQuoteEntries.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoQuoteEntries.shape] at this

theorem NoQuoteEntries.led (entry : NoQuoteEntries) : Lead [50, 57, 57] entry.encode :=
  lead_parts [50, 57, 57] entry.quoteEntryID _ NoQuoteEntries.tags.tail rfl (by decide +kernel)

structure NoQuoteSets where
  quoteSetID : Terminated 1  -- tag 302
  noQuoteEntries : List NoQuoteEntries  -- tag 295

def NoQuoteSets.parts (record : NoQuoteSets) : List Part :=
  [Part.required [51, 48, 50] record.quoteSetID,
   Part.group [50, 57, 53] NoQuoteEntries.members NoQuoteEntries.encode NoQuoteEntries.within record.noQuoteEntries]

def NoQuoteSets.tags : List (List (List UInt8)) :=
  [[[51, 48, 50]], [50, 57, 53] :: NoQuoteEntries.members]

theorem NoQuoteSets.shape (record : NoQuoteSets) : record.parts.map Part.tags = NoQuoteSets.tags := rfl

def NoQuoteSets.decode (tokens : List Token) : Option NoQuoteSets := do
  let quoteSetID ← readRequired [51, 48, 50] tokens
  let noQuoteEntries ← readGroup [50, 57, 53] [50, 57, 57] NoQuoteEntries.members NoQuoteEntries.decode tokens
  pure { quoteSetID, noQuoteEntries }

theorem NoQuoteSets.decode_agrees (record : NoQuoteSets) (tokens : List Token)
    (agrees : ∀ tags ∈ NoQuoteSets.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoQuoteSets.decode tokens = some record := by
  have distinct : NoQuoteSets.tags.flatten.Nodup := by decide +kernel
  have quoteSetID := readRequired_part [51, 48, 50] record.quoteSetID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have noQuoteEntries := readGroup_part [50, 57, 53] [50, 57, 57] NoQuoteEntries.members NoQuoteEntries.encode NoQuoteEntries.within NoQuoteEntries.decode NoQuoteEntries.decode_encode NoQuoteEntries.led record.noQuoteEntries tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [NoQuoteSets.decode, quoteSetID, noQuoteEntries, some_bind] <;> rfl

def NoQuoteSets.members : List (List UInt8) := NoQuoteSets.tags.flatten

def NoQuoteSets.encode (entry : NoQuoteSets) : List Token := encodeParts entry.parts

theorem NoQuoteSets.decode_encode (entry : NoQuoteSets) : NoQuoteSets.decode entry.encode = some entry :=
  NoQuoteSets.decode_agrees entry _ (fun _ _ => rfl)

theorem NoQuoteSets.within (entry : NoQuoteSets) : ∀ token ∈ entry.encode, token.tag ∈ NoQuoteSets.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoQuoteSets.shape] at this

theorem NoQuoteSets.led (entry : NoQuoteSets) : Lead [51, 48, 50] entry.encode :=
  lead_parts [51, 48, 50] entry.quoteSetID _ NoQuoteSets.tags.tail rfl (by decide +kernel)

structure MassQuoteAcknowledgement where
  applID : Option (Terminated 1)  -- tag 1180
  quoteID : Terminated 1  -- tag 117
  quoteCancelType : Option (Terminated 1)  -- tag 298
  quoteStatus : Terminated 1  -- tag 297
  quoteRejectReason : Option (Terminated 1)  -- tag 300
  text : Option (Terminated 1)  -- tag 58
  noQuoteSets : List NoQuoteSets  -- tag 296

def MassQuoteAcknowledgement.parts (record : MassQuoteAcknowledgement) : List Part :=
  [Part.optional [49, 49, 56, 48] record.applID,
   Part.required [49, 49, 55] record.quoteID,
   Part.optional [50, 57, 56] record.quoteCancelType,
   Part.required [50, 57, 55] record.quoteStatus,
   Part.optional [51, 48, 48] record.quoteRejectReason,
   Part.optional [53, 56] record.text,
   Part.group [50, 57, 54] NoQuoteSets.members NoQuoteSets.encode NoQuoteSets.within record.noQuoteSets]

def MassQuoteAcknowledgement.tags : List (List (List UInt8)) :=
  [[[49, 49, 56, 48]], [[49, 49, 55]], [[50, 57, 56]], [[50, 57, 55]], [[51, 48, 48]], [[53, 56]], [50, 57, 54] :: NoQuoteSets.members]

theorem MassQuoteAcknowledgement.shape (record : MassQuoteAcknowledgement) : record.parts.map Part.tags = MassQuoteAcknowledgement.tags := rfl

def MassQuoteAcknowledgement.decode (tokens : List Token) : Option MassQuoteAcknowledgement := do
  let applID ← readOptional [49, 49, 56, 48] tokens
  let quoteID ← readRequired [49, 49, 55] tokens
  let quoteCancelType ← readOptional [50, 57, 56] tokens
  let quoteStatus ← readRequired [50, 57, 55] tokens
  let quoteRejectReason ← readOptional [51, 48, 48] tokens
  let text ← readOptional [53, 56] tokens
  let noQuoteSets ← readGroup [50, 57, 54] [51, 48, 50] NoQuoteSets.members NoQuoteSets.decode tokens
  pure { applID, quoteID, quoteCancelType, quoteStatus, quoteRejectReason, text, noQuoteSets }

theorem MassQuoteAcknowledgement.decode_agrees (record : MassQuoteAcknowledgement) (tokens : List Token)
    (agrees : ∀ tags ∈ MassQuoteAcknowledgement.tags, select tags tokens = select tags (encodeParts record.parts)) :
    MassQuoteAcknowledgement.decode tokens = some record := by
  have distinct : MassQuoteAcknowledgement.tags.flatten.Nodup := by decide +kernel
  have applID := readOptional_part [49, 49, 56, 48] record.applID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have quoteID := readRequired_part [49, 49, 55] record.quoteID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have quoteCancelType := readOptional_part [50, 57, 56] record.quoteCancelType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have quoteStatus := readRequired_part [50, 57, 55] record.quoteStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have quoteRejectReason := readOptional_part [51, 48, 48] record.quoteRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have noQuoteSets := readGroup_part [50, 57, 54] [51, 48, 50] NoQuoteSets.members NoQuoteSets.encode NoQuoteSets.within NoQuoteSets.decode NoQuoteSets.decode_encode NoQuoteSets.led record.noQuoteSets tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  simp only [MassQuoteAcknowledgement.decode, applID, quoteID, quoteCancelType, quoteStatus, quoteRejectReason, text, noQuoteSets, some_bind] <;> rfl

structure NoRelatedSym where
  securityID : Terminated 1  -- tag 48
  securityIDSource : Terminated 1  -- tag 22
  side : Option (Terminated 1)  -- tag 54
  orderQty : Terminated 1  -- tag 38
  quoteRequestType : Option (Terminated 1)  -- tag 303
  price : Option (Terminated 1)  -- tag 44
  accountType : Option (Terminated 1)  -- tag 581
  rFQExecutionDelay : Option (Terminated 1)  -- tag 33001
  rFQMinQuotes : Option (Terminated 1)  -- tag 33002
  rFQDiscloseSide : Option (Terminated 1)  -- tag 33004
  noPartyIDs : List NoPartyIDs  -- tag 453
  marketMakerRank : Option (Terminated 1)  -- tag 27019
  autoRFQExecStrategy : Option (Terminated 1)  -- tag 33006
  numOfCompetitors : Option (Terminated 1)  -- tag 1913

def NoRelatedSym.parts (record : NoRelatedSym) : List Part :=
  [Part.required [52, 56] record.securityID,
   Part.required [50, 50] record.securityIDSource,
   Part.optional [53, 52] record.side,
   Part.required [51, 56] record.orderQty,
   Part.optional [51, 48, 51] record.quoteRequestType,
   Part.optional [52, 52] record.price,
   Part.optional [53, 56, 49] record.accountType,
   Part.optional [51, 51, 48, 48, 49] record.rFQExecutionDelay,
   Part.optional [51, 51, 48, 48, 50] record.rFQMinQuotes,
   Part.optional [51, 51, 48, 48, 52] record.rFQDiscloseSide,
   Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.optional [50, 55, 48, 49, 57] record.marketMakerRank,
   Part.optional [51, 51, 48, 48, 54] record.autoRFQExecStrategy,
   Part.optional [49, 57, 49, 51] record.numOfCompetitors]

def NoRelatedSym.tags : List (List (List UInt8)) :=
  [[[52, 56]], [[50, 50]], [[53, 52]], [[51, 56]], [[51, 48, 51]], [[52, 52]], [[53, 56, 49]], [[51, 51, 48, 48, 49]], [[51, 51, 48, 48, 50]], [[51, 51, 48, 48, 52]], [52, 53, 51] :: NoPartyIDs.members, [[50, 55, 48, 49, 57]], [[51, 51, 48, 48, 54]], [[49, 57, 49, 51]]]

theorem NoRelatedSym.shape (record : NoRelatedSym) : record.parts.map Part.tags = NoRelatedSym.tags := rfl

def NoRelatedSym.decode (tokens : List Token) : Option NoRelatedSym := do
  let securityID ← readRequired [52, 56] tokens
  let securityIDSource ← readRequired [50, 50] tokens
  let side ← readOptional [53, 52] tokens
  let orderQty ← readRequired [51, 56] tokens
  let quoteRequestType ← readOptional [51, 48, 51] tokens
  let price ← readOptional [52, 52] tokens
  let accountType ← readOptional [53, 56, 49] tokens
  let rFQExecutionDelay ← readOptional [51, 51, 48, 48, 49] tokens
  let rFQMinQuotes ← readOptional [51, 51, 48, 48, 50] tokens
  let rFQDiscloseSide ← readOptional [51, 51, 48, 48, 52] tokens
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let marketMakerRank ← readOptional [50, 55, 48, 49, 57] tokens
  let autoRFQExecStrategy ← readOptional [51, 51, 48, 48, 54] tokens
  let numOfCompetitors ← readOptional [49, 57, 49, 51] tokens
  pure { securityID, securityIDSource, side, orderQty, quoteRequestType, price, accountType, rFQExecutionDelay, rFQMinQuotes, rFQDiscloseSide, noPartyIDs, marketMakerRank, autoRFQExecStrategy, numOfCompetitors }

theorem NoRelatedSym.decode_agrees (record : NoRelatedSym) (tokens : List Token)
    (agrees : ∀ tags ∈ NoRelatedSym.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoRelatedSym.decode tokens = some record := by
  have distinct : NoRelatedSym.tags.flatten.Nodup := by decide +kernel
  have securityID := readRequired_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityIDSource := readRequired_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have quoteRequestType := readOptional_part [51, 48, 51] record.quoteRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have accountType := readOptional_part [53, 56, 49] record.accountType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have rFQExecutionDelay := readOptional_part [51, 51, 48, 48, 49] record.rFQExecutionDelay tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have rFQMinQuotes := readOptional_part [51, 51, 48, 48, 50] record.rFQMinQuotes tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have rFQDiscloseSide := readOptional_part [51, 51, 48, 48, 52] record.rFQDiscloseSide tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have marketMakerRank := readOptional_part [50, 55, 48, 49, 57] record.marketMakerRank tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have autoRFQExecStrategy := readOptional_part [51, 51, 48, 48, 54] record.autoRFQExecStrategy tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have numOfCompetitors := readOptional_part [49, 57, 49, 51] record.numOfCompetitors tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  simp only [NoRelatedSym.decode, securityID, securityIDSource, side, orderQty, quoteRequestType, price, accountType, rFQExecutionDelay, rFQMinQuotes, rFQDiscloseSide, noPartyIDs, marketMakerRank, autoRFQExecStrategy, numOfCompetitors, some_bind] <;> rfl

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

structure QuoteRequest where
  quoteReqID : Terminated 1  -- tag 131
  rFQID : Option (Terminated 1)  -- tag 30006
  privateQuote : Terminated 1  -- tag 1171
  orderBook : Terminated 1  -- tag 30001
  expireTime : Option (Terminated 1)  -- tag 126
  orderCapacity : Terminated 1  -- tag 528
  noRelatedSym : List NoRelatedSym  -- tag 146

def QuoteRequest.parts (record : QuoteRequest) : List Part :=
  [Part.required [49, 51, 49] record.quoteReqID,
   Part.optional [51, 48, 48, 48, 54] record.rFQID,
   Part.required [49, 49, 55, 49] record.privateQuote,
   Part.required [51, 48, 48, 48, 49] record.orderBook,
   Part.optional [49, 50, 54] record.expireTime,
   Part.required [53, 50, 56] record.orderCapacity,
   Part.group [49, 52, 54] NoRelatedSym.members NoRelatedSym.encode NoRelatedSym.within record.noRelatedSym]

def QuoteRequest.tags : List (List (List UInt8)) :=
  [[[49, 51, 49]], [[51, 48, 48, 48, 54]], [[49, 49, 55, 49]], [[51, 48, 48, 48, 49]], [[49, 50, 54]], [[53, 50, 56]], [49, 52, 54] :: NoRelatedSym.members]

theorem QuoteRequest.shape (record : QuoteRequest) : record.parts.map Part.tags = QuoteRequest.tags := rfl

def QuoteRequest.decode (tokens : List Token) : Option QuoteRequest := do
  let quoteReqID ← readRequired [49, 51, 49] tokens
  let rFQID ← readOptional [51, 48, 48, 48, 54] tokens
  let privateQuote ← readRequired [49, 49, 55, 49] tokens
  let orderBook ← readRequired [51, 48, 48, 48, 49] tokens
  let expireTime ← readOptional [49, 50, 54] tokens
  let orderCapacity ← readRequired [53, 50, 56] tokens
  let noRelatedSym ← readGroup [49, 52, 54] [52, 56] NoRelatedSym.members NoRelatedSym.decode tokens
  pure { quoteReqID, rFQID, privateQuote, orderBook, expireTime, orderCapacity, noRelatedSym }

theorem QuoteRequest.decode_agrees (record : QuoteRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ QuoteRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    QuoteRequest.decode tokens = some record := by
  have distinct : QuoteRequest.tags.flatten.Nodup := by decide +kernel
  have quoteReqID := readRequired_part [49, 51, 49] record.quoteReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have rFQID := readOptional_part [51, 48, 48, 48, 54] record.rFQID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have privateQuote := readRequired_part [49, 49, 55, 49] record.privateQuote tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have orderBook := readRequired_part [51, 48, 48, 48, 49] record.orderBook tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have expireTime := readOptional_part [49, 50, 54] record.expireTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have orderCapacity := readRequired_part [53, 50, 56] record.orderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have noRelatedSym := readGroup_part [49, 52, 54] [52, 56] NoRelatedSym.members NoRelatedSym.encode NoRelatedSym.within NoRelatedSym.decode NoRelatedSym.decode_encode NoRelatedSym.led record.noRelatedSym tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  simp only [QuoteRequest.decode, quoteReqID, rFQID, privateQuote, orderBook, expireTime, orderCapacity, noRelatedSym, some_bind] <;> rfl

structure QuoteRequestReject where
  applID : Terminated 1  -- tag 1180
  quoteReqID : Terminated 1  -- tag 131
  rFQID : Option (Terminated 1)  -- tag 30006
  quoteRequestRejectReason : Option (Terminated 1)  -- tag 658
  text : Option (Terminated 1)  -- tag 58
  orderBook : Terminated 1  -- tag 30001
  noRelatedSym : List NoRelatedSym  -- tag 146
  noOrderAttributes : List NoOrderAttributes  -- tag 2593
  orderOrigination : Option (Terminated 1)  -- tag 1724

def QuoteRequestReject.parts (record : QuoteRequestReject) : List Part :=
  [Part.required [49, 49, 56, 48] record.applID,
   Part.required [49, 51, 49] record.quoteReqID,
   Part.optional [51, 48, 48, 48, 54] record.rFQID,
   Part.optional [54, 53, 56] record.quoteRequestRejectReason,
   Part.optional [53, 56] record.text,
   Part.required [51, 48, 48, 48, 49] record.orderBook,
   Part.group [49, 52, 54] NoRelatedSym.members NoRelatedSym.encode NoRelatedSym.within record.noRelatedSym,
   Part.group [50, 53, 57, 51] NoOrderAttributes.members NoOrderAttributes.encode NoOrderAttributes.within record.noOrderAttributes,
   Part.optional [49, 55, 50, 52] record.orderOrigination]

def QuoteRequestReject.tags : List (List (List UInt8)) :=
  [[[49, 49, 56, 48]], [[49, 51, 49]], [[51, 48, 48, 48, 54]], [[54, 53, 56]], [[53, 56]], [[51, 48, 48, 48, 49]], [49, 52, 54] :: NoRelatedSym.members, [50, 53, 57, 51] :: NoOrderAttributes.members, [[49, 55, 50, 52]]]

theorem QuoteRequestReject.shape (record : QuoteRequestReject) : record.parts.map Part.tags = QuoteRequestReject.tags := rfl

def QuoteRequestReject.decode (tokens : List Token) : Option QuoteRequestReject := do
  let applID ← readRequired [49, 49, 56, 48] tokens
  let quoteReqID ← readRequired [49, 51, 49] tokens
  let rFQID ← readOptional [51, 48, 48, 48, 54] tokens
  let quoteRequestRejectReason ← readOptional [54, 53, 56] tokens
  let text ← readOptional [53, 56] tokens
  let orderBook ← readRequired [51, 48, 48, 48, 49] tokens
  let noRelatedSym ← readGroup [49, 52, 54] [52, 56] NoRelatedSym.members NoRelatedSym.decode tokens
  let noOrderAttributes ← readGroup [50, 53, 57, 51] [50, 53, 57, 52] NoOrderAttributes.members NoOrderAttributes.decode tokens
  let orderOrigination ← readOptional [49, 55, 50, 52] tokens
  pure { applID, quoteReqID, rFQID, quoteRequestRejectReason, text, orderBook, noRelatedSym, noOrderAttributes, orderOrigination }

theorem QuoteRequestReject.decode_agrees (record : QuoteRequestReject) (tokens : List Token)
    (agrees : ∀ tags ∈ QuoteRequestReject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    QuoteRequestReject.decode tokens = some record := by
  have distinct : QuoteRequestReject.tags.flatten.Nodup := by decide +kernel
  have applID := readRequired_part [49, 49, 56, 48] record.applID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have quoteReqID := readRequired_part [49, 51, 49] record.quoteReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have rFQID := readOptional_part [51, 48, 48, 48, 54] record.rFQID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have quoteRequestRejectReason := readOptional_part [54, 53, 56] record.quoteRequestRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have orderBook := readRequired_part [51, 48, 48, 48, 49] record.orderBook tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have noRelatedSym := readGroup_part [49, 52, 54] [52, 56] NoRelatedSym.members NoRelatedSym.encode NoRelatedSym.within NoRelatedSym.decode NoRelatedSym.decode_encode NoRelatedSym.led record.noRelatedSym tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have noOrderAttributes := readGroup_part [50, 53, 57, 51] [50, 53, 57, 52] NoOrderAttributes.members NoOrderAttributes.encode NoOrderAttributes.within NoOrderAttributes.decode NoOrderAttributes.decode_encode NoOrderAttributes.led record.noOrderAttributes tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have orderOrigination := readOptional_part [49, 55, 50, 52] record.orderOrigination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  simp only [QuoteRequestReject.decode, applID, quoteReqID, rFQID, quoteRequestRejectReason, text, orderBook, noRelatedSym, noOrderAttributes, orderOrigination, some_bind] <;> rfl

structure QuoteAck where
  applID : Terminated 1  -- tag 1180
  quoteID : Terminated 1  -- tag 117
  quoteMsgID : Option (Terminated 1)  -- tag 1166
  rFQID : Terminated 1  -- tag 30006
  bidID : Option (Terminated 1)  -- tag 30007
  offerID : Option (Terminated 1)  -- tag 30008
  quoteAckStatus : Terminated 1  -- tag 1865
  quoteRejectReason : Option (Terminated 1)  -- tag 300
  text : Option (Terminated 1)  -- tag 58
  transactTime : Terminated 1  -- tag 60
  orderBook : Terminated 1  -- tag 30001
  noPartyIDs : List NoPartyIDs  -- tag 453
  noOrderAttributes : List NoOrderAttributes  -- tag 2593
  orderOrigination : Option (Terminated 1)  -- tag 1724

def QuoteAck.parts (record : QuoteAck) : List Part :=
  [Part.required [49, 49, 56, 48] record.applID,
   Part.required [49, 49, 55] record.quoteID,
   Part.optional [49, 49, 54, 54] record.quoteMsgID,
   Part.required [51, 48, 48, 48, 54] record.rFQID,
   Part.optional [51, 48, 48, 48, 55] record.bidID,
   Part.optional [51, 48, 48, 48, 56] record.offerID,
   Part.required [49, 56, 54, 53] record.quoteAckStatus,
   Part.optional [51, 48, 48] record.quoteRejectReason,
   Part.optional [53, 56] record.text,
   Part.required [54, 48] record.transactTime,
   Part.required [51, 48, 48, 48, 49] record.orderBook,
   Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.group [50, 53, 57, 51] NoOrderAttributes.members NoOrderAttributes.encode NoOrderAttributes.within record.noOrderAttributes,
   Part.optional [49, 55, 50, 52] record.orderOrigination]

def QuoteAck.tags : List (List (List UInt8)) :=
  [[[49, 49, 56, 48]], [[49, 49, 55]], [[49, 49, 54, 54]], [[51, 48, 48, 48, 54]], [[51, 48, 48, 48, 55]], [[51, 48, 48, 48, 56]], [[49, 56, 54, 53]], [[51, 48, 48]], [[53, 56]], [[54, 48]], [[51, 48, 48, 48, 49]], [52, 53, 51] :: NoPartyIDs.members, [50, 53, 57, 51] :: NoOrderAttributes.members, [[49, 55, 50, 52]]]

theorem QuoteAck.shape (record : QuoteAck) : record.parts.map Part.tags = QuoteAck.tags := rfl

def QuoteAck.decode (tokens : List Token) : Option QuoteAck := do
  let applID ← readRequired [49, 49, 56, 48] tokens
  let quoteID ← readRequired [49, 49, 55] tokens
  let quoteMsgID ← readOptional [49, 49, 54, 54] tokens
  let rFQID ← readRequired [51, 48, 48, 48, 54] tokens
  let bidID ← readOptional [51, 48, 48, 48, 55] tokens
  let offerID ← readOptional [51, 48, 48, 48, 56] tokens
  let quoteAckStatus ← readRequired [49, 56, 54, 53] tokens
  let quoteRejectReason ← readOptional [51, 48, 48] tokens
  let text ← readOptional [53, 56] tokens
  let transactTime ← readRequired [54, 48] tokens
  let orderBook ← readRequired [51, 48, 48, 48, 49] tokens
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let noOrderAttributes ← readGroup [50, 53, 57, 51] [50, 53, 57, 52] NoOrderAttributes.members NoOrderAttributes.decode tokens
  let orderOrigination ← readOptional [49, 55, 50, 52] tokens
  pure { applID, quoteID, quoteMsgID, rFQID, bidID, offerID, quoteAckStatus, quoteRejectReason, text, transactTime, orderBook, noPartyIDs, noOrderAttributes, orderOrigination }

theorem QuoteAck.decode_agrees (record : QuoteAck) (tokens : List Token)
    (agrees : ∀ tags ∈ QuoteAck.tags, select tags tokens = select tags (encodeParts record.parts)) :
    QuoteAck.decode tokens = some record := by
  have distinct : QuoteAck.tags.flatten.Nodup := by decide +kernel
  have applID := readRequired_part [49, 49, 56, 48] record.applID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have quoteID := readRequired_part [49, 49, 55] record.quoteID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have quoteMsgID := readOptional_part [49, 49, 54, 54] record.quoteMsgID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have rFQID := readRequired_part [51, 48, 48, 48, 54] record.rFQID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have bidID := readOptional_part [51, 48, 48, 48, 55] record.bidID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have offerID := readOptional_part [51, 48, 48, 48, 56] record.offerID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have quoteAckStatus := readRequired_part [49, 56, 54, 53] record.quoteAckStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have quoteRejectReason := readOptional_part [51, 48, 48] record.quoteRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have orderBook := readRequired_part [51, 48, 48, 48, 49] record.orderBook tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have noOrderAttributes := readGroup_part [50, 53, 57, 51] [50, 53, 57, 52] NoOrderAttributes.members NoOrderAttributes.encode NoOrderAttributes.within NoOrderAttributes.decode NoOrderAttributes.decode_encode NoOrderAttributes.led record.noOrderAttributes tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have orderOrigination := readOptional_part [49, 55, 50, 52] record.orderOrigination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  simp only [QuoteAck.decode, applID, quoteID, quoteMsgID, rFQID, bidID, offerID, quoteAckStatus, quoteRejectReason, text, transactTime, orderBook, noPartyIDs, noOrderAttributes, orderOrigination, some_bind] <;> rfl

structure QuoteResponse where
  applID : Option (Terminated 1)  -- tag 1180
  quoteMsgID : Terminated 1  -- tag 1166
  rFQID : Terminated 1  -- tag 30006
  bidID : Option (Terminated 1)  -- tag 30007
  offerID : Option (Terminated 1)  -- tag 30008
  quoteRespType : Terminated 1  -- tag 694
  securityID : Terminated 1  -- tag 48
  securityIDSource : Terminated 1  -- tag 22
  orderQty : Terminated 1  -- tag 38
  price : Option (Terminated 1)  -- tag 44
  quoteResponsePrice : Option (Terminated 1)  -- tag 1917
  side : Option (Terminated 1)  -- tag 54
  transactTime : Terminated 1  -- tag 60
  orderBook : Terminated 1  -- tag 30001
  noPartyIDs : List NoPartyIDs  -- tag 453
  accountType : Option (Terminated 1)  -- tag 581
  orderCapacity : Option (Terminated 1)  -- tag 528
  text : Option (Terminated 1)  -- tag 58
  noOrderAttributes : List NoOrderAttributes  -- tag 2593
  orderOrigination : Option (Terminated 1)  -- tag 1724

def QuoteResponse.parts (record : QuoteResponse) : List Part :=
  [Part.optional [49, 49, 56, 48] record.applID,
   Part.required [49, 49, 54, 54] record.quoteMsgID,
   Part.required [51, 48, 48, 48, 54] record.rFQID,
   Part.optional [51, 48, 48, 48, 55] record.bidID,
   Part.optional [51, 48, 48, 48, 56] record.offerID,
   Part.required [54, 57, 52] record.quoteRespType,
   Part.required [52, 56] record.securityID,
   Part.required [50, 50] record.securityIDSource,
   Part.required [51, 56] record.orderQty,
   Part.optional [52, 52] record.price,
   Part.optional [49, 57, 49, 55] record.quoteResponsePrice,
   Part.optional [53, 52] record.side,
   Part.required [54, 48] record.transactTime,
   Part.required [51, 48, 48, 48, 49] record.orderBook,
   Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.optional [53, 56, 49] record.accountType,
   Part.optional [53, 50, 56] record.orderCapacity,
   Part.optional [53, 56] record.text,
   Part.group [50, 53, 57, 51] NoOrderAttributes.members NoOrderAttributes.encode NoOrderAttributes.within record.noOrderAttributes,
   Part.optional [49, 55, 50, 52] record.orderOrigination]

def QuoteResponse.tags : List (List (List UInt8)) :=
  [[[49, 49, 56, 48]], [[49, 49, 54, 54]], [[51, 48, 48, 48, 54]], [[51, 48, 48, 48, 55]], [[51, 48, 48, 48, 56]], [[54, 57, 52]], [[52, 56]], [[50, 50]], [[51, 56]], [[52, 52]], [[49, 57, 49, 55]], [[53, 52]], [[54, 48]], [[51, 48, 48, 48, 49]], [52, 53, 51] :: NoPartyIDs.members, [[53, 56, 49]], [[53, 50, 56]], [[53, 56]], [50, 53, 57, 51] :: NoOrderAttributes.members, [[49, 55, 50, 52]]]

theorem QuoteResponse.shape (record : QuoteResponse) : record.parts.map Part.tags = QuoteResponse.tags := rfl

def QuoteResponse.decode (tokens : List Token) : Option QuoteResponse := do
  let applID ← readOptional [49, 49, 56, 48] tokens
  let quoteMsgID ← readRequired [49, 49, 54, 54] tokens
  let rFQID ← readRequired [51, 48, 48, 48, 54] tokens
  let bidID ← readOptional [51, 48, 48, 48, 55] tokens
  let offerID ← readOptional [51, 48, 48, 48, 56] tokens
  let quoteRespType ← readRequired [54, 57, 52] tokens
  let securityID ← readRequired [52, 56] tokens
  let securityIDSource ← readRequired [50, 50] tokens
  let orderQty ← readRequired [51, 56] tokens
  let price ← readOptional [52, 52] tokens
  let quoteResponsePrice ← readOptional [49, 57, 49, 55] tokens
  let side ← readOptional [53, 52] tokens
  let transactTime ← readRequired [54, 48] tokens
  let orderBook ← readRequired [51, 48, 48, 48, 49] tokens
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let accountType ← readOptional [53, 56, 49] tokens
  let orderCapacity ← readOptional [53, 50, 56] tokens
  let text ← readOptional [53, 56] tokens
  let noOrderAttributes ← readGroup [50, 53, 57, 51] [50, 53, 57, 52] NoOrderAttributes.members NoOrderAttributes.decode tokens
  let orderOrigination ← readOptional [49, 55, 50, 52] tokens
  pure { applID, quoteMsgID, rFQID, bidID, offerID, quoteRespType, securityID, securityIDSource, orderQty, price, quoteResponsePrice, side, transactTime, orderBook, noPartyIDs, accountType, orderCapacity, text, noOrderAttributes, orderOrigination }

theorem QuoteResponse.decode_agrees (record : QuoteResponse) (tokens : List Token)
    (agrees : ∀ tags ∈ QuoteResponse.tags, select tags tokens = select tags (encodeParts record.parts)) :
    QuoteResponse.decode tokens = some record := by
  have distinct : QuoteResponse.tags.flatten.Nodup := by decide +kernel
  have applID := readOptional_part [49, 49, 56, 48] record.applID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have quoteMsgID := readRequired_part [49, 49, 54, 54] record.quoteMsgID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have rFQID := readRequired_part [51, 48, 48, 48, 54] record.rFQID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have bidID := readOptional_part [51, 48, 48, 48, 55] record.bidID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have offerID := readOptional_part [51, 48, 48, 48, 56] record.offerID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have quoteRespType := readRequired_part [54, 57, 52] record.quoteRespType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have securityID := readRequired_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have securityIDSource := readRequired_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have quoteResponsePrice := readOptional_part [49, 57, 49, 55] record.quoteResponsePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have orderBook := readRequired_part [51, 48, 48, 48, 49] record.orderBook tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have accountType := readOptional_part [53, 56, 49] record.accountType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have orderCapacity := readOptional_part [53, 50, 56] record.orderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have noOrderAttributes := readGroup_part [50, 53, 57, 51] [50, 53, 57, 52] NoOrderAttributes.members NoOrderAttributes.encode NoOrderAttributes.within NoOrderAttributes.decode NoOrderAttributes.decode_encode NoOrderAttributes.led record.noOrderAttributes tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have orderOrigination := readOptional_part [49, 55, 50, 52] record.orderOrigination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  simp only [QuoteResponse.decode, applID, quoteMsgID, rFQID, bidID, offerID, quoteRespType, securityID, securityIDSource, orderQty, price, quoteResponsePrice, side, transactTime, orderBook, noPartyIDs, accountType, orderCapacity, text, noOrderAttributes, orderOrigination, some_bind] <;> rfl

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
  | orderCancelReject (header : Header) (r0 : OrderCancelReject)
  | orderMassCancelReport (header : Header) (r0 : OrderMassCancelReport)
  | quote (header : Header) (r0 : Quote)
  | quoteStatusReport (header : Header) (r0 : QuoteStatusReport)
  | massQuoteAcknowledgement (header : Header) (r0 : MassQuoteAcknowledgement)
  | quoteRequest (header : Header) (r0 : QuoteRequest)
  | quoteRequestReject (header : Header) (r0 : QuoteRequestReject)
  | quoteAck (header : Header) (r0 : QuoteAck)
  | quoteResponse (header : Header) (r0 : QuoteResponse)
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
  | .orderCancelReject header r0 => ⟨[51, 53], ⟨[57], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderMassCancelReport header r0 => ⟨[51, 53], ⟨[114], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .quote header r0 => ⟨[51, 53], ⟨[83], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .quoteStatusReport header r0 => ⟨[51, 53], ⟨[65, 73], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .massQuoteAcknowledgement header r0 => ⟨[51, 53], ⟨[98], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .quoteRequest header r0 => ⟨[51, 53], ⟨[82], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .quoteRequestReject header r0 => ⟨[51, 53], ⟨[65, 71], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .quoteAck header r0 => ⟨[51, 53], ⟨[67, 87], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .quoteResponse header r0 => ⟨[51, 53], ⟨[65, 74], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
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
      else if token.value.val = [57] then
        if known (Header.tags ++ OrderCancelReject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderCancelReject.decode rest
          pure (.orderCancelReject header r0)
        else none
      else if token.value.val = [114] then
        if known (Header.tags ++ OrderMassCancelReport.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderMassCancelReport.decode rest
          pure (.orderMassCancelReport header r0)
        else none
      else if token.value.val = [83] then
        if known (Header.tags ++ Quote.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Quote.decode rest
          pure (.quote header r0)
        else none
      else if token.value.val = [65, 73] then
        if known (Header.tags ++ QuoteStatusReport.tags) rest then do
          let header ← Header.decode rest
          let r0 ← QuoteStatusReport.decode rest
          pure (.quoteStatusReport header r0)
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
      else if token.value.val = [67, 87] then
        if known (Header.tags ++ QuoteAck.tags) rest then do
          let header ← Header.decode rest
          let r0 ← QuoteAck.decode rest
          pure (.quoteAck header r0)
        else none
      else if token.value.val = [65, 74] then
        if known (Header.tags ++ QuoteResponse.tags) rest then do
          let header ← Header.decode rest
          let r0 ← QuoteResponse.decode rest
          pure (.quoteResponse header r0)
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

theorem Message.decode_orderCancelReject (header : Header) (r0 : OrderCancelReject) :
    Message.decode (Message.tokens (.orderCancelReject header r0)) = some (.orderCancelReject header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelReject.tags) rfl rfl (by decide +kernel))
  have c1 := OrderCancelReject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelReject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderCancelReject.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_orderMassCancelReport (header : Header) (r0 : OrderMassCancelReport) :
    Message.decode (Message.tokens (.orderMassCancelReport header r0)) = some (.orderMassCancelReport header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderMassCancelReport.tags) rfl rfl (by decide +kernel))
  have c1 := OrderMassCancelReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderMassCancelReport.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderMassCancelReport.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_quote (header : Header) (r0 : Quote) :
    Message.decode (Message.tokens (.quote header r0)) = some (.quote header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (Quote.tags) rfl rfl (by decide +kernel))
  have c1 := Quote.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (Quote.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ Quote.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_quoteStatusReport (header : Header) (r0 : QuoteStatusReport) :
    Message.decode (Message.tokens (.quoteStatusReport header r0)) = some (.quoteStatusReport header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (QuoteStatusReport.tags) rfl rfl (by decide +kernel))
  have c1 := QuoteStatusReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (QuoteStatusReport.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ QuoteStatusReport.tags) rfl
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

theorem Message.decode_quoteAck (header : Header) (r0 : QuoteAck) :
    Message.decode (Message.tokens (.quoteAck header r0)) = some (.quoteAck header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (QuoteAck.tags) rfl rfl (by decide +kernel))
  have c1 := QuoteAck.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (QuoteAck.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ QuoteAck.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_quoteResponse (header : Header) (r0 : QuoteResponse) :
    Message.decode (Message.tokens (.quoteResponse header r0)) = some (.quoteResponse header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (QuoteResponse.tags) rfl rfl (by decide +kernel))
  have c1 := QuoteResponse.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (QuoteResponse.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ QuoteResponse.tags) rfl
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
  | orderCancelReject header r0 => exact Message.decode_orderCancelReject header r0
  | orderMassCancelReport header r0 => exact Message.decode_orderMassCancelReport header r0
  | quote header r0 => exact Message.decode_quote header r0
  | quoteStatusReport header r0 => exact Message.decode_quoteStatusReport header r0
  | massQuoteAcknowledgement header r0 => exact Message.decode_massQuoteAcknowledgement header r0
  | quoteRequest header r0 => exact Message.decode_quoteRequest header r0
  | quoteRequestReject header r0 => exact Message.decode_quoteRequestReject header r0
  | quoteAck header r0 => exact Message.decode_quoteAck header r0
  | quoteResponse header r0 => exact Message.decode_quoteResponse header r0
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

theorem Message.decodeBytes_orderCancelReject (header : Header) (r0 : OrderCancelReject) :
    Message.decodeBytes (Message.encode (.orderCancelReject header r0)) = some (.orderCancelReject header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[57], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ OrderCancelReject.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderCancelReject header r0

theorem Message.decodeBytes_orderMassCancelReport (header : Header) (r0 : OrderMassCancelReport) :
    Message.decodeBytes (Message.encode (.orderMassCancelReport header r0)) = some (.orderMassCancelReport header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[114], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ OrderMassCancelReport.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderMassCancelReport header r0

theorem Message.decodeBytes_quote (header : Header) (r0 : Quote) :
    Message.decodeBytes (Message.encode (.quote header r0)) = some (.quote header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[83], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ Quote.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_quote header r0

theorem Message.decodeBytes_quoteStatusReport (header : Header) (r0 : QuoteStatusReport) :
    Message.decodeBytes (Message.encode (.quoteStatusReport header r0)) = some (.quoteStatusReport header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[65, 73], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ QuoteStatusReport.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_quoteStatusReport header r0

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

theorem Message.decodeBytes_quoteAck (header : Header) (r0 : QuoteAck) :
    Message.decodeBytes (Message.encode (.quoteAck header r0)) = some (.quoteAck header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[67, 87], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ QuoteAck.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_quoteAck header r0

theorem Message.decodeBytes_quoteResponse (header : Header) (r0 : QuoteResponse) :
    Message.decodeBytes (Message.encode (.quoteResponse header r0)) = some (.quoteResponse header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[65, 74], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ QuoteResponse.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_quoteResponse header r0

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
  | orderCancelReject header r0 => exact Message.decodeBytes_orderCancelReject header r0
  | orderMassCancelReport header r0 => exact Message.decodeBytes_orderMassCancelReport header r0
  | quote header r0 => exact Message.decodeBytes_quote header r0
  | quoteStatusReport header r0 => exact Message.decodeBytes_quoteStatusReport header r0
  | massQuoteAcknowledgement header r0 => exact Message.decodeBytes_massQuoteAcknowledgement header r0
  | quoteRequest header r0 => exact Message.decodeBytes_quoteRequest header r0
  | quoteRequestReject header r0 => exact Message.decodeBytes_quoteRequestReject header r0
  | quoteAck header r0 => exact Message.decodeBytes_quoteAck header r0
  | quoteResponse header r0 => exact Message.decodeBytes_quoteResponse header r0
  | businessMessageReject header r0 => exact Message.decodeBytes_businessMessageReject header r0

/-- BeginString as the venue fixes it: FIXT.1.1 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 84, 46, 49, 46, 49, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.LsegMillenniumTradingFixV211Exchange
