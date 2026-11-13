import Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq)  v2.01.4, Exchange messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.NasdaqNordicequitiesDropcopyFixV2014Exchange

structure Header where
  msgSeqNum : Terminated 1  -- tag 34
  possDupFlag : Option (Terminated 1)  -- tag 43
  senderCompID : Terminated 1  -- tag 49
  senderSubID : Option (Terminated 1)  -- tag 50
  sendingTime : Terminated 1  -- tag 52
  targetCompID : Terminated 1  -- tag 56
  targetSubID : Option (Terminated 1)  -- tag 57
  possResend : Option (Terminated 1)  -- tag 97
  onBehalfOfCompID : Option (Terminated 1)  -- tag 115
  onBehalfOfSubID : Option (Terminated 1)  -- tag 116
  origSendingTime : Option (Terminated 1)  -- tag 122
  deliverToCompID : Option (Terminated 1)  -- tag 128
  deliverToSubID : Option (Terminated 1)  -- tag 129
  deliverToLocationID : Option (Terminated 1)  -- tag 145

def Header.parts (record : Header) : List Part :=
  [Part.required [51, 52] record.msgSeqNum,
   Part.optional [52, 51] record.possDupFlag,
   Part.required [52, 57] record.senderCompID,
   Part.optional [53, 48] record.senderSubID,
   Part.required [53, 50] record.sendingTime,
   Part.required [53, 54] record.targetCompID,
   Part.optional [53, 55] record.targetSubID,
   Part.optional [57, 55] record.possResend,
   Part.optional [49, 49, 53] record.onBehalfOfCompID,
   Part.optional [49, 49, 54] record.onBehalfOfSubID,
   Part.optional [49, 50, 50] record.origSendingTime,
   Part.optional [49, 50, 56] record.deliverToCompID,
   Part.optional [49, 50, 57] record.deliverToSubID,
   Part.optional [49, 52, 53] record.deliverToLocationID]

def Header.tags : List (List (List UInt8)) :=
  [[[51, 52]], [[52, 51]], [[52, 57]], [[53, 48]], [[53, 50]], [[53, 54]], [[53, 55]], [[57, 55]], [[49, 49, 53]], [[49, 49, 54]], [[49, 50, 50]], [[49, 50, 56]], [[49, 50, 57]], [[49, 52, 53]]]

theorem Header.shape (record : Header) : record.parts.map Part.tags = Header.tags := rfl

def Header.decode (tokens : List Token) : Option Header := do
  let msgSeqNum ← readRequired [51, 52] tokens
  let possDupFlag ← readOptional [52, 51] tokens
  let senderCompID ← readRequired [52, 57] tokens
  let senderSubID ← readOptional [53, 48] tokens
  let sendingTime ← readRequired [53, 50] tokens
  let targetCompID ← readRequired [53, 54] tokens
  let targetSubID ← readOptional [53, 55] tokens
  let possResend ← readOptional [57, 55] tokens
  let onBehalfOfCompID ← readOptional [49, 49, 53] tokens
  let onBehalfOfSubID ← readOptional [49, 49, 54] tokens
  let origSendingTime ← readOptional [49, 50, 50] tokens
  let deliverToCompID ← readOptional [49, 50, 56] tokens
  let deliverToSubID ← readOptional [49, 50, 57] tokens
  let deliverToLocationID ← readOptional [49, 52, 53] tokens
  pure { msgSeqNum, possDupFlag, senderCompID, senderSubID, sendingTime, targetCompID, targetSubID, possResend, onBehalfOfCompID, onBehalfOfSubID, origSendingTime, deliverToCompID, deliverToSubID, deliverToLocationID }

theorem Header.decode_agrees (record : Header) (tokens : List Token)
    (agrees : ∀ tags ∈ Header.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Header.decode tokens = some record := by
  have distinct : Header.tags.flatten.Nodup := by decide +kernel
  have msgSeqNum := readRequired_part [51, 52] record.msgSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have possDupFlag := readOptional_part [52, 51] record.possDupFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have senderCompID := readRequired_part [52, 57] record.senderCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have senderSubID := readOptional_part [53, 48] record.senderSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have sendingTime := readRequired_part [53, 50] record.sendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have targetCompID := readRequired_part [53, 54] record.targetCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have targetSubID := readOptional_part [53, 55] record.targetSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have possResend := readOptional_part [57, 55] record.possResend tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have onBehalfOfCompID := readOptional_part [49, 49, 53] record.onBehalfOfCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have onBehalfOfSubID := readOptional_part [49, 49, 54] record.onBehalfOfSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have origSendingTime := readOptional_part [49, 50, 50] record.origSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have deliverToCompID := readOptional_part [49, 50, 56] record.deliverToCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have deliverToSubID := readOptional_part [49, 50, 57] record.deliverToSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have deliverToLocationID := readOptional_part [49, 52, 53] record.deliverToLocationID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  simp only [Header.decode, msgSeqNum, possDupFlag, senderCompID, senderSubID, sendingTime, targetCompID, targetSubID, possResend, onBehalfOfCompID, onBehalfOfSubID, origSendingTime, deliverToCompID, deliverToSubID, deliverToLocationID, some_bind] <;> rfl

structure Reject where
  refSeqNum : Terminated 1  -- tag 45
  text : Option (Terminated 1)  -- tag 58
  refTagID : Option (Terminated 1)  -- tag 371
  refMsgType : Option (Terminated 1)  -- tag 372
  sessionRejectReason : Terminated 1  -- tag 373

def Reject.parts (record : Reject) : List Part :=
  [Part.required [52, 53] record.refSeqNum,
   Part.optional [53, 56] record.text,
   Part.optional [51, 55, 49] record.refTagID,
   Part.optional [51, 55, 50] record.refMsgType,
   Part.required [51, 55, 51] record.sessionRejectReason]

def Reject.tags : List (List (List UInt8)) :=
  [[[52, 53]], [[53, 56]], [[51, 55, 49]], [[51, 55, 50]], [[51, 55, 51]]]

theorem Reject.shape (record : Reject) : record.parts.map Part.tags = Reject.tags := rfl

def Reject.decode (tokens : List Token) : Option Reject := do
  let refSeqNum ← readRequired [52, 53] tokens
  let text ← readOptional [53, 56] tokens
  let refTagID ← readOptional [51, 55, 49] tokens
  let refMsgType ← readOptional [51, 55, 50] tokens
  let sessionRejectReason ← readRequired [51, 55, 51] tokens
  pure { refSeqNum, text, refTagID, refMsgType, sessionRejectReason }

theorem Reject.decode_agrees (record : Reject) (tokens : List Token)
    (agrees : ∀ tags ∈ Reject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Reject.decode tokens = some record := by
  have distinct : Reject.tags.flatten.Nodup := by decide +kernel
  have refSeqNum := readRequired_part [52, 53] record.refSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have refTagID := readOptional_part [51, 55, 49] record.refTagID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have refMsgType := readOptional_part [51, 55, 50] record.refMsgType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have sessionRejectReason := readRequired_part [51, 55, 51] record.sessionRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [Reject.decode, refSeqNum, text, refTagID, refMsgType, sessionRejectReason, some_bind] <;> rfl

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

structure Logon where
  encryptMethod : Terminated 1  -- tag 98
  heartBtInt : Terminated 1  -- tag 108
  defaultApplVerID : Terminated 1  -- tag 1137

def Logon.parts (record : Logon) : List Part :=
  [Part.required [57, 56] record.encryptMethod,
   Part.required [49, 48, 56] record.heartBtInt,
   Part.required [49, 49, 51, 55] record.defaultApplVerID]

def Logon.tags : List (List (List UInt8)) :=
  [[[57, 56]], [[49, 48, 56]], [[49, 49, 51, 55]]]

theorem Logon.shape (record : Logon) : record.parts.map Part.tags = Logon.tags := rfl

def Logon.decode (tokens : List Token) : Option Logon := do
  let encryptMethod ← readRequired [57, 56] tokens
  let heartBtInt ← readRequired [49, 48, 56] tokens
  let defaultApplVerID ← readRequired [49, 49, 51, 55] tokens
  pure { encryptMethod, heartBtInt, defaultApplVerID }

theorem Logon.decode_agrees (record : Logon) (tokens : List Token)
    (agrees : ∀ tags ∈ Logon.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Logon.decode tokens = some record := by
  have distinct : Logon.tags.flatten.Nodup := by decide +kernel
  have encryptMethod := readRequired_part [57, 56] record.encryptMethod tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have heartBtInt := readRequired_part [49, 48, 56] record.heartBtInt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have defaultApplVerID := readRequired_part [49, 49, 51, 55] record.defaultApplVerID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [Logon.decode, encryptMethod, heartBtInt, defaultApplVerID, some_bind] <;> rfl

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

structure Logout where
  text : Option (Terminated 1)  -- tag 58

def Logout.parts (record : Logout) : List Part :=
  [Part.optional [53, 56] record.text]

def Logout.tags : List (List (List UInt8)) :=
  [[[53, 56]]]

theorem Logout.shape (record : Logout) : record.parts.map Part.tags = Logout.tags := rfl

def Logout.decode (tokens : List Token) : Option Logout := do
  let text ← readOptional [53, 56] tokens
  pure { text }

theorem Logout.decode_agrees (record : Logout) (tokens : List Token)
    (agrees : ∀ tags ∈ Logout.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Logout.decode tokens = some record := by
  have distinct : Logout.tags.flatten.Nodup := by decide +kernel
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [Logout.decode, text, some_bind] <;> rfl

structure NoContraBrokers where
  contraBroker : Terminated 1  -- tag 375

def NoContraBrokers.parts (record : NoContraBrokers) : List Part :=
  [Part.required [51, 55, 53] record.contraBroker]

def NoContraBrokers.tags : List (List (List UInt8)) :=
  [[[51, 55, 53]]]

theorem NoContraBrokers.shape (record : NoContraBrokers) : record.parts.map Part.tags = NoContraBrokers.tags := rfl

def NoContraBrokers.decode (tokens : List Token) : Option NoContraBrokers := do
  let contraBroker ← readRequired [51, 55, 53] tokens
  pure { contraBroker }

theorem NoContraBrokers.decode_agrees (record : NoContraBrokers) (tokens : List Token)
    (agrees : ∀ tags ∈ NoContraBrokers.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoContraBrokers.decode tokens = some record := by
  have distinct : NoContraBrokers.tags.flatten.Nodup := by decide +kernel
  have contraBroker := readRequired_part [51, 55, 53] record.contraBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [NoContraBrokers.decode, contraBroker, some_bind] <;> rfl

def NoContraBrokers.members : List (List UInt8) := NoContraBrokers.tags.flatten

def NoContraBrokers.encode (entry : NoContraBrokers) : List Token := encodeParts entry.parts

theorem NoContraBrokers.decode_encode (entry : NoContraBrokers) : NoContraBrokers.decode entry.encode = some entry :=
  NoContraBrokers.decode_agrees entry _ (fun _ _ => rfl)

theorem NoContraBrokers.within (entry : NoContraBrokers) : ∀ token ∈ entry.encode, token.tag ∈ NoContraBrokers.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoContraBrokers.shape] at this

theorem NoContraBrokers.led (entry : NoContraBrokers) : Lead [51, 55, 53] entry.encode :=
  lead_parts [51, 55, 53] entry.contraBroker _ NoContraBrokers.tags.tail rfl (by decide +kernel)

structure NoOrderAttributes where
  orderAttributeType : Terminated 1  -- tag 2594
  orderAttributeValue : Terminated 1  -- tag 2595

def NoOrderAttributes.parts (record : NoOrderAttributes) : List Part :=
  [Part.required [50, 53, 57, 52] record.orderAttributeType,
   Part.required [50, 53, 57, 53] record.orderAttributeValue]

def NoOrderAttributes.tags : List (List (List UInt8)) :=
  [[[50, 53, 57, 52]], [[50, 53, 57, 53]]]

theorem NoOrderAttributes.shape (record : NoOrderAttributes) : record.parts.map Part.tags = NoOrderAttributes.tags := rfl

def NoOrderAttributes.decode (tokens : List Token) : Option NoOrderAttributes := do
  let orderAttributeType ← readRequired [50, 53, 57, 52] tokens
  let orderAttributeValue ← readRequired [50, 53, 57, 53] tokens
  pure { orderAttributeType, orderAttributeValue }

theorem NoOrderAttributes.decode_agrees (record : NoOrderAttributes) (tokens : List Token)
    (agrees : ∀ tags ∈ NoOrderAttributes.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoOrderAttributes.decode tokens = some record := by
  have distinct : NoOrderAttributes.tags.flatten.Nodup := by decide +kernel
  have orderAttributeType := readRequired_part [50, 53, 57, 52] record.orderAttributeType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have orderAttributeValue := readRequired_part [50, 53, 57, 53] record.orderAttributeValue tokens
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
  partyRoleQualifier : Terminated 1  -- tag 2376

def NoPartyIDs.parts (record : NoPartyIDs) : List Part :=
  [Part.required [52, 52, 56] record.partyID,
   Part.required [52, 52, 55] record.partyIDSource,
   Part.required [52, 53, 50] record.partyRole,
   Part.required [50, 51, 55, 54] record.partyRoleQualifier]

def NoPartyIDs.tags : List (List (List UInt8)) :=
  [[[52, 52, 56]], [[52, 52, 55]], [[52, 53, 50]], [[50, 51, 55, 54]]]

theorem NoPartyIDs.shape (record : NoPartyIDs) : record.parts.map Part.tags = NoPartyIDs.tags := rfl

def NoPartyIDs.decode (tokens : List Token) : Option NoPartyIDs := do
  let partyID ← readRequired [52, 52, 56] tokens
  let partyIDSource ← readRequired [52, 52, 55] tokens
  let partyRole ← readRequired [52, 53, 50] tokens
  let partyRoleQualifier ← readRequired [50, 51, 55, 54] tokens
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
  have partyRoleQualifier := readRequired_part [50, 51, 55, 54] record.partyRoleQualifier tokens
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
  trdRegPublReason : Option (Terminated 1)  -- tag 2670

def NoTrdRegPublications.parts (record : NoTrdRegPublications) : List Part :=
  [Part.required [50, 54, 54, 57] record.trdRegPublicationType,
   Part.optional [50, 54, 55, 48] record.trdRegPublReason]

def NoTrdRegPublications.tags : List (List (List UInt8)) :=
  [[[50, 54, 54, 57]], [[50, 54, 55, 48]]]

theorem NoTrdRegPublications.shape (record : NoTrdRegPublications) : record.parts.map Part.tags = NoTrdRegPublications.tags := rfl

def NoTrdRegPublications.decode (tokens : List Token) : Option NoTrdRegPublications := do
  let trdRegPublicationType ← readRequired [50, 54, 54, 57] tokens
  let trdRegPublReason ← readOptional [50, 54, 55, 48] tokens
  pure { trdRegPublicationType, trdRegPublReason }

theorem NoTrdRegPublications.decode_agrees (record : NoTrdRegPublications) (tokens : List Token)
    (agrees : ∀ tags ∈ NoTrdRegPublications.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoTrdRegPublications.decode tokens = some record := by
  have distinct : NoTrdRegPublications.tags.flatten.Nodup := by decide +kernel
  have trdRegPublicationType := readRequired_part [50, 54, 54, 57] record.trdRegPublicationType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have trdRegPublReason := readOptional_part [50, 54, 55, 48] record.trdRegPublReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [NoTrdRegPublications.decode, trdRegPublicationType, trdRegPublReason, some_bind] <;> rfl

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

structure ExecutionReport where
  avgPx : Terminated 1  -- tag 6
  clOrdID : Terminated 1  -- tag 11
  cumQty : Terminated 1  -- tag 14
  currency : Option (Terminated 1)  -- tag 15
  execID : Terminated 1  -- tag 17
  execInst : Option (Terminated 1)  -- tag 18
  execRefID : Option (Terminated 1)  -- tag 19
  iDSource : Option (Terminated 1)  -- tag 22
  lastMkt : Option (Terminated 1)  -- tag 30
  lastPx : Option (Terminated 1)  -- tag 31
  lastShares : Option (Terminated 1)  -- tag 32
  orderID : Terminated 1  -- tag 37
  orderQty : Option (Terminated 1)  -- tag 38
  ordStatus : Terminated 1  -- tag 39
  ordType : Option (Terminated 1)  -- tag 40
  origClOrdID : Option (Terminated 1)  -- tag 41
  price : Option (Terminated 1)  -- tag 44
  securityID : Option (Terminated 1)  -- tag 48
  side : Terminated 1  -- tag 54
  symbol : Terminated 1  -- tag 55
  text : Option (Terminated 1)  -- tag 58
  timeInForce : Option (Terminated 1)  -- tag 59
  transactTime : Option (Terminated 1)  -- tag 60
  tradeDate : Option (Terminated 1)  -- tag 75
  execBroker : Option (Terminated 1)  -- tag 76
  ordRejReason : Option (Terminated 1)  -- tag 103
  clientID : Terminated 1  -- tag 109
  minQty : Option (Terminated 1)  -- tag 110
  maxFloor : Option (Terminated 1)  -- tag 111
  expireTime : Option (Terminated 1)  -- tag 126
  execType : Terminated 1  -- tag 150
  leavesQty : Terminated 1  -- tag 151
  secondaryOrderID : Option (Terminated 1)  -- tag 198
  pegDifference : Option (Terminated 1)  -- tag 211
  noContraBrokers : List NoContraBrokers  -- tag 382
  execRestatementReason : Option (Terminated 1)  -- tag 378
  clearingFirm : Option (Terminated 1)  -- tag 439
  clearingAccount : Option (Terminated 1)  -- tag 440
  orderCapacity : Option (Terminated 1)  -- tag 528
  orderRestrictions : Option (Terminated 1)  -- tag 529
  clOrdLinkID : Option (Terminated 1)  -- tag 583
  tradeID : Option (Terminated 1)  -- tag 1003
  displayQty : Option (Terminated 1)  -- tag 1138
  clearingAccountType : Option (Terminated 1)  -- tag 1816
  subMktID : Option (Terminated 1)  -- tag 5815
  clRefID : Option (Terminated 1)  -- tag 6209
  displayRange : Option (Terminated 1)  -- tag 6227
  displayInst : Option (Terminated 1)  -- tag 9140
  crossTradeFlag : Option (Terminated 1)  -- tag 9355
  brSeqNbr : Option (Terminated 1)  -- tag 9861
  liquidityFlag : Option (Terminated 1)  -- tag 9882
  effectiveTime : Option (Terminated 1)  -- tag 168
  targetVolume : Option (Terminated 1)  -- tag 20001
  maximumVolume : Option (Terminated 1)  -- tag 849
  minimumVolume : Option (Terminated 1)  -- tag 20003
  aggression : Option (Terminated 1)  -- tag 20002
  minChildOrderValue : Option (Terminated 1)  -- tag 20030
  spreadLimit : Option (Terminated 1)  -- tag 20020
  refPriceBidLeg : Option (Terminated 1)  -- tag 20021
  refPriceAskLeg : Option (Terminated 1)  -- tag 20022
  lagBidLeg : Option (Terminated 1)  -- tag 20023
  lagAskLeg : Option (Terminated 1)  -- tag 20024
  leadBidLeg : Option (Terminated 1)  -- tag 20025
  leadAskLeg : Option (Terminated 1)  -- tag 20026
  stopLossBidLeg : Option (Terminated 1)  -- tag 20027
  stopLossAskLeg : Option (Terminated 1)  -- tag 20028
  basketID : Option (Terminated 1)  -- tag 20029
  ratio : Option (Terminated 1)  -- tag 20031
  iWouldPrice : Option (Terminated 1)  -- tag 20006
  iWouldType : Option (Terminated 1)  -- tag 20007
  iWouldQty : Option (Terminated 1)  -- tag 20005
  cleanUpType : Option (Terminated 1)  -- tag 20012
  cleanUpQty : Option (Terminated 1)  -- tag 20013
  blockFilter : Option (Terminated 1)  -- tag 20004
  onOpenType : Option (Terminated 1)  -- tag 20010
  onOpenQty : Option (Terminated 1)  -- tag 20008
  onCloseType : Option (Terminated 1)  -- tag 20011
  onCloseQty : Option (Terminated 1)  -- tag 20009
  dynamicBenchmark : Option (Terminated 1)  -- tag 20014
  dynamicPrice : Option (Terminated 1)  -- tag 20015
  inMoneyStyle : Option (Terminated 1)  -- tag 20016
  outMoneyStyle : Option (Terminated 1)  -- tag 20018
  sTPLevel : Option (Terminated 1)  -- tag 20101
  sTPAction : Option (Terminated 1)  -- tag 20102
  sTPTraderGroup : Option (Terminated 1)  -- tag 20103
  lastExecFlagINT : Option (Terminated 1)  -- tag 20104
  lastExecFlagTOP : Option (Terminated 1)  -- tag 20105
  lastExecFlagSTP : Option (Terminated 1)  -- tag 20106
  lastLiquidityInd : Option (Terminated 1)  -- tag 851
  noOrderAttributes : List NoOrderAttributes  -- tag 2593
  tradeReportTransType : Option (Terminated 1)  -- tag 487
  algoIndicator : Option (Terminated 1)  -- tag 2667
  noPartyIDs : List NoPartyIDs  -- tag 453
  venueType : Option (Terminated 1)  -- tag 1430
  tradingSessionSubID : Option (Terminated 1)  -- tag 625
  matchType : Option (Terminated 1)  -- tag 574
  trdType : Option (Terminated 1)  -- tag 828
  orderCategory : Option (Terminated 1)  -- tag 1115
  orderOriginator : Option (Terminated 1)  -- tag 1724
  noTrdRegPublications : List NoTrdRegPublications  -- tag 2668
  tradingAtClosingPrice : Option (Terminated 1)  -- tag 20301
  originalOrderReferenceNumber : Option (Terminated 1)  -- tag 20107
  originalOrderEntryDate : Option (Terminated 1)  -- tag 20108
  orderCondition : Option (Terminated 1)  -- tag 20109
  custOrderCapacity : Option (Terminated 1)  -- tag 582

def ExecutionReport.parts (record : ExecutionReport) : List Part :=
  [Part.required [54] record.avgPx,
   Part.required [49, 49] record.clOrdID,
   Part.required [49, 52] record.cumQty,
   Part.optional [49, 53] record.currency,
   Part.required [49, 55] record.execID,
   Part.optional [49, 56] record.execInst,
   Part.optional [49, 57] record.execRefID,
   Part.optional [50, 50] record.iDSource,
   Part.optional [51, 48] record.lastMkt,
   Part.optional [51, 49] record.lastPx,
   Part.optional [51, 50] record.lastShares,
   Part.required [51, 55] record.orderID,
   Part.optional [51, 56] record.orderQty,
   Part.required [51, 57] record.ordStatus,
   Part.optional [52, 48] record.ordType,
   Part.optional [52, 49] record.origClOrdID,
   Part.optional [52, 52] record.price,
   Part.optional [52, 56] record.securityID,
   Part.required [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.optional [53, 56] record.text,
   Part.optional [53, 57] record.timeInForce,
   Part.optional [54, 48] record.transactTime,
   Part.optional [55, 53] record.tradeDate,
   Part.optional [55, 54] record.execBroker,
   Part.optional [49, 48, 51] record.ordRejReason,
   Part.required [49, 48, 57] record.clientID,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [49, 49, 49] record.maxFloor,
   Part.optional [49, 50, 54] record.expireTime,
   Part.required [49, 53, 48] record.execType,
   Part.required [49, 53, 49] record.leavesQty,
   Part.optional [49, 57, 56] record.secondaryOrderID,
   Part.optional [50, 49, 49] record.pegDifference,
   Part.group [51, 56, 50] NoContraBrokers.members NoContraBrokers.encode NoContraBrokers.within record.noContraBrokers,
   Part.optional [51, 55, 56] record.execRestatementReason,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.optional [53, 50, 56] record.orderCapacity,
   Part.optional [53, 50, 57] record.orderRestrictions,
   Part.optional [53, 56, 51] record.clOrdLinkID,
   Part.optional [49, 48, 48, 51] record.tradeID,
   Part.optional [49, 49, 51, 56] record.displayQty,
   Part.optional [49, 56, 49, 54] record.clearingAccountType,
   Part.optional [53, 56, 49, 53] record.subMktID,
   Part.optional [54, 50, 48, 57] record.clRefID,
   Part.optional [54, 50, 50, 55] record.displayRange,
   Part.optional [57, 49, 52, 48] record.displayInst,
   Part.optional [57, 51, 53, 53] record.crossTradeFlag,
   Part.optional [57, 56, 54, 49] record.brSeqNbr,
   Part.optional [57, 56, 56, 50] record.liquidityFlag,
   Part.optional [49, 54, 56] record.effectiveTime,
   Part.optional [50, 48, 48, 48, 49] record.targetVolume,
   Part.optional [56, 52, 57] record.maximumVolume,
   Part.optional [50, 48, 48, 48, 51] record.minimumVolume,
   Part.optional [50, 48, 48, 48, 50] record.aggression,
   Part.optional [50, 48, 48, 51, 48] record.minChildOrderValue,
   Part.optional [50, 48, 48, 50, 48] record.spreadLimit,
   Part.optional [50, 48, 48, 50, 49] record.refPriceBidLeg,
   Part.optional [50, 48, 48, 50, 50] record.refPriceAskLeg,
   Part.optional [50, 48, 48, 50, 51] record.lagBidLeg,
   Part.optional [50, 48, 48, 50, 52] record.lagAskLeg,
   Part.optional [50, 48, 48, 50, 53] record.leadBidLeg,
   Part.optional [50, 48, 48, 50, 54] record.leadAskLeg,
   Part.optional [50, 48, 48, 50, 55] record.stopLossBidLeg,
   Part.optional [50, 48, 48, 50, 56] record.stopLossAskLeg,
   Part.optional [50, 48, 48, 50, 57] record.basketID,
   Part.optional [50, 48, 48, 51, 49] record.ratio,
   Part.optional [50, 48, 48, 48, 54] record.iWouldPrice,
   Part.optional [50, 48, 48, 48, 55] record.iWouldType,
   Part.optional [50, 48, 48, 48, 53] record.iWouldQty,
   Part.optional [50, 48, 48, 49, 50] record.cleanUpType,
   Part.optional [50, 48, 48, 49, 51] record.cleanUpQty,
   Part.optional [50, 48, 48, 48, 52] record.blockFilter,
   Part.optional [50, 48, 48, 49, 48] record.onOpenType,
   Part.optional [50, 48, 48, 48, 56] record.onOpenQty,
   Part.optional [50, 48, 48, 49, 49] record.onCloseType,
   Part.optional [50, 48, 48, 48, 57] record.onCloseQty,
   Part.optional [50, 48, 48, 49, 52] record.dynamicBenchmark,
   Part.optional [50, 48, 48, 49, 53] record.dynamicPrice,
   Part.optional [50, 48, 48, 49, 54] record.inMoneyStyle,
   Part.optional [50, 48, 48, 49, 56] record.outMoneyStyle,
   Part.optional [50, 48, 49, 48, 49] record.sTPLevel,
   Part.optional [50, 48, 49, 48, 50] record.sTPAction,
   Part.optional [50, 48, 49, 48, 51] record.sTPTraderGroup,
   Part.optional [50, 48, 49, 48, 52] record.lastExecFlagINT,
   Part.optional [50, 48, 49, 48, 53] record.lastExecFlagTOP,
   Part.optional [50, 48, 49, 48, 54] record.lastExecFlagSTP,
   Part.optional [56, 53, 49] record.lastLiquidityInd,
   Part.group [50, 53, 57, 51] NoOrderAttributes.members NoOrderAttributes.encode NoOrderAttributes.within record.noOrderAttributes,
   Part.optional [52, 56, 55] record.tradeReportTransType,
   Part.optional [50, 54, 54, 55] record.algoIndicator,
   Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.optional [49, 52, 51, 48] record.venueType,
   Part.optional [54, 50, 53] record.tradingSessionSubID,
   Part.optional [53, 55, 52] record.matchType,
   Part.optional [56, 50, 56] record.trdType,
   Part.optional [49, 49, 49, 53] record.orderCategory,
   Part.optional [49, 55, 50, 52] record.orderOriginator,
   Part.group [50, 54, 54, 56] NoTrdRegPublications.members NoTrdRegPublications.encode NoTrdRegPublications.within record.noTrdRegPublications,
   Part.optional [50, 48, 51, 48, 49] record.tradingAtClosingPrice,
   Part.optional [50, 48, 49, 48, 55] record.originalOrderReferenceNumber,
   Part.optional [50, 48, 49, 48, 56] record.originalOrderEntryDate,
   Part.optional [50, 48, 49, 48, 57] record.orderCondition,
   Part.optional [53, 56, 50] record.custOrderCapacity]

def ExecutionReport.tags : List (List (List UInt8)) :=
  [[[54]], [[49, 49]], [[49, 52]], [[49, 53]], [[49, 55]], [[49, 56]], [[49, 57]], [[50, 50]], [[51, 48]], [[51, 49]], [[51, 50]], [[51, 55]], [[51, 56]], [[51, 57]], [[52, 48]], [[52, 49]], [[52, 52]], [[52, 56]], [[53, 52]], [[53, 53]], [[53, 56]], [[53, 57]], [[54, 48]], [[55, 53]], [[55, 54]], [[49, 48, 51]], [[49, 48, 57]], [[49, 49, 48]], [[49, 49, 49]], [[49, 50, 54]], [[49, 53, 48]], [[49, 53, 49]], [[49, 57, 56]], [[50, 49, 49]], [51, 56, 50] :: NoContraBrokers.members, [[51, 55, 56]], [[52, 51, 57]], [[52, 52, 48]], [[53, 50, 56]], [[53, 50, 57]], [[53, 56, 51]], [[49, 48, 48, 51]], [[49, 49, 51, 56]], [[49, 56, 49, 54]], [[53, 56, 49, 53]], [[54, 50, 48, 57]], [[54, 50, 50, 55]], [[57, 49, 52, 48]], [[57, 51, 53, 53]], [[57, 56, 54, 49]], [[57, 56, 56, 50]], [[49, 54, 56]], [[50, 48, 48, 48, 49]], [[56, 52, 57]], [[50, 48, 48, 48, 51]], [[50, 48, 48, 48, 50]], [[50, 48, 48, 51, 48]], [[50, 48, 48, 50, 48]], [[50, 48, 48, 50, 49]], [[50, 48, 48, 50, 50]], [[50, 48, 48, 50, 51]], [[50, 48, 48, 50, 52]], [[50, 48, 48, 50, 53]], [[50, 48, 48, 50, 54]], [[50, 48, 48, 50, 55]], [[50, 48, 48, 50, 56]], [[50, 48, 48, 50, 57]], [[50, 48, 48, 51, 49]], [[50, 48, 48, 48, 54]], [[50, 48, 48, 48, 55]], [[50, 48, 48, 48, 53]], [[50, 48, 48, 49, 50]], [[50, 48, 48, 49, 51]], [[50, 48, 48, 48, 52]], [[50, 48, 48, 49, 48]], [[50, 48, 48, 48, 56]], [[50, 48, 48, 49, 49]], [[50, 48, 48, 48, 57]], [[50, 48, 48, 49, 52]], [[50, 48, 48, 49, 53]], [[50, 48, 48, 49, 54]], [[50, 48, 48, 49, 56]], [[50, 48, 49, 48, 49]], [[50, 48, 49, 48, 50]], [[50, 48, 49, 48, 51]], [[50, 48, 49, 48, 52]], [[50, 48, 49, 48, 53]], [[50, 48, 49, 48, 54]], [[56, 53, 49]], [50, 53, 57, 51] :: NoOrderAttributes.members, [[52, 56, 55]], [[50, 54, 54, 55]], [52, 53, 51] :: NoPartyIDs.members, [[49, 52, 51, 48]], [[54, 50, 53]], [[53, 55, 52]], [[56, 50, 56]], [[49, 49, 49, 53]], [[49, 55, 50, 52]], [50, 54, 54, 56] :: NoTrdRegPublications.members, [[50, 48, 51, 48, 49]], [[50, 48, 49, 48, 55]], [[50, 48, 49, 48, 56]], [[50, 48, 49, 48, 57]], [[53, 56, 50]]]

theorem ExecutionReport.shape (record : ExecutionReport) : record.parts.map Part.tags = ExecutionReport.tags := rfl

def ExecutionReport.decode (tokens : List Token) : Option ExecutionReport := do
  let avgPx ← readRequired [54] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let cumQty ← readRequired [49, 52] tokens
  let currency ← readOptional [49, 53] tokens
  let execID ← readRequired [49, 55] tokens
  let execInst ← readOptional [49, 56] tokens
  let execRefID ← readOptional [49, 57] tokens
  let iDSource ← readOptional [50, 50] tokens
  let lastMkt ← readOptional [51, 48] tokens
  let lastPx ← readOptional [51, 49] tokens
  let lastShares ← readOptional [51, 50] tokens
  let orderID ← readRequired [51, 55] tokens
  let orderQty ← readOptional [51, 56] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let ordType ← readOptional [52, 48] tokens
  let origClOrdID ← readOptional [52, 49] tokens
  let price ← readOptional [52, 52] tokens
  let securityID ← readOptional [52, 56] tokens
  let side ← readRequired [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let text ← readOptional [53, 56] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let transactTime ← readOptional [54, 48] tokens
  let tradeDate ← readOptional [55, 53] tokens
  let execBroker ← readOptional [55, 54] tokens
  let ordRejReason ← readOptional [49, 48, 51] tokens
  let clientID ← readRequired [49, 48, 57] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let maxFloor ← readOptional [49, 49, 49] tokens
  let expireTime ← readOptional [49, 50, 54] tokens
  let execType ← readRequired [49, 53, 48] tokens
  let leavesQty ← readRequired [49, 53, 49] tokens
  let secondaryOrderID ← readOptional [49, 57, 56] tokens
  let pegDifference ← readOptional [50, 49, 49] tokens
  let noContraBrokers ← readGroup [51, 56, 50] [51, 55, 53] NoContraBrokers.members NoContraBrokers.decode tokens
  let execRestatementReason ← readOptional [51, 55, 56] tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let orderCapacity ← readOptional [53, 50, 56] tokens
  let orderRestrictions ← readOptional [53, 50, 57] tokens
  let clOrdLinkID ← readOptional [53, 56, 51] tokens
  let tradeID ← readOptional [49, 48, 48, 51] tokens
  let displayQty ← readOptional [49, 49, 51, 56] tokens
  let clearingAccountType ← readOptional [49, 56, 49, 54] tokens
  let subMktID ← readOptional [53, 56, 49, 53] tokens
  let clRefID ← readOptional [54, 50, 48, 57] tokens
  let displayRange ← readOptional [54, 50, 50, 55] tokens
  let displayInst ← readOptional [57, 49, 52, 48] tokens
  let crossTradeFlag ← readOptional [57, 51, 53, 53] tokens
  let brSeqNbr ← readOptional [57, 56, 54, 49] tokens
  let liquidityFlag ← readOptional [57, 56, 56, 50] tokens
  let effectiveTime ← readOptional [49, 54, 56] tokens
  let targetVolume ← readOptional [50, 48, 48, 48, 49] tokens
  let maximumVolume ← readOptional [56, 52, 57] tokens
  let minimumVolume ← readOptional [50, 48, 48, 48, 51] tokens
  let aggression ← readOptional [50, 48, 48, 48, 50] tokens
  let minChildOrderValue ← readOptional [50, 48, 48, 51, 48] tokens
  let spreadLimit ← readOptional [50, 48, 48, 50, 48] tokens
  let refPriceBidLeg ← readOptional [50, 48, 48, 50, 49] tokens
  let refPriceAskLeg ← readOptional [50, 48, 48, 50, 50] tokens
  let lagBidLeg ← readOptional [50, 48, 48, 50, 51] tokens
  let lagAskLeg ← readOptional [50, 48, 48, 50, 52] tokens
  let leadBidLeg ← readOptional [50, 48, 48, 50, 53] tokens
  let leadAskLeg ← readOptional [50, 48, 48, 50, 54] tokens
  let stopLossBidLeg ← readOptional [50, 48, 48, 50, 55] tokens
  let stopLossAskLeg ← readOptional [50, 48, 48, 50, 56] tokens
  let basketID ← readOptional [50, 48, 48, 50, 57] tokens
  let ratio ← readOptional [50, 48, 48, 51, 49] tokens
  let iWouldPrice ← readOptional [50, 48, 48, 48, 54] tokens
  let iWouldType ← readOptional [50, 48, 48, 48, 55] tokens
  let iWouldQty ← readOptional [50, 48, 48, 48, 53] tokens
  let cleanUpType ← readOptional [50, 48, 48, 49, 50] tokens
  let cleanUpQty ← readOptional [50, 48, 48, 49, 51] tokens
  let blockFilter ← readOptional [50, 48, 48, 48, 52] tokens
  let onOpenType ← readOptional [50, 48, 48, 49, 48] tokens
  let onOpenQty ← readOptional [50, 48, 48, 48, 56] tokens
  let onCloseType ← readOptional [50, 48, 48, 49, 49] tokens
  let onCloseQty ← readOptional [50, 48, 48, 48, 57] tokens
  let dynamicBenchmark ← readOptional [50, 48, 48, 49, 52] tokens
  let dynamicPrice ← readOptional [50, 48, 48, 49, 53] tokens
  let inMoneyStyle ← readOptional [50, 48, 48, 49, 54] tokens
  let outMoneyStyle ← readOptional [50, 48, 48, 49, 56] tokens
  let sTPLevel ← readOptional [50, 48, 49, 48, 49] tokens
  let sTPAction ← readOptional [50, 48, 49, 48, 50] tokens
  let sTPTraderGroup ← readOptional [50, 48, 49, 48, 51] tokens
  let lastExecFlagINT ← readOptional [50, 48, 49, 48, 52] tokens
  let lastExecFlagTOP ← readOptional [50, 48, 49, 48, 53] tokens
  let lastExecFlagSTP ← readOptional [50, 48, 49, 48, 54] tokens
  let lastLiquidityInd ← readOptional [56, 53, 49] tokens
  let noOrderAttributes ← readGroup [50, 53, 57, 51] [50, 53, 57, 52] NoOrderAttributes.members NoOrderAttributes.decode tokens
  let tradeReportTransType ← readOptional [52, 56, 55] tokens
  let algoIndicator ← readOptional [50, 54, 54, 55] tokens
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let venueType ← readOptional [49, 52, 51, 48] tokens
  let tradingSessionSubID ← readOptional [54, 50, 53] tokens
  let matchType ← readOptional [53, 55, 52] tokens
  let trdType ← readOptional [56, 50, 56] tokens
  let orderCategory ← readOptional [49, 49, 49, 53] tokens
  let orderOriginator ← readOptional [49, 55, 50, 52] tokens
  let noTrdRegPublications ← readGroup [50, 54, 54, 56] [50, 54, 54, 57] NoTrdRegPublications.members NoTrdRegPublications.decode tokens
  let tradingAtClosingPrice ← readOptional [50, 48, 51, 48, 49] tokens
  let originalOrderReferenceNumber ← readOptional [50, 48, 49, 48, 55] tokens
  let originalOrderEntryDate ← readOptional [50, 48, 49, 48, 56] tokens
  let orderCondition ← readOptional [50, 48, 49, 48, 57] tokens
  let custOrderCapacity ← readOptional [53, 56, 50] tokens
  pure { avgPx, clOrdID, cumQty, currency, execID, execInst, execRefID, iDSource, lastMkt, lastPx, lastShares, orderID, orderQty, ordStatus, ordType, origClOrdID, price, securityID, side, symbol, text, timeInForce, transactTime, tradeDate, execBroker, ordRejReason, clientID, minQty, maxFloor, expireTime, execType, leavesQty, secondaryOrderID, pegDifference, noContraBrokers, execRestatementReason, clearingFirm, clearingAccount, orderCapacity, orderRestrictions, clOrdLinkID, tradeID, displayQty, clearingAccountType, subMktID, clRefID, displayRange, displayInst, crossTradeFlag, brSeqNbr, liquidityFlag, effectiveTime, targetVolume, maximumVolume, minimumVolume, aggression, minChildOrderValue, spreadLimit, refPriceBidLeg, refPriceAskLeg, lagBidLeg, lagAskLeg, leadBidLeg, leadAskLeg, stopLossBidLeg, stopLossAskLeg, basketID, ratio, iWouldPrice, iWouldType, iWouldQty, cleanUpType, cleanUpQty, blockFilter, onOpenType, onOpenQty, onCloseType, onCloseQty, dynamicBenchmark, dynamicPrice, inMoneyStyle, outMoneyStyle, sTPLevel, sTPAction, sTPTraderGroup, lastExecFlagINT, lastExecFlagTOP, lastExecFlagSTP, lastLiquidityInd, noOrderAttributes, tradeReportTransType, algoIndicator, noPartyIDs, venueType, tradingSessionSubID, matchType, trdType, orderCategory, orderOriginator, noTrdRegPublications, tradingAtClosingPrice, originalOrderReferenceNumber, originalOrderEntryDate, orderCondition, custOrderCapacity }

theorem ExecutionReport.decode_agrees (record : ExecutionReport) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReport.decode tokens = some record := by
  have distinct : ExecutionReport.tags.flatten.Nodup := by decide +kernel
  have avgPx := readRequired_part [54] record.avgPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have cumQty := readRequired_part [49, 52] record.cumQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have currency := readOptional_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have execID := readRequired_part [49, 55] record.execID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have execRefID := readOptional_part [49, 57] record.execRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have iDSource := readOptional_part [50, 50] record.iDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have lastMkt := readOptional_part [51, 48] record.lastMkt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have lastPx := readOptional_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have lastShares := readOptional_part [51, 50] record.lastShares tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have orderQty := readOptional_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have ordType := readOptional_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have tradeDate := readOptional_part [55, 53] record.tradeDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have execBroker := readOptional_part [55, 54] record.execBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have ordRejReason := readOptional_part [49, 48, 51] record.ordRejReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have clientID := readRequired_part [49, 48, 57] record.clientID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have maxFloor := readOptional_part [49, 49, 49] record.maxFloor tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have expireTime := readOptional_part [49, 50, 54] record.expireTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have execType := readRequired_part [49, 53, 48] record.execType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have leavesQty := readRequired_part [49, 53, 49] record.leavesQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have secondaryOrderID := readOptional_part [49, 57, 56] record.secondaryOrderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have pegDifference := readOptional_part [50, 49, 49] record.pegDifference tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have noContraBrokers := readGroup_part [51, 56, 50] [51, 55, 53] NoContraBrokers.members NoContraBrokers.encode NoContraBrokers.within NoContraBrokers.decode NoContraBrokers.decode_encode NoContraBrokers.led record.noContraBrokers tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have execRestatementReason := readOptional_part [51, 55, 56] record.execRestatementReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have orderCapacity := readOptional_part [53, 50, 56] record.orderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  have orderRestrictions := readOptional_part [53, 50, 57] record.orderRestrictions tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 39 (by decide +kernel)))
  have clOrdLinkID := readOptional_part [53, 56, 51] record.clOrdLinkID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 40 (by decide +kernel)))
  have tradeID := readOptional_part [49, 48, 48, 51] record.tradeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 41 (by decide +kernel)))
  have displayQty := readOptional_part [49, 49, 51, 56] record.displayQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 42 (by decide +kernel)))
  have clearingAccountType := readOptional_part [49, 56, 49, 54] record.clearingAccountType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 43 (by decide +kernel)))
  have subMktID := readOptional_part [53, 56, 49, 53] record.subMktID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 44 (by decide +kernel)))
  have clRefID := readOptional_part [54, 50, 48, 57] record.clRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 45 (by decide +kernel)))
  have displayRange := readOptional_part [54, 50, 50, 55] record.displayRange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 46 (by decide +kernel)))
  have displayInst := readOptional_part [57, 49, 52, 48] record.displayInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 47 (by decide +kernel)))
  have crossTradeFlag := readOptional_part [57, 51, 53, 53] record.crossTradeFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 48 (by decide +kernel)))
  have brSeqNbr := readOptional_part [57, 56, 54, 49] record.brSeqNbr tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 49 (by decide +kernel)))
  have liquidityFlag := readOptional_part [57, 56, 56, 50] record.liquidityFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 50 (by decide +kernel)))
  have effectiveTime := readOptional_part [49, 54, 56] record.effectiveTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 51 (by decide +kernel)))
  have targetVolume := readOptional_part [50, 48, 48, 48, 49] record.targetVolume tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 52 (by decide +kernel)))
  have maximumVolume := readOptional_part [56, 52, 57] record.maximumVolume tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 53 (by decide +kernel)))
  have minimumVolume := readOptional_part [50, 48, 48, 48, 51] record.minimumVolume tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 54 (by decide +kernel)))
  have aggression := readOptional_part [50, 48, 48, 48, 50] record.aggression tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 55 (by decide +kernel)))
  have minChildOrderValue := readOptional_part [50, 48, 48, 51, 48] record.minChildOrderValue tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 56 (by decide +kernel)))
  have spreadLimit := readOptional_part [50, 48, 48, 50, 48] record.spreadLimit tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 57 (by decide +kernel)))
  have refPriceBidLeg := readOptional_part [50, 48, 48, 50, 49] record.refPriceBidLeg tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 58 (by decide +kernel)))
  have refPriceAskLeg := readOptional_part [50, 48, 48, 50, 50] record.refPriceAskLeg tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 59 (by decide +kernel)))
  have lagBidLeg := readOptional_part [50, 48, 48, 50, 51] record.lagBidLeg tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 60 (by decide +kernel)))
  have lagAskLeg := readOptional_part [50, 48, 48, 50, 52] record.lagAskLeg tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 61 (by decide +kernel)))
  have leadBidLeg := readOptional_part [50, 48, 48, 50, 53] record.leadBidLeg tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 62 (by decide +kernel)))
  have leadAskLeg := readOptional_part [50, 48, 48, 50, 54] record.leadAskLeg tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 63 (by decide +kernel)))
  have stopLossBidLeg := readOptional_part [50, 48, 48, 50, 55] record.stopLossBidLeg tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 64 (by decide +kernel)))
  have stopLossAskLeg := readOptional_part [50, 48, 48, 50, 56] record.stopLossAskLeg tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 65 (by decide +kernel)))
  have basketID := readOptional_part [50, 48, 48, 50, 57] record.basketID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 66 (by decide +kernel)))
  have ratio := readOptional_part [50, 48, 48, 51, 49] record.ratio tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 67 (by decide +kernel)))
  have iWouldPrice := readOptional_part [50, 48, 48, 48, 54] record.iWouldPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 68 (by decide +kernel)))
  have iWouldType := readOptional_part [50, 48, 48, 48, 55] record.iWouldType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 69 (by decide +kernel)))
  have iWouldQty := readOptional_part [50, 48, 48, 48, 53] record.iWouldQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 70 (by decide +kernel)))
  have cleanUpType := readOptional_part [50, 48, 48, 49, 50] record.cleanUpType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 71 (by decide +kernel)))
  have cleanUpQty := readOptional_part [50, 48, 48, 49, 51] record.cleanUpQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 72 (by decide +kernel)))
  have blockFilter := readOptional_part [50, 48, 48, 48, 52] record.blockFilter tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 73 (by decide +kernel)))
  have onOpenType := readOptional_part [50, 48, 48, 49, 48] record.onOpenType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 74 (by decide +kernel)))
  have onOpenQty := readOptional_part [50, 48, 48, 48, 56] record.onOpenQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 75 (by decide +kernel)))
  have onCloseType := readOptional_part [50, 48, 48, 49, 49] record.onCloseType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 76 (by decide +kernel)))
  have onCloseQty := readOptional_part [50, 48, 48, 48, 57] record.onCloseQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 77 (by decide +kernel)))
  have dynamicBenchmark := readOptional_part [50, 48, 48, 49, 52] record.dynamicBenchmark tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 78 (by decide +kernel)))
  have dynamicPrice := readOptional_part [50, 48, 48, 49, 53] record.dynamicPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 79 (by decide +kernel)))
  have inMoneyStyle := readOptional_part [50, 48, 48, 49, 54] record.inMoneyStyle tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 80 (by decide +kernel)))
  have outMoneyStyle := readOptional_part [50, 48, 48, 49, 56] record.outMoneyStyle tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 81 (by decide +kernel)))
  have sTPLevel := readOptional_part [50, 48, 49, 48, 49] record.sTPLevel tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 82 (by decide +kernel)))
  have sTPAction := readOptional_part [50, 48, 49, 48, 50] record.sTPAction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 83 (by decide +kernel)))
  have sTPTraderGroup := readOptional_part [50, 48, 49, 48, 51] record.sTPTraderGroup tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 84 (by decide +kernel)))
  have lastExecFlagINT := readOptional_part [50, 48, 49, 48, 52] record.lastExecFlagINT tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 85 (by decide +kernel)))
  have lastExecFlagTOP := readOptional_part [50, 48, 49, 48, 53] record.lastExecFlagTOP tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 86 (by decide +kernel)))
  have lastExecFlagSTP := readOptional_part [50, 48, 49, 48, 54] record.lastExecFlagSTP tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 87 (by decide +kernel)))
  have lastLiquidityInd := readOptional_part [56, 53, 49] record.lastLiquidityInd tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 88 (by decide +kernel)))
  have noOrderAttributes := readGroup_part [50, 53, 57, 51] [50, 53, 57, 52] NoOrderAttributes.members NoOrderAttributes.encode NoOrderAttributes.within NoOrderAttributes.decode NoOrderAttributes.decode_encode NoOrderAttributes.led record.noOrderAttributes tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 89 (by decide +kernel)))
  have tradeReportTransType := readOptional_part [52, 56, 55] record.tradeReportTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 90 (by decide +kernel)))
  have algoIndicator := readOptional_part [50, 54, 54, 55] record.algoIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 91 (by decide +kernel)))
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 92 (by decide +kernel)))
  have venueType := readOptional_part [49, 52, 51, 48] record.venueType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 93 (by decide +kernel)))
  have tradingSessionSubID := readOptional_part [54, 50, 53] record.tradingSessionSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 94 (by decide +kernel)))
  have matchType := readOptional_part [53, 55, 52] record.matchType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 95 (by decide +kernel)))
  have trdType := readOptional_part [56, 50, 56] record.trdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 96 (by decide +kernel)))
  have orderCategory := readOptional_part [49, 49, 49, 53] record.orderCategory tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 97 (by decide +kernel)))
  have orderOriginator := readOptional_part [49, 55, 50, 52] record.orderOriginator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 98 (by decide +kernel)))
  have noTrdRegPublications := readGroup_part [50, 54, 54, 56] [50, 54, 54, 57] NoTrdRegPublications.members NoTrdRegPublications.encode NoTrdRegPublications.within NoTrdRegPublications.decode NoTrdRegPublications.decode_encode NoTrdRegPublications.led record.noTrdRegPublications tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 99 (by decide +kernel)))
  have tradingAtClosingPrice := readOptional_part [50, 48, 51, 48, 49] record.tradingAtClosingPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 100 (by decide +kernel)))
  have originalOrderReferenceNumber := readOptional_part [50, 48, 49, 48, 55] record.originalOrderReferenceNumber tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 101 (by decide +kernel)))
  have originalOrderEntryDate := readOptional_part [50, 48, 49, 48, 56] record.originalOrderEntryDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 102 (by decide +kernel)))
  have orderCondition := readOptional_part [50, 48, 49, 48, 57] record.orderCondition tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 103 (by decide +kernel)))
  have custOrderCapacity := readOptional_part [53, 56, 50] record.custOrderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 104 (by decide +kernel)))
  simp only [ExecutionReport.decode, avgPx, clOrdID, cumQty, currency, execID, execInst, execRefID, iDSource, lastMkt, lastPx, lastShares, orderID, orderQty, ordStatus, ordType, origClOrdID, price, securityID, side, symbol, text, timeInForce, transactTime, tradeDate, execBroker, ordRejReason, clientID, minQty, maxFloor, expireTime, execType, leavesQty, secondaryOrderID, pegDifference, noContraBrokers, execRestatementReason, clearingFirm, clearingAccount, orderCapacity, orderRestrictions, clOrdLinkID, tradeID, displayQty, clearingAccountType, subMktID, clRefID, displayRange, displayInst, crossTradeFlag, brSeqNbr, liquidityFlag, effectiveTime, targetVolume, maximumVolume, minimumVolume, aggression, minChildOrderValue, spreadLimit, refPriceBidLeg, refPriceAskLeg, lagBidLeg, lagAskLeg, leadBidLeg, leadAskLeg, stopLossBidLeg, stopLossAskLeg, basketID, ratio, iWouldPrice, iWouldType, iWouldQty, cleanUpType, cleanUpQty, blockFilter, onOpenType, onOpenQty, onCloseType, onCloseQty, dynamicBenchmark, dynamicPrice, inMoneyStyle, outMoneyStyle, sTPLevel, sTPAction, sTPTraderGroup, lastExecFlagINT, lastExecFlagTOP, lastExecFlagSTP, lastLiquidityInd, noOrderAttributes, tradeReportTransType, algoIndicator, noPartyIDs, venueType, tradingSessionSubID, matchType, trdType, orderCategory, orderOriginator, noTrdRegPublications, tradingAtClosingPrice, originalOrderReferenceNumber, originalOrderEntryDate, orderCondition, custOrderCapacity, some_bind] <;> rfl

structure OrderCancelReject where
  clOrdID : Terminated 1  -- tag 11
  orderID : Terminated 1  -- tag 37
  ordStatus : Terminated 1  -- tag 39
  origClOrdID : Terminated 1  -- tag 41
  text : Option (Terminated 1)  -- tag 58
  transactTime : Option (Terminated 1)  -- tag 60
  cxlRejReason : Option (Terminated 1)  -- tag 102
  clientID : Terminated 1  -- tag 109
  cxlRejResponseTo : Terminated 1  -- tag 434

def OrderCancelReject.parts (record : OrderCancelReject) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.required [51, 55] record.orderID,
   Part.required [51, 57] record.ordStatus,
   Part.required [52, 49] record.origClOrdID,
   Part.optional [53, 56] record.text,
   Part.optional [54, 48] record.transactTime,
   Part.optional [49, 48, 50] record.cxlRejReason,
   Part.required [49, 48, 57] record.clientID,
   Part.required [52, 51, 52] record.cxlRejResponseTo]

def OrderCancelReject.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[51, 55]], [[51, 57]], [[52, 49]], [[53, 56]], [[54, 48]], [[49, 48, 50]], [[49, 48, 57]], [[52, 51, 52]]]

theorem OrderCancelReject.shape (record : OrderCancelReject) : record.parts.map Part.tags = OrderCancelReject.tags := rfl

def OrderCancelReject.decode (tokens : List Token) : Option OrderCancelReject := do
  let clOrdID ← readRequired [49, 49] tokens
  let orderID ← readRequired [51, 55] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let text ← readOptional [53, 56] tokens
  let transactTime ← readOptional [54, 48] tokens
  let cxlRejReason ← readOptional [49, 48, 50] tokens
  let clientID ← readRequired [49, 48, 57] tokens
  let cxlRejResponseTo ← readRequired [52, 51, 52] tokens
  pure { clOrdID, orderID, ordStatus, origClOrdID, text, transactTime, cxlRejReason, clientID, cxlRejResponseTo }

theorem OrderCancelReject.decode_agrees (record : OrderCancelReject) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelReject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelReject.decode tokens = some record := by
  have distinct : OrderCancelReject.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have cxlRejReason := readOptional_part [49, 48, 50] record.cxlRejReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have clientID := readRequired_part [49, 48, 57] record.clientID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have cxlRejResponseTo := readRequired_part [52, 51, 52] record.cxlRejResponseTo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  simp only [OrderCancelReject.decode, clOrdID, orderID, ordStatus, origClOrdID, text, transactTime, cxlRejReason, clientID, cxlRejResponseTo, some_bind] <;> rfl

inductive Message where
  | reject (header : Header) (r0 : Reject)
  | heartbeat (header : Header) (r0 : Heartbeat)
  | logon (header : Header) (r0 : Logon)
  | testRequest (header : Header) (r0 : TestRequest)
  | resendRequest (header : Header) (r0 : ResendRequest)
  | sequenceReset (header : Header) (r0 : SequenceReset)
  | logout (header : Header) (r0 : Logout)
  | executionReport (header : Header) (r0 : ExecutionReport)
  | orderCancelReject (header : Header) (r0 : OrderCancelReject)

def Message.tokens : Message → List Token
  | .reject header r0 => ⟨[51, 53], ⟨[51], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .heartbeat header r0 => ⟨[51, 53], ⟨[48], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logon header r0 => ⟨[51, 53], ⟨[65], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .testRequest header r0 => ⟨[51, 53], ⟨[49], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .resendRequest header r0 => ⟨[51, 53], ⟨[50], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .sequenceReset header r0 => ⟨[51, 53], ⟨[52], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logout header r0 => ⟨[51, 53], ⟨[53], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .executionReport header r0 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelReject header r0 => ⟨[51, 53], ⟨[57], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)

def Message.decode : List Token → Option Message
  | [] => none
  | token :: rest =>
    if token.tag = [51, 53] then
      if token.value.val = [51] then
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
      else if token.value.val = [65] then
        if known (Header.tags ++ Logon.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Logon.decode rest
          pure (.logon header r0)
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
      else if token.value.val = [52] then
        if known (Header.tags ++ SequenceReset.tags) rest then do
          let header ← Header.decode rest
          let r0 ← SequenceReset.decode rest
          pure (.sequenceReset header r0)
        else none
      else if token.value.val = [53] then
        if known (Header.tags ++ Logout.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Logout.decode rest
          pure (.logout header r0)
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
      else none
    else none

theorem Message.decode_reject (header : Header) (r0 : Reject) :
    Message.decode (Message.tokens (.reject header r0)) = some (.reject header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (Reject.tags) rfl rfl (by decide +kernel))
  have c1 := Reject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (Reject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ Reject.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, some_bind] <;> rfl

theorem Message.decode_heartbeat (header : Header) (r0 : Heartbeat) :
    Message.decode (Message.tokens (.heartbeat header r0)) = some (.heartbeat header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (Heartbeat.tags) rfl rfl (by decide +kernel))
  have c1 := Heartbeat.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (Heartbeat.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ Heartbeat.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_logon (header : Header) (r0 : Logon) :
    Message.decode (Message.tokens (.logon header r0)) = some (.logon header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (Logon.tags) rfl rfl (by decide +kernel))
  have c1 := Logon.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (Logon.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ Logon.tags) rfl
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

theorem Message.decode_sequenceReset (header : Header) (r0 : SequenceReset) :
    Message.decode (Message.tokens (.sequenceReset header r0)) = some (.sequenceReset header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (SequenceReset.tags) rfl rfl (by decide +kernel))
  have c1 := SequenceReset.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (SequenceReset.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ SequenceReset.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_logout (header : Header) (r0 : Logout) :
    Message.decode (Message.tokens (.logout header r0)) = some (.logout header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (Logout.tags) rfl rfl (by decide +kernel))
  have c1 := Logout.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (Logout.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ Logout.tags) rfl
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

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | reject header r0 => exact Message.decode_reject header r0
  | heartbeat header r0 => exact Message.decode_heartbeat header r0
  | logon header r0 => exact Message.decode_logon header r0
  | testRequest header r0 => exact Message.decode_testRequest header r0
  | resendRequest header r0 => exact Message.decode_resendRequest header r0
  | sequenceReset header r0 => exact Message.decode_sequenceReset header r0
  | logout header r0 => exact Message.decode_logout header r0
  | executionReport header r0 => exact Message.decode_executionReport header r0
  | orderCancelReject header r0 => exact Message.decode_orderCancelReject header r0

def Message.encode (message : Message) : List UInt8 := encodeTokens message.tokens

def Message.decodeBytes (bytes : List UInt8) : Option Message := do
  let tokens ← decodeTokens bytes.length bytes
  Message.decode tokens

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

theorem Message.decodeBytes_logon (header : Header) (r0 : Logon) :
    Message.decodeBytes (Message.encode (.logon header r0)) = some (.logon header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[65], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ Logon.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_logon header r0

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

theorem Message.decodeBytes_sequenceReset (header : Header) (r0 : SequenceReset) :
    Message.decodeBytes (Message.encode (.sequenceReset header r0)) = some (.sequenceReset header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[52], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ SequenceReset.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_sequenceReset header r0

theorem Message.decodeBytes_logout (header : Header) (r0 : Logout) :
    Message.decodeBytes (Message.encode (.logout header r0)) = some (.logout header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[53], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ Logout.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_logout header r0

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

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | reject header r0 => exact Message.decodeBytes_reject header r0
  | heartbeat header r0 => exact Message.decodeBytes_heartbeat header r0
  | logon header r0 => exact Message.decodeBytes_logon header r0
  | testRequest header r0 => exact Message.decodeBytes_testRequest header r0
  | resendRequest header r0 => exact Message.decodeBytes_resendRequest header r0
  | sequenceReset header r0 => exact Message.decodeBytes_sequenceReset header r0
  | logout header r0 => exact Message.decodeBytes_logout header r0
  | executionReport header r0 => exact Message.decodeBytes_executionReport header r0
  | orderCancelReject header r0 => exact Message.decodeBytes_orderCancelReject header r0

/-- BeginString as the venue fixes it: FIXT.1.1 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 84, 46, 49, 46, 49, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.NasdaqNordicequitiesDropcopyFixV2014Exchange
