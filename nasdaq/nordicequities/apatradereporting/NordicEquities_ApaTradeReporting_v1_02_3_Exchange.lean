import Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq)  v1.02.3, Exchange messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.NasdaqNordicequitiesApatradereportingFixV1023Exchange

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

structure NoTrdRegTimestamps where
  trdRegTimestamp : Terminated 1  -- tag 769
  trdRegTimestampType : Option (Terminated 1)  -- tag 770

def NoTrdRegTimestamps.parts (record : NoTrdRegTimestamps) : List Part :=
  [Part.required [55, 54, 57] record.trdRegTimestamp,
   Part.optional [55, 55, 48] record.trdRegTimestampType]

def NoTrdRegTimestamps.tags : List (List (List UInt8)) :=
  [[[55, 54, 57]], [[55, 55, 48]]]

theorem NoTrdRegTimestamps.shape (record : NoTrdRegTimestamps) : record.parts.map Part.tags = NoTrdRegTimestamps.tags := rfl

def NoTrdRegTimestamps.decode (tokens : List Token) : Option NoTrdRegTimestamps := do
  let trdRegTimestamp ← readRequired [55, 54, 57] tokens
  let trdRegTimestampType ← readOptional [55, 55, 48] tokens
  pure { trdRegTimestamp, trdRegTimestampType }

theorem NoTrdRegTimestamps.decode_agrees (record : NoTrdRegTimestamps) (tokens : List Token)
    (agrees : ∀ tags ∈ NoTrdRegTimestamps.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoTrdRegTimestamps.decode tokens = some record := by
  have distinct : NoTrdRegTimestamps.tags.flatten.Nodup := by decide +kernel
  have trdRegTimestamp := readRequired_part [55, 54, 57] record.trdRegTimestamp tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have trdRegTimestampType := readOptional_part [55, 55, 48] record.trdRegTimestampType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [NoTrdRegTimestamps.decode, trdRegTimestamp, trdRegTimestampType, some_bind] <;> rfl

def NoTrdRegTimestamps.members : List (List UInt8) := NoTrdRegTimestamps.tags.flatten

def NoTrdRegTimestamps.encode (entry : NoTrdRegTimestamps) : List Token := encodeParts entry.parts

theorem NoTrdRegTimestamps.decode_encode (entry : NoTrdRegTimestamps) : NoTrdRegTimestamps.decode entry.encode = some entry :=
  NoTrdRegTimestamps.decode_agrees entry _ (fun _ _ => rfl)

theorem NoTrdRegTimestamps.within (entry : NoTrdRegTimestamps) : ∀ token ∈ entry.encode, token.tag ∈ NoTrdRegTimestamps.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoTrdRegTimestamps.shape] at this

theorem NoTrdRegTimestamps.led (entry : NoTrdRegTimestamps) : Lead [55, 54, 57] entry.encode :=
  lead_parts [55, 54, 57] entry.trdRegTimestamp _ NoTrdRegTimestamps.tags.tail rfl (by decide +kernel)

structure NoTradePriceConditions where
  tradePriceCondition : Terminated 1  -- tag 1839

def NoTradePriceConditions.parts (record : NoTradePriceConditions) : List Part :=
  [Part.required [49, 56, 51, 57] record.tradePriceCondition]

def NoTradePriceConditions.tags : List (List (List UInt8)) :=
  [[[49, 56, 51, 57]]]

theorem NoTradePriceConditions.shape (record : NoTradePriceConditions) : record.parts.map Part.tags = NoTradePriceConditions.tags := rfl

def NoTradePriceConditions.decode (tokens : List Token) : Option NoTradePriceConditions := do
  let tradePriceCondition ← readRequired [49, 56, 51, 57] tokens
  pure { tradePriceCondition }

theorem NoTradePriceConditions.decode_agrees (record : NoTradePriceConditions) (tokens : List Token)
    (agrees : ∀ tags ∈ NoTradePriceConditions.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoTradePriceConditions.decode tokens = some record := by
  have distinct : NoTradePriceConditions.tags.flatten.Nodup := by decide +kernel
  have tradePriceCondition := readRequired_part [49, 56, 51, 57] record.tradePriceCondition tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [NoTradePriceConditions.decode, tradePriceCondition, some_bind] <;> rfl

def NoTradePriceConditions.members : List (List UInt8) := NoTradePriceConditions.tags.flatten

def NoTradePriceConditions.encode (entry : NoTradePriceConditions) : List Token := encodeParts entry.parts

theorem NoTradePriceConditions.decode_encode (entry : NoTradePriceConditions) : NoTradePriceConditions.decode entry.encode = some entry :=
  NoTradePriceConditions.decode_agrees entry _ (fun _ _ => rfl)

theorem NoTradePriceConditions.within (entry : NoTradePriceConditions) : ∀ token ∈ entry.encode, token.tag ∈ NoTradePriceConditions.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoTradePriceConditions.shape] at this

theorem NoTradePriceConditions.led (entry : NoTradePriceConditions) : Lead [49, 56, 51, 57] entry.encode :=
  lead_parts [49, 56, 51, 57] entry.tradePriceCondition _ NoTradePriceConditions.tags.tail rfl (by decide +kernel)

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

structure TradeCaptureReportAck where
  tradeReportID : Terminated 1  -- tag 571
  tradeReportType : Terminated 1  -- tag 856
  tradeHandlingInstr : Terminated 1  -- tag 1123
  tradeID : Option (Terminated 1)  -- tag 1003
  symbol : Terminated 1  -- tag 55
  securityIDSource : Option (Terminated 1)  -- tag 22
  securityID : Option (Terminated 1)  -- tag 48
  currency : Option (Terminated 1)  -- tag 15
  lastPx : Option (Terminated 1)  -- tag 31
  lastQty : Terminated 1  -- tag 32
  priceType : Option (Terminated 1)  -- tag 423
  assetType : Option (Terminated 1)  -- tag 1940
  tradeClearingInstruction : Option (Terminated 1)  -- tag 1925
  strikeValue : Option (Terminated 1)  -- tag 968
  strikeCurrency : Option (Terminated 1)  -- tag 947
  unitOfMeasure : Option (Terminated 1)  -- tag 996
  unitOfMeasureQty : Option (Terminated 1)  -- tag 1147
  transactTime : Option (Terminated 1)  -- tag 60
  noTrdRegTimestamps : List NoTrdRegTimestamps  -- tag 768
  venueType : Option (Terminated 1)  -- tag 1430
  matchType : Terminated 1  -- tag 574
  trdType : Option (Terminated 1)  -- tag 828
  tradeType : Option (Terminated 1)  -- tag 20202
  trdSubType : Option (Terminated 1)  -- tag 829
  secondaryTrdType : Option (Terminated 1)  -- tag 855
  tertiaryTrdType : Option (Terminated 1)  -- tag 2896
  noTradePriceConditions : List NoTradePriceConditions  -- tag 1838
  execMethod : Option (Terminated 1)  -- tag 2405
  tradePublishIndicator : Option (Terminated 1)  -- tag 1390
  noTrdRegPublications : List NoTrdRegPublications  -- tag 2668
  regulatoryReportType : Option (Terminated 1)  -- tag 1934
  investorCountryOfResidence : Option (Terminated 1)  -- tag 475
  rptTime : Option (Terminated 1)  -- tag 7570
  previouslyReported : Option (Terminated 1)  -- tag 570
  tradeReportTransType : Option (Terminated 1)  -- tag 487
  trdRptStatus : Option (Terminated 1)  -- tag 939
  tradeReportRejectReason : Option (Terminated 1)  -- tag 751
  text : Option (Terminated 1)  -- tag 58
  lastMkt : Option (Terminated 1)  -- tag 30

def TradeCaptureReportAck.parts (record : TradeCaptureReportAck) : List Part :=
  [Part.required [53, 55, 49] record.tradeReportID,
   Part.required [56, 53, 54] record.tradeReportType,
   Part.required [49, 49, 50, 51] record.tradeHandlingInstr,
   Part.optional [49, 48, 48, 51] record.tradeID,
   Part.required [53, 53] record.symbol,
   Part.optional [50, 50] record.securityIDSource,
   Part.optional [52, 56] record.securityID,
   Part.optional [49, 53] record.currency,
   Part.optional [51, 49] record.lastPx,
   Part.required [51, 50] record.lastQty,
   Part.optional [52, 50, 51] record.priceType,
   Part.optional [49, 57, 52, 48] record.assetType,
   Part.optional [49, 57, 50, 53] record.tradeClearingInstruction,
   Part.optional [57, 54, 56] record.strikeValue,
   Part.optional [57, 52, 55] record.strikeCurrency,
   Part.optional [57, 57, 54] record.unitOfMeasure,
   Part.optional [49, 49, 52, 55] record.unitOfMeasureQty,
   Part.optional [54, 48] record.transactTime,
   Part.group [55, 54, 56] NoTrdRegTimestamps.members NoTrdRegTimestamps.encode NoTrdRegTimestamps.within record.noTrdRegTimestamps,
   Part.optional [49, 52, 51, 48] record.venueType,
   Part.required [53, 55, 52] record.matchType,
   Part.optional [56, 50, 56] record.trdType,
   Part.optional [50, 48, 50, 48, 50] record.tradeType,
   Part.optional [56, 50, 57] record.trdSubType,
   Part.optional [56, 53, 53] record.secondaryTrdType,
   Part.optional [50, 56, 57, 54] record.tertiaryTrdType,
   Part.group [49, 56, 51, 56] NoTradePriceConditions.members NoTradePriceConditions.encode NoTradePriceConditions.within record.noTradePriceConditions,
   Part.optional [50, 52, 48, 53] record.execMethod,
   Part.optional [49, 51, 57, 48] record.tradePublishIndicator,
   Part.group [50, 54, 54, 56] NoTrdRegPublications.members NoTrdRegPublications.encode NoTrdRegPublications.within record.noTrdRegPublications,
   Part.optional [49, 57, 51, 52] record.regulatoryReportType,
   Part.optional [52, 55, 53] record.investorCountryOfResidence,
   Part.optional [55, 53, 55, 48] record.rptTime,
   Part.optional [53, 55, 48] record.previouslyReported,
   Part.optional [52, 56, 55] record.tradeReportTransType,
   Part.optional [57, 51, 57] record.trdRptStatus,
   Part.optional [55, 53, 49] record.tradeReportRejectReason,
   Part.optional [53, 56] record.text,
   Part.optional [51, 48] record.lastMkt]

def TradeCaptureReportAck.tags : List (List (List UInt8)) :=
  [[[53, 55, 49]], [[56, 53, 54]], [[49, 49, 50, 51]], [[49, 48, 48, 51]], [[53, 53]], [[50, 50]], [[52, 56]], [[49, 53]], [[51, 49]], [[51, 50]], [[52, 50, 51]], [[49, 57, 52, 48]], [[49, 57, 50, 53]], [[57, 54, 56]], [[57, 52, 55]], [[57, 57, 54]], [[49, 49, 52, 55]], [[54, 48]], [55, 54, 56] :: NoTrdRegTimestamps.members, [[49, 52, 51, 48]], [[53, 55, 52]], [[56, 50, 56]], [[50, 48, 50, 48, 50]], [[56, 50, 57]], [[56, 53, 53]], [[50, 56, 57, 54]], [49, 56, 51, 56] :: NoTradePriceConditions.members, [[50, 52, 48, 53]], [[49, 51, 57, 48]], [50, 54, 54, 56] :: NoTrdRegPublications.members, [[49, 57, 51, 52]], [[52, 55, 53]], [[55, 53, 55, 48]], [[53, 55, 48]], [[52, 56, 55]], [[57, 51, 57]], [[55, 53, 49]], [[53, 56]], [[51, 48]]]

theorem TradeCaptureReportAck.shape (record : TradeCaptureReportAck) : record.parts.map Part.tags = TradeCaptureReportAck.tags := rfl

def TradeCaptureReportAck.decode (tokens : List Token) : Option TradeCaptureReportAck := do
  let tradeReportID ← readRequired [53, 55, 49] tokens
  let tradeReportType ← readRequired [56, 53, 54] tokens
  let tradeHandlingInstr ← readRequired [49, 49, 50, 51] tokens
  let tradeID ← readOptional [49, 48, 48, 51] tokens
  let symbol ← readRequired [53, 53] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let securityID ← readOptional [52, 56] tokens
  let currency ← readOptional [49, 53] tokens
  let lastPx ← readOptional [51, 49] tokens
  let lastQty ← readRequired [51, 50] tokens
  let priceType ← readOptional [52, 50, 51] tokens
  let assetType ← readOptional [49, 57, 52, 48] tokens
  let tradeClearingInstruction ← readOptional [49, 57, 50, 53] tokens
  let strikeValue ← readOptional [57, 54, 56] tokens
  let strikeCurrency ← readOptional [57, 52, 55] tokens
  let unitOfMeasure ← readOptional [57, 57, 54] tokens
  let unitOfMeasureQty ← readOptional [49, 49, 52, 55] tokens
  let transactTime ← readOptional [54, 48] tokens
  let noTrdRegTimestamps ← readGroup [55, 54, 56] [55, 54, 57] NoTrdRegTimestamps.members NoTrdRegTimestamps.decode tokens
  let venueType ← readOptional [49, 52, 51, 48] tokens
  let matchType ← readRequired [53, 55, 52] tokens
  let trdType ← readOptional [56, 50, 56] tokens
  let tradeType ← readOptional [50, 48, 50, 48, 50] tokens
  let trdSubType ← readOptional [56, 50, 57] tokens
  let secondaryTrdType ← readOptional [56, 53, 53] tokens
  let tertiaryTrdType ← readOptional [50, 56, 57, 54] tokens
  let noTradePriceConditions ← readGroup [49, 56, 51, 56] [49, 56, 51, 57] NoTradePriceConditions.members NoTradePriceConditions.decode tokens
  let execMethod ← readOptional [50, 52, 48, 53] tokens
  let tradePublishIndicator ← readOptional [49, 51, 57, 48] tokens
  let noTrdRegPublications ← readGroup [50, 54, 54, 56] [50, 54, 54, 57] NoTrdRegPublications.members NoTrdRegPublications.decode tokens
  let regulatoryReportType ← readOptional [49, 57, 51, 52] tokens
  let investorCountryOfResidence ← readOptional [52, 55, 53] tokens
  let rptTime ← readOptional [55, 53, 55, 48] tokens
  let previouslyReported ← readOptional [53, 55, 48] tokens
  let tradeReportTransType ← readOptional [52, 56, 55] tokens
  let trdRptStatus ← readOptional [57, 51, 57] tokens
  let tradeReportRejectReason ← readOptional [55, 53, 49] tokens
  let text ← readOptional [53, 56] tokens
  let lastMkt ← readOptional [51, 48] tokens
  pure { tradeReportID, tradeReportType, tradeHandlingInstr, tradeID, symbol, securityIDSource, securityID, currency, lastPx, lastQty, priceType, assetType, tradeClearingInstruction, strikeValue, strikeCurrency, unitOfMeasure, unitOfMeasureQty, transactTime, noTrdRegTimestamps, venueType, matchType, trdType, tradeType, trdSubType, secondaryTrdType, tertiaryTrdType, noTradePriceConditions, execMethod, tradePublishIndicator, noTrdRegPublications, regulatoryReportType, investorCountryOfResidence, rptTime, previouslyReported, tradeReportTransType, trdRptStatus, tradeReportRejectReason, text, lastMkt }

theorem TradeCaptureReportAck.decode_agrees (record : TradeCaptureReportAck) (tokens : List Token)
    (agrees : ∀ tags ∈ TradeCaptureReportAck.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TradeCaptureReportAck.decode tokens = some record := by
  have distinct : TradeCaptureReportAck.tags.flatten.Nodup := by decide +kernel
  have tradeReportID := readRequired_part [53, 55, 49] record.tradeReportID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have tradeReportType := readRequired_part [56, 53, 54] record.tradeReportType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have tradeHandlingInstr := readRequired_part [49, 49, 50, 51] record.tradeHandlingInstr tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have tradeID := readOptional_part [49, 48, 48, 51] record.tradeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have currency := readOptional_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have lastPx := readOptional_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have lastQty := readRequired_part [51, 50] record.lastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have priceType := readOptional_part [52, 50, 51] record.priceType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have assetType := readOptional_part [49, 57, 52, 48] record.assetType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have tradeClearingInstruction := readOptional_part [49, 57, 50, 53] record.tradeClearingInstruction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have strikeValue := readOptional_part [57, 54, 56] record.strikeValue tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have strikeCurrency := readOptional_part [57, 52, 55] record.strikeCurrency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have unitOfMeasure := readOptional_part [57, 57, 54] record.unitOfMeasure tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have unitOfMeasureQty := readOptional_part [49, 49, 52, 55] record.unitOfMeasureQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have noTrdRegTimestamps := readGroup_part [55, 54, 56] [55, 54, 57] NoTrdRegTimestamps.members NoTrdRegTimestamps.encode NoTrdRegTimestamps.within NoTrdRegTimestamps.decode NoTrdRegTimestamps.decode_encode NoTrdRegTimestamps.led record.noTrdRegTimestamps tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have venueType := readOptional_part [49, 52, 51, 48] record.venueType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have matchType := readRequired_part [53, 55, 52] record.matchType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have trdType := readOptional_part [56, 50, 56] record.trdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have tradeType := readOptional_part [50, 48, 50, 48, 50] record.tradeType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have trdSubType := readOptional_part [56, 50, 57] record.trdSubType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have secondaryTrdType := readOptional_part [56, 53, 53] record.secondaryTrdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have tertiaryTrdType := readOptional_part [50, 56, 57, 54] record.tertiaryTrdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have noTradePriceConditions := readGroup_part [49, 56, 51, 56] [49, 56, 51, 57] NoTradePriceConditions.members NoTradePriceConditions.encode NoTradePriceConditions.within NoTradePriceConditions.decode NoTradePriceConditions.decode_encode NoTradePriceConditions.led record.noTradePriceConditions tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have execMethod := readOptional_part [50, 52, 48, 53] record.execMethod tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have tradePublishIndicator := readOptional_part [49, 51, 57, 48] record.tradePublishIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have noTrdRegPublications := readGroup_part [50, 54, 54, 56] [50, 54, 54, 57] NoTrdRegPublications.members NoTrdRegPublications.encode NoTrdRegPublications.within NoTrdRegPublications.decode NoTrdRegPublications.decode_encode NoTrdRegPublications.led record.noTrdRegPublications tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have regulatoryReportType := readOptional_part [49, 57, 51, 52] record.regulatoryReportType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have investorCountryOfResidence := readOptional_part [52, 55, 53] record.investorCountryOfResidence tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have rptTime := readOptional_part [55, 53, 55, 48] record.rptTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have previouslyReported := readOptional_part [53, 55, 48] record.previouslyReported tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have tradeReportTransType := readOptional_part [52, 56, 55] record.tradeReportTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have trdRptStatus := readOptional_part [57, 51, 57] record.trdRptStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have tradeReportRejectReason := readOptional_part [55, 53, 49] record.tradeReportRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have lastMkt := readOptional_part [51, 48] record.lastMkt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  simp only [TradeCaptureReportAck.decode, tradeReportID, tradeReportType, tradeHandlingInstr, tradeID, symbol, securityIDSource, securityID, currency, lastPx, lastQty, priceType, assetType, tradeClearingInstruction, strikeValue, strikeCurrency, unitOfMeasure, unitOfMeasureQty, transactTime, noTrdRegTimestamps, venueType, matchType, trdType, tradeType, trdSubType, secondaryTrdType, tertiaryTrdType, noTradePriceConditions, execMethod, tradePublishIndicator, noTrdRegPublications, regulatoryReportType, investorCountryOfResidence, rptTime, previouslyReported, tradeReportTransType, trdRptStatus, tradeReportRejectReason, text, lastMkt, some_bind] <;> rfl

structure TradeCaptureReport where
  tradeReportID : Terminated 1  -- tag 571
  tradeReportRefID : Terminated 1  -- tag 572
  tradeReportType : Terminated 1  -- tag 856
  tradeHandlingInstr : Terminated 1  -- tag 1123
  tradeID : Option (Terminated 1)  -- tag 1003
  symbol : Terminated 1  -- tag 55
  securityIDSource : Option (Terminated 1)  -- tag 22
  securityID : Option (Terminated 1)  -- tag 48
  currency : Option (Terminated 1)  -- tag 15
  lastPx : Option (Terminated 1)  -- tag 31
  lastQty : Terminated 1  -- tag 32
  priceType : Option (Terminated 1)  -- tag 423
  assetType : Option (Terminated 1)  -- tag 1940
  tradeClearingInstruction : Option (Terminated 1)  -- tag 1925
  strikeValue : Option (Terminated 1)  -- tag 968
  strikeCurrency : Option (Terminated 1)  -- tag 947
  unitOfMeasure : Option (Terminated 1)  -- tag 996
  unitOfMeasureQty : Option (Terminated 1)  -- tag 1147
  transactTime : Option (Terminated 1)  -- tag 60
  noTrdRegTimestamps : List NoTrdRegTimestamps  -- tag 768
  venueType : Option (Terminated 1)  -- tag 1430
  matchType : Terminated 1  -- tag 574
  trdType : Option (Terminated 1)  -- tag 828
  tradeType : Option (Terminated 1)  -- tag 20202
  trdSubType : Option (Terminated 1)  -- tag 829
  secondaryTrdType : Option (Terminated 1)  -- tag 855
  tertiaryTrdType : Option (Terminated 1)  -- tag 2896
  noTradePriceConditions : List NoTradePriceConditions  -- tag 1838
  execMethod : Option (Terminated 1)  -- tag 2405
  tradePublishIndicator : Option (Terminated 1)  -- tag 1390
  noTrdRegPublications : List NoTrdRegPublications  -- tag 2668
  regulatoryReportType : Option (Terminated 1)  -- tag 1934
  investorCountryOfResidence : Option (Terminated 1)  -- tag 475
  rptTime : Option (Terminated 1)  -- tag 7570
  previouslyReported : Option (Terminated 1)  -- tag 570
  tradeReportTransType : Option (Terminated 1)  -- tag 487
  execType : Option (Terminated 1)  -- tag 150
  lastMkt : Option (Terminated 1)  -- tag 30

def TradeCaptureReport.parts (record : TradeCaptureReport) : List Part :=
  [Part.required [53, 55, 49] record.tradeReportID,
   Part.required [53, 55, 50] record.tradeReportRefID,
   Part.required [56, 53, 54] record.tradeReportType,
   Part.required [49, 49, 50, 51] record.tradeHandlingInstr,
   Part.optional [49, 48, 48, 51] record.tradeID,
   Part.required [53, 53] record.symbol,
   Part.optional [50, 50] record.securityIDSource,
   Part.optional [52, 56] record.securityID,
   Part.optional [49, 53] record.currency,
   Part.optional [51, 49] record.lastPx,
   Part.required [51, 50] record.lastQty,
   Part.optional [52, 50, 51] record.priceType,
   Part.optional [49, 57, 52, 48] record.assetType,
   Part.optional [49, 57, 50, 53] record.tradeClearingInstruction,
   Part.optional [57, 54, 56] record.strikeValue,
   Part.optional [57, 52, 55] record.strikeCurrency,
   Part.optional [57, 57, 54] record.unitOfMeasure,
   Part.optional [49, 49, 52, 55] record.unitOfMeasureQty,
   Part.optional [54, 48] record.transactTime,
   Part.group [55, 54, 56] NoTrdRegTimestamps.members NoTrdRegTimestamps.encode NoTrdRegTimestamps.within record.noTrdRegTimestamps,
   Part.optional [49, 52, 51, 48] record.venueType,
   Part.required [53, 55, 52] record.matchType,
   Part.optional [56, 50, 56] record.trdType,
   Part.optional [50, 48, 50, 48, 50] record.tradeType,
   Part.optional [56, 50, 57] record.trdSubType,
   Part.optional [56, 53, 53] record.secondaryTrdType,
   Part.optional [50, 56, 57, 54] record.tertiaryTrdType,
   Part.group [49, 56, 51, 56] NoTradePriceConditions.members NoTradePriceConditions.encode NoTradePriceConditions.within record.noTradePriceConditions,
   Part.optional [50, 52, 48, 53] record.execMethod,
   Part.optional [49, 51, 57, 48] record.tradePublishIndicator,
   Part.group [50, 54, 54, 56] NoTrdRegPublications.members NoTrdRegPublications.encode NoTrdRegPublications.within record.noTrdRegPublications,
   Part.optional [49, 57, 51, 52] record.regulatoryReportType,
   Part.optional [52, 55, 53] record.investorCountryOfResidence,
   Part.optional [55, 53, 55, 48] record.rptTime,
   Part.optional [53, 55, 48] record.previouslyReported,
   Part.optional [52, 56, 55] record.tradeReportTransType,
   Part.optional [49, 53, 48] record.execType,
   Part.optional [51, 48] record.lastMkt]

def TradeCaptureReport.tags : List (List (List UInt8)) :=
  [[[53, 55, 49]], [[53, 55, 50]], [[56, 53, 54]], [[49, 49, 50, 51]], [[49, 48, 48, 51]], [[53, 53]], [[50, 50]], [[52, 56]], [[49, 53]], [[51, 49]], [[51, 50]], [[52, 50, 51]], [[49, 57, 52, 48]], [[49, 57, 50, 53]], [[57, 54, 56]], [[57, 52, 55]], [[57, 57, 54]], [[49, 49, 52, 55]], [[54, 48]], [55, 54, 56] :: NoTrdRegTimestamps.members, [[49, 52, 51, 48]], [[53, 55, 52]], [[56, 50, 56]], [[50, 48, 50, 48, 50]], [[56, 50, 57]], [[56, 53, 53]], [[50, 56, 57, 54]], [49, 56, 51, 56] :: NoTradePriceConditions.members, [[50, 52, 48, 53]], [[49, 51, 57, 48]], [50, 54, 54, 56] :: NoTrdRegPublications.members, [[49, 57, 51, 52]], [[52, 55, 53]], [[55, 53, 55, 48]], [[53, 55, 48]], [[52, 56, 55]], [[49, 53, 48]], [[51, 48]]]

theorem TradeCaptureReport.shape (record : TradeCaptureReport) : record.parts.map Part.tags = TradeCaptureReport.tags := rfl

def TradeCaptureReport.decode (tokens : List Token) : Option TradeCaptureReport := do
  let tradeReportID ← readRequired [53, 55, 49] tokens
  let tradeReportRefID ← readRequired [53, 55, 50] tokens
  let tradeReportType ← readRequired [56, 53, 54] tokens
  let tradeHandlingInstr ← readRequired [49, 49, 50, 51] tokens
  let tradeID ← readOptional [49, 48, 48, 51] tokens
  let symbol ← readRequired [53, 53] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let securityID ← readOptional [52, 56] tokens
  let currency ← readOptional [49, 53] tokens
  let lastPx ← readOptional [51, 49] tokens
  let lastQty ← readRequired [51, 50] tokens
  let priceType ← readOptional [52, 50, 51] tokens
  let assetType ← readOptional [49, 57, 52, 48] tokens
  let tradeClearingInstruction ← readOptional [49, 57, 50, 53] tokens
  let strikeValue ← readOptional [57, 54, 56] tokens
  let strikeCurrency ← readOptional [57, 52, 55] tokens
  let unitOfMeasure ← readOptional [57, 57, 54] tokens
  let unitOfMeasureQty ← readOptional [49, 49, 52, 55] tokens
  let transactTime ← readOptional [54, 48] tokens
  let noTrdRegTimestamps ← readGroup [55, 54, 56] [55, 54, 57] NoTrdRegTimestamps.members NoTrdRegTimestamps.decode tokens
  let venueType ← readOptional [49, 52, 51, 48] tokens
  let matchType ← readRequired [53, 55, 52] tokens
  let trdType ← readOptional [56, 50, 56] tokens
  let tradeType ← readOptional [50, 48, 50, 48, 50] tokens
  let trdSubType ← readOptional [56, 50, 57] tokens
  let secondaryTrdType ← readOptional [56, 53, 53] tokens
  let tertiaryTrdType ← readOptional [50, 56, 57, 54] tokens
  let noTradePriceConditions ← readGroup [49, 56, 51, 56] [49, 56, 51, 57] NoTradePriceConditions.members NoTradePriceConditions.decode tokens
  let execMethod ← readOptional [50, 52, 48, 53] tokens
  let tradePublishIndicator ← readOptional [49, 51, 57, 48] tokens
  let noTrdRegPublications ← readGroup [50, 54, 54, 56] [50, 54, 54, 57] NoTrdRegPublications.members NoTrdRegPublications.decode tokens
  let regulatoryReportType ← readOptional [49, 57, 51, 52] tokens
  let investorCountryOfResidence ← readOptional [52, 55, 53] tokens
  let rptTime ← readOptional [55, 53, 55, 48] tokens
  let previouslyReported ← readOptional [53, 55, 48] tokens
  let tradeReportTransType ← readOptional [52, 56, 55] tokens
  let execType ← readOptional [49, 53, 48] tokens
  let lastMkt ← readOptional [51, 48] tokens
  pure { tradeReportID, tradeReportRefID, tradeReportType, tradeHandlingInstr, tradeID, symbol, securityIDSource, securityID, currency, lastPx, lastQty, priceType, assetType, tradeClearingInstruction, strikeValue, strikeCurrency, unitOfMeasure, unitOfMeasureQty, transactTime, noTrdRegTimestamps, venueType, matchType, trdType, tradeType, trdSubType, secondaryTrdType, tertiaryTrdType, noTradePriceConditions, execMethod, tradePublishIndicator, noTrdRegPublications, regulatoryReportType, investorCountryOfResidence, rptTime, previouslyReported, tradeReportTransType, execType, lastMkt }

theorem TradeCaptureReport.decode_agrees (record : TradeCaptureReport) (tokens : List Token)
    (agrees : ∀ tags ∈ TradeCaptureReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TradeCaptureReport.decode tokens = some record := by
  have distinct : TradeCaptureReport.tags.flatten.Nodup := by decide +kernel
  have tradeReportID := readRequired_part [53, 55, 49] record.tradeReportID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have tradeReportRefID := readRequired_part [53, 55, 50] record.tradeReportRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have tradeReportType := readRequired_part [56, 53, 54] record.tradeReportType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have tradeHandlingInstr := readRequired_part [49, 49, 50, 51] record.tradeHandlingInstr tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have tradeID := readOptional_part [49, 48, 48, 51] record.tradeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have currency := readOptional_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have lastPx := readOptional_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have lastQty := readRequired_part [51, 50] record.lastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have priceType := readOptional_part [52, 50, 51] record.priceType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have assetType := readOptional_part [49, 57, 52, 48] record.assetType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have tradeClearingInstruction := readOptional_part [49, 57, 50, 53] record.tradeClearingInstruction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have strikeValue := readOptional_part [57, 54, 56] record.strikeValue tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have strikeCurrency := readOptional_part [57, 52, 55] record.strikeCurrency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have unitOfMeasure := readOptional_part [57, 57, 54] record.unitOfMeasure tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have unitOfMeasureQty := readOptional_part [49, 49, 52, 55] record.unitOfMeasureQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have noTrdRegTimestamps := readGroup_part [55, 54, 56] [55, 54, 57] NoTrdRegTimestamps.members NoTrdRegTimestamps.encode NoTrdRegTimestamps.within NoTrdRegTimestamps.decode NoTrdRegTimestamps.decode_encode NoTrdRegTimestamps.led record.noTrdRegTimestamps tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have venueType := readOptional_part [49, 52, 51, 48] record.venueType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have matchType := readRequired_part [53, 55, 52] record.matchType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have trdType := readOptional_part [56, 50, 56] record.trdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have tradeType := readOptional_part [50, 48, 50, 48, 50] record.tradeType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have trdSubType := readOptional_part [56, 50, 57] record.trdSubType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have secondaryTrdType := readOptional_part [56, 53, 53] record.secondaryTrdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have tertiaryTrdType := readOptional_part [50, 56, 57, 54] record.tertiaryTrdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have noTradePriceConditions := readGroup_part [49, 56, 51, 56] [49, 56, 51, 57] NoTradePriceConditions.members NoTradePriceConditions.encode NoTradePriceConditions.within NoTradePriceConditions.decode NoTradePriceConditions.decode_encode NoTradePriceConditions.led record.noTradePriceConditions tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have execMethod := readOptional_part [50, 52, 48, 53] record.execMethod tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have tradePublishIndicator := readOptional_part [49, 51, 57, 48] record.tradePublishIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have noTrdRegPublications := readGroup_part [50, 54, 54, 56] [50, 54, 54, 57] NoTrdRegPublications.members NoTrdRegPublications.encode NoTrdRegPublications.within NoTrdRegPublications.decode NoTrdRegPublications.decode_encode NoTrdRegPublications.led record.noTrdRegPublications tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have regulatoryReportType := readOptional_part [49, 57, 51, 52] record.regulatoryReportType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have investorCountryOfResidence := readOptional_part [52, 55, 53] record.investorCountryOfResidence tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have rptTime := readOptional_part [55, 53, 55, 48] record.rptTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have previouslyReported := readOptional_part [53, 55, 48] record.previouslyReported tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have tradeReportTransType := readOptional_part [52, 56, 55] record.tradeReportTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have execType := readOptional_part [49, 53, 48] record.execType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have lastMkt := readOptional_part [51, 48] record.lastMkt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  simp only [TradeCaptureReport.decode, tradeReportID, tradeReportRefID, tradeReportType, tradeHandlingInstr, tradeID, symbol, securityIDSource, securityID, currency, lastPx, lastQty, priceType, assetType, tradeClearingInstruction, strikeValue, strikeCurrency, unitOfMeasure, unitOfMeasureQty, transactTime, noTrdRegTimestamps, venueType, matchType, trdType, tradeType, trdSubType, secondaryTrdType, tertiaryTrdType, noTradePriceConditions, execMethod, tradePublishIndicator, noTrdRegPublications, regulatoryReportType, investorCountryOfResidence, rptTime, previouslyReported, tradeReportTransType, execType, lastMkt, some_bind] <;> rfl

inductive Message where
  | reject (header : Header) (r0 : Reject)
  | heartbeat (header : Header) (r0 : Heartbeat)
  | logon (header : Header) (r0 : Logon)
  | testRequest (header : Header) (r0 : TestRequest)
  | resendRequest (header : Header) (r0 : ResendRequest)
  | sequenceReset (header : Header) (r0 : SequenceReset)
  | logout (header : Header) (r0 : Logout)
  | tradeCaptureReportAck (header : Header) (r0 : TradeCaptureReportAck)
  | tradeCaptureReport (header : Header) (r0 : TradeCaptureReport)

def Message.tokens : Message → List Token
  | .reject header r0 => ⟨[51, 53], ⟨[51], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .heartbeat header r0 => ⟨[51, 53], ⟨[48], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logon header r0 => ⟨[51, 53], ⟨[65], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .testRequest header r0 => ⟨[51, 53], ⟨[49], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .resendRequest header r0 => ⟨[51, 53], ⟨[50], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .sequenceReset header r0 => ⟨[51, 53], ⟨[52], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logout header r0 => ⟨[51, 53], ⟨[53], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .tradeCaptureReportAck header r0 => ⟨[51, 53], ⟨[65, 82], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .tradeCaptureReport header r0 => ⟨[51, 53], ⟨[65, 69], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)

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
      else if token.value.val = [65, 82] then
        if known (Header.tags ++ TradeCaptureReportAck.tags) rest then do
          let header ← Header.decode rest
          let r0 ← TradeCaptureReportAck.decode rest
          pure (.tradeCaptureReportAck header r0)
        else none
      else if token.value.val = [65, 69] then
        if known (Header.tags ++ TradeCaptureReport.tags) rest then do
          let header ← Header.decode rest
          let r0 ← TradeCaptureReport.decode rest
          pure (.tradeCaptureReport header r0)
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

theorem Message.decode_tradeCaptureReportAck (header : Header) (r0 : TradeCaptureReportAck) :
    Message.decode (Message.tokens (.tradeCaptureReportAck header r0)) = some (.tradeCaptureReportAck header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (TradeCaptureReportAck.tags) rfl rfl (by decide +kernel))
  have c1 := TradeCaptureReportAck.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (TradeCaptureReportAck.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ TradeCaptureReportAck.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tradeCaptureReport (header : Header) (r0 : TradeCaptureReport) :
    Message.decode (Message.tokens (.tradeCaptureReport header r0)) = some (.tradeCaptureReport header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (TradeCaptureReport.tags) rfl rfl (by decide +kernel))
  have c1 := TradeCaptureReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (TradeCaptureReport.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ TradeCaptureReport.tags) rfl
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
  | tradeCaptureReportAck header r0 => exact Message.decode_tradeCaptureReportAck header r0
  | tradeCaptureReport header r0 => exact Message.decode_tradeCaptureReport header r0

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

theorem Message.decodeBytes_tradeCaptureReportAck (header : Header) (r0 : TradeCaptureReportAck) :
    Message.decodeBytes (Message.encode (.tradeCaptureReportAck header r0)) = some (.tradeCaptureReportAck header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[65, 82], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ TradeCaptureReportAck.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_tradeCaptureReportAck header r0

theorem Message.decodeBytes_tradeCaptureReport (header : Header) (r0 : TradeCaptureReport) :
    Message.decodeBytes (Message.encode (.tradeCaptureReport header r0)) = some (.tradeCaptureReport header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[65, 69], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ TradeCaptureReport.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_tradeCaptureReport header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | reject header r0 => exact Message.decodeBytes_reject header r0
  | heartbeat header r0 => exact Message.decodeBytes_heartbeat header r0
  | logon header r0 => exact Message.decodeBytes_logon header r0
  | testRequest header r0 => exact Message.decodeBytes_testRequest header r0
  | resendRequest header r0 => exact Message.decodeBytes_resendRequest header r0
  | sequenceReset header r0 => exact Message.decodeBytes_sequenceReset header r0
  | logout header r0 => exact Message.decodeBytes_logout header r0
  | tradeCaptureReportAck header r0 => exact Message.decodeBytes_tradeCaptureReportAck header r0
  | tradeCaptureReport header r0 => exact Message.decodeBytes_tradeCaptureReport header r0

/-- BeginString as the venue fixes it: FIXT.1.1 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 84, 46, 49, 46, 49, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.NasdaqNordicequitiesApatradereportingFixV1023Exchange
