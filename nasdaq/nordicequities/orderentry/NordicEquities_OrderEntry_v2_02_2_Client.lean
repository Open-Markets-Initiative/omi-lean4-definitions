import Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq)  v2.02.2, Client messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.NasdaqNordicequitiesOrderentryFixV2022Client

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

structure NewOrderSingle where
  clOrdID : Terminated 1  -- tag 11
  currency : Option (Terminated 1)  -- tag 15
  execInst : Option (Terminated 1)  -- tag 18
  handlInst : Terminated 1  -- tag 21
  iDSource : Option (Terminated 1)  -- tag 22
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  securityID : Option (Terminated 1)  -- tag 48
  side : Terminated 1  -- tag 54
  symbol : Terminated 1  -- tag 55
  timeInForce : Option (Terminated 1)  -- tag 59
  transactTime : Terminated 1  -- tag 60
  execBroker : Option (Terminated 1)  -- tag 76
  minQty : Option (Terminated 1)  -- tag 110
  maxFloor : Option (Terminated 1)  -- tag 111
  expireTime : Option (Terminated 1)  -- tag 126
  pegDifference : Option (Terminated 1)  -- tag 211
  clearingFirm : Option (Terminated 1)  -- tag 439
  clearingAccount : Option (Terminated 1)  -- tag 440
  orderCapacity : Option (Terminated 1)  -- tag 528
  orderRestrictions : Option (Terminated 1)  -- tag 529
  clearingAccountType : Option (Terminated 1)  -- tag 1816
  subMktID : Option (Terminated 1)  -- tag 5815
  clRefID : Option (Terminated 1)  -- tag 6209
  displayRange : Option (Terminated 1)  -- tag 6227
  displayInst : Option (Terminated 1)  -- tag 9140
  crossTradeFlag : Option (Terminated 1)  -- tag 9355
  brSeqNbr : Option (Terminated 1)  -- tag 9861
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
  noOrderAttributes : List NoOrderAttributes  -- tag 2593
  noPartyIDs : List NoPartyIDs  -- tag 453
  orderOrigination : Option (Terminated 1)  -- tag 1724
  tradingAtClosingPrice : Option (Terminated 1)  -- tag 20301
  orderCondition : Option (Terminated 1)  -- tag 20109
  custOrderCapacity : Option (Terminated 1)  -- tag 582
  targetStrategy : Option (Terminated 1)  -- tag 847
  minRate : Option (Terminated 1)  -- tag 27005
  maxRate : Option (Terminated 1)  -- tag 27006
  conditionalType : Option (Terminated 1)  -- tag 23012
  firmUpID : Option (Terminated 1)  -- tag 23014

def NewOrderSingle.parts (record : NewOrderSingle) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.optional [49, 53] record.currency,
   Part.optional [49, 56] record.execInst,
   Part.required [50, 49] record.handlInst,
   Part.optional [50, 50] record.iDSource,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.optional [52, 56] record.securityID,
   Part.required [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.optional [53, 57] record.timeInForce,
   Part.required [54, 48] record.transactTime,
   Part.optional [55, 54] record.execBroker,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [49, 49, 49] record.maxFloor,
   Part.optional [49, 50, 54] record.expireTime,
   Part.optional [50, 49, 49] record.pegDifference,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.optional [53, 50, 56] record.orderCapacity,
   Part.optional [53, 50, 57] record.orderRestrictions,
   Part.optional [49, 56, 49, 54] record.clearingAccountType,
   Part.optional [53, 56, 49, 53] record.subMktID,
   Part.optional [54, 50, 48, 57] record.clRefID,
   Part.optional [54, 50, 50, 55] record.displayRange,
   Part.optional [57, 49, 52, 48] record.displayInst,
   Part.optional [57, 51, 53, 53] record.crossTradeFlag,
   Part.optional [57, 56, 54, 49] record.brSeqNbr,
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
   Part.group [50, 53, 57, 51] NoOrderAttributes.members NoOrderAttributes.encode NoOrderAttributes.within record.noOrderAttributes,
   Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.optional [49, 55, 50, 52] record.orderOrigination,
   Part.optional [50, 48, 51, 48, 49] record.tradingAtClosingPrice,
   Part.optional [50, 48, 49, 48, 57] record.orderCondition,
   Part.optional [53, 56, 50] record.custOrderCapacity,
   Part.optional [56, 52, 55] record.targetStrategy,
   Part.optional [50, 55, 48, 48, 53] record.minRate,
   Part.optional [50, 55, 48, 48, 54] record.maxRate,
   Part.optional [50, 51, 48, 49, 50] record.conditionalType,
   Part.optional [50, 51, 48, 49, 52] record.firmUpID]

def NewOrderSingle.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[49, 53]], [[49, 56]], [[50, 49]], [[50, 50]], [[51, 56]], [[52, 48]], [[52, 52]], [[52, 56]], [[53, 52]], [[53, 53]], [[53, 57]], [[54, 48]], [[55, 54]], [[49, 49, 48]], [[49, 49, 49]], [[49, 50, 54]], [[50, 49, 49]], [[52, 51, 57]], [[52, 52, 48]], [[53, 50, 56]], [[53, 50, 57]], [[49, 56, 49, 54]], [[53, 56, 49, 53]], [[54, 50, 48, 57]], [[54, 50, 50, 55]], [[57, 49, 52, 48]], [[57, 51, 53, 53]], [[57, 56, 54, 49]], [[49, 54, 56]], [[50, 48, 48, 48, 49]], [[56, 52, 57]], [[50, 48, 48, 48, 51]], [[50, 48, 48, 48, 50]], [[50, 48, 48, 51, 48]], [[50, 48, 48, 50, 48]], [[50, 48, 48, 50, 49]], [[50, 48, 48, 50, 50]], [[50, 48, 48, 50, 51]], [[50, 48, 48, 50, 52]], [[50, 48, 48, 50, 53]], [[50, 48, 48, 50, 54]], [[50, 48, 48, 50, 55]], [[50, 48, 48, 50, 56]], [[50, 48, 48, 50, 57]], [[50, 48, 48, 51, 49]], [[50, 48, 48, 48, 54]], [[50, 48, 48, 48, 55]], [[50, 48, 48, 48, 53]], [[50, 48, 48, 49, 50]], [[50, 48, 48, 49, 51]], [[50, 48, 48, 48, 52]], [[50, 48, 48, 49, 48]], [[50, 48, 48, 48, 56]], [[50, 48, 48, 49, 49]], [[50, 48, 48, 48, 57]], [[50, 48, 48, 49, 52]], [[50, 48, 48, 49, 53]], [[50, 48, 48, 49, 54]], [[50, 48, 48, 49, 56]], [[50, 48, 49, 48, 49]], [[50, 48, 49, 48, 50]], [[50, 48, 49, 48, 51]], [50, 53, 57, 51] :: NoOrderAttributes.members, [52, 53, 51] :: NoPartyIDs.members, [[49, 55, 50, 52]], [[50, 48, 51, 48, 49]], [[50, 48, 49, 48, 57]], [[53, 56, 50]], [[56, 52, 55]], [[50, 55, 48, 48, 53]], [[50, 55, 48, 48, 54]], [[50, 51, 48, 49, 50]], [[50, 51, 48, 49, 52]]]

theorem NewOrderSingle.shape (record : NewOrderSingle) : record.parts.map Part.tags = NewOrderSingle.tags := rfl

def NewOrderSingle.decode (tokens : List Token) : Option NewOrderSingle := do
  let clOrdID ← readRequired [49, 49] tokens
  let currency ← readOptional [49, 53] tokens
  let execInst ← readOptional [49, 56] tokens
  let handlInst ← readRequired [50, 49] tokens
  let iDSource ← readOptional [50, 50] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let securityID ← readOptional [52, 56] tokens
  let side ← readRequired [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let transactTime ← readRequired [54, 48] tokens
  let execBroker ← readOptional [55, 54] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let maxFloor ← readOptional [49, 49, 49] tokens
  let expireTime ← readOptional [49, 50, 54] tokens
  let pegDifference ← readOptional [50, 49, 49] tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let orderCapacity ← readOptional [53, 50, 56] tokens
  let orderRestrictions ← readOptional [53, 50, 57] tokens
  let clearingAccountType ← readOptional [49, 56, 49, 54] tokens
  let subMktID ← readOptional [53, 56, 49, 53] tokens
  let clRefID ← readOptional [54, 50, 48, 57] tokens
  let displayRange ← readOptional [54, 50, 50, 55] tokens
  let displayInst ← readOptional [57, 49, 52, 48] tokens
  let crossTradeFlag ← readOptional [57, 51, 53, 53] tokens
  let brSeqNbr ← readOptional [57, 56, 54, 49] tokens
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
  let noOrderAttributes ← readGroup [50, 53, 57, 51] [50, 53, 57, 52] NoOrderAttributes.members NoOrderAttributes.decode tokens
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let orderOrigination ← readOptional [49, 55, 50, 52] tokens
  let tradingAtClosingPrice ← readOptional [50, 48, 51, 48, 49] tokens
  let orderCondition ← readOptional [50, 48, 49, 48, 57] tokens
  let custOrderCapacity ← readOptional [53, 56, 50] tokens
  let targetStrategy ← readOptional [56, 52, 55] tokens
  let minRate ← readOptional [50, 55, 48, 48, 53] tokens
  let maxRate ← readOptional [50, 55, 48, 48, 54] tokens
  let conditionalType ← readOptional [50, 51, 48, 49, 50] tokens
  let firmUpID ← readOptional [50, 51, 48, 49, 52] tokens
  pure { clOrdID, currency, execInst, handlInst, iDSource, orderQty, ordType, price, securityID, side, symbol, timeInForce, transactTime, execBroker, minQty, maxFloor, expireTime, pegDifference, clearingFirm, clearingAccount, orderCapacity, orderRestrictions, clearingAccountType, subMktID, clRefID, displayRange, displayInst, crossTradeFlag, brSeqNbr, effectiveTime, targetVolume, maximumVolume, minimumVolume, aggression, minChildOrderValue, spreadLimit, refPriceBidLeg, refPriceAskLeg, lagBidLeg, lagAskLeg, leadBidLeg, leadAskLeg, stopLossBidLeg, stopLossAskLeg, basketID, ratio, iWouldPrice, iWouldType, iWouldQty, cleanUpType, cleanUpQty, blockFilter, onOpenType, onOpenQty, onCloseType, onCloseQty, dynamicBenchmark, dynamicPrice, inMoneyStyle, outMoneyStyle, sTPLevel, sTPAction, sTPTraderGroup, noOrderAttributes, noPartyIDs, orderOrigination, tradingAtClosingPrice, orderCondition, custOrderCapacity, targetStrategy, minRate, maxRate, conditionalType, firmUpID }

theorem NewOrderSingle.decode_agrees (record : NewOrderSingle) (tokens : List Token)
    (agrees : ∀ tags ∈ NewOrderSingle.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NewOrderSingle.decode tokens = some record := by
  have distinct : NewOrderSingle.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have currency := readOptional_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have handlInst := readRequired_part [50, 49] record.handlInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have iDSource := readOptional_part [50, 50] record.iDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have execBroker := readOptional_part [55, 54] record.execBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have maxFloor := readOptional_part [49, 49, 49] record.maxFloor tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have expireTime := readOptional_part [49, 50, 54] record.expireTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have pegDifference := readOptional_part [50, 49, 49] record.pegDifference tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have orderCapacity := readOptional_part [53, 50, 56] record.orderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have orderRestrictions := readOptional_part [53, 50, 57] record.orderRestrictions tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have clearingAccountType := readOptional_part [49, 56, 49, 54] record.clearingAccountType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have subMktID := readOptional_part [53, 56, 49, 53] record.subMktID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have clRefID := readOptional_part [54, 50, 48, 57] record.clRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have displayRange := readOptional_part [54, 50, 50, 55] record.displayRange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have displayInst := readOptional_part [57, 49, 52, 48] record.displayInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have crossTradeFlag := readOptional_part [57, 51, 53, 53] record.crossTradeFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have brSeqNbr := readOptional_part [57, 56, 54, 49] record.brSeqNbr tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have effectiveTime := readOptional_part [49, 54, 56] record.effectiveTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have targetVolume := readOptional_part [50, 48, 48, 48, 49] record.targetVolume tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have maximumVolume := readOptional_part [56, 52, 57] record.maximumVolume tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have minimumVolume := readOptional_part [50, 48, 48, 48, 51] record.minimumVolume tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have aggression := readOptional_part [50, 48, 48, 48, 50] record.aggression tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have minChildOrderValue := readOptional_part [50, 48, 48, 51, 48] record.minChildOrderValue tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have spreadLimit := readOptional_part [50, 48, 48, 50, 48] record.spreadLimit tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have refPriceBidLeg := readOptional_part [50, 48, 48, 50, 49] record.refPriceBidLeg tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have refPriceAskLeg := readOptional_part [50, 48, 48, 50, 50] record.refPriceAskLeg tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have lagBidLeg := readOptional_part [50, 48, 48, 50, 51] record.lagBidLeg tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  have lagAskLeg := readOptional_part [50, 48, 48, 50, 52] record.lagAskLeg tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 39 (by decide +kernel)))
  have leadBidLeg := readOptional_part [50, 48, 48, 50, 53] record.leadBidLeg tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 40 (by decide +kernel)))
  have leadAskLeg := readOptional_part [50, 48, 48, 50, 54] record.leadAskLeg tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 41 (by decide +kernel)))
  have stopLossBidLeg := readOptional_part [50, 48, 48, 50, 55] record.stopLossBidLeg tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 42 (by decide +kernel)))
  have stopLossAskLeg := readOptional_part [50, 48, 48, 50, 56] record.stopLossAskLeg tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 43 (by decide +kernel)))
  have basketID := readOptional_part [50, 48, 48, 50, 57] record.basketID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 44 (by decide +kernel)))
  have ratio := readOptional_part [50, 48, 48, 51, 49] record.ratio tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 45 (by decide +kernel)))
  have iWouldPrice := readOptional_part [50, 48, 48, 48, 54] record.iWouldPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 46 (by decide +kernel)))
  have iWouldType := readOptional_part [50, 48, 48, 48, 55] record.iWouldType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 47 (by decide +kernel)))
  have iWouldQty := readOptional_part [50, 48, 48, 48, 53] record.iWouldQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 48 (by decide +kernel)))
  have cleanUpType := readOptional_part [50, 48, 48, 49, 50] record.cleanUpType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 49 (by decide +kernel)))
  have cleanUpQty := readOptional_part [50, 48, 48, 49, 51] record.cleanUpQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 50 (by decide +kernel)))
  have blockFilter := readOptional_part [50, 48, 48, 48, 52] record.blockFilter tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 51 (by decide +kernel)))
  have onOpenType := readOptional_part [50, 48, 48, 49, 48] record.onOpenType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 52 (by decide +kernel)))
  have onOpenQty := readOptional_part [50, 48, 48, 48, 56] record.onOpenQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 53 (by decide +kernel)))
  have onCloseType := readOptional_part [50, 48, 48, 49, 49] record.onCloseType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 54 (by decide +kernel)))
  have onCloseQty := readOptional_part [50, 48, 48, 48, 57] record.onCloseQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 55 (by decide +kernel)))
  have dynamicBenchmark := readOptional_part [50, 48, 48, 49, 52] record.dynamicBenchmark tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 56 (by decide +kernel)))
  have dynamicPrice := readOptional_part [50, 48, 48, 49, 53] record.dynamicPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 57 (by decide +kernel)))
  have inMoneyStyle := readOptional_part [50, 48, 48, 49, 54] record.inMoneyStyle tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 58 (by decide +kernel)))
  have outMoneyStyle := readOptional_part [50, 48, 48, 49, 56] record.outMoneyStyle tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 59 (by decide +kernel)))
  have sTPLevel := readOptional_part [50, 48, 49, 48, 49] record.sTPLevel tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 60 (by decide +kernel)))
  have sTPAction := readOptional_part [50, 48, 49, 48, 50] record.sTPAction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 61 (by decide +kernel)))
  have sTPTraderGroup := readOptional_part [50, 48, 49, 48, 51] record.sTPTraderGroup tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 62 (by decide +kernel)))
  have noOrderAttributes := readGroup_part [50, 53, 57, 51] [50, 53, 57, 52] NoOrderAttributes.members NoOrderAttributes.encode NoOrderAttributes.within NoOrderAttributes.decode NoOrderAttributes.decode_encode NoOrderAttributes.led record.noOrderAttributes tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 63 (by decide +kernel)))
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 64 (by decide +kernel)))
  have orderOrigination := readOptional_part [49, 55, 50, 52] record.orderOrigination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 65 (by decide +kernel)))
  have tradingAtClosingPrice := readOptional_part [50, 48, 51, 48, 49] record.tradingAtClosingPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 66 (by decide +kernel)))
  have orderCondition := readOptional_part [50, 48, 49, 48, 57] record.orderCondition tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 67 (by decide +kernel)))
  have custOrderCapacity := readOptional_part [53, 56, 50] record.custOrderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 68 (by decide +kernel)))
  have targetStrategy := readOptional_part [56, 52, 55] record.targetStrategy tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 69 (by decide +kernel)))
  have minRate := readOptional_part [50, 55, 48, 48, 53] record.minRate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 70 (by decide +kernel)))
  have maxRate := readOptional_part [50, 55, 48, 48, 54] record.maxRate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 71 (by decide +kernel)))
  have conditionalType := readOptional_part [50, 51, 48, 49, 50] record.conditionalType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 72 (by decide +kernel)))
  have firmUpID := readOptional_part [50, 51, 48, 49, 52] record.firmUpID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 73 (by decide +kernel)))
  simp only [NewOrderSingle.decode, clOrdID, currency, execInst, handlInst, iDSource, orderQty, ordType, price, securityID, side, symbol, timeInForce, transactTime, execBroker, minQty, maxFloor, expireTime, pegDifference, clearingFirm, clearingAccount, orderCapacity, orderRestrictions, clearingAccountType, subMktID, clRefID, displayRange, displayInst, crossTradeFlag, brSeqNbr, effectiveTime, targetVolume, maximumVolume, minimumVolume, aggression, minChildOrderValue, spreadLimit, refPriceBidLeg, refPriceAskLeg, lagBidLeg, lagAskLeg, leadBidLeg, leadAskLeg, stopLossBidLeg, stopLossAskLeg, basketID, ratio, iWouldPrice, iWouldType, iWouldQty, cleanUpType, cleanUpQty, blockFilter, onOpenType, onOpenQty, onCloseType, onCloseQty, dynamicBenchmark, dynamicPrice, inMoneyStyle, outMoneyStyle, sTPLevel, sTPAction, sTPTraderGroup, noOrderAttributes, noPartyIDs, orderOrigination, tradingAtClosingPrice, orderCondition, custOrderCapacity, targetStrategy, minRate, maxRate, conditionalType, firmUpID, some_bind] <;> rfl

structure OrderCancelRequest where
  clOrdID : Terminated 1  -- tag 11
  currency : Option (Terminated 1)  -- tag 15
  iDSource : Option (Terminated 1)  -- tag 22
  orderID : Option (Terminated 1)  -- tag 37
  origClOrdID : Terminated 1  -- tag 41
  securityID : Option (Terminated 1)  -- tag 48
  side : Terminated 1  -- tag 54
  symbol : Terminated 1  -- tag 55
  transactTime : Terminated 1  -- tag 60
  subMktID : Option (Terminated 1)  -- tag 5815

def OrderCancelRequest.parts (record : OrderCancelRequest) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.optional [49, 53] record.currency,
   Part.optional [50, 50] record.iDSource,
   Part.optional [51, 55] record.orderID,
   Part.required [52, 49] record.origClOrdID,
   Part.optional [52, 56] record.securityID,
   Part.required [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.required [54, 48] record.transactTime,
   Part.optional [53, 56, 49, 53] record.subMktID]

def OrderCancelRequest.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[49, 53]], [[50, 50]], [[51, 55]], [[52, 49]], [[52, 56]], [[53, 52]], [[53, 53]], [[54, 48]], [[53, 56, 49, 53]]]

theorem OrderCancelRequest.shape (record : OrderCancelRequest) : record.parts.map Part.tags = OrderCancelRequest.tags := rfl

def OrderCancelRequest.decode (tokens : List Token) : Option OrderCancelRequest := do
  let clOrdID ← readRequired [49, 49] tokens
  let currency ← readOptional [49, 53] tokens
  let iDSource ← readOptional [50, 50] tokens
  let orderID ← readOptional [51, 55] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let securityID ← readOptional [52, 56] tokens
  let side ← readRequired [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let transactTime ← readRequired [54, 48] tokens
  let subMktID ← readOptional [53, 56, 49, 53] tokens
  pure { clOrdID, currency, iDSource, orderID, origClOrdID, securityID, side, symbol, transactTime, subMktID }

theorem OrderCancelRequest.decode_agrees (record : OrderCancelRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelRequest.decode tokens = some record := by
  have distinct : OrderCancelRequest.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have currency := readOptional_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have iDSource := readOptional_part [50, 50] record.iDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have subMktID := readOptional_part [53, 56, 49, 53] record.subMktID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  simp only [OrderCancelRequest.decode, clOrdID, currency, iDSource, orderID, origClOrdID, securityID, side, symbol, transactTime, subMktID, some_bind] <;> rfl

structure OrderCancelReplaceRequest where
  clOrdID : Terminated 1  -- tag 11
  currency : Option (Terminated 1)  -- tag 15
  handlInst : Terminated 1  -- tag 21
  iDSource : Option (Terminated 1)  -- tag 22
  orderID : Option (Terminated 1)  -- tag 37
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  origClOrdID : Terminated 1  -- tag 41
  price : Option (Terminated 1)  -- tag 44
  securityID : Option (Terminated 1)  -- tag 48
  side : Terminated 1  -- tag 54
  symbol : Terminated 1  -- tag 55
  timeInForce : Option (Terminated 1)  -- tag 59
  transactTime : Terminated 1  -- tag 60
  minQty : Option (Terminated 1)  -- tag 110
  expireTime : Option (Terminated 1)  -- tag 126
  clearingFirm : Option (Terminated 1)  -- tag 439
  clearingAccount : Option (Terminated 1)  -- tag 440
  clearingAccountType : Option (Terminated 1)  -- tag 1816
  subMktID : Option (Terminated 1)  -- tag 5815
  crossTradeFlag : Option (Terminated 1)  -- tag 9355
  brSeqNbr : Option (Terminated 1)  -- tag 9861
  clRefID : Option (Terminated 1)  -- tag 6209
  displayRange : Option (Terminated 1)  -- tag 6227
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
  targetStrategy : Option (Terminated 1)  -- tag 847
  minRate : Option (Terminated 1)  -- tag 27005
  maxRate : Option (Terminated 1)  -- tag 27006

def OrderCancelReplaceRequest.parts (record : OrderCancelReplaceRequest) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.optional [49, 53] record.currency,
   Part.required [50, 49] record.handlInst,
   Part.optional [50, 50] record.iDSource,
   Part.optional [51, 55] record.orderID,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.required [52, 49] record.origClOrdID,
   Part.optional [52, 52] record.price,
   Part.optional [52, 56] record.securityID,
   Part.required [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.optional [53, 57] record.timeInForce,
   Part.required [54, 48] record.transactTime,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [49, 50, 54] record.expireTime,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.optional [49, 56, 49, 54] record.clearingAccountType,
   Part.optional [53, 56, 49, 53] record.subMktID,
   Part.optional [57, 51, 53, 53] record.crossTradeFlag,
   Part.optional [57, 56, 54, 49] record.brSeqNbr,
   Part.optional [54, 50, 48, 57] record.clRefID,
   Part.optional [54, 50, 50, 55] record.displayRange,
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
   Part.optional [56, 52, 55] record.targetStrategy,
   Part.optional [50, 55, 48, 48, 53] record.minRate,
   Part.optional [50, 55, 48, 48, 54] record.maxRate]

def OrderCancelReplaceRequest.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[49, 53]], [[50, 49]], [[50, 50]], [[51, 55]], [[51, 56]], [[52, 48]], [[52, 49]], [[52, 52]], [[52, 56]], [[53, 52]], [[53, 53]], [[53, 57]], [[54, 48]], [[49, 49, 48]], [[49, 50, 54]], [[52, 51, 57]], [[52, 52, 48]], [[49, 56, 49, 54]], [[53, 56, 49, 53]], [[57, 51, 53, 53]], [[57, 56, 54, 49]], [[54, 50, 48, 57]], [[54, 50, 50, 55]], [[49, 54, 56]], [[50, 48, 48, 48, 49]], [[56, 52, 57]], [[50, 48, 48, 48, 51]], [[50, 48, 48, 48, 50]], [[50, 48, 48, 51, 48]], [[50, 48, 48, 50, 48]], [[50, 48, 48, 50, 49]], [[50, 48, 48, 50, 50]], [[50, 48, 48, 50, 51]], [[50, 48, 48, 50, 52]], [[50, 48, 48, 50, 53]], [[50, 48, 48, 50, 54]], [[50, 48, 48, 50, 55]], [[50, 48, 48, 50, 56]], [[50, 48, 48, 50, 57]], [[50, 48, 48, 51, 49]], [[50, 48, 48, 48, 54]], [[50, 48, 48, 48, 55]], [[50, 48, 48, 48, 53]], [[50, 48, 48, 49, 50]], [[50, 48, 48, 49, 51]], [[50, 48, 48, 48, 52]], [[50, 48, 48, 49, 48]], [[50, 48, 48, 48, 56]], [[50, 48, 48, 49, 49]], [[50, 48, 48, 48, 57]], [[50, 48, 48, 49, 52]], [[50, 48, 48, 49, 53]], [[50, 48, 48, 49, 54]], [[50, 48, 48, 49, 56]], [[56, 52, 55]], [[50, 55, 48, 48, 53]], [[50, 55, 48, 48, 54]]]

theorem OrderCancelReplaceRequest.shape (record : OrderCancelReplaceRequest) : record.parts.map Part.tags = OrderCancelReplaceRequest.tags := rfl

def OrderCancelReplaceRequest.decode (tokens : List Token) : Option OrderCancelReplaceRequest := do
  let clOrdID ← readRequired [49, 49] tokens
  let currency ← readOptional [49, 53] tokens
  let handlInst ← readRequired [50, 49] tokens
  let iDSource ← readOptional [50, 50] tokens
  let orderID ← readOptional [51, 55] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let price ← readOptional [52, 52] tokens
  let securityID ← readOptional [52, 56] tokens
  let side ← readRequired [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let transactTime ← readRequired [54, 48] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let expireTime ← readOptional [49, 50, 54] tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let clearingAccountType ← readOptional [49, 56, 49, 54] tokens
  let subMktID ← readOptional [53, 56, 49, 53] tokens
  let crossTradeFlag ← readOptional [57, 51, 53, 53] tokens
  let brSeqNbr ← readOptional [57, 56, 54, 49] tokens
  let clRefID ← readOptional [54, 50, 48, 57] tokens
  let displayRange ← readOptional [54, 50, 50, 55] tokens
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
  let targetStrategy ← readOptional [56, 52, 55] tokens
  let minRate ← readOptional [50, 55, 48, 48, 53] tokens
  let maxRate ← readOptional [50, 55, 48, 48, 54] tokens
  pure { clOrdID, currency, handlInst, iDSource, orderID, orderQty, ordType, origClOrdID, price, securityID, side, symbol, timeInForce, transactTime, minQty, expireTime, clearingFirm, clearingAccount, clearingAccountType, subMktID, crossTradeFlag, brSeqNbr, clRefID, displayRange, effectiveTime, targetVolume, maximumVolume, minimumVolume, aggression, minChildOrderValue, spreadLimit, refPriceBidLeg, refPriceAskLeg, lagBidLeg, lagAskLeg, leadBidLeg, leadAskLeg, stopLossBidLeg, stopLossAskLeg, basketID, ratio, iWouldPrice, iWouldType, iWouldQty, cleanUpType, cleanUpQty, blockFilter, onOpenType, onOpenQty, onCloseType, onCloseQty, dynamicBenchmark, dynamicPrice, inMoneyStyle, outMoneyStyle, targetStrategy, minRate, maxRate }

theorem OrderCancelReplaceRequest.decode_agrees (record : OrderCancelReplaceRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelReplaceRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelReplaceRequest.decode tokens = some record := by
  have distinct : OrderCancelReplaceRequest.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have currency := readOptional_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have handlInst := readRequired_part [50, 49] record.handlInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have iDSource := readOptional_part [50, 50] record.iDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have expireTime := readOptional_part [49, 50, 54] record.expireTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have clearingAccountType := readOptional_part [49, 56, 49, 54] record.clearingAccountType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have subMktID := readOptional_part [53, 56, 49, 53] record.subMktID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have crossTradeFlag := readOptional_part [57, 51, 53, 53] record.crossTradeFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have brSeqNbr := readOptional_part [57, 56, 54, 49] record.brSeqNbr tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have clRefID := readOptional_part [54, 50, 48, 57] record.clRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have displayRange := readOptional_part [54, 50, 50, 55] record.displayRange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have effectiveTime := readOptional_part [49, 54, 56] record.effectiveTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have targetVolume := readOptional_part [50, 48, 48, 48, 49] record.targetVolume tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have maximumVolume := readOptional_part [56, 52, 57] record.maximumVolume tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have minimumVolume := readOptional_part [50, 48, 48, 48, 51] record.minimumVolume tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have aggression := readOptional_part [50, 48, 48, 48, 50] record.aggression tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have minChildOrderValue := readOptional_part [50, 48, 48, 51, 48] record.minChildOrderValue tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have spreadLimit := readOptional_part [50, 48, 48, 50, 48] record.spreadLimit tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have refPriceBidLeg := readOptional_part [50, 48, 48, 50, 49] record.refPriceBidLeg tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have refPriceAskLeg := readOptional_part [50, 48, 48, 50, 50] record.refPriceAskLeg tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have lagBidLeg := readOptional_part [50, 48, 48, 50, 51] record.lagBidLeg tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have lagAskLeg := readOptional_part [50, 48, 48, 50, 52] record.lagAskLeg tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have leadBidLeg := readOptional_part [50, 48, 48, 50, 53] record.leadBidLeg tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have leadAskLeg := readOptional_part [50, 48, 48, 50, 54] record.leadAskLeg tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have stopLossBidLeg := readOptional_part [50, 48, 48, 50, 55] record.stopLossBidLeg tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have stopLossAskLeg := readOptional_part [50, 48, 48, 50, 56] record.stopLossAskLeg tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  have basketID := readOptional_part [50, 48, 48, 50, 57] record.basketID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 39 (by decide +kernel)))
  have ratio := readOptional_part [50, 48, 48, 51, 49] record.ratio tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 40 (by decide +kernel)))
  have iWouldPrice := readOptional_part [50, 48, 48, 48, 54] record.iWouldPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 41 (by decide +kernel)))
  have iWouldType := readOptional_part [50, 48, 48, 48, 55] record.iWouldType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 42 (by decide +kernel)))
  have iWouldQty := readOptional_part [50, 48, 48, 48, 53] record.iWouldQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 43 (by decide +kernel)))
  have cleanUpType := readOptional_part [50, 48, 48, 49, 50] record.cleanUpType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 44 (by decide +kernel)))
  have cleanUpQty := readOptional_part [50, 48, 48, 49, 51] record.cleanUpQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 45 (by decide +kernel)))
  have blockFilter := readOptional_part [50, 48, 48, 48, 52] record.blockFilter tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 46 (by decide +kernel)))
  have onOpenType := readOptional_part [50, 48, 48, 49, 48] record.onOpenType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 47 (by decide +kernel)))
  have onOpenQty := readOptional_part [50, 48, 48, 48, 56] record.onOpenQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 48 (by decide +kernel)))
  have onCloseType := readOptional_part [50, 48, 48, 49, 49] record.onCloseType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 49 (by decide +kernel)))
  have onCloseQty := readOptional_part [50, 48, 48, 48, 57] record.onCloseQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 50 (by decide +kernel)))
  have dynamicBenchmark := readOptional_part [50, 48, 48, 49, 52] record.dynamicBenchmark tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 51 (by decide +kernel)))
  have dynamicPrice := readOptional_part [50, 48, 48, 49, 53] record.dynamicPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 52 (by decide +kernel)))
  have inMoneyStyle := readOptional_part [50, 48, 48, 49, 54] record.inMoneyStyle tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 53 (by decide +kernel)))
  have outMoneyStyle := readOptional_part [50, 48, 48, 49, 56] record.outMoneyStyle tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 54 (by decide +kernel)))
  have targetStrategy := readOptional_part [56, 52, 55] record.targetStrategy tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 55 (by decide +kernel)))
  have minRate := readOptional_part [50, 55, 48, 48, 53] record.minRate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 56 (by decide +kernel)))
  have maxRate := readOptional_part [50, 55, 48, 48, 54] record.maxRate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 57 (by decide +kernel)))
  simp only [OrderCancelReplaceRequest.decode, clOrdID, currency, handlInst, iDSource, orderID, orderQty, ordType, origClOrdID, price, securityID, side, symbol, timeInForce, transactTime, minQty, expireTime, clearingFirm, clearingAccount, clearingAccountType, subMktID, crossTradeFlag, brSeqNbr, clRefID, displayRange, effectiveTime, targetVolume, maximumVolume, minimumVolume, aggression, minChildOrderValue, spreadLimit, refPriceBidLeg, refPriceAskLeg, lagBidLeg, lagAskLeg, leadBidLeg, leadAskLeg, stopLossBidLeg, stopLossAskLeg, basketID, ratio, iWouldPrice, iWouldType, iWouldQty, cleanUpType, cleanUpQty, blockFilter, onOpenType, onOpenQty, onCloseType, onCloseQty, dynamicBenchmark, dynamicPrice, inMoneyStyle, outMoneyStyle, targetStrategy, minRate, maxRate, some_bind] <;> rfl

inductive Message where
  | reject (header : Header) (r0 : Reject)
  | heartbeat (header : Header) (r0 : Heartbeat)
  | logon (header : Header) (r0 : Logon)
  | testRequest (header : Header) (r0 : TestRequest)
  | resendRequest (header : Header) (r0 : ResendRequest)
  | sequenceReset (header : Header) (r0 : SequenceReset)
  | logout (header : Header) (r0 : Logout)
  | newOrderSingle (header : Header) (r0 : NewOrderSingle)
  | orderCancelRequest (header : Header) (r0 : OrderCancelRequest)
  | orderCancelReplaceRequest (header : Header) (r0 : OrderCancelReplaceRequest)

def Message.tokens : Message → List Token
  | .reject header r0 => ⟨[51, 53], ⟨[51], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .heartbeat header r0 => ⟨[51, 53], ⟨[48], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logon header r0 => ⟨[51, 53], ⟨[65], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .testRequest header r0 => ⟨[51, 53], ⟨[49], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .resendRequest header r0 => ⟨[51, 53], ⟨[50], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .sequenceReset header r0 => ⟨[51, 53], ⟨[52], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logout header r0 => ⟨[51, 53], ⟨[53], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .newOrderSingle header r0 => ⟨[51, 53], ⟨[68], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelRequest header r0 => ⟨[51, 53], ⟨[70], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelReplaceRequest header r0 => ⟨[51, 53], ⟨[71], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)

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
      else if token.value.val = [68] then
        if known (Header.tags ++ NewOrderSingle.tags) rest then do
          let header ← Header.decode rest
          let r0 ← NewOrderSingle.decode rest
          pure (.newOrderSingle header r0)
        else none
      else if token.value.val = [70] then
        if known (Header.tags ++ OrderCancelRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderCancelRequest.decode rest
          pure (.orderCancelRequest header r0)
        else none
      else if token.value.val = [71] then
        if known (Header.tags ++ OrderCancelReplaceRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderCancelReplaceRequest.decode rest
          pure (.orderCancelReplaceRequest header r0)
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

theorem Message.decode_newOrderSingle (header : Header) (r0 : NewOrderSingle) :
    Message.decode (Message.tokens (.newOrderSingle header r0)) = some (.newOrderSingle header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (NewOrderSingle.tags) rfl rfl (by decide +kernel))
  have c1 := NewOrderSingle.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (NewOrderSingle.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ NewOrderSingle.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_orderCancelRequest (header : Header) (r0 : OrderCancelRequest) :
    Message.decode (Message.tokens (.orderCancelRequest header r0)) = some (.orderCancelRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelRequest.tags) rfl rfl (by decide +kernel))
  have c1 := OrderCancelRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderCancelRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_orderCancelReplaceRequest (header : Header) (r0 : OrderCancelReplaceRequest) :
    Message.decode (Message.tokens (.orderCancelReplaceRequest header r0)) = some (.orderCancelReplaceRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelReplaceRequest.tags) rfl rfl (by decide +kernel))
  have c1 := OrderCancelReplaceRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelReplaceRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderCancelReplaceRequest.tags) rfl
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
  | newOrderSingle header r0 => exact Message.decode_newOrderSingle header r0
  | orderCancelRequest header r0 => exact Message.decode_orderCancelRequest header r0
  | orderCancelReplaceRequest header r0 => exact Message.decode_orderCancelReplaceRequest header r0

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

theorem Message.decodeBytes_newOrderSingle (header : Header) (r0 : NewOrderSingle) :
    Message.decodeBytes (Message.encode (.newOrderSingle header r0)) = some (.newOrderSingle header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[68], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ NewOrderSingle.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_newOrderSingle header r0

theorem Message.decodeBytes_orderCancelRequest (header : Header) (r0 : OrderCancelRequest) :
    Message.decodeBytes (Message.encode (.orderCancelRequest header r0)) = some (.orderCancelRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[70], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ OrderCancelRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderCancelRequest header r0

theorem Message.decodeBytes_orderCancelReplaceRequest (header : Header) (r0 : OrderCancelReplaceRequest) :
    Message.decodeBytes (Message.encode (.orderCancelReplaceRequest header r0)) = some (.orderCancelReplaceRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[71], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ OrderCancelReplaceRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderCancelReplaceRequest header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | reject header r0 => exact Message.decodeBytes_reject header r0
  | heartbeat header r0 => exact Message.decodeBytes_heartbeat header r0
  | logon header r0 => exact Message.decodeBytes_logon header r0
  | testRequest header r0 => exact Message.decodeBytes_testRequest header r0
  | resendRequest header r0 => exact Message.decodeBytes_resendRequest header r0
  | sequenceReset header r0 => exact Message.decodeBytes_sequenceReset header r0
  | logout header r0 => exact Message.decodeBytes_logout header r0
  | newOrderSingle header r0 => exact Message.decodeBytes_newOrderSingle header r0
  | orderCancelRequest header r0 => exact Message.decodeBytes_orderCancelRequest header r0
  | orderCancelReplaceRequest header r0 => exact Message.decodeBytes_orderCancelReplaceRequest header r0

/-- BeginString as the venue fixes it: FIXT.1.1 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 84, 46, 49, 46, 49, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.NasdaqNordicequitiesOrderentryFixV2022Client
