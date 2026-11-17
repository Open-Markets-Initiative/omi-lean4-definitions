import Wire

/-!
# Taiwan Futures Exchange Order Entry v3.1.2, Exchange messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.TaifexTaifexderivativesOrderentryFix42V312Exchange

/-- Each Length tag counting a data field, and the field it counts -/
def pairing : Pairing :=
  [([57, 53], [57, 54])]

structure Header where
  senderCompID : Terminated 1  -- tag 49
  senderSubID : Terminated 1  -- tag 50
  targetCompID : Terminated 1  -- tag 56
  targetSubID : Terminated 1  -- tag 57
  msgSeqNum : Terminated 1  -- tag 34
  possDupFlag : Option (Terminated 1)  -- tag 43
  possResend : Option (Terminated 1)  -- tag 97
  sendingTime : Terminated 1  -- tag 52
  origSendingTime : Option (Terminated 1)  -- tag 122

def Header.parts (record : Header) : List Part :=
  [Part.required [52, 57] record.senderCompID,
   Part.required [53, 48] record.senderSubID,
   Part.required [53, 54] record.targetCompID,
   Part.required [53, 55] record.targetSubID,
   Part.required [51, 52] record.msgSeqNum,
   Part.optional [52, 51] record.possDupFlag,
   Part.optional [57, 55] record.possResend,
   Part.required [53, 50] record.sendingTime,
   Part.optional [49, 50, 50] record.origSendingTime]

def Header.tags : List (List (List UInt8)) :=
  [[[52, 57]], [[53, 48]], [[53, 54]], [[53, 55]], [[51, 52]], [[52, 51]], [[57, 55]], [[53, 50]], [[49, 50, 50]]]

theorem Header.shape (record : Header) : record.parts.map Part.tags = Header.tags := rfl

def Header.decode (tokens : List Token) : Option Header := do
  let senderCompID ← readRequired [52, 57] tokens
  let senderSubID ← readRequired [53, 48] tokens
  let targetCompID ← readRequired [53, 54] tokens
  let targetSubID ← readRequired [53, 55] tokens
  let msgSeqNum ← readRequired [51, 52] tokens
  let possDupFlag ← readOptional [52, 51] tokens
  let possResend ← readOptional [57, 55] tokens
  let sendingTime ← readRequired [53, 50] tokens
  let origSendingTime ← readOptional [49, 50, 50] tokens
  pure { senderCompID, senderSubID, targetCompID, targetSubID, msgSeqNum, possDupFlag, possResend, sendingTime, origSendingTime }

theorem Header.decode_agrees (record : Header) (tokens : List Token)
    (agrees : ∀ tags ∈ Header.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Header.decode tokens = some record := by
  have distinct : Header.tags.flatten.Nodup := by decide +kernel
  have senderCompID := readRequired_part [52, 57] record.senderCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have senderSubID := readRequired_part [53, 48] record.senderSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have targetCompID := readRequired_part [53, 54] record.targetCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have targetSubID := readRequired_part [53, 55] record.targetSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have msgSeqNum := readRequired_part [51, 52] record.msgSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have possDupFlag := readOptional_part [52, 51] record.possDupFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have possResend := readOptional_part [57, 55] record.possResend tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have sendingTime := readRequired_part [53, 50] record.sendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have origSendingTime := readOptional_part [49, 50, 50] record.origSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  simp only [Header.decode, senderCompID, senderSubID, targetCompID, targetSubID, msgSeqNum, possDupFlag, possResend, sendingTime, origSendingTime, some_bind] <;> rfl

theorem Header.taken (record : Header) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [52, 57] record.senderCompID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [53, 48] record.senderSubID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [53, 54] record.targetCompID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [53, 55] record.targetSubID (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [51, 52] record.msgSeqNum (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [52, 51] record.possDupFlag (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [57, 55] record.possResend (by decide) (by decide))
         (paired_cons pairing _ _ (paired_required pairing [53, 50] record.sendingTime (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [49, 50, 50] record.origSendingTime (by decide) (by decide))
           (paired_none pairing)))))))))

structure Logon where
  encryptMethod : Terminated 1  -- tag 98
  heartBtInt : Terminated 1  -- tag 108
  resetSeqNumFlag : Option (Terminated 1)  -- tag 141
  taifexUsername : Option (Terminated 1)  -- tag 44553
  taifexPassword : Option (Terminated 1)  -- tag 44554
  rawData : Option (List UInt8)  -- tag 96
  maxMessageSize : Option (Terminated 1)  -- tag 383

def Logon.parts (record : Logon) : List Part :=
  [Part.required [57, 56] record.encryptMethod,
   Part.required [49, 48, 56] record.heartBtInt,
   Part.optional [49, 52, 49] record.resetSeqNumFlag,
   Part.optional [52, 52, 53, 53, 51] record.taifexUsername,
   Part.optional [52, 52, 53, 53, 52] record.taifexPassword,
   Part.dataOptional [57, 53] [57, 54] record.rawData,
   Part.optional [51, 56, 51] record.maxMessageSize]

def Logon.tags : List (List (List UInt8)) :=
  [[[57, 56]], [[49, 48, 56]], [[49, 52, 49]], [[52, 52, 53, 53, 51]], [[52, 52, 53, 53, 52]], [[57, 53], [57, 54]], [[51, 56, 51]]]

theorem Logon.shape (record : Logon) : record.parts.map Part.tags = Logon.tags := rfl

def Logon.decode (tokens : List Token) : Option Logon := do
  let encryptMethod ← readRequired [57, 56] tokens
  let heartBtInt ← readRequired [49, 48, 56] tokens
  let resetSeqNumFlag ← readOptional [49, 52, 49] tokens
  let taifexUsername ← readOptional [52, 52, 53, 53, 51] tokens
  let taifexPassword ← readOptional [52, 52, 53, 53, 52] tokens
  let rawData ← readDataOptional [57, 53] [57, 54] tokens
  let maxMessageSize ← readOptional [51, 56, 51] tokens
  pure { encryptMethod, heartBtInt, resetSeqNumFlag, taifexUsername, taifexPassword, rawData, maxMessageSize }

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
  have taifexUsername := readOptional_part [52, 52, 53, 53, 51] record.taifexUsername tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have taifexPassword := readOptional_part [52, 52, 53, 53, 52] record.taifexPassword tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have rawData := readDataOptional_part [57, 53] [57, 54] record.rawData tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have maxMessageSize := readOptional_part [51, 56, 51] record.maxMessageSize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  simp only [Logon.decode, encryptMethod, heartBtInt, resetSeqNumFlag, taifexUsername, taifexPassword, rawData, maxMessageSize, some_bind] <;> rfl

theorem Logon.taken (record : Logon) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [57, 56] record.encryptMethod (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 48, 56] record.heartBtInt (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [49, 52, 49] record.resetSeqNumFlag (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [52, 52, 53, 53, 51] record.taifexUsername (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [52, 52, 53, 53, 52] record.taifexPassword (by decide) (by decide))
       (paired_cons pairing _ _ (paired_dataOptional pairing [57, 53] [57, 54] record.rawData (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [51, 56, 51] record.maxMessageSize (by decide) (by decide))
         (paired_none pairing)))))))

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

theorem Logout.taken (record : Logout) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
   (paired_none pairing)

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

theorem Heartbeat.taken (record : Heartbeat) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49, 49, 50] record.testReqID (by decide) (by decide))
   (paired_none pairing)

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

theorem TestRequest.taken (record : TestRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 49, 50] record.testReqID (by decide) (by decide))
   (paired_none pairing)

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

theorem ResendRequest.taken (record : ResendRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [55] record.beginSeqNo (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 54] record.endSeqNo (by decide) (by decide))
    (paired_none pairing))

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

theorem Reject.taken (record : Reject) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [52, 53] record.refSeqNum (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [51, 55, 49] record.refTagID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [51, 55, 50] record.refMsgType (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [51, 55, 51] record.sessionRejectReason (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
       (paired_none pairing)))))

structure SequenceResetGapFill where
  newSeqNo : Terminated 1  -- tag 36
  gapFillFlag : Option (Terminated 1)  -- tag 123

def SequenceResetGapFill.parts (record : SequenceResetGapFill) : List Part :=
  [Part.required [51, 54] record.newSeqNo,
   Part.optional [49, 50, 51] record.gapFillFlag]

def SequenceResetGapFill.tags : List (List (List UInt8)) :=
  [[[51, 54]], [[49, 50, 51]]]

theorem SequenceResetGapFill.shape (record : SequenceResetGapFill) : record.parts.map Part.tags = SequenceResetGapFill.tags := rfl

def SequenceResetGapFill.decode (tokens : List Token) : Option SequenceResetGapFill := do
  let newSeqNo ← readRequired [51, 54] tokens
  let gapFillFlag ← readOptional [49, 50, 51] tokens
  pure { newSeqNo, gapFillFlag }

theorem SequenceResetGapFill.decode_agrees (record : SequenceResetGapFill) (tokens : List Token)
    (agrees : ∀ tags ∈ SequenceResetGapFill.tags, select tags tokens = select tags (encodeParts record.parts)) :
    SequenceResetGapFill.decode tokens = some record := by
  have distinct : SequenceResetGapFill.tags.flatten.Nodup := by decide +kernel
  have newSeqNo := readRequired_part [51, 54] record.newSeqNo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have gapFillFlag := readOptional_part [49, 50, 51] record.gapFillFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [SequenceResetGapFill.decode, newSeqNo, gapFillFlag, some_bind] <;> rfl

theorem SequenceResetGapFill.taken (record : SequenceResetGapFill) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 54] record.newSeqNo (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [49, 50, 51] record.gapFillFlag (by decide) (by decide))
    (paired_none pairing))

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

theorem BusinessMessageReject.taken (record : BusinessMessageReject) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [52, 53] record.refSeqNum (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [51, 55, 50] record.refMsgType (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [51, 56, 48] record.businessRejectReason (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
      (paired_none pairing))))

structure TaifexNoPartyIDs where
  taifexPartyID : Terminated 1  -- tag 44448
  taifexPartyIDSource : Terminated 1  -- tag 44447
  taifexPartyRole : Terminated 1  -- tag 44452

def TaifexNoPartyIDs.parts (record : TaifexNoPartyIDs) : List Part :=
  [Part.required [52, 52, 52, 52, 56] record.taifexPartyID,
   Part.required [52, 52, 52, 52, 55] record.taifexPartyIDSource,
   Part.required [52, 52, 52, 53, 50] record.taifexPartyRole]

def TaifexNoPartyIDs.tags : List (List (List UInt8)) :=
  [[[52, 52, 52, 52, 56]], [[52, 52, 52, 52, 55]], [[52, 52, 52, 53, 50]]]

theorem TaifexNoPartyIDs.shape (record : TaifexNoPartyIDs) : record.parts.map Part.tags = TaifexNoPartyIDs.tags := rfl

def TaifexNoPartyIDs.decode (tokens : List Token) : Option TaifexNoPartyIDs := do
  let taifexPartyID ← readRequired [52, 52, 52, 52, 56] tokens
  let taifexPartyIDSource ← readRequired [52, 52, 52, 52, 55] tokens
  let taifexPartyRole ← readRequired [52, 52, 52, 53, 50] tokens
  pure { taifexPartyID, taifexPartyIDSource, taifexPartyRole }

theorem TaifexNoPartyIDs.decode_agrees (record : TaifexNoPartyIDs) (tokens : List Token)
    (agrees : ∀ tags ∈ TaifexNoPartyIDs.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TaifexNoPartyIDs.decode tokens = some record := by
  have distinct : TaifexNoPartyIDs.tags.flatten.Nodup := by decide +kernel
  have taifexPartyID := readRequired_part [52, 52, 52, 52, 56] record.taifexPartyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have taifexPartyIDSource := readRequired_part [52, 52, 52, 52, 55] record.taifexPartyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have taifexPartyRole := readRequired_part [52, 52, 52, 53, 50] record.taifexPartyRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [TaifexNoPartyIDs.decode, taifexPartyID, taifexPartyIDSource, taifexPartyRole, some_bind] <;> rfl

theorem TaifexNoPartyIDs.taken (record : TaifexNoPartyIDs) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [52, 52, 52, 52, 56] record.taifexPartyID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [52, 52, 52, 52, 55] record.taifexPartyIDSource (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [52, 52, 52, 53, 50] record.taifexPartyRole (by decide) (by decide))
     (paired_none pairing)))

def TaifexNoPartyIDs.members : List (List UInt8) := TaifexNoPartyIDs.tags.flatten

def TaifexNoPartyIDs.encode (entry : TaifexNoPartyIDs) : List Token := encodeParts entry.parts

theorem TaifexNoPartyIDs.decode_encode (entry : TaifexNoPartyIDs) : TaifexNoPartyIDs.decode entry.encode = some entry :=
  TaifexNoPartyIDs.decode_agrees entry _ (fun _ _ => rfl)

theorem TaifexNoPartyIDs.within (entry : TaifexNoPartyIDs) : ∀ token ∈ entry.encode, token.tag ∈ TaifexNoPartyIDs.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [TaifexNoPartyIDs.shape] at this

theorem TaifexNoPartyIDs.led (entry : TaifexNoPartyIDs) : Lead [52, 52, 52, 52, 56] entry.encode :=
  lead_parts [52, 52, 52, 52, 56] entry.taifexPartyID _ TaifexNoPartyIDs.tags.tail rfl (by decide +kernel)

structure TaifexNoLegsExecution where
  taifexLegSymbol : Terminated 1  -- tag 44600
  taifexLegCFICode : Terminated 1  -- tag 44608
  taifexLegMaturityMonthYear : Terminated 1  -- tag 44610
  taifexLegSide : Terminated 1  -- tag 44624
  taifexLegLastPx : Terminated 1  -- tag 44637
  taifexLegQty : Terminated 1  -- tag 44687

def TaifexNoLegsExecution.parts (record : TaifexNoLegsExecution) : List Part :=
  [Part.required [52, 52, 54, 48, 48] record.taifexLegSymbol,
   Part.required [52, 52, 54, 48, 56] record.taifexLegCFICode,
   Part.required [52, 52, 54, 49, 48] record.taifexLegMaturityMonthYear,
   Part.required [52, 52, 54, 50, 52] record.taifexLegSide,
   Part.required [52, 52, 54, 51, 55] record.taifexLegLastPx,
   Part.required [52, 52, 54, 56, 55] record.taifexLegQty]

def TaifexNoLegsExecution.tags : List (List (List UInt8)) :=
  [[[52, 52, 54, 48, 48]], [[52, 52, 54, 48, 56]], [[52, 52, 54, 49, 48]], [[52, 52, 54, 50, 52]], [[52, 52, 54, 51, 55]], [[52, 52, 54, 56, 55]]]

theorem TaifexNoLegsExecution.shape (record : TaifexNoLegsExecution) : record.parts.map Part.tags = TaifexNoLegsExecution.tags := rfl

def TaifexNoLegsExecution.decode (tokens : List Token) : Option TaifexNoLegsExecution := do
  let taifexLegSymbol ← readRequired [52, 52, 54, 48, 48] tokens
  let taifexLegCFICode ← readRequired [52, 52, 54, 48, 56] tokens
  let taifexLegMaturityMonthYear ← readRequired [52, 52, 54, 49, 48] tokens
  let taifexLegSide ← readRequired [52, 52, 54, 50, 52] tokens
  let taifexLegLastPx ← readRequired [52, 52, 54, 51, 55] tokens
  let taifexLegQty ← readRequired [52, 52, 54, 56, 55] tokens
  pure { taifexLegSymbol, taifexLegCFICode, taifexLegMaturityMonthYear, taifexLegSide, taifexLegLastPx, taifexLegQty }

theorem TaifexNoLegsExecution.decode_agrees (record : TaifexNoLegsExecution) (tokens : List Token)
    (agrees : ∀ tags ∈ TaifexNoLegsExecution.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TaifexNoLegsExecution.decode tokens = some record := by
  have distinct : TaifexNoLegsExecution.tags.flatten.Nodup := by decide +kernel
  have taifexLegSymbol := readRequired_part [52, 52, 54, 48, 48] record.taifexLegSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have taifexLegCFICode := readRequired_part [52, 52, 54, 48, 56] record.taifexLegCFICode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have taifexLegMaturityMonthYear := readRequired_part [52, 52, 54, 49, 48] record.taifexLegMaturityMonthYear tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have taifexLegSide := readRequired_part [52, 52, 54, 50, 52] record.taifexLegSide tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have taifexLegLastPx := readRequired_part [52, 52, 54, 51, 55] record.taifexLegLastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have taifexLegQty := readRequired_part [52, 52, 54, 56, 55] record.taifexLegQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  simp only [TaifexNoLegsExecution.decode, taifexLegSymbol, taifexLegCFICode, taifexLegMaturityMonthYear, taifexLegSide, taifexLegLastPx, taifexLegQty, some_bind] <;> rfl

theorem TaifexNoLegsExecution.taken (record : TaifexNoLegsExecution) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [52, 52, 54, 48, 48] record.taifexLegSymbol (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [52, 52, 54, 48, 56] record.taifexLegCFICode (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [52, 52, 54, 49, 48] record.taifexLegMaturityMonthYear (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [52, 52, 54, 50, 52] record.taifexLegSide (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [52, 52, 54, 51, 55] record.taifexLegLastPx (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [52, 52, 54, 56, 55] record.taifexLegQty (by decide) (by decide))
        (paired_none pairing))))))

def TaifexNoLegsExecution.members : List (List UInt8) := TaifexNoLegsExecution.tags.flatten

def TaifexNoLegsExecution.encode (entry : TaifexNoLegsExecution) : List Token := encodeParts entry.parts

theorem TaifexNoLegsExecution.decode_encode (entry : TaifexNoLegsExecution) : TaifexNoLegsExecution.decode entry.encode = some entry :=
  TaifexNoLegsExecution.decode_agrees entry _ (fun _ _ => rfl)

theorem TaifexNoLegsExecution.within (entry : TaifexNoLegsExecution) : ∀ token ∈ entry.encode, token.tag ∈ TaifexNoLegsExecution.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [TaifexNoLegsExecution.shape] at this

theorem TaifexNoLegsExecution.led (entry : TaifexNoLegsExecution) : Lead [52, 52, 54, 48, 48] entry.encode :=
  lead_parts [52, 52, 54, 48, 48] entry.taifexLegSymbol _ TaifexNoLegsExecution.tags.tail rfl (by decide +kernel)

structure ExecutionReport where
  orderID : Terminated 1  -- tag 37
  clOrdID : Terminated 1  -- tag 11
  taifexNoPartyIDs : List TaifexNoPartyIDs  -- tag 44453
  execID : Terminated 1  -- tag 17
  execType : Terminated 1  -- tag 150
  origClOrdID : Option (Terminated 1)  -- tag 41
  account : Option (Terminated 1)  -- tag 1
  ordStatus : Terminated 1  -- tag 39
  symbol : Terminated 1  -- tag 55
  side : Terminated 1  -- tag 54
  ordType : Option (Terminated 1)  -- tag 40
  orderQty : Option (Terminated 1)  -- tag 38
  leavesQty : Terminated 1  -- tag 151
  cumQty : Terminated 1  -- tag 14
  avgPx : Terminated 1  -- tag 6
  price : Option (Terminated 1)  -- tag 44
  positionEffect : Option (Terminated 1)  -- tag 77
  text : Option (Terminated 1)  -- tag 58
  lastQty : Option (Terminated 1)  -- tag 32
  lastPx : Option (Terminated 1)  -- tag 31
  transactTime : Option (Terminated 1)  -- tag 60
  timeInForce : Option (Terminated 1)  -- tag 59
  taifexNoLegsExecution : List TaifexNoLegsExecution  -- tag 44555
  execTransType : Terminated 1  -- tag 20
  taifexCFICode : Option (Terminated 1)  -- tag 44461
  taifexSymbolType : Terminated 1  -- tag 10000
  taifexPartID : Option (Terminated 1)  -- tag 10004

def ExecutionReport.parts (record : ExecutionReport) : List Part :=
  [Part.required [51, 55] record.orderID,
   Part.required [49, 49] record.clOrdID,
   Part.group [52, 52, 52, 53, 51] TaifexNoPartyIDs.members TaifexNoPartyIDs.encode TaifexNoPartyIDs.within record.taifexNoPartyIDs,
   Part.required [49, 55] record.execID,
   Part.required [49, 53, 48] record.execType,
   Part.optional [52, 49] record.origClOrdID,
   Part.optional [49] record.account,
   Part.required [51, 57] record.ordStatus,
   Part.required [53, 53] record.symbol,
   Part.required [53, 52] record.side,
   Part.optional [52, 48] record.ordType,
   Part.optional [51, 56] record.orderQty,
   Part.required [49, 53, 49] record.leavesQty,
   Part.required [49, 52] record.cumQty,
   Part.required [54] record.avgPx,
   Part.optional [52, 52] record.price,
   Part.optional [55, 55] record.positionEffect,
   Part.optional [53, 56] record.text,
   Part.optional [51, 50] record.lastQty,
   Part.optional [51, 49] record.lastPx,
   Part.optional [54, 48] record.transactTime,
   Part.optional [53, 57] record.timeInForce,
   Part.group [52, 52, 53, 53, 53] TaifexNoLegsExecution.members TaifexNoLegsExecution.encode TaifexNoLegsExecution.within record.taifexNoLegsExecution,
   Part.required [50, 48] record.execTransType,
   Part.optional [52, 52, 52, 54, 49] record.taifexCFICode,
   Part.required [49, 48, 48, 48, 48] record.taifexSymbolType,
   Part.optional [49, 48, 48, 48, 52] record.taifexPartID]

def ExecutionReport.tags : List (List (List UInt8)) :=
  [[[51, 55]], [[49, 49]], [52, 52, 52, 53, 51] :: TaifexNoPartyIDs.members, [[49, 55]], [[49, 53, 48]], [[52, 49]], [[49]], [[51, 57]], [[53, 53]], [[53, 52]], [[52, 48]], [[51, 56]], [[49, 53, 49]], [[49, 52]], [[54]], [[52, 52]], [[55, 55]], [[53, 56]], [[51, 50]], [[51, 49]], [[54, 48]], [[53, 57]], [52, 52, 53, 53, 53] :: TaifexNoLegsExecution.members, [[50, 48]], [[52, 52, 52, 54, 49]], [[49, 48, 48, 48, 48]], [[49, 48, 48, 48, 52]]]

theorem ExecutionReport.shape (record : ExecutionReport) : record.parts.map Part.tags = ExecutionReport.tags := rfl

def ExecutionReport.decode (tokens : List Token) : Option ExecutionReport := do
  let orderID ← readRequired [51, 55] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let taifexNoPartyIDs ← readGroup [52, 52, 52, 53, 51] [52, 52, 52, 52, 56] TaifexNoPartyIDs.members TaifexNoPartyIDs.decode tokens
  let execID ← readRequired [49, 55] tokens
  let execType ← readRequired [49, 53, 48] tokens
  let origClOrdID ← readOptional [52, 49] tokens
  let account ← readOptional [49] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let symbol ← readRequired [53, 53] tokens
  let side ← readRequired [53, 52] tokens
  let ordType ← readOptional [52, 48] tokens
  let orderQty ← readOptional [51, 56] tokens
  let leavesQty ← readRequired [49, 53, 49] tokens
  let cumQty ← readRequired [49, 52] tokens
  let avgPx ← readRequired [54] tokens
  let price ← readOptional [52, 52] tokens
  let positionEffect ← readOptional [55, 55] tokens
  let text ← readOptional [53, 56] tokens
  let lastQty ← readOptional [51, 50] tokens
  let lastPx ← readOptional [51, 49] tokens
  let transactTime ← readOptional [54, 48] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let taifexNoLegsExecution ← readGroup [52, 52, 53, 53, 53] [52, 52, 54, 48, 48] TaifexNoLegsExecution.members TaifexNoLegsExecution.decode tokens
  let execTransType ← readRequired [50, 48] tokens
  let taifexCFICode ← readOptional [52, 52, 52, 54, 49] tokens
  let taifexSymbolType ← readRequired [49, 48, 48, 48, 48] tokens
  let taifexPartID ← readOptional [49, 48, 48, 48, 52] tokens
  pure { orderID, clOrdID, taifexNoPartyIDs, execID, execType, origClOrdID, account, ordStatus, symbol, side, ordType, orderQty, leavesQty, cumQty, avgPx, price, positionEffect, text, lastQty, lastPx, transactTime, timeInForce, taifexNoLegsExecution, execTransType, taifexCFICode, taifexSymbolType, taifexPartID }

theorem ExecutionReport.decode_agrees (record : ExecutionReport) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReport.decode tokens = some record := by
  have distinct : ExecutionReport.tags.flatten.Nodup := by decide +kernel
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have taifexNoPartyIDs := readGroup_part [52, 52, 52, 53, 51] [52, 52, 52, 52, 56] TaifexNoPartyIDs.members TaifexNoPartyIDs.encode TaifexNoPartyIDs.within TaifexNoPartyIDs.decode TaifexNoPartyIDs.decode_encode TaifexNoPartyIDs.led record.taifexNoPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have execID := readRequired_part [49, 55] record.execID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have execType := readRequired_part [49, 53, 48] record.execType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have ordType := readOptional_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have orderQty := readOptional_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have leavesQty := readRequired_part [49, 53, 49] record.leavesQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have cumQty := readRequired_part [49, 52] record.cumQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have avgPx := readRequired_part [54] record.avgPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have positionEffect := readOptional_part [55, 55] record.positionEffect tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have lastQty := readOptional_part [51, 50] record.lastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have lastPx := readOptional_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have taifexNoLegsExecution := readGroup_part [52, 52, 53, 53, 53] [52, 52, 54, 48, 48] TaifexNoLegsExecution.members TaifexNoLegsExecution.encode TaifexNoLegsExecution.within TaifexNoLegsExecution.decode TaifexNoLegsExecution.decode_encode TaifexNoLegsExecution.led record.taifexNoLegsExecution tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have execTransType := readRequired_part [50, 48] record.execTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have taifexCFICode := readOptional_part [52, 52, 52, 54, 49] record.taifexCFICode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have taifexSymbolType := readRequired_part [49, 48, 48, 48, 48] record.taifexSymbolType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have taifexPartID := readOptional_part [49, 48, 48, 48, 52] record.taifexPartID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  simp only [ExecutionReport.decode, orderID, clOrdID, taifexNoPartyIDs, execID, execType, origClOrdID, account, ordStatus, symbol, side, ordType, orderQty, leavesQty, cumQty, avgPx, price, positionEffect, text, lastQty, lastPx, transactTime, timeInForce, taifexNoLegsExecution, execTransType, taifexCFICode, taifexSymbolType, taifexPartID, some_bind] <;> rfl

theorem ExecutionReport.taken (record : ExecutionReport) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 55] record.orderID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_group pairing [52, 52, 52, 53, 51] TaifexNoPartyIDs.members TaifexNoPartyIDs.encode TaifexNoPartyIDs.within (by decide) (by decide) TaifexNoPartyIDs.taken record.taifexNoPartyIDs)
     (paired_cons pairing _ _ (paired_required pairing [49, 55] record.execID (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [49, 53, 48] record.execType (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [52, 49] record.origClOrdID (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [49] record.account (by decide) (by decide))
         (paired_cons pairing _ _ (paired_required pairing [51, 57] record.ordStatus (by decide) (by decide))
          (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
           (paired_cons pairing _ _ (paired_required pairing [53, 52] record.side (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [52, 48] record.ordType (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [51, 56] record.orderQty (by decide) (by decide))
              (paired_cons pairing _ _ (paired_required pairing [49, 53, 49] record.leavesQty (by decide) (by decide))
               (paired_cons pairing _ _ (paired_required pairing [49, 52] record.cumQty (by decide) (by decide))
                (paired_cons pairing _ _ (paired_required pairing [54] record.avgPx (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_optional pairing [52, 52] record.price (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [55, 55] record.positionEffect (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_optional pairing [51, 50] record.lastQty (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_optional pairing [51, 49] record.lastPx (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_optional pairing [54, 48] record.transactTime (by decide) (by decide))
                       (paired_cons pairing _ _ (paired_optional pairing [53, 57] record.timeInForce (by decide) (by decide))
                        (paired_cons pairing _ _ (paired_group pairing [52, 52, 53, 53, 53] TaifexNoLegsExecution.members TaifexNoLegsExecution.encode TaifexNoLegsExecution.within (by decide) (by decide) TaifexNoLegsExecution.taken record.taifexNoLegsExecution)
                         (paired_cons pairing _ _ (paired_required pairing [50, 48] record.execTransType (by decide) (by decide))
                          (paired_cons pairing _ _ (paired_optional pairing [52, 52, 52, 54, 49] record.taifexCFICode (by decide) (by decide))
                           (paired_cons pairing _ _ (paired_required pairing [49, 48, 48, 48, 48] record.taifexSymbolType (by decide) (by decide))
                            (paired_cons pairing _ _ (paired_optional pairing [49, 48, 48, 48, 52] record.taifexPartID (by decide) (by decide))
                             (paired_none pairing)))))))))))))))))))))))))))

structure OrderCancelReject where
  orderID : Terminated 1  -- tag 37
  clOrdID : Terminated 1  -- tag 11
  origClOrdID : Terminated 1  -- tag 41
  ordStatus : Terminated 1  -- tag 39
  cxlRejResponseTo : Terminated 1  -- tag 434
  execID : Option (Terminated 1)  -- tag 17
  text : Option (Terminated 1)  -- tag 58
  taifexPartID : Option (Terminated 1)  -- tag 10004

def OrderCancelReject.parts (record : OrderCancelReject) : List Part :=
  [Part.required [51, 55] record.orderID,
   Part.required [49, 49] record.clOrdID,
   Part.required [52, 49] record.origClOrdID,
   Part.required [51, 57] record.ordStatus,
   Part.required [52, 51, 52] record.cxlRejResponseTo,
   Part.optional [49, 55] record.execID,
   Part.optional [53, 56] record.text,
   Part.optional [49, 48, 48, 48, 52] record.taifexPartID]

def OrderCancelReject.tags : List (List (List UInt8)) :=
  [[[51, 55]], [[49, 49]], [[52, 49]], [[51, 57]], [[52, 51, 52]], [[49, 55]], [[53, 56]], [[49, 48, 48, 48, 52]]]

theorem OrderCancelReject.shape (record : OrderCancelReject) : record.parts.map Part.tags = OrderCancelReject.tags := rfl

def OrderCancelReject.decode (tokens : List Token) : Option OrderCancelReject := do
  let orderID ← readRequired [51, 55] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let cxlRejResponseTo ← readRequired [52, 51, 52] tokens
  let execID ← readOptional [49, 55] tokens
  let text ← readOptional [53, 56] tokens
  let taifexPartID ← readOptional [49, 48, 48, 48, 52] tokens
  pure { orderID, clOrdID, origClOrdID, ordStatus, cxlRejResponseTo, execID, text, taifexPartID }

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
  have cxlRejResponseTo := readRequired_part [52, 51, 52] record.cxlRejResponseTo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have execID := readOptional_part [49, 55] record.execID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have taifexPartID := readOptional_part [49, 48, 48, 48, 52] record.taifexPartID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  simp only [OrderCancelReject.decode, orderID, clOrdID, origClOrdID, ordStatus, cxlRejResponseTo, execID, text, taifexPartID, some_bind] <;> rfl

theorem OrderCancelReject.taken (record : OrderCancelReject) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 55] record.orderID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [52, 49] record.origClOrdID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [51, 57] record.ordStatus (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [52, 51, 52] record.cxlRejResponseTo (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [49, 55] record.execID (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [49, 48, 48, 48, 52] record.taifexPartID (by decide) (by decide))
          (paired_none pairing))))))))

structure QuoteRequestReport where
  quoteReqID : Terminated 1  -- tag 131
  taifexPartID : Option (Terminated 1)  -- tag 10004

def QuoteRequestReport.parts (record : QuoteRequestReport) : List Part :=
  [Part.required [49, 51, 49] record.quoteReqID,
   Part.optional [49, 48, 48, 48, 52] record.taifexPartID]

def QuoteRequestReport.tags : List (List (List UInt8)) :=
  [[[49, 51, 49]], [[49, 48, 48, 48, 52]]]

theorem QuoteRequestReport.shape (record : QuoteRequestReport) : record.parts.map Part.tags = QuoteRequestReport.tags := rfl

def QuoteRequestReport.decode (tokens : List Token) : Option QuoteRequestReport := do
  let quoteReqID ← readRequired [49, 51, 49] tokens
  let taifexPartID ← readOptional [49, 48, 48, 48, 52] tokens
  pure { quoteReqID, taifexPartID }

theorem QuoteRequestReport.decode_agrees (record : QuoteRequestReport) (tokens : List Token)
    (agrees : ∀ tags ∈ QuoteRequestReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    QuoteRequestReport.decode tokens = some record := by
  have distinct : QuoteRequestReport.tags.flatten.Nodup := by decide +kernel
  have quoteReqID := readRequired_part [49, 51, 49] record.quoteReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have taifexPartID := readOptional_part [49, 48, 48, 48, 52] record.taifexPartID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [QuoteRequestReport.decode, quoteReqID, taifexPartID, some_bind] <;> rfl

theorem QuoteRequestReport.taken (record : QuoteRequestReport) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 51, 49] record.quoteReqID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [49, 48, 48, 48, 52] record.taifexPartID (by decide) (by decide))
    (paired_none pairing))

structure NoRelatedSym where
  symbol : Terminated 1  -- tag 55
  taifexCFICode : Terminated 1  -- tag 44461
  taifexSymbolType : Terminated 1  -- tag 10000

def NoRelatedSym.parts (record : NoRelatedSym) : List Part :=
  [Part.required [53, 53] record.symbol,
   Part.required [52, 52, 52, 54, 49] record.taifexCFICode,
   Part.required [49, 48, 48, 48, 48] record.taifexSymbolType]

def NoRelatedSym.tags : List (List (List UInt8)) :=
  [[[53, 53]], [[52, 52, 52, 54, 49]], [[49, 48, 48, 48, 48]]]

theorem NoRelatedSym.shape (record : NoRelatedSym) : record.parts.map Part.tags = NoRelatedSym.tags := rfl

def NoRelatedSym.decode (tokens : List Token) : Option NoRelatedSym := do
  let symbol ← readRequired [53, 53] tokens
  let taifexCFICode ← readRequired [52, 52, 52, 54, 49] tokens
  let taifexSymbolType ← readRequired [49, 48, 48, 48, 48] tokens
  pure { symbol, taifexCFICode, taifexSymbolType }

theorem NoRelatedSym.decode_agrees (record : NoRelatedSym) (tokens : List Token)
    (agrees : ∀ tags ∈ NoRelatedSym.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoRelatedSym.decode tokens = some record := by
  have distinct : NoRelatedSym.tags.flatten.Nodup := by decide +kernel
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have taifexCFICode := readRequired_part [52, 52, 52, 54, 49] record.taifexCFICode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have taifexSymbolType := readRequired_part [49, 48, 48, 48, 48] record.taifexSymbolType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [NoRelatedSym.decode, symbol, taifexCFICode, taifexSymbolType, some_bind] <;> rfl

theorem NoRelatedSym.taken (record : NoRelatedSym) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [52, 52, 52, 54, 49] record.taifexCFICode (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [49, 48, 48, 48, 48] record.taifexSymbolType (by decide) (by decide))
     (paired_none pairing)))

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

structure QuoteRequestReject where
  quoteReqID : Terminated 1  -- tag 131
  taifexQuoteRequestRejectReason : Terminated 1  -- tag 44658
  noRelatedSym : List NoRelatedSym  -- tag 146
  text : Option (Terminated 1)  -- tag 58
  taifexPartID : Option (Terminated 1)  -- tag 10004

def QuoteRequestReject.parts (record : QuoteRequestReject) : List Part :=
  [Part.required [49, 51, 49] record.quoteReqID,
   Part.required [52, 52, 54, 53, 56] record.taifexQuoteRequestRejectReason,
   Part.group [49, 52, 54] NoRelatedSym.members NoRelatedSym.encode NoRelatedSym.within record.noRelatedSym,
   Part.optional [53, 56] record.text,
   Part.optional [49, 48, 48, 48, 52] record.taifexPartID]

def QuoteRequestReject.tags : List (List (List UInt8)) :=
  [[[49, 51, 49]], [[52, 52, 54, 53, 56]], [49, 52, 54] :: NoRelatedSym.members, [[53, 56]], [[49, 48, 48, 48, 52]]]

theorem QuoteRequestReject.shape (record : QuoteRequestReject) : record.parts.map Part.tags = QuoteRequestReject.tags := rfl

def QuoteRequestReject.decode (tokens : List Token) : Option QuoteRequestReject := do
  let quoteReqID ← readRequired [49, 51, 49] tokens
  let taifexQuoteRequestRejectReason ← readRequired [52, 52, 54, 53, 56] tokens
  let noRelatedSym ← readGroup [49, 52, 54] [53, 53] NoRelatedSym.members NoRelatedSym.decode tokens
  let text ← readOptional [53, 56] tokens
  let taifexPartID ← readOptional [49, 48, 48, 48, 52] tokens
  pure { quoteReqID, taifexQuoteRequestRejectReason, noRelatedSym, text, taifexPartID }

theorem QuoteRequestReject.decode_agrees (record : QuoteRequestReject) (tokens : List Token)
    (agrees : ∀ tags ∈ QuoteRequestReject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    QuoteRequestReject.decode tokens = some record := by
  have distinct : QuoteRequestReject.tags.flatten.Nodup := by decide +kernel
  have quoteReqID := readRequired_part [49, 51, 49] record.quoteReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have taifexQuoteRequestRejectReason := readRequired_part [52, 52, 54, 53, 56] record.taifexQuoteRequestRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have noRelatedSym := readGroup_part [49, 52, 54] [53, 53] NoRelatedSym.members NoRelatedSym.encode NoRelatedSym.within NoRelatedSym.decode NoRelatedSym.decode_encode NoRelatedSym.led record.noRelatedSym tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have taifexPartID := readOptional_part [49, 48, 48, 48, 52] record.taifexPartID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [QuoteRequestReject.decode, quoteReqID, taifexQuoteRequestRejectReason, noRelatedSym, text, taifexPartID, some_bind] <;> rfl

theorem QuoteRequestReject.taken (record : QuoteRequestReject) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 51, 49] record.quoteReqID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [52, 52, 54, 53, 56] record.taifexQuoteRequestRejectReason (by decide) (by decide))
    (paired_cons pairing _ _ (paired_group pairing [49, 52, 54] NoRelatedSym.members NoRelatedSym.encode NoRelatedSym.within (by decide) (by decide) NoRelatedSym.taken record.noRelatedSym)
     (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [49, 48, 48, 48, 52] record.taifexPartID (by decide) (by decide))
       (paired_none pairing)))))

structure QuoteStatusReport where
  quoteID : Terminated 1  -- tag 117
  symbol : Terminated 1  -- tag 55
  bidPx : Terminated 1  -- tag 132
  offerPx : Terminated 1  -- tag 133
  bidSize : Terminated 1  -- tag 134
  offerSize : Terminated 1  -- tag 135
  quoteAckStatus : Terminated 1  -- tag 297
  text : Option (Terminated 1)  -- tag 58
  taifexCFICode : Terminated 1  -- tag 44461
  taifexSymbolType : Terminated 1  -- tag 10000
  taifexPartID : Option (Terminated 1)  -- tag 10004

def QuoteStatusReport.parts (record : QuoteStatusReport) : List Part :=
  [Part.required [49, 49, 55] record.quoteID,
   Part.required [53, 53] record.symbol,
   Part.required [49, 51, 50] record.bidPx,
   Part.required [49, 51, 51] record.offerPx,
   Part.required [49, 51, 52] record.bidSize,
   Part.required [49, 51, 53] record.offerSize,
   Part.required [50, 57, 55] record.quoteAckStatus,
   Part.optional [53, 56] record.text,
   Part.required [52, 52, 52, 54, 49] record.taifexCFICode,
   Part.required [49, 48, 48, 48, 48] record.taifexSymbolType,
   Part.optional [49, 48, 48, 48, 52] record.taifexPartID]

def QuoteStatusReport.tags : List (List (List UInt8)) :=
  [[[49, 49, 55]], [[53, 53]], [[49, 51, 50]], [[49, 51, 51]], [[49, 51, 52]], [[49, 51, 53]], [[50, 57, 55]], [[53, 56]], [[52, 52, 52, 54, 49]], [[49, 48, 48, 48, 48]], [[49, 48, 48, 48, 52]]]

theorem QuoteStatusReport.shape (record : QuoteStatusReport) : record.parts.map Part.tags = QuoteStatusReport.tags := rfl

def QuoteStatusReport.decode (tokens : List Token) : Option QuoteStatusReport := do
  let quoteID ← readRequired [49, 49, 55] tokens
  let symbol ← readRequired [53, 53] tokens
  let bidPx ← readRequired [49, 51, 50] tokens
  let offerPx ← readRequired [49, 51, 51] tokens
  let bidSize ← readRequired [49, 51, 52] tokens
  let offerSize ← readRequired [49, 51, 53] tokens
  let quoteAckStatus ← readRequired [50, 57, 55] tokens
  let text ← readOptional [53, 56] tokens
  let taifexCFICode ← readRequired [52, 52, 52, 54, 49] tokens
  let taifexSymbolType ← readRequired [49, 48, 48, 48, 48] tokens
  let taifexPartID ← readOptional [49, 48, 48, 48, 52] tokens
  pure { quoteID, symbol, bidPx, offerPx, bidSize, offerSize, quoteAckStatus, text, taifexCFICode, taifexSymbolType, taifexPartID }

theorem QuoteStatusReport.decode_agrees (record : QuoteStatusReport) (tokens : List Token)
    (agrees : ∀ tags ∈ QuoteStatusReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    QuoteStatusReport.decode tokens = some record := by
  have distinct : QuoteStatusReport.tags.flatten.Nodup := by decide +kernel
  have quoteID := readRequired_part [49, 49, 55] record.quoteID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have bidPx := readRequired_part [49, 51, 50] record.bidPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have offerPx := readRequired_part [49, 51, 51] record.offerPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have bidSize := readRequired_part [49, 51, 52] record.bidSize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have offerSize := readRequired_part [49, 51, 53] record.offerSize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have quoteAckStatus := readRequired_part [50, 57, 55] record.quoteAckStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have taifexCFICode := readRequired_part [52, 52, 52, 54, 49] record.taifexCFICode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have taifexSymbolType := readRequired_part [49, 48, 48, 48, 48] record.taifexSymbolType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have taifexPartID := readOptional_part [49, 48, 48, 48, 52] record.taifexPartID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  simp only [QuoteStatusReport.decode, quoteID, symbol, bidPx, offerPx, bidSize, offerSize, quoteAckStatus, text, taifexCFICode, taifexSymbolType, taifexPartID, some_bind] <;> rfl

theorem QuoteStatusReport.taken (record : QuoteStatusReport) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 49, 55] record.quoteID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [49, 51, 50] record.bidPx (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [49, 51, 51] record.offerPx (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [49, 51, 52] record.bidSize (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [49, 51, 53] record.offerSize (by decide) (by decide))
        (paired_cons pairing _ _ (paired_required pairing [50, 57, 55] record.quoteAckStatus (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
          (paired_cons pairing _ _ (paired_required pairing [52, 52, 52, 54, 49] record.taifexCFICode (by decide) (by decide))
           (paired_cons pairing _ _ (paired_required pairing [49, 48, 48, 48, 48] record.taifexSymbolType (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [49, 48, 48, 48, 52] record.taifexPartID (by decide) (by decide))
             (paired_none pairing)))))))))))

structure TradingSessionStatus where
  tradSesReqID : Terminated 1  -- tag 335
  tradSesStatus : Terminated 1  -- tag 340
  tradingSessionID : Terminated 1  -- tag 336
  text : Option (Terminated 1)  -- tag 58

def TradingSessionStatus.parts (record : TradingSessionStatus) : List Part :=
  [Part.required [51, 51, 53] record.tradSesReqID,
   Part.required [51, 52, 48] record.tradSesStatus,
   Part.required [51, 51, 54] record.tradingSessionID,
   Part.optional [53, 56] record.text]

def TradingSessionStatus.tags : List (List (List UInt8)) :=
  [[[51, 51, 53]], [[51, 52, 48]], [[51, 51, 54]], [[53, 56]]]

theorem TradingSessionStatus.shape (record : TradingSessionStatus) : record.parts.map Part.tags = TradingSessionStatus.tags := rfl

def TradingSessionStatus.decode (tokens : List Token) : Option TradingSessionStatus := do
  let tradSesReqID ← readRequired [51, 51, 53] tokens
  let tradSesStatus ← readRequired [51, 52, 48] tokens
  let tradingSessionID ← readRequired [51, 51, 54] tokens
  let text ← readOptional [53, 56] tokens
  pure { tradSesReqID, tradSesStatus, tradingSessionID, text }

theorem TradingSessionStatus.decode_agrees (record : TradingSessionStatus) (tokens : List Token)
    (agrees : ∀ tags ∈ TradingSessionStatus.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TradingSessionStatus.decode tokens = some record := by
  have distinct : TradingSessionStatus.tags.flatten.Nodup := by decide +kernel
  have tradSesReqID := readRequired_part [51, 51, 53] record.tradSesReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have tradSesStatus := readRequired_part [51, 52, 48] record.tradSesStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have tradingSessionID := readRequired_part [51, 51, 54] record.tradingSessionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [TradingSessionStatus.decode, tradSesReqID, tradSesStatus, tradingSessionID, text, some_bind] <;> rfl

theorem TradingSessionStatus.taken (record : TradingSessionStatus) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 51, 53] record.tradSesReqID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [51, 52, 48] record.tradSesStatus (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [51, 51, 54] record.tradingSessionID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
      (paired_none pairing))))

structure LinesOfText where
  text : Terminated 1  -- tag 58

def LinesOfText.parts (record : LinesOfText) : List Part :=
  [Part.required [53, 56] record.text]

def LinesOfText.tags : List (List (List UInt8)) :=
  [[[53, 56]]]

theorem LinesOfText.shape (record : LinesOfText) : record.parts.map Part.tags = LinesOfText.tags := rfl

def LinesOfText.decode (tokens : List Token) : Option LinesOfText := do
  let text ← readRequired [53, 56] tokens
  pure { text }

theorem LinesOfText.decode_agrees (record : LinesOfText) (tokens : List Token)
    (agrees : ∀ tags ∈ LinesOfText.tags, select tags tokens = select tags (encodeParts record.parts)) :
    LinesOfText.decode tokens = some record := by
  have distinct : LinesOfText.tags.flatten.Nodup := by decide +kernel
  have text := readRequired_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [LinesOfText.decode, text, some_bind] <;> rfl

theorem LinesOfText.taken (record : LinesOfText) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [53, 56] record.text (by decide) (by decide))
   (paired_none pairing)

def LinesOfText.members : List (List UInt8) := LinesOfText.tags.flatten

def LinesOfText.encode (entry : LinesOfText) : List Token := encodeParts entry.parts

theorem LinesOfText.decode_encode (entry : LinesOfText) : LinesOfText.decode entry.encode = some entry :=
  LinesOfText.decode_agrees entry _ (fun _ _ => rfl)

theorem LinesOfText.within (entry : LinesOfText) : ∀ token ∈ entry.encode, token.tag ∈ LinesOfText.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [LinesOfText.shape] at this

theorem LinesOfText.led (entry : LinesOfText) : Lead [53, 56] entry.encode :=
  lead_parts [53, 56] entry.text _ LinesOfText.tags.tail rfl (by decide +kernel)

structure Email where
  emailThreadID : Terminated 1  -- tag 164
  emailType : Terminated 1  -- tag 94
  origTime : Terminated 1  -- tag 42
  subject : Terminated 1  -- tag 147
  linesOfText : List LinesOfText  -- tag 33

def Email.parts (record : Email) : List Part :=
  [Part.required [49, 54, 52] record.emailThreadID,
   Part.required [57, 52] record.emailType,
   Part.required [52, 50] record.origTime,
   Part.required [49, 52, 55] record.subject,
   Part.group [51, 51] LinesOfText.members LinesOfText.encode LinesOfText.within record.linesOfText]

def Email.tags : List (List (List UInt8)) :=
  [[[49, 54, 52]], [[57, 52]], [[52, 50]], [[49, 52, 55]], [51, 51] :: LinesOfText.members]

theorem Email.shape (record : Email) : record.parts.map Part.tags = Email.tags := rfl

def Email.decode (tokens : List Token) : Option Email := do
  let emailThreadID ← readRequired [49, 54, 52] tokens
  let emailType ← readRequired [57, 52] tokens
  let origTime ← readRequired [52, 50] tokens
  let subject ← readRequired [49, 52, 55] tokens
  let linesOfText ← readGroup [51, 51] [53, 56] LinesOfText.members LinesOfText.decode tokens
  pure { emailThreadID, emailType, origTime, subject, linesOfText }

theorem Email.decode_agrees (record : Email) (tokens : List Token)
    (agrees : ∀ tags ∈ Email.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Email.decode tokens = some record := by
  have distinct : Email.tags.flatten.Nodup := by decide +kernel
  have emailThreadID := readRequired_part [49, 54, 52] record.emailThreadID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have emailType := readRequired_part [57, 52] record.emailType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have origTime := readRequired_part [52, 50] record.origTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have subject := readRequired_part [49, 52, 55] record.subject tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have linesOfText := readGroup_part [51, 51] [53, 56] LinesOfText.members LinesOfText.encode LinesOfText.within LinesOfText.decode LinesOfText.decode_encode LinesOfText.led record.linesOfText tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [Email.decode, emailThreadID, emailType, origTime, subject, linesOfText, some_bind] <;> rfl

theorem Email.taken (record : Email) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 54, 52] record.emailThreadID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [57, 52] record.emailType (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [52, 50] record.origTime (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [49, 52, 55] record.subject (by decide) (by decide))
      (paired_cons pairing _ _ (paired_group pairing [51, 51] LinesOfText.members LinesOfText.encode LinesOfText.within (by decide) (by decide) LinesOfText.taken record.linesOfText)
       (paired_none pairing)))))

structure SecurityDefinition where
  securityReqID : Terminated 1  -- tag 320
  securityResponseType : Terminated 1  -- tag 323
  text : Option (Terminated 1)  -- tag 58

def SecurityDefinition.parts (record : SecurityDefinition) : List Part :=
  [Part.required [51, 50, 48] record.securityReqID,
   Part.required [51, 50, 51] record.securityResponseType,
   Part.optional [53, 56] record.text]

def SecurityDefinition.tags : List (List (List UInt8)) :=
  [[[51, 50, 48]], [[51, 50, 51]], [[53, 56]]]

theorem SecurityDefinition.shape (record : SecurityDefinition) : record.parts.map Part.tags = SecurityDefinition.tags := rfl

def SecurityDefinition.decode (tokens : List Token) : Option SecurityDefinition := do
  let securityReqID ← readRequired [51, 50, 48] tokens
  let securityResponseType ← readRequired [51, 50, 51] tokens
  let text ← readOptional [53, 56] tokens
  pure { securityReqID, securityResponseType, text }

theorem SecurityDefinition.decode_agrees (record : SecurityDefinition) (tokens : List Token)
    (agrees : ∀ tags ∈ SecurityDefinition.tags, select tags tokens = select tags (encodeParts record.parts)) :
    SecurityDefinition.decode tokens = some record := by
  have distinct : SecurityDefinition.tags.flatten.Nodup := by decide +kernel
  have securityReqID := readRequired_part [51, 50, 48] record.securityReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityResponseType := readRequired_part [51, 50, 51] record.securityResponseType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [SecurityDefinition.decode, securityReqID, securityResponseType, text, some_bind] <;> rfl

theorem SecurityDefinition.taken (record : SecurityDefinition) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 50, 48] record.securityReqID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [51, 50, 51] record.securityResponseType (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
     (paired_none pairing)))

inductive Message where
  | logon (header : Header) (r0 : Logon)
  | logout (header : Header) (r0 : Logout)
  | heartbeat (header : Header) (r0 : Heartbeat)
  | testRequest (header : Header) (r0 : TestRequest)
  | resendRequest (header : Header) (r0 : ResendRequest)
  | reject (header : Header) (r0 : Reject)
  | sequenceResetGapFill (header : Header) (r0 : SequenceResetGapFill)
  | businessMessageReject (header : Header) (r0 : BusinessMessageReject)
  | executionReport (header : Header) (r0 : ExecutionReport)
  | orderCancelReject (header : Header) (r0 : OrderCancelReject)
  | quoteRequestReport (header : Header) (r0 : QuoteRequestReport)
  | quoteRequestReject (header : Header) (r0 : QuoteRequestReject)
  | quoteStatusReport (header : Header) (r0 : QuoteStatusReport)
  | tradingSessionStatus (header : Header) (r0 : TradingSessionStatus)
  | email (header : Header) (r0 : Email)
  | securityDefinition (header : Header) (r0 : SecurityDefinition)

def Message.tokens : Message → List Token
  | .logon header r0 => ⟨[51, 53], [65]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logout header r0 => ⟨[51, 53], [53]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .heartbeat header r0 => ⟨[51, 53], [48]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .testRequest header r0 => ⟨[51, 53], [49]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .resendRequest header r0 => ⟨[51, 53], [50]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .reject header r0 => ⟨[51, 53], [51]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .sequenceResetGapFill header r0 => ⟨[51, 53], [52]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .businessMessageReject header r0 => ⟨[51, 53], [106]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .executionReport header r0 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelReject header r0 => ⟨[51, 53], [57]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .quoteRequestReport header r0 => ⟨[51, 53], [85, 48, 56, 48]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .quoteRequestReject header r0 => ⟨[51, 53], [85, 65, 71]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .quoteStatusReport header r0 => ⟨[51, 53], [85, 65, 73]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .tradingSessionStatus header r0 => ⟨[51, 53], [104]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .email header r0 => ⟨[51, 53], [67]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .securityDefinition header r0 => ⟨[51, 53], [100]⟩ :: encodeParts (header.parts ++ r0.parts)

def Message.decode : List Token → Option Message
  | [] => none
  | token :: rest =>
    if token.tag = [51, 53] then
      if token.value = [65] then
        if known (Header.tags ++ Logon.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Logon.decode rest
          pure (.logon header r0)
        else none
      else if token.value = [53] then
        if known (Header.tags ++ Logout.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Logout.decode rest
          pure (.logout header r0)
        else none
      else if token.value = [48] then
        if known (Header.tags ++ Heartbeat.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Heartbeat.decode rest
          pure (.heartbeat header r0)
        else none
      else if token.value = [49] then
        if known (Header.tags ++ TestRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← TestRequest.decode rest
          pure (.testRequest header r0)
        else none
      else if token.value = [50] then
        if known (Header.tags ++ ResendRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← ResendRequest.decode rest
          pure (.resendRequest header r0)
        else none
      else if token.value = [51] then
        if known (Header.tags ++ Reject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Reject.decode rest
          pure (.reject header r0)
        else none
      else if token.value = [52] then
        if known (Header.tags ++ SequenceResetGapFill.tags) rest then do
          let header ← Header.decode rest
          let r0 ← SequenceResetGapFill.decode rest
          pure (.sequenceResetGapFill header r0)
        else none
      else if token.value = [106] then
        if known (Header.tags ++ BusinessMessageReject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← BusinessMessageReject.decode rest
          pure (.businessMessageReject header r0)
        else none
      else if token.value = [56] then
        if known (Header.tags ++ ExecutionReport.tags) rest then do
          let header ← Header.decode rest
          let r0 ← ExecutionReport.decode rest
          pure (.executionReport header r0)
        else none
      else if token.value = [57] then
        if known (Header.tags ++ OrderCancelReject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderCancelReject.decode rest
          pure (.orderCancelReject header r0)
        else none
      else if token.value = [85, 48, 56, 48] then
        if known (Header.tags ++ QuoteRequestReport.tags) rest then do
          let header ← Header.decode rest
          let r0 ← QuoteRequestReport.decode rest
          pure (.quoteRequestReport header r0)
        else none
      else if token.value = [85, 65, 71] then
        if known (Header.tags ++ QuoteRequestReject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← QuoteRequestReject.decode rest
          pure (.quoteRequestReject header r0)
        else none
      else if token.value = [85, 65, 73] then
        if known (Header.tags ++ QuoteStatusReport.tags) rest then do
          let header ← Header.decode rest
          let r0 ← QuoteStatusReport.decode rest
          pure (.quoteStatusReport header r0)
        else none
      else if token.value = [104] then
        if known (Header.tags ++ TradingSessionStatus.tags) rest then do
          let header ← Header.decode rest
          let r0 ← TradingSessionStatus.decode rest
          pure (.tradingSessionStatus header r0)
        else none
      else if token.value = [67] then
        if known (Header.tags ++ Email.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Email.decode rest
          pure (.email header r0)
        else none
      else if token.value = [100] then
        if known (Header.tags ++ SecurityDefinition.tags) rest then do
          let header ← Header.decode rest
          let r0 ← SecurityDefinition.decode rest
          pure (.securityDefinition header r0)
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

theorem Message.decode_sequenceResetGapFill (header : Header) (r0 : SequenceResetGapFill) :
    Message.decode (Message.tokens (.sequenceResetGapFill header r0)) = some (.sequenceResetGapFill header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (SequenceResetGapFill.tags) rfl rfl (by decide +kernel))
  have c1 := SequenceResetGapFill.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (SequenceResetGapFill.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ SequenceResetGapFill.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_businessMessageReject (header : Header) (r0 : BusinessMessageReject) :
    Message.decode (Message.tokens (.businessMessageReject header r0)) = some (.businessMessageReject header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (BusinessMessageReject.tags) rfl rfl (by decide +kernel))
  have c1 := BusinessMessageReject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (BusinessMessageReject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ BusinessMessageReject.tags) rfl
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

theorem Message.decode_quoteRequestReport (header : Header) (r0 : QuoteRequestReport) :
    Message.decode (Message.tokens (.quoteRequestReport header r0)) = some (.quoteRequestReport header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (QuoteRequestReport.tags) rfl rfl (by decide +kernel))
  have c1 := QuoteRequestReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (QuoteRequestReport.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ QuoteRequestReport.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_quoteRequestReject (header : Header) (r0 : QuoteRequestReject) :
    Message.decode (Message.tokens (.quoteRequestReject header r0)) = some (.quoteRequestReject header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (QuoteRequestReject.tags) rfl rfl (by decide +kernel))
  have c1 := QuoteRequestReject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (QuoteRequestReject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ QuoteRequestReject.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_quoteStatusReport (header : Header) (r0 : QuoteStatusReport) :
    Message.decode (Message.tokens (.quoteStatusReport header r0)) = some (.quoteStatusReport header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (QuoteStatusReport.tags) rfl rfl (by decide +kernel))
  have c1 := QuoteStatusReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (QuoteStatusReport.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ QuoteStatusReport.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tradingSessionStatus (header : Header) (r0 : TradingSessionStatus) :
    Message.decode (Message.tokens (.tradingSessionStatus header r0)) = some (.tradingSessionStatus header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (TradingSessionStatus.tags) rfl rfl (by decide +kernel))
  have c1 := TradingSessionStatus.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (TradingSessionStatus.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ TradingSessionStatus.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_email (header : Header) (r0 : Email) :
    Message.decode (Message.tokens (.email header r0)) = some (.email header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (Email.tags) rfl rfl (by decide +kernel))
  have c1 := Email.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (Email.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ Email.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_securityDefinition (header : Header) (r0 : SecurityDefinition) :
    Message.decode (Message.tokens (.securityDefinition header r0)) = some (.securityDefinition header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (SecurityDefinition.tags) rfl rfl (by decide +kernel))
  have c1 := SecurityDefinition.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (SecurityDefinition.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ SecurityDefinition.tags) rfl
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
  | sequenceResetGapFill header r0 => exact Message.decode_sequenceResetGapFill header r0
  | businessMessageReject header r0 => exact Message.decode_businessMessageReject header r0
  | executionReport header r0 => exact Message.decode_executionReport header r0
  | orderCancelReject header r0 => exact Message.decode_orderCancelReject header r0
  | quoteRequestReport header r0 => exact Message.decode_quoteRequestReport header r0
  | quoteRequestReject header r0 => exact Message.decode_quoteRequestReject header r0
  | quoteStatusReport header r0 => exact Message.decode_quoteStatusReport header r0
  | tradingSessionStatus header r0 => exact Message.decode_tradingSessionStatus header r0
  | email header r0 => exact Message.decode_email header r0
  | securityDefinition header r0 => exact Message.decode_securityDefinition header r0

def Message.encode (message : Message) : List UInt8 := encodeTokens message.tokens

def Message.decodeBytes (bytes : List UInt8) : Option Message := do
  let tokens ← decodeTokens pairing bytes.length bytes
  Message.decode tokens

theorem Message.decodeBytes_logon (header : Header) (r0 : Logon) :
    Message.decodeBytes (Message.encode (.logon header r0)) = some (.logon header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [65]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (Logon.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_logon header r0

theorem Message.decodeBytes_logout (header : Header) (r0 : Logout) :
    Message.decodeBytes (Message.encode (.logout header r0)) = some (.logout header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [53]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (Logout.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_logout header r0

theorem Message.decodeBytes_heartbeat (header : Header) (r0 : Heartbeat) :
    Message.decodeBytes (Message.encode (.heartbeat header r0)) = some (.heartbeat header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [48]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (Heartbeat.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_heartbeat header r0

theorem Message.decodeBytes_testRequest (header : Header) (r0 : TestRequest) :
    Message.decodeBytes (Message.encode (.testRequest header r0)) = some (.testRequest header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [49]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (TestRequest.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_testRequest header r0

theorem Message.decodeBytes_resendRequest (header : Header) (r0 : ResendRequest) :
    Message.decodeBytes (Message.encode (.resendRequest header r0)) = some (.resendRequest header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [50]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (ResendRequest.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_resendRequest header r0

theorem Message.decodeBytes_reject (header : Header) (r0 : Reject) :
    Message.decodeBytes (Message.encode (.reject header r0)) = some (.reject header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [51]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (Reject.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_reject header r0

theorem Message.decodeBytes_sequenceResetGapFill (header : Header) (r0 : SequenceResetGapFill) :
    Message.decodeBytes (Message.encode (.sequenceResetGapFill header r0)) = some (.sequenceResetGapFill header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [52]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (SequenceResetGapFill.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_sequenceResetGapFill header r0

theorem Message.decodeBytes_businessMessageReject (header : Header) (r0 : BusinessMessageReject) :
    Message.decodeBytes (Message.encode (.businessMessageReject header r0)) = some (.businessMessageReject header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [106]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (BusinessMessageReject.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_businessMessageReject header r0

theorem Message.decodeBytes_executionReport (header : Header) (r0 : ExecutionReport) :
    Message.decodeBytes (Message.encode (.executionReport header r0)) = some (.executionReport header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [56]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (ExecutionReport.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReport header r0

theorem Message.decodeBytes_orderCancelReject (header : Header) (r0 : OrderCancelReject) :
    Message.decodeBytes (Message.encode (.orderCancelReject header r0)) = some (.orderCancelReject header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [57]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (OrderCancelReject.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderCancelReject header r0

theorem Message.decodeBytes_quoteRequestReport (header : Header) (r0 : QuoteRequestReport) :
    Message.decodeBytes (Message.encode (.quoteRequestReport header r0)) = some (.quoteRequestReport header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [85, 48, 56, 48]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (QuoteRequestReport.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_quoteRequestReport header r0

theorem Message.decodeBytes_quoteRequestReject (header : Header) (r0 : QuoteRequestReject) :
    Message.decodeBytes (Message.encode (.quoteRequestReject header r0)) = some (.quoteRequestReject header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [85, 65, 71]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (QuoteRequestReject.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_quoteRequestReject header r0

theorem Message.decodeBytes_quoteStatusReport (header : Header) (r0 : QuoteStatusReport) :
    Message.decodeBytes (Message.encode (.quoteStatusReport header r0)) = some (.quoteStatusReport header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [85, 65, 73]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (QuoteStatusReport.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_quoteStatusReport header r0

theorem Message.decodeBytes_tradingSessionStatus (header : Header) (r0 : TradingSessionStatus) :
    Message.decodeBytes (Message.encode (.tradingSessionStatus header r0)) = some (.tradingSessionStatus header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [104]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (TradingSessionStatus.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_tradingSessionStatus header r0

theorem Message.decodeBytes_email (header : Header) (r0 : Email) :
    Message.decodeBytes (Message.encode (.email header r0)) = some (.email header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [67]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (Email.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_email header r0

theorem Message.decodeBytes_securityDefinition (header : Header) (r0 : SecurityDefinition) :
    Message.decodeBytes (Message.encode (.securityDefinition header r0)) = some (.securityDefinition header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [100]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (SecurityDefinition.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_securityDefinition header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | logon header r0 => exact Message.decodeBytes_logon header r0
  | logout header r0 => exact Message.decodeBytes_logout header r0
  | heartbeat header r0 => exact Message.decodeBytes_heartbeat header r0
  | testRequest header r0 => exact Message.decodeBytes_testRequest header r0
  | resendRequest header r0 => exact Message.decodeBytes_resendRequest header r0
  | reject header r0 => exact Message.decodeBytes_reject header r0
  | sequenceResetGapFill header r0 => exact Message.decodeBytes_sequenceResetGapFill header r0
  | businessMessageReject header r0 => exact Message.decodeBytes_businessMessageReject header r0
  | executionReport header r0 => exact Message.decodeBytes_executionReport header r0
  | orderCancelReject header r0 => exact Message.decodeBytes_orderCancelReject header r0
  | quoteRequestReport header r0 => exact Message.decodeBytes_quoteRequestReport header r0
  | quoteRequestReject header r0 => exact Message.decodeBytes_quoteRequestReject header r0
  | quoteStatusReport header r0 => exact Message.decodeBytes_quoteStatusReport header r0
  | tradingSessionStatus header r0 => exact Message.decodeBytes_tradingSessionStatus header r0
  | email header r0 => exact Message.decodeBytes_email header r0
  | securityDefinition header r0 => exact Message.decodeBytes_securityDefinition header r0

/-- BeginString as the venue fixes it: FIX.4.2 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 46, 52, 46, 50, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.TaifexTaifexderivativesOrderentryFix42V312Exchange
