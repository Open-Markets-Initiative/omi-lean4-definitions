import Wire

/-!
# New York Stock Exchange Order Entry v3.24, Client messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.NyseAmexoptionsOrderentryFixV324Client

/-- No field of this tree is data, so every value ends at the separator -/
def pairing : Pairing := []

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
   Part.optional [49, 50, 56] record.deliverToCompID]

def Header.tags : List (List (List UInt8)) :=
  [[[51, 52]], [[52, 51]], [[52, 57]], [[53, 48]], [[53, 50]], [[53, 54]], [[53, 55]], [[57, 55]], [[49, 49, 53]], [[49, 49, 54]], [[49, 50, 50]], [[49, 50, 56]]]

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
  pure { msgSeqNum, possDupFlag, senderCompID, senderSubID, sendingTime, targetCompID, targetSubID, possResend, onBehalfOfCompID, onBehalfOfSubID, origSendingTime, deliverToCompID }

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
  simp only [Header.decode, msgSeqNum, possDupFlag, senderCompID, senderSubID, sendingTime, targetCompID, targetSubID, possResend, onBehalfOfCompID, onBehalfOfSubID, origSendingTime, deliverToCompID, some_bind] <;> rfl

theorem Header.taken (record : Header) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 52] record.msgSeqNum (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [52, 51] record.possDupFlag (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [52, 57] record.senderCompID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [53, 48] record.senderSubID (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [53, 50] record.sendingTime (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [53, 54] record.targetCompID (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [53, 55] record.targetSubID (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [57, 55] record.possResend (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [49, 49, 53] record.onBehalfOfCompID (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [49, 49, 54] record.onBehalfOfSubID (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [49, 50, 50] record.origSendingTime (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [49, 50, 56] record.deliverToCompID (by decide) (by decide))
              (paired_none pairing))))))))))))

structure Logon where
  encryptMethod : Terminated 1  -- tag 98
  heartBtInt : Terminated 1  -- tag 108
  rawDataLength : Option (Terminated 1)  -- tag 95
  rawData : Option (Terminated 1)  -- tag 96
  resetSeqNumFlag : Option (Terminated 1)  -- tag 141
  username : Terminated 1  -- tag 553
  password : Terminated 1  -- tag 554
  text : Option (Terminated 1)  -- tag 58
  nextExpectedMsgSeqNum : Terminated 1  -- tag 789
  sessionStatus : Option (Terminated 1)  -- tag 1409

def Logon.parts (record : Logon) : List Part :=
  [Part.required [57, 56] record.encryptMethod,
   Part.required [49, 48, 56] record.heartBtInt,
   Part.optional [57, 53] record.rawDataLength,
   Part.optional [57, 54] record.rawData,
   Part.optional [49, 52, 49] record.resetSeqNumFlag,
   Part.required [53, 53, 51] record.username,
   Part.required [53, 53, 52] record.password,
   Part.optional [53, 56] record.text,
   Part.required [55, 56, 57] record.nextExpectedMsgSeqNum,
   Part.optional [49, 52, 48, 57] record.sessionStatus]

def Logon.tags : List (List (List UInt8)) :=
  [[[57, 56]], [[49, 48, 56]], [[57, 53]], [[57, 54]], [[49, 52, 49]], [[53, 53, 51]], [[53, 53, 52]], [[53, 56]], [[55, 56, 57]], [[49, 52, 48, 57]]]

theorem Logon.shape (record : Logon) : record.parts.map Part.tags = Logon.tags := rfl

def Logon.decode (tokens : List Token) : Option Logon := do
  let encryptMethod ← readRequired [57, 56] tokens
  let heartBtInt ← readRequired [49, 48, 56] tokens
  let rawDataLength ← readOptional [57, 53] tokens
  let rawData ← readOptional [57, 54] tokens
  let resetSeqNumFlag ← readOptional [49, 52, 49] tokens
  let username ← readRequired [53, 53, 51] tokens
  let password ← readRequired [53, 53, 52] tokens
  let text ← readOptional [53, 56] tokens
  let nextExpectedMsgSeqNum ← readRequired [55, 56, 57] tokens
  let sessionStatus ← readOptional [49, 52, 48, 57] tokens
  pure { encryptMethod, heartBtInt, rawDataLength, rawData, resetSeqNumFlag, username, password, text, nextExpectedMsgSeqNum, sessionStatus }

theorem Logon.decode_agrees (record : Logon) (tokens : List Token)
    (agrees : ∀ tags ∈ Logon.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Logon.decode tokens = some record := by
  have distinct : Logon.tags.flatten.Nodup := by decide +kernel
  have encryptMethod := readRequired_part [57, 56] record.encryptMethod tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have heartBtInt := readRequired_part [49, 48, 56] record.heartBtInt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have rawDataLength := readOptional_part [57, 53] record.rawDataLength tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have rawData := readOptional_part [57, 54] record.rawData tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have resetSeqNumFlag := readOptional_part [49, 52, 49] record.resetSeqNumFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have username := readRequired_part [53, 53, 51] record.username tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have password := readRequired_part [53, 53, 52] record.password tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have nextExpectedMsgSeqNum := readRequired_part [55, 56, 57] record.nextExpectedMsgSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have sessionStatus := readOptional_part [49, 52, 48, 57] record.sessionStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  simp only [Logon.decode, encryptMethod, heartBtInt, rawDataLength, rawData, resetSeqNumFlag, username, password, text, nextExpectedMsgSeqNum, sessionStatus, some_bind] <;> rfl

theorem Logon.taken (record : Logon) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [57, 56] record.encryptMethod (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 48, 56] record.heartBtInt (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [57, 53] record.rawDataLength (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [57, 54] record.rawData (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [49, 52, 49] record.resetSeqNumFlag (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [53, 53, 51] record.username (by decide) (by decide))
        (paired_cons pairing _ _ (paired_required pairing [53, 53, 52] record.password (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
          (paired_cons pairing _ _ (paired_required pairing [55, 56, 57] record.nextExpectedMsgSeqNum (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [49, 52, 48, 57] record.sessionStatus (by decide) (by decide))
            (paired_none pairing))))))))))

structure Logout where
  sessionStatus : Option (Terminated 1)  -- tag 1409
  text : Option (Terminated 1)  -- tag 58
  nextExpectedMsgSeqNum : Terminated 1  -- tag 789

def Logout.parts (record : Logout) : List Part :=
  [Part.optional [49, 52, 48, 57] record.sessionStatus,
   Part.optional [53, 56] record.text,
   Part.required [55, 56, 57] record.nextExpectedMsgSeqNum]

def Logout.tags : List (List (List UInt8)) :=
  [[[49, 52, 48, 57]], [[53, 56]], [[55, 56, 57]]]

theorem Logout.shape (record : Logout) : record.parts.map Part.tags = Logout.tags := rfl

def Logout.decode (tokens : List Token) : Option Logout := do
  let sessionStatus ← readOptional [49, 52, 48, 57] tokens
  let text ← readOptional [53, 56] tokens
  let nextExpectedMsgSeqNum ← readRequired [55, 56, 57] tokens
  pure { sessionStatus, text, nextExpectedMsgSeqNum }

theorem Logout.decode_agrees (record : Logout) (tokens : List Token)
    (agrees : ∀ tags ∈ Logout.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Logout.decode tokens = some record := by
  have distinct : Logout.tags.flatten.Nodup := by decide +kernel
  have sessionStatus := readOptional_part [49, 52, 48, 57] record.sessionStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have nextExpectedMsgSeqNum := readRequired_part [55, 56, 57] record.nextExpectedMsgSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [Logout.decode, sessionStatus, text, nextExpectedMsgSeqNum, some_bind] <;> rfl

theorem Logout.taken (record : Logout) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49, 52, 48, 57] record.sessionStatus (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [55, 56, 57] record.nextExpectedMsgSeqNum (by decide) (by decide))
     (paired_none pairing)))

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

structure SequenceReset where
  gapFillFlag : Terminated 1  -- tag 123
  newSeqNo : Terminated 1  -- tag 36

def SequenceReset.parts (record : SequenceReset) : List Part :=
  [Part.required [49, 50, 51] record.gapFillFlag,
   Part.required [51, 54] record.newSeqNo]

def SequenceReset.tags : List (List (List UInt8)) :=
  [[[49, 50, 51]], [[51, 54]]]

theorem SequenceReset.shape (record : SequenceReset) : record.parts.map Part.tags = SequenceReset.tags := rfl

def SequenceReset.decode (tokens : List Token) : Option SequenceReset := do
  let gapFillFlag ← readRequired [49, 50, 51] tokens
  let newSeqNo ← readRequired [51, 54] tokens
  pure { gapFillFlag, newSeqNo }

theorem SequenceReset.decode_agrees (record : SequenceReset) (tokens : List Token)
    (agrees : ∀ tags ∈ SequenceReset.tags, select tags tokens = select tags (encodeParts record.parts)) :
    SequenceReset.decode tokens = some record := by
  have distinct : SequenceReset.tags.flatten.Nodup := by decide +kernel
  have gapFillFlag := readRequired_part [49, 50, 51] record.gapFillFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have newSeqNo := readRequired_part [51, 54] record.newSeqNo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [SequenceReset.decode, gapFillFlag, newSeqNo, some_bind] <;> rfl

theorem SequenceReset.taken (record : SequenceReset) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 50, 51] record.gapFillFlag (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [51, 54] record.newSeqNo (by decide) (by decide))
    (paired_none pairing))

structure Reject where
  refSeqNum : Terminated 1  -- tag 45
  sessionRejectReason : Option (Terminated 1)  -- tag 373
  refTagId : Option (Terminated 1)  -- tag 371
  refMsgType : Option (Terminated 1)  -- tag 372
  text : Option (Terminated 1)  -- tag 58
  nextExpectedMsgSeqNum : Terminated 1  -- tag 789

def Reject.parts (record : Reject) : List Part :=
  [Part.required [52, 53] record.refSeqNum,
   Part.optional [51, 55, 51] record.sessionRejectReason,
   Part.optional [51, 55, 49] record.refTagId,
   Part.optional [51, 55, 50] record.refMsgType,
   Part.optional [53, 56] record.text,
   Part.required [55, 56, 57] record.nextExpectedMsgSeqNum]

def Reject.tags : List (List (List UInt8)) :=
  [[[52, 53]], [[51, 55, 51]], [[51, 55, 49]], [[51, 55, 50]], [[53, 56]], [[55, 56, 57]]]

theorem Reject.shape (record : Reject) : record.parts.map Part.tags = Reject.tags := rfl

def Reject.decode (tokens : List Token) : Option Reject := do
  let refSeqNum ← readRequired [52, 53] tokens
  let sessionRejectReason ← readOptional [51, 55, 51] tokens
  let refTagId ← readOptional [51, 55, 49] tokens
  let refMsgType ← readOptional [51, 55, 50] tokens
  let text ← readOptional [53, 56] tokens
  let nextExpectedMsgSeqNum ← readRequired [55, 56, 57] tokens
  pure { refSeqNum, sessionRejectReason, refTagId, refMsgType, text, nextExpectedMsgSeqNum }

theorem Reject.decode_agrees (record : Reject) (tokens : List Token)
    (agrees : ∀ tags ∈ Reject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Reject.decode tokens = some record := by
  have distinct : Reject.tags.flatten.Nodup := by decide +kernel
  have refSeqNum := readRequired_part [52, 53] record.refSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have sessionRejectReason := readOptional_part [51, 55, 51] record.sessionRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have refTagId := readOptional_part [51, 55, 49] record.refTagId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have refMsgType := readOptional_part [51, 55, 50] record.refMsgType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have nextExpectedMsgSeqNum := readRequired_part [55, 56, 57] record.nextExpectedMsgSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  simp only [Reject.decode, refSeqNum, sessionRejectReason, refTagId, refMsgType, text, nextExpectedMsgSeqNum, some_bind] <;> rfl

theorem Reject.taken (record : Reject) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [52, 53] record.refSeqNum (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [51, 55, 51] record.sessionRejectReason (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [51, 55, 49] record.refTagId (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [51, 55, 50] record.refMsgType (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [55, 56, 57] record.nextExpectedMsgSeqNum (by decide) (by decide))
        (paired_none pairing))))))

structure NoTradingSessions where
  tradingSessionID : Terminated 1  -- tag 336

def NoTradingSessions.parts (record : NoTradingSessions) : List Part :=
  [Part.required [51, 51, 54] record.tradingSessionID]

def NoTradingSessions.tags : List (List (List UInt8)) :=
  [[[51, 51, 54]]]

theorem NoTradingSessions.shape (record : NoTradingSessions) : record.parts.map Part.tags = NoTradingSessions.tags := rfl

def NoTradingSessions.decode (tokens : List Token) : Option NoTradingSessions := do
  let tradingSessionID ← readRequired [51, 51, 54] tokens
  pure { tradingSessionID }

theorem NoTradingSessions.decode_agrees (record : NoTradingSessions) (tokens : List Token)
    (agrees : ∀ tags ∈ NoTradingSessions.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoTradingSessions.decode tokens = some record := by
  have distinct : NoTradingSessions.tags.flatten.Nodup := by decide +kernel
  have tradingSessionID := readRequired_part [51, 51, 54] record.tradingSessionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [NoTradingSessions.decode, tradingSessionID, some_bind] <;> rfl

theorem NoTradingSessions.taken (record : NoTradingSessions) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 51, 54] record.tradingSessionID (by decide) (by decide))
   (paired_none pairing)

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

structure NewOrderSingle where
  account : Option (Terminated 1)  -- tag 1
  clOrdID : Terminated 1  -- tag 11
  execInst : Option (Terminated 1)  -- tag 18
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  side : Terminated 1  -- tag 54
  symbol : Terminated 1  -- tag 55
  timeInForce : Terminated 1  -- tag 59
  transactTime : Option (Terminated 1)  -- tag 60
  openClose : Terminated 1  -- tag 77
  stopPx : Option (Terminated 1)  -- tag 99
  maxFloor : Option (Terminated 1)  -- tag 111
  securityType : Terminated 1  -- tag 167
  maturityMonthYear : Terminated 1  -- tag 200
  putOrCall : Terminated 1  -- tag 201
  strikePrice : Terminated 1  -- tag 202
  customerOrFirm : Terminated 1  -- tag 204
  maturityDay : Terminated 1  -- tag 205
  noTradingSessions : List NoTradingSessions  -- tag 386
  clearingFirm : Option (Terminated 1)  -- tag 439
  clearingAccount : Option (Terminated 1)  -- tag 440
  optionalData : Option (Terminated 1)  -- tag 526
  selfTradeType : Option (Terminated 1)  -- tag 7928
  routingInst : Option (Terminated 1)  -- tag 9303
  extendedExecInst : Option (Terminated 1)  -- tag 9416
  introducingBadgeID : Option (Terminated 1)  -- tag 9448
  billTo : Option (Terminated 1)  -- tag 9449
  attributedQuote : Option (Terminated 1)  -- tag 20001
  proactiveIfLocked : Option (Terminated 1)  -- tag 20002
  cancelInsteadOfReprice : Option (Terminated 1)  -- tag 20003
  subIDIndicator : Option (Terminated 1)  -- tag 20013
  auctionID : Option (Terminated 1)  -- tag 20041

def NewOrderSingle.parts (record : NewOrderSingle) : List Part :=
  [Part.optional [49] record.account,
   Part.required [49, 49] record.clOrdID,
   Part.optional [49, 56] record.execInst,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.required [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.required [53, 57] record.timeInForce,
   Part.optional [54, 48] record.transactTime,
   Part.required [55, 55] record.openClose,
   Part.optional [57, 57] record.stopPx,
   Part.optional [49, 49, 49] record.maxFloor,
   Part.required [49, 54, 55] record.securityType,
   Part.required [50, 48, 48] record.maturityMonthYear,
   Part.required [50, 48, 49] record.putOrCall,
   Part.required [50, 48, 50] record.strikePrice,
   Part.required [50, 48, 52] record.customerOrFirm,
   Part.required [50, 48, 53] record.maturityDay,
   Part.group [51, 56, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within record.noTradingSessions,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.optional [53, 50, 54] record.optionalData,
   Part.optional [55, 57, 50, 56] record.selfTradeType,
   Part.optional [57, 51, 48, 51] record.routingInst,
   Part.optional [57, 52, 49, 54] record.extendedExecInst,
   Part.optional [57, 52, 52, 56] record.introducingBadgeID,
   Part.optional [57, 52, 52, 57] record.billTo,
   Part.optional [50, 48, 48, 48, 49] record.attributedQuote,
   Part.optional [50, 48, 48, 48, 50] record.proactiveIfLocked,
   Part.optional [50, 48, 48, 48, 51] record.cancelInsteadOfReprice,
   Part.optional [50, 48, 48, 49, 51] record.subIDIndicator,
   Part.optional [50, 48, 48, 52, 49] record.auctionID]

def NewOrderSingle.tags : List (List (List UInt8)) :=
  [[[49]], [[49, 49]], [[49, 56]], [[51, 56]], [[52, 48]], [[52, 52]], [[53, 52]], [[53, 53]], [[53, 57]], [[54, 48]], [[55, 55]], [[57, 57]], [[49, 49, 49]], [[49, 54, 55]], [[50, 48, 48]], [[50, 48, 49]], [[50, 48, 50]], [[50, 48, 52]], [[50, 48, 53]], [51, 56, 54] :: NoTradingSessions.members, [[52, 51, 57]], [[52, 52, 48]], [[53, 50, 54]], [[55, 57, 50, 56]], [[57, 51, 48, 51]], [[57, 52, 49, 54]], [[57, 52, 52, 56]], [[57, 52, 52, 57]], [[50, 48, 48, 48, 49]], [[50, 48, 48, 48, 50]], [[50, 48, 48, 48, 51]], [[50, 48, 48, 49, 51]], [[50, 48, 48, 52, 49]]]

theorem NewOrderSingle.shape (record : NewOrderSingle) : record.parts.map Part.tags = NewOrderSingle.tags := rfl

def NewOrderSingle.decode (tokens : List Token) : Option NewOrderSingle := do
  let account ← readOptional [49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let execInst ← readOptional [49, 56] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let side ← readRequired [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let timeInForce ← readRequired [53, 57] tokens
  let transactTime ← readOptional [54, 48] tokens
  let openClose ← readRequired [55, 55] tokens
  let stopPx ← readOptional [57, 57] tokens
  let maxFloor ← readOptional [49, 49, 49] tokens
  let securityType ← readRequired [49, 54, 55] tokens
  let maturityMonthYear ← readRequired [50, 48, 48] tokens
  let putOrCall ← readRequired [50, 48, 49] tokens
  let strikePrice ← readRequired [50, 48, 50] tokens
  let customerOrFirm ← readRequired [50, 48, 52] tokens
  let maturityDay ← readRequired [50, 48, 53] tokens
  let noTradingSessions ← readGroup [51, 56, 54] [51, 51, 54] NoTradingSessions.members NoTradingSessions.decode tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let optionalData ← readOptional [53, 50, 54] tokens
  let selfTradeType ← readOptional [55, 57, 50, 56] tokens
  let routingInst ← readOptional [57, 51, 48, 51] tokens
  let extendedExecInst ← readOptional [57, 52, 49, 54] tokens
  let introducingBadgeID ← readOptional [57, 52, 52, 56] tokens
  let billTo ← readOptional [57, 52, 52, 57] tokens
  let attributedQuote ← readOptional [50, 48, 48, 48, 49] tokens
  let proactiveIfLocked ← readOptional [50, 48, 48, 48, 50] tokens
  let cancelInsteadOfReprice ← readOptional [50, 48, 48, 48, 51] tokens
  let subIDIndicator ← readOptional [50, 48, 48, 49, 51] tokens
  let auctionID ← readOptional [50, 48, 48, 52, 49] tokens
  pure { account, clOrdID, execInst, orderQty, ordType, price, side, symbol, timeInForce, transactTime, openClose, stopPx, maxFloor, securityType, maturityMonthYear, putOrCall, strikePrice, customerOrFirm, maturityDay, noTradingSessions, clearingFirm, clearingAccount, optionalData, selfTradeType, routingInst, extendedExecInst, introducingBadgeID, billTo, attributedQuote, proactiveIfLocked, cancelInsteadOfReprice, subIDIndicator, auctionID }

theorem NewOrderSingle.decode_agrees (record : NewOrderSingle) (tokens : List Token)
    (agrees : ∀ tags ∈ NewOrderSingle.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NewOrderSingle.decode tokens = some record := by
  have distinct : NewOrderSingle.tags.flatten.Nodup := by decide +kernel
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have timeInForce := readRequired_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have openClose := readRequired_part [55, 55] record.openClose tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have stopPx := readOptional_part [57, 57] record.stopPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have maxFloor := readOptional_part [49, 49, 49] record.maxFloor tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have securityType := readRequired_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have maturityMonthYear := readRequired_part [50, 48, 48] record.maturityMonthYear tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have putOrCall := readRequired_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have strikePrice := readRequired_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have customerOrFirm := readRequired_part [50, 48, 52] record.customerOrFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have maturityDay := readRequired_part [50, 48, 53] record.maturityDay tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have noTradingSessions := readGroup_part [51, 56, 54] [51, 51, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within NoTradingSessions.decode NoTradingSessions.decode_encode NoTradingSessions.led record.noTradingSessions tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have optionalData := readOptional_part [53, 50, 54] record.optionalData tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have selfTradeType := readOptional_part [55, 57, 50, 56] record.selfTradeType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have routingInst := readOptional_part [57, 51, 48, 51] record.routingInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have extendedExecInst := readOptional_part [57, 52, 49, 54] record.extendedExecInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have introducingBadgeID := readOptional_part [57, 52, 52, 56] record.introducingBadgeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have billTo := readOptional_part [57, 52, 52, 57] record.billTo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have attributedQuote := readOptional_part [50, 48, 48, 48, 49] record.attributedQuote tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have proactiveIfLocked := readOptional_part [50, 48, 48, 48, 50] record.proactiveIfLocked tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have cancelInsteadOfReprice := readOptional_part [50, 48, 48, 48, 51] record.cancelInsteadOfReprice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have subIDIndicator := readOptional_part [50, 48, 48, 49, 51] record.subIDIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have auctionID := readOptional_part [50, 48, 48, 52, 49] record.auctionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  simp only [NewOrderSingle.decode, account, clOrdID, execInst, orderQty, ordType, price, side, symbol, timeInForce, transactTime, openClose, stopPx, maxFloor, securityType, maturityMonthYear, putOrCall, strikePrice, customerOrFirm, maturityDay, noTradingSessions, clearingFirm, clearingAccount, optionalData, selfTradeType, routingInst, extendedExecInst, introducingBadgeID, billTo, attributedQuote, proactiveIfLocked, cancelInsteadOfReprice, subIDIndicator, auctionID, some_bind] <;> rfl

theorem NewOrderSingle.taken (record : NewOrderSingle) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49] record.account (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [49, 56] record.execInst (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [51, 56] record.orderQty (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [52, 48] record.ordType (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [52, 52] record.price (by decide) (by decide))
        (paired_cons pairing _ _ (paired_required pairing [53, 52] record.side (by decide) (by decide))
         (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
          (paired_cons pairing _ _ (paired_required pairing [53, 57] record.timeInForce (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [54, 48] record.transactTime (by decide) (by decide))
            (paired_cons pairing _ _ (paired_required pairing [55, 55] record.openClose (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [57, 57] record.stopPx (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [49, 49, 49] record.maxFloor (by decide) (by decide))
               (paired_cons pairing _ _ (paired_required pairing [49, 54, 55] record.securityType (by decide) (by decide))
                (paired_cons pairing _ _ (paired_required pairing [50, 48, 48] record.maturityMonthYear (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_required pairing [50, 48, 49] record.putOrCall (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_required pairing [50, 48, 50] record.strikePrice (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_required pairing [50, 48, 52] record.customerOrFirm (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_required pairing [50, 48, 53] record.maturityDay (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_group pairing [51, 56, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within (by decide) (by decide) NoTradingSessions.taken record.noTradingSessions)
                      (paired_cons pairing _ _ (paired_optional pairing [52, 51, 57] record.clearingFirm (by decide) (by decide))
                       (paired_cons pairing _ _ (paired_optional pairing [52, 52, 48] record.clearingAccount (by decide) (by decide))
                        (paired_cons pairing _ _ (paired_optional pairing [53, 50, 54] record.optionalData (by decide) (by decide))
                         (paired_cons pairing _ _ (paired_optional pairing [55, 57, 50, 56] record.selfTradeType (by decide) (by decide))
                          (paired_cons pairing _ _ (paired_optional pairing [57, 51, 48, 51] record.routingInst (by decide) (by decide))
                           (paired_cons pairing _ _ (paired_optional pairing [57, 52, 49, 54] record.extendedExecInst (by decide) (by decide))
                            (paired_cons pairing _ _ (paired_optional pairing [57, 52, 52, 56] record.introducingBadgeID (by decide) (by decide))
                             (paired_cons pairing _ _ (paired_optional pairing [57, 52, 52, 57] record.billTo (by decide) (by decide))
                              (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 48, 49] record.attributedQuote (by decide) (by decide))
                               (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 48, 50] record.proactiveIfLocked (by decide) (by decide))
                                (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 48, 51] record.cancelInsteadOfReprice (by decide) (by decide))
                                 (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 49, 51] record.subIDIndicator (by decide) (by decide))
                                  (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 52, 49] record.auctionID (by decide) (by decide))
                                   (paired_none pairing)))))))))))))))))))))))))))))))))

structure NoSides where
  side : Terminated 1  -- tag 54
  account : Option (Terminated 1)  -- tag 1
  clOrdID : Terminated 1  -- tag 11
  ordType : Terminated 1  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  openClose : Terminated 1  -- tag 77
  coveredOrUncovered : Terminated 1  -- tag 203
  customerOrFirm : Terminated 1  -- tag 204
  clearingFirm : Option (Terminated 1)  -- tag 439
  clearingAccount : Option (Terminated 1)  -- tag 440
  optionalData : Option (Terminated 1)  -- tag 526
  billTo : Option (Terminated 1)  -- tag 9449
  giveUpMarketMaker : Option (Terminated 1)  -- tag 20014
  allocationPct : Option (Terminated 1)  -- tag 20015

def NoSides.parts (record : NoSides) : List Part :=
  [Part.required [53, 52] record.side,
   Part.optional [49] record.account,
   Part.required [49, 49] record.clOrdID,
   Part.required [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.required [55, 55] record.openClose,
   Part.required [50, 48, 51] record.coveredOrUncovered,
   Part.required [50, 48, 52] record.customerOrFirm,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.optional [53, 50, 54] record.optionalData,
   Part.optional [57, 52, 52, 57] record.billTo,
   Part.optional [50, 48, 48, 49, 52] record.giveUpMarketMaker,
   Part.optional [50, 48, 48, 49, 53] record.allocationPct]

def NoSides.tags : List (List (List UInt8)) :=
  [[[53, 52]], [[49]], [[49, 49]], [[52, 48]], [[52, 52]], [[55, 55]], [[50, 48, 51]], [[50, 48, 52]], [[52, 51, 57]], [[52, 52, 48]], [[53, 50, 54]], [[57, 52, 52, 57]], [[50, 48, 48, 49, 52]], [[50, 48, 48, 49, 53]]]

theorem NoSides.shape (record : NoSides) : record.parts.map Part.tags = NoSides.tags := rfl

def NoSides.decode (tokens : List Token) : Option NoSides := do
  let side ← readRequired [53, 52] tokens
  let account ← readOptional [49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let openClose ← readRequired [55, 55] tokens
  let coveredOrUncovered ← readRequired [50, 48, 51] tokens
  let customerOrFirm ← readRequired [50, 48, 52] tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let optionalData ← readOptional [53, 50, 54] tokens
  let billTo ← readOptional [57, 52, 52, 57] tokens
  let giveUpMarketMaker ← readOptional [50, 48, 48, 49, 52] tokens
  let allocationPct ← readOptional [50, 48, 48, 49, 53] tokens
  pure { side, account, clOrdID, ordType, price, openClose, coveredOrUncovered, customerOrFirm, clearingFirm, clearingAccount, optionalData, billTo, giveUpMarketMaker, allocationPct }

theorem NoSides.decode_agrees (record : NoSides) (tokens : List Token)
    (agrees : ∀ tags ∈ NoSides.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoSides.decode tokens = some record := by
  have distinct : NoSides.tags.flatten.Nodup := by decide +kernel
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have openClose := readRequired_part [55, 55] record.openClose tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have coveredOrUncovered := readRequired_part [50, 48, 51] record.coveredOrUncovered tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have customerOrFirm := readRequired_part [50, 48, 52] record.customerOrFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have optionalData := readOptional_part [53, 50, 54] record.optionalData tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have billTo := readOptional_part [57, 52, 52, 57] record.billTo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have giveUpMarketMaker := readOptional_part [50, 48, 48, 49, 52] record.giveUpMarketMaker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have allocationPct := readOptional_part [50, 48, 48, 49, 53] record.allocationPct tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  simp only [NoSides.decode, side, account, clOrdID, ordType, price, openClose, coveredOrUncovered, customerOrFirm, clearingFirm, clearingAccount, optionalData, billTo, giveUpMarketMaker, allocationPct, some_bind] <;> rfl

theorem NoSides.taken (record : NoSides) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [53, 52] record.side (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [49] record.account (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [52, 48] record.ordType (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [52, 52] record.price (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [55, 55] record.openClose (by decide) (by decide))
        (paired_cons pairing _ _ (paired_required pairing [50, 48, 51] record.coveredOrUncovered (by decide) (by decide))
         (paired_cons pairing _ _ (paired_required pairing [50, 48, 52] record.customerOrFirm (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [52, 51, 57] record.clearingFirm (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [52, 52, 48] record.clearingAccount (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [53, 50, 54] record.optionalData (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [57, 52, 52, 57] record.billTo (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 49, 52] record.giveUpMarketMaker (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 49, 53] record.allocationPct (by decide) (by decide))
                (paired_none pairing))))))))))))))

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

structure NewOrderCross where
  orderQty : Terminated 1  -- tag 38
  symbol : Terminated 1  -- tag 55
  timeInForce : Terminated 1  -- tag 59
  transactTime : Option (Terminated 1)  -- tag 60
  securityType : Terminated 1  -- tag 167
  maturityMonthYear : Terminated 1  -- tag 200
  putOrCall : Terminated 1  -- tag 201
  strikePrice : Terminated 1  -- tag 202
  maturityDay : Terminated 1  -- tag 205
  noTradingSessions : List NoTradingSessions  -- tag 386
  crossID : Terminated 1  -- tag 548
  specialOrdType : Terminated 1  -- tag 9202
  introducingBadgeID : Option (Terminated 1)  -- tag 9448
  noSides : List NoSides  -- tag 552

def NewOrderCross.parts (record : NewOrderCross) : List Part :=
  [Part.required [51, 56] record.orderQty,
   Part.required [53, 53] record.symbol,
   Part.required [53, 57] record.timeInForce,
   Part.optional [54, 48] record.transactTime,
   Part.required [49, 54, 55] record.securityType,
   Part.required [50, 48, 48] record.maturityMonthYear,
   Part.required [50, 48, 49] record.putOrCall,
   Part.required [50, 48, 50] record.strikePrice,
   Part.required [50, 48, 53] record.maturityDay,
   Part.group [51, 56, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within record.noTradingSessions,
   Part.required [53, 52, 56] record.crossID,
   Part.required [57, 50, 48, 50] record.specialOrdType,
   Part.optional [57, 52, 52, 56] record.introducingBadgeID,
   Part.group [53, 53, 50] NoSides.members NoSides.encode NoSides.within record.noSides]

def NewOrderCross.tags : List (List (List UInt8)) :=
  [[[51, 56]], [[53, 53]], [[53, 57]], [[54, 48]], [[49, 54, 55]], [[50, 48, 48]], [[50, 48, 49]], [[50, 48, 50]], [[50, 48, 53]], [51, 56, 54] :: NoTradingSessions.members, [[53, 52, 56]], [[57, 50, 48, 50]], [[57, 52, 52, 56]], [53, 53, 50] :: NoSides.members]

theorem NewOrderCross.shape (record : NewOrderCross) : record.parts.map Part.tags = NewOrderCross.tags := rfl

def NewOrderCross.decode (tokens : List Token) : Option NewOrderCross := do
  let orderQty ← readRequired [51, 56] tokens
  let symbol ← readRequired [53, 53] tokens
  let timeInForce ← readRequired [53, 57] tokens
  let transactTime ← readOptional [54, 48] tokens
  let securityType ← readRequired [49, 54, 55] tokens
  let maturityMonthYear ← readRequired [50, 48, 48] tokens
  let putOrCall ← readRequired [50, 48, 49] tokens
  let strikePrice ← readRequired [50, 48, 50] tokens
  let maturityDay ← readRequired [50, 48, 53] tokens
  let noTradingSessions ← readGroup [51, 56, 54] [51, 51, 54] NoTradingSessions.members NoTradingSessions.decode tokens
  let crossID ← readRequired [53, 52, 56] tokens
  let specialOrdType ← readRequired [57, 50, 48, 50] tokens
  let introducingBadgeID ← readOptional [57, 52, 52, 56] tokens
  let noSides ← readGroup [53, 53, 50] [53, 52] NoSides.members NoSides.decode tokens
  pure { orderQty, symbol, timeInForce, transactTime, securityType, maturityMonthYear, putOrCall, strikePrice, maturityDay, noTradingSessions, crossID, specialOrdType, introducingBadgeID, noSides }

theorem NewOrderCross.decode_agrees (record : NewOrderCross) (tokens : List Token)
    (agrees : ∀ tags ∈ NewOrderCross.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NewOrderCross.decode tokens = some record := by
  have distinct : NewOrderCross.tags.flatten.Nodup := by decide +kernel
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have timeInForce := readRequired_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have securityType := readRequired_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have maturityMonthYear := readRequired_part [50, 48, 48] record.maturityMonthYear tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have putOrCall := readRequired_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have strikePrice := readRequired_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have maturityDay := readRequired_part [50, 48, 53] record.maturityDay tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have noTradingSessions := readGroup_part [51, 56, 54] [51, 51, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within NoTradingSessions.decode NoTradingSessions.decode_encode NoTradingSessions.led record.noTradingSessions tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have crossID := readRequired_part [53, 52, 56] record.crossID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have specialOrdType := readRequired_part [57, 50, 48, 50] record.specialOrdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have introducingBadgeID := readOptional_part [57, 52, 52, 56] record.introducingBadgeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have noSides := readGroup_part [53, 53, 50] [53, 52] NoSides.members NoSides.encode NoSides.within NoSides.decode NoSides.decode_encode NoSides.led record.noSides tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  simp only [NewOrderCross.decode, orderQty, symbol, timeInForce, transactTime, securityType, maturityMonthYear, putOrCall, strikePrice, maturityDay, noTradingSessions, crossID, specialOrdType, introducingBadgeID, noSides, some_bind] <;> rfl

theorem NewOrderCross.taken (record : NewOrderCross) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 56] record.orderQty (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [53, 57] record.timeInForce (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [54, 48] record.transactTime (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [49, 54, 55] record.securityType (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [50, 48, 48] record.maturityMonthYear (by decide) (by decide))
        (paired_cons pairing _ _ (paired_required pairing [50, 48, 49] record.putOrCall (by decide) (by decide))
         (paired_cons pairing _ _ (paired_required pairing [50, 48, 50] record.strikePrice (by decide) (by decide))
          (paired_cons pairing _ _ (paired_required pairing [50, 48, 53] record.maturityDay (by decide) (by decide))
           (paired_cons pairing _ _ (paired_group pairing [51, 56, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within (by decide) (by decide) NoTradingSessions.taken record.noTradingSessions)
            (paired_cons pairing _ _ (paired_required pairing [53, 52, 56] record.crossID (by decide) (by decide))
             (paired_cons pairing _ _ (paired_required pairing [57, 50, 48, 50] record.specialOrdType (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [57, 52, 52, 56] record.introducingBadgeID (by decide) (by decide))
               (paired_cons pairing _ _ (paired_group pairing [53, 53, 50] NoSides.members NoSides.encode NoSides.within (by decide) (by decide) NoSides.taken record.noSides)
                (paired_none pairing))))))))))))))

structure OrderCancelRequest

def OrderCancelRequest.parts (_ : OrderCancelRequest) : List Part :=
  []

def OrderCancelRequest.tags : List (List (List UInt8)) :=
  []

theorem OrderCancelRequest.shape (record : OrderCancelRequest) : record.parts.map Part.tags = OrderCancelRequest.tags := rfl

def OrderCancelRequest.decode (_ : List Token) : Option OrderCancelRequest := some {}

theorem OrderCancelRequest.decode_agrees (record : OrderCancelRequest) (tokens : List Token)
    (_ : ∀ tags ∈ OrderCancelRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelRequest.decode tokens = some record := by
  rfl

theorem OrderCancelRequest.taken (record : OrderCancelRequest) : Paired pairing (encodeParts record.parts) :=
  paired_none pairing

structure OrderCancelRequestCancelSingleLegonly where
  clOrdID : Terminated 1  -- tag 11
  orderID : Terminated 1  -- tag 37
  side : Option (Terminated 1)  -- tag 54
  symbol : Option (Terminated 1)  -- tag 55
  transactTime : Option (Terminated 1)  -- tag 60
  symbolSfx : Option (Terminated 1)  -- tag 65
  targetCancelSenderCompID : Option (Terminated 1)  -- tag 20025
  targetCancelMPID : Option (Terminated 1)  -- tag 20026

def OrderCancelRequestCancelSingleLegonly.parts (record : OrderCancelRequestCancelSingleLegonly) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.required [51, 55] record.orderID,
   Part.optional [53, 52] record.side,
   Part.optional [53, 53] record.symbol,
   Part.optional [54, 48] record.transactTime,
   Part.optional [54, 53] record.symbolSfx,
   Part.optional [50, 48, 48, 50, 53] record.targetCancelSenderCompID,
   Part.optional [50, 48, 48, 50, 54] record.targetCancelMPID]

def OrderCancelRequestCancelSingleLegonly.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[51, 55]], [[53, 52]], [[53, 53]], [[54, 48]], [[54, 53]], [[50, 48, 48, 50, 53]], [[50, 48, 48, 50, 54]]]

theorem OrderCancelRequestCancelSingleLegonly.shape (record : OrderCancelRequestCancelSingleLegonly) : record.parts.map Part.tags = OrderCancelRequestCancelSingleLegonly.tags := rfl

def OrderCancelRequestCancelSingleLegonly.decode (tokens : List Token) : Option OrderCancelRequestCancelSingleLegonly := do
  let clOrdID ← readRequired [49, 49] tokens
  let orderID ← readRequired [51, 55] tokens
  let side ← readOptional [53, 52] tokens
  let symbol ← readOptional [53, 53] tokens
  let transactTime ← readOptional [54, 48] tokens
  let symbolSfx ← readOptional [54, 53] tokens
  let targetCancelSenderCompID ← readOptional [50, 48, 48, 50, 53] tokens
  let targetCancelMPID ← readOptional [50, 48, 48, 50, 54] tokens
  pure { clOrdID, orderID, side, symbol, transactTime, symbolSfx, targetCancelSenderCompID, targetCancelMPID }

theorem OrderCancelRequestCancelSingleLegonly.decode_agrees (record : OrderCancelRequestCancelSingleLegonly) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelRequestCancelSingleLegonly.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelRequestCancelSingleLegonly.decode tokens = some record := by
  have distinct : OrderCancelRequestCancelSingleLegonly.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have symbolSfx := readOptional_part [54, 53] record.symbolSfx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have targetCancelSenderCompID := readOptional_part [50, 48, 48, 50, 53] record.targetCancelSenderCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have targetCancelMPID := readOptional_part [50, 48, 48, 50, 54] record.targetCancelMPID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  simp only [OrderCancelRequestCancelSingleLegonly.decode, clOrdID, orderID, side, symbol, transactTime, symbolSfx, targetCancelSenderCompID, targetCancelMPID, some_bind] <;> rfl

theorem OrderCancelRequestCancelSingleLegonly.taken (record : OrderCancelRequestCancelSingleLegonly) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [51, 55] record.orderID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [53, 52] record.side (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [53, 53] record.symbol (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [54, 48] record.transactTime (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [54, 53] record.symbolSfx (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 50, 53] record.targetCancelSenderCompID (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 50, 54] record.targetCancelMPID (by decide) (by decide))
          (paired_none pairing))))))))

structure OrderCancelRequestCancelComplexonly where
  clOrdID : Terminated 1  -- tag 11
  orderID : Terminated 1  -- tag 37
  side : Option (Terminated 1)  -- tag 54
  symbol : Option (Terminated 1)  -- tag 55
  transactTime : Option (Terminated 1)  -- tag 60
  symbolSfx : Option (Terminated 1)  -- tag 65
  targetCancelSenderCompID : Option (Terminated 1)  -- tag 20025
  targetCancelMPID : Option (Terminated 1)  -- tag 20026

def OrderCancelRequestCancelComplexonly.parts (record : OrderCancelRequestCancelComplexonly) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.required [51, 55] record.orderID,
   Part.optional [53, 52] record.side,
   Part.optional [53, 53] record.symbol,
   Part.optional [54, 48] record.transactTime,
   Part.optional [54, 53] record.symbolSfx,
   Part.optional [50, 48, 48, 50, 53] record.targetCancelSenderCompID,
   Part.optional [50, 48, 48, 50, 54] record.targetCancelMPID]

def OrderCancelRequestCancelComplexonly.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[51, 55]], [[53, 52]], [[53, 53]], [[54, 48]], [[54, 53]], [[50, 48, 48, 50, 53]], [[50, 48, 48, 50, 54]]]

theorem OrderCancelRequestCancelComplexonly.shape (record : OrderCancelRequestCancelComplexonly) : record.parts.map Part.tags = OrderCancelRequestCancelComplexonly.tags := rfl

def OrderCancelRequestCancelComplexonly.decode (tokens : List Token) : Option OrderCancelRequestCancelComplexonly := do
  let clOrdID ← readRequired [49, 49] tokens
  let orderID ← readRequired [51, 55] tokens
  let side ← readOptional [53, 52] tokens
  let symbol ← readOptional [53, 53] tokens
  let transactTime ← readOptional [54, 48] tokens
  let symbolSfx ← readOptional [54, 53] tokens
  let targetCancelSenderCompID ← readOptional [50, 48, 48, 50, 53] tokens
  let targetCancelMPID ← readOptional [50, 48, 48, 50, 54] tokens
  pure { clOrdID, orderID, side, symbol, transactTime, symbolSfx, targetCancelSenderCompID, targetCancelMPID }

theorem OrderCancelRequestCancelComplexonly.decode_agrees (record : OrderCancelRequestCancelComplexonly) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelRequestCancelComplexonly.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelRequestCancelComplexonly.decode tokens = some record := by
  have distinct : OrderCancelRequestCancelComplexonly.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have symbolSfx := readOptional_part [54, 53] record.symbolSfx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have targetCancelSenderCompID := readOptional_part [50, 48, 48, 50, 53] record.targetCancelSenderCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have targetCancelMPID := readOptional_part [50, 48, 48, 50, 54] record.targetCancelMPID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  simp only [OrderCancelRequestCancelComplexonly.decode, clOrdID, orderID, side, symbol, transactTime, symbolSfx, targetCancelSenderCompID, targetCancelMPID, some_bind] <;> rfl

theorem OrderCancelRequestCancelComplexonly.taken (record : OrderCancelRequestCancelComplexonly) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [51, 55] record.orderID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [53, 52] record.side (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [53, 53] record.symbol (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [54, 48] record.transactTime (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [54, 53] record.symbolSfx (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 50, 53] record.targetCancelSenderCompID (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 50, 54] record.targetCancelMPID (by decide) (by decide))
          (paired_none pairing))))))))

structure OrderCancelRequestCancelbothSingleLegandComplex where
  clOrdID : Terminated 1  -- tag 11
  orderID : Terminated 1  -- tag 37
  side : Option (Terminated 1)  -- tag 54
  symbol : Option (Terminated 1)  -- tag 55
  transactTime : Option (Terminated 1)  -- tag 60
  symbolSfx : Option (Terminated 1)  -- tag 65
  targetCancelSenderCompID : Option (Terminated 1)  -- tag 20025
  targetCancelMPID : Option (Terminated 1)  -- tag 20026

def OrderCancelRequestCancelbothSingleLegandComplex.parts (record : OrderCancelRequestCancelbothSingleLegandComplex) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.required [51, 55] record.orderID,
   Part.optional [53, 52] record.side,
   Part.optional [53, 53] record.symbol,
   Part.optional [54, 48] record.transactTime,
   Part.optional [54, 53] record.symbolSfx,
   Part.optional [50, 48, 48, 50, 53] record.targetCancelSenderCompID,
   Part.optional [50, 48, 48, 50, 54] record.targetCancelMPID]

def OrderCancelRequestCancelbothSingleLegandComplex.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[51, 55]], [[53, 52]], [[53, 53]], [[54, 48]], [[54, 53]], [[50, 48, 48, 50, 53]], [[50, 48, 48, 50, 54]]]

theorem OrderCancelRequestCancelbothSingleLegandComplex.shape (record : OrderCancelRequestCancelbothSingleLegandComplex) : record.parts.map Part.tags = OrderCancelRequestCancelbothSingleLegandComplex.tags := rfl

def OrderCancelRequestCancelbothSingleLegandComplex.decode (tokens : List Token) : Option OrderCancelRequestCancelbothSingleLegandComplex := do
  let clOrdID ← readRequired [49, 49] tokens
  let orderID ← readRequired [51, 55] tokens
  let side ← readOptional [53, 52] tokens
  let symbol ← readOptional [53, 53] tokens
  let transactTime ← readOptional [54, 48] tokens
  let symbolSfx ← readOptional [54, 53] tokens
  let targetCancelSenderCompID ← readOptional [50, 48, 48, 50, 53] tokens
  let targetCancelMPID ← readOptional [50, 48, 48, 50, 54] tokens
  pure { clOrdID, orderID, side, symbol, transactTime, symbolSfx, targetCancelSenderCompID, targetCancelMPID }

theorem OrderCancelRequestCancelbothSingleLegandComplex.decode_agrees (record : OrderCancelRequestCancelbothSingleLegandComplex) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelRequestCancelbothSingleLegandComplex.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelRequestCancelbothSingleLegandComplex.decode tokens = some record := by
  have distinct : OrderCancelRequestCancelbothSingleLegandComplex.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have symbolSfx := readOptional_part [54, 53] record.symbolSfx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have targetCancelSenderCompID := readOptional_part [50, 48, 48, 50, 53] record.targetCancelSenderCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have targetCancelMPID := readOptional_part [50, 48, 48, 50, 54] record.targetCancelMPID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  simp only [OrderCancelRequestCancelbothSingleLegandComplex.decode, clOrdID, orderID, side, symbol, transactTime, symbolSfx, targetCancelSenderCompID, targetCancelMPID, some_bind] <;> rfl

theorem OrderCancelRequestCancelbothSingleLegandComplex.taken (record : OrderCancelRequestCancelbothSingleLegandComplex) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [51, 55] record.orderID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [53, 52] record.side (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [53, 53] record.symbol (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [54, 48] record.transactTime (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [54, 53] record.symbolSfx (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 50, 53] record.targetCancelSenderCompID (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 50, 54] record.targetCancelMPID (by decide) (by decide))
          (paired_none pairing))))))))

structure OrderCancelRequestOrderCancelRequest where
  clOrdID : Terminated 1  -- tag 11
  origClOrdID : Terminated 1  -- tag 41
  side : Option (Terminated 1)  -- tag 54
  symbol : Option (Terminated 1)  -- tag 55
  transactTime : Option (Terminated 1)  -- tag 60

def OrderCancelRequestOrderCancelRequest.parts (record : OrderCancelRequestOrderCancelRequest) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.required [52, 49] record.origClOrdID,
   Part.optional [53, 52] record.side,
   Part.optional [53, 53] record.symbol,
   Part.optional [54, 48] record.transactTime]

def OrderCancelRequestOrderCancelRequest.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[52, 49]], [[53, 52]], [[53, 53]], [[54, 48]]]

theorem OrderCancelRequestOrderCancelRequest.shape (record : OrderCancelRequestOrderCancelRequest) : record.parts.map Part.tags = OrderCancelRequestOrderCancelRequest.tags := rfl

def OrderCancelRequestOrderCancelRequest.decode (tokens : List Token) : Option OrderCancelRequestOrderCancelRequest := do
  let clOrdID ← readRequired [49, 49] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let side ← readOptional [53, 52] tokens
  let symbol ← readOptional [53, 53] tokens
  let transactTime ← readOptional [54, 48] tokens
  pure { clOrdID, origClOrdID, side, symbol, transactTime }

theorem OrderCancelRequestOrderCancelRequest.decode_agrees (record : OrderCancelRequestOrderCancelRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelRequestOrderCancelRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelRequestOrderCancelRequest.decode tokens = some record := by
  have distinct : OrderCancelRequestOrderCancelRequest.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [OrderCancelRequestOrderCancelRequest.decode, clOrdID, origClOrdID, side, symbol, transactTime, some_bind] <;> rfl

theorem OrderCancelRequestOrderCancelRequest.taken (record : OrderCancelRequestOrderCancelRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [52, 49] record.origClOrdID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [53, 52] record.side (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [53, 53] record.symbol (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [54, 48] record.transactTime (by decide) (by decide))
       (paired_none pairing)))))

structure OrderCancelReplaceRequest where
  account : Option (Terminated 1)  -- tag 1
  clOrdID : Terminated 1  -- tag 11
  execInst : Option (Terminated 1)  -- tag 18
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  origClOrdID : Terminated 1  -- tag 41
  price : Option (Terminated 1)  -- tag 44
  side : Terminated 1  -- tag 54
  symbol : Terminated 1  -- tag 55
  timeInForce : Terminated 1  -- tag 59
  transactTime : Option (Terminated 1)  -- tag 60
  openClose : Option (Terminated 1)  -- tag 77
  stopPx : Option (Terminated 1)  -- tag 99
  maxFloor : Option (Terminated 1)  -- tag 111
  securityType : Terminated 1  -- tag 167
  maturityMonthYear : Terminated 1  -- tag 200
  putOrCall : Terminated 1  -- tag 201
  strikePrice : Terminated 1  -- tag 202
  customerOrFirm : Terminated 1  -- tag 204
  maturityDay : Terminated 1  -- tag 205
  noTradingSessions : List NoTradingSessions  -- tag 386
  clearingFirm : Option (Terminated 1)  -- tag 439
  clearingAccount : Option (Terminated 1)  -- tag 440
  optionalData : Option (Terminated 1)  -- tag 526
  selfTradeType : Option (Terminated 1)  -- tag 7928
  routingInst : Option (Terminated 1)  -- tag 9303
  extendedExecInst : Option (Terminated 1)  -- tag 9416
  introducingBadgeID : Option (Terminated 1)  -- tag 9448
  billTo : Option (Terminated 1)  -- tag 9449
  attributedQuote : Option (Terminated 1)  -- tag 20001
  proactiveIfLocked : Option (Terminated 1)  -- tag 20002
  cancelInsteadOfReprice : Option (Terminated 1)  -- tag 20003
  subIDIndicator : Option (Terminated 1)  -- tag 20013

def OrderCancelReplaceRequest.parts (record : OrderCancelReplaceRequest) : List Part :=
  [Part.optional [49] record.account,
   Part.required [49, 49] record.clOrdID,
   Part.optional [49, 56] record.execInst,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.required [52, 49] record.origClOrdID,
   Part.optional [52, 52] record.price,
   Part.required [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.required [53, 57] record.timeInForce,
   Part.optional [54, 48] record.transactTime,
   Part.optional [55, 55] record.openClose,
   Part.optional [57, 57] record.stopPx,
   Part.optional [49, 49, 49] record.maxFloor,
   Part.required [49, 54, 55] record.securityType,
   Part.required [50, 48, 48] record.maturityMonthYear,
   Part.required [50, 48, 49] record.putOrCall,
   Part.required [50, 48, 50] record.strikePrice,
   Part.required [50, 48, 52] record.customerOrFirm,
   Part.required [50, 48, 53] record.maturityDay,
   Part.group [51, 56, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within record.noTradingSessions,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.optional [53, 50, 54] record.optionalData,
   Part.optional [55, 57, 50, 56] record.selfTradeType,
   Part.optional [57, 51, 48, 51] record.routingInst,
   Part.optional [57, 52, 49, 54] record.extendedExecInst,
   Part.optional [57, 52, 52, 56] record.introducingBadgeID,
   Part.optional [57, 52, 52, 57] record.billTo,
   Part.optional [50, 48, 48, 48, 49] record.attributedQuote,
   Part.optional [50, 48, 48, 48, 50] record.proactiveIfLocked,
   Part.optional [50, 48, 48, 48, 51] record.cancelInsteadOfReprice,
   Part.optional [50, 48, 48, 49, 51] record.subIDIndicator]

def OrderCancelReplaceRequest.tags : List (List (List UInt8)) :=
  [[[49]], [[49, 49]], [[49, 56]], [[51, 56]], [[52, 48]], [[52, 49]], [[52, 52]], [[53, 52]], [[53, 53]], [[53, 57]], [[54, 48]], [[55, 55]], [[57, 57]], [[49, 49, 49]], [[49, 54, 55]], [[50, 48, 48]], [[50, 48, 49]], [[50, 48, 50]], [[50, 48, 52]], [[50, 48, 53]], [51, 56, 54] :: NoTradingSessions.members, [[52, 51, 57]], [[52, 52, 48]], [[53, 50, 54]], [[55, 57, 50, 56]], [[57, 51, 48, 51]], [[57, 52, 49, 54]], [[57, 52, 52, 56]], [[57, 52, 52, 57]], [[50, 48, 48, 48, 49]], [[50, 48, 48, 48, 50]], [[50, 48, 48, 48, 51]], [[50, 48, 48, 49, 51]]]

theorem OrderCancelReplaceRequest.shape (record : OrderCancelReplaceRequest) : record.parts.map Part.tags = OrderCancelReplaceRequest.tags := rfl

def OrderCancelReplaceRequest.decode (tokens : List Token) : Option OrderCancelReplaceRequest := do
  let account ← readOptional [49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let execInst ← readOptional [49, 56] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let price ← readOptional [52, 52] tokens
  let side ← readRequired [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let timeInForce ← readRequired [53, 57] tokens
  let transactTime ← readOptional [54, 48] tokens
  let openClose ← readOptional [55, 55] tokens
  let stopPx ← readOptional [57, 57] tokens
  let maxFloor ← readOptional [49, 49, 49] tokens
  let securityType ← readRequired [49, 54, 55] tokens
  let maturityMonthYear ← readRequired [50, 48, 48] tokens
  let putOrCall ← readRequired [50, 48, 49] tokens
  let strikePrice ← readRequired [50, 48, 50] tokens
  let customerOrFirm ← readRequired [50, 48, 52] tokens
  let maturityDay ← readRequired [50, 48, 53] tokens
  let noTradingSessions ← readGroup [51, 56, 54] [51, 51, 54] NoTradingSessions.members NoTradingSessions.decode tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let optionalData ← readOptional [53, 50, 54] tokens
  let selfTradeType ← readOptional [55, 57, 50, 56] tokens
  let routingInst ← readOptional [57, 51, 48, 51] tokens
  let extendedExecInst ← readOptional [57, 52, 49, 54] tokens
  let introducingBadgeID ← readOptional [57, 52, 52, 56] tokens
  let billTo ← readOptional [57, 52, 52, 57] tokens
  let attributedQuote ← readOptional [50, 48, 48, 48, 49] tokens
  let proactiveIfLocked ← readOptional [50, 48, 48, 48, 50] tokens
  let cancelInsteadOfReprice ← readOptional [50, 48, 48, 48, 51] tokens
  let subIDIndicator ← readOptional [50, 48, 48, 49, 51] tokens
  pure { account, clOrdID, execInst, orderQty, ordType, origClOrdID, price, side, symbol, timeInForce, transactTime, openClose, stopPx, maxFloor, securityType, maturityMonthYear, putOrCall, strikePrice, customerOrFirm, maturityDay, noTradingSessions, clearingFirm, clearingAccount, optionalData, selfTradeType, routingInst, extendedExecInst, introducingBadgeID, billTo, attributedQuote, proactiveIfLocked, cancelInsteadOfReprice, subIDIndicator }

theorem OrderCancelReplaceRequest.decode_agrees (record : OrderCancelReplaceRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelReplaceRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelReplaceRequest.decode tokens = some record := by
  have distinct : OrderCancelReplaceRequest.tags.flatten.Nodup := by decide +kernel
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have timeInForce := readRequired_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have openClose := readOptional_part [55, 55] record.openClose tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have stopPx := readOptional_part [57, 57] record.stopPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have maxFloor := readOptional_part [49, 49, 49] record.maxFloor tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have securityType := readRequired_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have maturityMonthYear := readRequired_part [50, 48, 48] record.maturityMonthYear tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have putOrCall := readRequired_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have strikePrice := readRequired_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have customerOrFirm := readRequired_part [50, 48, 52] record.customerOrFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have maturityDay := readRequired_part [50, 48, 53] record.maturityDay tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have noTradingSessions := readGroup_part [51, 56, 54] [51, 51, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within NoTradingSessions.decode NoTradingSessions.decode_encode NoTradingSessions.led record.noTradingSessions tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have optionalData := readOptional_part [53, 50, 54] record.optionalData tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have selfTradeType := readOptional_part [55, 57, 50, 56] record.selfTradeType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have routingInst := readOptional_part [57, 51, 48, 51] record.routingInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have extendedExecInst := readOptional_part [57, 52, 49, 54] record.extendedExecInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have introducingBadgeID := readOptional_part [57, 52, 52, 56] record.introducingBadgeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have billTo := readOptional_part [57, 52, 52, 57] record.billTo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have attributedQuote := readOptional_part [50, 48, 48, 48, 49] record.attributedQuote tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have proactiveIfLocked := readOptional_part [50, 48, 48, 48, 50] record.proactiveIfLocked tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have cancelInsteadOfReprice := readOptional_part [50, 48, 48, 48, 51] record.cancelInsteadOfReprice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have subIDIndicator := readOptional_part [50, 48, 48, 49, 51] record.subIDIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  simp only [OrderCancelReplaceRequest.decode, account, clOrdID, execInst, orderQty, ordType, origClOrdID, price, side, symbol, timeInForce, transactTime, openClose, stopPx, maxFloor, securityType, maturityMonthYear, putOrCall, strikePrice, customerOrFirm, maturityDay, noTradingSessions, clearingFirm, clearingAccount, optionalData, selfTradeType, routingInst, extendedExecInst, introducingBadgeID, billTo, attributedQuote, proactiveIfLocked, cancelInsteadOfReprice, subIDIndicator, some_bind] <;> rfl

theorem OrderCancelReplaceRequest.taken (record : OrderCancelReplaceRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49] record.account (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [49, 56] record.execInst (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [51, 56] record.orderQty (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [52, 48] record.ordType (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [52, 49] record.origClOrdID (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [52, 52] record.price (by decide) (by decide))
         (paired_cons pairing _ _ (paired_required pairing [53, 52] record.side (by decide) (by decide))
          (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
           (paired_cons pairing _ _ (paired_required pairing [53, 57] record.timeInForce (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [54, 48] record.transactTime (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [55, 55] record.openClose (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [57, 57] record.stopPx (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [49, 49, 49] record.maxFloor (by decide) (by decide))
                (paired_cons pairing _ _ (paired_required pairing [49, 54, 55] record.securityType (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_required pairing [50, 48, 48] record.maturityMonthYear (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_required pairing [50, 48, 49] record.putOrCall (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_required pairing [50, 48, 50] record.strikePrice (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_required pairing [50, 48, 52] record.customerOrFirm (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_required pairing [50, 48, 53] record.maturityDay (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_group pairing [51, 56, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within (by decide) (by decide) NoTradingSessions.taken record.noTradingSessions)
                       (paired_cons pairing _ _ (paired_optional pairing [52, 51, 57] record.clearingFirm (by decide) (by decide))
                        (paired_cons pairing _ _ (paired_optional pairing [52, 52, 48] record.clearingAccount (by decide) (by decide))
                         (paired_cons pairing _ _ (paired_optional pairing [53, 50, 54] record.optionalData (by decide) (by decide))
                          (paired_cons pairing _ _ (paired_optional pairing [55, 57, 50, 56] record.selfTradeType (by decide) (by decide))
                           (paired_cons pairing _ _ (paired_optional pairing [57, 51, 48, 51] record.routingInst (by decide) (by decide))
                            (paired_cons pairing _ _ (paired_optional pairing [57, 52, 49, 54] record.extendedExecInst (by decide) (by decide))
                             (paired_cons pairing _ _ (paired_optional pairing [57, 52, 52, 56] record.introducingBadgeID (by decide) (by decide))
                              (paired_cons pairing _ _ (paired_optional pairing [57, 52, 52, 57] record.billTo (by decide) (by decide))
                               (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 48, 49] record.attributedQuote (by decide) (by decide))
                                (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 48, 50] record.proactiveIfLocked (by decide) (by decide))
                                 (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 48, 51] record.cancelInsteadOfReprice (by decide) (by decide))
                                  (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 49, 51] record.subIDIndicator (by decide) (by decide))
                                   (paired_none pairing)))))))))))))))))))))))))))))))))

structure NoLegs where
  legSymbol : Terminated 1  -- tag 600
  legPositionEffect : Terminated 1  -- tag 564
  legCFICode : Terminated 1  -- tag 608
  legMaturityDate : Terminated 1  -- tag 611
  legStrikePrice : Terminated 1  -- tag 612
  legRatioQty : Terminated 1  -- tag 623
  legSide : Terminated 1  -- tag 624
  legRefID : Terminated 1  -- tag 654

def NoLegs.parts (record : NoLegs) : List Part :=
  [Part.required [54, 48, 48] record.legSymbol,
   Part.required [53, 54, 52] record.legPositionEffect,
   Part.required [54, 48, 56] record.legCFICode,
   Part.required [54, 49, 49] record.legMaturityDate,
   Part.required [54, 49, 50] record.legStrikePrice,
   Part.required [54, 50, 51] record.legRatioQty,
   Part.required [54, 50, 52] record.legSide,
   Part.required [54, 53, 52] record.legRefID]

def NoLegs.tags : List (List (List UInt8)) :=
  [[[54, 48, 48]], [[53, 54, 52]], [[54, 48, 56]], [[54, 49, 49]], [[54, 49, 50]], [[54, 50, 51]], [[54, 50, 52]], [[54, 53, 52]]]

theorem NoLegs.shape (record : NoLegs) : record.parts.map Part.tags = NoLegs.tags := rfl

def NoLegs.decode (tokens : List Token) : Option NoLegs := do
  let legSymbol ← readRequired [54, 48, 48] tokens
  let legPositionEffect ← readRequired [53, 54, 52] tokens
  let legCFICode ← readRequired [54, 48, 56] tokens
  let legMaturityDate ← readRequired [54, 49, 49] tokens
  let legStrikePrice ← readRequired [54, 49, 50] tokens
  let legRatioQty ← readRequired [54, 50, 51] tokens
  let legSide ← readRequired [54, 50, 52] tokens
  let legRefID ← readRequired [54, 53, 52] tokens
  pure { legSymbol, legPositionEffect, legCFICode, legMaturityDate, legStrikePrice, legRatioQty, legSide, legRefID }

theorem NoLegs.decode_agrees (record : NoLegs) (tokens : List Token)
    (agrees : ∀ tags ∈ NoLegs.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoLegs.decode tokens = some record := by
  have distinct : NoLegs.tags.flatten.Nodup := by decide +kernel
  have legSymbol := readRequired_part [54, 48, 48] record.legSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have legPositionEffect := readRequired_part [53, 54, 52] record.legPositionEffect tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have legCFICode := readRequired_part [54, 48, 56] record.legCFICode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have legMaturityDate := readRequired_part [54, 49, 49] record.legMaturityDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have legStrikePrice := readRequired_part [54, 49, 50] record.legStrikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have legRatioQty := readRequired_part [54, 50, 51] record.legRatioQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have legSide := readRequired_part [54, 50, 52] record.legSide tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have legRefID := readRequired_part [54, 53, 52] record.legRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  simp only [NoLegs.decode, legSymbol, legPositionEffect, legCFICode, legMaturityDate, legStrikePrice, legRatioQty, legSide, legRefID, some_bind] <;> rfl

theorem NoLegs.taken (record : NoLegs) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [54, 48, 48] record.legSymbol (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [53, 54, 52] record.legPositionEffect (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [54, 48, 56] record.legCFICode (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [54, 49, 49] record.legMaturityDate (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [54, 49, 50] record.legStrikePrice (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [54, 50, 51] record.legRatioQty (by decide) (by decide))
        (paired_cons pairing _ _ (paired_required pairing [54, 50, 52] record.legSide (by decide) (by decide))
         (paired_cons pairing _ _ (paired_required pairing [54, 53, 52] record.legRefID (by decide) (by decide))
          (paired_none pairing))))))))

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

structure NewOrderMultileg where
  account : Option (Terminated 1)  -- tag 1
  clOrdID : Terminated 1  -- tag 11
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  price : Terminated 1  -- tag 44
  timeInForce : Terminated 1  -- tag 59
  transactTime : Option (Terminated 1)  -- tag 60
  securityType : Terminated 1  -- tag 167
  customerOrFirm : Terminated 1  -- tag 204
  noTradingSessions : List NoTradingSessions  -- tag 386
  clearingFirm : Option (Terminated 1)  -- tag 439
  clearingAccount : Option (Terminated 1)  -- tag 440
  optionalData : Option (Terminated 1)  -- tag 526
  noLegs : List NoLegs  -- tag 555
  selfTradeType : Option (Terminated 1)  -- tag 7928
  routingInst : Option (Terminated 1)  -- tag 9303
  extendedExecInst : Option (Terminated 1)  -- tag 9416
  introducingBadgeID : Option (Terminated 1)  -- tag 9448
  billTo : Option (Terminated 1)  -- tag 9449
  cancelInsteadOfReprice : Option (Terminated 1)  -- tag 20003
  subIDIndicator : Option (Terminated 1)  -- tag 20013
  auctionID : Option (Terminated 1)  -- tag 20041

def NewOrderMultileg.parts (record : NewOrderMultileg) : List Part :=
  [Part.optional [49] record.account,
   Part.required [49, 49] record.clOrdID,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.required [52, 52] record.price,
   Part.required [53, 57] record.timeInForce,
   Part.optional [54, 48] record.transactTime,
   Part.required [49, 54, 55] record.securityType,
   Part.required [50, 48, 52] record.customerOrFirm,
   Part.group [51, 56, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within record.noTradingSessions,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.optional [53, 50, 54] record.optionalData,
   Part.group [53, 53, 53] NoLegs.members NoLegs.encode NoLegs.within record.noLegs,
   Part.optional [55, 57, 50, 56] record.selfTradeType,
   Part.optional [57, 51, 48, 51] record.routingInst,
   Part.optional [57, 52, 49, 54] record.extendedExecInst,
   Part.optional [57, 52, 52, 56] record.introducingBadgeID,
   Part.optional [57, 52, 52, 57] record.billTo,
   Part.optional [50, 48, 48, 48, 51] record.cancelInsteadOfReprice,
   Part.optional [50, 48, 48, 49, 51] record.subIDIndicator,
   Part.optional [50, 48, 48, 52, 49] record.auctionID]

def NewOrderMultileg.tags : List (List (List UInt8)) :=
  [[[49]], [[49, 49]], [[51, 56]], [[52, 48]], [[52, 52]], [[53, 57]], [[54, 48]], [[49, 54, 55]], [[50, 48, 52]], [51, 56, 54] :: NoTradingSessions.members, [[52, 51, 57]], [[52, 52, 48]], [[53, 50, 54]], [53, 53, 53] :: NoLegs.members, [[55, 57, 50, 56]], [[57, 51, 48, 51]], [[57, 52, 49, 54]], [[57, 52, 52, 56]], [[57, 52, 52, 57]], [[50, 48, 48, 48, 51]], [[50, 48, 48, 49, 51]], [[50, 48, 48, 52, 49]]]

theorem NewOrderMultileg.shape (record : NewOrderMultileg) : record.parts.map Part.tags = NewOrderMultileg.tags := rfl

def NewOrderMultileg.decode (tokens : List Token) : Option NewOrderMultileg := do
  let account ← readOptional [49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readRequired [52, 52] tokens
  let timeInForce ← readRequired [53, 57] tokens
  let transactTime ← readOptional [54, 48] tokens
  let securityType ← readRequired [49, 54, 55] tokens
  let customerOrFirm ← readRequired [50, 48, 52] tokens
  let noTradingSessions ← readGroup [51, 56, 54] [51, 51, 54] NoTradingSessions.members NoTradingSessions.decode tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let optionalData ← readOptional [53, 50, 54] tokens
  let noLegs ← readGroup [53, 53, 53] [54, 48, 48] NoLegs.members NoLegs.decode tokens
  let selfTradeType ← readOptional [55, 57, 50, 56] tokens
  let routingInst ← readOptional [57, 51, 48, 51] tokens
  let extendedExecInst ← readOptional [57, 52, 49, 54] tokens
  let introducingBadgeID ← readOptional [57, 52, 52, 56] tokens
  let billTo ← readOptional [57, 52, 52, 57] tokens
  let cancelInsteadOfReprice ← readOptional [50, 48, 48, 48, 51] tokens
  let subIDIndicator ← readOptional [50, 48, 48, 49, 51] tokens
  let auctionID ← readOptional [50, 48, 48, 52, 49] tokens
  pure { account, clOrdID, orderQty, ordType, price, timeInForce, transactTime, securityType, customerOrFirm, noTradingSessions, clearingFirm, clearingAccount, optionalData, noLegs, selfTradeType, routingInst, extendedExecInst, introducingBadgeID, billTo, cancelInsteadOfReprice, subIDIndicator, auctionID }

theorem NewOrderMultileg.decode_agrees (record : NewOrderMultileg) (tokens : List Token)
    (agrees : ∀ tags ∈ NewOrderMultileg.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NewOrderMultileg.decode tokens = some record := by
  have distinct : NewOrderMultileg.tags.flatten.Nodup := by decide +kernel
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have price := readRequired_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have timeInForce := readRequired_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have securityType := readRequired_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have customerOrFirm := readRequired_part [50, 48, 52] record.customerOrFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have noTradingSessions := readGroup_part [51, 56, 54] [51, 51, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within NoTradingSessions.decode NoTradingSessions.decode_encode NoTradingSessions.led record.noTradingSessions tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have optionalData := readOptional_part [53, 50, 54] record.optionalData tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have noLegs := readGroup_part [53, 53, 53] [54, 48, 48] NoLegs.members NoLegs.encode NoLegs.within NoLegs.decode NoLegs.decode_encode NoLegs.led record.noLegs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have selfTradeType := readOptional_part [55, 57, 50, 56] record.selfTradeType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have routingInst := readOptional_part [57, 51, 48, 51] record.routingInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have extendedExecInst := readOptional_part [57, 52, 49, 54] record.extendedExecInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have introducingBadgeID := readOptional_part [57, 52, 52, 56] record.introducingBadgeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have billTo := readOptional_part [57, 52, 52, 57] record.billTo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have cancelInsteadOfReprice := readOptional_part [50, 48, 48, 48, 51] record.cancelInsteadOfReprice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have subIDIndicator := readOptional_part [50, 48, 48, 49, 51] record.subIDIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have auctionID := readOptional_part [50, 48, 48, 52, 49] record.auctionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  simp only [NewOrderMultileg.decode, account, clOrdID, orderQty, ordType, price, timeInForce, transactTime, securityType, customerOrFirm, noTradingSessions, clearingFirm, clearingAccount, optionalData, noLegs, selfTradeType, routingInst, extendedExecInst, introducingBadgeID, billTo, cancelInsteadOfReprice, subIDIndicator, auctionID, some_bind] <;> rfl

theorem NewOrderMultileg.taken (record : NewOrderMultileg) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49] record.account (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [51, 56] record.orderQty (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [52, 48] record.ordType (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [52, 52] record.price (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [53, 57] record.timeInForce (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [54, 48] record.transactTime (by decide) (by decide))
         (paired_cons pairing _ _ (paired_required pairing [49, 54, 55] record.securityType (by decide) (by decide))
          (paired_cons pairing _ _ (paired_required pairing [50, 48, 52] record.customerOrFirm (by decide) (by decide))
           (paired_cons pairing _ _ (paired_group pairing [51, 56, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within (by decide) (by decide) NoTradingSessions.taken record.noTradingSessions)
            (paired_cons pairing _ _ (paired_optional pairing [52, 51, 57] record.clearingFirm (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [52, 52, 48] record.clearingAccount (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [53, 50, 54] record.optionalData (by decide) (by decide))
               (paired_cons pairing _ _ (paired_group pairing [53, 53, 53] NoLegs.members NoLegs.encode NoLegs.within (by decide) (by decide) NoLegs.taken record.noLegs)
                (paired_cons pairing _ _ (paired_optional pairing [55, 57, 50, 56] record.selfTradeType (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_optional pairing [57, 51, 48, 51] record.routingInst (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [57, 52, 49, 54] record.extendedExecInst (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_optional pairing [57, 52, 52, 56] record.introducingBadgeID (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_optional pairing [57, 52, 52, 57] record.billTo (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 48, 51] record.cancelInsteadOfReprice (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 49, 51] record.subIDIndicator (by decide) (by decide))
                       (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 52, 49] record.auctionID (by decide) (by decide))
                        (paired_none pairing))))))))))))))))))))))

structure NoSidesComplexCross where
  clOrdID : Terminated 1  -- tag 11
  account : Option (Terminated 1)  -- tag 1
  ordType : Terminated 1  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  coveredOrUncovered : Terminated 1  -- tag 203
  customerOrFirm : Terminated 1  -- tag 204
  clearingFirm : Option (Terminated 1)  -- tag 439
  clearingAccount : Option (Terminated 1)  -- tag 440
  optionalData : Option (Terminated 1)  -- tag 526
  noLegs : List NoLegs  -- tag 555
  billTo : Option (Terminated 1)  -- tag 9449
  giveUpMarketMaker : Option (Terminated 1)  -- tag 20014
  allocationPct : Option (Terminated 1)  -- tag 20015

def NoSidesComplexCross.parts (record : NoSidesComplexCross) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.optional [49] record.account,
   Part.required [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.required [50, 48, 51] record.coveredOrUncovered,
   Part.required [50, 48, 52] record.customerOrFirm,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.optional [53, 50, 54] record.optionalData,
   Part.group [53, 53, 53] NoLegs.members NoLegs.encode NoLegs.within record.noLegs,
   Part.optional [57, 52, 52, 57] record.billTo,
   Part.optional [50, 48, 48, 49, 52] record.giveUpMarketMaker,
   Part.optional [50, 48, 48, 49, 53] record.allocationPct]

def NoSidesComplexCross.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[49]], [[52, 48]], [[52, 52]], [[50, 48, 51]], [[50, 48, 52]], [[52, 51, 57]], [[52, 52, 48]], [[53, 50, 54]], [53, 53, 53] :: NoLegs.members, [[57, 52, 52, 57]], [[50, 48, 48, 49, 52]], [[50, 48, 48, 49, 53]]]

theorem NoSidesComplexCross.shape (record : NoSidesComplexCross) : record.parts.map Part.tags = NoSidesComplexCross.tags := rfl

def NoSidesComplexCross.decode (tokens : List Token) : Option NoSidesComplexCross := do
  let clOrdID ← readRequired [49, 49] tokens
  let account ← readOptional [49] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let coveredOrUncovered ← readRequired [50, 48, 51] tokens
  let customerOrFirm ← readRequired [50, 48, 52] tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let optionalData ← readOptional [53, 50, 54] tokens
  let noLegs ← readGroup [53, 53, 53] [54, 48, 48] NoLegs.members NoLegs.decode tokens
  let billTo ← readOptional [57, 52, 52, 57] tokens
  let giveUpMarketMaker ← readOptional [50, 48, 48, 49, 52] tokens
  let allocationPct ← readOptional [50, 48, 48, 49, 53] tokens
  pure { clOrdID, account, ordType, price, coveredOrUncovered, customerOrFirm, clearingFirm, clearingAccount, optionalData, noLegs, billTo, giveUpMarketMaker, allocationPct }

theorem NoSidesComplexCross.decode_agrees (record : NoSidesComplexCross) (tokens : List Token)
    (agrees : ∀ tags ∈ NoSidesComplexCross.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoSidesComplexCross.decode tokens = some record := by
  have distinct : NoSidesComplexCross.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have coveredOrUncovered := readRequired_part [50, 48, 51] record.coveredOrUncovered tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have customerOrFirm := readRequired_part [50, 48, 52] record.customerOrFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have optionalData := readOptional_part [53, 50, 54] record.optionalData tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have noLegs := readGroup_part [53, 53, 53] [54, 48, 48] NoLegs.members NoLegs.encode NoLegs.within NoLegs.decode NoLegs.decode_encode NoLegs.led record.noLegs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have billTo := readOptional_part [57, 52, 52, 57] record.billTo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have giveUpMarketMaker := readOptional_part [50, 48, 48, 49, 52] record.giveUpMarketMaker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have allocationPct := readOptional_part [50, 48, 48, 49, 53] record.allocationPct tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  simp only [NoSidesComplexCross.decode, clOrdID, account, ordType, price, coveredOrUncovered, customerOrFirm, clearingFirm, clearingAccount, optionalData, noLegs, billTo, giveUpMarketMaker, allocationPct, some_bind] <;> rfl

theorem NoSidesComplexCross.taken (record : NoSidesComplexCross) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [49] record.account (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [52, 48] record.ordType (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [52, 52] record.price (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [50, 48, 51] record.coveredOrUncovered (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [50, 48, 52] record.customerOrFirm (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [52, 51, 57] record.clearingFirm (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [52, 52, 48] record.clearingAccount (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [53, 50, 54] record.optionalData (by decide) (by decide))
           (paired_cons pairing _ _ (paired_group pairing [53, 53, 53] NoLegs.members NoLegs.encode NoLegs.within (by decide) (by decide) NoLegs.taken record.noLegs)
            (paired_cons pairing _ _ (paired_optional pairing [57, 52, 52, 57] record.billTo (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 49, 52] record.giveUpMarketMaker (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 49, 53] record.allocationPct (by decide) (by decide))
               (paired_none pairing)))))))))))))

def NoSidesComplexCross.members : List (List UInt8) := NoSidesComplexCross.tags.flatten

def NoSidesComplexCross.encode (entry : NoSidesComplexCross) : List Token := encodeParts entry.parts

theorem NoSidesComplexCross.decode_encode (entry : NoSidesComplexCross) : NoSidesComplexCross.decode entry.encode = some entry :=
  NoSidesComplexCross.decode_agrees entry _ (fun _ _ => rfl)

theorem NoSidesComplexCross.within (entry : NoSidesComplexCross) : ∀ token ∈ entry.encode, token.tag ∈ NoSidesComplexCross.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoSidesComplexCross.shape] at this

theorem NoSidesComplexCross.led (entry : NoSidesComplexCross) : Lead [49, 49] entry.encode :=
  lead_parts [49, 49] entry.clOrdID _ NoSidesComplexCross.tags.tail rfl (by decide +kernel)

structure NewMultilegCross where
  orderQty : Terminated 1  -- tag 38
  timeInForce : Terminated 1  -- tag 59
  transactTime : Option (Terminated 1)  -- tag 60
  securityType : Terminated 1  -- tag 167
  noTradingSessions : List NoTradingSessions  -- tag 386
  crossID : Terminated 1  -- tag 548
  specialOrdType : Terminated 1  -- tag 9202
  introducingBadgeID : Option (Terminated 1)  -- tag 9448
  noSidesComplexCross : List NoSidesComplexCross  -- tag 552

def NewMultilegCross.parts (record : NewMultilegCross) : List Part :=
  [Part.required [51, 56] record.orderQty,
   Part.required [53, 57] record.timeInForce,
   Part.optional [54, 48] record.transactTime,
   Part.required [49, 54, 55] record.securityType,
   Part.group [51, 56, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within record.noTradingSessions,
   Part.required [53, 52, 56] record.crossID,
   Part.required [57, 50, 48, 50] record.specialOrdType,
   Part.optional [57, 52, 52, 56] record.introducingBadgeID,
   Part.group [53, 53, 50] NoSidesComplexCross.members NoSidesComplexCross.encode NoSidesComplexCross.within record.noSidesComplexCross]

def NewMultilegCross.tags : List (List (List UInt8)) :=
  [[[51, 56]], [[53, 57]], [[54, 48]], [[49, 54, 55]], [51, 56, 54] :: NoTradingSessions.members, [[53, 52, 56]], [[57, 50, 48, 50]], [[57, 52, 52, 56]], [53, 53, 50] :: NoSidesComplexCross.members]

theorem NewMultilegCross.shape (record : NewMultilegCross) : record.parts.map Part.tags = NewMultilegCross.tags := rfl

def NewMultilegCross.decode (tokens : List Token) : Option NewMultilegCross := do
  let orderQty ← readRequired [51, 56] tokens
  let timeInForce ← readRequired [53, 57] tokens
  let transactTime ← readOptional [54, 48] tokens
  let securityType ← readRequired [49, 54, 55] tokens
  let noTradingSessions ← readGroup [51, 56, 54] [51, 51, 54] NoTradingSessions.members NoTradingSessions.decode tokens
  let crossID ← readRequired [53, 52, 56] tokens
  let specialOrdType ← readRequired [57, 50, 48, 50] tokens
  let introducingBadgeID ← readOptional [57, 52, 52, 56] tokens
  let noSidesComplexCross ← readGroup [53, 53, 50] [49, 49] NoSidesComplexCross.members NoSidesComplexCross.decode tokens
  pure { orderQty, timeInForce, transactTime, securityType, noTradingSessions, crossID, specialOrdType, introducingBadgeID, noSidesComplexCross }

theorem NewMultilegCross.decode_agrees (record : NewMultilegCross) (tokens : List Token)
    (agrees : ∀ tags ∈ NewMultilegCross.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NewMultilegCross.decode tokens = some record := by
  have distinct : NewMultilegCross.tags.flatten.Nodup := by decide +kernel
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have timeInForce := readRequired_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have securityType := readRequired_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have noTradingSessions := readGroup_part [51, 56, 54] [51, 51, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within NoTradingSessions.decode NoTradingSessions.decode_encode NoTradingSessions.led record.noTradingSessions tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have crossID := readRequired_part [53, 52, 56] record.crossID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have specialOrdType := readRequired_part [57, 50, 48, 50] record.specialOrdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have introducingBadgeID := readOptional_part [57, 52, 52, 56] record.introducingBadgeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have noSidesComplexCross := readGroup_part [53, 53, 50] [49, 49] NoSidesComplexCross.members NoSidesComplexCross.encode NoSidesComplexCross.within NoSidesComplexCross.decode NoSidesComplexCross.decode_encode NoSidesComplexCross.led record.noSidesComplexCross tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  simp only [NewMultilegCross.decode, orderQty, timeInForce, transactTime, securityType, noTradingSessions, crossID, specialOrdType, introducingBadgeID, noSidesComplexCross, some_bind] <;> rfl

theorem NewMultilegCross.taken (record : NewMultilegCross) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 56] record.orderQty (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [53, 57] record.timeInForce (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [54, 48] record.transactTime (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [49, 54, 55] record.securityType (by decide) (by decide))
      (paired_cons pairing _ _ (paired_group pairing [51, 56, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within (by decide) (by decide) NoTradingSessions.taken record.noTradingSessions)
       (paired_cons pairing _ _ (paired_required pairing [53, 52, 56] record.crossID (by decide) (by decide))
        (paired_cons pairing _ _ (paired_required pairing [57, 50, 48, 50] record.specialOrdType (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [57, 52, 52, 56] record.introducingBadgeID (by decide) (by decide))
          (paired_cons pairing _ _ (paired_group pairing [53, 53, 50] NoSidesComplexCross.members NoSidesComplexCross.encode NoSidesComplexCross.within (by decide) (by decide) NoSidesComplexCross.taken record.noSidesComplexCross)
           (paired_none pairing)))))))))

structure MultilegOrderCancelReplace where
  account : Option (Terminated 1)  -- tag 1
  clOrdID : Terminated 1  -- tag 11
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  origClOrdID : Terminated 1  -- tag 41
  price : Terminated 1  -- tag 44
  timeInForce : Terminated 1  -- tag 59
  transactTime : Option (Terminated 1)  -- tag 60
  securityType : Terminated 1  -- tag 167
  customerOrFirm : Terminated 1  -- tag 204
  noTradingSessions : List NoTradingSessions  -- tag 386
  clearingFirm : Option (Terminated 1)  -- tag 439
  clearingAccount : Option (Terminated 1)  -- tag 440
  optionalData : Option (Terminated 1)  -- tag 526
  noLegs : List NoLegs  -- tag 555
  selfTradeType : Option (Terminated 1)  -- tag 7928
  routingInst : Option (Terminated 1)  -- tag 9303
  extendedExecInst : Option (Terminated 1)  -- tag 9416
  introducingBadgeID : Option (Terminated 1)  -- tag 9448
  billTo : Option (Terminated 1)  -- tag 9449
  cancelInsteadOfReprice : Option (Terminated 1)  -- tag 20003
  subIDIndicator : Option (Terminated 1)  -- tag 20013

def MultilegOrderCancelReplace.parts (record : MultilegOrderCancelReplace) : List Part :=
  [Part.optional [49] record.account,
   Part.required [49, 49] record.clOrdID,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.required [52, 49] record.origClOrdID,
   Part.required [52, 52] record.price,
   Part.required [53, 57] record.timeInForce,
   Part.optional [54, 48] record.transactTime,
   Part.required [49, 54, 55] record.securityType,
   Part.required [50, 48, 52] record.customerOrFirm,
   Part.group [51, 56, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within record.noTradingSessions,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.optional [53, 50, 54] record.optionalData,
   Part.group [53, 53, 53] NoLegs.members NoLegs.encode NoLegs.within record.noLegs,
   Part.optional [55, 57, 50, 56] record.selfTradeType,
   Part.optional [57, 51, 48, 51] record.routingInst,
   Part.optional [57, 52, 49, 54] record.extendedExecInst,
   Part.optional [57, 52, 52, 56] record.introducingBadgeID,
   Part.optional [57, 52, 52, 57] record.billTo,
   Part.optional [50, 48, 48, 48, 51] record.cancelInsteadOfReprice,
   Part.optional [50, 48, 48, 49, 51] record.subIDIndicator]

def MultilegOrderCancelReplace.tags : List (List (List UInt8)) :=
  [[[49]], [[49, 49]], [[51, 56]], [[52, 48]], [[52, 49]], [[52, 52]], [[53, 57]], [[54, 48]], [[49, 54, 55]], [[50, 48, 52]], [51, 56, 54] :: NoTradingSessions.members, [[52, 51, 57]], [[52, 52, 48]], [[53, 50, 54]], [53, 53, 53] :: NoLegs.members, [[55, 57, 50, 56]], [[57, 51, 48, 51]], [[57, 52, 49, 54]], [[57, 52, 52, 56]], [[57, 52, 52, 57]], [[50, 48, 48, 48, 51]], [[50, 48, 48, 49, 51]]]

theorem MultilegOrderCancelReplace.shape (record : MultilegOrderCancelReplace) : record.parts.map Part.tags = MultilegOrderCancelReplace.tags := rfl

def MultilegOrderCancelReplace.decode (tokens : List Token) : Option MultilegOrderCancelReplace := do
  let account ← readOptional [49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let price ← readRequired [52, 52] tokens
  let timeInForce ← readRequired [53, 57] tokens
  let transactTime ← readOptional [54, 48] tokens
  let securityType ← readRequired [49, 54, 55] tokens
  let customerOrFirm ← readRequired [50, 48, 52] tokens
  let noTradingSessions ← readGroup [51, 56, 54] [51, 51, 54] NoTradingSessions.members NoTradingSessions.decode tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let optionalData ← readOptional [53, 50, 54] tokens
  let noLegs ← readGroup [53, 53, 53] [54, 48, 48] NoLegs.members NoLegs.decode tokens
  let selfTradeType ← readOptional [55, 57, 50, 56] tokens
  let routingInst ← readOptional [57, 51, 48, 51] tokens
  let extendedExecInst ← readOptional [57, 52, 49, 54] tokens
  let introducingBadgeID ← readOptional [57, 52, 52, 56] tokens
  let billTo ← readOptional [57, 52, 52, 57] tokens
  let cancelInsteadOfReprice ← readOptional [50, 48, 48, 48, 51] tokens
  let subIDIndicator ← readOptional [50, 48, 48, 49, 51] tokens
  pure { account, clOrdID, orderQty, ordType, origClOrdID, price, timeInForce, transactTime, securityType, customerOrFirm, noTradingSessions, clearingFirm, clearingAccount, optionalData, noLegs, selfTradeType, routingInst, extendedExecInst, introducingBadgeID, billTo, cancelInsteadOfReprice, subIDIndicator }

theorem MultilegOrderCancelReplace.decode_agrees (record : MultilegOrderCancelReplace) (tokens : List Token)
    (agrees : ∀ tags ∈ MultilegOrderCancelReplace.tags, select tags tokens = select tags (encodeParts record.parts)) :
    MultilegOrderCancelReplace.decode tokens = some record := by
  have distinct : MultilegOrderCancelReplace.tags.flatten.Nodup := by decide +kernel
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have price := readRequired_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have timeInForce := readRequired_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have securityType := readRequired_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have customerOrFirm := readRequired_part [50, 48, 52] record.customerOrFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have noTradingSessions := readGroup_part [51, 56, 54] [51, 51, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within NoTradingSessions.decode NoTradingSessions.decode_encode NoTradingSessions.led record.noTradingSessions tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have optionalData := readOptional_part [53, 50, 54] record.optionalData tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have noLegs := readGroup_part [53, 53, 53] [54, 48, 48] NoLegs.members NoLegs.encode NoLegs.within NoLegs.decode NoLegs.decode_encode NoLegs.led record.noLegs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have selfTradeType := readOptional_part [55, 57, 50, 56] record.selfTradeType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have routingInst := readOptional_part [57, 51, 48, 51] record.routingInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have extendedExecInst := readOptional_part [57, 52, 49, 54] record.extendedExecInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have introducingBadgeID := readOptional_part [57, 52, 52, 56] record.introducingBadgeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have billTo := readOptional_part [57, 52, 52, 57] record.billTo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have cancelInsteadOfReprice := readOptional_part [50, 48, 48, 48, 51] record.cancelInsteadOfReprice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have subIDIndicator := readOptional_part [50, 48, 48, 49, 51] record.subIDIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  simp only [MultilegOrderCancelReplace.decode, account, clOrdID, orderQty, ordType, origClOrdID, price, timeInForce, transactTime, securityType, customerOrFirm, noTradingSessions, clearingFirm, clearingAccount, optionalData, noLegs, selfTradeType, routingInst, extendedExecInst, introducingBadgeID, billTo, cancelInsteadOfReprice, subIDIndicator, some_bind] <;> rfl

theorem MultilegOrderCancelReplace.taken (record : MultilegOrderCancelReplace) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49] record.account (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [51, 56] record.orderQty (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [52, 48] record.ordType (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [52, 49] record.origClOrdID (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [52, 52] record.price (by decide) (by decide))
        (paired_cons pairing _ _ (paired_required pairing [53, 57] record.timeInForce (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [54, 48] record.transactTime (by decide) (by decide))
          (paired_cons pairing _ _ (paired_required pairing [49, 54, 55] record.securityType (by decide) (by decide))
           (paired_cons pairing _ _ (paired_required pairing [50, 48, 52] record.customerOrFirm (by decide) (by decide))
            (paired_cons pairing _ _ (paired_group pairing [51, 56, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within (by decide) (by decide) NoTradingSessions.taken record.noTradingSessions)
             (paired_cons pairing _ _ (paired_optional pairing [52, 51, 57] record.clearingFirm (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [52, 52, 48] record.clearingAccount (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [53, 50, 54] record.optionalData (by decide) (by decide))
                (paired_cons pairing _ _ (paired_group pairing [53, 53, 53] NoLegs.members NoLegs.encode NoLegs.within (by decide) (by decide) NoLegs.taken record.noLegs)
                 (paired_cons pairing _ _ (paired_optional pairing [55, 57, 50, 56] record.selfTradeType (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [57, 51, 48, 51] record.routingInst (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_optional pairing [57, 52, 49, 54] record.extendedExecInst (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_optional pairing [57, 52, 52, 56] record.introducingBadgeID (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_optional pairing [57, 52, 52, 57] record.billTo (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 48, 51] record.cancelInsteadOfReprice (by decide) (by decide))
                       (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 49, 51] record.subIDIndicator (by decide) (by decide))
                        (paired_none pairing))))))))))))))))))))))

inductive Message where
  | logon (header : Header) (r0 : Logon)
  | logout (header : Header) (r0 : Logout)
  | heartbeat (header : Header) (r0 : Heartbeat)
  | testRequest (header : Header) (r0 : TestRequest)
  | resendRequest (header : Header) (r0 : ResendRequest)
  | sequenceReset (header : Header) (r0 : SequenceReset)
  | reject (header : Header) (r0 : Reject)
  | newOrderSingle (header : Header) (r0 : NewOrderSingle)
  | newOrderCross (header : Header) (r0 : NewOrderCross)
  | orderCancelRequestCancelSingleLegonly (header : Header) (r0 : OrderCancelRequest) (r1 : OrderCancelRequestCancelSingleLegonly)
  | orderCancelRequestCancelComplexonly (header : Header) (r0 : OrderCancelRequest) (r1 : OrderCancelRequestCancelComplexonly)
  | orderCancelRequestCancelbothSingleLegandComplex (header : Header) (r0 : OrderCancelRequest) (r1 : OrderCancelRequestCancelbothSingleLegandComplex)
  | orderCancelRequestOrderCancelRequest (header : Header) (k0 : {v : Terminated 1 // v.val ∉ ([[49], [50], [51]] : List (List UInt8))}) (r0 : OrderCancelRequest) (r1 : OrderCancelRequestOrderCancelRequest)
  | orderCancelReplaceRequest (header : Header) (r0 : OrderCancelReplaceRequest)
  | newOrderMultileg (header : Header) (r0 : NewOrderMultileg)
  | newMultilegCross (header : Header) (r0 : NewMultilegCross)
  | multilegOrderCancelReplace (header : Header) (r0 : MultilegOrderCancelReplace)

def Message.tokens : Message → List Token
  | .logon header r0 => ⟨[51, 53], [65]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logout header r0 => ⟨[51, 53], [53]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .heartbeat header r0 => ⟨[51, 53], [48]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .testRequest header r0 => ⟨[51, 53], [49]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .resendRequest header r0 => ⟨[51, 53], [50]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .sequenceReset header r0 => ⟨[51, 53], [52]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .reject header r0 => ⟨[51, 53], [51]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .newOrderSingle header r0 => ⟨[51, 53], [68]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .newOrderCross header r0 => ⟨[51, 53], [115]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelRequestCancelSingleLegonly header r0 r1 => ⟨[51, 53], [70]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [50, 48, 48, 50, 55] ⟨[49], by decide⟩] ++ r1.parts)
  | .orderCancelRequestCancelComplexonly header r0 r1 => ⟨[51, 53], [70]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [50, 48, 48, 50, 55] ⟨[50], by decide⟩] ++ r1.parts)
  | .orderCancelRequestCancelbothSingleLegandComplex header r0 r1 => ⟨[51, 53], [70]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [50, 48, 48, 50, 55] ⟨[51], by decide⟩] ++ r1.parts)
  | .orderCancelRequestOrderCancelRequest header k0 r0 r1 => ⟨[51, 53], [70]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [50, 48, 48, 50, 55] k0.1] ++ r1.parts)
  | .orderCancelReplaceRequest header r0 => ⟨[51, 53], [71]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .newOrderMultileg header r0 => ⟨[51, 53], [65, 66]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .newMultilegCross header r0 => ⟨[51, 53], [65, 115]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .multilegOrderCancelReplace header r0 => ⟨[51, 53], [65, 67]⟩ :: encodeParts (header.parts ++ r0.parts)

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
      else if token.value = [52] then
        if known (Header.tags ++ SequenceReset.tags) rest then do
          let header ← Header.decode rest
          let r0 ← SequenceReset.decode rest
          pure (.sequenceReset header r0)
        else none
      else if token.value = [51] then
        if known (Header.tags ++ Reject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Reject.decode rest
          pure (.reject header r0)
        else none
      else if token.value = [68] then
        if known (Header.tags ++ NewOrderSingle.tags) rest then do
          let header ← Header.decode rest
          let r0 ← NewOrderSingle.decode rest
          pure (.newOrderSingle header r0)
        else none
      else if token.value = [115] then
        if known (Header.tags ++ NewOrderCross.tags) rest then do
          let header ← Header.decode rest
          let r0 ← NewOrderCross.decode rest
          pure (.newOrderCross header r0)
        else none
      else if token.value = [70] then
        match readRequired [50, 48, 48, 50, 55] rest with
        | none => none
        | some key =>
          if h0_0 : key.val = [49] then
            if known (Header.tags ++ OrderCancelRequest.tags ++ [[[50, 48, 48, 50, 55]]] ++ OrderCancelRequestCancelSingleLegonly.tags) rest then do
              let header ← Header.decode rest
              let r0 ← OrderCancelRequest.decode rest
              let r1 ← OrderCancelRequestCancelSingleLegonly.decode rest
              pure (.orderCancelRequestCancelSingleLegonly header r0 r1)
            else none
          else if h0_1 : key.val = [50] then
            if known (Header.tags ++ OrderCancelRequest.tags ++ [[[50, 48, 48, 50, 55]]] ++ OrderCancelRequestCancelComplexonly.tags) rest then do
              let header ← Header.decode rest
              let r0 ← OrderCancelRequest.decode rest
              let r1 ← OrderCancelRequestCancelComplexonly.decode rest
              pure (.orderCancelRequestCancelComplexonly header r0 r1)
            else none
          else if h0_2 : key.val = [51] then
            if known (Header.tags ++ OrderCancelRequest.tags ++ [[[50, 48, 48, 50, 55]]] ++ OrderCancelRequestCancelbothSingleLegandComplex.tags) rest then do
              let header ← Header.decode rest
              let r0 ← OrderCancelRequest.decode rest
              let r1 ← OrderCancelRequestCancelbothSingleLegandComplex.decode rest
              pure (.orderCancelRequestCancelbothSingleLegandComplex header r0 r1)
            else none
          else let k0 : {v : Terminated 1 // v.val ∉ ([[49], [50], [51]] : List (List UInt8))} := ⟨key, by simp [h0_0, h0_1, h0_2]⟩
          if known (Header.tags ++ OrderCancelRequest.tags ++ [[[50, 48, 48, 50, 55]]] ++ OrderCancelRequestOrderCancelRequest.tags) rest then do
            let header ← Header.decode rest
            let r0 ← OrderCancelRequest.decode rest
            let r1 ← OrderCancelRequestOrderCancelRequest.decode rest
            pure (.orderCancelRequestOrderCancelRequest header k0 r0 r1)
          else none
      else if token.value = [71] then
        if known (Header.tags ++ OrderCancelReplaceRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderCancelReplaceRequest.decode rest
          pure (.orderCancelReplaceRequest header r0)
        else none
      else if token.value = [65, 66] then
        if known (Header.tags ++ NewOrderMultileg.tags) rest then do
          let header ← Header.decode rest
          let r0 ← NewOrderMultileg.decode rest
          pure (.newOrderMultileg header r0)
        else none
      else if token.value = [65, 115] then
        if known (Header.tags ++ NewMultilegCross.tags) rest then do
          let header ← Header.decode rest
          let r0 ← NewMultilegCross.decode rest
          pure (.newMultilegCross header r0)
        else none
      else if token.value = [65, 67] then
        if known (Header.tags ++ MultilegOrderCancelReplace.tags) rest then do
          let header ← Header.decode rest
          let r0 ← MultilegOrderCancelReplace.decode rest
          pure (.multilegOrderCancelReplace header r0)
        else none
      else none
    else none

theorem Message.decode_logon (header : Header) (r0 : Logon) :
    Message.decode (Message.tokens (.logon header r0)) = some (.logon header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (Logon.tags) rfl rfl (by decide +kernel))
  have c1 := Logon.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (Logon.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ Logon.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, dite_true, dite_false, some_bind] <;> rfl

theorem Message.decode_logout (header : Header) (r0 : Logout) :
    Message.decode (Message.tokens (.logout header r0)) = some (.logout header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (Logout.tags) rfl rfl (by decide +kernel))
  have c1 := Logout.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (Logout.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ Logout.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, dite_true, dite_false, some_bind] <;> rfl

theorem Message.decode_heartbeat (header : Header) (r0 : Heartbeat) :
    Message.decode (Message.tokens (.heartbeat header r0)) = some (.heartbeat header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (Heartbeat.tags) rfl rfl (by decide +kernel))
  have c1 := Heartbeat.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (Heartbeat.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ Heartbeat.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, dite_true, dite_false, some_bind] <;> rfl

theorem Message.decode_testRequest (header : Header) (r0 : TestRequest) :
    Message.decode (Message.tokens (.testRequest header r0)) = some (.testRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (TestRequest.tags) rfl rfl (by decide +kernel))
  have c1 := TestRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (TestRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ TestRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, dite_true, dite_false, some_bind] <;> rfl

theorem Message.decode_resendRequest (header : Header) (r0 : ResendRequest) :
    Message.decode (Message.tokens (.resendRequest header r0)) = some (.resendRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (ResendRequest.tags) rfl rfl (by decide +kernel))
  have c1 := ResendRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (ResendRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ ResendRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, dite_true, dite_false, some_bind] <;> rfl

theorem Message.decode_sequenceReset (header : Header) (r0 : SequenceReset) :
    Message.decode (Message.tokens (.sequenceReset header r0)) = some (.sequenceReset header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (SequenceReset.tags) rfl rfl (by decide +kernel))
  have c1 := SequenceReset.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (SequenceReset.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ SequenceReset.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, dite_true, dite_false, some_bind] <;> rfl

theorem Message.decode_reject (header : Header) (r0 : Reject) :
    Message.decode (Message.tokens (.reject header r0)) = some (.reject header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (Reject.tags) rfl rfl (by decide +kernel))
  have c1 := Reject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (Reject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ Reject.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, dite_true, dite_false, some_bind] <;> rfl

theorem Message.decode_newOrderSingle (header : Header) (r0 : NewOrderSingle) :
    Message.decode (Message.tokens (.newOrderSingle header r0)) = some (.newOrderSingle header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (NewOrderSingle.tags) rfl rfl (by decide +kernel))
  have c1 := NewOrderSingle.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (NewOrderSingle.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ NewOrderSingle.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, dite_true, dite_false, some_bind] <;> rfl

theorem Message.decode_newOrderCross (header : Header) (r0 : NewOrderCross) :
    Message.decode (Message.tokens (.newOrderCross header r0)) = some (.newOrderCross header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (NewOrderCross.tags) rfl rfl (by decide +kernel))
  have c1 := NewOrderCross.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (NewOrderCross.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ NewOrderCross.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, dite_true, dite_false, some_bind] <;> rfl

theorem Message.decode_orderCancelRequestCancelSingleLegonly (header : Header) (r0 : OrderCancelRequest) (r1 : OrderCancelRequestCancelSingleLegonly) :
    Message.decode (Message.tokens (.orderCancelRequestCancelSingleLegonly header r0 r1)) = some (.orderCancelRequestCancelSingleLegonly header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [50, 48, 48, 50, 55] ⟨[49], by decide⟩] ++ r1.parts) ([]) (Header.tags) (OrderCancelRequest.tags ++ [[[50, 48, 48, 50, 55]]] ++ OrderCancelRequestCancelSingleLegonly.tags) rfl rfl (by decide +kernel))
  have c1 := OrderCancelRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [50, 48, 48, 50, 55] ⟨[49], by decide⟩] ++ r1.parts) (Header.tags) (OrderCancelRequest.tags) ([[[50, 48, 48, 50, 55]]] ++ OrderCancelRequestCancelSingleLegonly.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [50, 48, 48, 50, 55] ⟨[49], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [50, 48, 48, 50, 55] ⟨[49], by decide⟩]) (r1.parts) (Header.tags ++ OrderCancelRequest.tags) ([[[50, 48, 48, 50, 55]]]) (OrderCancelRequestCancelSingleLegonly.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := OrderCancelRequestCancelSingleLegonly.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [50, 48, 48, 50, 55] ⟨[49], by decide⟩]) (r1.parts) ([]) (Header.tags ++ OrderCancelRequest.tags ++ [[[50, 48, 48, 50, 55]]]) (OrderCancelRequestCancelSingleLegonly.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [50, 48, 48, 50, 55] ⟨[49], by decide⟩] ++ r1.parts) (Header.tags ++ OrderCancelRequest.tags ++ [[[50, 48, 48, 50, 55]]] ++ OrderCancelRequestCancelSingleLegonly.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, dite_true, dite_false, some_bind] <;> rfl

theorem Message.decode_orderCancelRequestCancelComplexonly (header : Header) (r0 : OrderCancelRequest) (r1 : OrderCancelRequestCancelComplexonly) :
    Message.decode (Message.tokens (.orderCancelRequestCancelComplexonly header r0 r1)) = some (.orderCancelRequestCancelComplexonly header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [50, 48, 48, 50, 55] ⟨[50], by decide⟩] ++ r1.parts) ([]) (Header.tags) (OrderCancelRequest.tags ++ [[[50, 48, 48, 50, 55]]] ++ OrderCancelRequestCancelComplexonly.tags) rfl rfl (by decide +kernel))
  have c1 := OrderCancelRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [50, 48, 48, 50, 55] ⟨[50], by decide⟩] ++ r1.parts) (Header.tags) (OrderCancelRequest.tags) ([[[50, 48, 48, 50, 55]]] ++ OrderCancelRequestCancelComplexonly.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [50, 48, 48, 50, 55] ⟨[50], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [50, 48, 48, 50, 55] ⟨[50], by decide⟩]) (r1.parts) (Header.tags ++ OrderCancelRequest.tags) ([[[50, 48, 48, 50, 55]]]) (OrderCancelRequestCancelComplexonly.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := OrderCancelRequestCancelComplexonly.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [50, 48, 48, 50, 55] ⟨[50], by decide⟩]) (r1.parts) ([]) (Header.tags ++ OrderCancelRequest.tags ++ [[[50, 48, 48, 50, 55]]]) (OrderCancelRequestCancelComplexonly.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [50, 48, 48, 50, 55] ⟨[50], by decide⟩] ++ r1.parts) (Header.tags ++ OrderCancelRequest.tags ++ [[[50, 48, 48, 50, 55]]] ++ OrderCancelRequestCancelComplexonly.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, dite_true, dite_false, some_bind] <;> rfl

theorem Message.decode_orderCancelRequestCancelbothSingleLegandComplex (header : Header) (r0 : OrderCancelRequest) (r1 : OrderCancelRequestCancelbothSingleLegandComplex) :
    Message.decode (Message.tokens (.orderCancelRequestCancelbothSingleLegandComplex header r0 r1)) = some (.orderCancelRequestCancelbothSingleLegandComplex header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [50, 48, 48, 50, 55] ⟨[51], by decide⟩] ++ r1.parts) ([]) (Header.tags) (OrderCancelRequest.tags ++ [[[50, 48, 48, 50, 55]]] ++ OrderCancelRequestCancelbothSingleLegandComplex.tags) rfl rfl (by decide +kernel))
  have c1 := OrderCancelRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [50, 48, 48, 50, 55] ⟨[51], by decide⟩] ++ r1.parts) (Header.tags) (OrderCancelRequest.tags) ([[[50, 48, 48, 50, 55]]] ++ OrderCancelRequestCancelbothSingleLegandComplex.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [50, 48, 48, 50, 55] ⟨[51], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [50, 48, 48, 50, 55] ⟨[51], by decide⟩]) (r1.parts) (Header.tags ++ OrderCancelRequest.tags) ([[[50, 48, 48, 50, 55]]]) (OrderCancelRequestCancelbothSingleLegandComplex.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := OrderCancelRequestCancelbothSingleLegandComplex.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [50, 48, 48, 50, 55] ⟨[51], by decide⟩]) (r1.parts) ([]) (Header.tags ++ OrderCancelRequest.tags ++ [[[50, 48, 48, 50, 55]]]) (OrderCancelRequestCancelbothSingleLegandComplex.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [50, 48, 48, 50, 55] ⟨[51], by decide⟩] ++ r1.parts) (Header.tags ++ OrderCancelRequest.tags ++ [[[50, 48, 48, 50, 55]]] ++ OrderCancelRequestCancelbothSingleLegandComplex.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, dite_true, dite_false, some_bind] <;> rfl

theorem Message.decode_orderCancelRequestOrderCancelRequest (header : Header) (k0 : {v : Terminated 1 // v.val ∉ ([[49], [50], [51]] : List (List UInt8))}) (r0 : OrderCancelRequest) (r1 : OrderCancelRequestOrderCancelRequest) :
    Message.decode (Message.tokens (.orderCancelRequestOrderCancelRequest header k0 r0 r1)) = some (.orderCancelRequestOrderCancelRequest header k0 r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [50, 48, 48, 50, 55] k0.1] ++ r1.parts) ([]) (Header.tags) (OrderCancelRequest.tags ++ [[[50, 48, 48, 50, 55]]] ++ OrderCancelRequestOrderCancelRequest.tags) rfl rfl (by decide +kernel))
  have c1 := OrderCancelRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [50, 48, 48, 50, 55] k0.1] ++ r1.parts) (Header.tags) (OrderCancelRequest.tags) ([[[50, 48, 48, 50, 55]]] ++ OrderCancelRequestOrderCancelRequest.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [50, 48, 48, 50, 55] k0.1 _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [50, 48, 48, 50, 55] k0.1]) (r1.parts) (Header.tags ++ OrderCancelRequest.tags) ([[[50, 48, 48, 50, 55]]]) (OrderCancelRequestOrderCancelRequest.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := OrderCancelRequestOrderCancelRequest.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [50, 48, 48, 50, 55] k0.1]) (r1.parts) ([]) (Header.tags ++ OrderCancelRequest.tags ++ [[[50, 48, 48, 50, 55]]]) (OrderCancelRequestOrderCancelRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [50, 48, 48, 50, 55] k0.1] ++ r1.parts) (Header.tags ++ OrderCancelRequest.tags ++ [[[50, 48, 48, 50, 55]]] ++ OrderCancelRequestOrderCancelRequest.tags) rfl
  have e0 := k0.2
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at e0
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, dite_true, dite_false, e0, some_bind] <;> rfl

theorem Message.decode_orderCancelReplaceRequest (header : Header) (r0 : OrderCancelReplaceRequest) :
    Message.decode (Message.tokens (.orderCancelReplaceRequest header r0)) = some (.orderCancelReplaceRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelReplaceRequest.tags) rfl rfl (by decide +kernel))
  have c1 := OrderCancelReplaceRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelReplaceRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderCancelReplaceRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, dite_true, dite_false, some_bind] <;> rfl

theorem Message.decode_newOrderMultileg (header : Header) (r0 : NewOrderMultileg) :
    Message.decode (Message.tokens (.newOrderMultileg header r0)) = some (.newOrderMultileg header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (NewOrderMultileg.tags) rfl rfl (by decide +kernel))
  have c1 := NewOrderMultileg.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (NewOrderMultileg.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ NewOrderMultileg.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, dite_true, dite_false, some_bind] <;> rfl

theorem Message.decode_newMultilegCross (header : Header) (r0 : NewMultilegCross) :
    Message.decode (Message.tokens (.newMultilegCross header r0)) = some (.newMultilegCross header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (NewMultilegCross.tags) rfl rfl (by decide +kernel))
  have c1 := NewMultilegCross.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (NewMultilegCross.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ NewMultilegCross.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, dite_true, dite_false, some_bind] <;> rfl

theorem Message.decode_multilegOrderCancelReplace (header : Header) (r0 : MultilegOrderCancelReplace) :
    Message.decode (Message.tokens (.multilegOrderCancelReplace header r0)) = some (.multilegOrderCancelReplace header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (MultilegOrderCancelReplace.tags) rfl rfl (by decide +kernel))
  have c1 := MultilegOrderCancelReplace.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (MultilegOrderCancelReplace.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ MultilegOrderCancelReplace.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, dite_true, dite_false, some_bind] <;> rfl

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | logon header r0 => exact Message.decode_logon header r0
  | logout header r0 => exact Message.decode_logout header r0
  | heartbeat header r0 => exact Message.decode_heartbeat header r0
  | testRequest header r0 => exact Message.decode_testRequest header r0
  | resendRequest header r0 => exact Message.decode_resendRequest header r0
  | sequenceReset header r0 => exact Message.decode_sequenceReset header r0
  | reject header r0 => exact Message.decode_reject header r0
  | newOrderSingle header r0 => exact Message.decode_newOrderSingle header r0
  | newOrderCross header r0 => exact Message.decode_newOrderCross header r0
  | orderCancelRequestCancelSingleLegonly header r0 r1 => exact Message.decode_orderCancelRequestCancelSingleLegonly header r0 r1
  | orderCancelRequestCancelComplexonly header r0 r1 => exact Message.decode_orderCancelRequestCancelComplexonly header r0 r1
  | orderCancelRequestCancelbothSingleLegandComplex header r0 r1 => exact Message.decode_orderCancelRequestCancelbothSingleLegandComplex header r0 r1
  | orderCancelRequestOrderCancelRequest header k0 r0 r1 => exact Message.decode_orderCancelRequestOrderCancelRequest header k0 r0 r1
  | orderCancelReplaceRequest header r0 => exact Message.decode_orderCancelReplaceRequest header r0
  | newOrderMultileg header r0 => exact Message.decode_newOrderMultileg header r0
  | newMultilegCross header r0 => exact Message.decode_newMultilegCross header r0
  | multilegOrderCancelReplace header r0 => exact Message.decode_multilegOrderCancelReplace header r0

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

theorem Message.decodeBytes_sequenceReset (header : Header) (r0 : SequenceReset) :
    Message.decodeBytes (Message.encode (.sequenceReset header r0)) = some (.sequenceReset header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [52]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (SequenceReset.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_sequenceReset header r0

theorem Message.decodeBytes_reject (header : Header) (r0 : Reject) :
    Message.decodeBytes (Message.encode (.reject header r0)) = some (.reject header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [51]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (Reject.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_reject header r0

theorem Message.decodeBytes_newOrderSingle (header : Header) (r0 : NewOrderSingle) :
    Message.decodeBytes (Message.encode (.newOrderSingle header r0)) = some (.newOrderSingle header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [68]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (NewOrderSingle.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_newOrderSingle header r0

theorem Message.decodeBytes_newOrderCross (header : Header) (r0 : NewOrderCross) :
    Message.decodeBytes (Message.encode (.newOrderCross header r0)) = some (.newOrderCross header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [115]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (NewOrderCross.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_newOrderCross header r0

theorem Message.decodeBytes_orderCancelRequestCancelSingleLegonly (header : Header) (r0 : OrderCancelRequest) (r1 : OrderCancelRequestCancelSingleLegonly) :
    Message.decodeBytes (Message.encode (.orderCancelRequestCancelSingleLegonly header r0 r1)) = some (.orderCancelRequestCancelSingleLegonly header r0 r1) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [70]⟩ (header.parts ++ r0.parts ++ [Part.required [50, 48, 48, 50, 55] ⟨[49], by decide⟩] ++ r1.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [50, 48, 48, 50, 55] ⟨[49], by decide⟩] ++ r1.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [50, 48, 48, 50, 55] ⟨[49], by decide⟩] ++ r1.parts) (OrderCancelRequest.taken r0) (paired_parts pairing ([Part.required [50, 48, 48, 50, 55] ⟨[49], by decide⟩]) (r1.parts) (paired_cons pairing (Part.required [50, 48, 48, 50, 55] ⟨[49], by decide⟩) [] (paired_required pairing [50, 48, 48, 50, 55] ⟨[49], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (OrderCancelRequestCancelSingleLegonly.taken r1))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderCancelRequestCancelSingleLegonly header r0 r1

theorem Message.decodeBytes_orderCancelRequestCancelComplexonly (header : Header) (r0 : OrderCancelRequest) (r1 : OrderCancelRequestCancelComplexonly) :
    Message.decodeBytes (Message.encode (.orderCancelRequestCancelComplexonly header r0 r1)) = some (.orderCancelRequestCancelComplexonly header r0 r1) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [70]⟩ (header.parts ++ r0.parts ++ [Part.required [50, 48, 48, 50, 55] ⟨[50], by decide⟩] ++ r1.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [50, 48, 48, 50, 55] ⟨[50], by decide⟩] ++ r1.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [50, 48, 48, 50, 55] ⟨[50], by decide⟩] ++ r1.parts) (OrderCancelRequest.taken r0) (paired_parts pairing ([Part.required [50, 48, 48, 50, 55] ⟨[50], by decide⟩]) (r1.parts) (paired_cons pairing (Part.required [50, 48, 48, 50, 55] ⟨[50], by decide⟩) [] (paired_required pairing [50, 48, 48, 50, 55] ⟨[50], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (OrderCancelRequestCancelComplexonly.taken r1))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderCancelRequestCancelComplexonly header r0 r1

theorem Message.decodeBytes_orderCancelRequestCancelbothSingleLegandComplex (header : Header) (r0 : OrderCancelRequest) (r1 : OrderCancelRequestCancelbothSingleLegandComplex) :
    Message.decodeBytes (Message.encode (.orderCancelRequestCancelbothSingleLegandComplex header r0 r1)) = some (.orderCancelRequestCancelbothSingleLegandComplex header r0 r1) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [70]⟩ (header.parts ++ r0.parts ++ [Part.required [50, 48, 48, 50, 55] ⟨[51], by decide⟩] ++ r1.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [50, 48, 48, 50, 55] ⟨[51], by decide⟩] ++ r1.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [50, 48, 48, 50, 55] ⟨[51], by decide⟩] ++ r1.parts) (OrderCancelRequest.taken r0) (paired_parts pairing ([Part.required [50, 48, 48, 50, 55] ⟨[51], by decide⟩]) (r1.parts) (paired_cons pairing (Part.required [50, 48, 48, 50, 55] ⟨[51], by decide⟩) [] (paired_required pairing [50, 48, 48, 50, 55] ⟨[51], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (OrderCancelRequestCancelbothSingleLegandComplex.taken r1))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderCancelRequestCancelbothSingleLegandComplex header r0 r1

theorem Message.decodeBytes_orderCancelRequestOrderCancelRequest (header : Header) (k0 : {v : Terminated 1 // v.val ∉ ([[49], [50], [51]] : List (List UInt8))}) (r0 : OrderCancelRequest) (r1 : OrderCancelRequestOrderCancelRequest) :
    Message.decodeBytes (Message.encode (.orderCancelRequestOrderCancelRequest header k0 r0 r1)) = some (.orderCancelRequestOrderCancelRequest header k0 r0 r1) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [70]⟩ (header.parts ++ r0.parts ++ [Part.required [50, 48, 48, 50, 55] k0.1] ++ r1.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [50, 48, 48, 50, 55] k0.1] ++ r1.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [50, 48, 48, 50, 55] k0.1] ++ r1.parts) (OrderCancelRequest.taken r0) (paired_parts pairing ([Part.required [50, 48, 48, 50, 55] k0.1]) (r1.parts) (paired_cons pairing (Part.required [50, 48, 48, 50, 55] k0.1) [] (paired_required pairing [50, 48, 48, 50, 55] k0.1 (by decide) (by decide)) (paired_none pairing)) (OrderCancelRequestOrderCancelRequest.taken r1))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderCancelRequestOrderCancelRequest header k0 r0 r1

theorem Message.decodeBytes_orderCancelReplaceRequest (header : Header) (r0 : OrderCancelReplaceRequest) :
    Message.decodeBytes (Message.encode (.orderCancelReplaceRequest header r0)) = some (.orderCancelReplaceRequest header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [71]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (OrderCancelReplaceRequest.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderCancelReplaceRequest header r0

theorem Message.decodeBytes_newOrderMultileg (header : Header) (r0 : NewOrderMultileg) :
    Message.decodeBytes (Message.encode (.newOrderMultileg header r0)) = some (.newOrderMultileg header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [65, 66]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (NewOrderMultileg.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_newOrderMultileg header r0

theorem Message.decodeBytes_newMultilegCross (header : Header) (r0 : NewMultilegCross) :
    Message.decodeBytes (Message.encode (.newMultilegCross header r0)) = some (.newMultilegCross header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [65, 115]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (NewMultilegCross.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_newMultilegCross header r0

theorem Message.decodeBytes_multilegOrderCancelReplace (header : Header) (r0 : MultilegOrderCancelReplace) :
    Message.decodeBytes (Message.encode (.multilegOrderCancelReplace header r0)) = some (.multilegOrderCancelReplace header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [65, 67]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (MultilegOrderCancelReplace.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_multilegOrderCancelReplace header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | logon header r0 => exact Message.decodeBytes_logon header r0
  | logout header r0 => exact Message.decodeBytes_logout header r0
  | heartbeat header r0 => exact Message.decodeBytes_heartbeat header r0
  | testRequest header r0 => exact Message.decodeBytes_testRequest header r0
  | resendRequest header r0 => exact Message.decodeBytes_resendRequest header r0
  | sequenceReset header r0 => exact Message.decodeBytes_sequenceReset header r0
  | reject header r0 => exact Message.decodeBytes_reject header r0
  | newOrderSingle header r0 => exact Message.decodeBytes_newOrderSingle header r0
  | newOrderCross header r0 => exact Message.decodeBytes_newOrderCross header r0
  | orderCancelRequestCancelSingleLegonly header r0 r1 => exact Message.decodeBytes_orderCancelRequestCancelSingleLegonly header r0 r1
  | orderCancelRequestCancelComplexonly header r0 r1 => exact Message.decodeBytes_orderCancelRequestCancelComplexonly header r0 r1
  | orderCancelRequestCancelbothSingleLegandComplex header r0 r1 => exact Message.decodeBytes_orderCancelRequestCancelbothSingleLegandComplex header r0 r1
  | orderCancelRequestOrderCancelRequest header k0 r0 r1 => exact Message.decodeBytes_orderCancelRequestOrderCancelRequest header k0 r0 r1
  | orderCancelReplaceRequest header r0 => exact Message.decodeBytes_orderCancelReplaceRequest header r0
  | newOrderMultileg header r0 => exact Message.decodeBytes_newOrderMultileg header r0
  | newMultilegCross header r0 => exact Message.decodeBytes_newMultilegCross header r0
  | multilegOrderCancelReplace header r0 => exact Message.decodeBytes_multilegOrderCancelReplace header r0

/-- BeginString as the venue fixes it: FIX.4.2 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 46, 52, 46, 50, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.NyseAmexoptionsOrderentryFixV324Client
