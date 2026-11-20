import Wire

/-!
# Australian Securities Exchange Order Entry v2.05, Exchange messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.AsxAsxderivativesOrderentryFixV205Exchange

/-- No field of this tree is data, so every value ends at the separator -/
def pairing : Pairing := []

structure Header where
  senderCompID : Terminated 1  -- tag 49
  targetCompID : Terminated 1  -- tag 56
  msgSeqNum : Terminated 1  -- tag 34
  sendingTime : Terminated 1  -- tag 52
  possDupFlag : Option (Terminated 1)  -- tag 43
  possResend : Option (Terminated 1)  -- tag 97
  origSendingTime : Option (Terminated 1)  -- tag 122
  applVerID : Option (Terminated 1)  -- tag 1128

def Header.parts (record : Header) : List Part :=
  [Part.required [52, 57] record.senderCompID,
   Part.required [53, 54] record.targetCompID,
   Part.required [51, 52] record.msgSeqNum,
   Part.required [53, 50] record.sendingTime,
   Part.optional [52, 51] record.possDupFlag,
   Part.optional [57, 55] record.possResend,
   Part.optional [49, 50, 50] record.origSendingTime,
   Part.optional [49, 49, 50, 56] record.applVerID]

def Header.tags : List (List (List UInt8)) :=
  [[[52, 57]], [[53, 54]], [[51, 52]], [[53, 50]], [[52, 51]], [[57, 55]], [[49, 50, 50]], [[49, 49, 50, 56]]]

theorem Header.shape (record : Header) : record.parts.map Part.tags = Header.tags := rfl

def Header.decode (tokens : List Token) : Option Header := do
  let senderCompID ← readRequired [52, 57] tokens
  let targetCompID ← readRequired [53, 54] tokens
  let msgSeqNum ← readRequired [51, 52] tokens
  let sendingTime ← readRequired [53, 50] tokens
  let possDupFlag ← readOptional [52, 51] tokens
  let possResend ← readOptional [57, 55] tokens
  let origSendingTime ← readOptional [49, 50, 50] tokens
  let applVerID ← readOptional [49, 49, 50, 56] tokens
  pure { senderCompID, targetCompID, msgSeqNum, sendingTime, possDupFlag, possResend, origSendingTime, applVerID }

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
  have possDupFlag := readOptional_part [52, 51] record.possDupFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have possResend := readOptional_part [57, 55] record.possResend tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have origSendingTime := readOptional_part [49, 50, 50] record.origSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have applVerID := readOptional_part [49, 49, 50, 56] record.applVerID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  simp only [Header.decode, senderCompID, targetCompID, msgSeqNum, sendingTime, possDupFlag, possResend, origSendingTime, applVerID, some_bind] <;> rfl

theorem Header.taken (record : Header) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [52, 57] record.senderCompID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [53, 54] record.targetCompID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [51, 52] record.msgSeqNum (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [53, 50] record.sendingTime (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [52, 51] record.possDupFlag (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [57, 55] record.possResend (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [49, 50, 50] record.origSendingTime (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [49, 49, 50, 56] record.applVerID (by decide) (by decide))
          (paired_none pairing))))))))

structure Logon where
  encryptMethod : Terminated 1  -- tag 98
  heartBtInt : Terminated 1  -- tag 108
  resetSeqNumFlag : Option (Terminated 1)  -- tag 141
  nextExpectedMsgSeqNum : Option (Terminated 1)  -- tag 789
  username : Option (Terminated 1)  -- tag 553
  password : Option (Terminated 1)  -- tag 554
  newPassword : Option (Terminated 1)  -- tag 925
  sessionStatus : Option (Terminated 1)  -- tag 1409
  defaultApplVerID : Option (Terminated 1)  -- tag 1137
  text : Option (Terminated 1)  -- tag 58

def Logon.parts (record : Logon) : List Part :=
  [Part.required [57, 56] record.encryptMethod,
   Part.required [49, 48, 56] record.heartBtInt,
   Part.optional [49, 52, 49] record.resetSeqNumFlag,
   Part.optional [55, 56, 57] record.nextExpectedMsgSeqNum,
   Part.optional [53, 53, 51] record.username,
   Part.optional [53, 53, 52] record.password,
   Part.optional [57, 50, 53] record.newPassword,
   Part.optional [49, 52, 48, 57] record.sessionStatus,
   Part.optional [49, 49, 51, 55] record.defaultApplVerID,
   Part.optional [53, 56] record.text]

def Logon.tags : List (List (List UInt8)) :=
  [[[57, 56]], [[49, 48, 56]], [[49, 52, 49]], [[55, 56, 57]], [[53, 53, 51]], [[53, 53, 52]], [[57, 50, 53]], [[49, 52, 48, 57]], [[49, 49, 51, 55]], [[53, 56]]]

theorem Logon.shape (record : Logon) : record.parts.map Part.tags = Logon.tags := rfl

def Logon.decode (tokens : List Token) : Option Logon := do
  let encryptMethod ← readRequired [57, 56] tokens
  let heartBtInt ← readRequired [49, 48, 56] tokens
  let resetSeqNumFlag ← readOptional [49, 52, 49] tokens
  let nextExpectedMsgSeqNum ← readOptional [55, 56, 57] tokens
  let username ← readOptional [53, 53, 51] tokens
  let password ← readOptional [53, 53, 52] tokens
  let newPassword ← readOptional [57, 50, 53] tokens
  let sessionStatus ← readOptional [49, 52, 48, 57] tokens
  let defaultApplVerID ← readOptional [49, 49, 51, 55] tokens
  let text ← readOptional [53, 56] tokens
  pure { encryptMethod, heartBtInt, resetSeqNumFlag, nextExpectedMsgSeqNum, username, password, newPassword, sessionStatus, defaultApplVerID, text }

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
  have nextExpectedMsgSeqNum := readOptional_part [55, 56, 57] record.nextExpectedMsgSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have username := readOptional_part [53, 53, 51] record.username tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have password := readOptional_part [53, 53, 52] record.password tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have newPassword := readOptional_part [57, 50, 53] record.newPassword tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have sessionStatus := readOptional_part [49, 52, 48, 57] record.sessionStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have defaultApplVerID := readOptional_part [49, 49, 51, 55] record.defaultApplVerID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  simp only [Logon.decode, encryptMethod, heartBtInt, resetSeqNumFlag, nextExpectedMsgSeqNum, username, password, newPassword, sessionStatus, defaultApplVerID, text, some_bind] <;> rfl

theorem Logon.taken (record : Logon) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [57, 56] record.encryptMethod (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 48, 56] record.heartBtInt (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [49, 52, 49] record.resetSeqNumFlag (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [55, 56, 57] record.nextExpectedMsgSeqNum (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [53, 53, 51] record.username (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [53, 53, 52] record.password (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [57, 50, 53] record.newPassword (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [49, 52, 48, 57] record.sessionStatus (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [49, 49, 51, 55] record.defaultApplVerID (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
            (paired_none pairing))))))))))

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

structure SequenceReset where
  gapFillFlag : Option (Terminated 1)  -- tag 123
  newSeqNo : Terminated 1  -- tag 36

def SequenceReset.parts (record : SequenceReset) : List Part :=
  [Part.optional [49, 50, 51] record.gapFillFlag,
   Part.required [51, 54] record.newSeqNo]

def SequenceReset.tags : List (List (List UInt8)) :=
  [[[49, 50, 51]], [[51, 54]]]

theorem SequenceReset.shape (record : SequenceReset) : record.parts.map Part.tags = SequenceReset.tags := rfl

def SequenceReset.decode (tokens : List Token) : Option SequenceReset := do
  let gapFillFlag ← readOptional [49, 50, 51] tokens
  let newSeqNo ← readRequired [51, 54] tokens
  pure { gapFillFlag, newSeqNo }

theorem SequenceReset.decode_agrees (record : SequenceReset) (tokens : List Token)
    (agrees : ∀ tags ∈ SequenceReset.tags, select tags tokens = select tags (encodeParts record.parts)) :
    SequenceReset.decode tokens = some record := by
  have distinct : SequenceReset.tags.flatten.Nodup := by decide +kernel
  have gapFillFlag := readOptional_part [49, 50, 51] record.gapFillFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have newSeqNo := readRequired_part [51, 54] record.newSeqNo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [SequenceReset.decode, gapFillFlag, newSeqNo, some_bind] <;> rfl

theorem SequenceReset.taken (record : SequenceReset) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49, 50, 51] record.gapFillFlag (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [51, 54] record.newSeqNo (by decide) (by decide))
    (paired_none pairing))

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

theorem Logout.taken (record : Logout) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49, 52, 48, 57] record.sessionStatus (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
    (paired_none pairing))

structure BusinessMessageReject where
  refSeqNum : Terminated 1  -- tag 45
  refMsgType : Terminated 1  -- tag 372
  businessRejectReason : Terminated 1  -- tag 380
  businessRejectRefID : Option (Terminated 1)  -- tag 379
  text : Option (Terminated 1)  -- tag 58

def BusinessMessageReject.parts (record : BusinessMessageReject) : List Part :=
  [Part.required [52, 53] record.refSeqNum,
   Part.required [51, 55, 50] record.refMsgType,
   Part.required [51, 56, 48] record.businessRejectReason,
   Part.optional [51, 55, 57] record.businessRejectRefID,
   Part.optional [53, 56] record.text]

def BusinessMessageReject.tags : List (List (List UInt8)) :=
  [[[52, 53]], [[51, 55, 50]], [[51, 56, 48]], [[51, 55, 57]], [[53, 56]]]

theorem BusinessMessageReject.shape (record : BusinessMessageReject) : record.parts.map Part.tags = BusinessMessageReject.tags := rfl

def BusinessMessageReject.decode (tokens : List Token) : Option BusinessMessageReject := do
  let refSeqNum ← readRequired [52, 53] tokens
  let refMsgType ← readRequired [51, 55, 50] tokens
  let businessRejectReason ← readRequired [51, 56, 48] tokens
  let businessRejectRefID ← readOptional [51, 55, 57] tokens
  let text ← readOptional [53, 56] tokens
  pure { refSeqNum, refMsgType, businessRejectReason, businessRejectRefID, text }

theorem BusinessMessageReject.decode_agrees (record : BusinessMessageReject) (tokens : List Token)
    (agrees : ∀ tags ∈ BusinessMessageReject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    BusinessMessageReject.decode tokens = some record := by
  have distinct : BusinessMessageReject.tags.flatten.Nodup := by decide +kernel
  have refSeqNum := readRequired_part [52, 53] record.refSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have refMsgType := readRequired_part [51, 55, 50] record.refMsgType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have businessRejectReason := readRequired_part [51, 56, 48] record.businessRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have businessRejectRefID := readOptional_part [51, 55, 57] record.businessRejectRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [BusinessMessageReject.decode, refSeqNum, refMsgType, businessRejectReason, businessRejectRefID, text, some_bind] <;> rfl

theorem BusinessMessageReject.taken (record : BusinessMessageReject) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [52, 53] record.refSeqNum (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [51, 55, 50] record.refMsgType (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [51, 56, 48] record.businessRejectReason (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [51, 55, 57] record.businessRejectRefID (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
       (paired_none pairing)))))

structure NoPartyIDs where
  partyID : Terminated 1  -- tag 448
  partyIDSource : Option (Terminated 1)  -- tag 447
  partyRole : Terminated 1  -- tag 452

def NoPartyIDs.parts (record : NoPartyIDs) : List Part :=
  [Part.required [52, 52, 56] record.partyID,
   Part.optional [52, 52, 55] record.partyIDSource,
   Part.required [52, 53, 50] record.partyRole]

def NoPartyIDs.tags : List (List (List UInt8)) :=
  [[[52, 52, 56]], [[52, 52, 55]], [[52, 53, 50]]]

theorem NoPartyIDs.shape (record : NoPartyIDs) : record.parts.map Part.tags = NoPartyIDs.tags := rfl

def NoPartyIDs.decode (tokens : List Token) : Option NoPartyIDs := do
  let partyID ← readRequired [52, 52, 56] tokens
  let partyIDSource ← readOptional [52, 52, 55] tokens
  let partyRole ← readRequired [52, 53, 50] tokens
  pure { partyID, partyIDSource, partyRole }

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
  simp only [NoPartyIDs.decode, partyID, partyIDSource, partyRole, some_bind] <;> rfl

theorem NoPartyIDs.taken (record : NoPartyIDs) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [52, 52, 56] record.partyID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [52, 52, 55] record.partyIDSource (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [52, 53, 50] record.partyRole (by decide) (by decide))
     (paired_none pairing)))

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

structure NoMatchInst where
  matchInst : Terminated 1  -- tag 1625
  matchAttribTagID : Option (Terminated 1)  -- tag 1626
  matchAttribValue : Option (Terminated 1)  -- tag 1627

def NoMatchInst.parts (record : NoMatchInst) : List Part :=
  [Part.required [49, 54, 50, 53] record.matchInst,
   Part.optional [49, 54, 50, 54] record.matchAttribTagID,
   Part.optional [49, 54, 50, 55] record.matchAttribValue]

def NoMatchInst.tags : List (List (List UInt8)) :=
  [[[49, 54, 50, 53]], [[49, 54, 50, 54]], [[49, 54, 50, 55]]]

theorem NoMatchInst.shape (record : NoMatchInst) : record.parts.map Part.tags = NoMatchInst.tags := rfl

def NoMatchInst.decode (tokens : List Token) : Option NoMatchInst := do
  let matchInst ← readRequired [49, 54, 50, 53] tokens
  let matchAttribTagID ← readOptional [49, 54, 50, 54] tokens
  let matchAttribValue ← readOptional [49, 54, 50, 55] tokens
  pure { matchInst, matchAttribTagID, matchAttribValue }

theorem NoMatchInst.decode_agrees (record : NoMatchInst) (tokens : List Token)
    (agrees : ∀ tags ∈ NoMatchInst.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoMatchInst.decode tokens = some record := by
  have distinct : NoMatchInst.tags.flatten.Nodup := by decide +kernel
  have matchInst := readRequired_part [49, 54, 50, 53] record.matchInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have matchAttribTagID := readOptional_part [49, 54, 50, 54] record.matchAttribTagID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have matchAttribValue := readOptional_part [49, 54, 50, 55] record.matchAttribValue tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [NoMatchInst.decode, matchInst, matchAttribTagID, matchAttribValue, some_bind] <;> rfl

theorem NoMatchInst.taken (record : NoMatchInst) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 54, 50, 53] record.matchInst (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [49, 54, 50, 54] record.matchAttribTagID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [49, 54, 50, 55] record.matchAttribValue (by decide) (by decide))
     (paired_none pairing)))

def NoMatchInst.members : List (List UInt8) := NoMatchInst.tags.flatten

def NoMatchInst.encode (entry : NoMatchInst) : List Token := encodeParts entry.parts

theorem NoMatchInst.decode_encode (entry : NoMatchInst) : NoMatchInst.decode entry.encode = some entry :=
  NoMatchInst.decode_agrees entry _ (fun _ _ => rfl)

theorem NoMatchInst.within (entry : NoMatchInst) : ∀ token ∈ entry.encode, token.tag ∈ NoMatchInst.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoMatchInst.shape] at this

theorem NoMatchInst.led (entry : NoMatchInst) : Lead [49, 54, 50, 53] entry.encode :=
  lead_parts [49, 54, 50, 53] entry.matchInst _ NoMatchInst.tags.tail rfl (by decide +kernel)

structure NoLegInstrumentParties where
  legInstrumentPartyID : Terminated 1  -- tag 2255
  legInstrumentPartyIDSource : Terminated 1  -- tag 2256
  legInstrumentPartyRole : Terminated 1  -- tag 2257

def NoLegInstrumentParties.parts (record : NoLegInstrumentParties) : List Part :=
  [Part.required [50, 50, 53, 53] record.legInstrumentPartyID,
   Part.required [50, 50, 53, 54] record.legInstrumentPartyIDSource,
   Part.required [50, 50, 53, 55] record.legInstrumentPartyRole]

def NoLegInstrumentParties.tags : List (List (List UInt8)) :=
  [[[50, 50, 53, 53]], [[50, 50, 53, 54]], [[50, 50, 53, 55]]]

theorem NoLegInstrumentParties.shape (record : NoLegInstrumentParties) : record.parts.map Part.tags = NoLegInstrumentParties.tags := rfl

def NoLegInstrumentParties.decode (tokens : List Token) : Option NoLegInstrumentParties := do
  let legInstrumentPartyID ← readRequired [50, 50, 53, 53] tokens
  let legInstrumentPartyIDSource ← readRequired [50, 50, 53, 54] tokens
  let legInstrumentPartyRole ← readRequired [50, 50, 53, 55] tokens
  pure { legInstrumentPartyID, legInstrumentPartyIDSource, legInstrumentPartyRole }

theorem NoLegInstrumentParties.decode_agrees (record : NoLegInstrumentParties) (tokens : List Token)
    (agrees : ∀ tags ∈ NoLegInstrumentParties.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoLegInstrumentParties.decode tokens = some record := by
  have distinct : NoLegInstrumentParties.tags.flatten.Nodup := by decide +kernel
  have legInstrumentPartyID := readRequired_part [50, 50, 53, 53] record.legInstrumentPartyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have legInstrumentPartyIDSource := readRequired_part [50, 50, 53, 54] record.legInstrumentPartyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have legInstrumentPartyRole := readRequired_part [50, 50, 53, 55] record.legInstrumentPartyRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [NoLegInstrumentParties.decode, legInstrumentPartyID, legInstrumentPartyIDSource, legInstrumentPartyRole, some_bind] <;> rfl

theorem NoLegInstrumentParties.taken (record : NoLegInstrumentParties) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [50, 50, 53, 53] record.legInstrumentPartyID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [50, 50, 53, 54] record.legInstrumentPartyIDSource (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [50, 50, 53, 55] record.legInstrumentPartyRole (by decide) (by decide))
     (paired_none pairing)))

def NoLegInstrumentParties.members : List (List UInt8) := NoLegInstrumentParties.tags.flatten

def NoLegInstrumentParties.encode (entry : NoLegInstrumentParties) : List Token := encodeParts entry.parts

theorem NoLegInstrumentParties.decode_encode (entry : NoLegInstrumentParties) : NoLegInstrumentParties.decode entry.encode = some entry :=
  NoLegInstrumentParties.decode_agrees entry _ (fun _ _ => rfl)

theorem NoLegInstrumentParties.within (entry : NoLegInstrumentParties) : ∀ token ∈ entry.encode, token.tag ∈ NoLegInstrumentParties.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoLegInstrumentParties.shape] at this

theorem NoLegInstrumentParties.led (entry : NoLegInstrumentParties) : Lead [50, 50, 53, 53] entry.encode :=
  lead_parts [50, 50, 53, 53] entry.legInstrumentPartyID _ NoLegInstrumentParties.tags.tail rfl (by decide +kernel)

structure NoLegs where
  legSymbol : Terminated 1  -- tag 600
  legSecurityID : Terminated 1  -- tag 602
  legSecurityIDSource : Terminated 1  -- tag 603
  legSide : Terminated 1  -- tag 624
  legPrice : Option (Terminated 1)  -- tag 566
  legID : Terminated 1  -- tag 1788
  legAllocID : Terminated 1  -- tag 1366
  legLastPx : Terminated 1  -- tag 637
  legLastQty : Terminated 1  -- tag 1418
  legCurrency : Terminated 1  -- tag 556
  legOrderQty : Terminated 1  -- tag 685
  noLegInstrumentParties : List NoLegInstrumentParties  -- tag 2254

def NoLegs.parts (record : NoLegs) : List Part :=
  [Part.required [54, 48, 48] record.legSymbol,
   Part.required [54, 48, 50] record.legSecurityID,
   Part.required [54, 48, 51] record.legSecurityIDSource,
   Part.required [54, 50, 52] record.legSide,
   Part.optional [53, 54, 54] record.legPrice,
   Part.required [49, 55, 56, 56] record.legID,
   Part.required [49, 51, 54, 54] record.legAllocID,
   Part.required [54, 51, 55] record.legLastPx,
   Part.required [49, 52, 49, 56] record.legLastQty,
   Part.required [53, 53, 54] record.legCurrency,
   Part.required [54, 56, 53] record.legOrderQty,
   Part.group [50, 50, 53, 52] NoLegInstrumentParties.members NoLegInstrumentParties.encode NoLegInstrumentParties.within record.noLegInstrumentParties]

def NoLegs.tags : List (List (List UInt8)) :=
  [[[54, 48, 48]], [[54, 48, 50]], [[54, 48, 51]], [[54, 50, 52]], [[53, 54, 54]], [[49, 55, 56, 56]], [[49, 51, 54, 54]], [[54, 51, 55]], [[49, 52, 49, 56]], [[53, 53, 54]], [[54, 56, 53]], [50, 50, 53, 52] :: NoLegInstrumentParties.members]

theorem NoLegs.shape (record : NoLegs) : record.parts.map Part.tags = NoLegs.tags := rfl

def NoLegs.decode (tokens : List Token) : Option NoLegs := do
  let legSymbol ← readRequired [54, 48, 48] tokens
  let legSecurityID ← readRequired [54, 48, 50] tokens
  let legSecurityIDSource ← readRequired [54, 48, 51] tokens
  let legSide ← readRequired [54, 50, 52] tokens
  let legPrice ← readOptional [53, 54, 54] tokens
  let legID ← readRequired [49, 55, 56, 56] tokens
  let legAllocID ← readRequired [49, 51, 54, 54] tokens
  let legLastPx ← readRequired [54, 51, 55] tokens
  let legLastQty ← readRequired [49, 52, 49, 56] tokens
  let legCurrency ← readRequired [53, 53, 54] tokens
  let legOrderQty ← readRequired [54, 56, 53] tokens
  let noLegInstrumentParties ← readGroup [50, 50, 53, 52] [50, 50, 53, 53] NoLegInstrumentParties.members NoLegInstrumentParties.decode tokens
  pure { legSymbol, legSecurityID, legSecurityIDSource, legSide, legPrice, legID, legAllocID, legLastPx, legLastQty, legCurrency, legOrderQty, noLegInstrumentParties }

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
  have legSide := readRequired_part [54, 50, 52] record.legSide tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have legPrice := readOptional_part [53, 54, 54] record.legPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have legID := readRequired_part [49, 55, 56, 56] record.legID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have legAllocID := readRequired_part [49, 51, 54, 54] record.legAllocID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have legLastPx := readRequired_part [54, 51, 55] record.legLastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have legLastQty := readRequired_part [49, 52, 49, 56] record.legLastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have legCurrency := readRequired_part [53, 53, 54] record.legCurrency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have legOrderQty := readRequired_part [54, 56, 53] record.legOrderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have noLegInstrumentParties := readGroup_part [50, 50, 53, 52] [50, 50, 53, 53] NoLegInstrumentParties.members NoLegInstrumentParties.encode NoLegInstrumentParties.within NoLegInstrumentParties.decode NoLegInstrumentParties.decode_encode NoLegInstrumentParties.led record.noLegInstrumentParties tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  simp only [NoLegs.decode, legSymbol, legSecurityID, legSecurityIDSource, legSide, legPrice, legID, legAllocID, legLastPx, legLastQty, legCurrency, legOrderQty, noLegInstrumentParties, some_bind] <;> rfl

theorem NoLegs.taken (record : NoLegs) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [54, 48, 48] record.legSymbol (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [54, 48, 50] record.legSecurityID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [54, 48, 51] record.legSecurityIDSource (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [54, 50, 52] record.legSide (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [53, 54, 54] record.legPrice (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [49, 55, 56, 56] record.legID (by decide) (by decide))
        (paired_cons pairing _ _ (paired_required pairing [49, 51, 54, 54] record.legAllocID (by decide) (by decide))
         (paired_cons pairing _ _ (paired_required pairing [54, 51, 55] record.legLastPx (by decide) (by decide))
          (paired_cons pairing _ _ (paired_required pairing [49, 52, 49, 56] record.legLastQty (by decide) (by decide))
           (paired_cons pairing _ _ (paired_required pairing [53, 53, 54] record.legCurrency (by decide) (by decide))
            (paired_cons pairing _ _ (paired_required pairing [54, 56, 53] record.legOrderQty (by decide) (by decide))
             (paired_cons pairing _ _ (paired_group pairing [50, 50, 53, 52] NoLegInstrumentParties.members NoLegInstrumentParties.encode NoLegInstrumentParties.within (by decide) (by decide) NoLegInstrumentParties.taken record.noLegInstrumentParties)
              (paired_none pairing))))))))))))

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

structure ExecutionReport where
  orderID : Terminated 1  -- tag 37
  secondaryOrderID : Option (Terminated 1)  -- tag 198
  clOrdID : Option (Terminated 1)  -- tag 11
  origClOrdID : Option (Terminated 1)  -- tag 41
  massStatusReqID : Option (Terminated 1)  -- tag 584
  totNumReports : Option (Terminated 1)  -- tag 911
  lastRptRequested : Option (Terminated 1)  -- tag 912
  execID : Terminated 1  -- tag 17
  execRefID : Option (Terminated 1)  -- tag 19
  execType : Terminated 1  -- tag 150
  ordStatus : Terminated 1  -- tag 39
  ordRejReason : Option (Terminated 1)  -- tag 103
  execRestatementReason : Option (Terminated 1)  -- tag 378
  account : Option (Terminated 1)  -- tag 1
  accountType : Option (Terminated 1)  -- tag 581
  matchType : Option (Terminated 1)  -- tag 574
  symbol : Terminated 1  -- tag 55
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22
  securityExchange : Option (Terminated 1)  -- tag 207
  lastCapacity : Option (Terminated 1)  -- tag 29
  side : Terminated 1  -- tag 54
  orderQty : Terminated 1  -- tag 38
  trdMatchID : Option (Terminated 1)  -- tag 880
  ordType : Option (Terminated 1)  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  currency : Option (Terminated 1)  -- tag 15
  timeInForce : Option (Terminated 1)  -- tag 59
  lastQty : Option (Terminated 1)  -- tag 32
  lastPx : Option (Terminated 1)  -- tag 31
  leavesQty : Terminated 1  -- tag 151
  cumQty : Terminated 1  -- tag 14
  avgPx : Terminated 1  -- tag 6
  tradeDate : Option (Terminated 1)  -- tag 75
  transactTime : Option (Terminated 1)  -- tag 60
  execInst : Option (Terminated 1)  -- tag 18
  noPartyIDs : List NoPartyIDs  -- tag 453
  aggressorIndicator : Option (Terminated 1)  -- tag 1057
  noMatchInst : List NoMatchInst  -- tag 1624
  expireDate : Option (Terminated 1)  -- tag 432
  expireTime : Option (Terminated 1)  -- tag 126
  text : Option (Terminated 1)  -- tag 58
  noLegs : List NoLegs  -- tag 555

def ExecutionReport.parts (record : ExecutionReport) : List Part :=
  [Part.required [51, 55] record.orderID,
   Part.optional [49, 57, 56] record.secondaryOrderID,
   Part.optional [49, 49] record.clOrdID,
   Part.optional [52, 49] record.origClOrdID,
   Part.optional [53, 56, 52] record.massStatusReqID,
   Part.optional [57, 49, 49] record.totNumReports,
   Part.optional [57, 49, 50] record.lastRptRequested,
   Part.required [49, 55] record.execID,
   Part.optional [49, 57] record.execRefID,
   Part.required [49, 53, 48] record.execType,
   Part.required [51, 57] record.ordStatus,
   Part.optional [49, 48, 51] record.ordRejReason,
   Part.optional [51, 55, 56] record.execRestatementReason,
   Part.optional [49] record.account,
   Part.optional [53, 56, 49] record.accountType,
   Part.optional [53, 55, 52] record.matchType,
   Part.required [53, 53] record.symbol,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource,
   Part.optional [50, 48, 55] record.securityExchange,
   Part.optional [50, 57] record.lastCapacity,
   Part.required [53, 52] record.side,
   Part.required [51, 56] record.orderQty,
   Part.optional [56, 56, 48] record.trdMatchID,
   Part.optional [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.optional [49, 53] record.currency,
   Part.optional [53, 57] record.timeInForce,
   Part.optional [51, 50] record.lastQty,
   Part.optional [51, 49] record.lastPx,
   Part.required [49, 53, 49] record.leavesQty,
   Part.required [49, 52] record.cumQty,
   Part.required [54] record.avgPx,
   Part.optional [55, 53] record.tradeDate,
   Part.optional [54, 48] record.transactTime,
   Part.optional [49, 56] record.execInst,
   Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.optional [49, 48, 53, 55] record.aggressorIndicator,
   Part.group [49, 54, 50, 52] NoMatchInst.members NoMatchInst.encode NoMatchInst.within record.noMatchInst,
   Part.optional [52, 51, 50] record.expireDate,
   Part.optional [49, 50, 54] record.expireTime,
   Part.optional [53, 56] record.text,
   Part.group [53, 53, 53] NoLegs.members NoLegs.encode NoLegs.within record.noLegs]

def ExecutionReport.tags : List (List (List UInt8)) :=
  [[[51, 55]], [[49, 57, 56]], [[49, 49]], [[52, 49]], [[53, 56, 52]], [[57, 49, 49]], [[57, 49, 50]], [[49, 55]], [[49, 57]], [[49, 53, 48]], [[51, 57]], [[49, 48, 51]], [[51, 55, 56]], [[49]], [[53, 56, 49]], [[53, 55, 52]], [[53, 53]], [[52, 56]], [[50, 50]], [[50, 48, 55]], [[50, 57]], [[53, 52]], [[51, 56]], [[56, 56, 48]], [[52, 48]], [[52, 52]], [[49, 53]], [[53, 57]], [[51, 50]], [[51, 49]], [[49, 53, 49]], [[49, 52]], [[54]], [[55, 53]], [[54, 48]], [[49, 56]], [52, 53, 51] :: NoPartyIDs.members, [[49, 48, 53, 55]], [49, 54, 50, 52] :: NoMatchInst.members, [[52, 51, 50]], [[49, 50, 54]], [[53, 56]], [53, 53, 53] :: NoLegs.members]

theorem ExecutionReport.shape (record : ExecutionReport) : record.parts.map Part.tags = ExecutionReport.tags := rfl

def ExecutionReport.decode (tokens : List Token) : Option ExecutionReport := do
  let orderID ← readRequired [51, 55] tokens
  let secondaryOrderID ← readOptional [49, 57, 56] tokens
  let clOrdID ← readOptional [49, 49] tokens
  let origClOrdID ← readOptional [52, 49] tokens
  let massStatusReqID ← readOptional [53, 56, 52] tokens
  let totNumReports ← readOptional [57, 49, 49] tokens
  let lastRptRequested ← readOptional [57, 49, 50] tokens
  let execID ← readRequired [49, 55] tokens
  let execRefID ← readOptional [49, 57] tokens
  let execType ← readRequired [49, 53, 48] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let ordRejReason ← readOptional [49, 48, 51] tokens
  let execRestatementReason ← readOptional [51, 55, 56] tokens
  let account ← readOptional [49] tokens
  let accountType ← readOptional [53, 56, 49] tokens
  let matchType ← readOptional [53, 55, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let securityExchange ← readOptional [50, 48, 55] tokens
  let lastCapacity ← readOptional [50, 57] tokens
  let side ← readRequired [53, 52] tokens
  let orderQty ← readRequired [51, 56] tokens
  let trdMatchID ← readOptional [56, 56, 48] tokens
  let ordType ← readOptional [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let currency ← readOptional [49, 53] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let lastQty ← readOptional [51, 50] tokens
  let lastPx ← readOptional [51, 49] tokens
  let leavesQty ← readRequired [49, 53, 49] tokens
  let cumQty ← readRequired [49, 52] tokens
  let avgPx ← readRequired [54] tokens
  let tradeDate ← readOptional [55, 53] tokens
  let transactTime ← readOptional [54, 48] tokens
  let execInst ← readOptional [49, 56] tokens
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let aggressorIndicator ← readOptional [49, 48, 53, 55] tokens
  let noMatchInst ← readGroup [49, 54, 50, 52] [49, 54, 50, 53] NoMatchInst.members NoMatchInst.decode tokens
  let expireDate ← readOptional [52, 51, 50] tokens
  let expireTime ← readOptional [49, 50, 54] tokens
  let text ← readOptional [53, 56] tokens
  let noLegs ← readGroup [53, 53, 53] [54, 48, 48] NoLegs.members NoLegs.decode tokens
  pure { orderID, secondaryOrderID, clOrdID, origClOrdID, massStatusReqID, totNumReports, lastRptRequested, execID, execRefID, execType, ordStatus, ordRejReason, execRestatementReason, account, accountType, matchType, symbol, securityID, securityIDSource, securityExchange, lastCapacity, side, orderQty, trdMatchID, ordType, price, currency, timeInForce, lastQty, lastPx, leavesQty, cumQty, avgPx, tradeDate, transactTime, execInst, noPartyIDs, aggressorIndicator, noMatchInst, expireDate, expireTime, text, noLegs }

theorem ExecutionReport.decode_agrees (record : ExecutionReport) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReport.decode tokens = some record := by
  have distinct : ExecutionReport.tags.flatten.Nodup := by decide +kernel
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have secondaryOrderID := readOptional_part [49, 57, 56] record.secondaryOrderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have clOrdID := readOptional_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have massStatusReqID := readOptional_part [53, 56, 52] record.massStatusReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have totNumReports := readOptional_part [57, 49, 49] record.totNumReports tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have lastRptRequested := readOptional_part [57, 49, 50] record.lastRptRequested tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have execID := readRequired_part [49, 55] record.execID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have execRefID := readOptional_part [49, 57] record.execRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have execType := readRequired_part [49, 53, 48] record.execType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have ordRejReason := readOptional_part [49, 48, 51] record.ordRejReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have execRestatementReason := readOptional_part [51, 55, 56] record.execRestatementReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have accountType := readOptional_part [53, 56, 49] record.accountType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have matchType := readOptional_part [53, 55, 52] record.matchType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have securityExchange := readOptional_part [50, 48, 55] record.securityExchange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have lastCapacity := readOptional_part [50, 57] record.lastCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have trdMatchID := readOptional_part [56, 56, 48] record.trdMatchID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have ordType := readOptional_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have currency := readOptional_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have lastQty := readOptional_part [51, 50] record.lastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have lastPx := readOptional_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have leavesQty := readRequired_part [49, 53, 49] record.leavesQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have cumQty := readRequired_part [49, 52] record.cumQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have avgPx := readRequired_part [54] record.avgPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have tradeDate := readOptional_part [55, 53] record.tradeDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have aggressorIndicator := readOptional_part [49, 48, 53, 55] record.aggressorIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have noMatchInst := readGroup_part [49, 54, 50, 52] [49, 54, 50, 53] NoMatchInst.members NoMatchInst.encode NoMatchInst.within NoMatchInst.decode NoMatchInst.decode_encode NoMatchInst.led record.noMatchInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  have expireDate := readOptional_part [52, 51, 50] record.expireDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 39 (by decide +kernel)))
  have expireTime := readOptional_part [49, 50, 54] record.expireTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 40 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 41 (by decide +kernel)))
  have noLegs := readGroup_part [53, 53, 53] [54, 48, 48] NoLegs.members NoLegs.encode NoLegs.within NoLegs.decode NoLegs.decode_encode NoLegs.led record.noLegs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 42 (by decide +kernel)))
  simp only [ExecutionReport.decode, orderID, secondaryOrderID, clOrdID, origClOrdID, massStatusReqID, totNumReports, lastRptRequested, execID, execRefID, execType, ordStatus, ordRejReason, execRestatementReason, account, accountType, matchType, symbol, securityID, securityIDSource, securityExchange, lastCapacity, side, orderQty, trdMatchID, ordType, price, currency, timeInForce, lastQty, lastPx, leavesQty, cumQty, avgPx, tradeDate, transactTime, execInst, noPartyIDs, aggressorIndicator, noMatchInst, expireDate, expireTime, text, noLegs, some_bind] <;> rfl

theorem ExecutionReport.taken (record : ExecutionReport) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 55] record.orderID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [49, 57, 56] record.secondaryOrderID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [49, 49] record.clOrdID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [52, 49] record.origClOrdID (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [53, 56, 52] record.massStatusReqID (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [57, 49, 49] record.totNumReports (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [57, 49, 50] record.lastRptRequested (by decide) (by decide))
         (paired_cons pairing _ _ (paired_required pairing [49, 55] record.execID (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [49, 57] record.execRefID (by decide) (by decide))
           (paired_cons pairing _ _ (paired_required pairing [49, 53, 48] record.execType (by decide) (by decide))
            (paired_cons pairing _ _ (paired_required pairing [51, 57] record.ordStatus (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [49, 48, 51] record.ordRejReason (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [51, 55, 56] record.execRestatementReason (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [49] record.account (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [53, 56, 49] record.accountType (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_optional pairing [53, 55, 52] record.matchType (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_optional pairing [52, 56] record.securityID (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_optional pairing [50, 50] record.securityIDSource (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_optional pairing [50, 48, 55] record.securityExchange (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_optional pairing [50, 57] record.lastCapacity (by decide) (by decide))
                       (paired_cons pairing _ _ (paired_required pairing [53, 52] record.side (by decide) (by decide))
                        (paired_cons pairing _ _ (paired_required pairing [51, 56] record.orderQty (by decide) (by decide))
                         (paired_cons pairing _ _ (paired_optional pairing [56, 56, 48] record.trdMatchID (by decide) (by decide))
                          (paired_cons pairing _ _ (paired_optional pairing [52, 48] record.ordType (by decide) (by decide))
                           (paired_cons pairing _ _ (paired_optional pairing [52, 52] record.price (by decide) (by decide))
                            (paired_cons pairing _ _ (paired_optional pairing [49, 53] record.currency (by decide) (by decide))
                             (paired_cons pairing _ _ (paired_optional pairing [53, 57] record.timeInForce (by decide) (by decide))
                              (paired_cons pairing _ _ (paired_optional pairing [51, 50] record.lastQty (by decide) (by decide))
                               (paired_cons pairing _ _ (paired_optional pairing [51, 49] record.lastPx (by decide) (by decide))
                                (paired_cons pairing _ _ (paired_required pairing [49, 53, 49] record.leavesQty (by decide) (by decide))
                                 (paired_cons pairing _ _ (paired_required pairing [49, 52] record.cumQty (by decide) (by decide))
                                  (paired_cons pairing _ _ (paired_required pairing [54] record.avgPx (by decide) (by decide))
                                   (paired_cons pairing _ _ (paired_optional pairing [55, 53] record.tradeDate (by decide) (by decide))
                                    (paired_cons pairing _ _ (paired_optional pairing [54, 48] record.transactTime (by decide) (by decide))
                                     (paired_cons pairing _ _ (paired_optional pairing [49, 56] record.execInst (by decide) (by decide))
                                      (paired_cons pairing _ _ (paired_group pairing [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within (by decide) (by decide) NoPartyIDs.taken record.noPartyIDs)
                                       (paired_cons pairing _ _ (paired_optional pairing [49, 48, 53, 55] record.aggressorIndicator (by decide) (by decide))
                                        (paired_cons pairing _ _ (paired_group pairing [49, 54, 50, 52] NoMatchInst.members NoMatchInst.encode NoMatchInst.within (by decide) (by decide) NoMatchInst.taken record.noMatchInst)
                                         (paired_cons pairing _ _ (paired_optional pairing [52, 51, 50] record.expireDate (by decide) (by decide))
                                          (paired_cons pairing _ _ (paired_optional pairing [49, 50, 54] record.expireTime (by decide) (by decide))
                                           (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
                                            (paired_cons pairing _ _ (paired_group pairing [53, 53, 53] NoLegs.members NoLegs.encode NoLegs.within (by decide) (by decide) NoLegs.taken record.noLegs)
                                             (paired_none pairing)))))))))))))))))))))))))))))))))))))))))))

structure OrderCancelReject where
  orderID : Terminated 1  -- tag 37
  secondaryOrderID : Option (Terminated 1)  -- tag 198
  clOrdID : Terminated 1  -- tag 11
  origClOrdID : Terminated 1  -- tag 41
  ordStatus : Terminated 1  -- tag 39
  cxlRejResponseTo : Terminated 1  -- tag 434
  cxlRejReason : Terminated 1  -- tag 102
  text : Terminated 1  -- tag 58
  transactTime : Terminated 1  -- tag 60

def OrderCancelReject.parts (record : OrderCancelReject) : List Part :=
  [Part.required [51, 55] record.orderID,
   Part.optional [49, 57, 56] record.secondaryOrderID,
   Part.required [49, 49] record.clOrdID,
   Part.required [52, 49] record.origClOrdID,
   Part.required [51, 57] record.ordStatus,
   Part.required [52, 51, 52] record.cxlRejResponseTo,
   Part.required [49, 48, 50] record.cxlRejReason,
   Part.required [53, 56] record.text,
   Part.required [54, 48] record.transactTime]

def OrderCancelReject.tags : List (List (List UInt8)) :=
  [[[51, 55]], [[49, 57, 56]], [[49, 49]], [[52, 49]], [[51, 57]], [[52, 51, 52]], [[49, 48, 50]], [[53, 56]], [[54, 48]]]

theorem OrderCancelReject.shape (record : OrderCancelReject) : record.parts.map Part.tags = OrderCancelReject.tags := rfl

def OrderCancelReject.decode (tokens : List Token) : Option OrderCancelReject := do
  let orderID ← readRequired [51, 55] tokens
  let secondaryOrderID ← readOptional [49, 57, 56] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let cxlRejResponseTo ← readRequired [52, 51, 52] tokens
  let cxlRejReason ← readRequired [49, 48, 50] tokens
  let text ← readRequired [53, 56] tokens
  let transactTime ← readRequired [54, 48] tokens
  pure { orderID, secondaryOrderID, clOrdID, origClOrdID, ordStatus, cxlRejResponseTo, cxlRejReason, text, transactTime }

theorem OrderCancelReject.decode_agrees (record : OrderCancelReject) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelReject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelReject.decode tokens = some record := by
  have distinct : OrderCancelReject.tags.flatten.Nodup := by decide +kernel
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have secondaryOrderID := readOptional_part [49, 57, 56] record.secondaryOrderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have cxlRejResponseTo := readRequired_part [52, 51, 52] record.cxlRejResponseTo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have cxlRejReason := readRequired_part [49, 48, 50] record.cxlRejReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have text := readRequired_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  simp only [OrderCancelReject.decode, orderID, secondaryOrderID, clOrdID, origClOrdID, ordStatus, cxlRejResponseTo, cxlRejReason, text, transactTime, some_bind] <;> rfl

theorem OrderCancelReject.taken (record : OrderCancelReject) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 55] record.orderID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [49, 57, 56] record.secondaryOrderID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [52, 49] record.origClOrdID (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [51, 57] record.ordStatus (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [52, 51, 52] record.cxlRejResponseTo (by decide) (by decide))
        (paired_cons pairing _ _ (paired_required pairing [49, 48, 50] record.cxlRejReason (by decide) (by decide))
         (paired_cons pairing _ _ (paired_required pairing [53, 56] record.text (by decide) (by decide))
          (paired_cons pairing _ _ (paired_required pairing [54, 48] record.transactTime (by decide) (by decide))
           (paired_none pairing)))))))))

structure NoRelatedSym where
  symbol : Terminated 1  -- tag 55
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22
  side : Option (Terminated 1)  -- tag 54
  orderQty : Option (Terminated 1)  -- tag 38

def NoRelatedSym.parts (record : NoRelatedSym) : List Part :=
  [Part.required [53, 53] record.symbol,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource,
   Part.optional [53, 52] record.side,
   Part.optional [51, 56] record.orderQty]

def NoRelatedSym.tags : List (List (List UInt8)) :=
  [[[53, 53]], [[52, 56]], [[50, 50]], [[53, 52]], [[51, 56]]]

theorem NoRelatedSym.shape (record : NoRelatedSym) : record.parts.map Part.tags = NoRelatedSym.tags := rfl

def NoRelatedSym.decode (tokens : List Token) : Option NoRelatedSym := do
  let symbol ← readRequired [53, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let side ← readOptional [53, 52] tokens
  let orderQty ← readOptional [51, 56] tokens
  pure { symbol, securityID, securityIDSource, side, orderQty }

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
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have orderQty := readOptional_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [NoRelatedSym.decode, symbol, securityID, securityIDSource, side, orderQty, some_bind] <;> rfl

theorem NoRelatedSym.taken (record : NoRelatedSym) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [52, 56] record.securityID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [50, 50] record.securityIDSource (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [53, 52] record.side (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [51, 56] record.orderQty (by decide) (by decide))
       (paired_none pairing)))))

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
  quoteRequestRejectReason : Terminated 1  -- tag 658
  noRelatedSym : List NoRelatedSym  -- tag 146
  text : Terminated 1  -- tag 58

def QuoteRequestReject.parts (record : QuoteRequestReject) : List Part :=
  [Part.required [49, 51, 49] record.quoteReqID,
   Part.required [54, 53, 56] record.quoteRequestRejectReason,
   Part.group [49, 52, 54] NoRelatedSym.members NoRelatedSym.encode NoRelatedSym.within record.noRelatedSym,
   Part.required [53, 56] record.text]

def QuoteRequestReject.tags : List (List (List UInt8)) :=
  [[[49, 51, 49]], [[54, 53, 56]], [49, 52, 54] :: NoRelatedSym.members, [[53, 56]]]

theorem QuoteRequestReject.shape (record : QuoteRequestReject) : record.parts.map Part.tags = QuoteRequestReject.tags := rfl

def QuoteRequestReject.decode (tokens : List Token) : Option QuoteRequestReject := do
  let quoteReqID ← readRequired [49, 51, 49] tokens
  let quoteRequestRejectReason ← readRequired [54, 53, 56] tokens
  let noRelatedSym ← readGroup [49, 52, 54] [53, 53] NoRelatedSym.members NoRelatedSym.decode tokens
  let text ← readRequired [53, 56] tokens
  pure { quoteReqID, quoteRequestRejectReason, noRelatedSym, text }

theorem QuoteRequestReject.decode_agrees (record : QuoteRequestReject) (tokens : List Token)
    (agrees : ∀ tags ∈ QuoteRequestReject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    QuoteRequestReject.decode tokens = some record := by
  have distinct : QuoteRequestReject.tags.flatten.Nodup := by decide +kernel
  have quoteReqID := readRequired_part [49, 51, 49] record.quoteReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have quoteRequestRejectReason := readRequired_part [54, 53, 56] record.quoteRequestRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have noRelatedSym := readGroup_part [49, 52, 54] [53, 53] NoRelatedSym.members NoRelatedSym.encode NoRelatedSym.within NoRelatedSym.decode NoRelatedSym.decode_encode NoRelatedSym.led record.noRelatedSym tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have text := readRequired_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [QuoteRequestReject.decode, quoteReqID, quoteRequestRejectReason, noRelatedSym, text, some_bind] <;> rfl

theorem QuoteRequestReject.taken (record : QuoteRequestReject) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 51, 49] record.quoteReqID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [54, 53, 56] record.quoteRequestRejectReason (by decide) (by decide))
    (paired_cons pairing _ _ (paired_group pairing [49, 52, 54] NoRelatedSym.members NoRelatedSym.encode NoRelatedSym.within (by decide) (by decide) NoRelatedSym.taken record.noRelatedSym)
     (paired_cons pairing _ _ (paired_required pairing [53, 56] record.text (by decide) (by decide))
      (paired_none pairing))))

structure SecurityDefinition where
  securityReqID : Terminated 1  -- tag 320
  securityResponseID : Terminated 1  -- tag 322
  securityResponseType : Terminated 1  -- tag 323
  text : Option (Terminated 1)  -- tag 58
  symbol : Terminated 1  -- tag 55
  securityID : Terminated 1  -- tag 48
  securityIDSource : Terminated 1  -- tag 22

def SecurityDefinition.parts (record : SecurityDefinition) : List Part :=
  [Part.required [51, 50, 48] record.securityReqID,
   Part.required [51, 50, 50] record.securityResponseID,
   Part.required [51, 50, 51] record.securityResponseType,
   Part.optional [53, 56] record.text,
   Part.required [53, 53] record.symbol,
   Part.required [52, 56] record.securityID,
   Part.required [50, 50] record.securityIDSource]

def SecurityDefinition.tags : List (List (List UInt8)) :=
  [[[51, 50, 48]], [[51, 50, 50]], [[51, 50, 51]], [[53, 56]], [[53, 53]], [[52, 56]], [[50, 50]]]

theorem SecurityDefinition.shape (record : SecurityDefinition) : record.parts.map Part.tags = SecurityDefinition.tags := rfl

def SecurityDefinition.decode (tokens : List Token) : Option SecurityDefinition := do
  let securityReqID ← readRequired [51, 50, 48] tokens
  let securityResponseID ← readRequired [51, 50, 50] tokens
  let securityResponseType ← readRequired [51, 50, 51] tokens
  let text ← readOptional [53, 56] tokens
  let symbol ← readRequired [53, 53] tokens
  let securityID ← readRequired [52, 56] tokens
  let securityIDSource ← readRequired [50, 50] tokens
  pure { securityReqID, securityResponseID, securityResponseType, text, symbol, securityID, securityIDSource }

theorem SecurityDefinition.decode_agrees (record : SecurityDefinition) (tokens : List Token)
    (agrees : ∀ tags ∈ SecurityDefinition.tags, select tags tokens = select tags (encodeParts record.parts)) :
    SecurityDefinition.decode tokens = some record := by
  have distinct : SecurityDefinition.tags.flatten.Nodup := by decide +kernel
  have securityReqID := readRequired_part [51, 50, 48] record.securityReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityResponseID := readRequired_part [51, 50, 50] record.securityResponseID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityResponseType := readRequired_part [51, 50, 51] record.securityResponseType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have securityID := readRequired_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have securityIDSource := readRequired_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  simp only [SecurityDefinition.decode, securityReqID, securityResponseID, securityResponseType, text, symbol, securityID, securityIDSource, some_bind] <;> rfl

theorem SecurityDefinition.taken (record : SecurityDefinition) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 50, 48] record.securityReqID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [51, 50, 50] record.securityResponseID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [51, 50, 51] record.securityResponseType (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [52, 56] record.securityID (by decide) (by decide))
        (paired_cons pairing _ _ (paired_required pairing [50, 50] record.securityIDSource (by decide) (by decide))
         (paired_none pairing)))))))

structure NoTargetPartyIDs where
  targetPartyID : Terminated 1  -- tag 1462
  targetPartyIDSource : Option (Terminated 1)  -- tag 1463
  targetPartyRole : Option (Terminated 1)  -- tag 1464

def NoTargetPartyIDs.parts (record : NoTargetPartyIDs) : List Part :=
  [Part.required [49, 52, 54, 50] record.targetPartyID,
   Part.optional [49, 52, 54, 51] record.targetPartyIDSource,
   Part.optional [49, 52, 54, 52] record.targetPartyRole]

def NoTargetPartyIDs.tags : List (List (List UInt8)) :=
  [[[49, 52, 54, 50]], [[49, 52, 54, 51]], [[49, 52, 54, 52]]]

theorem NoTargetPartyIDs.shape (record : NoTargetPartyIDs) : record.parts.map Part.tags = NoTargetPartyIDs.tags := rfl

def NoTargetPartyIDs.decode (tokens : List Token) : Option NoTargetPartyIDs := do
  let targetPartyID ← readRequired [49, 52, 54, 50] tokens
  let targetPartyIDSource ← readOptional [49, 52, 54, 51] tokens
  let targetPartyRole ← readOptional [49, 52, 54, 52] tokens
  pure { targetPartyID, targetPartyIDSource, targetPartyRole }

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
  simp only [NoTargetPartyIDs.decode, targetPartyID, targetPartyIDSource, targetPartyRole, some_bind] <;> rfl

theorem NoTargetPartyIDs.taken (record : NoTargetPartyIDs) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 52, 54, 50] record.targetPartyID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [49, 52, 54, 51] record.targetPartyIDSource (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [49, 52, 54, 52] record.targetPartyRole (by decide) (by decide))
     (paired_none pairing)))

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

structure OrderMassCancelReport where
  clOrdID : Terminated 1  -- tag 11
  massActionReportID : Terminated 1  -- tag 1369
  massCancelRequestType : Terminated 1  -- tag 530
  massCancelResponse : Terminated 1  -- tag 531
  massCancelRejectReason : Option (Terminated 1)  -- tag 532
  noTargetPartyIDs : List NoTargetPartyIDs  -- tag 1461
  text : Option (Terminated 1)  -- tag 58

def OrderMassCancelReport.parts (record : OrderMassCancelReport) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.required [49, 51, 54, 57] record.massActionReportID,
   Part.required [53, 51, 48] record.massCancelRequestType,
   Part.required [53, 51, 49] record.massCancelResponse,
   Part.optional [53, 51, 50] record.massCancelRejectReason,
   Part.group [49, 52, 54, 49] NoTargetPartyIDs.members NoTargetPartyIDs.encode NoTargetPartyIDs.within record.noTargetPartyIDs,
   Part.optional [53, 56] record.text]

def OrderMassCancelReport.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[49, 51, 54, 57]], [[53, 51, 48]], [[53, 51, 49]], [[53, 51, 50]], [49, 52, 54, 49] :: NoTargetPartyIDs.members, [[53, 56]]]

theorem OrderMassCancelReport.shape (record : OrderMassCancelReport) : record.parts.map Part.tags = OrderMassCancelReport.tags := rfl

def OrderMassCancelReport.decode (tokens : List Token) : Option OrderMassCancelReport := do
  let clOrdID ← readRequired [49, 49] tokens
  let massActionReportID ← readRequired [49, 51, 54, 57] tokens
  let massCancelRequestType ← readRequired [53, 51, 48] tokens
  let massCancelResponse ← readRequired [53, 51, 49] tokens
  let massCancelRejectReason ← readOptional [53, 51, 50] tokens
  let noTargetPartyIDs ← readGroup [49, 52, 54, 49] [49, 52, 54, 50] NoTargetPartyIDs.members NoTargetPartyIDs.decode tokens
  let text ← readOptional [53, 56] tokens
  pure { clOrdID, massActionReportID, massCancelRequestType, massCancelResponse, massCancelRejectReason, noTargetPartyIDs, text }

theorem OrderMassCancelReport.decode_agrees (record : OrderMassCancelReport) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderMassCancelReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderMassCancelReport.decode tokens = some record := by
  have distinct : OrderMassCancelReport.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have massActionReportID := readRequired_part [49, 51, 54, 57] record.massActionReportID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have massCancelRequestType := readRequired_part [53, 51, 48] record.massCancelRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have massCancelResponse := readRequired_part [53, 51, 49] record.massCancelResponse tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have massCancelRejectReason := readOptional_part [53, 51, 50] record.massCancelRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have noTargetPartyIDs := readGroup_part [49, 52, 54, 49] [49, 52, 54, 50] NoTargetPartyIDs.members NoTargetPartyIDs.encode NoTargetPartyIDs.within NoTargetPartyIDs.decode NoTargetPartyIDs.decode_encode NoTargetPartyIDs.led record.noTargetPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  simp only [OrderMassCancelReport.decode, clOrdID, massActionReportID, massCancelRequestType, massCancelResponse, massCancelRejectReason, noTargetPartyIDs, text, some_bind] <;> rfl

theorem OrderMassCancelReport.taken (record : OrderMassCancelReport) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 51, 54, 57] record.massActionReportID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [53, 51, 48] record.massCancelRequestType (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [53, 51, 49] record.massCancelResponse (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [53, 51, 50] record.massCancelRejectReason (by decide) (by decide))
       (paired_cons pairing _ _ (paired_group pairing [49, 52, 54, 49] NoTargetPartyIDs.members NoTargetPartyIDs.encode NoTargetPartyIDs.within (by decide) (by decide) NoTargetPartyIDs.taken record.noTargetPartyIDs)
        (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
         (paired_none pairing)))))))

structure NoPartyDetails where
  partyDetailID : Terminated 1  -- tag 1691
  partyDetailIDSource : Terminated 1  -- tag 1692
  partyDetailRole : Terminated 1  -- tag 1693

def NoPartyDetails.parts (record : NoPartyDetails) : List Part :=
  [Part.required [49, 54, 57, 49] record.partyDetailID,
   Part.required [49, 54, 57, 50] record.partyDetailIDSource,
   Part.required [49, 54, 57, 51] record.partyDetailRole]

def NoPartyDetails.tags : List (List (List UInt8)) :=
  [[[49, 54, 57, 49]], [[49, 54, 57, 50]], [[49, 54, 57, 51]]]

theorem NoPartyDetails.shape (record : NoPartyDetails) : record.parts.map Part.tags = NoPartyDetails.tags := rfl

def NoPartyDetails.decode (tokens : List Token) : Option NoPartyDetails := do
  let partyDetailID ← readRequired [49, 54, 57, 49] tokens
  let partyDetailIDSource ← readRequired [49, 54, 57, 50] tokens
  let partyDetailRole ← readRequired [49, 54, 57, 51] tokens
  pure { partyDetailID, partyDetailIDSource, partyDetailRole }

theorem NoPartyDetails.decode_agrees (record : NoPartyDetails) (tokens : List Token)
    (agrees : ∀ tags ∈ NoPartyDetails.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoPartyDetails.decode tokens = some record := by
  have distinct : NoPartyDetails.tags.flatten.Nodup := by decide +kernel
  have partyDetailID := readRequired_part [49, 54, 57, 49] record.partyDetailID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have partyDetailIDSource := readRequired_part [49, 54, 57, 50] record.partyDetailIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have partyDetailRole := readRequired_part [49, 54, 57, 51] record.partyDetailRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [NoPartyDetails.decode, partyDetailID, partyDetailIDSource, partyDetailRole, some_bind] <;> rfl

theorem NoPartyDetails.taken (record : NoPartyDetails) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 54, 57, 49] record.partyDetailID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 54, 57, 50] record.partyDetailIDSource (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [49, 54, 57, 51] record.partyDetailRole (by decide) (by decide))
     (paired_none pairing)))

def NoPartyDetails.members : List (List UInt8) := NoPartyDetails.tags.flatten

def NoPartyDetails.encode (entry : NoPartyDetails) : List Token := encodeParts entry.parts

theorem NoPartyDetails.decode_encode (entry : NoPartyDetails) : NoPartyDetails.decode entry.encode = some entry :=
  NoPartyDetails.decode_agrees entry _ (fun _ _ => rfl)

theorem NoPartyDetails.within (entry : NoPartyDetails) : ∀ token ∈ entry.encode, token.tag ∈ NoPartyDetails.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoPartyDetails.shape] at this

theorem NoPartyDetails.led (entry : NoPartyDetails) : Lead [49, 54, 57, 49] entry.encode :=
  lead_parts [49, 54, 57, 49] entry.partyDetailID _ NoPartyDetails.tags.tail rfl (by decide +kernel)

structure NoRiskWarningLevel where
  riskWarningLevelAction : Terminated 1  -- tag 1769
  riskWarningLevelPercent : Terminated 1  -- tag 1560

def NoRiskWarningLevel.parts (record : NoRiskWarningLevel) : List Part :=
  [Part.required [49, 55, 54, 57] record.riskWarningLevelAction,
   Part.required [49, 53, 54, 48] record.riskWarningLevelPercent]

def NoRiskWarningLevel.tags : List (List (List UInt8)) :=
  [[[49, 55, 54, 57]], [[49, 53, 54, 48]]]

theorem NoRiskWarningLevel.shape (record : NoRiskWarningLevel) : record.parts.map Part.tags = NoRiskWarningLevel.tags := rfl

def NoRiskWarningLevel.decode (tokens : List Token) : Option NoRiskWarningLevel := do
  let riskWarningLevelAction ← readRequired [49, 55, 54, 57] tokens
  let riskWarningLevelPercent ← readRequired [49, 53, 54, 48] tokens
  pure { riskWarningLevelAction, riskWarningLevelPercent }

theorem NoRiskWarningLevel.decode_agrees (record : NoRiskWarningLevel) (tokens : List Token)
    (agrees : ∀ tags ∈ NoRiskWarningLevel.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoRiskWarningLevel.decode tokens = some record := by
  have distinct : NoRiskWarningLevel.tags.flatten.Nodup := by decide +kernel
  have riskWarningLevelAction := readRequired_part [49, 55, 54, 57] record.riskWarningLevelAction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have riskWarningLevelPercent := readRequired_part [49, 53, 54, 48] record.riskWarningLevelPercent tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [NoRiskWarningLevel.decode, riskWarningLevelAction, riskWarningLevelPercent, some_bind] <;> rfl

theorem NoRiskWarningLevel.taken (record : NoRiskWarningLevel) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 55, 54, 57] record.riskWarningLevelAction (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 53, 54, 48] record.riskWarningLevelPercent (by decide) (by decide))
    (paired_none pairing))

def NoRiskWarningLevel.members : List (List UInt8) := NoRiskWarningLevel.tags.flatten

def NoRiskWarningLevel.encode (entry : NoRiskWarningLevel) : List Token := encodeParts entry.parts

theorem NoRiskWarningLevel.decode_encode (entry : NoRiskWarningLevel) : NoRiskWarningLevel.decode entry.encode = some entry :=
  NoRiskWarningLevel.decode_agrees entry _ (fun _ _ => rfl)

theorem NoRiskWarningLevel.within (entry : NoRiskWarningLevel) : ∀ token ∈ entry.encode, token.tag ∈ NoRiskWarningLevel.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoRiskWarningLevel.shape] at this

theorem NoRiskWarningLevel.led (entry : NoRiskWarningLevel) : Lead [49, 55, 54, 57] entry.encode :=
  lead_parts [49, 55, 54, 57] entry.riskWarningLevelAction _ NoRiskWarningLevel.tags.tail rfl (by decide +kernel)

structure NoRiskLimitTypes where
  riskLimitType : Terminated 1  -- tag 1530
  riskLimitUtilizationPercent : Terminated 1  -- tag 1765
  riskLimitAction : Terminated 1  -- tag 1767
  noRiskWarningLevel : List NoRiskWarningLevel  -- tag 1559

def NoRiskLimitTypes.parts (record : NoRiskLimitTypes) : List Part :=
  [Part.required [49, 53, 51, 48] record.riskLimitType,
   Part.required [49, 55, 54, 53] record.riskLimitUtilizationPercent,
   Part.required [49, 55, 54, 55] record.riskLimitAction,
   Part.group [49, 53, 53, 57] NoRiskWarningLevel.members NoRiskWarningLevel.encode NoRiskWarningLevel.within record.noRiskWarningLevel]

def NoRiskLimitTypes.tags : List (List (List UInt8)) :=
  [[[49, 53, 51, 48]], [[49, 55, 54, 53]], [[49, 55, 54, 55]], [49, 53, 53, 57] :: NoRiskWarningLevel.members]

theorem NoRiskLimitTypes.shape (record : NoRiskLimitTypes) : record.parts.map Part.tags = NoRiskLimitTypes.tags := rfl

def NoRiskLimitTypes.decode (tokens : List Token) : Option NoRiskLimitTypes := do
  let riskLimitType ← readRequired [49, 53, 51, 48] tokens
  let riskLimitUtilizationPercent ← readRequired [49, 55, 54, 53] tokens
  let riskLimitAction ← readRequired [49, 55, 54, 55] tokens
  let noRiskWarningLevel ← readGroup [49, 53, 53, 57] [49, 55, 54, 57] NoRiskWarningLevel.members NoRiskWarningLevel.decode tokens
  pure { riskLimitType, riskLimitUtilizationPercent, riskLimitAction, noRiskWarningLevel }

theorem NoRiskLimitTypes.decode_agrees (record : NoRiskLimitTypes) (tokens : List Token)
    (agrees : ∀ tags ∈ NoRiskLimitTypes.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoRiskLimitTypes.decode tokens = some record := by
  have distinct : NoRiskLimitTypes.tags.flatten.Nodup := by decide +kernel
  have riskLimitType := readRequired_part [49, 53, 51, 48] record.riskLimitType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have riskLimitUtilizationPercent := readRequired_part [49, 55, 54, 53] record.riskLimitUtilizationPercent tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have riskLimitAction := readRequired_part [49, 55, 54, 55] record.riskLimitAction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have noRiskWarningLevel := readGroup_part [49, 53, 53, 57] [49, 55, 54, 57] NoRiskWarningLevel.members NoRiskWarningLevel.encode NoRiskWarningLevel.within NoRiskWarningLevel.decode NoRiskWarningLevel.decode_encode NoRiskWarningLevel.led record.noRiskWarningLevel tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [NoRiskLimitTypes.decode, riskLimitType, riskLimitUtilizationPercent, riskLimitAction, noRiskWarningLevel, some_bind] <;> rfl

theorem NoRiskLimitTypes.taken (record : NoRiskLimitTypes) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 53, 51, 48] record.riskLimitType (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 55, 54, 53] record.riskLimitUtilizationPercent (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [49, 55, 54, 55] record.riskLimitAction (by decide) (by decide))
     (paired_cons pairing _ _ (paired_group pairing [49, 53, 53, 57] NoRiskWarningLevel.members NoRiskWarningLevel.encode NoRiskWarningLevel.within (by decide) (by decide) NoRiskWarningLevel.taken record.noRiskWarningLevel)
      (paired_none pairing))))

def NoRiskLimitTypes.members : List (List UInt8) := NoRiskLimitTypes.tags.flatten

def NoRiskLimitTypes.encode (entry : NoRiskLimitTypes) : List Token := encodeParts entry.parts

theorem NoRiskLimitTypes.decode_encode (entry : NoRiskLimitTypes) : NoRiskLimitTypes.decode entry.encode = some entry :=
  NoRiskLimitTypes.decode_agrees entry _ (fun _ _ => rfl)

theorem NoRiskLimitTypes.within (entry : NoRiskLimitTypes) : ∀ token ∈ entry.encode, token.tag ∈ NoRiskLimitTypes.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoRiskLimitTypes.shape] at this

theorem NoRiskLimitTypes.led (entry : NoRiskLimitTypes) : Lead [49, 53, 51, 48] entry.encode :=
  lead_parts [49, 53, 51, 48] entry.riskLimitType _ NoRiskLimitTypes.tags.tail rfl (by decide +kernel)

structure NoRiskInstrumentScopes where
  instrumentScopeOperator : Terminated 1  -- tag 1535
  instrumentScopeSecurityGroup : Terminated 1  -- tag 1545
  instrumentScopeSecurityExchange : Option (Terminated 1)  -- tag 1616

def NoRiskInstrumentScopes.parts (record : NoRiskInstrumentScopes) : List Part :=
  [Part.required [49, 53, 51, 53] record.instrumentScopeOperator,
   Part.required [49, 53, 52, 53] record.instrumentScopeSecurityGroup,
   Part.optional [49, 54, 49, 54] record.instrumentScopeSecurityExchange]

def NoRiskInstrumentScopes.tags : List (List (List UInt8)) :=
  [[[49, 53, 51, 53]], [[49, 53, 52, 53]], [[49, 54, 49, 54]]]

theorem NoRiskInstrumentScopes.shape (record : NoRiskInstrumentScopes) : record.parts.map Part.tags = NoRiskInstrumentScopes.tags := rfl

def NoRiskInstrumentScopes.decode (tokens : List Token) : Option NoRiskInstrumentScopes := do
  let instrumentScopeOperator ← readRequired [49, 53, 51, 53] tokens
  let instrumentScopeSecurityGroup ← readRequired [49, 53, 52, 53] tokens
  let instrumentScopeSecurityExchange ← readOptional [49, 54, 49, 54] tokens
  pure { instrumentScopeOperator, instrumentScopeSecurityGroup, instrumentScopeSecurityExchange }

theorem NoRiskInstrumentScopes.decode_agrees (record : NoRiskInstrumentScopes) (tokens : List Token)
    (agrees : ∀ tags ∈ NoRiskInstrumentScopes.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoRiskInstrumentScopes.decode tokens = some record := by
  have distinct : NoRiskInstrumentScopes.tags.flatten.Nodup := by decide +kernel
  have instrumentScopeOperator := readRequired_part [49, 53, 51, 53] record.instrumentScopeOperator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have instrumentScopeSecurityGroup := readRequired_part [49, 53, 52, 53] record.instrumentScopeSecurityGroup tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have instrumentScopeSecurityExchange := readOptional_part [49, 54, 49, 54] record.instrumentScopeSecurityExchange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [NoRiskInstrumentScopes.decode, instrumentScopeOperator, instrumentScopeSecurityGroup, instrumentScopeSecurityExchange, some_bind] <;> rfl

theorem NoRiskInstrumentScopes.taken (record : NoRiskInstrumentScopes) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 53, 51, 53] record.instrumentScopeOperator (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 53, 52, 53] record.instrumentScopeSecurityGroup (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [49, 54, 49, 54] record.instrumentScopeSecurityExchange (by decide) (by decide))
     (paired_none pairing)))

def NoRiskInstrumentScopes.members : List (List UInt8) := NoRiskInstrumentScopes.tags.flatten

def NoRiskInstrumentScopes.encode (entry : NoRiskInstrumentScopes) : List Token := encodeParts entry.parts

theorem NoRiskInstrumentScopes.decode_encode (entry : NoRiskInstrumentScopes) : NoRiskInstrumentScopes.decode entry.encode = some entry :=
  NoRiskInstrumentScopes.decode_agrees entry _ (fun _ _ => rfl)

theorem NoRiskInstrumentScopes.within (entry : NoRiskInstrumentScopes) : ∀ token ∈ entry.encode, token.tag ∈ NoRiskInstrumentScopes.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoRiskInstrumentScopes.shape] at this

theorem NoRiskInstrumentScopes.led (entry : NoRiskInstrumentScopes) : Lead [49, 53, 51, 53] entry.encode :=
  lead_parts [49, 53, 51, 53] entry.instrumentScopeOperator _ NoRiskInstrumentScopes.tags.tail rfl (by decide +kernel)

structure NoRiskLimits where
  noRiskLimitTypes : List NoRiskLimitTypes  -- tag 1529
  noRiskInstrumentScopes : List NoRiskInstrumentScopes  -- tag 1534

def NoRiskLimits.parts (record : NoRiskLimits) : List Part :=
  [Part.groupLed [49, 53, 50, 57] NoRiskLimitTypes.members NoRiskLimitTypes.encode NoRiskLimitTypes.within record.noRiskLimitTypes,
   Part.group [49, 53, 51, 52] NoRiskInstrumentScopes.members NoRiskInstrumentScopes.encode NoRiskInstrumentScopes.within record.noRiskInstrumentScopes]

def NoRiskLimits.tags : List (List (List UInt8)) :=
  [[49, 53, 50, 57] :: NoRiskLimitTypes.members, [49, 53, 51, 52] :: NoRiskInstrumentScopes.members]

theorem NoRiskLimits.shape (record : NoRiskLimits) : record.parts.map Part.tags = NoRiskLimits.tags := rfl

def NoRiskLimits.decode (tokens : List Token) : Option NoRiskLimits := do
  let noRiskLimitTypes ← readGroup [49, 53, 50, 57] [49, 53, 51, 48] NoRiskLimitTypes.members NoRiskLimitTypes.decode tokens
  let noRiskInstrumentScopes ← readGroup [49, 53, 51, 52] [49, 53, 51, 53] NoRiskInstrumentScopes.members NoRiskInstrumentScopes.decode tokens
  pure { noRiskLimitTypes, noRiskInstrumentScopes }

theorem NoRiskLimits.decode_agrees (record : NoRiskLimits) (tokens : List Token)
    (agrees : ∀ tags ∈ NoRiskLimits.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoRiskLimits.decode tokens = some record := by
  have distinct : NoRiskLimits.tags.flatten.Nodup := by decide +kernel
  have noRiskLimitTypes := readGroup_partLed [49, 53, 50, 57] [49, 53, 51, 48] NoRiskLimitTypes.members NoRiskLimitTypes.encode NoRiskLimitTypes.within NoRiskLimitTypes.decode NoRiskLimitTypes.decode_encode NoRiskLimitTypes.led record.noRiskLimitTypes tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have noRiskInstrumentScopes := readGroup_part [49, 53, 51, 52] [49, 53, 51, 53] NoRiskInstrumentScopes.members NoRiskInstrumentScopes.encode NoRiskInstrumentScopes.within NoRiskInstrumentScopes.decode NoRiskInstrumentScopes.decode_encode NoRiskInstrumentScopes.led record.noRiskInstrumentScopes tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [NoRiskLimits.decode, noRiskLimitTypes, noRiskInstrumentScopes, some_bind] <;> rfl

theorem NoRiskLimits.taken (record : NoRiskLimits) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_groupLed pairing [49, 53, 50, 57] NoRiskLimitTypes.members NoRiskLimitTypes.encode NoRiskLimitTypes.within (by decide) (by decide) NoRiskLimitTypes.taken record.noRiskLimitTypes)
   (paired_cons pairing _ _ (paired_group pairing [49, 53, 51, 52] NoRiskInstrumentScopes.members NoRiskInstrumentScopes.encode NoRiskInstrumentScopes.within (by decide) (by decide) NoRiskInstrumentScopes.taken record.noRiskInstrumentScopes)
    (paired_none pairing))

def NoRiskLimits.members : List (List UInt8) := NoRiskLimits.tags.flatten

def NoRiskLimits.encode (entry : NoRiskLimits) : List Token := encodeParts entry.parts

theorem NoRiskLimits.decode_encode (entry : NoRiskLimits) : NoRiskLimits.decode entry.encode = some entry :=
  NoRiskLimits.decode_agrees entry _ (fun _ _ => rfl)

theorem NoRiskLimits.within (entry : NoRiskLimits) : ∀ token ∈ entry.encode, token.tag ∈ NoRiskLimits.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoRiskLimits.shape] at this

theorem NoRiskLimits.led (entry : NoRiskLimits) : Lead [49, 53, 50, 57] entry.encode :=
  lead_groupLed [49, 53, 50, 57] NoRiskLimitTypes.members NoRiskLimitTypes.encode NoRiskLimitTypes.within entry.noRiskLimitTypes _ NoRiskLimits.tags.tail rfl (by decide +kernel) (by decide +kernel)

structure NoPartyRiskLimits where
  noPartyDetails : List NoPartyDetails  -- tag 1671
  noRiskLimits : List NoRiskLimits  -- tag 1669

def NoPartyRiskLimits.parts (record : NoPartyRiskLimits) : List Part :=
  [Part.groupLed [49, 54, 55, 49] NoPartyDetails.members NoPartyDetails.encode NoPartyDetails.within record.noPartyDetails,
   Part.group [49, 54, 54, 57] NoRiskLimits.members NoRiskLimits.encode NoRiskLimits.within record.noRiskLimits]

def NoPartyRiskLimits.tags : List (List (List UInt8)) :=
  [[49, 54, 55, 49] :: NoPartyDetails.members, [49, 54, 54, 57] :: NoRiskLimits.members]

theorem NoPartyRiskLimits.shape (record : NoPartyRiskLimits) : record.parts.map Part.tags = NoPartyRiskLimits.tags := rfl

def NoPartyRiskLimits.decode (tokens : List Token) : Option NoPartyRiskLimits := do
  let noPartyDetails ← readGroup [49, 54, 55, 49] [49, 54, 57, 49] NoPartyDetails.members NoPartyDetails.decode tokens
  let noRiskLimits ← readGroup [49, 54, 54, 57] [49, 53, 50, 57] NoRiskLimits.members NoRiskLimits.decode tokens
  pure { noPartyDetails, noRiskLimits }

theorem NoPartyRiskLimits.decode_agrees (record : NoPartyRiskLimits) (tokens : List Token)
    (agrees : ∀ tags ∈ NoPartyRiskLimits.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoPartyRiskLimits.decode tokens = some record := by
  have distinct : NoPartyRiskLimits.tags.flatten.Nodup := by decide +kernel
  have noPartyDetails := readGroup_partLed [49, 54, 55, 49] [49, 54, 57, 49] NoPartyDetails.members NoPartyDetails.encode NoPartyDetails.within NoPartyDetails.decode NoPartyDetails.decode_encode NoPartyDetails.led record.noPartyDetails tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have noRiskLimits := readGroup_part [49, 54, 54, 57] [49, 53, 50, 57] NoRiskLimits.members NoRiskLimits.encode NoRiskLimits.within NoRiskLimits.decode NoRiskLimits.decode_encode NoRiskLimits.led record.noRiskLimits tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [NoPartyRiskLimits.decode, noPartyDetails, noRiskLimits, some_bind] <;> rfl

theorem NoPartyRiskLimits.taken (record : NoPartyRiskLimits) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_groupLed pairing [49, 54, 55, 49] NoPartyDetails.members NoPartyDetails.encode NoPartyDetails.within (by decide) (by decide) NoPartyDetails.taken record.noPartyDetails)
   (paired_cons pairing _ _ (paired_group pairing [49, 54, 54, 57] NoRiskLimits.members NoRiskLimits.encode NoRiskLimits.within (by decide) (by decide) NoRiskLimits.taken record.noRiskLimits)
    (paired_none pairing))

def NoPartyRiskLimits.members : List (List UInt8) := NoPartyRiskLimits.tags.flatten

def NoPartyRiskLimits.encode (entry : NoPartyRiskLimits) : List Token := encodeParts entry.parts

theorem NoPartyRiskLimits.decode_encode (entry : NoPartyRiskLimits) : NoPartyRiskLimits.decode entry.encode = some entry :=
  NoPartyRiskLimits.decode_agrees entry _ (fun _ _ => rfl)

theorem NoPartyRiskLimits.within (entry : NoPartyRiskLimits) : ∀ token ∈ entry.encode, token.tag ∈ NoPartyRiskLimits.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoPartyRiskLimits.shape] at this

theorem NoPartyRiskLimits.led (entry : NoPartyRiskLimits) : Lead [49, 54, 55, 49] entry.encode :=
  lead_groupLed [49, 54, 55, 49] NoPartyDetails.members NoPartyDetails.encode NoPartyDetails.within entry.noPartyDetails _ NoPartyRiskLimits.tags.tail rfl (by decide +kernel) (by decide +kernel)

structure PartyRiskLimitsReport where
  riskLimitReportID : Terminated 1  -- tag 1667
  transactTime : Terminated 1  -- tag 60
  text : Terminated 1  -- tag 58
  noPartyRiskLimits : List NoPartyRiskLimits  -- tag 1677

def PartyRiskLimitsReport.parts (record : PartyRiskLimitsReport) : List Part :=
  [Part.required [49, 54, 54, 55] record.riskLimitReportID,
   Part.required [54, 48] record.transactTime,
   Part.required [53, 56] record.text,
   Part.group [49, 54, 55, 55] NoPartyRiskLimits.members NoPartyRiskLimits.encode NoPartyRiskLimits.within record.noPartyRiskLimits]

def PartyRiskLimitsReport.tags : List (List (List UInt8)) :=
  [[[49, 54, 54, 55]], [[54, 48]], [[53, 56]], [49, 54, 55, 55] :: NoPartyRiskLimits.members]

theorem PartyRiskLimitsReport.shape (record : PartyRiskLimitsReport) : record.parts.map Part.tags = PartyRiskLimitsReport.tags := rfl

def PartyRiskLimitsReport.decode (tokens : List Token) : Option PartyRiskLimitsReport := do
  let riskLimitReportID ← readRequired [49, 54, 54, 55] tokens
  let transactTime ← readRequired [54, 48] tokens
  let text ← readRequired [53, 56] tokens
  let noPartyRiskLimits ← readGroup [49, 54, 55, 55] [49, 54, 55, 49] NoPartyRiskLimits.members NoPartyRiskLimits.decode tokens
  pure { riskLimitReportID, transactTime, text, noPartyRiskLimits }

theorem PartyRiskLimitsReport.decode_agrees (record : PartyRiskLimitsReport) (tokens : List Token)
    (agrees : ∀ tags ∈ PartyRiskLimitsReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    PartyRiskLimitsReport.decode tokens = some record := by
  have distinct : PartyRiskLimitsReport.tags.flatten.Nodup := by decide +kernel
  have riskLimitReportID := readRequired_part [49, 54, 54, 55] record.riskLimitReportID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have text := readRequired_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have noPartyRiskLimits := readGroup_part [49, 54, 55, 55] [49, 54, 55, 49] NoPartyRiskLimits.members NoPartyRiskLimits.encode NoPartyRiskLimits.within NoPartyRiskLimits.decode NoPartyRiskLimits.decode_encode NoPartyRiskLimits.led record.noPartyRiskLimits tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [PartyRiskLimitsReport.decode, riskLimitReportID, transactTime, text, noPartyRiskLimits, some_bind] <;> rfl

theorem PartyRiskLimitsReport.taken (record : PartyRiskLimitsReport) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 54, 54, 55] record.riskLimitReportID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [54, 48] record.transactTime (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [53, 56] record.text (by decide) (by decide))
     (paired_cons pairing _ _ (paired_group pairing [49, 54, 55, 55] NoPartyRiskLimits.members NoPartyRiskLimits.encode NoPartyRiskLimits.within (by decide) (by decide) NoPartyRiskLimits.taken record.noPartyRiskLimits)
      (paired_none pairing))))

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

theorem NoLinesOfText.taken (record : NoLinesOfText) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [53, 56] record.text (by decide) (by decide))
   (paired_none pairing)

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

structure News where
  headline : Terminated 1  -- tag 148
  origTime : Terminated 1  -- tag 42
  noLinesOfText : List NoLinesOfText  -- tag 33

def News.parts (record : News) : List Part :=
  [Part.required [49, 52, 56] record.headline,
   Part.required [52, 50] record.origTime,
   Part.group [51, 51] NoLinesOfText.members NoLinesOfText.encode NoLinesOfText.within record.noLinesOfText]

def News.tags : List (List (List UInt8)) :=
  [[[49, 52, 56]], [[52, 50]], [51, 51] :: NoLinesOfText.members]

theorem News.shape (record : News) : record.parts.map Part.tags = News.tags := rfl

def News.decode (tokens : List Token) : Option News := do
  let headline ← readRequired [49, 52, 56] tokens
  let origTime ← readRequired [52, 50] tokens
  let noLinesOfText ← readGroup [51, 51] [53, 56] NoLinesOfText.members NoLinesOfText.decode tokens
  pure { headline, origTime, noLinesOfText }

theorem News.decode_agrees (record : News) (tokens : List Token)
    (agrees : ∀ tags ∈ News.tags, select tags tokens = select tags (encodeParts record.parts)) :
    News.decode tokens = some record := by
  have distinct : News.tags.flatten.Nodup := by decide +kernel
  have headline := readRequired_part [49, 52, 56] record.headline tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have origTime := readRequired_part [52, 50] record.origTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have noLinesOfText := readGroup_part [51, 51] [53, 56] NoLinesOfText.members NoLinesOfText.encode NoLinesOfText.within NoLinesOfText.decode NoLinesOfText.decode_encode NoLinesOfText.led record.noLinesOfText tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [News.decode, headline, origTime, noLinesOfText, some_bind] <;> rfl

theorem News.taken (record : News) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 52, 56] record.headline (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [52, 50] record.origTime (by decide) (by decide))
    (paired_cons pairing _ _ (paired_group pairing [51, 51] NoLinesOfText.members NoLinesOfText.encode NoLinesOfText.within (by decide) (by decide) NoLinesOfText.taken record.noLinesOfText)
     (paired_none pairing)))

inductive Message where
  | logon (header : Header) (r0 : Logon)
  | heartbeat (header : Header) (r0 : Heartbeat)
  | testRequest (header : Header) (r0 : TestRequest)
  | resendRequest (header : Header) (r0 : ResendRequest)
  | reject (header : Header) (r0 : Reject)
  | sequenceReset (header : Header) (r0 : SequenceReset)
  | logout (header : Header) (r0 : Logout)
  | businessMessageReject (header : Header) (r0 : BusinessMessageReject)
  | executionReport (header : Header) (r0 : ExecutionReport)
  | orderCancelReject (header : Header) (r0 : OrderCancelReject)
  | quoteRequestReject (header : Header) (r0 : QuoteRequestReject)
  | securityDefinition (header : Header) (r0 : SecurityDefinition)
  | orderMassCancelReport (header : Header) (r0 : OrderMassCancelReport)
  | partyRiskLimitsReport (header : Header) (r0 : PartyRiskLimitsReport)
  | news (header : Header) (r0 : News)

def Message.tokens : Message → List Token
  | .logon header r0 => ⟨[51, 53], [65]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .heartbeat header r0 => ⟨[51, 53], [48]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .testRequest header r0 => ⟨[51, 53], [49]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .resendRequest header r0 => ⟨[51, 53], [50]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .reject header r0 => ⟨[51, 53], [51]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .sequenceReset header r0 => ⟨[51, 53], [52]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logout header r0 => ⟨[51, 53], [53]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .businessMessageReject header r0 => ⟨[51, 53], [106]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .executionReport header r0 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelReject header r0 => ⟨[51, 53], [57]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .quoteRequestReject header r0 => ⟨[51, 53], [65, 71]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .securityDefinition header r0 => ⟨[51, 53], [100]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderMassCancelReport header r0 => ⟨[51, 53], [114]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .partyRiskLimitsReport header r0 => ⟨[51, 53], [67, 77]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .news header r0 => ⟨[51, 53], [66]⟩ :: encodeParts (header.parts ++ r0.parts)

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
        if known (Header.tags ++ SequenceReset.tags) rest then do
          let header ← Header.decode rest
          let r0 ← SequenceReset.decode rest
          pure (.sequenceReset header r0)
        else none
      else if token.value = [53] then
        if known (Header.tags ++ Logout.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Logout.decode rest
          pure (.logout header r0)
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
      else if token.value = [65, 71] then
        if known (Header.tags ++ QuoteRequestReject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← QuoteRequestReject.decode rest
          pure (.quoteRequestReject header r0)
        else none
      else if token.value = [100] then
        if known (Header.tags ++ SecurityDefinition.tags) rest then do
          let header ← Header.decode rest
          let r0 ← SecurityDefinition.decode rest
          pure (.securityDefinition header r0)
        else none
      else if token.value = [114] then
        if known (Header.tags ++ OrderMassCancelReport.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderMassCancelReport.decode rest
          pure (.orderMassCancelReport header r0)
        else none
      else if token.value = [67, 77] then
        if known (Header.tags ++ PartyRiskLimitsReport.tags) rest then do
          let header ← Header.decode rest
          let r0 ← PartyRiskLimitsReport.decode rest
          pure (.partyRiskLimitsReport header r0)
        else none
      else if token.value = [66] then
        if known (Header.tags ++ News.tags) rest then do
          let header ← Header.decode rest
          let r0 ← News.decode rest
          pure (.news header r0)
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

theorem Message.decode_logout (header : Header) (r0 : Logout) :
    Message.decode (Message.tokens (.logout header r0)) = some (.logout header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (Logout.tags) rfl rfl (by decide +kernel))
  have c1 := Logout.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (Logout.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ Logout.tags) rfl
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

theorem Message.decode_quoteRequestReject (header : Header) (r0 : QuoteRequestReject) :
    Message.decode (Message.tokens (.quoteRequestReject header r0)) = some (.quoteRequestReject header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (QuoteRequestReject.tags) rfl rfl (by decide +kernel))
  have c1 := QuoteRequestReject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (QuoteRequestReject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ QuoteRequestReject.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_securityDefinition (header : Header) (r0 : SecurityDefinition) :
    Message.decode (Message.tokens (.securityDefinition header r0)) = some (.securityDefinition header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (SecurityDefinition.tags) rfl rfl (by decide +kernel))
  have c1 := SecurityDefinition.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (SecurityDefinition.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ SecurityDefinition.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_orderMassCancelReport (header : Header) (r0 : OrderMassCancelReport) :
    Message.decode (Message.tokens (.orderMassCancelReport header r0)) = some (.orderMassCancelReport header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderMassCancelReport.tags) rfl rfl (by decide +kernel))
  have c1 := OrderMassCancelReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderMassCancelReport.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderMassCancelReport.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_partyRiskLimitsReport (header : Header) (r0 : PartyRiskLimitsReport) :
    Message.decode (Message.tokens (.partyRiskLimitsReport header r0)) = some (.partyRiskLimitsReport header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (PartyRiskLimitsReport.tags) rfl rfl (by decide +kernel))
  have c1 := PartyRiskLimitsReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (PartyRiskLimitsReport.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ PartyRiskLimitsReport.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_news (header : Header) (r0 : News) :
    Message.decode (Message.tokens (.news header r0)) = some (.news header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (News.tags) rfl rfl (by decide +kernel))
  have c1 := News.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (News.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ News.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | logon header r0 => exact Message.decode_logon header r0
  | heartbeat header r0 => exact Message.decode_heartbeat header r0
  | testRequest header r0 => exact Message.decode_testRequest header r0
  | resendRequest header r0 => exact Message.decode_resendRequest header r0
  | reject header r0 => exact Message.decode_reject header r0
  | sequenceReset header r0 => exact Message.decode_sequenceReset header r0
  | logout header r0 => exact Message.decode_logout header r0
  | businessMessageReject header r0 => exact Message.decode_businessMessageReject header r0
  | executionReport header r0 => exact Message.decode_executionReport header r0
  | orderCancelReject header r0 => exact Message.decode_orderCancelReject header r0
  | quoteRequestReject header r0 => exact Message.decode_quoteRequestReject header r0
  | securityDefinition header r0 => exact Message.decode_securityDefinition header r0
  | orderMassCancelReport header r0 => exact Message.decode_orderMassCancelReport header r0
  | partyRiskLimitsReport header r0 => exact Message.decode_partyRiskLimitsReport header r0
  | news header r0 => exact Message.decode_news header r0

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

theorem Message.decodeBytes_sequenceReset (header : Header) (r0 : SequenceReset) :
    Message.decodeBytes (Message.encode (.sequenceReset header r0)) = some (.sequenceReset header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [52]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (SequenceReset.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_sequenceReset header r0

theorem Message.decodeBytes_logout (header : Header) (r0 : Logout) :
    Message.decodeBytes (Message.encode (.logout header r0)) = some (.logout header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [53]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (Logout.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_logout header r0

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

theorem Message.decodeBytes_quoteRequestReject (header : Header) (r0 : QuoteRequestReject) :
    Message.decodeBytes (Message.encode (.quoteRequestReject header r0)) = some (.quoteRequestReject header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [65, 71]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (QuoteRequestReject.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_quoteRequestReject header r0

theorem Message.decodeBytes_securityDefinition (header : Header) (r0 : SecurityDefinition) :
    Message.decodeBytes (Message.encode (.securityDefinition header r0)) = some (.securityDefinition header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [100]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (SecurityDefinition.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_securityDefinition header r0

theorem Message.decodeBytes_orderMassCancelReport (header : Header) (r0 : OrderMassCancelReport) :
    Message.decodeBytes (Message.encode (.orderMassCancelReport header r0)) = some (.orderMassCancelReport header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [114]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (OrderMassCancelReport.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderMassCancelReport header r0

theorem Message.decodeBytes_partyRiskLimitsReport (header : Header) (r0 : PartyRiskLimitsReport) :
    Message.decodeBytes (Message.encode (.partyRiskLimitsReport header r0)) = some (.partyRiskLimitsReport header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [67, 77]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (PartyRiskLimitsReport.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_partyRiskLimitsReport header r0

theorem Message.decodeBytes_news (header : Header) (r0 : News) :
    Message.decodeBytes (Message.encode (.news header r0)) = some (.news header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [66]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (News.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_news header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | logon header r0 => exact Message.decodeBytes_logon header r0
  | heartbeat header r0 => exact Message.decodeBytes_heartbeat header r0
  | testRequest header r0 => exact Message.decodeBytes_testRequest header r0
  | resendRequest header r0 => exact Message.decodeBytes_resendRequest header r0
  | reject header r0 => exact Message.decodeBytes_reject header r0
  | sequenceReset header r0 => exact Message.decodeBytes_sequenceReset header r0
  | logout header r0 => exact Message.decodeBytes_logout header r0
  | businessMessageReject header r0 => exact Message.decodeBytes_businessMessageReject header r0
  | executionReport header r0 => exact Message.decodeBytes_executionReport header r0
  | orderCancelReject header r0 => exact Message.decodeBytes_orderCancelReject header r0
  | quoteRequestReject header r0 => exact Message.decodeBytes_quoteRequestReject header r0
  | securityDefinition header r0 => exact Message.decodeBytes_securityDefinition header r0
  | orderMassCancelReport header r0 => exact Message.decodeBytes_orderMassCancelReport header r0
  | partyRiskLimitsReport header r0 => exact Message.decodeBytes_partyRiskLimitsReport header r0
  | news header r0 => exact Message.decodeBytes_news header r0

/-- BeginString as the venue fixes it: FIXT.1.1 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 84, 46, 49, 46, 49, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.AsxAsxderivativesOrderentryFixV205Exchange
