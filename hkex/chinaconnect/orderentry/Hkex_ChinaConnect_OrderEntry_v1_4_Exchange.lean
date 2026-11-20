import Wire

/-!
#  Order Entry v1.4, Exchange messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.HkexChinaconnectOrderentryFixV14Exchange

/-- No field of this tree is data, so every value ends at the separator -/
def pairing : Pairing := []

structure Header where
  senderCompID : Terminated 1  -- tag 49
  targetCompID : Terminated 1  -- tag 56
  msgSeqNum : Terminated 1  -- tag 34
  possDupFlag : Option (Terminated 1)  -- tag 43
  possResend : Option (Terminated 1)  -- tag 97
  sendingTime : Terminated 1  -- tag 52
  origSendingTime : Option (Terminated 1)  -- tag 122
  applVerID : Option (Terminated 1)  -- tag 1128

def Header.parts (record : Header) : List Part :=
  [Part.required [52, 57] record.senderCompID,
   Part.required [53, 54] record.targetCompID,
   Part.required [51, 52] record.msgSeqNum,
   Part.optional [52, 51] record.possDupFlag,
   Part.optional [57, 55] record.possResend,
   Part.required [53, 50] record.sendingTime,
   Part.optional [49, 50, 50] record.origSendingTime,
   Part.optional [49, 49, 50, 56] record.applVerID]

def Header.tags : List (List (List UInt8)) :=
  [[[52, 57]], [[53, 54]], [[51, 52]], [[52, 51]], [[57, 55]], [[53, 50]], [[49, 50, 50]], [[49, 49, 50, 56]]]

theorem Header.shape (record : Header) : record.parts.map Part.tags = Header.tags := rfl

def Header.decode (tokens : List Token) : Option Header := do
  let senderCompID ← readRequired [52, 57] tokens
  let targetCompID ← readRequired [53, 54] tokens
  let msgSeqNum ← readRequired [51, 52] tokens
  let possDupFlag ← readOptional [52, 51] tokens
  let possResend ← readOptional [57, 55] tokens
  let sendingTime ← readRequired [53, 50] tokens
  let origSendingTime ← readOptional [49, 50, 50] tokens
  let applVerID ← readOptional [49, 49, 50, 56] tokens
  pure { senderCompID, targetCompID, msgSeqNum, possDupFlag, possResend, sendingTime, origSendingTime, applVerID }

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
  have sendingTime := readRequired_part [53, 50] record.sendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have origSendingTime := readOptional_part [49, 50, 50] record.origSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have applVerID := readOptional_part [49, 49, 50, 56] record.applVerID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  simp only [Header.decode, senderCompID, targetCompID, msgSeqNum, possDupFlag, possResend, sendingTime, origSendingTime, applVerID, some_bind] <;> rfl

theorem Header.taken (record : Header) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [52, 57] record.senderCompID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [53, 54] record.targetCompID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [51, 52] record.msgSeqNum (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [52, 51] record.possDupFlag (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [57, 55] record.possResend (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [53, 50] record.sendingTime (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [49, 50, 50] record.origSendingTime (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [49, 49, 50, 56] record.applVerID (by decide) (by decide))
          (paired_none pairing))))))))

structure Logon where
  encryptMethod : Terminated 1  -- tag 98
  heartBtInt : Terminated 1  -- tag 108
  nextExpectedMsgSeqNum : Terminated 1  -- tag 789
  encryptedPasswordMethod : Option (Terminated 1)  -- tag 1400
  encryptedPassword : Option (Terminated 1)  -- tag 1402
  encryptedNewPassword : Option (Terminated 1)  -- tag 1404
  sessionStatus : Option (Terminated 1)  -- tag 1409
  defaultApplVerID : Terminated 1  -- tag 1137
  testMessageIndicator : Option (Terminated 1)  -- tag 464
  text : Option (Terminated 1)  -- tag 58

def Logon.parts (record : Logon) : List Part :=
  [Part.required [57, 56] record.encryptMethod,
   Part.required [49, 48, 56] record.heartBtInt,
   Part.required [55, 56, 57] record.nextExpectedMsgSeqNum,
   Part.optional [49, 52, 48, 48] record.encryptedPasswordMethod,
   Part.optional [49, 52, 48, 50] record.encryptedPassword,
   Part.optional [49, 52, 48, 52] record.encryptedNewPassword,
   Part.optional [49, 52, 48, 57] record.sessionStatus,
   Part.required [49, 49, 51, 55] record.defaultApplVerID,
   Part.optional [52, 54, 52] record.testMessageIndicator,
   Part.optional [53, 56] record.text]

def Logon.tags : List (List (List UInt8)) :=
  [[[57, 56]], [[49, 48, 56]], [[55, 56, 57]], [[49, 52, 48, 48]], [[49, 52, 48, 50]], [[49, 52, 48, 52]], [[49, 52, 48, 57]], [[49, 49, 51, 55]], [[52, 54, 52]], [[53, 56]]]

theorem Logon.shape (record : Logon) : record.parts.map Part.tags = Logon.tags := rfl

def Logon.decode (tokens : List Token) : Option Logon := do
  let encryptMethod ← readRequired [57, 56] tokens
  let heartBtInt ← readRequired [49, 48, 56] tokens
  let nextExpectedMsgSeqNum ← readRequired [55, 56, 57] tokens
  let encryptedPasswordMethod ← readOptional [49, 52, 48, 48] tokens
  let encryptedPassword ← readOptional [49, 52, 48, 50] tokens
  let encryptedNewPassword ← readOptional [49, 52, 48, 52] tokens
  let sessionStatus ← readOptional [49, 52, 48, 57] tokens
  let defaultApplVerID ← readRequired [49, 49, 51, 55] tokens
  let testMessageIndicator ← readOptional [52, 54, 52] tokens
  let text ← readOptional [53, 56] tokens
  pure { encryptMethod, heartBtInt, nextExpectedMsgSeqNum, encryptedPasswordMethod, encryptedPassword, encryptedNewPassword, sessionStatus, defaultApplVerID, testMessageIndicator, text }

theorem Logon.decode_agrees (record : Logon) (tokens : List Token)
    (agrees : ∀ tags ∈ Logon.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Logon.decode tokens = some record := by
  have distinct : Logon.tags.flatten.Nodup := by decide +kernel
  have encryptMethod := readRequired_part [57, 56] record.encryptMethod tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have heartBtInt := readRequired_part [49, 48, 56] record.heartBtInt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have nextExpectedMsgSeqNum := readRequired_part [55, 56, 57] record.nextExpectedMsgSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have encryptedPasswordMethod := readOptional_part [49, 52, 48, 48] record.encryptedPasswordMethod tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have encryptedPassword := readOptional_part [49, 52, 48, 50] record.encryptedPassword tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have encryptedNewPassword := readOptional_part [49, 52, 48, 52] record.encryptedNewPassword tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have sessionStatus := readOptional_part [49, 52, 48, 57] record.sessionStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have defaultApplVerID := readRequired_part [49, 49, 51, 55] record.defaultApplVerID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have testMessageIndicator := readOptional_part [52, 54, 52] record.testMessageIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  simp only [Logon.decode, encryptMethod, heartBtInt, nextExpectedMsgSeqNum, encryptedPasswordMethod, encryptedPassword, encryptedNewPassword, sessionStatus, defaultApplVerID, testMessageIndicator, text, some_bind] <;> rfl

theorem Logon.taken (record : Logon) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [57, 56] record.encryptMethod (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 48, 56] record.heartBtInt (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [55, 56, 57] record.nextExpectedMsgSeqNum (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [49, 52, 48, 48] record.encryptedPasswordMethod (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [49, 52, 48, 50] record.encryptedPassword (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [49, 52, 48, 52] record.encryptedNewPassword (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [49, 52, 48, 57] record.sessionStatus (by decide) (by decide))
         (paired_cons pairing _ _ (paired_required pairing [49, 49, 51, 55] record.defaultApplVerID (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [52, 54, 52] record.testMessageIndicator (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
            (paired_none pairing))))))))))

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

theorem SequenceReset.taken (record : SequenceReset) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 54] record.newSeqNo (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [49, 50, 51] record.gapFillFlag (by decide) (by decide))
    (paired_none pairing))

structure NoPartyIDs where
  partyID : Terminated 1  -- tag 448
  partyIDSource : Terminated 1  -- tag 447
  partyRole : Terminated 1  -- tag 452

def NoPartyIDs.parts (record : NoPartyIDs) : List Part :=
  [Part.required [52, 52, 56] record.partyID,
   Part.required [52, 52, 55] record.partyIDSource,
   Part.required [52, 53, 50] record.partyRole]

def NoPartyIDs.tags : List (List (List UInt8)) :=
  [[[52, 52, 56]], [[52, 52, 55]], [[52, 53, 50]]]

theorem NoPartyIDs.shape (record : NoPartyIDs) : record.parts.map Part.tags = NoPartyIDs.tags := rfl

def NoPartyIDs.decode (tokens : List Token) : Option NoPartyIDs := do
  let partyID ← readRequired [52, 52, 56] tokens
  let partyIDSource ← readRequired [52, 52, 55] tokens
  let partyRole ← readRequired [52, 53, 50] tokens
  pure { partyID, partyIDSource, partyRole }

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
  simp only [NoPartyIDs.decode, partyID, partyIDSource, partyRole, some_bind] <;> rfl

theorem NoPartyIDs.taken (record : NoPartyIDs) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [52, 52, 56] record.partyID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [52, 52, 55] record.partyIDSource (by decide) (by decide))
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

structure ExecutionReport where
  clOrdID : Option (Terminated 1)  -- tag 11
  orderID : Terminated 1  -- tag 37
  execID : Terminated 1  -- tag 17
  noPartyIDs : List NoPartyIDs  -- tag 453
  securityID : Terminated 1  -- tag 48
  securityIDSource : Terminated 1  -- tag 22
  securityExchange : Option (Terminated 1)  -- tag 207
  ordType : Option (Terminated 1)  -- tag 40
  timeInForce : Option (Terminated 1)  -- tag 59
  side : Terminated 1  -- tag 54
  orderQty : Option (Terminated 1)  -- tag 38
  price : Option (Terminated 1)  -- tag 44
  transactTime : Terminated 1  -- tag 60
  orderCapacity : Option (Terminated 1)  -- tag 528
  maxPriceLevels : Option (Terminated 1)  -- tag 1090
  positionEffect : Option (Terminated 1)  -- tag 77
  ordStatus : Terminated 1  -- tag 39
  execType : Terminated 1  -- tag 150
  cumQty : Terminated 1  -- tag 14
  leavesQty : Terminated 1  -- tag 151
  text : Option (Terminated 1)  -- tag 58
  lotType : Option (Terminated 1)  -- tag 1093
  ordRejReason : Option (Terminated 1)  -- tag 103
  rejectText : Option (Terminated 1)  -- tag 1328
  origClOrdID : Option (Terminated 1)  -- tag 41
  execRestatementReason : Option (Terminated 1)  -- tag 378
  trdMatchID : Option (Terminated 1)  -- tag 880
  lastPx : Option (Terminated 1)  -- tag 31
  lastQty : Option (Terminated 1)  -- tag 32
  matchType : Option (Terminated 1)  -- tag 574
  tradeDate : Option (Terminated 1)  -- tag 75

def ExecutionReport.parts (record : ExecutionReport) : List Part :=
  [Part.optional [49, 49] record.clOrdID,
   Part.required [51, 55] record.orderID,
   Part.required [49, 55] record.execID,
   Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.required [52, 56] record.securityID,
   Part.required [50, 50] record.securityIDSource,
   Part.optional [50, 48, 55] record.securityExchange,
   Part.optional [52, 48] record.ordType,
   Part.optional [53, 57] record.timeInForce,
   Part.required [53, 52] record.side,
   Part.optional [51, 56] record.orderQty,
   Part.optional [52, 52] record.price,
   Part.required [54, 48] record.transactTime,
   Part.optional [53, 50, 56] record.orderCapacity,
   Part.optional [49, 48, 57, 48] record.maxPriceLevels,
   Part.optional [55, 55] record.positionEffect,
   Part.required [51, 57] record.ordStatus,
   Part.required [49, 53, 48] record.execType,
   Part.required [49, 52] record.cumQty,
   Part.required [49, 53, 49] record.leavesQty,
   Part.optional [53, 56] record.text,
   Part.optional [49, 48, 57, 51] record.lotType,
   Part.optional [49, 48, 51] record.ordRejReason,
   Part.optional [49, 51, 50, 56] record.rejectText,
   Part.optional [52, 49] record.origClOrdID,
   Part.optional [51, 55, 56] record.execRestatementReason,
   Part.optional [56, 56, 48] record.trdMatchID,
   Part.optional [51, 49] record.lastPx,
   Part.optional [51, 50] record.lastQty,
   Part.optional [53, 55, 52] record.matchType,
   Part.optional [55, 53] record.tradeDate]

def ExecutionReport.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[51, 55]], [[49, 55]], [52, 53, 51] :: NoPartyIDs.members, [[52, 56]], [[50, 50]], [[50, 48, 55]], [[52, 48]], [[53, 57]], [[53, 52]], [[51, 56]], [[52, 52]], [[54, 48]], [[53, 50, 56]], [[49, 48, 57, 48]], [[55, 55]], [[51, 57]], [[49, 53, 48]], [[49, 52]], [[49, 53, 49]], [[53, 56]], [[49, 48, 57, 51]], [[49, 48, 51]], [[49, 51, 50, 56]], [[52, 49]], [[51, 55, 56]], [[56, 56, 48]], [[51, 49]], [[51, 50]], [[53, 55, 52]], [[55, 53]]]

theorem ExecutionReport.shape (record : ExecutionReport) : record.parts.map Part.tags = ExecutionReport.tags := rfl

def ExecutionReport.decode (tokens : List Token) : Option ExecutionReport := do
  let clOrdID ← readOptional [49, 49] tokens
  let orderID ← readRequired [51, 55] tokens
  let execID ← readRequired [49, 55] tokens
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let securityID ← readRequired [52, 56] tokens
  let securityIDSource ← readRequired [50, 50] tokens
  let securityExchange ← readOptional [50, 48, 55] tokens
  let ordType ← readOptional [52, 48] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let side ← readRequired [53, 52] tokens
  let orderQty ← readOptional [51, 56] tokens
  let price ← readOptional [52, 52] tokens
  let transactTime ← readRequired [54, 48] tokens
  let orderCapacity ← readOptional [53, 50, 56] tokens
  let maxPriceLevels ← readOptional [49, 48, 57, 48] tokens
  let positionEffect ← readOptional [55, 55] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let execType ← readRequired [49, 53, 48] tokens
  let cumQty ← readRequired [49, 52] tokens
  let leavesQty ← readRequired [49, 53, 49] tokens
  let text ← readOptional [53, 56] tokens
  let lotType ← readOptional [49, 48, 57, 51] tokens
  let ordRejReason ← readOptional [49, 48, 51] tokens
  let rejectText ← readOptional [49, 51, 50, 56] tokens
  let origClOrdID ← readOptional [52, 49] tokens
  let execRestatementReason ← readOptional [51, 55, 56] tokens
  let trdMatchID ← readOptional [56, 56, 48] tokens
  let lastPx ← readOptional [51, 49] tokens
  let lastQty ← readOptional [51, 50] tokens
  let matchType ← readOptional [53, 55, 52] tokens
  let tradeDate ← readOptional [55, 53] tokens
  pure { clOrdID, orderID, execID, noPartyIDs, securityID, securityIDSource, securityExchange, ordType, timeInForce, side, orderQty, price, transactTime, orderCapacity, maxPriceLevels, positionEffect, ordStatus, execType, cumQty, leavesQty, text, lotType, ordRejReason, rejectText, origClOrdID, execRestatementReason, trdMatchID, lastPx, lastQty, matchType, tradeDate }

theorem ExecutionReport.decode_agrees (record : ExecutionReport) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReport.decode tokens = some record := by
  have distinct : ExecutionReport.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readOptional_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have execID := readRequired_part [49, 55] record.execID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have securityID := readRequired_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have securityIDSource := readRequired_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have securityExchange := readOptional_part [50, 48, 55] record.securityExchange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have ordType := readOptional_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have orderQty := readOptional_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have orderCapacity := readOptional_part [53, 50, 56] record.orderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have maxPriceLevels := readOptional_part [49, 48, 57, 48] record.maxPriceLevels tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have positionEffect := readOptional_part [55, 55] record.positionEffect tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have execType := readRequired_part [49, 53, 48] record.execType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have cumQty := readRequired_part [49, 52] record.cumQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have leavesQty := readRequired_part [49, 53, 49] record.leavesQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have lotType := readOptional_part [49, 48, 57, 51] record.lotType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have ordRejReason := readOptional_part [49, 48, 51] record.ordRejReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have rejectText := readOptional_part [49, 51, 50, 56] record.rejectText tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have execRestatementReason := readOptional_part [51, 55, 56] record.execRestatementReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have trdMatchID := readOptional_part [56, 56, 48] record.trdMatchID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have lastPx := readOptional_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have lastQty := readOptional_part [51, 50] record.lastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have matchType := readOptional_part [53, 55, 52] record.matchType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have tradeDate := readOptional_part [55, 53] record.tradeDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  simp only [ExecutionReport.decode, clOrdID, orderID, execID, noPartyIDs, securityID, securityIDSource, securityExchange, ordType, timeInForce, side, orderQty, price, transactTime, orderCapacity, maxPriceLevels, positionEffect, ordStatus, execType, cumQty, leavesQty, text, lotType, ordRejReason, rejectText, origClOrdID, execRestatementReason, trdMatchID, lastPx, lastQty, matchType, tradeDate, some_bind] <;> rfl

theorem ExecutionReport.taken (record : ExecutionReport) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49, 49] record.clOrdID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [51, 55] record.orderID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [49, 55] record.execID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_group pairing [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within (by decide) (by decide) NoPartyIDs.taken record.noPartyIDs)
      (paired_cons pairing _ _ (paired_required pairing [52, 56] record.securityID (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [50, 50] record.securityIDSource (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [50, 48, 55] record.securityExchange (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [52, 48] record.ordType (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [53, 57] record.timeInForce (by decide) (by decide))
           (paired_cons pairing _ _ (paired_required pairing [53, 52] record.side (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [51, 56] record.orderQty (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [52, 52] record.price (by decide) (by decide))
              (paired_cons pairing _ _ (paired_required pairing [54, 48] record.transactTime (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [53, 50, 56] record.orderCapacity (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [49, 48, 57, 48] record.maxPriceLevels (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_optional pairing [55, 55] record.positionEffect (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_required pairing [51, 57] record.ordStatus (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_required pairing [49, 53, 48] record.execType (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_required pairing [49, 52] record.cumQty (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_required pairing [49, 53, 49] record.leavesQty (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
                       (paired_cons pairing _ _ (paired_optional pairing [49, 48, 57, 51] record.lotType (by decide) (by decide))
                        (paired_cons pairing _ _ (paired_optional pairing [49, 48, 51] record.ordRejReason (by decide) (by decide))
                         (paired_cons pairing _ _ (paired_optional pairing [49, 51, 50, 56] record.rejectText (by decide) (by decide))
                          (paired_cons pairing _ _ (paired_optional pairing [52, 49] record.origClOrdID (by decide) (by decide))
                           (paired_cons pairing _ _ (paired_optional pairing [51, 55, 56] record.execRestatementReason (by decide) (by decide))
                            (paired_cons pairing _ _ (paired_optional pairing [56, 56, 48] record.trdMatchID (by decide) (by decide))
                             (paired_cons pairing _ _ (paired_optional pairing [51, 49] record.lastPx (by decide) (by decide))
                              (paired_cons pairing _ _ (paired_optional pairing [51, 50] record.lastQty (by decide) (by decide))
                               (paired_cons pairing _ _ (paired_optional pairing [53, 55, 52] record.matchType (by decide) (by decide))
                                (paired_cons pairing _ _ (paired_optional pairing [55, 53] record.tradeDate (by decide) (by decide))
                                 (paired_none pairing)))))))))))))))))))))))))))))))

structure CancelReject where
  clOrdID : Terminated 1  -- tag 11
  origClOrdID : Option (Terminated 1)  -- tag 41
  orderID : Terminated 1  -- tag 37
  noPartyIDs : List NoPartyIDs  -- tag 453
  transactTime : Terminated 1  -- tag 60
  ordStatus : Terminated 1  -- tag 39
  cxlRejResponseTo : Terminated 1  -- tag 434
  cxlRejReason : Option (Terminated 1)  -- tag 102
  text : Option (Terminated 1)  -- tag 58
  rejectText : Option (Terminated 1)  -- tag 1328

def CancelReject.parts (record : CancelReject) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.optional [52, 49] record.origClOrdID,
   Part.required [51, 55] record.orderID,
   Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.required [54, 48] record.transactTime,
   Part.required [51, 57] record.ordStatus,
   Part.required [52, 51, 52] record.cxlRejResponseTo,
   Part.optional [49, 48, 50] record.cxlRejReason,
   Part.optional [53, 56] record.text,
   Part.optional [49, 51, 50, 56] record.rejectText]

def CancelReject.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[52, 49]], [[51, 55]], [52, 53, 51] :: NoPartyIDs.members, [[54, 48]], [[51, 57]], [[52, 51, 52]], [[49, 48, 50]], [[53, 56]], [[49, 51, 50, 56]]]

theorem CancelReject.shape (record : CancelReject) : record.parts.map Part.tags = CancelReject.tags := rfl

def CancelReject.decode (tokens : List Token) : Option CancelReject := do
  let clOrdID ← readRequired [49, 49] tokens
  let origClOrdID ← readOptional [52, 49] tokens
  let orderID ← readRequired [51, 55] tokens
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let transactTime ← readRequired [54, 48] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let cxlRejResponseTo ← readRequired [52, 51, 52] tokens
  let cxlRejReason ← readOptional [49, 48, 50] tokens
  let text ← readOptional [53, 56] tokens
  let rejectText ← readOptional [49, 51, 50, 56] tokens
  pure { clOrdID, origClOrdID, orderID, noPartyIDs, transactTime, ordStatus, cxlRejResponseTo, cxlRejReason, text, rejectText }

theorem CancelReject.decode_agrees (record : CancelReject) (tokens : List Token)
    (agrees : ∀ tags ∈ CancelReject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    CancelReject.decode tokens = some record := by
  have distinct : CancelReject.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have cxlRejResponseTo := readRequired_part [52, 51, 52] record.cxlRejResponseTo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have cxlRejReason := readOptional_part [49, 48, 50] record.cxlRejReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have rejectText := readOptional_part [49, 51, 50, 56] record.rejectText tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  simp only [CancelReject.decode, clOrdID, origClOrdID, orderID, noPartyIDs, transactTime, ordStatus, cxlRejResponseTo, cxlRejReason, text, rejectText, some_bind] <;> rfl

theorem CancelReject.taken (record : CancelReject) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [52, 49] record.origClOrdID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [51, 55] record.orderID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_group pairing [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within (by decide) (by decide) NoPartyIDs.taken record.noPartyIDs)
      (paired_cons pairing _ _ (paired_required pairing [54, 48] record.transactTime (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [51, 57] record.ordStatus (by decide) (by decide))
        (paired_cons pairing _ _ (paired_required pairing [52, 51, 52] record.cxlRejResponseTo (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [49, 48, 50] record.cxlRejReason (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [49, 51, 50, 56] record.rejectText (by decide) (by decide))
            (paired_none pairing))))))))))

structure BusinessMessageReject where
  refSeqNum : Option (Terminated 1)  -- tag 45
  refMsgType : Terminated 1  -- tag 372
  businessRejectRefID : Option (Terminated 1)  -- tag 379
  businessRejectReason : Terminated 1  -- tag 380
  text : Option (Terminated 1)  -- tag 58

def BusinessMessageReject.parts (record : BusinessMessageReject) : List Part :=
  [Part.optional [52, 53] record.refSeqNum,
   Part.required [51, 55, 50] record.refMsgType,
   Part.optional [51, 55, 57] record.businessRejectRefID,
   Part.required [51, 56, 48] record.businessRejectReason,
   Part.optional [53, 56] record.text]

def BusinessMessageReject.tags : List (List (List UInt8)) :=
  [[[52, 53]], [[51, 55, 50]], [[51, 55, 57]], [[51, 56, 48]], [[53, 56]]]

theorem BusinessMessageReject.shape (record : BusinessMessageReject) : record.parts.map Part.tags = BusinessMessageReject.tags := rfl

def BusinessMessageReject.decode (tokens : List Token) : Option BusinessMessageReject := do
  let refSeqNum ← readOptional [52, 53] tokens
  let refMsgType ← readRequired [51, 55, 50] tokens
  let businessRejectRefID ← readOptional [51, 55, 57] tokens
  let businessRejectReason ← readRequired [51, 56, 48] tokens
  let text ← readOptional [53, 56] tokens
  pure { refSeqNum, refMsgType, businessRejectRefID, businessRejectReason, text }

theorem BusinessMessageReject.decode_agrees (record : BusinessMessageReject) (tokens : List Token)
    (agrees : ∀ tags ∈ BusinessMessageReject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    BusinessMessageReject.decode tokens = some record := by
  have distinct : BusinessMessageReject.tags.flatten.Nodup := by decide +kernel
  have refSeqNum := readOptional_part [52, 53] record.refSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have refMsgType := readRequired_part [51, 55, 50] record.refMsgType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have businessRejectRefID := readOptional_part [51, 55, 57] record.businessRejectRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have businessRejectReason := readRequired_part [51, 56, 48] record.businessRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [BusinessMessageReject.decode, refSeqNum, refMsgType, businessRejectRefID, businessRejectReason, text, some_bind] <;> rfl

theorem BusinessMessageReject.taken (record : BusinessMessageReject) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [52, 53] record.refSeqNum (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [51, 55, 50] record.refMsgType (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [51, 55, 57] record.businessRejectRefID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [51, 56, 48] record.businessRejectReason (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
       (paired_none pairing)))))

structure NoThrottles where
  throttleAction : Terminated 1  -- tag 1611
  throttleType : Option (Terminated 1)  -- tag 1612
  throttleNoMsgs : Option (Terminated 1)  -- tag 1613
  throttleTimeInterval : Option (Terminated 1)  -- tag 1614
  throttleTimeUnit : Option (Terminated 1)  -- tag 1615

def NoThrottles.parts (record : NoThrottles) : List Part :=
  [Part.required [49, 54, 49, 49] record.throttleAction,
   Part.optional [49, 54, 49, 50] record.throttleType,
   Part.optional [49, 54, 49, 51] record.throttleNoMsgs,
   Part.optional [49, 54, 49, 52] record.throttleTimeInterval,
   Part.optional [49, 54, 49, 53] record.throttleTimeUnit]

def NoThrottles.tags : List (List (List UInt8)) :=
  [[[49, 54, 49, 49]], [[49, 54, 49, 50]], [[49, 54, 49, 51]], [[49, 54, 49, 52]], [[49, 54, 49, 53]]]

theorem NoThrottles.shape (record : NoThrottles) : record.parts.map Part.tags = NoThrottles.tags := rfl

def NoThrottles.decode (tokens : List Token) : Option NoThrottles := do
  let throttleAction ← readRequired [49, 54, 49, 49] tokens
  let throttleType ← readOptional [49, 54, 49, 50] tokens
  let throttleNoMsgs ← readOptional [49, 54, 49, 51] tokens
  let throttleTimeInterval ← readOptional [49, 54, 49, 52] tokens
  let throttleTimeUnit ← readOptional [49, 54, 49, 53] tokens
  pure { throttleAction, throttleType, throttleNoMsgs, throttleTimeInterval, throttleTimeUnit }

theorem NoThrottles.decode_agrees (record : NoThrottles) (tokens : List Token)
    (agrees : ∀ tags ∈ NoThrottles.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoThrottles.decode tokens = some record := by
  have distinct : NoThrottles.tags.flatten.Nodup := by decide +kernel
  have throttleAction := readRequired_part [49, 54, 49, 49] record.throttleAction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have throttleType := readOptional_part [49, 54, 49, 50] record.throttleType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have throttleNoMsgs := readOptional_part [49, 54, 49, 51] record.throttleNoMsgs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have throttleTimeInterval := readOptional_part [49, 54, 49, 52] record.throttleTimeInterval tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have throttleTimeUnit := readOptional_part [49, 54, 49, 53] record.throttleTimeUnit tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [NoThrottles.decode, throttleAction, throttleType, throttleNoMsgs, throttleTimeInterval, throttleTimeUnit, some_bind] <;> rfl

theorem NoThrottles.taken (record : NoThrottles) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 54, 49, 49] record.throttleAction (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [49, 54, 49, 50] record.throttleType (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [49, 54, 49, 51] record.throttleNoMsgs (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [49, 54, 49, 52] record.throttleTimeInterval (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [49, 54, 49, 53] record.throttleTimeUnit (by decide) (by decide))
       (paired_none pairing)))))

def NoThrottles.members : List (List UInt8) := NoThrottles.tags.flatten

def NoThrottles.encode (entry : NoThrottles) : List Token := encodeParts entry.parts

theorem NoThrottles.decode_encode (entry : NoThrottles) : NoThrottles.decode entry.encode = some entry :=
  NoThrottles.decode_agrees entry _ (fun _ _ => rfl)

theorem NoThrottles.within (entry : NoThrottles) : ∀ token ∈ entry.encode, token.tag ∈ NoThrottles.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoThrottles.shape] at this

theorem NoThrottles.led (entry : NoThrottles) : Lead [49, 54, 49, 49] entry.encode :=
  lead_parts [49, 54, 49, 49] entry.throttleAction _ NoThrottles.tags.tail rfl (by decide +kernel)

structure UserResponse where
  userRequestID : Terminated 1  -- tag 923
  userName : Terminated 1  -- tag 553
  noThrottles : List NoThrottles  -- tag 1610

def UserResponse.parts (record : UserResponse) : List Part :=
  [Part.required [57, 50, 51] record.userRequestID,
   Part.required [53, 53, 51] record.userName,
   Part.group [49, 54, 49, 48] NoThrottles.members NoThrottles.encode NoThrottles.within record.noThrottles]

def UserResponse.tags : List (List (List UInt8)) :=
  [[[57, 50, 51]], [[53, 53, 51]], [49, 54, 49, 48] :: NoThrottles.members]

theorem UserResponse.shape (record : UserResponse) : record.parts.map Part.tags = UserResponse.tags := rfl

def UserResponse.decode (tokens : List Token) : Option UserResponse := do
  let userRequestID ← readRequired [57, 50, 51] tokens
  let userName ← readRequired [53, 53, 51] tokens
  let noThrottles ← readGroup [49, 54, 49, 48] [49, 54, 49, 49] NoThrottles.members NoThrottles.decode tokens
  pure { userRequestID, userName, noThrottles }

theorem UserResponse.decode_agrees (record : UserResponse) (tokens : List Token)
    (agrees : ∀ tags ∈ UserResponse.tags, select tags tokens = select tags (encodeParts record.parts)) :
    UserResponse.decode tokens = some record := by
  have distinct : UserResponse.tags.flatten.Nodup := by decide +kernel
  have userRequestID := readRequired_part [57, 50, 51] record.userRequestID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have userName := readRequired_part [53, 53, 51] record.userName tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have noThrottles := readGroup_part [49, 54, 49, 48] [49, 54, 49, 49] NoThrottles.members NoThrottles.encode NoThrottles.within NoThrottles.decode NoThrottles.decode_encode NoThrottles.led record.noThrottles tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [UserResponse.decode, userRequestID, userName, noThrottles, some_bind] <;> rfl

theorem UserResponse.taken (record : UserResponse) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [57, 50, 51] record.userRequestID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [53, 53, 51] record.userName (by decide) (by decide))
    (paired_cons pairing _ _ (paired_group pairing [49, 54, 49, 48] NoThrottles.members NoThrottles.encode NoThrottles.within (by decide) (by decide) NoThrottles.taken record.noThrottles)
     (paired_none pairing)))

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

structure NoMarketSegments where
  marketID : Terminated 1  -- tag 1301

def NoMarketSegments.parts (record : NoMarketSegments) : List Part :=
  [Part.required [49, 51, 48, 49] record.marketID]

def NoMarketSegments.tags : List (List (List UInt8)) :=
  [[[49, 51, 48, 49]]]

theorem NoMarketSegments.shape (record : NoMarketSegments) : record.parts.map Part.tags = NoMarketSegments.tags := rfl

def NoMarketSegments.decode (tokens : List Token) : Option NoMarketSegments := do
  let marketID ← readRequired [49, 51, 48, 49] tokens
  pure { marketID }

theorem NoMarketSegments.decode_agrees (record : NoMarketSegments) (tokens : List Token)
    (agrees : ∀ tags ∈ NoMarketSegments.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoMarketSegments.decode tokens = some record := by
  have distinct : NoMarketSegments.tags.flatten.Nodup := by decide +kernel
  have marketID := readRequired_part [49, 51, 48, 49] record.marketID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [NoMarketSegments.decode, marketID, some_bind] <;> rfl

theorem NoMarketSegments.taken (record : NoMarketSegments) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 51, 48, 49] record.marketID (by decide) (by decide))
   (paired_none pairing)

def NoMarketSegments.members : List (List UInt8) := NoMarketSegments.tags.flatten

def NoMarketSegments.encode (entry : NoMarketSegments) : List Token := encodeParts entry.parts

theorem NoMarketSegments.decode_encode (entry : NoMarketSegments) : NoMarketSegments.decode entry.encode = some entry :=
  NoMarketSegments.decode_agrees entry _ (fun _ _ => rfl)

theorem NoMarketSegments.within (entry : NoMarketSegments) : ∀ token ∈ entry.encode, token.tag ∈ NoMarketSegments.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoMarketSegments.shape] at this

theorem NoMarketSegments.led (entry : NoMarketSegments) : Lead [49, 51, 48, 49] entry.encode :=
  lead_parts [49, 51, 48, 49] entry.marketID _ NoMarketSegments.tags.tail rfl (by decide +kernel)

structure NoEntitlements where
  entitlementIndicator : Terminated 1  -- tag 1774
  entitlementType : Option (Terminated 1)  -- tag 1775
  noMarketSegments : List NoMarketSegments  -- tag 1310
  entitlementID : Option (Terminated 1)  -- tag 1776

def NoEntitlements.parts (record : NoEntitlements) : List Part :=
  [Part.required [49, 55, 55, 52] record.entitlementIndicator,
   Part.optional [49, 55, 55, 53] record.entitlementType,
   Part.group [49, 51, 49, 48] NoMarketSegments.members NoMarketSegments.encode NoMarketSegments.within record.noMarketSegments,
   Part.optional [49, 55, 55, 54] record.entitlementID]

def NoEntitlements.tags : List (List (List UInt8)) :=
  [[[49, 55, 55, 52]], [[49, 55, 55, 53]], [49, 51, 49, 48] :: NoMarketSegments.members, [[49, 55, 55, 54]]]

theorem NoEntitlements.shape (record : NoEntitlements) : record.parts.map Part.tags = NoEntitlements.tags := rfl

def NoEntitlements.decode (tokens : List Token) : Option NoEntitlements := do
  let entitlementIndicator ← readRequired [49, 55, 55, 52] tokens
  let entitlementType ← readOptional [49, 55, 55, 53] tokens
  let noMarketSegments ← readGroup [49, 51, 49, 48] [49, 51, 48, 49] NoMarketSegments.members NoMarketSegments.decode tokens
  let entitlementID ← readOptional [49, 55, 55, 54] tokens
  pure { entitlementIndicator, entitlementType, noMarketSegments, entitlementID }

theorem NoEntitlements.decode_agrees (record : NoEntitlements) (tokens : List Token)
    (agrees : ∀ tags ∈ NoEntitlements.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoEntitlements.decode tokens = some record := by
  have distinct : NoEntitlements.tags.flatten.Nodup := by decide +kernel
  have entitlementIndicator := readRequired_part [49, 55, 55, 52] record.entitlementIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have entitlementType := readOptional_part [49, 55, 55, 53] record.entitlementType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have noMarketSegments := readGroup_part [49, 51, 49, 48] [49, 51, 48, 49] NoMarketSegments.members NoMarketSegments.encode NoMarketSegments.within NoMarketSegments.decode NoMarketSegments.decode_encode NoMarketSegments.led record.noMarketSegments tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have entitlementID := readOptional_part [49, 55, 55, 54] record.entitlementID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [NoEntitlements.decode, entitlementIndicator, entitlementType, noMarketSegments, entitlementID, some_bind] <;> rfl

theorem NoEntitlements.taken (record : NoEntitlements) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 55, 55, 52] record.entitlementIndicator (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [49, 55, 55, 53] record.entitlementType (by decide) (by decide))
    (paired_cons pairing _ _ (paired_group pairing [49, 51, 49, 48] NoMarketSegments.members NoMarketSegments.encode NoMarketSegments.within (by decide) (by decide) NoMarketSegments.taken record.noMarketSegments)
     (paired_cons pairing _ _ (paired_optional pairing [49, 55, 55, 54] record.entitlementID (by decide) (by decide))
      (paired_none pairing))))

def NoEntitlements.members : List (List UInt8) := NoEntitlements.tags.flatten

def NoEntitlements.encode (entry : NoEntitlements) : List Token := encodeParts entry.parts

theorem NoEntitlements.decode_encode (entry : NoEntitlements) : NoEntitlements.decode entry.encode = some entry :=
  NoEntitlements.decode_agrees entry _ (fun _ _ => rfl)

theorem NoEntitlements.within (entry : NoEntitlements) : ∀ token ∈ entry.encode, token.tag ∈ NoEntitlements.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoEntitlements.shape] at this

theorem NoEntitlements.led (entry : NoEntitlements) : Lead [49, 55, 55, 52] entry.encode :=
  lead_parts [49, 55, 55, 52] entry.entitlementIndicator _ NoEntitlements.tags.tail rfl (by decide +kernel)

structure NoPartyEntitlements where
  noPartyDetails : List NoPartyDetails  -- tag 1671
  noEntitlements : List NoEntitlements  -- tag 1773

def NoPartyEntitlements.parts (record : NoPartyEntitlements) : List Part :=
  [Part.groupLed [49, 54, 55, 49] NoPartyDetails.members NoPartyDetails.encode NoPartyDetails.within record.noPartyDetails,
   Part.group [49, 55, 55, 51] NoEntitlements.members NoEntitlements.encode NoEntitlements.within record.noEntitlements]

def NoPartyEntitlements.tags : List (List (List UInt8)) :=
  [[49, 54, 55, 49] :: NoPartyDetails.members, [49, 55, 55, 51] :: NoEntitlements.members]

theorem NoPartyEntitlements.shape (record : NoPartyEntitlements) : record.parts.map Part.tags = NoPartyEntitlements.tags := rfl

def NoPartyEntitlements.decode (tokens : List Token) : Option NoPartyEntitlements := do
  let noPartyDetails ← readGroup [49, 54, 55, 49] [49, 54, 57, 49] NoPartyDetails.members NoPartyDetails.decode tokens
  let noEntitlements ← readGroup [49, 55, 55, 51] [49, 55, 55, 52] NoEntitlements.members NoEntitlements.decode tokens
  pure { noPartyDetails, noEntitlements }

theorem NoPartyEntitlements.decode_agrees (record : NoPartyEntitlements) (tokens : List Token)
    (agrees : ∀ tags ∈ NoPartyEntitlements.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoPartyEntitlements.decode tokens = some record := by
  have distinct : NoPartyEntitlements.tags.flatten.Nodup := by decide +kernel
  have noPartyDetails := readGroup_partLed [49, 54, 55, 49] [49, 54, 57, 49] NoPartyDetails.members NoPartyDetails.encode NoPartyDetails.within NoPartyDetails.decode NoPartyDetails.decode_encode NoPartyDetails.led record.noPartyDetails tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have noEntitlements := readGroup_part [49, 55, 55, 51] [49, 55, 55, 52] NoEntitlements.members NoEntitlements.encode NoEntitlements.within NoEntitlements.decode NoEntitlements.decode_encode NoEntitlements.led record.noEntitlements tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [NoPartyEntitlements.decode, noPartyDetails, noEntitlements, some_bind] <;> rfl

theorem NoPartyEntitlements.taken (record : NoPartyEntitlements) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_groupLed pairing [49, 54, 55, 49] NoPartyDetails.members NoPartyDetails.encode NoPartyDetails.within (by decide) (by decide) NoPartyDetails.taken record.noPartyDetails)
   (paired_cons pairing _ _ (paired_group pairing [49, 55, 55, 51] NoEntitlements.members NoEntitlements.encode NoEntitlements.within (by decide) (by decide) NoEntitlements.taken record.noEntitlements)
    (paired_none pairing))

def NoPartyEntitlements.members : List (List UInt8) := NoPartyEntitlements.tags.flatten

def NoPartyEntitlements.encode (entry : NoPartyEntitlements) : List Token := encodeParts entry.parts

theorem NoPartyEntitlements.decode_encode (entry : NoPartyEntitlements) : NoPartyEntitlements.decode entry.encode = some entry :=
  NoPartyEntitlements.decode_agrees entry _ (fun _ _ => rfl)

theorem NoPartyEntitlements.within (entry : NoPartyEntitlements) : ∀ token ∈ entry.encode, token.tag ∈ NoPartyEntitlements.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoPartyEntitlements.shape] at this

theorem NoPartyEntitlements.led (entry : NoPartyEntitlements) : Lead [49, 54, 55, 49] entry.encode :=
  lead_groupLed [49, 54, 55, 49] NoPartyDetails.members NoPartyDetails.encode NoPartyDetails.within entry.noPartyDetails _ NoPartyEntitlements.tags.tail rfl (by decide +kernel) (by decide +kernel)

structure PartyEntitlementsReport where
  entitlementsReportID : Terminated 1  -- tag 1771
  entitlementsRequestID : Option (Terminated 1)  -- tag 1770
  requestResult : Option (Terminated 1)  -- tag 1511
  totNoPartyList : Option (Terminated 1)  -- tag 1512
  lastFragment : Option (Terminated 1)  -- tag 893
  noPartyEntitlements : List NoPartyEntitlements  -- tag 1772

def PartyEntitlementsReport.parts (record : PartyEntitlementsReport) : List Part :=
  [Part.required [49, 55, 55, 49] record.entitlementsReportID,
   Part.optional [49, 55, 55, 48] record.entitlementsRequestID,
   Part.optional [49, 53, 49, 49] record.requestResult,
   Part.optional [49, 53, 49, 50] record.totNoPartyList,
   Part.optional [56, 57, 51] record.lastFragment,
   Part.group [49, 55, 55, 50] NoPartyEntitlements.members NoPartyEntitlements.encode NoPartyEntitlements.within record.noPartyEntitlements]

def PartyEntitlementsReport.tags : List (List (List UInt8)) :=
  [[[49, 55, 55, 49]], [[49, 55, 55, 48]], [[49, 53, 49, 49]], [[49, 53, 49, 50]], [[56, 57, 51]], [49, 55, 55, 50] :: NoPartyEntitlements.members]

theorem PartyEntitlementsReport.shape (record : PartyEntitlementsReport) : record.parts.map Part.tags = PartyEntitlementsReport.tags := rfl

def PartyEntitlementsReport.decode (tokens : List Token) : Option PartyEntitlementsReport := do
  let entitlementsReportID ← readRequired [49, 55, 55, 49] tokens
  let entitlementsRequestID ← readOptional [49, 55, 55, 48] tokens
  let requestResult ← readOptional [49, 53, 49, 49] tokens
  let totNoPartyList ← readOptional [49, 53, 49, 50] tokens
  let lastFragment ← readOptional [56, 57, 51] tokens
  let noPartyEntitlements ← readGroup [49, 55, 55, 50] [49, 54, 55, 49] NoPartyEntitlements.members NoPartyEntitlements.decode tokens
  pure { entitlementsReportID, entitlementsRequestID, requestResult, totNoPartyList, lastFragment, noPartyEntitlements }

theorem PartyEntitlementsReport.decode_agrees (record : PartyEntitlementsReport) (tokens : List Token)
    (agrees : ∀ tags ∈ PartyEntitlementsReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    PartyEntitlementsReport.decode tokens = some record := by
  have distinct : PartyEntitlementsReport.tags.flatten.Nodup := by decide +kernel
  have entitlementsReportID := readRequired_part [49, 55, 55, 49] record.entitlementsReportID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have entitlementsRequestID := readOptional_part [49, 55, 55, 48] record.entitlementsRequestID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have requestResult := readOptional_part [49, 53, 49, 49] record.requestResult tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have totNoPartyList := readOptional_part [49, 53, 49, 50] record.totNoPartyList tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have lastFragment := readOptional_part [56, 57, 51] record.lastFragment tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have noPartyEntitlements := readGroup_part [49, 55, 55, 50] [49, 54, 55, 49] NoPartyEntitlements.members NoPartyEntitlements.encode NoPartyEntitlements.within NoPartyEntitlements.decode NoPartyEntitlements.decode_encode NoPartyEntitlements.led record.noPartyEntitlements tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  simp only [PartyEntitlementsReport.decode, entitlementsReportID, entitlementsRequestID, requestResult, totNoPartyList, lastFragment, noPartyEntitlements, some_bind] <;> rfl

theorem PartyEntitlementsReport.taken (record : PartyEntitlementsReport) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 55, 55, 49] record.entitlementsReportID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [49, 55, 55, 48] record.entitlementsRequestID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [49, 53, 49, 49] record.requestResult (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [49, 53, 49, 50] record.totNoPartyList (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [56, 57, 51] record.lastFragment (by decide) (by decide))
       (paired_cons pairing _ _ (paired_group pairing [49, 55, 55, 50] NoPartyEntitlements.members NoPartyEntitlements.encode NoPartyEntitlements.within (by decide) (by decide) NoPartyEntitlements.taken record.noPartyEntitlements)
        (paired_none pairing))))))

inductive Message where
  | logon (header : Header) (r0 : Logon)
  | logout (header : Header) (r0 : Logout)
  | heartbeat (header : Header) (r0 : Heartbeat)
  | testRequest (header : Header) (r0 : TestRequest)
  | resendRequest (header : Header) (r0 : ResendRequest)
  | reject (header : Header) (r0 : Reject)
  | sequenceReset (header : Header) (r0 : SequenceReset)
  | executionReport (header : Header) (r0 : ExecutionReport)
  | cancelReject (header : Header) (r0 : CancelReject)
  | businessMessageReject (header : Header) (r0 : BusinessMessageReject)
  | userResponse (header : Header) (r0 : UserResponse)
  | partyEntitlementsReport (header : Header) (r0 : PartyEntitlementsReport)

def Message.tokens : Message → List Token
  | .logon header r0 => ⟨[51, 53], [65]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logout header r0 => ⟨[51, 53], [53]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .heartbeat header r0 => ⟨[51, 53], [48]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .testRequest header r0 => ⟨[51, 53], [49]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .resendRequest header r0 => ⟨[51, 53], [50]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .reject header r0 => ⟨[51, 53], [51]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .sequenceReset header r0 => ⟨[51, 53], [52]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .executionReport header r0 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .cancelReject header r0 => ⟨[51, 53], [57]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .businessMessageReject header r0 => ⟨[51, 53], [106]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .userResponse header r0 => ⟨[51, 53], [66, 70]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .partyEntitlementsReport header r0 => ⟨[51, 53], [67, 86]⟩ :: encodeParts (header.parts ++ r0.parts)

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
        if known (Header.tags ++ SequenceReset.tags) rest then do
          let header ← Header.decode rest
          let r0 ← SequenceReset.decode rest
          pure (.sequenceReset header r0)
        else none
      else if token.value = [56] then
        if known (Header.tags ++ ExecutionReport.tags) rest then do
          let header ← Header.decode rest
          let r0 ← ExecutionReport.decode rest
          pure (.executionReport header r0)
        else none
      else if token.value = [57] then
        if known (Header.tags ++ CancelReject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← CancelReject.decode rest
          pure (.cancelReject header r0)
        else none
      else if token.value = [106] then
        if known (Header.tags ++ BusinessMessageReject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← BusinessMessageReject.decode rest
          pure (.businessMessageReject header r0)
        else none
      else if token.value = [66, 70] then
        if known (Header.tags ++ UserResponse.tags) rest then do
          let header ← Header.decode rest
          let r0 ← UserResponse.decode rest
          pure (.userResponse header r0)
        else none
      else if token.value = [67, 86] then
        if known (Header.tags ++ PartyEntitlementsReport.tags) rest then do
          let header ← Header.decode rest
          let r0 ← PartyEntitlementsReport.decode rest
          pure (.partyEntitlementsReport header r0)
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

theorem Message.decode_cancelReject (header : Header) (r0 : CancelReject) :
    Message.decode (Message.tokens (.cancelReject header r0)) = some (.cancelReject header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (CancelReject.tags) rfl rfl (by decide +kernel))
  have c1 := CancelReject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (CancelReject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ CancelReject.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_businessMessageReject (header : Header) (r0 : BusinessMessageReject) :
    Message.decode (Message.tokens (.businessMessageReject header r0)) = some (.businessMessageReject header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (BusinessMessageReject.tags) rfl rfl (by decide +kernel))
  have c1 := BusinessMessageReject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (BusinessMessageReject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ BusinessMessageReject.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_userResponse (header : Header) (r0 : UserResponse) :
    Message.decode (Message.tokens (.userResponse header r0)) = some (.userResponse header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (UserResponse.tags) rfl rfl (by decide +kernel))
  have c1 := UserResponse.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (UserResponse.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ UserResponse.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_partyEntitlementsReport (header : Header) (r0 : PartyEntitlementsReport) :
    Message.decode (Message.tokens (.partyEntitlementsReport header r0)) = some (.partyEntitlementsReport header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (PartyEntitlementsReport.tags) rfl rfl (by decide +kernel))
  have c1 := PartyEntitlementsReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (PartyEntitlementsReport.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ PartyEntitlementsReport.tags) rfl
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
  | cancelReject header r0 => exact Message.decode_cancelReject header r0
  | businessMessageReject header r0 => exact Message.decode_businessMessageReject header r0
  | userResponse header r0 => exact Message.decode_userResponse header r0
  | partyEntitlementsReport header r0 => exact Message.decode_partyEntitlementsReport header r0

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

theorem Message.decodeBytes_sequenceReset (header : Header) (r0 : SequenceReset) :
    Message.decodeBytes (Message.encode (.sequenceReset header r0)) = some (.sequenceReset header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [52]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (SequenceReset.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_sequenceReset header r0

theorem Message.decodeBytes_executionReport (header : Header) (r0 : ExecutionReport) :
    Message.decodeBytes (Message.encode (.executionReport header r0)) = some (.executionReport header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [56]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (ExecutionReport.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReport header r0

theorem Message.decodeBytes_cancelReject (header : Header) (r0 : CancelReject) :
    Message.decodeBytes (Message.encode (.cancelReject header r0)) = some (.cancelReject header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [57]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (CancelReject.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_cancelReject header r0

theorem Message.decodeBytes_businessMessageReject (header : Header) (r0 : BusinessMessageReject) :
    Message.decodeBytes (Message.encode (.businessMessageReject header r0)) = some (.businessMessageReject header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [106]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (BusinessMessageReject.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_businessMessageReject header r0

theorem Message.decodeBytes_userResponse (header : Header) (r0 : UserResponse) :
    Message.decodeBytes (Message.encode (.userResponse header r0)) = some (.userResponse header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [66, 70]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (UserResponse.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_userResponse header r0

theorem Message.decodeBytes_partyEntitlementsReport (header : Header) (r0 : PartyEntitlementsReport) :
    Message.decodeBytes (Message.encode (.partyEntitlementsReport header r0)) = some (.partyEntitlementsReport header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [67, 86]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (PartyEntitlementsReport.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_partyEntitlementsReport header r0

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
  | cancelReject header r0 => exact Message.decodeBytes_cancelReject header r0
  | businessMessageReject header r0 => exact Message.decodeBytes_businessMessageReject header r0
  | userResponse header r0 => exact Message.decodeBytes_userResponse header r0
  | partyEntitlementsReport header r0 => exact Message.decodeBytes_partyEntitlementsReport header r0

/-- BeginString as the venue fixes it: FIXT.1.1 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 84, 46, 49, 46, 49, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.HkexChinaconnectOrderentryFixV14Exchange
