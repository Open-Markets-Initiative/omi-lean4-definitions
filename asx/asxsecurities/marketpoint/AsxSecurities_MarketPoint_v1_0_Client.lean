import Wire

/-!
# Australian Securities Exchange Market Point v1.0, Client messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.AsxAsxsecuritiesMarketpointFixV10Client

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
  lastMsgSeqNumProcessed : Option (Terminated 1)  -- tag 369

def Header.parts (record : Header) : List Part :=
  [Part.required [52, 57] record.senderCompID,
   Part.required [53, 54] record.targetCompID,
   Part.required [51, 52] record.msgSeqNum,
   Part.required [53, 50] record.sendingTime,
   Part.optional [52, 51] record.possDupFlag,
   Part.optional [57, 55] record.possResend,
   Part.optional [49, 50, 50] record.origSendingTime,
   Part.optional [51, 54, 57] record.lastMsgSeqNumProcessed]

def Header.tags : List (List (List UInt8)) :=
  [[[52, 57]], [[53, 54]], [[51, 52]], [[53, 50]], [[52, 51]], [[57, 55]], [[49, 50, 50]], [[51, 54, 57]]]

theorem Header.shape (record : Header) : record.parts.map Part.tags = Header.tags := rfl

def Header.decode (tokens : List Token) : Option Header := do
  let senderCompID ← readRequired [52, 57] tokens
  let targetCompID ← readRequired [53, 54] tokens
  let msgSeqNum ← readRequired [51, 52] tokens
  let sendingTime ← readRequired [53, 50] tokens
  let possDupFlag ← readOptional [52, 51] tokens
  let possResend ← readOptional [57, 55] tokens
  let origSendingTime ← readOptional [49, 50, 50] tokens
  let lastMsgSeqNumProcessed ← readOptional [51, 54, 57] tokens
  pure { senderCompID, targetCompID, msgSeqNum, sendingTime, possDupFlag, possResend, origSendingTime, lastMsgSeqNumProcessed }

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
  have lastMsgSeqNumProcessed := readOptional_part [51, 54, 57] record.lastMsgSeqNumProcessed tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  simp only [Header.decode, senderCompID, targetCompID, msgSeqNum, sendingTime, possDupFlag, possResend, origSendingTime, lastMsgSeqNumProcessed, some_bind] <;> rfl

theorem Header.taken (record : Header) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [52, 57] record.senderCompID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [53, 54] record.targetCompID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [51, 52] record.msgSeqNum (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [53, 50] record.sendingTime (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [52, 51] record.possDupFlag (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [57, 55] record.possResend (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [49, 50, 50] record.origSendingTime (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [51, 54, 57] record.lastMsgSeqNumProcessed (by decide) (by decide))
          (paired_none pairing))))))))

structure Logon where
  encryptMethod : Terminated 1  -- tag 98
  heartBtInt : Terminated 1  -- tag 108
  resetSeqNumFlag : Option (Terminated 1)  -- tag 141
  username : Option (Terminated 1)  -- tag 553
  password : Option (Terminated 1)  -- tag 554

def Logon.parts (record : Logon) : List Part :=
  [Part.required [57, 56] record.encryptMethod,
   Part.required [49, 48, 56] record.heartBtInt,
   Part.optional [49, 52, 49] record.resetSeqNumFlag,
   Part.optional [53, 53, 51] record.username,
   Part.optional [53, 53, 52] record.password]

def Logon.tags : List (List (List UInt8)) :=
  [[[57, 56]], [[49, 48, 56]], [[49, 52, 49]], [[53, 53, 51]], [[53, 53, 52]]]

theorem Logon.shape (record : Logon) : record.parts.map Part.tags = Logon.tags := rfl

def Logon.decode (tokens : List Token) : Option Logon := do
  let encryptMethod ← readRequired [57, 56] tokens
  let heartBtInt ← readRequired [49, 48, 56] tokens
  let resetSeqNumFlag ← readOptional [49, 52, 49] tokens
  let username ← readOptional [53, 53, 51] tokens
  let password ← readOptional [53, 53, 52] tokens
  pure { encryptMethod, heartBtInt, resetSeqNumFlag, username, password }

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
  have username := readOptional_part [53, 53, 51] record.username tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have password := readOptional_part [53, 53, 52] record.password tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [Logon.decode, encryptMethod, heartBtInt, resetSeqNumFlag, username, password, some_bind] <;> rfl

theorem Logon.taken (record : Logon) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [57, 56] record.encryptMethod (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 48, 56] record.heartBtInt (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [49, 52, 49] record.resetSeqNumFlag (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [53, 53, 51] record.username (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [53, 53, 52] record.password (by decide) (by decide))
       (paired_none pairing)))))

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

structure UserRequest where
  userRequestID : Terminated 1  -- tag 923
  userRequestType : Terminated 1  -- tag 924
  username : Terminated 1  -- tag 553
  password : Option (Terminated 1)  -- tag 554
  newPassword : Option (Terminated 1)  -- tag 925

def UserRequest.parts (record : UserRequest) : List Part :=
  [Part.required [57, 50, 51] record.userRequestID,
   Part.required [57, 50, 52] record.userRequestType,
   Part.required [53, 53, 51] record.username,
   Part.optional [53, 53, 52] record.password,
   Part.optional [57, 50, 53] record.newPassword]

def UserRequest.tags : List (List (List UInt8)) :=
  [[[57, 50, 51]], [[57, 50, 52]], [[53, 53, 51]], [[53, 53, 52]], [[57, 50, 53]]]

theorem UserRequest.shape (record : UserRequest) : record.parts.map Part.tags = UserRequest.tags := rfl

def UserRequest.decode (tokens : List Token) : Option UserRequest := do
  let userRequestID ← readRequired [57, 50, 51] tokens
  let userRequestType ← readRequired [57, 50, 52] tokens
  let username ← readRequired [53, 53, 51] tokens
  let password ← readOptional [53, 53, 52] tokens
  let newPassword ← readOptional [57, 50, 53] tokens
  pure { userRequestID, userRequestType, username, password, newPassword }

theorem UserRequest.decode_agrees (record : UserRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ UserRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    UserRequest.decode tokens = some record := by
  have distinct : UserRequest.tags.flatten.Nodup := by decide +kernel
  have userRequestID := readRequired_part [57, 50, 51] record.userRequestID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have userRequestType := readRequired_part [57, 50, 52] record.userRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have username := readRequired_part [53, 53, 51] record.username tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have password := readOptional_part [53, 53, 52] record.password tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have newPassword := readOptional_part [57, 50, 53] record.newPassword tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [UserRequest.decode, userRequestID, userRequestType, username, password, newPassword, some_bind] <;> rfl

theorem UserRequest.taken (record : UserRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [57, 50, 51] record.userRequestID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [57, 50, 52] record.userRequestType (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [53, 53, 51] record.username (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [53, 53, 52] record.password (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [57, 50, 53] record.newPassword (by decide) (by decide))
       (paired_none pairing)))))

structure NoMDEntryTypes where
  mDEntryType : Terminated 1  -- tag 269

def NoMDEntryTypes.parts (record : NoMDEntryTypes) : List Part :=
  [Part.required [50, 54, 57] record.mDEntryType]

def NoMDEntryTypes.tags : List (List (List UInt8)) :=
  [[[50, 54, 57]]]

theorem NoMDEntryTypes.shape (record : NoMDEntryTypes) : record.parts.map Part.tags = NoMDEntryTypes.tags := rfl

def NoMDEntryTypes.decode (tokens : List Token) : Option NoMDEntryTypes := do
  let mDEntryType ← readRequired [50, 54, 57] tokens
  pure { mDEntryType }

theorem NoMDEntryTypes.decode_agrees (record : NoMDEntryTypes) (tokens : List Token)
    (agrees : ∀ tags ∈ NoMDEntryTypes.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoMDEntryTypes.decode tokens = some record := by
  have distinct : NoMDEntryTypes.tags.flatten.Nodup := by decide +kernel
  have mDEntryType := readRequired_part [50, 54, 57] record.mDEntryType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [NoMDEntryTypes.decode, mDEntryType, some_bind] <;> rfl

theorem NoMDEntryTypes.taken (record : NoMDEntryTypes) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [50, 54, 57] record.mDEntryType (by decide) (by decide))
   (paired_none pairing)

def NoMDEntryTypes.members : List (List UInt8) := NoMDEntryTypes.tags.flatten

def NoMDEntryTypes.encode (entry : NoMDEntryTypes) : List Token := encodeParts entry.parts

theorem NoMDEntryTypes.decode_encode (entry : NoMDEntryTypes) : NoMDEntryTypes.decode entry.encode = some entry :=
  NoMDEntryTypes.decode_agrees entry _ (fun _ _ => rfl)

theorem NoMDEntryTypes.within (entry : NoMDEntryTypes) : ∀ token ∈ entry.encode, token.tag ∈ NoMDEntryTypes.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoMDEntryTypes.shape] at this

theorem NoMDEntryTypes.led (entry : NoMDEntryTypes) : Lead [50, 54, 57] entry.encode :=
  lead_parts [50, 54, 57] entry.mDEntryType _ NoMDEntryTypes.tags.tail rfl (by decide +kernel)

structure NoRelatedSym where
  symbol : Terminated 1  -- tag 55

def NoRelatedSym.parts (record : NoRelatedSym) : List Part :=
  [Part.required [53, 53] record.symbol]

def NoRelatedSym.tags : List (List (List UInt8)) :=
  [[[53, 53]]]

theorem NoRelatedSym.shape (record : NoRelatedSym) : record.parts.map Part.tags = NoRelatedSym.tags := rfl

def NoRelatedSym.decode (tokens : List Token) : Option NoRelatedSym := do
  let symbol ← readRequired [53, 53] tokens
  pure { symbol }

theorem NoRelatedSym.decode_agrees (record : NoRelatedSym) (tokens : List Token)
    (agrees : ∀ tags ∈ NoRelatedSym.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoRelatedSym.decode tokens = some record := by
  have distinct : NoRelatedSym.tags.flatten.Nodup := by decide +kernel
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [NoRelatedSym.decode, symbol, some_bind] <;> rfl

theorem NoRelatedSym.taken (record : NoRelatedSym) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
   (paired_none pairing)

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

structure MarketDataRequest where
  mDReqID : Terminated 1  -- tag 262
  subscriptionRequestType : Terminated 1  -- tag 263
  marketDepth : Terminated 1  -- tag 264
  mDUpdateType : Option (Terminated 1)  -- tag 265
  aggregatedBook : Option (Terminated 1)  -- tag 266
  undisclosedQtyIndicator : Option (Terminated 1)  -- tag 7956
  mDQuoteType : Option (Terminated 1)  -- tag 1070
  noMDEntryTypes : List NoMDEntryTypes  -- tag 267
  noRelatedSym : List NoRelatedSym  -- tag 146

def MarketDataRequest.parts (record : MarketDataRequest) : List Part :=
  [Part.required [50, 54, 50] record.mDReqID,
   Part.required [50, 54, 51] record.subscriptionRequestType,
   Part.required [50, 54, 52] record.marketDepth,
   Part.optional [50, 54, 53] record.mDUpdateType,
   Part.optional [50, 54, 54] record.aggregatedBook,
   Part.optional [55, 57, 53, 54] record.undisclosedQtyIndicator,
   Part.optional [49, 48, 55, 48] record.mDQuoteType,
   Part.group [50, 54, 55] NoMDEntryTypes.members NoMDEntryTypes.encode NoMDEntryTypes.within record.noMDEntryTypes,
   Part.group [49, 52, 54] NoRelatedSym.members NoRelatedSym.encode NoRelatedSym.within record.noRelatedSym]

def MarketDataRequest.tags : List (List (List UInt8)) :=
  [[[50, 54, 50]], [[50, 54, 51]], [[50, 54, 52]], [[50, 54, 53]], [[50, 54, 54]], [[55, 57, 53, 54]], [[49, 48, 55, 48]], [50, 54, 55] :: NoMDEntryTypes.members, [49, 52, 54] :: NoRelatedSym.members]

theorem MarketDataRequest.shape (record : MarketDataRequest) : record.parts.map Part.tags = MarketDataRequest.tags := rfl

def MarketDataRequest.decode (tokens : List Token) : Option MarketDataRequest := do
  let mDReqID ← readRequired [50, 54, 50] tokens
  let subscriptionRequestType ← readRequired [50, 54, 51] tokens
  let marketDepth ← readRequired [50, 54, 52] tokens
  let mDUpdateType ← readOptional [50, 54, 53] tokens
  let aggregatedBook ← readOptional [50, 54, 54] tokens
  let undisclosedQtyIndicator ← readOptional [55, 57, 53, 54] tokens
  let mDQuoteType ← readOptional [49, 48, 55, 48] tokens
  let noMDEntryTypes ← readGroup [50, 54, 55] [50, 54, 57] NoMDEntryTypes.members NoMDEntryTypes.decode tokens
  let noRelatedSym ← readGroup [49, 52, 54] [53, 53] NoRelatedSym.members NoRelatedSym.decode tokens
  pure { mDReqID, subscriptionRequestType, marketDepth, mDUpdateType, aggregatedBook, undisclosedQtyIndicator, mDQuoteType, noMDEntryTypes, noRelatedSym }

theorem MarketDataRequest.decode_agrees (record : MarketDataRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ MarketDataRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    MarketDataRequest.decode tokens = some record := by
  have distinct : MarketDataRequest.tags.flatten.Nodup := by decide +kernel
  have mDReqID := readRequired_part [50, 54, 50] record.mDReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have subscriptionRequestType := readRequired_part [50, 54, 51] record.subscriptionRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have marketDepth := readRequired_part [50, 54, 52] record.marketDepth tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have mDUpdateType := readOptional_part [50, 54, 53] record.mDUpdateType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have aggregatedBook := readOptional_part [50, 54, 54] record.aggregatedBook tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have undisclosedQtyIndicator := readOptional_part [55, 57, 53, 54] record.undisclosedQtyIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have mDQuoteType := readOptional_part [49, 48, 55, 48] record.mDQuoteType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have noMDEntryTypes := readGroup_part [50, 54, 55] [50, 54, 57] NoMDEntryTypes.members NoMDEntryTypes.encode NoMDEntryTypes.within NoMDEntryTypes.decode NoMDEntryTypes.decode_encode NoMDEntryTypes.led record.noMDEntryTypes tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have noRelatedSym := readGroup_part [49, 52, 54] [53, 53] NoRelatedSym.members NoRelatedSym.encode NoRelatedSym.within NoRelatedSym.decode NoRelatedSym.decode_encode NoRelatedSym.led record.noRelatedSym tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  simp only [MarketDataRequest.decode, mDReqID, subscriptionRequestType, marketDepth, mDUpdateType, aggregatedBook, undisclosedQtyIndicator, mDQuoteType, noMDEntryTypes, noRelatedSym, some_bind] <;> rfl

theorem MarketDataRequest.taken (record : MarketDataRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [50, 54, 50] record.mDReqID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [50, 54, 51] record.subscriptionRequestType (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [50, 54, 52] record.marketDepth (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [50, 54, 53] record.mDUpdateType (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [50, 54, 54] record.aggregatedBook (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [55, 57, 53, 54] record.undisclosedQtyIndicator (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [49, 48, 55, 48] record.mDQuoteType (by decide) (by decide))
         (paired_cons pairing _ _ (paired_group pairing [50, 54, 55] NoMDEntryTypes.members NoMDEntryTypes.encode NoMDEntryTypes.within (by decide) (by decide) NoMDEntryTypes.taken record.noMDEntryTypes)
          (paired_cons pairing _ _ (paired_group pairing [49, 52, 54] NoRelatedSym.members NoRelatedSym.encode NoRelatedSym.within (by decide) (by decide) NoRelatedSym.taken record.noRelatedSym)
           (paired_none pairing)))))))))

structure SecurityStatusRequest where
  securityStatusReqID : Terminated 1  -- tag 324
  symbol : Terminated 1  -- tag 55
  subscriptionRequestType : Option (Terminated 1)  -- tag 263
  mDQuoteType : Option (Terminated 1)  -- tag 1070

def SecurityStatusRequest.parts (record : SecurityStatusRequest) : List Part :=
  [Part.required [51, 50, 52] record.securityStatusReqID,
   Part.required [53, 53] record.symbol,
   Part.optional [50, 54, 51] record.subscriptionRequestType,
   Part.optional [49, 48, 55, 48] record.mDQuoteType]

def SecurityStatusRequest.tags : List (List (List UInt8)) :=
  [[[51, 50, 52]], [[53, 53]], [[50, 54, 51]], [[49, 48, 55, 48]]]

theorem SecurityStatusRequest.shape (record : SecurityStatusRequest) : record.parts.map Part.tags = SecurityStatusRequest.tags := rfl

def SecurityStatusRequest.decode (tokens : List Token) : Option SecurityStatusRequest := do
  let securityStatusReqID ← readRequired [51, 50, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let subscriptionRequestType ← readOptional [50, 54, 51] tokens
  let mDQuoteType ← readOptional [49, 48, 55, 48] tokens
  pure { securityStatusReqID, symbol, subscriptionRequestType, mDQuoteType }

theorem SecurityStatusRequest.decode_agrees (record : SecurityStatusRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ SecurityStatusRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    SecurityStatusRequest.decode tokens = some record := by
  have distinct : SecurityStatusRequest.tags.flatten.Nodup := by decide +kernel
  have securityStatusReqID := readRequired_part [51, 50, 52] record.securityStatusReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have subscriptionRequestType := readOptional_part [50, 54, 51] record.subscriptionRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have mDQuoteType := readOptional_part [49, 48, 55, 48] record.mDQuoteType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [SecurityStatusRequest.decode, securityStatusReqID, symbol, subscriptionRequestType, mDQuoteType, some_bind] <;> rfl

theorem SecurityStatusRequest.taken (record : SecurityStatusRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 50, 52] record.securityStatusReqID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [50, 54, 51] record.subscriptionRequestType (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [49, 48, 55, 48] record.mDQuoteType (by decide) (by decide))
      (paired_none pairing))))

structure TradingSessionStatusRequest where
  tradSesReqID : Terminated 1  -- tag 335
  subscriptionRequestType : Option (Terminated 1)  -- tag 263

def TradingSessionStatusRequest.parts (record : TradingSessionStatusRequest) : List Part :=
  [Part.required [51, 51, 53] record.tradSesReqID,
   Part.optional [50, 54, 51] record.subscriptionRequestType]

def TradingSessionStatusRequest.tags : List (List (List UInt8)) :=
  [[[51, 51, 53]], [[50, 54, 51]]]

theorem TradingSessionStatusRequest.shape (record : TradingSessionStatusRequest) : record.parts.map Part.tags = TradingSessionStatusRequest.tags := rfl

def TradingSessionStatusRequest.decode (tokens : List Token) : Option TradingSessionStatusRequest := do
  let tradSesReqID ← readRequired [51, 51, 53] tokens
  let subscriptionRequestType ← readOptional [50, 54, 51] tokens
  pure { tradSesReqID, subscriptionRequestType }

theorem TradingSessionStatusRequest.decode_agrees (record : TradingSessionStatusRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ TradingSessionStatusRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TradingSessionStatusRequest.decode tokens = some record := by
  have distinct : TradingSessionStatusRequest.tags.flatten.Nodup := by decide +kernel
  have tradSesReqID := readRequired_part [51, 51, 53] record.tradSesReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have subscriptionRequestType := readOptional_part [50, 54, 51] record.subscriptionRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [TradingSessionStatusRequest.decode, tradSesReqID, subscriptionRequestType, some_bind] <;> rfl

theorem TradingSessionStatusRequest.taken (record : TradingSessionStatusRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 51, 53] record.tradSesReqID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [50, 54, 51] record.subscriptionRequestType (by decide) (by decide))
    (paired_none pairing))

inductive Message where
  | logon (header : Header) (r0 : Logon)
  | heartbeat (header : Header) (r0 : Heartbeat)
  | testRequest (header : Header) (r0 : TestRequest)
  | resendRequest (header : Header) (r0 : ResendRequest)
  | reject (header : Header) (r0 : Reject)
  | sequenceReset (header : Header) (r0 : SequenceReset)
  | logout (header : Header) (r0 : Logout)
  | userRequest (header : Header) (r0 : UserRequest)
  | marketDataRequest (header : Header) (r0 : MarketDataRequest)
  | securityStatusRequest (header : Header) (r0 : SecurityStatusRequest)
  | tradingSessionStatusRequest (header : Header) (r0 : TradingSessionStatusRequest)

def Message.tokens : Message → List Token
  | .logon header r0 => ⟨[51, 53], [65]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .heartbeat header r0 => ⟨[51, 53], [48]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .testRequest header r0 => ⟨[51, 53], [49]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .resendRequest header r0 => ⟨[51, 53], [50]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .reject header r0 => ⟨[51, 53], [51]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .sequenceReset header r0 => ⟨[51, 53], [52]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logout header r0 => ⟨[51, 53], [53]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .userRequest header r0 => ⟨[51, 53], [66, 69]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .marketDataRequest header r0 => ⟨[51, 53], [86]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .securityStatusRequest header r0 => ⟨[51, 53], [101]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .tradingSessionStatusRequest header r0 => ⟨[51, 53], [103]⟩ :: encodeParts (header.parts ++ r0.parts)

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
      else if token.value = [66, 69] then
        if known (Header.tags ++ UserRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← UserRequest.decode rest
          pure (.userRequest header r0)
        else none
      else if token.value = [86] then
        if known (Header.tags ++ MarketDataRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← MarketDataRequest.decode rest
          pure (.marketDataRequest header r0)
        else none
      else if token.value = [101] then
        if known (Header.tags ++ SecurityStatusRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← SecurityStatusRequest.decode rest
          pure (.securityStatusRequest header r0)
        else none
      else if token.value = [103] then
        if known (Header.tags ++ TradingSessionStatusRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← TradingSessionStatusRequest.decode rest
          pure (.tradingSessionStatusRequest header r0)
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

theorem Message.decode_userRequest (header : Header) (r0 : UserRequest) :
    Message.decode (Message.tokens (.userRequest header r0)) = some (.userRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (UserRequest.tags) rfl rfl (by decide +kernel))
  have c1 := UserRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (UserRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ UserRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_marketDataRequest (header : Header) (r0 : MarketDataRequest) :
    Message.decode (Message.tokens (.marketDataRequest header r0)) = some (.marketDataRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (MarketDataRequest.tags) rfl rfl (by decide +kernel))
  have c1 := MarketDataRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (MarketDataRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ MarketDataRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_securityStatusRequest (header : Header) (r0 : SecurityStatusRequest) :
    Message.decode (Message.tokens (.securityStatusRequest header r0)) = some (.securityStatusRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (SecurityStatusRequest.tags) rfl rfl (by decide +kernel))
  have c1 := SecurityStatusRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (SecurityStatusRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ SecurityStatusRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tradingSessionStatusRequest (header : Header) (r0 : TradingSessionStatusRequest) :
    Message.decode (Message.tokens (.tradingSessionStatusRequest header r0)) = some (.tradingSessionStatusRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (TradingSessionStatusRequest.tags) rfl rfl (by decide +kernel))
  have c1 := TradingSessionStatusRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (TradingSessionStatusRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ TradingSessionStatusRequest.tags) rfl
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
  | userRequest header r0 => exact Message.decode_userRequest header r0
  | marketDataRequest header r0 => exact Message.decode_marketDataRequest header r0
  | securityStatusRequest header r0 => exact Message.decode_securityStatusRequest header r0
  | tradingSessionStatusRequest header r0 => exact Message.decode_tradingSessionStatusRequest header r0

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

theorem Message.decodeBytes_userRequest (header : Header) (r0 : UserRequest) :
    Message.decodeBytes (Message.encode (.userRequest header r0)) = some (.userRequest header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [66, 69]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (UserRequest.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_userRequest header r0

theorem Message.decodeBytes_marketDataRequest (header : Header) (r0 : MarketDataRequest) :
    Message.decodeBytes (Message.encode (.marketDataRequest header r0)) = some (.marketDataRequest header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [86]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (MarketDataRequest.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_marketDataRequest header r0

theorem Message.decodeBytes_securityStatusRequest (header : Header) (r0 : SecurityStatusRequest) :
    Message.decodeBytes (Message.encode (.securityStatusRequest header r0)) = some (.securityStatusRequest header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [101]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (SecurityStatusRequest.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_securityStatusRequest header r0

theorem Message.decodeBytes_tradingSessionStatusRequest (header : Header) (r0 : TradingSessionStatusRequest) :
    Message.decodeBytes (Message.encode (.tradingSessionStatusRequest header r0)) = some (.tradingSessionStatusRequest header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [103]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (TradingSessionStatusRequest.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_tradingSessionStatusRequest header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | logon header r0 => exact Message.decodeBytes_logon header r0
  | heartbeat header r0 => exact Message.decodeBytes_heartbeat header r0
  | testRequest header r0 => exact Message.decodeBytes_testRequest header r0
  | resendRequest header r0 => exact Message.decodeBytes_resendRequest header r0
  | reject header r0 => exact Message.decodeBytes_reject header r0
  | sequenceReset header r0 => exact Message.decodeBytes_sequenceReset header r0
  | logout header r0 => exact Message.decodeBytes_logout header r0
  | userRequest header r0 => exact Message.decodeBytes_userRequest header r0
  | marketDataRequest header r0 => exact Message.decodeBytes_marketDataRequest header r0
  | securityStatusRequest header r0 => exact Message.decodeBytes_securityStatusRequest header r0
  | tradingSessionStatusRequest header r0 => exact Message.decodeBytes_tradingSessionStatusRequest header r0

/-- BeginString as the venue states it: one of FIX.4.2, FIX.4.4, read with the message -/
def begins : List (List UInt8) := [[70, 73, 88, 46, 52, 46, 50], [70, 73, 88, 46, 52, 46, 52]]

/-- A packet: the BeginString it was sent under, and the message -/
abbrev Packet := Terminated 1 × Message

def Packet.encode (packet : Packet) : List UInt8 := encodeFixAmong Message.encode packet

def Packet.decode (bytes : List UInt8) : Option (Packet × List UInt8) := decodeFixAmong begins Message.decodeBytes bytes

theorem Packet.decode_encode (packet : Packet) (stated : packet.1.val ∈ begins) (rest : List UInt8) :
    Packet.decode (Packet.encode packet ++ rest) = some (packet, rest) :=
  decodeFixAmong_encodeFixAmong begins Message.encode Message.decodeBytes Message.decodeBytes_encode packet stated rest

end Omi.AsxAsxsecuritiesMarketpointFixV10Client
