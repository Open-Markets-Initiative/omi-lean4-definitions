import Wire

/-!
# Taiwan Futures Exchange Order Entry v3.1.2, Client messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.TaifexTaifexderivativesOrderentryFix42V312Client

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

structure NewOrderSingle where
  clOrdID : Terminated 1  -- tag 11
  taifexNoPartyIDs : List TaifexNoPartyIDs  -- tag 44453
  account : Terminated 1  -- tag 1
  symbol : Terminated 1  -- tag 55
  side : Terminated 1  -- tag 54
  transactTime : Terminated 1  -- tag 60
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  price : Terminated 1  -- tag 44
  timeInForce : Terminated 1  -- tag 59
  positionEffect : Terminated 1  -- tag 77
  taifexCFICode : Terminated 1  -- tag 44461
  handlInst : Terminated 1  -- tag 21
  taifexSymbolType : Terminated 1  -- tag 10000
  taifexOrderSource : Terminated 1  -- tag 10001
  taifexInfoSource : Option (Terminated 1)  -- tag 10002

def NewOrderSingle.parts (record : NewOrderSingle) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.group [52, 52, 52, 53, 51] TaifexNoPartyIDs.members TaifexNoPartyIDs.encode TaifexNoPartyIDs.within record.taifexNoPartyIDs,
   Part.required [49] record.account,
   Part.required [53, 53] record.symbol,
   Part.required [53, 52] record.side,
   Part.required [54, 48] record.transactTime,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.required [52, 52] record.price,
   Part.required [53, 57] record.timeInForce,
   Part.required [55, 55] record.positionEffect,
   Part.required [52, 52, 52, 54, 49] record.taifexCFICode,
   Part.required [50, 49] record.handlInst,
   Part.required [49, 48, 48, 48, 48] record.taifexSymbolType,
   Part.required [49, 48, 48, 48, 49] record.taifexOrderSource,
   Part.optional [49, 48, 48, 48, 50] record.taifexInfoSource]

def NewOrderSingle.tags : List (List (List UInt8)) :=
  [[[49, 49]], [52, 52, 52, 53, 51] :: TaifexNoPartyIDs.members, [[49]], [[53, 53]], [[53, 52]], [[54, 48]], [[51, 56]], [[52, 48]], [[52, 52]], [[53, 57]], [[55, 55]], [[52, 52, 52, 54, 49]], [[50, 49]], [[49, 48, 48, 48, 48]], [[49, 48, 48, 48, 49]], [[49, 48, 48, 48, 50]]]

theorem NewOrderSingle.shape (record : NewOrderSingle) : record.parts.map Part.tags = NewOrderSingle.tags := rfl

def NewOrderSingle.decode (tokens : List Token) : Option NewOrderSingle := do
  let clOrdID ← readRequired [49, 49] tokens
  let taifexNoPartyIDs ← readGroup [52, 52, 52, 53, 51] [52, 52, 52, 52, 56] TaifexNoPartyIDs.members TaifexNoPartyIDs.decode tokens
  let account ← readRequired [49] tokens
  let symbol ← readRequired [53, 53] tokens
  let side ← readRequired [53, 52] tokens
  let transactTime ← readRequired [54, 48] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readRequired [52, 52] tokens
  let timeInForce ← readRequired [53, 57] tokens
  let positionEffect ← readRequired [55, 55] tokens
  let taifexCFICode ← readRequired [52, 52, 52, 54, 49] tokens
  let handlInst ← readRequired [50, 49] tokens
  let taifexSymbolType ← readRequired [49, 48, 48, 48, 48] tokens
  let taifexOrderSource ← readRequired [49, 48, 48, 48, 49] tokens
  let taifexInfoSource ← readOptional [49, 48, 48, 48, 50] tokens
  pure { clOrdID, taifexNoPartyIDs, account, symbol, side, transactTime, orderQty, ordType, price, timeInForce, positionEffect, taifexCFICode, handlInst, taifexSymbolType, taifexOrderSource, taifexInfoSource }

theorem NewOrderSingle.decode_agrees (record : NewOrderSingle) (tokens : List Token)
    (agrees : ∀ tags ∈ NewOrderSingle.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NewOrderSingle.decode tokens = some record := by
  have distinct : NewOrderSingle.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have taifexNoPartyIDs := readGroup_part [52, 52, 52, 53, 51] [52, 52, 52, 52, 56] TaifexNoPartyIDs.members TaifexNoPartyIDs.encode TaifexNoPartyIDs.within TaifexNoPartyIDs.decode TaifexNoPartyIDs.decode_encode TaifexNoPartyIDs.led record.taifexNoPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have account := readRequired_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have price := readRequired_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have timeInForce := readRequired_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have positionEffect := readRequired_part [55, 55] record.positionEffect tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have taifexCFICode := readRequired_part [52, 52, 52, 54, 49] record.taifexCFICode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have handlInst := readRequired_part [50, 49] record.handlInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have taifexSymbolType := readRequired_part [49, 48, 48, 48, 48] record.taifexSymbolType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have taifexOrderSource := readRequired_part [49, 48, 48, 48, 49] record.taifexOrderSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have taifexInfoSource := readOptional_part [49, 48, 48, 48, 50] record.taifexInfoSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  simp only [NewOrderSingle.decode, clOrdID, taifexNoPartyIDs, account, symbol, side, transactTime, orderQty, ordType, price, timeInForce, positionEffect, taifexCFICode, handlInst, taifexSymbolType, taifexOrderSource, taifexInfoSource, some_bind] <;> rfl

theorem NewOrderSingle.taken (record : NewOrderSingle) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_group pairing [52, 52, 52, 53, 51] TaifexNoPartyIDs.members TaifexNoPartyIDs.encode TaifexNoPartyIDs.within (by decide) (by decide) TaifexNoPartyIDs.taken record.taifexNoPartyIDs)
    (paired_cons pairing _ _ (paired_required pairing [49] record.account (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [53, 52] record.side (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [54, 48] record.transactTime (by decide) (by decide))
        (paired_cons pairing _ _ (paired_required pairing [51, 56] record.orderQty (by decide) (by decide))
         (paired_cons pairing _ _ (paired_required pairing [52, 48] record.ordType (by decide) (by decide))
          (paired_cons pairing _ _ (paired_required pairing [52, 52] record.price (by decide) (by decide))
           (paired_cons pairing _ _ (paired_required pairing [53, 57] record.timeInForce (by decide) (by decide))
            (paired_cons pairing _ _ (paired_required pairing [55, 55] record.positionEffect (by decide) (by decide))
             (paired_cons pairing _ _ (paired_required pairing [52, 52, 52, 54, 49] record.taifexCFICode (by decide) (by decide))
              (paired_cons pairing _ _ (paired_required pairing [50, 49] record.handlInst (by decide) (by decide))
               (paired_cons pairing _ _ (paired_required pairing [49, 48, 48, 48, 48] record.taifexSymbolType (by decide) (by decide))
                (paired_cons pairing _ _ (paired_required pairing [49, 48, 48, 48, 49] record.taifexOrderSource (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_optional pairing [49, 48, 48, 48, 50] record.taifexInfoSource (by decide) (by decide))
                  (paired_none pairing))))))))))))))))

structure TaifexNoLegs where
  taifexLegSymbol : Terminated 1  -- tag 44600
  taifexLegCFICode : Terminated 1  -- tag 44608
  taifexLegMaturityMonthYear : Terminated 1  -- tag 44610
  taifexLegSide : Terminated 1  -- tag 44624
  taifexLegQty : Terminated 1  -- tag 44687

def TaifexNoLegs.parts (record : TaifexNoLegs) : List Part :=
  [Part.required [52, 52, 54, 48, 48] record.taifexLegSymbol,
   Part.required [52, 52, 54, 48, 56] record.taifexLegCFICode,
   Part.required [52, 52, 54, 49, 48] record.taifexLegMaturityMonthYear,
   Part.required [52, 52, 54, 50, 52] record.taifexLegSide,
   Part.required [52, 52, 54, 56, 55] record.taifexLegQty]

def TaifexNoLegs.tags : List (List (List UInt8)) :=
  [[[52, 52, 54, 48, 48]], [[52, 52, 54, 48, 56]], [[52, 52, 54, 49, 48]], [[52, 52, 54, 50, 52]], [[52, 52, 54, 56, 55]]]

theorem TaifexNoLegs.shape (record : TaifexNoLegs) : record.parts.map Part.tags = TaifexNoLegs.tags := rfl

def TaifexNoLegs.decode (tokens : List Token) : Option TaifexNoLegs := do
  let taifexLegSymbol ← readRequired [52, 52, 54, 48, 48] tokens
  let taifexLegCFICode ← readRequired [52, 52, 54, 48, 56] tokens
  let taifexLegMaturityMonthYear ← readRequired [52, 52, 54, 49, 48] tokens
  let taifexLegSide ← readRequired [52, 52, 54, 50, 52] tokens
  let taifexLegQty ← readRequired [52, 52, 54, 56, 55] tokens
  pure { taifexLegSymbol, taifexLegCFICode, taifexLegMaturityMonthYear, taifexLegSide, taifexLegQty }

theorem TaifexNoLegs.decode_agrees (record : TaifexNoLegs) (tokens : List Token)
    (agrees : ∀ tags ∈ TaifexNoLegs.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TaifexNoLegs.decode tokens = some record := by
  have distinct : TaifexNoLegs.tags.flatten.Nodup := by decide +kernel
  have taifexLegSymbol := readRequired_part [52, 52, 54, 48, 48] record.taifexLegSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have taifexLegCFICode := readRequired_part [52, 52, 54, 48, 56] record.taifexLegCFICode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have taifexLegMaturityMonthYear := readRequired_part [52, 52, 54, 49, 48] record.taifexLegMaturityMonthYear tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have taifexLegSide := readRequired_part [52, 52, 54, 50, 52] record.taifexLegSide tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have taifexLegQty := readRequired_part [52, 52, 54, 56, 55] record.taifexLegQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [TaifexNoLegs.decode, taifexLegSymbol, taifexLegCFICode, taifexLegMaturityMonthYear, taifexLegSide, taifexLegQty, some_bind] <;> rfl

theorem TaifexNoLegs.taken (record : TaifexNoLegs) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [52, 52, 54, 48, 48] record.taifexLegSymbol (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [52, 52, 54, 48, 56] record.taifexLegCFICode (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [52, 52, 54, 49, 48] record.taifexLegMaturityMonthYear (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [52, 52, 54, 50, 52] record.taifexLegSide (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [52, 52, 54, 56, 55] record.taifexLegQty (by decide) (by decide))
       (paired_none pairing)))))

def TaifexNoLegs.members : List (List UInt8) := TaifexNoLegs.tags.flatten

def TaifexNoLegs.encode (entry : TaifexNoLegs) : List Token := encodeParts entry.parts

theorem TaifexNoLegs.decode_encode (entry : TaifexNoLegs) : TaifexNoLegs.decode entry.encode = some entry :=
  TaifexNoLegs.decode_agrees entry _ (fun _ _ => rfl)

theorem TaifexNoLegs.within (entry : TaifexNoLegs) : ∀ token ∈ entry.encode, token.tag ∈ TaifexNoLegs.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [TaifexNoLegs.shape] at this

theorem TaifexNoLegs.led (entry : TaifexNoLegs) : Lead [52, 52, 54, 48, 48] entry.encode :=
  lead_parts [52, 52, 54, 48, 48] entry.taifexLegSymbol _ TaifexNoLegs.tags.tail rfl (by decide +kernel)

structure NewOrderMultileg where
  clOrdID : Terminated 1  -- tag 11
  taifexNoPartyIDs : List TaifexNoPartyIDs  -- tag 44453
  account : Terminated 1  -- tag 1
  symbol : Terminated 1  -- tag 55
  side : Terminated 1  -- tag 54
  taifexNoLegs : List TaifexNoLegs  -- tag 44555
  transactTime : Terminated 1  -- tag 60
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  price : Terminated 1  -- tag 44
  timeInForce : Terminated 1  -- tag 59
  positionEffect : Terminated 1  -- tag 77
  taifexSymbolType : Terminated 1  -- tag 10000
  taifexOrderSource : Terminated 1  -- tag 10001
  taifexInfoSource : Option (Terminated 1)  -- tag 10002

def NewOrderMultileg.parts (record : NewOrderMultileg) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.group [52, 52, 52, 53, 51] TaifexNoPartyIDs.members TaifexNoPartyIDs.encode TaifexNoPartyIDs.within record.taifexNoPartyIDs,
   Part.required [49] record.account,
   Part.required [53, 53] record.symbol,
   Part.required [53, 52] record.side,
   Part.group [52, 52, 53, 53, 53] TaifexNoLegs.members TaifexNoLegs.encode TaifexNoLegs.within record.taifexNoLegs,
   Part.required [54, 48] record.transactTime,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.required [52, 52] record.price,
   Part.required [53, 57] record.timeInForce,
   Part.required [55, 55] record.positionEffect,
   Part.required [49, 48, 48, 48, 48] record.taifexSymbolType,
   Part.required [49, 48, 48, 48, 49] record.taifexOrderSource,
   Part.optional [49, 48, 48, 48, 50] record.taifexInfoSource]

def NewOrderMultileg.tags : List (List (List UInt8)) :=
  [[[49, 49]], [52, 52, 52, 53, 51] :: TaifexNoPartyIDs.members, [[49]], [[53, 53]], [[53, 52]], [52, 52, 53, 53, 53] :: TaifexNoLegs.members, [[54, 48]], [[51, 56]], [[52, 48]], [[52, 52]], [[53, 57]], [[55, 55]], [[49, 48, 48, 48, 48]], [[49, 48, 48, 48, 49]], [[49, 48, 48, 48, 50]]]

theorem NewOrderMultileg.shape (record : NewOrderMultileg) : record.parts.map Part.tags = NewOrderMultileg.tags := rfl

def NewOrderMultileg.decode (tokens : List Token) : Option NewOrderMultileg := do
  let clOrdID ← readRequired [49, 49] tokens
  let taifexNoPartyIDs ← readGroup [52, 52, 52, 53, 51] [52, 52, 52, 52, 56] TaifexNoPartyIDs.members TaifexNoPartyIDs.decode tokens
  let account ← readRequired [49] tokens
  let symbol ← readRequired [53, 53] tokens
  let side ← readRequired [53, 52] tokens
  let taifexNoLegs ← readGroup [52, 52, 53, 53, 53] [52, 52, 54, 48, 48] TaifexNoLegs.members TaifexNoLegs.decode tokens
  let transactTime ← readRequired [54, 48] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readRequired [52, 52] tokens
  let timeInForce ← readRequired [53, 57] tokens
  let positionEffect ← readRequired [55, 55] tokens
  let taifexSymbolType ← readRequired [49, 48, 48, 48, 48] tokens
  let taifexOrderSource ← readRequired [49, 48, 48, 48, 49] tokens
  let taifexInfoSource ← readOptional [49, 48, 48, 48, 50] tokens
  pure { clOrdID, taifexNoPartyIDs, account, symbol, side, taifexNoLegs, transactTime, orderQty, ordType, price, timeInForce, positionEffect, taifexSymbolType, taifexOrderSource, taifexInfoSource }

theorem NewOrderMultileg.decode_agrees (record : NewOrderMultileg) (tokens : List Token)
    (agrees : ∀ tags ∈ NewOrderMultileg.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NewOrderMultileg.decode tokens = some record := by
  have distinct : NewOrderMultileg.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have taifexNoPartyIDs := readGroup_part [52, 52, 52, 53, 51] [52, 52, 52, 52, 56] TaifexNoPartyIDs.members TaifexNoPartyIDs.encode TaifexNoPartyIDs.within TaifexNoPartyIDs.decode TaifexNoPartyIDs.decode_encode TaifexNoPartyIDs.led record.taifexNoPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have account := readRequired_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have taifexNoLegs := readGroup_part [52, 52, 53, 53, 53] [52, 52, 54, 48, 48] TaifexNoLegs.members TaifexNoLegs.encode TaifexNoLegs.within TaifexNoLegs.decode TaifexNoLegs.decode_encode TaifexNoLegs.led record.taifexNoLegs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have price := readRequired_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have timeInForce := readRequired_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have positionEffect := readRequired_part [55, 55] record.positionEffect tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have taifexSymbolType := readRequired_part [49, 48, 48, 48, 48] record.taifexSymbolType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have taifexOrderSource := readRequired_part [49, 48, 48, 48, 49] record.taifexOrderSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have taifexInfoSource := readOptional_part [49, 48, 48, 48, 50] record.taifexInfoSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  simp only [NewOrderMultileg.decode, clOrdID, taifexNoPartyIDs, account, symbol, side, taifexNoLegs, transactTime, orderQty, ordType, price, timeInForce, positionEffect, taifexSymbolType, taifexOrderSource, taifexInfoSource, some_bind] <;> rfl

theorem NewOrderMultileg.taken (record : NewOrderMultileg) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_group pairing [52, 52, 52, 53, 51] TaifexNoPartyIDs.members TaifexNoPartyIDs.encode TaifexNoPartyIDs.within (by decide) (by decide) TaifexNoPartyIDs.taken record.taifexNoPartyIDs)
    (paired_cons pairing _ _ (paired_required pairing [49] record.account (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [53, 52] record.side (by decide) (by decide))
       (paired_cons pairing _ _ (paired_group pairing [52, 52, 53, 53, 53] TaifexNoLegs.members TaifexNoLegs.encode TaifexNoLegs.within (by decide) (by decide) TaifexNoLegs.taken record.taifexNoLegs)
        (paired_cons pairing _ _ (paired_required pairing [54, 48] record.transactTime (by decide) (by decide))
         (paired_cons pairing _ _ (paired_required pairing [51, 56] record.orderQty (by decide) (by decide))
          (paired_cons pairing _ _ (paired_required pairing [52, 48] record.ordType (by decide) (by decide))
           (paired_cons pairing _ _ (paired_required pairing [52, 52] record.price (by decide) (by decide))
            (paired_cons pairing _ _ (paired_required pairing [53, 57] record.timeInForce (by decide) (by decide))
             (paired_cons pairing _ _ (paired_required pairing [55, 55] record.positionEffect (by decide) (by decide))
              (paired_cons pairing _ _ (paired_required pairing [49, 48, 48, 48, 48] record.taifexSymbolType (by decide) (by decide))
               (paired_cons pairing _ _ (paired_required pairing [49, 48, 48, 48, 49] record.taifexOrderSource (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [49, 48, 48, 48, 50] record.taifexInfoSource (by decide) (by decide))
                 (paired_none pairing)))))))))))))))

structure OrderCancelRequest where
  origClOrdID : Terminated 1  -- tag 41
  clOrdID : Terminated 1  -- tag 11
  taifexNoPartyIDs : List TaifexNoPartyIDs  -- tag 44453
  symbol : Terminated 1  -- tag 55
  side : Terminated 1  -- tag 54
  transactTime : Terminated 1  -- tag 60
  taifexCFICode : Terminated 1  -- tag 44461
  taifexSymbolType : Terminated 1  -- tag 10000
  taifexOrderSource : Terminated 1  -- tag 10001
  taifexInfoSource : Option (Terminated 1)  -- tag 10002

def OrderCancelRequest.parts (record : OrderCancelRequest) : List Part :=
  [Part.required [52, 49] record.origClOrdID,
   Part.required [49, 49] record.clOrdID,
   Part.group [52, 52, 52, 53, 51] TaifexNoPartyIDs.members TaifexNoPartyIDs.encode TaifexNoPartyIDs.within record.taifexNoPartyIDs,
   Part.required [53, 53] record.symbol,
   Part.required [53, 52] record.side,
   Part.required [54, 48] record.transactTime,
   Part.required [52, 52, 52, 54, 49] record.taifexCFICode,
   Part.required [49, 48, 48, 48, 48] record.taifexSymbolType,
   Part.required [49, 48, 48, 48, 49] record.taifexOrderSource,
   Part.optional [49, 48, 48, 48, 50] record.taifexInfoSource]

def OrderCancelRequest.tags : List (List (List UInt8)) :=
  [[[52, 49]], [[49, 49]], [52, 52, 52, 53, 51] :: TaifexNoPartyIDs.members, [[53, 53]], [[53, 52]], [[54, 48]], [[52, 52, 52, 54, 49]], [[49, 48, 48, 48, 48]], [[49, 48, 48, 48, 49]], [[49, 48, 48, 48, 50]]]

theorem OrderCancelRequest.shape (record : OrderCancelRequest) : record.parts.map Part.tags = OrderCancelRequest.tags := rfl

def OrderCancelRequest.decode (tokens : List Token) : Option OrderCancelRequest := do
  let origClOrdID ← readRequired [52, 49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let taifexNoPartyIDs ← readGroup [52, 52, 52, 53, 51] [52, 52, 52, 52, 56] TaifexNoPartyIDs.members TaifexNoPartyIDs.decode tokens
  let symbol ← readRequired [53, 53] tokens
  let side ← readRequired [53, 52] tokens
  let transactTime ← readRequired [54, 48] tokens
  let taifexCFICode ← readRequired [52, 52, 52, 54, 49] tokens
  let taifexSymbolType ← readRequired [49, 48, 48, 48, 48] tokens
  let taifexOrderSource ← readRequired [49, 48, 48, 48, 49] tokens
  let taifexInfoSource ← readOptional [49, 48, 48, 48, 50] tokens
  pure { origClOrdID, clOrdID, taifexNoPartyIDs, symbol, side, transactTime, taifexCFICode, taifexSymbolType, taifexOrderSource, taifexInfoSource }

theorem OrderCancelRequest.decode_agrees (record : OrderCancelRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelRequest.decode tokens = some record := by
  have distinct : OrderCancelRequest.tags.flatten.Nodup := by decide +kernel
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have taifexNoPartyIDs := readGroup_part [52, 52, 52, 53, 51] [52, 52, 52, 52, 56] TaifexNoPartyIDs.members TaifexNoPartyIDs.encode TaifexNoPartyIDs.within TaifexNoPartyIDs.decode TaifexNoPartyIDs.decode_encode TaifexNoPartyIDs.led record.taifexNoPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have taifexCFICode := readRequired_part [52, 52, 52, 54, 49] record.taifexCFICode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have taifexSymbolType := readRequired_part [49, 48, 48, 48, 48] record.taifexSymbolType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have taifexOrderSource := readRequired_part [49, 48, 48, 48, 49] record.taifexOrderSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have taifexInfoSource := readOptional_part [49, 48, 48, 48, 50] record.taifexInfoSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  simp only [OrderCancelRequest.decode, origClOrdID, clOrdID, taifexNoPartyIDs, symbol, side, transactTime, taifexCFICode, taifexSymbolType, taifexOrderSource, taifexInfoSource, some_bind] <;> rfl

theorem OrderCancelRequest.taken (record : OrderCancelRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [52, 49] record.origClOrdID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_group pairing [52, 52, 52, 53, 51] TaifexNoPartyIDs.members TaifexNoPartyIDs.encode TaifexNoPartyIDs.within (by decide) (by decide) TaifexNoPartyIDs.taken record.taifexNoPartyIDs)
     (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [53, 52] record.side (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [54, 48] record.transactTime (by decide) (by decide))
        (paired_cons pairing _ _ (paired_required pairing [52, 52, 52, 54, 49] record.taifexCFICode (by decide) (by decide))
         (paired_cons pairing _ _ (paired_required pairing [49, 48, 48, 48, 48] record.taifexSymbolType (by decide) (by decide))
          (paired_cons pairing _ _ (paired_required pairing [49, 48, 48, 48, 49] record.taifexOrderSource (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [49, 48, 48, 48, 50] record.taifexInfoSource (by decide) (by decide))
            (paired_none pairing))))))))))

structure OrderCancelReplaceRequest where
  origClOrdID : Terminated 1  -- tag 41
  clOrdID : Terminated 1  -- tag 11
  taifexNoPartyIDs : List TaifexNoPartyIDs  -- tag 44453
  symbol : Terminated 1  -- tag 55
  side : Terminated 1  -- tag 54
  transactTime : Terminated 1  -- tag 60
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  price : Terminated 1  -- tag 44
  timeInForce : Terminated 1  -- tag 59
  handlInst : Terminated 1  -- tag 21
  taifexCFICode : Terminated 1  -- tag 44461
  taifexSymbolType : Terminated 1  -- tag 10000
  taifexOrderSource : Terminated 1  -- tag 10001
  taifexInfoSource : Option (Terminated 1)  -- tag 10002
  taifexExecType : Terminated 1  -- tag 10003

def OrderCancelReplaceRequest.parts (record : OrderCancelReplaceRequest) : List Part :=
  [Part.required [52, 49] record.origClOrdID,
   Part.required [49, 49] record.clOrdID,
   Part.group [52, 52, 52, 53, 51] TaifexNoPartyIDs.members TaifexNoPartyIDs.encode TaifexNoPartyIDs.within record.taifexNoPartyIDs,
   Part.required [53, 53] record.symbol,
   Part.required [53, 52] record.side,
   Part.required [54, 48] record.transactTime,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.required [52, 52] record.price,
   Part.required [53, 57] record.timeInForce,
   Part.required [50, 49] record.handlInst,
   Part.required [52, 52, 52, 54, 49] record.taifexCFICode,
   Part.required [49, 48, 48, 48, 48] record.taifexSymbolType,
   Part.required [49, 48, 48, 48, 49] record.taifexOrderSource,
   Part.optional [49, 48, 48, 48, 50] record.taifexInfoSource,
   Part.required [49, 48, 48, 48, 51] record.taifexExecType]

def OrderCancelReplaceRequest.tags : List (List (List UInt8)) :=
  [[[52, 49]], [[49, 49]], [52, 52, 52, 53, 51] :: TaifexNoPartyIDs.members, [[53, 53]], [[53, 52]], [[54, 48]], [[51, 56]], [[52, 48]], [[52, 52]], [[53, 57]], [[50, 49]], [[52, 52, 52, 54, 49]], [[49, 48, 48, 48, 48]], [[49, 48, 48, 48, 49]], [[49, 48, 48, 48, 50]], [[49, 48, 48, 48, 51]]]

theorem OrderCancelReplaceRequest.shape (record : OrderCancelReplaceRequest) : record.parts.map Part.tags = OrderCancelReplaceRequest.tags := rfl

def OrderCancelReplaceRequest.decode (tokens : List Token) : Option OrderCancelReplaceRequest := do
  let origClOrdID ← readRequired [52, 49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let taifexNoPartyIDs ← readGroup [52, 52, 52, 53, 51] [52, 52, 52, 52, 56] TaifexNoPartyIDs.members TaifexNoPartyIDs.decode tokens
  let symbol ← readRequired [53, 53] tokens
  let side ← readRequired [53, 52] tokens
  let transactTime ← readRequired [54, 48] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readRequired [52, 52] tokens
  let timeInForce ← readRequired [53, 57] tokens
  let handlInst ← readRequired [50, 49] tokens
  let taifexCFICode ← readRequired [52, 52, 52, 54, 49] tokens
  let taifexSymbolType ← readRequired [49, 48, 48, 48, 48] tokens
  let taifexOrderSource ← readRequired [49, 48, 48, 48, 49] tokens
  let taifexInfoSource ← readOptional [49, 48, 48, 48, 50] tokens
  let taifexExecType ← readRequired [49, 48, 48, 48, 51] tokens
  pure { origClOrdID, clOrdID, taifexNoPartyIDs, symbol, side, transactTime, orderQty, ordType, price, timeInForce, handlInst, taifexCFICode, taifexSymbolType, taifexOrderSource, taifexInfoSource, taifexExecType }

theorem OrderCancelReplaceRequest.decode_agrees (record : OrderCancelReplaceRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelReplaceRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelReplaceRequest.decode tokens = some record := by
  have distinct : OrderCancelReplaceRequest.tags.flatten.Nodup := by decide +kernel
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have taifexNoPartyIDs := readGroup_part [52, 52, 52, 53, 51] [52, 52, 52, 52, 56] TaifexNoPartyIDs.members TaifexNoPartyIDs.encode TaifexNoPartyIDs.within TaifexNoPartyIDs.decode TaifexNoPartyIDs.decode_encode TaifexNoPartyIDs.led record.taifexNoPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have price := readRequired_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have timeInForce := readRequired_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have handlInst := readRequired_part [50, 49] record.handlInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have taifexCFICode := readRequired_part [52, 52, 52, 54, 49] record.taifexCFICode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have taifexSymbolType := readRequired_part [49, 48, 48, 48, 48] record.taifexSymbolType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have taifexOrderSource := readRequired_part [49, 48, 48, 48, 49] record.taifexOrderSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have taifexInfoSource := readOptional_part [49, 48, 48, 48, 50] record.taifexInfoSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have taifexExecType := readRequired_part [49, 48, 48, 48, 51] record.taifexExecType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  simp only [OrderCancelReplaceRequest.decode, origClOrdID, clOrdID, taifexNoPartyIDs, symbol, side, transactTime, orderQty, ordType, price, timeInForce, handlInst, taifexCFICode, taifexSymbolType, taifexOrderSource, taifexInfoSource, taifexExecType, some_bind] <;> rfl

theorem OrderCancelReplaceRequest.taken (record : OrderCancelReplaceRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [52, 49] record.origClOrdID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_group pairing [52, 52, 52, 53, 51] TaifexNoPartyIDs.members TaifexNoPartyIDs.encode TaifexNoPartyIDs.within (by decide) (by decide) TaifexNoPartyIDs.taken record.taifexNoPartyIDs)
     (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [53, 52] record.side (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [54, 48] record.transactTime (by decide) (by decide))
        (paired_cons pairing _ _ (paired_required pairing [51, 56] record.orderQty (by decide) (by decide))
         (paired_cons pairing _ _ (paired_required pairing [52, 48] record.ordType (by decide) (by decide))
          (paired_cons pairing _ _ (paired_required pairing [52, 52] record.price (by decide) (by decide))
           (paired_cons pairing _ _ (paired_required pairing [53, 57] record.timeInForce (by decide) (by decide))
            (paired_cons pairing _ _ (paired_required pairing [50, 49] record.handlInst (by decide) (by decide))
             (paired_cons pairing _ _ (paired_required pairing [52, 52, 52, 54, 49] record.taifexCFICode (by decide) (by decide))
              (paired_cons pairing _ _ (paired_required pairing [49, 48, 48, 48, 48] record.taifexSymbolType (by decide) (by decide))
               (paired_cons pairing _ _ (paired_required pairing [49, 48, 48, 48, 49] record.taifexOrderSource (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [49, 48, 48, 48, 50] record.taifexInfoSource (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_required pairing [49, 48, 48, 48, 51] record.taifexExecType (by decide) (by decide))
                  (paired_none pairing))))))))))))))))

structure MultilegOrderCancelReplaceRequest where
  origClOrdID : Terminated 1  -- tag 41
  clOrdID : Terminated 1  -- tag 11
  taifexNoPartyIDs : List TaifexNoPartyIDs  -- tag 44453
  symbol : Terminated 1  -- tag 55
  side : Terminated 1  -- tag 54
  taifexNoLegs : List TaifexNoLegs  -- tag 44555
  transactTime : Terminated 1  -- tag 60
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  price : Terminated 1  -- tag 44
  timeInForce : Terminated 1  -- tag 59
  taifexSymbolType : Terminated 1  -- tag 10000
  taifexOrderSource : Terminated 1  -- tag 10001
  taifexInfoSource : Option (Terminated 1)  -- tag 10002
  taifexExecType : Terminated 1  -- tag 10003

def MultilegOrderCancelReplaceRequest.parts (record : MultilegOrderCancelReplaceRequest) : List Part :=
  [Part.required [52, 49] record.origClOrdID,
   Part.required [49, 49] record.clOrdID,
   Part.group [52, 52, 52, 53, 51] TaifexNoPartyIDs.members TaifexNoPartyIDs.encode TaifexNoPartyIDs.within record.taifexNoPartyIDs,
   Part.required [53, 53] record.symbol,
   Part.required [53, 52] record.side,
   Part.group [52, 52, 53, 53, 53] TaifexNoLegs.members TaifexNoLegs.encode TaifexNoLegs.within record.taifexNoLegs,
   Part.required [54, 48] record.transactTime,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.required [52, 52] record.price,
   Part.required [53, 57] record.timeInForce,
   Part.required [49, 48, 48, 48, 48] record.taifexSymbolType,
   Part.required [49, 48, 48, 48, 49] record.taifexOrderSource,
   Part.optional [49, 48, 48, 48, 50] record.taifexInfoSource,
   Part.required [49, 48, 48, 48, 51] record.taifexExecType]

def MultilegOrderCancelReplaceRequest.tags : List (List (List UInt8)) :=
  [[[52, 49]], [[49, 49]], [52, 52, 52, 53, 51] :: TaifexNoPartyIDs.members, [[53, 53]], [[53, 52]], [52, 52, 53, 53, 53] :: TaifexNoLegs.members, [[54, 48]], [[51, 56]], [[52, 48]], [[52, 52]], [[53, 57]], [[49, 48, 48, 48, 48]], [[49, 48, 48, 48, 49]], [[49, 48, 48, 48, 50]], [[49, 48, 48, 48, 51]]]

theorem MultilegOrderCancelReplaceRequest.shape (record : MultilegOrderCancelReplaceRequest) : record.parts.map Part.tags = MultilegOrderCancelReplaceRequest.tags := rfl

def MultilegOrderCancelReplaceRequest.decode (tokens : List Token) : Option MultilegOrderCancelReplaceRequest := do
  let origClOrdID ← readRequired [52, 49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let taifexNoPartyIDs ← readGroup [52, 52, 52, 53, 51] [52, 52, 52, 52, 56] TaifexNoPartyIDs.members TaifexNoPartyIDs.decode tokens
  let symbol ← readRequired [53, 53] tokens
  let side ← readRequired [53, 52] tokens
  let taifexNoLegs ← readGroup [52, 52, 53, 53, 53] [52, 52, 54, 48, 48] TaifexNoLegs.members TaifexNoLegs.decode tokens
  let transactTime ← readRequired [54, 48] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readRequired [52, 52] tokens
  let timeInForce ← readRequired [53, 57] tokens
  let taifexSymbolType ← readRequired [49, 48, 48, 48, 48] tokens
  let taifexOrderSource ← readRequired [49, 48, 48, 48, 49] tokens
  let taifexInfoSource ← readOptional [49, 48, 48, 48, 50] tokens
  let taifexExecType ← readRequired [49, 48, 48, 48, 51] tokens
  pure { origClOrdID, clOrdID, taifexNoPartyIDs, symbol, side, taifexNoLegs, transactTime, orderQty, ordType, price, timeInForce, taifexSymbolType, taifexOrderSource, taifexInfoSource, taifexExecType }

theorem MultilegOrderCancelReplaceRequest.decode_agrees (record : MultilegOrderCancelReplaceRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ MultilegOrderCancelReplaceRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    MultilegOrderCancelReplaceRequest.decode tokens = some record := by
  have distinct : MultilegOrderCancelReplaceRequest.tags.flatten.Nodup := by decide +kernel
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have taifexNoPartyIDs := readGroup_part [52, 52, 52, 53, 51] [52, 52, 52, 52, 56] TaifexNoPartyIDs.members TaifexNoPartyIDs.encode TaifexNoPartyIDs.within TaifexNoPartyIDs.decode TaifexNoPartyIDs.decode_encode TaifexNoPartyIDs.led record.taifexNoPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have taifexNoLegs := readGroup_part [52, 52, 53, 53, 53] [52, 52, 54, 48, 48] TaifexNoLegs.members TaifexNoLegs.encode TaifexNoLegs.within TaifexNoLegs.decode TaifexNoLegs.decode_encode TaifexNoLegs.led record.taifexNoLegs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have price := readRequired_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have timeInForce := readRequired_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have taifexSymbolType := readRequired_part [49, 48, 48, 48, 48] record.taifexSymbolType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have taifexOrderSource := readRequired_part [49, 48, 48, 48, 49] record.taifexOrderSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have taifexInfoSource := readOptional_part [49, 48, 48, 48, 50] record.taifexInfoSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have taifexExecType := readRequired_part [49, 48, 48, 48, 51] record.taifexExecType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  simp only [MultilegOrderCancelReplaceRequest.decode, origClOrdID, clOrdID, taifexNoPartyIDs, symbol, side, taifexNoLegs, transactTime, orderQty, ordType, price, timeInForce, taifexSymbolType, taifexOrderSource, taifexInfoSource, taifexExecType, some_bind] <;> rfl

theorem MultilegOrderCancelReplaceRequest.taken (record : MultilegOrderCancelReplaceRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [52, 49] record.origClOrdID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_group pairing [52, 52, 52, 53, 51] TaifexNoPartyIDs.members TaifexNoPartyIDs.encode TaifexNoPartyIDs.within (by decide) (by decide) TaifexNoPartyIDs.taken record.taifexNoPartyIDs)
     (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [53, 52] record.side (by decide) (by decide))
       (paired_cons pairing _ _ (paired_group pairing [52, 52, 53, 53, 53] TaifexNoLegs.members TaifexNoLegs.encode TaifexNoLegs.within (by decide) (by decide) TaifexNoLegs.taken record.taifexNoLegs)
        (paired_cons pairing _ _ (paired_required pairing [54, 48] record.transactTime (by decide) (by decide))
         (paired_cons pairing _ _ (paired_required pairing [51, 56] record.orderQty (by decide) (by decide))
          (paired_cons pairing _ _ (paired_required pairing [52, 48] record.ordType (by decide) (by decide))
           (paired_cons pairing _ _ (paired_required pairing [52, 52] record.price (by decide) (by decide))
            (paired_cons pairing _ _ (paired_required pairing [53, 57] record.timeInForce (by decide) (by decide))
             (paired_cons pairing _ _ (paired_required pairing [49, 48, 48, 48, 48] record.taifexSymbolType (by decide) (by decide))
              (paired_cons pairing _ _ (paired_required pairing [49, 48, 48, 48, 49] record.taifexOrderSource (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [49, 48, 48, 48, 50] record.taifexInfoSource (by decide) (by decide))
                (paired_cons pairing _ _ (paired_required pairing [49, 48, 48, 48, 51] record.taifexExecType (by decide) (by decide))
                 (paired_none pairing)))))))))))))))

structure OrderStatusRequest where
  clOrdID : Terminated 1  -- tag 11
  symbol : Terminated 1  -- tag 55
  side : Terminated 1  -- tag 54
  taifexCFICode : Terminated 1  -- tag 44461
  taifexSymbolType : Terminated 1  -- tag 10000
  taifexOrderSource : Terminated 1  -- tag 10001
  taifexInfoSource : Option (Terminated 1)  -- tag 10002

def OrderStatusRequest.parts (record : OrderStatusRequest) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.required [53, 53] record.symbol,
   Part.required [53, 52] record.side,
   Part.required [52, 52, 52, 54, 49] record.taifexCFICode,
   Part.required [49, 48, 48, 48, 48] record.taifexSymbolType,
   Part.required [49, 48, 48, 48, 49] record.taifexOrderSource,
   Part.optional [49, 48, 48, 48, 50] record.taifexInfoSource]

def OrderStatusRequest.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[53, 53]], [[53, 52]], [[52, 52, 52, 54, 49]], [[49, 48, 48, 48, 48]], [[49, 48, 48, 48, 49]], [[49, 48, 48, 48, 50]]]

theorem OrderStatusRequest.shape (record : OrderStatusRequest) : record.parts.map Part.tags = OrderStatusRequest.tags := rfl

def OrderStatusRequest.decode (tokens : List Token) : Option OrderStatusRequest := do
  let clOrdID ← readRequired [49, 49] tokens
  let symbol ← readRequired [53, 53] tokens
  let side ← readRequired [53, 52] tokens
  let taifexCFICode ← readRequired [52, 52, 52, 54, 49] tokens
  let taifexSymbolType ← readRequired [49, 48, 48, 48, 48] tokens
  let taifexOrderSource ← readRequired [49, 48, 48, 48, 49] tokens
  let taifexInfoSource ← readOptional [49, 48, 48, 48, 50] tokens
  pure { clOrdID, symbol, side, taifexCFICode, taifexSymbolType, taifexOrderSource, taifexInfoSource }

theorem OrderStatusRequest.decode_agrees (record : OrderStatusRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderStatusRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderStatusRequest.decode tokens = some record := by
  have distinct : OrderStatusRequest.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have taifexCFICode := readRequired_part [52, 52, 52, 54, 49] record.taifexCFICode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have taifexSymbolType := readRequired_part [49, 48, 48, 48, 48] record.taifexSymbolType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have taifexOrderSource := readRequired_part [49, 48, 48, 48, 49] record.taifexOrderSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have taifexInfoSource := readOptional_part [49, 48, 48, 48, 50] record.taifexInfoSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  simp only [OrderStatusRequest.decode, clOrdID, symbol, side, taifexCFICode, taifexSymbolType, taifexOrderSource, taifexInfoSource, some_bind] <;> rfl

theorem OrderStatusRequest.taken (record : OrderStatusRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [53, 52] record.side (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [52, 52, 52, 54, 49] record.taifexCFICode (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [49, 48, 48, 48, 48] record.taifexSymbolType (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [49, 48, 48, 48, 49] record.taifexOrderSource (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [49, 48, 48, 48, 50] record.taifexInfoSource (by decide) (by decide))
         (paired_none pairing)))))))

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

structure QuoteRequest where
  quoteReqID : Terminated 1  -- tag 131
  noRelatedSym : List NoRelatedSym  -- tag 146
  taifexOrderSource : Terminated 1  -- tag 10001
  taifexInfoSource : Option (Terminated 1)  -- tag 10002

def QuoteRequest.parts (record : QuoteRequest) : List Part :=
  [Part.required [49, 51, 49] record.quoteReqID,
   Part.group [49, 52, 54] NoRelatedSym.members NoRelatedSym.encode NoRelatedSym.within record.noRelatedSym,
   Part.required [49, 48, 48, 48, 49] record.taifexOrderSource,
   Part.optional [49, 48, 48, 48, 50] record.taifexInfoSource]

def QuoteRequest.tags : List (List (List UInt8)) :=
  [[[49, 51, 49]], [49, 52, 54] :: NoRelatedSym.members, [[49, 48, 48, 48, 49]], [[49, 48, 48, 48, 50]]]

theorem QuoteRequest.shape (record : QuoteRequest) : record.parts.map Part.tags = QuoteRequest.tags := rfl

def QuoteRequest.decode (tokens : List Token) : Option QuoteRequest := do
  let quoteReqID ← readRequired [49, 51, 49] tokens
  let noRelatedSym ← readGroup [49, 52, 54] [53, 53] NoRelatedSym.members NoRelatedSym.decode tokens
  let taifexOrderSource ← readRequired [49, 48, 48, 48, 49] tokens
  let taifexInfoSource ← readOptional [49, 48, 48, 48, 50] tokens
  pure { quoteReqID, noRelatedSym, taifexOrderSource, taifexInfoSource }

theorem QuoteRequest.decode_agrees (record : QuoteRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ QuoteRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    QuoteRequest.decode tokens = some record := by
  have distinct : QuoteRequest.tags.flatten.Nodup := by decide +kernel
  have quoteReqID := readRequired_part [49, 51, 49] record.quoteReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have noRelatedSym := readGroup_part [49, 52, 54] [53, 53] NoRelatedSym.members NoRelatedSym.encode NoRelatedSym.within NoRelatedSym.decode NoRelatedSym.decode_encode NoRelatedSym.led record.noRelatedSym tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have taifexOrderSource := readRequired_part [49, 48, 48, 48, 49] record.taifexOrderSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have taifexInfoSource := readOptional_part [49, 48, 48, 48, 50] record.taifexInfoSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [QuoteRequest.decode, quoteReqID, noRelatedSym, taifexOrderSource, taifexInfoSource, some_bind] <;> rfl

theorem QuoteRequest.taken (record : QuoteRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 51, 49] record.quoteReqID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_group pairing [49, 52, 54] NoRelatedSym.members NoRelatedSym.encode NoRelatedSym.within (by decide) (by decide) NoRelatedSym.taken record.noRelatedSym)
    (paired_cons pairing _ _ (paired_required pairing [49, 48, 48, 48, 49] record.taifexOrderSource (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [49, 48, 48, 48, 50] record.taifexInfoSource (by decide) (by decide))
      (paired_none pairing))))

structure Quote where
  quoteID : Terminated 1  -- tag 117
  taifexNoPartyIDs : List TaifexNoPartyIDs  -- tag 44453
  account : Terminated 1  -- tag 1
  symbol : Terminated 1  -- tag 55
  bidPx : Terminated 1  -- tag 132
  offerPx : Terminated 1  -- tag 133
  bidSize : Terminated 1  -- tag 134
  offerSize : Terminated 1  -- tag 135
  transactTime : Terminated 1  -- tag 60
  timeInForce : Terminated 1  -- tag 59
  positionEffect : Terminated 1  -- tag 77
  taifexCFICode : Terminated 1  -- tag 44461
  taifexSymbolType : Terminated 1  -- tag 10000
  taifexOrderSource : Terminated 1  -- tag 10001
  taifexInfoSource : Terminated 1  -- tag 10002
  taifexExecType : Terminated 1  -- tag 10003

def Quote.parts (record : Quote) : List Part :=
  [Part.required [49, 49, 55] record.quoteID,
   Part.group [52, 52, 52, 53, 51] TaifexNoPartyIDs.members TaifexNoPartyIDs.encode TaifexNoPartyIDs.within record.taifexNoPartyIDs,
   Part.required [49] record.account,
   Part.required [53, 53] record.symbol,
   Part.required [49, 51, 50] record.bidPx,
   Part.required [49, 51, 51] record.offerPx,
   Part.required [49, 51, 52] record.bidSize,
   Part.required [49, 51, 53] record.offerSize,
   Part.required [54, 48] record.transactTime,
   Part.required [53, 57] record.timeInForce,
   Part.required [55, 55] record.positionEffect,
   Part.required [52, 52, 52, 54, 49] record.taifexCFICode,
   Part.required [49, 48, 48, 48, 48] record.taifexSymbolType,
   Part.required [49, 48, 48, 48, 49] record.taifexOrderSource,
   Part.required [49, 48, 48, 48, 50] record.taifexInfoSource,
   Part.required [49, 48, 48, 48, 51] record.taifexExecType]

def Quote.tags : List (List (List UInt8)) :=
  [[[49, 49, 55]], [52, 52, 52, 53, 51] :: TaifexNoPartyIDs.members, [[49]], [[53, 53]], [[49, 51, 50]], [[49, 51, 51]], [[49, 51, 52]], [[49, 51, 53]], [[54, 48]], [[53, 57]], [[55, 55]], [[52, 52, 52, 54, 49]], [[49, 48, 48, 48, 48]], [[49, 48, 48, 48, 49]], [[49, 48, 48, 48, 50]], [[49, 48, 48, 48, 51]]]

theorem Quote.shape (record : Quote) : record.parts.map Part.tags = Quote.tags := rfl

def Quote.decode (tokens : List Token) : Option Quote := do
  let quoteID ← readRequired [49, 49, 55] tokens
  let taifexNoPartyIDs ← readGroup [52, 52, 52, 53, 51] [52, 52, 52, 52, 56] TaifexNoPartyIDs.members TaifexNoPartyIDs.decode tokens
  let account ← readRequired [49] tokens
  let symbol ← readRequired [53, 53] tokens
  let bidPx ← readRequired [49, 51, 50] tokens
  let offerPx ← readRequired [49, 51, 51] tokens
  let bidSize ← readRequired [49, 51, 52] tokens
  let offerSize ← readRequired [49, 51, 53] tokens
  let transactTime ← readRequired [54, 48] tokens
  let timeInForce ← readRequired [53, 57] tokens
  let positionEffect ← readRequired [55, 55] tokens
  let taifexCFICode ← readRequired [52, 52, 52, 54, 49] tokens
  let taifexSymbolType ← readRequired [49, 48, 48, 48, 48] tokens
  let taifexOrderSource ← readRequired [49, 48, 48, 48, 49] tokens
  let taifexInfoSource ← readRequired [49, 48, 48, 48, 50] tokens
  let taifexExecType ← readRequired [49, 48, 48, 48, 51] tokens
  pure { quoteID, taifexNoPartyIDs, account, symbol, bidPx, offerPx, bidSize, offerSize, transactTime, timeInForce, positionEffect, taifexCFICode, taifexSymbolType, taifexOrderSource, taifexInfoSource, taifexExecType }

theorem Quote.decode_agrees (record : Quote) (tokens : List Token)
    (agrees : ∀ tags ∈ Quote.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Quote.decode tokens = some record := by
  have distinct : Quote.tags.flatten.Nodup := by decide +kernel
  have quoteID := readRequired_part [49, 49, 55] record.quoteID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have taifexNoPartyIDs := readGroup_part [52, 52, 52, 53, 51] [52, 52, 52, 52, 56] TaifexNoPartyIDs.members TaifexNoPartyIDs.encode TaifexNoPartyIDs.within TaifexNoPartyIDs.decode TaifexNoPartyIDs.decode_encode TaifexNoPartyIDs.led record.taifexNoPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have account := readRequired_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have bidPx := readRequired_part [49, 51, 50] record.bidPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have offerPx := readRequired_part [49, 51, 51] record.offerPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have bidSize := readRequired_part [49, 51, 52] record.bidSize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have offerSize := readRequired_part [49, 51, 53] record.offerSize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have timeInForce := readRequired_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have positionEffect := readRequired_part [55, 55] record.positionEffect tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have taifexCFICode := readRequired_part [52, 52, 52, 54, 49] record.taifexCFICode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have taifexSymbolType := readRequired_part [49, 48, 48, 48, 48] record.taifexSymbolType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have taifexOrderSource := readRequired_part [49, 48, 48, 48, 49] record.taifexOrderSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have taifexInfoSource := readRequired_part [49, 48, 48, 48, 50] record.taifexInfoSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have taifexExecType := readRequired_part [49, 48, 48, 48, 51] record.taifexExecType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  simp only [Quote.decode, quoteID, taifexNoPartyIDs, account, symbol, bidPx, offerPx, bidSize, offerSize, transactTime, timeInForce, positionEffect, taifexCFICode, taifexSymbolType, taifexOrderSource, taifexInfoSource, taifexExecType, some_bind] <;> rfl

theorem Quote.taken (record : Quote) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 49, 55] record.quoteID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_group pairing [52, 52, 52, 53, 51] TaifexNoPartyIDs.members TaifexNoPartyIDs.encode TaifexNoPartyIDs.within (by decide) (by decide) TaifexNoPartyIDs.taken record.taifexNoPartyIDs)
    (paired_cons pairing _ _ (paired_required pairing [49] record.account (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [49, 51, 50] record.bidPx (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [49, 51, 51] record.offerPx (by decide) (by decide))
        (paired_cons pairing _ _ (paired_required pairing [49, 51, 52] record.bidSize (by decide) (by decide))
         (paired_cons pairing _ _ (paired_required pairing [49, 51, 53] record.offerSize (by decide) (by decide))
          (paired_cons pairing _ _ (paired_required pairing [54, 48] record.transactTime (by decide) (by decide))
           (paired_cons pairing _ _ (paired_required pairing [53, 57] record.timeInForce (by decide) (by decide))
            (paired_cons pairing _ _ (paired_required pairing [55, 55] record.positionEffect (by decide) (by decide))
             (paired_cons pairing _ _ (paired_required pairing [52, 52, 52, 54, 49] record.taifexCFICode (by decide) (by decide))
              (paired_cons pairing _ _ (paired_required pairing [49, 48, 48, 48, 48] record.taifexSymbolType (by decide) (by decide))
               (paired_cons pairing _ _ (paired_required pairing [49, 48, 48, 48, 49] record.taifexOrderSource (by decide) (by decide))
                (paired_cons pairing _ _ (paired_required pairing [49, 48, 48, 48, 50] record.taifexInfoSource (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_required pairing [49, 48, 48, 48, 51] record.taifexExecType (by decide) (by decide))
                  (paired_none pairing))))))))))))))))

structure NoQuoteEntries where
  noRelatedSym : List NoRelatedSym  -- tag 146

def NoQuoteEntries.parts (record : NoQuoteEntries) : List Part :=
  [Part.groupLed [49, 52, 54] NoRelatedSym.members NoRelatedSym.encode NoRelatedSym.within record.noRelatedSym]

def NoQuoteEntries.tags : List (List (List UInt8)) :=
  [[49, 52, 54] :: NoRelatedSym.members]

theorem NoQuoteEntries.shape (record : NoQuoteEntries) : record.parts.map Part.tags = NoQuoteEntries.tags := rfl

def NoQuoteEntries.decode (tokens : List Token) : Option NoQuoteEntries := do
  let noRelatedSym ← readGroup [49, 52, 54] [53, 53] NoRelatedSym.members NoRelatedSym.decode tokens
  pure { noRelatedSym }

theorem NoQuoteEntries.decode_agrees (record : NoQuoteEntries) (tokens : List Token)
    (agrees : ∀ tags ∈ NoQuoteEntries.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoQuoteEntries.decode tokens = some record := by
  have distinct : NoQuoteEntries.tags.flatten.Nodup := by decide +kernel
  have noRelatedSym := readGroup_partLed [49, 52, 54] [53, 53] NoRelatedSym.members NoRelatedSym.encode NoRelatedSym.within NoRelatedSym.decode NoRelatedSym.decode_encode NoRelatedSym.led record.noRelatedSym tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [NoQuoteEntries.decode, noRelatedSym, some_bind] <;> rfl

theorem NoQuoteEntries.taken (record : NoQuoteEntries) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_groupLed pairing [49, 52, 54] NoRelatedSym.members NoRelatedSym.encode NoRelatedSym.within (by decide) (by decide) NoRelatedSym.taken record.noRelatedSym)
   (paired_none pairing)

def NoQuoteEntries.members : List (List UInt8) := NoQuoteEntries.tags.flatten

def NoQuoteEntries.encode (entry : NoQuoteEntries) : List Token := encodeParts entry.parts

theorem NoQuoteEntries.decode_encode (entry : NoQuoteEntries) : NoQuoteEntries.decode entry.encode = some entry :=
  NoQuoteEntries.decode_agrees entry _ (fun _ _ => rfl)

theorem NoQuoteEntries.within (entry : NoQuoteEntries) : ∀ token ∈ entry.encode, token.tag ∈ NoQuoteEntries.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoQuoteEntries.shape] at this

theorem NoQuoteEntries.led (entry : NoQuoteEntries) : Lead [49, 52, 54] entry.encode :=
  lead_groupLed [49, 52, 54] NoRelatedSym.members NoRelatedSym.encode NoRelatedSym.within entry.noRelatedSym _ NoQuoteEntries.tags.tail rfl (by decide +kernel) (by decide +kernel)

structure QuoteCancel where
  quoteID : Terminated 1  -- tag 117
  quoteCancelType : Terminated 1  -- tag 298
  taifexNoPartyIDs : List TaifexNoPartyIDs  -- tag 44453
  noQuoteEntries : List NoQuoteEntries  -- tag 295
  taifexOrderSource : Terminated 1  -- tag 10001
  taifexInfoSource : Terminated 1  -- tag 10002

def QuoteCancel.parts (record : QuoteCancel) : List Part :=
  [Part.required [49, 49, 55] record.quoteID,
   Part.required [50, 57, 56] record.quoteCancelType,
   Part.group [52, 52, 52, 53, 51] TaifexNoPartyIDs.members TaifexNoPartyIDs.encode TaifexNoPartyIDs.within record.taifexNoPartyIDs,
   Part.group [50, 57, 53] NoQuoteEntries.members NoQuoteEntries.encode NoQuoteEntries.within record.noQuoteEntries,
   Part.required [49, 48, 48, 48, 49] record.taifexOrderSource,
   Part.required [49, 48, 48, 48, 50] record.taifexInfoSource]

def QuoteCancel.tags : List (List (List UInt8)) :=
  [[[49, 49, 55]], [[50, 57, 56]], [52, 52, 52, 53, 51] :: TaifexNoPartyIDs.members, [50, 57, 53] :: NoQuoteEntries.members, [[49, 48, 48, 48, 49]], [[49, 48, 48, 48, 50]]]

theorem QuoteCancel.shape (record : QuoteCancel) : record.parts.map Part.tags = QuoteCancel.tags := rfl

def QuoteCancel.decode (tokens : List Token) : Option QuoteCancel := do
  let quoteID ← readRequired [49, 49, 55] tokens
  let quoteCancelType ← readRequired [50, 57, 56] tokens
  let taifexNoPartyIDs ← readGroup [52, 52, 52, 53, 51] [52, 52, 52, 52, 56] TaifexNoPartyIDs.members TaifexNoPartyIDs.decode tokens
  let noQuoteEntries ← readGroup [50, 57, 53] [49, 52, 54] NoQuoteEntries.members NoQuoteEntries.decode tokens
  let taifexOrderSource ← readRequired [49, 48, 48, 48, 49] tokens
  let taifexInfoSource ← readRequired [49, 48, 48, 48, 50] tokens
  pure { quoteID, quoteCancelType, taifexNoPartyIDs, noQuoteEntries, taifexOrderSource, taifexInfoSource }

theorem QuoteCancel.decode_agrees (record : QuoteCancel) (tokens : List Token)
    (agrees : ∀ tags ∈ QuoteCancel.tags, select tags tokens = select tags (encodeParts record.parts)) :
    QuoteCancel.decode tokens = some record := by
  have distinct : QuoteCancel.tags.flatten.Nodup := by decide +kernel
  have quoteID := readRequired_part [49, 49, 55] record.quoteID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have quoteCancelType := readRequired_part [50, 57, 56] record.quoteCancelType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have taifexNoPartyIDs := readGroup_part [52, 52, 52, 53, 51] [52, 52, 52, 52, 56] TaifexNoPartyIDs.members TaifexNoPartyIDs.encode TaifexNoPartyIDs.within TaifexNoPartyIDs.decode TaifexNoPartyIDs.decode_encode TaifexNoPartyIDs.led record.taifexNoPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have noQuoteEntries := readGroup_part [50, 57, 53] [49, 52, 54] NoQuoteEntries.members NoQuoteEntries.encode NoQuoteEntries.within NoQuoteEntries.decode NoQuoteEntries.decode_encode NoQuoteEntries.led record.noQuoteEntries tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have taifexOrderSource := readRequired_part [49, 48, 48, 48, 49] record.taifexOrderSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have taifexInfoSource := readRequired_part [49, 48, 48, 48, 50] record.taifexInfoSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  simp only [QuoteCancel.decode, quoteID, quoteCancelType, taifexNoPartyIDs, noQuoteEntries, taifexOrderSource, taifexInfoSource, some_bind] <;> rfl

theorem QuoteCancel.taken (record : QuoteCancel) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 49, 55] record.quoteID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [50, 57, 56] record.quoteCancelType (by decide) (by decide))
    (paired_cons pairing _ _ (paired_group pairing [52, 52, 52, 53, 51] TaifexNoPartyIDs.members TaifexNoPartyIDs.encode TaifexNoPartyIDs.within (by decide) (by decide) TaifexNoPartyIDs.taken record.taifexNoPartyIDs)
     (paired_cons pairing _ _ (paired_group pairing [50, 57, 53] NoQuoteEntries.members NoQuoteEntries.encode NoQuoteEntries.within (by decide) (by decide) NoQuoteEntries.taken record.noQuoteEntries)
      (paired_cons pairing _ _ (paired_required pairing [49, 48, 48, 48, 49] record.taifexOrderSource (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [49, 48, 48, 48, 50] record.taifexInfoSource (by decide) (by decide))
        (paired_none pairing))))))

structure QuoteStatusRequest where
  quoteID : Terminated 1  -- tag 117
  symbol : Terminated 1  -- tag 55
  taifexCFICode : Terminated 1  -- tag 44461
  taifexSymbolType : Terminated 1  -- tag 10000
  taifexOrderSource : Terminated 1  -- tag 10001
  taifexInfoSource : Option (Terminated 1)  -- tag 10002

def QuoteStatusRequest.parts (record : QuoteStatusRequest) : List Part :=
  [Part.required [49, 49, 55] record.quoteID,
   Part.required [53, 53] record.symbol,
   Part.required [52, 52, 52, 54, 49] record.taifexCFICode,
   Part.required [49, 48, 48, 48, 48] record.taifexSymbolType,
   Part.required [49, 48, 48, 48, 49] record.taifexOrderSource,
   Part.optional [49, 48, 48, 48, 50] record.taifexInfoSource]

def QuoteStatusRequest.tags : List (List (List UInt8)) :=
  [[[49, 49, 55]], [[53, 53]], [[52, 52, 52, 54, 49]], [[49, 48, 48, 48, 48]], [[49, 48, 48, 48, 49]], [[49, 48, 48, 48, 50]]]

theorem QuoteStatusRequest.shape (record : QuoteStatusRequest) : record.parts.map Part.tags = QuoteStatusRequest.tags := rfl

def QuoteStatusRequest.decode (tokens : List Token) : Option QuoteStatusRequest := do
  let quoteID ← readRequired [49, 49, 55] tokens
  let symbol ← readRequired [53, 53] tokens
  let taifexCFICode ← readRequired [52, 52, 52, 54, 49] tokens
  let taifexSymbolType ← readRequired [49, 48, 48, 48, 48] tokens
  let taifexOrderSource ← readRequired [49, 48, 48, 48, 49] tokens
  let taifexInfoSource ← readOptional [49, 48, 48, 48, 50] tokens
  pure { quoteID, symbol, taifexCFICode, taifexSymbolType, taifexOrderSource, taifexInfoSource }

theorem QuoteStatusRequest.decode_agrees (record : QuoteStatusRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ QuoteStatusRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    QuoteStatusRequest.decode tokens = some record := by
  have distinct : QuoteStatusRequest.tags.flatten.Nodup := by decide +kernel
  have quoteID := readRequired_part [49, 49, 55] record.quoteID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have taifexCFICode := readRequired_part [52, 52, 52, 54, 49] record.taifexCFICode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have taifexSymbolType := readRequired_part [49, 48, 48, 48, 48] record.taifexSymbolType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have taifexOrderSource := readRequired_part [49, 48, 48, 48, 49] record.taifexOrderSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have taifexInfoSource := readOptional_part [49, 48, 48, 48, 50] record.taifexInfoSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  simp only [QuoteStatusRequest.decode, quoteID, symbol, taifexCFICode, taifexSymbolType, taifexOrderSource, taifexInfoSource, some_bind] <;> rfl

theorem QuoteStatusRequest.taken (record : QuoteStatusRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 49, 55] record.quoteID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [52, 52, 52, 54, 49] record.taifexCFICode (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [49, 48, 48, 48, 48] record.taifexSymbolType (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [49, 48, 48, 48, 49] record.taifexOrderSource (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [49, 48, 48, 48, 50] record.taifexInfoSource (by decide) (by decide))
        (paired_none pairing))))))

structure TradingSessionStatusRequest where
  tradSesReqID : Terminated 1  -- tag 335
  subscriptionRequestType : Terminated 1  -- tag 263
  tradingSessionID : Terminated 1  -- tag 336

def TradingSessionStatusRequest.parts (record : TradingSessionStatusRequest) : List Part :=
  [Part.required [51, 51, 53] record.tradSesReqID,
   Part.required [50, 54, 51] record.subscriptionRequestType,
   Part.required [51, 51, 54] record.tradingSessionID]

def TradingSessionStatusRequest.tags : List (List (List UInt8)) :=
  [[[51, 51, 53]], [[50, 54, 51]], [[51, 51, 54]]]

theorem TradingSessionStatusRequest.shape (record : TradingSessionStatusRequest) : record.parts.map Part.tags = TradingSessionStatusRequest.tags := rfl

def TradingSessionStatusRequest.decode (tokens : List Token) : Option TradingSessionStatusRequest := do
  let tradSesReqID ← readRequired [51, 51, 53] tokens
  let subscriptionRequestType ← readRequired [50, 54, 51] tokens
  let tradingSessionID ← readRequired [51, 51, 54] tokens
  pure { tradSesReqID, subscriptionRequestType, tradingSessionID }

theorem TradingSessionStatusRequest.decode_agrees (record : TradingSessionStatusRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ TradingSessionStatusRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TradingSessionStatusRequest.decode tokens = some record := by
  have distinct : TradingSessionStatusRequest.tags.flatten.Nodup := by decide +kernel
  have tradSesReqID := readRequired_part [51, 51, 53] record.tradSesReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have subscriptionRequestType := readRequired_part [50, 54, 51] record.subscriptionRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have tradingSessionID := readRequired_part [51, 51, 54] record.tradingSessionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [TradingSessionStatusRequest.decode, tradSesReqID, subscriptionRequestType, tradingSessionID, some_bind] <;> rfl

theorem TradingSessionStatusRequest.taken (record : TradingSessionStatusRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 51, 53] record.tradSesReqID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [50, 54, 51] record.subscriptionRequestType (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [51, 51, 54] record.tradingSessionID (by decide) (by decide))
     (paired_none pairing)))

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

structure TaifexNoLegsDefinition where
  taifexLegSymbol : Terminated 1  -- tag 44600
  taifexLegCFICode : Terminated 1  -- tag 44608
  taifexLegMaturityDate : Terminated 1  -- tag 44611
  legStrikePrice : Terminated 1  -- tag 612

def TaifexNoLegsDefinition.parts (record : TaifexNoLegsDefinition) : List Part :=
  [Part.required [52, 52, 54, 48, 48] record.taifexLegSymbol,
   Part.required [52, 52, 54, 48, 56] record.taifexLegCFICode,
   Part.required [52, 52, 54, 49, 49] record.taifexLegMaturityDate,
   Part.required [54, 49, 50] record.legStrikePrice]

def TaifexNoLegsDefinition.tags : List (List (List UInt8)) :=
  [[[52, 52, 54, 48, 48]], [[52, 52, 54, 48, 56]], [[52, 52, 54, 49, 49]], [[54, 49, 50]]]

theorem TaifexNoLegsDefinition.shape (record : TaifexNoLegsDefinition) : record.parts.map Part.tags = TaifexNoLegsDefinition.tags := rfl

def TaifexNoLegsDefinition.decode (tokens : List Token) : Option TaifexNoLegsDefinition := do
  let taifexLegSymbol ← readRequired [52, 52, 54, 48, 48] tokens
  let taifexLegCFICode ← readRequired [52, 52, 54, 48, 56] tokens
  let taifexLegMaturityDate ← readRequired [52, 52, 54, 49, 49] tokens
  let legStrikePrice ← readRequired [54, 49, 50] tokens
  pure { taifexLegSymbol, taifexLegCFICode, taifexLegMaturityDate, legStrikePrice }

theorem TaifexNoLegsDefinition.decode_agrees (record : TaifexNoLegsDefinition) (tokens : List Token)
    (agrees : ∀ tags ∈ TaifexNoLegsDefinition.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TaifexNoLegsDefinition.decode tokens = some record := by
  have distinct : TaifexNoLegsDefinition.tags.flatten.Nodup := by decide +kernel
  have taifexLegSymbol := readRequired_part [52, 52, 54, 48, 48] record.taifexLegSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have taifexLegCFICode := readRequired_part [52, 52, 54, 48, 56] record.taifexLegCFICode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have taifexLegMaturityDate := readRequired_part [52, 52, 54, 49, 49] record.taifexLegMaturityDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have legStrikePrice := readRequired_part [54, 49, 50] record.legStrikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [TaifexNoLegsDefinition.decode, taifexLegSymbol, taifexLegCFICode, taifexLegMaturityDate, legStrikePrice, some_bind] <;> rfl

theorem TaifexNoLegsDefinition.taken (record : TaifexNoLegsDefinition) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [52, 52, 54, 48, 48] record.taifexLegSymbol (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [52, 52, 54, 48, 56] record.taifexLegCFICode (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [52, 52, 54, 49, 49] record.taifexLegMaturityDate (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [54, 49, 50] record.legStrikePrice (by decide) (by decide))
      (paired_none pairing))))

def TaifexNoLegsDefinition.members : List (List UInt8) := TaifexNoLegsDefinition.tags.flatten

def TaifexNoLegsDefinition.encode (entry : TaifexNoLegsDefinition) : List Token := encodeParts entry.parts

theorem TaifexNoLegsDefinition.decode_encode (entry : TaifexNoLegsDefinition) : TaifexNoLegsDefinition.decode entry.encode = some entry :=
  TaifexNoLegsDefinition.decode_agrees entry _ (fun _ _ => rfl)

theorem TaifexNoLegsDefinition.within (entry : TaifexNoLegsDefinition) : ∀ token ∈ entry.encode, token.tag ∈ TaifexNoLegsDefinition.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [TaifexNoLegsDefinition.shape] at this

theorem TaifexNoLegsDefinition.led (entry : TaifexNoLegsDefinition) : Lead [52, 52, 54, 48, 48] entry.encode :=
  lead_parts [52, 52, 54, 48, 48] entry.taifexLegSymbol _ TaifexNoLegsDefinition.tags.tail rfl (by decide +kernel)

structure SecurityDefinitionRequest where
  securityReqID : Terminated 1  -- tag 320
  securityRequestType : Terminated 1  -- tag 321
  account : Terminated 1  -- tag 1
  taifexNoLegsDefinition : List TaifexNoLegsDefinition  -- tag 44555

def SecurityDefinitionRequest.parts (record : SecurityDefinitionRequest) : List Part :=
  [Part.required [51, 50, 48] record.securityReqID,
   Part.required [51, 50, 49] record.securityRequestType,
   Part.required [49] record.account,
   Part.group [52, 52, 53, 53, 53] TaifexNoLegsDefinition.members TaifexNoLegsDefinition.encode TaifexNoLegsDefinition.within record.taifexNoLegsDefinition]

def SecurityDefinitionRequest.tags : List (List (List UInt8)) :=
  [[[51, 50, 48]], [[51, 50, 49]], [[49]], [52, 52, 53, 53, 53] :: TaifexNoLegsDefinition.members]

theorem SecurityDefinitionRequest.shape (record : SecurityDefinitionRequest) : record.parts.map Part.tags = SecurityDefinitionRequest.tags := rfl

def SecurityDefinitionRequest.decode (tokens : List Token) : Option SecurityDefinitionRequest := do
  let securityReqID ← readRequired [51, 50, 48] tokens
  let securityRequestType ← readRequired [51, 50, 49] tokens
  let account ← readRequired [49] tokens
  let taifexNoLegsDefinition ← readGroup [52, 52, 53, 53, 53] [52, 52, 54, 48, 48] TaifexNoLegsDefinition.members TaifexNoLegsDefinition.decode tokens
  pure { securityReqID, securityRequestType, account, taifexNoLegsDefinition }

theorem SecurityDefinitionRequest.decode_agrees (record : SecurityDefinitionRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ SecurityDefinitionRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    SecurityDefinitionRequest.decode tokens = some record := by
  have distinct : SecurityDefinitionRequest.tags.flatten.Nodup := by decide +kernel
  have securityReqID := readRequired_part [51, 50, 48] record.securityReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityRequestType := readRequired_part [51, 50, 49] record.securityRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have account := readRequired_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have taifexNoLegsDefinition := readGroup_part [52, 52, 53, 53, 53] [52, 52, 54, 48, 48] TaifexNoLegsDefinition.members TaifexNoLegsDefinition.encode TaifexNoLegsDefinition.within TaifexNoLegsDefinition.decode TaifexNoLegsDefinition.decode_encode TaifexNoLegsDefinition.led record.taifexNoLegsDefinition tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [SecurityDefinitionRequest.decode, securityReqID, securityRequestType, account, taifexNoLegsDefinition, some_bind] <;> rfl

theorem SecurityDefinitionRequest.taken (record : SecurityDefinitionRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 50, 48] record.securityReqID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [51, 50, 49] record.securityRequestType (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [49] record.account (by decide) (by decide))
     (paired_cons pairing _ _ (paired_group pairing [52, 52, 53, 53, 53] TaifexNoLegsDefinition.members TaifexNoLegsDefinition.encode TaifexNoLegsDefinition.within (by decide) (by decide) TaifexNoLegsDefinition.taken record.taifexNoLegsDefinition)
      (paired_none pairing))))

inductive Message where
  | logon (header : Header) (r0 : Logon)
  | logout (header : Header) (r0 : Logout)
  | heartbeat (header : Header) (r0 : Heartbeat)
  | testRequest (header : Header) (r0 : TestRequest)
  | resendRequest (header : Header) (r0 : ResendRequest)
  | reject (header : Header) (r0 : Reject)
  | sequenceResetGapFill (header : Header) (r0 : SequenceResetGapFill)
  | newOrderSingle (header : Header) (r0 : NewOrderSingle)
  | newOrderMultileg (header : Header) (r0 : NewOrderMultileg)
  | orderCancelRequest (header : Header) (r0 : OrderCancelRequest)
  | orderCancelReplaceRequest (header : Header) (r0 : OrderCancelReplaceRequest)
  | multilegOrderCancelReplaceRequest (header : Header) (r0 : MultilegOrderCancelReplaceRequest)
  | orderStatusRequest (header : Header) (r0 : OrderStatusRequest)
  | quoteRequest (header : Header) (r0 : QuoteRequest)
  | quote (header : Header) (r0 : Quote)
  | quoteCancel (header : Header) (r0 : QuoteCancel)
  | quoteStatusRequest (header : Header) (r0 : QuoteStatusRequest)
  | tradingSessionStatusRequest (header : Header) (r0 : TradingSessionStatusRequest)
  | email (header : Header) (r0 : Email)
  | securityDefinitionRequest (header : Header) (r0 : SecurityDefinitionRequest)

def Message.tokens : Message → List Token
  | .logon header r0 => ⟨[51, 53], [65]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logout header r0 => ⟨[51, 53], [53]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .heartbeat header r0 => ⟨[51, 53], [48]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .testRequest header r0 => ⟨[51, 53], [49]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .resendRequest header r0 => ⟨[51, 53], [50]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .reject header r0 => ⟨[51, 53], [51]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .sequenceResetGapFill header r0 => ⟨[51, 53], [52]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .newOrderSingle header r0 => ⟨[51, 53], [68]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .newOrderMultileg header r0 => ⟨[51, 53], [85, 65, 66]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelRequest header r0 => ⟨[51, 53], [70]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelReplaceRequest header r0 => ⟨[51, 53], [71]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .multilegOrderCancelReplaceRequest header r0 => ⟨[51, 53], [85, 65, 67]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderStatusRequest header r0 => ⟨[51, 53], [72]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .quoteRequest header r0 => ⟨[51, 53], [82]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .quote header r0 => ⟨[51, 53], [83]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .quoteCancel header r0 => ⟨[51, 53], [90]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .quoteStatusRequest header r0 => ⟨[51, 53], [97]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .tradingSessionStatusRequest header r0 => ⟨[51, 53], [103]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .email header r0 => ⟨[51, 53], [67]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .securityDefinitionRequest header r0 => ⟨[51, 53], [99]⟩ :: encodeParts (header.parts ++ r0.parts)

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
      else if token.value = [68] then
        if known (Header.tags ++ NewOrderSingle.tags) rest then do
          let header ← Header.decode rest
          let r0 ← NewOrderSingle.decode rest
          pure (.newOrderSingle header r0)
        else none
      else if token.value = [85, 65, 66] then
        if known (Header.tags ++ NewOrderMultileg.tags) rest then do
          let header ← Header.decode rest
          let r0 ← NewOrderMultileg.decode rest
          pure (.newOrderMultileg header r0)
        else none
      else if token.value = [70] then
        if known (Header.tags ++ OrderCancelRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderCancelRequest.decode rest
          pure (.orderCancelRequest header r0)
        else none
      else if token.value = [71] then
        if known (Header.tags ++ OrderCancelReplaceRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderCancelReplaceRequest.decode rest
          pure (.orderCancelReplaceRequest header r0)
        else none
      else if token.value = [85, 65, 67] then
        if known (Header.tags ++ MultilegOrderCancelReplaceRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← MultilegOrderCancelReplaceRequest.decode rest
          pure (.multilegOrderCancelReplaceRequest header r0)
        else none
      else if token.value = [72] then
        if known (Header.tags ++ OrderStatusRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderStatusRequest.decode rest
          pure (.orderStatusRequest header r0)
        else none
      else if token.value = [82] then
        if known (Header.tags ++ QuoteRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← QuoteRequest.decode rest
          pure (.quoteRequest header r0)
        else none
      else if token.value = [83] then
        if known (Header.tags ++ Quote.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Quote.decode rest
          pure (.quote header r0)
        else none
      else if token.value = [90] then
        if known (Header.tags ++ QuoteCancel.tags) rest then do
          let header ← Header.decode rest
          let r0 ← QuoteCancel.decode rest
          pure (.quoteCancel header r0)
        else none
      else if token.value = [97] then
        if known (Header.tags ++ QuoteStatusRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← QuoteStatusRequest.decode rest
          pure (.quoteStatusRequest header r0)
        else none
      else if token.value = [103] then
        if known (Header.tags ++ TradingSessionStatusRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← TradingSessionStatusRequest.decode rest
          pure (.tradingSessionStatusRequest header r0)
        else none
      else if token.value = [67] then
        if known (Header.tags ++ Email.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Email.decode rest
          pure (.email header r0)
        else none
      else if token.value = [99] then
        if known (Header.tags ++ SecurityDefinitionRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← SecurityDefinitionRequest.decode rest
          pure (.securityDefinitionRequest header r0)
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

theorem Message.decode_newOrderSingle (header : Header) (r0 : NewOrderSingle) :
    Message.decode (Message.tokens (.newOrderSingle header r0)) = some (.newOrderSingle header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (NewOrderSingle.tags) rfl rfl (by decide +kernel))
  have c1 := NewOrderSingle.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (NewOrderSingle.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ NewOrderSingle.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_newOrderMultileg (header : Header) (r0 : NewOrderMultileg) :
    Message.decode (Message.tokens (.newOrderMultileg header r0)) = some (.newOrderMultileg header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (NewOrderMultileg.tags) rfl rfl (by decide +kernel))
  have c1 := NewOrderMultileg.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (NewOrderMultileg.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ NewOrderMultileg.tags) rfl
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

theorem Message.decode_multilegOrderCancelReplaceRequest (header : Header) (r0 : MultilegOrderCancelReplaceRequest) :
    Message.decode (Message.tokens (.multilegOrderCancelReplaceRequest header r0)) = some (.multilegOrderCancelReplaceRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (MultilegOrderCancelReplaceRequest.tags) rfl rfl (by decide +kernel))
  have c1 := MultilegOrderCancelReplaceRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (MultilegOrderCancelReplaceRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ MultilegOrderCancelReplaceRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_orderStatusRequest (header : Header) (r0 : OrderStatusRequest) :
    Message.decode (Message.tokens (.orderStatusRequest header r0)) = some (.orderStatusRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderStatusRequest.tags) rfl rfl (by decide +kernel))
  have c1 := OrderStatusRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderStatusRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderStatusRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_quoteRequest (header : Header) (r0 : QuoteRequest) :
    Message.decode (Message.tokens (.quoteRequest header r0)) = some (.quoteRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (QuoteRequest.tags) rfl rfl (by decide +kernel))
  have c1 := QuoteRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (QuoteRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ QuoteRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_quote (header : Header) (r0 : Quote) :
    Message.decode (Message.tokens (.quote header r0)) = some (.quote header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (Quote.tags) rfl rfl (by decide +kernel))
  have c1 := Quote.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (Quote.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ Quote.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_quoteCancel (header : Header) (r0 : QuoteCancel) :
    Message.decode (Message.tokens (.quoteCancel header r0)) = some (.quoteCancel header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (QuoteCancel.tags) rfl rfl (by decide +kernel))
  have c1 := QuoteCancel.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (QuoteCancel.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ QuoteCancel.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_quoteStatusRequest (header : Header) (r0 : QuoteStatusRequest) :
    Message.decode (Message.tokens (.quoteStatusRequest header r0)) = some (.quoteStatusRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (QuoteStatusRequest.tags) rfl rfl (by decide +kernel))
  have c1 := QuoteStatusRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (QuoteStatusRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ QuoteStatusRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tradingSessionStatusRequest (header : Header) (r0 : TradingSessionStatusRequest) :
    Message.decode (Message.tokens (.tradingSessionStatusRequest header r0)) = some (.tradingSessionStatusRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (TradingSessionStatusRequest.tags) rfl rfl (by decide +kernel))
  have c1 := TradingSessionStatusRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (TradingSessionStatusRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ TradingSessionStatusRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_email (header : Header) (r0 : Email) :
    Message.decode (Message.tokens (.email header r0)) = some (.email header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (Email.tags) rfl rfl (by decide +kernel))
  have c1 := Email.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (Email.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ Email.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_securityDefinitionRequest (header : Header) (r0 : SecurityDefinitionRequest) :
    Message.decode (Message.tokens (.securityDefinitionRequest header r0)) = some (.securityDefinitionRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (SecurityDefinitionRequest.tags) rfl rfl (by decide +kernel))
  have c1 := SecurityDefinitionRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (SecurityDefinitionRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ SecurityDefinitionRequest.tags) rfl
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
  | newOrderSingle header r0 => exact Message.decode_newOrderSingle header r0
  | newOrderMultileg header r0 => exact Message.decode_newOrderMultileg header r0
  | orderCancelRequest header r0 => exact Message.decode_orderCancelRequest header r0
  | orderCancelReplaceRequest header r0 => exact Message.decode_orderCancelReplaceRequest header r0
  | multilegOrderCancelReplaceRequest header r0 => exact Message.decode_multilegOrderCancelReplaceRequest header r0
  | orderStatusRequest header r0 => exact Message.decode_orderStatusRequest header r0
  | quoteRequest header r0 => exact Message.decode_quoteRequest header r0
  | quote header r0 => exact Message.decode_quote header r0
  | quoteCancel header r0 => exact Message.decode_quoteCancel header r0
  | quoteStatusRequest header r0 => exact Message.decode_quoteStatusRequest header r0
  | tradingSessionStatusRequest header r0 => exact Message.decode_tradingSessionStatusRequest header r0
  | email header r0 => exact Message.decode_email header r0
  | securityDefinitionRequest header r0 => exact Message.decode_securityDefinitionRequest header r0

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

theorem Message.decodeBytes_newOrderSingle (header : Header) (r0 : NewOrderSingle) :
    Message.decodeBytes (Message.encode (.newOrderSingle header r0)) = some (.newOrderSingle header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [68]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (NewOrderSingle.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_newOrderSingle header r0

theorem Message.decodeBytes_newOrderMultileg (header : Header) (r0 : NewOrderMultileg) :
    Message.decodeBytes (Message.encode (.newOrderMultileg header r0)) = some (.newOrderMultileg header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [85, 65, 66]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (NewOrderMultileg.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_newOrderMultileg header r0

theorem Message.decodeBytes_orderCancelRequest (header : Header) (r0 : OrderCancelRequest) :
    Message.decodeBytes (Message.encode (.orderCancelRequest header r0)) = some (.orderCancelRequest header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [70]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (OrderCancelRequest.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderCancelRequest header r0

theorem Message.decodeBytes_orderCancelReplaceRequest (header : Header) (r0 : OrderCancelReplaceRequest) :
    Message.decodeBytes (Message.encode (.orderCancelReplaceRequest header r0)) = some (.orderCancelReplaceRequest header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [71]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (OrderCancelReplaceRequest.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderCancelReplaceRequest header r0

theorem Message.decodeBytes_multilegOrderCancelReplaceRequest (header : Header) (r0 : MultilegOrderCancelReplaceRequest) :
    Message.decodeBytes (Message.encode (.multilegOrderCancelReplaceRequest header r0)) = some (.multilegOrderCancelReplaceRequest header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [85, 65, 67]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (MultilegOrderCancelReplaceRequest.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_multilegOrderCancelReplaceRequest header r0

theorem Message.decodeBytes_orderStatusRequest (header : Header) (r0 : OrderStatusRequest) :
    Message.decodeBytes (Message.encode (.orderStatusRequest header r0)) = some (.orderStatusRequest header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [72]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (OrderStatusRequest.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderStatusRequest header r0

theorem Message.decodeBytes_quoteRequest (header : Header) (r0 : QuoteRequest) :
    Message.decodeBytes (Message.encode (.quoteRequest header r0)) = some (.quoteRequest header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [82]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (QuoteRequest.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_quoteRequest header r0

theorem Message.decodeBytes_quote (header : Header) (r0 : Quote) :
    Message.decodeBytes (Message.encode (.quote header r0)) = some (.quote header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [83]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (Quote.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_quote header r0

theorem Message.decodeBytes_quoteCancel (header : Header) (r0 : QuoteCancel) :
    Message.decodeBytes (Message.encode (.quoteCancel header r0)) = some (.quoteCancel header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [90]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (QuoteCancel.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_quoteCancel header r0

theorem Message.decodeBytes_quoteStatusRequest (header : Header) (r0 : QuoteStatusRequest) :
    Message.decodeBytes (Message.encode (.quoteStatusRequest header r0)) = some (.quoteStatusRequest header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [97]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (QuoteStatusRequest.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_quoteStatusRequest header r0

theorem Message.decodeBytes_tradingSessionStatusRequest (header : Header) (r0 : TradingSessionStatusRequest) :
    Message.decodeBytes (Message.encode (.tradingSessionStatusRequest header r0)) = some (.tradingSessionStatusRequest header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [103]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (TradingSessionStatusRequest.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_tradingSessionStatusRequest header r0

theorem Message.decodeBytes_email (header : Header) (r0 : Email) :
    Message.decodeBytes (Message.encode (.email header r0)) = some (.email header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [67]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (Email.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_email header r0

theorem Message.decodeBytes_securityDefinitionRequest (header : Header) (r0 : SecurityDefinitionRequest) :
    Message.decodeBytes (Message.encode (.securityDefinitionRequest header r0)) = some (.securityDefinitionRequest header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [99]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (SecurityDefinitionRequest.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_securityDefinitionRequest header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | logon header r0 => exact Message.decodeBytes_logon header r0
  | logout header r0 => exact Message.decodeBytes_logout header r0
  | heartbeat header r0 => exact Message.decodeBytes_heartbeat header r0
  | testRequest header r0 => exact Message.decodeBytes_testRequest header r0
  | resendRequest header r0 => exact Message.decodeBytes_resendRequest header r0
  | reject header r0 => exact Message.decodeBytes_reject header r0
  | sequenceResetGapFill header r0 => exact Message.decodeBytes_sequenceResetGapFill header r0
  | newOrderSingle header r0 => exact Message.decodeBytes_newOrderSingle header r0
  | newOrderMultileg header r0 => exact Message.decodeBytes_newOrderMultileg header r0
  | orderCancelRequest header r0 => exact Message.decodeBytes_orderCancelRequest header r0
  | orderCancelReplaceRequest header r0 => exact Message.decodeBytes_orderCancelReplaceRequest header r0
  | multilegOrderCancelReplaceRequest header r0 => exact Message.decodeBytes_multilegOrderCancelReplaceRequest header r0
  | orderStatusRequest header r0 => exact Message.decodeBytes_orderStatusRequest header r0
  | quoteRequest header r0 => exact Message.decodeBytes_quoteRequest header r0
  | quote header r0 => exact Message.decodeBytes_quote header r0
  | quoteCancel header r0 => exact Message.decodeBytes_quoteCancel header r0
  | quoteStatusRequest header r0 => exact Message.decodeBytes_quoteStatusRequest header r0
  | tradingSessionStatusRequest header r0 => exact Message.decodeBytes_tradingSessionStatusRequest header r0
  | email header r0 => exact Message.decodeBytes_email header r0
  | securityDefinitionRequest header r0 => exact Message.decodeBytes_securityDefinitionRequest header r0

/-- BeginString as the venue fixes it: FIX.4.2 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 46, 52, 46, 50, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.TaifexTaifexderivativesOrderentryFix42V312Client
